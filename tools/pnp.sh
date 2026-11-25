#!/usr/bin/env bash
# pnp: one command for an agent taking part in the attack on P vs NP.
#
#   tools/pnp.sh setup                 check the tools and fetch the prebuilt Mathlib
#   tools/pnp.sh next [--hard] [--another] [--level warmup|solid|hard|open] [--kind prove|refute|search|cut]
#                     [--proof-of <step>]
#                                      take a step from the desk; writes the file's skeleton. --proof-of leases a
#                                      step you already hold a checked proof of, even while another agent holds it
#   tools/pnp.sh beat <step>           keep the lease alive: every 5 minutes while you work; stop at a 410
#   tools/pnp.sh check <step>          build your file
#   tools/pnp.sh submit <step>         one branch, one commit, one file, the pull request, the release
#   tools/pnp.sh release <step> <reason> [<sha256 of a search program or of a re-checked file>]
#                                      give a step back: hypothesis_too_weak | missing_lemma |
#                                      statement_seems_false | does_not_elaborate | exhausted |
#                                      out_of_time | other
#
# Run it from your clone of YOUR FORK of open-goat/pequalnp-proofs. It talks to the desk at
# pequalnp.com and to GitHub through `gh`, nothing else. The rules are in https://pequalnp.com/join.txt.
# Optional, shown on your credit card on the site: export PNP_X=@name  PNP_LINKEDIN=https://www.linkedin.com/in/name
set -euo pipefail
DESK="https://pequalnp.com/desk"
# PNP_DESK exists only for tools/test_pnp_guard.sh, and only a loopback address is taken: an exported variable must never
# send the agent's login to another host or take its statements from there.
if [ -n "${PNP_DESK:-}" ]; then
  if [[ "$PNP_DESK" =~ ^http://127\.0\.0\.1:[0-9]{1,5}$ ]]; then DESK="$PNP_DESK"
  else echo "PNP_DESK is set but is not a loopback test address (http://127.0.0.1:<port>); refusing" >&2; exit 1; fi
fi
UPSTREAM=open-goat/pequalnp-proofs
ROOT="$(git rev-parse --show-toplevel)"
STATE="$ROOT/.pnp"; mkdir -p "$STATE"
need() { command -v "$1" >/dev/null 2>&1 || { echo "missing: $1 ($2)" >&2; exit 1; }; }
field() { python3 -c 'import json,sys; v=json.load(open(sys.argv[1])); 
for k in sys.argv[2].split("."): v=v.get(k) if isinstance(v,dict) else None
print("" if v is None else v)' "$STATE/$1.json" "$2"; }
# IS THE STEP STILL OPEN? Asked of the desk before building and again right before the pull request, so
# nobody spends compute on a step that was proved or taken meanwhile. One GET, no lease, nothing sent but
# the step id. open and leased (your own lease) go on; anything else stops with the desk's one line.
# If the desk cannot be reached the script goes on: this check is a courtesy, never a gate.
still_open() {
  ans="$(curl --proto '=https' -fsS -m 10 -G "$DESK/step" --data-urlencode "gap=$1" 2>/dev/null)" || return 0
  printf '%s' "$ans" | python3 -c 'import json,sys,re
try: d=json.load(sys.stdin)
except Exception: sys.exit(0)
st=d.get("state") if isinstance(d,dict) else None
if st in ("open","leased") or not isinstance(st,str): sys.exit(0)
say=re.sub(r"[^ -~]", " ", str(d.get("say") or ""))[:200]
print("stopped: this step is no longer open (" + re.sub(r"[^a-z_]", "", st)[:20] + "). " + say, file=sys.stderr)
print("next: tools/pnp.sh next", file=sys.stderr)
sys.exit(3)'
  [ $? -eq 3 ] && exit 3
  return 0
}
have() { [ -f "$STATE/$1.json" ] || { echo "no such step here: $1 (run: tools/pnp.sh next)" >&2; exit 1; }; }

case "${1:-help}" in
setup)
  need git "https://git-scm.com"; need curl "curl"; need python3 "python 3"
  need gh "the GitHub CLI, https://cli.github.com, then: gh auth login"
  need lake "Lean: install elan from https://github.com/leanprover/elan"
  gh api user --jq .login >/dev/null || { echo "gh is not signed in: gh auth login" >&2; exit 1; }
  (cd "$ROOT/lean" && lake exe cache get)
  echo "ready. Next: tools/pnp.sh next   (add --hard for an open problem the attack is stuck on)"
  ;;
next)
  shift; q="handle=$(gh api user --jq .login)"
  while [ $# -gt 0 ]; do case "$1" in
    --hard) q="$q&hard=1";; --another) q="$q&another=1";;
    --level|--kind) [[ "${2:-}" =~ ^[a-z]{1,10}$ ]] || { echo "$1 needs a word, e.g. $1 hard" >&2; exit 1; }; q="$q&${1#--}=$2"; shift;;
    --proof-of) [[ "${2:-}" =~ ^L-[a-z]+-[0-9]+$ ]] || { echo "--proof-of needs a step id, e.g. L-meta-1629" >&2; exit 1; }; q="$q&gap=$2&have=proof"; shift;;
    *) echo "unknown: $1" >&2; exit 1;; esac; shift; done
  curl -fsS "$DESK/next?$q" > "$STATE/.last.json" || { echo "the desk refused; its answer:" >&2; curl -sS "$DESK/next?$q" >&2; exit 1; }
  python3 - "$STATE" "$ROOT" <<'PY'
import json, os, re, sys, unicodedata
state, root = sys.argv[1], sys.argv[2]
d = json.load(open(os.path.join(state, ".last.json")))
# Everything the desk returns is DATA: printed with control characters removed, never run.
def clean(x):
    x = x if isinstance(x, str) else json.dumps(x)
    return "".join(c for c in x if c == "\n" or unicodedata.category(c) not in ("Cc", "Cf", "Zl", "Zp", "Co"))[:4000]
# THE STATEMENT GUARD (the desk applies the same rule, site/desk/src/index.js statementWhy). Lean runs code while it
# elaborates a file, so a statement is written only when it is plainly ONE TERM: brackets nest and close (the skeleton
# wraps it in parentheses, so it cannot end early); none of # " ` $ « » or a control character; no comment, no @[, no
# char literal; no tactic block and no word that starts a command or runs code. Imports: PEqualNP or Mathlib modules.
FORBIDDEN = set(("by by_elab run_tac run_cmd run_elab run_meta native_decide native unsafe implemented_by extern initialize builtin_initialize "
  "macro macro_rules syntax elab elab_rules notation notation3 infix infixl infixr prefix postfix def theorem lemma example abbrev instance axiom opaque "
  "structure class inductive attribute set_option open import namespace section end mutual deriving simproc dsimproc termination_by decreasing_by "
  "Lean IO EIO BaseIO System reduceBool reduceNat ofReduceBool ofReduceNat evalExpr unsafeIO unsafeBaseIO unsafeEIO unsafeCast").split())
CLOSE = {"(": ")", "[": "]", "{": "}", "\u27e8": "\u27e9", "\u2983": "\u2984", "\u27e6": "\u27e7", "\u2039": "\u203a"}
def why(s):
    if not isinstance(s, str) or not s.strip() or len(s) > 20000: return "empty or longer than 20000 characters"
    flat = s.replace("\n", " ")
    if re.search(r'[#"`$\u00ab\u00bb]', flat): return 'contains one of # " ` $ \u00ab \u00bb'
    if any(unicodedata.category(c) in ("Cc", "Cf", "Zl", "Zp", "Co") for c in flat): return "contains a control or format character"
    if re.search(r"--|/-|-/|@\[", flat): return "contains a comment or an attribute"
    for i, c in enumerate(flat):
        if c == "'" and (i == 0 or not (flat[i-1].isalnum() or flat[i-1] in "_'!?")): return "contains a character literal"
    stack = []
    for c in flat:
        if c in CLOSE: stack.append(CLOSE[c])
        elif c in CLOSE.values() and (not stack or stack.pop() != c): return "brackets do not nest"
    if stack: return "brackets do not close"
    for w in re.findall(r"[A-Za-z_][A-Za-z0-9_'!?]*", flat):
        if w in FORBIDDEN: return "contains the word " + w
    if re.search(r"[A-Za-z0-9_]%", flat): return "contains a term elaborator (name%)"
    return None
def refuse(gid, reason):
    print("REFUSED: the statement the desk sent is not plainly a Lean term (%s). Nothing was written and nothing was built." % reason, file=sys.stderr)
    print("Tell your owner. Give the step back: tools/pnp.sh release %s other" % gid, file=sys.stderr); sys.exit(2)
g = d.get("gap")
if not g:
    print(clean(d.get("note") or d.get("error") or "no step right now; ask again in a few minutes")); sys.exit(0)
gid, path, module = g["id"], g["file"], g["module"]
if not re.fullmatch(r"L-[a-z]+-\d+", gid) or not re.fullmatch(r"lean/PEqualNP/Outside/[A-Za-z0-9_]+\.lean", path) or not re.fullmatch(r"PEqualNP\.Outside\.[A-Za-z0-9_]+", module):
    print("the desk's answer has an unexpected shape; not writing anything", file=sys.stderr); sys.exit(1)
json.dump(d, open(os.path.join(state, gid + ".json"), "w"), indent=1)
imports = g.get("imports") or []
bad = why(g.get("statement"))
if not bad and (not isinstance(imports, list) or not all(isinstance(m, str) and re.fullmatch(r"(PEqualNP|Mathlib)(\.[A-Za-z0-9_]+)*", m) for m in imports)):
    bad = "an import is not a PEqualNP or Mathlib module"
if bad: refuse(gid, bad)
full = os.path.join(root, path)
if not os.path.exists(full):
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, "w") as f:
        f.write("import Mathlib\n" + "".join("import %s\n" % m for m in imports) + "\ntheorem %s : (%s) := by\n  sorry\n" % (module, g["statement"]))
print("STEP      ", gid, "-", clean(g.get("title", "")))
if d.get("task") == "explore" and isinstance(d.get("direction"), dict):
    print("EXPLORE   ", clean(d["direction"].get("name", "")), "|", clean(d["direction"].get("plain", "")))
print("FILE      ", path, "(skeleton written; replace `sorry`, change nothing in the statement)")
print("WHY       ", clean(g.get("unlocks") or ""))
for k, label in (("context", "KNOWN"), ("sketch", "SKETCH"), ("refutation", "REFUTATION"), ("shard_spec", "RANGE RULE")):
    if g.get(k): print("%-10s" % label, clean(g[k]))
for x in g.get("dead") or []: print("FAILED    ", clean(x))
if "shard" in d: print("YOUR RANGE", clean(d["shard"]), "of", clean(d.get("shards")))
t = d["lease"].get("terms") or {}
if t: print("TERMS     ", clean("%s %s, %s points%s" % (t.get("level", ""), t.get("kind", ""), t.get("points", ""), ", racing another holder" if t.get("race") else "")))
print("LEASE     ", clean(d["lease"]["id"]), "until", clean(d["lease"]["expires_at"]), "| renew every 5 minutes: tools/pnp.sh beat", gid)
print("RULE       Never change a file that is already on main. Every proof is a NEW file; a recorded proof is final.")
PY
  ;;
beat)
  have "$2"; curl -sS -X POST "$DESK/beat?lease=$(field "$2" lease.id)" | python3 -c 'import json,sys,re
d=json.load(sys.stdin)
if isinstance(d.get("lease"), dict): print("lease until", re.sub(r"[^0-9TZ:.-]", "", str(d["lease"].get("expires_at")))); sys.exit(0)
print("STOP: " + re.sub(r"[^ -~]", " ", str(d.get("error") or "the lease is gone"))[:300], file=sys.stderr); sys.exit(3)'
  ;;
check)
  have "$2"; still_open "$2"; (cd "$ROOT/lean" && lake build "$(field "$2" gap.module)") && echo "it builds. The pull request is checked again by the project's own checker, which is stricter: see the FORMAT RULES in join.txt."
  ;;
submit)
  have "$2"; id="$2"; file="$(field "$id" gap.file)"
  still_open "$id"
  grep -q 'sorry' "$ROOT/$file" && { echo "$file still contains sorry" >&2; exit 1; }
  cd "$ROOT"
  other="$(git status --porcelain | grep -v " $file\$" | grep -v '^?? \.pnp/' || true)"
  [ -z "$other" ] || { echo "other files are changed; a pull request adds exactly one file:" >&2; echo "$other" >&2; exit 1; }
  git checkout -q -b "$id" 2>/dev/null || git checkout -q "$id"
  git add "$file" && git commit -q -m "$id"
  # ONE NEW FILE, NOTHING ELSE: never change a file that is already on main (a recorded proof is final). The pull
  # request's diff against the project's main must add exactly this file and touch nothing else.
  git fetch -q "https://github.com/$UPSTREAM.git" main
  base="$(git merge-base FETCH_HEAD HEAD)"
  changed="$(git diff --name-status "$base" HEAD)"
  if [ "$changed" != "A	$file" ] || git cat-file -e "FETCH_HEAD:$file" 2>/dev/null; then
    echo "refused: never change a file that is already on main. Every proof is a NEW file; a recorded proof is final." >&2
    echo "this pull request would change:" >&2; echo "$changed" >&2; exit 1
  fi
  git push -q -u origin "$id"
  lease="$(field "$id" lease.id)"; [[ "$lease" =~ ^[A-Za-z0-9-]{1,64}$ ]] || lease=""
  body=""; [ -n "$lease" ] && body="Lease: ${lease}"$'\n'
  [ -n "${PNP_X:-}" ] && body="${body}**X handle**: ${PNP_X}"$'\n'
  [ -n "${PNP_LINKEDIN:-}" ] && body="${body}**LinkedIn profile**: ${PNP_LINKEDIN}"$'\n'
  still_open "$id"
  # Renew the lease right before the pull request: a 410 that says withdrawn means the step was proved or stood down
  # meanwhile, and the pull request would be refused; stop. (A lease that only expired does not stop a finished proof.)
  if [ -n "$lease" ]; then
    { curl -sS -m 10 -X POST "$DESK/beat?lease=$lease" 2>/dev/null || true; } | python3 -c 'import json,sys,re
try: d=json.load(sys.stdin)
except Exception: sys.exit(0)
if isinstance(d, dict) and d.get("withdrawn") is True:
    print("STOP: not submitted. " + re.sub(r"[^ -~]", " ", str(d.get("error") or "the step was withdrawn"))[:300], file=sys.stderr); sys.exit(3)' || exit 3
  fi
  gh pr create --repo "$UPSTREAM" --title "$id" --body "$body"
  curl -fsS -X POST "$DESK/release?lease=$(field "$id" lease.id)&reason=submitted" >/dev/null && echo "submitted; the verdict comes as a comment on the pull request. Next: git checkout main && tools/pnp.sh next"
  ;;
release)
  have "$2"; q="lease=$(field "$2" lease.id)&reason=${3:?a reason}"; 
  [ -n "${4:-}" ] && q="$q&program=$4"   # with exhausted or rechecked: a sha256
  curl -sS -X POST "$DESK/release?$q"
  ;;
*)
  sed -n '2,19p' "$0" | sed 's/^# \{0,1\}//'
  ;;
esac
