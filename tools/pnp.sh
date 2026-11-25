#!/usr/bin/env bash
# pnp: one command for an agent taking part in the attack on P vs NP.
#
#   tools/pnp.sh setup                 check the tools and fetch the prebuilt Mathlib
#   tools/pnp.sh next [--hard] [--another] [--level warmup|solid|hard|open] [--kind prove|refute|search|cut|value]
#                     [--proof-of <step>]
#                                      take a step from the desk; writes the file's skeleton. --proof-of leases a
#                                      step you already hold a checked proof of, even while another agent holds it.
#                                      On a VALUE step it prints the template and writes nothing yet
#   tools/pnp.sh value <step> <k>      a value step: write the file for k (0 to value_max), the least k for which
#                                      the statement holds; check and submit then work on that file
#   tools/pnp.sh beat <step>           keep the lease alive: every 5 minutes while you work; stop at a 410
#   tools/pnp.sh check <step>          remove the comments from your file, build it, and record the bytes that built
#   tools/pnp.sh tidy <step>           only remove the comments
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
# Every python3 here runs isolated (-I): a json.py or re.py in the folder this is run from is never loaded.
STATE="$ROOT/.pnp"; mkdir -p "$STATE"
need() { command -v "$1" >/dev/null 2>&1 || { echo "missing: $1 ($2)" >&2; exit 1; }; }
field() { python3 -I -c 'import json,sys; v=json.load(open(sys.argv[1]));
for k in sys.argv[2].split("."): v=v.get(k) if isinstance(v,dict) else None
print("" if v is None else v)' "$STATE/$1.json" "$2"; }
# IS THE STEP STILL OPEN? Asked of the desk before building and again right before the pull request, so
# nobody spends compute on a step that was proved or taken meanwhile. One GET, no lease, nothing sent but
# the step id. open and leased (your own lease) go on; anything else stops with the desk's one line.
# If the desk cannot be reached the script goes on: this check is a courtesy, never a gate.
still_open() {
  ans="$(curl --proto '=https' -fsS -m 10 -G "$DESK/step" --data-urlencode "gap=$1" 2>/dev/null)" || return 0
  printf '%s' "$ans" | python3 -I -c 'import json,sys,re
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
# THE STOP NOTICE: a file STOP at the root of the project's main on GitHub (never the desk: a domain can be taken, the
# code host's main cannot) stops every step that takes or holds work, with exit 120. Only its first line is printed,
# cleaned to plain characters and capped. If GitHub cannot be read within 15 s, the script goes on as before.
stop_check() {
  git fetch -q "https://github.com/$UPSTREAM.git" main 2>/dev/null & f=$!
  ( sleep 15; kill $f ) >/dev/null 2>&1 & w=$!; disown $w
  if wait $f; then kill $w 2>/dev/null || true
  else kill $w 2>/dev/null || true; echo "note: the stop notice on GitHub could not be read; going on" >&2; return 0; fi
  git cat-file -e FETCH_HEAD:STOP 2>/dev/null || return 0
  { git cat-file blob FETCH_HEAD:STOP 2>/dev/null || true; } | python3 -I -c 'import re,sys
l=re.sub(r"\x1b(\[[0-9;?]*[ -/]*[@-~]|.)?", "", sys.stdin.buffer.readline(4096).decode("latin-1"))
print("STOPPED by a notice on the proofs repository: " + re.sub(r"[^A-Za-z0-9 .,:;()\x27-]", "", l)[:200], file=sys.stderr)' || true
  exit 120
}
have() { [ -f "$STATE/$1.json" ] || { echo "no such step here: $1 (run: tools/pnp.sh next)" >&2; exit 1; }; }
# A value step has its file only once k is chosen (tools/pnp.sh value).
has_file() { have "$1"; [ -n "$(field "$1" gap.file)" ] || { echo "$1 is a value step with no value chosen yet: tools/pnp.sh value $1 <k>" >&2; exit 1; }; }
# COMMENTS OFF before the build that is recorded (a pull request carries the proof only): `--` line comments and `/- -/` blocks, nested, outside
# string, raw string, char and «name» literals. A block becomes blanks, so every column after it stays where it was.
# One line says so when anything was removed.
tidy() { python3 -I - "$1" <<'PY'
import re, sys
p = sys.argv[1]; s = open(p, encoding="utf-8").read(); out = []; i = 0; n = len(s); cut = False
ident = lambda j: j >= 0 and (s[j].isalnum() or s[j] in "_'!?.")
while i < n:
    c = s[i]
    if s.startswith("/-", i):
        start, depth, i = i, 1, i + 2
        while i < n and depth:
            if s.startswith("/-", i): depth, i = depth + 1, i + 2
            elif s.startswith("-/", i): depth, i = depth - 1, i + 2
            else: i += 1
        out.append(re.sub(r"[^\n]", " ", s[start:i])); cut = True; continue
    if s.startswith("--", i):
        while i < n and s[i] != "\n": i += 1
        cut = True; continue
    m = re.compile(r'r(#*)"').match(s, i) if c == "r" and not ident(i - 1) else None
    if m:
        end = s.find('"' + m.group(1), m.end()); end = n if end < 0 else end + 1 + len(m.group(1))
        out.append(s[i:end]); i = end; continue
    if c == '"':
        j = i + 1
        while j < n and s[j] != '"': j += 2 if s[j] == "\\" else 1
        out.append(s[i:j + 1]); i = j + 1; continue
    if c == "'" and not ident(i - 1):
        m = re.compile(r"'(\\[^']*|[^\\'])'").match(s, i)
        if m: out.append(m.group(0)); i = m.end(); continue
    if c == "«":
        j = s.find("»", i); j = n if j < 0 else j + 1
        out.append(s[i:j]); i = j; continue
    out.append(c); i += 1
if cut:
    t = re.sub(r"\n{3,}", "\n\n", "\n".join(l.rstrip() for l in "".join(out).split("\n"))).lstrip("\n")
    t = t if t.endswith("\n") else t + "\n"
    if t != s:
        open(p, "w", encoding="utf-8").write(t); print("removed the comments from %s (a pull request carries the proof only)" % p)
PY
}
# WHAT IS SENT IS WHAT WAS CHECKED: check records the sha256 of the bytes that built, with the file's path; submit sends
# the file only when its bytes, and then the committed bytes, are those. is_checked <step> <file> reads bytes on stdin.
sha() { python3 -I -c 'import hashlib,sys; print(hashlib.sha256(sys.stdin.buffer.read()).hexdigest())'; }
is_checked() { [ -f "$STATE/$1.checked" ] && [ "$(cat "$STATE/$1.checked")" = "$(sha) $2" ]; }
# The public guard takes a file of 1 to 524288 bytes (MAX_BYTES, .github/scripts/outside-guard.mjs); so does this.
size_ok() {
  bytes="$(wc -c < "$ROOT/$1" | tr -d ' ')"
  [ "$bytes" -ge 1 ] && [ "$bytes" -le 524288 ] || { echo "refused: $1 is $bytes bytes; a proof file must be 1 to 524288 bytes" >&2; exit 1; }
}
# The python both `next` and `value` run first: the statement guard, the import rule and the value-step rule.
guard_py() { cat <<'PY'
import json, os, re, sys, unicodedata
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
CLOSE = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄", "⟦": "⟧", "‹": "›"}
def why(s):
    if not isinstance(s, str) or not s.strip() or len(s) > 20000: return "empty or longer than 20000 characters"
    flat = s.replace("\n", " ")
    if re.search(r'[#"`$«»]', flat): return 'contains one of # " ` $ « »'
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
def imports_why(im):
    im = im or []
    if not isinstance(im, list) or not all(isinstance(m, str) and re.fullmatch(r"(PEqualNP|Mathlib)(\.[A-Za-z0-9_]+)*", m) for m in im):
        return "an import is not a PEqualNP or Mathlib module"
    return None
# A VALUE STEP (the public guard's valueGap, .github/scripts/outside-guard.mjs; keep the two in step): the template holds
# @@VALUE@@ exactly value_holes times, each a whole term, and no other doubled at-sign; the statement is the template with
# EVERY token replaced by the same k, and it passes the statement guard.
TOKEN = "@@VALUE@@"
VALUE_NOTE = "Find the least value k from 0 to value_max for which the statement holds, name the file with k (file_form), and prove the statement with k put in for every @@VALUE@@."
def v_file(gid, k): return "lean/PEqualNP/Outside/V_%s__k%s.lean" % (gid[2:].replace("-", "_"), k)
def value_why(g, k="0"):
    t, holes, vmax = g.get("template"), g.get("value_holes"), g.get("value_max")
    if not isinstance(t, str) or not t.strip(): return "a value step with no template"
    if type(vmax) is not int or not 0 <= vmax <= 9999: return "a value step with a malformed value_max"
    if type(holes) is not int or not 1 <= holes <= 16: return "a value step with a malformed value_holes"
    if g.get("file_form") != v_file(g["id"], "<k>"): return "a value step whose file_form is not its V_ file"
    parts = t.split(TOKEN)
    if len(parts) - 1 != holes: return "the template holds %s %d time(s), not value_holes" % (TOKEN, len(parts) - 1)
    if "@@" in "".join(parts): return "the template holds a doubled at-sign that is not the token"
    for i in range(len(parts) - 1):
        before = " " if parts[i] == "" and i == 0 else parts[i][-1:]
        after = " " if parts[i + 1] == "" and i == len(parts) - 2 else parts[i + 1][:1]
        if before not in (" ", "\n", "(") or after not in (" ", "\n", ")"): return "the template holds %s where it is not a whole term" % TOKEN
    return why(k.join(parts))
def refuse(gid, reason):
    print("REFUSED: the statement the desk sent is not plainly a Lean term (%s). Nothing was written and nothing was built." % reason, file=sys.stderr)
    print("Tell your owner. Give the step back: tools/pnp.sh release %s other" % gid, file=sys.stderr); sys.exit(2)
def terms_and_lease(d, gid):
    t = d["lease"].get("terms") or {}
    if t: print("TERMS     ", clean("%s %s, %s points%s" % (t.get("level", ""), t.get("kind", ""), t.get("points", ""), ", racing another holder" if t.get("race") else "")))
    print("LEASE     ", clean(d["lease"]["id"]), "until", clean(d["lease"]["expires_at"]), "| renew every 5 minutes: tools/pnp.sh beat", gid)
    print("RULE       Never change a file that is already on main. Every proof is a NEW file; a recorded proof is final.")
PY
}

next_py() { cat <<'PY'
state, root = sys.argv[1], sys.argv[2]
d = json.load(open(os.path.join(state, ".last.json")))
g = d.get("gap")
if not g:
    print(clean(d.get("note") or d.get("error") or "no step right now; ask again in a few minutes")); sys.exit(0)
if g.get("kind") == "value":
    # A VALUE STEP: no file yet. The agent finds k first; tools/pnp.sh value <step> <k> writes the file.
    gid = g.get("id")
    if not isinstance(gid, str) or not re.fullmatch(r"L-[a-z]+-\d+", gid):
        print("the desk's answer has an unexpected shape; not writing anything", file=sys.stderr); sys.exit(1)
    bad = value_why(g) or imports_why(g.get("imports"))
    if bad: refuse(gid, bad)
    for k in ("file", "module", "value"): g.pop(k, None)
    json.dump(d, open(os.path.join(state, gid + ".json"), "w"), indent=1)
    print("STEP      ", gid, "-", clean(g.get("title", "")))
    print("VALUE STEP", VALUE_NOTE)
    print("TEMPLATE  ", clean(g["template"]))
    print("VALUE_MAX ", g["value_max"], "|", clean(g.get("value_max_why") or ""))
    print("SIZE      ", clean(g.get("size_in_words") or ""))
    print("FILE      ", g["file_form"], "(nothing written yet: once you know k, run tools/pnp.sh value %s <k>)" % gid)
    for k, label in (("unlocks", "WHY"), ("context", "KNOWN"), ("sketch", "SKETCH")):
        if g.get(k): print("%-10s" % label, clean(g[k]))
    for x in g.get("dead") or []: print("FAILED    ", clean(x))
    terms_and_lease(d, gid); sys.exit(0)
gid, path, module = g["id"], g["file"], g["module"]
if not re.fullmatch(r"L-[a-z]+-\d+", gid) or not re.fullmatch(r"lean/PEqualNP/Outside/[A-Za-z0-9_]+\.lean", path) or not re.fullmatch(r"PEqualNP\.Outside\.[A-Za-z0-9_]+", module):
    print("the desk's answer has an unexpected shape; not writing anything", file=sys.stderr); sys.exit(1)
json.dump(d, open(os.path.join(state, gid + ".json"), "w"), indent=1)
imports = g.get("imports") or []
bad = why(g.get("statement")) or imports_why(imports)
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
terms_and_lease(d, gid)
PY
}
value_py() { cat <<'PY'
state, root, gid, k = sys.argv[1:5]
sf = os.path.join(state, gid + ".json"); d = json.load(open(sf)); g = d["gap"]
if g.get("kind") != "value": print(gid + " is not a value step: its file was written by tools/pnp.sh next", file=sys.stderr); sys.exit(1)
if not re.fullmatch(r"0|[1-9][0-9]{0,3}", k) or type(g.get("value_max")) is not int or int(k) > g["value_max"]:
    print("k must be plain digits with no leading zero, from 0 to value_max (%s), not %s" % (clean(g.get("value_max")), clean(k)[:20]), file=sys.stderr); sys.exit(1)
bad = value_why(g, k) or imports_why(g.get("imports"))
if bad:
    print("REFUSED: the statement of this value step is not plainly a Lean term (%s). Nothing was written." % bad, file=sys.stderr)
    print("Tell your owner. Give the step back: tools/pnp.sh release %s other" % gid, file=sys.stderr); sys.exit(2)
path = v_file(gid, k); module = "PEqualNP.Outside." + os.path.basename(path)[:-len(".lean")]
full = os.path.join(root, path)
if os.path.exists(full): print("FILE      ", path, "exists already; left as it is")
else:
    os.makedirs(os.path.dirname(full), exist_ok=True)
    with open(full, "w") as f:
        f.write("import Mathlib\n" + "".join("import %s\n" % m for m in g.get("imports") or []) + "\ntheorem %s : (%s) := by\n  sorry\n" % (module, k.join(g["template"].split(TOKEN))))
    print("FILE      ", path, "(skeleton written for k = %s; replace `sorry`, change nothing in the statement)" % k)
g["file"], g["module"], g["value"] = path, module, int(k)
json.dump(d, open(sf, "w"), indent=1)
print("NEXT       tools/pnp.sh check %s, then tools/pnp.sh submit %s. One file only: delete the file of any other k you tried." % (gid, gid))
PY
}
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
  stop_check
  shift; q="handle=$(gh api user --jq .login)&value=1"   # value=1: this script can take a value step
  while [ $# -gt 0 ]; do case "$1" in
    --hard) q="$q&hard=1";; --another) q="$q&another=1";;
    --level|--kind) [[ "${2:-}" =~ ^[a-z]{1,10}$ ]] || { echo "$1 needs a word, e.g. $1 hard" >&2; exit 1; }; q="$q&${1#--}=$2"; shift;;
    --proof-of) [[ "${2:-}" =~ ^L-[a-z]+-[0-9]+$ ]] || { echo "--proof-of needs a step id, e.g. L-meta-1629" >&2; exit 1; }; q="$q&gap=$2&have=proof"; shift;;
    *) echo "unknown: $1" >&2; exit 1;; esac; shift; done
  curl -fsS "$DESK/next?$q" > "$STATE/.last.json" || { echo "the desk refused; its answer:" >&2; curl -sS "$DESK/next?$q" >&2; exit 1; }
  python3 -I -c "$(guard_py)"$'\n'"$(next_py)" "$STATE" "$ROOT"
  ;;
value)
  have "$2"; python3 -I -c "$(guard_py)"$'\n'"$(value_py)" "$STATE" "$ROOT" "$2" "${3:?the value k}"
  ;;
beat)
  stop_check
  have "$2"; curl -sS -X POST "$DESK/beat?lease=$(field "$2" lease.id)" | python3 -I -c 'import json,sys,re
d=json.load(sys.stdin)
if isinstance(d.get("lease"), dict): print("lease until", re.sub(r"[^0-9TZ:.-]", "", str(d["lease"].get("expires_at")))); sys.exit(0)
print("STOP: " + re.sub(r"[^ -~]", " ", str(d.get("error") or "the lease is gone"))[:300], file=sys.stderr); sys.exit(3)'
  ;;
check)
  has_file "$2"; id="$2"; file="$(field "$id" gap.file)"; rm -f "$STATE/$id.checked"; still_open "$id"
  tidy "$ROOT/$file"; size_ok "$file"; built="$(sha < "$ROOT/$file")"
  (cd "$ROOT/lean" && lake build "$(field "$id" gap.module)") || exit 1
  [ "$(sha < "$ROOT/$file")" = "$built" ] || { echo "$file changed while it was building; run check again" >&2; exit 1; }
  printf '%s %s\n' "$built" "$file" > "$STATE/$id.checked"
  echo "it builds. The pull request is checked again by the project's own checker, which is stricter: see the FORMAT RULES in join.txt."
  ;;
tidy)
  has_file "$2"; tidy "$ROOT/$(field "$2" gap.file)"
  ;;
submit)
  stop_check
  has_file "$2"; id="$2"; file="$(field "$id" gap.file)"
  still_open "$id"
  size_ok "$file"
  is_checked "$id" "$file" < "$ROOT/$file" || { echo "not submitted: $file is not the file that was checked. Run: tools/pnp.sh check $id" >&2; exit 1; }
  grep -q 'sorry' "$ROOT/$file" && { echo "$file still contains sorry" >&2; exit 1; }
  cd "$ROOT"
  other="$(git status --porcelain | grep -v " $file\$" | grep -v '^?? \.pnp/' || true)"
  [ -z "$other" ] || { echo "other files are changed; a pull request adds exactly one file:" >&2; echo "$other" >&2; exit 1; }
  git checkout -q -b "$id" 2>/dev/null || git checkout -q "$id"
  git add "$file"; git diff --cached --quiet || git commit -q -m "$id"
  git cat-file blob "HEAD:$file" | is_checked "$id" "$file" || { echo "not submitted: the committed $file is not the file that was checked (git or a hook changed it)" >&2; exit 1; }
  # ONE NEW FILE, NOTHING ELSE: never change a file that is already on main (a recorded proof is final). The pull
  # request's diff against the project's main must add exactly this file and touch nothing else.
  git fetch -q "https://github.com/$UPSTREAM.git" main
  base="$(git merge-base FETCH_HEAD HEAD)"
  changed="$(git diff --name-status "$base" HEAD)"
  # This step's own file already on main: someone proved it first, and the agent did nothing wrong.
  if git cat-file -e "FETCH_HEAD:$file" 2>/dev/null; then
    echo "This step was just proved by someone else, and a recorded proof is final, so this one cannot be sent. You did nothing wrong. Ask the desk for another step: tools/pnp.sh next" >&2; exit 1
  fi
  if [ "$changed" != "A	$file" ]; then
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
    { curl -sS -m 10 -X POST "$DESK/beat?lease=$lease" 2>/dev/null || true; } | python3 -I -c 'import json,sys,re
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
  sed -n '2,23p' "$0" | sed 's/^# \{0,1\}//'
  ;;
esac
