#!/usr/bin/env python3
# outside-strip.py <in> <out>: the ONE comment stripper for outside Lean proofs, shared by the
# public workflow (which judges the stripped bytes) and the intake (which commits them).
# A pure text transform, never a build: every Lean 4 comment (line `--`, block `/- -/` nested,
# doc `/-- -/`, module doc `/-! -/`) becomes spaces byte for byte, newlines kept, so no token
# moves and the line count is unchanged; `\r\n` and a lone `\r` become `\n` first.
# Exit 0: <out> written, its sha256 (hex) printed. Exit 2: a comment survives, or the text has a
# shape where this lexer and Lean's could disagree about what is a comment (it refuses rather
# than guess; nothing is written). Exit 3: input over 2 MB. Exit 64: usage or unreadable input.
# The refusal names a line number only, never the input's text.
# Mirrors Lean's own whitespace and finishCommentBlock: a block comment's body starts three
# bytes after its `/` (Lean skips the character after `/-`; `/--` and `/-!` bodies start there
# too); inside a block only `/-` and `-/` count, quotes do not.
import sys, hashlib
LIMIT = 2 * 1024 * 1024
IDENT = frozenset(b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'!?")
LETTER = frozenset(b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_")
SPACE = frozenset(b" \n\t")
START = SPACE | frozenset(b"()[]{},;")       # a token surely starts after one of these
OPENER_OK = START | IDENT | frozenset(b'"')   # no Lean token glues to a comment opener after these
OPEN_ID, CLOSE_ID = b"\xc2\xab", b"\xc2\xbb"   # the escaped identifier quotes << >>

class Unsafe(Exception): pass

def normalize(data): return data.replace(b"\r\n", b"\n").replace(b"\r", b"\n")

def strip(src):
    """(stripped bytes, number of comments removed); raises Unsafe."""
    b = bytearray(src); n = len(b); i = 0; found = 0
    line = lambda at: src.count(b"\n", 0, at) + 1
    def bad(why, at): raise Unsafe(f"line {line(at)}: {why}")
    def blank(a, z):
        for j in range(a, z):
            if b[j] != 10: b[j] = 32
    def kind(i):
        # "start": a new token begins at i; "ident": i continues an identifier; else "ambiguous".
        if i == 0 or b[i - 1] in START: return "start"
        j = i
        while j > 0 and b[j - 1] in IDENT: j -= 1
        if j < i and b[j] in LETTER and not (j > 0 and b[j - 1] == 0x2E): return "ident"
        return "ambiguous"
    def charlit(i):
        # Lean's char literal at i: ' (one UTF-8 char | \\ \" \' \n \t \r | \xHH | \uHHHH) '
        j = i + 1
        if j >= n: return None
        if b[j] == 0x5C:
            e = b[j + 1] if j + 1 < n else -1
            hexes = {0x78: 2, 0x75: 4}.get(e)
            if hexes:
                if not all(c in b"0123456789abcdefABCDEF" for c in b[j + 2:j + 2 + hexes]) or j + 2 + hexes > n: return None
                j += 2 + hexes
            elif e in b"\\\"'ntr": j += 2
            else: return None
        else:
            c = b[j]; j += 1 if c < 0xC0 else 2 if c < 0xE0 else 3 if c < 0xF0 else 4
        return j + 1 if j < n and b[j] == 0x27 else None
    while i < n:
        c = b[i]; nx = b[i + 1] if i + 1 < n else -1
        if (c == 0x2D or c == 0x2F) and nx == 0x2D:   # -- or /-
            if i > 0 and b[i - 1] not in OPENER_OK: bad("a comment opener glued to a symbol", i)
            found += 1
            if c == 0x2D:
                z = b.find(b"\n", i); z = n if z < 0 else z
                blank(i, z); i = z; continue
            if i + 2 >= n: bad("an unterminated block comment", i)
            if b[i + 2] == 0x2F and i + 3 < n and b[i + 3] == 0x2D: bad("a block comment opening /-/-", i)
            j, depth = i + 3, 1
            while depth:
                if j >= n: bad("an unterminated block comment", i)
                if b[j] == 0x2D and j + 1 < n and b[j + 1] == 0x2F: depth -= 1; j += 2
                elif b[j] == 0x2F and j + 1 < n and b[j + 1] == 0x2D: depth += 1; j += 2
                else: j += 1
            blank(i, j); i = j; continue
        if c == 0x22:   # a string literal
            j = i + 1
            while True:
                if j >= n: bad("an unterminated string", i)
                if b[j] == 0x5C: j += 2; continue
                if b[j] == 0x7B: bad("a brace inside a string (it may interpolate code)", i)
                if b[j] == 0x22: break
                j += 1
            i = j + 1; continue
        if c == 0x72:   # r"..." or r#"..."#: a raw string, if a token starts here
            h = i + 1
            while h < n and b[h] == 0x23: h += 1
            if h < n and b[h] == 0x22:
                k = kind(i)
                if k == "ambiguous": bad("a raw string after a symbol", i)
                if k == "start":
                    end = b.find(b'"' + b"#" * (h - i - 1), h + 1)
                    if end < 0: bad("an unterminated raw string", i)
                    i = end + 1 + (h - i - 1); continue
            i += 1; continue
        if c == 0x27:   # a char literal, if a token starts here
            end = charlit(i)
            if end is not None:
                k = kind(i)
                if k == "start": i = end; continue
                if k == "ambiguous":
                    if 0x22 in b[i + 1:end - 1] or 0x5C in b[i + 1:end - 1]: bad("a char literal after a symbol", i)
                    i = end; continue
            i += 1; continue
        if b[i:i + 2] == OPEN_ID:
            z = b.find(CLOSE_ID, i + 2)
            if z < 0: bad("an unterminated escaped identifier", i)
            i = z + 2; continue
        i += 1
    return bytes(b), found

def run(data):
    """The whole transform with its after-check; raises Unsafe."""
    out, _ = strip(normalize(data))
    again, found = strip(out)
    if found or again != out: raise Unsafe("a comment survived stripping")
    return out

def main(argv):
    if len(argv) != 3: print("usage: outside-strip.py <in> <out>", file=sys.stderr); return 64
    try:
        with open(argv[1], "rb") as f: data = f.read(LIMIT + 1)
    except OSError as e: print(f"cannot read the input: {e.strerror}", file=sys.stderr); return 64
    if len(data) > LIMIT: print("REFUSED: the input is larger than 2 MB", file=sys.stderr); return 3
    try: out = run(data)
    except Unsafe as e: print(f"REFUSED: {e}", file=sys.stderr); return 2
    with open(argv[2], "wb") as f: f.write(out)
    print(hashlib.sha256(out).hexdigest()); return 0

if __name__ == "__main__": sys.exit(main(sys.argv))
