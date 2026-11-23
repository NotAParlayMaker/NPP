#!/usr/bin/env python3
# Tests for outside-strip.py (or the file named in STRIP_UNDER_TEST). Every input is a string
# written here; no outside file is read. Run: python3 outside-strip.test.py
import hashlib, importlib.util, os, subprocess, sys, tempfile, unittest
HERE = os.path.dirname(os.path.abspath(__file__))
UNDER = os.environ.get("STRIP_UNDER_TEST", f"{HERE}/outside-strip.py")
spec = importlib.util.spec_from_file_location("strip", UNDER); S = importlib.util.module_from_spec(spec); spec.loader.exec_module(S)

def cli(data):
    d = tempfile.mkdtemp(); i, o = f"{d}/in.lean", f"{d}/out.lean"
    open(i, "wb").write(data)
    r = subprocess.run([sys.executable, "-I", UNDER, i, o], capture_output=True, text=True)
    return r.returncode, (open(o, "rb").read() if os.path.exists(o) else None), r.stdout, r.stderr
def blanks(s): return bytes(32 if c != 10 else 10 for c in s)

class Strip(unittest.TestCase):
    def ok(self, src, want):
        self.assertEqual(S.run(src), want)
        self.assertEqual(len(S.run(src)), len(S.normalize(src)))
    def refused(self, src):
        with self.assertRaises(S.Unsafe): S.run(src)

    def test_line_comment(self):
        self.ok(b"theorem t : True := trivial -- by the author\n", b"theorem t : True := trivial " + b" " * 16 + b"\n")
        self.ok(b"-- first\nx", b"        \nx")
        self.ok(b"x -- at the end, no newline", b"x " + b" " * 25)
    def test_nested_block(self):
        src = b"a /- one /- two -/ still one -/ b"
        self.ok(src, b"a " + blanks(src[2:-2]) + b" b")
        self.ok(b"/- /- /- deep -/ -/ -/x", b" " * 22 + b"x")
    def test_naive_non_nested_stripper_would_leave_text(self):
        src = b"/- a /- b -/ prose -/\ndef x := 1\n"
        out = S.run(src)
        self.assertNotIn(b"prose", out); self.assertNotIn(b"-/", out); self.assertTrue(out.endswith(b"\ndef x := 1\n"))
    def test_doc_and_module_comments(self):
        src = b"/-! module doc\n  spanning -/\n/-- a doc comment -/\ntheorem t : True := trivial\n"
        out = S.run(src)
        self.assertEqual(out.splitlines()[3], b"theorem t : True := trivial")
        self.assertEqual(out.splitlines()[:3], [b" " * 14, b" " * 13, b" " * 20])
    def test_doc_body_starts_after_the_opener(self):
        # Lean reads /--/ as a doc comment still open: the text after it is comment too.
        self.ok(b"/--/ prose -/x", b" " * 13 + b"x")
        self.refused(b"/--/ prose")
    def test_dash_runs_inside_a_block(self):
        self.ok(b"/- a --/x", b" " * 8 + b"x")
        self.ok(b"/- --- -/x", b" " * 9 + b"x")
    def test_dashes_inside_strings_are_kept(self):
        for src in (b'def s := "a -- b"\n', b'def s := "/- not a comment"\n', b'def s := "-/ x /-"\n'):
            with self.subTest(src=src): self.ok(src, src)
    def test_escaped_quotes(self):
        src = b'def s := "say \\"-- hi\\" /- x" -- gone\n'
        self.ok(src, src.replace(b"-- gone", b"       "))
        self.ok(b'def s := "\\\\" -- gone\n', b'def s := "\\\\"        \n')
    def test_char_literals(self):
        self.ok(b"def c := '\"' -- gone\n", b"def c := '\"'        \n")
        self.ok(b"def c := '-' -- gone\n", b"def c := '-'        \n")
        self.ok(b"def c := '\\'' -- gone\n", b"def c := '\\''        \n")
        self.ok(b"theorem h' : x' = y' := rfl -- gone\n", b"theorem h' : x' = y' := rfl        \n")
    def test_quote_after_an_identifier_starts_a_string(self):
        # x'"' is the identifier x' then a string: the -- inside it stays.
        self.ok(b"x'\"' -- in the string\"", b"x'\"' -- in the string\"")
    def test_raw_strings(self):
        self.ok(b'def s := r"\\" -- gone\n', b'def s := r"\\"        \n')
        self.ok(b'def s := r#"a "-- b" c"# -- gone\n', b'def s := r#"a "-- b" c"#        \n')
        self.ok(b'def bar := for"-- kept"\n', b'def bar := for"-- kept"\n')   # identifier then a plain string
    def test_escaped_identifiers(self):
        self.ok('«"» -- gone\n'.encode(), '«"»        \n'.encode())
    def test_crlf_and_lone_cr(self):
        self.ok(b"a -- x\r\nb\rc /- y\r\n -/d", b"a     \nb\nc     \n   d")
    def test_non_ascii_passes_through(self):
        src = "theorem α_β (h : ∀ n, n ≥ 0) : ⊤ := trivial -- ünïcödé\n".encode()
        out = S.run(src)
        self.assertTrue(out.startswith("theorem α_β (h : ∀ n, n ≥ 0) : ⊤ := trivial ".encode()))
        self.assertEqual(len(out), len(src)); self.assertEqual(out[-1:], b"\n")
        self.ok(b"x \xff\xfe /- \xe2\x9c\x93 -/ y", b"x \xff\xfe " + b" " * 9 + b" y")
    def test_unterminated(self):
        for src in (b"/- never closed", b"/- a /- b -/", b"/-", b'def s := "open', b"/--", b"\xc2\xab never closed"):
            with self.subTest(src=src): self.refused(src)
    def test_ambiguous_shapes_are_refused(self):
        for src in (b'def s := s!"{x -- prose\n}"', b'"{"}" -- prose "}"',   # interpolation
                    b"x <-- prose", b"{ x //- prose -/ }", b"a.--b",          # a symbol glued to an opener
                    "→r\"\\\" -- prose \"".encode(), "α'\"' -- prose".encode(),  # raw or char after a symbol
                    b"/-/- a -/ prose -/"):
            with self.subTest(src=src): self.refused(src)
    def test_idempotent(self):
        for src in (b"/- a /- b -/ c -/ d -- e\n", b'"--" -- x\n/-- d -/\ny', "«a» -- é\r\n'\"'".encode()):
            with self.subTest(src=src): once = S.run(src); self.assertEqual(S.run(once), once)
    def test_lines_and_columns_preserved(self):
        src = b"theorem t /- a\nb -/ : True := by\n  -- c\n  trivial -- d\n"
        out = S.run(src)
        self.assertEqual(out.count(b"\n"), src.count(b"\n"))
        for a, z in zip(src.split(b"\n"), out.split(b"\n")):
            self.assertEqual(len(a), len(z))
        self.assertEqual(out.index(b": True"), src.index(b": True")); self.assertEqual(out.index(b"trivial"), src.index(b"trivial"))
    def test_after_check_catches_a_surviving_opener(self):
        # Spaces cannot glue two halves into an opener, so the after-check is defense in depth:
        # prove it fires by giving it output a broken transform would have produced.
        real = S.strip
        S.strip = lambda src: (src, src.count(b"--")) if src.startswith(b"x") else real(src)   # leaves the comment, counts it
        try:
            with self.assertRaises(S.Unsafe): S.run(b"x -- survives")
        finally: S.strip = real
        self.ok(b"a/- x -/-/ b", b"a" + b" " * 7 + b"-/ b")   # the halves left beside a blanked comment never join

class Cli(unittest.TestCase):
    def test_exit_0_prints_the_sha256_of_what_it_wrote(self):
        rc, out, so, _ = cli(b"theorem t : True := trivial -- c\r\n")
        self.assertEqual(rc, 0); self.assertEqual(out, b"theorem t : True := trivial     \n")
        self.assertEqual(so.strip(), hashlib.sha256(out).hexdigest())
    def test_exit_2_writes_nothing_and_quotes_no_text(self):
        rc, out, so, se = cli(b"ok\n/- secret prose never closed")
        self.assertEqual((rc, out, so), (2, None, "")); self.assertIn("line 2", se); self.assertNotIn("secret", se)
    def test_exit_3_over_2_mb(self):
        rc, out, _, _ = cli(b"a" * (2 * 1024 * 1024 + 1)); self.assertEqual((rc, out), (3, None))
        rc, _, _, _ = cli(b"a" * (2 * 1024 * 1024)); self.assertEqual(rc, 0)
    def test_imports_only_sys_and_hashlib(self):
        src = open(UNDER).read()
        imports = [l.strip() for l in src.splitlines() if l.lstrip().startswith(("import ", "from "))]
        self.assertEqual(imports, ["import sys, hashlib"])
        for word in ("eval(", "exec(", "subprocess", "__import__", "compile("): self.assertNotIn(word, src)

if __name__ == "__main__": unittest.main(verbosity=2)
