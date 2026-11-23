// node --test .github/scripts/outside-guard.test.mjs
// The plain-file rule of outside-guard.mjs: one fixture per way a proof file could carry code
// that runs while it compiles (or hide it from a reader), and the honest shapes that must pass.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { checkImports } from './outside-guard.mjs';

const head = 'import Mathlib\nimport PEqualNP.Defs\n\n';
const run = (body) => checkImports(new TextEncoder().encode(head + body), ['PEqualNP.Defs']);
const refused = (name, body, word) => test(`refused: ${name}`, () => {
  assert.throws(() => run(body), (e) => e.message.includes(word), 'not refused, or for another reason');
});
const passes = (name, body) => test(`passes: ${name}`, () => { assert.deepEqual(run(body), ['Mathlib', 'PEqualNP.Defs']); });
const thm = 'theorem PEqualNP.Outside.L_x_1 : True := trivial\n';
const by = (tac) => `theorem PEqualNP.Outside.L_x_1 : True := by\n  ${tac}\n`;

refused('an initialize', `initialize pure ()\n${thm}`, 'initialize');
refused('an indented initialize', `${thm}  initialize pure ()\n`, 'initialize');
refused('run_cmd, indented', `${thm} run_cmd pure ()\n`, 'run_cmd');
refused('#eval', `${thm} #eval 1\n`, '#');
refused('a tactic that runs code', by('run_tac (do return ())'), 'run_tac');
refused('an elaborator, indented', `${thm} elab x : term => pure default\n`, 'elab');
refused('a macro, indented', `${thm} macro x : tactic => y\n`, 'macro');
refused('notation3', `${thm} notation3 x => y\n`, 'notation');
refused('an attribute command', `${thm} attribute [simp] Nat.add_comm\n`, 'attribute');
refused('a generating attribute', `@[to_additive] theorem foo : True := trivial\n${thm}`, '@[');
refused('an option that is not a limit', `set_option debug.skipKernelTC true in\n${thm}`, 'set_option');
refused('an indented option that is not a limit', by('set_option debug.skipKernelTC true in\n  trivial'), 'set_option');
refused('a same-line option that is not a limit', `set_option maxHeartbeats 1 in set_option debug.skipKernelTC true in\n${thm}`, 'set_option');
refused('an axiom', `${thm} axiom a : False\n`, 'axiom');
refused('sorry', by('sorry'), 'sorry');
refused('sorryAx', 'theorem PEqualNP.Outside.L_x_1 : False := sorryAx _\n', 'sorry');
refused('lcProof', 'theorem PEqualNP.Outside.L_x_1 : False := lcProof\n', 'lcProof');
refused('native_decide', by('native_decide'), 'native');
refused('decide +native', by('decide +native'), 'native');
refused('bv_decide', by('bv_decide'), 'bv_decide');
refused('a simproc', `${thm}  simproc foo (x) := y\n`, 'simproc');
refused('open Lean', `open Lean in\n${thm}`, 'Lean');
refused('ofReduceBool', by('exact ofReduceBool x true rfl'), 'ofReduce');
refused('_root_', by('exact _root_.id trivial'), '_root_');
refused('include_str', by('exact include_str x'), 'include_str');
refused('polyrith', by('polyrith'), 'polyrith');
refused('a string literal', `private def s : String := "x"\n${thm}`, '"');
refused('a character-literal trick', `${thm}  -- '"'\n`, '"');
refused('a quoted identifier', `private def «a» : Nat := 1\n${thm}`, '«');
refused('code hidden behind a comment trick', `-- a note /- here\n  initialize pure ()\n-- done -/\n${thm}`, 'initialize');
refused('a command after a comment on one line', `/- note -/ initialize pure ()\n${thm}`, 'initialize');
refused('a syntax quotation', by('exact \x60(tactic| trivial)'), '(tactic|');
refused('#check', `#check Nat\n${thm}`, '#check');
refused('#print axioms, indented', `${thm}  #print axioms Nat.add_comm\n`, '#print');
refused('a direction-changing character', `-- ‮\n${thm}`, 'invisible');
refused('no theorem at all', 'def x : Nat := 1\n', 'no theorem');

passes('one theorem', thm);
passes('helpers, definitions, namespaces, a docstring', `namespace Gap\nopen Finset\nvariable {n : ℕ}\n/-- A doc comment. -/\nprivate def f (x : ℕ) : ℕ := x\nprivate lemma l : f 1 = 1 := rfl\nend Gap\n\n${thm}`);
passes('a block comment with indented prose', `/-\n  The idea of the proof,\n  in two lines.\n-/\n${thm}`);
passes('the simp attributes', `@[simp] private theorem a : True := trivial\n@[local simp] private theorem b : True := trivial\n${thm}`);
passes('the four limit options', `set_option maxHeartbeats 400000 in\nset_option maxRecDepth 2000 in\n${thm}`);
passes('an indented limit option inside a proof', by('set_option maxRecDepth 2000 in\n  trivial'));
passes('comment prose at column 0 and a heading (form is not judged)', `/-!\n# A heading\n\nProse that starts in column 0,\nover two lines.\n-/\n${thm}`);
passes('a small enumerated type and an instance', `private inductive Stack | input | output\n  deriving DecidableEq\n\nprivate instance : Inhabited Stack := ⟨.input⟩\n${thm}`);
passes('open scoped, and a cardinality written with a hash', `open scoped BigOperators\ntheorem PEqualNP.Outside.L_x_1 (s : Finset ℕ) : #s = #s := rfl\n`);
passes('a pair in backticks inside a doc comment', '/-- The coordinates \x60(a, b, c, d)\x60 of the block. -/\n' + thm);
passes('lemma names that contain add_', by('simp only [Nat.add_comm, add_zero]'));

// The closure rule: which listed modules the base step may build, and which are outside-written
// and built only in the locked step. The base tree is a map here; `read` answers null for a file
// that is not a plain file of the base tree.
import { importClosure, headerImports } from './outside-guard.mjs';
const tree = (files) => (m) => (m in files ? new TextEncoder().encode(files[m]) : null);
const proof = (imports, name = 'PEqualNP.Outside.L_x_2') => `${imports.map((m) => `import ${m}\n`).join('')}\ntheorem ${name} : True := trivial\n`;
const judged = 'PEqualNP.Outside.L_x_1';
const closure = (listed, files) => importClosure(listed, tree(files), judged);
const closureRefused = (name, listed, files, word) => test(`closure refused: ${name}`, () => {
  assert.throws(() => closure(listed, files), (e) => e.message.includes(word), 'not refused, or for another reason');
});

test('closure: base modules only, as before', () => {
  assert.deepEqual(closure(['PEqualNP.Gct.A'], { 'PEqualNP.Gct.A': 'import Mathlib\nimport PEqualNP.Gct.B\n', 'PEqualNP.Gct.B': '-- note\nimport PEqualNP.Defs\n', 'PEqualNP.Defs': 'import Mathlib\n' }),
    { outside: [], base: ['PEqualNP.Defs', 'PEqualNP.Gct.A', 'PEqualNP.Gct.B'] });
});
test('closure: a listed outside module is never handed to the base step; the base modules it imports are', () => {
  const r = closure(['PEqualNP.Outside.L_meta_473'], {
    'PEqualNP.Outside.L_meta_473': proof(['Mathlib', 'PEqualNP.Defs', 'PEqualNP.Outside.L_meta_9'], 'PEqualNP.Outside.L_meta_473'),
    'PEqualNP.Outside.L_meta_9': proof(['Mathlib', 'PEqualNP.Gct.L090'], 'PEqualNP.Outside.L_meta_9'),
    'PEqualNP.Defs': 'import Mathlib\n', 'PEqualNP.Gct.L090': 'import PEqualNP.Defs\n' });
  assert.deepEqual(r, { outside: ['PEqualNP.Outside.L_meta_473', 'PEqualNP.Outside.L_meta_9'], base: ['PEqualNP.Defs', 'PEqualNP.Gct.L090'] });
});
closureRefused('the judged file itself', [judged], {}, 'the file being judged');
closureRefused('an outside module that imports the judged file', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof([judged]) }, 'the file being judged');
closureRefused('a listed module missing from the base', ['PEqualNP.Outside.L_x_9'], {}, 'not a plain file of the base tree');
closureRefused('a listed base module missing from the base', ['PEqualNP.Gct.Nope'], {}, 'not a plain file of the base tree');
closureRefused('a base module that imports an outside module', ['PEqualNP.Gct.A'], { 'PEqualNP.Gct.A': 'import PEqualNP.Gct.B\n', 'PEqualNP.Gct.B': '/- x -/ import PEqualNP.Outside.L_x_2\n', 'PEqualNP.Outside.L_x_2': proof(['Mathlib']) }, 'imports the outside-written');
closureRefused('a base module behind an outside module that imports another outside module', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof(['PEqualNP.Gct.B']), 'PEqualNP.Gct.B': 'import PEqualNP.Outside.L_x_3\n', 'PEqualNP.Outside.L_x_3': proof([]) }, 'imports the outside-written');
closureRefused('an outside module that runs code when it compiles', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': `import Mathlib\ninitialize pure ()\n${thm}` }, 'initialize');
closureRefused('an outside module with an import below its header', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': `import Mathlib\n${thm}/- -/ import PEqualNP.Gct.B\n` }, 'the word "import"');
closureRefused('an outside module importing something not Mathlib and not the project', ['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof(['Lean.Elab']) }, 'not allowed');
closureRefused('a module under Outside that is not a proof file name', ['PEqualNP.Outside.Helper'], { 'PEqualNP.Outside.Helper': proof(['Mathlib']) }, 'not the name of an outside proof file');
test('closure: a cycle between outside modules ends', () => {
  assert.deepEqual(closure(['PEqualNP.Outside.L_x_2'], { 'PEqualNP.Outside.L_x_2': proof(['PEqualNP.Outside.L_x_3']), 'PEqualNP.Outside.L_x_3': proof(['PEqualNP.Outside.L_x_2']) }).outside, ['PEqualNP.Outside.L_x_2', 'PEqualNP.Outside.L_x_3']);
});

test('header: comments, module, modifiers, quoted names', () => {
  assert.deepEqual(headerImports('/- a /- nested -/ b -/\n-- c\nmodule\npublic import «PEqualNP».Outside.L_x_2\nmeta import all Mathlib.Tactic\nimport PEqualNP.Defs -- d\n\ntheorem t : True := trivial\n', 'm'),
    ['PEqualNP.Outside.L_x_2', 'Mathlib.Tactic', 'PEqualNP.Defs']);
});
test('header: an import line below the header is refused, never passed over', () => {
  assert.throws(() => headerImports('import Mathlib\ndef x := 1\nimport PEqualNP.Outside.L_x_2\n', 'm'), /below its header/);
});
