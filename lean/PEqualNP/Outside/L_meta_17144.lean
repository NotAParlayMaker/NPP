import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17144_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

abbrev S := Bool × Nat × Nat

def gate (s : S) : Gate :=
  ⟨if s.1 then .or else .and, [s.2.1, s.2.2]⟩

def step (w : List Nat) (s : S) : List Nat :=
  let a := w.getD s.2.1 0
  let b := w.getD s.2.2 0
  w ++ [if s.1 then a ||| b else a &&& b]

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem retrieve (w : List Nat) (i j : Nat) :
    (w.map (fun n => n.testBit j)).getD i false = (w.getD i 0).testBit j := by
  simpa using (List.getD_map (l := w) (n := i) (d := 0) (fun n : Nat => n.testBit j))

theorem step_commutes (w : List Nat) (s : S) (j : Nat) :
    (step w s).map (fun n => n.testBit j) =
    boolStep (w.map (fun n => n.testBit j)) (gate s) := by
  rcases s with ⟨b,a,c⟩
  cases b <;> simp [step, boolStep, gate, GateOp.eval, Nat.testBit_or, Nat.testBit_and]
    <;> cases ha : w[a]? <;> cases hc : w[c]? <;> simp [ha, hc]

theorem run_commutes (ss : List S) (w : List Nat) (j : Nat) :
    (ss.foldl step w).map (fun n => n.testBit j) =
    (ss.map gate).foldl boolStep (w.map (fun n => n.testBit j)) := by
  induction ss generalizing w with
  | nil => rfl
  | cons s rest ih => simp only [List.map_cons, List.foldl_cons, ih, step_commutes]

def stride : Nat := 0x100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001000000010000000100000001

def start : List Nat :=
  (List.ofFn fun i : Fin 32 => (2 ^ 32 - 1 : Nat) <<< (32 * i.val)) ++
  (List.ofFn fun i : Fin 32 => stride <<< i.val)

set_option maxRecDepth 100000 in
theorem stride_bit : ∀ k : Fin 1024, stride.testBit k.val = decide (k.val % 32 = 0) := by
  decide +kernel

theorem row_bit (i u v : Fin 32) :
    ((2 ^ 32 - 1 : Nat) <<< (32 * i.val)).testBit (32 * u.val + v.val) = decide (i = u) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, Fin.ext_iff]
  have hv := v.isLt
  omega

theorem col_bit (i u v : Fin 32) :
    (stride <<< i.val).testBit (32 * u.val + v.val) = decide (i = v) := by
  rw [Nat.testBit_shiftLeft]
  have hu := u.isLt
  have hv := v.isLt
  have hi := i.isLt
  have hb : 32 * u.val + v.val - i.val < 1024 := by omega
  rw [stride_bit ⟨_, hb⟩]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, Fin.ext_iff]
  omega

theorem start_correct (u v : Fin 32) :
    start.map (fun n => n.testBit (32 * u.val + v.val)) = oneEach u v := by
  simp only [start, oneEach, List.map_append, List.map_ofFn, Function.comp_def, row_bit, col_bit]

theorem eval_at (ss : List S) (idx : Nat) (u v : Fin 32) :
    (Circuit.mk (ss.map gate) idx).eval (oneEach u v) =
      ((ss.foldl step start).getD idx 0).testBit (32 * u.val + v.val) := by
  change ((ss.map gate).foldl boolStep (oneEach u v)).getD idx false = _
  rw [← start_correct, ← run_commutes, retrieve]
theorem monotone (ss : List S) (idx : Nat) :
    PEqualNP.MetaComplexity.Monotone2 (Circuit.mk (ss.map gate) idx) := by
  intro g hg
  obtain ⟨⟨b,a,c⟩, _, rfl⟩ := List.mem_map.mp hg
  cases b <;> simp [gate]

def ops : List S := [
  (true, 0, 19),
  (true, 6, 10),
  (true, 24, 65),
  (true, 64, 66),
  (true, 8, 13),
  (true, 1, 68),
  (true, 4, 14),
  (true, 69, 70),
  (true, 67, 71),
  (false, 32, 72),
  (true, 9, 15),
  (true, 3, 4),
  (true, 26, 75),
  (true, 74, 76),
  (true, 28, 77),
  (true, 2, 11),
  (true, 0, 23),
  (true, 25, 80),
  (true, 7, 22),
  (true, 10, 82),
  (true, 81, 83),
  (true, 79, 84),
  (true, 78, 85),
  (false, 33, 86),
  (true, 73, 87),
  (true, 21, 25),
  (true, 1, 89),
  (true, 14, 90),
  (true, 28, 91),
  (true, 22, 26),
  (true, 16, 68),
  (true, 93, 94),
  (true, 6, 15),
  (true, 95, 96),
  (true, 92, 97),
  (false, 34, 98),
  (true, 24, 28),
  (true, 27, 100),
  (true, 90, 101),
  (true, 11, 30),
  (true, 17, 103),
  (true, 77, 104),
  (true, 102, 105),
  (false, 35, 106),
  (true, 99, 107),
  (true, 88, 108),
  (true, 12, 103),
  (true, 5, 20),
  (true, 111, 101),
  (true, 110, 112),
  (true, 91, 113),
  (true, 17, 31),
  (true, 64, 115),
  (true, 13, 116),
  (true, 9, 76),
  (true, 117, 118),
  (true, 114, 119),
  (false, 36, 120),
  (true, 0, 16),
  (true, 14, 76),
  (true, 122, 123),
  (true, 8, 66),
  (true, 21, 27),
  (true, 125, 126),
  (true, 124, 127),
  (false, 37, 128),
  (true, 121, 129),
  (true, 18, 27),
  (true, 2, 117),
  (true, 131, 132),
  (false, 38, 133),
  (true, 2, 68),
  (true, 23, 135),
  (true, 4, 136),
  (true, 90, 137),
  (true, 10, 138),
  (true, 16, 112),
  (true, 29, 140),
  (true, 93, 141),
  (true, 139, 142),
  (false, 39, 143),
  (true, 134, 144),
  (true, 130, 145),
  (true, 109, 146),
  (true, 18, 65),
  (true, 74, 148),
  (true, 14, 89),
  (true, 149, 150),
  (true, 151, 67),
  (false, 40, 152),
  (true, 18, 29),
  (true, 9, 154),
  (true, 100, 155),
  (true, 4, 10),
  (true, 156, 157),
  (true, 13, 19),
  (true, 111, 91),
  (true, 159, 160),
  (true, 158, 161),
  (false, 41, 162),
  (true, 153, 163),
  (true, 156, 104),
  (true, 6, 150),
  (true, 122, 82),
  (true, 166, 167),
  (true, 165, 168),
  (false, 42, 169),
  (true, 103, 135),
  (true, 100, 149),
  (true, 1, 172),
  (true, 3, 29),
  (true, 173, 174),
  (true, 171, 175),
  (false, 43, 176),
  (true, 170, 177),
  (true, 164, 178),
  (true, 89, 65),
  (true, 116, 82),
  (true, 180, 181),
  (false, 44, 182),
  (true, 8, 111),
  (true, 64, 184),
  (true, 12, 25),
  (true, 173, 186),
  (true, 185, 187),
  (false, 45, 188),
  (true, 183, 189),
  (true, 74, 64),
  (true, 2, 3),
  (true, 180, 192),
  (true, 191, 193),
  (false, 46, 194),
  (true, 89, 110),
  (true, 101, 196),
  (true, 26, 148),
  (true, 137, 198),
  (true, 197, 199),
  (false, 47, 200),
  (true, 195, 201),
  (true, 190, 202),
  (true, 179, 203),
  (true, 147, 204),
  (true, 15, 24),
  (true, 131, 139),
  (true, 206, 207),
  (false, 48, 208),
  (true, 2, 155),
  (false, 49, 210),
  (true, 209, 211),
  (true, 20, 154),
  (true, 13, 15),
  (true, 84, 214),
  (true, 213, 215),
  (false, 50, 216),
  (true, 9, 184),
  (true, 90, 122),
  (true, 28, 75),
  (true, 219, 220),
  (true, 218, 221),
  (false, 51, 222),
  (true, 217, 223),
  (true, 212, 224),
  (true, 196, 77),
  (true, 16, 116),
  (true, 125, 227),
  (true, 226, 228),
  (false, 52, 229),
  (true, 116, 95),
  (true, 70, 231),
  (false, 53, 232),
  (true, 230, 233),
  (true, 31, 149),
  (true, 196, 235),
  (true, 27, 135),
  (true, 220, 237),
  (true, 236, 238),
  (false, 54, 239),
  (true, 116, 141),
  (true, 166, 241),
  (false, 55, 242),
  (true, 240, 243),
  (true, 234, 244),
  (true, 225, 245),
  (true, 1, 76),
  (false, 56, 247),
  (true, 4, 28),
  (true, 29, 122),
  (true, 74, 250),
  (true, 249, 251),
  (false, 57, 252),
  (true, 248, 253),
  (true, 149, 79),
  (true, 23, 26),
  (true, 174, 256),
  (true, 255, 257),
  (false, 58, 258),
  (true, 15, 75),
  (true, 140, 69),
  (true, 260, 261),
  (false, 59, 262),
  (true, 259, 263),
  (true, 254, 264),
  (true, 81, 235),
  (true, 1, 12),
  (true, 123, 267),
  (true, 266, 268),
  (false, 60, 269),
  (true, 68, 148),
  (true, 113, 250),
  (true, 271, 272),
  (false, 61, 273),
  (true, 270, 274),
  (true, 136, 93),
  (true, 172, 219),
  (true, 276, 277),
  (false, 62, 278),
  (true, 0, 111),
  (true, 210, 280),
  (false, 63, 281),
  (true, 279, 282),
  (true, 275, 283),
  (true, 265, 284),
  (true, 246, 285),
  (true, 205, 286)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem table_checked : (ops.foldl step start).getD 287 0 = 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 := by
  decide +kernel

end PEqualNP.Outside.L_meta_17144_aux

open PEqualNP.Outside.L_meta_17144_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_17144 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 32 => Nat.testBit 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 (32 * u.val + v.val)) 224 := by
  refine ⟨⟨ops.map gate, 287⟩, monotone ops 287, ?_, ?_⟩
  · change (ops.map gate).length ≤ 224
    rw [List.length_map]
    decide
  · intro u v
    rw [eval_at, table_checked]
