import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17144

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev Instr := Bool × Nat × Nat

def makeGate (g : Instr) : Gate := ⟨if g.1 then .or else .and, [g.2.1,g.2.2]⟩

def step (w : List Nat) (g : Instr) : List Nat :=
  w ++ [if g.1 then w.getD g.2.1 0 ||| w.getD g.2.2 0 else w.getD g.2.1 0 &&& w.getD g.2.2 0]

theorem readBit (w : List Nat) (i j : Nat) :
    (w.map (fun z => z.testBit j)).getD i false = (w.getD i 0).testBit j := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> simp

theorem runBits (gs : List Instr) (w : List Nat) (j o : Nat) :
    (Circuit.mk (gs.map makeGate) o).eval (w.map fun z => z.testBit j) =
      ((gs.foldl step w).getD o 0).testBit j := by
  induction gs generalizing w with
  | nil => exact readBit w o j
  | cons g gs ih =>
    change (Circuit.mk (gs.map makeGate) o).eval (_ ++ [_]) = _
    rw [List.foldl_cons, ← ih]
    congr 1
    rcases g with ⟨b,a,d⟩
    cases b <;> simp [makeGate, step, GateOp.eval, Nat.testBit_and, Nat.testBit_or] <;>
      cases w[a]? <;> cases w[d]? <;> simp

def first (i : Fin 32) : Nat := 4294967295 <<< (32*i.val)
def columnZero : Nat := ((2 : Nat)^1024 - 1) / 4294967295
def second (i : Fin 32) : Nat := columnZero <<< i.val
def start : List Nat := List.ofFn first ++ List.ofFn second

theorem firstBit (i u v : Fin 32) : (first i).testBit (32*u.val + v.val) = decide (i = u) := by
  have masks : ∀ i u : Fin 32, ((first i >>> (32*u.val)) % 2^32) =
      (if i = u then 2^32 - 1 else 0) := by decide +kernel
  have eq := congrArg (fun t : Nat => t.testBit v.val) (masks i u)
  change (((first i >>> (32*u.val)) % 2^32).testBit v.val) =
    (if i = u then 2^32-1 else 0).testBit v.val at eq
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight] at eq
  by_cases hi : i = u
  · rw [ite_eq_left hi, Nat.testBit_two_pow_sub_one] at eq
    simpa only [decide_eq_true v.isLt, Bool.true_and, decide_eq_true hi] using eq
  · rw [ite_eq_right hi] at eq
    simpa only [decide_eq_true v.isLt, Bool.true_and, decide_eq_false hi, Nat.zero_testBit] using eq
theorem secondBit (i u v : Fin 32) : (second i).testBit (32*u.val+v.val) = decide (i=v) := by
  have masks : ∀ i u : Fin 32, ((second i >>> (32*u.val)) % 2^32) = 2^i.val := by decide +kernel
  have eq := congrArg (fun t : Nat => t.testBit v.val) (masks i u)
  change (((second i >>> (32*u.val))%2^32).testBit v.val) = (2^i.val : Nat).testBit v.val at eq
  rw [Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,Nat.testBit_two_pow] at eq
  simpa only [decide_eq_true v.isLt,Bool.true_and,Fin.ext_iff] using eq
theorem starts (u v : Fin 32) : (start.map fun z => z.testBit (32*u.val+v.val)) = oneEach u v := by
  unfold start oneEach
  rw [List.map_append, List.map_ofFn, List.map_ofFn]
  congr 1
  · congr 1; funext i; exact firstBit i u v
  · congr 1; funext i; exact secondBit i u v

theorem mono (gs : List Instr) (o : Nat) : Monotone2 ⟨gs.map makeGate, o⟩ := by
  intro g hg
  obtain ⟨⟨b,a,d⟩,_,rfl⟩ := List.mem_map.mp hg
  cases b <;> simp [makeGate]


def prog : List Instr := [(true, 25, 21),
  (true, 10, 6),
  (true, 28, 24),
  (true, 15, 9),
  (true, 13, 8),
  (true, 19, 0),
  (true, 4, 3),
  (true, 20, 5),
  (true, 65, 18),
  (true, 66, 64),
  (true, 30, 11),
  (true, 70, 26),
  (true, 69, 17),
  (true, 72, 67),
  (true, 68, 1),
  (true, 23, 2),
  (true, 76, 31),
  (true, 16, 0),
  (true, 29, 18),
  (true, 74, 27),
  (true, 82, 9),
  (true, 73, 14),
  (true, 79, 26),
  (true, 22, 7),
  (true, 83, 12),
  (true, 71, 1),
  (true, 71, 16),
  (true, 90, 27),
  (true, 86, 73),
  (true, 65, 64),
  (true, 75, 1),
  (true, 24, 14),
  (true, 88, 68),
  (true, 25, 0),
  (true, 78, 15),
  (true, 10, 4),
  (true, 64, 28),
  (true, 26, 22),
  (true, 97, 10),
  (true, 89, 9),
  (true, 77, 31),
  (true, 95, 65),
  (true, 101, 14),
  (true, 96, 72),
  (true, 92, 22),
  (true, 108, 78),
  (true, 85, 13),
  (true, 12, 8),
  (true, 106, 16),
  (true, 67, 28),
  (true, 102, 87),
  (true, 85, 6),
  (true, 27, 18),
  (true, 91, 29),
  (true, 77, 69),
  (true, 81, 8),
  (true, 93, 67),
  (true, 80, 75),
  (true, 3, 2),
  (true, 84, 2),
  (true, 81, 29),
  (true, 77, 29),
  (true, 100, 70),
  (true, 35, 56),
  (true, 127, 60),
  (false, 94, 128),
  (true, 49, 63),
  (false, 123, 130),
  (true, 4, 69),
  (true, 78, 105),
  (true, 132, 133),
  (false, 32, 134),
  (true, 11, 75),
  (true, 79, 113),
  (true, 136, 137),
  (true, 138, 114),
  (false, 33, 139),
  (true, 6, 98),
  (true, 100, 112),
  (true, 141, 142),
  (false, 34, 143),
  (true, 17, 67),
  (true, 73, 83),
  (true, 145, 146),
  (false, 35, 147),
  (true, 88, 103),
  (true, 110, 121),
  (true, 149, 150),
  (false, 36, 151),
  (true, 21, 27),
  (true, 75, 105),
  (true, 153, 154),
  (true, 155, 119),
  (false, 37, 156),
  (true, 2, 13),
  (true, 80, 116),
  (true, 158, 159),
  (false, 38, 160),
  (true, 99, 109),
  (true, 162, 117),
  (false, 39, 163),
  (true, 64, 95),
  (true, 165, 118),
  (false, 40, 166),
  (true, 19, 84),
  (true, 89, 99),
  (true, 168, 169),
  (true, 170, 110),
  (false, 41, 171),
  (true, 17, 74),
  (true, 81, 84),
  (true, 87, 115),
  (true, 173, 174),
  (true, 176, 175),
  (false, 42, 177),
  (true, 66, 74),
  (true, 78, 122),
  (true, 179, 180),
  (true, 181, 125),
  (false, 43, 182),
  (true, 80, 87),
  (true, 184, 93),
  (false, 44, 185),
  (true, 25, 66),
  (true, 89, 111),
  (true, 187, 188),
  (true, 189, 118),
  (false, 45, 190),
  (true, 69, 120),
  (true, 192, 122),
  (false, 46, 193),
  (true, 4, 92),
  (true, 195, 107),
  (false, 47, 196),
  (true, 24, 64),
  (true, 79, 98),
  (true, 99, 116),
  (true, 198, 199),
  (true, 201, 200),
  (false, 48, 202),
  (true, 13, 15),
  (true, 20, 23),
  (true, 82, 114),
  (true, 204, 205),
  (true, 207, 206),
  (false, 50, 208),
  (true, 103, 119),
  (true, 210, 126),
  (false, 51, 211),
  (true, 16, 24),
  (true, 74, 111),
  (true, 120, 121),
  (true, 213, 214),
  (true, 216, 215),
  (false, 52, 217),
  (true, 4, 68),
  (true, 80, 112),
  (true, 219, 220),
  (false, 53, 221),
  (true, 2, 96),
  (true, 104, 126),
  (true, 223, 224),
  (false, 54, 225),
  (true, 80, 115),
  (true, 227, 117),
  (false, 55, 228),
  (true, 4, 113),
  (true, 230, 124),
  (false, 57, 231),
  (true, 3, 11),
  (true, 86, 125),
  (true, 233, 234),
  (false, 58, 235),
  (true, 66, 70),
  (true, 91, 98),
  (true, 237, 238),
  (false, 59, 239),
  (true, 12, 14),
  (true, 23, 97),
  (true, 241, 242),
  (true, 243, 104),
  (false, 60, 244),
  (true, 66, 71),
  (true, 107, 124),
  (true, 246, 247),
  (false, 61, 248),
  (true, 77, 81),
  (true, 250, 109),
  (false, 62, 251),
  (true, 0, 71),
  (false, 63, 253),
  (true, 129, 131),
  (true, 135, 140),
  (true, 144, 148),
  (true, 152, 157),
  (true, 161, 164),
  (true, 167, 172),
  (true, 178, 183),
  (true, 186, 191),
  (true, 194, 197),
  (true, 203, 209),
  (true, 212, 218),
  (true, 222, 226),
  (true, 229, 232),
  (true, 236, 240),
  (true, 245, 249),
  (true, 252, 254),
  (true, 255, 256),
  (true, 257, 258),
  (true, 259, 260),
  (true, 261, 262),
  (true, 263, 264),
  (true, 265, 266),
  (true, 267, 268),
  (true, 269, 270),
  (true, 271, 272),
  (true, 273, 274),
  (true, 275, 276),
  (true, 277, 278),
  (true, 279, 280),
  (true, 281, 282),
  (true, 283, 284)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert : (prog.foldl step start).getD 285 0 = 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 := by
  decide +kernel

end PEqualNP.Outside.L_meta_17144

open PEqualNP.Outside.L_meta_17144 in
theorem PEqualNP.Outside.L_meta_17144 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 32 => Nat.testBit 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 (32 * u.val + v.val)) 224) := by
  refine ⟨⟨prog.map makeGate,285⟩, mono _ _, by decide +kernel, ?_⟩
  intro u v
  rw [← starts, runBits, cert]

