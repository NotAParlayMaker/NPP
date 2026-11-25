import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17145.Work

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

abbrev Op := Nat × Nat × Nat

def gate (o : Op) : Gate :=
  if o.1 = 0 then ⟨.and, [o.2.1, o.2.2]⟩
  else if o.1 = 1 then ⟨.or, [o.2.1, o.2.2]⟩
  else ⟨.not, [o.2.1]⟩

def packed (mask : Nat) (a : List Nat) (o : Op) : List Nat :=
  let x := a.getD o.2.1 0
  let y := a.getD o.2.2 0
  a ++ [if o.1 = 0 then x &&& y else if o.1 = 1 then x ||| y else mask ^^^ x]

theorem optRead (k : Nat) (o : Option Nat) :
    (o.map (fun n => n.testBit k)).getD false = (o.getD 0).testBit k := by
  cases o <;> simp

theorem packedRead (xs : List Nat) (k i : Nat) :
    (xs.map (fun a => a.testBit k)).getD i false = (xs.getD i 0).testBit k := by
  simp [List.getD, optRead]

theorem packedCorrect (mask k : Nat) (hm : mask.testBit k = true)
    (os : List Op) (a : List Nat) :
    ((os.foldl (packed mask) a).map (fun n => n.testBit k)) =
    (os.map gate).foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (a.map (fun n => n.testBit k)) := by
  induction os generalizing a with
  | nil => rfl
  | cons o os ih =>
    simp only [List.foldl_cons,List.map_cons]
    rw [ih]
    congr 1
    by_cases h : o.1 = 0
    · simp [packed, gate, h, GateOp.eval, optRead, Nat.testBit_and]
    · by_cases j : o.1 = 1
      · simp [packed, gate, h, j, GateOp.eval, optRead, Nat.testBit_or]
      · simp [packed, gate, h, j, GateOp.eval, optRead, Nat.testBit_xor, hm]

def operations : List Op := [
  (2, 0, 0),
  (2, 1, 1),
  (0, 10, 11),
  (0, 0, 11),
  (0, 1, 10),
  (0, 0, 1),
  (2, 2, 2),
  (2, 3, 3),
  (2, 4, 4),
  (0, 17, 18),
  (0, 3, 18),
  (0, 4, 17),
  (0, 3, 4),
  (0, 16, 19),
  (0, 2, 19),
  (0, 16, 20),
  (0, 2, 20),
  (0, 16, 21),
  (0, 2, 21),
  (0, 16, 22),
  (0, 2, 22),
  (2, 5, 5),
  (2, 6, 6),
  (0, 31, 32),
  (0, 5, 32),
  (0, 6, 31),
  (0, 5, 6),
  (2, 7, 7),
  (2, 8, 8),
  (2, 9, 9),
  (0, 38, 39),
  (0, 8, 39),
  (0, 9, 38),
  (0, 8, 9),
  (0, 37, 40),
  (0, 7, 40),
  (0, 37, 41),
  (0, 7, 41),
  (0, 37, 42),
  (0, 7, 42),
  (0, 37, 43),
  (0, 7, 43),
  (0, 33, 44),
  (0, 34, 44),
  (0, 35, 44),
  (0, 36, 44),
  (0, 33, 45),
  (0, 34, 45),
  (0, 35, 45),
  (0, 36, 45),
  (0, 33, 46),
  (0, 34, 46),
  (0, 35, 46),
  (0, 36, 46),
  (0, 33, 47),
  (0, 34, 47),
  (0, 35, 47),
  (0, 36, 47),
  (0, 33, 48),
  (0, 34, 48),
  (0, 35, 48),
  (0, 36, 48),
  (0, 33, 49),
  (0, 34, 49),
  (0, 35, 49),
  (0, 36, 49),
  (0, 33, 50),
  (0, 34, 50),
  (0, 35, 50),
  (0, 36, 50),
  (0, 33, 51),
  (0, 34, 51),
  (0, 35, 51),
  (0, 36, 51),
  (1, 67, 74),
  (1, 56, 72),
  (1, 59, 82),
  (1, 61, 65),
  (1, 81, 84),
  (1, 55, 85),
  (1, 62, 75),
  (1, 63, 78),
  (1, 54, 86),
  (1, 53, 80),
  (1, 60, 66),
  (1, 71, 79),
  (1, 52, 57),
  (1, 64, 94),
  (1, 68, 70),
  (1, 73, 92),
  (1, 89, 93),
  (1, 69, 83),
  (1, 77, 90),
  (1, 56, 87),
  (1, 63, 88),
  (1, 91, 101),
  (1, 95, 103),
  (1, 58, 73),
  (1, 59, 75),
  (1, 72, 96),
  (1, 90, 97),
  (1, 53, 62),
  (1, 93, 98),
  (1, 81, 102),
  (1, 80, 88),
  (1, 76, 100),
  (1, 85, 107),
  (1, 68, 84),
  (1, 65, 82),
  (1, 70, 113),
  (1, 59, 61),
  (1, 90, 96),
  (1, 56, 79),
  (1, 92, 110),
  (1, 71, 123),
  (1, 58, 122),
  (1, 91, 112),
  (1, 97, 116),
  (1, 86, 87),
  (1, 62, 82),
  (1, 54, 118),
  (1, 87, 100),
  (1, 81, 106),
  (1, 57, 99),
  (1, 55, 106),
  (1, 108, 132),
  (1, 67, 78),
  (1, 74, 77),
  (1, 95, 115),
  (1, 83, 135),
  (1, 58, 105),
  (1, 60, 121),
  (1, 63, 68),
  (1, 92, 134),
  (1, 70, 111),
  (1, 94, 137),
  (1, 99, 104),
  (1, 64, 144),
  (1, 71, 83),
  (1, 93, 96),
  (1, 118, 119),
  (1, 148, 149),
  (1, 127, 150),
  (1, 151, 152),
  (0, 12, 153),
  (1, 52, 76),
  (1, 80, 142),
  (1, 155, 156),
  (1, 143, 157),
  (0, 13, 158),
  (1, 53, 66),
  (1, 86, 117),
  (1, 160, 161),
  (1, 140, 162),
  (0, 14, 163),
  (1, 57, 66),
  (1, 74, 91),
  (1, 165, 166),
  (1, 138, 167),
  (0, 15, 168),
  (1, 154, 159),
  (1, 164, 169),
  (1, 170, 171),
  (0, 23, 172),
  (1, 73, 77),
  (1, 96, 117),
  (1, 120, 138),
  (1, 174, 175),
  (1, 176, 177),
  (0, 12, 178),
  (0, 13, 139),
  (1, 91, 109),
  (1, 110, 114),
  (1, 181, 182),
  (1, 130, 183),
  (0, 14, 184),
  (0, 15, 147),
  (1, 179, 180),
  (1, 185, 186),
  (1, 187, 188),
  (0, 24, 189),
  (1, 65, 68),
  (1, 95, 109),
  (1, 191, 192),
  (1, 146, 193),
  (0, 12, 194),
  (1, 71, 105),
  (1, 129, 131),
  (1, 196, 197),
  (1, 145, 198),
  (0, 13, 199),
  (1, 88, 97),
  (1, 109, 126),
  (1, 201, 202),
  (1, 128, 203),
  (0, 14, 204),
  (1, 88, 89),
  (1, 91, 111),
  (1, 206, 207),
  (0, 15, 208),
  (1, 195, 200),
  (1, 205, 209),
  (1, 210, 211),
  (0, 25, 212),
  (1, 65, 85),
  (1, 114, 214),
  (0, 12, 215),
  (1, 52, 61),
  (1, 98, 125),
  (1, 217, 218),
  (1, 146, 219),
  (0, 13, 220),
  (1, 54, 56),
  (1, 61, 73),
  (1, 80, 141),
  (1, 222, 223),
  (1, 224, 225),
  (0, 14, 226),
  (1, 55, 72),
  (1, 79, 126),
  (1, 130, 145),
  (1, 228, 229),
  (1, 230, 231),
  (0, 15, 232),
  (1, 216, 221),
  (1, 227, 233),
  (1, 234, 235),
  (0, 26, 236),
  (1, 72, 95),
  (1, 113, 133),
  (1, 238, 239),
  (0, 12, 240),
  (1, 64, 89),
  (1, 90, 107),
  (1, 242, 243),
  (0, 13, 244),
  (1, 60, 87),
  (1, 98, 114),
  (1, 129, 140),
  (1, 246, 247),
  (1, 248, 249),
  (0, 14, 250),
  (1, 52, 75),
  (1, 87, 127),
  (1, 252, 253),
  (0, 15, 254),
  (1, 241, 245),
  (1, 251, 255),
  (1, 256, 257),
  (0, 27, 258),
  (1, 70, 139),
  (0, 12, 260),
  (1, 57, 61),
  (1, 89, 117),
  (1, 262, 263),
  (1, 124, 264),
  (0, 13, 265),
  (1, 99, 147),
  (0, 14, 267),
  (1, 86, 112),
  (1, 136, 269),
  (0, 15, 270),
  (1, 261, 266),
  (1, 268, 271),
  (1, 272, 273),
  (0, 28, 274),
  (1, 67, 79),
  (1, 81, 89),
  (1, 128, 141),
  (1, 276, 277),
  (1, 142, 278),
  (1, 279, 280),
  (0, 12, 281),
  (1, 84, 98),
  (1, 124, 131),
  (1, 283, 284),
  (0, 13, 285),
  (1, 115, 133),
  (1, 136, 287),
  (0, 14, 288),
  (1, 55, 57),
  (1, 68, 88),
  (1, 108, 125),
  (1, 290, 291),
  (1, 292, 293),
  (0, 15, 294),
  (1, 282, 286),
  (1, 289, 295),
  (1, 296, 297),
  (0, 29, 298),
  (1, 53, 102),
  (1, 104, 143),
  (1, 300, 301),
  (0, 12, 302),
  (1, 105, 119),
  (1, 120, 304),
  (0, 13, 305),
  (1, 62, 89),
  (1, 104, 307),
  (0, 14, 308),
  (1, 64, 74),
  (1, 75, 80),
  (1, 310, 311),
  (1, 116, 312),
  (0, 15, 313),
  (1, 303, 306),
  (1, 309, 314),
  (1, 315, 316),
  (0, 30, 317),
  (1, 173, 190),
  (1, 213, 237),
  (1, 259, 275),
  (1, 299, 318),
  (1, 319, 320),
  (1, 321, 322),
  (1, 323, 324)]
def C : Circuit := ⟨operations.map gate, 325⟩
theorem cFanIn : FanInTwo C := by
  intro g hg
  change g ∈ operations.map gate at hg
  obtain ⟨o, _, rfl⟩ := List.mem_map.mp hg
  by_cases h : o.1 = 0
  · simp [gate, h]
  · by_cases j : o.1 = 1 <;> simp [gate, h, j]

def start : List Nat := [
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000]
def mask : Nat := 2 ^ 1024 - 1
def index (x : Fin 10 → Bool) : Nat :=
  let u : Fin (2 ^ 5) := Fin.ofNat _ (tableIndex fun i : Fin 5 => x (Fin.castAdd 5 i))
  let v : Fin (2 ^ 5) := Fin.ofNat _ (tableIndex fun i : Fin 5 => x (Fin.natAdd 5 i))
  2 ^ 5 * u.val + v.val

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inputTable : ∀ x : Fin 10 → Bool,
    start.map (fun n => n.testBit (index x)) = List.ofFn x := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem maskTable : ∀ x : Fin 10 → Bool, mask.testBit (index x) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem outputTable : ((operations.foldl (packed mask) start).getD 325 0) = 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 := by decide +kernel

end PEqualNP.Outside.L_meta_17145.Work

open PEqualNP.Outside.L_meta_17145.Work in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_17145 : PEqualNP.MetaComplexity.HasCircuitSize 10 (PEqualNP.Represents.adjFun (k := 5) (l := 5) (fun u v : Fin (2 ^ 5) => Nat.testBit 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 (32 * u.val + v.val))) 330 := by
  refine ⟨C, cFanIn, by decide +kernel, ?_⟩
  intro x
  have eq := packedCorrect mask (index x) (maskTable x) operations start
  rw [inputTable x] at eq
  change (C.wires (List.ofFn x)).getD 325 false = (0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 : Nat).testBit (index x)
  change ((operations.foldl (packed mask) start).map (fun n => n.testBit (index x))) =
    C.wires (List.ofFn x) at eq
  rw [← eq, packedRead, outputTable]
