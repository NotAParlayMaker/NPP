import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1701_aux

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 75] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 78] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 93] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [104, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [105, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [106, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [107, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [109, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [111, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [112, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [114, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [115, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [116, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [117, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [119, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [120, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [121, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [122, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [124, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [139, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [140, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [141, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [151, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [157, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [160, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [161, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [162, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [171, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [177, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [180, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [181, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [182, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [184, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 186] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [188, 189] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 190] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [192, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [196, 197] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [200, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [204, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 206] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [208, 209] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 210] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [212, 213] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [216, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [220, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 225] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 226] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 229] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 230] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 233] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 234] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 237] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 238] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 242] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 245] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [187, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [195, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [203, 207] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [211, 215] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [219, 223] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 231] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 239] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 249] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [252, 253] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [256, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 259] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 261] }], output := 262 }

def L : List (ℕ × ℕ) := [(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)]

def inc (a l : Fin 16) : Bool := decide (((a : ℕ), (l : ℕ)) ∈ L)

def X (a b : Fin 16) : Fin 16 → Bool := fun p => decide (p = a) || decide (p = b)

def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

abbrev R : Bool → Bool → Prop := fun p q => p = true → q = true

theorem getD_mono {a b : List Bool} (h : List.Forall₂ R a b) :
    ∀ i, a.getD i false = true → b.getD i false = true := by
  induction h with
  | nil => intro i; simp
  | cons hx _ ih =>
    intro i
    cases i with
    | zero => simpa using hx
    | succ n => simpa using ih n

theorem op_mono (op : GateOp) (hop : isAO op = true) (ins : List ℕ) {a b : List Bool}
    (h : List.Forall₂ R a b) :
    op.eval (ins.map fun i => a.getD i false) = true →
      op.eval (ins.map fun i => b.getD i false) = true := by
  cases op with
  | and =>
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp, id]
    intro h1 v i hi hv
    subst hv
    exact getD_mono h i (h1 _ i hi rfl)
  | or =>
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨v, ⟨i, hi, rfl⟩, hv⟩
    exact ⟨_, ⟨i, hi, rfl⟩, getD_mono h i hv⟩
  | not => simp [isAO] at hop
  | mod m => simp [isAO] at hop
  | maj => simp [isAO] at hop

theorem wires_mono (gs : List Gate) (hao : ∀ g ∈ gs, isAO g.op = true) :
    ∀ a b : List Bool, List.Forall₂ R a b →
      List.Forall₂ R
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b) := by
  induction gs with
  | nil => intro a b h; simpa using h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hao g' (List.mem_cons_of_mem _ hg'))
    exact List.rel_append h
      (List.Forall₂.cons (op_mono g.op (hao g List.mem_cons_self) g.inputs h) List.Forall₂.nil)

theorem eval_mono (C : Circuit) (hao : ∀ g ∈ C.gates, isAO g.op = true) (a b : List Bool)
    (h : List.Forall₂ R a b) : C.eval a = true → C.eval b = true :=
  getD_mono (wires_mono C.gates hao a b h) C.output

theorem ofFn_rel : ∀ (n : ℕ) (u v : Fin n → Bool), (∀ i, u i = true → v i = true) →
    List.Forall₂ R (List.ofFn u) (List.ofFn v) := by
  intro n
  induction n with
  | zero => intro u v _; simp
  | succ n ih =>
    intro u v h
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih _ _ (fun i => h i.succ))

theorem in_mono (x y y' : Fin 16 → Bool) (h : ∀ l, y l = true → y' l = true) :
    List.Forall₂ R (List.ofFn x ++ List.ofFn y) (List.ofFn x ++ List.ofFn y') :=
  List.rel_append (ofFn_rel 16 x x (fun _ hh => hh)) (ofFn_rel 16 y y' h)

theorem hao : ∀ g ∈ C0.gates, isAO g.op = true := by decide +kernel

def force {α : Type} (m : ℕ) (k : ℕ → α) : α :=
  match m with
  | 0 => k 0
  | n + 1 => k (n + 1)

theorem force_eq {α : Type} (m : ℕ) (k : ℕ → α) : force m k = k m := by
  cases m <;> rfl

def mop : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.foldr (fun a b => a &&& b) (2 ^ 17 - 1)
  | GateOp.or, l => l.foldr (fun a b => a ||| b) 0
  | _, _ => 0

def look (rev : List ℕ) (i : ℕ) : ℕ :=
  if i < rev.length then rev.getD (rev.length - 1 - i) 0 else 0

def stepM (rev : List ℕ) (g : Gate) : List ℕ :=
  force (mop g.op (g.inputs.map fun i => look rev i)) fun m => m :: rev

def outMask (ms : List ℕ) : ℕ := look (C0.gates.foldl stepM ms.reverse) C0.output

theorem look_tb (rev : List ℕ) (i j : ℕ) :
    (look rev i).testBit j = ((rev.reverse.map fun m => m.testBit j).getD i false) := by
  unfold look
  split
  · rename_i h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_reverse h]
    cases rev[rev.length - 1 - i]? <;> simp
  · rename_i h
    have h2 : rev.length ≤ i := Nat.le_of_not_lt h
    simp [List.getD_eq_getElem?_getD, h2]

theorem mop_tb (op : GateOp) (hop : isAO op = true) (l : List ℕ) (j : ℕ) (hj : j < 17) :
    (mop op l).testBit j = op.eval (l.map fun m => m.testBit j) := by
  cases op with
  | and =>
    induction l with
    | nil =>
      simp only [mop, GateOp.eval, List.foldr_nil, List.map_nil, List.all_nil]
      interval_cases j <;> decide
    | cons a l ih =>
      simp only [mop, GateOp.eval, List.foldr_cons, Nat.testBit_and, List.map_cons,
        List.all_cons, id] at ih ⊢
      rw [ih]
  | or =>
    induction l with
    | nil => simp [mop, GateOp.eval]
    | cons a l ih =>
      simp only [mop, GateOp.eval, List.foldr_cons, Nat.testBit_or, List.map_cons,
        List.any_cons, id] at ih ⊢
      rw [ih]
  | not => simp [isAO] at hop
  | mod m => simp [isAO] at hop
  | maj => simp [isAO] at hop

theorem sim_fold (j : ℕ) (hj : j < 17) (gs : List Gate) (hao : ∀ g ∈ gs, isAO g.op = true) :
    ∀ (w : List Bool) (rev : List ℕ), w = (rev.reverse.map fun m => m.testBit j) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
        ((gs.foldl stepM rev).reverse.map fun m => m.testBit j) := by
  induction gs with
  | nil => intro w rev h; simpa using h
  | cons g gs ih =>
    intro w rev h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hao g' (List.mem_cons_of_mem _ hg'))
    subst h
    simp only [stepM, force_eq, List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    rw [mop_tb g.op (hao g List.mem_cons_self) _ j hj, List.map_map]
    congr 3
    apply List.map_congr_left
    intro i _
    simp [look_tb]

theorem sim_eval (ms : List ℕ) (j : ℕ) (hj : j < 17) :
    C0.eval (ms.map fun m => m.testBit j) = (outMask ms).testBit j := by
  unfold outMask Circuit.eval Circuit.wires
  rw [look_tb, sim_fold j hj C0.gates hao (ms.map fun m => m.testBit j) ms.reverse (by simp)]

def MS (a b : Fin 16) : List ℕ :=
  List.ofFn (fun p : Fin 16 => if X a b p = true then 2 ^ 17 - 1 else 0) ++
    List.ofFn (fun l : Fin 16 => 2 ^ (l : ℕ) + if (inc a l || inc b l) = true then 0 else 2 ^ 16)

def MS0 : List ℕ := List.replicate 16 0 ++ List.replicate 16 1

theorem chkM0 : (MS0.map fun m => m.testBit 0) =
      List.ofFn (fun _ : Fin 16 => false) ++ List.ofFn (fun _ : Fin 16 => true) ∧
    (outMask MS0).testBit 0 = false := by decide +kernel

theorem chkM_0 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 0 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 0 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 0 b).map fun m => m.testBit 16) =
      List.ofFn (X 0 b) ++ List.ofFn (fun l : Fin 16 => !(inc 0 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 0 l || inc b l) = true → (outMask (MS 0 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 0 b)).testBit 16 = false := by decide +kernel

theorem chkM_1 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 1 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 1 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 1 b).map fun m => m.testBit 16) =
      List.ofFn (X 1 b) ++ List.ofFn (fun l : Fin 16 => !(inc 1 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 1 l || inc b l) = true → (outMask (MS 1 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 1 b)).testBit 16 = false := by decide +kernel

theorem chkM_2 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 2 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 2 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 2 b).map fun m => m.testBit 16) =
      List.ofFn (X 2 b) ++ List.ofFn (fun l : Fin 16 => !(inc 2 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 2 l || inc b l) = true → (outMask (MS 2 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 2 b)).testBit 16 = false := by decide +kernel

theorem chkM_3 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 3 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 3 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 3 b).map fun m => m.testBit 16) =
      List.ofFn (X 3 b) ++ List.ofFn (fun l : Fin 16 => !(inc 3 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 3 l || inc b l) = true → (outMask (MS 3 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 3 b)).testBit 16 = false := by decide +kernel

theorem chkM_4 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 4 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 4 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 4 b).map fun m => m.testBit 16) =
      List.ofFn (X 4 b) ++ List.ofFn (fun l : Fin 16 => !(inc 4 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 4 l || inc b l) = true → (outMask (MS 4 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 4 b)).testBit 16 = false := by decide +kernel

theorem chkM_5 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 5 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 5 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 5 b).map fun m => m.testBit 16) =
      List.ofFn (X 5 b) ++ List.ofFn (fun l : Fin 16 => !(inc 5 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 5 l || inc b l) = true → (outMask (MS 5 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 5 b)).testBit 16 = false := by decide +kernel

theorem chkM_6 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 6 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 6 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 6 b).map fun m => m.testBit 16) =
      List.ofFn (X 6 b) ++ List.ofFn (fun l : Fin 16 => !(inc 6 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 6 l || inc b l) = true → (outMask (MS 6 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 6 b)).testBit 16 = false := by decide +kernel

theorem chkM_7 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 7 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 7 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 7 b).map fun m => m.testBit 16) =
      List.ofFn (X 7 b) ++ List.ofFn (fun l : Fin 16 => !(inc 7 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 7 l || inc b l) = true → (outMask (MS 7 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 7 b)).testBit 16 = false := by decide +kernel

theorem chkM_8 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 8 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 8 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 8 b).map fun m => m.testBit 16) =
      List.ofFn (X 8 b) ++ List.ofFn (fun l : Fin 16 => !(inc 8 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 8 l || inc b l) = true → (outMask (MS 8 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 8 b)).testBit 16 = false := by decide +kernel

theorem chkM_9 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 9 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 9 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 9 b).map fun m => m.testBit 16) =
      List.ofFn (X 9 b) ++ List.ofFn (fun l : Fin 16 => !(inc 9 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 9 l || inc b l) = true → (outMask (MS 9 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 9 b)).testBit 16 = false := by decide +kernel

theorem chkM_10 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 10 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 10 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 10 b).map fun m => m.testBit 16) =
      List.ofFn (X 10 b) ++ List.ofFn (fun l : Fin 16 => !(inc 10 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 10 l || inc b l) = true → (outMask (MS 10 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 10 b)).testBit 16 = false := by decide +kernel

theorem chkM_11 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 11 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 11 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 11 b).map fun m => m.testBit 16) =
      List.ofFn (X 11 b) ++ List.ofFn (fun l : Fin 16 => !(inc 11 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 11 l || inc b l) = true → (outMask (MS 11 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 11 b)).testBit 16 = false := by decide +kernel

theorem chkM_12 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 12 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 12 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 12 b).map fun m => m.testBit 16) =
      List.ofFn (X 12 b) ++ List.ofFn (fun l : Fin 16 => !(inc 12 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 12 l || inc b l) = true → (outMask (MS 12 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 12 b)).testBit 16 = false := by decide +kernel

theorem chkM_13 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 13 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 13 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 13 b).map fun m => m.testBit 16) =
      List.ofFn (X 13 b) ++ List.ofFn (fun l : Fin 16 => !(inc 13 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 13 l || inc b l) = true → (outMask (MS 13 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 13 b)).testBit 16 = false := by decide +kernel

theorem chkM_14 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 14 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 14 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 14 b).map fun m => m.testBit 16) =
      List.ofFn (X 14 b) ++ List.ofFn (fun l : Fin 16 => !(inc 14 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 14 l || inc b l) = true → (outMask (MS 14 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 14 b)).testBit 16 = false := by decide +kernel

theorem chkM_15 : ∀ b : Fin 16,
    (∀ l : Fin 16, ((MS 15 b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X 15 b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS 15 b).map fun m => m.testBit 16) =
      List.ofFn (X 15 b) ++ List.ofFn (fun l : Fin 16 => !(inc 15 l || inc b l)) ∧
    (∀ l : Fin 16, (inc 15 l || inc b l) = true → (outMask (MS 15 b)).testBit (l : ℕ) = true) ∧
    (outMask (MS 15 b)).testBit 16 = false := by decide +kernel

theorem chkM (a b : Fin 16) :
    (∀ l : Fin 16, ((MS a b).map fun m => m.testBit (l : ℕ)) =
      List.ofFn (X a b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) ∧
    ((MS a b).map fun m => m.testBit 16) =
      List.ofFn (X a b) ++ List.ofFn (fun l : Fin 16 => !(inc a l || inc b l)) ∧
    (∀ l : Fin 16, (inc a l || inc b l) = true → (outMask (MS a b)).testBit (l : ℕ) = true) ∧
    (outMask (MS a b)).testBit 16 = false := by
  have h : ∀ a : Fin 16, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 := by decide
  rcases h a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chkM_0 b
  · exact chkM_1 b
  · exact chkM_2 b
  · exact chkM_3 b
  · exact chkM_4 b
  · exact chkM_5 b
  · exact chkM_6 b
  · exact chkM_7 b
  · exact chkM_8 b
  · exact chkM_9 b
  · exact chkM_10 b
  · exact chkM_11 b
  · exact chkM_12 b
  · exact chkM_13 b
  · exact chkM_14 b
  · exact chkM_15 b

theorem evalTrue (a b l : Fin 16) (y : Fin 16 → Bool) (hl : (inc a l || inc b l) = true)
    (hy : y l = true) : C0.eval (List.ofFn (X a b) ++ List.ofFn y) = true := by
  obtain ⟨h1, _, h3, _⟩ := chkM a b
  have e : C0.eval (List.ofFn (X a b) ++ List.ofFn (fun l' : Fin 16 => decide (l' = l))) = true := by
    rw [← h1 l, sim_eval _ _ (by omega)]
    exact h3 l hl
  refine eval_mono C0 hao _ _ (in_mono (X a b) _ y ?_) e
  intro l' hl'
  have : l' = l := by simpa using hl'
  rw [this]
  exact hy

theorem evalFalse (a b : Fin 16) (y : Fin 16 → Bool)
    (hy : ∀ l, y l = true → (inc a l || inc b l) = false) :
    C0.eval (List.ofFn (X a b) ++ List.ofFn y) = false := by
  obtain ⟨_, h2, _, h4⟩ := chkM a b
  have e : C0.eval (List.ofFn (X a b) ++
      List.ofFn (fun l : Fin 16 => !(inc a l || inc b l))) = false := by
    rw [← h2, sim_eval _ 16 (by omega)]
    exact h4
  cases hE : C0.eval (List.ofFn (X a b) ++ List.ofFn y) with
  | false => rfl
  | true =>
    have := eval_mono C0 hao _ _ (in_mono (X a b) y (fun l => !(inc a l || inc b l))
      (fun l hl => by rw [hy l hl]; rfl)) hE
    rw [e] at this
    exact absurd this (by decide)

theorem key (a b : Fin 16) (y : Fin 16 → Bool) :
    C0.eval (List.ofFn (X a b) ++ List.ofFn y) =
      decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ L ∧ X a b p = true ∧ y l = true) := by
  by_cases h : ∃ l : Fin 16, (inc a l || inc b l) = true ∧ y l = true
  · obtain ⟨l, hl, hy⟩ := h
    rw [evalTrue a b l y hl hy]
    symm
    rw [decide_eq_true_iff]
    rw [Bool.or_eq_true] at hl
    rcases hl with hl | hl
    · exact ⟨a, l, by simpa [inc] using hl, by simp [X], hy⟩
    · exact ⟨b, l, by simpa [inc] using hl, by simp [X], hy⟩
  · rw [evalFalse a b y]
    · symm
      rw [decide_eq_false_iff_not]
      rintro ⟨p, l, hm, hx, hy⟩
      apply h
      refine ⟨l, ?_, hy⟩
      have hx' : p = a ∨ p = b := by simpa [X] using hx
      rw [Bool.or_eq_true]
      rcases hx' with rfl | rfl
      · left; simpa [inc] using hm
      · right; simpa [inc] using hm
    · intro l hy
      cases hh : (inc a l || inc b l) with
      | false => rfl
      | true => exact absurd ⟨l, hh, hy⟩ h

theorem key0 (y : Fin 16 → Bool) :
    C0.eval (List.ofFn (fun _ : Fin 16 => false) ++ List.ofFn y) = false := by
  have e : C0.eval (List.ofFn (fun _ : Fin 16 => false) ++ List.ofFn (fun _ : Fin 16 => true))
      = false := by
    rw [← chkM0.1, sim_eval _ 0 (by omega)]
    exact chkM0.2
  cases hE : C0.eval (List.ofFn (fun _ : Fin 16 => false) ++ List.ofFn y) with
  | false => rfl
  | true =>
    have := eval_mono C0 hao _ _ (in_mono (fun _ : Fin 16 => false) y _ (fun l hl => rfl)) hE
    rw [e] at this
    exact absurd this (by decide)

theorem main (x y : Fin 16 → Bool)
    (hx : (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2) :
    C0.eval (List.ofFn x ++ List.ofFn y) =
      decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ L ∧ x p = true ∧ y l = true) := by
  have hmem : ∀ p, x p = true ↔ p ∈ Finset.univ.filter (fun p : Fin 16 => x p = true) := by
    intro p; simp
  have hc : (Finset.univ.filter (fun p : Fin 16 => x p = true)).card = 0 ∨
      (Finset.univ.filter (fun p : Fin 16 => x p = true)).card = 1 ∨
      (Finset.univ.filter (fun p : Fin 16 => x p = true)).card = 2 := by omega
  rcases hc with h | h | h
  · rw [Finset.card_eq_zero] at h
    have hx0 : x = fun _ => false := by
      funext p
      cases hp : x p with
      | false => rfl
      | true => rw [hmem, h] at hp; simp at hp
    subst hx0
    rw [key0 y]
    simp
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h
    have hxa : x = X a a := by
      funext p
      rw [Bool.eq_iff_iff, hmem, ha]
      simp [X]
    rw [hxa]
    exact key a a y
  · obtain ⟨a, b, _, hab⟩ := Finset.card_eq_two.1 h
    have hxa : x = X a b := by
      funext p
      rw [Bool.eq_iff_iff, hmem, hab]
      simp [X]
    rw [hxa]
    exact key a b y

end PEqualNP.Outside.L_meta_1701_aux

theorem PEqualNP.Outside.L_meta_1701 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 39] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 45] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [47, 48] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [50, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 54] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 57] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [59, 60] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [62, 63] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [65, 66] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [68, 69] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [71, 72] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [74, 75] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [77, 78] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [80, 81] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [83, 84] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [86, 87] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [89, 90] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [92, 93] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [95, 96] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [98, 99] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [101, 102] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [104, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [105, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [106, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [107, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [109, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [110, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [111, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [112, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [114, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [115, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [116, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [117, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [119, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [120, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [121, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [122, 94] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [124, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [125, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [126, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [127, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [129, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [130, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [131, 82] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [132, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [134, 58] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [135, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [136, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [137, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [139, 64] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [140, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [141, 88] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [142, 100] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [144, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [145, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [146, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [147, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [149, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [150, 70] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [151, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [152, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 46] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [154, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [155, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [156, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [157, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 52] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [159, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [160, 76] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [161, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [162, 97] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [34, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [164, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [165, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [166, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [167, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [40, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [169, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [170, 73] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [171, 85] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [172, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [37, 49] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [174, 61] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [175, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [176, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [177, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [43, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [179, 67] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [180, 79] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [181, 91] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [182, 103] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [184, 185] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 186] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [188, 189] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 190] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [192, 193] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 194] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [196, 197] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 198] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [200, 201] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 202] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [204, 205] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 206] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [208, 209] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 210] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [212, 213] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [23, 214] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [216, 217] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 218] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [220, 221] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 222] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [224, 225] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [26, 226] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [228, 229] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [27, 230] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [108, 143] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [153, 178] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [232, 233] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 234] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [113, 138] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [148, 183] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [236, 237] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 238] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [118, 133] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [163, 168] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [240, 241] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 242] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [123, 128] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [158, 173] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [244, 245] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [31, 246] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [187, 191] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [195, 199] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [203, 207] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [211, 215] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [219, 223] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [227, 231] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [235, 239] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [243, 247] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [248, 249] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [250, 251] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [252, 253] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [254, 255] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [256, 257] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [258, 259] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [260, 261] }], output := 262 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 231 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 + 16) C ∧ ∀ (x y : Fin 16 → Bool), (Finset.univ.filter (fun p : Fin 16 => x p = true)).card ≤ 2 →
    C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ p : Fin 16, ∃ l : Fin 16, ((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (4, 0), (8, 0), (12, 0), (1, 1), (5, 1), (9, 1), (13, 1), (2, 2), (6, 2), (10, 2), (14, 2), (3, 3), (7, 3), (11, 3), (15, 3), (0, 4), (5, 4), (10, 4), (15, 4), (1, 5), (4, 5), (11, 5), (14, 5), (2, 6), (7, 6), (8, 6), (13, 6), (3, 7), (6, 7), (9, 7), (12, 7), (0, 8), (6, 8), (11, 8), (13, 8), (1, 9), (7, 9), (10, 9), (12, 9), (2, 10), (4, 10), (9, 10), (15, 10), (3, 11), (5, 11), (8, 11), (14, 11), (0, 12), (7, 12), (9, 12), (14, 12), (1, 13), (6, 13), (8, 13), (15, 13), (2, 14), (5, 14), (11, 14), (12, 14), (3, 15), (4, 15), (10, 15), (13, 15)] : List (ℕ × ℕ)) ∧ x p = true ∧ y l = true) := by
  intro C hC
  subst hC
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro x y hx
  exact PEqualNP.Outside.L_meta_1701_aux.main x y hx
