import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17153

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

def hcsBitsNat : {k : Nat} → (Fin k → Bool) → Nat
  | 0, _ => 0
  | k + 1, x => (if x 0 then 1 else 0) + 2 * hcsBitsNat (fun i : Fin k => x i.succ)

theorem hcsBitsNat_lt : ∀ {k : Nat} (x : Fin k → Bool), hcsBitsNat x < 2 ^ k
  | 0, _ => by simp [hcsBitsNat]
  | k + 1, x => by
    have ih := hcsBitsNat_lt (fun i : Fin k => x i.succ)
    simp only [hcsBitsNat, Nat.pow_succ]
    cases x 0
    · simp; omega
    · simp; omega

theorem hcsBitsNat_testBit : ∀ {k : Nat} (x : Fin k → Bool) (i : Fin k),
    (hcsBitsNat x).testBit i.val = x i
  | 0, _, i => Fin.elim0 i
  | k + 1, x, i => by
    refine Fin.cases ?_ ?_ i
    · simp only [hcsBitsNat, Fin.val_zero]
      cases x 0
      · simp [Nat.testBit_zero]
      · have hmod : (1 + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) % 2 = 1 := by omega
        simp [Nat.testBit_zero, hmod]
    · intro j
      have ih := hcsBitsNat_testBit (fun m : Fin k => x m.succ) j
      have hdiv : ((if x 0 then 1 else 0) + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) / 2 =
          hcsBitsNat (fun m : Fin k => x m.succ) := by
        cases x 0
        · simp
        · simp; omega
      simpa only [hcsBitsNat, Fin.val_succ, Nat.testBit_succ, hdiv] using ih

theorem hcsWitnessEval {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (hEval : (C.gates.foldl hcsStep raw).getD C.output 0 = goal) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  let r := hcsBitsNat x
  have hr : r < 2 ^ n := hcsBitsNat_lt x
  have hx : x = fun j : Fin n => r.testBit j.val := by
    funext j
    exact (hcsBitsNat_testBit x j).symm
  rw [hx]
  have hbank : raw.map (fun v => v.getLsbD r) = List.ofFn fun j : Fin n => r.testBit j.val :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hfg : goal.getLsbD r = f (fun j : Fin n => r.testBit j.val) :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hbits := hcsFoldBits raw ⟨r, hr⟩ C.gates hfan
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn fun j : Fin n => r.testBit j.val)).getD C.output false =
      f (fun j : Fin n => r.testBit j.val)
  rw [← hbank, ← hbits, ← hcsGetDBit, hEval, hfg]

theorem hcsWitness {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Nat) (f : (Fin n → Bool) → Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hsz : C.size ≤ s)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (hEval : (C.gates.foldl hcsStep raw).getD C.output 0 = goal) :
    PEqualNP.MetaComplexity.HasCircuitSize n f s := by
  exact ⟨C, hfan, hsz, hcsWitnessEval raw goal C f hfan hRaw hGoal hEval⟩



def asGate (t : Option Bool × Nat × Nat) : Gate :=
  match t.1 with
  | none => ⟨.not, [t.2.1]⟩
  | some b => ⟨if b then .or else .and, [t.2.1,t.2.2]⟩

def codes : List (Option Bool × Nat × Nat) := [
  (none, 0, 0),
  (none, 1, 0),
  (none, 2, 0),
  (none, 3, 0),
  (none, 4, 0),
  (some false, 10, 11),
  (some false, 0, 11),
  (some false, 10, 1),
  (some false, 0, 1),
  (some false, 12, 13),
  (some false, 2, 13),
  (some false, 12, 3),
  (some false, 2, 3),
  (some false, 19, 14),
  (some false, 20, 14),
  (some false, 21, 14),
  (some false, 22, 14),
  (some false, 19, 4),
  (some false, 20, 4),
  (some false, 21, 4),
  (some false, 22, 4),
  (some false, 15, 23),
  (some false, 16, 23),
  (some false, 17, 23),
  (some false, 18, 23),
  (some false, 15, 24),
  (some false, 16, 24),
  (some false, 17, 24),
  (some false, 18, 24),
  (some false, 15, 25),
  (some false, 16, 25),
  (some false, 17, 25),
  (some false, 18, 25),
  (some false, 15, 26),
  (some false, 16, 26),
  (some false, 17, 26),
  (some false, 18, 26),
  (some false, 15, 27),
  (some false, 16, 27),
  (some false, 17, 27),
  (some false, 18, 27),
  (some false, 15, 28),
  (some false, 16, 28),
  (some false, 17, 28),
  (some false, 18, 28),
  (some false, 15, 29),
  (some false, 16, 29),
  (some false, 17, 29),
  (some false, 18, 29),
  (some false, 15, 30),
  (some false, 16, 30),
  (some false, 17, 30),
  (some false, 18, 30),
  (none, 5, 0),
  (none, 6, 0),
  (none, 7, 0),
  (none, 8, 0),
  (none, 9, 0),
  (some false, 63, 64),
  (some false, 5, 64),
  (some false, 63, 6),
  (some false, 5, 6),
  (some false, 65, 66),
  (some false, 7, 66),
  (some false, 65, 8),
  (some false, 7, 8),
  (some false, 72, 67),
  (some false, 73, 67),
  (some false, 74, 67),
  (some false, 75, 67),
  (some false, 72, 9),
  (some false, 73, 9),
  (some false, 74, 9),
  (some false, 75, 9),
  (some false, 68, 76),
  (some false, 69, 76),
  (some false, 70, 76),
  (some false, 71, 76),
  (some false, 68, 77),
  (some false, 69, 77),
  (some false, 70, 77),
  (some false, 71, 77),
  (some false, 68, 78),
  (some false, 69, 78),
  (some false, 70, 78),
  (some false, 71, 78),
  (some false, 68, 79),
  (some false, 69, 79),
  (some false, 70, 79),
  (some false, 71, 79),
  (some false, 68, 80),
  (some false, 69, 80),
  (some false, 70, 80),
  (some false, 71, 80),
  (some false, 68, 81),
  (some false, 69, 81),
  (some false, 70, 81),
  (some false, 71, 81),
  (some false, 68, 82),
  (some false, 69, 82),
  (some false, 70, 82),
  (some false, 71, 82),
  (some false, 68, 83),
  (some false, 69, 83),
  (some false, 70, 83),
  (some false, 71, 83),
  (some true, 89, 106),
  (some true, 84, 105),
  (some true, 99, 107),
  (some true, 96, 100),
  (some true, 108, 110),
  (some true, 93, 98),
  (some true, 109, 112),
  (some true, 101, 116),
  (some true, 90, 115),
  (some true, 85, 114),
  (some true, 87, 121),
  (some true, 103, 104),
  (some true, 88, 92),
  (some true, 97, 118),
  (some true, 91, 117),
  (some true, 86, 88),
  (some true, 95, 106),
  (some true, 95, 123),
  (some true, 122, 124),
  (some true, 103, 129),
  (some true, 102, 113),
  (some true, 102, 125),
  (some true, 114, 119),
  (some true, 92, 122),
  (some true, 90, 109),
  (some true, 93, 135),
  (some true, 94, 100),
  (some true, 120, 125),
  (some true, 86, 105),
  (some true, 108, 112),
  (some true, 84, 91),
  (some true, 96, 141),
  (some true, 93, 120),
  (some true, 87, 113),
  (some true, 89, 126),
  (some true, 111, 126),
  (some true, 94, 130),
  (some true, 120, 144),
  (some true, 109, 119),
  (some true, 94, 133),
  (some true, 86, 127),
  (some true, 106, 128),
  (some true, 117, 143),
  (some true, 87, 105),
  (some true, 104, 132),
  (some true, 111, 147),
  (some true, 136, 152),
  (some true, 116, 146),
  (some true, 107, 123),
  (some true, 84, 101),
  (some true, 100, 115),
  (some true, 88, 148),
  (some true, 99, 131),
  (some true, 97, 123),
  (some true, 98, 134),
  (some true, 98, 138),
  (some true, 114, 132),
  (some true, 92, 124),
  (some true, 101, 129),
  (some true, 95, 145),
  (some true, 90, 107),
  (some true, 109, 115),
  (some true, 85, 127),
  (some true, 99, 137),
  (some true, 128, 132),
  (some true, 154, 159),
  (some true, 180, 181),
  (some false, 31, 182),
  (some true, 94, 150),
  (some true, 165, 177),
  (some true, 184, 185),
  (some true, 178, 186),
  (some false, 32, 187),
  (some true, 117, 122),
  (some true, 126, 166),
  (some true, 189, 190),
  (some true, 179, 191),
  (some false, 33, 192),
  (some true, 102, 111),
  (some true, 112, 146),
  (some true, 160, 166),
  (some true, 194, 195),
  (some true, 167, 196),
  (some true, 197, 198),
  (some false, 34, 199),
  (some true, 94, 138),
  (some true, 148, 168),
  (some true, 201, 202),
  (some false, 35, 203),
  (some true, 137, 155),
  (some true, 161, 205),
  (some false, 36, 206),
  (some true, 85, 91),
  (some true, 104, 105),
  (some true, 108, 128),
  (some true, 133, 142),
  (some true, 208, 209),
  (some true, 210, 211),
  (some true, 212, 213),
  (some false, 37, 214),
  (some true, 91, 121),
  (some true, 124, 127),
  (some true, 138, 164),
  (some true, 216, 217),
  (some true, 218, 219),
  (some false, 38, 220),
  (some true, 96, 107),
  (some true, 117, 120),
  (some true, 136, 156),
  (some true, 172, 177),
  (some true, 222, 223),
  (some true, 224, 225),
  (some true, 226, 227),
  (some false, 39, 228),
  (some true, 99, 145),
  (some true, 159, 171),
  (some true, 230, 231),
  (some true, 173, 232),
  (some false, 40, 233),
  (some true, 87, 90),
  (some true, 128, 143),
  (some true, 235, 236),
  (some true, 163, 237),
  (some false, 41, 238),
  (some true, 110, 117),
  (some true, 168, 169),
  (some true, 240, 241),
  (some false, 42, 242),
  (some true, 118, 127),
  (some true, 151, 175),
  (some true, 244, 245),
  (some false, 43, 246),
  (some true, 110, 131),
  (some true, 162, 174),
  (some true, 248, 249),
  (some false, 44, 250),
  (some true, 89, 101),
  (some true, 104, 111),
  (some true, 118, 134),
  (some true, 252, 253),
  (some true, 254, 255),
  (some false, 45, 256),
  (some true, 119, 135),
  (some true, 165, 173),
  (some true, 258, 259),
  (some false, 46, 260),
  (some true, 91, 110),
  (some true, 118, 136),
  (some true, 144, 154),
  (some true, 262, 263),
  (some true, 264, 265),
  (some false, 47, 266),
  (some true, 116, 139),
  (some true, 152, 161),
  (some true, 268, 269),
  (some false, 48, 270),
  (some true, 127, 142),
  (some true, 157, 158),
  (some true, 272, 273),
  (some true, 170, 274),
  (some false, 49, 275),
  (some true, 85, 139),
  (some true, 151, 153),
  (some true, 277, 278),
  (some true, 164, 279),
  (some false, 50, 280),
  (some true, 116, 149),
  (some true, 175, 176),
  (some true, 282, 283),
  (some false, 51, 284),
  (some true, 84, 98),
  (some true, 119, 131),
  (some true, 133, 137),
  (some true, 286, 287),
  (some true, 176, 288),
  (some true, 289, 290),
  (some false, 52, 291),
  (some true, 102, 103),
  (some true, 118, 124),
  (some true, 128, 150),
  (some true, 293, 294),
  (some true, 295, 296),
  (some false, 53, 297),
  (some true, 115, 125),
  (some true, 139, 149),
  (some true, 299, 300),
  (some true, 169, 301),
  (some false, 54, 302),
  (some true, 114, 140),
  (some true, 149, 167),
  (some true, 304, 305),
  (some true, 174, 306),
  (some false, 55, 307),
  (some true, 95, 100),
  (some true, 131, 163),
  (some true, 309, 310),
  (some true, 178, 311),
  (some false, 56, 312),
  (some true, 97, 108),
  (some true, 155, 156),
  (some true, 314, 315),
  (some true, 170, 316),
  (some false, 57, 317),
  (some true, 112, 162),
  (some true, 171, 319),
  (some false, 58, 320),
  (some true, 140, 142),
  (some true, 150, 153),
  (some true, 322, 323),
  (some true, 179, 324),
  (some false, 59, 325),
  (some true, 97, 119),
  (some true, 158, 160),
  (some true, 327, 328),
  (some false, 60, 329),
  (some true, 130, 140),
  (some true, 151, 157),
  (some true, 331, 332),
  (some false, 61, 333),
  (some true, 113, 130),
  (some true, 134, 147),
  (some true, 335, 336),
  (some true, 172, 337),
  (some false, 62, 338),
  (some true, 183, 188),
  (some true, 193, 200),
  (some true, 204, 207),
  (some true, 215, 221),
  (some true, 229, 234),
  (some true, 239, 243),
  (some true, 247, 251),
  (some true, 257, 261),
  (some true, 267, 271),
  (some true, 276, 281),
  (some true, 285, 292),
  (some true, 298, 303),
  (some true, 308, 313),
  (some true, 318, 321),
  (some true, 326, 330),
  (some true, 334, 339),
  (some true, 340, 341),
  (some true, 342, 343),
  (some true, 344, 345),
  (some true, 346, 347),
  (some true, 348, 349),
  (some true, 350, 351),
  (some true, 352, 353),
  (some true, 354, 355),
  (some true, 356, 357),
  (some true, 358, 359),
  (some true, 360, 361),
  (some true, 362, 363),
  (some true, 364, 365),
  (some true, 366, 367),
  (some true, 368, 369)]
def witness : Circuit := ⟨codes.map asGate, 370⟩

theorem basis : FanInTwo witness := by
  intro g hg
  obtain ⟨⟨o,i,j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases o with
  | none => simp [asGate]
  | some b => cases b <;> simp [asGate]
def words (xs : List ℕ) : BitVec 1024 :=
  BitVec.ofNat 1024 (xs.foldr (fun w rest => w + rest * 2 ^ 64) 0)

def inputTables : List (BitVec 1024) := [
  words [0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa, 0xaaaaaaaaaaaaaaaa],
  words [0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc, 0xcccccccccccccccc],
  words [0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0, 0xf0f0f0f0f0f0f0f0],
  words [0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00, 0xff00ff00ff00ff00],
  words [0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000, 0xffff0000ffff0000],
  words [0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000, 0xffffffff00000000],
  words [0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff, 0x0000000000000000, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff],
  words [0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff]]

def outputTable : BitVec 1024 := words [0x32ac0466ea26ad0e, 0x51d8160716292910, 0x16fa4ce243642c59, 0xca0324c8d574c680, 0xd14a10be40ce8641, 0xa63011691c062072, 0xa582a820a82383b1, 0x9143fa345c6c1286, 0x5a8e8e23a2582dd, 0x864691a21861212c, 0xf80f2b45260451ca, 0x817bf1a0e6be0de9, 0xd58f4107351c1758, 0x400a5028310d2d18, 0x899121008c9e520c, 0x84c4c38eb9a407b4]

end PEqualNP.Outside.L_meta_17153

open PEqualNP.Outside.L_meta_17153

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_17153 : PEqualNP.MetaComplexity.HasCircuitSize 10 (PEqualNP.Represents.adjFun (k := 5) (l := 5) (fun u v : Fin (2 ^ 5) => Nat.testBit 0xf2e8bac10a6043d9457138034725c66e70255481935a6c64005908b76782a258f242212a808cc37840c7587731c008681fe2432ed77945531ae8b7a126a59084808bb1419a92806024a6a4951998ca080462a035454001fbd121d148e7fc1805c0db52e001730db248cebe22450196149d550a91d225c20b821a462b02611918 (32 * u.val + v.val))) 365 := by
  exact hcsWitness (n := 10) inputTables outputTable witness 365 _ basis
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
