import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17145

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
  (some true, 52, 56),
  (some true, 37, 41),
  (some true, 40, 46),
  (some true, 55, 59),
  (some true, 39, 44),
  (some true, 31, 50),
  (some true, 34, 35),
  (some true, 33, 49),
  (some true, 36, 51),
  (some true, 117, 118),
  (some true, 42, 61),
  (some true, 116, 119),
  (some true, 32, 120),
  (some true, 57, 122),
  (some true, 48, 121),
  (some true, 31, 47),
  (some true, 62, 130),
  (some true, 58, 124),
  (some true, 43, 126),
  (some true, 60, 123),
  (some true, 32, 129),
  (some true, 45, 127),
  (some true, 54, 57),
  (some true, 38, 53),
  (some true, 49, 60),
  (some true, 116, 125),
  (some true, 58, 123),
  (some true, 32, 124),
  (some true, 47, 133),
  (some true, 120, 134),
  (some true, 46, 128),
  (some true, 31, 54),
  (some true, 40, 137),
  (some true, 45, 55),
  (some true, 127, 138),
  (some true, 56, 147),
  (some true, 35, 41),
  (some true, 125, 135),
  (some true, 121, 149),
  (some true, 40, 135),
  (some true, 142, 145),
  (some true, 47, 132),
  (some true, 131, 140),
  (some true, 39, 143),
  (some true, 59, 122),
  (some true, 39, 129),
  (some true, 116, 146),
  (some true, 35, 117),
  (some true, 45, 57),
  (some true, 128, 150),
  (some true, 41, 139),
  (some true, 48, 126),
  (some true, 49, 125),
  (some true, 53, 164),
  (some true, 53, 165),
  (some true, 60, 144),
  (some true, 151, 166),
  (some true, 59, 118),
  (some true, 43, 168),
  (some true, 34, 153),
  (some true, 44, 140),
  (some true, 44, 132),
  (some true, 128, 154),
  (some true, 178, 163),
  (some false, 179, 84),
  (some true, 33, 42),
  (some true, 181, 129),
  (some true, 182, 172),
  (some true, 183, 173),
  (some false, 184, 85),
  (some true, 37, 47),
  (some true, 186, 59),
  (some true, 187, 162),
  (some true, 188, 169),
  (some false, 189, 86),
  (some true, 58, 118),
  (some true, 191, 127),
  (some true, 192, 136),
  (some true, 193, 167),
  (some false, 194, 87),
  (some true, 133, 134),
  (some true, 196, 136),
  (some true, 197, 148),
  (some true, 198, 177),
  (some false, 199, 88),
  (some true, 52, 58),
  (some true, 201, 117),
  (some true, 202, 131),
  (some true, 203, 149),
  (some true, 204, 161),
  (some false, 205, 89),
  (some true, 142, 177),
  (some false, 207, 90),
  (some true, 33, 152),
  (some true, 209, 170),
  (some true, 210, 171),
  (some false, 211, 91),
  (some true, 49, 141),
  (some true, 213, 154),
  (some false, 214, 92),
  (some true, 50, 143),
  (some true, 216, 148),
  (some true, 217, 152),
  (some true, 218, 176),
  (some false, 219, 93),
  (some true, 37, 139),
  (some true, 221, 148),
  (some true, 222, 158),
  (some true, 223, 167),
  (some false, 224, 94),
  (some true, 119, 126),
  (some true, 226, 128),
  (some true, 227, 175),
  (some false, 228, 95),
  (some true, 116, 117),
  (some true, 230, 132),
  (some true, 231, 139),
  (some false, 232, 96),
  (some true, 56, 119),
  (some true, 234, 121),
  (some true, 235, 159),
  (some true, 236, 174),
  (some false, 237, 97),
  (some true, 33, 34),
  (some true, 239, 121),
  (some true, 240, 141),
  (some false, 241, 98),
  (some true, 150, 156),
  (some true, 243, 163),
  (some false, 244, 99),
  (some true, 54, 55),
  (some true, 246, 142),
  (some true, 247, 152),
  (some true, 248, 162),
  (some false, 249, 100),
  (some false, 155, 101),
  (some true, 46, 51),
  (some true, 252, 172),
  (some true, 253, 176),
  (some false, 254, 102),
  (some true, 40, 116),
  (some true, 256, 131),
  (some true, 257, 159),
  (some true, 258, 160),
  (some false, 259, 103),
  (some true, 55, 134),
  (some true, 261, 141),
  (some true, 262, 157),
  (some true, 263, 161),
  (some false, 264, 104),
  (some true, 35, 120),
  (some true, 266, 157),
  (some true, 267, 169),
  (some false, 268, 105),
  (some true, 62, 141),
  (some true, 270, 156),
  (some true, 271, 160),
  (some false, 272, 106),
  (some true, 37, 132),
  (some true, 274, 137),
  (some true, 275, 171),
  (some false, 276, 107),
  (some false, 136, 108),
  (some true, 35, 60),
  (some true, 279, 131),
  (some true, 280, 173),
  (some false, 281, 109),
  (some true, 42, 138),
  (some true, 283, 175),
  (some false, 284, 110),
  (some true, 119, 122),
  (some true, 286, 144),
  (some true, 287, 146),
  (some false, 288, 111),
  (some true, 45, 62),
  (some true, 290, 136),
  (some true, 291, 151),
  (some true, 292, 174),
  (some false, 293, 112),
  (some true, 117, 119),
  (some true, 295, 133),
  (some true, 296, 145),
  (some true, 297, 158),
  (some false, 298, 113),
  (some true, 123, 125),
  (some true, 300, 131),
  (some true, 301, 170),
  (some false, 302, 114),
  (some true, 31, 124),
  (some true, 304, 155),
  (some false, 305, 115),
  (some true, 180, 185),
  (some true, 307, 190),
  (some true, 308, 195),
  (some true, 309, 200),
  (some true, 310, 206),
  (some true, 311, 208),
  (some true, 312, 212),
  (some true, 313, 215),
  (some true, 314, 220),
  (some true, 315, 225),
  (some true, 316, 229),
  (some true, 317, 233),
  (some true, 318, 238),
  (some true, 319, 242),
  (some true, 320, 245),
  (some true, 321, 250),
  (some true, 322, 251),
  (some true, 323, 255),
  (some true, 324, 260),
  (some true, 325, 265),
  (some true, 326, 269),
  (some true, 327, 273),
  (some true, 328, 277),
  (some true, 329, 278),
  (some true, 330, 282),
  (some true, 331, 285),
  (some true, 332, 289),
  (some true, 333, 294),
  (some true, 334, 299),
  (some true, 335, 303),
  (some true, 336, 306)]
def witness : Circuit := ⟨codes.map asGate, 337⟩

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

def outputTable : BitVec 1024 := words [0x16c08e9d01086553, 0x5f228a1a1661e142, 0xd214559df3a7a3b, 0x3ff12536880e2005, 0x333c6632032cc641, 0x7104af4e73674ac1, 0x131c9763826a04c1, 0x5fa43d540228864d, 0x200402040ba4a516, 0x1231033b22d4a481, 0x844b6111c72b9f59, 0xbb3b4061da24bf5c, 0x300182110400001a, 0x1911a13a24848e4c, 0x79153d618684d65b, 0x2014022517e5a747]

end PEqualNP.Outside.L_meta_17145

open PEqualNP.Outside.L_meta_17145

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_17145 : PEqualNP.MetaComplexity.HasCircuitSize 10 (PEqualNP.Represents.adjFun (k := 5) (l := 5) (fun u v : Fin (2 ^ 5) => Nat.testBit 0x10f0105020508c18a6860e806ac8ae9e28c180f8553080be50ddf79e6891afb9540580824024148640d9d7bca88c229000b07351f447af4000b014586ab804a45e55690e10a0073568658ad53050a01024508c1a7455fba3d65a6f1a6879a8a50004140274d0fd25a88822901b7982bb1d58483ac443c8c259092a9df2bc7573 (32 * u.val + v.val))) 330 := by
  exact hcsWitness (n := 10) inputTables outputTable witness 330 _ basis
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
