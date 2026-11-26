import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18226

open PEqualNP.CircuitLowerBounds

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

theorem two_pow_succ' (k : Nat) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
  rw [Nat.pow_succ]; omega

def inPat : (k : Nat) → Nat → BitVec (2 ^ k)
  | 0, _ => 0#1
  | k + 1, j =>
    if j < k then (inPat k j ++ inPat k j).cast (two_pow_succ' k)
    else if j = k then (BitVec.allOnes (2 ^ k) ++ 0#(2 ^ k)).cast (two_pow_succ' k)
    else 0#(2 ^ (k + 1))

theorem inPat_getLsbD : ∀ (k j r : Nat), (inPat k j).getLsbD r = (decide (r < 2 ^ k) && r.testBit j)
  | 0, j, r => by
    simp only [inPat, BitVec.getLsbD_zero, Nat.pow_zero]
    rcases Nat.lt_or_ge r 1 with h | h
    · have : r = 0 := by omega
      subst this; simp
    · simp [show ¬ r < 1 by omega]
  | k + 1, j, r => by
    have hk : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := (two_pow_succ' k).symm
    unfold inPat
    split_ifs with h1 h2
    · rw [BitVec.getLsbD_cast, BitVec.getLsbD_append]
      by_cases hr : r < 2 ^ k
      · simp only [hr, decide_true, ite_true, inPat_getLsbD k j r, Bool.true_and]
        have : r < 2 ^ (k + 1) := by omega
        simp [this]
      · simp only [hr, ite_false, inPat_getLsbD k j (r - 2 ^ k)]
        have e : r = 2 ^ k + (r - 2 ^ k) := by omega
        have hb : r.testBit j = (r - 2 ^ k).testBit j := by
          conv_lhs => rw [e]
          exact Nat.testBit_two_pow_add_gt h1 (r - 2 ^ k)
        rw [hb]
        congr 1
        simp only [decide_eq_decide]; omega
    · subst h2
      rw [BitVec.getLsbD_cast, BitVec.getLsbD_append]
      by_cases hr : r < 2 ^ j
      · simp only [hr, ite_true, BitVec.getLsbD_zero]
        rw [Nat.testBit_lt_two_pow hr]; simp
      · simp only [hr, ite_false, BitVec.getLsbD_allOnes]
        by_cases hr2 : r < 2 ^ (j + 1)
        · have e : r = 2 ^ j + (r - 2 ^ j) := by omega
          have hb : r.testBit j = true := by
            rw [e, Nat.testBit_two_pow_add_eq]
            rw [Nat.testBit_lt_two_pow (by omega)]; rfl
          rw [hb]; simp [hr2]; omega
        · simp [hr2]; omega
    · rw [BitVec.getLsbD_zero]
      by_cases hr2 : r < 2 ^ (k + 1)
      · have hj : k + 1 ≤ j := by omega
        have : r < 2 ^ j := lt_of_lt_of_le hr2 (Nat.pow_le_pow_right (by norm_num) hj)
        rw [Nat.testBit_lt_two_pow this]; simp
      · simp [hr2]

theorem inBank_getLsbD (n r : Nat) (hr : r < 2 ^ n) :
    ((List.ofFn fun j : Fin n => inPat n j.val).map fun v => v.getLsbD r) = List.ofFn fun j : Fin n => r.testBit j.val := by
  rw [List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply, inPat_getLsbD, hr, decide_true, Bool.true_and]

theorem hcsSymWitness {n : Nat} (goal : BitVec (2 ^ n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Nat) (f : (Fin n → Bool) → Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C) (hsz : C.size ≤ s)
    (hGoal : ∀ r, r < 2 ^ n → goal.getLsbD r = f (fun j : Fin n => r.testBit j.val))
    (hEval : (C.gates.foldl hcsStep (List.ofFn fun j : Fin n => inPat n j.val)).getD C.output 0 = goal) :
    PEqualNP.MetaComplexity.HasCircuitSize n f s := by
  refine ⟨C, hfan, hsz, ?_⟩
  intro x
  let r := hcsBitsNat x
  have hr : r < 2 ^ n := hcsBitsNat_lt x
  have hx : x = fun j : Fin n => r.testBit j.val := by
    funext j
    exact (hcsBitsNat_testBit x j).symm
  rw [hx]
  have hbank := inBank_getLsbD n r hr
  have hfg := hGoal r hr
  have hbits := hcsFoldBits (List.ofFn fun j : Fin n => inPat n j.val) ⟨r, hr⟩ C.gates hfan
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn fun j : Fin n => r.testBit j.val)).getD C.output false =
      f (fun j : Fin n => r.testBit j.val)
  rw [← hbank, ← hbits, ← hcsGetDBit, hEval, hfg]

def okOp : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | .and => true
  | .or => true
  | .not => true
  | _ => false

theorem okOp_mem {o : PEqualNP.CircuitLowerBounds.GateOp} (h : okOp o = true) :
    o ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) := by
  cases o <;> simp_all [okOp]

theorem fanInTwo_of_all (C : PEqualNP.CircuitLowerBounds.Circuit)
    (h : C.gates.all (fun g => okOp g.op && decide (g.inputs.length ≤ 2)) = true) :
    PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  have hg2 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg2
  exact ⟨okOp_mem hg2.1, hg2.2⟩

def witness : Circuit :=
  ⟨[⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [4, 8]⟩, ⟨.and, [16, 9]⟩, ⟨.and, [17, 10]⟩, ⟨.and, [18, 11]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [22, 21]⟩, ⟨.and, [15, 23]⟩, ⟨.and, [17, 12]⟩, ⟨.and, [18, 13]⟩, ⟨.or, [25, 26]⟩, ⟨.and, [16, 27]⟩, ⟨.and, [17, 18]⟩, ⟨.and, [29, 14]⟩, ⟨.or, [24, 28]⟩, ⟨.or, [31, 30]⟩, ⟨.and, [0, 32]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [10, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [36, 3]⟩, ⟨.and, [37, 4]⟩, ⟨.or, [38, 39]⟩, ⟨.and, [34, 40]⟩, ⟨.and, [36, 7]⟩, ⟨.and, [37, 8]⟩, ⟨.or, [42, 43]⟩, ⟨.and, [35, 44]⟩, ⟨.and, [36, 37]⟩, ⟨.and, [46, 14]⟩, ⟨.or, [41, 45]⟩, ⟨.or, [48, 47]⟩, ⟨.and, [9, 49]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [53, 1]⟩, ⟨.and, [54, 2]⟩, ⟨.or, [55, 56]⟩, ⟨.and, [51, 57]⟩, ⟨.and, [53, 5]⟩, ⟨.and, [54, 6]⟩, ⟨.or, [59, 60]⟩, ⟨.and, [52, 61]⟩, ⟨.or, [58, 62]⟩, ⟨.and, [14, 63]⟩, ⟨.or, [33, 50]⟩, ⟨.or, [65, 64]⟩], 66⟩

set_option maxRecDepth 100000 in
theorem basis : PEqualNP.MetaComplexity.FanInTwo witness :=
  fanInTwo_of_all witness (by decide +kernel)

set_option maxRecDepth 100000 in
theorem hsz : witness.size ≤ 60 := by
  decide +kernel

def goalV : BitVec (2 ^ 15) := (inPat 15 0 &&& inPat 15 1 &&& inPat 15 2 &&& inPat 15 5 &&& inPat 15 6 &&& inPat 15 9) ||| (inPat 15 0 &&& inPat 15 1 &&& inPat 15 3 &&& inPat 15 5 &&& inPat 15 7 &&& inPat 15 10) ||| (inPat 15 0 &&& inPat 15 1 &&& inPat 15 4 &&& inPat 15 5 &&& inPat 15 8 &&& inPat 15 11) ||| (inPat 15 0 &&& inPat 15 2 &&& inPat 15 3 &&& inPat 15 6 &&& inPat 15 7 &&& inPat 15 12) ||| (inPat 15 0 &&& inPat 15 2 &&& inPat 15 4 &&& inPat 15 6 &&& inPat 15 8 &&& inPat 15 13) ||| (inPat 15 0 &&& inPat 15 3 &&& inPat 15 4 &&& inPat 15 7 &&& inPat 15 8 &&& inPat 15 14) ||| (inPat 15 1 &&& inPat 15 2 &&& inPat 15 3 &&& inPat 15 9 &&& inPat 15 10 &&& inPat 15 12) ||| (inPat 15 1 &&& inPat 15 2 &&& inPat 15 4 &&& inPat 15 9 &&& inPat 15 11 &&& inPat 15 13) ||| (inPat 15 1 &&& inPat 15 3 &&& inPat 15 4 &&& inPat 15 10 &&& inPat 15 11 &&& inPat 15 14) ||| (inPat 15 2 &&& inPat 15 3 &&& inPat 15 4 &&& inPat 15 12 &&& inPat 15 13 &&& inPat 15 14) ||| (inPat 15 5 &&& inPat 15 6 &&& inPat 15 7 &&& inPat 15 9 &&& inPat 15 10 &&& inPat 15 12) ||| (inPat 15 5 &&& inPat 15 6 &&& inPat 15 8 &&& inPat 15 9 &&& inPat 15 11 &&& inPat 15 13) ||| (inPat 15 5 &&& inPat 15 7 &&& inPat 15 8 &&& inPat 15 10 &&& inPat 15 11 &&& inPat 15 14) ||| (inPat 15 6 &&& inPat 15 7 &&& inPat 15 8 &&& inPat 15 12 &&& inPat 15 13 &&& inPat 15 14) ||| (inPat 15 9 &&& inPat 15 10 &&& inPat 15 11 &&& inPat 15 12 &&& inPat 15 13 &&& inPat 15 14)

def fstmt : (Fin 15 → Bool) → Bool := fun x : Fin 15 → Bool => (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14)

theorem hGoal : ∀ r, r < 2 ^ 15 → goalV.getLsbD r = fstmt (fun j : Fin 15 => r.testBit j.val) := by
  intro r hr
  simp only [goalV, fstmt, BitVec.getLsbD_not, BitVec.getLsbD_and, BitVec.getLsbD_or, inPat_getLsbD, hr,
    decide_true, Bool.true_and, Fin.isValue]
  rfl

set_option maxRecDepth 100000 in
theorem hEval : (witness.gates.foldl hcsStep (List.ofFn fun j : Fin 15 => inPat 15 j.val)).getD witness.output 0 = goalV := by
  decide +kernel

end PEqualNP.Outside.L_meta_18226

theorem PEqualNP.Outside.L_meta_18226 : (PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14)) 60) := by
  exact PEqualNP.Outside.L_meta_18226.hcsSymWitness (n := 15) PEqualNP.Outside.L_meta_18226.goalV PEqualNP.Outside.L_meta_18226.witness 60 PEqualNP.Outside.L_meta_18226.fstmt PEqualNP.Outside.L_meta_18226.basis PEqualNP.Outside.L_meta_18226.hsz PEqualNP.Outside.L_meta_18226.hGoal PEqualNP.Outside.L_meta_18226.hEval
