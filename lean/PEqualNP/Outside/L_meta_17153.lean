import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17153

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

def hcsFanGate (g : PEqualNP.CircuitLowerBounds.Gate) : Bool :=
  (match g.op with
   | PEqualNP.CircuitLowerBounds.GateOp.and => true
   | PEqualNP.CircuitLowerBounds.GateOp.or => true
   | PEqualNP.CircuitLowerBounds.GateOp.not => true
   | _ => false) && decide (g.inputs.length ≤ 2)

theorem hcsFanInTwo_of_all (C : PEqualNP.CircuitLowerBounds.Circuit)
    (h : C.gates.all hcsFanGate = true) : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  unfold hcsFanGate at h1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

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

def rawInputs : List (BitVec 1024) :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]

def goalVec : BitVec 1024 :=
  0x84c4c38eb9a407b4899121008c9e520c400a5028310d2d18d58f4107351c1758817bf1a0e6be0de9f80f2b45260451ca864691a21861212c05a8e8e23a2582dd9143fa345c6c1286a582a820a82383b1a63011691c062072d14a10be40ce8641ca0324c8d574c68016fa4ce243642c5951d816071629291032ac0466ea26ad0e

def traceCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.not, [5]⟩, ⟨.not, [6]⟩, ⟨.not, [7]⟩, ⟨.not, [8]⟩, ⟨.not, [9]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [5, 11]⟩, ⟨.and, [10, 6]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [7, 13]⟩, ⟨.and, [12, 8]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [19, 14]⟩, ⟨.and, [20, 14]⟩, ⟨.and, [21, 14]⟩, ⟨.and, [22, 14]⟩, ⟨.and, [19, 9]⟩, ⟨.and, [20, 9]⟩, ⟨.and, [21, 9]⟩, ⟨.and, [22, 9]⟩, ⟨.and, [15, 23]⟩, ⟨.and, [16, 23]⟩, ⟨.and, [17, 23]⟩, ⟨.and, [18, 23]⟩, ⟨.and, [15, 24]⟩, ⟨.and, [16, 24]⟩, ⟨.and, [17, 24]⟩, ⟨.and, [18, 24]⟩, ⟨.and, [15, 25]⟩, ⟨.and, [16, 25]⟩, ⟨.and, [17, 25]⟩, ⟨.and, [18, 25]⟩, ⟨.and, [15, 26]⟩, ⟨.and, [16, 26]⟩, ⟨.and, [17, 26]⟩, ⟨.and, [18, 26]⟩, ⟨.and, [15, 27]⟩, ⟨.and, [16, 27]⟩, ⟨.and, [17, 27]⟩, ⟨.and, [18, 27]⟩, ⟨.and, [15, 28]⟩, ⟨.and, [16, 28]⟩, ⟨.and, [17, 28]⟩, ⟨.and, [18, 28]⟩, ⟨.and, [15, 29]⟩, ⟨.and, [16, 29]⟩, ⟨.and, [17, 29]⟩, ⟨.and, [18, 29]⟩, ⟨.and, [15, 30]⟩, ⟨.and, [16, 30]⟩, ⟨.and, [17, 30]⟩, ⟨.and, [18, 30]⟩, ⟨.or, [36, 53]⟩, ⟨.or, [52, 56]⟩, ⟨.or, [46, 54]⟩, ⟨.or, [43, 47]⟩, ⟨.or, [55, 57]⟩, ⟨.or, [34, 40]⟩, ⟨.or, [50, 62]⟩, ⟨.or, [31, 61]⟩, ⟨.or, [48, 63]⟩, ⟨.or, [37, 45]⟩, ⟨.or, [42, 51]⟩, ⟨.or, [35, 39]⟩, ⟨.or, [44, 65]⟩, ⟨.or, [53, 64]⟩, ⟨.or, [32, 41]⟩, ⟨.or, [59, 62]⟩, ⟨.or, [31, 38]⟩, ⟨.or, [33, 35]⟩, ⟨.or, [45, 68]⟩, ⟨.or, [32, 70]⟩, ⟨.or, [69, 72]⟩, ⟨.or, [49, 60]⟩, ⟨.or, [74, 76]⟩, ⟨.or, [48, 56]⟩, ⟨.or, [47, 49]⟩, ⟨.or, [40, 58]⟩, ⟨.or, [67, 73]⟩, ⟨.or, [46, 61]⟩, ⟨.or, [43, 75]⟩, ⟨.or, [61, 71]⟩, ⟨.or, [55, 73]⟩, ⟨.or, [38, 66]⟩, ⟨.or, [33, 64]⟩, ⟨.or, [41, 59]⟩, ⟨.or, [37, 60]⟩, ⟨.or, [34, 42]⟩, ⟨.or, [31, 69]⟩, ⟨.or, [36, 51]⟩, ⟨.or, [86, 100]⟩, ⟨.or, [78, 87]⟩, ⟨.or, [53, 89]⟩, ⟨.or, [79, 88]⟩, ⟨.or, [41, 80]⟩, ⟨.or, [66, 90]⟩, ⟨.or, [42, 49]⟩, ⟨.or, [50, 91]⟩, ⟨.or, [38, 74]⟩, ⟨.or, [47, 77]⟩, ⟨.or, [52, 71]⟩, ⟨.or, [51, 83]⟩, ⟨.or, [69, 70]⟩, ⟨.or, [76, 113]⟩, ⟨.or, [34, 39]⟩, ⟨.or, [78, 115]⟩, ⟨.or, [58, 59]⟩, ⟨.or, [81, 117]⟩, ⟨.or, [48, 75]⟩, ⟨.or, [52, 84]⟩, ⟨.or, [54, 71]⟩, ⟨.or, [67, 95]⟩, ⟨.or, [59, 97]⟩, ⟨.or, [66, 82]⟩, ⟨.or, [36, 68]⟩, ⟨.or, [44, 56]⟩, ⟨.or, [66, 85]⟩, ⟨.or, [127, 98]⟩, ⟨.or, [77, 81]⟩, ⟨.or, [129, 99]⟩, ⟨.or, [130, 101]⟩, ⟨.or, [46, 64]⟩, ⟨.or, [132, 81]⟩, ⟨.or, [133, 82]⟩, ⟨.or, [134, 102]⟩, ⟨.or, [35, 102]⟩, ⟨.or, [136, 103]⟩, ⟨.or, [137, 104]⟩, ⟨.or, [40, 67]⟩, ⟨.or, [139, 105]⟩, ⟨.or, [140, 106]⟩, ⟨.or, [77, 88]⟩, ⟨.or, [142, 92]⟩, ⟨.or, [143, 107]⟩, ⟨.or, [144, 108]⟩, ⟨.or, [93, 109]⟩, ⟨.or, [146, 110]⟩, ⟨.or, [147, 111]⟩, ⟨.or, [40, 54]⟩, ⟨.or, [149, 92]⟩, ⟨.or, [150, 94]⟩, ⟨.or, [151, 112]⟩, ⟨.or, [33, 43]⟩, ⟨.or, [153, 54]⟩, ⟨.or, [154, 84]⟩, ⟨.or, [155, 89]⟩, ⟨.or, [156, 114]⟩, ⟨.or, [52, 55]⟩, ⟨.or, [158, 72]⟩, ⟨.or, [159, 106]⟩, ⟨.or, [160, 116]⟩, ⟨.or, [34, 37]⟩, ⟨.or, [162, 63]⟩, ⟨.or, [163, 67]⟩, ⟨.or, [164, 82]⟩, ⟨.or, [165, 109]⟩, ⟨.or, [31, 44]⟩, ⟨.or, [167, 46]⟩, ⟨.or, [168, 57]⟩, ⟨.or, [169, 80]⟩, ⟨.or, [170, 111]⟩, ⟨.or, [50, 65]⟩, ⟨.or, [172, 93]⟩, ⟨.or, [173, 118]⟩, ⟨.or, [57, 79]⟩, ⟨.or, [175, 105]⟩, ⟨.or, [176, 119]⟩, ⟨.or, [177, 120]⟩, ⟨.or, [37, 58]⟩, ⟨.or, [179, 65]⟩, ⟨.or, [180, 78]⟩, ⟨.or, [181, 101]⟩, ⟨.or, [37, 39]⟩, ⟨.or, [183, 66]⟩, ⟨.or, [184, 99]⟩, ⟨.or, [185, 119]⟩, ⟨.or, [57, 65]⟩, ⟨.or, [187, 84]⟩, ⟨.or, [188, 94]⟩, ⟨.or, [189, 95]⟩, ⟨.or, [39, 63]⟩, ⟨.or, [191, 64]⟩, ⟨.or, [192, 96]⟩, ⟨.or, [193, 104]⟩, ⟨.or, [194, 108]⟩, ⟨.or, [59, 67]⟩, ⟨.or, [196, 70]⟩, ⟨.or, [197, 85]⟩, ⟨.or, [198, 110]⟩, ⟨.or, [199, 112]⟩, ⟨.or, [32, 39]⟩, ⟨.or, [201, 118]⟩, ⟨.or, [202, 121]⟩, ⟨.or, [203, 122]⟩, ⟨.or, [54, 55]⟩, ⟨.or, [205, 63]⟩, ⟨.or, [206, 98]⟩, ⟨.or, [207, 123]⟩, ⟨.or, [72, 80]⟩, ⟨.or, [209, 107]⟩, ⟨.or, [210, 121]⟩, ⟨.or, [211, 124]⟩, ⟨.or, [49, 65]⟩, ⟨.or, [213, 74]⟩, ⟨.or, [214, 83]⟩, ⟨.or, [215, 125]⟩, ⟨.or, [32, 60]⟩, ⟨.or, [217, 92]⟩, ⟨.or, [218, 116]⟩, ⟨.or, [219, 126]⟩, ⟨.or, [35, 61]⟩, ⟨.or, [221, 67]⟩, ⟨.or, [222, 68]⟩, ⟨.or, [223, 75]⟩, ⟨.or, [224, 86]⟩, ⟨.or, [225, 97]⟩, ⟨.or, [32, 47]⟩, ⟨.or, [227, 50]⟩, ⟨.or, [228, 63]⟩, ⟨.or, [229, 73]⟩, ⟨.or, [230, 79]⟩, ⟨.or, [231, 80]⟩, ⟨.or, [33, 71]⟩, ⟨.or, [233, 83]⟩, ⟨.or, [234, 93]⟩, ⟨.or, [235, 96]⟩, ⟨.or, [236, 126]⟩, ⟨.or, [45, 70]⟩, ⟨.or, [238, 94]⟩, ⟨.or, [239, 96]⟩, ⟨.or, [240, 120]⟩, ⟨.or, [72, 77]⟩, ⟨.or, [242, 87]⟩, ⟨.or, [243, 90]⟩, ⟨.or, [244, 122]⟩, ⟨.or, [245, 125]⟩, ⟨.or, [44, 52]⟩, ⟨.or, [247, 103]⟩, ⟨.or, [248, 124]⟩, ⟨.or, [58, 68]⟩, ⟨.or, [250, 72]⟩, ⟨.or, [251, 79]⟩, ⟨.or, [252, 85]⟩, ⟨.or, [38, 40]⟩, ⟨.or, [254, 42]⟩, ⟨.or, [255, 91]⟩, ⟨.or, [256, 114]⟩, ⟨.or, [257, 123]⟩, ⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.not, [2]⟩, ⟨.not, [3]⟩, ⟨.not, [4]⟩, ⟨.and, [259, 128]⟩, ⟨.and, [0, 131]⟩, ⟨.or, [264, 265]⟩, ⟨.and, [259, 135]⟩, ⟨.and, [0, 138]⟩, ⟨.or, [267, 268]⟩, ⟨.and, [259, 141]⟩, ⟨.and, [0, 145]⟩, ⟨.or, [270, 271]⟩, ⟨.and, [259, 148]⟩, ⟨.and, [0, 152]⟩, ⟨.or, [273, 274]⟩, ⟨.and, [259, 157]⟩, ⟨.and, [0, 161]⟩, ⟨.or, [276, 277]⟩, ⟨.and, [259, 166]⟩, ⟨.and, [0, 171]⟩, ⟨.or, [279, 280]⟩, ⟨.and, [259, 174]⟩, ⟨.and, [0, 178]⟩, ⟨.or, [282, 283]⟩, ⟨.and, [259, 182]⟩, ⟨.and, [0, 186]⟩, ⟨.or, [285, 286]⟩, ⟨.and, [259, 190]⟩, ⟨.and, [0, 195]⟩, ⟨.or, [288, 289]⟩, ⟨.and, [259, 200]⟩, ⟨.and, [0, 204]⟩, ⟨.or, [291, 292]⟩, ⟨.and, [259, 208]⟩, ⟨.and, [0, 212]⟩, ⟨.or, [294, 295]⟩, ⟨.and, [259, 216]⟩, ⟨.and, [0, 220]⟩, ⟨.or, [297, 298]⟩, ⟨.and, [259, 226]⟩, ⟨.and, [0, 232]⟩, ⟨.or, [300, 301]⟩, ⟨.and, [259, 237]⟩, ⟨.and, [0, 241]⟩, ⟨.or, [303, 304]⟩, ⟨.and, [259, 246]⟩, ⟨.and, [0, 249]⟩, ⟨.or, [306, 307]⟩, ⟨.and, [259, 253]⟩, ⟨.and, [0, 258]⟩, ⟨.or, [309, 310]⟩, ⟨.and, [260, 266]⟩, ⟨.and, [1, 269]⟩, ⟨.or, [312, 313]⟩, ⟨.and, [260, 272]⟩, ⟨.and, [1, 275]⟩, ⟨.or, [315, 316]⟩, ⟨.and, [260, 278]⟩, ⟨.and, [1, 281]⟩, ⟨.or, [318, 319]⟩, ⟨.and, [260, 284]⟩, ⟨.and, [1, 287]⟩, ⟨.or, [321, 322]⟩, ⟨.and, [260, 290]⟩, ⟨.and, [1, 293]⟩, ⟨.or, [324, 325]⟩, ⟨.and, [260, 296]⟩, ⟨.and, [1, 299]⟩, ⟨.or, [327, 328]⟩, ⟨.and, [260, 302]⟩, ⟨.and, [1, 305]⟩, ⟨.or, [330, 331]⟩, ⟨.and, [260, 308]⟩, ⟨.and, [1, 311]⟩, ⟨.or, [333, 334]⟩, ⟨.and, [261, 314]⟩, ⟨.and, [2, 317]⟩, ⟨.or, [336, 337]⟩, ⟨.and, [261, 320]⟩, ⟨.and, [2, 323]⟩, ⟨.or, [339, 340]⟩, ⟨.and, [261, 326]⟩, ⟨.and, [2, 329]⟩, ⟨.or, [342, 343]⟩, ⟨.and, [261, 332]⟩, ⟨.and, [2, 335]⟩, ⟨.or, [345, 346]⟩, ⟨.and, [262, 338]⟩, ⟨.and, [3, 341]⟩, ⟨.or, [348, 349]⟩, ⟨.and, [262, 344]⟩, ⟨.and, [3, 347]⟩, ⟨.or, [351, 352]⟩, ⟨.and, [263, 350]⟩, ⟨.and, [4, 353]⟩, ⟨.or, [354, 355]⟩], 356⟩

end PEqualNP.Outside.L_meta_17153

open PEqualNP.Outside.L_meta_17153 in
theorem PEqualNP.Outside.L_meta_17153 : (PEqualNP.MetaComplexity.HasCircuitSize 10 (PEqualNP.Represents.adjFun (k := 5) (l := 5) (fun u v : Fin (2 ^ 5) => Nat.testBit 0xf2e8bac10a6043d9457138034725c66e70255481935a6c64005908b76782a258f242212a808cc37840c7587731c008681fe2432ed77945531ae8b7a126a59084808bb1419a92806024a6a4951998ca080462a035454001fbd121d148e7fc1805c0db52e001730db248cebe22450196149d550a91d225c20b821a462b02611918 (32 * u.val + v.val))) 365) := by
  exact hcsWitness (n := 10) rawInputs goalVec traceCircuit 365 _
    (hcsFanInTwo_of_all traceCircuit (by decide +kernel))
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
