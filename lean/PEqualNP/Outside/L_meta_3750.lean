import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3750

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

def G : List (Bool × ℕ × ℕ) := [(false, 0, 1), (false, 14, 3), (false, 7, 8), (false, 16, 10), (true, 15, 17), (false, 7, 10), (true, 5, 19), (false, 18, 20), (false, 0, 10), (false, 1, 5), (false, 23, 7), (true, 22, 24), (true, 21, 25), (false, 7, 8), (true, 4, 27), (false, 18, 28), (false, 1, 8), (false, 0, 3), (false, 31, 4), (true, 30, 32), (true, 29, 33), (false, 26, 34), (false, 7, 8), (true, 2, 36), (false, 18, 37), (false, 3, 7), (false, 1, 2), (false, 40, 10), (true, 39, 41), (true, 38, 42), (false, 35, 43), (false, 0, 5), (false, 45, 6), (true, 46, 9), (false, 44, 47), (false, 1, 4), (false, 49, 6), (true, 50, 11), (false, 48, 51), (false, 2, 3), (false, 53, 6), (true, 54, 12), (false, 52, 55), (false, 2, 4), (false, 57, 5), (true, 58, 13), (false, 56, 59)]

def Inc : List (Fin 14 × Fin 14) := [(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)]

def repeated : List (Fin 14 × Fin 14) := [(0, 7), (0, 8), (1, 7), (1, 10), (2, 7), (3, 8), (3, 10), (4, 8), (5, 10)]

def toGate (g : Bool × ℕ × ℕ) : Gate := ⟨cond g.1 GateOp.and GateOp.or, [g.2.1, g.2.2]⟩

def C0 : Circuit := ⟨G.map toGate, 60⟩

def stpG (fa fo : ℕ → ℕ → ℕ) (w : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ :=
  w ++ [cond g.1 (fa (w.getD g.2.1 0) (w.getD g.2.2 0)) (fo (w.getD g.2.1 0) (w.getD g.2.2 0))]

def rd (n : ℕ) (r : List ℕ) (a : ℕ) : ℕ := if a < n then r.getD (n - 1 - a) 0 else 0

def evR (fa fo : ℕ → ℕ → ℕ) : List (Bool × ℕ × ℕ) → ℕ → List ℕ → List ℕ
  | [], _, r => r
  | g :: gs, n, r =>
    evR fa fo gs (n + 1)
      (cond g.1 (fa (rd n r g.2.1) (rd n r g.2.2)) (fo (rd n r g.2.1) (rd n r g.2.2)) :: r)

theorem rd_eq (w : List ℕ) (a : ℕ) : rd w.length w.reverse a = w.getD a 0 := by
  unfold rd
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by omega)]
    congr 2
    omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem evR_eq (fa fo : ℕ → ℕ → ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List ℕ),
    evR fa fo gs w.length w.reverse = (gs.foldl (stpG fa fo) w).reverse := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ← ih, evR, rd_eq, rd_eq]
    simp [stpG]

theorem length_fold (fa fo : ℕ → ℕ → ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List ℕ),
    (gs.foldl (stpG fa fo) w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stpG]
    omega

theorem fold_getD (fa fo : ℕ → ℕ → ℕ) (gs : List (Bool × ℕ × ℕ)) (w : List ℕ) (a : ℕ) :
    (gs.foldl (stpG fa fo) w).getD a 0
      = rd (w.length + gs.length) (evR fa fo gs w.length w.reverse) a := by
  rw [evR_eq, ← length_fold fa fo, rd_eq]

def stpN (w : List ℕ) (g : Bool × ℕ × ℕ) : List ℕ := stpG (fun a b => a &&& b) (fun a b => a ||| b) w g

theorem getD_tb (k : ℕ) (W : List ℕ) (i : ℕ) :
    (W.map fun v => v.testBit k).getD i false = (W.getD i 0).testBit k := by
  have h := List.getD_map (f := fun v : ℕ => v.testBit k) (l := W) (d := 0) (n := i)
  simpa using h

theorem bridge (k : ℕ) : ∀ (gs : List (Bool × ℕ × ℕ)) (W : List ℕ),
    (gs.map toGate).foldl stp (W.map fun v => v.testBit k)
      = (gs.foldl stpN W).map fun v => v.testBit k := by
  intro gs
  induction gs with
  | nil => intro W; rfl
  | cons g gs ih =>
    intro W
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, ← ih]
    congr 1
    obtain ⟨b, i, j⟩ := g
    have hi := getD_tb k W i
    have hj := getD_tb k W j
    cases b
    · simp only [stp, stpN, stpG, toGate, GateOp.eval, cond, List.map_cons, List.map_nil, List.map_append, hi, hj]
      simp [Nat.testBit_lor]
    · simp only [stp, stpN, stpG, toGate, GateOp.eval, cond, List.map_cons, List.map_nil, List.map_append, hi, hj]
      simp [Nat.testBit_land]

def tab : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, p => if p = n then (2 ^ 2 ^ n - 1) <<< 2 ^ n else tab n p ||| (tab n p <<< 2 ^ n)

theorem tab_bit : ∀ n p k, p < n →
    (tab n p).testBit k = (decide (k < 2 ^ n) && k.testBit p) := by
  intro n
  induction n with
  | zero => intro p k h; omega
  | succ n ih =>
    intro p k hp
    have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    rw [tab]
    split_ifs with hpn
    · subst hpn
      rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases hk : k < 2 ^ p
      · rw [Nat.testBit_lt_two_pow hk]
        simp
        omega
      · have hb : k.testBit p = !((k - 2 ^ p).testBit p) := by
          rw [← Nat.testBit_two_pow_add_eq]
          congr 1
          omega
        by_cases hk2 : k - 2 ^ p < 2 ^ p
        · have e0 : decide (k ≥ 2 ^ p) = true := by
            simp only [decide_eq_true_eq]
            omega
          have e1 : decide (k - 2 ^ p < 2 ^ p) = true := by simpa using hk2
          have e2 : decide (k < 2 ^ (p + 1)) = true := by
            simp only [decide_eq_true_eq]
            omega
          rw [hb, Nat.testBit_lt_two_pow hk2, e0, e1, e2]
          rfl
        · have e1 : decide (k - 2 ^ p < 2 ^ p) = false := by simpa using hk2
          have e2 : decide (k < 2 ^ (p + 1)) = false := by
            simp only [decide_eq_false_iff_not]
            omega
          rw [e1, e2]
          simp
    · have hp' : p < n := by omega
      rw [Nat.testBit_lor, Nat.testBit_shiftLeft, ih p k hp', ih p (k - 2 ^ n) hp']
      by_cases hk : k < 2 ^ n
      · have e1 : decide (k < 2 ^ n) = true := by simpa using hk
        have e2 : decide (k < 2 ^ (n + 1)) = true := by
          simp only [decide_eq_true_eq]
          omega
        have e3 : decide (k ≥ 2 ^ n) = false := by
          simp only [decide_eq_false_iff_not]
          omega
        rw [e1, e2, e3]
        simp
      · have hb : (k - 2 ^ n).testBit p = k.testBit p := by
          rw [← Nat.testBit_two_pow_add_gt hp' (k - 2 ^ n)]
          congr 1
          omega
        have e1 : decide (k < 2 ^ n) = false := by simpa using hk
        have e3 : decide (k ≥ 2 ^ n) = true := by
          simp only [decide_eq_true_eq]
          omega
        have e4 : decide (k - 2 ^ n < 2 ^ n) = decide (k < 2 ^ (n + 1)) := by
          apply decide_eq_decide.mpr
          omega
        rw [e1, e3, e4, hb]
        simp

def W : List ℕ := (List.range 14).map (tab 14)

theorem W_getD (i : ℕ) : W.getD i 0 = if i < 14 then tab 14 i else 0 := by
  unfold W
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem W_len : W.length = 14 := by simp [W]

theorem G_len : G.length = 47 := by decide +kernel

def E : ℕ := Inc.foldr (fun q acc => (tab 14 q.1 &&& tab 14 q.2) ||| acc) 0

set_option maxRecDepth 100000 in
theorem out0 :
    rd 61 (evR (fun a b => a &&& b) (fun a b => a ||| b) G 14 W.reverse) 60 = E := by
  decide +kernel

theorem out_eq : (G.foldl stpN W).getD 60 0 = E := by
  have h := fold_getD (fun a b => a &&& b) (fun a b => a ||| b) G W 60
  rw [W_len, G_len] at h
  exact h.trans out0

theorem any_bit (x : Fin 14 → Bool) : ∀ L : List (Fin 14 × Fin 14),
    (L.foldr (fun q acc => (tab 14 q.1 &&& tab 14 q.2) ||| acc) 0).testBit (Nat.ofBits x)
      = L.any (fun q => x q.1 && x q.2) := by
  intro L
  induction L with
  | nil => simp
  | cons q L ih =>
    rw [List.foldr_cons, List.any_cons, Nat.testBit_lor, Nat.testBit_land,
      tab_bit 14 q.1 (Nat.ofBits x) q.1.isLt, tab_bit 14 q.2 (Nat.ofBits x) q.2.isLt,
      decide_eq_true (Nat.ofBits_lt_two_pow x), Bool.true_and, Bool.true_and,
      Nat.testBit_ofBits_lt x q.1 q.1.isLt, Nat.testBit_ofBits_lt x q.2 q.2.isLt, ih]

theorem len : C0.gates.length = 47 := by
  show (G.map toGate).length = 47
  rw [List.length_map, G_len]

theorem andOr : ∀ g ∈ C0.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  simp only [C0, List.mem_map] at hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := hg
  cases b
  · exact ⟨Or.inr rfl, rfl⟩
  · exact ⟨Or.inl rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem readsG : ∀ j < 47, (G.getD j (false, 0, 0)).2.1 < 14 + j ∧ (G.getD j (false, 0, 0)).2.2 < 14 + j := by
  decide +kernel

theorem readsBack : PEqualNP.MetaComplexity.NestedCover.ReadsBack (7 + 7) C0 := by
  intro j hj i hi
  rw [len] at hj
  have h := readsG j hj
  have e : PEqualNP.MetaComplexity.NestedCover.gateAt C0 j = toGate (G.getD j (false, 0, 0)) := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    show (G.map toGate).getD j _ = _
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by rw [G_len]; exact hj)]
    rfl
  rw [e] at hi
  simp only [toGate, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact h.1
  · exact h.2

theorem computes (x : Fin 14 → Bool) : C0.eval (List.ofFn x) =
    decide (∃ e ∈ Inc, x e.1 = true ∧ x e.2 = true) := by
  let k := Nat.ofBits x
  have hin : List.ofFn x = W.map (fun v => v.testBit k) := by
    refine List.ext_getElem (by simp [W]) (fun i h1 h2 => ?_)
    have hi : i < 14 := by simpa using h1
    rw [List.getElem_ofFn, ← List.getD_eq_getElem _ false h2, getD_tb, W_getD, if_pos hi,
      tab_bit 14 i k hi, decide_eq_true (Nat.ofBits_lt_two_pow x), Bool.true_and]
    exact (Nat.testBit_ofBits_lt x i hi).symm
  rw [eval_eq,hin]
  show ((G.map toGate).foldl stp (W.map fun v => v.testBit k)).getD 60 false = _
  rw [bridge,getD_tb,out_eq]
  rw [show E.testBit k = Inc.any (fun q => x q.1 && x q.2) from any_bit x Inc]
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true]

set_option maxRecDepth 100000 in
theorem edgeReads : ∀ e ∈ Inc, PEqualNP.Core.ReadTwiceAt 14 C0 (C0.output-14) e.1 e.2 ↔
    e ∈ repeated := by
  decide +kernel

end PEqualNP.Outside.L_meta_3750

open PEqualNP.Outside.L_meta_3750

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_3750 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 24] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [21, 25] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 27] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 28] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [31, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [30, 32] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [29, 33] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 36] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [40, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [39, 41] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [38, 42] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 43] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [45, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [44, 47] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [49, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [50, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [48, 51] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [53, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [54, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [52, 55] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [57, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [58, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [56, 59] }], output := 60 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 14 C ∧ C.size = 47 ∧
  (∀ x : Fin 14 → Bool, PEqualNP.MetaComplexity.circuitFun 14 C x = decide (∃ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (0, 8), (0, 9), (1, 7), (1, 10), (1, 11), (2, 7), (2, 12), (2, 13), (3, 8), (3, 10), (3, 12), (4, 8), (4, 11), (4, 13), (5, 9), (5, 10), (5, 13), (6, 9), (6, 11), (6, 12)] : List (Fin 14 × Fin 14)), PEqualNP.Core.ReadTwiceAt 14 C (C.output - 14) e.1 e.2 ↔ e ∈ ([(0, 7), (0, 8), (1, 7), (1, 10), (2, 7), (3, 8), (3, 10), (4, 8), (5, 10)] : List (Fin 14 × Fin 14))) := by
  intro C h
  change C = C0 at h
  subst C
  refine ⟨⟨fun g hg => (andOr g hg).1, readsBack, fun g hg => (andOr g hg).2⟩,len,computes,edgeReads⟩
