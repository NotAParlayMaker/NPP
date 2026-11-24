import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1492

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

lemma wireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    wireVal n C p x = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma gateVal_eq {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    gateVal n C j x = (gateAt C j).op.eval ((gateAt C j).inputs.map fun r =>
      if r < n + j then wireVal n C r x else false) := by
  have hga : gateAt C j = C.gates[j] := by
    unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
  rw [hga]
  set w := n + j with hwdef
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, hwdef]
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then wireVal n C r x else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then wireVal n C r x else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma wireVal_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) :
    wireVal n C (n + j) x = gateVal n C j x := rfl

lemma and_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (a : ℕ) (ha : a < C.gates.length)
    (hrb : ReadsBack n C) (h2 : (gateAt C a).inputs.length = 2)
    (hop : (gateAt C a).op = GateOp.and) :
    gateVal n C a x = (wireVal n C (opnd C a 0) x && wireVal n C (opnd C a 1) x) := by
  rw [gateVal_eq C x a ha, hop]
  obtain ⟨p, q, hpq⟩ : ∃ p q, (gateAt C a).inputs = [p, q] := by
    match h : (gateAt C a).inputs, h2 with
    | [p, q], _ => exact ⟨p, q, rfl⟩
  have hp : p < n + a := hrb a ha p (by rw [hpq]; simp)
  have hq : q < n + a := hrb a ha q (by rw [hpq]; simp)
  simp [hpq, opnd, GateOp.eval, hp, hq]

lemma or_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (a : ℕ) (ha : a < C.gates.length)
    (hrb : ReadsBack n C) (hop : (gateAt C a).op = GateOp.or) (r : ℕ)
    (hr : r ∈ (gateAt C a).inputs) (hv : wireVal n C r x = true) : gateVal n C a x = true := by
  rw [gateVal_eq C x a ha, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true]
  exact ⟨r, hr, by simp [hrb a ha r hr, hv]⟩


def foldS (F : List (List ℕ) → Gate → List ℕ) (gs : List Gate) : List (List ℕ) :=
  gs.foldl (fun cs g => cs ++ [F cs g]) []

lemma foldl_len (F : List (List ℕ) → Gate → List ℕ) (hs : List Gate) :
    ∀ cs : List (List ℕ), (hs.foldl (fun cs g => cs ++ [F cs g]) cs).length = cs.length + hs.length := by
  induction hs with
  | nil => intro cs; simp
  | cons h hs ih => intro cs; simp only [List.foldl_cons]; rw [ih]; simp; omega

lemma foldl_prefix (F : List (List ℕ) → Gate → List ℕ) (hs : List Gate) :
    ∀ (cs : List (List ℕ)) (i : ℕ), i < cs.length →
      (hs.foldl (fun cs g => cs ++ [F cs g]) cs).getD i [] = cs.getD i [] := by
  induction hs with
  | nil => intro cs i _; rfl
  | cons h hs ih =>
    intro cs i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp; omega), List.getD_append _ _ _ _ hi]

lemma foldS_length (F : List (List ℕ) → Gate → List ℕ) (gs : List Gate) :
    (foldS F gs).length = gs.length := by
  unfold foldS; rw [foldl_len]; simp

lemma foldS_split (F : List (List ℕ) → Gate → List ℕ) (gs : List Gate) (j : ℕ) :
    foldS F gs = (gs.drop j).foldl (fun cs g => cs ++ [F cs g]) (foldS F (gs.take j)) := by
  unfold foldS
  rw [← List.foldl_append, List.take_append_drop]

lemma foldS_take (F : List (List ℕ) → Gate → List ℕ) (gs : List Gate) (j i : ℕ) (hi : i < j)
    (hj : j ≤ gs.length) : (foldS F (gs.take j)).getD i [] = (foldS F gs).getD i [] := by
  rw [foldS_split F gs j, foldl_prefix]
  rw [foldS_length]; simp; omega

lemma foldS_self (F : List (List ℕ) → Gate → List ℕ) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) : (foldS F gs).getD j [] = F (foldS F (gs.take j)) gs[j] := by
  rw [foldS_split F gs j, List.drop_eq_getElem_cons hj, List.foldl_cons, foldl_prefix]
  · have hl : (foldS F (gs.take j)).length = j := by rw [foldS_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl]
  · simp [foldS_length]; omega

def orF (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ := (orStep n cs g).getD cs.length []

lemma orStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) : orStep n cs g = cs ++ [orF n cs g] := by
  unfold orF orStep; simp

lemma orSets_eq (n : ℕ) (C : Circuit) : orSets n C = foldS (orF n) C.gates := by
  unfold orSets foldS
  have : orStep n = fun cs g => cs ++ [orF n cs g] := by
    funext cs g; exact orStep_eq n cs g
  rw [this]

lemma orF_or (n : ℕ) (cs : List (List ℕ)) (g : Gate) (h : g.op = GateOp.or) :
    orF n cs g = cs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => cs.getD (w - n) []) := by
  unfold orF orStep; simp [h]

lemma orF_not (n : ℕ) (cs : List (List ℕ)) (g : Gate) (h : g.op ≠ GateOp.or) :
    orF n cs g = [cs.length] := by
  unfold orF orStep; simp [h]

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt; rw [List.getD_eq_getElem _ _ hj]

lemma orSets_or (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (h : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] = j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  rw [orSets_eq, foldS_self _ _ _ hj]
  rw [gateAt_eq C j hj] at h ⊢
  rw [orF_or _ _ _ h]
  have hl : (foldS (orF n) (C.gates.take j)).length = j := by
    rw [foldS_length]; simp; omega
  rw [hl]
  congr 1
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  exact foldS_take _ _ _ _ (by omega) hj.le

lemma orSets_and (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (h : (gateAt C j).op ≠ GateOp.or) : (orSets n C).getD j [] = [j] := by
  rw [orSets_eq, foldS_self _ _ _ hj]
  rw [gateAt_eq C j hj] at h
  rw [orF_not _ _ _ h, foldS_length]; simp; omega

lemma orSets_nil (n : ℕ) (C : Circuit) (j : ℕ) (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  rw [orSets_eq]; apply List.getD_eq_default; rw [foldS_length]; exact hj

def coneF (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ := (coneStep n cs g).getD cs.length []

lemma cones_eq (n : ℕ) (C : Circuit) : cones n C = foldS (coneF n) C.gates := by
  unfold cones foldS
  have : coneStep n = fun cs g => cs ++ [coneF n cs g] := by
    funext cs g; unfold coneF coneStep; simp
  rw [this]

lemma coneF_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) : coneF n cs g =
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) []) := by
  unfold coneF coneStep; simp

lemma cones_get (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  rw [cones_eq, foldS_self _ _ _ hj, gateAt_eq C j hj, coneF_eq]
  have hl : (foldS (coneF n) (C.gates.take j)).length = j := by
    rw [foldS_length]; simp; omega
  rw [hl]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  rw [foldS_take _ _ _ _ (by omega) hj.le]

lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

lemma orSets_le (n : ℕ) (C : Circuit) : ∀ j k, k ∈ (orSets n C).getD j [] → k ≤ j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro k hk
    by_cases hj : j < C.gates.length
    · by_cases hop : (gateAt C j).op = GateOp.or
      · rw [orSets_or n C j hj hop] at hk
        rcases List.mem_cons.mp hk with h | h
        · exact ⟨h.le, hj⟩
        · obtain ⟨w, hw, hk2⟩ := List.mem_flatMap.mp h
          simp only [List.mem_filter, decide_eq_true_eq] at hw
          have := ih (w - n) (by omega) k hk2
          exact ⟨by omega, hj⟩
      · rw [orSets_and n C j hj hop] at hk
        simp at hk; exact ⟨hk.le, hj⟩
    · rw [orSets_nil n C j (by omega)] at hk; simp at hk

lemma orSets_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    j ∈ (orSets n C).getD j [] := by
  by_cases hop : (gateAt C j).op = GateOp.or
  · rw [orSets_or n C j hj hop]; simp
  · rw [orSets_and n C j hj hop]; simp

lemma orSets_val {n : ℕ} (C : Circuit) (hrb : ReadsBack n C) (x : Fin n → Bool) :
    ∀ j k, k ∈ (orSets n C).getD j [] → gateVal n C k x = true → gateVal n C j x = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro k hk hv
    have hj := (orSets_le n C j k hk).2
    by_cases hop : (gateAt C j).op = GateOp.or
    · rw [orSets_or n C j hj hop] at hk
      rcases List.mem_cons.mp hk with h | h
      · subst h; exact hv
      · obtain ⟨w, hw, hk2⟩ := List.mem_flatMap.mp h
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have h1 := ih (w - n) (by omega) k hk2 hv
        apply or_val C x j hj hrb hop w hw.1
        have : w = n + (w - n) := by omega
        rw [this, wireVal_gate]; exact h1
    · rw [orSets_and n C j hj hop] at hk
      simp at hk; subst hk; exact hv

lemma reach_val {n : ℕ} (C : Circuit) (hrb : ReadsBack n C) (x : Fin n → Bool) (w k : ℕ)
    (h : OrReaches n C w k) (hv : gateVal n C k x = true) : wireVal n C w x = true := by
  obtain ⟨hw, hk⟩ := h
  have := orSets_val C hrb x (w - n) k hk hv
  have e : w = n + (w - n) := by omega
  rw [e, wireVal_gate]; exact this

lemma orIn_val {n : ℕ} (C : Circuit) (hrb : ReadsBack n C) (x : Fin n → Bool) (w : ℕ)
    (i : Fin n) (hi : i ∈ orIn n C w) (hx : x i = true) : wireVal n C w x = true := by
  unfold orIn at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with h | ⟨k, hk, hr, hop, hin⟩
  · rw [← h, wireVal_input]; exact hx
  · apply reach_val C hrb x w k hr
    apply or_val C x k hk hrb hop i hin
    rw [wireVal_input]; exact hx

lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ j k, k ∈ (orSets n C).getD j [] →
    k = j ∨ k ∈ (cones n C).getD j [] := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro k hk
    have hj := (orSets_le n C j k hk).2
    by_cases hop : (gateAt C j).op = GateOp.or
    · rw [orSets_or n C j hj hop] at hk
      rcases List.mem_cons.mp hk with h | h
      · exact Or.inl h
      · obtain ⟨w, hw, hk2⟩ := List.mem_flatMap.mp h
        have hw' := hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw'
        right
        rw [cones_get n C j hj]
        apply List.mem_flatMap.mpr
        refine ⟨w, hw, ?_⟩
        rcases ih (w - n) (by omega) k hk2 with h3 | h3
        · rw [h3]; simp
        · exact List.mem_cons_of_mem _ h3
    · rw [orSets_and n C j hj hop] at hk
      simp at hk; exact Or.inl hk

lemma reach_cone {n : ℕ} (C : Circuit) (hrb : ReadsBack n C) (a : ℕ) (ha : a < C.gates.length)
    (w : ℕ) (hw : w ∈ (gateAt C a).inputs) (k : ℕ) (h : OrReaches n C w k) : InCone n C k a := by
  obtain ⟨hn, hk⟩ := h
  have hwa := hrb a ha w hw
  unfold InCone
  rw [cones_get n C a ha]
  apply List.mem_flatMap.mpr
  refine ⟨w, by simp [hw, hn, hwa], ?_⟩
  rcases orSets_cone n C (w - n) k hk with h3 | h3
  · rw [h3]; simp
  · exact List.mem_cons_of_mem _ h3

lemma leaf_exists {n : ℕ} (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hrb : ReadsBack n C) : ∀ j, j < C.gates.length →
    (∀ k ∈ (orSets n C).getD j [], (gateAt C k).op = GateOp.or → ∀ i ∈ (gateAt C k).inputs, n ≤ i) →
    ∃ k ∈ (orSets n C).getD j [], (gateAt C k).op ≠ GateOp.or := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hyp
    by_cases hop : (gateAt C j).op = GateOp.or
    · obtain ⟨p, q, hpq⟩ : ∃ p q, (gateAt C j).inputs = [p, q] := by
        have := h2 _ (gateAt_mem C j hj)
        match h : (gateAt C j).inputs, this with
        | [p, q], _ => exact ⟨p, q, rfl⟩
      have hpin : p ∈ (gateAt C j).inputs := by rw [hpq]; simp
      have hpn : n ≤ p := hyp j (orSets_self n C j hj) hop p hpin
      have hpj : p < n + j := hrb j hj p hpin
      have sub : ∀ k ∈ (orSets n C).getD (p - n) [], k ∈ (orSets n C).getD j [] := by
        intro k hk
        rw [orSets_or n C j hj hop]
        apply List.mem_cons_of_mem
        apply List.mem_flatMap.mpr
        exact ⟨p, by simp [hpin, hpn, hpj], hk⟩
      obtain ⟨k, hk, hk2⟩ := ih (p - n) (by omega) (by omega)
        (fun k hk => hyp k (sub k hk))
      exact ⟨k, sub k hk, hk2⟩
    · exact ⟨j, orSets_self n C j hj, hop⟩

section Tops

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

lemma mem_tops (a : ℕ) : a ∈ tops G C ↔
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  unfold tops gatesWhere; simp

lemma mem_junk (g : ℕ) : g ∈ junk G C ↔ g < C.gates.length ∧ IsDirtyAnd n G C g := by
  unfold junk gatesWhere; simp

lemma opnd_mem (hAO : IsAO2 n C) (a : ℕ) (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ : ∃ p q, (gateAt C a).inputs = [p, q] := by
    have := hAO.2.2 _ (gateAt_mem C a ha)
    match h : (gateAt C a).inputs, this with
    | [p, q], _ => exact ⟨p, q, rfl⟩
  unfold opnd; rw [hpq]
  fin_cases b <;> simp

lemma top_val (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) (x : Fin n → Bool) :
    gateVal n C a x = (wireVal n C (opnd C a 0) x && wireVal n C (opnd C a 1) x) := by
  rw [mem_tops] at ha
  exact and_val C x a ha.1 hAO.2.1 (hAO.2.2 _ (gateAt_mem C a ha.1)) ha.2.1

lemma top_true (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) (x : Fin n → Bool) (b : Fin 2)
    (h1 : wireVal n C (opnd C a b) x = true) (h2 : wireVal n C (opnd C a (1 - b)) x = true) :
    graphFun G ∅ x = true := by
  have hb := ((mem_tops G C a).mp ha).2.2
  apply hb x
  rw [top_val G C hAO a ha]
  fin_cases b
  · simp only [Fin.zero_eta, Fin.isValue, sub_zero] at h1 h2; simp [h1, h2]
  · simp only [Fin.mk_one, Fin.isValue, sub_self] at h1 h2; simp [h1, h2]

lemma cross_adj (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2) (u v : Fin n)
    (hu : u ∈ side C a b) (hv : v ∈ side C a (1 - b)) : G.Adj u v := by
  have hrb := hAO.2.1
  have hF := top_true G C hAO a ha (pairInput u v) b
    (orIn_val C hrb _ _ u hu (by simp [pairInput]))
    (orIn_val C hrb _ _ v hv (by simp [pairInput]))
  unfold graphFun at hF
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq] at hF
  obtain ⟨p, q, hpq, hp, hq⟩ := hF
  simp only [pairInput, decide_eq_true_eq] at hp hq
  have hne : p ≠ q := G.ne_of_adj hpq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hne
  · exact hpq
  · exact hpq.symm
  · exact absurd rfl hne

lemma singleton_side (hAO : IsAO2 n C) (h4 : NoFourCycle G) (a : ℕ) (ha : a ∈ tops G C)
    (h0 : (side C a 0 : Finset (Fin n)).Nonempty) (h1 : (side C a 1 : Finset (Fin n)).Nonempty) :
    ∃ b : Fin 2, ∃ c : Fin n, side C a b = {c} := by
  by_contra hno
  push Not at hno
  have big : ∀ b : Fin 2, 1 < (side C a b : Finset (Fin n)).card := by
    intro b
    have hne : (side C a b : Finset (Fin n)).Nonempty := by fin_cases b; exact h0; exact h1
    rw [Finset.one_lt_card_iff_nontrivial]
    rcases hne.exists_eq_singleton_or_nontrivial with ⟨c, hc⟩ | h
    · exact absurd hc (hno b c)
    · exact h
  obtain ⟨u1, hu1, u2, hu2, hu⟩ := Finset.one_lt_card.mp (big 0)
  obtain ⟨v1, hv1, v2, hv2, hv⟩ := Finset.one_lt_card.mp (big 1)
  have hc := h4 u1 u2 hu
  have sub : ({v1, v2} : Finset (Fin n)) ⊆ Finset.univ.filter fun w => G.Adj u1 w ∧ G.Adj u2 w := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with rfl | rfl
    · exact ⟨cross_adj G C hAO a ha 0 u1 w hu1 hv1, cross_adj G C hAO a ha 0 u2 w hu2 hv1⟩
    · exact ⟨cross_adj G C hAO a ha 0 u1 w hu1 hv2, cross_adj G C hAO a ha 0 u2 w hu2 hv2⟩
  have := Finset.card_le_card sub
  rw [Finset.card_pair hv] at this
  omega

lemma junk_dirty (g : ℕ) (hg : g ∈ junk G C) :
    ∃ x : Fin n → Bool, gateVal n C g x = true ∧ graphFun G ∅ x = false := by
  rw [mem_junk] at hg
  exact hg.2.2.2

lemma not_both (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) (g : ℕ) (hg : g ∈ junk G C)
    (b : Fin 2) (h1 : OrReaches n C (opnd C a b) g) (h2 : OrReaches n C (opnd C a (1 - b)) g) :
    False := by
  obtain ⟨x, hx, hF⟩ := junk_dirty G C g hg
  have := top_true G C hAO a ha x b (reach_val C hAO.2.1 x _ g h1 hx)
    (reach_val C hAO.2.1 x _ g h2 hx)
  rw [hF] at this; exact Bool.false_ne_true this

lemma empty_side_reach (hAO : IsAO2 n C) (hTF : TopForm G C) (g : ℕ) (hj : junk G C = {g})
    (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2) (he : side (n := n) C a b = ∅) :
    OrReaches n C (opnd C a b) g := by
  have hal := ((mem_tops G C a).mp ha)
  set w := opnd C a b with hwdef
  have hwin : w ∈ (gateAt C a).inputs := opnd_mem C hAO a hal.1 b
  have hwa : w < n + a := hAO.2.1 a hal.1 w hwin
  have hside : orIn n C w = ∅ := he
  have hn : n ≤ w := by
    by_contra hlt
    push Not at hlt
    have : (⟨w, hlt⟩ : Fin n) ∈ orIn n C w := by unfold orIn; simp
    rw [hside] at this; simp at this
  obtain ⟨k, hk, hkop⟩ := leaf_exists C hAO.2.2 hAO.2.1 (w - n) (by omega) (by
    intro k hk hop i hi
    by_contra hlt
    push Not at hlt
    have hkl := (orSets_le n C (w - n) k hk)
    have : (⟨i, hlt⟩ : Fin n) ∈ orIn n C w := by
      unfold orIn
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨k, by have := hkl.2; have := hkl.1; omega, ⟨hn, hk⟩, hop, hi⟩
    rw [hside] at this; simp at this)
  have hkl := orSets_le n C (w - n) k hk
  have hklen : k < C.gates.length := by have := hkl.1; have := hkl.2; omega
  have hkand : (gateAt C k).op = GateOp.and := by
    rcases hAO.1 _ (gateAt_mem C k hklen) with h | h
    · exact h
    · exact absurd h hkop
  have hcone : InCone n C k a := reach_cone C hAO.2.1 a hal.1 w hwin k ⟨hn, hk⟩
  have hnb : ¬ BelowF G C k := fun hb => hTF k hklen a hal.1 hkand hb hal.2.1 hcone
  have hkj : k ∈ junk G C := by
    rw [mem_junk]
    refine ⟨hklen, hkand, hklen, ?_⟩
    unfold BelowF at hnb
    push Not at hnb
    obtain ⟨x, hx, hF⟩ := hnb
    exact ⟨x, hx, by simpa using hF⟩
  rw [hj, Finset.mem_singleton] at hkj
  rw [← hkj]; exact ⟨hn, hk⟩

end Tops

section Forced

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)

lemma fin2_other (b b' : Fin 2) (h : b ≠ b') : b' = 1 - b := by
  fin_cases b <;> fin_cases b' <;> simp_all

lemma fin2_sub_sub (b : Fin 2) : 1 - (1 - b) = b := by fin_cases b <;> rfl

def Forced (g : ℕ) (a : ℕ) (u : Fin n) : Prop :=
  (∃ b : Fin 2, side C a b = {u} ∧ OrReaches n C (opnd C a b) g) ∨
  (∃ b : Fin 2, 2 ≤ (side (n := n) C a b).card ∧ OrReaches n C (opnd C a b) g ∧
    side C a (1 - b) = {u})

lemma forced_unique (hAO : IsAO2 n C) (g : ℕ) (hg : g ∈ junk G C) (a : ℕ) (ha : a ∈ tops G C)
    (u u' : Fin n) (h : Forced C g a u) (h' : Forced C g a u') : u = u' := by
  have nb := not_both G C hAO a ha g hg
  rcases h with ⟨b, hs, hr⟩ | ⟨b, hc, hr, hs⟩ <;>
    rcases h' with ⟨b', hs', hr'⟩ | ⟨b', hc', hr', hs'⟩
  · by_cases e : b = b'
    · subst e; rw [hs] at hs'; exact Finset.singleton_injective hs'
    · rw [fin2_other b b' e] at hr'; exact (nb b hr hr').elim
  · by_cases e : b = b'
    · subst e; rw [hs] at hc'; simp at hc'
    · rw [fin2_other b b' e] at hr'; exact (nb b hr hr').elim
  · by_cases e : b = b'
    · subst e; rw [hs'] at hc; simp at hc
    · rw [fin2_other b b' e] at hr'; exact (nb b hr hr').elim
  · by_cases e : b = b'
    · subst e; rw [hs] at hs'; exact Finset.singleton_injective hs'
    · rw [fin2_other b b' e] at hc'; rw [hs] at hc'; simp at hc'

lemma mem_centreless (a : ℕ) : a ∈ centreless G C ↔ a ∈ tops G C ∧
    (side (n := n) C a 0 = ∅ ∨ side (n := n) C a 1 = ∅) := by
  unfold centreless; simp

lemma dom_sides (a : ℕ) (ha : a ∈ tops G C \ centreless G C) :
    a ∈ tops G C ∧ (side (n := n) C a 0).Nonempty ∧ (side (n := n) C a 1).Nonempty := by
  rw [Finset.mem_sdiff, mem_centreless] at ha
  refine ⟨ha.1, ?_, ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]; intro h; exact ha.2 ⟨ha.1, Or.inl h⟩
  · rw [Finset.nonempty_iff_ne_empty]; intro h; exact ha.2 ⟨ha.1, Or.inr h⟩

lemma forced_dom (hAO : IsAO2 n C) (hTF : TopForm G C) (g : ℕ) (hj : junk G C = {g})
    (a : ℕ) (ha : a ∈ tops G C) (u : Fin n) (h : Forced C g a u) :
    a ∈ tops G C \ centreless G C ∧ ∃ b : Fin 2, side C a b = {u} := by
  have hg : g ∈ junk G C := by rw [hj]; simp
  have nb := not_both G C hAO a ha g hg
  have nonempty_of : ∀ b : Fin 2, side (n := n) C a b ≠ ∅ → side (n := n) C a (1 - b) ≠ ∅ →
      a ∈ tops G C \ centreless G C := by
    intro b h1 h2
    rw [Finset.mem_sdiff, mem_centreless]
    refine ⟨ha, ?_⟩
    rintro ⟨_, h0 | h0⟩
    · fin_cases b
      · exact h1 h0
      · exact h2 h0
    · fin_cases b
      · exact h2 h0
      · exact h1 h0
  rcases h with ⟨b, hs, hr⟩ | ⟨b, hc, hr, hs⟩
  · refine ⟨nonempty_of b (by rw [hs]; simp) ?_, b, hs⟩
    intro he
    exact nb b hr (empty_side_reach G C hAO hTF g hj a ha (1 - b) he)
  · refine ⟨nonempty_of b ?_ (by rw [hs]; simp), 1 - b, hs⟩
    intro he; rw [he] at hc; simp at hc

end Forced

theorem count_fibres {α β : Type*} [DecidableEq β] (D : Finset α) (c : α → β) (P : Finset β)
    (hP : P ⊆ D.image c) (h2 : ∀ u ∈ P, 2 ≤ (D.filter fun a => c a = u).card) :
    (D.image c).card + P.card ≤ D.card := by
  rw [Finset.card_eq_sum_card_image c D]
  have : (D.image c).card + P.card = ∑ u ∈ D.image c, (if u ∈ P then 2 else 1) := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, mul_one]
    have e1 : (D.image c).filter (fun u => u ∈ P) = P := by
      ext u; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hP h, h⟩⟩
    rw [e1]
    have e2 := Finset.card_filter_add_card_filter_not (s := D.image c) (fun u => u ∈ P)
    rw [e1] at e2
    omega
  rw [this]
  apply Finset.sum_le_sum
  intro u hu
  split_ifs with hup
  · exact h2 u hup
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.card_pos.mpr ⟨a, by simp [ha]⟩

lemma star_mem {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (e : Sym2 (Fin n)) (he : e ∈ starEdges G C) :
    ∃ a ∈ tops G C, ∃ p ∈ side (n := n) C a 0, ∃ q ∈ side (n := n) C a 1, e = s(p, q) := by
  unfold starEdges at he
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at he
  obtain ⟨a, ha, ⟨p, q⟩, ⟨hp, hq⟩, rfl⟩ := he
  exact ⟨a, ha, p, hp, q, hq, rfl⟩

lemma star_dom {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (a : ℕ)
    (ha : a ∈ tops G C) (p : Fin n) (hp : p ∈ side (n := n) C a 0) (q : Fin n)
    (hq : q ∈ side (n := n) C a 1) : a ∈ tops G C \ centreless G C := by
  rw [Finset.mem_sdiff, mem_centreless]
  refine ⟨ha, ?_⟩
  rintro ⟨_, h0 | h0⟩
  · rw [h0] at hp; simp at hp
  · rw [h0] at hq; simp at hq

lemma centre_in {n : ℕ} (C : Circuit) (a : ℕ) (c p q : Fin n) (b : Fin 2)
    (hb : side C a b = {c}) (hp : p ∈ side (n := n) C a 0) (hq : q ∈ side (n := n) C a 1) :
    c = p ∨ c = q := by
  fin_cases b
  · left; simp only [Fin.zero_eta, Fin.isValue] at hb; rw [hb] at hp; simp at hp; exact hp.symm
  · right; simp only [Fin.mk_one, Fin.isValue] at hb; rw [hb] at hq; simp at hq; exact hq.symm

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    ∃ K : Finset (Fin n), (∀ e ∈ PEqualNP.TopForm.starEdges G C, ∃ v ∈ K, v ∈ e) ∧
      (Finset.univ : Finset (Fin n)).filter (fun u => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ⊆ K ∧
      (Finset.univ : Finset (Fin n)).filter (fun w => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          2 ≤ (PEqualNP.TopForm.side (n := n) C a b).card ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g ∧
          PEqualNP.TopForm.side (n := n) C a (1 - b) = {w}) ⊆ K ∧
      K.card + ((Finset.univ : Finset (Fin n)).filter (fun u => (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ PEqualNP.TopForm.Ustar G C ∧ v ∉ PEqualNP.TopForm.wmax G C g ∧ v ∉ K)).card ≤
        (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  intro n G _ C h4 _ hL hTF g hj
  have hAO : IsAO2 n C := hL.1
  have hg : g ∈ junk G C := by rw [hj]; simp
  set D := tops G C \ centreless G C with hD
  have hex : ∀ a ∈ D, ∃ c : Fin n, (∃ b : Fin 2, side C a b = {c}) ∧
      ∀ u, Forced C g a u → u = c := by
    intro a ha
    have hds := dom_sides G C a ha
    by_cases hf : ∃ u : Fin n, Forced C g a u
    · obtain ⟨u, hu⟩ := hf
      refine ⟨u, (forced_dom G C hAO hTF g hj a hds.1 u hu).2, ?_⟩
      intro u' hu'
      exact forced_unique G C hAO g hg a hds.1 u' u hu' hu
    · push Not at hf
      obtain ⟨b, c, hc⟩ := singleton_side G C hAO h4 a hds.1 hds.2.1 hds.2.2
      exact ⟨c, ⟨b, hc⟩, fun u hu => (hf u hu).elim⟩
  choose c hc using hex
  let cc : D → Fin n := fun a => c a.1 a.2
  refine ⟨D.attach.image cc, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, ha, p, hp, q, hq, rfl⟩ := star_mem G C e he
    have haD : a ∈ D := star_dom G C a ha p hp q hq
    refine ⟨c a haD, Finset.mem_image.mpr ⟨⟨a, haD⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    obtain ⟨b, hb⟩ := (hc a haD).1
    rcases centre_in C a (c a haD) p q b hb hp hq with h | h <;> rw [h] <;> simp
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨a, ha, b, hs, hr⟩ := hu
    have hf : Forced C g a u := Or.inl ⟨b, hs, hr⟩
    have haD := (forced_dom G C hAO hTF g hj a ha u hf).1
    exact Finset.mem_image.mpr ⟨⟨a, haD⟩, Finset.mem_attach _ _, ((hc a haD).2 u hf).symm⟩
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨a, ha, b, hcard, hr, hs⟩ := hu
    have hf : Forced C g a u := Or.inr ⟨b, hcard, hr, hs⟩
    have haD := (forced_dom G C hAO hTF g hj a ha u hf).1
    exact Finset.mem_image.mpr ⟨⟨a, haD⟩, Finset.mem_attach _ _, ((hc a haD).2 u hf).symm⟩
  · have hcard := count_fibres D.attach cc
      ((Finset.univ : Finset (Fin n)).filter (fun u => (∃ a ∈ tops G C, ∃ b : Fin 2,
          side (n := n) C a b = {u} ∧ OrReaches n C (opnd C a b) g) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ Ustar G C ∧ v ∉ wmax G C g ∧ v ∉ D.attach.image cc))
      (by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        obtain ⟨⟨a, ha, b, hs, hr⟩, _⟩ := hu
        have hf : Forced C g a u := Or.inl ⟨b, hs, hr⟩
        have haD := (forced_dom G C hAO hTF g hj a ha u hf).1
        exact Finset.mem_image.mpr ⟨⟨a, haD⟩, Finset.mem_attach _ _, ((hc a haD).2 u hf).symm⟩)
      (by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        obtain ⟨⟨a, ha, b, hs, hr⟩, v, hadj, hU, hW, hK⟩ := hu
        have hf : Forced C g a u := Or.inl ⟨b, hs, hr⟩
        have haD := (forced_dom G C hAO hTF g hj a ha u hf).1
        have hca : c a haD = u := ((hc a haD).2 u hf).symm
        have hstar : s(u, v) ∈ starEdges G C := by
          unfold Ustar at hU
          rw [Finset.mem_sdiff] at hU
          push Not at hU
          exact hU (by rw [SimpleGraph.mem_edgeFinset]; exact hadj)
        obtain ⟨a', ha', p, hp, q, hq, hpq⟩ := star_mem G C _ hstar
        have ha'D : a' ∈ D := star_dom G C a' ha' p hp q hq
        have hca' : c a' ha'D = u := by
          obtain ⟨b', hb'⟩ := (hc a' ha'D).1
          have hin := centre_in C a' (c a' ha'D) p q b' hb' hp hq
          have hmem : c a' ha'D ∈ s(u, v) := by
            rw [hpq]; rcases hin with h | h <;> rw [h] <;> simp
          rcases Sym2.mem_iff.mp hmem with h | h
          · exact h
          · exfalso; apply hK
            exact Finset.mem_image.mpr ⟨⟨a', ha'D⟩, Finset.mem_attach _ _, h⟩
        have hne : a ≠ a' := by
          intro e
          subst e
          apply hW
          have hv : v ∈ side (n := n) C a (1 - b) := by
            rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · fin_cases b
              · simpa [h2] using hq
              · exfalso; simp only [Fin.mk_one, Fin.isValue] at hs; rw [hs] at hq; simp at hq
                rw [h2, hq] at hadj; exact G.irrefl hadj
            · fin_cases b
              · exfalso; simp only [Fin.zero_eta, Fin.isValue] at hs; rw [hs] at hp; simp at hp
                rw [h2, hp] at hadj; exact G.irrefl hadj
              · rw [h2]; simpa using hp
          unfold wmax
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro x hx hxv
          exact top_true G C hAO a ha x b (reach_val C hAO.2.1 x _ g hr hx)
            (orIn_val C hAO.2.1 x _ v hv hxv)
        have sub : ({⟨a, haD⟩, ⟨a', ha'D⟩} : Finset D) ⊆ D.attach.filter fun z => cc z = u := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          simp only [Finset.mem_filter, Finset.mem_attach, true_and]
          rcases hz with rfl | rfl
          · exact hca
          · exact hca'
        have := Finset.card_le_card sub
        rw [Finset.card_pair (by intro e; apply hne; exact congrArg Subtype.val e)] at this
        exact this)
    rw [Finset.card_attach] at hcard
    exact hcard

end PEqualNP.Outside.L_meta_1492

theorem PEqualNP.Outside.L_meta_1492 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    ∃ K : Finset (Fin n), (∀ e ∈ PEqualNP.TopForm.starEdges G C, ∃ v ∈ K, v ∈ e) ∧
      (Finset.univ : Finset (Fin n)).filter (fun u => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ⊆ K ∧
      (Finset.univ : Finset (Fin n)).filter (fun w => ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          2 ≤ (PEqualNP.TopForm.side (n := n) C a b).card ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g ∧
          PEqualNP.TopForm.side (n := n) C a (1 - b) = {w}) ⊆ K ∧
      K.card + ((Finset.univ : Finset (Fin n)).filter (fun u => (∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
          PEqualNP.TopForm.side (n := n) C a b = {u} ∧
          PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) g) ∧
          ∃ v, G.Adj u v ∧ s(u, v) ∉ PEqualNP.TopForm.Ustar G C ∧ v ∉ PEqualNP.TopForm.wmax G C g ∧ v ∉ K)).card ≤
        (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card :=
  PEqualNP.Outside.L_meta_1492.main
