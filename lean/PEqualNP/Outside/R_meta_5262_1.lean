import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- A centreless edge either needs both endpoints at a junk gate, or has a singleton witness
-- opposite a vertex in Wmax. Peel each class to its 3-core and count small junk profiles directly.
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_5262_1
    (pairCore : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → 4 ≤ (junk G C).card →
      ∀ F : Finset (Sym2 (Fin n)),
        F ⊆ {e ∈ Ustar G C | (¬∃ u v : Fin n, e = s(u,v) ∧ ∃ h < C.gates.length,
          ∃ b : Fin 2, 2 ≤ (orIn n C (n+h)).card ∧ (∀ w ∈ orIn n C (n+h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v}) ∧ ∃ a ∈ centreless G C, e ∈ gammaE G C a} →
        (∀ w : Fin n, (∃ e ∈ F, w ∈ e) → 3 ≤ (F.filter fun e => w ∈ e).card) →
        (∀ e ∈ F, ∃ u v, e = s(u,v) ∧ ∃ j ∈ junk G C,
          gateVal n C j (pairInput u v) = true ∧ gateVal n C j (pairInput u u) = false ∧
          gateVal n C j (pairInput v v) = false) → F.card ≤ k * (C.size+1))
    (contactCore : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → 4 ≤ (junk G C).card →
      ∀ F : Finset (Sym2 (Fin n)),
        F ⊆ {e ∈ Ustar G C | (¬∃ u v : Fin n, e = s(u,v) ∧ ∃ h < C.gates.length,
          ∃ b : Fin 2, 2 ≤ (orIn n C (n+h)).card ∧ (∀ w ∈ orIn n C (n+h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v}) ∧ ∃ a ∈ centreless G C, e ∈ gammaE G C a} →
        (∀ w : Fin n, (∃ e ∈ F, w ∈ e) → 3 ≤ (F.filter fun e => w ∈ e).card) →
        (∀ e ∈ F, ∃ u v, e = s(u,v) ∧ ∃ j ∈ junk G C,
          gateVal n C j (pairInput u u) = true ∧ v ∈ wmax G C j) → F.card ≤ k * (C.size+1))
    : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  let _ : DecidableEq GateOp := gateOpDecEq
  have reachDef (n : ℕ) (C : Circuit) (w k : ℕ) : OrReaches n C w k ↔
      n ≤ w ∧ k ∈ (orSets n C).getD (w - n) [] := Iff.rfl
  have gateDef (C : Circuit) (j : ℕ) : gateAt C j = C.gates.getD j ⟨.or, []⟩ := rfl
  have orStepDef (n : ℕ) (cs : List (List ℕ)) (g : Gate) : orStep n cs g =
      cs ++ [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) []) else [])] := rfl
  have graphDef {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
      (x : Fin n → Bool) : graphFun K A x =
        (decide (∃ a ∈ A, x a = true) || decide (∃ u v, K.Adj u v ∧ x u = true ∧ x v = true)) := rfl
  have pairDef {n : ℕ} (u v w : Fin n) : pairInput u v w = decide (w = u ∨ w = v) := rfl
  have opndDef (C : Circuit) (j : ℕ) (b : Fin 2) :
      opnd C j b = (gateAt C j).inputs.getD b.val 0 := rfl
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wire_len (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      change (gs.foldl step (step w g)).length = _
      rw [ih]
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega

  have old_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (gs.foldl step (step w g)).getD i false = _
      rw [ih _ (by simp [step]; omega)]
      apply List.getD_append
      exact hi

  have gate_value (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
      (valid : ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < w.length + j) :
      let W := gs.foldl step w
      W.getD (w.length + j) false = (gs.getD j ⟨.or, []⟩).op.eval
        ((gs.getD j ⟨.or, []⟩).inputs.map fun i => W.getD i false) := by
    induction gs using List.reverseRecOn with
    | nil => simp at hj
    | append_singleton gs g ih =>
      have before : ((gs ++ [g]).foldl step w) = step (gs.foldl step w) g := by
        rw [List.foldl_append]; rfl
      rw [List.length_append, List.length_singleton] at hj
      by_cases he : j < gs.length
      · rw [List.getD_append _ _ _ _ he] at valid
        simp only [before, List.getD_append _ _ _ _ he]
        have h₁ : w.length + j < (gs.foldl step w).length := by rw [wire_len]; omega
        have h₂ (i : ℕ) (hi : i ∈ (gs.getD j ⟨.or, []⟩).inputs) :
            (step (gs.foldl step w) g).getD i false = (gs.foldl step w).getD i false := by
          apply List.getD_append
          rw [wire_len]
          have := valid i hi
          omega
        change (step (gs.foldl step w) g).getD (w.length + j) false = _
        rw [show (step (gs.foldl step w) g).getD (w.length + j) false =
          (gs.foldl step w).getD (w.length + j) false from List.getD_append _ _ _ _ h₁,
          List.map_congr_left h₂]
        exact ih he valid
      · have heq : j = gs.length := by omega
        subst j
        simp only [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at valid ⊢
        rw [before]
        have h₁ : w.length + gs.length = (gs.foldl step w).length := (wire_len gs w).symm
        have h₂ (i : ℕ) (hi : i ∈ g.inputs) :
            (step (gs.foldl step w) g).getD i false = (gs.foldl step w).getD i false := by
          apply List.getD_append
          exact (valid i hi).trans_eq h₁
        change (step (gs.foldl step w) g).getD (w.length + gs.length) false = _
        rw [List.map_congr_left h₂, h₁]
        simp [step, List.getD_eq_getElem?_getD]

  have wire_at {n : ℕ} (C : Circuit) (B : ReadsBack n C) (x : Fin n → Bool)
      (j : ℕ) (hj : j < C.gates.length) :
      wireVal n C (n + j) x = (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
    have h := gate_value C.gates (List.ofFn x) j hj (by simpa only [List.length_ofFn, gateDef] using B j hj)
    let W := C.gates.foldl step (List.ofFn x)
    change W.getD (n + j) false = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => W.getD i false)
    simpa only [W, List.length_ofFn, gateDef] using h

  have input_at {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
      wireVal n C i x = x i := by
    unfold wireVal
    change (C.gates.foldl step (List.ofFn x)).getD i false = x i
    rw [old_read _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, i.isLt]

  have or_at {n : ℕ} (C : Circuit) (B : ReadsBack n C) (x : Fin n → Bool)
      (j i : ℕ) (hj : j < C.gates.length) (ho : (gateAt C j).op = .or)
      (hi : i ∈ (gateAt C j).inputs) (ht : wireVal n C i x = true) :
      wireVal n C (n + j) x = true := by
    rw [wire_at C B x j hj, ho]
    change (((gateAt C j).inputs.map fun k => wireVal n C k x).any id) = true
    exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨i, hi, ht⟩, rfl⟩

  have or_length (n : ℕ) (gs : List Gate) :
      (gs.foldl (orStep n) []).length = gs.length := by
    induction gs using List.reverseRecOn with
    | nil => rfl
    | append_singleton gs g ih =>
      rw [List.foldl_append]
      simp [orStepDef, ih]

  have or_parent (n : ℕ) (gs : List Gate) (j t : ℕ) (hj : j < gs.length)
      (ht : t ∈ (gs.foldl (orStep n) []).getD j []) :
      t = j ∨ ((gs.getD j ⟨.or, []⟩).op = .or ∧
        ∃ i ∈ (gs.getD j ⟨.or, []⟩).inputs, n ≤ i ∧ i < n + j ∧
          t ∈ (gs.foldl (orStep n) []).getD (i - n) []) := by
    induction gs using List.reverseRecOn with
    | nil => simp at hj
    | append_singleton gs g ih =>
      let T := gs.foldl (orStep n) []
      have len : T.length = gs.length := or_length n gs
      have htStep : ((gs ++ [g]).foldl (orStep n) []) = orStep n T g := by
        rw [List.foldl_append]; rfl
      have keep (i : ℕ) (h : i < gs.length) : (orStep n T g).getD i [] = T.getD i [] := by
        apply List.getD_append
        rwa [len]
      simp only [List.length_append, List.length_singleton] at hj
      by_cases h : j < gs.length
      · rw [htStep, keep j h] at ht
        rw [List.getD_append _ _ _ _ h]
        rcases ih h ht with same | ⟨hop, i, hi, hn, hb, hm⟩
        · exact Or.inl same
        · refine Or.inr ⟨hop, i, hi, hn, hb, ?_⟩
          rw [htStep, keep _ (by omega)]
          exact hm
      · have e : j = gs.length := by omega
        subst j
        rw [htStep] at ht
        unfold orStep at ht
        rw [List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self] at ht
        simp only [List.getD_cons_zero, List.mem_cons] at ht
        rcases ht with same | fromOr
        · exact Or.inl same
        · have hop : g.op = .or := by
            by_contra bad
            simp [bad] at fromOr
          rw [ite_eq_left hop] at fromOr
          obtain ⟨i, ihf, hm⟩ := List.mem_flatMap.mp fromOr
          obtain ⟨hi, hh⟩ := List.mem_filter.mp ihf
          obtain ⟨hn, hb⟩ := of_decide_eq_true hh
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
          refine Or.inr ⟨hop, i, hi, hn, hb, ?_⟩
          rw [htStep, keep _ (by omega)]
          exact hm

  have follow_or {n : ℕ} (C : Circuit) (B : ReadsBack n C) (x : Fin n → Bool)
      (j : ℕ) (hj : j < C.gates.length) (t : ℕ)
      (reach : OrReaches n C (n + j) t) (ht : wireVal n C (n + t) x = true) :
      wireVal n C (n + j) x = true := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      have hm := reach.2
      rw [Nat.add_sub_cancel_left] at hm
      rcases or_parent n C.gates j t hj hm with same | ⟨hop, i, hi, hn, hb, hmi⟩
      · rwa [same] at ht
      · have eqi : n + (i - n) = i := by omega
        have hp : OrReaches n C (n + (i - n)) t := by
          rw [eqi]
          exact ⟨hn, hmi⟩
        have hval := ih (i - n) (by omega) (by omega) hp
        rw [eqi] at hval
        exact or_at C B x j i hj hop hi hval

  have or_in_true {n : ℕ} (C : Circuit) (B : ReadsBack n C) (x : Fin n → Bool)
      (w : ℕ) (hw : w < n + C.gates.length) (v : Fin n)
      (hv : v ∈ orIn n C w) (ht : x v = true) : wireVal n C w x = true := by
    let _ : DecidableEq GateOp := gateOpDecEq
    rcases (Finset.mem_filter.mp hv).2 with direct | ⟨j, hj, hr, ho, hi⟩
    · rw [← direct, input_at]
      exact ht
    · have atGate : wireVal n C (n + j) x = true := or_at C B x j v.val hj ho hi
        ((input_at C x v).trans ht)
      have eqw : n + (w - n) = w := by have := hr.1; omega
      rw [← eqw] at hr ⊢
      exact follow_or C B x (w - n) (by omega) j hr atGate

  let run {α : Type} (next : List α → Gate → α) (gs : List Gate) : List α :=
    gs.foldl (fun s g => s ++ [next s g]) []

  have run_length {α : Type} (next : List α → Gate → α) (gs : List Gate) :
      (run next gs).length = gs.length := by
    induction gs using List.reverseRecOn with
    | nil => rfl
    | append_singleton gs g ih =>
      unfold run at ih ⊢
      rw [List.foldl_append]
      simp [ih]

  have run_slot {α : Type} (next : List α → Gate → α) (d : α)
      (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
      (run next gs).getD j d = next ((run next gs).take j) (gs.getD j ⟨.or, []⟩) := by
    induction gs using List.reverseRecOn with
    | nil => simp at hj
    | append_singleton gs g ih =>
      have grow : run next (gs ++ [g]) = run next gs ++ [next (run next gs) g] := by
        unfold run
        rw [List.foldl_append]
        rfl
      have len := run_length next gs
      rw [grow]
      by_cases h : j < gs.length
      · have hs : j < (run next gs).length := h.trans_eq len.symm
        rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ h,
          List.take_append_of_le_length (Nat.le_of_lt hs)]
        exact ih h
      · rw [List.length_append, List.length_singleton] at hj
        have eq : j = gs.length := by omega
        subst j
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ le_rfl,
          len, Nat.sub_self, List.getD_cons_zero, List.getD_cons_zero,
          List.take_append_of_le_length (by omega)]
        simp [←len]

  let orEntry (n : ℕ) (s : List (List ℕ)) (g : Gate) : List ℕ :=
    let _ : DecidableEq GateOp := gateOpDecEq
    s.length :: (if g.op = .or then
      (g.inputs.filter fun w => decide (n ≤ w ∧ w < n + s.length)).flatMap
        (fun w => s.getD (w - n) []) else [])

  let coneEntry (n : ℕ) (s : List (List ℕ)) (g : Gate) : List ℕ :=
    (g.inputs.filter fun w => decide (n ≤ w ∧ w < n + s.length)).flatMap
      (fun w => (w - n) :: s.getD (w - n) [])

  have or_entry {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (k : ℕ) :
      OrReaches n C (n + j) k ↔ k = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w k) := by
    let _ : DecidableEq GateOp := gateOpDecEq
    have slot := run_slot (orEntry n) [] C.gates j hj
    let s := run (orEntry n) C.gates
    have len : (s.take j).length = j := by
      simp [s, run_length, Nat.min_eq_left (Nat.le_of_lt hj)]
    change n ≤ n + j ∧ k ∈ s.getD (n + j - n) [] ↔ _
    rw [Nat.add_sub_cancel_left, slot]
    change n ≤ n+j ∧ k ∈ orEntry n (s.take j) (gateAt C j) ↔ _
    simp only [orEntry, len, Nat.le_add_right, true_and, List.mem_cons]
    by_cases hor : (gateAt C j).op = .or
    · simp only [hor, ite_true, true_and, List.mem_flatMap, List.mem_filter,
        decide_eq_true_eq, reachDef]
      constructor
      · rintro (rfl | ⟨w, ⟨hin, hlow, hhigh⟩, hm⟩)
        · exact Or.inl rfl
        · refine Or.inr ⟨w, hin, hlow, hhigh, hlow, ?_⟩
          change k ∈ s.getD (w - n) []
          rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)] at hm
          simpa only [List.getD_eq_getElem?_getD] using hm
      · rintro (rfl | ⟨w, hin, hlow, hhigh, _, hm⟩)
        · exact Or.inl rfl
        · refine Or.inr ⟨w, ⟨hin, hlow, hhigh⟩, ?_⟩
          change k ∈ s.getD (w - n) [] at hm
          rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
          simpa only [List.getD_eq_getElem?_getD] using hm
    · simp [hor]

  have cone_from_pin {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
      (w : ℕ) (hw : w ∈ (gateAt C j).inputs) (hl : n ≤ w) (hh : w < n + j)
      (k : ℕ) (hk : k = w - n ∨ InCone n C k (w - n)) : InCone n C k j := by
    let s := run (coneEntry n) C.gates
    have len : (s.take j).length = j := by
      simp [s, run_length, Nat.min_eq_left (Nat.le_of_lt hj)]
    have slot := run_slot (coneEntry n) [] C.gates j hj
    change k ∈ s.getD j []
    rw [slot]
    change k ∈ coneEntry n (s.take j) (gateAt C j)
    simp only [coneEntry, len, List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
    refine ⟨w, ⟨hw, hl, hh⟩, ?_⟩
    rcases hk with h | h
    · exact Or.inl h
    · right
      change k ∈ s.getD (w - n) [] at h
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
      simpa only [List.getD_eq_getElem?_getD] using h

  have or_path_hits {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (k : ℕ)
      (h : OrReaches n C (n + j) k) : k ≤ j ∧ (k = j ∨ InCone n C k j) := by
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      rcases (or_entry C j hj k).mp h with e | ⟨_, w, hin, hl, hh, reach⟩
      · exact ⟨e.le, Or.inl e⟩
      · have he : n + (w-n) = w := by omega
        have prev := ih (w-n) (by omega) (by omega) (by rwa [he])
        exact ⟨by omega, Or.inr (cone_from_pin C j hj w hin hl hh k prev.2)⟩

  have complete_product_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hf : NoFourCycle G) (S A B : Finset (Fin n))
      (aS : A ⊆ S) (bS : B ⊆ S) (complete : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
      (A ×ˢ B).card ≤ S.card := by
    classical
    rw [Finset.card_product]
    have sides : A.card ≤ 1 ∨ B.card ≤ 1 := by
      by_contra both
      push Not at both
      obtain ⟨a, ha, a', ha', naa⟩ := Finset.one_lt_card.1 both.1
      obtain ⟨b, hb, b', hb', nbb⟩ := Finset.one_lt_card.1 both.2
      have hs : ({b, b'} : Finset (Fin n)) ⊆ (Finset.univ.filter fun t => G.Adj a t ∧ G.Adj a' t) := by
        intro t ht
        rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using ht : t = b ∨ t = b') with rfl | rfl
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, complete a ha _ hb, complete a' ha' _ hb⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, complete a ha _ hb', complete a' ha' _ hb'⟩
      have lo := Finset.card_le_card hs
      have hi := hf a a' naa
      simp [nbb] at lo
      omega
    rcases sides with ha | hb
    · simpa using Nat.mul_le_mul ha (Finset.card_le_card bS)
    · simpa using Nat.mul_le_mul (Finset.card_le_card aS) hb

  have count_profiles {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hf : NoFourCycle G) (S : Finset (Fin n)) {T : Type} [Fintype T] (label : Fin n → T)
      (R : Finset (Sym2 (Fin n)))
      (cert : ∀ e ∈ R, ∃ u ∈ S, ∃ v ∈ S, e = s(u,v) ∧
        ∀ a ∈ S, ∀ b ∈ S, label a = label u → label b = label v → G.Adj a b) :
      R.card ≤ (Fintype.card T * Fintype.card T) * S.card := by
    classical
    let part (t : T) := S.filter (fun v => label v = t)
    let box (p : T × T) : Finset (Sym2 (Fin n)) :=
      if ∀ a ∈ part p.1, ∀ b ∈ part p.2, G.Adj a b then
        (part p.1 ×ˢ part p.2).image (fun ab => s(ab.1, ab.2))
      else ∅
    have all : R ⊆ (Finset.univ : Finset (T × T)).biUnion box := by
      intro e he
      obtain ⟨u, hu, v, hv, rfl, hcomp⟩ := cert e he
      have c : ∀ a ∈ part (label u), ∀ b ∈ part (label v), G.Adj a b := by
        intro a ha b hb
        obtain ⟨ha', ea⟩ := Finset.mem_filter.mp ha
        obtain ⟨hb', eb⟩ := Finset.mem_filter.mp hb
        exact hcomp a ha' b hb' ea eb
      apply Finset.mem_biUnion.mpr
      refine ⟨(label u, label v), Finset.mem_univ _, ?_⟩
      dsimp only [box]
      rw [ite_eq_left c]
      exact Finset.mem_image.mpr ⟨(u,v), Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hu, rfl⟩, Finset.mem_filter.mpr ⟨hv, rfl⟩⟩, rfl⟩
    have budget (p : T × T) : (box p).card ≤ S.card := by
      dsimp only [box]
      split
      · rename_i pcomplete
        exact Finset.card_image_le.trans (complete_product_card G hf S _ _
          (Finset.filter_subset _ _) (Finset.filter_subset _ _) pcomplete)
      · simp
    calc
      R.card ≤ ((Finset.univ : Finset (T × T)).biUnion box).card := Finset.card_le_card all
      _ ≤ ∑ p : T × T, (box p).card := Finset.card_biUnion_le
      _ ≤ ∑ _ : T × T, S.card := Finset.sum_le_sum fun p _ => budget p
      _ = (Fintype.card T * Fintype.card T) * S.card := by simp

  let readInputs (n : ℕ) (C : Circuit) : Finset (Fin n) := by
    classical
    exact Finset.univ.filter fun v => ∃ g ∈ C.gates, v.val ∈ g.inputs

  have readInputs_card {n : ℕ} (C : Circuit) (H : IsAO2 n C) :
      (readInputs n C).card ≤ 2 * C.size := by
    classical
    let pins := C.gates.toFinset.biUnion fun g => g.inputs.toFinset
    have raw : (readInputs n C).card ≤ pins.card := by
      apply Finset.card_le_card_of_injOn Fin.val
      · intro v hv
        obtain ⟨g, hg, hi⟩ := (Finset.mem_filter.mp hv).2
        exact Finset.mem_biUnion.mpr ⟨g, List.mem_toFinset.mpr hg, List.mem_toFinset.mpr hi⟩
      · exact Fin.val_injective.injOn
    have cap : pins.card ≤ C.gates.toFinset.card * 2 := by
      calc
        pins.card ≤ ∑ g ∈ C.gates.toFinset, g.inputs.toFinset.card := Finset.card_biUnion_le
        _ ≤ ∑ _ ∈ C.gates.toFinset, 2 := Finset.sum_le_sum fun g hg =>
          (List.toFinset_card_le _).trans_eq (H.2.2 _ (List.mem_toFinset.mp hg))
        _ = C.gates.toFinset.card * 2 := by simp
    have len : C.gates.toFinset.card ≤ C.size := List.toFinset_card_le _
    omega

  have graph_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    rw [graphDef]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, pairDef, decide_eq_true_eq]
    constructor
    · rintro ⟨p, q, hpq, hp, hq⟩
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact (hpq.ne rfl).elim
      · exact hpq
      · exact hpq.symm
      · exact (hpq.ne rfl).elim
    · intro e
      exact ⟨u, v, e, Or.inl rfl, Or.inr rfl⟩

  let evalStep (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

  have wire_agree_outside (gs : List Gate) (u : ℕ)
      (unused : ∀ g ∈ gs, u ∉ g.inputs) (w w' : List Bool) (hlen : w.length = w'.length)
      (hvals : ∀ i, i ≠ u → w.getD i false = w'.getD i false) :
      ∀ i, i ≠ u → (gs.foldl evalStep w).getD i false = (gs.foldl evalStep w').getD i false := by
    induction gs generalizing w w' with
    | nil => exact hvals
    | cons g gs ih =>
      have eqv : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => w'.getD i false) := by
        apply List.map_congr_left
        intro i hi
        apply hvals
        rintro rfl
        exact unused g (by simp) hi
      have later : ∀ h ∈ gs, u ∉ h.inputs := fun h hh => unused h (by simp [hh])
      change ∀ i, i ≠ u → (gs.foldl evalStep (evalStep w g)).getD i false =
        (gs.foldl evalStep (evalStep w' g)).getD i false
      apply ih later
      · simp [evalStep, hlen]
      · intro i hi
        let bit := g.op.eval (g.inputs.map fun i => w'.getD i false)
        change (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false =
          (w' ++ [bit]).getD i false
        rw [eqv]
        change (w ++ [bit]).getD i false = (w' ++ [bit]).getD i false
        by_cases h : i < w.length
        · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (by omega : i < w'.length)]
          exact hvals i hi
        · rw [List.getD_append_right _ _ _ _ (by omega : w.length ≤ i),
            List.getD_append_right _ _ _ _ (by omega : w'.length ≤ i), hlen]

  have raw_input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
      (C.wires (List.ofFn x)).getD u.val false = x u := by
    have aux (gs : List Gate) (w : List Bool) (h : u.val < w.length) :
        (gs.foldl evalStep w).getD u.val false = w.getD u.val false := by
      induction gs generalizing w with
      | nil => rfl
      | cons g gs ih =>
        change (gs.foldl evalStep (evalStep w g)).getD u.val false = _
        rw [ih _ (by simp [evalStep]; omega)]
        exact List.getD_append _ _ _ _ h
    change (C.gates.foldl evalStep (List.ofFn x)).getD u.val false = _
    rw [aux _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, u.isLt]

  have edge_endpoint_read {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (compute : circuitFun n C = graphFun G ∅) {u v : Fin n}
      (edge : G.Adj u v) : u ∈ readInputs n C := by
    classical
    by_contra hno
    have none : ∀ g ∈ C.gates, u.val ∉ g.inputs := by
      intro g hg hi
      exact hno (Finset.mem_filter.mpr ⟨Finset.mem_univ _, g, hg, hi⟩)
    have output : C.output ≠ u.val := by
      intro hout
      have hx : circuitFun n C (pairInput u u) = true := by
        change (C.wires (List.ofFn (pairInput u u))).getD C.output false = true
        rw [hout, raw_input_value C (pairInput u u) u]
        simp [pairDef]
      rw [compute] at hx
      exact G.ne_of_adj ((graph_pair_iff G u u).mp hx) rfl
    have hv : ∀ i : ℕ, i ≠ u.val →
        (List.ofFn (pairInput u v)).getD i false = (List.ofFn (pairInput v v)).getD i false := by
      intro i hi
      by_cases hn : i < n
      · have fne : (⟨i, hn⟩ : Fin n) ≠ u := fun he => hi (congrArg Fin.val he)
        simp [List.getD_eq_getElem?_getD, hn, pairDef, fne]
      · simp [List.getD_eq_getElem?_getD, hn]
    have wrong : circuitFun n C (pairInput u v) = circuitFun n C (pairInput v v) :=
      wire_agree_outside C.gates u.val none _ _ (by simp) hv _ output
    rw [compute, (graph_pair_iff G u v).mpr edge] at wrong
    exact G.ne_of_adj ((graph_pair_iff G v v).mp wrong.symm) rfl

  let contact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (j : ℕ) (v : Fin n) : Prop :=
    ∃ a ∈ tops G C, ∃ b : Fin 2, v ∈ side C a b ∧
      PEqualNP.CleanedNonEdge.OrReaches n C (opnd C a (1 - b)) j

  have bound_three_profiles {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (H : IsLeastAO G C) (hf : NoFourCycle G) (few : (junk G C).card ≤ 3)
      (E : Finset (Sym2 (Fin n)))
      (cert : ∀ e ∈ E, ∃ u v : Fin n, e = s(u, v) ∧ ∃ j ∈ junk G C,
        contact G C j u ∧ gateVal n C j (pairInput u v) = true)
      (sound : ∀ j : ℕ, ∀ a b : Fin n, contact G C j a →
        gateVal n C j (pairInput a b) = true → G.Adj a b)
      (stable : ∀ j ∈ junk G C, ∀ u v a b : Fin n,
        (∀ k ∈ junk G C, ∀ d : Fin 2, decide (a ∈ side C k d) = decide (u ∈ side C k d)) →
        (∀ k ∈ junk G C, ∀ d : Fin 2, decide (b ∈ side C k d) = decide (v ∈ side C k d)) →
        gateVal n C j (pairInput a b) = gateVal n C j (pairInput u v)) :
      E.card ≤ 98304 * C.size := by
    classical
    let J := junk G C
    let T := (({j : ℕ // j ∈ J} × Fin 2) → Bool) × Bool
    let _ : Fintype T := by unfold T; infer_instance
    let S := readInputs n C
    let label (j : ℕ) (u : Fin n) : T :=
      (fun w => decide (u ∈ side C w.1.val w.2), decide (contact G C j u))
    let group (j : ℕ) := E.filter fun e => ∃ u v : Fin n, e = s(u, v) ∧
      contact G C j u ∧ gateVal n C j (pairInput u v) = true
    have hall : E ⊆ J.biUnion group := by
      intro e he
      obtain ⟨u, v, eq, j, hj, hc, hv⟩ := cert e he
      exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨he, u, v, eq, hc, hv⟩⟩
    have cards : Fintype.card T ≤ 128 := by
      have small : J.card * 2 ≤ 6 := by change (junk G C).card * 2 ≤ 6; omega
      simp only [T, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_coe]
      have powSmall : 2 ^ (J.card * 2) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) small
      norm_num at powSmall ⊢
      omega
    have per (j : ℕ) (hj : j ∈ J) : (group j).card ≤ 16384 * S.card := by
      have rows : ∀ e ∈ group j, ∃ u ∈ S, ∃ v ∈ S, e = s(u, v) ∧
          ∀ a ∈ S, ∀ b ∈ S, label j a = label j u → label j b = label j v → G.Adj a b := by
        intro e he
        obtain ⟨u, v, euv, hu, hv⟩ := (Finset.mem_filter.mp he).2
        have adj := sound j u v hu hv
        refine ⟨u, edge_endpoint_read G C H.2.1 adj, v, edge_endpoint_read G C H.2.1 adj.symm,
          euv, ?_⟩
        intro a _ b _ ha hb
        have ca : contact G C j a := by
          have equality := congrArg Prod.snd ha
          change decide (contact G C j a) = decide (contact G C j u) at equality
          rw [decide_eq_true hu] at equality
          exact of_decide_eq_true equality
        have pa (k : ℕ) (hk : k ∈ J) (d : Fin 2) :
            decide (a ∈ side C k d) = decide (u ∈ side C k d) :=
          congrFun (congrArg Prod.fst ha) (⟨k, hk⟩, d)
        have pb (k : ℕ) (hk : k ∈ J) (d : Fin 2) :
            decide (b ∈ side C k d) = decide (v ∈ side C k d) :=
          congrFun (congrArg Prod.fst hb) (⟨k, hk⟩, d)
        exact sound j a b ca ((stable j hj u v a b pa pb).trans hv)
      have hcount := count_profiles G hf S (label j) (group j) rows
      have q := Nat.mul_le_mul cards cards
      exact hcount.trans (Nat.mul_le_mul_right _ q)
    have hs : S.card ≤ 2 * C.size := readInputs_card C H.1
    calc
      E.card ≤ (J.biUnion group).card := Finset.card_le_card hall
      _ ≤ ∑ j ∈ J, (group j).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ J, 16384 * S.card := Finset.sum_le_sum per
      _ = J.card * (16384 * S.card) := by simp
      _ ≤ 3 * (16384 * (2 * C.size)) := Nat.mul_le_mul few (Nat.mul_le_mul_left _ hs)
      _ = 98304 * C.size := by ring

  have gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _

  have reach_through_or {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
      (hor : (gateAt C j).op = .or) (i : ℕ) (hi : i ∈ (gateAt C j).inputs) (hb : i < n + j)
      (k : ℕ) (reach : OrReaches n C i k) : OrReaches n C (n+j) k :=
    (or_entry C j hj k).mpr (Or.inr ⟨hor, i, hi, reach.1, hb, reach⟩)

  have raw_through_or {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
      (hor : (gateAt C j).op = .or) (i : ℕ) (hi : i ∈ (gateAt C j).inputs) (hb : i < n + j)
      (v : Fin n) (hv : v ∈ orIn n C i) : v ∈ orIn n C (n+j) := by
    let _ : DecidableEq GateOp := gateOpDecEq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Or.inr ?_⟩
    rcases (Finset.mem_filter.mp hv).2 with rfl | ⟨k, hk, hr, hop, pin⟩
    · exact ⟨j, hj, (or_entry C j hj j).mpr (Or.inl rfl), hor, hi⟩
    · exact ⟨k, hk, reach_through_or C j hj hor i hi hb k hr, hop, pin⟩

  have true_trace {n : ℕ} (C : Circuit) (AO : IsAO2 n C) (x : Fin n → Bool) (w : ℕ)
      (hw : w < n + C.gates.length) (hx : wireVal n C w x = true) :
      (∃ v ∈ orIn n C w, x v = true) ∨
      (∃ j < C.gates.length, (gateAt C j).op = .and ∧ OrReaches n C w j ∧ wireVal n C (n+j) x = true) := by
    let _ : DecidableEq GateOp := gateOpDecEq
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases raw : w < n
      · have vr : wireVal n C w x = x ⟨w,raw⟩ := input_at C x ⟨w,raw⟩
        exact Or.inl ⟨⟨w, raw⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩, vr.symm.trans hx⟩
      · let j := w - n
        have wj : n + j = w := by dsimp [j]; omega
        have hj : j < C.gates.length := by omega
        rw [← wj] at hx ⊢
        rcases AO.1 _ (gate_mem C j hj) with hAnd | hOr
        · exact Or.inr ⟨j, hj, hAnd, (or_entry C j hj j).mpr (Or.inl rfl), hx⟩
        · rw [wire_at C AO.2.1 x j hj, hOr] at hx
          change (((gateAt C j).inputs.map fun i => wireVal n C i x).any id) = true at hx
          obtain ⟨_, hb, hbTrue⟩ := List.any_eq_true.mp hx
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
          have back : i < n+j := AO.2.1 j hj i hi
          rcases ih i (by omega) (by omega) hbTrue with ⟨v, hm, ht⟩ | ⟨k, hk, hop, hr, ht⟩
          · exact Or.inl ⟨v, raw_through_or C j hj hOr i hi back v hm, ht⟩
          · exact Or.inr ⟨k, hk, hop, reach_through_or C j hj hOr i hi back k hr, ht⟩

  have reached_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (AO : IsAO2 n C) (top : TopForm G C)
      (j : ℕ) (hj : j < C.gates.length) (jand : (gateAt C j).op = .and)
      (i : ℕ) (hi : i ∈ (gateAt C j).inputs)
      (k : ℕ) (hk : k < C.gates.length) (kand : (gateAt C k).op = .and)
      (reach : OrReaches n C i k) : k < j ∧ k ∈ junk G C := by
    let _ : DecidableEq GateOp := gateOpDecEq
    have back := AO.2.1 j hj i hi
    have hiLo := reach.1
    have conv : n + (i - n) = i := by omega
    have hp := or_path_hits C (i-n) (by omega) k (by rwa [conv])
    have cone := cone_from_pin C j hj i hi hiLo back k hp.2
    have kl : k < j := by omega
    have nb : ¬ BelowF G C k := fun b => top k hk j hj kand b jand cone
    have bad : ∃ x, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
      by_contra none
      apply nb
      intro x hx
      by_contra hf
      exact none ⟨x, hx, Bool.eq_false_of_not_eq_true hf⟩
    obtain ⟨x, hx, hfalse⟩ := bad
    exact ⟨kl, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, kand, hk, x, hx, hfalse⟩⟩

  have profile_stable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (AO : IsAO2 n C) (top : TopForm G C)
      (u v a b : Fin n)
      (pa : ∀ k ∈ junk G C, ∀ d : Fin 2, decide (a ∈ side C k d) = decide (u ∈ side C k d))
      (pb : ∀ k ∈ junk G C, ∀ d : Fin 2, decide (b ∈ side C k d) = decide (v ∈ side C k d)) :
      ∀ j ∈ junk G C, gateVal n C j (pairInput a b) = gateVal n C j (pairInput u v) := by
    let _ : DecidableEq GateOp := gateOpDecEq
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      obtain ⟨jRange, jOp, _⟩ := Finset.mem_filter.mp hj
      have jLt : j < C.gates.length := Finset.mem_range.mp jRange
      obtain ⟨r, s, pins⟩ := List.length_eq_two.mp (AO.2.2 _ (gate_mem C j jLt))
      have step (d : Fin 2) (x₀ x₁ y₀ y₁ : Fin n)
          (h₀ : decide (x₀ ∈ side C j d) = decide (y₀ ∈ side C j d))
          (h₁ : decide (x₁ ∈ side C j d) = decide (y₁ ∈ side C j d))
          (prev : ∀ k < j, k ∈ junk G C →
            gateVal n C k (pairInput x₀ x₁) = gateVal n C k (pairInput y₀ y₁))
          (h : wireVal n C (opnd C j d) (pairInput x₀ x₁) = true) :
          wireVal n C (opnd C j d) (pairInput y₀ y₁) = true := by
        let i := opnd C j d
        have mem : i ∈ (gateAt C j).inputs := by
          fin_cases d <;> simp [i, opndDef, pins]
        have back := AO.2.1 j jLt i mem
        rcases true_trace C AO (pairInput x₀ x₁) i (by omega) h with
          ⟨t, ht, hv⟩ | ⟨k, hk, hop, hr, hv⟩
        · have htt : t = x₀ ∨ t = x₁ := of_decide_eq_true hv
          rcases htt with rfl | rfl
          · have hy : y₀ ∈ orIn n C i := of_decide_eq_true (h₀.symm.trans (decide_eq_true ht))
            exact or_in_true C AO.2.1 _ i (by omega) y₀ hy (by simp [pairDef])
          · have hy : y₁ ∈ orIn n C i := of_decide_eq_true (h₁.symm.trans (decide_eq_true ht))
            exact or_in_true C AO.2.1 _ i (by omega) y₁ hy (by simp [pairDef])
        · obtain ⟨kj, kJ⟩ := reached_dirty G C AO top j jLt jOp i mem k hk hop hr
          have value : wireVal n C (n+k) (pairInput y₀ y₁) = true := (prev k kj kJ).symm.trans hv
          have hn := hr.1
          have eq : n + (i-n) = i := by omega
          change wireVal n C i (pairInput y₀ y₁) = true
          rw [←eq]
          exact follow_or C AO.2.1 _ (i-n) (by omega) k (by rwa [eq]) value
      have each (d : Fin 2) : wireVal n C (opnd C j d) (pairInput a b) =
          wireVal n C (opnd C j d) (pairInput u v) := by
        rw [Bool.eq_iff_iff]
        exact ⟨step d a b u v (pa j hj d) (pb j hj d) ih,
          step d u v a b (pa j hj d).symm (pb j hj d).symm (fun k hk hJ => (ih k hk hJ).symm)⟩
      have eq₀ : opnd C j 0 = r := by simp [opndDef, pins]
      have eq₁ : opnd C j 1 = s := by simp [opndDef, pins]
      have h0 := each 0
      have h1 := each 1
      rw [eq₀] at h0
      rw [eq₁] at h1
      change wireVal n C (n+j) (pairInput a b) = wireVal n C (n+j) (pairInput u v)
      simp only [wire_at C AO.2.1 _ j jLt, jOp, pins, List.map_cons, List.map_nil, h0, h1]

  have contact_sound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (AO : IsAO2 n C) (j : ℕ) (u v : Fin n)
      (hc : contact G C j u) (hv : gateVal n C j (pairInput u v) = true) : G.Adj u v := by
    let _ : DecidableEq GateOp := gateOpDecEq
    obtain ⟨t, ht, d, hu, hr⟩ := hc
    obtain ⟨tr, op, below⟩ := Finset.mem_filter.mp ht
    have tl : t < C.gates.length := Finset.mem_range.mp tr
    obtain ⟨r, s, pins⟩ := List.length_eq_two.mp (AO.2.2 _ (gate_mem C t tl))
    have bnd (q : Fin 2) : opnd C t q < n+t := by
      apply AO.2.1 t tl
      fin_cases q <;> simp [opndDef, pins]
    let x := pairInput u v
    let w := opnd C t (1-d)
    have left : wireVal n C (opnd C t d) x = true :=
      or_in_true C AO.2.1 x _ (by have := bnd d; omega) u hu (by simp [x, pairDef])
    have right : wireVal n C w x = true := by
      have hw : n ≤ w := hr.1
      have eq : n + (w-n) = w := by omega
      have lw : w < n+t := bnd (1-d)
      rw [←eq]
      exact follow_or C AO.2.1 x (w-n) (by omega) j (by rwa [eq]) hv
    apply (graph_pair_iff G u v).mp
    apply below x
    change wireVal n C (n+t) x = true
    rw [wire_at C AO.2.1 x t tl, op, pins]
    fin_cases d <;> simp [w, opndDef, pins] at left right ⊢ <;> simp [left, right] <;> rfl

  have no_four {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (girth : ∀ a : Fin n, ∀ p : G.Walk a a, p.IsCycle → 5 ≤ p.length) : NoFourCycle G := by
    intro a b ab
    by_contra t
    have two := Nat.lt_of_not_ge t
    obtain ⟨u, hu, v, hv, uv⟩ := Finset.one_lt_card.mp two
    obtain ⟨_, au, bu⟩ := Finset.mem_filter.mp hu
    obtain ⟨_, av, bv⟩ := Finset.mem_filter.mp hv
    let p := SimpleGraph.Walk.cons au (.cons bu.symm (.cons bv (.cons av.symm .nil)))
    have cyc : p.IsCycle := by
      dsimp [p]
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      constructor
      · simp [SimpleGraph.Walk.cons_isPath_iff, ab.symm, uv, au.ne.symm, bu.ne.symm, av.ne.symm, bv.ne]
      · simp [ab, uv, au.ne, au.ne.symm, bu.ne.symm, av.ne]
    have bad := girth a p cyc
    simp [p] at bad

  have bounded_three_contacts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (H : IsLeastAO G C) (top : TopForm G C) (hf : NoFourCycle G)
      (few : (junk G C).card ≤ 3) (E : Finset (Sym2 (Fin n)))
      (cert : ∀ e ∈ E, ∃ u v : Fin n, e = s(u, v) ∧ ∃ j ∈ junk G C,
        contact G C j u ∧ gateVal n C j (pairInput u v) = true) :
      E.card ≤ 98304 * C.size :=
    bound_three_profiles G C H hf few E cert (contact_sound G C H.1)
      (fun j hj u v a b ha hb => profile_stable G C H.1 top u v a b ha hb j hj)
  have boundedThreeCentreless {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (least : IsLeastAO G C) (top : TopForm G C)
      (girth : ∀ v (p : G.Walk v v), p.IsCycle → 5 ≤ p.length)
      (few : (junk G C).card ≤ 3) (E : Finset (Sym2 (Fin n)))
      (cert : ∀ e ∈ E, ∃ a ∈ centreless G C, e ∈ gammaE G C a) :
      E.card ≤ 106496 * C.size := by
    classical
    let _ : DecidableEq GateOp := gateOpDecEq
    let contactCase (e : Sym2 (Fin n)) : Prop :=
      ∃ u v : Fin n, e = s(u,v) ∧ ∃ j ∈ junk G C,
        contact G C j u ∧ gateVal n C j (pairInput u v) = true
    let Eraw := E.filter contactCase
    let Ejunk := E \ Eraw
    have hraw : Eraw.card ≤ 98304 * C.size :=
      bounded_three_contacts G C least top (no_four G girth) few Eraw
        (fun e he => (Finset.mem_filter.mp he).2)
    let J := junk G C
    let T := ({j : ℕ // j ∈ J} × Fin 2) → Bool
    let _ : Fintype T := by unfold T; infer_instance
    let label (u : Fin n) : T := fun p => decide (u ∈ side C p.1.val p.2)
    let S := readInputs n C
    have cards : Fintype.card T ≤ 64 := by
      have small : J.card * 2 ≤ 6 := by change (junk G C).card * 2 ≤ 6; omega
      simp only [T, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, Fintype.card_coe]
      exact Nat.pow_le_pow_right (by decide) small
    have hjunk : Ejunk.card ≤ (Fintype.card T * Fintype.card T) * S.card := by
      apply count_profiles G (no_four G girth) S label Ejunk
      intro e he
      obtain ⟨heE, heRaw⟩ := Finset.mem_sdiff.mp he
      obtain ⟨t, ht, hcarry⟩ := cert e heE
      obtain ⟨tTop, tEmpty⟩ := Finset.mem_filter.mp ht
      obtain ⟨tRange, tAnd, tBelow⟩ := Finset.mem_filter.mp tTop
      have tl := Finset.mem_range.mp tRange
      obtain ⟨edge, u, v, rfl, yes⟩ := Finset.mem_filter.mp hcarry
      have adj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp edge
      refine ⟨u, edge_endpoint_read G C least.2.1 adj,
        v, edge_endpoint_read G C least.2.1 adj.symm, rfl, ?_⟩
      obtain ⟨r, s, pins⟩ := List.length_eq_two.mp (least.1.2.2 _ (gate_mem C t tl))
      have pinMem (d : Fin 2) : opnd C t d ∈ (gateAt C t).inputs := by
        fin_cases d <;> simp [opndDef, pins]
      have eqAnd (x : Fin n → Bool) : gateVal n C t x =
          (wireVal n C (opnd C t 0) x && wireVal n C (opnd C t 1) x) := by
        have andDef (l : List Bool) : GateOp.eval .and l = l.all id := rfl
        change wireVal n C (n+t) x = _
        rw [wire_at C least.1.2.1 x t tl, tAnd, pins, andDef]
        simp [opndDef, pins]
      have traces (d : Fin 2) :
          (∃ w ∈ side C t d, pairInput u v w = true) ∨
          (∃ j ∈ junk G C, OrReaches n C (opnd C t d) j ∧
            gateVal n C j (pairInput u v) = true) := by
        rw [eqAnd, Bool.and_eq_true] at yes
        have y : wireVal n C (opnd C t d) (pairInput u v) = true := by
          fin_cases d
          · exact yes.1
          · exact yes.2
        have back := least.1.2.1 t tl _ (pinMem d)
        rcases true_trace C least.1 (pairInput u v) (opnd C t d) (by omega) y with
          ⟨w, hw, hy⟩ | ⟨j, jl, jAnd, path, hy⟩
        · exact Or.inl ⟨w, hw, hy⟩
        · exact Or.inr ⟨j, (reached_dirty G C least.1 top t tl tAnd _ (pinMem d)
            j jl jAnd path).2, path, hy⟩
      have noRaw (d : Fin 2) (w : Fin n) (wh : w ∈ side C t d)
          (wy : pairInput u v w = true) (j : ℕ) (hj : j ∈ junk G C)
          (path : OrReaches n C (opnd C t (1-d)) j)
          (jy : gateVal n C j (pairInput u v) = true) : False := by
        have ends : w = u ∨ w = v := of_decide_eq_true wy
        apply heRaw
        apply Finset.mem_filter.mpr
        refine ⟨heE, ?_⟩
        rcases ends with h | h
        · exact ⟨u, v, rfl, j, hj, ⟨t, tTop, d, h ▸ wh, path⟩, jy⟩
        · have swap : pairInput v u = pairInput u v := by
            funext i
            simp only [pairDef, or_comm]
          exact ⟨v, u, Sym2.eq_swap, j, hj, ⟨t, tTop, d, h ▸ wh, path⟩, by rwa [swap]⟩
      obtain ⟨j, hj, jPath, jYes⟩ : ∃ j ∈ junk G C, OrReaches n C (opnd C t 0) j ∧
          gateVal n C j (pairInput u v) = true := by
        rcases traces 0 with ⟨w, wh, wy⟩ | h
        · rcases traces 1 with ⟨z, zh, _⟩ | ⟨j, hj, path, jy⟩
          · rcases tEmpty with h | h
            · simp only [h, Finset.notMem_empty] at wh
            · simp only [h, Finset.notMem_empty] at zh
          · exact (noRaw 0 w wh wy j hj (by simpa using path) jy).elim
        · exact h
      obtain ⟨k, hk, kPath, kYes⟩ : ∃ k ∈ junk G C, OrReaches n C (opnd C t 1) k ∧
          gateVal n C k (pairInput u v) = true := by
        rcases traces 1 with ⟨w, wh, wy⟩ | h
        · exact (noRaw 1 w wh wy j hj (by simpa using jPath) jYes).elim
        · exact h
      intro a _ b _ ha hb
      have same (q z : Fin n) (h : label q = label z) (i : ℕ)
          (ih : i ∈ junk G C) (d : Fin 2) :
          decide (q ∈ side C i d) = decide (z ∈ side C i d) :=
        congrFun h (⟨i, ih⟩, d)
      have stable := profile_stable G C least.1 top u v a b (same a u ha) (same b v hb)
      have follow (d : Fin 2) (i : ℕ) (path : OrReaches n C (opnd C t d) i)
          (h : gateVal n C i (pairInput a b) = true) :
          wireVal n C (opnd C t d) (pairInput a b) = true := by
        have hn := path.1
        have back := least.1.2.1 t tl _ (pinMem d)
        have wEq : n + (opnd C t d - n) = opnd C t d := by omega
        rw [← wEq]
        exact follow_or C least.1.2.1 (pairInput a b) _ (by omega) i (by rwa [wEq]) h
      apply (graph_pair_iff G a b).mp
      apply tBelow
      rw [eqAnd, Bool.and_eq_true]
      exact ⟨follow 0 j jPath ((stable j hj).trans jYes),
        follow 1 k kPath ((stable k hk).trans kYes)⟩
    have hjunk' : Ejunk.card ≤ 8192 * C.size := by
      have hsize : S.card ≤ 2 * C.size := readInputs_card C least.1
      calc
        Ejunk.card ≤ (Fintype.card T * Fintype.card T) * S.card := hjunk
        _ ≤ (64 * 64) * (2 * C.size) := Nat.mul_le_mul (Nat.mul_le_mul cards cards) hsize
        _ = 8192 * C.size := by omega
    have hE : E.card = Ejunk.card + Eraw.card := by
      have hh := Finset.card_sdiff_add_card_eq_card
        (Finset.filter_subset contactCase E)
      exact hh.symm
    rw [hE]
    omega
  let support {n : ℕ} (F : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
    Finset.univ.filter fun w => ∃ e ∈ F, w ∈ e
  have peel {n : ℕ} (H : Finset (Sym2 (Fin n))) (cap : ℕ)
      (core : ∀ K ⊆ H, (∀ w : Fin n, (∃ e ∈ K, w ∈ e) →
        3 ≤ (K.filter fun e => w ∈ e).card) → K.card ≤ cap) :
      H.card ≤ 2 * (support H).card + cap := by
    classical
    induction H using Finset.strongInductionOn with
    | _ H ih =>
      by_cases dense : ∀ w : Fin n, (∃ e ∈ H, w ∈ e) → 3 ≤ (H.filter fun e => w ∈ e).card
      · exact (core H (fun _ h => h) dense).trans (by omega)
      · push Not at dense
        obtain ⟨w, ⟨e,he,hw⟩, low⟩ := dense
        let K := H.filter fun e => w ∉ e
        have sub : K ⊆ H := Finset.filter_subset _ _
        have miss : e ∉ K := fun h => (Finset.mem_filter.mp h).2 hw
        have strict : K ⊂ H := Finset.ssubset_iff_subset_ne.mpr ⟨sub, fun h => miss (h ▸ he)⟩
        have sup : support K ⊆ support H := by
          intro v hv
          obtain ⟨e',hK,hv'⟩ := (Finset.mem_filter.mp hv).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e',sub hK,hv'⟩
        have win : w ∈ support H := Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,he,hw⟩
        have wout : w ∉ support K := by
          intro h
          obtain ⟨e',hK,hv'⟩ := (Finset.mem_filter.mp h).2
          exact (Finset.mem_filter.mp hK).2 hv'
        have fewer := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨sup, fun h => wout (h ▸ win)⟩)
        have bound := ih K strict (fun L hL => core L (fun _ h => sub (hL h)))
        have sum : (H.filter fun e => w ∈ e).card + K.card = H.card :=
          Finset.card_filter_add_card_filter_not (s := H) _
        omega
  have eval_preserves_true (g : Gate) (basis : g.op = .and ∨ g.op = .or)
      (a b : ℕ → Bool) (pointwise : ∀ i, a i = true → b i = true)
      (yes : g.op.eval (g.inputs.map a) = true) : g.op.eval (g.inputs.map b) = true := by
    rcases basis with hop | hop
    · rw [hop] at yes ⊢
      change (g.inputs.map a).all id = true at yes
      change (g.inputs.map b).all id = true
      apply List.all_eq_true.mpr
      intro t ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact pointwise i (List.all_eq_true.mp yes _ (List.mem_map.mpr ⟨i,hi,rfl⟩))
    · rw [hop] at yes ⊢
      change (g.inputs.map a).any id = true at yes
      change (g.inputs.map b).any id = true
      obtain ⟨t, ht, htTrue⟩ := List.any_eq_true.mp yes
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact List.any_eq_true.mpr ⟨b i, List.mem_map.mpr ⟨i,hi,rfl⟩, pointwise i htTrue⟩

  have run_preserves_true (gs : List Gate)
      (basis : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (a b : List Bool) (len : a.length = b.length)
      (h : ∀ i, a.getD i false = true → b.getD i false = true) :
      ∀ i, (gs.foldl step a).getD i false = true → (gs.foldl step b).getD i false = true := by
    induction gs generalizing a b with
    | nil => exact h
    | cons g gs ih =>
      have basis_g := basis g (by simp)
      have basis_tail : ∀ z ∈ gs, z.op = .and ∨ z.op = .or := fun z hz => basis z (by simp [hz])
      change ∀ i, (gs.foldl step (step a g)).getD i false = true →
        (gs.foldl step (step b g)).getD i false = true
      apply ih basis_tail
      · simp [step, len]
      · intro i hi
        by_cases hs : i < a.length
        · have ht : i < b.length := by omega
          change (a ++ [_]).getD i false = true at hi
          rw [List.getD_append _ _ _ _ hs] at hi
          change (b ++ [_]).getD i false = true
          rw [List.getD_append _ _ _ _ ht]
          exact h i hi
        · change (a ++ [_]).getD i false = true at hi
          change (b ++ [_]).getD i false = true
          rw [List.getD_append_right _ _ _ _ (by omega : a.length ≤ i)] at hi
          rw [List.getD_append_right _ _ _ _ (by omega : b.length ≤ i), ←len]
          by_cases eq : i = a.length
          · simp only [eq, Nat.sub_self, List.getD_cons_zero] at hi ⊢
            exact eval_preserves_true g basis_g (fun p => a.getD p false) (fun p => b.getD p false) h hi
          · have positive : 0 < i - a.length := by omega
            rw [List.getD_eq_default _ _ (by simp; omega)] at hi
            contradiction

  have wire_preserves_true {n : ℕ} (C : Circuit) (basis : AndOrOnly C)
      (a b : Fin n → Bool) (pointwise : ∀ j, a j = true → b j = true) (w : ℕ) :
      wireVal n C w a = true → wireVal n C w b = true := by
    apply run_preserves_true C.gates basis (List.ofFn a) (List.ofFn b) (by simp) _ w
    intro i hi
    by_cases h : i < n
    · have aTrue : a ⟨i,h⟩ = true := by simpa [List.getD_eq_getElem?_getD, h] using hi
      simpa [List.getD_eq_getElem?_getD, h] using pointwise ⟨i,h⟩ aTrue
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      contradiction

  let joint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (e : Sym2 (Fin n)) : Prop := ∃ u v, e = s(u,v) ∧ ∃ j ∈ junk G C,
        gateVal n C j (pairInput u v) = true ∧ gateVal n C j (pairInput u u) = false ∧
        gateVal n C j (pairInput v v) = false
  let contactOne {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (e : Sym2 (Fin n)) : Prop := ∃ u v, e = s(u,v) ∧ ∃ j ∈ junk G C,
        gateVal n C j (pairInput u u) = true ∧ v ∈ wmax G C j
  have classify {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
      (AO : IsAO2 n C) (top : TopForm G C) (e : Sym2 (Fin n))
      (ht : ∃ t ∈ centreless G C, e ∈ gammaE G C t) : joint G C e ∨ contactOne G C e := by
    classical
    obtain ⟨t, ht, cover⟩ := ht
    obtain ⟨htop, empty⟩ := Finset.mem_filter.mp ht
    obtain ⟨range, andGate, below⟩ := Finset.mem_filter.mp htop
    have tl := Finset.mem_range.mp range
    obtain ⟨_,u,v,rfl,yes⟩ := Finset.mem_filter.mp cover
    by_cases isJoint : joint G C s(u,v)
    · exact Or.inl isJoint
    right
    obtain ⟨r,s,pins⟩ := List.length_eq_two.mp (AO.2.2 _ (gate_mem C t tl))
    have pinMem (d : Fin 2) : opnd C t d ∈ (gateAt C t).inputs := by
      fin_cases d <;> simp [opndDef, pins]
    have pinBound (d : Fin 2) : opnd C t d < n + C.gates.length := by
      have := AO.2.1 t tl _ (pinMem d)
      omega
    let V (d : Fin 2) (x : Fin n → Bool) := wireVal n C (opnd C t d) x
    have eqAnd (d : Fin 2) (x : Fin n → Bool) : gateVal n C t x = (V d x && V (1-d) x) := by
      have andDef (l : List Bool) : GateOp.eval .and l = l.all id := rfl
      change wireVal n C (n+t) x = _
      rw [wire_at C AO.2.1 x t tl, andGate, pins, andDef]
      fin_cases d <;> simp [V, opndDef, pins, Bool.and_comm]
    have trace (d : Fin 2) (x : Fin n → Bool) (hx : V d x = true) :
        (∃ w ∈ side C t d, x w = true) ∨
        ∃ j ∈ junk G C, OrReaches n C (opnd C t d) j ∧ gateVal n C j x = true := by
      rcases true_trace C AO x _ (pinBound d) hx with h | ⟨j,jl,ja,path,jy⟩
      · exact Or.inl h
      · exact Or.inr ⟨j,(reached_dirty G C AO top t tl andGate _ (pinMem d) j jl ja path).2,path,jy⟩
    have carry (d : Fin 2) (j : ℕ) (path : OrReaches n C (opnd C t d) j)
        (x : Fin n → Bool) (jy : gateVal n C j x = true) : V d x = true := by
      have hn := path.1
      have hb := pinBound d
      have he : n + (opnd C t d - n) = opnd C t d := by omega
      change wireVal n C (opnd C t d) x = true
      rw [← he]
      exact follow_or C AO.2.1 x _ (by omega) j (by rwa [he]) jy
    have one (d : Fin 2) : V d (pairInput u u) = true ∨ V d (pairInput v v) = true := by
      by_contra none
      have vals := (eqAnd d _).symm.trans yes
      rw [Bool.and_eq_true] at vals
      have val := vals.1
      rcases trace d _ val with ⟨w,wh,wy⟩ | ⟨j,hj,path,jy⟩
      · have ends : w = u ∨ w = v := of_decide_eq_true wy
        rcases ends with rfl | rfl
        · exact none (Or.inl (or_in_true C AO.2.1 _ _ (pinBound d) _ wh (by simp [pairDef])))
        · exact none (Or.inr (or_in_true C AO.2.1 _ _ (pinBound d) _ wh (by simp [pairDef])))
      · exact isJoint ⟨u,v,rfl,j,hj,jy,
          Bool.eq_false_of_not_eq_true (fun h => none (Or.inl (carry d j path _ h))),
          Bool.eq_false_of_not_eq_true (fun h => none (Or.inr (carry d j path _ h)))⟩
    obtain ⟨d,ed⟩ : ∃ d : Fin 2, side (n:=n) C t d = ∅ := by
      rcases empty with h | h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
    have split (w : Fin n) (h₁ : V d (pairInput w w) = true)
        (h₂ : V (1-d) (pairInput w w) = true) : False :=
      ((graph_pair_iff G w w).mp (below _ ((eqAnd d _).trans
        (by rw [h₁,h₂]; rfl)))).ne rfl
    have combine (a b : Fin n) (ab : s(u,v) = s(a,b))
        (ha : V d (pairInput a a) = true) (hb : V (1-d) (pairInput b b) = true) :
        contactOne G C s(u,v) := by
      rcases trace d _ ha with ⟨w,wh,_⟩ | ⟨j,hj,path,jy⟩
      · rw [ed] at wh
        exact (Finset.notMem_empty w wh).elim
      · refine ⟨a,b,ab,j,hj,jy,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
        intro x jx bx
        apply below x
        rw [eqAnd d, Bool.and_eq_true]
        refine ⟨carry d j path x jx, wire_preserves_true C AO.1 _ x ?_ _ hb⟩
        intro i hi
        have h : i = b ∨ i = b := of_decide_eq_true hi
        exact h.elim (fun e => e ▸ bx) (fun e => e ▸ bx)
    rcases one d with hu | hv
    · rcases one (1-d) with h | h
      · exact (split u hu h).elim
      · exact combine u v rfl hu h
    · rcases one (1-d) with h | h
      · exact combine v u Sym2.eq_swap hv h
      · exact (split v hv h).elim
  obtain ⟨kJoint,hJoint⟩ := pairCore
  obtain ⟨kOne,hOne⟩ := contactCore
  refine ⟨106504 + kJoint + kOne, ?_⟩
  intro n G inst girth nonempty C least top
  let E := {e ∈ Ustar G C | (¬∃ u v : Fin n, e = s(u,v) ∧ ∃ h < C.gates.length,
    ∃ b : Fin 2, 2 ≤ (orIn n C (n+h)).card ∧ (∀ w ∈ orIn n C (n+h), G.Adj u w) ∧
    orIn n C (opnd C h b) = {v}) ∧ ∃ a ∈ centreless G C, e ∈ gammaE G C a}
  change E.card ≤ _
  have cert (e) (he : e ∈ E) : ∃ a ∈ centreless G C, e ∈ gammaE G C a :=
    (Finset.mem_filter.mp he).2.2
  by_cases few : (junk G C).card ≤ 3
  · have hb := boundedThreeCentreless G C least top girth few E cert
    calc
      E.card ≤ 106496 * C.size := hb
      _ ≤ (106504 + kJoint + kOne) * (C.size + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
  have many : 4 ≤ (junk G C).card := by omega
  let J := E.filter (joint G C)
  let S := E \ J
  have jsub : J ⊆ E := Finset.filter_subset _ _
  have ssub : S ⊆ E := Finset.sdiff_subset
  have endpoints (F : Finset (Sym2 (Fin n))) (sub : F ⊆ E) :
      (support F).card ≤ 2*C.size := by
    apply le_trans (Finset.card_le_card (show support F ⊆ readInputs n C from ?_))
      (readInputs_card C least.1)
    intro w hw
    obtain ⟨e,he,we⟩ := (Finset.mem_filter.mp hw).2
    obtain ⟨a,_,ga⟩ := cert e (sub he)
    obtain ⟨eg,u,v,rfl,_⟩ := Finset.mem_filter.mp ga
    have adj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp eg
    rcases Sym2.mem_iff.mp we with rfl | rfl
    · exact edge_endpoint_read G C least.2.1 adj
    · exact edge_endpoint_read G C least.2.1 adj.symm
  have jb := peel J (kJoint * (C.size+1)) (by
    intro K hK core
    apply hJoint n G girth nonempty C least top many K
    · exact fun _ he => jsub (hK he)
    · exact core
    · exact fun _ he => (Finset.mem_filter.mp (hK he)).2)
  have sb := peel S (kOne * (C.size+1)) (by
    intro K hK core
    apply hOne n G girth nonempty C least top many K
    · exact fun _ he => ssub (hK he)
    · exact core
    · intro e he
      obtain ⟨inE,notJ⟩ := Finset.mem_sdiff.mp (hK he)
      exact (classify G C least.1 top e (cert e inE)).resolve_left
        (fun h => notJ (Finset.mem_filter.mpr ⟨inE,h⟩)))
  have sum : S.card + J.card = E.card := Finset.card_sdiff_add_card_eq_card jsub
  have hj := endpoints J jsub
  have hs := endpoints S ssub
  rw [Nat.add_mul, Nat.add_mul]
  omega
