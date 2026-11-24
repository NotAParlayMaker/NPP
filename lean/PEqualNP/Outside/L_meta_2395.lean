import Mathlib

namespace PEqualNP.Outside.L_meta_2395_aux


abbrev V := Fin 13
abbrev incidence (p l : V) : Prop := p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem uniqueLine : ∀ a b l m : V, a ≠ b →
    incidence a l → incidence b l → incidence a m → incidence b m → l = m := by
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem pointAvoidance : ∀ A : Finset V,
    (∀ l : V, (A.filter (fun p => incidence p l)).card ≤ 2) →
    ∀ r : V, ∃ l : V, (∀ p ∈ A, ¬ incidence p l) ∧ ¬ incidence r l := by
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lineAvoidance : ∀ B : Finset V,
    (∀ p : V, (B.filter (fun l => incidence p l)).card ≤ 2) →
    ∀ l : V, ∃ p : V, (∀ w ∈ B, ¬ incidence p w) ∧ ¬ incidence p l := by
  decide +kernel

theorem completion (P W : Finset V)
    (disjoint : ∀ p ∈ P, ∀ w ∈ W, ¬ incidence p w)
    (pointArc : ∀ w : V, (P.filter (fun p => incidence p w)).card ≤ 2)
    (lineArc : ∀ p : V, (W.filter (fun w => incidence p w)).card ≤ 2) :
    ∃ Q : Finset V, P ⊆ Q ∧
      (∀ w ∈ W, ∀ p ∈ Q, ¬ incidence p w) ∧
      (∀ v : V, v ∉ Q → ∃ w : V, (∀ p ∈ Q, ¬ incidence p w) ∧ incidence v w) ∧
      ¬ (∃ w : V, ∀ p ∈ Q, incidence p w) ∧
      ¬ (∃ v : V, ∀ w : V, (∀ p ∈ Q, ¬ incidence p w) → incidence v w) := by
  classical
  let valid (A : Finset V) : Prop := P ⊆ A ∧
    (∀ p ∈ A, ∀ w ∈ W, ¬ incidence p w) ∧
    (∀ w : V, (A.filter (fun p => incidence p w)).card ≤ 2)
  let candidates := Finset.univ.filter valid
  have hP : P ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.Subset.rfl, disjoint, pointArc⟩
  obtain ⟨A, hA, maximum⟩ := Finset.exists_max_image candidates Finset.card ⟨P, hP⟩
  obtain ⟨hPA, hAW, arc⟩ := (Finset.mem_filter.mp hA).2
  have spans : ¬ ∃ l : V, ∀ p ∈ A, incidence p l := by
    rintro ⟨l, hcol⟩
    obtain ⟨v, avoids, outside⟩ := lineAvoidance W lineArc l
    have fresh : v ∉ A := fun hv => outside (hcol _ hv)
    have incArc : ∀ m : V, ((insert v A).filter (fun p => incidence p m)).card ≤ 2 := by
      intro m
      by_cases hv : incidence v m
      · have diff : m ≠ l := by rintro rfl; exact outside hv
        have one : (A.filter (fun p => incidence p m)).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro a ha b hb
          obtain ⟨haA, ham⟩ := Finset.mem_filter.mp ha
          obtain ⟨hbA, hbm⟩ := Finset.mem_filter.mp hb
          by_contra hab
          exact diff (uniqueLine a b m l hab ham hbm (hcol a haA) (hcol b hbA))
        rw [Finset.filter_insert, if_pos hv]
        exact (Finset.card_insert_le _ _).trans (by omega)
      · simpa [Finset.filter_insert, hv] using arc m
    have bigger : insert v A ∈ candidates := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hPA.trans (Finset.subset_insert _ _), ?_, incArc⟩
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact avoids
      · exact hAW p hp
    have contra := maximum _ bigger
    rw [Finset.card_insert_of_notMem fresh] at contra
    omega
  let B := Finset.univ.filter (fun w : V => ∀ p ∈ A, ¬ incidence p w)
  let Q := Finset.univ.filter (fun p : V => ∀ w ∈ B, ¬ incidence p w)
  have memB (w : V) : w ∈ B ↔ ∀ p ∈ A, ¬ incidence p w := by simp [B]
  have memQ (p : V) : p ∈ Q ↔ ∀ w ∈ B, ¬ incidence p w := by simp [Q]
  have hAQ : A ⊆ Q := fun p hp => (memQ p).mpr (fun w hw => (memB w).mp hw p hp)
  have hWB : W ⊆ B := fun w hw => (memB w).mpr (fun p hp => hAW p hp w hw)
  refine ⟨Q, hPA.trans hAQ, fun w hw p hp => (memQ p).mp hp w (hWB hw), ?_, ?_, ?_⟩
  · intro v hv
    have h := mt (memQ v).mpr hv
    push Not at h
    obtain ⟨w, hw, hvw⟩ := h
    exact ⟨w, fun p hp => (memQ p).mp hp w hw, hvw⟩
  · rintro ⟨w, hw⟩
    exact spans ⟨w, fun p hp => hw p (hAQ hp)⟩
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw, hn⟩ := pointAvoidance A arc v
    exact hn (hv w (fun p hp => (memQ p).mp hp w ((memB w).mpr hw)))

end PEqualNP.Outside.L_meta_2395_aux

theorem PEqualNP.Outside.L_meta_2395 : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 x3 : Finset (Fin (13 : ℕ))), (∀ x4 ∈ x2, ∀ x6 ∈ x3, ¬x1 x4 x6) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x2 | x1 x6 x5}.card ≤ (2 : ℕ)) → (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x3 | x1 x6 x7}.card ≤ (2 : ℕ)) → ∃ (x7 : Finset (Fin (13 : ℕ))), x2 ⊆ x7 ∧ (∀ x8 ∈ x3, ∀ x10 ∈ x7, ¬x1 x10 x8) ∧ (∀ x8 ∉ x7, ∃ (x10 : Fin (13 : ℕ)), (∀ x11 ∈ x7, ¬x1 x11 x10) ∧ x1 x8 x10) ∧ (¬∃ (x8 : Fin (13 : ℕ)), ∀ x9 ∈ x7, x1 x9 x8) ∧ ¬∃ (x8 : Fin (13 : ℕ)), ∀ (x9 : Fin (13 : ℕ)), (∀ x10 ∈ x7, ¬x1 x10 x9) → x1 x8 x9 := by
  exact PEqualNP.Outside.L_meta_2395_aux.completion
