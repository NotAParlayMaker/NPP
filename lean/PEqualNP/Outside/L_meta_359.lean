import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PEqualNP.Outside.L_meta_359_aux

private def netEdges : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)]

private lemma ind_singleton (u : Fin 6) :
    ∀ f ∈ netEdges, ¬ (f.1 ∈ ({u} : Finset (Fin 6)) ∧ f.2 ∈ ({u} : Finset (Fin 6))) := by
  intro f hf ⟨h1, h2⟩
  rw [Finset.mem_singleton] at h1 h2
  have heq : f.1 = f.2 := h1.trans h2.symm
  simp only [netEdges, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd heq (by decide)

private lemma filter_cons_sum (a : Fin 6 × Fin 6) (l : List (Fin 6 × Fin 6))
    (p : Fin 6 × Fin 6 → Bool) (c : Fin 6 × Fin 6 → ℚ) :
    (((a :: l).filter p).map c).sum = (if p a then c a else 0) + ((l.filter p).map c).sum := by
  cases hp : p a <;> simp [List.filter_cons, hp]

private lemma filter_sum_eq (p : Fin 6 × Fin 6 → Bool) (c : Fin 6 × Fin 6 → ℚ) :
    ((netEdges.filter p).map c).sum =
      (if p (0, 1) then c (0, 1) else 0) +
      (if p (0, 2) then c (0, 2) else 0) +
      (if p (1, 2) then c (1, 2) else 0) +
      (if p (0, 3) then c (0, 3) else 0) +
      (if p (1, 4) then c (1, 4) else 0) +
      (if p (2, 5) then c (2, 5) else 0) := by
  simp only [netEdges, filter_cons_sum, List.filter_nil, List.map_nil, List.sum_nil]
  linarith

private lemma main_net
    (τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6)
    (hτ : ∀ e ∈ netEdges, ∀ I : Finset (Fin 6),
      (∀ f ∈ netEdges, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (c : Fin 6 × Fin 6 → ℚ)
    (hc : ∀ I : Finset (Fin 6), (∀ f ∈ netEdges, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
      ∀ v : Fin 6, ((netEdges.filter (fun e => decide (τ e I = v))).map c).sum = 0) :
    ∀ e ∈ netEdges, c e = 0 := by
  have e01 : ((0 : Fin 6), (1 : Fin 6)) ∈ netEdges := by simp [netEdges]
  have e02 : ((0 : Fin 6), (2 : Fin 6)) ∈ netEdges := by simp [netEdges]
  have e12 : ((1 : Fin 6), (2 : Fin 6)) ∈ netEdges := by simp [netEdges]
  have e03 : ((0 : Fin 6), (3 : Fin 6)) ∈ netEdges := by simp [netEdges]
  have e14 : ((1 : Fin 6), (4 : Fin 6)) ∈ netEdges := by simp [netEdges]
  have e25 : ((2 : Fin 6), (5 : Fin 6)) ∈ netEdges := by simp [netEdges]
  have hI0 := ind_singleton 0
  have hI1 := ind_singleton 1
  have hI2 := ind_singleton 2
  have h01_0 : τ (0, 1) {0} = 1 := by
    rcases hτ (0, 1) e01 {0} hI0 with ⟨h | h, hne⟩
    · exact absurd (by simp [h]) hne
    · exact h
  have h02_0 : τ (0, 2) {0} = 2 := by
    rcases hτ (0, 2) e02 {0} hI0 with ⟨h | h, hne⟩
    · exact absurd (by simp [h]) hne
    · exact h
  have h03_0 : τ (0, 3) {0} = 3 := by
    rcases hτ (0, 3) e03 {0} hI0 with ⟨h | h, hne⟩
    · exact absurd (by simp [h]) hne
    · exact h
  have h12_0 : τ (1, 2) {0} = 1 ∨ τ (1, 2) {0} = 2 := (hτ (1, 2) e12 {0} hI0).1
  have h14_0 : τ (1, 4) {0} = 1 ∨ τ (1, 4) {0} = 4 := (hτ (1, 4) e14 {0} hI0).1
  have h25_0 : τ (2, 5) {0} = 2 ∨ τ (2, 5) {0} = 5 := (hτ (2, 5) e25 {0} hI0).1
  have h01_1 : τ (0, 1) {1} = 0 := by
    rcases hτ (0, 1) e01 {1} hI1 with ⟨h | h, hne⟩
    · exact h
    · exact absurd (by simp [h]) hne
  have h12_1 : τ (1, 2) {1} = 2 := by
    rcases hτ (1, 2) e12 {1} hI1 with ⟨h | h, hne⟩
    · exact absurd (by simp [h]) hne
    · exact h
  have h14_1 : τ (1, 4) {1} = 4 := by
    rcases hτ (1, 4) e14 {1} hI1 with ⟨h | h, hne⟩
    · exact absurd (by simp [h]) hne
    · exact h
  have h02_1 : τ (0, 2) {1} = 0 ∨ τ (0, 2) {1} = 2 := (hτ (0, 2) e02 {1} hI1).1
  have h03_1 : τ (0, 3) {1} = 0 ∨ τ (0, 3) {1} = 3 := (hτ (0, 3) e03 {1} hI1).1
  have h25_1 : τ (2, 5) {1} = 2 ∨ τ (2, 5) {1} = 5 := (hτ (2, 5) e25 {1} hI1).1
  have h02_2 : τ (0, 2) {2} = 0 := by
    rcases hτ (0, 2) e02 {2} hI2 with ⟨h | h, hne⟩
    · exact h
    · exact absurd (by simp [h]) hne
  have h12_2 : τ (1, 2) {2} = 1 := by
    rcases hτ (1, 2) e12 {2} hI2 with ⟨h | h, hne⟩
    · exact h
    · exact absurd (by simp [h]) hne
  have h25_2 : τ (2, 5) {2} = 5 := by
    rcases hτ (2, 5) e25 {2} hI2 with ⟨h | h, hne⟩
    · exact absurd (by simp [h]) hne
    · exact h
  have h01_2 : τ (0, 1) {2} = 0 ∨ τ (0, 1) {2} = 1 := (hτ (0, 1) e01 {2} hI2).1
  have h03_2 : τ (0, 3) {2} = 0 ∨ τ (0, 3) {2} = 3 := (hτ (0, 3) e03 {2} hI2).1
  have h14_2 : τ (1, 4) {2} = 1 ∨ τ (1, 4) {2} = 4 := (hτ (1, 4) e14 {2} hI2).1
  have hx : c (0, 3) = 0 := by
    have h := hc {0} hI0 3
    rw [filter_sum_eq] at h
    rcases h12_0 with h12 | h12 <;> rcases h14_0 with h14 | h14 <;> rcases h25_0 with h25 | h25 <;>
      (simp only [h01_0, h02_0, h03_0, h12, h14, h25] at h; norm_num at h; exact h)
  have hy : c (1, 4) = 0 := by
    have h := hc {1} hI1 4
    rw [filter_sum_eq] at h
    rcases h02_1 with h02 | h02 <;> rcases h03_1 with h03 | h03 <;> rcases h25_1 with h25 | h25 <;>
      (simp only [h01_1, h12_1, h14_1, h02, h03, h25] at h; norm_num at h; exact h)
  have hz : c (2, 5) = 0 := by
    have h := hc {2} hI2 5
    rw [filter_sum_eq] at h
    rcases h01_2 with h01 | h01 <;> rcases h03_2 with h03 | h03 <;> rcases h14_2 with h14 | h14 <;>
      (simp only [h02_2, h12_2, h25_2, h01, h03, h14] at h; norm_num at h; exact h)
  have htri0 : (c (0, 1) = 0 ∨ c (0, 2) = 0) ∧ c (0, 1) + c (0, 2) + c (1, 2) = 0 := by
    have hv1 := hc {0} hI0 1
    have hv2 := hc {0} hI0 2
    rw [filter_sum_eq] at hv1 hv2
    rcases h12_0 with h12 | h12 <;> rcases h14_0 with h14 | h14 <;> rcases h25_0 with h25 | h25 <;>
      (simp only [h01_0, h02_0, h03_0, h12, h14, h25, hx, hy, hz] at hv1 hv2;
       norm_num at hv1 hv2;
       first
       | exact ⟨Or.inr hv2, by linarith⟩
       | exact ⟨Or.inl hv1, by linarith⟩)
  have htri1 : c (0, 1) = 0 ∨ c (1, 2) = 0 := by
    have hv0 := hc {1} hI1 0
    have hv2 := hc {1} hI1 2
    rw [filter_sum_eq] at hv0 hv2
    rcases h02_1 with h02 | h02 <;> rcases h03_1 with h03 | h03 <;> rcases h25_1 with h25 | h25 <;>
      (simp only [h01_1, h12_1, h14_1, h02, h03, h25, hx, hy, hz] at hv0 hv2;
       norm_num at hv0 hv2;
       first | exact Or.inr hv2 | exact Or.inl hv0)
  have htri2 : c (0, 2) = 0 ∨ c (1, 2) = 0 := by
    have hv0 := hc {2} hI2 0
    have hv1 := hc {2} hI2 1
    rw [filter_sum_eq] at hv0 hv1
    rcases h01_2 with h01 | h01 <;> rcases h03_2 with h03 | h03 <;> rcases h14_2 with h14 | h14 <;>
      (simp only [h02_2, h12_2, h25_2, h01, h03, h14, hx, hy, hz] at hv0 hv1;
       norm_num at hv0 hv1;
       first | exact Or.inr hv1 | exact Or.inl hv0)
  have ha : c (0, 1) = 0 := by
    rcases htri0.1 with h | h
    · exact h
    · rcases htri1 with h1 | h1
      · exact h1
      · linarith [htri0.2]
  have hb : c (0, 2) = 0 := by
    rcases htri2 with h | h
    · exact h
    · linarith [htri0.2]
  have hd : c (1, 2) = 0 := by linarith [htri0.2]
  intro e he
  simp only [netEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

end PEqualNP.Outside.L_meta_359_aux

theorem PEqualNP.Outside.L_meta_359 :
    ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] →
      ∀ τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6,
        (∀ e ∈ E, ∀ I : Finset (Fin 6),
          (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) →
        ∀ c : Fin 6 × Fin 6 → ℚ,
          (∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
            ∀ v : Fin 6, ((E.filter (fun e => τ e I = v)).map c).sum = 0) →
          ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hc
  subst hE
  exact PEqualNP.Outside.L_meta_359_aux.main_net τ hτ c hc
