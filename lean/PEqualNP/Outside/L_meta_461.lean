import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_461_aux

private lemma filter_map_sum (l : List (Fin 6 × Fin 6)) (p : Fin 6 × Fin 6 → Bool)
    (c : Fin 6 × Fin 6 → ℚ) :
    ((l.filter p).map c).sum = (l.map fun e => if p e then c e else 0).sum := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases h : p a <;> simp [h, ih]

private lemma ind_singleton (v : Fin 6) :
    ∀ f ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)),
      ¬ (f.1 ∈ ({v} : Finset (Fin 6)) ∧ f.2 ∈ ({v} : Finset (Fin 6))) := by
  intro f hf ⟨h1, h2⟩
  rw [Finset.mem_singleton] at h1 h2
  have heq : f.1 = f.2 := h1.trans h2.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> exact absurd heq (by decide)

theorem net_zero :
    ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] →
      ∀ τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6,
        (∀ e ∈ E, ∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
          (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) →
      ∀ c : Fin 6 × Fin 6 → ℚ,
        (∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
          ∀ v : Fin 6, ((E.filter (fun e => τ e I = v)).map c).sum = 0) →
      ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hc
  subst hE
  have hI0 := ind_singleton 0
  have hI1 := ind_singleton 1
  have hI2 := ind_singleton 2
  have eq_of : ∀ (I : Finset (Fin 6)),
      (∀ f ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)),
        ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
      ∀ v : Fin 6,
        (if τ (0, 1) I = v then c (0, 1) else 0) +
        (if τ (0, 2) I = v then c (0, 2) else 0) +
        (if τ (1, 2) I = v then c (1, 2) else 0) +
        (if τ (0, 3) I = v then c (0, 3) else 0) +
        (if τ (1, 4) I = v then c (1, 4) else 0) +
        (if τ (2, 5) I = v then c (2, 5) else 0) = 0 := by
    intro I hI v
    have h := hc I hI v
    rw [filter_map_sum] at h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      decide_eq_true_eq] at h
    linarith
  have hmem01 : ((0, 1) : Fin 6 × Fin 6) ∈ [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by decide
  have hmem02 : ((0, 2) : Fin 6 × Fin 6) ∈ [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by decide
  have hmem12 : ((1, 2) : Fin 6 × Fin 6) ∈ [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by decide
  have hmem03 : ((0, 3) : Fin 6 × Fin 6) ∈ [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by decide
  have hmem14 : ((1, 4) : Fin 6 × Fin 6) ∈ [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by decide
  have hmem25 : ((2, 5) : Fin 6 × Fin 6) ∈ [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] := by decide
  have force_snd : ∀ (a b : Fin 6) (hab : (a, b) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6))),
      τ (a, b) {a} = b := by
    intro a b hab
    have ⟨hor, hnot⟩ := hτ (a, b) hab {a} (ind_singleton a)
    rcases hor with h | h
    · exact absurd (h ▸ Finset.mem_singleton_self a) hnot
    · exact h
  have force_fst : ∀ (a b : Fin 6) (hab : (a, b) ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6))),
      τ (a, b) {b} = a := by
    intro a b hab
    have ⟨hor, hnot⟩ := hτ (a, b) hab {b} (ind_singleton b)
    rcases hor with h | h
    · exact h
    · exact absurd (h ▸ Finset.mem_singleton_self b) hnot
  have hc03 : c (0, 3) = 0 := by
    have h := eq_of {0} hI0 3
    have h01 := (hτ _ hmem01 {0} hI0).1
    have h02 := (hτ _ hmem02 {0} hI0).1
    have h12 := (hτ _ hmem12 {0} hI0).1
    have h03 := force_snd 0 3 hmem03
    have h14 := (hτ _ hmem14 {0} hI0).1
    have h25 := (hτ _ hmem25 {0} hI0).1
    have n01 : τ (0, 1) {0} ≠ 3 := by rcases h01 with h' | h' <;> rw [h'] <;> decide
    have n02 : τ (0, 2) {0} ≠ 3 := by rcases h02 with h' | h' <;> rw [h'] <;> decide
    have n12 : τ (1, 2) {0} ≠ 3 := by rcases h12 with h' | h' <;> rw [h'] <;> decide
    have n14 : τ (1, 4) {0} ≠ 3 := by rcases h14 with h' | h' <;> rw [h'] <;> decide
    have n25 : τ (2, 5) {0} ≠ 3 := by rcases h25 with h' | h' <;> rw [h'] <;> decide
    simp only [h03, n01, n02, n12, n14, n25, ↓reduceIte] at h
    linarith
  have hc14 : c (1, 4) = 0 := by
    have h := eq_of {1} hI1 4
    have h01 := (hτ _ hmem01 {1} hI1).1
    have h02 := (hτ _ hmem02 {1} hI1).1
    have h12 := (hτ _ hmem12 {1} hI1).1
    have h03 := (hτ _ hmem03 {1} hI1).1
    have h14 := force_snd 1 4 hmem14
    have h25 := (hτ _ hmem25 {1} hI1).1
    have n01 : τ (0, 1) {1} ≠ 4 := by rcases h01 with h' | h' <;> rw [h'] <;> decide
    have n02 : τ (0, 2) {1} ≠ 4 := by rcases h02 with h' | h' <;> rw [h'] <;> decide
    have n12 : τ (1, 2) {1} ≠ 4 := by rcases h12 with h' | h' <;> rw [h'] <;> decide
    have n03 : τ (0, 3) {1} ≠ 4 := by rcases h03 with h' | h' <;> rw [h'] <;> decide
    have n25 : τ (2, 5) {1} ≠ 4 := by rcases h25 with h' | h' <;> rw [h'] <;> decide
    simp only [h14, n01, n02, n12, n03, n25, ↓reduceIte] at h
    linarith
  have hc25 : c (2, 5) = 0 := by
    have h := eq_of {2} hI2 5
    have h01 := (hτ _ hmem01 {2} hI2).1
    have h02 := (hτ _ hmem02 {2} hI2).1
    have h12 := (hτ _ hmem12 {2} hI2).1
    have h03 := (hτ _ hmem03 {2} hI2).1
    have h14 := (hτ _ hmem14 {2} hI2).1
    have h25 := force_snd 2 5 hmem25
    have n01 : τ (0, 1) {2} ≠ 5 := by rcases h01 with h' | h' <;> rw [h'] <;> decide
    have n02 : τ (0, 2) {2} ≠ 5 := by rcases h02 with h' | h' <;> rw [h'] <;> decide
    have n12 : τ (1, 2) {2} ≠ 5 := by rcases h12 with h' | h' <;> rw [h'] <;> decide
    have n03 : τ (0, 3) {2} ≠ 5 := by rcases h03 with h' | h' <;> rw [h'] <;> decide
    have n14 : τ (1, 4) {2} ≠ 5 := by rcases h14 with h' | h' <;> rw [h'] <;> decide
    simp only [h25, n01, n02, n12, n03, n14, ↓reduceIte] at h
    linarith
  have htri0 : (c (0, 2) = 0 ∧ c (0, 1) + c (1, 2) = 0) ∨
      (c (0, 1) = 0 ∧ c (0, 2) + c (1, 2) = 0) := by
    have h01 := force_snd 0 1 hmem01
    have h02 := force_snd 0 2 hmem02
    have h12 := (hτ _ hmem12 {0} hI0).1
    have hv1 := eq_of {0} hI0 1
    have hv2 := eq_of {0} hI0 2
    simp only [hc03, hc14, hc25, ite_self, h01, h02] at hv1 hv2
    rcases h12 with h | h
    · left
      simp only [h] at hv1 hv2
      have d12 : ((1 : Fin 6) ≠ 2) := by decide
      have d21 : ((2 : Fin 6) ≠ 1) := by decide
      simp only [d12, d21, ↓reduceIte] at hv1 hv2
      exact ⟨by linarith, by linarith⟩
    · right
      simp only [h] at hv1 hv2
      have d12 : ((1 : Fin 6) ≠ 2) := by decide
      have d21 : ((2 : Fin 6) ≠ 1) := by decide
      simp only [d12, d21, ↓reduceIte] at hv1 hv2
      exact ⟨by linarith, by linarith⟩
  have htri1 : (c (1, 2) = 0 ∧ c (0, 1) + c (0, 2) = 0) ∨
      (c (0, 1) = 0 ∧ c (0, 2) + c (1, 2) = 0) := by
    have h01 := force_fst 0 1 hmem01
    have h12 := force_snd 1 2 hmem12
    have h02 := (hτ _ hmem02 {1} hI1).1
    have hv0 := eq_of {1} hI1 0
    have hv2 := eq_of {1} hI1 2
    simp only [hc03, hc14, hc25, ite_self, h01, h12] at hv0 hv2
    rcases h02 with h | h
    · left
      simp only [h] at hv0 hv2
      have d02 : ((0 : Fin 6) ≠ 2) := by decide
      have d20 : ((2 : Fin 6) ≠ 0) := by decide
      simp only [d02, d20, ↓reduceIte] at hv0 hv2
      exact ⟨by linarith, by linarith⟩
    · right
      simp only [h] at hv0 hv2
      have d02 : ((0 : Fin 6) ≠ 2) := by decide
      have d20 : ((2 : Fin 6) ≠ 0) := by decide
      simp only [d02, d20, ↓reduceIte] at hv0 hv2
      exact ⟨by linarith, by linarith⟩
  have htri2 : (c (1, 2) = 0 ∧ c (0, 1) + c (0, 2) = 0) ∨
      (c (0, 2) = 0 ∧ c (0, 1) + c (1, 2) = 0) := by
    have h02 := force_fst 0 2 hmem02
    have h12 := force_fst 1 2 hmem12
    have h01 := (hτ _ hmem01 {2} hI2).1
    have hv0 := eq_of {2} hI2 0
    have hv1 := eq_of {2} hI2 1
    simp only [hc03, hc14, hc25, ite_self, h02, h12] at hv0 hv1
    rcases h01 with h | h
    · left
      simp only [h] at hv0 hv1
      have d01 : ((0 : Fin 6) ≠ 1) := by decide
      have d10 : ((1 : Fin 6) ≠ 0) := by decide
      simp only [d01, d10, ↓reduceIte] at hv0 hv1
      exact ⟨by linarith, by linarith⟩
    · right
      simp only [h] at hv0 hv1
      have d01 : ((0 : Fin 6) ≠ 1) := by decide
      have d10 : ((1 : Fin 6) ≠ 0) := by decide
      simp only [d01, d10, ↓reduceIte] at hv0 hv1
      exact ⟨by linarith, by linarith⟩
  have hc01 : c (0, 1) = 0 := by
    rcases htri0 with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases htri1 with ⟨d, e⟩ | ⟨d, e⟩ <;>
      rcases htri2 with ⟨f, g⟩ | ⟨f, g⟩ <;> linarith
  have hc02 : c (0, 2) = 0 := by
    rcases htri0 with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases htri1 with ⟨d, e⟩ | ⟨d, e⟩ <;>
      rcases htri2 with ⟨f, g⟩ | ⟨f, g⟩ <;> linarith
  have hc12 : c (1, 2) = 0 := by
    rcases htri0 with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases htri1 with ⟨d, e⟩ | ⟨d, e⟩ <;>
      rcases htri2 with ⟨f, g⟩ | ⟨f, g⟩ <;> linarith
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hc01
  · exact hc02
  · exact hc12
  · exact hc03
  · exact hc14
  · exact hc25

end PEqualNP.Outside.L_meta_461_aux

theorem PEqualNP.Outside.L_meta_461 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] → ∀ τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6, (∀ e ∈ E, ∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 6 × Fin 6 → ℚ, (∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 6, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 :=
  PEqualNP.Outside.L_meta_461_aux.net_zero
