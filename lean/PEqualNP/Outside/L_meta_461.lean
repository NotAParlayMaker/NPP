import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_461

theorem indep_045 :
    ∀ f ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)),
      ¬ (f.1 ∈ ({0, 4, 5} : Finset (Fin 6)) ∧ f.2 ∈ ({0, 4, 5} : Finset (Fin 6))) := by
  intro f hf
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with h | h | h | h | h | h <;> subst f <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] <;> decide

theorem indep_135 :
    ∀ f ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)),
      ¬ (f.1 ∈ ({1, 3, 5} : Finset (Fin 6)) ∧ f.2 ∈ ({1, 3, 5} : Finset (Fin 6))) := by
  intro f hf
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with h | h | h | h | h | h <;> subst f <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] <;> decide

theorem indep_234 :
    ∀ f ∈ ([(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] : List (Fin 6 × Fin 6)),
      ¬ (f.1 ∈ ({2, 3, 4} : Finset (Fin 6)) ∧ f.2 ∈ ({2, 3, 4} : Finset (Fin 6))) := by
  intro f hf
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with h | h | h | h | h | h <;> subst f <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] <;> decide

theorem tau_eq_snd (τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6)
    (I : Finset (Fin 6)) (a b : Fin 6)
    (h : (τ (a, b) I = (a, b).1 ∨ τ (a, b) I = (a, b).2) ∧ τ (a, b) I ∉ I)
    (ha : a ∈ I) : τ (a, b) I = b := by
  rcases h with ⟨h1 | h2, hnot⟩
  · rw [h1] at hnot
    exact (hnot ha).elim
  · exact h2

theorem tau_eq_fst (τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6)
    (I : Finset (Fin 6)) (a b : Fin 6)
    (h : (τ (a, b) I = (a, b).1 ∨ τ (a, b) I = (a, b).2) ∧ τ (a, b) I ∉ I)
    (hb : b ∈ I) : τ (a, b) I = a := by
  rcases h with ⟨h1 | h2, hnot⟩
  · exact h1
  · rw [h2] at hnot
    exact (hnot hb).elim

theorem tau_ne (τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6)
    (I : Finset (Fin 6)) (a b v : Fin 6)
    (h : (τ (a, b) I = (a, b).1 ∨ τ (a, b) I = (a, b).2) ∧ τ (a, b) I ∉ I)
    (hav : a ≠ v) (hbv : b ≠ v) : τ (a, b) I ≠ v := by
  rcases h with ⟨h1 | h2, _⟩
  · simpa [h1] using hav
  · simpa [h2] using hbv

end PEqualNP.Outside.L_meta_461

theorem PEqualNP.Outside.L_meta_461 : ∀ E : List (Fin 6 × Fin 6), E = [(0, 1), (0, 2), (1, 2), (0, 3), (1, 4), (2, 5)] → ∀ τ : Fin 6 × Fin 6 → Finset (Fin 6) → Fin 6, (∀ e ∈ E, ∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 6 × Fin 6 → ℚ, (∀ I : Finset (Fin 6), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 6, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  intro E hE τ hτ c hsum e he
  subst E
  have hI0 := PEqualNP.Outside.L_meta_461.indep_045
  have hI1 := PEqualNP.Outside.L_meta_461.indep_135
  have hI2 := PEqualNP.Outside.L_meta_461.indep_234
  have h01_0 : τ (0, 1) {0, 4, 5} = 1 :=
    PEqualNP.Outside.L_meta_461.tau_eq_snd τ {0, 4, 5} 0 1
      (hτ (0, 1) (by decide) {0, 4, 5} hI0)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h02_0 : τ (0, 2) {0, 4, 5} = 2 :=
    PEqualNP.Outside.L_meta_461.tau_eq_snd τ {0, 4, 5} 0 2
      (hτ (0, 2) (by decide) {0, 4, 5} hI0)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h03_0 : τ (0, 3) {0, 4, 5} = 3 :=
    PEqualNP.Outside.L_meta_461.tau_eq_snd τ {0, 4, 5} 0 3
      (hτ (0, 3) (by decide) {0, 4, 5} hI0)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h14_0 : τ (1, 4) {0, 4, 5} = 1 :=
    PEqualNP.Outside.L_meta_461.tau_eq_fst τ {0, 4, 5} 1 4
      (hτ (1, 4) (by decide) {0, 4, 5} hI0)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h25_0 : τ (2, 5) {0, 4, 5} = 2 :=
    PEqualNP.Outside.L_meta_461.tau_eq_fst τ {0, 4, 5} 2 5
      (hτ (2, 5) (by decide) {0, 4, 5} hI0)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h12_0_ne3 : τ (1, 2) {0, 4, 5} ≠ 3 :=
    PEqualNP.Outside.L_meta_461.tau_ne τ {0, 4, 5} 1 2 3
      (hτ (1, 2) (by decide) {0, 4, 5} hI0) (by decide) (by decide)
  have h12_0_choice : τ (1, 2) {0, 4, 5} = 1 ∨ τ (1, 2) {0, 4, 5} = 2 :=
    (hτ (1, 2) (by decide) {0, 4, 5} hI0).1
  have h01_1 : τ (0, 1) {1, 3, 5} = 0 :=
    PEqualNP.Outside.L_meta_461.tau_eq_fst τ {1, 3, 5} 0 1
      (hτ (0, 1) (by decide) {1, 3, 5} hI1)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h12_1 : τ (1, 2) {1, 3, 5} = 2 :=
    PEqualNP.Outside.L_meta_461.tau_eq_snd τ {1, 3, 5} 1 2
      (hτ (1, 2) (by decide) {1, 3, 5} hI1)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h03_1 : τ (0, 3) {1, 3, 5} = 0 :=
    PEqualNP.Outside.L_meta_461.tau_eq_fst τ {1, 3, 5} 0 3
      (hτ (0, 3) (by decide) {1, 3, 5} hI1)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h14_1 : τ (1, 4) {1, 3, 5} = 4 :=
    PEqualNP.Outside.L_meta_461.tau_eq_snd τ {1, 3, 5} 1 4
      (hτ (1, 4) (by decide) {1, 3, 5} hI1)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h25_1 : τ (2, 5) {1, 3, 5} = 2 :=
    PEqualNP.Outside.L_meta_461.tau_eq_fst τ {1, 3, 5} 2 5
      (hτ (2, 5) (by decide) {1, 3, 5} hI1)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h02_1_ne4 : τ (0, 2) {1, 3, 5} ≠ 4 :=
    PEqualNP.Outside.L_meta_461.tau_ne τ {1, 3, 5} 0 2 4
      (hτ (0, 2) (by decide) {1, 3, 5} hI1) (by decide) (by decide)
  have h02_1_choice : τ (0, 2) {1, 3, 5} = 0 ∨ τ (0, 2) {1, 3, 5} = 2 :=
    (hτ (0, 2) (by decide) {1, 3, 5} hI1).1
  have h02_2 : τ (0, 2) {2, 3, 4} = 0 :=
    PEqualNP.Outside.L_meta_461.tau_eq_fst τ {2, 3, 4} 0 2
      (hτ (0, 2) (by decide) {2, 3, 4} hI2)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h12_2 : τ (1, 2) {2, 3, 4} = 1 :=
    PEqualNP.Outside.L_meta_461.tau_eq_fst τ {2, 3, 4} 1 2
      (hτ (1, 2) (by decide) {2, 3, 4} hI2)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h03_2 : τ (0, 3) {2, 3, 4} = 0 :=
    PEqualNP.Outside.L_meta_461.tau_eq_fst τ {2, 3, 4} 0 3
      (hτ (0, 3) (by decide) {2, 3, 4} hI2)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h14_2 : τ (1, 4) {2, 3, 4} = 1 :=
    PEqualNP.Outside.L_meta_461.tau_eq_fst τ {2, 3, 4} 1 4
      (hτ (1, 4) (by decide) {2, 3, 4} hI2)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h25_2 : τ (2, 5) {2, 3, 4} = 5 :=
    PEqualNP.Outside.L_meta_461.tau_eq_snd τ {2, 3, 4} 2 5
      (hτ (2, 5) (by decide) {2, 3, 4} hI2)
      (by simp only [Finset.mem_insert, Finset.mem_singleton]; decide)
  have h01_2_ne5 : τ (0, 1) {2, 3, 4} ≠ 5 :=
    PEqualNP.Outside.L_meta_461.tau_ne τ {2, 3, 4} 0 1 5
      (hτ (0, 1) (by decide) {2, 3, 4} hI2) (by decide) (by decide)
  have h01_2_choice : τ (0, 1) {2, 3, 4} = 0 ∨ τ (0, 1) {2, 3, 4} = 1 :=
    (hτ (0, 1) (by decide) {2, 3, 4} hI2).1
  have hc03 : c (0, 3) = 0 := by
    have h := hsum {0, 4, 5} hI0 3
    simp [h01_0, h02_0, h12_0_ne3, h03_0, h14_0, h25_0] at h
    linarith
  have hc14 : c (1, 4) = 0 := by
    have h := hsum {1, 3, 5} hI1 4
    simp [h01_1, h02_1_ne4, h12_1, h03_1, h14_1, h25_1] at h
    linarith
  have hc25 : c (2, 5) = 0 := by
    have h := hsum {2, 3, 4} hI2 5
    simp [h01_2_ne5, h02_2, h12_2, h03_2, h14_2, h25_2] at h
    linarith
  have htri : c (0, 1) = 0 ∧ c (0, 2) = 0 ∧ c (1, 2) = 0 := by
    rcases h12_0_choice with h12_0 | h12_0
    · have ha := hsum {0, 4, 5} hI0 1
      have hb := hsum {0, 4, 5} hI0 2
      simp [h01_0, h02_0, h12_0, h03_0, h14_0, h25_0, hc14, hc25] at ha hb
      rcases h02_1_choice with h02_1 | h02_1
      · have hc := hsum {1, 3, 5} hI1 2
        simp [h01_1, h02_1, h12_1, h03_1, h14_1, h25_1, hc25] at hc
        exact ⟨by linarith, by linarith, by linarith⟩
      · have hc := hsum {1, 3, 5} hI1 2
        simp [h01_1, h02_1, h12_1, h03_1, h14_1, h25_1, hc25] at hc
        exact ⟨by linarith, by linarith, by linarith⟩
    · have ha := hsum {0, 4, 5} hI0 1
      have hb := hsum {0, 4, 5} hI0 2
      simp [h01_0, h02_0, h12_0, h03_0, h14_0, h25_0, hc14, hc25] at ha hb
      rcases h01_2_choice with h01_2 | h01_2
      · have hc := hsum {2, 3, 4} hI2 1
        simp [h01_2, h02_2, h12_2, h03_2, h14_2, h25_2, hc14] at hc
        exact ⟨by linarith, by linarith, by linarith⟩
      · have hc := hsum {2, 3, 4} hI2 1
        simp [h01_2, h02_2, h12_2, h03_2, h14_2, h25_2, hc14] at hc
        exact ⟨by linarith, by linarith, by linarith⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with h | h | h | h | h | h <;> subst e <;>
    simp only [htri.1, htri.2.1, htri.2.2, hc03, hc14, hc25]
