import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_457

theorem ne_01 : (0 : Fin 3) ≠ 1 := by decide
theorem ne_02 : (0 : Fin 3) ≠ 2 := by decide
theorem ne_10 : (1 : Fin 3) ≠ 0 := by decide
theorem ne_12 : (1 : Fin 3) ≠ 2 := by decide
theorem ne_20 : (2 : Fin 3) ≠ 0 := by decide
theorem ne_21 : (2 : Fin 3) ≠ 1 := by decide

theorem singleton_indep (k : Fin 3) :
    ∀ f ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)),
      ¬ (f.1 ∈ ({k} : Finset (Fin 3)) ∧ f.2 ∈ ({k} : Finset (Fin 3))) := by
  intro f hf hmem
  simp at hf hmem
  rcases hmem with ⟨h1, h2⟩
  rcases hf with rfl | rfl | rfl
  · exact absurd (h1.trans h2.symm) ne_01
  · exact absurd (h1.trans h2.symm) ne_02
  · exact absurd (h1.trans h2.symm) ne_12

theorem filter_triple_sum {α : Type} (p : α → Bool) (f : α → ℚ) (a b c : α) :
    (([a, b, c].filter p).map f).sum =
      (if p a = true then f a else 0) +
      (if p b = true then f b else 0) +
      (if p c = true then f c else 0) := by
  cases ha : p a <;> cases hb : p b <;> cases hc : p c <;>
    simp [List.filter_cons, ha, hb, hc] <;> ring

theorem edge_sum_eq (τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3)
    (c : Fin 3 × Fin 3 → ℚ) (I : Finset (Fin 3)) (v a b d : Fin 3)
    (hsum : (([(0, 1), (0, 2), (1, 2)].filter (fun e => τ e I = v)).map c).sum = 0)
    (ha : τ (0, 1) I = a) (hb : τ (0, 2) I = b) (hd : τ (1, 2) I = d) :
    (if a = v then c (0, 1) else 0) +
      (if b = v then c (0, 2) else 0) +
      (if d = v then c (1, 2) else 0) = 0 := by
  rw [filter_triple_sum] at hsum
  simp at hsum
  rw [ha, hb, hd] at hsum
  exact hsum

theorem tau_mem (τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3)
    (hτ : ∀ e ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ∀ I : Finset (Fin 3),
      (∀ f ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
      (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (e : Fin 3 × Fin 3) (he : e ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)))
    (k : Fin 3) :
    (τ e {k} = e.1 ∨ τ e {k} = e.2) ∧ τ e {k} ≠ k := by
  have h := hτ e he {k} (singleton_indep k)
  simpa using h

theorem tau_left (τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3)
    (hτ : ∀ e ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ∀ I : Finset (Fin 3),
      (∀ f ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
      (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (e : Fin 3 × Fin 3) (he : e ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3))) :
    τ e {e.1} = e.2 := by
  obtain ⟨h1 | h2, hne⟩ := tau_mem τ hτ e he e.1
  · exact absurd h1 hne
  · exact h2

theorem tau_right (τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3)
    (hτ : ∀ e ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ∀ I : Finset (Fin 3),
      (∀ f ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
      (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (e : Fin 3 × Fin 3) (he : e ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3))) :
    τ e {e.2} = e.1 := by
  obtain ⟨h1 | h2, hne⟩ := tau_mem τ hτ e he e.2
  · exact h1
  · exact absurd h2 hne

theorem zero_of_sums (x y z : ℚ)
    (d0 b1 a2 : Fin 3)
    (hd0 : d0 = 1 ∨ d0 = 2)
    (hb1 : b1 = 0 ∨ b1 = 2)
    (ha2 : a2 = 0 ∨ a2 = 1)
    (h0 : ∀ v : Fin 3, (if (1 : Fin 3) = v then x else 0) + (if (2 : Fin 3) = v then y else 0) + (if d0 = v then z else 0) = 0)
    (h1 : ∀ v : Fin 3, (if (0 : Fin 3) = v then x else 0) + (if b1 = v then y else 0) + (if (2 : Fin 3) = v then z else 0) = 0)
    (h2 : ∀ v : Fin 3, (if a2 = v then x else 0) + (if (0 : Fin 3) = v then y else 0) + (if (1 : Fin 3) = v then z else 0) = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 := by
  have s01 := h0 1
  have s02 := h0 2
  have s10 := h1 0
  have s12 := h1 2
  have s20 := h2 0
  have s21 := h2 1
  rcases hd0 with rfl | rfl <;>
    rcases hb1 with rfl | rfl <;>
    rcases ha2 with rfl | rfl <;>
    simp [ne_01, ne_02, ne_10, ne_12, ne_20, ne_21] at s01 s02 s10 s12 s20 s21 <;>
    refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem solve
    (τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3)
    (hτ : ∀ e ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ∀ I : Finset (Fin 3),
      (∀ f ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
      (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I)
    (c : Fin 3 × Fin 3 → ℚ)
    (hc : ∀ I : Finset (Fin 3),
      (∀ f ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), ¬ (f.1 ∈ I ∧ f.2 ∈ I)) →
      ∀ v : Fin 3, (([(0, 1), (0, 2), (1, 2)].filter (fun e => τ e I = v)).map c).sum = 0) :
    ∀ e ∈ ([(0, 1), (0, 2), (1, 2)] : List (Fin 3 × Fin 3)), c e = 0 := by
  have hd0 : τ (1, 2) {0} = 1 ∨ τ (1, 2) {0} = 2 := (tau_mem τ hτ (1, 2) (by simp) 0).1
  have hb1 : τ (0, 2) {1} = 0 ∨ τ (0, 2) {1} = 2 := (tau_mem τ hτ (0, 2) (by simp) 1).1
  have ha2 : τ (0, 1) {2} = 0 ∨ τ (0, 1) {2} = 1 := (tau_mem τ hτ (0, 1) (by simp) 2).1
  have h0 : ∀ v : Fin 3,
      (if (1 : Fin 3) = v then c (0, 1) else 0) +
      (if (2 : Fin 3) = v then c (0, 2) else 0) +
      (if τ (1, 2) {0} = v then c (1, 2) else 0) = 0 := fun v =>
    edge_sum_eq τ c {0} v 1 2 (τ (1, 2) {0})
      (hc {0} (singleton_indep 0) v)
      (tau_left τ hτ (0, 1) (by simp))
      (tau_left τ hτ (0, 2) (by simp))
      rfl
  have h1 : ∀ v : Fin 3,
      (if (0 : Fin 3) = v then c (0, 1) else 0) +
      (if τ (0, 2) {1} = v then c (0, 2) else 0) +
      (if (2 : Fin 3) = v then c (1, 2) else 0) = 0 := fun v =>
    edge_sum_eq τ c {1} v 0 (τ (0, 2) {1}) 2
      (hc {1} (singleton_indep 1) v)
      (tau_right τ hτ (0, 1) (by simp))
      rfl
      (tau_left τ hτ (1, 2) (by simp))
  have h2 : ∀ v : Fin 3,
      (if τ (0, 1) {2} = v then c (0, 1) else 0) +
      (if (0 : Fin 3) = v then c (0, 2) else 0) +
      (if (1 : Fin 3) = v then c (1, 2) else 0) = 0 := fun v =>
    edge_sum_eq τ c {2} v (τ (0, 1) {2}) 0 1
      (hc {2} (singleton_indep 2) v)
      rfl
      (tau_right τ hτ (0, 2) (by simp))
      (tau_right τ hτ (1, 2) (by simp))
  obtain ⟨hc01, hc02, hc12⟩ := zero_of_sums (c (0, 1)) (c (0, 2)) (c (1, 2))
    (τ (1, 2) {0}) (τ (0, 2) {1}) (τ (0, 1) {2}) hd0 hb1 ha2 h0 h1 h2
  intro e he
  simp at he
  rcases he with rfl | rfl | rfl
  · exact hc01
  · exact hc02
  · exact hc12

end PEqualNP.Outside.L_meta_457

theorem PEqualNP.Outside.L_meta_457 : ∀ E : List (Fin 3 × Fin 3), E = [(0, 1), (0, 2), (1, 2)] → ∀ τ : Fin 3 × Fin 3 → Finset (Fin 3) → Fin 3, (∀ e ∈ E, ∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → (τ e I = e.1 ∨ τ e I = e.2) ∧ τ e I ∉ I) → ∀ c : Fin 3 × Fin 3 → ℚ, (∀ I : Finset (Fin 3), (∀ f ∈ E, ¬ (f.1 ∈ I ∧ f.2 ∈ I)) → ∀ v : Fin 3, ((E.filter (fun e => τ e I = v)).map c).sum = 0) → ∀ e ∈ E, c e = 0 := by
  rintro E rfl τ hτ c hc
  exact PEqualNP.Outside.L_meta_457.solve τ hτ c hc
