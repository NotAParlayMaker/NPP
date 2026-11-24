import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3328

def Step (A : List ℕ) (y : ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, y = a &&& b ∨ y = a ||| b

def Der (S L : List ℕ) : Prop :=
  ∀ i : Fin L.length, Step (S ++ L.take i) (L.get i)

theorem step_mono {A B : List ℕ} {y : ℕ} (h : Step A y) (hAB : ∀ a ∈ A, a ∈ B) :
    Step B y := by
  obtain ⟨a, ha, b, hb, h⟩ := h
  exact ⟨a, hAB a ha, b, hAB b hb, h⟩

theorem der_mono {A B L : List ℕ} (h : Der A L) (hAB : ∀ a ∈ A, a ∈ B) : Der B L := by
  intro i
  apply step_mono (h i)
  intro a ha
  rcases List.mem_append.mp ha with h1 | h1
  · exact List.mem_append_left _ (hAB a h1)
  · exact List.mem_append_right _ h1

theorem der_append (S L M : List ℕ) :
    Der S (L ++ M) ↔ Der S L ∧ Der (S ++ L) M := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · have hi : (i : ℕ) < (L ++ M).length := by simp; omega
      have := h ⟨i, hi⟩
      simp only [List.get_eq_getElem] at this ⊢
      rw [List.take_append_of_le_length (by omega), List.getElem_append_left i.isLt] at this
      exact this
    · have hj : L.length + (j : ℕ) < (L ++ M).length := by simp
      have := h ⟨L.length + j, hj⟩
      simp only [List.get_eq_getElem] at this ⊢
      rw [List.take_append, List.getElem_append_right (by omega)] at this
      simpa [List.take_of_length_le, List.append_assoc] using this
  · rintro ⟨h1, h2⟩ i
    simp only [List.get_eq_getElem]
    by_cases hi : (i : ℕ) < L.length
    · have := h1 ⟨i, hi⟩
      simp only [List.get_eq_getElem] at this
      rw [List.take_append_of_le_length (by omega), List.getElem_append_left hi]
      exact this
    · have hj : (i : ℕ) - L.length < M.length := by
        have := i.isLt; simp at this; omega
      have := h2 ⟨(i : ℕ) - L.length, hj⟩
      simp only [List.get_eq_getElem] at this
      rw [List.getElem_append_right (by omega)]
      have ht : (L ++ M).take i = L ++ M.take ((i : ℕ) - L.length) := by
        rw [List.take_append]
        rw [List.take_of_length_le (by omega)]
      rw [ht, ← List.append_assoc]
      exact this

theorem der_single (S : List ℕ) (y : ℕ) : Der S [y] ↔ Step S y := by
  constructor
  · intro h
    simpa using h ⟨0, by simp⟩
  · intro h i
    obtain ⟨i, hi⟩ := i
    have h0 : i = 0 := by simpa using hi
    subst h0
    simpa using h

theorem clean (S : List ℕ) : ∀ ys : List ℕ, Der S ys →
    ∃ L : List ℕ, L.length ≤ ys.length ∧ L.Nodup ∧ (∀ y ∈ L, y ∉ S) ∧ Der S L ∧
      (∀ y ∈ ys, y ∈ S ∨ y ∈ L) ∧ (∀ y ∈ L, y ∈ ys) := by
  intro ys
  induction ys using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], by simp, by simp, by simp, fun i => i.elim0, by simp, by simp⟩
  | append_singleton zs y ih =>
    intro h
    rw [der_append, der_single] at h
    obtain ⟨L, hlen, hnd, hS, hd, hcov, hsub⟩ := ih h.1
    by_cases hy : y ∈ S ∨ y ∈ L
    · refine ⟨L, by simp; omega, hnd, hS, hd, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hcov x hx
        · simp at hx; subst hx; exact hy
      · intro x hx; exact List.mem_append_left _ (hsub x hx)
    · simp only [not_or] at hy
      refine ⟨L ++ [y], by simp; omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnd, by simp, ?_⟩
        intro a ha b hb
        simp at hb; subst hb
        intro hab; subst hab; exact hy.2 ha
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hS x hx
        · simp at hx; subst hx; exact hy.1
      · rw [der_append, der_single]
        refine ⟨hd, step_mono h.2 ?_⟩
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact List.mem_append_left _ ha
        · rcases hcov a ha with h1 | h1
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ h1
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rcases hcov x hx with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (List.mem_append_left _ h1)
        · simp at hx; subst hx; exact Or.inr (by simp)
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ (hsub x hx)
        · exact List.mem_append_right _ hx

theorem main (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ) (h5 : x5 ∉ x3) (h4 : Step x3 x4)
    (h6 : Der (x4 :: x3) x6) (h56 : Step (x4 :: x3 ++ x6) x5) :
    ∃ L : List ℕ, L.length ≤ x6.length + 2 ∧ L.Nodup ∧ (∀ y ∈ L, y ∉ x3) ∧ x5 ∈ L ∧
      Der x3 L := by
  have hd : Der x3 ([x4] ++ x6 ++ [x5]) := by
    rw [der_append, der_append, der_single, der_single]
    refine ⟨⟨h4, der_mono h6 ?_⟩, step_mono h56 ?_⟩
    · intro a ha; simp at ha ⊢; tauto
    · intro a ha; simp at ha ⊢; tauto
  obtain ⟨L, hlen, hnd, hS, hD, hcov, _⟩ := clean x3 _ hd
  refine ⟨L, by simp at hlen; omega, hnd, hS, ?_, hD⟩
  rcases hcov x5 (by simp) with h | h
  · exact absurd h h5
  · exact h

end PEqualNP.Outside.L_meta_3328

theorem PEqualNP.Outside.L_meta_3328 : have x1 : List ℕ → ℕ → Prop := fun (x1 : List ℕ) (x2 : ℕ) => ∃ x3 ∈ x1, ∃ x4 ∈ x1, x2 = x3 &&& x4 ∨ x2 = x3 ||| x4; have x2 : List ℕ → List ℕ → Prop := fun (x2 x3 : List ℕ) => ∀ (x4 : Fin x3.length), x1 (x2 ++ List.take (↑x4) x3) (x3.get x4); ∀ (x3 : List ℕ) (x4 x5 : ℕ) (x6 : List ℕ), x5 ∉ x3 → x1 x3 x4 → x2 (x4 :: x3) x6 → x1 (x4 :: x3 ++ x6) x5 → ∃ (x11 : List ℕ), x11.length ≤ x6.length + (2 : ℕ) ∧ x11.Nodup ∧ (∀ x12 ∈ x11, x12 ∉ x3) ∧ x5 ∈ x11 ∧ x2 x3 x11 := by
  intro x1 x2 x3 x4 x5 x6 h5 h4 h6 h56
  exact PEqualNP.Outside.L_meta_3328.main x3 x4 x5 x6 h5 h4 h6 h56
