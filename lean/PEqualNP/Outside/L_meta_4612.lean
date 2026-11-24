import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4612

def R (B l : List ℕ) : Prop :=
  ∀ i : Fin l.length, ∃ u ∈ B ++ List.take (↑i) l, ∃ v ∈ B ++ List.take (↑i) l,
    l.get i = u &&& v ∨ l.get i = u ||| v

def D (B : List ℕ) (a : ℕ) : Prop := ∃ u ∈ B, ∃ v ∈ B, a = u &&& v ∨ a = u ||| v

theorem mono {B B' : List ℕ} {a : ℕ} (h : D B a) (hs : ∀ x ∈ B, x ∈ B') : D B' a := by
  obtain ⟨u, hu, v, hv, h1⟩ := h
  exact ⟨u, hs u hu, v, hs v hv, h1⟩

theorem snoc (B l : List ℕ) (a : ℕ) : R B (l ++ [a]) ↔ R B l ∧ D (B ++ l) a := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · obtain ⟨u, hu, v, hv, h1⟩ := h ⟨i.1, by simp <;> omega⟩
      have ht : List.take i.1 (l ++ [a]) = List.take i.1 l :=
        List.take_append_of_le_length (by omega)
      have hg : (l ++ [a]).get ⟨i.1, by simp <;> omega⟩ = l.get i := by
        simp [List.getElem_append_left]
      rw [ht] at hu hv
      rw [hg] at h1
      exact ⟨u, hu, v, hv, h1⟩
    · obtain ⟨u, hu, v, hv, h1⟩ := h ⟨l.length, by simp⟩
      simp only [List.take_left'] at hu hv
      simp at h1
      exact ⟨u, by simpa using hu, v, by simpa using hv, h1⟩
  · rintro ⟨h, ⟨u, hu, v, hv, h1⟩⟩ i
    by_cases hi : i.1 < l.length
    · obtain ⟨u, hu, v, hv, h1⟩ := h ⟨i.1, hi⟩
      have ht : List.take i.1 (l ++ [a]) = List.take i.1 l :=
        List.take_append_of_le_length (by omega)
      have hg : (l ++ [a]).get i = l.get ⟨i.1, hi⟩ := by
        simp [List.getElem_append_left hi]
      rw [ht, hg]
      exact ⟨u, hu, v, hv, h1⟩
    · have hil : i.1 = l.length := by
        have := i.2
        simp at this
        omega
      have ht : List.take i.1 (l ++ [a]) = l := by
        rw [hil]
        simp
      have hg : (l ++ [a]).get i = a := by
        simp [hil]
      rw [ht, hg]
      exact ⟨u, hu, v, hv, h1⟩

theorem app (B B' l1 : List ℕ) (h1 : R B l1) (hsub : ∀ z ∈ B', z ∈ B ++ l1) :
    ∀ l2, R B' l2 → R B (l1 ++ l2) := by
  intro l2
  induction l2 using List.reverseRecOn with
  | nil => intro _; simpa using h1
  | append_singleton l2 a ih =>
    intro h2
    rw [← List.append_assoc, snoc]
    rw [snoc] at h2
    obtain ⟨h2', hd⟩ := h2
    refine ⟨ih h2', mono hd ?_⟩
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · have := hsub x hx
      simp only [List.mem_append] at this ⊢
      tauto
    · simp [hx]

theorem clean (X : List ℕ) : ∀ L, R X L → ∃ S : List ℕ, S.Nodup ∧ (∀ s ∈ S, s ∉ X) ∧
    S.length ≤ L.length ∧ (∀ a ∈ L, a ∈ X ∨ a ∈ S) ∧ R X S := by
  intro L
  induction L using List.reverseRecOn with
  | nil =>
    intro _
    exact ⟨[], by simp, by simp, by simp, by simp, fun i => i.elim0⟩
  | append_singleton L a ih =>
    intro h
    rw [snoc] at h
    obtain ⟨hL, hd⟩ := h
    obtain ⟨S, hn, hx, hl, hc, hR⟩ := ih hL
    by_cases hc' : a ∈ X ∨ a ∈ S
    · refine ⟨S, hn, hx, by simp; omega, ?_, hR⟩
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact hc b hb
      · rw [List.mem_singleton] at hb
        subst hb
        exact hc'
    · simp only [not_or] at hc'
      refine ⟨S ++ [a], ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hn, List.nodup_singleton a, ?_⟩
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        subst hy
        subst hxy
        exact hc'.2 hx
      · intro s hs
        rcases List.mem_append.1 hs with hs | hs
        · exact hx s hs
        · rw [List.mem_singleton] at hs
          subst hs
          exact hc'.1
      · simp
        omega
      · intro b hb
        rcases List.mem_append.1 hb with hb | hb
        · rcases hc b hb with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_append_left _ h)
        · rw [List.mem_singleton] at hb
          subst hb
          exact Or.inr (by simp)
      · rw [snoc]
        refine ⟨hR, mono hd ?_⟩
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact List.mem_append_left _ hy
        · rcases hc y hy with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ h

end PEqualNP.Outside.L_meta_4612

theorem PEqualNP.Outside.L_meta_4612 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 x4 x5 : List ℕ), ∀ x6 ∉ x2, x1 x2 x3 → (∀ x9 ∈ x4, x9 ∈ x2 ++ x3) → x1 x4 x5 → x6 ∈ x4 ++ x5 → ∃ (x12 : List ℕ), x12.length ≤ x3.length + x5.length ∧ x12.Nodup ∧ (∀ x13 ∈ x12, x13 ∉ x2) ∧ x6 ∈ x12 ∧ x1 x2 x12
 := by
  intro x1 X Y Z W t ht hY hZ hW hts
  have hL := PEqualNP.Outside.L_meta_4612.app X Z Y hY hZ W hW
  obtain ⟨S, hn, hx, hl, hc, hR⟩ := PEqualNP.Outside.L_meta_4612.clean X (Y ++ W) hL
  refine ⟨S, by simp at hl; omega, hn, hx, ?_, hR⟩
  have htL : t ∈ Y ++ W := by
    rcases List.mem_append.1 hts with h | h
    · rcases List.mem_append.1 (hZ t h) with h' | h'
      · exact absurd h' ht
      · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ h
  rcases hc t htL with h | h
  · exact absurd h ht
  · exact h
