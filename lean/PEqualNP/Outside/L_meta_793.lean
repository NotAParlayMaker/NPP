import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_793 : ∀ G : SimpleGraph (Fin 2), G.edgeSet = {s(0, 1)} → ∀ C : PEqualNP.AndCount.AndCountCircuit 2, C.WellFormed → (∀ I : Finset (Fin 2), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → 1 ≤ C.size := by
  intro G hG C _ h
  have hadj : ∀ a b : Fin 2, G.Adj a b ↔ s(a, b) = s(0, 1) := by
    intro a b
    rw [← SimpleGraph.mem_edgeSet, hG, Set.mem_singleton_iff]
  have h01 : G.Adj 0 1 := (hadj 0 1).2 rfl
  have h10 : G.Adj 1 0 := h01.symm
  have hn00 : ¬ G.Adj 0 0 := G.irrefl
  have hn11 : ¬ G.Adj 1 1 := G.irrefl
  have hI0 : ∀ v ∈ ({0} : Finset (Fin 2)), ∀ w ∈ ({0} : Finset (Fin 2)), ¬ G.Adj v w := by
    intro v hv w hw
    simp only [Finset.mem_singleton] at hv hw
    subst hv hw
    exact hn00
  have hI1 : ∀ v ∈ ({1} : Finset (Fin 2)), ∀ w ∈ ({1} : Finset (Fin 2)), ¬ G.Adj v w := by
    intro v hv w hw
    simp only [Finset.mem_singleton] at hv hw
    subst hv hw
    exact hn11
  have hM0 : ∀ u, u ∉ ({0} : Finset (Fin 2)) → ∃ v ∈ ({0} : Finset (Fin 2)), G.Adj u v := by
    intro u hu
    refine ⟨0, Finset.mem_singleton_self _, ?_⟩
    fin_cases u
    · simp at hu
    · exact h10
  have hM1 : ∀ u, u ∉ ({1} : Finset (Fin 2)) → ∃ v ∈ ({1} : Finset (Fin 2)), G.Adj u v := by
    intro u hu
    refine ⟨1, Finset.mem_singleton_self _, ?_⟩
    fin_cases u
    · exact h01
    · simp at hu
  obtain ⟨hA, hB⟩ := h {0} hI0 hM0
  obtain ⟨hC1, _⟩ := h {1} hI1 hM1
  have hT := hB 1 (by simp)
  by_contra hs
  have hs0 : C.size = 0 := by omega
  have hg : ∀ U : Finset (Fin 2), C.eval U = decide (∃ v ∈ C.outVars, v ∈ U) := by
    intro U
    unfold PEqualNP.AndCount.AndCountCircuit.eval
    congr 1
    apply propext
    constructor
    · rintro (h1 | ⟨j, _, _⟩)
      · exact h1
      · exact absurd j.2 (by omega)
    · intro h1
      exact Or.inl h1
  rw [hg] at hT hC1 hA
  simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hT hC1 hA
  obtain ⟨v, hv, hvU⟩ := hT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvU
  rcases hvU with e | e
  · exact hC1 ⟨v, hv, by simp [e]⟩
  · exact hA ⟨v, hv, by simp [e]⟩
