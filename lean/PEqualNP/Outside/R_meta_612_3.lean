import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_612_3
    (peel : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (v u : Fin n) (C : Circuit), 2 < G.edgeFinset.card →
      G.Adj v u → G.degree v = 1 → G.degree u = 2 → Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∃ D : Circuit, Monotone2 D ∧ D.size + 3 ≤ C.size ∧
        ∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔
          ∃ i j, (G.deleteIncidenceSet u).Adj i j ∧ x i = true ∧ x j = true)
    (core : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (2 < G.edgeFinset.card → ∀ v u, G.Adj v u → G.degree v = 1 → G.degree u ≠ 2) →
      Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
        G.edgeFinset.card + S.card ≤ C.size + 1) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  classical
  have bound : ∀ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), C.size = k →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
        G.edgeFinset.card + S.card ≤ C.size + 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro n G inst C hsize square hm hf
      by_cases hleaf : 2 < G.edgeFinset.card ∧
        ∃ v u, G.Adj v u ∧ G.degree v = 1 ∧ G.degree u = 2
      · obtain ⟨many, v, u, huv, hv, hu⟩ := hleaf
        obtain ⟨D, hd, hs, hf'⟩ := peel n G v u C many huv hv hu hm hf
        have sub := G.deleteIncidenceSet_le u
        obtain ⟨T, ht, hb⟩ := ih D.size (by omega) n (G.deleteIncidenceSet u) D rfl
          (fun a b c d h₁ h₂ h₃ h₄ h₅ h₆ ab bc cd da =>
            square a b c d h₁ h₂ h₃ h₄ h₅ h₆ (sub ab) (sub bc) (sub cd) (sub da)) hd hf'
        refine ⟨insert u T, ?_, ?_⟩
        · intro a b hab
          by_cases ha : a = u
          · exact Or.inl (by simp [ha])
          by_cases hb' : b = u
          · exact Or.inr (by simp [hb'])
          exact (ht a b (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hab, ha, hb'⟩)).imp
            (Finset.mem_insert_of_mem) (Finset.mem_insert_of_mem)
        · have cut := G.card_edgeFinset_deleteIncidenceSet u
          have one := Finset.card_insert_le u T
          omega
      · apply core n G C square _ hm hf
        intro many v u hadj hv hu
        exact hleaf ⟨many, v, u, hadj, hv, hu⟩
  intro n t G C _ square _ minimal hm hf
  obtain ⟨S, hS, hb⟩ := bound C.size n G C rfl square hm hf
  have mt := minimal S hS
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]
  omega
