import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_612_2_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma minimal_mono_exists (n : ℕ) (C : Circuit) (hC : Monotone2 C) :
    ∃ D : Circuit, IsMinimalMonoCircuit n D ∧ D.size ≤ C.size ∧
      circuitFun n D = circuitFun n C := by
  classical
  have hex : ∃ s : ℕ, ∃ D : Circuit, Monotone2 D ∧ D.size = s ∧ circuitFun n D = circuitFun n C :=
    ⟨C.size, C, hC, rfl, rfl⟩
  set s0 := Nat.find hex
  obtain ⟨D, hDm, hDs, hDf⟩ := Nat.find_spec hex
  have hmin : IsMinimalMonoCircuit n D := by
    refine ⟨hDm, fun E hEm hEf => ?_⟩
    rw [hDs]
    exact Nat.find_min' hex ⟨E, hEm, rfl, hEf.trans hDf⟩
  have hle : D.size ≤ C.size := by
    rw [hDs]
    exact Nat.find_min' hex ⟨C, hC, rfl, rfl⟩
  exact ⟨D, hmin, hle, hDf⟩

end PEqualNP.Outside.R_meta_612_2_aux

theorem PEqualNP.Outside.R_meta_612_2
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.IsMinimalMonoCircuit n D →
      (∀ x : Fin n → Bool, (D.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      ∃ D' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 n D' ∧ D'.size ≤ D.size ∧
        (∀ x : Fin n → Bool, (D'.eval (List.ofFn x) = true ↔
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)))
    (h2 : ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) →
      (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) →
      PEqualNP.TopForm.IsAO2 n C →
      (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      G.edgeSet.ncard + t ≤ C.size + 1) :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1 := by
  intro n t G C hne hC4 hvc hmin_vc hmono heval
  obtain ⟨D, hDmin, hDle, hDfun⟩ := PEqualNP.Outside.R_meta_612_2_aux.minimal_mono_exists n C hmono
  have hDeval : ∀ x : Fin n → Bool, (D.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    have hfx : D.eval (List.ofFn x) = C.eval (List.ofFn x) :=
      congrFun hDfun x
    rw [hfx]
    exact heval x
  obtain ⟨D', hAO, hD'le, hD'eval⟩ := h1 n G D hne hC4 hDmin hDeval
  have hbound := h2 n t G D' hne hC4 hvc hmin_vc hAO hD'eval
  omega
