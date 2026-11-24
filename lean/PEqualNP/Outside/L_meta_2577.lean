import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2577

theorem uniq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (A : Finset (Fin n)) (hA : 2 ≤ A.card)
    (a a' : Fin n) (ha : ∀ x ∈ A, G.Adj a x) (ha' : ∀ x ∈ A, G.Adj a' x) : a = a' := by
  by_contra hne
  have h1 := h4 a a' hne
  have hsub : A ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj a' w) := by
    intro x hx
    simp [ha x hx, ha' x hx]
  have h2 := Finset.card_le_card hsub
  omega

end PEqualNP.Outside.L_meta_2577

theorem PEqualNP.Outside.L_meta_2577 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Sym2 (Fin x1))), PEqualNP.TopForm.NoFourCycle x2 → {x7 ∈ x5 | ∃ (x8 : Fin x1) (x9 : Fin x1), x7 = s(x8, x9) ∧ ∃ x10 < x4.gates.length, ∃ (x11 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x1 x4 (x1 + x10)).card ∧ (∀ x12 ∈ PEqualNP.TopForm.orIn x1 x4 (x1 + x10), x2.Adj x8 x12) ∧ PEqualNP.TopForm.orIn x1 x4 (PEqualNP.TopForm.opnd x4 x10 x11) = {x9}}.card ≤ (2 : ℕ) * x4.size := by
  intro n G _ C E h4
  classical
  let S : ℕ × Fin 2 → Finset (Sym2 (Fin n)) := fun p => E.filter (fun e => ∃ (a : Fin n) (c : Fin n),
    e = s(a, c) ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + p.1)).card ∧
    (∀ x ∈ PEqualNP.TopForm.orIn n C (n + p.1), G.Adj a x) ∧
    PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C p.1 p.2) = {c})
  have hS : ∀ p, (S p).card ≤ 1 := by
    intro p
    rw [Finset.card_le_one]
    intro e he e' he'
    simp only [S, Finset.mem_filter] at he he'
    obtain ⟨-, a, c, rfl, hA, ha, hc⟩ := he
    obtain ⟨-, a', c', rfl, -, ha', hc'⟩ := he'
    have hcc : c = c' := by
      rw [hc] at hc'
      exact Finset.singleton_injective hc'
    have haa : a = a' := PEqualNP.Outside.L_meta_2577.uniq G h4 _ hA a a' ha ha'
    rw [hcc, haa]
  refine le_trans (Finset.card_le_card (t := (Finset.range C.gates.length ×ˢ
    (Finset.univ : Finset (Fin 2))).biUnion S) ?_) ?_
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨heE, a, c, hac, j, hj, b, hA, ha, hc⟩ := he
    rw [Finset.mem_biUnion]
    refine ⟨(j, b), ?_, ?_⟩
    · simp [hj]
    · simp only [S, Finset.mem_filter]
      exact ⟨heE, a, c, hac, hA, ha, hc⟩
  · refine le_trans Finset.card_biUnion_le ?_
    refine le_trans (Finset.sum_le_sum (fun p _ => hS p)) ?_
    simp [PEqualNP.CircuitLowerBounds.Circuit.size, mul_comm]
