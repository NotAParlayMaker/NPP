import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_8287 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 x7 : Fin x1), x2.Adj x6 x7 → x6 ∉ x3) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → ∀ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∈ x8 ∨ x10 ∈ x8) → (Finset.univ \ x3).card / (2 : ℕ) ≤ x8.card := by
  classical
  intro n G S _ hdeg hS _ C hC
  have hd : ∀ v, G.degree v = if v ∈ S then 0 else 3 := by
    intro v
    split_ifs with h
    · rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      exact hS v w hw h
    · rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hdeg v h, ← Set.ncard_coe_finset, SimpleGraph.coe_neighborFinset]
  have hle : ∀ v, G.degree v ≤ 3 := by
    intro v; rw [hd v]; split_ifs <;> omega
  have h2 : 2 * G.edgeFinset.card = 3 * (Finset.univ \ S).card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    simp only [hd]
    rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, smul_eq_mul, zero_add, mul_comm]
    congr 2
    ext v; simp
  have hsub : G.edgeFinset ⊆ C.biUnion (fun v => G.incidenceFinset v) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rw [Finset.mem_biUnion]
      rcases hC a b he with h | h
      · exact ⟨a, h, by rw [SimpleGraph.mem_incidenceFinset]; exact ⟨he, Sym2.mem_mk_left a b⟩⟩
      · exact ⟨b, h, by rw [SimpleGraph.mem_incidenceFinset]; exact ⟨he, Sym2.mem_mk_right a b⟩⟩
  have h3 : G.edgeFinset.card ≤ 3 * C.card := by
    calc G.edgeFinset.card ≤ (C.biUnion (fun v => G.incidenceFinset v)).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ C, (G.incidenceFinset v).card := Finset.card_biUnion_le
      _ ≤ ∑ v ∈ C, 3 := Finset.sum_le_sum (fun v _ => by rw [SimpleGraph.card_incidenceFinset_eq_degree]; exact hle v)
      _ = 3 * C.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega
