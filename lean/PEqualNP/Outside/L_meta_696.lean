import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L663

namespace PEqualNP.Outside.L_meta_696

private lemma countPairs {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop) [∀ a b, Decidable (r a b)] :
    (∑ b ∈ t, (s.filter (fun a => r a b)).card) =
      ((s ×ˢ t).filter (fun e => r e.1 e.2)).card := by
  simp only [Finset.card_filter, Finset.sum_product_right]

end PEqualNP.Outside.L_meta_696

theorem PEqualNP.Outside.L_meta_696 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → (∀ g ∈ C.gates, g.inputs.length ≤ 2) → (∀ (x : Fin P → Bool) (y : Fin L → Bool), C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ (p : Fin P) (w : Fin L), inc p w = true ∧ x p = true ∧ y w = true)) → (Finset.univ.filter (fun e : Fin P × Fin L => inc e.1 e.2 = true)).card ≤ ((Finset.range (P + L + C.gates.length) ×ˢ (Finset.univ : Finset (Fin L))).filter (fun e : ℕ × Fin L => PEqualNP.LowMerge.IsLowMerge P L inc C e.1 e.2)).card + L := by
  intro P L inc C hMono hFan hComputes
  have total := Finset.sum_le_sum (s := Finset.univ) (fun w _ =>
    PEqualNP.MetaComplexity.L663 P L inc C hMono hFan hComputes w)
  rw [Finset.sum_add_distrib] at total
  simpa only [PEqualNP.Outside.L_meta_696.countPairs, Finset.univ_product_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using total
