import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L663

theorem PEqualNP.Outside.L_meta_696 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → (∀ g ∈ C.gates, g.inputs.length ≤ 2) → (∀ (x : Fin P → Bool) (y : Fin L → Bool), C.eval (List.ofFn x ++ List.ofFn y) = decide (∃ (p : Fin P) (w : Fin L), inc p w = true ∧ x p = true ∧ y w = true)) → (Finset.univ.filter (fun e : Fin P × Fin L => inc e.1 e.2 = true)).card ≤ ((Finset.range (P + L + C.gates.length) ×ˢ (Finset.univ : Finset (Fin L))).filter (fun e : ℕ × Fin L => PEqualNP.LowMerge.IsLowMerge P L inc C e.1 e.2)).card + L := by
  intro P L inc C hC hfan hcomp
  have key := PEqualNP.MetaComplexity.L663 P L inc C hC hfan hcomp
  have h1 : (Finset.univ.filter (fun e : Fin P × Fin L => inc e.1 e.2 = true)).card
      = ∑ w : Fin L, (Finset.univ.filter (fun p : Fin P => inc p w = true)).card := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  have h2 : ((Finset.range (P + L + C.gates.length) ×ˢ (Finset.univ : Finset (Fin L))).filter
        (fun e : ℕ × Fin L => PEqualNP.LowMerge.IsLowMerge P L inc C e.1 e.2)).card
      = ∑ w : Fin L, ((Finset.range (P + L + C.gates.length)).filter
          (fun g => PEqualNP.LowMerge.IsLowMerge P L inc C g w)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_product, Finset.sum_comm]
  rw [h1, h2]
  calc ∑ w : Fin L, (Finset.univ.filter (fun p : Fin P => inc p w = true)).card
      ≤ ∑ w : Fin L, (((Finset.range (P + L + C.gates.length)).filter
          (fun g => PEqualNP.LowMerge.IsLowMerge P L inc C g w)).card + 1) :=
        Finset.sum_le_sum (fun w _ => key w)
    _ = ∑ w : Fin L, ((Finset.range (P + L + C.gates.length)).filter
          (fun g => PEqualNP.LowMerge.IsLowMerge P L inc C g w)).card + L := by
        rw [Finset.sum_add_distrib]
        simp
