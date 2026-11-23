import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_708 : ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∃ (m' : ℕ) (e : Fin m' → Fin m), m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧ Function.Injective e ∧ (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧ (∀ i : Fin m', (S (e i)).card = q + 1) ∧ (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1) := by
  intro n m q S y h1 h2
  have hr := Finset.range_orderEmbOfFin (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)) rfl
  refine ⟨_, fun i => (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).orderEmbOfFin rfl i, rfl, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact ((Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).orderEmbOfFin rfl).injective hab
  · intro w
    have h : w ∈ Set.range ((Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).orderEmbOfFin rfl) ↔ w ∈ ((Finset.univ.filter (fun w : Fin m => Disjoint (S w) y) : Finset (Fin m)) : Set (Fin m)) := by
      rw [hr]
    rw [Set.mem_range] at h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h
    exact h.symm
  · intro i
    exact h1 _
  · intro i j hij
    apply h2
    intro h
    exact hij (((Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).orderEmbOfFin rfl).injective h)
