import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2998
open PEqualNP.CircuitLowerBounds

theorem step (gs : List Gate) (op : GateOp) (o a b : ℕ) (x : List Bool) :
    Circuit.eval ⟨⟨op, [a, b]⟩ :: gs, o⟩ x
      = Circuit.eval ⟨gs, o⟩ (x ++ [op.eval [x.getD a false, x.getD b false]]) := by
  simp [Circuit.eval, Circuit.wires]

end PEqualNP.Outside.L_meta_2998

open PEqualNP.Outside.L_meta_2998 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2998 : ∀ (x1 : Type) (x2 x3 : ℕ) (x4 : ℕ → Set x1), (∀ x5 < x3, ∃ x7 < x2 + x5, ∃ x8 < x2 + x5, x4 (x2 + x5) = x4 x7 ∪ x4 x8 ∨ x4 (x2 + x5) = x4 x7 ∨ x4 (x2 + x5) = ∅ ∨ x4 (x2 + x5) = x4 x7 ∩ x4 x8) → ∃ (x6 : ℕ → Set (Finset ℕ)), (∀ x7 < x2, x6 x7 = {{x7}}) ∧ (∀ x7 < x3, ∃ x9 < x2 + x7, ∃ x10 < x2 + x7, x6 (x2 + x7) = Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x6 x9) (x6 x10) ∨ x6 (x2 + x7) = x6 x9 ∨ x6 (x2 + x7) = {∅} ∨ x6 (x2 + x7) = x6 x9 ∪ x6 x10) ∧ ∀ x7 < x2 + x3, (∀ x9 ∈ x6 x7, ∀ x11 ∈ x9, x11 < x2) ∧ ∀ (x9 : x1), x9 ∉ x4 x7 ↔ ∃ x10 ∈ x6 x7, ∀ x11 ∈ x10, x9 ∉ x4 x11 := by
  intro α n m X hX
  have main : ∀ k ≤ m, ∃ x6 : ℕ → Set (Finset ℕ), (∀ i < n, x6 i = {{i}}) ∧
      (∀ j < k, ∃ a < n + j, ∃ b < n + j,
        x6 (n + j) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (x6 a) (x6 b) ∨ x6 (n + j) = x6 a ∨
          x6 (n + j) = {∅} ∨ x6 (n + j) = x6 a ∪ x6 b) ∧
      ∀ w < n + k, (∀ F ∈ x6 w, ∀ i ∈ F, i < n) ∧
        ∀ x : α, x ∉ X w ↔ ∃ F ∈ x6 w, ∀ i ∈ F, x ∉ X i := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun i => {{i}}, fun i _ => rfl, fun j hj => absurd hj (by omega), ?_⟩
      intro w _
      refine ⟨?_, ?_⟩
      · intro F hF i hi
        rw [Set.mem_singleton_iff] at hF
        subst hF
        rw [Finset.mem_singleton] at hi
        omega
      · intro x
        constructor
        · intro h
          exact ⟨{w}, rfl, fun i hi => by rw [Finset.mem_singleton] at hi; rw [hi]; exact h⟩
        · rintro ⟨F, hF, h⟩
          rw [Set.mem_singleton_iff] at hF
          subst hF
          exact h w (Finset.mem_singleton_self w)
    | succ k ih =>
      intro hk
      obtain ⟨x6, hin, hg, hw⟩ := ih (by omega)
      have step : ∀ (V : Set (Finset ℕ)) (a b : ℕ), a < n + k → b < n + k →
          (V = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (x6 a) (x6 b) ∨ V = x6 a ∨ V = {∅} ∨ V = x6 a ∪ x6 b) →
          ((∀ F ∈ V, ∀ i ∈ F, i < n) ∧ ∀ x : α, x ∉ X (n + k) ↔ ∃ F ∈ V, ∀ i ∈ F, x ∉ X i) →
          ∃ x6' : ℕ → Set (Finset ℕ), (∀ i < n, x6' i = {{i}}) ∧
            (∀ j < k + 1, ∃ a < n + j, ∃ b < n + j,
              x6' (n + j) = Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (x6' a) (x6' b) ∨ x6' (n + j) = x6' a ∨
                x6' (n + j) = {∅} ∨ x6' (n + j) = x6' a ∪ x6' b) ∧
            ∀ w < n + (k + 1), (∀ F ∈ x6' w, ∀ i ∈ F, i < n) ∧
              ∀ x : α, x ∉ X w ↔ ∃ F ∈ x6' w, ∀ i ∈ F, x ∉ X i := by
        intro V a b ha hb hV hprop
        have fw : ∀ w, w < n + k → Function.update x6 (n + k) V w = x6 w :=
          fun w hlt => Function.update_of_ne (by omega) _ _
        have fk : Function.update x6 (n + k) V (n + k) = V := Function.update_self _ _ _
        refine ⟨Function.update x6 (n + k) V, ?_, ?_, ?_⟩
        · intro i hi
          rw [fw i (by omega)]
          exact hin i hi
        · intro j hj
          by_cases hjk : j < k
          · obtain ⟨a', ha', b', hb', h⟩ := hg j hjk
            refine ⟨a', ha', b', hb', ?_⟩
            rw [fw (n + j) (by omega), fw a' (by omega), fw b' (by omega)]
            exact h
          · have hje : j = k := by omega
            subst hje
            refine ⟨a, ha, b, hb, ?_⟩
            rw [fk, fw a ha, fw b hb]
            exact hV
        · intro w hlt
          by_cases hwk : w < n + k
          · rw [fw w hwk]
            exact hw w hwk
          · have hwe : w = n + k := by omega
            subst hwe
            rw [fk]
            exact hprop
      obtain ⟨a, ha, b, hb, hcase⟩ := hX k (by omega)
      obtain ⟨ba, ia⟩ := hw a ha
      obtain ⟨bb, ib⟩ := hw b hb
      rcases hcase with h | h | h | h
      · refine step (Set.image2 (fun (u v : Finset ℕ) => u ∪ v) (x6 a) (x6 b)) a b ha hb (Or.inl rfl) ⟨?_, ?_⟩
        · rintro F ⟨F1, hF1, F2, hF2, rfl⟩ i hi
          rcases Finset.mem_union.mp hi with h1 | h1
          · exact ba F1 hF1 i h1
          · exact bb F2 hF2 i h1
        · intro x
          rw [h, Set.mem_union, not_or]
          constructor
          · rintro ⟨h1, h2⟩
            obtain ⟨F1, hF1, g1⟩ := (ia x).mp h1
            obtain ⟨F2, hF2, g2⟩ := (ib x).mp h2
            exact ⟨F1 ∪ F2, ⟨F1, hF1, F2, hF2, rfl⟩, fun i hi =>
              (Finset.mem_union.mp hi).elim (g1 i) (g2 i)⟩
          · rintro ⟨F, ⟨F1, hF1, F2, hF2, rfl⟩, hF⟩
            exact ⟨(ia x).mpr ⟨F1, hF1, fun i hi => hF i (Finset.mem_union_left _ hi)⟩,
              (ib x).mpr ⟨F2, hF2, fun i hi => hF i (Finset.mem_union_right _ hi)⟩⟩
      · refine step (x6 a) a b ha hb (Or.inr (Or.inl rfl)) ⟨ba, ?_⟩
        intro x
        rw [h]
        exact ia x
      · refine step {∅} a b ha hb (Or.inr (Or.inr (Or.inl rfl))) ⟨?_, ?_⟩
        · intro F hF i hi
          rw [Set.mem_singleton_iff] at hF
          subst hF
          exact absurd hi (Finset.notMem_empty i)
        · intro x
          rw [h]
          constructor
          · intro _
            exact ⟨∅, rfl, fun i hi => absurd hi (Finset.notMem_empty i)⟩
          · intro _ hx
            exact hx
      · refine step (x6 a ∪ x6 b) a b ha hb (Or.inr (Or.inr (Or.inr rfl))) ⟨?_, ?_⟩
        · intro F hF i hi
          rcases hF with hF | hF
          · exact ba F hF i hi
          · exact bb F hF i hi
        · intro x
          rw [h, Set.mem_inter_iff, not_and_or]
          constructor
          · rintro (h1 | h1)
            · obtain ⟨F, hF, g⟩ := (ia x).mp h1
              exact ⟨F, Or.inl hF, g⟩
            · obtain ⟨F, hF, g⟩ := (ib x).mp h1
              exact ⟨F, Or.inr hF, g⟩
          · rintro ⟨F, hF | hF, g⟩
            · exact Or.inl ((ia x).mpr ⟨F, hF, g⟩)
            · exact Or.inr ((ib x).mpr ⟨F, hF, g⟩)
  obtain ⟨x6, h1, h2, h3⟩ := main m (le_refl m)
  exact ⟨x6, h1, h2, h3⟩
