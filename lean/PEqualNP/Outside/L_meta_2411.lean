import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2411

theorem core {α β : Type} (A : Finset (α × β)) (T : Set ℕ) (hfin : T.Finite) (g0 g1 : ℕ → ℕ)
    (P : α → ℕ → Prop) (Q : β → ℕ → Prop)
    (h : ∀ e ∈ A, ∃ (j a b : ℕ), (j ∈ T ∧ ((g0 j = a ∧ g1 j = b) ∨ (g0 j = b ∧ g1 j = a))) ∧
      {x : α | P x a} = {e.1} ∧ {y : β | Q y b} = {e.2}) :
    A.card ≤ 2 * T.ncard := by
  classical
  choose! j a b hj using h
  have key : A.card ≤ (hfin.toFinset ×ˢ (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (fun e => (j e, decide (g0 (j e) = a e)))
    · intro e he
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr
        ⟨hfin.mem_toFinset.mpr (hj e he).1.1, Finset.mem_univ _⟩)
    · intro e he e1 he1 heq
      simp only [Prod.mk.injEq, decide_eq_decide] at heq
      obtain ⟨hjj, hside⟩ := heq
      obtain ⟨⟨_, hab⟩, h1, h2⟩ := hj e he
      obtain ⟨⟨_, hab1⟩, h11, h21⟩ := hj e1 he1
      rw [← hjj] at hab1 hside
      have haa : a e = a e1 ∧ b e = b e1 := by
        by_cases hc : g0 (j e) = a e
        · have hc1 := hside.mp hc
          refine ⟨hc.symm.trans hc1, ?_⟩
          rcases hab with ⟨_, hb⟩ | ⟨hb, ha⟩ <;> rcases hab1 with ⟨_, hb1⟩ | ⟨hb1, ha1⟩ <;> omega
        · have hc1 : ¬ g0 (j e) = a e1 := fun x => hc (hside.mpr x)
          rcases hab with ⟨ha, _⟩ | ⟨hb, ha⟩
          · exact absurd ha hc
          rcases hab1 with ⟨ha1, _⟩ | ⟨hb1, ha1⟩
          · exact absurd ha1 hc1
          exact ⟨ha.symm.trans ha1, hb.symm.trans hb1⟩
      rw [← haa.1] at h11
      rw [← haa.2] at h21
      exact Prod.ext (Set.singleton_injective (h1.symm.trans h11))
        (Set.singleton_injective (h2.symm.trans h21))
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool,
    ← Set.ncard_eq_toFinset_card T hfin] at key
  omega

end PEqualNP.Outside.L_meta_2411

theorem PEqualNP.Outside.L_meta_2411 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (A : Finset (Fin N × Fin M)), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ e ∈ A, ∃ (j a b : ℕ), (j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = a))) ∧ {x1 : Fin N | R (pw x1) a} = {e.1} ∧ {y1 : Fin M | R (lw y1) b} = {e.2}) → A.card ≤ 2 * {ja : ℕ | ja < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro n N M pw lw C A _ R _ h
  have hfin : {ja : ℕ | ja < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C ja).op = PEqualNP.CircuitLowerBounds.GateOp.and}.Finite :=
    (Set.finite_lt_nat C.gates.length).subset (fun x hx => hx.1)
  refine PEqualNP.Outside.L_meta_2411.core A _ hfin
    (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0)
    (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0)
    (fun x a => R (pw x) a) (fun y b => R (lw y) b) ?_
  intro e he
  obtain ⟨j, a, b, ⟨hj, hop, hab⟩, h1, h2⟩ := h e he
  exact ⟨j, a, b, ⟨⟨hj, hop⟩, hab⟩, h1, h2⟩
