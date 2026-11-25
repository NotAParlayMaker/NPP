import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2685_1
    (h1 : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)),
    (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
    let small := fun (F : (Fin (n+m) → Bool) → Bool) =>
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)), A.card + B.card ≤ 4 ∧
        ∀ p l, (p,l) ∉ E → (∀ z, z (Fin.castAdd m p) = true → z (Fin.natAdd n l) = true → F z = true) → p ∈ A ∨ l ∈ B
    ∀ F G, (∀ z, F z = true → G z = true → (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) → small F ∨ small G)
    (h2 : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) → PEqualNP.TopForm.IsAO2 (n+m) C →
    (∀ z, PEqualNP.MetaComplexity.circuitFun (n+m) C z = decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
    let small := fun (F : (Fin (n+m) → Bool) → Bool) =>
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)), A.card + B.card ≤ 4 ∧
        ∀ p l, (p,l) ∉ E → (∀ z, z (Fin.castAdd m p) = true → z (Fin.natAdd n l) = true → F z = true) → p ∈ A ∨ l ∈ B
    let W := PEqualNP.CleanedNonEdge.wireVal (n+m) C
    (∀ a b, (∀ z, W a z = true → W b z = true → PEqualNP.MetaComplexity.circuitFun (n+m) C z = true) →
      small (W a) ∨ small (W b)) →
    ∃ (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧
      E.card + A.card + B.card ≤ C.size + 1)
    (h3 : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (A : Finset (Fin n)) (B : Finset (Fin m)), (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (S : Bool → Finset ℕ),
        PEqualNP.TopForm.IsAO2 (n+m) D ∧ D.size ≤ E.card + A.card + B.card - 1 ∧
        (∀ z, PEqualNP.MetaComplexity.circuitFun (n+m) D z = decide (∃ p l, (p,l) ∈ E ∧
          z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) ∧
        let g := PEqualNP.MetaComplexity.NestedCover.gateAt D
        (∀ t w, w ∈ S t → (w < n+m ∧ decide (n ≤ w) = t) ∨
          ∃ i < D.size, w = n+m+i ∧ (g i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (g i).inputs, u ∈ S t) ∧
        ∀ i < D.size, (g i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ a b t, (g i).inputs = [a,b] ∧ a ∈ S t ∧ b ∈ S (!t)) : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  classical
  intro n m I _ C square ao correct
  let E : Finset (Fin n × Fin m) := Finset.univ.filter fun e => I e.1 e.2
  have mem (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by simp [E]
  have sq : ∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E) := by
    simpa only [mem] using square
  obtain ⟨A,B,cover,budget⟩ := h2 n m E C sq ao (by simpa only [mem] using correct) (by
    intro a b below
    apply h1 n m E sq
    intro z ha hb
    have hout := below z ha hb
    rw [correct z, decide_eq_true_eq] at hout
    simpa only [mem] using hout)
  obtain ⟨D,S,strict,size,eval,closed,ands⟩ := h3 n m E A B cover
  refine ⟨D,S false,S true,strict,by simpa only [mem] using eval,by omega,?_,?_,?_⟩
  · intro w hw
    rcases closed false w hw with ⟨_,side⟩ | gate
    · exact Or.inl (by simpa using side)
    · exact Or.inr gate
  · intro w hw
    rcases closed true w hw with ⟨bound,side⟩ | gate
    · exact Or.inl ⟨by simpa using side,bound⟩
    · exact Or.inr gate
  · intro i hi hand
    obtain ⟨a,b,t,inputs,ha,hb⟩ := ands i hi hand
    refine ⟨a,b,inputs,?_⟩
    cases t with
    | false => exact Or.inl ⟨ha,hb⟩
    | true => exact Or.inr ⟨ha,hb⟩
