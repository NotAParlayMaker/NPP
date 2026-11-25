import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CrossAnd PEqualNP.GenericRejection

-- A cross AND can be replaced at no gate cost whenever an OR over a sublist
-- of its current operands has the same effect on the circuit output.
theorem PEqualNP.Outside.R_meta_4594_1
    (price : ∀ (n : ℕ) (M : Finset (Fin n)) (C : Circuit) (j : ℕ) (ins : List ℕ),
      Monotone2 C → j < C.size → IsCrossAnd n M C j → ins.Sublist (gateAt C j).inputs →
      let D : Circuit := ⟨C.gates.set j ⟨.or,ins⟩,C.output⟩
      Monotone2 D ∧ crossCount n M D < crossCount n M C ∧ D.size = C.size)
    (residual : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      199 ≤ q → N = q^2+q+1 → (∀ l, (S l).card=q+1) →
      (∀ l m, l ≠ m → (S l ∩ S m).card ≤ 1) → Monotone2 C → ComputesIncidence S C →
      let M := Finset.univ.map (Fin.natAddEmb N)
      2*C.size < N*q → 0 < crossCount (N+N) M C →
      (∀ j < C.size, IsCrossAnd (N+N) M C j → ∀ ins : List ℕ,
        ins.Sublist (gateAt C j).inputs →
        ¬ ComputesIncidence S ⟨C.gates.set j ⟨.or,ins⟩,C.output⟩) →
      ∃ D : Circuit, Monotone2 D ∧ ComputesIncidence S D ∧
        crossCount (N+N) M D < crossCount (N+N) M C ∧ D.size ≤ C.size + 49) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (199 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → (x3 x8 ∩ x3 x9).card ≤ (1 : ℕ)) →           PEqualNP.MetaComplexity.Monotone2 x4 →             PEqualNP.GenericRejection.ComputesIncidence x3 x4 →               have x11 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := PEqualNP.CrossAnd.crossCount (x2 + x2) (Finset.map (Fin.natAddEmb x2) Finset.univ);               (2 : ℕ) * x4.size < x2 * x1 → (0 : ℕ) < x11 x4 → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ PEqualNP.GenericRejection.ComputesIncidence x3 x14 ∧ x11 x14 < x11 x4 ∧ x14.size ≤ x4.size + (49 : ℕ) := by
  classical
  intro q N S C hq hN degree meet mono correct cost size positive
  let M : Finset (Fin (N+N)) := Finset.univ.map (Fin.natAddEmb N)
  by_cases h : ∃ j < C.size, IsCrossAnd (N+N) M C j ∧ ∃ ins : List ℕ,
      ins.Sublist (gateAt C j).inputs ∧
      ComputesIncidence S ⟨C.gates.set j ⟨.or,ins⟩,C.output⟩
  · obtain ⟨j,hj,hcross,ins,hsub,hvalue⟩ := h
    obtain ⟨mono',less,eq⟩ := price (N+N) M C j ins mono hj hcross hsub
    exact ⟨⟨C.gates.set j ⟨.or,ins⟩,C.output⟩,mono',hvalue,less,by omega⟩
  · apply residual q N S C hq hN degree meet mono correct size positive
    intro j hj hcross ins hsub hval
    exact h ⟨j,hj,hcross,ins,hsub,hval⟩
