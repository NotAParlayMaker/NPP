import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_3807_317
    (rectangle : ∀ (n : ℕ) (C : Circuit) (j : ℕ), IsAO2 n C → j < C.size →
      (gateAt C j).op = GateOp.and →
      (∀ i < C.size, InCone n C i j → (gateAt C i).op = GateOp.or) →
      ∀ u v : Fin n, gateVal n C j (pairInput u v) = true →
        (u ∈ side C j 0 ∨ v ∈ side C j 0) ∧ (u ∈ side C j 1 ∨ v ∈ side C j 1))
    (count : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) → G.edgeFinset.Nonempty →
      ∀ C : Circuit, IsLeastAO G C → PEqualNP.TopForm.TopForm G C → 3 ≤ (junk G C).card →
      (∀ j ∈ junk G C, ∀ k ∈ junk G C, ¬ InCone n C j k) →
      ∀ E : Finset (Sym2 (Fin n)), (∀ e, e ∈ E ↔ e ∈ Ustar G C ∧ ∃ u v : Fin n, e = s(u, v) ∧
          ∃ a ∈ tops G C, ∃ j ∈ junk G C, ∃ k ∈ junk G C, j ≠ k ∧
            OrReaches n C (opnd C a 0) j ∧ OrReaches n C (opnd C a 1) k ∧
            ((u ∈ side C j 0 ∨ v ∈ side C j 0) ∧ (u ∈ side C j 1 ∨ v ∈ side C j 1)) ∧
            ((u ∈ side C k 0 ∨ v ∈ side C k 0) ∧ (u ∈ side C k 1 ∨ v ∈ side C k 1))) →
        E.card ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∀ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x13 ∈ PEqualNP.TopForm.junk x3 x7, ¬PEqualNP.EdgeOwnership.InCone x2 x7 x11 x13) → {x12 ∈ PEqualNP.TopForm.Ustar x3 x7 | ∃ (x13 : Fin x2) (x14 : Fin x2), x12 = s(x13, x14) ∧ ∃ x15 ∈ PEqualNP.TopForm.tops x3 x7, ∃ x16 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x17 ∈ PEqualNP.TopForm.junk x3 x7, x16 ≠ x17 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x15 (0 : Fin (2 : ℕ))) x16 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 x15 (1 : Fin (2 : ℕ))) x17 ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x16 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 x17 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  have pure :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      (∀ j ∈ junk G C, ∀ k ∈ junk G C, ¬ InCone n C j k) →
      ∀ j ∈ junk G C, j < C.size ∧ (gateAt C j).op = GateOp.and ∧
        ∀ i < C.size, InCone n C i j → (gateAt C i).op = GateOp.or := by
    intro n G _ C hLeast hTop hAnti j hj
    have hMem (k : ℕ) : k ∈ junk G C ↔ k < C.size ∧ IsDirtyAnd n G C k := by
      change k ∈ (Finset.range C.size).filter (IsDirtyAnd n G C) ↔ _
      rw [Finset.mem_filter, Finset.mem_range]
    obtain ⟨hjSize, hjDirty⟩ := (hMem j).1 hj
    have hjAnd : (gateAt C j).op = GateOp.and := hjDirty.1
    refine ⟨hjSize, hjAnd, ?_⟩
    intro i hi hCone
    have hi' : i < C.gates.length := hi
    have hAt : gateAt C i = C.gates[i] := List.getD_eq_getElem _ _ hi'
    have hGateMem : gateAt C i ∈ C.gates := by
      rw [hAt]
      exact List.getElem_mem hi'
    rcases hLeast.1.1 (gateAt C i) hGateMem with hAnd | hOr
    · exfalso
      by_cases hBelow : BelowF G C i
      · exact hTop i hi j hjSize hAnd hBelow hjAnd hCone
      · have hWitness : ∃ x : Fin n → Bool,
            gateVal n C i x = true ∧ graphFun G ∅ x = false := by
          by_contra hNone
          apply hBelow
          intro x hx
          cases hF : graphFun G ∅ x with
          | false => exact (hNone ⟨x, hx, hF⟩).elim
          | true => rfl
        have hiJunk : i ∈ junk G C := (hMem i).2 ⟨hi, hAnd, hi, hWitness⟩
        exact hAnti i hiJunk j hj hCone
    · exact hOr
  obtain ⟨c, hCount⟩ := count
  refine ⟨c, ?_⟩
  intro n G _ hCycle hEdge C hLeast hTop hThree hAnti
  have hValid := pure n G C hLeast hTop hAnti
  classical
  let E := (Ustar G C).filter (fun e => ∃ u v : Fin n, e = s(u, v) ∧
          ∃ a ∈ tops G C, ∃ j ∈ junk G C, ∃ k ∈ junk G C, j ≠ k ∧
            OrReaches n C (opnd C a 0) j ∧ OrReaches n C (opnd C a 1) k ∧
            ((u ∈ side C j 0 ∨ v ∈ side C j 0) ∧ (u ∈ side C j 1 ∨ v ∈ side C j 1)) ∧
            ((u ∈ side C k 0 ∨ v ∈ side C k 0) ∧ (u ∈ side C k 1 ∨ v ∈ side C k 1)))
  have hBound := hCount n G hCycle hEdge C hLeast hTop hThree hAnti E (fun _ => Finset.mem_filter)
  refine (Finset.card_le_card ?_).trans hBound
  intro e he
  obtain ⟨hU, u, v, he, a, ha, j, hj, k, hk, hne, hL, hR, hjv, hkv⟩ := Finset.mem_filter.mp he
  have hjPure := hValid j hj
  have hkPure := hValid k hk
  have hjHit := rectangle n C j hLeast.1 hjPure.1 hjPure.2.1 hjPure.2.2 u v hjv
  have hkHit := rectangle n C k hLeast.1 hkPure.1 hkPure.2.1 hkPure.2.2 u v hkv
  exact Finset.mem_filter.mpr ⟨hU, u, v, he, a, ha, j, hj, k, hk, hne, hL, hR, hjHit, hkHit⟩
