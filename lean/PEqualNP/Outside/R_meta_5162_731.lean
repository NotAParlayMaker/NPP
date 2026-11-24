import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5162_731
    (cleanBound :
      let neg (Q : Finset (Fin 13)) :=
        List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
          List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))
      let good (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧
        (∀ p l : Fin 13, p ∈ singerLines3 l →
          C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
        ∀ Q, IsQuadrangle singerLines3 Q → C.eval (neg Q) = false
      ∀ C, good C → (∀ D, good D → C.size ≤ D.size) →
        andPairs 26 C = 1 →
        (∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j ∧
          ∀ Q, IsQuadrangle singerLines3 Q → (C.wires (neg Q)).getD (26 + i) false = false) →
        64 ≤ C.size)
    (dirtyBound :
      let neg (Q : Finset (Fin 13)) :=
        List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
          List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))
      let good (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧
        (∀ p l : Fin 13, p ∈ singerLines3 l →
          C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++
            List.ofFn (fun v : Fin 13 => decide (v = l))) = true) ∧
        ∀ Q, IsQuadrangle singerLines3 Q → C.eval (neg Q) = false
      ∀ C, good C → (∀ D, good D → C.size ≤ D.size) →
        andPairs 26 C = 1 →
        (∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j ∧
          ∃ Q, IsQuadrangle singerLines3 Q ∧ (C.wires (neg Q)).getD (26 + i) false = true) →
        64 ≤ C.size) :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3.size ≤ x5.size) → PEqualNP.TopForm.andPairs (26 : ℕ) x3 = (1 : ℕ) → (64 : ℕ) ≤ x3.size := by
  intro neg good C valid least one
  letI : DecidableEq GateOp := gateOpDecEq
  let pairs := ((Finset.range C.gates.length).product (Finset.range C.gates.length)).filter fun p : ℕ × ℕ =>
    (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 26 C p.1 p.2
  have nonempty : pairs.Nonempty := Finset.card_pos.mp (by
    change 0 < andPairs 26 C
    omega)
  obtain ⟨⟨i, j⟩, member⟩ := nonempty
  obtain ⟨_, inner, outer, nested⟩ := Finset.mem_filter.mp member
  by_cases witness : ∃ Q, IsQuadrangle singerLines3 Q ∧
      (C.wires (neg Q)).getD (26 + i) false = true
  · exact dirtyBound C valid least one ⟨i, j, inner, outer, nested, witness⟩
  · exact cleanBound C valid least one ⟨i, j, inner, outer, nested,
      fun Q hQ => Bool.eq_false_iff.mpr (fun h => witness ⟨Q, hQ, h⟩)⟩
