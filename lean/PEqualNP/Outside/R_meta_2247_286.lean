import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.NotPremium

-- Among least candidates, minimize nested AND pairs.
-- A gate needed on at most one positive input can be replaced by an incident pair.
-- The remaining case has two distinct necessary positive inputs per inner AND.
theorem PEqualNP.Outside.R_meta_2247_286
    (flat : let neg (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
      let good (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs singerLines3 C ∧
        ∀ Q, IsQuadrangle singerLines3 Q → C.eval (neg Q) = false
      ∀ C, good C → andPairs 26 C = 0 → 64 ≤ C.size)
    (cleanMove : let neg (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
      let good (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs singerLines3 C ∧
        ∀ Q, IsQuadrangle singerLines3 Q → C.eval (neg Q) = false
      let nested (C : Circuit) (i j : ℕ) := (gateAt C i).op = .and ∧
        (gateAt C j).op = .and ∧ InCone 26 C i j
      let clean (C : Circuit) (i : ℕ) := ∀ Q, IsQuadrangle singerLines3 Q →
        (C.wires (neg Q)).getD (26 + i) false = false
      ∀ C, good C → (∃ i j, nested C i j ∧ clean C i) →
        ∃ D, good D ∧ (D.size < C.size ∨ D.size = C.size ∧ andPairs 26 D < andPairs 26 C))
    (sparse : let neg (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
      let good (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs singerLines3 C ∧
        ∀ Q, IsQuadrangle singerLines3 Q → C.eval (neg Q) = false
      let nested (C : Circuit) (i j : ℕ) := (gateAt C i).op = .and ∧
        (gateAt C j).op = .and ∧ InCone 26 C i j
      let loses (C : Circuit) (i : ℕ) (p : Fin 13 × Fin 13) :=
        p.1 ∈ singerLines3 p.2 ∧
        ({C with gates := replaceByConst C.gates i false} : Circuit).eval (incidenceInput {p.1} {p.2}) = false
      ∀ C i j, good C → nested C i j →
        (∀ p q, loses C i p → loses C i q → p = q) →
        ∃ D, good D ∧ D.size = C.size ∧ andPairs 26 D ≤ andPairs 26 C ∧ nested D i j ∧
          ∀ Q, IsQuadrangle singerLines3 Q → (D.wires (neg Q)).getD (26 + i) false = false)
    (dense : let neg (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
      let good (C : Circuit) := Monotone2 C ∧ ReadsBack 26 C ∧ RightOnIncidentPairs singerLines3 C ∧
        ∀ Q, IsQuadrangle singerLines3 Q → C.eval (neg Q) = false
      let nested (C : Circuit) (i j : ℕ) := (gateAt C i).op = .and ∧
        (gateAt C j).op = .and ∧ InCone 26 C i j
      let loses (C : Circuit) (i : ℕ) (p : Fin 13 × Fin 13) :=
        p.1 ∈ singerLines3 p.2 ∧
        ({C with gates := replaceByConst C.gates i false} : Circuit).eval (incidenceInput {p.1} {p.2}) = false
      ∀ C, good C → C.size < 64 →
        (∀ D, good D → C.size ≤ D.size ∧ (D.size = C.size → andPairs 26 C ≤ andPairs 26 D)) →
        (∃ i j, nested C i j) →
        (∀ i j, nested C i j → ∃ p q, loses C i p ∧ loses C i q ∧ p ≠ q) → False) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 ∧ x5.size < x4.size; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ x6 < x5.gates.length,     have x8 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6;     have x9 : Bool := !x8.op.eval [];     ∀ x10 ∈ x8.inputs, ∃ (x12 : List Bool), x2 x9 x12 ∧ (x5.wires x12).getD x10 Bool.false = !x9 ∧ (x5.wires x12).getD ((26 : ℕ) + x6) Bool.false = x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x5 x6 → x6.size < (64 : ℕ) → (∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x6 x10 x11) → x4 x6 := by
  intro d tests valid smaller _ C hC _ hsmall _
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  let neg (Q : Finset (Fin 13)) :=
    List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
      List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))
  let good (D : Circuit) := Monotone2 D ∧ ReadsBack 26 D ∧
    RightOnIncidentPairs singerLines3 D ∧ ∀ Q, IsQuadrangle singerLines3 Q → D.eval (neg Q) = false
  have incidence : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p - l ∈ d := by
    change ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))
    decide
  have quadrangle (Q : Finset (Fin 13)) : IsQuadrangle singerLines3 Q ↔
      Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => p - l ∈ d)).card ≤ 2 := by
    have equal (l : Fin 13) : Q ∩ singerLines3 l = Q.filter (fun p => p - l ∈ d) := by
      ext p
      simp [incidence p l]
    unfold IsQuadrangle
    simp_rw [equal]
  have negativeInput (Q : Finset (Fin 13)) : neg Q =
      List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ d)) := by
    have tail : List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)) =
        List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ d)) := by
      apply congrArg List.ofFn
      funext l
      apply decide_eq_decide.mpr
      change (l ∈ (Finset.univ : Finset (Fin 13)).filter
        (fun a => Disjoint (singerLines3 a) Q)) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
      constructor
      · intro h p hp hpl
        exact h ((incidence p l).mpr hpl) hp
      · intro h p hpl hp
        exact h p hp ((incidence p l).mp hpl)
    exact congrArg (fun ys => List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++ ys) tail
  have specification (D : Circuit) : valid D ↔ good D := by
    constructor
    · rintro ⟨m, r, h⟩
      refine ⟨m, r, ?_, ?_⟩
      · intro l p hpl
        exact h true _ ⟨p, l, (incidence p l).mp hpl, by
          unfold incidenceInput
          simp only [Finset.mem_singleton]⟩
      · intro Q hQ
        obtain ⟨hc, hl⟩ := (quadrangle Q).mp hQ
        exact h false _ ⟨Q, hc, hl, negativeInput Q⟩
    · rintro ⟨m, r, accepted, rejected⟩
      refine ⟨m, r, ?_⟩
      intro b xs h
      cases b with
      | false =>
        obtain ⟨Q, hc, hl, rfl⟩ := h
        rw [← negativeInput Q]
        exact rejected Q ((quadrangle Q).mpr ⟨hc, hl⟩)
      | true =>
        obtain ⟨p, l, hpl, rfl⟩ := h
        have hAccept := accepted l p ((incidence p l).mpr hpl)
        unfold incidenceInput at hAccept
        simpa only [Finset.mem_singleton] using hAccept
  by_contra noSmaller
  have leastSize (D : Circuit) (hD : good D) : C.size ≤ D.size := by
    by_contra! smallerD
    exact noSmaller ⟨D, (specification D).mpr hD, smallerD⟩
  let attainable (k : ℕ) := ∃ D, good D ∧ D.size = C.size ∧ andPairs 26 D = k
  have existsCount : ∃ k, attainable k :=
    ⟨andPairs 26 C, C, (specification C).mp hC, rfl, rfl⟩
  obtain ⟨D, hD, hsize, hcount⟩ := Nat.find_spec existsCount
  have leastPairs (E : Circuit) (hE : good E) (same : E.size = D.size) :
      andPairs 26 D ≤ andPairs 26 E := by
    rw [hcount]
    exact Nat.find_min' existsCount ⟨E, hE, same.trans hsize, rfl⟩
  have sizeD : D.size < 64 := hsize ▸ hsmall
  by_cases flatD : andPairs 26 D = 0
  · exact (not_le_of_gt sizeD) (flat D hD flatD)
  let nested (E : Circuit) (i j : ℕ) := (gateAt E i).op = .and ∧
    (gateAt E j).op = .and ∧ InCone 26 E i j
  let clean (E : Circuit) (i : ℕ) := ∀ Q, IsQuadrangle singerLines3 Q →
    (E.wires (neg Q)).getD (26 + i) false = false
  let loses (E : Circuit) (i : ℕ) (p : Fin 13 × Fin 13) :=
    p.1 ∈ singerLines3 p.2 ∧
    ({E with gates := replaceByConst E.gates i false} : Circuit).eval (incidenceInput {p.1} {p.2}) = false
  have noClean (E : Circuit) (hE : good E) (same : E.size = D.size)
      (pairs : andPairs 26 E ≤ andPairs 26 D) :
      ¬ ∃ i j, nested E i j ∧ clean E i := by
    intro allowed
    obtain ⟨F, hF, smallerF | ⟨sameF, fewer⟩⟩ := cleanMove E hE allowed
    · have gt : F.size < C.size := smallerF.trans_eq (same.trans hsize)
      exact (not_le_of_gt gt) (leastSize F hF)
    · exact (not_le_of_gt (fewer.trans_le pairs)) (leastPairs F hF (sameF.trans same))
  have allNeeded (i j : ℕ) (hij : nested D i j) : ∃ p q, loses D i p ∧ loses D i q ∧ p ≠ q := by
    by_contra noTwo
    have one (p q : Fin 13 × Fin 13) (hp : loses D i p) (hq : loses D i q) : p = q := by
      by_contra different
      exact noTwo ⟨p, q, hp, hq, different⟩
    obtain ⟨E, hE, same, pairs, stillNested, cleanNow⟩ := sparse D i j hD hij one
    exact noClean E hE same pairs ⟨i, j, stillNested, cleanNow⟩
  have hasNested : ∃ i j, nested D i j := by
    have somePair : (Finset.range D.gates.length ×ˢ Finset.range D.gates.length).filter
        (fun p => (gateAt D p.1).op = .and ∧ (gateAt D p.2).op = .and ∧ InCone 26 D p.1 p.2) |>.Nonempty := by
      apply Finset.card_pos.mp
      change 0 < andPairs 26 D
      omega
    obtain ⟨⟨i, j⟩, h⟩ := somePair
    exact ⟨i, j, (Finset.mem_filter.mp h).2⟩
  have minimum (E : Circuit) (hE : good E) : D.size ≤ E.size := hsize.symm ▸ leastSize E hE
  exact dense D hD sizeD (fun E hE => ⟨minimum E hE, leastPairs E hE⟩) hasNested allNeeded
