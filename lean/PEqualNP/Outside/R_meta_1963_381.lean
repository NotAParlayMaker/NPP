import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.GenericRejection

-- At the first nested AND, a predecessor is either the inner AND itself or an OR above it.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_1963_381
    (oneStep : ∀ (n : ℕ) (C : Circuit) (i j : ℕ), j < C.size → InCone n C i j →
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ InCone n C i (w - n)))
    (repair : ∀ (C : Circuit),
      let checks (D : Circuit) := RightOnIncidentPairs singerLines3 D ∧
        ∀ Q ∈ quadrangles singerLines3, D.eval (incidenceInput Q (missLines singerLines3 Q)) = false
      IsAO2 26 C → (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
      checks C → C.size < 64 → 2 ≤ andPairs 26 C →
      ∀ (i j w : ℕ), j < C.size → (gateAt C i).op = .and → (gateAt C j).op = .and →
      InCone 26 C i j →
      (∀ k < j, (gateAt C k).op = .and →
        ∀ b, (gateAt C b).op = .and → ¬ InCone 26 C b k) →
      w ∈ (gateAt C j).inputs → 26 ≤ w → w < 26 + j →
      (i = w - 26 ∨ (gateAt C (w - 26)).op = .or ∧ InCone 26 C i (w - 26)) →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ checks D ∧ D.size < C.size) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size := by

  classical
  intro Delta Correct Nested C mono back eval below nested strict pairs
  let N (Q : Finset (Fin 13)) := incidenceInput Q (missLines singerLines3 Q)
  let N' (Q : Finset (Fin 13)) := List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
    List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ Delta))
  have incident : ∀ p l : Fin 13, p - l ∈ Delta ↔ p ∈ singerLines3 l := by decide
  have shape (Q : Finset (Fin 13)) :
      Q ∈ quadrangles singerLines3 ↔
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ Delta)).card ≤ 2 := by
    have same (k : Fin 13) : Q ∩ singerLines3 k = Q.filter (fun u => u - k ∈ Delta) := by
      ext u
      simp [incident u k]
    change Q ∈ ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter
      (fun A => ∀ l : Fin 13, (A ∩ singerLines3 l).card ≤ 2) ↔ _
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and, same]
  have sameInputs (Q : Finset (Fin 13)) : N Q = N' Q := by
    have tailEq : List.ofFn (fun v : Fin 13 => decide (v ∈ missLines singerLines3 Q)) =
        List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ Delta)) := by
      apply congrArg List.ofFn
      funext v
      apply decide_eq_decide.mpr
      change (v ∈ (Finset.univ : Finset (Fin 13)).filter
        (fun l => Disjoint (singerLines3 l) Q)) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left, ← incident]
      constructor
      · intro h r hr hi
        exact h hi hr
      · intro h r hi hr
        exact h r hr hi
    exact congrArg (fun tail : List Bool => List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++ tail) tailEq
  have singletons (p l : Fin 13) : incidenceInput {p} {l} =
      List.ofFn (fun u : Fin 13 => decide (u = p)) ++
        List.ofFn (fun v : Fin 13 => decide (v = l)) := by
    change List.ofFn (fun u : Fin 13 => decide (u ∈ ({p} : Finset (Fin 13)))) ++
      List.ofFn (fun v : Fin 13 => decide (v ∈ ({l} : Finset (Fin 13)))) = _
    simp only [Finset.mem_singleton]
  have correct (D : Circuit) : Correct D ↔
      RightOnIncidentPairs singerLines3 D ∧ ∀ Q ∈ quadrangles singerLines3, D.eval (N Q) = false := by
    constructor
    · intro h
      constructor
      · intro l p hp
        rw [singletons]
        exact h.1 p l ((incident p l).mpr hp)
      · intro Q hQ
        rw [sameInputs]
        exact h.2 Q ((shape Q).mp hQ).1 ((shape Q).mp hQ).2
    · intro h
      constructor
      · intro p l hp
        rw [← singletons]
        exact h.1 l p ((incident p l).mp hp)
      · intro Q hQ hNoncollinear
        change D.eval (N' Q) = false
        rw [← sameInputs]
        exact h.2 Q ((shape Q).mpr ⟨hQ,hNoncollinear⟩)
  have andInRange (j : ℕ) (hj : (gateAt C j).op = .and) : j < C.size := by
    by_contra! beyond
    have eq : gateAt C j = ⟨.or,[]⟩ := List.getD_eq_default _ _ beyond
    rw [eq] at hj
    cases hj
  let marked (j : ℕ) := (gateAt C j).op = .and ∧ ∃ i, (gateAt C i).op = .and ∧ InCone 26 C i j
  obtain ⟨a,b,ha,hb,cone⟩ := nested
  have existsMarked : ∃ j, marked j := ⟨b,hb,a,ha,cone⟩
  let j := Nat.find existsMarked
  obtain ⟨hj,i,hi,hcone⟩ := Nat.find_spec existsMarked
  have minJ (k : ℕ) (hk : k < j) (ho : (gateAt C k).op = .and)
      (r : ℕ) (hr : (gateAt C r).op = .and) : ¬ InCone 26 C r k :=
    fun bad => Nat.find_min existsMarked hk ⟨ho,r,hr,bad⟩
  obtain ⟨w,mem,lower,upper,source⟩ := oneStep 26 C i j (andInRange j hj) hcone
  have via : i = w - 26 ∨ (gateAt C (w - 26)).op = .or ∧ InCone 26 C i (w - 26) := by
    rcases source with h | h
    · exact Or.inl h
    · have lt : w - 26 < j := by omega
      have valid : w - 26 < C.gates.length := lt.trans (andInRange j hj)
      have get : gateAt C (w - 26) = C.gates[w - 26] := List.getD_eq_getElem _ _ valid
      have gin : gateAt C (w - 26) ∈ C.gates := by
        rw [get]
        exact List.getElem_mem _
      have either := (Set.mem_insert_iff.mp (mono _ gin).1).imp id Set.mem_singleton_iff.mp
      exact Or.inr ⟨either.resolve_left (fun ho => minJ _ lt ho i hi h),h⟩
  have model : IsAO2 26 C := by
    refine ⟨?_,back,fun g hg => (strict g hg).1⟩
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (mono g hg).1
  obtain ⟨D,hm,hb,hcheck,shrinks⟩ :=
    repair C model (fun g hg => (strict g hg).2) ((correct C).mp eval) below pairs
      i j w (andInRange j hj) hi hj hcone minJ mem lower upper via
  exact ⟨D,hm,hb,(correct D).mpr hcheck,shrinks⟩
