import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover PEqualNP.TopForm

-- A replacement can use any earlier wire. The required direction of implication depends
-- on whether the test row is an incidence or a quadrangle.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_1963_528
    (shrink :
      let pos (p l : Fin 13) :=
        List.ofFn (fun i : Fin 13 => decide (i = p)) ++ List.ofFn (fun i : Fin 13 => decide (i = l))
      let neg (Q : Finset (Fin 13)) :=
        List.ofFn (fun i : Fin 13 => decide (i ∈ Q)) ++
          List.ofFn (fun i : Fin 13 => decide (i ∈ missLines singerLines3 Q))
      let correct (C : Circuit) :=
        (∀ p l : Fin 13, p ∈ singerLines3 l → C.eval (pos p l) = true) ∧
        (∀ Q ∈ quadrangles singerLines3, C.eval (neg Q) = false)
      let dominates (C : Circuit) (j p : ℕ) :=
        (∀ a b : Fin 13, a ∈ singerLines3 b →
          (C.wires (pos a b)).getD (26+j) false = true → (C.wires (pos a b)).getD p false = true) ∧
        (∀ Q ∈ quadrangles singerLines3,
          (C.wires (neg Q)).getD p false = true → (C.wires (neg Q)).getD (26+j) false = true)
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → correct C →
        (∃ j<C.size, ∃ p<26+j, dominates C j p) →
        ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ correct D ∧ D.size < C.size)
    (quadranglePairs :
      let neg (Q : Finset (Fin 13)) :=
        List.ofFn (fun i : Fin 13 => decide (i ∈ Q)) ++
          List.ofFn (fun i : Fin 13 => decide (i ∈ missLines singerLines3 Q))
      let rawIncident (a b : Fin 26) :=
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧
          ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
           (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))
      ∀ C : Circuit, Monotone2 C → (∀ Q ∈ quadrangles singerLines3, C.eval (neg Q) = false) →
        (∀ a b : Fin 26, ¬ rawIncident a b →
          C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput a b)) = false))
    (remaining :
      let pos (p l : Fin 13) :=
        List.ofFn (fun i : Fin 13 => decide (i = p)) ++ List.ofFn (fun i : Fin 13 => decide (i = l))
      let neg (Q : Finset (Fin 13)) :=
        List.ofFn (fun i : Fin 13 => decide (i ∈ Q)) ++
          List.ofFn (fun i : Fin 13 => decide (i ∈ missLines singerLines3 Q))
      let correct (C : Circuit) :=
        (∀ p l : Fin 13, p ∈ singerLines3 l → C.eval (pos p l) = true) ∧
        (∀ Q ∈ quadrangles singerLines3, C.eval (neg Q) = false)
      let dominates (C : Circuit) (j p : ℕ) :=
        (∀ a b : Fin 13, a ∈ singerLines3 b →
          (C.wires (pos a b)).getD (26+j) false = true → (C.wires (pos a b)).getD p false = true) ∧
        (∀ Q ∈ quadrangles singerLines3,
          (C.wires (neg Q)).getD p false = true → (C.wires (neg Q)).getD (26+j) false = true)
      let rawIncident (a b : Fin 26) :=
        ∃ p l : Fin 13, p ∈ singerLines3 l ∧
          ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
           (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))
      ∀ C : Circuit, IsAO2 26 C → correct C →
        2 ≤ andPairs 26 C →
        (∀ a b : Fin 26, ¬ rawIncident a b →
          C.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput a b)) = false) →
        (∀ j<C.size, ∀ p<26+j, ¬ dominates C j p) → 64 ≤ C.size) :
have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size := by
  dsimp only
  intro C mono back agrees size nested strict pairs
  let pos (p l : Fin 13) :=
    List.ofFn (fun i : Fin 13 => decide (i = p)) ++ List.ofFn (fun i : Fin 13 => decide (i = l))
  let neg (Q : Finset (Fin 13)) :=
    List.ofFn (fun i : Fin 13 => decide (i ∈ Q)) ++
      List.ofFn (fun i : Fin 13 => decide (i ∈ missLines singerLines3 Q))
  let correct (C : Circuit) :=
    (∀ p l : Fin 13, p ∈ singerLines3 l → C.eval (pos p l) = true) ∧
    (∀ Q ∈ quadrangles singerLines3, C.eval (neg Q) = false)
  let dominates (C : Circuit) (j p : ℕ) :=
    (∀ a b : Fin 13, a ∈ singerLines3 b →
      (C.wires (pos a b)).getD (26+j) false = true → (C.wires (pos a b)).getD p false = true) ∧
    (∀ Q ∈ quadrangles singerLines3,
      (C.wires (neg Q)).getD p false = true → (C.wires (neg Q)).getD (26+j) false = true)
  let rawIncident (a b : Fin 26) :=
    ∃ p l : Fin 13, p ∈ singerLines3 l ∧
      ((a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l) ∨
       (b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l))
  let offsets : Finset (Fin 13) := {0,1,3,9}
  let card4 (Q : Finset (Fin 13)) :=
    Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u-k ∈ offsets)).card ≤ 2
  let listed (Q : Finset (Fin 13)) :=
    List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++
      List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ offsets))
  let original (C : Circuit) :=
    (∀ a b : Fin 13, a-b ∈ offsets → C.eval (pos a b) = true) ∧
    (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u => u-k ∈ offsets)).card ≤ 2) → C.eval (listed Q) = false)
  have incident : ∀ p l : Fin 13, p-l ∈ offsets ↔ p ∈ singerLines3 l := by decide +kernel
  have shape (Q : Finset (Fin 13)) : Q ∈ quadrangles singerLines3 ↔ card4 Q := by
    have meet (l : Fin 13) : Q ∩ singerLines3 l = Q.filter (fun p => p-l ∈ offsets) := by
      ext p
      simp [incident]
    change Q ∈ ((Finset.univ : Finset (Fin 13)).powersetCard 4).filter
      (fun X => ∀ l : Fin 13, (X ∩ singerLines3 l).card ≤ 2) ↔ _
    simp only [card4,Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_univ,true_and,meet]
  have inputs (Q : Finset (Fin 13)) : neg Q = listed Q := by
    have miss (l : Fin 13) : l ∈ missLines singerLines3 Q ↔ ∀ p ∈ Q, p-l ∉ offsets := by
      change (l ∈ (Finset.univ : Finset (Fin 13)).filter
        (fun l => Disjoint (singerLines3 l) Q)) ↔ _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left,← incident]
      exact ⟨fun h p mem on => h on mem,fun h p on mem => h p mem on⟩
    have tail : List.ofFn (fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)) =
        List.ofFn (fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ offsets)) := by
      apply congrArg List.ofFn
      funext l
      exact decide_eq_decide.mpr (miss l)
    exact congrArg (fun ys : List Bool => List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++ ys) tail
  have compare (D : Circuit) : original D ↔ correct D := by
    constructor
    · intro h
      refine ⟨fun p l inc => h.1 p l ((incident p l).mpr inc),?_⟩
      intro Q quad
      rw [inputs Q]
      have data := (shape Q).mp quad
      exact h.2 Q data.1 data.2
    · intro h
      refine ⟨fun p l inc => h.1 p l ((incident p l).mp inc),?_⟩
      intro Q card cap
      rw [← inputs Q]
      exact h.2 Q ((shape Q).mpr ⟨card,cap⟩)
  have tests : correct C := (compare C).mp agrees
  by_cases can : ∃ j<C.size, ∃ p<26+j, dominates C j p
  · obtain ⟨D,hM,hB,hD,hS⟩ := shrink C mono back tests can
    exact ⟨D,hM,hB,(compare D).mpr hD,hS⟩
  · have legal : IsAO2 26 C := by
      exact ⟨fun g mem => by simpa using (mono g mem).1,back,fun g mem => (strict g mem).1⟩
    have no : ∀ j<C.size, ∀ p<26+j, ¬ dominates C j p := by
      intro j hj p hp dominates
      exact can ⟨j,hj,p,hp,dominates⟩
    exact (Nat.not_lt_of_ge (remaining C legal tests pairs (quadranglePairs C mono tests.2) no) size).elim
