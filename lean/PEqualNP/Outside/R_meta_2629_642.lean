import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Remove the marked inputs, apply the unmarked circuit bound, then restore the marked literals.
theorem PEqualNP.Outside.R_meta_2629_642
    (strip : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (C : Circuit), let readers := fun (D : Circuit) (v : Fin n) => D.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G A →
    (∀ v ∉ A, 2 ≤ (readers C v).length) →
    (∃ v ∉ A, ∃ g ∈ readers C v, g.op = .not) →
    ∃ D : Circuit, D.size + A.card ≤ C.size ∧ IsMinimalCircuit n D ∧
      circuitFun n D = NestedCover.graphFun G ∅ ∧
      (∀ v ∉ A, 2 ≤ (readers D v).length) ∧
      ∃ v ∉ A, ∃ g ∈ readers D v, g.op = .not)
    (pure : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (D : Circuit), let readers := fun (D : Circuit) (v : Fin n) => D.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    IsMinimalCircuit n D → circuitFun n D = NestedCover.graphFun G ∅ →
    (∀ v ∉ A, 2 ≤ (readers D v).length) →
    (∃ v ∉ A, ∃ g ∈ readers D v, g.op = .not) →
    ∃ v ∉ A, ∃ s, s + 4 ≤ D.size ∧
      HasCircuitSize n (fun x => NestedCover.graphFun G ∅ (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  classical
  have restore : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (v : Fin n) (s : ℕ), v ∉ A →
    HasCircuitSize n (fun x => NestedCover.graphFun G ∅ (Function.update x v false)) s →
    HasCircuitSize n (fun x => NestedCover.graphFun G A (Function.update x v false)) (s + A.card) := by
    classical
    intro n G dec A v s hv start
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have wirePrefix (gs : List Gate) (w : List Bool) : ∃ tail : List Bool,
        gs.foldl step w = w ++ tail ∧ tail.length = gs.length := by
      induction gs generalizing w with
      | nil => exact ⟨[], by simp, rfl⟩
      | cons g gs ih =>
        let b := g.op.eval (g.inputs.map fun i => w.getD i false)
        obtain ⟨tail, eq, length⟩ := ih (w ++ [b])
        refine ⟨b :: tail, ?_, by simp [length]⟩
        change gs.foldl step (w ++ [b]) = w ++ b :: tail
        rw [eq]
        simp
    have append (a : Fin n) (f : (Fin n → Bool) → Bool) (k : ℕ) (base : HasCircuitSize n f k) :
        HasCircuitSize n (fun x => f x || x a) (k+1) := by
      obtain ⟨C, fan, size, computes⟩ := base
      let g : Gate := ⟨.or, [C.output, a.val]⟩
      let D : Circuit := ⟨C.gates ++ [g], n+C.size⟩
      refine ⟨D, ?_, ?_, ?_⟩
      · intro h hh
        rcases List.mem_append.mp hh with old | new
        · exact fan h old
        · obtain rfl : h = g := by simpa using new
          simp [g]
      · change (C.gates ++ [g]).length ≤ k + 1
        change C.gates.length ≤ k at size
        simp [size]
      · intro x
        obtain ⟨tail, eq, ht⟩ := wirePrefix C.gates (List.ofFn x)
        have length : (C.wires (List.ofFn x)).length = n+C.size := by
          change (C.gates.foldl step (List.ofFn x)).length = n + C.gates.length
          simp [eq,ht]
        have raw : (C.wires (List.ofFn x)).getD a.val false = x a := by
          change (C.gates.foldl step (List.ofFn x)).getD a.val false = x a
          rw [eq,List.getD_append _ _ _ _ (by simpa using a.isLt)]
          simp
        have concat : D.wires (List.ofFn x) = step (C.wires (List.ofFn x)) g := by
          change (C.gates ++ [g]).foldl step (List.ofFn x) = step (C.gates.foldl step (List.ofFn x)) g
          rw [List.foldl_append]
          rfl
        change (D.wires (List.ofFn x)).getD (n + C.size) false = (f x || x a)
        rw [concat, ← length]
        let W := C.wires (List.ofFn x)
        change (W ++ [[W.getD C.output false, W.getD a.val false].any id]).getD W.length false = (f x || x a)
        have last (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by simp
        rw [last, raw]
        simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact congrArg (fun b => b || x a) (computes x)
    induction A using Finset.induction_on with
    | empty => exact start
    | @insert a T fresh ih =>
      have hT : v ∉ T := fun h => hv (Finset.mem_insert_of_mem h)
      have av : a ≠ v := fun h => hv (h ▸ Finset.mem_insert_self a T)
      have h := append a _ _ (ih hT)
      have eq : (fun x : Fin n → Bool => NestedCover.graphFun G T (Function.update x v false) || x a) =
          (fun x => NestedCover.graphFun G (insert a T) (Function.update x v false)) := by
        funext x
        let y := Function.update x v false
        let marks := fun (M : Finset (Fin n)) => decide (∃ t ∈ M, y t = true)
        let edges := decide (∃ i j, G.Adj i j ∧ y i = true ∧ y j = true)
        change ((marks T || edges) || x a) = (marks (insert a T) || edges)
        apply Bool.eq_iff_iff.mpr
        simp only [marks, y, Bool.or_eq_true, decide_eq_true_eq,
          Finset.exists_mem_insert, Function.update_of_ne av]
        constructor
        · rintro ((hm | he) | ha)
          · exact .inl (.inr hm)
          · exact .inr he
          · exact .inl (.inl ha)
        · rintro ((ha | hm) | he)
          · exact .inr ha
          · exact .inl (.inl hm)
          · exact .inl (.inr he)
      rw [eq] at h
      rw [Finset.card_insert_of_notMem fresh, ← Nat.add_assoc]
      exact h
  intro n G dec A C f readers deg girth ends edge fan eval least counts witness
  have minimal : IsMinimalCircuit n C := by
    refine ⟨fan, ?_⟩
    intro D hD same
    exact least D.size ⟨D, hD, le_rfl, fun x => congrFun (same.trans eval) x⟩
  obtain ⟨u, hu, _, reader⟩ := witness
  obtain ⟨D, budget, minimum, computes, twice, neg⟩ :=
    strip n G A C ends edge minimal eval (fun v hv => (counts v hv).1) ⟨u, hu, reader⟩
  obtain ⟨v, hv, s, save, restricted⟩ :=
    pure n G A D deg girth ends edge minimum computes twice neg
  exact ⟨v, hv, s + A.card, by omega, restore n G A v s hv restricted⟩
