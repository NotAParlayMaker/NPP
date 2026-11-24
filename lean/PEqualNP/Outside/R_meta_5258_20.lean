import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

-- With at most 19 OR gates, each rejected quadrangle leaves at most one OR gate true.
-- The first child turns this constraint into a lower bound on the number of AND gates.
theorem PEqualNP.Outside.R_meta_5258_20
    (floor :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
          List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let G := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      ∀ (C : Circuit) (a b : Nat), Monotone2 C → ReadsBack 26 C →
        let V := fun w x => (C.wires x).getD w false
        (∀ p l : Fin 13, p-l ∈ D → (V a (P p l) && V b (P p l)) = true) →
        (∀ Q, G Q → (V a (N Q) && V b (N Q)) = false) →
        ((Finset.range C.size).filter (fun j => (gateAt C j).op.eval [false,true])).card ≤ 19 → 65 ≤ C.size)
    (remaining :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
          List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let G := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let ok := fun (C : Circuit) (a b : ℕ) =>
        let V := fun (w : ℕ) (x : List Bool) => (C.wires x).getD w false
        Monotone2 C ∧ ReadsBack 26 C ∧
        (∀ p l : Fin 13, p - l ∈ D → (V a (P p l) && V b (P p l)) = true) ∧
        (∀ Q : Finset (Fin 13), G Q → (V a (N Q) && V b (N Q)) = false) ∧
        (∃ Q : Finset (Fin 13), G Q ∧ V a (N Q) < V b (N Q)) ∧
        (∃ Q : Finset (Fin 13), G Q ∧ V b (N Q) < V a (N Q))
      ∀ (C : Circuit) (a b : Nat), ok C a b → C.size < 63 →
        20 ≤ ((Finset.range C.size).filter (fun j => (gateAt C j).op.eval [false,true])).card →
        0 < PEqualNP.TopForm.andPairs 26 C →
        ∃ (E : Circuit) (a' b' : Nat), ok E a' b' ∧ E.size < C.size) :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let P := fun (p l : Fin 13) =>
        List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l))
      let N := fun (Q : Finset (Fin 13)) =>
        List.ofFn (fun u : Fin 13 => decide (u ∈ Q)) ++
          List.ofFn (fun v : Fin 13 => decide (∀ r ∈ Q, r - v ∉ D))
      let G := fun (Q : Finset (Fin 13)) =>
        Q.card = 4 ∧ ∀ k : Fin 13, (Q.filter (fun u => u - k ∈ D)).card ≤ 2
      let ok := fun (C : Circuit) (a b : ℕ) =>
        let V := fun (w : ℕ) (x : List Bool) => (C.wires x).getD w false
        Monotone2 C ∧ ReadsBack 26 C ∧
        (∀ p l : Fin 13, p - l ∈ D → (V a (P p l) && V b (P p l)) = true) ∧
        (∀ Q : Finset (Fin 13), G Q → (V a (N Q) && V b (N Q)) = false) ∧
        (∃ Q : Finset (Fin 13), G Q ∧ V a (N Q) < V b (N Q)) ∧
        (∃ Q : Finset (Fin 13), G Q ∧ V b (N Q) < V a (N Q))
      ∀ (C : Circuit) (a b : Nat), ok C a b → C.size < 63 →
        (∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j) →
        ∃ (E : Circuit) (a' b' : Nat), ok E a' b' ∧ E.size < C.size := by
  let _ := gateOpDecEq
  dsimp only
  intro C a b h small nested
  by_cases enough : 20 ≤ ((Finset.range C.size).filter (fun j => (gateAt C j).op.eval [false,true])).card
  · obtain ⟨i,j,ai,aj,ij⟩ := nested
    have range (k : Nat) (ak : (gateAt C k).op = GateOp.and) : k < C.gates.length := by
      by_contra! bad
      change (C.gates.getD k ⟨.or, []⟩).op = .and at ak
      rw [List.getD_eq_default _ _ bad] at ak
      exact GateOp.noConfusion ak
    have pairs : 0 < PEqualNP.TopForm.andPairs 26 C := by
      apply Finset.card_pos.mpr
      exact ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (range _ ai), Finset.mem_range.mpr (range _ aj)⟩, ai, aj, ij⟩⟩
    exact remaining C a b h small enough pairs
  · have large := floor C a b h.1 h.2.1 h.2.2.1 h.2.2.2.1 (Nat.le_of_lt_succ (Nat.lt_of_not_ge enough))
    exact False.elim ((Nat.not_le_of_lt small) ((by decide : 63 ≤ 65).trans large))
