import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def both (x y : Bool) : Bool := [x,y].all id
private def either (x y : Bool) : Bool := [x,y].any id

private theorem graph1 : PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1 := by
  let C : Circuit := ⟨[⟨.and, [0, 1]⟩], 2⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w2 := [x 0, x 1]
    have start : List.ofFn x = w2 := rfl
    let v2 := both (x 0) (x 1)
    let w3 := [x 0, x 1, v2]
    have g2 : gateStep w2 ⟨.and, [0, 1]⟩ = w3 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 2 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g2]
    change v2 = ((x 0 && x 1))
    simp [v2, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph2 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 3]⟩], 4⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w3 := [x 0, x 1, x 2]
    have start : List.ofFn x = w3 := rfl
    let v3 := either (x 1) (x 2)
    let w4 := [x 0, x 1, x 2, v3]
    have g3 : gateStep w3 ⟨.or, [1, 2]⟩ = w4 := rfl
    let v4 := both (x 0) v3
    let w5 := [x 0, x 1, x 2, v3, v4]
    have g4 : gateStep w4 ⟨.and, [0, 3]⟩ = w5 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 4 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g3, g4]
    change v4 = ((x 0 && x 1) || (x 0 && x 2))
    simp [v4, v3, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph3 : PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩], 6⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w3 := [x 0, x 1, x 2]
    have start : List.ofFn x = w3 := rfl
    let v3 := either (x 1) (x 2)
    let w4 := [x 0, x 1, x 2, v3]
    have g3 : gateStep w3 ⟨.or, [1, 2]⟩ = w4 := rfl
    let v4 := both (x 0) v3
    let w5 := [x 0, x 1, x 2, v3, v4]
    have g4 : gateStep w4 ⟨.and, [0, 3]⟩ = w5 := rfl
    let v5 := both (x 1) (x 2)
    let w6 := [x 0, x 1, x 2, v3, v4, v5]
    have g5 : gateStep w5 ⟨.and, [1, 2]⟩ = w6 := rfl
    let v6 := either v4 v5
    let w7 := [x 0, x 1, x 2, v3, v4, v5, v6]
    have g6 : gateStep w6 ⟨.or, [4, 5]⟩ = w7 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 6 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g3, g4, g5, g6]
    change v6 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2))
    simp [v6, v5, v4, v3, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph4 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3 := by
  let C : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩], 6⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w4 := [x 0, x 1, x 2, x 3]
    have start : List.ofFn x = w4 := rfl
    let v4 := both (x 0) (x 1)
    let w5 := [x 0, x 1, x 2, x 3, v4]
    have g4 : gateStep w4 ⟨.and, [0, 1]⟩ = w5 := rfl
    let v5 := both (x 2) (x 3)
    let w6 := [x 0, x 1, x 2, x 3, v4, v5]
    have g5 : gateStep w5 ⟨.and, [2, 3]⟩ = w6 := rfl
    let v6 := either v4 v5
    let w7 := [x 0, x 1, x 2, x 3, v4, v5, v6]
    have g6 : gateStep w6 ⟨.or, [4, 5]⟩ = w7 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 6 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g4, g5, g6]
    change v6 = ((x 0 && x 1) || (x 2 && x 3))
    simp [v6, v5, v4, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph5 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩], 6⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w4 := [x 0, x 1, x 2, x 3]
    have start : List.ofFn x = w4 := rfl
    let v4 := either (x 1) (x 2)
    let w5 := [x 0, x 1, x 2, x 3, v4]
    have g4 : gateStep w4 ⟨.or, [1, 2]⟩ = w5 := rfl
    let v5 := either v4 (x 3)
    let w6 := [x 0, x 1, x 2, x 3, v4, v5]
    have g5 : gateStep w5 ⟨.or, [4, 3]⟩ = w6 := rfl
    let v6 := both (x 0) v5
    let w7 := [x 0, x 1, x 2, x 3, v4, v5, v6]
    have g6 : gateStep w6 ⟨.and, [0, 5]⟩ = w7 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 6 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g4, g5, g6]
    change v6 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3))
    simp [v6, v5, v4, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph6 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w4 := [x 0, x 1, x 2, x 3]
    have start : List.ofFn x = w4 := rfl
    let v4 := either (x 1) (x 2)
    let w5 := [x 0, x 1, x 2, x 3, v4]
    have g4 : gateStep w4 ⟨.or, [1, 2]⟩ = w5 := rfl
    let v5 := both (x 0) v4
    let w6 := [x 0, x 1, x 2, x 3, v4, v5]
    have g5 : gateStep w5 ⟨.and, [0, 4]⟩ = w6 := rfl
    let v6 := both (x 1) (x 3)
    let w7 := [x 0, x 1, x 2, x 3, v4, v5, v6]
    have g6 : gateStep w6 ⟨.and, [1, 3]⟩ = w7 := rfl
    let v7 := either v5 v6
    let w8 := [x 0, x 1, x 2, x 3, v4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [5, 6]⟩ = w8 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 7 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g4, g5, g6, g7]
    change v7 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3))
    simp [v7, v6, v5, v4, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph7 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩], 8⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w4 := [x 0, x 1, x 2, x 3]
    have start : List.ofFn x = w4 := rfl
    let v4 := either (x 1) (x 2)
    let w5 := [x 0, x 1, x 2, x 3, v4]
    have g4 : gateStep w4 ⟨.or, [1, 2]⟩ = w5 := rfl
    let v5 := either v4 (x 3)
    let w6 := [x 0, x 1, x 2, x 3, v4, v5]
    have g5 : gateStep w5 ⟨.or, [4, 3]⟩ = w6 := rfl
    let v6 := both (x 0) v5
    let w7 := [x 0, x 1, x 2, x 3, v4, v5, v6]
    have g6 : gateStep w6 ⟨.and, [0, 5]⟩ = w7 := rfl
    let v7 := both (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, v4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [1, 2]⟩ = w8 := rfl
    let v8 := either v6 v7
    let w9 := [x 0, x 1, x 2, x 3, v4, v5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [6, 7]⟩ = w9 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 8 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g4, g5, g6, g7, g8]
    change v8 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2))
    simp [v8, v7, v6, v5, v4, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph8 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩], 8⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w5 := [x 0, x 1, x 2, x 3, x 4]
    have start : List.ofFn x = w5 := rfl
    let v5 := either (x 1) (x 2)
    let w6 := [x 0, x 1, x 2, x 3, x 4, v5]
    have g5 : gateStep w5 ⟨.or, [1, 2]⟩ = w6 := rfl
    let v6 := both (x 0) v5
    let w7 := [x 0, x 1, x 2, x 3, x 4, v5, v6]
    have g6 : gateStep w6 ⟨.and, [0, 5]⟩ = w7 := rfl
    let v7 := both (x 3) (x 4)
    let w8 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [3, 4]⟩ = w8 := rfl
    let v8 := either v6 v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [6, 7]⟩ = w9 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 8 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g5, g6, g7, g8]
    change v8 = ((x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4))
    simp [v8, v7, v6, v5, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph9 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩], 8⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w5 := [x 0, x 1, x 2, x 3, x 4]
    have start : List.ofFn x = w5 := rfl
    let v5 := either (x 1) (x 2)
    let w6 := [x 0, x 1, x 2, x 3, x 4, v5]
    have g5 : gateStep w5 ⟨.or, [1, 2]⟩ = w6 := rfl
    let v6 := either v5 (x 3)
    let w7 := [x 0, x 1, x 2, x 3, x 4, v5, v6]
    have g6 : gateStep w6 ⟨.or, [5, 3]⟩ = w7 := rfl
    let v7 := either v6 (x 4)
    let w8 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 4]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 8 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g5, g6, g7, g8]
    change v8 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4))
    simp [v8, v7, v6, v5, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph10 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [7, 8]⟩], 9⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w5 := [x 0, x 1, x 2, x 3, x 4]
    have start : List.ofFn x = w5 := rfl
    let v5 := either (x 1) (x 2)
    let w6 := [x 0, x 1, x 2, x 3, x 4, v5]
    have g5 : gateStep w5 ⟨.or, [1, 2]⟩ = w6 := rfl
    let v6 := either v5 (x 3)
    let w7 := [x 0, x 1, x 2, x 3, x 4, v5, v6]
    have g6 : gateStep w6 ⟨.or, [5, 3]⟩ = w7 := rfl
    let v7 := both (x 0) v6
    let w8 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [0, 6]⟩ = w8 := rfl
    let v8 := both (x 1) (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [1, 4]⟩ = w9 := rfl
    let v9 := either v7 v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [7, 8]⟩ = w10 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 9 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g5, g6, g7, g8, g9]
    change v9 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4))
    simp [v9, v8, v7, v6, v5, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph11 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w5 := [x 0, x 1, x 2, x 3, x 4]
    have start : List.ofFn x = w5 := rfl
    let v5 := either (x 1) (x 2)
    let w6 := [x 0, x 1, x 2, x 3, x 4, v5]
    have g5 : gateStep w5 ⟨.or, [1, 2]⟩ = w6 := rfl
    let v6 := both (x 0) v5
    let w7 := [x 0, x 1, x 2, x 3, x 4, v5, v6]
    have g6 : gateStep w6 ⟨.and, [0, 5]⟩ = w7 := rfl
    let v7 := both (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [1, 2]⟩ = w8 := rfl
    let v8 := both (x 3) (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [3, 4]⟩ = w9 := rfl
    let v9 := either v6 v7
    let w10 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [6, 7]⟩ = w10 := rfl
    let v10 := either v9 v8
    let w11 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [9, 8]⟩ = w11 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 10 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g5, g6, g7, g8, g9, g10]
    change v10 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4))
    simp [v10, v9, v8, v7, v6, v5, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph12 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5 := by
  let C : Circuit := ⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩], 9⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w5 := [x 0, x 1, x 2, x 3, x 4]
    have start : List.ofFn x = w5 := rfl
    let v5 := either (x 0) (x 3)
    let w6 := [x 0, x 1, x 2, x 3, x 4, v5]
    have g5 : gateStep w5 ⟨.or, [0, 3]⟩ = w6 := rfl
    let v6 := both (x 1) v5
    let w7 := [x 0, x 1, x 2, x 3, x 4, v5, v6]
    have g6 : gateStep w6 ⟨.and, [1, 5]⟩ = w7 := rfl
    let v7 := either (x 0) (x 4)
    let w8 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [0, 4]⟩ = w8 := rfl
    let v8 := both (x 2) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [2, 7]⟩ = w9 := rfl
    let v9 := either v6 v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [6, 8]⟩ = w10 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 9 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g5, g6, g7, g8, g9]
    change v9 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4))
    simp [v9, v8, v7, v6, v5, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph13 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [8, 9]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w5 := [x 0, x 1, x 2, x 3, x 4]
    have start : List.ofFn x = w5 := rfl
    let v5 := either (x 1) (x 2)
    let w6 := [x 0, x 1, x 2, x 3, x 4, v5]
    have g5 : gateStep w5 ⟨.or, [1, 2]⟩ = w6 := rfl
    let v6 := either v5 (x 3)
    let w7 := [x 0, x 1, x 2, x 3, x 4, v5, v6]
    have g6 : gateStep w6 ⟨.or, [5, 3]⟩ = w7 := rfl
    let v7 := either v6 (x 4)
    let w8 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 4]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 1) (x 2)
    let w10 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 2]⟩ = w10 := rfl
    let v10 := either v8 v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [8, 9]⟩ = w11 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 10 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g5, g6, g7, g8, g9, g10]
    change v10 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2))
    simp [v10, v9, v8, v7, v6, v5, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph14 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w5 := [x 0, x 1, x 2, x 3, x 4]
    have start : List.ofFn x = w5 := rfl
    let v5 := either (x 1) (x 2)
    let w6 := [x 0, x 1, x 2, x 3, x 4, v5]
    have g5 : gateStep w5 ⟨.or, [1, 2]⟩ = w6 := rfl
    let v6 := either v5 (x 3)
    let w7 := [x 0, x 1, x 2, x 3, x 4, v5, v6]
    have g6 : gateStep w6 ⟨.or, [5, 3]⟩ = w7 := rfl
    let v7 := both (x 0) v6
    let w8 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [0, 6]⟩ = w8 := rfl
    let v8 := either (x 2) (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [2, 4]⟩ = w9 := rfl
    let v9 := both (x 1) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 8]⟩ = w10 := rfl
    let v10 := either v7 v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [7, 9]⟩ = w11 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 10 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g5, g6, g7, g8, g9, g10]
    change v10 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4))
    simp [v10, v9, v8, v7, v6, v5, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph15 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [10, 9]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w5 := [x 0, x 1, x 2, x 3, x 4]
    have start : List.ofFn x = w5 := rfl
    let v5 := either (x 1) (x 2)
    let w6 := [x 0, x 1, x 2, x 3, x 4, v5]
    have g5 : gateStep w5 ⟨.or, [1, 2]⟩ = w6 := rfl
    let v6 := either v5 (x 3)
    let w7 := [x 0, x 1, x 2, x 3, x 4, v5, v6]
    have g6 : gateStep w6 ⟨.or, [5, 3]⟩ = w7 := rfl
    let v7 := both (x 0) v6
    let w8 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [0, 6]⟩ = w8 := rfl
    let v8 := both (x 1) (x 2)
    let w9 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [1, 2]⟩ = w9 := rfl
    let v9 := both (x 3) (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [3, 4]⟩ = w10 := rfl
    let v10 := either v7 v8
    let w11 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [7, 8]⟩ = w11 := rfl
    let v11 := either v10 v9
    let w12 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [10, 9]⟩ = w12 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 11 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g5, g6, g7, g8, g9, g10, g11]
    change v11 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4))
    simp [v11, v10, v9, v8, v7, v6, v5, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph16 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [10, 9]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w5 := [x 0, x 1, x 2, x 3, x 4]
    have start : List.ofFn x = w5 := rfl
    let v5 := either (x 1) (x 2)
    let w6 := [x 0, x 1, x 2, x 3, x 4, v5]
    have g5 : gateStep w5 ⟨.or, [1, 2]⟩ = w6 := rfl
    let v6 := both (x 0) v5
    let w7 := [x 0, x 1, x 2, x 3, x 4, v5, v6]
    have g6 : gateStep w6 ⟨.and, [0, 5]⟩ = w7 := rfl
    let v7 := both (x 1) (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [1, 3]⟩ = w8 := rfl
    let v8 := either (x 2) (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [2, 3]⟩ = w9 := rfl
    let v9 := both (x 4) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [4, 8]⟩ = w10 := rfl
    let v10 := either v6 v7
    let w11 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [6, 7]⟩ = w11 := rfl
    let v11 := either v10 v9
    let w12 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [10, 9]⟩ = w12 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 11 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g5, g6, g7, g8, g9, g10, g11]
    change v11 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4))
    simp [v11, v10, v9, v8, v7, v6, v5, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph17 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w5 := [x 0, x 1, x 2, x 3, x 4]
    have start : List.ofFn x = w5 := rfl
    let v5 := either (x 1) (x 2)
    let w6 := [x 0, x 1, x 2, x 3, x 4, v5]
    have g5 : gateStep w5 ⟨.or, [1, 2]⟩ = w6 := rfl
    let v6 := either v5 (x 3)
    let w7 := [x 0, x 1, x 2, x 3, x 4, v5, v6]
    have g6 : gateStep w6 ⟨.or, [5, 3]⟩ = w7 := rfl
    let v7 := either v6 (x 4)
    let w8 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 4]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 1) (x 2)
    let w10 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 2]⟩ = w10 := rfl
    let v10 := both (x 3) (x 4)
    let w11 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [3, 4]⟩ = w11 := rfl
    let v11 := either v8 v9
    let w12 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [8, 9]⟩ = w12 := rfl
    let v12 := either v11 v10
    let w13 := [x 0, x 1, x 2, x 3, x 4, v5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [11, 10]⟩ = w13 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 12 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g5, g6, g7, g8, g9, g10, g11, g12]
    change v12 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4))
    simp [v12, v11, v10, v9, v8, v7, v6, v5, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph18 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5 := by
  let C : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := both (x 0) (x 1)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.and, [0, 1]⟩ = w7 := rfl
    let v7 := both (x 2) (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [2, 3]⟩ = w8 := rfl
    let v8 := both (x 4) (x 5)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [4, 5]⟩ = w9 := rfl
    let v9 := either v6 v7
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [6, 7]⟩ = w10 := rfl
    let v10 := either v9 v8
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [9, 8]⟩ = w11 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 10 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10]
    change v10 = ((x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5))
    simp [v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph19 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 4) (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [4, 5]⟩ = w10 := rfl
    let v10 := either v8 v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [8, 9]⟩ = w11 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 10 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10]
    change v10 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5))
    simp [v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph20 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 3]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [10, 9]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := both (x 0) v6
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [0, 6]⟩ = w8 := rfl
    let v8 := both (x 1) (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [1, 3]⟩ = w9 := rfl
    let v9 := both (x 4) (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [4, 5]⟩ = w10 := rfl
    let v10 := either v7 v8
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [7, 8]⟩ = w11 := rfl
    let v11 := either v10 v9
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [10, 9]⟩ = w12 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 11 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11]
    change v11 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5))
    simp [v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph21 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := both (x 0) v6
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [0, 6]⟩ = w8 := rfl
    let v8 := either (x 4) (x 5)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [4, 5]⟩ = w9 := rfl
    let v9 := both (x 3) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [3, 8]⟩ = w10 := rfl
    let v10 := either v7 v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [7, 9]⟩ = w11 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 10 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10]
    change v10 = ((x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5))
    simp [v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph22 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩], 10⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := either v7 (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 4]⟩ = w9 := rfl
    let v9 := either v8 (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 5]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 10 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10]
    change v10 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5))
    simp [v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph23 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [9, 10]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := either v7 (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 4]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := both (x 1) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [1, 5]⟩ = w11 := rfl
    let v11 := either v9 v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [9, 10]⟩ = w12 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 11 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11]
    change v11 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5))
    simp [v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph24 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 1) (x 2)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 2]⟩ = w10 := rfl
    let v10 := both (x 4) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [4, 5]⟩ = w11 := rfl
    let v11 := either v8 v9
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [8, 9]⟩ = w12 := rfl
    let v12 := either v11 v10
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [11, 10]⟩ = w13 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 12 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12]
    change v12 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5))
    simp [v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph25 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := either (x 4) (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [4, 5]⟩ = w10 := rfl
    let v10 := both (x 1) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [1, 9]⟩ = w11 := rfl
    let v11 := either v8 v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [8, 10]⟩ = w12 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 11 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11]
    change v11 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5))
    simp [v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph26 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 1) (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 4]⟩ = w10 := rfl
    let v10 := both (x 2) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [2, 5]⟩ = w11 := rfl
    let v11 := either v8 v9
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [8, 9]⟩ = w12 := rfl
    let v12 := either v11 v10
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [11, 10]⟩ = w13 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 12 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12]
    change v12 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5))
    simp [v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph27 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [8, 10]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := either (x 1) (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [1, 5]⟩ = w10 := rfl
    let v10 := both (x 4) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [4, 9]⟩ = w11 := rfl
    let v11 := either v8 v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [8, 10]⟩ = w12 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 11 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11]
    change v11 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5))
    simp [v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph28 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [11, 10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := both (x 0) v6
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [0, 6]⟩ = w8 := rfl
    let v8 := both (x 1) (x 2)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [1, 2]⟩ = w9 := rfl
    let v9 := either (x 4) (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [4, 5]⟩ = w10 := rfl
    let v10 := both (x 3) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [3, 9]⟩ = w11 := rfl
    let v11 := either v7 v8
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [7, 8]⟩ = w12 := rfl
    let v12 := either v11 v10
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [11, 10]⟩ = w13 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 12 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12]
    change v12 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5))
    simp [v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph29 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [11, 10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := both (x 0) v6
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [0, 6]⟩ = w8 := rfl
    let v8 := both (x 2) (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [2, 4]⟩ = w9 := rfl
    let v9 := either (x 1) (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [1, 5]⟩ = w10 := rfl
    let v10 := both (x 3) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [3, 9]⟩ = w11 := rfl
    let v11 := either v7 v8
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [7, 8]⟩ = w12 := rfl
    let v12 := either v11 v10
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [11, 10]⟩ = w13 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 12 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12]
    change v12 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5))
    simp [v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph30 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [10, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := either v7 (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 4]⟩ = w9 := rfl
    let v9 := either v8 (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 5]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := both (x 1) (x 2)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 2]⟩ = w12 := rfl
    let v12 := either v10 v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [10, 11]⟩ = w13 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 12 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12]
    change v12 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2))
    simp [v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph31 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := either v7 (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 4]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := either (x 2) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [2, 5]⟩ = w11 := rfl
    let v11 := both (x 1) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 10]⟩ = w12 := rfl
    let v12 := either v9 v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [9, 11]⟩ = w13 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 12 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12]
    change v12 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5))
    simp [v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph32 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := either v7 (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 4]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := both (x 1) (x 2)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [1, 2]⟩ = w11 := rfl
    let v11 := both (x 3) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [3, 5]⟩ = w12 := rfl
    let v12 := either v9 v10
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [9, 10]⟩ = w13 := rfl
    let v13 := either v12 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 11]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5))
    simp [v13, v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph33 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := either (x 2) (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [2, 4]⟩ = w10 := rfl
    let v10 := both (x 1) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [1, 9]⟩ = w11 := rfl
    let v11 := both (x 2) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [2, 5]⟩ = w12 := rfl
    let v12 := either v8 v10
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [8, 10]⟩ = w13 := rfl
    let v13 := either v12 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 11]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5))
    simp [v13, v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph34 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := either (x 2) (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [2, 4]⟩ = w10 := rfl
    let v10 := both (x 1) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [1, 9]⟩ = w11 := rfl
    let v11 := both (x 3) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [3, 5]⟩ = w12 := rfl
    let v12 := either v8 v10
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [8, 10]⟩ = w13 := rfl
    let v13 := either v12 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 11]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5))
    simp [v13, v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph35 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 1) (x 2)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 2]⟩ = w10 := rfl
    let v10 := either (x 4) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [4, 5]⟩ = w11 := rfl
    let v11 := both (x 3) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [3, 10]⟩ = w12 := rfl
    let v12 := either v8 v9
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [8, 9]⟩ = w13 := rfl
    let v13 := either v12 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 11]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5))
    simp [v13, v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph36 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 1) (x 2)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 2]⟩ = w10 := rfl
    let v10 := either (x 3) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [3, 5]⟩ = w11 := rfl
    let v11 := both (x 4) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [4, 10]⟩ = w12 := rfl
    let v12 := either v8 v9
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [8, 9]⟩ = w13 := rfl
    let v13 := either v12 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 11]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5))
    simp [v13, v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph37 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 1) (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 4]⟩ = w10 := rfl
    let v10 := either (x 2) (x 4)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [2, 4]⟩ = w11 := rfl
    let v11 := both (x 5) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [5, 10]⟩ = w12 := rfl
    let v12 := either v8 v9
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [8, 9]⟩ = w13 := rfl
    let v13 := either v12 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 11]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5))
    simp [v13, v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph38 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [13, 11]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := both (x 0) v6
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [0, 6]⟩ = w8 := rfl
    let v8 := both (x 1) (x 2)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [1, 2]⟩ = w9 := rfl
    let v9 := either (x 4) (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [4, 5]⟩ = w10 := rfl
    let v10 := both (x 3) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [3, 9]⟩ = w11 := rfl
    let v11 := both (x 4) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [4, 5]⟩ = w12 := rfl
    let v12 := either v7 v8
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [7, 8]⟩ = w13 := rfl
    let v13 := either v12 v10
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 10]⟩ = w14 := rfl
    let v14 := either v13 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 11]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph39 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := both (x 0) v6
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.and, [0, 6]⟩ = w8 := rfl
    let v8 := either (x 1) (x 5)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [1, 5]⟩ = w9 := rfl
    let v9 := both (x 3) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [3, 8]⟩ = w10 := rfl
    let v10 := either (x 2) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [2, 5]⟩ = w11 := rfl
    let v11 := both (x 4) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [4, 10]⟩ = w12 := rfl
    let v12 := either v7 v9
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [7, 9]⟩ = w13 := rfl
    let v13 := either v12 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 11]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5))
    simp [v13, v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph40 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := either v7 (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 4]⟩ = w9 := rfl
    let v9 := either v8 (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 5]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := both (x 1) (x 2)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 2]⟩ = w12 := rfl
    let v12 := both (x 3) (x 4)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [3, 4]⟩ = w13 := rfl
    let v13 := either v10 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [10, 11]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph41 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := either v7 (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 4]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := either (x 2) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [2, 5]⟩ = w11 := rfl
    let v11 := both (x 1) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 10]⟩ = w12 := rfl
    let v12 := both (x 3) (x 4)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [3, 4]⟩ = w13 := rfl
    let v13 := either v9 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [9, 11]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph42 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w6 := [x 0, x 1, x 2, x 3, x 4, x 5]
    have start : List.ofFn x = w6 := rfl
    let v6 := either (x 1) (x 2)
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, v6]
    have g6 : gateStep w6 ⟨.or, [1, 2]⟩ = w7 := rfl
    let v7 := either v6 (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7]
    have g7 : gateStep w7 ⟨.or, [6, 3]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := either (x 2) (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [2, 4]⟩ = w10 := rfl
    let v10 := both (x 1) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [1, 9]⟩ = w11 := rfl
    let v11 := either (x 3) (x 4)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [3, 4]⟩ = w12 := rfl
    let v12 := both (x 5) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [5, 11]⟩ = w13 := rfl
    let v13 := either v8 v10
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [8, 10]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g6, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, v6, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph43 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 10]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 3) (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [3, 4]⟩ = w10 := rfl
    let v10 := both (x 5) (x 6)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [5, 6]⟩ = w11 := rfl
    let v11 := either v8 v9
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [8, 9]⟩ = w12 := rfl
    let v12 := either v11 v10
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [11, 10]⟩ = w13 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 12 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12]
    change v12 = ((x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6))
    simp [v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph44 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := both (x 5) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [5, 6]⟩ = w12 := rfl
    let v12 := either v10 v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [10, 11]⟩ = w13 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 12 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12]
    change v12 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6))
    simp [v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph45 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := both (x 1) (x 4)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [1, 4]⟩ = w11 := rfl
    let v11 := both (x 5) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [5, 6]⟩ = w12 := rfl
    let v12 := either v9 v10
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [9, 10]⟩ = w13 := rfl
    let v13 := either v12 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 11]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6))
    simp [v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph46 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := either (x 5) (x 6)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [5, 6]⟩ = w11 := rfl
    let v11 := both (x 4) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [4, 10]⟩ = w12 := rfl
    let v12 := either v9 v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [9, 11]⟩ = w13 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 12 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12]
    change v12 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6))
    simp [v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph47 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [13, 11]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 1) (x 2)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 2]⟩ = w10 := rfl
    let v10 := both (x 3) (x 4)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [3, 4]⟩ = w11 := rfl
    let v11 := both (x 5) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [5, 6]⟩ = w12 := rfl
    let v12 := either v8 v9
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [8, 9]⟩ = w13 := rfl
    let v13 := either v12 v10
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 10]⟩ = w14 := rfl
    let v14 := either v13 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 11]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph48 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7 := by
  let C : Circuit := ⟨[⟨.or, [0, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 0) (x 3)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [0, 3]⟩ = w8 := rfl
    let v8 := both (x 1) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [1, 7]⟩ = w9 := rfl
    let v9 := either (x 0) (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [0, 4]⟩ = w10 := rfl
    let v10 := both (x 2) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [2, 9]⟩ = w11 := rfl
    let v11 := both (x 5) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [5, 6]⟩ = w12 := rfl
    let v12 := either v8 v10
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [8, 10]⟩ = w13 := rfl
    let v13 := either v12 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 11]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6))
    simp [v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph49 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 1) (x 3)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 3]⟩ = w10 := rfl
    let v10 := either (x 5) (x 6)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [5, 6]⟩ = w11 := rfl
    let v11 := both (x 4) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [4, 10]⟩ = w12 := rfl
    let v12 := either v8 v9
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [8, 9]⟩ = w13 := rfl
    let v13 := either v12 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [12, 11]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6))
    simp [v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph50 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := either v9 (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [9, 5]⟩ = w11 := rfl
    let v11 := either v10 (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [10, 6]⟩ = w12 := rfl
    let v12 := both (x 0) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [0, 11]⟩ = w13 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 12 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12]
    change v12 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6))
    simp [v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph51 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [11, 12]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := either v9 (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [9, 5]⟩ = w11 := rfl
    let v11 := both (x 0) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [0, 10]⟩ = w12 := rfl
    let v12 := both (x 1) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [1, 6]⟩ = w13 := rfl
    let v13 := either v11 v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [11, 12]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6))
    simp [v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph52 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := both (x 1) (x 2)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 2]⟩ = w12 := rfl
    let v12 := both (x 5) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [5, 6]⟩ = w13 := rfl
    let v13 := either v10 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [10, 11]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph53 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := either (x 5) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [5, 6]⟩ = w12 := rfl
    let v12 := both (x 1) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [1, 11]⟩ = w13 := rfl
    let v13 := either v10 v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [10, 12]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6))
    simp [v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph54 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := both (x 1) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 5]⟩ = w12 := rfl
    let v12 := both (x 2) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [2, 6]⟩ = w13 := rfl
    let v13 := either v10 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [10, 11]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph55 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := either (x 1) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [1, 6]⟩ = w12 := rfl
    let v12 := both (x 5) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [5, 11]⟩ = w13 := rfl
    let v13 := either v10 v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [10, 12]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6))
    simp [v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph56 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := either (x 2) (x 4)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [2, 4]⟩ = w11 := rfl
    let v11 := both (x 1) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 10]⟩ = w12 := rfl
    let v12 := both (x 5) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [5, 6]⟩ = w13 := rfl
    let v13 := either v9 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [9, 11]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph57 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := both (x 1) (x 2)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [1, 2]⟩ = w11 := rfl
    let v11 := both (x 3) (x 4)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [3, 4]⟩ = w12 := rfl
    let v12 := both (x 5) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [5, 6]⟩ = w13 := rfl
    let v13 := either v9 v10
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [9, 10]⟩ = w14 := rfl
    let v14 := either v13 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 11]⟩ = w15 := rfl
    let v15 := either v14 v12
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 12]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph58 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := both (x 1) (x 2)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [1, 2]⟩ = w11 := rfl
    let v11 := either (x 5) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [5, 6]⟩ = w12 := rfl
    let v12 := both (x 4) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [4, 11]⟩ = w13 := rfl
    let v13 := either v9 v10
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [9, 10]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph59 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := either (x 4) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [4, 5]⟩ = w11 := rfl
    let v11 := both (x 1) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 10]⟩ = w12 := rfl
    let v12 := both (x 2) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [2, 6]⟩ = w13 := rfl
    let v13 := either v9 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [9, 11]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph60 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 0) (x 4)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [0, 4]⟩ = w8 := rfl
    let v8 := both (x 1) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [1, 7]⟩ = w9 := rfl
    let v9 := either (x 0) (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [0, 5]⟩ = w10 := rfl
    let v10 := both (x 2) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [2, 9]⟩ = w11 := rfl
    let v11 := either (x 0) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [0, 6]⟩ = w12 := rfl
    let v12 := both (x 3) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [3, 11]⟩ = w13 := rfl
    let v13 := either v8 v10
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [8, 10]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph61 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := both (x 2) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [2, 5]⟩ = w11 := rfl
    let v11 := either (x 1) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [1, 6]⟩ = w12 := rfl
    let v12 := both (x 4) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [4, 11]⟩ = w13 := rfl
    let v13 := either v9 v10
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [9, 10]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph62 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [9, 12]⟩], 13⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := either (x 1) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [1, 5]⟩ = w11 := rfl
    let v11 := either v10 (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [10, 6]⟩ = w12 := rfl
    let v12 := both (x 4) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [4, 11]⟩ = w13 := rfl
    let v13 := either v9 v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [9, 12]⟩ = w14 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 13 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13]
    change v13 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6))
    simp [v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph63 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := both (x 1) (x 4)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [1, 4]⟩ = w11 := rfl
    let v11 := either (x 4) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [4, 6]⟩ = w12 := rfl
    let v12 := both (x 5) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [5, 11]⟩ = w13 := rfl
    let v13 := either v9 v10
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [9, 10]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph64 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := either (x 5) (x 6)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [5, 6]⟩ = w11 := rfl
    let v11 := both (x 4) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [4, 10]⟩ = w12 := rfl
    let v12 := both (x 5) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [5, 6]⟩ = w13 := rfl
    let v13 := either v9 v11
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [9, 11]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph65 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 10]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 1) (x 2)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 2]⟩ = w10 := rfl
    let v10 := either (x 4) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [4, 5]⟩ = w11 := rfl
    let v11 := both (x 3) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [3, 10]⟩ = w12 := rfl
    let v12 := both (x 4) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [4, 6]⟩ = w13 := rfl
    let v13 := either v8 v9
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [8, 9]⟩ = w14 := rfl
    let v14 := either v13 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 11]⟩ = w15 := rfl
    let v15 := either v14 v12
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 12]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph66 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 10]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := both (x 1) (x 3)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 3]⟩ = w10 := rfl
    let v10 := either (x 2) (x 3)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [2, 3]⟩ = w11 := rfl
    let v11 := both (x 4) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [4, 10]⟩ = w12 := rfl
    let v12 := both (x 5) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [5, 6]⟩ = w13 := rfl
    let v13 := either v8 v9
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [8, 9]⟩ = w14 := rfl
    let v14 := either v13 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 11]⟩ = w15 := rfl
    let v15 := either v14 v12
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 12]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph67 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [13, 12]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := both (x 0) v7
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.and, [0, 7]⟩ = w9 := rfl
    let v9 := either (x 1) (x 5)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [1, 5]⟩ = w10 := rfl
    let v10 := both (x 3) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [3, 9]⟩ = w11 := rfl
    let v11 := either (x 2) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [2, 6]⟩ = w12 := rfl
    let v12 := both (x 4) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [4, 11]⟩ = w13 := rfl
    let v13 := either v8 v10
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.or, [8, 10]⟩ = w14 := rfl
    let v14 := either v13 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [13, 12]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph68 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [12, 13]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := either v9 (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [9, 5]⟩ = w11 := rfl
    let v11 := either v10 (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [10, 6]⟩ = w12 := rfl
    let v12 := both (x 0) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [0, 11]⟩ = w13 := rfl
    let v13 := both (x 1) (x 2)
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [1, 2]⟩ = w14 := rfl
    let v14 := either v12 v13
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [12, 13]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph69 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := either v9 (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [9, 5]⟩ = w11 := rfl
    let v11 := both (x 0) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [0, 10]⟩ = w12 := rfl
    let v12 := either (x 2) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [2, 6]⟩ = w13 := rfl
    let v13 := both (x 1) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [1, 12]⟩ = w14 := rfl
    let v14 := either v11 v13
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [11, 13]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph70 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := either v9 (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [9, 5]⟩ = w11 := rfl
    let v11 := both (x 0) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [0, 10]⟩ = w12 := rfl
    let v12 := both (x 1) (x 2)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [1, 2]⟩ = w13 := rfl
    let v13 := both (x 3) (x 6)
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [3, 6]⟩ = w14 := rfl
    let v14 := either v11 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [11, 12]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph71 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := either (x 2) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [2, 5]⟩ = w12 := rfl
    let v12 := either v11 (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [11, 6]⟩ = w13 := rfl
    let v13 := both (x 1) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [1, 12]⟩ = w14 := rfl
    let v14 := either v10 v13
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [10, 13]⟩ = w15 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 14 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14]
    change v14 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6))
    simp [v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph72 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := either (x 2) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [2, 5]⟩ = w12 := rfl
    let v12 := both (x 1) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [1, 11]⟩ = w13 := rfl
    let v13 := both (x 2) (x 6)
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [2, 6]⟩ = w14 := rfl
    let v14 := either v10 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [10, 12]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph73 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := either (x 2) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [2, 5]⟩ = w12 := rfl
    let v12 := both (x 1) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [1, 11]⟩ = w13 := rfl
    let v13 := both (x 3) (x 6)
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [3, 6]⟩ = w14 := rfl
    let v14 := either v10 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [10, 12]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph74 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := either (x 2) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [2, 5]⟩ = w12 := rfl
    let v12 := both (x 1) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [1, 11]⟩ = w13 := rfl
    let v13 := both (x 5) (x 6)
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [5, 6]⟩ = w14 := rfl
    let v14 := either v10 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [10, 12]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph75 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := both (x 1) (x 2)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 2]⟩ = w12 := rfl
    let v12 := either (x 5) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [5, 6]⟩ = w13 := rfl
    let v13 := both (x 3) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [3, 12]⟩ = w14 := rfl
    let v14 := either v10 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [10, 11]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph76 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := both (x 1) (x 2)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 2]⟩ = w12 := rfl
    let v12 := either (x 3) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [3, 6]⟩ = w13 := rfl
    let v13 := both (x 5) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [5, 12]⟩ = w14 := rfl
    let v14 := either v10 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [10, 11]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph77 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := either (x 5) (x 6)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [5, 6]⟩ = w12 := rfl
    let v12 := both (x 1) v11
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.and, [1, 11]⟩ = w13 := rfl
    let v13 := both (x 5) (x 6)
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [5, 6]⟩ = w14 := rfl
    let v14 := either v10 v12
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [10, 12]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph78 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := either v8 (x 4)
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.or, [8, 4]⟩ = w10 := rfl
    let v10 := both (x 0) v9
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [0, 9]⟩ = w11 := rfl
    let v11 := both (x 1) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 5]⟩ = w12 := rfl
    let v12 := either (x 2) (x 5)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [2, 5]⟩ = w13 := rfl
    let v13 := both (x 6) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [6, 12]⟩ = w14 := rfl
    let v14 := either v10 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [10, 11]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph79 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 0) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [0, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 4)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 4]⟩ = w9 := rfl
    let v9 := both (x 1) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [1, 8]⟩ = w10 := rfl
    let v10 := either (x 0) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [0, 5]⟩ = w11 := rfl
    let v11 := both (x 2) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [2, 10]⟩ = w12 := rfl
    let v12 := either (x 0) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [0, 6]⟩ = w13 := rfl
    let v13 := both (x 3) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [3, 12]⟩ = w14 := rfl
    let v14 := either v9 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [9, 11]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph80 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := either (x 2) (x 4)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [2, 4]⟩ = w11 := rfl
    let v11 := both (x 1) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 10]⟩ = w12 := rfl
    let v12 := either (x 5) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [5, 6]⟩ = w13 := rfl
    let v13 := both (x 3) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [3, 12]⟩ = w14 := rfl
    let v14 := either v9 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [9, 11]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph81 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := either (x 2) (x 4)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [2, 4]⟩ = w11 := rfl
    let v11 := both (x 1) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 10]⟩ = w12 := rfl
    let v12 := either (x 3) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [3, 6]⟩ = w13 := rfl
    let v13 := both (x 5) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [5, 12]⟩ = w14 := rfl
    let v14 := either v9 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [9, 11]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph82 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := both (x 1) (x 2)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [1, 2]⟩ = w11 := rfl
    let v11 := either (x 3) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [3, 5]⟩ = w12 := rfl
    let v12 := either v11 (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [11, 6]⟩ = w13 := rfl
    let v13 := both (x 4) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [4, 12]⟩ = w14 := rfl
    let v14 := either v9 v10
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [9, 10]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph83 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := either (x 4) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [4, 5]⟩ = w11 := rfl
    let v11 := both (x 1) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [1, 10]⟩ = w12 := rfl
    let v12 := either (x 2) (x 4)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [2, 4]⟩ = w13 := rfl
    let v13 := both (x 6) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [6, 12]⟩ = w14 := rfl
    let v14 := either v9 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [9, 11]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph84 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [11, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := both (x 2) (x 5)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.and, [2, 5]⟩ = w11 := rfl
    let v11 := either (x 1) (x 5)
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.or, [1, 5]⟩ = w12 := rfl
    let v12 := either v11 (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [11, 6]⟩ = w13 := rfl
    let v13 := both (x 4) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [4, 12]⟩ = w14 := rfl
    let v14 := either v9 v10
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [9, 10]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

private theorem graph85 : PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9 := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, FanInTwo, Set.mem_insert_iff]
  · intro x
    let w7 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6]
    have start : List.ofFn x = w7 := rfl
    let v7 := either (x 1) (x 2)
    let w8 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7]
    have g7 : gateStep w7 ⟨.or, [1, 2]⟩ = w8 := rfl
    let v8 := either v7 (x 3)
    let w9 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8]
    have g8 : gateStep w8 ⟨.or, [7, 3]⟩ = w9 := rfl
    let v9 := both (x 0) v8
    let w10 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9]
    have g9 : gateStep w9 ⟨.and, [0, 8]⟩ = w10 := rfl
    let v10 := either (x 1) (x 6)
    let w11 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10]
    have g10 : gateStep w10 ⟨.or, [1, 6]⟩ = w11 := rfl
    let v11 := both (x 4) v10
    let w12 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11]
    have g11 : gateStep w11 ⟨.and, [4, 10]⟩ = w12 := rfl
    let v12 := either (x 2) (x 6)
    let w13 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12]
    have g12 : gateStep w12 ⟨.or, [2, 6]⟩ = w13 := rfl
    let v13 := both (x 5) v12
    let w14 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13]
    have g13 : gateStep w13 ⟨.and, [5, 12]⟩ = w14 := rfl
    let v14 := either v9 v11
    let w15 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14]
    have g14 : gateStep w14 ⟨.or, [9, 11]⟩ = w15 := rfl
    let v15 := either v14 v13
    let w16 := [x 0, x 1, x 2, x 3, x 4, x 5, x 6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
    have g15 : gateStep w15 ⟨.or, [14, 13]⟩ = w16 := rfl
    change (C.gates.foldl gateStep (List.ofFn x)).getD 15 false = _
    rw [start]
    simp only [C, List.foldl_cons, List.foldl_nil, g7, g8, g9, g10, g11, g12, g13, g14, g15]
    change v15 = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6))
    simp [v15, v14, v13, v12, v11, v10, v9, v8, v7, both, either, Bool.and_or_distrib_left, Bool.and_or_distrib_right,
      Bool.and_comm, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

end PEqualNP.Outside.L_meta_926

theorem PEqualNP.Outside.L_meta_926 : (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) :=
  ⟨PEqualNP.Outside.L_meta_926.graph1, PEqualNP.Outside.L_meta_926.graph2, PEqualNP.Outside.L_meta_926.graph3, PEqualNP.Outside.L_meta_926.graph4, PEqualNP.Outside.L_meta_926.graph5, PEqualNP.Outside.L_meta_926.graph6, PEqualNP.Outside.L_meta_926.graph7, PEqualNP.Outside.L_meta_926.graph8, PEqualNP.Outside.L_meta_926.graph9, PEqualNP.Outside.L_meta_926.graph10, PEqualNP.Outside.L_meta_926.graph11, PEqualNP.Outside.L_meta_926.graph12, PEqualNP.Outside.L_meta_926.graph13, PEqualNP.Outside.L_meta_926.graph14, PEqualNP.Outside.L_meta_926.graph15, PEqualNP.Outside.L_meta_926.graph16, PEqualNP.Outside.L_meta_926.graph17, PEqualNP.Outside.L_meta_926.graph18, PEqualNP.Outside.L_meta_926.graph19, PEqualNP.Outside.L_meta_926.graph20, PEqualNP.Outside.L_meta_926.graph21, PEqualNP.Outside.L_meta_926.graph22, PEqualNP.Outside.L_meta_926.graph23, PEqualNP.Outside.L_meta_926.graph24, PEqualNP.Outside.L_meta_926.graph25, PEqualNP.Outside.L_meta_926.graph26, PEqualNP.Outside.L_meta_926.graph27, PEqualNP.Outside.L_meta_926.graph28, PEqualNP.Outside.L_meta_926.graph29, PEqualNP.Outside.L_meta_926.graph30, PEqualNP.Outside.L_meta_926.graph31, PEqualNP.Outside.L_meta_926.graph32, PEqualNP.Outside.L_meta_926.graph33, PEqualNP.Outside.L_meta_926.graph34, PEqualNP.Outside.L_meta_926.graph35, PEqualNP.Outside.L_meta_926.graph36, PEqualNP.Outside.L_meta_926.graph37, PEqualNP.Outside.L_meta_926.graph38, PEqualNP.Outside.L_meta_926.graph39, PEqualNP.Outside.L_meta_926.graph40, PEqualNP.Outside.L_meta_926.graph41, PEqualNP.Outside.L_meta_926.graph42, PEqualNP.Outside.L_meta_926.graph43, PEqualNP.Outside.L_meta_926.graph44, PEqualNP.Outside.L_meta_926.graph45, PEqualNP.Outside.L_meta_926.graph46, PEqualNP.Outside.L_meta_926.graph47, PEqualNP.Outside.L_meta_926.graph48, PEqualNP.Outside.L_meta_926.graph49, PEqualNP.Outside.L_meta_926.graph50, PEqualNP.Outside.L_meta_926.graph51, PEqualNP.Outside.L_meta_926.graph52, PEqualNP.Outside.L_meta_926.graph53, PEqualNP.Outside.L_meta_926.graph54, PEqualNP.Outside.L_meta_926.graph55, PEqualNP.Outside.L_meta_926.graph56, PEqualNP.Outside.L_meta_926.graph57, PEqualNP.Outside.L_meta_926.graph58, PEqualNP.Outside.L_meta_926.graph59, PEqualNP.Outside.L_meta_926.graph60, PEqualNP.Outside.L_meta_926.graph61, PEqualNP.Outside.L_meta_926.graph62, PEqualNP.Outside.L_meta_926.graph63, PEqualNP.Outside.L_meta_926.graph64, PEqualNP.Outside.L_meta_926.graph65, PEqualNP.Outside.L_meta_926.graph66, PEqualNP.Outside.L_meta_926.graph67, PEqualNP.Outside.L_meta_926.graph68, PEqualNP.Outside.L_meta_926.graph69, PEqualNP.Outside.L_meta_926.graph70, PEqualNP.Outside.L_meta_926.graph71, PEqualNP.Outside.L_meta_926.graph72, PEqualNP.Outside.L_meta_926.graph73, PEqualNP.Outside.L_meta_926.graph74, PEqualNP.Outside.L_meta_926.graph75, PEqualNP.Outside.L_meta_926.graph76, PEqualNP.Outside.L_meta_926.graph77, PEqualNP.Outside.L_meta_926.graph78, PEqualNP.Outside.L_meta_926.graph79, PEqualNP.Outside.L_meta_926.graph80, PEqualNP.Outside.L_meta_926.graph81, PEqualNP.Outside.L_meta_926.graph82, PEqualNP.Outside.L_meta_926.graph83, PEqualNP.Outside.L_meta_926.graph84, PEqualNP.Outside.L_meta_926.graph85⟩
