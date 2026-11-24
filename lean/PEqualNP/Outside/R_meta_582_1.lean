import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_582_1
    (h1 : ∃ (P C1 C2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 P ∧
      PEqualNP.MetaComplexity.Monotone2 C1 ∧
      PEqualNP.MetaComplexity.Monotone2 C2 ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 + P.size) C1 ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 + P.size) C2 ∧
      C1.output < 14 + P.size + C1.size ∧
      C2.output < 14 + P.size + C2.size ∧
      P.size + C1.size + C2.size + 1 ≤ 26 ∧
      ∀ x : Fin 14 → Bool,
        (C1.eval (P.wires (List.ofFn x)) || C2.eval (P.wires (List.ofFn x))) =
          decide (∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 26 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have foldl_step_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) :
      (gs.foldl step init).length = init.length + gs.length := by
    induction gs generalizing init with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have foldl_step_preserved (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool) (k : ℕ)
      (hk : k < init.length) :
      (gs.foldl step init).getD k false = init.getD k false := by
    induction gs generalizing init with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step init g) (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
  let shiftWire (base shift w : ℕ) : ℕ :=
    if w < base then w else w + shift
  let shiftGate (base shift : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
    ⟨g.op, g.inputs.map (shiftWire base shift)⟩
  let shiftCircuit (base shift : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (shiftGate base shift), shiftWire base shift C.output⟩
  have shiftWire_lt {base shift w k : ℕ} (hk : w < base + k) :
      shiftWire base shift w < base + shift + k := by
    dsimp only [shiftWire]
    split_ifs <;> omega
  have shiftCircuit_wires (base shift : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack base C)
      (init1 init2 : List Bool) (h1l : init1.length = base) (h2l : init2.length = base + shift)
      (hagree : ∀ w < base, init2.getD w false = init1.getD w false) :
      ∀ j ≤ C.gates.length, ∀ w < base + j,
        (((C.gates.take j).map (shiftGate base shift)).foldl step init2).getD (shiftWire base shift w) false =
        ((C.gates.take j).foldl step init1).getD w false := by
    intro j
    induction j with
    | zero =>
      intro _ w hw
      simp only [List.take_zero, List.map_nil, List.foldl_nil]
      have hsw : shiftWire base shift w = w := by simp [shiftWire, show w < base by omega]
      rw [hsw]
      exact hagree w hw
    | succ j ih =>
      intro hj_le w hw
      have hj : j < C.gates.length := by omega
      have htake : C.gates.take (j + 1) = C.gates.take j ++ [C.gates[j]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      rw [htake, List.map_append, List.map_singleton, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
      set w1 := (C.gates.take j).foldl step init1
      set w2 := ((C.gates.take j).map (shiftGate base shift)).foldl step init2
      have hlen1 : w1.length = base + j := by
        simp [w1, foldl_step_length, h1l, Nat.le_of_lt hj]
      have hlen2 : w2.length = base + shift + j := by
        simp [w2, foldl_step_length, h2l, Nat.le_of_lt hj]
      by_cases hw_lt : w < base + j
      · have hw1 : w < w1.length := by omega
        have hw2 : shiftWire base shift w < w2.length := by
          rw [hlen2]
          exact shiftWire_lt hw_lt
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hw1,
          List.getElem?_append_left hw2]
        exact ih (Nat.le_of_lt hj) w hw_lt
      · have hw_eq : w = base + j := by omega
        subst hw_eq
        have hsw : shiftWire base shift (base + j) = base + shift + j := by
          simp [shiftWire]
          omega
        rw [hsw]
        have h_w1 : (step w1 C.gates[j]).getD (base + j) false =
            C.gates[j].op.eval (C.gates[j].inputs.map fun i => w1.getD i false) := by
          simp [step, hlen1]
        have h_w2 : (step w2 (shiftGate base shift C.gates[j])).getD (base + shift + j) false =
            C.gates[j].op.eval
              ((C.gates[j].inputs.map (shiftWire base shift)).map fun i => w2.getD i false) := by
          simp [step, hlen2, shiftGate]
        rw [h_w2, h_w1, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hgate_eq : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
          simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hj]
        have hi_lt : i < base + j := hRB j hj i (by rw [hgate_eq]; exact hi)
        exact ih (Nat.le_of_lt hj) i hi_lt
  let glueOr (P C1 C2 : PEqualNP.CircuitLowerBounds.Circuit) : PEqualNP.CircuitLowerBounds.Circuit :=
    let sC2 := shiftCircuit (14 + P.size) C1.size C2
    let out1 := C1.output
    let out2 := sC2.output
    { gates := P.gates ++ C1.gates ++ sC2.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [out1, out2]⟩],
      output := 14 + P.size + C1.size + C2.size }
  have glueOr_monotone2 (P C1 C2 : PEqualNP.CircuitLowerBounds.Circuit)
      (hP : PEqualNP.MetaComplexity.Monotone2 P) (h1M : PEqualNP.MetaComplexity.Monotone2 C1)
      (h2M : PEqualNP.MetaComplexity.Monotone2 C2) : PEqualNP.MetaComplexity.Monotone2 (glueOr P C1 C2) := by
    intro g hg
    simp only [glueOr, List.mem_append, List.mem_singleton] at hg
    rcases hg with ((hg | hg) | hg) | rfl
    · exact hP g hg
    · exact h1M g hg
    · simp only [shiftCircuit, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      obtain ⟨hop, hlen⟩ := h2M g0 hg0
      exact ⟨hop, by simp [shiftGate, hlen]⟩
    · exact ⟨Set.mem_insert_of_mem _ rfl, by simp⟩
  have glueOr_size (P C1 C2 : PEqualNP.CircuitLowerBounds.Circuit) :
      (glueOr P C1 C2).size = P.size + C1.size + C2.size + 1 := by
    simp [glueOr, PEqualNP.CircuitLowerBounds.Circuit.size, shiftCircuit]
    omega
  have glueOr_eval (P C1 C2 : PEqualNP.CircuitLowerBounds.Circuit)
      (hRB1 : PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 + P.size) C1)
      (hRB2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack (14 + P.size) C2)
      (ho1 : C1.output < 14 + P.size + C1.size) (ho2 : C2.output < 14 + P.size + C2.size)
      (x : Fin 14 → Bool) :
      (glueOr P C1 C2).eval (List.ofFn x) =
        (C1.eval (P.wires (List.ofFn x)) || C2.eval (P.wires (List.ofFn x))) := by
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    dsimp only [glueOr]
    set sC2 := shiftCircuit (14 + P.size) C1.size C2
    set wP := P.gates.foldl step (List.ofFn x)
    set w1 := C1.gates.foldl step wP
    set w2 := sC2.gates.foldl step w1
    have hlenP : wP.length = 14 + P.size := by
      simp [wP, foldl_step_length, PEqualNP.CircuitLowerBounds.Circuit.size]
    have hlen1 : w1.length = 14 + P.size + C1.size := by
      simp [w1, foldl_step_length, hlenP, PEqualNP.CircuitLowerBounds.Circuit.size]
    have hlen2 : w2.length = 14 + P.size + C1.size + C2.size := by
      simp [w2, sC2, shiftCircuit, foldl_step_length, hlen1, PEqualNP.CircuitLowerBounds.Circuit.size]
    rw [List.foldl_append, List.foldl_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    change (step w2 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C1.output, sC2.output]⟩).getD
      (14 + P.size + C1.size + C2.size) false = _
    have h_top : (step w2 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [C1.output, sC2.output]⟩).getD
        (14 + P.size + C1.size + C2.size) false =
        (w2.getD C1.output false || w2.getD sC2.output false) := by
      simp [step, hlen2, PEqualNP.CircuitLowerBounds.GateOp.eval]
    rw [h_top]
    have h_out1 : w2.getD C1.output false = w1.getD C1.output false :=
      foldl_step_preserved sC2.gates w1 C1.output (by omega)
    have h_out2 : w2.getD sC2.output false =
        (C2.gates.foldl step wP).getD C2.output false := by
      have hsh := shiftCircuit_wires (14 + P.size) C1.size C2 hRB2 wP w1 hlenP hlen1
        (fun w hw => foldl_step_preserved C1.gates wP w (by omega))
        C2.gates.length (le_refl _) C2.output ho2
      rw [List.take_length] at hsh
      exact hsh
    rw [h_out1, h_out2]
  obtain ⟨P, C1, C2, hP, h1M, h2M, hRB1, hRB2, ho1, ho2, hsz, hfun⟩ := h1
  refine ⟨glueOr P C1 C2, glueOr_monotone2 P C1 C2 hP h1M h2M, ?_, ?_⟩
  · rw [glueOr_size]
    exact hsz
  · intro x
    rw [glueOr_eval P C1 C2 hRB1 hRB2 ho1 ho2 x, hfun x]
    simp
