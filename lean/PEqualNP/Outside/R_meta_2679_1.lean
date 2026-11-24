import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2679_1
    (no14 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (split15 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ) ∨ ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size ≤ (11 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x7 = fun (x8 : Fin (7 : ℕ) → Bool) => x1 (Fin.insertNth (0 : Fin (9 : ℕ)) Bool.false (Fin.insertNth (3 : Fin (8 : ℕ)) Bool.false x8))) ∧ ∀ (x8 : Bool), ∃ (x9 : ℕ) (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Circuit), x11.output = x7.output + (1 : ℕ) ∧ List.Forall₂ (fun (x12 x13 : PEqualNP.CircuitLowerBounds.Gate) => x12.op = x13.op ∧ List.Forall₂ (fun (x14 x15 : ℕ) => x15 = x14 + (1 : ℕ) ∨ x15 = (0 : ℕ) ∧ (x14 = x9 ∨ x14 = x10)) x12.inputs x13.inputs) x7.gates x11.gates ∧ ∀ (x12 : Fin (7 : ℕ) → Bool), x11.eval (Bool.true :: List.ofFn x12) = x1 (Fin.insertNth (0 : Fin (9 : ℕ)) x8 (Fin.insertNth (3 : Fin (8 : ℕ)) (!x8) x12)))
    (theta11 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize (7 : ℕ) (fun (x3 : Fin (7 : ℕ) → Bool) => x1 (Fin.insertNth (0 : Fin (9 : ℕ)) Bool.false (Fin.insertNth (3 : Fin (8 : ℕ)) Bool.false x3))) x2 → (11 : ℕ) ≤ x2)
    (noSplice : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 ∧ x2.size = (11 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = fun (x3 : Fin (7 : ℕ) → Bool) => x1 (Fin.insertNth (0 : Fin (9 : ℕ)) Bool.false (Fin.insertNth (3 : Fin (8 : ℕ)) Bool.false x3))) ∧ ∀ (x3 : Bool), ∃ (x4 : ℕ) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.output = x2.output + (1 : ℕ) ∧ List.Forall₂ (fun (x7 x8 : PEqualNP.CircuitLowerBounds.Gate) => x7.op = x8.op ∧ List.Forall₂ (fun (x9 x10 : ℕ) => x10 = x9 + (1 : ℕ) ∨ x10 = (0 : ℕ) ∧ (x9 = x4 ∨ x9 = x5)) x7.inputs x8.inputs) x2.gates x6.gates ∧ ∀ (x7 : Fin (7 : ℕ) → Bool), x6.eval (Bool.true :: List.ofFn x7) = x1 (Fin.insertNth (0 : Fin (9 : ℕ)) x3 (Fin.insertNth (3 : Fin (8 : ℕ)) (!x3) x7))) :
    ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit),   x1.output ≤ (24 : ℕ) →     x2.output ≤ (24 : ℕ) →       (∀ x5 ∈ x1.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (24 : ℕ)) →         (∀ x6 ∈ x2.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (24 : ℕ)) →           x1.size + x2.size ≤ (13 : ℕ) →             PEqualNP.MetaComplexity.Monotone2 x1 →               PEqualNP.MetaComplexity.FanInTwo x2 →                 ¬∀ (x10 : Fin (9 : ℕ) → Bool),                     have x11 : List Bool := x1.wires (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ))]);                     x2.eval (x11 ++ [!x11.getD x1.output Bool.false]) = (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ))) := by
  intro C1 C2 _ _ _ _ hsz hmono hfan heval
  let g0 : Gate := ⟨GateOp.or, [0, 4]⟩
  let gnot : Gate := ⟨GateOp.not, [C1.output]⟩
  let C : Circuit := ⟨g0 :: C1.gates ++ [gnot] ++ C2.gates, C2.output⟩
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hkeep : ∀ (gs : List Gate) (w : List Bool) (k : ℕ), k < w.length →
      (gs.foldl step w).getD k false = w.getD k false := by
    intro gs
    induction gs with
    | nil => intro w k _; rfl
    | cons g gs ih =>
      intro w k hk
      rw [List.foldl_cons, ih _ _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hk
  have hfanC : FanInTwo C := by
    intro g hg
    change g ∈ g0 :: C1.gates ++ [gnot] ++ C2.gates at hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with ((rfl | h1) | rfl) | h2
    · exact ⟨by simp [g0], by decide⟩
    · have hm := hmono g h1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
      exact ⟨by rcases hm.1 with h | h <;> simp [h], hm.2⟩
    · exact ⟨by simp [gnot], by simp [gnot]⟩
    · exact hfan g h2
  have hstep0 : ∀ x : Fin 9 → Bool, step (List.ofFn x) g0 = List.ofFn x ++ [x 0 || x 4] := by
    intro x
    have hor : GateOp.or.eval [(List.ofFn x).getD 0 false, (List.ofFn x).getD 4 false] =
        ((List.ofFn x).getD 0 false || ((List.ofFn x).getD 4 false || false)) := rfl
    change List.ofFn x ++ [GateOp.or.eval [(List.ofFn x).getD 0 false, (List.ofFn x).getD 4 false]] = _
    rw [hor]
    simp [List.getD_eq_getElem?_getD]
  have hfirst : ∀ x : Fin 9 → Bool,
      (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4) := by
    intro x
    change ((C1.gates ++ [gnot] ++ C2.gates).foldl step (step (List.ofFn x) g0)).getD 9 false = _
    rw [hstep0 x, hkeep _ _ 9 (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have hwires : ∀ x : Fin 9 → Bool,
      let w := C1.wires (List.ofFn x ++ [x 0 || x 4])
      C.wires (List.ofFn x) = C2.wires (w ++ [!w.getD C1.output false]) := by
    intro x
    dsimp only
    change ((g0 :: C1.gates ++ [gnot] ++ C2.gates).foldl step (List.ofFn x)) =
      C2.gates.foldl step (C1.gates.foldl step (List.ofFn x ++ [x 0 || x 4]) ++
        [!(C1.gates.foldl step (List.ofFn x ++ [x 0 || x 4])).getD C1.output false])
    rw [List.cons_append, List.cons_append, List.foldl_cons, hstep0 x,
      List.foldl_append, List.foldl_append]
    rfl
  have hedge : ∀ x : Fin 9 → Bool,
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
       x 6 && x 8 || x 8 && x 5) =
      [(1 : ℕ), 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) := by
    decide +kernel
  have hfunC : circuitFun 9 C =
      fun x : Fin 9 → Bool =>
        [(1 : ℕ), 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) := by
    funext x
    change (C.wires (List.ofFn x)).getD C2.output false = _
    rw [hwires x]
    exact (heval x).trans (hedge x)
  have hszC : C.size ≤ 15 := by
    change (g0 :: C1.gates ++ [gnot] ++ C2.gates).length ≤ 15
    simp only [List.length_append, List.length_cons, List.length_nil]
    change C1.gates.length + C2.gates.length ≤ 13 at hsz
    omega
  rcases split15 C hfanC hfirst hfunC hszC with h14 | ⟨B, hfanB, hszB, hfunB, hsplice⟩
  · exact no14 h14
  · have hge : 11 ≤ B.size := theta11 B.size ⟨B, hfanB, le_rfl, congrFun hfunB⟩
    have heq : B.size = 11 := by omega
    exact noSplice ⟨B, hfanB, heq, hfunB, hsplice⟩
