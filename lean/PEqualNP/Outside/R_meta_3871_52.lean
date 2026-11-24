import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3871_52
    (h1 : ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ))) (12 : ℕ))
    (h2 : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 x2 || x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)); ∀ (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Bool), PEqualNP.MetaComplexity.FanInTwo x3 → PEqualNP.MetaComplexity.FanInTwo x4 → x3.output + (1 : ℕ) = (8 : ℕ) + x3.size → x4.output ≠ (8 : ℕ) + x3.size → List.countP (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => (if x10.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x10.inputs else x10.inputs).contains ((8 : ℕ) + x3.size)) x4.gates = (1 : ℕ) → (13 : ℕ) ≤ x3.size + x4.size → x3.size + x4.size ≤ (13 : ℕ) → (∀ (x13 : Fin (8 : ℕ)), (PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => x14 x13) ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => !x14 x13) → (∀ (x14 : Fin (8 : ℕ) → Bool), x1 x14 ≠ x2 x14 → PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 x14 = !x5) → (∀ (x15 : Fin (8 : ℕ) → Bool), x4.eval (x3.wires (List.ofFn x15) ++ [PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 x15]) = x1 x15) → (∀ (x16 : Fin (8 : ℕ) → Bool), x4.eval (x3.wires (List.ofFn x16) ++ [x5]) = x2 x16) → False) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 x2 || x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ)); ∀ (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Bool), PEqualNP.MetaComplexity.FanInTwo x3 → PEqualNP.MetaComplexity.FanInTwo x4 → x3.output + (1 : ℕ) = (8 : ℕ) + x3.size → x4.output ≠ (8 : ℕ) + x3.size → List.countP (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => (if x10.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x10.inputs else x10.inputs).contains ((8 : ℕ) + x3.size)) x4.gates = (1 : ℕ) → (11 : ℕ) ≤ x3.size + x4.size → x3.size + x4.size ≤ (13 : ℕ) → (∀ (x13 : Fin (8 : ℕ)), (PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => x14 x13) ∧ PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 ≠ fun (x14 : Fin (8 : ℕ) → Bool) => !x14 x13) → (∀ (x14 : Fin (8 : ℕ) → Bool), x1 x14 ≠ x2 x14 → PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 x14 = !x5) → (∀ (x15 : Fin (8 : ℕ) → Bool), x4.eval (x3.wires (List.ofFn x15) ++ [PEqualNP.MetaComplexity.circuitFun (8 : ℕ) x3 x15]) = x1 x15) → (∀ (x16 : Fin (8 : ℕ) → Bool), x4.eval (x3.wires (List.ofFn x16) ++ [x5]) = x2 x16) → False := by
  let step : List Bool → Gate → List Bool := fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let ren : (ℕ → ℕ) → Gate → Gate := fun f g => ⟨g.op, g.inputs.map f⟩
  have translate (f : ℕ → ℕ) (u v : List Bool)
      (read : ∀ (z : List Bool) i, (v ++ z).getD (f i) false = (u ++ z).getD i false)
      (gs : List Gate) : ∃ z, gs.foldl step u = u ++ z ∧ (gs.map (ren f)).foldl step v = v ++ z := by
    induction gs using List.reverseRecOn with
    | nil => exact ⟨[], by simp, by simp⟩
    | append_singleton gs g ih =>
      obtain ⟨z, old, fresh⟩ := ih
      refine ⟨z ++ [g.op.eval (g.inputs.map fun i => (u ++ z).getD i false)], ?_, ?_⟩
      · rw [List.foldl_append, old]
        simp [step, List.append_assoc]
      · rw [List.map_append, List.foldl_append, fresh]
        simp only [step, ren, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
          List.append_assoc, List.map_map, Function.comp_def]
        rw [List.map_congr_left (fun i _ => read z i)]
  have wires_len (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
  have merge (A B : Circuit) (hA : FanInTwo A) (hB : FanInTwo B) (ho : A.output + 1 = 8 + A.size) :
      ∃ C : Circuit, FanInTwo C ∧ C.size = A.size + B.size ∧ ∀ x : Fin 8 → Bool,
        C.eval (List.ofFn x) = B.eval (A.wires (List.ofFn x) ++ [circuitFun 8 A x]) := by
    let m := 8 + A.size
    let σ : ℕ → ℕ := fun i => if i < m then i else if i = m then A.output else i - 1
    refine ⟨⟨A.gates ++ B.gates.map (ren σ), σ B.output⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact hA g h
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
        exact ⟨(hB a ha).1, by simpa [ren] using (hB a ha).2⟩
    · simp [Circuit.size]
    · intro x
      let v := A.wires (List.ofFn x)
      have hv : v.length = m := by
        show (A.gates.foldl step (List.ofFn x)).length = _
        rw [wires_len]; simp [m, Circuit.size]
      let u := v ++ [circuitFun 8 A x]
      have read : ∀ (z : List Bool) i, (v ++ z).getD (σ i) false = (u ++ z).getD i false := by
        intro z i
        have hc : circuitFun 8 A x = v.getD A.output false := rfl
        by_cases h1 : i < m
        · simp only [σ, h1, ite_true, u, List.append_assoc]
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        by_cases h2 : i = m
        · subst h2
          simp only [σ, lt_irrefl, ite_false, ite_true, u, List.append_assoc]
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hv]
          simp [hc]
        · have e : σ i = i - 1 := by simp [σ, h1, h2]
          rw [e, List.getD_append_right _ _ _ _ (by rw [hv]; omega),
            List.getD_append_right _ _ _ _ (by simp [u, hv]; omega)]
          simp only [u, List.length_append, List.length_singleton, hv]
          congr 1
          omega
      obtain ⟨z, old, fresh⟩ := translate σ u v read B.gates
      show ((A.gates ++ B.gates.map (ren σ)).foldl step (List.ofFn x)).getD (σ B.output) false =
        (B.gates.foldl step u).getD B.output false
      rw [List.foldl_append]
      change ((B.gates.map (ren σ)).foldl step v).getD _ _ = _
      rw [fresh, old]
      simpa using read z B.output
  
  intro x1 x2 A B k fanA fanB ho hout hcount hlo hhi hnl hsw hf hh
  by_cases hs : 13 ≤ A.size + B.size
  · exact h2 A B k fanA fanB ho hout hcount hs hhi hnl hsw hf hh
  · obtain ⟨C, fanC, sizeC, evalC⟩ := merge A B fanA fanB ho
    exact h1 ⟨C, fanC, by omega, fun x => (evalC x).trans (hf x)⟩
