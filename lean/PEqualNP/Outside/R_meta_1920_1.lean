import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Split on how many tail gates read the first inverter or its input.
-- With at most one reader the inverter contracts away and a finite search
-- over the smaller circuits closes the case. With at least two readers,
-- pinning the fourth input to false erases the inverter and both readers,
-- leaving a circuit for the ten-edge cofactor, which needs thirteen gates.
theorem PEqualNP.Outside.R_meta_1920_1
    (contract : ∀ C : Circuit,
      let tail := (C.gates.drop 1).map (fun g => Gate.mk g.op (ite (g.op.eval [false] = true) (g.inputs.take 1) g.inputs))
      FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !(x 4)) →
      (tail.filter (fun g => [4, 9].any fun j => g.inputs.contains j)).length ≤ 1 →
      ∃ (D : Circuit) (b : Bool), FanInTwo D ∧ D.size < C.size ∧
        (D.gates.filter (fun g => g.inputs.contains 4)).length ≤ 1 ∧
        ∀ x : Fin 9 → Bool, circuitFun 9 C x =
          circuitFun 9 D (fun i => if i = 4 then b != x 4 else x i))
    (exclude : ∀ (D : Circuit) (b : Bool), FanInTwo D → D.size ≤ 14 →
      (D.gates.filter (fun g => g.inputs.contains 4)).length ≤ 1 →
      ∃ x : Fin 9 → Bool,
        circuitFun 9 D (fun i => if i = 4 then b != x 4 else x i) ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (erase : ∀ C : Circuit,
      let tail := (C.gates.drop 1).map (fun g => Gate.mk g.op (ite (g.op.eval [false] = true) (g.inputs.take 1) g.inputs))
      FanInTwo C → C.size ≤ 15 →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !(x 4)) →
      2 ≤ (tail.filter (fun g => [4, 9].any fun j => g.inputs.contains j)).length →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 3 ≤ C.size ∧
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x) =
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 5) || (x 1 && x 6) ||
           (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (lower : ∀ s : ℕ, HasCircuitSize 9 (fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) s → 13 ≤ s) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate), x1.length = (15 : ℕ) → x1.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(4 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x4 : Fin x1.length), (∃ (x5 : ℕ) (x6 : ℕ), x5 ≤ x6 ∧ x6 ≤ (9 : ℕ) + ↑x4 ∧ (x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate })) ∨ ∃ x5 ≤ (9 : ℕ) + ↑x4, x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }) → ∃ (x5 : Fin (9 : ℕ) → Bool), { gates := x1, output := (23 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x5) ≠ (fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) x5 := by
  intro x1 hlen hhead hshape
  let C : Circuit := ⟨x1, 23⟩
  have hCsize : C.size = 15 := hlen
  have hfan : FanInTwo C := by
    intro g hg
    change g ∈ x1 at hg
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
    have hsh := hshape i
    rw [hi] at hsh
    rcases hsh with ⟨x5, x6, -, -, h | h⟩ | ⟨x5, -, h⟩
    · refine ⟨?_, ?_⟩
      · rw [h]; simp
      · rw [h]; simp
    · refine ⟨?_, ?_⟩
      · rw [h]; simp
      · rw [h]; simp
    · refine ⟨?_, ?_⟩
      · rw [h]; simp
      · rw [h]; simp
  have hfirst : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !(x 4) := by
    intro x
    have hpfx : ∀ (gs : List Gate) (w : List Bool), ∃ t : List Bool,
        gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
      intro gs w
      induction gs generalizing w with
      | nil => exact ⟨[], by simp⟩
      | cons g gs ih =>
        obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
          simp only [List.foldl_cons, ht, List.append_assoc]⟩
    obtain ⟨rest, hx1⟩ := List.head?_eq_some_iff.mp hhead
    obtain ⟨t, ht⟩ := hpfx rest ((List.ofFn x) ++ [GateOp.not.eval ([(4 : ℕ)].map fun i => (List.ofFn x).getD i false)])
    have hv : GateOp.not.eval ([(4 : ℕ)].map fun i => (List.ofFn x).getD i false) = !(x 4) := by
      have h4 : (List.ofFn x).getD 4 false = x 4 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [GateOp.eval, h4]
    have hw : C.wires (List.ofFn x) = ((List.ofFn x) ++ [GateOp.not.eval ([(4 : ℕ)].map fun i => (List.ofFn x).getD i false)]) ++ t := by
      show x1.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x) = _
      rw [hx1]
      simp only [List.foldl_cons]
      exact ht
    rw [hw, hv]
    simp
  by_contra hcon
  push_neg at hcon
  have hfun : circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    funext x
    exact hcon x
  by_cases hle : (((C.gates.drop 1).map (fun g => Gate.mk g.op (ite (g.op.eval [false] = true) (g.inputs.take 1) g.inputs))).filter (fun g => [4, 9].any fun j => g.inputs.contains j)).length ≤ 1
  · obtain ⟨D, b, hDfan, hDsize, hDone, heq⟩ := contract C hfan hfirst hle
    obtain ⟨x, hx⟩ := exclude D b hDfan (by omega) hDone
    exact hx ((heq x).symm.trans (congrFun hfun x))
  · push_neg at hle
    obtain ⟨D, hDfan, hDsize, hDeval⟩ := erase C hfan (by omega) hfirst (by omega) hfun
    have hcs : HasCircuitSize 9 (fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) D.size :=
      ⟨D, hDfan, le_rfl, hDeval⟩
    have h13 := lower D.size hcs
    omega
