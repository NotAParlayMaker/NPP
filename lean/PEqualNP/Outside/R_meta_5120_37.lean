import PEqualNP.Defs

-- Prefix the tail with the gate OR(x0, x3). Under the negated conclusion the two cofactors
-- in the inserted input 4 agree with the nine-input edge function, so the prefixed circuit
-- computes it with the first gate OR(x0, x3), at most 15 gates and the same reads of 4, 6, 7.
-- The two cases are circuits without a NOT gate (monotone runs) and circuits with one.
theorem PEqualNP.Outside.R_meta_5120_37
    (mono : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      (∀ v ∈ ([4, 6, 7] : List ℕ), C.gates.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.head? == some v || (!g.op.eval [false] && g.inputs.contains v)) ≤ 2) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size)
    (negs : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3)) →
      (∀ v ∈ ([4, 6, 7] : List ℕ), C.gates.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs.head? == some v || (!g.op.eval [false] && g.inputs.contains v)) ≤ 2) →
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size)
    : have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); have x2 : (Fin (8 : ℕ) → Bool) → Bool → List Bool := fun (x2 : Fin (8 : ℕ) → Bool) (x3 : Bool) => List.ofFn (Fin.insertNth (4 : Fin (9 : ℕ)) x3 x2) ++ [x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ))]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (14 : ℕ) → (∀ x6 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)], List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.head? == Option.some x6 || !x8.op.eval [Bool.false] && x8.inputs.contains x6) x3.gates ≤ (2 : ℕ)) → (∀ (x7 : Fin (8 : ℕ) → Bool), x3.eval (x2 x7 Bool.false) = x1 x7) → ∃ (x8 : Fin (8 : ℕ) → Bool), x3.eval (x2 x8 Bool.true) ≠ (x1 x8 || x8 (0 : Fin (8 : ℕ)) || x8 (3 : Fin (8 : ℕ))) := by
  intro H w D fan small reads off
  by_contra hcon
  push Not at hcon
  let g0 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0 :: D.gates, D.output⟩
  have extend : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool), ∃ extra : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) l = l ++ extra := by
    intro gs
    induction gs with
    | nil => intro l; exact ⟨[], by simp⟩
    | cons g rest ih =>
      intro l
      obtain ⟨e, he⟩ := ih (l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)])
      exact ⟨g.op.eval (g.inputs.map fun i => l.getD i false) :: e, by rw [List.foldl_cons, he]; simp⟩
  have wiresC : ∀ y : Fin 9 → Bool,
      C.wires (List.ofFn y) = D.wires (List.ofFn y ++ [y 0 || y 3]) := by
    intro y
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    simp only [C, List.foldl_cons]
    congr 1
    simp [g0, PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ]
  have firstC : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 3) := by
    intro y
    rw [wiresC]
    obtain ⟨e, he⟩ := extend D.gates (List.ofFn y ++ [y 0 || y 3])
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    rw [he, List.getD_append _ _ false 9 (by simp),
      List.getD_append_right _ _ false 9 (by simp)]
    simp
  have readsC : ∀ v ∈ ([4, 6, 7] : List ℕ), C.gates.countP (fun g : PEqualNP.CircuitLowerBounds.Gate =>
      g.inputs.head? == some v || (!g.op.eval [false] && g.inputs.contains v)) ≤ 2 := by
    intro v hv
    have hb := reads v hv
    have hv' : v = 4 ∨ v = 6 ∨ v = 7 := by simpa using hv
    rcases hv' with rfl | rfl | rfl <;>
      simpa [C, g0, List.countP_cons, PEqualNP.CircuitLowerBounds.GateOp.eval] using hb
  have computesC : PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
      (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
      (x 6 && x 8) || (x 8 && x 5)) := by
    funext y
    obtain ⟨b, x, rfl⟩ : ∃ (b : Bool) (x : Fin 8 → Bool), y = Fin.insertNth (4 : Fin 9) b x :=
      ⟨y 4, Fin.removeNth 4 y, (Fin.insertNth_self_removeNth 4 y).symm⟩
    have e : PEqualNP.MetaComplexity.circuitFun 9 C (Fin.insertNth (4 : Fin 9) b x) =
        D.eval (w x b) := by
      show (C.wires _).getD D.output false = (D.wires _).getD D.output false
      rw [wiresC]
      rfl
    rw [e]
    cases b
    · rw [off x]
      show (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 ||
        x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && false || false && x 0 ||
        x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
        x 5 && x 7 || x 7 && x 4)
      simp
    · rw [hcon x]
      show (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 || x 2 && x 6 ||
        x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4 || x 0 || x 3) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && true || true && x 0 ||
        x 0 && x 4 || x 1 && x 5 || x 2 && x 6 || x 3 && x 7 || x 4 && x 6 ||
        x 5 && x 7 || x 7 && x 4)
      cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;>
        cases x 6 <;> cases x 7 <;> rfl
  have fanC : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨by simp [g0], by simp [g0]⟩
    · exact fan g hg
  have sizeC : C.size = D.size + 1 := rfl
  by_cases hn : ∃ g ∈ D.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, hg, hgo⟩ := hn
    have big := negs C fanC ⟨g, List.mem_cons_of_mem _ hg, hgo⟩ firstC readsC computesC
    omega
  · push Not at hn
    have hm : ∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp [g0]
      · exact hn g hg
    have big := mono C fanC hm firstC readsC computesC
    omega
