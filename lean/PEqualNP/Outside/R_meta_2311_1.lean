import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2311_1 :
    (∀ D : Circuit,
      FanInTwo D → D.size ≤ 14 →
      (∀ g ∈ D.gates, g.op = GateOp.not → g.inputs.length ≤ 1) →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0]) =
        (fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))) x) →
      let reads := fun g : Gate => g.inputs.contains 0 || g.inputs.contains 9
      (D.gates.filter reads).length = 2 →
      (¬ ∃ pre g post, D.gates = pre ++ g :: post ∧
        ((g.op = GateOp.and ∧ 0 ∈ g.inputs) ∨ (g.op = GateOp.or ∧ 9 ∈ g.inputs)) ∧
        ∃ h ∈ post, reads h = false ∧ 10 + pre.length ∈ h.inputs) →
      (Monotone2 D) → False) →
    (∀ D : Circuit,
      FanInTwo D → D.size ≤ 14 →
      (∀ g ∈ D.gates, g.op = GateOp.not → g.inputs.length ≤ 1) →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0]) =
        (fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))) x) →
      let reads := fun g : Gate => g.inputs.contains 0 || g.inputs.contains 9
      (D.gates.filter reads).length = 2 →
      (¬ ∃ pre g post, D.gates = pre ++ g :: post ∧
        ((g.op = GateOp.and ∧ 0 ∈ g.inputs) ∨ (g.op = GateOp.or ∧ 9 ∈ g.inputs)) ∧
        ∃ h ∈ post, reads h = false ∧ 10 + pre.length ∈ h.inputs) →
      (∃ g ∈ D.gates, g.op = GateOp.not) → False) →
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => { op := x3.op, inputs := if x3.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x2.gates);   have x4 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5;   have x5 : ℕ := (List.filter x4 x3).length;   have x6 : Prop := ∃ (x6 : List PEqualNP.CircuitLowerBounds.Gate) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 : List PEqualNP.CircuitLowerBounds.Gate), x3 = x6 ++ x7 :: x8 ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x7.inputs ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x7.inputs) ∧ ∃ x9 ∈ x8, x4 x9 = Bool.false ∧ (10 : ℕ) + x6.length ∈ x9.inputs;   PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x8 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x8)).getD (9 : ℕ) Bool.false = !x8 (0 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → x5 = (2 : ℕ) → ¬x6 → False := by
  intro monotone negating
  dsimp only
  intro C hFan hFirst hFun hSize hCount hNoEscape
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let trim (g : Gate) : Gate :=
    ⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]; omega
  rcases C with ⟨gs, out⟩
  rcases gs with _ | ⟨first, tail⟩
  · simp at hCount
  let D : Circuit := ⟨tail.map trim, out⟩
  have hOps (g : Gate) (hg : g ∈ tail) :
      g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (hFan g (List.mem_cons_of_mem _ hg)).1
  have hTrim (g : Gate) (hg : g ∈ tail) (w : List Bool) :
      step w (trim g) = step w g := by
    rcases hOps g hg with ho | ho | ho
    · simp [step, trim, ho, GateOp.eval]
    · simp [step, trim, ho, GateOp.eval]
    · cases he : g.inputs <;> simp [step, trim, ho, he, GateOp.eval]
  have hFold (gs : List Gate) (hSubset : ∀ g ∈ gs, g ∈ tail) (w : List Bool) :
      (gs.map trim).foldl step w = gs.foldl step w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      rw [hTrim g (hSubset g (by simp)), ih]
      intro a ha
      exact hSubset a (List.mem_cons_of_mem _ ha)
  have hDFan : FanInTwo D := by
    intro g hg
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
    have h := hFan b (List.mem_cons_of_mem _ hb)
    refine ⟨h.1, ?_⟩
    change (if b.op.eval [false] = true then b.inputs.take 1 else b.inputs).length ≤ 2
    split <;> simp [List.length_take, h.2]
  have hUnary : ∀ g ∈ D.gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
    intro g hg hop
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hg
    change b.op = GateOp.not at hop
    simp [trim, hop, GateOp.eval, List.length_take]
  have hDSize : D.size ≤ 14 := by
    change (tail.map trim).length ≤ 14
    change (first :: tail).length ≤ 15 at hSize
    simp at hSize ⊢
    omega
  have hPrefix (x : Fin 9 → Bool) : step (List.ofFn x) first = List.ofFn x ++ [!x 0] := by
    have hv := hFirst x
    change (tail.foldl step (step (List.ofFn x) first)).getD 9 false = _ at hv
    rw [keep] at hv
    · have last (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
        simp [List.getD_eq_getElem?_getD]
      have hLast := last (List.ofFn x)
        (first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false))
      rw [List.length_ofFn] at hLast
      change (List.ofFn x ++ [_]).getD 9 false = _ at hv
      rw [hLast] at hv
      simp only [step, hv]
    · simp [step]
  have hDEval (x : Fin 9 → Bool) : D.eval (List.ofFn x ++ [!x 0]) = (fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ))) x := by
    have h := congrFun hFun x
    change (tail.foldl step (step (List.ofFn x) first)).getD out false = _ at h
    rw [hPrefix] at h
    change ((tail.map trim).foldl step (List.ofFn x ++ [!x 0])).getD out false = _
    rw [hFold tail (fun _ hg => hg)]
    exact h
  by_cases hNot : ∃ g ∈ D.gates, g.op = GateOp.not
  · exact negating D hDFan hDSize hUnary hDEval (by simpa [D, trim] using hCount)
      (by simpa [D, trim] using hNoEscape) hNot
  · have hMono : Monotone2 D := by
      intro g hg
      obtain ⟨ho, hl⟩ := hDFan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
      exact ⟨ho.elim Or.inl (fun h => Or.inr (h.resolve_right (fun hn => hNot ⟨g, hg, hn⟩))), hl⟩
    exact monotone D hDFan hDSize hUnary hDEval (by simpa [D, trim] using hCount)
      (by simpa [D, trim] using hNoEscape) hMono
