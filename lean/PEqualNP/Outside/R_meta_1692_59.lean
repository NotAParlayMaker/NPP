import PEqualNP.Defs

-- Deleting a point or line leaves 48 of the 52 incident pairs.
-- The 59-gate star construction for the smaller problem uses twelve centers.
-- The two hypotheses ask for its lower bound and a five-gate deletion.

theorem PEqualNP.Outside.R_meta_1692_59
    (punctured : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin 26),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ p l : Fin 13, p - l ∈ ([0, 1, 3, 9] : List (Fin 13)).toFinset →
        (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun w : Fin 13 => decide (w = l))).getD v false = false → C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun w : Fin 13 => decide (w = l))) = true) →
      (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun r => r - k ∈ ([0, 1, 3, 9] : List (Fin 13)).toFinset)).card ≤ 2) → C.eval (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++ List.ofFn (fun l : Fin 13 => decide (∀ r ∈ Q, r - l ∉ ([0, 1, 3, 9] : List (Fin 13)).toFinset))) = false) → 59 ≤ C.size)
    (deletion : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < 26 + (i : ℕ)) →
      (∀ p l : Fin 13, p - l ∈ ([0, 1, 3, 9] : List (Fin 13)).toFinset → C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun w : Fin 13 => decide (w = l))) = true) →
      (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun r => r - k ∈ ([0, 1, 3, 9] : List (Fin 13)).toFinset)).card ≤ 2) → C.eval (List.ofFn (fun p : Fin 13 => decide (p ∈ Q)) ++ List.ofFn (fun l : Fin 13 => decide (∀ r ∈ Q, r - l ∉ ([0, 1, 3, 9] : List (Fin 13)).toFinset))) = false) →
      ∃ (v : Fin 26) (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + 5 ≤ C.size ∧
        (∀ x : List Bool, x.length = 26 → D.eval x = true → C.eval x = true) ∧
        (∀ p l : Fin 13, p - l ∈ ([0, 1, 3, 9] : List (Fin 13)).toFinset →
          let x := List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun w : Fin 13 => decide (w = l))
          x.getD v false = false → D.eval x = true)) :
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 26 + (i : ℕ)) → (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u1 : Fin 13 => decide (u1 = p)) ++ List.ofFn (fun v1 : Fin 13 => decide (v1 = l))) = true) → (∀ Q : Finset (Fin 13), Q.card = 4 → (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q)) ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) → 64 ≤ gates.length := by
  intro gates out ops wf pos neg
  have offsets : ([0, 1, 3, 9] : List (Fin 13)).toFinset = ({0, 1, 3, 9} : Finset (Fin 13)) := by decide
  simp only [offsets] at punctured deletion
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,out⟩
  have mono : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    obtain ⟨hg,arity⟩ := ops g hg
    exact ⟨hg,arity⟩
  obtain ⟨v,D,hD,saved,below,face⟩ := deletion C mono wf pos neg
  have lower := punctured D v hD face (by
      intro Q four arc
      cases h : D.eval _ with
      | false => rfl
      | true =>
        have a := below _ (by simp) h
        have b := neg Q four arc
        change C.eval _ = false at b
        rw [b] at a
        contradiction)
  change D.size + 5 ≤ gates.length at saved
  omega
