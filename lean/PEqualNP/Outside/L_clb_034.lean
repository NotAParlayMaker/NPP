import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_clb_034_aux

/-- A circuit with at most one gate, whose gates read at most one wire, has an output that depends
on at most one position of the input. -/
theorem one_position (C : Circuit) (N : ℕ) (hsize : C.size ≤ 1)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 1) :
    ∃ i : ℕ, ∀ x y : List Bool, x.length = N → y.length = N →
      x.getD i false = y.getD i false → C.eval x = C.eval y := by
  obtain ⟨gates, o⟩ := C
  simp only [Circuit.size] at hsize
  match gates, hsize, hg with
  | [], _, _ =>
    refine ⟨o, fun x y _ _ h => ?_⟩
    simpa [Circuit.eval, Circuit.wires] using h
  | [g], _, hg =>
    have hgl : g.inputs.length ≤ 1 := hg g (by simp)
    have hv : ∀ x y : List Bool, x.getD (g.inputs.headD 0) false = y.getD (g.inputs.headD 0) false →
        g.op.eval (g.inputs.map fun i => x.getD i false) =
          g.op.eval (g.inputs.map fun i => y.getD i false) := by
      intro x y h
      rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · rfl
      · rw [hgi] at h
        simp only [List.headD_cons] at h
        simp only [List.map_cons, List.map_nil]
        rw [h]
      · rw [hgi] at hgl
        simp at hgl
    by_cases ho : o < N
    · refine ⟨o, fun x y hx hy h => ?_⟩
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil]
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega), h]
    · refine ⟨g.inputs.headD 0, fun x y hx hy h => ?_⟩
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil]
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
        hx, hy, hv x y h]
  | _ :: _ :: _, h, _ =>
    simp at h

end PEqualNP.Outside.L_clb_034_aux

open PEqualNP.Outside.L_clb_034_aux in
theorem PEqualNP.Outside.L_clb_034 : ∀ (n d : ℕ), 2 ≤ n → ({x : List Bool | x.all id = true} : Language Bool) ∉ PEqualNP.CircuitLowerBounds.SizeDepth {PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} (fun m : ℕ => if m = n then 1 else m + 2) d := by
  intro n d hn hL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨C, hg, hsize, -, hdec⟩ := hL (m + 2)
  have hsize' : C.size ≤ 1 := by simpa using hsize
  have hg' : ∀ g ∈ C.gates, g.inputs.length ≤ 1 := fun g hgm => by simpa using (hg g hgm).2
  obtain ⟨i, hi⟩ := one_position C (m + 2) hsize' hg'
  have hone : C.eval (true :: true :: List.replicate m true) = true :=
    (hdec _ (by simp)).2 (show (true :: true :: List.replicate m true).all id = true by simp)
  have hzero : ∀ x : List Bool, x.length = m + 2 → x.all id = false → C.eval x = false := by
    intro x hx hall
    cases h : C.eval x
    · rfl
    · have this : x.all id = true := (hdec x hx).1 h
      rw [hall] at this
      exact absurd this (by decide)
  by_cases hi0 : i = 0
  · subst hi0
    have h2 := hzero (true :: false :: List.replicate m true) (by simp) (by simp)
    have := hi (true :: true :: List.replicate m true) (true :: false :: List.replicate m true)
      (by simp) (by simp) rfl
    rw [hone, h2] at this
    exact absurd this (by decide)
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have h2 := hzero (false :: true :: List.replicate m true) (by simp) (by simp)
    have := hi (true :: true :: List.replicate m true) (false :: true :: List.replicate m true)
      (by simp) (by simp) (by simp)
    rw [hone, h2] at this
    exact absurd this (by decide)
