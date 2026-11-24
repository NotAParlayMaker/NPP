import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4700_aux

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem drun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

theorem drun_length (gs : List Gate) (x : List Bool) :
    (drun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [drun]
  | cons g gs ih => rw [drun_cons, ih]; simp; omega

def cg (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map (fun i => min i 23) }

theorem drun_clamp (gs : List Gate) : ∀ (x : List Bool), x.length + gs.length ≤ 23 →
    drun (gs.map cg) x = drun gs x := by
  induction gs with
  | nil => intro x _; rfl
  | cons g gs ih =>
    intro x hx
    simp only [List.length_cons] at hx
    rw [List.map_cons, drun_cons, drun_cons]
    have hval : (cg g).op.eval ((cg g).inputs.map fun i => x.getD i false) =
        g.op.eval (g.inputs.map fun i => x.getD i false) := by
      simp only [cg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp]
      by_cases hi : i ≤ 23
      · rw [Nat.min_eq_left hi]
      · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by omega)]
    rw [hval]
    exact ih _ (by simp only [List.length_append, List.length_singleton]; omega)

theorem main (C : Circuit) (hs : C.size ≤ 13) (hf : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ D.output ≤ 23 ∧
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ 23) ∧
      ∀ x : List Bool, x.length = 10 → D.eval x = C.eval x := by
  refine ⟨{ gates := C.gates.map cg, output := min C.output 23 }, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hf g0 hg0
    exact ⟨h1, by simpa [cg] using h2⟩
  · simp [Circuit.size]
  · exact Nat.min_le_right _ _
  · intro g hg i hi
    simp only [List.mem_map] at hg
    obtain ⟨g0, _, rfl⟩ := hg
    simp only [cg, List.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    exact Nat.min_le_right _ _
  · intro x hx
    have hsz : C.gates.length ≤ 13 := hs
    show (drun (C.gates.map cg) x).getD (min C.output 23) false = (drun C.gates x).getD C.output false
    rw [drun_clamp C.gates x (by omega)]
    by_cases ho : C.output ≤ 23
    · rw [Nat.min_eq_left ho]
    · rw [Nat.min_eq_right (by omega), List.getD_eq_default _ _ (by rw [drun_length]; omega),
        List.getD_eq_default _ _ (by rw [drun_length]; omega)]

end PEqualNP.Outside.L_meta_4700_aux

theorem PEqualNP.Outside.L_meta_4700 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (13 : ℕ) → PEqualNP.MetaComplexity.FanInTwo x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size = x1.size ∧ x4.output ≤ (23 : ℕ) ∧ (∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → x4.eval x5 = x1.eval x5 := by
  intro C hs hf
  exact PEqualNP.Outside.L_meta_4700_aux.main C hs hf
