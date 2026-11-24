import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_2677 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size = x1.size ∧ (PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.Monotone2 x2) ∧ (PEqualNP.MetaComplexity.FanInTwo x1 → PEqualNP.MetaComplexity.FanInTwo x2) ∧ x2.output ≤ (24 : ℕ) ∧ (∀ x3 ∈ x2.gates, ∀ x5 ∈ x3.inputs, x5 ≤ (24 : ℕ)) ∧ ∀ (x3 : List Bool), x3.length + x1.size ≤ (24 : ℕ) → x2.wires x3 = x1.wires x3 ∧ x2.eval x3 = x1.eval x3 ∧ (x1.wires x3).length = x3.length + x1.size := by
  classical
  intro x1
  let f : ℕ → ℕ := fun i => if i ≤ 24 then i else 24
  let x2 : Circuit := { gates := x1.gates.map fun g => ⟨g.op, g.inputs.map f⟩, output := min x1.output 24 }
  have key : ∀ (gs : List Gate) (w : List Bool), w.length + gs.length ≤ 24 →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
      gs.foldl (fun w g => w ++ [g.op.eval ((g.inputs.map f).map fun i => w.getD i false)]) w := by
    intro gs w
    induction gs generalizing w with
    | nil => intro; rfl
    | cons g gs ih =>
        intro h
        simp only [List.length_cons] at h
        have hv : g.op.eval (g.inputs.map fun i => w.getD i false)
            = g.op.eval ((g.inputs.map f).map fun i => w.getD i false) := by
          rw [List.map_map]
          congr 1
          apply List.map_congr_left
          intro i _
          by_cases hi24 : i ≤ 24
          · simp only [Function.comp_apply, f, hi24, ite_true]
          · simp only [Function.comp_apply, f, hi24, ite_false]
            rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        simp only [List.foldl_cons, hv]
        apply ih
        have e : (g :: gs).length = gs.length + 1 := rfl
        have : (w ++ [g.op.eval ((g.inputs.map f).map fun i => w.getD i false)]).length = w.length + 1 := by simp
        omega
  have hlen : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
        = w.length + gs.length := by
    intro gs w
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
        rw [List.foldl_cons, ih]
        have e : (g :: gs).length = gs.length + 1 := rfl
        have : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1 := by simp
        omega
  have hsize : x2.size = x1.size := by simp [x2, Circuit.size]
  have hmono : Monotone2 x1 → Monotone2 x2 := by
    intro hm g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨hm g' hg' |>.1, by simpa using (hm g' hg').2⟩
  have hfan : FanInTwo x1 → FanInTwo x2 := by
    intro hm g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact ⟨hm g' hg' |>.1, by simpa using (hm g' hg').2⟩
  have hout : x2.output ≤ 24 := by simp [x2]
  have hins : ∀ g ∈ x2.gates, ∀ i ∈ g.inputs, i ≤ 24 := by
    intro g hg i hi
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    by_cases h24 : i' ≤ 24 <;> simp [f, h24]
  refine ⟨x2, hsize, hmono, hfan, hout, hins, ?_⟩
  intro x3 hx3
  have hsz : x1.size = x1.gates.length := rfl
  rw [hsz] at hx3
  have hw : x2.wires x3 = x1.wires x3 := by
    simp only [Circuit.wires]
    rw [show x2.gates = x1.gates.map (fun g => ⟨g.op, g.inputs.map f⟩) from rfl]
    rw [List.foldl_map]
    exact (key x1.gates x3 hx3).symm
  have hwl : (x1.wires x3).length = x3.length + x1.gates.length := hlen x1.gates x3
  refine ⟨hw, ?_, ?_⟩
  · show (x2.wires x3).getD (min x1.output 24) false = (x1.wires x3).getD x1.output false
    rw [hw]
    by_cases ho : x1.output ≤ 24
    · rw [min_eq_left ho]
    · rw [min_eq_right (by omega)]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  · show (x1.wires x3).length = x3.length + x1.size
    rw [hsz]; exact hwl
