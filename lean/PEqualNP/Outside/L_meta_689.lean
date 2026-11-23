import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_689_aux

open PEqualNP.CircuitLowerBounds

theorem getD_snoc (a : List Bool) (v : Bool) (i : ℕ) :
    (a ++ [v]).getD i false = if i < a.length then a.getD i false else if i = a.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : i - a.length ≠ 0 := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
    rw [hk]; simp

theorem step (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → (∀ i, a.getD i false = true → b.getD i false = true) →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).length =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).length ∧
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).getD i false = true := by
  induction gs with
  | nil => intro a b hl h; exact ⟨hl, h⟩
  | cons g gs ih =>
    intro a b hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · have hv : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
          g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
        rcases hg g List.mem_cons_self with ho | ho
        · rw [ho]; simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
          intro H x hx
          obtain ⟨j, hj, rfl⟩ := hx
          exact h j (H _ ⟨j, hj, rfl⟩)
        · rw [ho]; simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
          rintro ⟨x, ⟨j, hj, rfl⟩, hx⟩
          exact ⟨_, ⟨j, hj, rfl⟩, h j hx⟩
      intro i
      rw [getD_snoc, getD_snoc, hl]
      split_ifs with h1 h2
      · rw [← hl] at h1; exact h i
      · exact hv
      · exact id

end PEqualNP.Outside.L_meta_689_aux

open PEqualNP.Outside.L_meta_689_aux in
theorem PEqualNP.Outside.L_meta_689 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : Fin n → Bool) (w : ℕ), (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ q : Fin n, x q = true → y q = true) → (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro n C x y w hg hxy hw
  refine (step C.gates hg (List.ofFn x) (List.ofFn y) (by simp) ?_).2 w hw
  intro i hi
  by_cases h : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi ⊢
    simp [h] at hi ⊢
    exact hxy ⟨i, h⟩ hi
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hi
    simp [h] at hi
