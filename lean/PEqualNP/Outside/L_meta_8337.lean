import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_8337

theorem all_mono (f1 f2 : ℕ → Bool) (hf : ∀ i, f1 i = true → f2 i = true) (l : List ℕ) :
    (l.map f1).all id = true → (l.map f2).all id = true := by
  simp only [List.all_eq_true, List.mem_map, id_eq]
  intro h x hx
  obtain ⟨a, ha, hx⟩ := hx
  rw [← hx]
  exact hf a (h (f1 a) ⟨a, ha, rfl⟩)

theorem any_mono (f1 f2 : ℕ → Bool) (hf : ∀ i, f1 i = true → f2 i = true) (l : List ℕ) :
    (l.map f1).any id = true → (l.map f2).any id = true := by
  simp only [List.any_eq_true, List.mem_map, id_eq]
  intro h
  obtain ⟨x, ⟨a, ha, hax⟩, hx⟩ := h
  rw [← hax] at hx
  exact ⟨f2 a, ⟨a, ha, rfl⟩, hf a hx⟩

theorem getD_snoc (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false
      = if i < w.length then w.getD i false else if i = w.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_append_right (by omega)]
    have h3 : i - w.length ≠ 0 := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h3
    rw [hk]
    simp

theorem fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
    (∀ i, w1.getD i false = true → w2.getD i false = true) →
    ∀ i, (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1 gs).getD i false = true →
      (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2 gs).getD i false = true := by
  induction gs with
  | nil =>
    intro w1 w2 hl hw
    exact hw
  | cons g gs ih =>
    intro w1 w2 hl hw
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · intro i
      rw [getD_snoc, getD_snoc, ← hl]
      split_ifs with h1 h2
      · exact hw i
      · rcases hg g (by simp) with h | h
        · rw [h]
          exact all_mono _ _ hw _
        · rw [h]
          exact any_mono _ _ hw _
      · exact id

theorem main (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x3 x4 : Fin 14 → Bool) (h34 : ∀ (x5 : Fin 14), x3 x5 = true → x4 x5 = true) (x6 : ℕ) :
    (C.wires (List.ofFn x3)).getD x6 false = true → (C.wires (List.ofFn x4)).getD x6 false = true := by
  have hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hgm
    have h := (hm g hgm).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  refine fold_mono C.gates hg (List.ofFn x3) (List.ofFn x4) ?_ ?_ x6
  · rw [List.length_ofFn, List.length_ofFn]
  · intro i
    by_cases hi : i < 14
    · have e : ∀ (x : Fin 14 → Bool), (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
        intro x
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hi), Option.getD_some,
          List.getElem_ofFn]
      rw [e, e]
      exact h34 _
    · have e : ∀ (x : Fin 14 → Bool), (List.ofFn x).getD i false = false := by
        intro x
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by rw [List.length_ofFn]; omega)]
        rfl
      rw [e, e]
      exact id

end PEqualNP.Outside.L_meta_8337

theorem PEqualNP.Outside.L_meta_8337 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : Fin (14 : ℕ) → Bool), (∀ (x5 : Fin (14 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → ∀ (x6 : ℕ), (x1.wires (List.ofFn x3)).getD x6 Bool.false = Bool.true → (x1.wires (List.ofFn x4)).getD x6 Bool.false = Bool.true :=
  fun x1 hm x3 x4 h34 x6 => PEqualNP.Outside.L_meta_8337.main x1 hm x3 x4 h34 x6
