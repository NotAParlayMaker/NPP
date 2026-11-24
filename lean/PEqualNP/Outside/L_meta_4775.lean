import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4775

open PEqualNP.CircuitLowerBounds

def wst (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_app_lt (l l' : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_last (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
    intro hf i hi
    exact h i hi (hf i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    rintro ⟨i, hi, hf⟩
    exact ⟨i, hi, h i hi hf⟩

theorem mono_fold (gs : List Gate) (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (U V : List Bool), U.length = V.length →
    (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (gs.foldl wst U).getD i false = true → (gs.foldl wst V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h; simpa using h
  | cons g gs ih =>
    intro U V hl h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hop g' (List.mem_cons_of_mem g hg')) _ _ (by simp [wst, hl])
    intro i hi
    rcases lt_trichotomy i U.length with hlt | heq | hgt
    · rw [show wst U g = U ++ _ from rfl, getD_app_lt _ _ _ hlt] at hi
      rw [show wst V g = V ++ _ from rfl, getD_app_lt _ _ _ (by omega)]
      exact h i hi
    · subst heq
      rw [show wst U g = U ++ _ from rfl, getD_last] at hi
      rw [show wst V g = V ++ _ from rfl, hl, getD_last]
      exact eval_mono g.op (hop g (List.mem_cons_self ..)) g.inputs _ _ (fun i _ => h i) hi
    · rw [getD_ge _ _ (by simp [wst]; omega)] at hi
      cases hi

end PEqualNP.Outside.L_meta_4775

theorem PEqualNP.Outside.L_meta_4775 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 x4 : Fin (14 : ℕ) → Bool), (∀ (x5 : Fin (14 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → x1.eval (List.ofFn x3) = Bool.true → x1.eval (List.ofFn x4) = Bool.true := by
  intro C hC x y hxy hx
  have hop : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  apply PEqualNP.Outside.L_meta_4775.mono_fold C.gates hop (List.ofFn x) (List.ofFn y) (by simp)
    _ C.output hx
  intro i hi
  by_cases hlt : i < 14
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt] at hi ⊢
    simp only [dite_true, Option.getD_some] at hi ⊢
    exact hxy _ hi
  · rw [PEqualNP.Outside.L_meta_4775.getD_ge _ _ (by simp; omega)] at hi
    cases hi
