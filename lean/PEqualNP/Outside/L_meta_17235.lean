import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17235_aux

open PEqualNP.CircuitLowerBounds

theorem all_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    (l.map f).all id ≤ (l.map g).all id := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a
    simp only [List.map_cons, List.all_cons, id] at ih ⊢
    revert ih ha
    cases f a <;> cases g a <;> cases (t.map f).all id <;> cases (t.map g).all id <;> decide

theorem any_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    (l.map f).any id ≤ (l.map g).any id := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha := h a
    simp only [List.map_cons, List.any_cons, id] at ih ⊢
    revert ih ha
    cases f a <;> cases g a <;> cases (t.map f).any id <;> cases (t.map g).any id <;> decide

theorem step (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w w' : List Bool) (hl : w.length = w'.length)
    (hw : ∀ i, w.getD i false ≤ w'.getD i false) :
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false ≤
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD i false := by
  induction gs generalizing w w' with
  | nil => simpa using hw
  | cons g t ih =>
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · have hop := hg g (List.mem_cons_self)
      have hb : g.op.eval (g.inputs.map fun i => w.getD i false) ≤
          g.op.eval (g.inputs.map fun i => w'.getD i false) := by
        rcases hop with h | h
        · rw [h]; simp only [GateOp.eval]; exact all_mono _ _ _ hw
        · rw [Set.mem_singleton_iff] at h
          rw [h]; simp only [GateOp.eval]; exact any_mono _ _ _ hw
      intro i
      by_cases hi : i < w.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi)]
        exact hw i
      · rw [not_lt] at hi
        rw [List.getD_append_right _ _ _ _ hi, List.getD_append_right _ _ _ _ (hl ▸ hi), hl]
        rcases Nat.eq_zero_or_pos (i - w'.length) with h0 | h0
        · rw [h0]; simpa using hb
        · obtain ⟨k, hk⟩ : ∃ k, i - w'.length = k + 1 := ⟨i - w'.length - 1, by omega⟩
          rw [hk]; simp

end PEqualNP.Outside.L_meta_17235_aux

open PEqualNP.Outside.L_meta_17235_aux in
theorem PEqualNP.Outside.L_meta_17235 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 x5 : Fin x1 → Bool), (∀ (x6 : Fin x1), x4 x6 = Bool.true → x5 x6 = Bool.true) → ∀ (x7 : ℕ), (x2.wires (List.ofFn x4)).getD x7 Bool.false = Bool.true → (x2.wires (List.ofFn x5)).getD x7 Bool.false = Bool.true := by
  intro n C hC x y hxy k hk
  have key := step C.gates (fun g hg => (hC g hg).1) (List.ofFn x) (List.ofFn y) (by simp) (by
    intro i
    by_cases hi : i < n
    · have := hxy ⟨i, hi⟩
      simp [List.getD_eq_getElem?_getD, hi]
      revert this; cases x ⟨i, hi⟩ <;> cases y ⟨i, hi⟩ <;> simp
    · simp [List.getD_eq_getElem?_getD, hi]) k
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires at hk ⊢
  rw [hk] at key
  revert key; cases (List.foldl _ (List.ofFn y) C.gates).getD k false <;> simp
