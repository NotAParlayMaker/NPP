import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9065_aux

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

theorem step (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
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
        · rw [h]; simp only [GateOp.eval]; exact any_mono _ _ _ hw
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

end PEqualNP.Outside.L_meta_9065_aux

open PEqualNP.Outside.L_meta_9065_aux in
theorem PEqualNP.Outside.L_meta_9065 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly x1 → Monotone fun (x3 : Fin (26 : ℕ) → Bool) => x1.eval (List.ofFn x3 ++ [x3 (1 : Fin (26 : ℕ)) || x3 (2 : Fin (26 : ℕ))]) := by
  intro C hC x y hxy
  have hm := step C.gates hC (List.ofFn x ++ [x 1 || x 2]) (List.ofFn y ++ [y 1 || y 2])
    (by simp) (by
      intro i
      simp only [List.getD_eq_getElem?_getD]
      by_cases hi : i < 26
      · rw [List.getElem?_append_left (by simpa using hi), List.getElem?_append_left (by simpa using hi)]
        simp only [List.getElem?_ofFn, hi]
        simpa using hxy ⟨i, hi⟩
      · rw [not_lt] at hi
        rw [List.getElem?_append_right (by simpa using hi), List.getElem?_append_right (by simpa using hi)]
        simp only [List.length_ofFn]
        rcases Nat.eq_zero_or_pos (i - 26) with h0 | h0
        · rw [h0]
          have h1 := hxy 1
          have h2 := hxy 2
          simp only [List.getElem?_cons_zero, Option.getD_some]
          revert h1 h2
          cases x 1 <;> cases x 2 <;> cases y 1 <;> cases y 2 <;> decide
        · obtain ⟨k, hk⟩ : ∃ k, i - 26 = k + 1 := ⟨i - 26 - 1, by omega⟩
          rw [hk]; simp) C.output
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
  exact hm
