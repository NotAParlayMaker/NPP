import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17376_aux

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


theorem cmono (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    Monotone (PEqualNP.MetaComplexity.circuitFun n C) := by
  intro x y hxy
  unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
    PEqualNP.CircuitLowerBounds.Circuit.wires
  apply step C.gates (fun g hg => (hC g hg).1)
  · simp
  · intro i
    by_cases hi : i < n
    · simp [List.getD_eq_getElem?_getD, hi]
      exact hxy ⟨i, hi⟩
    · simp [List.getD_eq_getElem?_getD, hi]

theorem main (n : ℕ) (f : (Fin n → Bool) → Bool) (g : (Fin n → Bool) → Bool)
    (hg : Monotone g) (hf : Monotone f)
    (hcrit : ∀ x : Fin n → Bool, (∀ i, x i = f x → f (Function.update x i !x i) ≠ f x) → g x = f x) :
    ∀ m : ℕ, ∀ x : Fin n → Bool, (Finset.univ.filter (fun i => x i = f x)).card ≤ m → g x = f x := by
  intro m
  induction m with
  | zero =>
    intro x hx
    apply hcrit
    intro i hi
    have : i ∈ Finset.univ.filter (fun i => x i = f x) := by simp [hi]
    have := Finset.card_pos.mpr ⟨i, this⟩
    omega
  | succ m ih =>
    intro x hx
    by_cases hc : ∀ i, x i = f x → f (Function.update x i !x i) ≠ f x
    · exact hcrit x hc
    push Not at hc
    obtain ⟨i, hi, hfy⟩ := hc
    set y := Function.update x i !x i with hy
    have hyi : y i = !x i := by simp [hy]
    have hyj : ∀ j, j ≠ i → y j = x j := by intro j hj; simp [hy, hj]
    clear_value y
    have hsub : Finset.univ.filter (fun j => y j = f y) ⊂ Finset.univ.filter (fun j => x j = f x) := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨i, by simp [hi], ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfy, hyi, hi]
        cases f x <;> decide
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        by_cases hji : j = i
        · subst hji; rw [hyi, hfy, hi] at hj; revert hj; cases f x <;> simp
        · rw [hfy, hyj j hji] at hj; exact hj
    have hlt := Finset.card_lt_card hsub
    have hgy : g y = f x := by rw [← hfy]; exact ih y (by omega)
    cases hfx : f x with
    | true =>
      have hle : y ≤ x := by
        intro j
        by_cases hji : j = i
        · subst hji; rw [hyi, hi, hfx]; simp
        · rw [hyj j hji]
      have := hg hle
      rw [hgy, hfx] at this
      revert this; cases g x <;> simp
    | false =>
      have hle : x ≤ y := by
        intro j
        by_cases hji : j = i
        · subst hji; rw [hyi, hi, hfx]; simp
        · rw [hyj j hji]
      have := hg hle
      rw [hgy, hfx] at this
      revert this; cases g x <;> simp

end PEqualNP.Outside.L_meta_17376_aux

open PEqualNP.Outside.L_meta_17376_aux in
theorem PEqualNP.Outside.L_meta_17376 : ∀ (x1 : ℕ) (x2 : (Fin x1 → Bool) → Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit), Monotone x2 → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x6 x7 = x2 x6 → x2 (Function.update x6 x7 !x6 x7) ≠ x2 x6) → PEqualNP.MetaComplexity.circuitFun x1 x3 x6 = x2 x6) → ∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x3 x7 = x2 x7 := by
  intro n f C hf hC hcrit x
  exact main n f _ (cmono n C hC) hf hcrit _ x le_rfl
