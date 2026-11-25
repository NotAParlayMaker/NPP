import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8827_aux

open PEqualNP.CircuitLowerBounds

def fmap (n : ℕ) (p : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then (p ⟨i, h⟩).val else i

theorem fmap_lt (n : ℕ) (p : Equiv.Perm (Fin n)) (i m : ℕ) (hn : n ≤ m) (hi : i < m) :
    fmap n p i < m := by
  unfold fmap
  split_ifs with h
  · have := (p ⟨i, h⟩).isLt
    omega
  · exact hi

theorem fmap_ge (n : ℕ) (p : Equiv.Perm (Fin n)) (i : ℕ) (hi : n ≤ i) : fmap n p i = i := by
  unfold fmap
  rw [dif_neg (by omega)]

def rg (n : ℕ) (p : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (fmap n p)⟩

theorem getD_app (w : List Bool) (a : Bool) (j : ℕ) (h : j < w.length) :
    (w ++ [a]).getD j false = w.getD j false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem key (n : ℕ) (p : Equiv.Perm (Fin n)) (gs : List Gate) :
    ∀ w w' : List Bool, w.length = w'.length → n ≤ w.length →
      (∀ j, w.getD (fmap n p j) false = w'.getD j false) →
      ∀ j, ((gs.map (rg n p)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
          (fmap n p j) false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD
          j false := by
  induction gs with
  | nil => intro w w' _ _ h j; exact h j
  | cons g gs ih =>
    intro w w' hl hn h
    simp only [List.map_cons, List.foldl_cons]
    have he : (rg n p g).op.eval ((rg n p g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    rw [he]
    apply ih
    · simp [hl]
    · simp; omega
    · intro j
      by_cases hj : j < w.length
      · rw [getD_app _ _ _ (fmap_lt n p j _ hn hj), getD_app _ _ _ (by omega)]
        exact h j
      · rw [fmap_ge n p j (by omega)]
        simp only [List.getD_eq_getElem?_getD]
        by_cases hj2 : j = w.length
        · subst hj2
          simp [hl]
        · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

end PEqualNP.Outside.L_meta_8827_aux

open PEqualNP.Outside.L_meta_8827_aux in
theorem PEqualNP.Outside.L_meta_8827 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 : Equiv.Perm (Fin x1)), ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x2.size ∧ ∀ (x6 : ℕ) (x7 : Fin x1 → Bool), x1 ≤ x6 → (x5.wires (List.ofFn x7)).getD x6 Bool.false = (x2.wires (List.ofFn (x7 ∘ ⇑x4))).getD x6 Bool.false := by
  intro x1 x2 hm x4
  refine ⟨⟨x2.gates.map (rg x1 x4), x2.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hm g0 hg0
    exact ⟨h1, by simpa [rg] using h2⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x6 x7 h6
    have := key x1 x4 x2.gates (List.ofFn x7) (List.ofFn (x7 ∘ ⇑x4)) (by simp) (by simp)
      (by
        intro j
        by_cases hj : j < x1
        · simp [fmap, hj, List.getD_eq_getElem?_getD]
        · rw [fmap_ge x1 x4 j (by omega)]
          simp [List.getD_eq_getElem?_getD, hj, List.getElem?_eq_none, Nat.le_of_not_lt hj]) x6
    rw [fmap_ge x1 x4 x6 h6] at this
    exact this
