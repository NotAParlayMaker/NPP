import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1334

open PEqualNP.CircuitLowerBounds

-- one gate appended to the list of wire values
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

-- two wire lists that agree off wire m stay so under gates that never read m
theorem agree (m : ℕ) (gs : List Gate) : ∀ W1 W2 : List Bool, W1.length = W2.length →
    (∀ i, i ≠ m → W1.getD i false = W2.getD i false) → (∀ g ∈ gs, m ∉ g.inputs) →
    (gs.foldl stp W1).length = (gs.foldl stp W2).length ∧
    ∀ i, i ≠ m → (gs.foldl stp W1).getD i false = (gs.foldl stp W2).getD i false := by
  induction gs with
  | nil => intro W1 W2 hl h _; exact ⟨hl, h⟩
  | cons g gs ih =>
    intro W1 W2 hl h hno
    have hv : g.op.eval (g.inputs.map fun i => W1.getD i false)
        = g.op.eval (g.inputs.map fun i => W2.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (fun e => hno g (by simp) (e ▸ hi))
    apply ih (stp W1 g) (stp W2 g)
    · simp [stp, hl]
    · intro i hi
      rw [stp, stp, getD_snoc, getD_snoc, hv, hl]
      split_ifs
      · rfl
      · exact h i hi
    · intro g2 hg2
      exact hno g2 (List.mem_cons_of_mem _ hg2)

-- replacing gate q, which no gate reads, changes no wire but its own
theorem setq (g' : Gate) (gs : List Gate) : ∀ (q : ℕ) (W : List Bool),
    (∀ g ∈ gs, W.length + q ∉ g.inputs) →
    ∀ i, i ≠ W.length + q → ((gs.set q g').foldl stp W).getD i false = (gs.foldl stp W).getD i false := by
  induction gs with
  | nil => intro q W _ i _; simp
  | cons g gs ih =>
    intro q W hno i hi
    cases q with
    | zero =>
      simp only [List.set_cons_zero, List.foldl_cons]
      refine (agree (W.length + 0) gs (stp W g') (stp W g) (by simp [stp]) ?_ ?_).2 i hi
      · intro j hj
        rw [stp, stp, getD_snoc, getD_snoc]
        split_ifs with h1
        · exact absurd h1 (by omega)
        · rfl
      · intro g2 hg2
        exact hno g2 (List.mem_cons_of_mem _ hg2)
    | succ q =>
      simp only [List.set_cons_succ, List.foldl_cons]
      have hlen : (stp W g).length + q = W.length + (q + 1) := by
        simp [stp]; omega
      apply ih q (stp W g)
      · intro g2 hg2
        rw [hlen]
        exact hno g2 (List.mem_cons_of_mem _ hg2)
      · rw [hlen]; exact hi

end PEqualNP.Outside.L_meta_1334

open PEqualNP.Outside.L_meta_1334 in
theorem PEqualNP.Outside.L_meta_1334 : ∀ (n q w : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (g' : PEqualNP.CircuitLowerBounds.Gate), (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), gates[k]? = some g → n + q ∉ g.inputs) → w ≠ n + q → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates.set q g', w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x) := by
  intro n q w gates g' hno hw x
  show ((gates.set q g').foldl stp (List.ofFn x)).getD w false = (gates.foldl stp (List.ofFn x)).getD w false
  have hno' : ∀ g ∈ gates, (List.ofFn x).length + q ∉ g.inputs := by
    intro g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hg
    rw [List.length_ofFn]
    exact hno k g hk
  exact setq g' gates q (List.ofFn x) hno' w (by rw [List.length_ofFn]; exact hw)
