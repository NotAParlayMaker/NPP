import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3081_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def reads (g : Gate) (i : ℕ) : Prop :=
  (g.op = .not ∧ g.inputs.head? = some i) ∨ (g.op ≠ .not ∧ i ∈ g.inputs)

private def value (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def step (w : List Bool) (g : Gate) : List Bool := w ++ [value w g]

private lemma get_initial (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

private lemma value_eq (g : Gate) (v : ℕ) (w u : List Bool)
    (h : ∀ i, i ≠ v → w.getD i false = u.getD i false) (avoid : ¬ reads g v) :
    value w g = value u g := by
  by_cases hnot : g.op = .not
  · cases hins : g.inputs with
    | nil => simp [value, hnot, hins]
    | cons a rest =>
      have ha : a ≠ v := by
        intro eq
        apply avoid
        exact Or.inl ⟨hnot, by simp [hins, eq]⟩
      simpa [value, hnot, hins, GateOp.eval] using congrArg Bool.not (h a ha)
  · unfold value
    congr 1
    apply List.map_congr_left
    intro i hi
    apply h
    intro eq
    subst i
    exact avoid (Or.inr ⟨hnot, hi⟩)

private lemma append_eq (w u : List Bool) (a : Bool) (v : ℕ)
    (hlen : w.length = u.length)
    (h : ∀ i, i ≠ v → w.getD i false = u.getD i false) :
    ∀ i, i ≠ v → (w ++ [a]).getD i false = (u ++ [a]).getD i false := by
  intro i hi
  by_cases small : i < w.length
  · rw [List.getD_append _ _ _ _ small, List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]

private lemma propagate (gs : List Gate) (v : ℕ) (hgs : ∀ g ∈ gs, ¬ reads g v)
    (w u : List Bool) (hlen : w.length = u.length)
    (h : ∀ i, i ≠ v → w.getD i false = u.getD i false) :
    ∀ i, i ≠ v → (gs.foldl step w).getD i false = (gs.foldl step u).getD i false := by
  induction gs generalizing w u with
  | nil => exact h
  | cons g gs ih =>
    have hv := value_eq g v w u h (hgs g (by simp))
    simp only [List.foldl_cons, step, hv]
    exact ih (fun a ha => hgs a (by simp [ha])) _ _ (by simp [hlen]) (append_eq w u _ v hlen h)

private lemma forced (C : Circuit) (v : ℕ) (w u z : List Bool)
    (hw : w.length = 9) (hu : u.length = 9) (hz : z.length = 9)
    (hv : v < 9) (hs : z.getD v false = true) (hzero : C.eval z = false)
    (hfirst : (C.wires w).getD 9 false = (C.wires u).getD 9 false)
    (hclose : ∀ i, i ≠ v → w.getD i false = u.getD i false)
    (hdiff : C.eval w ≠ C.eval u) : ∃ g ∈ C.gates.drop 1, reads g v := by
  have hout : C.output ≠ v := by
    intro eq
    unfold Circuit.eval Circuit.wires at hzero
    change (C.gates.foldl step z).getD C.output false = false at hzero
    rw [eq, get_initial _ _ _ (by omega), hs] at hzero
    contradiction
  by_contra hn
  have hgs : ∀ g ∈ C.gates.drop 1, ¬ reads g v := fun g hg h => hn ⟨g, hg, h⟩
  apply hdiff
  unfold Circuit.eval Circuit.wires at *
  cases hc : C.gates with
  | nil => simpa [hc] using hclose C.output hout
  | cons g gs =>
    have hval (a : List Bool) (ha : a.length = 9) :
        (gs.foldl step (step a g)).getD 9 false = value a g := by
      rw [get_initial _ _ _ (by simp [step, ha])]
      simp [step, ha]
    change (C.gates.foldl step w).getD 9 false = (C.gates.foldl step u).getD 9 false at hfirst
    rw [hc, List.foldl_cons, List.foldl_cons, hval w hw, hval u hu] at hfirst
    change (gs.foldl step (step w g)).getD C.output false =
      (gs.foldl step (step u g)).getD C.output false
    apply propagate gs v (by simpa [hc] using hgs) _ _ (by simp [step, hw, hu]) _ _ hout
    simpa [step, hfirst] using append_eq w u (value u g) v (hw.trans hu.symm) hclose

end PEqualNP.Outside.L_meta_3081_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3081_aux

theorem PEqualNP.Outside.L_meta_3081 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : ℕ), x5 = (0 : ℕ) ∨ x5 = (2 : ℕ) → ∃ x7 ∈ List.drop (1 : ℕ) x2.gates, x1 x7 x5 := by
  dsimp only
  intro C hfirst heval v hv
  let z : Fin 9 → Bool := fun i => decide (i.val = v)
  have hz : C.eval (List.ofFn z) = false := by
    change circuitFun 9 C z = false
    rcases hv with h | h <;> subst v <;> rw [heval] <;> decide
  let check (a b : ℕ) (v : ℕ) : Fin 9 → Bool :=
    fun i => decide (i.val = a ∨ i.val = b ∨ i.val = v)
  rcases hv with rfl | rfl
  · let x : Fin 9 → Bool := check 2 5 2
    let y : Fin 9 → Bool := check 2 5 0
    refine forced C 0 (List.ofFn x) (List.ofFn y) (List.ofFn z)
      List.length_ofFn List.length_ofFn List.length_ofFn (by decide) (by decide) hz
      ((hfirst x).trans (hfirst y).symm) ?_ ?_
    · intro i hi
      by_cases hs : i < 9
      · interval_cases i <;> first | contradiction | decide
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hs),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hs)]
    · change circuitFun 9 C x ≠ circuitFun 9 C y
      rw [heval]
      decide
  · let x : Fin 9 → Bool := check 0 7 0
    let y : Fin 9 → Bool := check 0 7 2
    refine forced C 2 (List.ofFn x) (List.ofFn y) (List.ofFn z)
      List.length_ofFn List.length_ofFn List.length_ofFn (by decide) (by decide) hz
      ((hfirst x).trans (hfirst y).symm) ?_ ?_
    · intro i hi
      by_cases hs : i < 9
      · interval_cases i <;> first | contradiction | decide
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hs),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hs)]
    · change circuitFun 9 C x ≠ circuitFun 9 C y
      rw [heval]
      decide
