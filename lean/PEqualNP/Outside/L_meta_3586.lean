import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3586 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) →       Option.map PEqualNP.CircuitLowerBounds.Gate.op x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or →         ∃ (x5 : Fin (11 : ℕ)) (x6 : Fin (11 : ℕ)) (x7 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x7 ∧             x7.size + (2 : ℕ) = x1.size ∧               ∀ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];                 x7.eval (x9 ++ [x9.getD (↑x5) Bool.false || x9.getD (↑x6) Bool.false]) = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 := by
  intro C fan front second
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  -- Appending gates preserves every wire that has already been written.
  have keep (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp [step]; omega
  let pin (i : ℕ) : Fin 11 := if hi : i < 10 then ⟨i,by omega⟩ else 10
  have atPin (w : List Bool) (hlen : w.length = 10) (i) :
      w.getD (pin i).val false = w.getD i false := by
    by_cases hi : i < 10
    · simp [pin,hi]
    · have h1 : w.length ≤ i := by omega
      simp only [pin,dif_neg hi]
      change w.getD 10 false = w.getD i false
      rw [List.getD_eq_default _ _ hlen.le,List.getD_eq_default _ _ h1]
  have normalize (args : List ℕ) (len : args.length ≤ 2) :
      ∃ a b : Fin 11, ∀ w : List Bool, w.length=10 →
        PEqualNP.CircuitLowerBounds.GateOp.or.eval (args.map fun i => w.getD i false) =
          (w.getD a.val false || w.getD b.val false) := by
    cases args with
    | nil =>
      refine ⟨10,10,fun w h => ?_⟩
      change false = (w.getD 10 false || w.getD 10 false)
      rw [List.getD_eq_default _ _ h.le]; rfl
    | cons i tail =>
      cases tail with
      | nil =>
        refine ⟨pin i,10,fun w h => ?_⟩
        change (w.getD i false || false) = (w.getD (pin i).val false || w.getD 10 false)
        rw [atPin w h,List.getD_eq_default _ _ h.le]
      | cons j tail =>
        cases tail with
        | nil =>
          refine ⟨pin i,pin j,fun w h => ?_⟩
          change (w.getD i false || (w.getD j false || false)) = _
          simp only [atPin w h,Bool.or_false]
        | cons k more =>
          simp at len
  rcases C with ⟨gates,o⟩
  cases gates with
  | nil => cases second
  | cons g tail =>
    cases tail with
    | nil => cases second
    | cons h gs =>
      let row (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
      have firstValue (x : Fin 9 → Bool) : step (List.ofFn x) g = row x := by
        have e := front x
        change ((h::gs).foldl step (step (List.ofFn x) g)).getD 9 false = _ at e
        rw [keep _ _ _ (by simp [step])] at e
        have read : (step (List.ofFn x) g).getD 9 false =
            g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
          change (List.ofFn x ++ [_]).getD 9 false = _
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
          simp
        rw [read] at e
        change List.ofFn x ++ [_] = List.ofFn x ++ [_]
        rw [e]
      have hop : h.op = PEqualNP.CircuitLowerBounds.GateOp.or := Option.some.inj second
      obtain ⟨a,b,pins⟩ := normalize h.inputs (fan h (by simp)).2
      refine ⟨a,b,⟨gs,o⟩,fun k hk => fan k (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk)),?_,?_⟩
      · change gs.length + 2 = (g::h::gs).length
        simp
      · intro x
        change (gs.foldl step (row x ++ [(row x).getD a.val false || (row x).getD b.val false])).getD o false =
          (gs.foldl step (step (step (List.ofFn x) g) h)).getD o false
        rw [firstValue]
        have hrow := pins (row x) (by simp [row])
        unfold step at *
        rw [hop,hrow]
