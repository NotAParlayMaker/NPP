import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The case where the bundled input has no effective reader uses the checked ordinary bound.
-- A remaining candidate must also read both of its constituent inputs independently.
theorem PEqualNP.Outside.R_meta_4360_219
    (ordinary : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates)
    (readers : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (∀ i : ℕ, i = 0 ∨ i = 6 ∨ i = 9 → ∃ g ∈ x1.gates,
      i ∈ (if GateOp.rec false false true (fun _ => false) false g.op = true then g.inputs.take 1 else g.inputs)) →
    10 ≤ x1.output → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x3 ++ [x3 (0 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ))]) = (x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)))) → (13 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates := by
  intro C legal computes
  let read (g : Gate) : List ℕ :=
    if GateOp.rec false false true (fun _ => false) false g.op = true then g.inputs.take 1 else g.inputs
  let step (ws : List Bool) (g : Gate) : List Bool :=
    ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have evaluation (g : Gate) (v : ℕ → Bool) :
      g.op.eval (g.inputs.map v) = g.op.eval ((read g).map v) := by
    rcases g with ⟨op, args⟩
    cases op <;> try rfl
    cases args <;> rfl
  have foldAgree (w : ℕ) (gates : List Gate) (unused : ∀ g ∈ gates, w ∉ read g)
      (a b : List Bool) (len : a.length = b.length)
      (agree : ∀ j, j ≠ w → a.getD j false = b.getD j false) :
      ∀ j, j ≠ w → (gates.foldl step a).getD j false = (gates.foldl step b).getD j false := by
    induction gates generalizing a b with
    | nil => exact agree
    | cons g tail ih =>
      have sameGate : g.op.eval (g.inputs.map fun i => a.getD i false) =
          g.op.eval (g.inputs.map fun i => b.getD i false) := by
        rw [evaluation, evaluation g (fun i => b.getD i false)]
        congr 1
        apply List.map_congr_left
        intro i hi
        apply agree i
        intro hiw
        exact unused g (by simp) (hiw ▸ hi)
      simp only [List.foldl_cons]
      apply ih (fun h hh => unused h (by simp [hh]))
      · simp [step, len]
      · intro j hj
        simp only [step]
        rw [sameGate]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append, len]
        split
        · exact agree j hj
        · rfl
  have evalAgree (w : ℕ) (unused : ∀ g ∈ C.gates, w ∉ read g) (hout : C.output ≠ w)
      (a b : List Bool) (len : a.length = b.length)
      (agree : ∀ j, j ≠ w → a.getD j false = b.getD j false) : C.eval a = C.eval b :=
    foldAgree w C.gates unused a b len agree C.output hout
  let args (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6]
  let f (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  change ∀ x, C.eval (args x) = f x at computes
  have validOutput : 10 ≤ C.output := by
    by_contra! short
    let i : Fin 10 := ⟨C.output, short⟩
    have witness : ∀ i : Fin 10, ∃ x : Fin 9 → Bool, (args x).getD i.val false ≠ f x := by
      dsimp [args, f]
      decide +kernel
    obtain ⟨x, hx⟩ := witness i
    apply hx
    rw [← computes x]
    change (args x).getD C.output false = (C.gates.foldl step (args x)).getD C.output false
    have preserve (ws : List Bool) (gs : List Gate) (o : ℕ) (ho : o < ws.length) :
        (gs.foldl step ws).getD o false = ws.getD o false := by
      induction gs generalizing ws with
      | nil => rfl
      | cons g gs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left ho]
    exact (preserve _ _ _ (by simpa [args] using short)).symm
  have requireSource (i : Fin 10) (h : i.val = 0 ∨ i.val = 6) : ∃ g ∈ C.gates, i.val ∈ read g := by
    have witness : ∃ x y : Fin 9 → Bool, f x ≠ f y ∧
        ∀ j : Fin 10, j ≠ i → (args x).getD j.val false = (args y).getD j.val false := by
      rcases h with hz | hs
      · have hi : i = 0 := Fin.ext hz
        subst i
        exact ⟨![true, false, false, false, true, false, true, false, false],
          ![false, false, false, false, true, false, true, false, false], by decide, by decide +kernel⟩
      · have hi : i = 6 := Fin.ext hs
        subst i
        exact ⟨![true, false, false, false, false, false, true, false, true],
          ![true, false, false, false, false, false, false, false, true], by decide, by decide +kernel⟩
    obtain ⟨x, y, distinct, agreed⟩ := witness
    classical
    by_contra absent
    have unused (g : Gate) (hg : g ∈ C.gates) : i.val ∉ read g := fun hw => absent ⟨g, hg, hw⟩
    apply distinct
    rw [← computes x, ← computes y]
    apply evalAgree i.val unused (by omega) _ _ (by simp [args])
    intro j hj
    by_cases jlt : j < 10
    · exact agreed ⟨j, jlt⟩ (fun hji => hj (congrArg Fin.val hji))
    · have le : 10 ≤ j := by omega
      simp only [List.getD_eq_getElem?_getD]
      have len (t : Fin 9 → Bool) : (args t).length = 10 := by simp [args]
      rw [List.getElem?_eq_none (by simpa [len] using le),
        List.getElem?_eq_none (by simpa [len] using le)]
  rcases Classical.em (∃ g ∈ C.gates, 9 ∈ read g) with used | used
  · apply readers C legal computes _ validOutput
    intro i hi
    rcases hi with rfl | rfl | rfl
    · exact requireSource 0 (Or.inl rfl)
    · exact requireSource 6 (Or.inr rfl)
    · exact used
  · have unused (g : Gate) (hg : g ∈ C.gates) : 9 ∉ read g := fun hw => used ⟨g, hg, hw⟩
    let D : Circuit := ⟨⟨.not, []⟩ :: C.gates, C.output⟩
    have dLegal : FanInTwo D := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp
      · exact legal _ hg
    have dEval (x : Fin 9 → Bool) : D.eval (List.ofFn x) = f x := by
      rw [← computes x]
      change C.eval (List.ofFn x ++ [true]) = C.eval (args x)
      apply evalAgree 9 unused (by omega) _ _ (by simp [args])
      intro j hj
      simp only [args, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn]
      split
      · rfl
      · have hnz : j - 9 ≠ 0 := by omega
        simp [List.getElem?_singleton, hnz]
    simpa [D, List.countP_cons] using ordinary D dLegal dEval
