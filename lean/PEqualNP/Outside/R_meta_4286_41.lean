import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4286_41
    (or01Lower :
      let F : (Fin 9 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      ∀ C : Circuit, FanInTwo C →
        (∀ x : Fin 9 → Bool,
          (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1)) →
        circuitFun 9 C = F → 16 ≤ C.size)
    (dependentCase :
      let F : (Fin 9 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
      let tap : List Gate → ℕ → ℕ → (Fin 9 → Bool) → Bool → Bool :=
        fun gs a b x z =>
          let w := (⟨gs, 0⟩ : Circuit).wires (List.ofFn x ++ [z])
          w.getD a false && w.getD b false
      ∀ (gs : List Gate) (a b : ℕ),
        gs.length = 13 → FanInTwo (⟨gs, 0⟩ : Circuit) →
        gs.countP (fun g => g.op.eval [false]) = 1 →
        10 ≤ a → a ≤ b → b < 23 →
        (∃ x : Fin 9 → Bool,
          tap gs a b x (x 0 || x 3) = F x ∧
          tap gs a b x (x 0 || x 1) ≠ F x ∧
          x 0 = false ∧ x 1 ≠ x 3) →
        ∃ x : Fin 9 → Bool, tap gs a b x (x 0 || x 3) ≠ F x)
    : ∀ (gs : List Gate) (a b : ℕ),
        gs.length = 13 → FanInTwo (⟨gs, 0⟩ : Circuit) →
        gs.countP (fun g => g.op.eval [false]) = 1 →
        10 ≤ a → a ≤ b → b < 23 →
        ∃ x : Fin 9 → Bool,
          let w := (⟨gs, 0⟩ : Circuit).wires (List.ofFn x ++ [x 0 || x 3])
          (w.getD a false && w.getD b false) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
              x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
              x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
  classical
  intro gs a b hlen hfan hcount ha hab hb
  dsimp only at or01Lower dependentCase
  let F : (Fin 9 → Bool) → Bool := fun x =>
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let tap : List Gate → ℕ → ℕ → (Fin 9 → Bool) → Bool → Bool :=
    fun gs a b x z =>
      let w := (⟨gs, 0⟩ : Circuit).wires (List.ofFn x ++ [z])
      w.getD a false && w.getD b false
  let step (w : List Bool) (g : Gate) : List Bool :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
  have runLength (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
        change (run gs (step w g)).length = w.length + (gs.length + 1)
        rw [ih]
        simp [step]
        omega
  have runPreserves (gs : List Gate) (w : List Bool) (i : ℕ)
      (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
        calc
          (run (g :: gs) w).getD i false = (run gs (step w g)).getD i false := rfl
          _ = (step w g).getD i false := ih (step w g) (by simp [step]; omega)
          _ = w.getD i false := List.getD_append _ _ _ _ hi
  have runAppendLast (gs : List Gate) (w : List Bool) (g : Gate) :
      run (gs ++ [g]) w = step (run gs w) g := by
    simp [run, List.foldl_append, step]
  by_contra h
  have allA (x : Fin 9 → Bool) : tap gs a b x (x 0 || x 3) = F x := by
    by_contra hx
    have hm :
        (let w := (⟨gs, 0⟩ : Circuit).wires (List.ofFn x ++ [x 0 || x 3]);
          (w.getD a false && w.getD b false) ≠
            (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
              x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
              x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) := by
      simpa [tap, F] using hx
    exact h ⟨x, hm⟩
  have orValue (x y : Bool) : GateOp.or.eval [x,y] = (x || y) := by
    cases x <;> cases y <;> rfl
  have andValue (x y : Bool) : GateOp.and.eval [x,y] = (x && y) := by
    cases x <;> cases y <;> rfl
  let first : Gate := ⟨.or, [0, 1]⟩
  let last : Gate := ⟨.and, [a, b]⟩
  let C : Circuit := ⟨first :: (gs ++ [last]), 23⟩
  have hfanC : FanInTwo C := by
    intro g hg
    simp only [C, List.mem_cons, List.mem_append] at hg
    rcases hg with h | h
    · subst g
      simp [first]
    · rcases h with h | h
      · exact hfan g h
      · rcases h with h | h
        · subst g
          simp [last]
        · simp at h
  have hlenC : C.gates.length = 15 := by simp [C, hlen]
  have hfirstC : ∀ x : Fin 9 → Bool,
      (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 1) := by
    intro x
    change (run (gs ++ [last]) (step (List.ofFn x) first)).getD 9 false = _
    have hkeep := runPreserves (gs ++ [last]) (step (List.ofFn x) first)
      9 (by simp [step])
    rw [hkeep]
    simp [step, first, orValue, List.getD_eq_getElem?_getD]
  have hBval (x : Fin 9 → Bool) :
      C.eval (List.ofFn x) = tap gs a b x (x 0 || x 1) := by
    let seed := List.ofFn x ++ [x 0 || x 1]
    have hseed : seed.length = 10 := by simp [seed]
    have hprefix : step (List.ofFn x) first = seed := by
      simp [step, first, seed, orValue, List.getD_eq_getElem?_getD]
    have hcwire : C.wires (List.ofFn x) =
        run gs seed ++ [(run gs seed).getD a false && (run gs seed).getD b false] := by
      change run (gs ++ [last]) (step (List.ofFn x) first) = _
      rw [runAppendLast, hprefix]
      simp [step, last, andValue]
    change (C.wires (List.ofFn x)).getD 23 false = _
    rw [hcwire]
    have hrlen : (run gs seed).length = 23 := by
      rw [runLength, hseed, hlen]
    rw [List.getD_append_right _ _ _ _ (by omega), hrlen]
    change ((run gs seed).getD a false && (run gs seed).getD b false) =
      tap gs a b x (x 0 || x 1)
    rfl
  have hCneq : circuitFun 9 C ≠ F := by
    intro hCeq
    have hbound := or01Lower C hfanC hfirstC hCeq
    have hCsize : C.size = 15 := hlenC
    omega
  have rowB : ∃ x : Fin 9 → Bool,
      tap gs a b x (x 0 || x 1) ≠ F x := by
    by_contra hNone
    apply hCneq
    funext x
    by_contra hx
    have hB : tap gs a b x (x 0 || x 1) ≠ F x := by
      rw [← hBval x]
      exact hx
    exact hNone ⟨x, hB⟩
  obtain ⟨x, hxB⟩ := rowB
  have hxA := allA x
  have hseedNe : (x 0 || x 3) ≠ (x 0 || x 1) := by
    intro heq
    have hseed : List.ofFn x ++ [x 0 || x 3] = List.ofFn x ++ [x 0 || x 1] := by
      simp [heq]
    have hrun : (⟨gs, 0⟩ : Circuit).wires
        (List.ofFn x ++ [x 0 || x 3]) = (⟨gs, 0⟩ : Circuit).wires
        (List.ofFn x ++ [x 0 || x 1]) := by rw [hseed]
    have hprod : tap gs a b x (x 0 || x 3) =
        tap gs a b x (x 0 || x 1) := by
      dsimp [tap]
      rw [hrun]
    exact hxB (by rw [← hxA, ← hprod])
  have hx0 : x 0 = false := by
    cases h0 : x 0 <;> simp [h0] at hseedNe ⊢
  have hx13 : x 1 ≠ x 3 := by
    intro heq
    apply hseedNe
    simp [heq]
  have separating :
      tap gs a b x (x 0 || x 3) = F x ∧
      tap gs a b x (x 0 || x 1) ≠ F x ∧
      x 0 = false ∧ x 1 ≠ x 3 := ⟨hxA, hxB, hx0, hx13⟩
  obtain ⟨y, hy⟩ := dependentCase gs a b hlen hfan hcount ha hab hb
    ⟨x, separating.1, separating.2.1, separating.2.2.1, separating.2.2.2⟩
  exact h ⟨y, by simpa [tap, F] using hy⟩
