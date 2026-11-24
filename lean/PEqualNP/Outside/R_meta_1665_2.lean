import PEqualNP.Defs

-- Peel the first two gates (wire 9 = !(x 0) and gate 1 by its operator), leaving at most 13 gates.
theorem PEqualNP.Outside.R_meta_1665_2
    (h1 : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!(x 0)]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h2 : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!(x 0)]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h3 : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!(x 0)]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  let target : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let init (x : Fin 9 → Bool) := List.ofFn x ++ [!(x 0)]
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserved (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons]
      have hlt : i < (step w g).length := by
        change i < (w ++ [_]).length
        rw [List.length_append]
        exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)
      rw [ih (step w g) hlt]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have atEnd (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl w.length), Nat.sub_self]
    rfl
  have headVal (g : PEqualNP.CircuitLowerBounds.Gate) (tail : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : Fin 9 → Bool) :
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨g :: tail, o⟩ (List.ofFn x)).getD 9 false =
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
    let w := List.ofFn x
    have hl : w.length = 9 := List.length_ofFn
    change (tail.foldl step (step w g)).getD 9 false = _
    have hlt : 9 < (step w g).length := by
      rw [List.length_append, hl, List.length_singleton]
      exact Nat.lt_succ_self 9
    rw [preserved tail (step w g) 9 hlt]
    exact Eq.subst (motive := fun m => (step w g).getD m false = _) hl
      (atEnd w (g.op.eval (g.inputs.map fun i => w.getD i false)))
  have pad (w : List Bool) (o : ℕ) : (w ++ [false]).getD o false = w.getD o false := by
    by_cases h : o < w.length
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · have h' : w.length ≤ o := Nat.le_of_not_lt h
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right h', List.getElem?_eq_none h', Option.getD_none]
      cases o - w.length with
      | zero => rfl
      | succ _ => rfl
  intro C hfan hhead hfun
  rcases C with ⟨gs, o⟩
  cases gs with
  | nil =>
    have bad := hhead (fun _ => false)
    change (List.ofFn (fun _ : Fin 9 => false)).getD 9 false = true at bad
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_eq List.length_ofFn)] at bad
    cases bad
  | cons g tail =>
    have agree (x : Fin 9 → Bool) :
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨tail, o⟩ (init x) = target x := by
      have hg := (headVal g tail o x).symm.trans (hhead x)
      have hh := congrFun hfun x
      change (tail.foldl step (List.ofFn x ++ [g.op.eval
        (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD o false = target x at hh
      rw [hg] at hh
      exact hh
    cases tail with
    | nil =>
      let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨[], o⟩
      have hf : PEqualNP.MetaComplexity.FanInTwo D := fun _ ha => False.elim (List.not_mem_nil ha)
      rcases h2 [] (Nat.zero_le 2) D hf (Nat.zero_le 13) with ⟨x, hx⟩
      change (init x ++ [false]).getD o false ≠ target x at hx
      exact False.elim (hx ((pad (init x) o).trans (agree x)))
    | cons k rest =>
      by_contra short
      change ¬ 16 ≤ (g :: k :: rest).length at short
      have hs : (PEqualNP.CircuitLowerBounds.Circuit.mk rest o).size ≤ 13 := by
        change rest.length ≤ 13
        have h1 : rest.length + 2 < 14 + 2 := Nat.lt_of_not_le short
        exact Nat.le_of_lt_succ (Nat.lt_of_add_lt_add_right h1)
      let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨rest, o⟩
      have hd : PEqualNP.MetaComplexity.FanInTwo D :=
        fun a ha => hfan a (List.mem_cons_of_mem g (List.mem_cons_of_mem k ha))
      have hk := hfan k (List.mem_cons_of_mem g (List.mem_cons_self))
      have hlen : k.inputs.length ≤ 2 := hk.2
      have bad : ∃ x : Fin 9 → Bool, D.eval (step (init x) k) ≠ target x := by
        change ∃ x : Fin 9 → Bool,
          D.eval (init x ++ [k.op.eval (k.inputs.map fun i => (init x).getD i false)]) ≠ target x
        rcases Set.mem_insert_iff.mp hk.1 with h | h
        · rw [h]; exact h1 k.inputs hlen D hd hs
        · rcases Set.mem_insert_iff.mp h with h | h
          · rw [h]; exact h2 k.inputs hlen D hd hs
          · rw [Set.mem_singleton_iff.mp h]; exact h3 k.inputs hlen D hd hs
      rcases bad with ⟨x, hx⟩
      exact hx (agree x)
