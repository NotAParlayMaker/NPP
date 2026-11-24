import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1666_2
    (h1 : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!(x 4)]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h2 : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!(x 4)]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (h3 : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → D.size ≤ 13 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [!(x 4)]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.not.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  let target : (Fin 9 → Bool) → Bool := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let init (x : Fin 9 → Bool) := List.ofFn x ++ [!(x 4)]
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserved (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons]
      have hlt : i < (step w g).length := by
        rw [List.length_append, List.length_cons, List.length_nil]
        exact Nat.lt_succ_of_lt hi
      rw [ih (step w g) hlt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hi]
  have atEnd (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl w.length),
      Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  have headVal (g : PEqualNP.CircuitLowerBounds.Gate) (tail : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (x : Fin 9 → Bool) :
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨g :: tail, o⟩ (List.ofFn x)).getD 9 false =
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) := by
    let w := List.ofFn x
    have hl : w.length = 9 := List.length_ofFn
    have hlt9 : 9 < (step w g).length := by
      change 9 < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length
      rw [List.length_append, List.length_cons, List.length_nil, hl]
      exact Nat.lt_succ_self 9
    change (tail.foldl step (step w g)).getD 9 false = _
    rw [preserved tail (step w g) 9 hlt9]
    have ha := atEnd w (g.op.eval (g.inputs.map fun i => w.getD i false))
    rw [hl] at ha
    exact ha
  have pad (w : List Bool) (o : ℕ) : (w ++ [false]).getD o false = w.getD o false := by
    by_cases h : o < w.length
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · have h' : w.length ≤ o := Nat.le_of_not_lt h
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_right h', List.getElem?_eq_none h', Option.getD_none]
      cases o - w.length <;> rfl
  intro C hfan hhead hfun
  obtain ⟨gs, o⟩ := C
  cases gs with
  | nil =>
    have bad := hhead (fun _ => false)
    change (List.ofFn (fun _ : Fin 9 => false)).getD 9 false = true at bad
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (le_of_eq (List.length_ofFn : (List.ofFn (fun _ : Fin 9 => false)).length = 9)),
      Option.getD_none] at bad
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
      have hf : PEqualNP.MetaComplexity.FanInTwo D := by
        intro a ha
        change a ∈ ([] : List PEqualNP.CircuitLowerBounds.Gate) at ha
        cases ha
      obtain ⟨x, hx⟩ := h2 [] (Nat.zero_le 2) D hf (Nat.zero_le 13)
      change (init x ++ [false]).getD o false ≠ target x at hx
      exact False.elim (hx ((pad (init x) o).trans (agree x)))
    | cons k rest =>
      by_contra short
      change ¬ 16 ≤ (g :: k :: rest).length at short
      have hlen16 : ¬ 16 ≤ rest.length + 2 := short
      let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨rest, o⟩
      have hd : PEqualNP.MetaComplexity.FanInTwo D := by
        intro a ha
        exact hfan a (List.mem_cons_of_mem g (List.mem_cons_of_mem k ha))
      have hs : D.size ≤ 13 := by
        change rest.length ≤ 13
        have hlt16 : rest.length + 2 < 14 + 2 := Nat.lt_of_not_ge hlen16
        exact Nat.le_of_lt_succ (Nat.lt_of_add_lt_add_right hlt16)
      have hk := hfan k (List.mem_cons_of_mem g (List.mem_cons_self ..))
      obtain ⟨hop, hlen⟩ := hk
      have bad : ∃ x : Fin 9 → Bool, D.eval (step (init x) k) ≠ target x := by
        rcases hop with h | h | h
        · obtain ⟨x, hx⟩ := h1 k.inputs hlen D hd hs
          exact ⟨x, by change D.eval (init x ++ [k.op.eval _]) ≠ _; rw [h]; exact hx⟩
        · obtain ⟨x, hx⟩ := h2 k.inputs hlen D hd hs
          exact ⟨x, by change D.eval (init x ++ [k.op.eval _]) ≠ _; rw [h]; exact hx⟩
        · obtain ⟨x, hx⟩ := h3 k.inputs hlen D hd hs
          exact ⟨x, by change D.eval (init x ++ [k.op.eval _]) ≠ _; rw [h]; exact hx⟩
      obtain ⟨x, hx⟩ := bad
      exact hx (agree x)
