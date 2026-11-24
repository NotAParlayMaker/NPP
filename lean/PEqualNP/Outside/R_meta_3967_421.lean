import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3967_421
    (low : ∀ (C : Circuit), FanInTwo C → C.size ≤ 14 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (compress : ∀ (C : Circuit) (j : ℕ), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size + 1 ∧
        ∀ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
        D.eval (List.ofFn x) = C.eval (w ++ [w.getD j false]))
    (residual : ∀ (a b : Fin 10) (C : Circuit), a < b → FanInTwo C → C.size ≤ 13 →
      (a.val = 0 ∨ a.val = 4 ∨ b.val = 4 ∨ b.val = 9 ∨
        List.countP (fun g : Gate => g.op.eval [false]) C.gates < 2) →
      (a.val, b.val) ∉ ([(0,4),(0,9),(4,9)] : List (ℕ × ℕ)) →
      ∃ x : Fin 9 → Bool, let w := List.ofFn x ++ [x 0 || x 4]
        C.eval (w ++ [w.getD a.val false || w.getD b.val false]) ≠ ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (¬∃ (x6 : Fin (9 : ℕ)) (x7 : Fin (9 : ℕ)), x6 ≠ (0 : Fin (9 : ℕ)) ∧ x6 ≠ (4 : Fin (9 : ℕ)) ∧ x7 ≠ (0 : Fin (9 : ℕ)) ∧ x7 ≠ (4 : Fin (9 : ℕ)) ∧ x6 < x7 ∧ x1.Perm [↑x6, ↑x7]) ∨ List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x3.gates < (2 : ℕ) →             ∃ (x7 : Fin (9 : ℕ) → Bool),               have x8 : List Bool := List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ))];               x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro pins hp C hc hsize hcase
  classical
  let edge (x : Fin 9 → Bool) : Bool := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let seed (x : Fin 9 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 4]
  have edgeEq (x : Fin 9 → Bool) :
      (x (0 : Fin (9 : ℕ)) && x (1 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (2 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (3 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (4 : Fin (9 : ℕ)) || x (4 : Fin (9 : ℕ)) && x (0 : Fin (9 : ℕ)) || x (0 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ)) || x (1 : Fin (9 : ℕ)) && x (6 : Fin (9 : ℕ)) || x (2 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (3 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (5 : Fin (9 : ℕ)) && x (7 : Fin (9 : ℕ)) || x (6 : Fin (9 : ℕ)) && x (8 : Fin (9 : ℕ)) || x (8 : Fin (9 : ℕ)) && x (5 : Fin (9 : ℕ))) = edge x := by
    simp only [edge, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  simp only [edgeEq]
  have noRead (j : ℕ) (hj : 10 ≤ j) (x : Fin 9 → Bool) :
      (seed x).getD j false = false := by
    exact List.getD_eq_default _ _ (by simpa [seed] using hj)
  have read0 (x : Fin 9 → Bool) : (seed x).getD 0 false = x 0 := by
    have h : 0 < (List.ofFn x).length := by simp
    change (List.ofFn x ++ _).getD 0 false = x 0
    rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h, List.getElem_ofFn]
    rfl
  have read4 (x : Fin 9 → Bool) : (seed x).getD 4 false = x 4 := by
    have h : 4 < (List.ofFn x).length := by simp
    change (List.ofFn x ++ _).getD 4 false = x 4
    rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h, List.getElem_ofFn]
    rfl
  have read9 (x : Fin 9 → Bool) : (seed x).getD 9 false = (x 0 || x 4) := by
    simp [seed]
  have simple (j : ℕ) (hj : ∀ x : Fin 9 → Bool,
      GateOp.or.eval (pins.map fun i => (seed x).getD i false) = (seed x).getD j false) :
      ∃ x : Fin 9 → Bool,
        C.eval (seed x ++ [GateOp.or.eval (pins.map fun i => (seed x).getD i false)]) ≠ edge x := by
    obtain ⟨D, hD, hs, same⟩ := compress C j hc
    obtain ⟨x, fails⟩ := low D hD (by omega)
    refine ⟨x, ?_⟩
    rw [hj x]
    intro eq
    exact fails ((same x).trans eq)
  have pair (a b : Fin 10) (hab : a < b) (hpins : pins.Perm [a.val,b.val]) :
      ∃ x : Fin 9 → Bool,
        C.eval (seed x ++ [GateOp.or.eval (pins.map fun i => (seed x).getD i false)]) ≠ edge x := by
    have value (x : Fin 9 → Bool) :
        GateOp.or.eval (pins.map fun i => (seed x).getD i false) =
          ((seed x).getD a.val false || (seed x).getD b.val false) := by
      change (pins.map (fun i => (seed x).getD i false)).any id = _
      rw [(hpins.map (fun i => (seed x).getD i false)).any_eq]
      simp
    have smallOrOne (a b : Fin 10) (hab : a < b)
        (hpins : pins.Perm [a.val,b.val]) :
        a.val = 0 ∨ a.val = 4 ∨ b.val = 4 ∨ b.val = 9 ∨
          List.countP (fun g : Gate => g.op.eval [false]) C.gates < 2 := by
      by_contra hd
      push Not at hd
      obtain ⟨ha0,ha4,hb4,hb9,hn⟩ := hd
      have hlt : a.val < b.val := hab
      have hbb : b.val < 9 := by have := b.isLt; omega
      have haa : a.val < 9 := by omega
      let u : Fin 9 := ⟨a.val,haa⟩
      let v : Fin 9 := ⟨b.val,hbb⟩
      rcases hcase with hbad | hnot
      · apply hbad
        refine ⟨u,v,?_,?_,?_,?_,hlt,hpins⟩
        · intro e
          exact ha0 (congrArg Fin.val e)
        · intro e
          exact ha4 (congrArg Fin.val e)
        · intro e
          have e0 : b.val = 0 := congrArg Fin.val e
          omega
        · intro e
          exact hb4 (congrArg Fin.val e)
      · omega
    by_cases he : (a.val,b.val) ∈ ([(0,4),(0,9),(4,9)] : List (ℕ × ℕ))
    · apply simple 9
      intro x
      rw [value x]
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at he
      rcases he with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩
      · rw [ha,hb,read0 x,read4 x,read9 x]
      · rw [ha,hb,read0 x,read9 x]
        simp only [← Bool.or_assoc, Bool.or_self]
      · rw [ha,hb,read4 x,read9 x]
        simp only [Bool.or_left_comm (x 4) (x 0) (x 4), Bool.or_self]
    · obtain ⟨x,hx⟩ := residual a b C hab hc hsize (smallOrOne a b hab hpins) he
      refine ⟨x, ?_⟩
      rw [value x]
      exact hx
  change ∃ x : Fin 9 → Bool,
    C.eval (seed x ++ [GateOp.or.eval (pins.map fun i => (seed x).getD i false)]) ≠ edge x
  cases pins with
  | nil =>
    exact simple 10 (by intro x; exact (noRead 10 le_rfl x).symm)
  | cons a tail =>
    cases tail with
    | nil =>
      apply simple a
      intro x
      change ([(seed x).getD a false] : List Bool).any id = _
      simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
    | cons b tail =>
      cases tail with
      | nil =>
        by_cases ha : a < 10
        · by_cases hb : b < 10
          · by_cases he : a = b
            · subst b
              apply simple a
              intro x
              change ([(seed x).getD a false, (seed x).getD a false] : List Bool).any id = _
              simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self]
            · let u : Fin 10 := ⟨a,ha⟩
              let v : Fin 10 := ⟨b,hb⟩
              by_cases hab : a < b
              · exact pair u v hab (List.Perm.refl _)
              · have hba : b < a := by omega
                exact pair v u hba (List.Perm.swap b a [])
          · apply simple a
            intro x
            change ([(seed x).getD a false, (seed x).getD b false] : List Bool).any id = _
            simp only [List.any_cons, List.any_nil, id_eq, noRead b (by omega) x, Bool.or_false]
        · apply simple b
          intro x
          change ([(seed x).getD a false, (seed x).getD b false] : List Bool).any id = _
          simp only [List.any_cons, List.any_nil, id_eq, noRead a (by omega) x, Bool.or_false, Bool.false_or]
      | cons j tail =>
        simp at hp

