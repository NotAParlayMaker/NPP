import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2531_74 :
    (¬ HasCircuitSize 8 (fun x : Fin 8 → Bool =>
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 0 && x 4 || x 1 && x 5 ||
      x 2 && x 6 || x 3 && x 7 || x 4 && x 6 || x 5 && x 7 || x 7 && x 4) 12) →
    (let f : (Fin 9 → Bool) → Bool := fun x =>
       ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
         (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
     let ws : List Gate → (Fin 9 → Bool) → List Bool := fun gs x =>
       (⟨gs, 0⟩ : Circuit).wires (List.ofFn x ++ [x 0 && x 6])
     let ge : List Gate → Gate → (Fin 9 → Bool) → Bool := fun gs g x =>
       g.op.eval (g.inputs.map fun i => (ws gs x).getD i false)
     ∀ (gs : List Gate) (g : Gate) (a : ℕ), gs.length ≤ 11 → 10 ≤ a →
       a < 10 + gs.length → FanInTwo ⟨gs ++ [g], 0⟩ →
       (∀ w ∈ gs ++ [g], ∀ i ∈ w.inputs, i ≤ 21) →
       (∃ r ∈ gs, r.op = GateOp.not) →
       (∃ x : Fin 9 → Bool, x 6 = false ∧ ge gs g x = true ∧ (ws gs x).getD a false = true) →
       (∃ x : Fin 9 → Bool, x 6 = false ∧ ge gs g x = false ∧ (ws gs x).getD a false = false) →
       (fun x => ge gs g x || !((ws gs x).getD a false)) ≠ f) →
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 : PEqualNP.CircuitLowerBounds.Gate) (x4 : ℕ),   x2.length ≤ (11 : ℕ) →     x4 ≤ (21 : ℕ) →       PEqualNP.MetaComplexity.FanInTwo { gates := x2 ++ [x3], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →         (∀ x8 ∈ x2 ++ [x3], ∀ x10 ∈ x8.inputs, x10 ≤ (21 : ℕ)) →           have x9 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x9 : Fin (9 : ℕ) → Bool) => { gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ))]);           have x10 : (Fin (9 : ℕ) → Bool) → Bool := fun (x10 : Fin (9 : ℕ) → Bool) => x3.op.eval (List.map (fun (x11 : ℕ) => (x9 x10).getD x11 Bool.false) x3.inputs);           (∀ (x11 : Fin (9 : ℕ) → Bool), x1 x11 = Bool.false → x10 x11 = Bool.false ∧ (x9 x11).getD x4 Bool.false = Bool.true) → ∃ (x12 : Fin (9 : ℕ) → Bool), x1 x12 = Bool.true ∧ x10 x12 = Bool.false ∧ (x9 x12).getD x4 Bool.false = Bool.true := by
  intro lower remaining f gs g a len maxA fanin bounded ws ge neg
  by_contra! omitted
  have accepts (x : Fin 9 → Bool) : (ge x || !((ws x).getD a false)) = f x := by
    cases target : f x with
    | false =>
        obtain ⟨low, high⟩ := neg x target
        simp only [low, high, Bool.not_true, Bool.or_false]
    | true =>
        specialize omitted x target
        cases h : ge x <;> cases j : (ws x).getD a false <;> simp_all
  let word : (Fin 9 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 && x 6]
  let step : List Bool → Gate → List Bool := fun u r =>
    u ++ [r.op.eval (r.inputs.map fun i => u.getD i false)]
  have appendOther (xs : List Bool) (b : Bool) (i : ℕ) (different : i ≠ xs.length) :
      (xs ++ [b]).getD i false = xs.getD i false := by
    by_cases before : i < xs.length
    · exact List.getD_append _ _ _ _ before
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have stayRaw (rs : List Gate) (xs : List Bool) (i : ℕ) (before : i < xs.length) :
      (rs.foldl step xs).getD i false = xs.getD i false := by
    induction rs generalizing xs with
    | nil => rfl
    | cons r rs ih =>
        rw [List.foldl_cons, ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ before
  have wireLen (rs : List Gate) (xs : List Bool) :
      (rs.foldl step xs).length = xs.length + rs.length := by
    induction rs generalizing xs with
    | nil => simp
    | cons r rs ih =>
        rw [List.foldl_cons, ih]
        simp [step]
        omega
  let zero : Fin 9 → Bool := fun _ => false
  have zeros : word zero = List.replicate 10 false := by
    dsimp only [word, zero]
    decide
  have fzero : f zero = false := by
    simp [f, zero]
  have selected := (neg zero fzero).2
  have gateOnly : 10 ≤ a := by
    by_contra! raw
    have old : (word zero).getD a false = false := by
      rw [zeros, List.getD_eq_getElem _ _ (by simp; omega)]
      apply List.getElem_replicate
    have conserved := stayRaw gs (word zero) a (by simp [word]; omega)
    change (gs.foldl step (word zero)).getD a false = true at selected
    rw [conserved, old] at selected
    contradiction
  have valid : a < 10 + gs.length := by
    by_contra! missing
    have tooLate : (gs.foldl step (word zero)).length ≤ a := by
      rw [wireLen]
      simpa [word] using missing
    change (gs.foldl step (word zero)).getD a false = true at selected
    rw [List.getD_eq_default _ _ tooLate] at selected
    contradiction
  let embed : (Fin 8 → Bool) → Fin 9 → Bool := fun y =>
    ![y 1, y 0, y 4, y 7, y 5, y 2, false, y 6, y 3]
  let ren : ℕ → ℕ := fun i =>
    if hi : i < 10 then ![1, 0, 4, 7, 5, 2, 100, 6, 3, 100] (⟨i, hi⟩ : Fin 10)
    else i - 2
  let rename : Gate → Gate := fun r => ⟨r.op, r.inputs.map ren⟩
  have unchanged (i : ℕ) (before : 10 ≤ i) : ren i = i - 2 := by
    simp [ren, Nat.not_lt.mpr before]
  have renSmall (i : Fin 10) : ren i < 8 ∨ ren i = 100 := by
    fin_cases i <;> dsimp only [ren] <;> decide
  have rawWord (y : Fin 8 → Bool) (i : Fin 10) :
      (word (embed y)).getD i false = (List.ofFn y).getD (ren i) false := by
    fin_cases i <;> simp [word, embed, ren, List.ofFn_succ, List.getD]
  have relWord (y : Fin 8 → Bool) (i : ℕ) :
      (word (embed y)).getD i false = (List.ofFn y).getD (ren i) false := by
    by_cases raw : i < 10
    · exact rawWord y ⟨i, raw⟩
    · rw [unchanged i (by omega)]
      rw [List.getD_eq_default _ _ (by simp [word]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  have simulate (rs : List Gate) (u v : List Bool) (oldLen : u.length = v.length + 2)
      (lowerLen : 8 ≤ v.length) (upperLen : v.length + rs.length < 100)
      (agrees : ∀ i, u.getD i false = v.getD (ren i) false) (i : ℕ) :
      (rs.foldl step u).getD i false = ((rs.map rename).foldl step v).getD (ren i) false := by
    induction rs generalizing u v with
    | nil => exact agrees i
    | cons r rs ih =>
        have body : r.op.eval (r.inputs.map fun j => u.getD j false) =
            (rename r).op.eval ((rename r).inputs.map fun j => v.getD j false) := by
          simp only [rename, List.map_map, agrees]
          rfl
        rw [List.map_cons, List.foldl_cons, List.foldl_cons]
        apply ih
        · simp [step, oldLen]
        · simp [step]
          omega
        · simp [step] at upperLen ⊢
          omega
        · intro j
          by_cases isNew : j = u.length
          · have renNew : ren j = v.length := by
              rw [unchanged j (by omega)]
              omega
            rw [isNew, show ren u.length = v.length from isNew ▸ renNew]
            change (u ++ [_]).getD u.length false = (v ++ [_]).getD v.length false
            rw [List.getD_append_right _ _ _ _ (by omega),
                List.getD_append_right _ _ _ _ (by omega)]
            simpa only [Nat.sub_self, List.getD_cons_zero] using body
          · have noNew : ren j ≠ v.length := by
              by_cases raw : j < 10
              · have small : ren j < 8 ∨ ren j = 100 := renSmall ⟨j, raw⟩
                omega
              · rw [unchanged j (by omega)]
                omega
            exact (appendOther u _ j isNew).trans
              ((agrees j).trans (appendOther v _ (ren j) noNew).symm)
  have cofactor (y : Fin 8 → Bool) : f (embed y) =
      (y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 0 && y 4 || y 1 && y 5 ||
        y 2 && y 6 || y 3 && y 7 || y 4 && y 6 || y 5 && y 7 || y 7 && y 4) := by
    change (y 1 && y 0 || (y 0 && y 4 || (y 4 && y 7 || (y 7 && y 5 ||
      (y 5 && y 1 || (y 1 && y 2 || (y 0 && false || (y 4 && y 6 || (y 7 && y 3 ||
      (y 2 && y 6 || (false && y 3 || (y 3 && y 2 || false)))))))))))) = _
    simp only [Bool.and_false, Bool.false_and, Bool.false_or, Bool.or_false]
    ac_rfl
  have cannotRestrict (rs : List Gate) (j : ℕ) (small : rs.length ≤ 12)
      (eligible : FanInTwo ⟨rs, j⟩)
      (exactSlice : ∀ y : Fin 8 → Bool,
        (rs.foldl step (word (embed y))).getD j false = f (embed y)) : False := by
    let C : Circuit := ⟨rs.map rename, ren j⟩
    have shape : FanInTwo C := by
      intro r hr
      change r ∈ rs.map rename at hr
      obtain ⟨original, mem, rfl⟩ := List.mem_map.mp hr
      obtain ⟨kind, arity⟩ := eligible original mem
      exact ⟨kind, by simpa [rename] using arity⟩
    apply lower
    refine ⟨C, shape, ?_, ?_⟩
    · change (rs.map rename).length ≤ 12
      simpa only [List.length_map] using small
    intro y
    have preserves := simulate rs (word (embed y)) (List.ofFn y)
      (by simp [word]) (by simp) (by simp; omega) (relWord y) j
    exact preserves.symm.trans ((exactSlice y).trans (cofactor y))
  have readLast (r : Gate) (x : Fin 9 → Bool) :
      ((gs ++ [r]).foldl step (word x)).getD (10 + gs.length) false =
        r.op.eval (r.inputs.map fun i => (ws x).getD i false) := by
    let computed := gs.foldl step (word x)
    have computedLen : computed.length = 10 + gs.length := by simp [computed, wireLen, word]
    rw [List.foldl_append]
    change (computed ++ [_]).getD (10 + gs.length) false = _
    rw [← computedLen, List.getD_append_right _ _ _ _ (by omega)]
    simp only [Nat.sub_self, List.getD_cons_zero]
    rfl
  let inv : Gate := ⟨.not, [a]⟩
  have eligibleInv : FanInTwo ⟨gs ++ [inv], 10 + gs.length⟩ := by
    intro r hr
    change r ∈ gs ++ [inv] at hr
    rcases List.mem_append.mp hr with front | last
    · exact fanin r (List.mem_append_left _ front)
    · have eq : r = inv := by simpa using last
      subst r
      constructor <;> simp [inv]
  classical
  have gPrivate : ∃ x : Fin 9 → Bool, x 6 = false ∧ ge x = true ∧ (ws x).getD a false = true := by
    by_contra absent
    apply cannotRestrict (gs ++ [inv]) (10 + gs.length) (by simp; omega) eligibleInv
    intro y
    have slice := accepts (embed y)
    rw [readLast, show inv.op.eval (inv.inputs.map fun i => (ws (embed y)).getD i false) =
      !((ws (embed y)).getD a false) from rfl]
    cases hw : (ws (embed y)).getD a false with
    | false =>
        rw [hw] at slice
        simpa only [Bool.not_false, Bool.or_true] using slice
    | true =>
        have hg : ge (embed y) = false := Bool.eq_false_of_not_eq_true fun high =>
          absent ⟨embed y, rfl, high, hw⟩
        rw [hg, hw] at slice
        simpa only [Bool.not_true, Bool.or_false] using slice
  have wPrivate : ∃ x : Fin 9 → Bool, x 6 = false ∧ ge x = false ∧ (ws x).getD a false = false := by
    by_contra absent
    apply cannotRestrict (gs ++ [g]) (10 + gs.length) (by simp; omega)
      (fun r hr => fanin r hr)
    intro y
    rw [readLast]
    change ge (embed y) = f (embed y)
    have slice := accepts (embed y)
    cases hg : ge (embed y) with
    | true =>
        rw [hg] at slice
        simpa only [Bool.true_or] using slice
    | false =>
        have hw : (ws (embed y)).getD a false = true := Bool.eq_true_of_not_eq_false fun low =>
          absent ⟨embed y, rfl, hg, low⟩
        rw [hg, hw] at slice
        simpa only [Bool.not_true, Bool.or_false] using slice
  have prefixNot : ∃ r ∈ gs, r.op = GateOp.not := by
    by_contra! onlyPositive
    have allowed (r : Gate) (h : r ∈ gs) : r.op = .and ∨ r.op = .or := by
      have kind := (fanin r (List.mem_append_left _ h)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, onlyPositive r h, or_false] at kind
      exact kind
    have monotonicOp (r : Gate) (kind : r.op = .and ∨ r.op = .or)
        (u v : List Bool) (mon : ∀ i, u.getD i false = true → v.getD i false = true)
        (yes : r.op.eval (r.inputs.map fun i => u.getD i false) = true) :
        r.op.eval (r.inputs.map fun i => v.getD i false) = true := by
      rcases kind with both | either
      · rw [both] at yes ⊢
        change (r.inputs.map fun i => u.getD i false).all id = true at yes
        change (r.inputs.map fun i => v.getD i false).all id = true
        simp only [List.all_eq_true, id_eq] at yes ⊢
        intro j hj
        obtain ⟨i, present, rfl⟩ := List.mem_map.mp hj
        exact mon i (yes _ (List.mem_map.mpr ⟨i, present, rfl⟩))
      · rw [either] at yes ⊢
        change (r.inputs.map fun i => u.getD i false).any id = true at yes
        change (r.inputs.map fun i => v.getD i false).any id = true
        simp only [List.any_eq_true, id_eq] at yes ⊢
        obtain ⟨j, hj, trueAt⟩ := yes
        obtain ⟨i, present, rfl⟩ := List.mem_map.mp hj
        exact ⟨_, List.mem_map.mpr ⟨i, present, rfl⟩, mon i trueAt⟩
    have monotonicWires (rs : List Gate) (ok : ∀ r ∈ rs, r.op = .and ∨ r.op = .or)
        (u v : List Bool) (sameLen : u.length = v.length)
        (mon : ∀ i, u.getD i false = true → v.getD i false = true) (i : ℕ) :
        (rs.foldl step u).getD i false = true → (rs.foldl step v).getD i false = true := by
      induction rs generalizing u v with
      | nil => exact mon i
      | cons r rs ih =>
          have equalStep : (step u r).length = (step v r).length := by simp [step, sameLen]
          have monStep (j : ℕ) : (step u r).getD j false = true → (step v r).getD j false = true := by
            by_cases birth : j = u.length
            · have nextBirth := birth.trans sameLen
              change (u ++ [_]).getD j false = true → (v ++ [_]).getD j false = true
              rw [List.getD_append_right _ _ _ _ (by omega),
                List.getD_append_right _ _ _ _ (by omega)]
              have left : j - u.length = 0 := by omega
              have right : j - v.length = 0 := by omega
              simpa only [left, right, List.getD_cons_zero] using
                monotonicOp r (ok r (by simp)) u v mon
            · change (u ++ [_]).getD j false = true → (v ++ [_]).getD j false = true
              rw [appendOther _ _ _ birth, appendOther _ _ _ (by omega)]
              exact mon j
          exact ih (fun q hq => ok q (List.mem_cons_of_mem _ hq)) _ _ equalStep monStep
    obtain ⟨x, _, _, wlow⟩ := wPrivate
    have minWords (i : ℕ) : (word zero).getD i false = true → (word x).getD i false = true := by
      intro bad
      rw [zeros] at bad
      by_cases before : i < 10
      · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate] at bad
        contradiction
      · rw [List.getD_eq_default _ _ (by simp; omega)] at bad
        contradiction
    have whigh := monotonicWires gs allowed (word zero) (word x) (by simp [word]) minWords a selected
    exact Bool.noConfusion (wlow.symm.trans whigh)
  exact remaining gs g a len gateOnly valid fanin bounded prefixNot gPrivate wPrivate (funext accepts)
