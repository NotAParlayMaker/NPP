import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2800000 in
theorem PEqualNP.Outside.R_meta_3509_691
    (firstCases :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (a b : Fin 9) (C : Circuit), a.val * 10 + b.val ∈ [13,15,17,18] →
      FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) = f x) → False)
    (secondCases :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (a b : Fin 9) (C : Circuit), a.val * 10 + b.val ∈ [26,28,36,67] →
      FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) = f x) → False) :
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → ↑x1 * (10 : ℕ) + ↑x2 ∉ [(12 : ℕ), (21 : ℕ), (23 : ℕ), (32 : ℕ), (16 : ℕ), (61 : ℕ), (27 : ℕ), (72 : ℕ), (38 : ℕ), (83 : ℕ), (57 : ℕ), (75 : ℕ), (68 : ℕ), (86 : ℕ), (58 : ℕ), (85 : ℕ)] → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x12 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x12 ++ [x12 (0 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)), x12 x1 || x12 x2]) = (x12 (0 : Fin (9 : ℕ)) && x12 (1 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (2 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (3 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (4 : Fin (9 : ℕ)) || x12 (4 : Fin (9 : ℕ)) && x12 (0 : Fin (9 : ℕ)) || x12 (0 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)) || x12 (1 : Fin (9 : ℕ)) && x12 (6 : Fin (9 : ℕ)) || x12 (2 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (3 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (5 : Fin (9 : ℕ)) && x12 (7 : Fin (9 : ℕ)) || x12 (6 : Fin (9 : ℕ)) && x12 (8 : Fin (9 : ℕ)) || x12 (8 : Fin (9 : ℕ)) && x12 (5 : Fin (9 : ℕ)))) → False := by
  intro a b C a0 a4 b0 b4 distinct nonedge fan budget correct
  let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have computes (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) = f x := by
    have h := correct x
    simp only [Bool.or_assoc] at h
    simp only [f, List.any_cons, List.any_nil, Bool.or_false]
    exact h
  let ren (j : ℕ) := ([0,5,8,3,4,1,7,6,2] : List ℕ).getD j j
  have renSmall (j : ℕ) (hj : j < 9) : ren j < 9 := by
    interval_cases j <;> decide
  have renLarge (j : ℕ) (hj : 9 ≤ j) : ren j = j := by
    exact List.getD_eq_default _ _ (by simpa using hj)
  let π (i : Fin 9) : Fin 9 := ⟨ren i.val, renSmall i.val i.isLt⟩
  let flip (x : Fin 9 → Bool) (i : Fin 9) := x (π i)
  have invariant (x : Fin 9 → Bool) : f (flip x) = f x := by
    have h : ∀ p0 p1 p2 p3 p4 p5 p6 p7 p8 : Bool,
        (p0 && p5 || (p5 && p8 || (p8 && p3 || (p3 && p4 || (p4 && p0 ||
          (p0 && p1 || (p5 && p7 || (p8 && p6 || (p3 && p2 || (p1 && p6 ||
            (p7 && p2 || p2 && p1))))))))))) =
        (p0 && p1 || (p1 && p2 || (p2 && p3 || (p3 && p4 || (p4 && p0 ||
          (p0 && p5 || (p1 && p6 || (p2 && p7 || (p3 && p8 || (p5 && p7 ||
            (p6 && p8 || p8 && p5))))))))))) := by decide
    simp only [f, List.any_cons, List.any_nil, Bool.or_false]
    exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
  let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map ren⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  have sim (gs : List Gate) (w v : List Bool) (len : w.length = v.length)
      (low : 9 ≤ w.length) (agree : ∀ j, w.getD j false = v.getD (ren j) false) :
      ∀ j, (gs.foldl step w).getD j false =
        ((gs.map rename).foldl step v).getD (ren j) false := by
    induction gs generalizing w v with
    | nil => exact agree
    | cons g gs ih =>
      simp only [List.foldl_cons, List.map_cons]
      apply ih
      · simp only [step, List.length_append, List.length_cons, List.length_nil, len]
      · simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      · intro j
        have matchInputs :
            g.inputs.map (fun k => w.getD k false) =
              (g.inputs.map ren).map (fun k => v.getD k false) := by
          rw [List.map_map]
          exact List.map_congr_left (fun k _ => agree k)
        simp only [step, rename]
        rw [matchInputs]
        by_cases before : j < w.length
        · have after : ren j < v.length := by
            by_cases small : j < 9
            · have := renSmall j small
              omega
            · rw [renLarge j (by omega)]
              omega
          rw [List.getD_append _ _ _ _ before, List.getD_append _ _ _ _ after, agree]
        · rw [renLarge j (by omega)]
          rw [List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
  let D : Circuit := ⟨C.gates.map rename, ren C.output⟩
  have fanD : FanInTwo D := by
    intro g hg
    change g ∈ C.gates.map rename at hg
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
    obtain ⟨op, arity⟩ := fan q hq
    exact ⟨op, by simpa only [rename, List.length_map] using arity⟩
  have sizeD : D.size ≤ 13 := by
    change (C.gates.map rename).length ≤ 13
    simpa only [List.length_map] using (show C.gates.length ≤ 13 from budget)
  have readInput (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have transported (x : Fin 9 → Bool) :
      D.eval (List.ofFn x ++ [x 0 || x 4, x (π a) || x (π b)]) = f x := by
    let w := List.ofFn (flip x) ++ [flip x 0 || flip x 4, flip x a || flip x b]
    let v := List.ofFn x ++ [x 0 || x 4, x (π a) || x (π b)]
    have agree (j : ℕ) : w.getD j false = v.getD (ren j) false := by
      by_cases small : j < 9
      · let i : Fin 9 := ⟨j, small⟩
        change (List.ofFn (flip x) ++ [_ , _]).getD i.val false =
          (List.ofFn x ++ [_,_]).getD (π i).val false
        rw [List.getD_append _ _ _ _ (by simp),
            List.getD_append _ _ _ _ (by simp),
            readInput, readInput] <;> rfl
      · rw [renLarge j (by omega)]
        change (List.ofFn (flip x) ++ [flip x 0 || flip x 4, flip x a || flip x b]).getD j false =
          (List.ofFn x ++ [x 0 || x 4, x (π a) || x (π b)]).getD j false
        rw [List.getD_append_right _ _ _ _ (by simp; omega),
            List.getD_append_right _ _ _ _ (by simp; omega),
            List.length_ofFn, List.length_ofFn] <;> rfl
    have related : C.eval w = D.eval v := sim C.gates w v (by simp [w,v]) (by simp [w]) agree C.output
    change D.eval v = f x
    exact related.symm.trans ((computes (flip x)).trans (invariant x))
  let key (i j : Fin 9) := i.val * 10 + j.val
  let reps : List ℕ := [13,15,17,18,26,28,36,67]
  have coverage : ∀ i j : Fin 9, i ≠ 0 → i ≠ 4 → j ≠ 0 → j ≠ 4 → i ≠ j →
      key i j ∉ [12,21,23,32,16,61,27,72,38,83,57,75,68,86,58,85] →
      key i j ∈ reps ∨ key j i ∈ reps ∨ key (π i) (π j) ∈ reps ∨ key (π j) (π i) ∈ reps := by
    change ∀ i j : Fin 9, i ≠ 0 → i ≠ 4 → j ≠ 0 → j ≠ 4 → i ≠ j →
      key i j ∉ [12,21,23,32,16,61,27,72,38,83,57,75,68,86,58,85] →
      key i j ∈ reps ∨ key j i ∈ reps ∨ (ren i.val * 10 + ren j.val) ∈ reps ∨
        (ren j.val * 10 + ren i.val) ∈ reps
    decide
  have excluded (i j : Fin 9) (E : Circuit) (pt : key i j ∈ reps)
      (ef : FanInTwo E) (es : E.size ≤ 13)
      (ev : ∀ x : Fin 9 → Bool, E.eval (List.ofFn x ++ [x 0 || x 4, x i || x j]) = f x) : False := by
    change key i j ∈ [13,15,17,18] ++ [26,28,36,67] at pt
    rcases List.mem_append.mp pt with h | h
    · exact firstCases i j E h ef es ev
    · exact secondCases i j E h ef es ev
  rcases coverage a b a0 a4 b0 b4 distinct nonedge with h | h | h | h
  · exact excluded a b C h fan budget computes
  · exact excluded b a C h fan budget (fun x => by rw [Bool.or_comm (x b) (x a)]; exact computes x)
  · exact excluded (π a) (π b) D h fanD sizeD transported
  · exact excluded (π b) (π a) D h fanD sizeD
      (fun x => by rw [Bool.or_comm (x (π b)) (x (π a))]; exact transported x)
