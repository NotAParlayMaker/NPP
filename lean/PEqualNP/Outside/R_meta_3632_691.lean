import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2800000 in
theorem PEqualNP.Outside.R_meta_3632_691
    (sharedZero :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (r : Fin 9) (C : Circuit), r.val ∈ ([1,2,3,6] : List ℕ) → FanInTwo C → C.size = 13 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x 0 || x r]) = f x) → False)
    (sharedFour :
      let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (r : Fin 9) (C : Circuit), r.val ∈ ([1,2,3,6] : List ℕ) → FanInTwo C → C.size = 13 →
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x 4 || x r]) = f x) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Finset (Fin (9 : ℕ))), PEqualNP.MetaComplexity.FanInTwo x1 → x2.card = (2 : ℕ) → x2 ≠ {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → ¬Disjoint x2 {(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))} → x1.size = (13 : ℕ) → (∀ (x8 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), Decidable.decide (∃ x9 ∈ x2, x8 x9 = Bool.true)]) = [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x9 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x9.1 && x8 x9.2) → False := by
  intro C T fan card ne overlap budget correct
  obtain ⟨p, pT, special⟩ := Finset.not_disjoint_iff.mp overlap
  have hp : p = 0 ∨ p = 4 := by simpa only [Finset.mem_insert, Finset.mem_singleton] using special
  obtain ⟨r,rp,pair⟩ : ∃ r : Fin 9, r ≠ p ∧ T = {p,r} := by
    obtain ⟨i,j,ij,h⟩ := Finset.card_eq_two.mp card
    rw [h] at pT
    simp only [Finset.mem_insert, Finset.mem_singleton] at pT
    rcases pT with hi | hj
    · exact ⟨j, by simpa only [hi] using ij.symm, by simpa only [hi] using h⟩
    · exact ⟨i, by simpa only [hj] using ij, by simpa only [hj] using h.trans (Finset.pair_comm i j)⟩
  have r0 : r ≠ 0 := by
    intro eq
    subst r
    rcases hp with h | h
    · exact rp h.symm
    · exact ne (pair.trans (by rw [h,Finset.pair_comm]))
  have r4 : r ≠ 4 := by
    intro eq
    subst r
    rcases hp with h | h
    · exact ne (pair.trans (by rw [h]))
    · exact rp h.symm
  let f (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have computes (x : Fin 9 → Bool) : C.eval (List.ofFn x ++ [x 0 || x 4, x p || x r]) = f x := by
    have bit : decide (∃ i ∈ T, x i = true) = (x p || x r) := by
      cases h : x p <;> cases k : x r <;> simp [pair,h,k]
    rw [← bit]
    exact correct x
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
  have sizeD : D.size = 13 := by
    change (C.gates.map rename).length = 13
    simpa only [List.length_map] using (show C.gates.length = 13 from budget)
  have readInput (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have fixed : π p = p := by
    rcases hp with h | h <;> rw [h] <;> rfl
  have transported (x : Fin 9 → Bool) :
      D.eval (List.ofFn x ++ [x 0 || x 4, x p || x (π r)]) = f x := by
    let w := List.ofFn (flip x) ++ [flip x 0 || flip x 4, flip x p || flip x r]
    let v := List.ofFn x ++ [x 0 || x 4, x p || x (π r)]
    have agree (j : ℕ) : w.getD j false = v.getD (ren j) false := by
      by_cases small : j < 9
      · let i : Fin 9 := ⟨j, small⟩
        change (List.ofFn (flip x) ++ [_ , _]).getD i.val false =
          (List.ofFn x ++ [_,_]).getD (π i).val false
        rw [List.getD_append _ _ _ _ (by simp),
            List.getD_append _ _ _ _ (by simp),
            readInput, readInput] <;> rfl
      · rw [renLarge j (by omega)]
        change (List.ofFn (flip x) ++ [flip x 0 || flip x 4, flip x p || flip x r]).getD j false =
          (List.ofFn x ++ [x 0 || x 4, x p || x (π r)]).getD j false
        rw [List.getD_append_right _ _ _ _ (by simp; omega),
            List.getD_append_right _ _ _ _ (by simp; omega),
            List.length_ofFn, List.length_ofFn]
        change [x (π 0) || x (π 4), x (π p) || x (π r)].getD (j-9) false =
          [x 0 || x 4, x p || x (π r)].getD (j-9) false
        rw [fixed] <;> rfl
    have related : C.eval w = D.eval v := sim C.gates w v (by simp [w,v]) (by simp [w]) agree C.output
    change D.eval v = f x
    exact related.symm.trans ((computes (flip x)).trans (invariant x))
  have coverage : ∀ i : Fin 9, i ≠ 0 → i ≠ 4 →
      i.val ∈ ([1,2,3,6] : List ℕ) ∨ ren i.val ∈ ([1,2,3,6] : List ℕ) := by decide
  have exclude (P R : Fin 9) (E : Circuit) (hs : P = 0 ∨ P = 4)
      (hr : R.val ∈ ([1,2,3,6] : List ℕ)) (ef : FanInTwo E) (es : E.size = 13)
      (ev : ∀ x, E.eval (List.ofFn x ++ [x 0 || x 4, x P || x R]) = f x) : False := by
    rcases hs with rfl | rfl
    · exact sharedZero R E hr ef es ev
    · exact sharedFour R E hr ef es ev
  rcases coverage r r0 r4 with h | h
  · exact exclude p r C hp h fan budget computes
  · exact exclude p (π r) D hp h fanD sizeD transported
