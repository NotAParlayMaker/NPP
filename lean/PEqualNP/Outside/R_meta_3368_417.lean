import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_3368_417
    (ordinary : ∀ (C : Circuit), FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [false]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) → 15 ≤ C.size)
    (bothLive :
      let f (x : Fin 9 → Bool) := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),
        (1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
          (fun e => x e.1 && x e.2)
      let w (x : Fin 9 → Bool) := List.ofFn (Function.update x 4 false) ++
        [x 0 || x 4, x 4 || x 1]
      ∀ C : Circuit, FanInTwo C → C.size = 13 →
        C.output + 1 = 11 + C.size →
        (∀ i ∈ ([9,10] : List ℕ), ∃ g ∈ C.gates,
          i ∈ g.inputs ∧ (g.op ≠ GateOp.not ∨ g.inputs.head? = some i)) →
        ∃ x : Fin 9 → Bool, C.eval (w x) ≠ f x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (13 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn (Function.update x5 (4 : Fin (9 : ℕ)) Bool.false) ++ [x5 (0 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)), x5 (4 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ))]) = x1 x5) → False := by
  intro f C legal budget correct
  let w (x : Fin 9 → Bool) := List.ofFn (Function.update x 4 false) ++
    [x 0 || x 4, x 4 || x 1]
  let runGate (z : List Bool) (g : Gate) :=
    z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]
  have lengthW (x : Fin 9 → Bool) : (w x).length = 11 := by simp [w]
  let move (i : ℕ) := if i = 4 then 9 else if i < 9 then i else i + 1
  let rewire (g : Gate) : Gate := ⟨g.op, g.inputs.map move⟩
  let g0 : Gate := ⟨.or,[0,4]⟩
  let g1 : Gate := ⟨.or,[4,1]⟩
  let build (B : Circuit) : Circuit := ⟨g0 :: g1 :: B.gates.map rewire, move B.output⟩
  have dLegal (B : Circuit) (ok : FanInTwo B) : FanInTwo (build B) := by
    intro g hg
    change g ∈ g0 :: g1 :: B.gates.map rewire at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [g0]
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [g1]
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    exact ⟨(ok h hh).1, by simpa only [rewire, List.length_map] using (ok h hh).2⟩
  let full (x : Fin 9 → Bool) := (List.ofFn x ++ [false]) ++ [x 0 || x 4, x 4 || x 1]
  have prep (x : Fin 9 → Bool) : runGate (runGate (List.ofFn x ++ [false]) g0) g1 = full x := by
    let a := List.ofFn x ++ [false]
    have firstOr : runGate a g0 = a ++ [x 0 || x 4] := by
      change a ++ [(a.getD 0 false || (a.getD 4 false || false))] = _
      simp [a, List.getD_eq_getElem?_getD]
    rw [show runGate (List.ofFn x ++ [false]) g0 = _ from firstOr]
    let b := a ++ [x 0 || x 4]
    change b ++ [(b.getD 4 false || (b.getD 1 false || false))] = full x
    simp [b, a, full, List.getD_eq_getElem?_getD]
  have moveSmall (i : ℕ) (L : ℕ) (hL : 11 ≤ L) (hi : i < L) : move i < L + 1 := by
    dsimp only [move]
    split <;> (try split) <;> omega
  have moveLarge (i : ℕ) (hi : 9 ≤ i) : move i = i + 1 := by
    simp [move, show i ≠ 4 by omega, show ¬ i < 9 by omega]
  have inputEq (x : Fin 9 → Bool) (i : ℕ) : (full x).getD (move i) false = (w x).getD i false := by
    by_cases hi : i < 11
    · interval_cases i <;>
        simp [full, w, move, List.getD_eq_getElem?_getD]
    · rw [moveLarge _ (by omega), List.getD_eq_default, List.getD_eq_default]
      · rw [lengthW]; omega
      · simp [full]; omega
  have rewireMatches (gs : List Gate) (u v : List Bool) (len : v.length = u.length + 1)
      (base : 11 ≤ u.length) (eq : ∀ i, v.getD (move i) false = u.getD i false) :
      ∀ i, ((gs.map rewire).foldl runGate v).getD (move i) false =
        (gs.foldl runGate u).getD i false := by
    induction gs generalizing u v with
    | nil => exact eq
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp only [runGate, List.length_append, List.length_singleton, len]
      · simp only [runGate, List.length_append, List.length_singleton]; omega
      · have stepEq : (rewire g).op.eval ((rewire g).inputs.map fun i => v.getD i false) =
            g.op.eval (g.inputs.map fun i => u.getD i false) := by
          simp only [rewire, List.map_map, Function.comp_def, eq]
        intro i
        dsimp only [runGate]
        rw [stepEq]
        by_cases hi : i < u.length
        · have hj : move i < v.length := by rw [len]; exact moveSmall i _ base hi
          rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hi]
          exact eq i
        · rw [moveLarge _ (by omega), List.getD_append_right _ _ _ _ (by omega),
            List.getD_append_right _ _ _ _ (by omega), len, Nat.add_sub_add_right]
  have required (B : Circuit) (ok : FanInTwo B)
      (fits : ∀ x, B.eval (w x) = f x) : 13 ≤ B.size := by
    have spec (x : Fin 9 → Bool) : (build B).eval (List.ofFn x ++ [false]) = f x := by
      change ((B.gates.map rewire).foldl runGate (runGate (runGate _ g0) g1)).getD (move B.output) false = _
      rw [prep]
      have len : (full x).length = (w x).length + 1 := by simp [full, lengthW]
      exact (rewireMatches B.gates (w x) (full x) len (by rw [lengthW]) (inputEq x) B.output).trans (fits x)
    have fifteen := ordinary (build B) (dLegal B ok) (fun x => by
      simpa only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using spec x)
    have dSize : (build B).size = B.size + 2 := by
      change (g0 :: g1 :: B.gates.map rewire).length = B.gates.length + 2
      simp only [List.length_cons, List.length_map]
    omega
  have exactSize : C.size = 13 := by have bound := required C legal correct; omega
  let reads (g : Gate) (i : ℕ) := i ∈ g.inputs ∧ (g.op ≠ GateOp.not ∨ g.inputs.head? = some i)
  -- Each pair changes exactly one auxiliary wire and changes the graph output.
  have pinW (i : ℕ) (hi : i ∈ ([9,10] : List ℕ)) : ∃ x y : Fin 9 → Bool,
      f x ≠ f y ∧ ∀ j ≠ i, (w x).getD j false = (w y).getD j false := by
    have either : i = 9 ∨ i = 10 := by simpa using hi
    rcases either with rfl | rfl
    · let x : Fin 9 → Bool := fun j => j == 1 || j == 3
      let y : Fin 9 → Bool := fun j => j == 1 || j == 3 || j == 4
      refine ⟨x, y, by decide, ?_⟩
      intro j hj
      by_cases small : j < 11
      · interval_cases j <;> first | contradiction | rfl
      · rw [List.getD_eq_default _ _ (by rw [lengthW]; omega),
          List.getD_eq_default _ _ (by rw [lengthW]; omega)]
    · let x : Fin 9 → Bool := fun j => j == 0
      let y : Fin 9 → Bool := fun j => j == 0 || j == 4
      refine ⟨x, y, by decide, ?_⟩
      intro j hj
      by_cases small : j < 11
      · interval_cases j <;> first | contradiction | rfl
      · rw [List.getD_eq_default _ _ (by rw [lengthW]; omega),
          List.getD_eq_default _ _ (by rw [lengthW]; omega)]
  have preserves (gs : List Gate) (z : List Bool) (n : ℕ) (hn : n < z.length) :
      (gs.foldl runGate z).getD n false = z.getD n false := by
    induction gs generalizing z with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · exact List.getD_append _ _ _ _ hn
      · simp only [runGate, List.length_append, List.length_singleton]; omega
  have out (i k : ℕ) (hik : i ≠ k) (hi : i < 11) (hk : k ∈ ([9,10] : List ℕ)) :
      C.output ≠ i := by
    intro h
    obtain ⟨x,y,fx,agree⟩ := pinW k hk
    apply fx
    rw [← correct x, ← correct y]
    change (C.gates.foldl runGate (w x)).getD C.output false =
      (C.gates.foldl runGate (w y)).getD C.output false
    rw [h, preserves _ _ _ (by rw [lengthW]; exact hi),
      preserves _ _ _ (by rw [lengthW]; exact hi)]
    exact agree i hik
  have out9 := out 9 10 (by decide) (by decide) (by simp)
  have out10 := out 10 9 (by decide) (by decide) (by simp)
  -- A NOT gate can transmit a change only through its first operand.
  have live (i : ℕ) (hi : i ∈ ([9,10] : List ℕ)) : ∃ g ∈ C.gates, reads g i := by
    by_contra! absent
    have silence (gs : List Gate) (u v : List Bool) (len : u.length = v.length)
        (noneRead : ∀ g ∈ gs, ¬ reads g i) (eq : ∀ j ≠ i, u.getD j false = v.getD j false) :
        ∀ j ≠ i, (gs.foldl runGate u).getD j false = (gs.foldl runGate v).getD j false := by
      induction gs generalizing u v with
      | nil => exact eq
      | cons g gs ih =>
        simp only [List.foldl_cons]
        have same : g.op.eval (g.inputs.map fun j => u.getD j false) =
            g.op.eval (g.inputs.map fun j => v.getD j false) := by
          by_cases neg : g.op = GateOp.not
          · rw [neg]
            cases inp : g.inputs with
            | nil => rfl
            | cons j rest =>
              have nej : j ≠ i := by
                intro he
                apply noneRead g (by simp)
                refine ⟨by simp [inp, he], Or.inr (by simp [inp, he])⟩
              change (!(u.getD j false)) = (!(v.getD j false))
              rw [eq j nej]
          · have notMem : i ∉ g.inputs := fun hm => noneRead g (by simp) ⟨hm, Or.inl neg⟩
            congr 1
            exact List.map_congr_left (fun j hj => eq j (fun he => notMem (he ▸ hj)))
        apply ih
        · simp only [runGate, List.length_append, List.length_singleton, len]
        · exact fun h hh => noneRead h (List.mem_cons_of_mem _ hh)
        · intro j hj
          dsimp only [runGate]
          rw [same]
          by_cases low : j < u.length
          · rw [List.getD_append _ _ _ _ low, List.getD_append _ _ _ _ (by omega)]
            exact eq j hj
          · rw [List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    obtain ⟨x,y,fx,eq⟩ := pinW i hi
    have output : C.output ≠ i := by
      have either : i = 9 ∨ i = 10 := by simpa using hi
      rcases either with rfl | rfl
      · exact out9
      · exact out10
    apply fx
    rw [← correct x, ← correct y]
    exact silence C.gates (w x) (w y) (by rw [lengthW, lengthW]) absent eq C.output output
  have coreOutput : 11 ≤ C.output := by
    by_contra! bad
    by_cases h : C.output = 9
    · exact out9 h
    · exact out C.output 9 h bad (by simp) rfl
  have foldLength (gs : List Gate) (u : List Bool) :
      (gs.foldl runGate u).length = u.length + gs.length := by
    induction gs generalizing u with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, runGate, List.length_append, List.length_cons, List.length_nil]
      omega
  have validOutput : C.output < 11 + C.size := by
    by_contra! h
    have ev (x : Fin 9 → Bool) : C.eval (w x) = false := by
      change (C.gates.foldl runGate (w x)).getD C.output false = false
      apply List.getD_eq_default
      rw [foldLength, lengthW]
      exact h
    have different (x : Fin 9 → Bool) : f x = false := (correct x).symm.trans (ev x)
    obtain ⟨x,y,neq,_⟩ := pinW 9 (by simp)
    exact neq ((different x).trans (different y).symm)
  have lastOutput : C.output + 1 = 11 + C.size := by
    by_contra h
    let keep := C.output - 11 + 1
    have keepLt : keep < C.gates.length := by
      change C.output - 11 + 1 < C.size
      omega
    let B : Circuit := ⟨C.gates.take keep, C.output⟩
    have bLegal : FanInTwo B := fun g hg => legal g (List.mem_of_mem_take hg)
    have bCorrect (x : Fin 9 → Bool) : B.eval (w x) = f x := by
      rw [← correct x]
      change ((C.gates.take keep).foldl runGate (w x)).getD C.output false =
        (C.gates.foldl runGate (w x)).getD C.output false
      conv_rhs => rw [← List.take_append_drop keep C.gates, List.foldl_append]
      symm
      apply preserves
      rw [foldLength, lengthW, List.length_take, Nat.min_eq_left (Nat.le_of_lt keepLt)]
      omega
    have bBound := required B bLegal bCorrect
    change (C.gates.take keep).length ≥ 13 at bBound
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt keepLt)] at bBound
    change keep < C.size at keepLt
    omega
  obtain ⟨x,hx⟩ := bothLive C legal exactSize lastOutput live
  exact hx (correct x)
