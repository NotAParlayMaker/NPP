import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.R_meta_1890_734
    (cutoffs : ∀ (D : Circuit) (p : Fin 10 → Fin 10) (a b : ℕ), FanInTwo D →
      let W := fun (k : ℕ) (x : Fin 10 → Bool) =>
        (D.wires (List.ofFn (x ∘ p) ++ [x 0 && x 2])).getD k false
      let edge := fun x : Fin 10 → Bool =>
        let e := fun i j : Fin 10 => x i && x j
        e 0 1 || e 1 2 || e 2 3 || e 3 4 || e 4 0 || e 0 5 || e 1 6 || e 2 7 ||
          e 3 8 || e 4 9 || e 5 7 || e 7 9 || e 9 6 || e 6 8 || e 8 5
      ((∀ x, (W a x && W b x) = edge x) → 19 ≤ max a b) ∧
      ((∀ x, (W a x || W b x) = edge x) → 17 ≤ max a b))
    (andPrefix : ∀ (D : Circuit) (p : Fin 10 → Fin 10) (a b : ℕ),
      let W := fun (k : ℕ) (x : Fin 10 → Bool) =>
        (D.wires (List.ofFn (x ∘ p) ++ [x 0 && x 2])).getD k false
      let edge := fun x : Fin 10 → Bool =>
        let e := fun i j : Fin 10 => x i && x j
        e 0 1 || e 1 2 || e 2 3 || e 3 4 || e 4 0 || e 0 5 || e 1 6 || e 2 7 ||
          e 3 8 || e 4 9 || e 5 7 || e 7 9 || e 9 6 || e 6 8 || e 8 5
      FanInTwo D → D.size ≤ 17 → b ≤ a → 19 ≤ a → a < 11 + D.size →
      ∃ x, (W a x && W b x) ≠ edge x)
    (orPrefix : ∀ (D : Circuit) (p : Fin 10 → Fin 10) (a b : ℕ),
      let W := fun (k : ℕ) (x : Fin 10 → Bool) =>
        (D.wires (List.ofFn (x ∘ p) ++ [x 0 && x 2])).getD k false
      let edge := fun x : Fin 10 → Bool =>
        let e := fun i j : Fin 10 => x i && x j
        e 0 1 || e 1 2 || e 2 3 || e 3 4 || e 4 0 || e 0 5 || e 1 6 || e 2 7 ||
          e 3 8 || e 4 9 || e 5 7 || e 7 9 || e 9 6 || e 6 8 || e 8 5
      FanInTwo D → D.size ≤ 17 → b ≤ a → 17 ≤ a → a < 11 + D.size →
      ∃ x, (W a x || W b x) ≠ edge x)
    (notPrefix : ∀ (D : Circuit) (p : Fin 10 → Fin 10) (a : ℕ),
      let W := fun (k : ℕ) (x : Fin 10 → Bool) =>
        (D.wires (List.ofFn (x ∘ p) ++ [x 0 && x 2])).getD k false
      let edge := fun x : Fin 10 → Bool =>
        let e := fun i j : Fin 10 => x i && x j
        e 0 1 || e 1 2 || e 2 3 || e 3 4 || e 4 0 || e 0 5 || e 1 6 || e 2 7 ||
          e 3 8 || e 4 9 || e 5 7 || e 7 9 || e 9 6 || e 6 8 || e 8 5
      FanInTwo D → D.size ≤ 17 → a < 11 + D.size → ∃ x, (!W a x) ≠ edge x) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  classical
  let edge := fun x : Fin 10 → Bool =>
    let e := fun i j : Fin 10 => x i && x j
    e 0 1 || e 1 2 || e 2 3 || e 3 4 || e 4 0 || e 0 5 || e 1 6 || e 2 7 ||
      e 3 8 || e 4 9 || e 5 7 || e 7 9 || e 9 6 || e 6 8 || e 8 5
  let step := fun (v : List Bool) (g : Gate) =>
    v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)]
  have lengthRun (gs : List Gate) (v : List Bool) :
      (gs.foldl step v).length = v.length + gs.length := by
    induction gs generalizing v with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step, Nat.add_comm, Nat.add_left_comm]
  have preserved (gs : List Gate) (v : List Bool) (i : ℕ) (hi : i < v.length) :
      (gs.foldl step v).getD i false = v.getD i false := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step v g) (by simp [step]; omega)]
      simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have atEnd (v : List Bool) (b : Bool) : (v ++ [b]).getD v.length false = b := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl v.length)]
    simp
  intro C p fan size
  by_contra! correct
  let init (x : Fin 10 → Bool) := List.ofFn (x ∘ p) ++ [x 0 && x 2]
  have initLen (x : Fin 10 → Bool) : (init x).length = 11 := by simp [init]
  change ∀ x, C.eval (init x) = edge x at correct
  by_cases raw : C.output < 11
  · have same (x : Fin 10 → Bool) : (init x).getD C.output false = edge x := by
      have hh := correct x
      change (C.gates.foldl step (init x)).getD C.output false = edge x at hh
      rwa [preserved _ _ _ (by rw [initLen]; exact raw)] at hh
    by_cases v : C.output < 10
    · let i : Fin 10 := p ⟨C.output,v⟩
      let x := fun j : Fin 10 => decide (j = i)
      have h0 : ∀ i : Fin 10, edge (fun j => decide (j = i)) = false := by decide
      have h := (same x).trans (h0 i)
      have l : C.output < (List.ofFn (x ∘ p)).length := by simpa using v
      change (List.ofFn (x ∘ p) ++ [x 0 && x 2]).getD C.output false = false at h
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left l, List.getElem?_ofFn] at h
      simp only [v, dite_eq_left, Option.getD_some] at h
      change decide (i = i) = false at h
      simp at h
    · have ho : C.output = 10 := by omega
      let x := fun j : Fin 10 => decide (j = 0 ∨ j = 1)
      have h := same x
      rw [ho] at h
      have input : (init x).getD 10 false = false := by
        change (List.ofFn (x ∘ p) ++ [x 0 && x 2]).getD 10 false = false
        simp [x]
      have target : edge x = true := by decide
      rw [input, target] at h
      exact Bool.noConfusion h
  have valid : C.output < 11 + C.gates.length := by
    by_contra! bad
    have h := correct (fun _ => true)
    change (C.gates.foldl step _).getD C.output false = true at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [lengthRun, initLen]; exact bad)] at h
    exact Bool.noConfusion h
  let k := C.output - 11
  have hk : k < C.gates.length := by dsimp [k]; omega
  let gs := C.gates.take k
  let g := C.gates[k]
  let rest := C.gates.drop (k+1)
  have decomp : C.gates = gs ++ g :: rest := by
    change C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k+1)
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have idx : C.output = 11 + gs.length := by simp [gs, Nat.min_eq_left hk.le, k]; omega
  let D : Circuit := ⟨gs,0⟩
  have df : FanInTwo D := by
    intro t ht
    exact fan t (by rw [decomp]; exact List.mem_append_left _ ht)
  have ds : D.size ≤ 17 := by
    change gs.length ≤ 17
    change C.gates.length ≤ 18 at size
    rw [decomp, List.length_append, List.length_cons] at size
    omega
  let W := fun (a : ℕ) (x : Fin 10 → Bool) => (D.wires (init x)).getD a false
  have computed (x : Fin 10 → Bool) : g.op.eval (g.inputs.map fun a => W a x) = edge x := by
    let v := gs.foldl step (init x)
    have vl : v.length = 11+gs.length := by dsimp [v]; rw [lengthRun,initLen]
    have h := correct x
    change (C.gates.foldl step (init x)).getD C.output false = edge x at h
    rw [decomp, List.foldl_append, List.foldl_cons] at h
    change (rest.foldl step (step v g)).getD C.output false = edge x at h
    rw [preserved _ _ _ (by simp [step,idx,vl])] at h
    rw [idx, ← vl] at h
    change g.op.eval (g.inputs.map fun a => v.getD a false) = edge x
    simpa only [step, atEnd] using h
  have gm : g ∈ C.gates := by rw [decomp]; simp
  obtain ⟨ops,arity⟩ := fan g gm
  have absent (a : ℕ) (bad : ¬ a < 11 + D.size) (x) : W a x = false := by
    change (gs.foldl step (init x)).getD a false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [lengthRun,initLen]; exact Nat.le_of_not_lt bad)]
    rfl
  have ones : edge (fun _ => true) = true := by rfl
  have zeros : edge (fun _ => false) = false := by rfl
  have impossibleAnd (a b : ℕ) (h : ∀ x, (W a x && W b x) = edge x) : False := by
    have h1 := Bool.and_eq_true_iff.mp ((h (fun _ => true)).trans ones)
    have validA : a < 11 + D.size := by
      by_contra bad
      exact Bool.noConfusion ((absent a bad _).symm.trans h1.1)
    have validB : b < 11 + D.size := by
      by_contra bad
      exact Bool.noConfusion ((absent b bad _).symm.trans h1.2)
    have bound := (cutoffs D p a b df).1 h
    by_cases ab : b ≤ a
    · obtain ⟨x,hx⟩ := andPrefix D p a b df ds ab (by omega) validA
      exact hx (h x)
    · obtain ⟨x,hx⟩ := andPrefix D p b a df ds (by omega) (by omega) validB
      exact hx ((Bool.and_comm _ _).trans (h x))
  have impossibleCopy (a : ℕ) (h : ∀ x, W a x = edge x) : False :=
    impossibleAnd a a (fun x => by simp only [Bool.and_self,h x])
  have impossibleOr (a b : ℕ) (h : ∀ x, (W a x || W b x) = edge x) : False := by
    by_cases validA : a < 11 + D.size
    · by_cases validB : b < 11 + D.size
      · have bound := (cutoffs D p a b df).2 h
        by_cases ab : b ≤ a
        · obtain ⟨x,hx⟩ := orPrefix D p a b df ds ab (by omega) validA
          exact hx (h x)
        · obtain ⟨x,hx⟩ := orPrefix D p b a df ds (by omega) (by omega) validB
          exact hx ((Bool.or_comm _ _).trans (h x))
      · exact impossibleCopy a (fun x => by simpa only [absent b validB, Bool.or_false] using h x)
    · exact impossibleCopy b (fun x => by simpa only [absent a validA, Bool.false_or] using h x)
  have impossibleNot (a : ℕ) (h : ∀ x, (!W a x) = edge x) : False := by
    by_cases ok : a < 11 + D.size
    · obtain ⟨x,hx⟩ := notPrefix D p a df ds ok
      exact hx (h x)
    · have hx := (h (fun _ => false)).trans zeros
      rw [absent a ok] at hx
      exact Bool.noConfusion hx
  have ops' : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using ops
  have andNil : GateOp.and.eval [] = true := rfl
  have orNil : GateOp.or.eval [] = false := rfl
  have notNil : GateOp.not.eval [] = true := rfl
  have andOne (u : Bool) : GateOp.and.eval [u] = u := by cases u <;> rfl
  have orOne (u : Bool) : GateOp.or.eval [u] = u := by cases u <;> rfl
  have notOne (u : Bool) : GateOp.not.eval [u] = !u := rfl
  have andTwo (u v : Bool) : GateOp.and.eval [u,v] = (u && v) := by
    cases u <;> cases v <;> rfl
  have orTwo (u v : Bool) : GateOp.or.eval [u,v] = (u || v) := by
    cases u <;> cases v <;> rfl
  have notTwo (u v : Bool) : GateOp.not.eval [u,v] = !u := rfl
  cases pins : g.inputs with
  | nil =>
    obtain hop | hop | hop := ops'
    · exact Bool.noConfusion (show true = false by simpa only [pins,hop,List.map_nil,List.map_cons,andNil,orNil,notNil,andOne,orOne,notOne,andTwo,orTwo,notTwo] using (computed (fun _ => false)).trans zeros)
    · exact Bool.noConfusion (show false = true by simpa only [pins,hop,List.map_nil,List.map_cons,andNil,orNil,notNil,andOne,orOne,notOne,andTwo,orTwo,notTwo] using (computed (fun _ => true)).trans ones)
    · exact Bool.noConfusion (show true = false by simpa only [pins,hop,List.map_nil,List.map_cons,andNil,orNil,notNil,andOne,orOne,notOne,andTwo,orTwo,notTwo] using (computed (fun _ => false)).trans zeros)
  | cons a tail =>
    cases tail with
    | nil =>
      obtain hop | hop | hop := ops'
      · exact impossibleCopy a (fun x => by simpa only [pins,hop,List.map_nil,List.map_cons,andNil,orNil,notNil,andOne,orOne,notOne,andTwo,orTwo,notTwo] using computed x)
      · exact impossibleCopy a (fun x => by simpa only [pins,hop,List.map_nil,List.map_cons,andNil,orNil,notNil,andOne,orOne,notOne,andTwo,orTwo,notTwo] using computed x)
      · exact impossibleNot a (fun x => by simpa only [pins,hop,List.map_nil,List.map_cons,andNil,orNil,notNil,andOne,orOne,notOne,andTwo,orTwo,notTwo] using computed x)
    | cons b more =>
      have nilMore : more = [] := by
        rw [pins, List.length_cons, List.length_cons] at arity
        exact List.length_eq_zero_iff.mp (by omega)
      subst more
      obtain hop | hop | hop := ops'
      · exact impossibleAnd a b (fun x => by simpa only [pins,hop,List.map_nil,List.map_cons,andNil,orNil,notNil,andOne,orOne,notOne,andTwo,orTwo,notTwo] using computed x)
      · exact impossibleOr a b (fun x => by simpa only [pins,hop,List.map_nil,List.map_cons,andNil,orNil,notNil,andOne,orOne,notOne,andTwo,orTwo,notTwo] using computed x)
      · exact impossibleNot a (fun x => by simpa only [pins,hop,List.map_nil,List.map_cons,andNil,orNil,notNil,andOne,orOne,notOne,andTwo,orTwo,notTwo] using computed x)
