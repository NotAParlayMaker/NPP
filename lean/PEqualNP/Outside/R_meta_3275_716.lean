import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first three premises are L_meta_2012, L_meta_1667 and L_meta_1671.
set_option maxRecDepth 5000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3275_716
    (lower : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (edgeLower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (nonedgeLower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size)
    (residual : ∀ (a b : Fin 9) (C : Circuit), a.val * 10 + b.val ∈ ([2,3,4,13,15,16,18,27,28,34,46,67] : List ℕ) →
      FanInTwo C → C.size = 13 → ∃ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [!x 0, x a && x b]) ≠ ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
    ∀ x1 ∈ [((0 : Fin (12 : ℕ)), (1 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((0 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (2 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (5 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ))), ((1 : Fin (12 : ℕ)), (8 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (3 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ))), ((2 : Fin (12 : ℕ)), (8 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (4 : Fin (12 : ℕ))), ((3 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((4 : Fin (12 : ℕ)), (6 : Fin (12 : ℕ))), ((6 : Fin (12 : ℕ)), (7 : Fin (12 : ℕ)))],   ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x6 : Fin (9 : ℕ) → Bool),           have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];           have x8 : Fin (12 : ℕ) → Bool := fun (x8 : Fin (12 : ℕ)) => if x8 = (11 : Fin (12 : ℕ)) then Bool.true else x7.getD (↑x8) Bool.false;           x3.eval (x7 ++ [x8 x1.1 && x8 x1.2]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro p hp C fan size
  classical
  let f (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let edgeFun (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  have sameTarget (x : Fin 9 → Bool) : f x = edgeFun x := by
    simp only [f, edgeFun, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  let label (q : Fin 12 × Fin 12) : ℕ := q.1.val * 10 + q.2.val
  let perm (k : ℕ) : Fin 9 → Fin 9 :=
    if k = 12 then ![2,1,0,5,7,3,6,4,8] else
    if k = 14 then ![1,0,5,8,6,2,4,7,3] else
    if k = 17 then ![5,0,1,2,7,8,4,6,3] else
    if k = 23 then ![3,2,1,0,4,8,7,6,5] else
    if k = 24 then ![8,5,0,1,6,3,7,4,2] else
    if k = 26 then ![2,1,0,5,7,3,6,4,8] else
    if k = 36 then ![3,8,5,0,4,2,6,7,1] else
    id
  let per := perm (label p)
  let a := Fin.ofNat 9 p.1.val
  let b := Fin.ofNat 9 p.2.val
  have classified : ∀ q ∈ ([(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3),(2,4),(2,6),(2,7),(2,8),(3,4),(3,6),(4,6),(6,7)] : List (Fin 12 × Fin 12)),
      q.1.val < 9 ∧ q.2.val < 9 ∧
      ((Fin.ofNat 9 q.1.val).val * 10 + (Fin.ofNat 9 q.2.val).val ∈ ([2,3,4,13,15,16,18,27,28,34,46,67] : List ℕ) ∨
        let u := perm (label q) (Fin.ofNat 9 q.1.val)
        let v := perm (label q) (Fin.ofNat 9 q.2.val)
        (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 0 ∧ v = 6) ∨ (u = 6 ∧ v = 0)) := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨ha,hb,branch⟩ := classified p hp
  have sym (x : Fin 9 → Bool) : f (x ∘ per) = f x := by
    unfold per perm
    split_ifs
    · change (x 2 && x 1 || x 1 && x 0 || x 0 && x 5 || x 5 && x 7 || x 7 && x 2 || x 2 && x 3 || x 1 && x 6 || x 0 && x 4 || x 5 && x 8 || x 3 && x 4 || x 6 && x 8 || x 8 && x 3) = f x
      simp only [f, Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
    · change (x 1 && x 0 || x 0 && x 5 || x 5 && x 8 || x 8 && x 6 || x 6 && x 1 || x 1 && x 2 || x 0 && x 4 || x 5 && x 7 || x 8 && x 3 || x 2 && x 7 || x 4 && x 3 || x 3 && x 2) = f x
      simp only [f, Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
    · change (x 5 && x 0 || x 0 && x 1 || x 1 && x 2 || x 2 && x 7 || x 7 && x 5 || x 5 && x 8 || x 0 && x 4 || x 1 && x 6 || x 2 && x 3 || x 8 && x 6 || x 4 && x 3 || x 3 && x 8) = f x
      simp only [f, Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
    · change (x 3 && x 2 || x 2 && x 1 || x 1 && x 0 || x 0 && x 4 || x 4 && x 3 || x 3 && x 8 || x 2 && x 7 || x 1 && x 6 || x 0 && x 5 || x 8 && x 6 || x 7 && x 5 || x 5 && x 8) = f x
      simp only [f, Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
    · change (x 8 && x 5 || x 5 && x 0 || x 0 && x 1 || x 1 && x 6 || x 6 && x 8 || x 8 && x 3 || x 5 && x 7 || x 0 && x 4 || x 1 && x 2 || x 3 && x 4 || x 7 && x 2 || x 2 && x 3) = f x
      simp only [f, Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
    · change (x 2 && x 1 || x 1 && x 0 || x 0 && x 5 || x 5 && x 7 || x 7 && x 2 || x 2 && x 3 || x 1 && x 6 || x 0 && x 4 || x 5 && x 8 || x 3 && x 4 || x 6 && x 8 || x 8 && x 3) = f x
      simp only [f, Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
    · change (x 3 && x 8 || x 8 && x 5 || x 5 && x 0 || x 0 && x 4 || x 4 && x 3 || x 3 && x 2 || x 8 && x 6 || x 5 && x 7 || x 0 && x 1 || x 2 && x 7 || x 6 && x 1 || x 1 && x 2) = f x
      simp only [f, Bool.and_comm, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
    · rfl
  let inp (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0, x a && x b]
  have raw (x : Fin 9 → Bool) (i : Fin 12) (hi : i.val < 9) :
      (if i = 11 then true else (List.ofFn x ++ [!x 0]).getD i.val false) =
        x (Fin.ofNat 9 i.val) := by
    have ni : i ≠ 11 := by
      intro h
      subst i
      omega
    let j := Fin.ofNat 9 i.val
    have jv : j.val = i.val := Nat.mod_eq_of_lt hi
    have readJ : (List.ofFn x).getD j.val false = x j := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    rw [ite_eq_right ni, List.getD_append _ _ _ _ (by simpa using hi)]
    exact (congrArg (fun k => (List.ofFn x).getD k false) jv.symm).trans readJ
  have original (x : Fin 9 → Bool) :
      (let rows := List.ofFn x ++ [!x 0]
       let read := fun i : Fin 12 => if i = 11 then true else rows.getD i.val false
       rows ++ [read p.1 && read p.2]) = inp x := by
    dsimp only
    rw [raw x p.1 ha, raw x p.2 hb, List.append_assoc]
    rfl
  by_contra! good
  have computes (x : Fin 9 → Bool) : C.eval (inp x) = f x := by
    have e := Classical.byContradiction (good x)
    rw [original] at e
    exact e
  let swap (i : ℕ) := if h : i < 9 then (per ⟨i,h⟩).val
    else if i = 9 then 10 else if i = 10 then 9 else i
  have mapValue (i : ℕ) (h : i < 9) : swap i = (per ⟨i,h⟩).val := by
    simp only [swap, dite_eq_left h]
  have mappedSmall (i : ℕ) (h : i < 9) : swap i < 9 := by
    rw [mapValue i h]
    exact (per ⟨i,h⟩).isLt
  have mapNine : swap 9 = 10 := rfl
  have mapTen : swap 10 = 9 := rfl
  have fixed (i : ℕ) (h : 11 ≤ i) : swap i = i := by
    unfold swap
    split_ifs <;> omega
  let first : Gate := ⟨.and,[(per a).val,(per b).val]⟩
  let neg : Gate := ⟨.not,[(per 0).val]⟩
  let rename (g : Gate) : Gate := ⟨g.op,g.inputs.map swap⟩
  let D : Circuit := ⟨first :: neg :: C.gates.map rename, swap C.output⟩
  have fanD : FanInTwo D := by
    intro g hg
    change g ∈ first :: neg :: C.gates.map rename at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inl rfl, by
        change (2 : ℕ) ≤ 2
        exact le_rfl⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨Or.inr (Or.inr rfl), by
        change (1 : ℕ) ≤ 2
        decide⟩
    obtain ⟨originalGate,hOriginal,rfl⟩ := List.mem_map.mp hg
    exact ⟨(fan originalGate hOriginal).1, by simpa only [rename,List.length_map] using (fan originalGate hOriginal).2⟩
  have lenD : D.size = C.size + 2 := by
    change (first :: neg :: C.gates.map rename).length = C.gates.length + 2
    simp only [List.length_cons,List.length_map]
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have inputRead (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  let new (x : Fin 9 → Bool) := List.ofFn x ++ [x (per a) && x (per b), !x (per 0)]
  have step1 (x : Fin 9 → Bool) :
      step (List.ofFn x) first = List.ofFn x ++ [x (per a) && x (per b)] := by
    change List.ofFn x ++ [[(List.ofFn x).getD (per a).val false,
      (List.ofFn x).getD (per b).val false].all id] = _
    rw [inputRead,inputRead]
    simp only [List.all_cons,List.all_nil,id,Bool.and_true]
  have step2 (x : Fin 9 → Bool) :
      step (step (List.ofFn x) first) neg = new x := by
    rw [step1]
    change (List.ofFn x ++ [x (per a) && x (per b)]) ++
      [!((List.ofFn x ++ [x (per a) && x (per b)]).getD (per 0).val false)] = _
    rw [List.getD_append _ _ _ _ (by simp), inputRead, List.append_assoc]
    rfl
  have retain (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g)]
      · exact List.getD_append _ _ _ _ h
      · simp only [step,List.length_append,List.length_singleton]
        omega
  have firstWire (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false =
      (x (per a) && x (per b)) := by
    change ((C.gates.map rename).foldl step (step (step (List.ofFn x) first) neg)).getD 9 false = _
    rw [step2, retain _ _ _ (by simp [new])]
    change (List.ofFn x ++ [x (per a) && x (per b), !x (per 0)]).getD 9 false = _
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn]
    rfl
  have last (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    rfl
  have old (w : List Bool) (v : Bool) (i : ℕ) (h : i ≠ w.length) :
      (w ++ [v]).getD i false = w.getD i false := by
    by_cases hi : i < w.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have simulates (gs : List Gate) (w z : List Bool) (len : w.length = z.length)
      (enough : 11 ≤ w.length) (eq : ∀ i, w.getD i false = z.getD (swap i) false) :
      ∀ i, (gs.foldl step w).getD i false =
        ((gs.map rename).foldl step z).getD (swap i) false := by
    induction gs generalizing w z with
    | nil => exact eq
    | cons g gs ih =>
      simp only [List.map_cons,List.foldl_cons]
      apply ih
      · simp only [step,List.length_append,List.length_singleton,len]
      · simp only [step,List.length_append,List.length_singleton]
        omega
      intro i
      have pins : g.inputs.map (fun j => w.getD j false) =
          (g.inputs.map swap).map (fun j => z.getD j false) := by
        rw [List.map_map]
        exact List.map_congr_left (fun j _ => eq j)
      by_cases hi : i = w.length
      · rw [hi, fixed _ enough]
        conv_rhs => rw [len]
        simp only [step,rename,last]
        rw [pins]
      · have hj : swap i ≠ z.length := by
          by_cases hs : i < 9
          · have hmap := mappedSmall i hs
            omega
          · unfold swap
            rw [dite_eq_right hs]
            split_ifs <;> omega
        simp only [step,rename]
        rw [old _ _ _ hi, old _ _ _ hj, eq]
  have seeds (x : Fin 9 → Bool) (i : ℕ) :
      (inp (x ∘ per)).getD i false = (new x).getD (swap i) false := by
    by_cases hi : i < 9
    · have ri := mappedSmall i hi
      change (List.ofFn (x ∘ per) ++ [_ , _]).getD i false = (List.ofFn x ++ [_ , _]).getD (swap i) false
      rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_append _ _ _ _ (by simpa using ri)]
      change (List.ofFn (x ∘ per)).getD (⟨i,hi⟩ : Fin 9).val false = _
      rw [inputRead,mapValue i hi,inputRead]
      rfl
    · by_cases high : 11 ≤ i
      · rw [fixed i high, List.getD_eq_default _ _ (by simpa [inp] using high),
          List.getD_eq_default _ _ (by simpa [new] using high)]
      · have e : i = 9 ∨ i = 10 := by omega
        rcases e with rfl | rfl <;>
          simp only [inp,new,mapNine,mapTen] <;>
          rw [List.getD_append_right _ _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)] <;>
          rfl
  have evalD : circuitFun 9 D = f := by
    funext x
    change ((C.gates.map rename).foldl step (step (step (List.ofFn x) first) neg)).getD
      (swap C.output) false = f x
    rw [step2, ← simulates C.gates (inp (x ∘ per)) (new x)
      (by simp [inp,new]) (by simp [inp]) (seeds x)]
    change C.eval (inp (x ∘ per)) = f x
    rw [computes,sym]
  by_cases small : C.size ≤ 12
  · apply lower
    exact ⟨D,fanD,by omega,fun x => (congrFun evalD x).trans (sameTarget x)⟩
  rcases branch with rest | key
  · obtain ⟨x,ne⟩ := residual a b C rest fan (by omega)
    exact ne ((computes x).trans (sameTarget x))
  · have keys : (per a = 0 ∧ per b = 1) ∨ (per a = 1 ∧ per b = 0) ∨
          (per a = 0 ∧ per b = 6) ∨ (per a = 6 ∧ per b = 0) := key
    have bound : 16 ≤ D.size := by
      rcases keys with h | h | h | h
      · exact edgeLower D fanD (fun x => by rw [firstWire,h.1,h.2]) evalD
      · exact edgeLower D fanD (fun x => by rw [firstWire,h.1,h.2,Bool.and_comm]) evalD
      · exact nonedgeLower D fanD (fun x => by rw [firstWire,h.1,h.2]) evalD
      · exact nonedgeLower D fanD (fun x => by rw [firstWire,h.1,h.2,Bool.and_comm]) evalD
    omega
