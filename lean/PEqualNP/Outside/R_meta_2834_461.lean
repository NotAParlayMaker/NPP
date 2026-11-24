import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_2834_461
    (floor15 : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) → 15 ≤ D.size)
    (threeExtra : ∀ (a b : Fin 9), a < b → a ≠ 0 → a ≠ 4 → b ≠ 0 → b ≠ 4 →
      ∀ C : Circuit, FanInTwo C → C.size = 13 →
        (∀ k < 24, k ∈ C.output :: C.gates.flatMap Gate.inputs) →
        (C.output :: C.gates.flatMap Gate.inputs).length ≤ 27 →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [x 0 || x 4, x a || x b]) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (13 : ℕ) → (∀ (x11 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)), x11 x1 || x11 x2]) = (x11 (0 : Fin (9 : ℕ)) && x11 (1 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (2 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (3 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (4 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ)) && x11 (0 : Fin (9 : ℕ)) || x11 (0 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ)) && x11 (6 : Fin (9 : ℕ)) || x11 (2 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (3 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (5 : Fin (9 : ℕ)) && x11 (7 : Fin (9 : ℕ)) || x11 (6 : Fin (9 : ℕ)) && x11 (8 : Fin (9 : ℕ)) || x11 (8 : Fin (9 : ℕ)) && x11 (5 : Fin (9 : ℕ)))) → False := by
  intro a b C ha0 ha4 hb0 hb4 hab fan budget computes
  classical
  have prune (n : ℕ) (D : Circuit) (j : Fin D.gates.length) (fanD : FanInTwo D)
      (missing : n + j.val ∉ D.output :: D.gates.flatMap Gate.inputs) :
      ∃ E : Circuit, FanInTwo E ∧ E.size < D.size ∧
        ∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x) := by
    let t := n+j.val
    let f (i : ℕ) := if i<t then i else i-1
    let rg (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩
    let step (u : List Bool) (g : Gate) := u ++ [g.op.eval (g.inputs.map fun z => u.getD z false)]
    let pre := D.gates.take j.val
    let post := D.gates.drop (j.val+1)
    let E : Circuit := ⟨pre ++ post.map rg, f D.output⟩
    have splitD : D.gates = pre ++ D.gates[j.val] :: post := by
      symm
      change D.gates.take j.val ++ D.gates[j.val] :: D.gates.drop (j.val+1) = D.gates
      rw [List.getElem_cons_drop j.isLt, List.take_append_drop]
    have fresh (g : Gate) (hg : g ∈ post) : t ∉ g.inputs := by
      intro h
      exact missing (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨g, List.mem_of_mem_drop hg, h⟩))
    have out : D.output ≠ t := fun eq => missing (List.mem_cons.mpr (Or.inl eq.symm))
    refine ⟨E, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact fanD g (List.mem_of_mem_take h)
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
        obtain ⟨op,arity⟩ := fanD v (List.mem_of_mem_drop hv)
        exact ⟨op, by simpa [rg] using arity⟩
    · change (pre ++ post.map rg).length < D.gates.length
      rw [splitD]
      simp
    · intro x
      let u := pre.foldl step (List.ofFn x)
      have lengthFold (gs : List Gate) (xs : List Bool) :
          (gs.foldl step xs).length = xs.length + gs.length := by
        induction gs generalizing xs with
        | nil => simp
        | cons g gs ih =>
          rw [List.foldl_cons,ih]
          simp [step]
          omega
      have lenu : u.length = t := by
        simp [u,lengthFold,pre,t]
      have snoc (xs : List Bool) (b : Bool) (i : ℕ) :
          (xs ++ [b]).getD i false = if i < xs.length then xs.getD i false else
            if i=xs.length then b else false := by
        simp only [List.getD_eq_getElem?_getD]
        split_ifs with h he
        · rw [List.getElem?_append_left h]
        · subst he; simp
        · rw [List.getElem?_eq_none (by simp; omega)]
          rfl
      have recRun (gs : List Gate) (xs ys : List Bool)
          (no : ∀ g ∈ gs, t ∉ g.inputs) (short : t < ys.length)
          (lens : xs.length + 1 = ys.length)
          (rel : ∀ i, i ≠ t → xs.getD (f i) false = ys.getD i false) :
          ∀ i, i ≠ t → ((gs.map rg).foldl step xs).getD (f i) false =
            (gs.foldl step ys).getD i false := by
        induction gs generalizing xs ys with
        | nil => exact rel
        | cons g gs ih =>
          have vals : (g.inputs.map f).map (fun i => xs.getD i false) =
              g.inputs.map (fun i => ys.getD i false) := by
            rw [List.map_map]
            exact List.map_congr_left (fun i hi => rel i (fun e => no g List.mem_cons_self (e ▸ hi)))
          have newEq : step xs (rg g) = xs ++ [g.op.eval (g.inputs.map fun i => ys.getD i false)] := by
            change xs ++ [g.op.eval ((g.inputs.map f).map _)] = _
            rw [vals]
          simp only [List.map_cons,List.foldl_cons,newEq]
          apply ih _ _ (fun g' hg' => no g' (List.mem_cons_of_mem _ hg')) (by simp [step]; omega)
            (by simp [step]; omega)
          intro i unequal
          have below : (f i < xs.length) ↔ i < ys.length := by unfold f; split <;> omega
          have atEnd : (f i = xs.length) ↔ i = ys.length := by unfold f; split <;> omega
          rw [snoc]
          unfold step
          rw [snoc]
          simp only [below, atEnd, rel i unequal]
      have base (i : ℕ) (ne : i ≠ t) :
          u.getD (f i) false = (step u D.gates[j.val]).getD i false := by
        unfold step
        rw [snoc,lenu]
        by_cases before : i<t
        · simp [f,before]
        · have past : u.length ≤ f i := by simp [f,before,lenu]; omega
          simp only [ite_eq_right before, ite_eq_right ne]
          exact List.getD_eq_default _ _ past
      have finalEq := recRun post u (step u D.gates[j.val]) fresh (by simp [step,lenu])
        (by simp [step]) base D.output out
      change ((pre ++ post.map rg).foldl step (List.ofFn x)).getD (f D.output) false =
        (D.gates.foldl step (List.ofFn x)).getD D.output false
      rw [splitD,List.foldl_append,List.foldl_append,List.foldl_cons]
      exact finalEq
  let target := fun (x : Fin 9 → Bool) => ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
  let enc := fun (x : Fin 9 → Bool) => List.ofFn x ++ [x 0 || x 4, x a || x b]
  let g₁ : Gate := ⟨.or,[0,4]⟩
  let g₂ : Gate := ⟨.or,[a.val,b.val]⟩
  let D : Circuit := ⟨g₁ :: g₂ :: C.gates, C.output⟩
  have df : FanInTwo D := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hh
    · simp [g₁]
    rcases List.mem_cons.mp hh with rfl | hh
    · simp [g₂]
    exact fan g hh
  have dc (x : Fin 9 → Bool) : D.eval (List.ofFn x) = target x := by
    let bits := List.ofFn x
    let val₁ := g₁.op.eval (g₁.inputs.map fun i => bits.getD i false)
    have rd (i : Fin 9) : bits.getD i.val false = x i := by
      rw [List.getD_eq_getElem _ _ (by simp [bits])]
      exact List.getElem_ofFn _
    have e₁ : val₁ = (x 0 || x 4) := by
      change (bits.getD 0 false || (bits.getD 4 false || false)) = _
      have r0 : bits.getD 0 false = x 0 := rd 0
      have r4 : bits.getD 4 false = x 4 := rd 4
      rw [r0,r4,Bool.or_false]
    have rd₂ (i : Fin 9) : (bits ++ [val₁]).getD i.val false = x i := by
      rw [List.getD_append _ _ _ _ (by simp [bits]), rd]
    change C.eval ((bits ++ [val₁]) ++ [g₂.op.eval (g₂.inputs.map fun i => (bits ++ [val₁]).getD i false)]) = _
    change C.eval ((bits ++ [val₁]) ++ [(bits ++ [val₁]).getD a.val false ||
      ((bits ++ [val₁]).getD b.val false || false)]) = _
    rw [Bool.or_false]
    rw [rd₂ a, rd₂ b, e₁, List.append_assoc]
    change C.eval (List.ofFn x ++ [x 0 || x 4,x a || x b]) = target x
    exact computes x
  have hd := floor15 D df dc
  have sizes : D.size = C.size + 2 := by
    change (g₁ :: g₂ :: C.gates).length = C.gates.length + 2
    simp
  have exactSize : C.size = 13 := by omega
  let refs := C.output :: C.gates.flatMap Gate.inputs
  have live (k : ℕ) (lo : 9 ≤ k) (hi : k < 24) : k ∈ refs := by
    by_contra missing
    have hk : k-9 < D.gates.length := by change k-9 < D.size; omega
    have missingD : 9 + (k-9) ∉ D.output :: D.gates.flatMap Gate.inputs := by
      have sub : 9 + (k-9) = k := by omega
      have ha : a.val < 9 := a.isLt
      have hb : b.val < 9 := b.isLt
      rw [sub]
      change k ∉ C.output :: ([0,4] ++ ([a.val,b.val] ++ C.gates.flatMap Gate.inputs))
      simp only [refs,List.mem_cons, not_or] at missing
      simp only [List.mem_cons,List.cons_append,List.nil_append,not_or]
      exact ⟨missing.1, by omega, by omega, by omega, by omega, missing.2⟩
    obtain ⟨E,ef,es,ee⟩ := prune 9 D ⟨_, hk⟩ df missingD
    have := floor15 E ef (fun x => (ee x).trans (dc x))
    omega
  have stable (k : ℕ) (gs : List Gate) (u v : List Bool)
      (hl : u.length = v.length) (hn : ∀ g ∈ gs, k ∉ g.inputs)
      (same : ∀ i, i ≠ k → u.getD i false = v.getD i false) :
      ∀ o, o ≠ k → (Circuit.mk gs o).eval u = (Circuit.mk gs o).eval v := by
    induction gs generalizing u v with
    | nil => exact same
    | cons g gs ih =>
      have hv := List.map_congr_left (l := g.inputs) (fun i hi => same i (by
        intro he; exact hn g List.mem_cons_self (he ▸ hi)))
      let t := g.op.eval (g.inputs.map fun i => u.getD i false)
      have tg : g.op.eval (g.inputs.map fun i => v.getD i false) = t := (congrArg g.op.eval hv).symm
      intro o ho
      change (Circuit.mk gs o).eval (u ++ [t]) =
        (Circuit.mk gs o).eval (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
      rw [tg]
      apply ih (u ++ [t]) (v ++ [t]) (by simp [hl]) (fun z hz => hn z (List.mem_cons_of_mem g hz)) _ o ho
      intro i hi
      by_cases small : i < u.length
      · rw [List.getD_append _ _ _ _ small, List.getD_append _ _ _ _ (by omega), same i hi]
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : u.length ≤ i),
          List.getElem?_append_right (by omega : v.length ≤ i), hl]
  let mate (p q v : Fin 9) : Fin 9 :=
    if v=0 then 4 else if v=4 then 0 else if v=p then q else if v=q then p else v
  let low (p q v w i : Fin 9) := decide (i ≠ v ∧ (i = mate p q v ∨ i = w))
  let high (p q v w i : Fin 9) := decide (i=v) || low p q v w i
  have witnesses : ∀ p q v : Fin 9, p ≠ 0 → p ≠ 4 → q ≠ 0 → q ≠ 4 → p ≠ q →
      ∃ w : Fin 9, let x := low p q v w; let y := high p q v w
        target x ≠ target y ∧ (x 0 || x 4) = (y 0 || y 4) ∧ (x p || x q) = (y p || y q) := by
    decide +kernel
  have covered (k : ℕ) (hk : k < 24) : k ∈ refs := by
    by_cases hi : k < 9
    · let v : Fin 9 := ⟨k,hi⟩
      obtain ⟨w, diff, same₁, same₂⟩ := witnesses a b v ha0 ha4 hb0 hb4 hab
      let x := low a b v w
      let y := high a b v w
      by_contra nope
      have hno : k ≠ C.output ∧ k ∉ C.gates.flatMap Gate.inputs := by simpa [refs] using nope
      have agree (i : ℕ) (h : i ≠ k) : (enc x).getD i false = (enc y).getD i false := by
        by_cases small : i < 9
        · let j : Fin 9 := ⟨i,small⟩
          have ne : j ≠ v := fun e => h (congrArg Fin.val e)
          have atInput (z : Fin 9 → Bool) : (enc z).getD i false = z j := by
            rw [show enc z = List.ofFn z ++ _ from rfl, List.getD_append _ _ _ _ (by simpa)]
            rw [List.getD_eq_getElem _ _ (by simpa)]
            exact List.getElem_ofFn _
          rw [atInput,atInput]
          simp [y,x,high,ne]
        · change (List.ofFn x ++ [_,_]).getD i false = (List.ofFn y ++ [_,_]).getD i false
          have leX : (List.ofFn x).length ≤ i := by simp only [List.length_ofFn]; omega
          have leY : (List.ofFn y).length ≤ i := by simp only [List.length_ofFn]; omega
          simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right leX,
            List.getElem?_append_right leY, List.length_ofFn]
          rw [show (x 0 || x 4) = (y 0 || y 4) from same₁, show (x a || x b) = (y a || y b) from same₂]
      have eq := stable k C.gates (enc x) (enc y) (by simp [enc])
        (fun g hg hm => hno.2 (List.mem_flatMap.mpr ⟨g,hg,hm⟩)) agree C.output hno.1.symm
      exact diff ((computes x).symm.trans (eq.trans (computes y)))
    · exact live k (by omega) hk
  have slots (gs : List Gate) (hs : ∀ g ∈ gs, g.inputs.length ≤ 2) :
      (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
    induction gs with
    | nil => simp
    | cons g gs ih =>
      have base := ih (fun z hz => hs z (List.mem_cons_of_mem g hz))
      have head := hs g List.mem_cons_self
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega
  have used := slots C.gates (fun g hg => (fan g hg).2)
  have limit : refs.length ≤ 27 := by
    change (C.gates.flatMap Gate.inputs).length + 1 ≤ 27
    change C.gates.length = 13 at exactSize
    omega
  rcases lt_or_gt_of_ne hab with order | order
  · obtain ⟨x,hx⟩ := threeExtra a b order ha0 ha4 hb0 hb4 C fan exactSize covered limit
    exact hx (computes x)
  · obtain ⟨x,hx⟩ := threeExtra b a order hb0 hb4 ha0 ha4 C fan exactSize covered limit
    rw [Bool.or_comm (x b) (x a)] at hx
    exact hx (computes x)
