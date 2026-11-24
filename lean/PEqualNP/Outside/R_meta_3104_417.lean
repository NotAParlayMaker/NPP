import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first premise is the checked eight-input lower bound L_meta_2036.
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_3104_417
    (lower : ¬PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ))) (12 : ℕ))
    (residual :
      let f (x : Fin 8 → Bool) := ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any
        (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10)))
      ∀ (A B : Circuit) (k : ℕ), FanInTwo A → FanInTwo B → A.size + B.size = 13 →
      let w (b : Bool) (x : Fin 8 → Bool) := A.wires (List.ofFn x ++ [x 1 || b])
      B.output ≠ 9 + A.size →
      (∃ g ∈ B.gates, 9 + A.size ∈ g.inputs) →
      (w false (fun i => decide (i = 1 ∨ i = 3))).getD k false = false →
      (∀ x, B.eval (w false x ++ [(w false x).getD k false]) = f x) →
      ∃ x, B.eval (w true x ++ [true]) ≠ (f x || x 0 || x 3)) :
    have x1 : (Fin (8 : ℕ) → Bool) → Bool := fun (x1 : Fin (8 : ℕ) → Bool) => x1 (0 : Fin (8 : ℕ)) && x1 (1 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (2 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (3 : Fin (8 : ℕ)) || x1 (0 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)) || x1 (1 : Fin (8 : ℕ)) && x1 (5 : Fin (8 : ℕ)) || x1 (2 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (3 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (4 : Fin (8 : ℕ)) && x1 (6 : Fin (8 : ℕ)) || x1 (5 : Fin (8 : ℕ)) && x1 (7 : Fin (8 : ℕ)) || x1 (7 : Fin (8 : ℕ)) && x1 (4 : Fin (8 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x2.size + x3.size ≤ (13 : ℕ) →         have x8 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x8 : Bool) (x9 : Fin (8 : ℕ) → Bool) => x2.wires (List.ofFn x9 ++ [x9 (1 : Fin (8 : ℕ)) || x8]);         (∀ (x9 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.false x9 ++ [(x8 Bool.false x9).getD x4 Bool.false]) = x1 x9) → ∃ (x10 : Fin (8 : ℕ) → Bool), x3.eval (x8 Bool.true x10 ++ [Bool.true]) ≠ (x1 x10 || x10 (0 : Fin (8 : ℕ)) || x10 (3 : Fin (8 : ℕ))) := by
  intro f A B tap fanA fanB budget w good
  classical
  let target (x : Fin 8 → Bool) := ([1,12,23,4,15,26,37,46,57,74] : List ℕ).any
    (fun e => x (Fin.ofNat 8 (e / 10)) && x (Fin.ofNat 8 (e % 10)))
  have graphEq (x : Fin 8 → Bool) : f x = target x := by
    simp only [f,target,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl
  let step (z : List Bool) (g : Gate) := z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]
  let rename (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map ρ⟩
  have runLength (gs : List Gate) (z : List Bool) : (gs.foldl step z).length = z.length + gs.length := by
    induction gs generalizing z with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [step,List.length_append,List.length_cons,List.length_nil]
      omega
  have keep (gs : List Gate) (z : List Bool) (i : ℕ) (hi : i < z.length) :
      (gs.foldl step z).getD i false = z.getD i false := by
    induction gs generalizing z with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step z g)]
      · exact List.getD_append _ _ _ _ hi
      · simp only [step,List.length_append,List.length_singleton]
        omega
  have last (z : List Bool) (v : Bool) : (z ++ [v]).getD z.length false = v := by
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    rfl
  have old (z : List Bool) (v : Bool) (i : ℕ) (h : i ≠ z.length) :
      (z ++ [v]).getD i false = z.getD i false := by
    by_cases hi : i < z.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have sim (ρ : ℕ → ℕ) (gs : List Gate) (l r : List Bool)
      (future : ∀ j, ρ (l.length + j) = r.length + j)
      (valid : ∀ i < l.length, ρ i < r.length ∨ r.length + gs.length ≤ ρ i)
      (agree : ∀ i, l.getD i false = r.getD (ρ i) false) :
      ∀ i, (gs.foldl step l).getD i false =
        ((gs.map (rename ρ)).foldl step r).getD (ρ i) false := by
    induction gs generalizing l r with
    | nil => exact agree
    | cons g gs ih =>
      simp only [List.foldl_cons,List.map_cons]
      apply ih
      · intro j
        simp only [step,List.length_append,List.length_singleton,Nat.add_assoc]
        exact future (1+j)
      · intro i hi
        simp only [step,List.length_append,List.length_singleton] at hi ⊢
        by_cases h : i < l.length
        · have hvalid := valid i h
          simp only [List.length_cons] at hvalid
          omega
        · have now : i = l.length := by omega
          have val : ρ l.length = r.length := by simpa using future 0
          rw [now,val]
          exact Or.inl (by omega)
      · intro i
        have same : g.inputs.map (fun j => l.getD j false) =
            (g.inputs.map ρ).map (fun j => r.getD j false) := by
          rw [List.map_map]
          exact List.map_congr_left (fun j _ => agree j)
        by_cases atEnd : i = l.length
        · have sameIndex : ρ l.length = r.length := by simpa using future 0
          rw [atEnd,sameIndex]
          simp only [step,rename,last,same]
        · have atEnd' : ρ i ≠ r.length := by
            by_cases h : i < l.length
            · have offset := valid i h
              simp only [List.length_cons] at offset
              omega
            · have eq : i = l.length + (i-l.length) := by omega
              have eval : ρ i = r.length + (i-l.length) := by
                calc
                  ρ i = ρ (l.length + (i-l.length)) := congrArg ρ eq
                  _ = _ := future _
              omega
          simp only [step,rename]
          rw [old _ _ _ atEnd, old _ _ _ atEnd', agree]
  let aMap (i : ℕ) := if i < 8 then i else if i = 8 then 1 else i - 1
  let m := 8 + A.size
  let bMap (i : ℕ) := if i < m+1 then aMap i
    else if i = m+1 then if tap < m+1 then aMap tap else m+B.size
    else m + (i-(m+2))
  have aSmall (i : ℕ) (h : i < m+1) : aMap i < m := by
    unfold aMap m at *
    split_ifs <;> omega
  have wLength (b : Bool) (x : Fin 8 → Bool) : (w b x).length = m+1 := by
    change (A.gates.foldl step (List.ofFn x ++ [x 1 || b])).length = _
    rw [runLength]
    simp only [List.length_append,List.length_ofFn,List.length_singleton]
    change 8 + 1 + A.size = m+1
    unfold m
    omega
  have flat : HasCircuitSize 8 f (A.size+B.size) := by
    let D : Circuit := ⟨A.gates.map (rename aMap) ++ B.gates.map (rename bMap), bMap B.output⟩
    refine ⟨D,?_ ,?_ ,?_⟩
    · intro g hg
      change g ∈ A.gates.map (rename aMap) ++ B.gates.map (rename bMap) at hg
      rcases List.mem_append.mp hg with ha | hb
      · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
        exact ⟨(fanA k hk).1,by simpa only [rename,List.length_map] using (fanA k hk).2⟩
      · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hb
        exact ⟨(fanB k hk).1,by simpa only [rename,List.length_map] using (fanB k hk).2⟩
    · change (A.gates.map (rename aMap) ++ B.gates.map (rename bMap)).length ≤
          A.gates.length + B.gates.length
      simp only [List.length_append,List.length_map,le_refl]
    · intro x
      let xs := List.ofFn x
      have xsLength : xs.length = 8 := List.length_ofFn
      have aAgree (i : ℕ) : (xs ++ [x 1]).getD i false = xs.getD (aMap i) false := by
        by_cases h : i < 8
        · rw [show aMap i = i from ite_eq_left h, List.getD_append _ _ _ _ (by rwa [xsLength])]
        · by_cases eq : i = 8
          · subst i
            have h1 : xs.getD 1 false = x 1 := by
              change (List.ofFn x).getD (1 : Fin 8).val false = x 1
              rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
            rw [show aMap 8 = 1 by rfl, h1]
            exact (congrArg (fun i => (xs ++ [x 1]).getD i false) xsLength.symm).trans (last xs (x 1))
          · rw [List.getD_eq_default _ _ (by simp only [List.length_append,List.length_singleton,xsLength]; omega),
              List.getD_eq_default _ _ (by
                rw [xsLength]
                unfold aMap
                split_ifs <;> omega)]
      have aRel := sim aMap A.gates (xs ++ [x 1]) xs (by
          intro j
          simp only [List.length_append,List.length_singleton,xsLength]
          unfold aMap
          split_ifs <;> omega) (by
          intro i hi
          simp only [List.length_append,List.length_singleton,xsLength] at hi ⊢
          left
          unfold aMap
          split_ifs <;> omega) aAgree
      let base := (A.gates.map (rename aMap)).foldl step xs
      have baseLen : base.length = m := by
        change ((A.gates.map (rename aMap)).foldl step xs).length = _
        rw [runLength,xsLength,List.length_map]
        rfl
      let ws := w false x
      have wsLen : ws.length = m+1 := wLength false x
      have lookup (i : ℕ) : ws.getD i false = base.getD (aMap i) false := by
        change (A.gates.foldl step (xs ++ [x 1 || false])).getD i false = _
        rw [Bool.or_false]
        exact aRel i
      have bAgree (i : ℕ) :
          (ws ++ [ws.getD tap false]).getD i false = base.getD (bMap i) false := by
        by_cases h : i < m+1
        · rw [show bMap i = aMap i from ite_eq_left h,
            List.getD_append _ _ _ _ (by rwa [wsLen]), lookup]
        · by_cases eq : i = m+1
          · have tapRead : (ws ++ [ws.getD tap false]).getD i false = ws.getD tap false := by
              rw [eq,← wsLen,last]
            rw [tapRead]
            by_cases available : tap < m+1
            · rw [show bMap i = aMap tap by simp [bMap,h,eq,available], lookup]
            · rw [show bMap i = m+B.size by simp [bMap,h,eq,available],
                List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
          · have after : m+2 ≤ i := by omega
            have bAfter : m ≤ bMap i := by
              unfold bMap
              split_ifs <;> omega
            rw [List.getD_eq_default _ _ (by simp only [List.length_append,List.length_singleton,wsLen]; omega),
              List.getD_eq_default _ _ (by omega)]
      have bRel := sim bMap B.gates (ws ++ [ws.getD tap false]) base (by
          intro j
          simp only [List.length_append,List.length_singleton,wsLen,baseLen]
          unfold bMap
          split_ifs <;> omega) (by
          intro i hi
          simp only [List.length_append,List.length_singleton,wsLen,baseLen] at hi ⊢
          by_cases h : i < m+1
          · left
            rw [show bMap i = aMap i from ite_eq_left h]
            exact aSmall i h
          · have eq : i = m+1 := by omega
            by_cases av : tap < m+1
            · left
              rw [show bMap i = aMap tap by simp [bMap,h,eq,av]]
              exact aSmall tap av
            · right
              rw [show bMap i = m+B.size by simp [bMap,h,eq,av]]
              exact le_rfl) bAgree
      change ((A.gates.map (rename aMap) ++ B.gates.map (rename bMap)).foldl step xs).getD
        (bMap B.output) false = f x
      rw [List.foldl_append]
      exact (bRel B.output).symm.trans (good x)
  have exactSize : A.size+B.size = 13 := by
    by_contra! h
    obtain ⟨D,df,ds,de⟩ := flat
    apply lower
    exact ⟨D,df,by omega,de⟩
  by_contra none
  have goodTrue (x : Fin 8 → Bool) :
      B.eval (w true x ++ [true]) = (f x || x 0 || x 3) :=
    Classical.byContradiction (fun h => none ⟨x,h⟩)
  let witness : Fin 8 → Bool := fun i => decide (i = 1 ∨ i = 3)
  have sameW : w false witness = w true witness := by
    change A.wires (List.ofFn witness ++ [witness 1 || false]) =
      A.wires (List.ofFn witness ++ [witness 1 || true])
    rfl
  have leftFalse : B.eval (w false witness ++ [(w false witness).getD tap false]) = false :=
    good witness
  have rightTrue : B.eval (w false witness ++ [true]) = true := by
    rw [sameW]
    exact goodTrue witness
  have pinFalse : (w false witness).getD tap false = false := by
    cases eq : (w false witness).getD tap false with
    | false => rfl
    | true =>
      rw [eq,rightTrue] at leftFalse
      exact Bool.noConfusion leftFalse
  have out : B.output ≠ m+1 := by
    intro eq
    let x : Fin 8 → Bool := fun _ => false
    have result := goodTrue x
    have prefixLen := wLength true x
    change (B.gates.foldl step (w true x ++ [true])).getD B.output false = false at result
    rw [eq, keep _ _ _ (by simp [prefixLen]), ← prefixLen, last] at result
    exact Bool.noConfusion result
  have live : ∃ g ∈ B.gates, m+1 ∈ g.inputs := by
    by_contra! h
    let z := w false witness
    have ignore (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ B.gates)
        (p q : List Bool) (len : p.length = q.length)
        (agree : ∀ i ≠ m+1, p.getD i false = q.getD i false) :
        ∀ i ≠ m+1, (gs.foldl step p).getD i false = (gs.foldl step q).getD i false := by
      induction gs generalizing p q with
      | nil => exact agree
      | cons g gs ih =>
        rw [List.foldl_cons,List.foldl_cons]
        apply ih (fun k hk => sub k (List.mem_cons_of_mem _ hk))
        · simp only [step,List.length_append,List.length_singleton,len]
        · intro i hi
          have same : g.inputs.map (fun j => p.getD j false) =
              g.inputs.map (fun j => q.getD j false) :=
            List.map_congr_left (fun j hj => agree j (fun e => h g (sub g List.mem_cons_self) (e ▸ hj)))
          change (p ++ [_]).getD i false = (q ++ [_]).getD i false
          rw [same]
          by_cases atEnd : i = p.length
          · rw [atEnd,last,len,last]
          · rw [old _ _ _ atEnd, old _ _ _ (by omega), agree _ hi]
    have agree (i : ℕ) (hi : i ≠ m+1) :
        (z ++ [z.getD tap false]).getD i false = (z ++ [true]).getD i false := by
      have len := wLength false witness
      have ne : i ≠ z.length := by
        change i ≠ (w false witness).length
        rwa [len]
      rw [old _ _ _ ne, old _ _ _ ne]
    have eq : B.eval (z ++ [z.getD tap false]) = B.eval (z ++ [true]) :=
      ignore B.gates (fun _ h => h) _ _ (by simp) agree B.output out
    exact Bool.noConfusion (leftFalse.symm.trans (eq.trans rightTrue))
  have pinIndex : m+1 = 9 + A.size := by
    unfold m
    omega
  obtain ⟨x,bad⟩ := residual A B tap fanA fanB exactSize
    (pinIndex ▸ out) (pinIndex ▸ live) pinFalse
    (fun x => (good x).trans (graphEq x))
  exact bad ((goodTrue x).trans (by rw [graphEq x]))
