import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.HeptadCover PEqualNP.LowMerge PEqualNP.GenericRejection

set_option maxRecDepth 8000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_5080_680
    (masks : ∀ (n : ℕ) (C : Circuit), ReadsBack n C → ∀ R : Finset (List Bool),
      (∀ x ∈ R, x.length = n) →
      let v (i : ℕ) := R.filter fun x => (C.wires x).getD i false
      (∀ i < n, v i = R.filter fun x => x.getD i false) ∧
      ∀ j < C.size, let g := gateAt C j
        v (n+j) = R.filter fun x => g.op.eval (g.inputs.map fun i => decide (x ∈ v i)))
    (paths : ∀ (n : ℕ) (C : Circuit) (i j : ℕ), j < C.size → InCone n C i j →
      Relation.TransGen (fun a b : ℕ => b < C.size ∧ n+a ∈ (gateAt C b).inputs) i j)
    (bound :
    let S := singerLines3
    let pos := (incidences S).image fun p => pointLineInput 13 13 p.1 p.2
    let neg := (quadrangles S).image fun q => incidenceInput q (missLines S q)
    let T := Finset (List Bool)
    let B := (Finset.range 26).image fun i => (pos ∪ neg).filter fun x => x.getD i false
    ∀ (V K : Finset T) (l r : T → T),
      let E (a b : T) := b ∈ V \ B ∧ (a = l b ∨ a = r b)
      pos ∈ V → B ⊆ V → K ⊆ V \ B → WellFounded E →
      (∀ b ∈ V \ B, l b ∈ V ∧ r b ∈ V ∧ l b ≠ r b ∧
        b = if b ∈ K then l b ∩ r b else l b ∪ r b) →
      (∀ a ∈ K, 2 ≤ (V.filter (E a)).card) →
      (∃ p ∈ K ×ˢ K, ∃ q ∈ K ×ˢ K, p ≠ q ∧
        Relation.TransGen E p.1 p.2 ∧ Relation.TransGen E q.1 q.2) →
      90 ≤ V.card) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 → (∀ x12 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → (2 : ℕ) ≤ (PEqualNP.TopForm.readers (26 : ℕ) x4 x12).card) → ∃ x13 < x4.gates.length, ∃ x14 < (26 : ℕ) + x13, ∀ (x15 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x16 : List Bool), x16.length = (26 : ℕ) → (x4.wires x16).getD ((26 : ℕ) + x13) Bool.false = (x4.wires x16).getD x14 Bool.false → x15.eval x16 = x4.eval x16) → x2 x15 := by
  classical
  intro off valid nested C mono back good small _ binary pairs share
  let S := singerLines3
  let pos := (incidences S).image fun p => pointLineInput 13 13 p.1 p.2
  let neg := (quadrangles S).image fun q => incidenceInput q (missLines S q)
  let T := Finset (List Bool)
  let B := (Finset.range 26).image fun i => (pos ∪ neg).filter fun x => x.getD i false
  let R := pos ∪ neg
  let v (i : ℕ) := R.filter fun x => (C.wires x).getD i false
  have inc : ∀ p l : Fin 13, p ∈ S l ↔ p-l ∈ off := by decide
  have quad (q : Finset (Fin 13)) : q ∈ quadrangles S ↔
      q.card = 4 ∧ ∀ l, (q.filter fun a => a-l ∈ off).card ≤ 2 := by
    have pl (l : Fin 13) : q.filter (fun a => a-l ∈ off) = q ∩ S l := by
      ext a; simp [inc]
    change q ∈ (Finset.univ.powersetCard 4).filter _ ↔ _
    simp [pl]
  have negrow (q : Finset (Fin 13)) : incidenceInput q (missLines S q) =
        (List.ofFn fun a : Fin 13 => decide (a ∈ q)) ++
          List.ofFn fun l : Fin 13 => decide (∀ a ∈ q, a-l ∉ off) := by
    apply congrArg (List.append _)
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    change l ∈ Finset.univ.filter _ ↔ _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_left]
    constructor
    · intro z a ha hb; exact z ((inc a l).mpr hb) ha
    · intro z a ha hb; exact z a hb ((inc a l).mp ha)
  have semantic (D : Circuit) : valid D ↔
      (∀ x ∈ pos, D.eval x = true) ∧ (∀ x ∈ neg, D.eval x = false) := by
    constructor
    · rintro ⟨p,n⟩
      constructor
      · intro x hx
        obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hx
        exact p a b ((inc a b).mp (Finset.mem_filter.mp hab).2)
      · intro x hx
        obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
        rw [negrow]
        exact n q ((quad _).mp hq).1 ((quad _).mp hq).2
    · rintro ⟨p,n⟩
      constructor
      · intro a b h; exact p _ (Finset.mem_image.mpr ⟨(a,b),Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,(inc a b).mpr h⟩,rfl⟩)
      · intro q h1 h2
        rw [← negrow]
        exact n _ (Finset.mem_image.mpr ⟨q,(quad _).mpr ⟨h1,h2⟩,rfl⟩)
  have gold := (semantic C).mp good
  have lens (x) (hx : x ∈ R) : x.length = 26 := by
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨⟨p,l⟩,_,rfl⟩ := Finset.mem_image.mp h
      change (List.ofFn _ ++ List.ofFn _).length = 26
      simp
    · obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp h
      change (List.ofFn _ ++ List.ofFn _).length = 26
      simp
  have distinct (i j : Fin 26) (hne : i ≠ j) : ∃ a b : Fin 13, a ∈ S b ∧
      (pointLineInput 13 13 a b).getD i false ≠ (pointLineInput 13 13 a b).getD j false := by
    let p (i j : Fin 26) : Fin 13 :=
      if i.val ≥ 13 ∧ j.val = i.val - 13 then Fin.ofNat 13 i.val + 1 else Fin.ofNat 13 i.val
    let t (i j : Fin 26) : Fin 13 :=
      if i.val < 13 ∧ j.val = i.val + 13 then Fin.ofNat 13 i.val - 1 else Fin.ofNat 13 i.val
    exact ⟨p i j,t i j,(show ∀ i j : Fin 26, i ≠ j → p i j ∈ S (t i j) ∧
      (pointLineInput 13 13 (p i j) (t i j)).getD i false ≠
      (pointLineInput 13 13 (p i j) (t i j)).getD j false by decide) i j hne⟩
  have dist (i j : Fin 26) (hne : i ≠ j) : ∃ x ∈ pos, x.getD i false ≠ x.getD j false := by
    obtain ⟨a,b,hab,diff⟩ := distinct i j hne
    exact ⟨_,Finset.mem_image.mpr ⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab⟩,rfl⟩,diff⟩
  change ∀ (V K : Finset T) (l r : T → T), let E (a b : T) := b ∈ V \ B ∧ (a = l b ∨ a = r b)
    pos ∈ V → B ⊆ V → K ⊆ V \ B → WellFounded E →
    (∀ b ∈ V \ B, l b ∈ V ∧ r b ∈ V ∧ l b ≠ r b ∧
      b = if b ∈ K then l b ∩ r b else l b ∪ r b) →
    (∀ a ∈ K, 2 ≤ (V.filter (E a)).card) →
    (∃ p ∈ K ×ˢ K, ∃ q ∈ K ×ˢ K, p ≠ q ∧ Relation.TransGen E p.1 p.2 ∧ Relation.TransGen E q.1 q.2) →
    90 ≤ V.card at bound
  clear_value pos neg
  obtain ⟨base,rule⟩ := masks 26 C back R lens
  by_contra fail
  have fresh (j : ℕ) (hj : j < C.size) (i : ℕ) (hi : i < 26+j) : v (26+j) ≠ v i := by
    intro eq
    apply fail
    refine ⟨j,hj,i,hi,?_⟩
    intro D agree
    apply (semantic D).mpr
    have right (x) (hx : x ∈ R) : D.eval x = C.eval x := by
      apply agree x (lens x hx)
      have he : x ∈ v (26+j) ↔ x ∈ v i := by rw [eq]
      apply Bool.eq_iff_iff.mpr
      simpa only [v,Finset.mem_filter,hx,true_and] using he
    exact ⟨fun x hx => (right _ (Finset.mem_union_left _ hx)).trans (gold.1 x hx),
      fun x hx => (right _ (Finset.mem_union_right _ hx)).trans (gold.2 x hx)⟩
  have sep (i j : ℕ) (lt : i < j) (hj : j < 26+C.size) : v i ≠ v j := by
    by_cases h : j < 26
    · obtain ⟨x,hp,diff⟩ := dist ⟨i,by omega⟩ ⟨j,h⟩ (by simp; omega)
      have hx : x ∈ R := Finset.mem_union_left _ hp
      intro eq
      have he : x ∈ v i ↔ x ∈ v j := by rw [eq]
      rw [show v i = _ from base i (by omega),show v j = _ from base j h] at he
      exact diff (Bool.eq_iff_iff.mpr (by simpa only [Finset.mem_filter,hx,true_and] using he))
    · have je : 26+(j-26) = j := by omega
      have ne := fresh (j-26) (by omega) i (by omega)
      rwa [je,ne_comm] at ne
  let m := 26+C.size
  let V := (Finset.range m).image v
  have inj (i j : ℕ) (hi : i < m) (hj : j < m) (e : v i = v j) : i = j := by
    rcases lt_trichotomy i j with lt|eq|gt
    · exact (sep i j lt hj e).elim
    · exact eq
    · exact (sep j i gt hi e.symm).elim
  have vin (i : ℕ) (h : i < m) : v i ∈ V := Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr h,rfl⟩
  have beq : B = (Finset.range 26).image v := by
    apply Finset.image_congr
    intro i hi; exact (base i (Finset.mem_range.mp hi)).symm
  let idx (a : T) := if h : ∃ i < m, v i = a then h.choose else 0
  have index (i : ℕ) (h : i < m) : idx (v i) = i := by
    let ex : ∃ j < m, v j = v i := ⟨i,h,rfl⟩
    simpa only [idx,dite_eq_left ex] using inj ex.choose i ex.choose_spec.1 h ex.choose_spec.2
  have newmem (j : ℕ) (hj : j < C.size) : v (26+j) ∈ V \ B := by
    apply Finset.mem_sdiff.mpr
    refine ⟨vin _ (by dsimp [m]; omega),?_⟩
    rw [beq]; rintro h
    obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
    exact fresh j hj i (by have := Finset.mem_range.mp hi; omega) eq.symm
  have decode (b : T) (hb : b ∈ V \ B) : ∃ j < C.size, b = v (26+j) := by
    obtain ⟨inV,notB⟩ := Finset.mem_sdiff.mp hb
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp inV
    have low : 26 ≤ i := by
      by_contra! h
      exact notB (beq ▸ Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr h,rfl⟩)
    have hi' : i < 26+C.size := Finset.mem_range.mp hi
    exact ⟨i-26,by omega,by congr 1; omega⟩
  let g := gateAt C
  let w (j t : ℕ) := (g j).inputs.getD t 0
  have gate (j : ℕ) (hj : j < C.size) : g j ∈ C.gates := by
    rw [show g j = C.gates[j]'hj from List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem _
  have desc (j : ℕ) (hj : j < C.size) : (g j).inputs = [w j 0,w j 1] := by
    have L := (binary _ (gate j hj)).1
    generalize eq : (g j).inputs = as at L
    dsimp [w]; rw [eq]
    cases as with
    | nil => simp at L
    | cons a t => cases t with
      | nil => simp at L
      | cons b t => cases t <;> simp at L ⊢
  have prev (j : ℕ) (hj : j < C.size) (t : ℕ) (ht : t=0 ∨ t=1) : w j t < 26+j := by
    apply back j hj
    change _ ∈ (g j).inputs
    rw [desc j hj]; rcases ht with rfl|rfl <;> simp
  let l (b : T) := v (w (idx b - 26) 0)
  let r (b : T) := v (w (idx b - 26) 1)
  let E (a b : T) := b ∈ V \ B ∧ (a = l b ∨ a = r b)
  let h (j : ℕ) := v (26+j)
  have left (j : ℕ) (hj : j < C.size) : l (h j) = v (w j 0) := by
    simp [l,h,index _ (show 26+j<m by dsimp [m]; omega)]
  have right (j : ℕ) (hj : j < C.size) : r (h j) = v (w j 1) := by
    simp [r,h,index _ (show 26+j<m by dsimp [m]; omega)]
  let A := (Finset.range C.size).filter fun j => (g j).op = .and
  let K := A.image h
  have aiff (j : ℕ) (hj : j < C.size) : h j ∈ K ↔ (g j).op = .and := by
    constructor
    · intro mem
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp mem
      obtain ⟨lt,tag⟩ := Finset.mem_filter.mp hi
      have ilt := Finset.mem_range.mp lt
      have := inj (26+i) (26+j) (by dsimp [m]; omega) (by dsimp [m]; omega) he
      rwa [show j = i by omega]
    · intro tag; exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,tag⟩,rfl⟩
  have well : WellFounded E := by
    apply Subrelation.wf (r := InvImage (· < ·) idx) _ (InvImage.wf _ Nat.lt_wfRel.wf)
    rintro a b ⟨hb,op⟩
    obtain ⟨j,hj,rfl⟩ := decode b hb
    change a = l (h j) ∨ a = r (h j) at op
    rw [left j hj,right j hj] at op
    have jlt : 26+j<m := by dsimp [m]; omega
    rcases op with rfl|rfl
    · have H := prev j hj 0 (Or.inl rfl)
      exact show idx (v _) < idx (v _) by rw [index _ (by omega),index _ jlt]; exact H
    · have H := prev j hj 1 (Or.inr rfl)
      exact show idx (v _) < idx (v _) by rw [index _ (by omega),index _ jlt]; exact H
  have translate (i j : ℕ) (hj : j < C.size) (read : 26+i ∈ (gateAt C j).inputs) : E (h i) (h j) := by
    refine ⟨newmem j hj,?_⟩
    change _ ∈ (g j).inputs at read
    rw [desc j hj] at read
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at read
    rw [left j hj,right j hj]; exact read.imp (congrArg v) (congrArg v)
  have path (i j : ℕ) (hj : j < C.size) (cone : InCone 26 C i j) : Relation.TransGen E (h i) (h j) := by
    have steps := paths 26 C i j hj cone
    exact Relation.TransGen.lift (r := fun a b => b < C.size ∧ 26+a ∈ (gateAt C b).inputs)
      h (fun _ _ a => translate _ _ a.1 a.2) i j steps
  have pout : v C.output = pos := by
    ext x
    change x ∈ R.filter (fun x => C.eval x = true) ↔ _
    constructor
    · intro he
      obtain ⟨hx,yes⟩ := Finset.mem_filter.mp he
      rcases Finset.mem_union.mp hx with hp | hn
      · exact hp
      · simp [gold.2 x hn] at yes
    · intro hx; exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hx,gold.1 _ hx⟩
  have outlt : C.output < m := by
    let x := pointLineInput 13 13 0 0
    have yes := good.1 0 0 (by decide)
    change (C.wires x).getD C.output false = true at yes
    have len (gs : List Gate) (z : List Bool) :
        (gs.foldl (fun p t => p ++ [t.op.eval (t.inputs.map fun i => p.getD i false)]) z).length = z.length + gs.length := by
      induction gs generalizing z with
      | nil => simp
      | cons a gs ih => rw [List.foldl_cons,ih]; simp; omega
    have count : (C.wires x).length = m := by
      change (C.gates.foldl _ x).length = _
      rw [len]; rfl
    by_contra! outside
    rw [List.getD_eq_default _ _ (count ▸ outside)] at yes
    contradiction
  apply Nat.not_le_of_lt (show V.card < 90 from
    (Finset.card_image_le.trans_lt (by simp [m]; omega))) 
  apply bound V K l r
  · exact pout ▸ vin _ outlt
  · rw [beq]; exact Finset.image_subset_image (Finset.range_mono (by dsimp [m]; omega))
  · intro b hb
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
    exact newmem j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  · exact well
  · intro b hb
    obtain ⟨j,hj,rfl⟩ := decode b hb
    change l (h j) ∈ V ∧ r (h j) ∈ V ∧ l (h j) ≠ r (h j) ∧ h j =
      if h j ∈ K then l (h j) ∩ r (h j) else l (h j) ∪ r (h j)
    simp only [left j hj,right j hj,aiff j hj]
    have lt₀ := prev j hj 0 (Or.inl rfl)
    have lt₁ := prev j hj 1 (Or.inr rfl)
    have lt : 26+j<m := by dsimp [m]; omega
    refine ⟨vin _ (by omega),vin _ (by omega),fun eq => (binary _ (gate j hj)).2
      (inj (w j 0) (w j 1) (by omega) (by omega) eq),?_⟩
    have recurrence := rule j hj
    change h j = R.filter (fun x => (g j).op.eval ((g j).inputs.map fun i => decide (x ∈ v i))) at recurrence
    rw [recurrence,desc j hj]
    have types : (g j).op = .and ∨ (g j).op = .or := (mono _ (gate j hj)).1
    rcases types with op | op
    · have ev (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
      ext x; by_cases hx : x ∈ R <;> simp [op,ev,v,hx]
    · have ev (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
      ext x; by_cases hx : x ∈ R <;> simp [op,ev,v,hx]
  · intro b hb
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨ilt,tag⟩ := Finset.mem_filter.mp hi
    have fan := share i (Finset.mem_range.mp ilt) tag
    let D := PEqualNP.TopForm.readers 26 C i
    have inside (j) (hj : j ∈ D) : j < C.size ∧ 26+i ∈ (g j).inputs := by
      exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hj).1,(Finset.mem_filter.mp hj).2⟩
    have emb : Set.InjOn h D := by
      intro a ha b hb eq
      have al := (inside a ha).1
      have bl := (inside b hb).1
      have := inj (26+a) (26+b) (by dsimp [m];omega) (by dsimp [m];omega) eq
      omega
    apply fan.trans
    rw [← show (D.image h).card = D.card from Finset.card_image_of_injOn emb]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨jlt,read⟩ := inside j hj
    exact Finset.mem_filter.mpr ⟨vin _ (by dsimp [m]; omega),translate i j jlt read⟩
  · letI : DecidableEq GateOp := gateOpDecEq
    let D := ((Finset.range C.size) ×ˢ (Finset.range C.size)).filter fun p =>
        (g p.1).op = .and ∧ (g p.2).op = .and ∧ InCone 26 C p.1 p.2
    obtain ⟨p,hp,q,hq,diff⟩ := Finset.one_lt_card.mp (show 1 < D.card from pairs)
    have data (p : ℕ × ℕ) (hp : p ∈ D) :
        (h p.1,h p.2) ∈ K ×ˢ K ∧ Relation.TransGen E (h p.1) (h p.2) ∧
        p.1 < C.size ∧ p.2 < C.size := by
      simp only [D,Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hp
      exact ⟨Finset.mem_product.mpr ⟨(aiff _ hp.1.1).mpr hp.2.1,(aiff _ hp.1.2).mpr hp.2.2.1⟩,
        path _ _ hp.1.2 hp.2.2.2,hp.1⟩
    obtain ⟨pK,pPath,p1,p2⟩ := data p hp
    obtain ⟨qK,qPath,q1,q2⟩ := data q hq
    refine ⟨_,pK,_,qK,?_,pPath,qPath⟩
    intro eq; apply diff
    apply Prod.ext
    · have := inj _ _ (show 26+p.1 < m by dsimp [m];omega)
        (show 26+q.1<m by dsimp [m];omega) (congrArg Prod.fst eq)
      omega
    · have := inj _ _ (show 26+p.2 < m by dsimp [m];omega)
        (show 26+q.2<m by dsimp [m];omega) (congrArg Prod.snd eq)
      omega
