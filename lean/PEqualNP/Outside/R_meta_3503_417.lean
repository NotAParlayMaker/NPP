import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3503_417
    (improve :
      ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I] (C : Circuit),
      let cost := fun D : Circuit => {j : ℕ | j<D.size ∧ (gateAt D j).op=.and ∧
        (¬OrReaches (n+m) D D.output j ∨ ∃ w∈(gateAt D j).inputs,∃ i<D.size,
          (gateAt D i).op=.and ∧ OrReaches (n+m) D w i)}.ncard
      let fits := fun (D : Circuit) => IsAO2 (n+m) D ∧ (∀ x,circuitFun (n+m) D x=decide (∃ p l,I p l ∧ x (Fin.castAdd m p)=true ∧ x (Fin.natAdd n l)=true))
      (∀ p q l s,p≠q → l≠s → ¬(I p l ∧ I p s ∧ I q l ∧ I q s)) → fits C → 0<cost C → ∃ D,fits D ∧ D.size≤ C.size ∧ cost D<cost C)
    (wireSemantics :
      ∀ (N : ℕ) (C : Circuit), IsAO2 N C →
      (∀ k i, OrReaches N C (N+k) i ↔ k<C.size ∧
        (i=k ∨ ((gateAt C k).op=.or ∧ ∃ w∈(gateAt C k).inputs,w<N+k ∧ OrReaches N C w i))) ∧
      ∀ x : Fin N → Bool,
      let v := fun w => (C.wires (List.ofFn x)).getD w false
      (∀ i : Fin N,v i=x i) ∧
      (∀ j<C.gates.length,(gateAt C j).op=.or → (v (N+j)=true ↔ ∃ w∈(gateAt C j).inputs,w<N+j ∧ v w=true)) ∧
      (∀ j<C.gates.length,(gateAt C j).op=.and → (v (N+j)=true ↔ ∀ w∈(gateAt C j).inputs,w<N+j ∧ v w=true)) ∧
      ∀ j,OrReaches N C C.output j → v (N+j)=true → circuitFun N C x=true)
    : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ (x15 ∈ x10 ∧ x16 ∈ x11 ∨ x15 ∈ x11 ∧ x16 ∈ x10) := by
  classical
  intro n m I inst C rect ao correct
  let cost := fun D : Circuit => {j : ℕ | j<D.size ∧ (gateAt D j).op=.and ∧
    (¬OrReaches (n+m) D D.output j ∨ ∃ w∈(gateAt D j).inputs,∃ i<D.size,
      (gateAt D i).op=.and ∧ OrReaches (n+m) D w i)}.ncard
  let fits := fun (D : Circuit) => IsAO2 (n+m) D ∧ (∀ x,circuitFun (n+m) D x=decide (∃ p l,I p l ∧ x (Fin.castAdd m p)=true ∧ x (Fin.natAdd n l)=true))
  let Bad := fun (D : Circuit) (j : ℕ) => j<D.size ∧ (gateAt D j).op=.and ∧
    (¬OrReaches (n+m) D D.output j ∨ ∃ w∈(gateAt D j).inputs,∃ i<D.size,
      (gateAt D i).op=.and ∧ OrReaches (n+m) D w i)
  let M := fun t => ∃ D : Circuit,fits D ∧ D.size≤ C.size ∧ cost D=t
  have any : ∃ t,M t := ⟨_,C,⟨ao,correct⟩,le_rfl,rfl⟩
  obtain ⟨D,⟨leg,evaluates⟩,small,least⟩ := Nat.find_spec any
  have zero : cost D=0 := by
    by_contra! nz
    obtain ⟨B,fitB,sm,less⟩ := improve n m I D rect ⟨leg,evaluates⟩ (Nat.pos_of_ne_zero nz)
    have lim := Nat.find_min' any (show M (cost B) from ⟨B,fitB,sm.trans small,rfl⟩)
    change cost B<cost D at less
    rw [least] at less
    exact (Nat.not_lt_of_ge lim) less
  have clean (j : ℕ) : ¬Bad D j := by
    intro bad
    have finite : {k | Bad D k}.Finite := (Set.finite_lt_nat D.size).subset (fun k hk => hk.1)
    have pos := (Set.ncard_pos finite).mpr (show {k | Bad D k}.Nonempty from ⟨j,bad⟩)
    change 0<cost D at pos
    omega
  let U := (Finset.range (n+m+D.size)).filter (fun w => ∀ i<D.size,(gateAt D i).op=.and →
    ¬OrReaches (n+m) D w i)
  obtain ⟨reaches,laws⟩ := wireSemantics (n+m) D leg
  have closed : ∀ w∈U,w<n+m ∨ ∃ j<D.gates.length,w=n+m+j ∧ (gateAt D j).op=.or ∧ ∀ v∈(gateAt D j).inputs,v∈U := by
    intro w hw
    obtain ⟨valid,free⟩ := Finset.mem_filter.mp hw
    have bound := Finset.mem_range.mp valid
    by_cases raw : w<n+m
    · exact .inl raw
    · obtain ⟨j,rfl⟩ : ∃ j,w=n+m+j := ⟨w-(n+m),by omega⟩
      have hj : j<D.size := by omega
      have mem : gateAt D j∈D.gates := by
        have len : j<D.gates.length := hj
        change D.gates.getD j _ ∈ D.gates
        simp [List.getD_eq_getElem?_getD,len]
      have op : (gateAt D j).op=.or := (leg.1 _ mem).resolve_left (fun andg =>
        free j hj andg ((reaches j j).2 ⟨hj,.inl rfl⟩))
      refine .inr ⟨j,hj,rfl,op,?_⟩
      intro v hv
      have lt := leg.2.1 j hj v hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩
      intro i hi andg reached
      exact free i hi andg ((reaches j i).2 ⟨hj,.inr ⟨op,v,hv,lt,reached⟩⟩)
  have ports : ∀ j<D.gates.length,(gateAt D j).op=.and → ∃ a b,(gateAt D j).inputs=[a,b] ∧ a∈U ∧ b∈U ∧ OrReaches (n+m) D D.output j := by
    intro j hj ag
    have mem : gateAt D j∈D.gates := by
      change D.gates.getD j _ ∈ D.gates
      simp [List.getD_eq_getElem?_getD,hj]
    have len := leg.2.2 _ mem
    have pair (xs : List ℕ) (sz : xs.length=2) : ∃ a b,xs=[a,b] := by
      cases xs with
      | nil => simp at sz
      | cons a ys =>
        cases ys with
        | nil => simp at sz
        | cons b zs =>
          cases zs with
          | nil => exact ⟨a,b,rfl⟩
          | cons d ds => simp at sz
    obtain ⟨a,b,ins⟩ := pair _ len
    have goodPort (w) (hw : w∈(gateAt D j).inputs) : w∈U := by
      have lt := leg.2.1 j hj w hw
      have jd : j<D.size := hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩
      intro i hi ai path
      exact clean j ⟨hj,ag,.inr ⟨w,hw,i,hi,ai,path⟩⟩
    exact ⟨a,b,ins,goodPort a (by rw [ins];simp),goodPort b (by rw [ins];simp),
      Classical.byContradiction (fun h => clean j ⟨hj,ag,.inl h⟩)⟩
  let left := fun i : Fin (n+m) => decide (i.val<n)
  let right := fun i : Fin (n+m) => decide (n≤ i.val)
  let L := fun w => (D.wires (List.ofFn left)).getD w false
  let R := fun w => (D.wires (List.ofFn right)).getD w false
  obtain ⟨rawL,orL,andL,upL⟩ := laws left
  obtain ⟨rawR,orR,andR,upR⟩ := laws right
  have noL : circuitFun (n+m) D left=false := by
    rw [evaluates]
    simp [left,Fin.natAdd]
  have noR : circuitFun (n+m) D right=false := by
    rw [evaluates]
    apply decide_eq_false_iff_not.mpr
    rintro ⟨p,l,_,on,_⟩
    change decide (n ≤ p.val)=true at on
    exact (Nat.not_le_of_gt p.isLt) (of_decide_eq_true on)
  have total (w) (member : w∈U) : L w=true ∨ R w=true := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      rcases closed w member with raw|⟨j,hj,rfl,op,sources⟩
      · let i : Fin (n+m) := ⟨w,raw⟩
        change (D.wires (List.ofFn left)).getD i.val false=true ∨
          (D.wires (List.ofFn right)).getD i.val false=true
        have hl : L i.val=left i := rawL i
        have hr : R i.val=right i := rawR i
        change L i.val=true ∨ R i.val=true
        rw [hl,hr]
        simp [left,right];omega
      · have memg : gateAt D j∈D.gates := by
          change D.gates.getD j _ ∈ D.gates
          simp [List.getD_eq_getElem?_getD,hj]
        have len := leg.2.2 _ memg
        obtain ⟨v,vs⟩ : ∃ v,v∈(gateAt D j).inputs := by
          cases h : (gateAt D j).inputs with
          | nil => simp [h] at len
          | cons a rest => exact ⟨a,by simp⟩
        have lt := leg.2.1 j hj v vs
        rcases ih v lt (sources v vs) with l|r
        · exact Or.inl ((orL j hj op).2 ⟨v,vs,lt,l⟩)
        · exact Or.inr ((orR j hj op).2 ⟨v,vs,lt,r⟩)
  let P := U.filter (fun w => R w=false)
  let Q := U.filter (fun w => L w=false)
  refine ⟨D,P,Q,leg,evaluates,small,?_,?_,?_⟩
  · intro w hw
    obtain ⟨mem,off⟩ := Finset.mem_filter.mp hw
    rcases closed w mem with raw|⟨j,hj,rfl,op,sources⟩
    · let i : Fin (n+m) := ⟨w,raw⟩
      have h : right i=false := (rawR i).symm.trans off
      exact .inl (by simpa [right,i] using h)
    · refine .inr ⟨j,hj,rfl,op,?_⟩
      intro v hv
      refine Finset.mem_filter.mpr ⟨sources v hv,Bool.eq_false_iff.mpr ?_⟩
      intro on
      have hit := (orR j hj op).2 ⟨v,hv,leg.2.1 j hj v hv,on⟩
      change R _=true at hit
      rw [off] at hit
      contradiction
  · intro w hw
    obtain ⟨mem,off⟩ := Finset.mem_filter.mp hw
    rcases closed w mem with raw|⟨j,hj,rfl,op,sources⟩
    · let i : Fin (n+m) := ⟨w,raw⟩
      have h : left i=false := (rawL i).symm.trans off
      exact .inl ⟨by simpa [left,i] using h,raw⟩
    · refine .inr ⟨j,hj,rfl,op,?_⟩
      intro v hv
      refine Finset.mem_filter.mpr ⟨sources v hv,Bool.eq_false_iff.mpr ?_⟩
      intro on
      have hit := (orL j hj op).2 ⟨v,hv,leg.2.1 j hj v hv,on⟩
      change L _=true at hit
      rw [off] at hit
      contradiction
  · intro j hj op
    obtain ⟨a,b,ins,ua,ub,path⟩ := ports j hj op
    have anyOn (x : Fin (n+m) → Bool) (f : ℕ → Bool)
        (gate : f (n+m+j)=true ↔ ∀ v∈(gateAt D j).inputs,v<n+m+j ∧ f v=true)
        (up : f (n+m+j)=true → circuitFun (n+m) D x=true)
        (off : circuitFun (n+m) D x=false) (ha : f a=true) (hb : f b=true) : False := by
      have fired := up (gate.2 (by
        intro v hv
        refine ⟨leg.2.1 j hj v hv,?_⟩
        rw [ins] at hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl <;> assumption))
      rw [off] at fired
      contradiction
    have badL := anyOn left L (andL j hj op) (upL j path) noL
    have badR := anyOn right R (andR j hj op) (upR j path) noR
    refine ⟨a,b,ins,?_⟩
    have ta := total a ua
    have tb := total b ub
    rcases ta with la|ra
    · have lb := Bool.eq_false_iff.mpr (badL la)
      have rb := tb.resolve_left (fun a => by rw [lb] at a;contradiction)
      have ar := Bool.eq_false_iff.mpr (fun a => badR a rb)
      exact .inl ⟨Finset.mem_filter.mpr ⟨ua,ar⟩,Finset.mem_filter.mpr ⟨ub,lb⟩⟩
    · have rb := Bool.eq_false_iff.mpr (badR ra)
      have lb := tb.resolve_right (fun a => by rw [rb] at a;contradiction)
      have al := Bool.eq_false_iff.mpr (fun a => badL a lb)
      exact .inr ⟨Finset.mem_filter.mpr ⟨ua,al⟩,Finset.mem_filter.mpr ⟨ub,rb⟩⟩
