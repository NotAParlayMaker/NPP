import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge

theorem PEqualNP.Outside.R_meta_5330_753
    (support : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → G.support.ncard ≤ C.size + 1)
    (dense : ∃ d c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ∀ (S : Finset (Sym2 (Fin n))) (f : Fin 5 → Sym2 (Fin n) → ℕ),
        (∀ e ∈ S, e ∈ Ustar G C ∧ let w := fun i => f i e
          ∃ u v : Fin n, e = s(u,v) ∧ w 0 = u.val ∧ w 1 = v.val ∧
          w 2 ∈ tops G C ∧ w 3 ∈ junk G C ∧ w 4 ∈ junk G C ∧ w 3 ≠ w 4 ∧
          OrReaches n C (opnd C (w 2) 0) (w 3) ∧ OrReaches n C (opnd C (w 2) 1) (w 4) ∧
          ∀ i ∈ [w 3,w 4], gateVal n C i (pairInput u v) = true ∧
            gateVal n C i (pairInput u u) = false ∧ gateVal n C i (pairInput v v) = false) →
        (∀ x ∈ S, ∀ y ∈ S, f 0 x ≠ f 1 y ∧ f 3 x ≠ f 4 y) →
        (∀ i e, e ∈ S → d+1 ≤ (S.filter fun z => f i z = f i e).card) →
        S.card ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → {x9 ∈ PEqualNP.TopForm.Ustar x3 x5 | ∃ (x10 : Fin x2) (x11 : Fin x2), x9 = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops x3 x5, ∃ x13 ∈ PEqualNP.TopForm.junk x3 x5, ∃ x14 ∈ PEqualNP.TopForm.junk x3 x5, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x2 x5 (PEqualNP.TopForm.opnd x5 x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x13 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x2 x5 x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false}.card ≤ x1 * (x5.size + (1 : ℕ)) := by
  classical
  let := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have peel (d n : ℕ) (S : Finset (Sym2 (Fin n))) (V : Finset (Fin 5 × ℕ))
      (f : Fin 5 → Sym2 (Fin n) → ℕ)
      (labels : ∀ i e, e ∈ S → (i, f i e) ∈ V) :
      ∃ T ⊆ S, S.card ≤ T.card + d * V.card ∧
        ∀ i e, e ∈ T → d+1 ≤ (T.filter fun z => f i z = f i e).card := by
    classical
    induction V using Finset.strongInductionOn generalizing S with
    | _ V smaller =>
      by_cases done : ∀ i e, e ∈ S → d+1 ≤ (S.filter fun z => f i z = f i e).card
      · exact ⟨S, Finset.Subset.rfl, by omega, done⟩
      push Not at done
      obtain ⟨i,e,he,rare⟩ := done
      let D := S.filter fun z => f i z = f i e
      have key := labels i e he
      have drop : V.erase (i,f i e) ⊂ V := Finset.erase_ssubset key
      have remain : ∀ j z, z ∈ S \ D → (j,f j z) ∈ V.erase (i,f i e) := by
        intro j z hz
        obtain ⟨hs,hn⟩ := Finset.mem_sdiff.mp hz
        refine Finset.mem_erase.mpr ⟨?_,labels j z hs⟩
        intro eq
        have ij := congrArg Prod.fst eq
        change j=i at ij
        subst j
        exact hn (Finset.mem_filter.mpr ⟨hs,congrArg Prod.snd eq⟩)
      obtain ⟨T,hT,count,core⟩ := smaller _ drop _ remain
      refine ⟨T,hT.trans Finset.sdiff_subset,?_,core⟩
      have hd : D ⊆ S := Finset.filter_subset _ _
      have sub := Finset.card_sdiff_add_card_eq_card hd
      have hv := Finset.card_erase_add_one key
      change D.card < d+1 at rare
      have splitCost : d*V.card = d*(V.erase (i,f i e)).card + d := by
        conv_lhs => rw [← hv, Nat.mul_succ]
      omega
  have cut (n : ℕ) (S : Finset (Sym2 (Fin n))) (a b : Sym2 (Fin n) → ℕ)
      (ne : ∀ e ∈ S, a e ≠ b e) :
      ∃ T ⊆ S, S.card ≤ 4*T.card ∧ ∀ x ∈ T, ∀ y ∈ T, a x ≠ b y := by
    classical
    by_cases empty : S = ∅
    · subst S
      exact ⟨∅,by simp,by simp,by simp⟩
    let V := S.image a ∪ S.image b
    let r (e : Sym2 (Fin n)) (B : Finset ℕ) := a e ∈ B ∧ b e ∉ B
    let score (B : Finset ℕ) := (S.bipartiteBelow r B).card
    obtain ⟨M,hM,best⟩ := V.powerset.exists_max_image score ⟨∅,by simp⟩
    let k := 2^(V.card-2)
    have contains (e) (he : e ∈ S) : a e ∈ V ∧ b e ∈ V :=
      ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ he),
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)⟩
    have sizeTwo : 2 ≤ V.card := by
      obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      exact Finset.one_lt_card.mpr ⟨a e,(contains e he).1,b e,(contains e he).2,ne e he⟩
    have degree (e) (he : e ∈ S) : k ≤ (V.powerset.bipartiteAbove r e).card := by
      let A := (V.erase (a e)).erase (b e)
      have ha := (contains e he).1
      have hb := (contains e he).2
      have hb' : b e ∈ V.erase (a e) := Finset.mem_erase.mpr ⟨(ne e he).symm,hb⟩
      have asize : A.card = V.card-2 := by
        have h1 := Finset.card_erase_add_one ha
        have h2 := Finset.card_erase_add_one hb'
        change ((V.erase (a e)).erase (b e)).card = _
        omega
      have amap (B) (hB : B ∈ A.powerset) : insert (a e) B ∈ V.powerset.bipartiteAbove r e := by
        have hs := Finset.mem_powerset.mp hB
        refine (Finset.mem_bipartiteAbove r).mpr ⟨Finset.mem_powerset.mpr ?_,Finset.mem_insert_self _ _,?_⟩
        · exact Finset.insert_subset ha (hs.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)))
        · intro h
          rcases Finset.mem_insert.mp h with h|h
          · exact ne e he h.symm
          · exact Finset.notMem_erase _ _ (hs h)
      have inj : Set.InjOn (insert (a e)) (A.powerset : Set (Finset ℕ)) := by
        intro X hX Y hY eq
        have avoid (B) (hb : B ∈ A.powerset) : a e ∉ B := by
          intro h
          exact Finset.notMem_erase _ _ (Finset.mem_erase.mp (Finset.mem_powerset.mp hb h)).2
        simpa [Finset.erase_insert (avoid X hX),Finset.erase_insert (avoid Y hY)] using
          congrArg (fun s : Finset ℕ => s.erase (a e)) eq
      calc
        k = A.powerset.card := by rw [Finset.card_powerset,asize]
        _ ≤ _ := Finset.card_le_card_of_injOn (insert (a e)) amap inj
    have both : S.card*k ≤ V.powerset.card*score M :=
      Finset.card_nsmul_le_card_nsmul r degree best
    have pv : V.powerset.card = k*4 := by
      rw [Finset.card_powerset,show V.card=V.card-2+2 by omega,pow_add]
      simp [k]
    rw [pv] at both
    have sharp : S.card ≤ 4*score M := by
      refine Nat.le_of_mul_le_mul_right (c:=k) ?_ (by dsimp [k]; positivity)
      calc
        S.card*k ≤ k*4*score M := both
        _ = _ := by ring
    refine ⟨S.bipartiteBelow r M,Finset.filter_subset _ _,sharp,?_⟩
    intro x hx y hy eq
    exact (Finset.mem_bipartiteBelow r |>.mp hy).2.2 (eq ▸ (Finset.mem_bipartiteBelow r |>.mp hx).2.1)
  obtain ⟨d,c,dense⟩ := dense
  refine ⟨16*(c+d*5), ?_⟩
  intro n G dec C girth least topform
  let S := (Ustar G C).filter fun e => ∃ (x10 : Fin n) (x11 : Fin n), e = s(x10, x11) ∧ ∃ x12 ∈ PEqualNP.TopForm.tops G C, ∃ x13 ∈ PEqualNP.TopForm.junk G C, ∃ x14 ∈ PEqualNP.TopForm.junk G C, x13 ≠ x14 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 (0 : Fin (2 : ℕ))) x13 ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C x12 (1 : Fin (2 : ℕ))) x14 ∧ PEqualNP.EdgeOwnership.gateVal n C x13 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal n C x13 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal n C x13 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x10 x10) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal n C x14 (PEqualNP.EdgeOwnership.pairInput x11 x11) = Bool.false
  change S.card ≤ _
  let valid (e : Sym2 (Fin n)) (w : Fin 5 → ℕ) : Prop := ∃ u v : Fin n, e = s(u,v) ∧ w 0 = u.val ∧ w 1 = v.val ∧
          w 2 ∈ tops G C ∧ w 3 ∈ junk G C ∧ w 4 ∈ junk G C ∧ w 3 ≠ w 4 ∧
          OrReaches n C (opnd C (w 2) 0) (w 3) ∧ OrReaches n C (opnd C (w 2) 1) (w 4) ∧
          ∀ i ∈ [w 3,w 4], gateVal n C i (pairInput u v) = true ∧
            gateVal n C i (pairInput u u) = false ∧ gateVal n C i (pairInput v v) = false
  have represent (e : S) : ∃ w, valid e.val w := by
    obtain ⟨_,u,v,edge,a,atop,g,gj,h,hj,ne,rg,rh,guv,huv,gu,gv,hu,hv⟩ := Finset.mem_filter.mp e.prop
    refine ⟨![u.val,v.val,a,g,h],u,v,edge,rfl,rfl,atop,gj,hj,ne,rg,rh,?_⟩
    intro j mem
    change j ∈ [g,h] at mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact ⟨guv,gu,gv⟩
    · exact ⟨huv,hu,hv⟩
  choose pick hp using represent
  let f (i : Fin 5) (e : Sym2 (Fin n)) := if he : e ∈ S then pick ⟨e,he⟩ i else 0
  have marks (e) (he : e ∈ S) : valid e (fun i => f i e) := by
    simpa only [f,dite_eq_left he] using hp ⟨e,he⟩
  let vertices := G.support.toFinset.image Fin.val
  let domain (i : Fin 5) := if i.val < 2 then vertices else Finset.range C.size
  let V := (Finset.univ : Finset (Fin 5)).biUnion fun i => (domain i).image (Prod.mk i)
  have labels (i : Fin 5) (e) (he : e ∈ S) : (i,f i e) ∈ V := by
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨_,?_,rfl⟩⟩
    obtain ⟨u,v,edge,pu,pv,ta,tg,th,_⟩ := marks e he
    have inU : e ∈ Ustar G C := (Finset.mem_filter.mp he).1
    have ge : s(u,v) ∈ G.edgeFinset := edge ▸ (Finset.mem_sdiff.mp inU).1
    have uv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp ge
    have vu0 : u ∈ G.support := ⟨v,uv⟩
    have vv0 : v ∈ G.support := ⟨u,uv.symm⟩
    have vu : u.val ∈ vertices := Finset.mem_image.mpr ⟨u,Set.mem_toFinset.mpr vu0,rfl⟩
    have vv : v.val ∈ vertices := Finset.mem_image.mpr ⟨v,Set.mem_toFinset.mpr vv0,rfl⟩
    fin_cases i
    · change f 0 e ∈ vertices
      rw [show f 0 e = u.val from pu]
      exact vu
    · change f 1 e ∈ vertices
      rw [show f 1 e = v.val from pv]
      exact vv
    · exact (Finset.mem_filter.mp ta).1
    · exact (Finset.mem_filter.mp tg).1
    · exact (Finset.mem_filter.mp th).1
  have apart (e) (he : e ∈ S) : f 0 e ≠ f 1 e ∧ f 3 e ≠ f 4 e := by
    obtain ⟨u,v,h,pu,pv,_,_,_,neq,_⟩ := marks e he
    have ge : s(u,v) ∈ G.edgeFinset := h ▸ (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1
    have uv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp ge
    change f 0 e = u.val at pu
    change f 1 e = v.val at pv
    exact ⟨by rw [pu,pv]; exact fun eq => uv.ne (Fin.ext eq),neq⟩
  obtain ⟨A,hA,sA,vCut⟩ := cut n S (f 0) (f 1) (fun e he => (apart e he).1)
  obtain ⟨B,hB,sB,gCut⟩ := cut n A (f 3) (f 4) (fun e he => (apart e (hA he)).2)
  obtain ⟨T,hT,loss,loads⟩ := peel d n B V f (fun i e h => labels i e (hA (hB h)))
  have sub := hT.trans (hB.trans hA)
  have core := dense n G C girth least topform T f (fun e he =>
    ⟨(Finset.mem_filter.mp (sub he)).1,marks e (sub he)⟩)
    (fun x hx y hy => ⟨vCut x (hB (hT hx)) y (hB (hT hy)),gCut x (hT hx) y (hT hy)⟩) loads
  have nv : vertices.card ≤ C.size+1 := by
    calc
      _ ≤ G.support.toFinset.card := Finset.card_image_le
      _ = G.support.ncard := (Set.toFinset_card _).trans (Set.fintypeCard_eq_ncard _)
      _ ≤ _ := support n G C least
  have nd (i : Fin 5) : (domain i).card ≤ C.size+1 := by
    unfold domain
    split
    · exact nv
    · simp
  have resources : V.card ≤ 5*(C.size+1) := by
    calc
      _ ≤ ∑ i : Fin 5, ((domain i).image (Prod.mk i)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin 5, (C.size+1) :=
        Finset.sum_le_sum fun i _ => Finset.card_image_le.trans (nd i)
      _ = _ := by simp
  calc
    S.card ≤ 4*A.card := sA
    _ ≤ 16*B.card := by omega
    _ ≤ 16*(T.card + d*V.card) := Nat.mul_le_mul_left _ loss
    _ ≤ 16*(c*(C.size+1) + d*(5*(C.size+1))) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add core (Nat.mul_le_mul_left d resources))
    _ = _ := by ring
