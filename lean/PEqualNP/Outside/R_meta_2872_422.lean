import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- A least-edge counterexample has a matching of maximum cardinality. Deleting
-- an omitted pendant edge would keep this matching and save a gate, so every
-- maximum matching uses every pendant edge. Every remaining unmatched column
-- has two neighbours; square-freeness makes their unordered pair private to it.
-- The same count on the other side retains both original support parameters.
theorem PEqualNP.Outside.R_meta_2872_422
    (pendant : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (p : Fin n × Fin m) (C : Circuit),
    let f := fun (A : Finset (Fin n × Fin m)) (x : Fin (n+m)→Bool) =>
      decide (∃ i j, (i,j)∈A ∧ x (Fin.castAdd m i)=true ∧ x (Fin.natAdd n j)=true)
    p∈E → ((E.filter (fun q=>q.1=p.1)).card≤1 ∨ (E.filter (fun q=>q.2=p.2)).card≤1) →
    (E.erase p).Nonempty → IsAO2 (n+m) C → circuitFun (n+m) C=f E →
    ∃ D : Circuit, IsAO2 (n+m) D ∧ D.size+1≤C.size ∧ circuitFun (n+m) D=f (E.erase p))
    (narrow : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
    let f := fun (A : Finset (Fin n × Fin m)) (x : Fin (n+m)→Bool) =>
      decide (∃ i j, (i,j)∈A ∧ x (Fin.castAdd m i)=true ∧ x (Fin.natAdd n j)=true)
    let mat := fun (T : Finset (Fin n × Fin m)) => ∀ p∈T, ∀ q∈T, p.1=q.1 ∨ p.2=q.2 → p=q
    (∀ a b j k, a≠b → j≠k → ¬((a,j)∈E ∧ (a,k)∈E ∧ (b,j)∈E ∧ (b,k)∈E)) →
    (min (E.image Prod.fst).card (E.image Prod.snd).card≤2) → M⊆E → mat M →
    IsAO2 (n+m) C → circuitFun (n+m) C=f E → E.card+M.card≤C.size+1)
    (kernel : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
    let f := fun (A : Finset (Fin n × Fin m)) (x : Fin (n+m)→Bool) =>
      decide (∃ i j, (i,j)∈A ∧ x (Fin.castAdd m i)=true ∧ x (Fin.natAdd n j)=true)
    let mat := fun (T : Finset (Fin n × Fin m)) => ∀ p∈T, ∀ q∈T, p.1=q.1 ∨ p.2=q.2 → p=q
    let r := (E.image Prod.fst).card
    let c := (E.image Prod.snd).card
    (∀ a b j k, a≠b → j≠k → ¬((a,j)∈E ∧ (a,k)∈E ∧ (b,j)∈E ∧ (b,k)∈E)) → M⊆E → mat M → IsAO2 (n+m) C → circuitFun (n+m) C=f E →
    3≤min r c → c≤r.choose 2+M.card → r≤c.choose 2+M.card →
    (∀ T⊆E, mat T → T.card≤M.card ∧ (T.card=M.card → ∀ p∈E \ T,
      1<(E.filter (fun q=>q.1=p.1)).card ∧ 1<(E.filter (fun q=>q.2=p.2)).card)) →
    E.card+M.card≤C.size+1) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x4 ⊆ x3 → (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) → (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro n m E M C free hc computes sub rowMatch colMatch
  let f := fun (A : Finset (Fin n × Fin m)) (x : Fin (n+m)→Bool) =>
    decide (∃ i j, (i,j)∈A ∧ x (Fin.castAdd m i)=true ∧ x (Fin.natAdd n j)=true)
  let mat := fun (T : Finset (Fin n × Fin m)) => ∀ p∈T, ∀ q∈T, p.1=q.1 ∨ p.2=q.2 → p=q
  have matM : mat M := fun p hp q hq h=>h.elim (rowMatch p hp q hq) (colMatch p hp q hq)
  by_contra! cheap
  let bad := fun s : ℕ => ∃ F⊆E, F.card=s ∧ ∃ T⊆F, mat T ∧ ∃ D : Circuit,
    IsAO2 (n+m) D ∧ circuitFun (n+m) D=f F ∧ D.size+1<F.card+T.card
  have witness : ∃s,bad s := ⟨E.card,E,Finset.Subset.rfl,rfl,M,sub,matM,C,hc,funext computes,cheap⟩
  obtain ⟨F,subF,cF,T,subT,matT,D,law,eval,sm⟩:=Nat.find_spec witness
  let potential:= F.powerset.filter (fun S=>mat S)
  have inT : T∈potential:=Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr subT,matT⟩
  obtain ⟨U,memU,maximal⟩:=Finset.exists_max_image potential Finset.card ⟨T,inT⟩
  obtain ⟨uF,matU⟩:=Finset.mem_filter.mp memU
  have subU:=Finset.mem_powerset.mp uF
  have maxU (A) (hA:A⊆F) (hm:mat A) : A.card≤U.card :=
    maximal A (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA,hm⟩)
  have fail : D.size+1<F.card+U.card := by have:=maxU T subT matT; omega
  have square (a b : Fin n) (j k : Fin m) (ab:a≠b) (jk:j≠k) :
      ¬((a,j)∈F ∧ (a,k)∈F ∧ (b,j)∈F ∧ (b,k)∈F) := fun h=>
    free a b j k ab jk ⟨subF h.1,subF h.2.1,subF h.2.2.1,subF h.2.2.2⟩
  let rows:=F.image Prod.fst
  let cols:=F.image Prod.snd
  have large : 3≤min rows.card cols.card := by
    by_contra! small
    have h:=narrow n m F U D square (show min rows.card cols.card≤2 by omega) subU matU law eval
    omega
  have critical (A) (hA:A⊆F) (hm:mat A) (rank:A.card=U.card) (p) (hp:p∈F \ A) :
      1<(F.filter (fun q=>q.1=p.1)).card ∧ 1<(F.filter (fun q=>q.2=p.2)).card := by
    obtain ⟨pF,pA⟩:=Finset.mem_sdiff.mp hp
    by_contra! leaf
    have leaf' : (F.filter (fun q=>q.1=p.1)).card≤1 ∨ (F.filter (fun q=>q.2=p.2)).card≤1 := by omega
    have sizeF : 2≤F.card := by
      have h:rows.card≤F.card:=Finset.card_image_le
      omega
    have rem : (F.erase p).Nonempty:=Finset.card_pos.mp (by rw [Finset.card_erase_of_mem pF];omega)
    obtain ⟨B,valid,saved,val⟩:=pendant n m F p D pF leaf' rem law eval
    have small : (F.erase p).card<F.card:=Finset.card_erase_lt_of_mem pF
    have other : bad (F.erase p).card := by
      refine ⟨F.erase p,(Finset.erase_subset p F).trans subF,rfl,A,?_,hm,B,valid,val,?_⟩
      · intro q hq
        exact Finset.mem_erase.mpr ⟨fun e=>pA (e▸hq),hA hq⟩
      · rw [Finset.card_erase_of_mem pF]
        omega
    have minEdge:=Nat.find_min' witness other
    omega
  have countSide {X Y : Type} [DecidableEq X] [DecidableEq Y] (P : Finset X) (Q J : Finset Y)
      (R : X→Y→Prop)
      (rect : ∀ a b j k, a≠b → j≠k → ¬(R a j ∧ R a k ∧ R b j ∧ R b k))
      (two : ∀j∈Q, j∉J → ∃a∈P, ∃b∈P, a≠b ∧ R a j ∧ R b j) :
      Q.card≤P.card.choose 2+J.card := by
    let H:=Q \ J
    have pair (j : H) : ∃ s∈P.powersetCard 2, ∀a∈s,R a j.val := by
      obtain ⟨q,notJ⟩:=Finset.mem_sdiff.mp j.property
      obtain ⟨a,ha,b,hb,ab,ar,br⟩:=two _ q notJ
      refine ⟨{a,b},Finset.mem_powersetCard.mpr ⟨?_,by simp [ab]⟩,?_⟩
      · intro i hi; rcases (show i=a∨i=b by simpa using hi) with rfl|rfl <;> assumption
      · intro i hi; rcases (show i=a∨i=b by simpa using hi) with rfl|rfl <;> assumption
    let pick (j : H) := Classical.choose (pair j)
    have spec (j : H) : pick j∈P.powersetCard 2 ∧ ∀a∈pick j,R a j.val := Classical.choose_spec (pair j)
    let label (j : H) : ↥(P.powersetCard 2) := ⟨pick j,(spec j).1⟩
    have inj : Function.Injective label := by
      intro j k eq
      by_contra ne
      have jk:j.val≠k.val:=fun h=>ne (Subtype.ext h)
      have sets:pick j=pick k:=congrArg Subtype.val eq
      obtain ⟨a,b,ab,h⟩:=Finset.card_eq_two.mp (Finset.mem_powersetCard.mp (spec j).1).2
      have aS:a∈pick j:=by simp [h]
      have bS:b∈pick j:=by simp [h]
      exact rect a b _ _ ab jk ⟨(spec j).2 _ aS,(spec k).2 _ (sets ▸ aS),(spec j).2 _ bS,(spec k).2 _ (sets ▸ bS)⟩
    have bound := Fintype.card_le_of_injective label inj
    change Fintype.card ↥H≤Fintype.card ↥(P.powersetCard 2) at bound
    simp only [Fintype.card_coe,Finset.card_powersetCard] at bound
    have h:Q.card≤H.card+J.card:=Finset.card_le_card_sdiff_add_card
    omega
  have rowsCard : rows.card≤cols.card.choose 2+U.card := by
    have inc:=countSide cols rows (U.image Prod.fst) (fun j a=>(a,j)∈F)
      (fun j k a b jk ab h=>square a b j k ab jk ⟨h.1,h.2.2.1,h.2.1,h.2.2.2⟩) (by
      intro a ha absent
      obtain ⟨p,pF,rfl⟩:=Finset.mem_image.mp ha
      have excluded:p∉U:=fun h=>absent (Finset.mem_image_of_mem _ h)
      have d:=(critical U subU matU rfl p (Finset.mem_sdiff.mpr ⟨pF,excluded⟩)).1
      obtain ⟨q,hq,qp⟩:=Finset.exists_mem_ne d p
      obtain ⟨qF,rowsEq⟩:=Finset.mem_filter.mp hq
      refine ⟨p.2,Finset.mem_image_of_mem _ pF,q.2,Finset.mem_image_of_mem _ qF,?_,pF,?_⟩
      · exact fun eq=>qp (Prod.ext rowsEq eq.symm)
      · exact rowsEq ▸ qF)
    exact inc.trans (Nat.add_le_add_left Finset.card_image_le _)
  have colsCard : cols.card≤rows.card.choose 2+U.card := by
    have inc:=countSide rows cols (U.image Prod.snd) (fun a j=>(a,j)∈F) square (by
      intro j hj absent
      obtain ⟨p,pF,rfl⟩:=Finset.mem_image.mp hj
      have excluded:p∉U:=fun h=>absent (Finset.mem_image_of_mem _ h)
      have d:=(critical U subU matU rfl p (Finset.mem_sdiff.mpr ⟨pF,excluded⟩)).2
      obtain ⟨q,hq,qp⟩:=Finset.exists_mem_ne d p
      obtain ⟨qF,colsEq⟩:=Finset.mem_filter.mp hq
      refine ⟨p.1,Finset.mem_image_of_mem _ pF,q.1,Finset.mem_image_of_mem _ qF,?_,pF,?_⟩
      · exact fun eq=>qp (Prod.ext eq.symm colsEq)
      · exact colsEq ▸ qF)
    exact inc.trans (Nat.add_le_add_left Finset.card_image_le _)
  have result:=kernel n m F U D square subU matU law eval large colsCard rowsCard
    (fun A hA hm=>⟨maxU A hA hm,critical A hA hm⟩)
  omega
