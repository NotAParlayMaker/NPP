import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
theorem PEqualNP.Outside.R_meta_4079_619
  (paid : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), IsLeastAO G C → TopForm G C →
    ∀u v : Fin n, s(u,v)∈Ustar G C →
      (∃a∈centreless G C,gateVal n C a (pairInput u v)=true) ∨
      ∃m∈orN G C \ lam G C, ∃g∈junk G C, n+g∈(gateAt C m).inputs ∧
        gateVal n C g (pairInput u v)=true ∧ gateVal n C m (pairInput u v)=true)
  (geometry : let G : SimpleGraph (Fin 11) := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).map (fun e => (e / 11,e % 11)))
  (∀z∈([8,9,10]:List (Fin 11)),(G.edgeFinset.filter (fun e=>z∈e)).card=4) ∧
  ∀ S : Finset (Sym2 (Fin 11)), S⊆G.edgeFinset → 4≤S.card →
    (∃e∈S,∃f∈S,∀v:Fin 11,v∈e→v∉f) ∨
    ∃z∈([8,9,10]:List (Fin 11)),S=G.edgeFinset.filter (fun e=>z∈e))
  (disjointCase : let G := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).map (fun e => (e / 11,e % 11)))
  ∀ (C:Circuit), C.size≤21 → IsLeastAO G C → TopForm G C →
    let J:=junk G C; let U:=Ustar G C; let A:=centreless G C; let B:=orN G C \ lam G C
    J.card=2 → (∃e∈U,∃f∈U,∀v:Fin 11,v∈e→v∉f) → 4≤U.card →
    (∃X⊆U, 3≤X.card ∧ ∀a∈A∪B∪J, let k:=(X∩gammaE G C a).card
        k=0 ∨ (if a∈A then 3 else 2)≤k) → U.card≤2*A.card+2+B.card)
  (starCase : let G := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).map (fun e => (e / 11,e % 11)))
  ∀ (C:Circuit), C.size≤21 → IsLeastAO G C → TopForm G C →
    let J:=junk G C; let U:=Ustar G C
    J.card=2 → centreless G C=∅ → ∀m, orN G C \ lam G C={m} →
    (∃z∈([8,9,10]:List (Fin 11)), U=G.edgeFinset.filter (fun e=>z∈e)) →
    U⊆gammaE G C m → U⊆(J.filter (fun g=>11+g∈(gateAt C m).inputs)).biUnion (gammaE G C) → False) :
let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) → (∀ (x7 x8 : Fin (11 : ℕ)), s(x7, x8) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x10 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x10 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  let G:=edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).map (fun e => (e / 11,e % 11)))
  intro _graph C cap least top countJ cover many _
  let U:=Ustar G C
  let A:=centreless G C
  let B:=orN G C \ lam G C
  let J:=junk G C
  let rows:=gammaE G C
  let used (pool:Finset Nat) (rows:Nat→Finset (Sym2 (Fin 11))) (X:Finset (Sym2 (Fin 11))) :=
    pool.filter (fun g=>(X∩rows g).Nonempty)
  let cost (A B J:Finset Nat) (rows:Nat→Finset (Sym2 (Fin 11))) (X:Finset (Sym2 (Fin 11))) :=
    2*(used A rows X).card+(used B rows X).card+(used J rows X).card
  have monoUsed (pool:Finset Nat) (rows:Nat→Finset (Sym2 (Fin 11))) {X Y:Finset (Sym2 (Fin 11))} (h:X⊆Y) :
      used pool rows X ⊆ used pool rows Y := by
    intro a ha
    obtain ⟨m,e,he⟩:=Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨m,e,Finset.mem_inter.mpr ⟨h (Finset.mem_inter.mp he).1,(Finset.mem_inter.mp he).2⟩⟩
  have upper (A B J:Finset Nat) (rows:Nat→Finset (Sym2 (Fin 11))) (X:Finset (Sym2 (Fin 11))) :
      cost A B J rows X≤2*A.card+B.card+J.card := by
    have each (S:Finset Nat): (used S rows X).card≤S.card:=Finset.card_le_card (Finset.filter_subset _ _)
    have hA:=each A; have hB:=each B; have hJ:=each J
    dsimp only [cost]
    omega
  have minimum (A B J:Finset Nat) (rows:Nat→Finset (Sym2 (Fin 11))) (S:Finset (Sym2 (Fin 11)))
      (small:2*A.card+B.card+J.card<S.card) :
      ∃X⊆S, cost A B J rows X<X.card ∧ ∀Y⊆X,Y.card<X.card → Y.card≤cost A B J rows Y := by
    classical
    let P (k:Nat) := ∃U⊆S,U.card=k ∧ cost A B J rows U<U.card
    have someP : ∃k,P k := ⟨_,S,Finset.Subset.rfl,rfl,lt_of_le_of_lt (upper A B J rows S) small⟩
    obtain ⟨X,sub,eq,hX⟩:=Nat.find_spec someP
    refine ⟨X,sub,hX,?_⟩
    intro Y subY card
    apply Nat.le_of_not_gt
    intro hy
    exact Nat.find_min someP (by omega : Y.card < Nat.find someP) ⟨Y,subY.trans sub,rfl,hy⟩
  have drop (pool:Finset Nat) (rows:Nat→Finset (Sym2 (Fin 11))) (X:Finset (Sym2 (Fin 11))) (g:Nat)
      (hg:g∈used pool rows X) : (used pool rows (X \ rows g)).card < (used pool rows X).card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨monoUsed _ _ Finset.sdiff_subset,?_⟩
    intro eq
    have haveG:g∈used pool rows (X \ rows g):=eq ▸ hg
    obtain ⟨_,e,h⟩:=Finset.mem_filter.mp haveG
    obtain ⟨hx,hr⟩:=Finset.mem_inter.mp h
    exact (Finset.mem_sdiff.mp hx).2 hr

  have multiplicity (A B J:Finset Nat) (rows:Nat→Finset (Sym2 (Fin 11))) (S:Finset (Sym2 (Fin 11)))
      (small:2*A.card+B.card+J.card<S.card) :
      ∃X⊆S,cost A B J rows X<X.card ∧
        (∀g∈used A rows X,3≤(X∩rows g).card) ∧
        (∀g∈used B rows X,2≤(X∩rows g).card) ∧ (∀g∈used J rows X,2≤(X∩rows g).card) := by
    classical
    obtain ⟨X,sub,bad,minimal⟩:=minimum A B J rows S small
    refine ⟨X,sub,bad,?_⟩
    have lower (pool:Finset Nat) (g:Nat) (hg:g∈used pool rows X) :
        (X \ rows g).card≤cost A B J rows (X \ rows g) := by
      have pos:=Finset.card_pos.mpr (Finset.mem_filter.mp hg).2
      have sum:=Finset.card_sdiff_add_card_inter X (rows g)
      exact minimal _ Finset.sdiff_subset (by omega)
    have noninc (pool:Finset Nat) (g:Nat) : (used pool rows (X \ rows g)).card≤(used pool rows X).card:=
      Finset.card_le_card (monoUsed _ _ Finset.sdiff_subset)
    dsimp only [cost] at bad lower
    constructor
    · intro g hg
      have l:=lower A g hg; have d:=drop A rows X g hg;have b:=noninc B g;have j:=noninc J g
      have sum:=Finset.card_sdiff_add_card_inter X (rows g)
      omega
    constructor
    · intro g hg
      have l:=lower B g hg; have d:=drop B rows X g hg;have a:=noninc A g;have j:=noninc J g
      have sum:=Finset.card_sdiff_add_card_inter X (rows g)
      omega
    · intro g hg
      have l:=lower J g hg; have d:=drop J rows X g hg;have a:=noninc A g;have b:=noninc B g
      have sum:=Finset.card_sdiff_add_card_inter X (rows g)
      omega
  change J.card=2 at countJ
  change 3≤U.card at many
  change U.card≤2*A.card+J.card+B.card
  have hit (u v:Fin 11) (j:Nat) (m:s(u,v)∈U) (on:gateVal 11 C j (pairInput u v)=true) :
      s(u,v)∈rows j := Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp m).1,u,v,rfl,on⟩
  have collect (e:Sym2 (Fin 11)) (mem:e∈U):
      ((∃a∈A,e∈rows a) ∨ ∃m∈B,∃g∈J,11+g∈(gateAt C m).inputs ∧ e∈rows g ∧ e∈rows m) ∧
      ∃g∈J,e∈rows g := by
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨g,hg,active⟩:=cover u v mem
      refine ⟨?_,g,hg,hit u v g mem active⟩
      rcases paid 11 G C least top u v mem with ⟨a,ha,atA⟩|⟨m,hm,g,hg,reads,atG,atM⟩
      · exact Or.inl ⟨a,ha,hit u v a mem atA⟩
      · exact Or.inr ⟨m,hm,g,hg,reads,hit u v g mem atG,hit u v m mem atM⟩
  have paidCount : 1≤A.card+B.card := by
    obtain ⟨e,he⟩:=Finset.card_pos.mp (show 0<U.card by omega)
    rcases (collect e he).1 with ⟨a,ha,_⟩|⟨m,hm,_⟩
    · have := Finset.card_pos.mpr (show A.Nonempty from ⟨a,ha⟩); omega
    · have := Finset.card_pos.mpr (show B.Nonempty from ⟨m,hm⟩); omega
  by_contra! short
  have atFour:4≤U.card:=by omega
  obtain ⟨starSize,shape⟩:=geometry
  rcases shape U Finset.sdiff_subset atFour with separated|⟨z,hz,zshape⟩
  · obtain ⟨X,hX,bad,am,bm,jm⟩:=multiplicity A B J rows U (by omega)
    have nz:X.Nonempty:=Finset.card_pos.mp (by omega)
    obtain ⟨e,he⟩:=nz
    have active (S : Finset Nat) (g : Nat) (h:g∈S) (hg:e∈rows g) : g∈used S rows X :=
      Finset.mem_filter.mpr ⟨h,e,Finset.mem_inter.mpr ⟨he,hg⟩⟩
    obtain ⟨pn,g,hg,atG⟩:=collect e (hX he)
    have hj:=Finset.card_pos.mpr (show (used J rows X).Nonempty from ⟨g,active J g hg atG⟩)
    have hc:3≤X.card:=by
      dsimp only [cost] at bad
      rcases pn with ⟨a,ha,aa⟩|⟨m,hm,_,_,_,_,atM⟩
      · have :=Finset.card_pos.mpr (show (used A rows X).Nonempty from ⟨a,active A a ha aa⟩); omega
      · have :=Finset.card_pos.mpr (show (used B rows X).Nonempty from ⟨m,active B m hm atM⟩); omega
    have localBounds (a:Nat) (inc:a∈A∪B∪J) : (X∩rows a).card=0 ∨ (if a∈A then 3 else 2)≤(X∩rows a).card := by
      by_cases zero:(X∩rows a).card=0
      · exact Or.inl zero
      right
      have positive:(X∩rows a).Nonempty:=Finset.card_pos.mp (by omega)
      by_cases ha:a∈A
      · rw [if_pos ha]; exact am a (Finset.mem_filter.mpr ⟨ha,positive⟩)
      · rw [if_neg ha]
        rcases Finset.mem_union.mp inc with x|x
        · exact bm a (Finset.mem_filter.mpr ⟨(Finset.mem_union.mp x).resolve_left ha,positive⟩)
        · exact jm a (Finset.mem_filter.mpr ⟨x,positive⟩)
    have en:=disjointCase C cap least top countJ separated atFour ⟨X,hX,hc,localBounds⟩
    change U.card≤2*A.card+2+B.card at en
    omega
  · have sc:U.card=4:=zshape ▸ starSize z hz
    have empty:A=∅:=Finset.card_eq_zero.mp (by omega)
    have single:B.card=1:=by omega
    obtain ⟨m,eq⟩:=Finset.card_eq_one.mp single
    have here (e:Sym2 (Fin 11)) (he:e∈U): ∃g∈J,11+g∈(gateAt C m).inputs ∧ e∈rows g ∧ e∈rows m := by
      rcases (collect e he).1 with ⟨a,ha,_⟩|⟨q,hq,rest⟩
      · rw [empty] at ha;exact (Finset.notMem_empty _ ha).elim
      · rw [eq,Finset.mem_singleton] at hq;subst q;exact rest
    apply starCase C cap least top countJ empty m eq ⟨z,hz,zshape⟩
    · intro e he;obtain ⟨_,_,_,_,hm⟩:=here e he;exact hm
    · intro e he;obtain ⟨g,hg,reader,atG,_⟩:=here e he
      exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_filter.mpr ⟨hg,reader⟩,atG⟩
