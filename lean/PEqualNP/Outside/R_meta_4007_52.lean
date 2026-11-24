import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- On a negative input, the first junk gate can have a witness of size two.
-- A minimal three-vertex witness for the second must use the first.
set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_4007_52
    (blind : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let on := fun (I : Finset (Fin n)) => graphFun G ∅ (fun v => decide (v ∈ I))
      ∀ (S : Finset (Fin n)) (x : Fin n), x ∉ S → (∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) →
        (∀ I : Finset (Fin n), S ⊆ I → on I = on (insert x I)) →
        (∀ t ∈ S, ¬ G.Adj x t) ∧ ∀ y, G.Adj x y → ∃ t ∈ S, G.Adj t y)
    (supports :
      let G := edgeGraph 11 (((List.range 121).filter (158533781311273338870281307648 : Nat).testBit).map fun k => (k/11,k%11))
      let mask := fun (I : Finset (Fin 11)) (v : Fin 11) => decide (v ∈ I)
      let on := fun I => graphFun G ∅ (mask I)
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → ∀ g h, junk G C = {g,h} → InCone 11 C g h →
        ∃ f : Nat → Finset (Fin 11) → Prop,
        (∃ S, f g S) ∧ (∃ S, f h S) ∧ (∀ S, f g S → S.card ≤ 2) ∧
        (∀ S, f h S → S.card ≤ 3 ∧ (S.card = 3 → ∃ A, f g A ∧ A ⊆ S)) ∧
        (∀ j S, f j S → ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) ∧
        (∀ I, on I = false → (gateVal 11 C h (mask I) = true ↔ ∃ S, f h S ∧ S ⊆ I)) ∧
        ∀ x : Fin 11, ((C.gates.flatMap Gate.inputs).count x.val = 1 ∧ ∃ r ∈ C.gates, r.op = .or ∧ x.val ∈ r.inputs) → ∃ j, (j = g ∨ j = h) ∧ ∀ S, f j S →
          x ∉ S ∧ ∀ I : Finset (Fin 11), S ⊆ I → on I = on (insert x I))
    (budget :
      let G := edgeGraph 11 (((List.range 121).filter (158533781311273338870281307648 : Nat).testBit).map fun k => (k/11,k%11))
      ∀ (C : Circuit) (g h : Nat), IsLeastAO G C → TopForm G C →
        junk G C = {g,h} → InCone 11 C g h →
        let U := Ustar G C
        let Q := centreless G C
        let d := 2*Q.card + (orN G C \ lam G C).card
        let onlyOr := fun (x : Fin 11) => ((C.gates.flatMap Gate.inputs).count x.val = 1 ∧ ∃ r ∈ C.gates, r.op = .or ∧ x.val ∈ r.inputs)
        3+d ≤ 2*U.card → (tops G C \ Q).card+d ≤ 4+U.card →
        (∀ x y, s(x,y) ∈ U → ∃ j ∈ junk G C, ∀ b : Fin 2, x ∈ side C j b ∨ y ∈ side C j b) →
        ((∀ x : Fin 11, onlyOr x → x.val < 4) ∨
          (∀ x : Fin 11, onlyOr x → x = 5) ∧
          ∀ I : Finset (Fin 11), let z := fun v => decide (v ∈ I)
            graphFun G ∅ z = false → (gateVal 11 C h z = true ↔ (1 : Fin 11) ∈ I ∧ 7 ∈ I ∧ 10 ∈ I)) →
        22 ≤ C.size) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : ℕ := (2 : ℕ) * x12.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;             (3 : ℕ) + x13 ≤ (2 : ℕ) * x11.card → (PEqualNP.TopForm.tops x1 x3 \ x12).card + x13 ≤ (4 : ℕ) + x11.card → (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ PEqualNP.TopForm.junk x1 x3, ∀ (x20 : Fin (2 : ℕ)), x16 ∈ PEqualNP.TopForm.side x3 x19 x20 ∨ x17 ∈ PEqualNP.TopForm.side x3 x19 x20) → (22 : ℕ) ≤ x3.size := by
  intro H inst C g h hg least top pair nested U Q d lo hi edges
  let G := edgeGraph 11 (((List.range 121).filter (158533781311273338870281307648 : Nat).testBit).map fun k => (k/11,k%11))
  have same : H = G := hg
  subst H
  have uniqueInst : inst = (inferInstance : DecidableRel G.Adj) := Subsingleton.elim _ _
  cases uniqueInst
  let F := edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List Nat).map fun k => (k/11,k%11))
  let T : Finset (Fin 11) := {1,7,10}
  let good := fun (S : Finset (Fin 11)) => ∀ u ∈ S, ∀ v ∈ S, ¬F.Adj u v
  let block := fun (S : Finset (Fin 11)) (x : Fin 11) => x ∉ S ∧ (∀ t ∈ S, ¬F.Adj x t) ∧
    ∀ y : Fin 11, F.Adj x y → ∃ t ∈ S, F.Adj t y
  let cls := fun (x : Fin 11) (S : Finset (Fin 11)) =>
    good S → block S x → (4 ≤ x.val → S = T ∧ x = 5) ∧ (S ⊆ T → x = 5)
  have tuple (x : Fin 11) : ∀ a b c : Fin 11, cls x {a,b,c} := by
    dsimp only [cls,good,block,T,F]
    fin_cases x <;> decide +kernel
  have geom (S : Finset (Fin 11)) (hs : S.card ≤ 3) (x : Fin 11) : cls x S := by
    by_cases he : S = ∅
    · subst S
      intro _ h
      have noIso : ∀ v : Fin 11, ∃ w : Fin 11, F.Adj v w := by
        dsimp only [F]
        decide +kernel
      obtain ⟨w,hw⟩ := noIso x
      obtain ⟨t,ht,_⟩ := h.2.2 w hw
      simp at ht
    have hn := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    rcases (by omega : S.card = 1 ∨ S.card = 2 ∨ S.card = 3) with h | h | h
    · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h
      simpa using tuple x a a a
    · obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp h
      simpa using tuple x a b b
    · obtain ⟨a,b,c,_,_,_,rfl⟩ := Finset.card_eq_three.mp h
      exact tuple x a b c
  apply budget C g h least top pair nested lo hi edges
  by_cases light : ∀ x : Fin 11, ((C.gates.flatMap Gate.inputs).count x.val = 1 ∧ ∃ r ∈ C.gates, r.op = .or ∧ x.val ∈ r.inputs) → x.val < 4
  · exact Or.inl light
  push_neg at light
  obtain ⟨v,hv,large⟩ := light
  obtain ⟨f,⟨A,fa⟩,⟨B,fb⟩,hA,hB,ind,sem,cover⟩ := supports C least top g h pair nested
  have priv (x : Fin 11) (hx : ((C.gates.flatMap Gate.inputs).count x.val = 1 ∧ ∃ r ∈ C.gates, r.op = .or ∧ x.val ∈ r.inputs)) : ∃ j, (j=g ∨ j=h) ∧ ∀ S, f j S → block S x := by
    obtain ⟨j,hj,allS⟩ := cover x hx
    refine ⟨j,hj,fun S hs => ?_⟩
    obtain ⟨absent,eq⟩ := allS S hs
    exact ⟨absent,blind 11 G S x absent (ind j S hs) eq⟩
  have ct : T.card = 3 := by decide
  obtain ⟨j,hj,hblock⟩ := priv v hv
  have allT : ∀ S, f h S → S = T := by
    rcases hj with e | e <;> subst j
    · have sizeA := hA A fa
      have eq := ((geom A (by omega) v (ind g A fa) (hblock A fa)).1 large).1
      rw [eq,ct] at sizeA
      omega
    · exact fun S hs => ((geom S (hB S hs).1 v (ind h S hs) (hblock S hs)).1 large).1
  have ft : f h T := allT B fb ▸ fb
  obtain ⟨a,ha,sub⟩ := (hB T ft).2 ct
  refine Or.inr ⟨?_,?_⟩
  · intro x hx
    obtain ⟨k,hk,hblock'⟩ := priv x hx
    rcases hk with e | e <;> subst k
    · have sz := hA a ha
      exact (geom a (by omega) x (ind g a ha) (hblock' a ha)).2 sub
    · exact (geom T (by omega) x (ind h T ft) (hblock' T ft)).2 (by rfl)
  · intro I z neg
    rw [sem I neg]
    constructor
    · rintro ⟨S,hs,subS⟩
      rw [allT S hs] at subS
      exact ⟨subS (by simp [T]),subS (by simp [T]),subS (by simp [T])⟩
    · rintro ⟨i,j',k⟩
      exact ⟨T,ft,Finset.insert_subset i (Finset.insert_subset j' (Finset.singleton_subset_iff.mpr k))⟩
