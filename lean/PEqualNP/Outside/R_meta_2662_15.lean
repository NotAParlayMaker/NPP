import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open scoped BigOperators

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_2662_15
  (matchingBound :
    ∃ d c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      ∀ T ⊆ G.edgeFinset,
        (∀ e ∈ T, ∀ u v : Fin n, e = s(u,v) → ∀ j : Fin C.gates.length, Owns n C j u v →
          ∃ S : Finset (Fin n), (∀ p ∈ S, ∀ q ∈ S, ¬G.Adj p q) ∧
            ∀ B : Finset (Fin n), B.card ≤ d →
              ∃ p ∈ S \ B, ∃ q ∈ S \ B, gateVal n C j (pairInput p q) = true) →
        T.card ≤ c * (C.size + 1))
  (rootedBound :
    ∀ k : ℕ, ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
      (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
      ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
      let blocks := fun (j : Fin C.gates.length) (B : Finset (Fin n)) =>
        ∀ p ∉ B, ∀ q ∉ B, gateVal n C j (pairInput p q) = true → G.Adj p q
      ∀ T ⊆ G.edgeFinset, ∀ B : Fin C.gates.length → Finset (Fin n),
        (∀ j, (B j).card ≤ 2 * k) →
        (∀ e ∈ T, ∀ u v : Fin n, e = s(u,v) → ∀ j : Fin C.gates.length, Owns n C j u v →
          ∀ R : Finset (Fin n), R.card ≤ 2*k → u ∉ R → v ∉ R → ¬ blocks j R) →
        (∀ e ∈ T, ∃ (u v : Fin n) (j : Fin C.gates.length), e = s(u,v) ∧ Owns n C j u v ∧
          blocks j (B j) ∧ (u ∈ B j ∨ v ∈ B j)) →
        T.card ≤ c * (C.size + 1))
  : ∃ (x1 : ℕ) (x2 : ℕ),
   ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [_x5 : DecidableRel x4.Adj],
    (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) →
     (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →
      ∀ (x8 : Circuit),
       IsMinimalMonoCircuit x3 x8 →
        circuitFun x3 x8 = graphFun x4 ∅ →
         ∀ x11 ⊆ x4.edgeFinset,
          (∀ x13 ∈ x11,
            ∀ (x15 x16 : Fin x3),
             x13 = s(x15, x16) →
              ∀ (x18 : Fin x8.gates.length),
               Owns x3 x8 (↑x18) x15 x16 →
                have x20 : Fin x3 → Fin x3 → Prop := fun (x20 x21 : Fin x3) => gateVal x3 x8 (↑x18) (pairInput x20 x21) = Bool.true;
                have x21 : Fin x3 × Fin x3 → Finset (Fin x3) := fun (x21 : Fin x3 × Fin x3) => {x21.1, x21.2} \ {x15, x16};
                x20 x15 x15 ∨ x20 x16 x16 ∨ ∃ (x22 : Finset (Fin x3 × Fin x3)), x22.card = x1 + (3 : ℕ) ∧ (∀ x23 ∈ x22, x20 x23.1 x23.2 ∧ ¬x4.Adj x23.1 x23.2) ∧ ∀ x23 ∈ x22, ∀ x25 ∈ x22, x23 ≠ x25 → Disjoint (x21 x23) (x21 x25)) →
           x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  classical
  have scatter : ∀ k : Nat, ∃ m : Nat, ∀ n : Nat, ∀ G : SimpleGraph (Fin n),
      (∀ a : Fin n, ∀ w : G.Walk a a, w.IsCycle → 5 ≤ w.length) →
      ∀ (u v : Fin n) (F : Finset (Fin n × Fin n)), m ≤ F.card →
      (∀ p ∈ F, ¬ G.Adj p.1 p.2) →
      (let support : Fin n × Fin n → Finset (Fin n) := fun p => {p.1,p.2} \ {u,v}
       ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (support p) (support q)) →
      ∃ S : Finset (Fin n), (∀ a ∈ S, ∀ b ∈ S, ¬G.Adj a b) ∧
        ∀ B : Finset (Fin n), B.card ≤ k → u ∉ B → v ∉ B →
        ∃ p ∈ F, p.1 ∈ S \ B ∧ p.2 ∈ S \ B := by
    have common_unique {V : Type} (G : SimpleGraph V)
        (girth : ∀ a : V, ∀ w : G.Walk a a, w.IsCycle → 5 ≤ w.length)
        (p q x y : V) (pq : p ≠ q)
        (xp : G.Adj x p) (xq : G.Adj x q) (yp : G.Adj y p) (yq : G.Adj y q) :
        x = y := by
      by_contra xy
      let rest : G.Walk x p := .cons xq (.cons yq.symm (.cons yp .nil))
      let walk : G.Walk p p := .cons xp.symm rest
      have path : rest.IsPath := by
        apply SimpleGraph.Walk.IsPath.mk'
        change [x,q,y,p].Nodup
        simp [xq.ne,xy,xp.ne,yq.ne',pq.symm,yp.ne]
      have tailPath : walk.tail.IsPath := by
        change (SimpleGraph.Walk.cons xp.symm rest).tail.IsPath
        simpa only [SimpleGraph.Walk.getVert_cons_succ,SimpleGraph.Walk.tail_cons,
          SimpleGraph.Walk.isPath_copy] using path
      have len : walk.length = 4 := rfl
      have cyc : walk.IsCycle :=
        SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨tailPath,by omega⟩
      have bound := girth p walk cyc
      omega

    have no_clique_sixteen {V : Type} [DecidableEq V] (G : SimpleGraph V)
        (unique : ∀ p q x y : V, p ≠ q →
          G.Adj x p → G.Adj x q → G.Adj y p → G.Adj y q → x = y)
        (support : Fin 16 → Finset V)
        (small : ∀ i, (support i).card ≤ 2)
        (apart : ∀ i j, i ≠ j → Disjoint (support i) (support j))
        (links : ∀ i j, i ≠ j → ∃ x ∈ support i, ∃ y ∈ support j, G.Adj x y) :
        False := by
      classical
      let anchor (i : Fin 3) : Fin 16 := Fin.castAdd 13 i
      let tail (t : Fin 13) : Fin 16 := Fin.natAdd 3 t
      let pool := (support (anchor 0)).product (support (anchor 1)) ∪
        (support (anchor 0)).product (support (anchor 2)) ∪
        (support (anchor 1)).product (support (anchor 2))
      have pairCard (i j : Fin 3) :
          ((support (anchor i)).product (support (anchor j))).card ≤ 4 := by
        have prodSize := Finset.card_product (support (anchor i)) (support (anchor j))
        change ((support (anchor i)).product (support (anchor j))).card = _ at prodSize
        rw [prodSize]
        exact Nat.mul_le_mul (small _) (small _)
      have poolCard : pool.card ≤ 12 := by
        have a := pairCard 0 1
        have b := pairCard 0 2
        have c := pairCard 1 2
        have h1 := Finset.card_union_le
          ((support (anchor 0)).product (support (anchor 1)))
          ((support (anchor 0)).product (support (anchor 2)))
        have h2 := Finset.card_union_le
          ((support (anchor 0)).product (support (anchor 1)) ∪
            (support (anchor 0)).product (support (anchor 2)))
          ((support (anchor 1)).product (support (anchor 2)))
        change pool.card ≤ _ at h2
        omega
      have anchorInj : Function.Injective anchor := by
        intro a b eq
        apply Fin.ext
        exact congrArg (fun i : Fin 16 => i.val) eq
      have tailInj : Function.Injective tail := by
        intro a b eq
        apply Fin.ext
        have same := congrArg Fin.val eq
        change 3 + a.val = 3 + b.val at same
        omega
      have chooseContact (t : Fin 13) (i : Fin 3) :
          ∃ x ∈ support (tail t), ∃ y ∈ support (anchor i), G.Adj x y := by
        apply links
        intro eq
        have h := congrArg Fin.val eq
        change 3 + t.val = i.val at h
        omega
      have choosePair (t : Fin 13) :
          ∃ p : V × V, p ∈ pool ∧ p.1 ≠ p.2 ∧
            ∃ x ∈ support (tail t), G.Adj x p.1 ∧ G.Adj x p.2 := by
        choose x hx y hy hAdj using chooseContact t
        let asSubtype (i : Fin 3) : ↥(support (tail t)) := ⟨x i,hx i⟩
        have noninj : ¬ Function.Injective x := by
          intro h
          have h' : Function.Injective asSubtype := by
            intro i j same
            exact h (congrArg Subtype.val same)
          have card := Fintype.card_le_of_injective asSubtype h'
          rw [Fintype.card_fin,Fintype.card_coe] at card
          have bound := small (tail t)
          omega
        have duplicate : x 0 = x 1 ∨ x 0 = x 2 ∨ x 1 = x 2 := by
          by_contra h
          apply noninj
          intro i j eq
          fin_cases i <;> fin_cases j <;> first
          | rfl
          | exact (h (Or.inl eq)).elim
          | exact (h (Or.inl eq.symm)).elim
          | exact (h (Or.inr (Or.inl eq))).elim
          | exact (h (Or.inr (Or.inl eq.symm))).elim
          | exact (h (Or.inr (Or.inr eq))).elim
          | exact (h (Or.inr (Or.inr eq.symm))).elim
        have put (i j : Fin 3) (ij : i ≠ j)
            (same : x i = x j)
            (mem : (y i,y j) ∈ pool) :
            ∃ p : V × V, p ∈ pool ∧ p.1 ≠ p.2 ∧
              ∃ w ∈ support (tail t), G.Adj w p.1 ∧ G.Adj w p.2 := by
          have disj := apart (anchor i) (anchor j) (fun h => ij (anchorInj h))
          have ne : y i ≠ y j := fun e =>
            Finset.disjoint_left.mp disj (hy i) (e.symm ▸ hy j)
          exact ⟨(y i,y j),mem,ne,x i,hx i,hAdj i,same.symm ▸ hAdj j⟩
        rcases duplicate with e | e | e
        · apply put 0 1 (by decide) e
          apply Finset.mem_union.mpr
          left
          apply Finset.mem_union.mpr
          exact Or.inl (Finset.mem_product.mpr ⟨hy 0,hy 1⟩)
        · apply put 0 2 (by decide) e
          apply Finset.mem_union.mpr
          left
          apply Finset.mem_union.mpr
          exact Or.inr (Finset.mem_product.mpr ⟨hy 0,hy 2⟩)
        · apply put 1 2 (by decide) e
          apply Finset.mem_union.mpr
          exact Or.inr (Finset.mem_product.mpr ⟨hy 1,hy 2⟩)
      choose key keyMem keyNe x xMem hx hy using choosePair
      let keys (t : Fin 13) : ↥pool := ⟨key t,keyMem t⟩
      have keyInj : Function.Injective keys := by
        intro s t h
        by_contra hst
        have eq : key s = key t := congrArg Subtype.val h
        have xeq : x s = x t :=
          unique _ _ _ _ (keyNe s) (hx s) (hy s) (eq.symm ▸ hx t) (eq.symm ▸ hy t)
        have disj := apart (tail s) (tail t) (fun h' => hst (tailInj h'))
        exact Finset.disjoint_left.mp disj (xMem s) (xeq.symm ▸ xMem t)
      have card := Fintype.card_le_of_injective keys keyInj
      rw [Fintype.card_fin,Fintype.card_coe] at card
      omega

    have insert_homogeneous {V : Type} [DecidableEq V]
        (R : V → V → Prop) (sym : ∀ x y, R x y → R y x)
        (x : V) (T : Finset V)
        (old : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → R p q)
        (added : ∀ q ∈ T, R x q) :
        ∀ p ∈ insert x T, ∀ q ∈ insert x T, p ≠ q → R p q := by
      intro p hp q hq ne
      rcases Finset.mem_insert.mp hp with ep | hp
      · subst p
        rcases Finset.mem_insert.mp hq with eq | hq
        · exact (ne eq.symm).elim
        · exact added q hq
      · rcases Finset.mem_insert.mp hq with eq | hq
        · subst q
          exact sym _ _ (added p hp)
        · exact old p hp q hq ne

    have finite_ramsey {V : Type} [DecidableEq V]
        (R : V → V → Prop) (sym : ∀ x y, R x y → R y x) :
        ∀ a b : ℕ, ∀ U : Finset V, 2^(a+b) ≤ U.card →
          (∃ K ⊆ U, K.card = a ∧ ∀ p ∈ K, ∀ q ∈ K, p ≠ q → R p q) ∨
          (∃ I ⊆ U, I.card = b ∧ ∀ p ∈ I, ∀ q ∈ I, p ≠ q → ¬R p q) := by
      classical
      have symNot : ∀ x y, ¬R x y → ¬R y x := fun x y hn h => hn (sym y x h)
      intro a
      induction a with
      | zero =>
        intro b U _
        exact Or.inl ⟨∅,Finset.empty_subset _,rfl,fun _ h _ _ _ => (Finset.notMem_empty _ h).elim⟩
      | succ a indA =>
        intro b
        induction b with
        | zero =>
          intro U _
          exact Or.inr ⟨∅,Finset.empty_subset _,rfl,fun _ h _ _ _ => (Finset.notMem_empty _ h).elim⟩
        | succ b indB =>
          intro U large
          let half := 2^(a+b+1)
          have large' : 2 * half ≤ U.card := by
            have e : a.succ+b.succ = (a+b+1)+1 := by omega
            rw [e,pow_succ,Nat.mul_comm _ 2] at large
            exact large
          have halfPos : 0 < half := by dsimp [half]; positivity
          obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
          let rest := U.erase x
          let yes := rest.filter (R x)
          let no := rest.filter (fun y => ¬R x y)
          have sums : yes.card + no.card = rest.card :=
            Finset.card_filter_add_card_filter_not (s := rest) (R x)
          have eraseSize : rest.card + 1 = U.card := Finset.card_erase_add_one hx
          have bigHalf : half ≤ yes.card ∨ half ≤ no.card := by omega
          have notRest : x ∉ rest := Finset.notMem_erase _ _
          have yesRest : yes ⊆ rest := Finset.filter_subset _ _
          have noRest : no ⊆ rest := Finset.filter_subset _ _
          have restU : rest ⊆ U := Finset.erase_subset _ _
          rcases bigHalf with bigYes | bigNo
          · have h : 2^(a+b.succ) ≤ yes.card := by
              simpa only [half,Nat.succ_eq_add_one,Nat.add_assoc] using bigYes
            rcases indA b.succ yes h with ⟨K,hK,cK,RK⟩ | ⟨I,hI,cI,RI⟩
            · have nx : x ∉ K := fun hx' => notRest (yesRest (hK hx'))
              refine Or.inl ⟨insert x K,Finset.insert_subset_iff.mpr ⟨hx,hK.trans (yesRest.trans restU)⟩,?_,?_⟩
              · rw [Finset.card_insert_of_notMem nx,cK]
              · exact insert_homogeneous R sym x K RK (fun q hq => (Finset.mem_filter.mp (hK hq)).2)
            · exact Or.inr ⟨I,hI.trans (yesRest.trans restU),cI,RI⟩
          · have h : 2^(a.succ+b) ≤ no.card := by
              have e : a.succ+b = a+b+1 := by omega
              rw [e]
              exact bigNo
            rcases indB no h with ⟨K,hK,cK,RK⟩ | ⟨I,hI,cI,RI⟩
            · exact Or.inl ⟨K,hK.trans (noRest.trans restU),cK,RK⟩
            · have nx : x ∉ I := fun hx' => notRest (noRest (hI hx'))
              refine Or.inr ⟨insert x I,Finset.insert_subset_iff.mpr ⟨hx,hI.trans (noRest.trans restU)⟩,?_,?_⟩
              · rw [Finset.card_insert_of_notMem nx,cI]
              · exact insert_homogeneous (fun p q => ¬R p q) symNot x I RI
                  (fun q hq => (Finset.mem_filter.mp (hI hq)).2)

    classical
    intro k
    let threshold := 2^(16+(k+1))
    refine ⟨4*threshold+1,?_⟩
    intro n G girth u v F fLarge nonedge apart
    let protectedVertices : Finset (Fin n) := {u,v}
    let pair (p : Fin n × Fin n) : Finset (Fin n) := {p.1,p.2}
    let support (p : Fin n × Fin n) : Finset (Fin n) := pair p \ protectedVertices
    let tag (p : Fin n × Fin n) : Finset (Fin n) := pair p ∩ protectedVertices
    let fiber (E : Finset (Fin n)) := F.filter fun p => tag p = E
    have tagCount : protectedVertices.powerset.card ≤ 4 := by
      rw [Finset.card_powerset]
      have b : protectedVertices.card ≤ 2 := Finset.card_le_two
      exact Nat.pow_le_pow_right (by decide) b
    have largeClass : ∃ E ∈ protectedVertices.powerset, threshold ≤ (fiber E).card := by
      by_contra h
      have hfiber (E : Finset (Fin n)) (hE : E ∈ protectedVertices.powerset) :
          (fiber E).card ≤ threshold := by
        by_contra! small
        exact h ⟨E,hE,Nat.le_of_lt small⟩
      have maps (p : Fin n × Fin n) (_ : p ∈ F) : tag p ∈ protectedVertices.powerset :=
        Finset.mem_powerset.mpr Finset.inter_subset_right
      have total := Finset.card_le_mul_card_image_of_maps_to (f := tag) maps threshold hfiber
      have upper := total.trans (Nat.mul_le_mul_left threshold tagCount)
      omega
    obtain ⟨E,_,largeE⟩ := largeClass
    let conflicts (p q : Fin n × Fin n) := ∃ x ∈ support p, ∃ y ∈ support q, G.Adj x y
    have flip (p q : Fin n × Fin n) : conflicts p q → conflicts q p := by
      rintro ⟨x,hx,y,hy,edge⟩
      exact ⟨y,hy,x,hx,edge.symm⟩
    have fiberSub : fiber E ⊆ F := Finset.filter_subset _ _
    have tagEq (p : Fin n × Fin n) (hp : p ∈ fiber E) : tag p = E :=
      (Finset.mem_filter.mp hp).2
    have supportSmall (p : Fin n × Fin n) : (support p).card ≤ 2 :=
      (Finset.card_le_card Finset.sdiff_subset).trans Finset.card_le_two
    obtain ⟨T,Ttag,Tcard,Tind⟩ : ∃ T ⊆ fiber E, T.card = k+1 ∧
        ∀ p ∈ T, ∀ q ∈ T, p ≠ q → ¬ conflicts p q := by
      rcases finite_ramsey conflicts flip 16 (k+1) (fiber E) largeE with
        ⟨K,hK,Kcard,clique⟩ | hInd
      · exfalso
        let e : Fin 16 ≃ ↥K := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe,Kcard])).symm
        let blocks := fun i : Fin 16 => support (e i).val
        have diff (i j : Fin 16) (ne : i ≠ j) : (e i).val ≠ (e j).val :=
          fun h => ne (e.injective (Subtype.ext h))
        apply no_clique_sixteen G (common_unique G girth) blocks
        · intro i
          exact supportSmall (e i).val
        · intro i j ne
          exact apart (e i).val (fiberSub (hK (e i).property))
            (e j).val (fiberSub (hK (e j).property)) (diff i j ne)
        · intro i j ne
          exact clique (e i).val (e i).property (e j).val (e j).property (diff i j ne)
      · exact hInd
    have sub : T ⊆ F := Ttag.trans fiberSub
    have pairIndep (p : Fin n × Fin n) (hp : p ∈ T) :
        ∀ a ∈ pair p, ∀ b ∈ pair p, ¬G.Adj a b := by
      intro a ha b hb
      have no := nonedge p (sub hp)
      simp only [pair,Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha,hb]
      · exact fun h => h.ne rfl
      · exact no
      · exact fun h => no h.symm
      · exact fun h => h.ne rfl
    have share (p q : Fin n × Fin n) (hp : p ∈ T) (hq : q ∈ T)
        (a : Fin n) (ha : a ∈ pair p) (fixed : a ∈ protectedVertices) :
        a ∈ pair q := by
      have inTag : a ∈ tag p := Finset.mem_inter.mpr ⟨ha,fixed⟩
      have same : tag p = tag q := (tagEq p (Ttag hp)).trans (tagEq q (Ttag hq)).symm
      rw [same] at inTag
      exact (Finset.mem_inter.mp inTag).1
    let S := T.biUnion pair
    refine ⟨S,?_,?_⟩
    · intro a ha b hb
      obtain ⟨p,hp,ha'⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨q,hq,hb'⟩ := Finset.mem_biUnion.mp hb
      by_cases atA : a ∈ protectedVertices
      · exact pairIndep q hq a (share p q hp hq a ha' atA) b hb'
      · by_cases atB : b ∈ protectedVertices
        · exact pairIndep p hp a ha' b (share q p hq hp b hb' atB)
        · by_cases pq : p = q
          · subst q
            exact pairIndep p hp a ha' b hb'
          · intro edge
            exact Tind p hp q hq pq
              ⟨a,Finset.mem_sdiff.mpr ⟨ha',atA⟩,b,Finset.mem_sdiff.mpr ⟨hb',atB⟩,edge⟩
    · intro B small hu hv
      have protect (a : Fin n) (ha : a ∈ B) : a ∉ protectedVertices := by
        intro hom
        simp only [protectedVertices,Finset.mem_insert,Finset.mem_singleton] at hom
        rcases hom with h | h
        · exact hu (h ▸ ha)
        · exact hv (h ▸ ha)
      have surviving : ∃ p ∈ T, p.1 ∉ B ∧ p.2 ∉ B := by
        by_contra allHit
        have blocked (p : ↥T) : ∃ a ∈ support p.val, a ∈ B := by
          by_cases h₁ : p.val.1 ∈ B
          · refine ⟨p.val.1,Finset.mem_sdiff.mpr ⟨?_,protect _ h₁⟩,h₁⟩
            exact Finset.mem_insert_self _ _
          · have h₂ : p.val.2 ∈ B := by
              by_contra h
              exact allHit ⟨p.val,p.property,h₁,h⟩
            refine ⟨p.val.2,Finset.mem_sdiff.mpr ⟨?_,protect _ h₂⟩,h₂⟩
            exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
        choose f fs fb using blocked
        let injectB (p : ↥T) : ↥B := ⟨f p,fb p⟩
        have injective : Function.Injective injectB := by
          intro p q eq
          by_contra h
          have ne : p.val ≠ q.val := fun e => h (Subtype.ext e)
          have diff := apart p.val (sub p.property) q.val (sub q.property) ne
          have same : f p = f q := congrArg Subtype.val eq
          exact Finset.disjoint_left.mp diff (fs p) (same.symm ▸ fs q)
        have bound := Fintype.card_le_of_injective injectB injective
        rw [Fintype.card_coe,Fintype.card_coe,Tcard] at bound
        omega
      obtain ⟨p,hp,hp₁,hp₂⟩ := surviving
      refine ⟨p,sub hp,Finset.mem_sdiff.mpr ⟨?_,hp₁⟩,Finset.mem_sdiff.mpr ⟨?_,hp₂⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_insert_self _ _⟩
      · exact Finset.mem_biUnion.mpr ⟨p,hp,
          Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))⟩
  -- A small vertex cover of the accepted nonedges, or a matching of the requested size.
  have coverOrPack (n k : ℕ) (good : Fin n × Fin n → Prop) :
      let support (p : Fin n × Fin n) : Finset (Fin n) := {p.1,p.2}
      (∃ F : Finset (Fin n × Fin n), F.card = k ∧ (∀ p ∈ F, good p) ∧
        ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (support p) (support q)) ∨
        ∃ B : Finset (Fin n), B.card ≤ 2*k ∧
          ∀ p, good p → ¬ Disjoint (support p) B := by
    intro support
    by_cases cov : ∃ B : Finset (Fin n), B.card ≤ 2*k ∧ ∀ p, good p → ¬ Disjoint (support p) B
    · exact Or.inr cov
    apply Or.inl
    have more (B : Finset (Fin n)) (cap : B.card ≤ 2*k) :
        ∃ p, good p ∧ Disjoint (support p) B := by
      by_contra h
      exact cov ⟨B, cap, fun p hp hD => h ⟨p,hp,hD⟩⟩
    have sizeBound (p : Fin n × Fin n) : (support p).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    have grow (r : ℕ) (hr : r ≤ k) :
        ∃ F : Finset (Fin n × Fin n), F.card = r ∧ (∀ p ∈ F, good p) ∧
          ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (support p) (support q) := by
      induction r with
      | zero => exact ⟨∅, by simp, by simp, by simp⟩
      | succ r ih =>
        obtain ⟨F, hF, hg, hdis⟩ := ih (by omega)
        let B := F.biUnion support
        have cap : B.card ≤ 2*k := calc
          B.card ≤ ∑ p ∈ F, (support p).card := Finset.card_biUnion_le
          _ ≤ ∑ p ∈ F, 2 := Finset.sum_le_sum fun p _ => sizeBound p
          _ = 2*r := by simp [hF, Nat.mul_comm]
          _ ≤ 2*k := Nat.mul_le_mul_left 2 (by omega)
        obtain ⟨p, hp, dis⟩ := more B cap
        have cross (q) (hq : q ∈ F) :
            Disjoint (support p) (support q) := dis.mono_right (Finset.subset_biUnion_of_mem support hq)
        have fresh : p ∉ F := by
          intro old
          have hmem : p.1 ∈ support p := by simp [support]
          exact Finset.disjoint_left.mp (cross p old) hmem hmem
        refine ⟨insert p F, by simp [fresh, hF], ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hp
          · exact hg x hx
        · intro q hq t ht hne
          rcases Finset.mem_insert.mp hq with hEq | hOldQ
          · subst q
            rcases Finset.mem_insert.mp ht with hEq | hOldT
            · exact (hne hEq.symm).elim
            · exact cross _ hOldT
          · rcases Finset.mem_insert.mp ht with hEq | hOldT
            · subst t
              exact (cross _ hOldQ).symm
            · exact hdis q hOldQ t hOldT hne
    exact grow k le_rfl
  obtain ⟨d, c₁, many⟩ := matchingBound
  obtain ⟨m, chooseIndependent⟩ := scatter d
  let k := m + 1
  obtain ⟨c₂, few⟩ := rootedBound k
  refine ⟨2*k, c₁+c₂, ?_⟩
  intro n G inst deg girth C least computes T sub dirty
  let support (p : Fin n × Fin n) : Finset (Fin n) := {p.1,p.2}
  let onPair (j : Fin C.gates.length) (p q : Fin n) := gateVal n C j (pairInput p q) = true
  let blocks (j : Fin C.gates.length) (B : Finset (Fin n)) :=
    ∀ p ∉ B, ∀ q ∉ B, onPair j p q → G.Adj p q
  let hasPack (j : Fin C.gates.length) := ∃ F : Finset (Fin n × Fin n), F.card = k ∧
    (∀ p ∈ F, onPair j p.1 p.2 ∧ ¬G.Adj p.1 p.2) ∧
      ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (support p) (support q)
  have caps (j : Fin C.gates.length) :
      ∃ B : Finset (Fin n), B.card ≤ 2*k ∧ (¬ hasPack j → blocks j B) := by
    rcases coverOrPack n k (fun p => onPair j p.1 p.2 ∧ ¬G.Adj p.1 p.2) with pack | ⟨B, hB, cb⟩
    · exact ⟨∅, by simp, fun hnone => (hnone pack).elim⟩
    refine ⟨B, hB, fun _ p hp q hq hon => ?_⟩
    by_contra hno
    have dis : Disjoint (support (p,q)) B := by
      apply Finset.disjoint_left.mpr
      intro a ha
      simp only [support, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hp
      · exact hq
    exact cb (p,q) ⟨hon,hno⟩ dis
  choose B cert using caps
  have robust (e : Sym2 (Fin n)) (he : e ∈ T) (u v : Fin n) (eq : e = s(u,v))
      (j : Fin C.gates.length) (own : Owns n C j u v) (R : Finset (Fin n))
      (cap : R.card ≤ 2*k) (hu : u ∉ R) (hv : v ∉ R) : ¬ blocks j R := by
    intro blocked
    rcases dirty e he u v eq j own with hu' | hv' | ⟨F,card,accept,disjoint⟩
    · exact G.loopless.irrefl u (blocked u hu u hu hu')
    · exact G.loopless.irrefl v (blocked v hv v hv hv')
    have hit (p) (hp : p ∈ F) :
        ∃ a ∈ R, a ∈ support p \ ({u,v} : Finset (Fin n)) := by
      have he := accept p hp
      by_cases ha : p.1 ∈ R
      · refine ⟨p.1, ha, Finset.mem_sdiff.mpr ⟨by simp [support], ?_⟩⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun e => hu (e ▸ ha), fun e => hv (e ▸ ha)⟩
      · have hb : p.2 ∈ R := by
          by_contra hb
          exact he.2 (blocked _ ha _ hb he.1)
        refine ⟨p.2, hb, Finset.mem_sdiff.mpr ⟨by simp [support], ?_⟩⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun e => hu (e ▸ hb), fun e => hv (e ▸ hb)⟩
    let f (p : Fin n × Fin n) := if h : p ∈ F then Classical.choose (hit p h) else u
    have selected (p) (hp : p ∈ F) : f p ∈ R ∧ f p ∈ support p \ ({u,v} : Finset (Fin n)) := by
      dsimp only [f]
      rw [dite_eq_left hp]
      exact Classical.choose_spec (hit p hp)
    have inj : (↑F : Set (Fin n × Fin n)).InjOn f := by
      intro p hp q hq same
      by_contra ne
      exact Finset.disjoint_left.mp (disjoint p hp q hq ne) (selected p hp).2 (same.symm ▸ (selected q hq).2)
    have cards : F.card ≤ R.card :=
      Finset.card_le_card_of_injOn f (fun p hp => (selected p hp).1) inj
    omega
  -- A large matching gives a robust independent set with no protected endpoints.
  have robustSet (j : Fin C.gates.length) (u : Fin n) (pack : hasPack j) :
      ∃ S : Finset (Fin n), (∀ p ∈ S, ∀ q ∈ S, ¬G.Adj p q) ∧
        ∀ B : Finset (Fin n), B.card ≤ d →
          ∃ p ∈ S \ B, ∃ q ∈ S \ B, onPair j p q := by
    obtain ⟨F, cardF, good, dis⟩ := pack
    let hit := F.filter fun p => u ∈ support p
    let kept := F.filter fun p => u ∉ support p
    have atMostOne : hit.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp q hq
      by_contra neq
      have hp' : p ∈ F ∧ u ∈ support p := Finset.mem_filter.mp hp
      have hq' : q ∈ F ∧ u ∈ support q := Finset.mem_filter.mp hq
      exact Finset.disjoint_left.mp (dis p hp'.1 q hq'.1 neq) hp'.2 hq'.2
    have splitCard : hit.card + kept.card = F.card :=
      Finset.card_filter_add_card_filter_not (s := F) (fun p => u ∈ support p)
    have enough : m ≤ kept.card := by
      change F.card = m + 1 at cardF
      omega
    have disKept : ∀ p ∈ kept, ∀ q ∈ kept, p ≠ q →
        Disjoint (support p \ ({u,u} : Finset (Fin n))) (support q \ ({u,u} : Finset (Fin n))) := by
      intro p hp q hq neq
      exact Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset
        (dis p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 neq)
    obtain ⟨S, indep, remains⟩ := chooseIndependent n G girth u u kept enough
      (fun p hp => (good p (Finset.mem_filter.mp hp).1).2) disKept
    refine ⟨S, indep, fun B cap => ?_⟩
    have small : (B.erase u).card ≤ d := (Finset.card_erase_le).trans cap
    have out : u ∉ B.erase u := Finset.notMem_erase u B
    obtain ⟨p, hp, p1, p2⟩ := remains (B.erase u) small out out
    have pData : p ∈ F ∧ u ∉ support p := Finset.mem_filter.mp hp
    have remove (x : Fin n) (hx : x ∈ S \ B.erase u) (xne : x ≠ u) : x ∈ S \ B :=
      Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
        fun hb => (Finset.mem_sdiff.mp hx).2 (Finset.mem_erase.mpr ⟨xne,hb⟩)⟩
    have p1ne : p.1 ≠ u := fun e => pData.2 (e ▸ (by simp [support] : p.1 ∈ support p))
    have p2ne : p.2 ≠ u := fun e => pData.2 (e ▸ (by simp [support] : p.2 ∈ support p))
    exact ⟨p.1, remove _ p1 p1ne, p.2, remove _ p2 p2ne, (good p pData.1).1⟩
  let stable (e : Sym2 (Fin n)) := ∀ u v : Fin n, e = s(u,v) →
    ∀ j : Fin C.gates.length, Owns n C j u v → hasPack j
  let M := T.filter stable
  let R := T \ M
  have mSub : M ⊆ T := Finset.filter_subset _ _
  have rSub : R ⊆ T := Finset.sdiff_subset
  have mCount : M.card ≤ c₁ * (C.size + 1) := by
    apply many n G deg girth C least computes M (mSub.trans sub)
    intro e he u v eq j own
    exact robustSet j u ((Finset.mem_filter.mp he).2 u v eq j own)
  have rCount : R.card ≤ c₂ * (C.size + 1) := by
    apply few n G deg girth C least computes R (rSub.trans sub) B
    · exact fun j => (cert j).1
    · exact fun e he => robust e (rSub he)
    · intro e he
      have hno : ¬ stable e := fun good =>
        (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mpr ⟨rSub he,good⟩)
      dsimp only [stable] at hno
      push Not at hno
      obtain ⟨u,v,eq,j,own,nopack⟩ := hno
      have hB := (cert j).2 nopack
      refine ⟨u,v,j,eq,own,hB,?_⟩
      by_contra! h
      exact robust e (rSub he) u v eq j own (B j) (cert j).1 h.1 h.2 hB
  rw [Nat.add_mul, ← Finset.card_sdiff_add_card_eq_card mSub]
  exact (Nat.add_le_add rCount mCount).trans (Nat.add_comm _ _).le
