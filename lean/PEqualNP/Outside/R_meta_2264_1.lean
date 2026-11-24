import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Incomparable dirty ANDs have pure OR operands. Checking their products on the sixteen
-- edge inputs and the twenty-four maximal independent sets gives a finite synthesis problem.
-- The observation word stores eleven vertex bits per row, least significant row first.
-- Edges 513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768.
-- Independent sets 15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546.
theorem PEqualNP.Outside.R_meta_2264_1
  (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (p q j : ℕ),
    IsLeastAO G C → TopForm G C → junk G C = {p,q} → ¬InCone n C p q → ¬InCone n C q p → j∈junk G C →
    ∃ A B : Finset (Fin n),
      (∀ x, gateVal n C j x = true ↔ (∃ a∈A, x a = true) ∧ (∃ b∈B, x b = true)) ∧
      ∃ a∈A, ∃ b∈B, ¬G.Adj a b)
  (exclude : let observations : ℕ := 2144227204674281117716733471064479240048699598153746539848189215416262796910578454998445252325344873415139243611333406575860924811777
    let X : Fin 40 → Fin 11 → Bool := fun t i => observations.testBit (11*t.val+i.val)
    let Y : Fin 40 → Bool := fun t => decide (t.val < 16)
    ∀ (C : Circuit) (p q : ℕ),
    let isAnd := fun j => (gateAt C j).op = GateOp.and
    let clean := fun j => ∀ t : Fin 40, Y t = false → gateVal 11 C j (X t) = false
    IsAO2 11 C → C.size ≤ 21 → p < q → q < C.size → isAnd p → isAnd q →
    (∀ j < C.size, isAnd j → (clean j ↔ j≠p ∧ j≠q)) →
    (∀ j, j=p ∨ j=q → ∃ A B : Finset (Fin 11), ∀ t, gateVal 11 C j (X t) = true ↔
      (∃ u∈A, X t u = true) ∧ (∃ u∈B, X t u = true)) →
    (∀ i < C.size, isAnd i → clean i → ∀ j < C.size, isAnd j → ¬InCone 11 C i j) →
    ¬InCone 11 C p q → ¬InCone 11 C q p →
    (∀ j < C.size, isAnd j → clean j → InCone 11 C p j → ¬InCone 11 C q j) →
    (∀ t, circuitFun 11 C (X t) = Y t) → False) :
  ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∀ x21 ∈ x9, x12 x4 x21 → ¬x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  intro G inst C p q hg least top T Z U Anc stars traced count cover hpq hj noPQ noQP apart
  by_contra! short
  let observations : ℕ := 2144227204674281117716733471064479240048699598153746539848189215416262796910578454998445252325344873415139243611333406575860924811777
  let X : Fin 40 → Fin 11 → Bool := fun t i => observations.testBit (11*t.val+i.val)
  let Y : Fin 40 → Bool := fun t => decide (t.val < 16)
  let H := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  have check : ∀ t : Fin 40, (∃ u v : Fin 11, H.Adj u v ∧ X t u = true ∧ X t v = true) ↔ Y t = true := by
    decide +kernel
  have seen (t : Fin 40) : graphFun G ∅ (X t) = Y t := by
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ i∈(∅ : Finset (Fin 11)), X t i = true) ||
      decide (∃ u w : Fin 11, G.Adj u w ∧ X t u = true ∧ X t w = true)) = true ↔ Y t = true
    simp only [Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
    rw [hg]
    exact check t
  have pairs0 : ∀ u w : Fin 11, ¬ H.Adj u w → ∃ t, Y t = false ∧ X t u = true ∧ X t w = true := by
    decide +kernel
  have pairs : ∀ u w : Fin 11, ¬ G.Adj u w → ∃ t, Y t = false ∧ X t u = true ∧ X t w = true := by
    rw [hg]
    exact pairs0
  classical
  have jp : p∈junk G C := by rw [hj]; simp
  have jq : q∈junk G C := by rw [hj]; simp
  have info (j) (h : j∈junk G C) : j<C.size ∧ (gateAt C j).op = GateOp.and := by
    unfold junk gatesWhere at h
    rw [Finset.mem_filter,Finset.mem_range] at h
    exact ⟨h.1,h.2.1⟩
  have rep (j) (h : j∈junk G C) := normalize 11 G C p q j least top hj noPQ noQP h
  let clean (j : ℕ) := ∀ t : Fin 40, Y t=false → gateVal 11 C j (X t)=false
  have fails (j) (h : j∈junk G C) : ¬clean j := by
    intro quiet
    obtain ⟨A,B,prod,a,ha,b,hb,nonedge⟩ := rep j h
    obtain ⟨t,ht,hA,hB⟩ := pairs a b nonedge
    have on := (prod (X t)).mpr ⟨⟨a,ha,hA⟩,⟨b,hb,hB⟩⟩
    rw [quiet t ht] at on
    contradiction
  have below (j) (valid : j<C.size) (op : (gateAt C j).op = GateOp.and) (np : j≠p) (nq : j≠q) :
      BelowF G C j := by
    intro x hx
    cases hf : graphFun G ∅ x with
    | true => rfl
    | false =>
      have m : j∈junk G C := by
        unfold junk gatesWhere
        rw [Finset.mem_filter,Finset.mem_range]
        exact ⟨valid,op,valid,x,hx,hf⟩
      rw [hj] at m
      simp only [Finset.mem_insert,Finset.mem_singleton] at m
      exact (m.elim np nq).elim
  have criterion (j) (valid : j<C.size) (op : (gateAt C j).op=GateOp.and) :
      clean j ↔ j≠p ∧ j≠q := by
    constructor
    · intro c
      exact ⟨fun e => fails p jp (e ▸ c),fun e => fails q jq (e ▸ c)⟩
    · rintro ⟨np,nq⟩ t ht
      cases hon : gateVal 11 C j (X t) with
      | false => rfl
      | true =>
        have impossible := (below j valid op np nq _ hon).symm.trans ((seen t).trans ht)
        contradiction
  refine exclude C p q least.1 (by omega) hpq (info q jq).1 (info p jp).2 (info q jq).2 criterion
    ?_ ?_ noPQ noQP ?_ (fun t => (congrFun least.2.1 (X t)).trans (seen t))
  · intro j h
    have mem : j∈junk G C := by rcases h with rfl | rfl <;> assumption
    obtain ⟨A,B,prod,_⟩ := rep j mem
    exact ⟨A,B,fun t => prod (X t)⟩
  · intro i hi hop hclean j hj' hand
    obtain ⟨np,nq⟩ := (criterion i hi hop).mp hclean
    exact top i hi j hj' hop (below i hi hop np nq) hand
  · intro j hj' hop hclean
    obtain ⟨np,nq⟩ := (criterion j hj' hop).mp hclean
    have filterIntro (P : ℕ → Prop) (D : DecidablePred P) (S : Finset ℕ) (x : ℕ)
        (xs : x∈S) (xp : P x) : x ∈ @Finset.filter ℕ P D S := by
      letI : DecidablePred P := D
      exact Finset.mem_filter.mpr ⟨xs,xp⟩
    have mem : j∈tops G C := filterIntro (fun z => (gateAt C z).op=GateOp.and ∧ BelowF G C z)
      _ (Finset.range C.gates.length) j (Finset.mem_range.mpr hj') ⟨hop,below j hj' hop np nq⟩
    exact apart j mem
