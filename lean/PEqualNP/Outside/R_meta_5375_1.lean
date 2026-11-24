import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- A bad gate accepts a nonedge across its two owned edges. Follow a positive edge
-- on which forcing that gate low changes the output until a later AND rejects the nonedge.
theorem PEqualNP.Outside.R_meta_5375_1
    (easy : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ((G.IsAcyclic ∨ ∀ v, G.degree v ≤ 2) → HasStarProfile n G C))
    (rows : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ (j : ℕ) (a b c d : Fin n),
      a ≠ b → c ≠ d → Owns n C j a b → Owns n C j c d →
      let pairs : Finset (Fin n × Fin n) := ({a,b} : Finset _) ×ˢ ({c,d} : Finset _)
      2 ≤ (pairs.filter (fun z =>
        gateVal n C j (pairInput z.1 z.2) = true)).card)
    (mask : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → ∀ j < C.size,
      ∀ p q, ¬G.Adj p q → gateVal n C j (pairInput p q) = true →
      ∃ k < C.size, InCone n C j k ∧ (gateAt C k).op = GateOp.and ∧
        gateVal n C k (pairInput p q) = false ∧
        ∃ u v, G.Adj u v ∧ gateVal n C j (pairInput u v) = true ∧
          gateVal n C k (pairInput u v) = true ∧
          circuitFun n ⟨PEqualNP.NotPremium.replaceByConst C.gates j false,C.output⟩ (pairInput u v) = false)
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      5 ≤ G.girth → 3 ≤ G.maxDegree →
      let r := fun C j a b => G.Adj a b ∧ Owns n C j a b
      let bad := fun C j p q => ∃ b d, r C j p b ∧ r C j q d ∧
        ¬(r C j p q ∨ r C j p d ∨ r C j b q ∨ r C j b d)
      let count := fun C => {j : ℕ | ∃ p q, bad C j p q}.ncard
      ∀ (C : Circuit) (j k : ℕ) (p q u v : Fin n),
      let x := pairInput u v
      let y := pairInput p q
      let value := gateVal n C
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → bad C j p q →
      ¬G.Adj p q → value j y = true → InCone n C j k → (gateAt C k).op = GateOp.and →
      value k y = false → G.Adj u v → value k x = true →
      circuitFun n ⟨PEqualNP.NotPremium.replaceByConst C.gates j false,C.output⟩ x = false →
      ∃ E : Circuit, IsMinimalMonoCircuit n E ∧ circuitFun n E = circuitFun n C ∧ count E < count C) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 x9 : Fin x1) => x2.Adj x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9;       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ (x8 : ℕ) (x9 x10 x11 x12 : Fin x1), x6 x7 x8 x9 x10 → x6 x7 x8 x11 x12 → x6 x7 x8 x9 x11 ∨ x6 x7 x8 x9 x12 ∨ x6 x7 x8 x10 x11 ∨ x6 x7 x8 x10 x12 := by
  intro n G _ tri sq
  classical
  let r := fun C j a b => G.Adj a b ∧ Owns n C j a b
  let bad := fun C j p q => ∃ b d, r C j p b ∧ r C j q d ∧
    ¬(r C j p q ∨ r C j p d ∨ r C j b q ∨ r C j b d)
  let count := fun C => {j : ℕ | ∃ p q, bad C j p q}.ncard
  let feasible := fun t => ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
    circuitFun n C = graphFun G ∅ ∧ count C = t
  have reverse {C : Circuit} {j : ℕ} {x y : Fin n} (xy : r C j x y) : r C j y x := by
    have eq : pairInput y x = pairInput x y := by funext w; unfold pairInput; exact decide_eq_decide.mpr or_comm
    obtain ⟨adj,bound,op,on,ancestors⟩ := xy
    exact ⟨adj.symm,bound,op,eq ▸ on,fun i hi hc and => eq ▸ ancestors i hi hc and⟩
  obtain ⟨C₀,m₀,f₀,profile⟩ := easy n G tri sq
  by_cases simple : G.IsAcyclic ∨ ∀ z, G.degree z ≤ 2
  · refine ⟨C₀,m₀,f₀,?_⟩
    intro j a b c d ab cd
    rcases profile simple j ab.2.1 ab.2.2.1 with no|⟨z,center⟩
    · exact (no a b ab.1 ab.2).elim
    · rcases center a b ab.1 ab.2 with az|bz <;> rcases center c d cd.1 cd.2 with cz|dz
      · exact Or.inr (Or.inl ((az.trans cz.symm).symm ▸ cd))
      · exact Or.inl ((az.trans dz.symm).symm ▸ reverse cd)
      · exact Or.inl ((bz.trans cz.symm) ▸ ab)
      · exact Or.inr (Or.inl ((bz.trans dz.symm) ▸ ab))
  have cyclic : ¬G.IsAcyclic := fun h => simple (Or.inl h)
  have branch : ∃ z, 3 ≤ G.degree z := by
    by_contra! no
    exact simple (Or.inr fun z => by have := no z; omega)
  have existsCount : ∃ t, feasible t := ⟨_,C₀,m₀,f₀,rfl⟩
  obtain ⟨C,mc,fc,least⟩ := Nat.find_spec existsCount
  refine ⟨C,mc,fc,?_⟩
  intro j a b c d ab cd
  by_contra missing
  have dis : Disjoint ({a,b} : Finset _) {c,d} := by
    apply Finset.disjoint_left.mpr
    intro w hw hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw hz
    rcases hw with rfl|rfl <;> rcases hz with rfl|rfl
    · exact missing (Or.inr (Or.inl cd))
    · exact missing (Or.inl (reverse cd))
    · exact missing (Or.inl ab)
    · exact missing (Or.inr (Or.inl ab))
  let A : Finset (Fin n) := {a,b}
  let B : Finset (Fin n) := {c,d}
  let hotPairs := (A ×ˢ B).filter (fun z => gateVal n C j (pairInput z.1 z.2) = true)
  have two : 2 ≤ hotPairs.card := rows n C mc.1 j a b c d ab.1.ne cd.1.ne ab.2 cd.2
  have sameSide {x y s t : Fin n} (e : G.Adj x y) (hs : s ∈ ({x,y} : Finset _))
      (ht : t ∈ ({x,y} : Finset _)) (ne : s ≠ t) : G.Adj s t := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs ht
    rcases hs with rfl|rfl <;> rcases ht with rfl|rfl <;> first | exact e | exact e.symm | exact (ne rfl).elim
  have someFalse : ∃ z ∈ hotPairs, ¬G.Adj z.1 z.2 := by
    by_contra! all
    have one : hotPairs.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      rintro ⟨p,q⟩ hp ⟨v,w⟩ hv
      obtain ⟨pa,qb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      obtain ⟨va,wb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hv).1
      have pq : G.Adj p q := all _ hp
      have vw : G.Adj v w := all _ hv
      by_cases pv : p=v
      · subst v
        by_cases qw : q=w
        · exact Prod.ext rfl qw
        · exact (tri _ _ _ pq (sameSide cd.1 qb wb qw) vw.symm).elim
      have adjPV := sameSide ab.1 pa va pv
      by_cases qw : q=w
      · subst w
        exact (tri _ _ _ adjPV vw pq.symm).elim
      have pw : p ≠ w := fun h => Finset.disjoint_left.mp dis pa (h.symm ▸ wb)
      have qv : q ≠ v := fun h => Finset.disjoint_left.mp dis va (h ▸ qb)
      exact (qv (Finset.card_le_one.mp (sq p w pw) q
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,pq,(sameSide cd.1 qb wb qw).symm⟩)
        v (Finset.mem_filter.mpr ⟨Finset.mem_univ _,adjPV,vw.symm⟩))).elim
    omega
  obtain ⟨⟨p,q⟩,mem,pq⟩ := someFalse
  obtain ⟨inRows,hot⟩ := Finset.mem_filter.mp mem
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp inRows
  obtain ⟨k,hk,cone,op,cold,u,v,edge,ju,ku,pivotal⟩ := mask n G C mc fc j ab.2.1 p q pq hot
  have defect : bad C j p q := by
    have none : ¬(r C j a c ∨ r C j a d ∨ r C j b c ∨ r C j b d) := missing
    change p ∈ ({a,b} : Finset _) at hp
    change q ∈ ({c,d} : Finset _) at hq
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp hq
    rcases hp with rfl|rfl <;> rcases hq with rfl|rfl
    · exact ⟨b,d,ab,cd,none⟩
    · exact ⟨b,c,ab,reverse cd,fun h => none (by
        rcases h with h|h|h|h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h)))⟩
    · exact ⟨a,d,reverse ab,cd,fun h => none (by
        rcases h with h|h|h|h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inl h
        · exact Or.inr (Or.inl h))⟩
    · exact ⟨a,c,reverse ab,reverse cd,fun h => none (by
        rcases h with h|h|h|h
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inl h)
        · exact Or.inl h)⟩
  have girth : 5 ≤ G.egirth := by
    apply SimpleGraph.le_egirth.mpr
    intro w p cyc
    have five : 5 ≤ p.length := by
      by_contra! small
      have min := cyc.three_le_length
      have edge := fun i (hi : i < p.length) => p.adj_getVert_succ hi
      have a := edge 0 (by omega)
      have b := edge 1 (by omega)
      have c := edge 2 (by omega)
      rcases (show p.length=3 ∨ p.length=4 by omega) with h|h
      · apply tri _ _ _ a b
        simpa only [show 2+1=p.length by omega,p.getVert_length,SimpleGraph.Walk.getVert_zero] using c
      · have d := edge 3 (by omega)
        have close : G.Adj (p.getVert 3) (p.getVert 0) := by
          simpa only [show 3+1=p.length by omega,p.getVert_length,SimpleGraph.Walk.getVert_zero] using d
        have same : p.getVert 0 = p.getVert 2 ∨ p.getVert 1 = p.getVert 3 := by
          by_cases h : p.getVert 0 = p.getVert 2
          · exact Or.inl h
          · exact Or.inr (Finset.card_le_one.mp (sq _ _ h) _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,b.symm⟩)
            _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,close.symm,c⟩))
        rcases same with eq|eq
        · have := cyc.getVert_injOn' (show 0 ≤ p.length-1 by omega) (show 2 ≤ p.length-1 by omega) eq
          omega
        · have := cyc.getVert_injOn' (show 1 ≤ p.length-1 by omega) (show 3 ≤ p.length-1 by omega) eq
          omega
    exact_mod_cast five
  have finiteGirth : 5 ≤ G.girth :=
    ENat.toNat_le_toNat girth (SimpleGraph.egirth_eq_top.not.mpr cyclic)
  obtain ⟨z,high⟩ := branch
  have maxDeg := high.trans (G.degree_le_maxDegree z)
  obtain ⟨E,minE,fe,drop⟩ := repair n G finiteGirth maxDeg C j k p q u v mc fc defect pq hot cone op cold edge ku pivotal
  have best := Nat.find_min' existsCount (show feasible (count E) from ⟨E,minE,fe.trans fc,rfl⟩)
  change count E < count C at drop
  omega
