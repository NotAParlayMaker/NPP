import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2448_619
    (compile : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (K : Finset (Fin n)), (∀u v,G.Adj u v → u∈K ∨ v∈K) → ∃C : Circuit,Monotone2 C ∧ circuitFun n C=graphFun G ∅ ∧ C.size≤G.edgeFinset.card+K.card-1 ∧ HasStarProfile n G C)
    (price : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∀a b c d,G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) → (∀S : Finset (Fin n), {e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀v∈e,v∈S}.ncard≤S.card) → Monotone2 C → circuitFun n C=graphFun G ∅ → ∃K : Finset (Fin n), (∀u v,G.Adj u v → u∈K ∨ v∈K) ∧ G.edgeFinset.card+K.card≤C.size+1)
    (localFailure : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∀a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) → (∀a b c d,G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) → Monotone2 C → circuitFun n C=graphFun G ∅ → ¬HasStarProfile n G C → ∃j u v p q,
  G.Adj u v ∧ G.Adj p q ∧ Owns n C j u v ∧ Owns n C j p q ∧
  u≠p ∧ u≠q ∧ v≠p ∧ v≠q ∧ ¬OrReaches n C C.output j ∧
  ∃r t, (r=u ∨ r=v ∨ r=p ∨ r=q) ∧ (t=u ∨ t=v ∨ t=p ∨ t=q) ∧
    ¬G.Adj r t ∧ gateVal n C j (pairInput r t)=true)
    (exchange : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), (∀a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G → IsMinimalMonoCircuit n C → circuitFun n C=graphFun G ∅ →
 (∃ S : Finset (Fin n), S.card < {e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀v∈e,v∈S}.ncard) →
 (∀ K : Finset (Fin n), (∀u v,G.Adj u v → u∈K ∨ v∈K) → C.size+1<G.edgeFinset.card+K.card) →
 (∃j u v p q,
  G.Adj u v ∧ G.Adj p q ∧ Owns n C j u v ∧ Owns n C j p q ∧
  u≠p ∧ u≠q ∧ v≠p ∧ v≠q ∧ ¬OrReaches n C C.output j ∧
  ∃r t, (r=u ∨ r=v ∨ r=p ∨ r=q) ∧ (t=u ∨ t=v ∨ t=p ∨ t=q) ∧
    ¬G.Adj r t ∧ gateVal n C j (pairInput r t)=true) → ∃ D : Circuit, Monotone2 D ∧ circuitFun n D=graphFun G ∅ ∧ D.size≤C.size ∧
 (HasStarProfile n G D ∨ (junk G D).card < (junk G C).card))
    : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6.size ≤ x7.size) ∧ PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x6 := by

  classical
  intro n G dec tri four
  let good (C : Circuit) := Monotone2 C ∧ circuitFun n C=graphFun G ∅
  let bySize (s : Nat) := ∃C : Circuit,good C ∧ C.size=s
  obtain ⟨B,mono,correct,_,_⟩ := compile n G Finset.univ (fun u _ _=>Or.inl (Finset.mem_univ u))
  have possible : ∃s,bySize s := ⟨B.size,B,⟨mono,correct⟩,rfl⟩
  let byJunk (k : Nat) := ∃C : Circuit,good C ∧ C.size=Nat.find possible ∧ (junk G C).card=k
  obtain ⟨X,gx,sx⟩ := Nat.find_spec possible
  have possibleJunk : ∃k,byJunk k := ⟨_,X,gx,sx,rfl⟩
  obtain ⟨C,g,sz,dirty⟩ := Nat.find_spec possibleJunk
  have least (D : Circuit) (h : good D) : C.size≤D.size := by
    rw [sz]
    exact Nat.find_min' possible (show bySize D.size from ⟨D,h,rfl⟩)
  have answer (D : Circuit) (hd : good D) (small : D.size≤C.size) (profile : HasStarProfile n G D) :
      ∃Y : Circuit,Monotone2 Y ∧ circuitFun n Y=graphFun G ∅ ∧
       (∀Z : Circuit,Monotone2 Z → circuitFun n Z=graphFun G ∅ → Y.size≤Z.size) ∧ HasStarProfile n G Y :=
    ⟨D,hd.1,hd.2,fun Z zm zf => small.trans (least Z ⟨zm,zf⟩),profile⟩
  by_cases ok : HasStarProfile n G C
  · exact answer C g le_rfl ok
  by_cases fits : ∃K : Finset (Fin n), (∀u v,G.Adj u v → u∈K ∨ v∈K) ∧ G.edgeFinset.card+K.card≤C.size+1
  · obtain ⟨K,cov,pay⟩ := fits
    obtain ⟨D,m,s,cost,profile⟩ := compile n G K cov
    exact answer D ⟨m,s⟩ (by omega) profile
  have dense : ∃S : Finset (Fin n),S.card<{e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀v∈e,v∈S}.ncard := by
    by_contra! sparse
    exact fits (price n G C four sparse g.1 g.2)
  have ns : NoFourCycle G := by
    intro a c ne
    apply Finset.card_le_one.mpr
    intro b hb d hd
    obtain ⟨ab,cb⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨ad,cd⟩ := (Finset.mem_filter.mp hd).2
    exact (four a b c d ab cb.symm cd ad.symm).resolve_left ne
  have minimal : IsMinimalMonoCircuit n C :=
    ⟨g.1,fun D m h=>least D ⟨m,h.trans g.2⟩⟩
  obtain ⟨D,m,s,cost,profile|shrink⟩ := exchange n G C tri ns minimal g.2 dense
    (fun K h=>Nat.lt_of_not_ge (fun le=>fits ⟨K,h,le⟩)) (localFailure n G C tri four g.1 g.2 ok)
  · exact answer D ⟨m,s⟩ cost profile
  · have equal := Nat.le_antisymm cost (least D ⟨m,s⟩)
    have other : byJunk (junk G D).card := ⟨D,⟨m,s⟩,equal.trans sz,rfl⟩
    have := Nat.find_min' possibleJunk other
    omega
