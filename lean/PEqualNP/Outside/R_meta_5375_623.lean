import Mathlib
import PEqualNP.Defs

open Relation PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

-- In a connected edge relation, a first step from a crossed edge to an
-- uncrossed one would produce a path on five different vertices.
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5375_623
(normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  (∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
  let r := fun (C : Circuit) (j : ℕ) (a b : Fin n) => G.Adj a b ∧ Owns n C j a b
  let ready := fun C : Circuit => IsMinimalMonoCircuit n C ∧ circuitFun n C=graphFun G ∅ ∧
    ∀ j a b c d e,[a,b,c,d,e].Nodup → r C j a b → r C j b c → r C j c d → r C j d e → r C j a e
  ∃ C,ready C)
(branches : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), NoFourCycle G → IsMinimalMonoCircuit n C → circuitFun n C=graphFun G ∅ →
  let r := fun (C : Circuit) (j : ℕ) (a b : Fin n) => G.Adj a b ∧ Owns n C j a b
  let fork := fun (C : Circuit) (w : ℕ) => ∃ i k : ℕ,i<k ∧ k<C.gates.length ∧ w<n+i ∧ w∈(gateAt C i).inputs ∧ w∈(gateAt C k).inputs
  ∀ j a b c d,r C j a b → r C j c d → (a≠c ∧ a≠d ∧ b≠c ∧ b≠d) → ∃ s<n+j,∃ t<n+j,s≠t ∧ fork C s ∧ fork C t)
(connect : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  (∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) → NoFourCycle G →
  let r := fun (C : Circuit) (j : ℕ) (a b : Fin n) => G.Adj a b ∧ Owns n C j a b
  let ready := fun C : Circuit => IsMinimalMonoCircuit n C ∧ circuitFun n C=graphFun G ∅ ∧
    ∀ j a b c d e,[a,b,c,d,e].Nodup → r C j a b → r C j b c → r C j c d → r C j d e → r C j a e
  let linked := fun (C : Circuit) (k : ℕ) => ∀ j<k,∀ a b c d,r C j a b → r C j c d → Relation.ReflTransGen (r C j) b c
  let fork := fun (C : Circuit) (w : ℕ) => ∃ i k : ℕ,i<k ∧ k<C.gates.length ∧ w<n+i ∧ w∈(gateAt C i).inputs ∧ w∈(gateAt C k).inputs
  ∀ C j,ready C → j<C.size → linked C j → (∃ a b c d,r C j a b ∧ r C j c d ∧ ¬Relation.ReflTransGen (r C j) b c) →
  (∃ s<n+j,∃ t<n+j,s≠t ∧ fork C s ∧ fork C t) → ∃ D,ready D ∧ linked D (j+1)) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 x9 : Fin x1) => x2.Adj x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9;       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ (x8 : ℕ) (x9 x10 x11 x12 : Fin x1), x6 x7 x8 x9 x10 → x6 x7 x8 x11 x12 → x6 x7 x8 x9 x11 ∨ x6 x7 x8 x9 x12 ∨ x6 x7 x8 x10 x11 ∨ x6 x7 x8 x10 x12 := by
  classical
  let Cross {V : Type} (R : V → V → Prop) (a b c d : V) := R a c ∨ R a d ∨ R b c ∨ R b d
  let Linked {V : Type} (R : V → V → Prop) := ∀ a b c d,R a b → R c d → ReflTransGen R b c
  let Closed {V : Type} (R : V → V → Prop) := ∀ a b c d e, [a,b,c,d,e].Nodup → R a b → R b c → R c d → R d e → R a e
  have advance {V : Type} {R : V → V → Prop} (s : ∀ {x y},R x y → R y x) (ir : ∀ x,¬R x x) (cycles : Closed R)
      (a b c d e : V) (ab : R a b) (cd : R c d) (de : R d e) (prev : Cross R a b c d) : Cross R a b d e := by
    by_contra miss
    have no : ¬R a d ∧ ¬R a e ∧ ¬R b d ∧ ¬R b e := by simpa [Cross,not_or] using miss
    have path (x y : V) (xy : R x y) (yc : R y c) (xd : ¬R x d) (xe : ¬R x e) (yd : ¬R y d) (ye : ¬R y e) : False := by
      have ne {u v : V} (uv : R u v) : u≠v := fun h => ir v (h ▸ uv)
      have xc : x≠c := fun h => xd (h ▸ cd)
      have xD : x≠d := fun h => yd (h ▸ s xy)
      have xE : x≠e := fun h => ye (h ▸ s xy)
      have yD : y≠d := fun h => xd (h ▸ xy)
      have yE : y≠e := fun h => xe (h ▸ xy)
      have cE : c≠e := fun h => ye (h ▸ yc)
      exact xe (cycles x y c d e (by simp [ne xy,xc,xD,xE,ne yc,yD,yE,ne cd,cE,ne de]) xy yc cd de)
    rcases prev with ac|ad|bc|bd
    · exact path b a (s ab) ac no.2.2.1 no.2.2.2 no.1 no.2.1
    · exact no.1 ad
    · exact path a b ab bc no.1 no.2.1 no.2.2.1 no.2.2.2
    · exact no.2.2.1 bd
  have sufficient {V : Type} {R : V → V → Prop} (s : ∀ {x y},R x y → R y x) (ir : ∀ x,¬R x x) (conn : Linked R) (cycles : Closed R) :
      ∀ a b c d,R a b → R c d → Cross R a b c d := by
    intro a b c d ab cd
    have walk {u v : V} (h : ReflTransGen R u v) :
        ∀ t,R t u → Cross R a b t u → ∀ w,R v w → Cross R a b v w := by
      induction h with
      | refl =>
        intro t tu near w uw
        exact advance (R:=R) s ir cycles a b t _ w ab tu uw near
      | tail _ edge ih =>
        intro t tu near w vw
        exact advance (R:=R) s ir cycles a b _ _ w ab edge vw (ih t tu near _ edge)
    exact walk (conn a b c d ab cd) a ab (Or.inr (Or.inl ab)) d cd

  intro n G inst tri sq
  let r := fun (C : Circuit) (j : ℕ) (a b : Fin n) => G.Adj a b ∧ Owns n C j a b
  let ready := fun C : Circuit => IsMinimalMonoCircuit n C ∧ circuitFun n C=graphFun G ∅ ∧
    ∀ j a b c d e,[a,b,c,d,e].Nodup → r C j a b → r C j b c → r C j c d → r C j d e → r C j a e
  let linked := fun (C : Circuit) (k : ℕ) => ∀ j<k,∀ a b c d,r C j a b → r C j c d → Relation.ReflTransGen (r C j) b c
  let fork := fun (C : Circuit) (w : ℕ) => ∃ i k : ℕ,i<k ∧ k<C.gates.length ∧ w<n+i ∧ w∈(gateAt C i).inputs ∧ w∈(gateAt C k).inputs
  have flip {C j a b} (h : r C j a b) : r C j b a := by
    have eq : pairInput b a=pairInput a b := by
      funext i
      change decide (i=b ∨ i=a)=decide (i=a ∨ i=b)
      simp [or_comm]
    exact ⟨h.1.symm,h.2.1,h.2.2.1,eq ▸ h.2.2.2.1,fun i lt sub andi => eq ▸ h.2.2.2.2 i lt sub andi⟩
  obtain ⟨base,hbase⟩ := normalize n G tri sq
  have advanceCircuit (k : ℕ) : k≤base.size → ∃ C,ready C ∧ linked C k := by
    induction k with
    | zero => exact fun _ => ⟨base,hbase,fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ j ih =>
      intro nbound
      obtain ⟨C,hC,prior⟩ := ih (by omega)
      have size : C.size=base.size := le_antisymm (hC.1.2 base hbase.1.1 (hbase.2.1.trans hC.2.1.symm))
        (hbase.1.2 C hC.1.1 (hC.2.1.trans hbase.2.1.symm))
      by_cases yes : Linked (r C j)
      · refine ⟨C,hC,?_⟩
        intro i hi
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with less|eq
        · exact prior i less
        · exact eq ▸ yes
      · unfold Linked at yes
        push Not at yes
        obtain ⟨a,b,c,d,ab,cd,separate⟩ := yes
        have apart : Disjoint ({a,b} : Finset _) {c,d} := by
          rw [Finset.disjoint_left]
          intro u hu hv
          simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
          apply separate
          rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
          · exact .single (flip ab)
          · exact (ReflTransGen.single (flip ab)).tail (flip cd)
          · exact .refl
          · exact .single (flip cd)
        exact connect n G tri sq C j hC (by omega) prior ⟨a,b,c,d,ab,cd,separate⟩
          (branches n G C sq hC.1 hC.2.1 j a b c d ab cd (by simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_insert, Finset.mem_singleton, not_or] at apart; exact ⟨apart.1.1,apart.1.2,apart.2⟩))
  obtain ⟨C,good,linkedAll⟩ := advanceCircuit base.size le_rfl
  refine ⟨C,good.1,good.2.1,?_⟩
  intro j a b c d ab cd
  have size : C.size≤base.size := good.1.2 base hbase.1.1 (hbase.2.1.trans good.2.1.symm)
  have jBelow : j<base.size := lt_of_lt_of_le ab.2.1 size
  exact sufficient (R:=r C j) flip (fun x h => G.irrefl h.1) (linkedAll j jBelow) (good.2.2 j) a b c d ab cd
