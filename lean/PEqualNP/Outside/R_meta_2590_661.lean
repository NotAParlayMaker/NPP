import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.ReadTwo

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_2590_661
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → Monotone2 C → circuitFun n C=graphFun G ∅ →
      ∃ A : Circuit, IsLeastAO G A ∧ TopForm G A ∧ A.size≤C.size)
    (smallProjection : ∀ (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj] (A : Circuit) (M : Finset (Sym2 (Fin 10)))
      (I : Finset (Fin A.size)),
      G.edgeFinset={s(0,1), s(1,2), s(2,3), s(3,4), s(4,0), s(0,5), s(1,6), s(2,7), s(3,8), s(4,9), s(5,7), s(7,9), s(9,6), s(6,8), s(8,5)} → IsLeastAO G A → TopForm G A → A.size≤19 →
      (∀ e : Sym2 (Fin 10), e∈M ↔ e∈G.edgeFinset ∧ ¬(∃ (u v : Fin 10) (j p q : ℕ), e=s(u,v) ∧ andOn A j p q ∧ orp A 10 u.val p ∧ orp A 10 v.val q ∧ orp A 10 (10+j) A.output)) → (∀ j : Fin A.size, j∈I ↔ (A.gates.get j).op=.and ∧ ¬orp A 10 (10+j.val) A.output) → (M.card ≤ 3 ∨ I.card ≤ 1) → False)
    (largeProjection : ∀ (G : SimpleGraph (Fin 10)) [DecidableRel G.Adj] (A : Circuit) (M : Finset (Sym2 (Fin 10)))
      (I : Finset (Fin A.size)),
      G.edgeFinset={s(0,1), s(1,2), s(2,3), s(3,4), s(4,0), s(0,5), s(1,6), s(2,7), s(3,8), s(4,9), s(5,7), s(7,9), s(9,6), s(6,8), s(8,5)} → IsLeastAO G A → TopForm G A → A.size≤19 →
      (∀ e : Sym2 (Fin 10), e∈M ↔ e∈G.edgeFinset ∧ ¬(∃ (u v : Fin 10) (j p q : ℕ), e=s(u,v) ∧ andOn A j p q ∧ orp A 10 u.val p ∧ orp A 10 v.val q ∧ orp A 10 (10+j) A.output)) → (∀ j : Fin A.size, j∈I ↔ (A.gates.get j).op=.and ∧ ¬orp A 10 (10+j.val) A.output) → 4 ≤ M.card → 2 ≤ I.card → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → ¬∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4) = (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C model budget computes
  let E : Finset (Sym2 (Fin 10)) := {s(0,1), s(1,2), s(2,3), s(3,4), s(4,0), s(0,5), s(1,6), s(2,7), s(3,8), s(4,9), s(5,7), s(7,9), s(9,6), s(6,8), s(8,5)}
  let G : SimpleGraph (Fin 10) := SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin 10)))
  letI : DecidableRel G.Adj := fun a b=>
    inferInstanceAs (Decidable (s(a,b)∈E ∧ a≠b))
  letI : Fintype G.edgeSet := G.fintypeEdgeSet
  have loops : ∀ a : Fin 10, s(a,a)∉E := by decide +kernel
  have edges : G.edgeFinset=E := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      calc
        s(a,b)∈G.edgeFinset ↔ G.Adj a b := SimpleGraph.mem_edgeFinset
        _ ↔ s(a,b)∈E := by
          change (s(a,b)∈E ∧ a≠b) ↔ s(a,b)∈E
          exact ⟨And.left,fun h=>⟨h,fun eq=>loops a (eq.symm ▸ h)⟩⟩
  have explicit : ∀ x : Fin 10→Bool, graphFun G ∅ x=(fun (v : Fin (10 : ℕ) → Bool) => v (0 : Fin (10 : ℕ)) && v (1 : Fin (10 : ℕ)) || v (1 : Fin (10 : ℕ)) && v (2 : Fin (10 : ℕ)) || v (2 : Fin (10 : ℕ)) && v (3 : Fin (10 : ℕ)) || v (3 : Fin (10 : ℕ)) && v (4 : Fin (10 : ℕ)) || v (4 : Fin (10 : ℕ)) && v (0 : Fin (10 : ℕ)) || v (0 : Fin (10 : ℕ)) && v (5 : Fin (10 : ℕ)) || v (1 : Fin (10 : ℕ)) && v (6 : Fin (10 : ℕ)) || v (2 : Fin (10 : ℕ)) && v (7 : Fin (10 : ℕ)) || v (3 : Fin (10 : ℕ)) && v (8 : Fin (10 : ℕ)) || v (4 : Fin (10 : ℕ)) && v (9 : Fin (10 : ℕ)) || v (5 : Fin (10 : ℕ)) && v (7 : Fin (10 : ℕ)) || v (7 : Fin (10 : ℕ)) && v (9 : Fin (10 : ℕ)) || v (9 : Fin (10 : ℕ)) && v (6 : Fin (10 : ℕ)) || v (6 : Fin (10 : ℕ)) && v (8 : Fin (10 : ℕ)) || v (8 : Fin (10 : ℕ)) && v (5 : Fin (10 : ℕ))) x := by
    decide +kernel
  have someEdge : G.edgeFinset.Nonempty := by rw [edges]; exact ⟨s(0,1),by decide +kernel⟩
  have graphEval : circuitFun 10 C=graphFun G ∅ :=
    funext fun x=>(computes x).trans (explicit x).symm
  obtain ⟨A,least,top,small⟩ := normalize 10 G C someEdge model graphEval
  classical
  let M : Finset (Sym2 (Fin 10)) := G.edgeFinset.filter fun e=>¬(∃ (u v : Fin 10) (j p q : ℕ), e=s(u,v) ∧ andOn A j p q ∧ orp A 10 u.val p ∧ orp A 10 v.val q ∧ orp A 10 (10+j) A.output)
  have missed : ∀ e : Sym2 (Fin 10), e∈M ↔ e∈G.edgeFinset ∧ ¬(∃ (u v : Fin 10) (j p q : ℕ), e=s(u,v) ∧ andOn A j p q ∧ orp A 10 u.val p ∧ orp A 10 v.val q ∧ orp A 10 (10+j) A.output) := by
    intro e
    exact Finset.mem_filter
  let I : Finset (Fin A.size) := Finset.univ.filter fun j=>
    (A.gates.get j).op=.and ∧ ¬orp A 10 (10+j.val) A.output
  have internal : ∀ j : Fin A.size, j∈I ↔ (A.gates.get j).op=.and ∧ ¬orp A 10 (10+j.val) A.output := by
    intro j
    exact ⟨fun h=>(Finset.mem_filter.mp h).2, fun h=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  by_cases few : M.card≤3 ∨ I.card≤1
  · exact smallProjection G A M I edges least top (small.trans budget) missed internal few
  · have beyond : 4≤M.card := by omega
    have two : 2≤I.card := by omega
    exact largeProjection G A M I edges least top (small.trans budget) missed internal beyond two
