import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- First minimize nested AND pairs, then minimize the number of AND gates with no owned edge.
theorem PEqualNP.Outside.R_meta_1772_1
    (leastAO : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.edgeFinset.Nonempty →
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ IsAO2 n C ∧ circuitFun n C = graphFun G ∅)
    (lift : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C → ¬ TopForm G C →
      ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
        D.size ≤ C.size ∧ andPairs n D < andPairs n C)
    (witness : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → TopForm G C →
      ∀ j < C.size, (gateAt C j).op = .and → (∀ u v, G.Adj u v → ¬ Owns n C j u v) →
        ∃ (i : ℕ) (u v : Fin n), G.Adj u v ∧ InCone n C i j ∧ Owns n C i u v ∧ ¬ BelowF G C i ∧
          gateVal n C j (pairInput u v) = true ∧
          circuitFun n (eraseGate n C j (n + C.size)) (pairInput u v) = false)
    (exchange : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      let hasEdge := fun (C : Circuit) j => ∃ u v, G.Adj u v ∧ Owns n C j u v
      let bad := fun (C : Circuit) => {j : ℕ | j < C.size ∧ (gateAt C j).op = .and ∧ ¬ hasEdge C j}.ncard
      ∀ C : Circuit, IsMinimalMonoCircuit n C → IsAO2 n C → circuitFun n C = graphFun G ∅ → TopForm G C →
      ∀ j < C.size, (gateAt C j).op = .and → ¬ hasEdge C j →
      (∀ k < j, (gateAt C k).op = .and → hasEdge C k) →
      ∀ (i : ℕ) (u v : Fin n), G.Adj u v → InCone n C i j → Owns n C i u v → ¬ BelowF G C i →
      gateVal n C j (pairInput u v) = true →
      circuitFun n (eraseGate n C j (n + C.size)) (pairInput u v) = false →
      ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
        (andPairs n D < andPairs n C ∨ andPairs n D = andPairs n C ∧ bad D < bad C)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 := by
  intro n G decG tri four
  classical
  by_cases ne : ∃ u v, G.Adj u v
  · have hn : G.edgeFinset.Nonempty := by
      obtain ⟨u, v, huv⟩ := ne
      exact ⟨s(u, v), by simpa using huv⟩
    obtain ⟨A, ma, aa, fa⟩ := leastAO n G hn
    let hasEdge (C : Circuit) (j : ℕ) := ∃ u v, G.Adj u v ∧ Owns n C j u v
    let badSet (C : Circuit) : Set ℕ := {j | j < C.size ∧ (gateAt C j).op = .and ∧ ¬ hasEdge C j}
    let bad (C : Circuit) := (badSet C).ncard
    let admissible (C : Circuit) := IsAO2 n C ∧ circuitFun n C = graphFun G ∅ ∧ C.size ≤ A.size
    have haveFirst : ∃ q : ℕ, ∃ C : Circuit, admissible C ∧ andPairs n C = q :=
      ⟨_, A, ⟨aa, fa, le_rfl⟩, rfl⟩
    let q := Nat.find haveFirst
    have haveSecond : ∃ r : ℕ, ∃ C : Circuit, admissible C ∧ andPairs n C = q ∧ bad C = r := by
      obtain ⟨C, ac, qc⟩ := Nat.find_spec haveFirst
      exact ⟨_, C, ac, qc, rfl⟩
    obtain ⟨C, ac, qc, rc⟩ := Nat.find_spec haveSecond
    obtain ⟨ao, f, sz⟩ := ac
    have mono (D : Circuit) (hd : IsAO2 n D) : Monotone2 D := by
      intro g hg
      exact ⟨by simpa using hd.1 g hg, (hd.2.2 g hg).le⟩
    have minC : IsMinimalMonoCircuit n C :=
      ⟨mono C ao, fun D md fd => sz.trans (ma.2 D md (fd.trans (f.trans fa.symm)))⟩
    have leastC : IsLeastAO G C :=
      ⟨ao, f, fun D ad fd => minC.2 D (mono D ad) (fd.trans f.symm)⟩
    have rank (D : Circuit) (ad : admissible D) :
        ¬ (andPairs n D < andPairs n C ∨ andPairs n D = andPairs n C ∧ bad D < bad C) := by
      rintro (hp | ⟨hp, hb⟩)
      · have hl := Nat.find_min' haveFirst ⟨D, ad, rfl⟩
        exact (not_lt_of_ge (qc.trans_le hl)) hp
      · have hl := Nat.find_min' haveSecond ⟨D, ad, hp.trans qc, rfl⟩
        exact (not_lt_of_ge (rc.trans_le hl)) hb
    have top : TopForm G C := by
      by_contra h
      obtain ⟨D, aoD, fD, szD, hp⟩ := lift n G C hn leastC h
      exact rank D ⟨aoD, fD, szD.trans sz⟩ (Or.inl hp)
    refine ⟨C, minC, f, fun j hj hjAnd => ?_⟩
    change hasEdge C j
    by_contra missing
    have existsBad : ∃ k, k ∈ badSet C := ⟨j, hj, hjAnd, missing⟩
    let k := Nat.find existsBad
    have hk : k ∈ badSet C := Nat.find_spec existsBad
    obtain ⟨hkLt, hkAnd, hkBad⟩ := hk
    have before (l : ℕ) (hl : l < k) (hlAnd : (gateAt C l).op = .and) : hasEdge C l := by
      by_contra hlBad
      have hlMem : l ∈ badSet C := ⟨hl.trans hkLt, hlAnd, hlBad⟩
      exact (not_le_of_gt hl) (Nat.find_min' existsBad hlMem)
    obtain ⟨i, u, v, adj, cone, owner, dirty, vtrue, lost⟩ :=
      witness n G C minC f top k hkLt hkAnd (fun u v adj own => hkBad ⟨u, v, adj, own⟩)
    obtain ⟨D, aoD, fD, szD, better⟩ :=
      exchange n G tri four C minC ao f top k hkLt hkAnd hkBad before i u v adj cone owner dirty vtrue lost
    exact rank D ⟨aoD, fD, szD.trans sz⟩ better
  · have empty : ∀ u v, ¬ G.Adj u v := fun u v h => ne ⟨u, v, h⟩
    refine ⟨⟨[], n⟩, ⟨?_, fun _ _ _ => Nat.zero_le _⟩, ?_, ?_⟩
    · intro g hg
      exact (List.not_mem_nil hg).elim
    · funext x
      change (List.ofFn x).getD n false =
        (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
          decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true))
      simp [empty, List.getD_eq_getElem?_getD]
    · intro j hj
      simp at hj
