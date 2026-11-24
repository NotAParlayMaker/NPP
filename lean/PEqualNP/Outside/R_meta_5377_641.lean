import Mathlib
import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

-- Separate actual singleton ownership from the disjoint two-support rectangle obstruction.
-- Compress the five-cycle profile to five cyclic indices in the two exchange children.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_5377_641
  (decomp : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (k : ℕ),
    have E : Fin n → Fin n → Prop := fun p q => G.Adj p q ∧ Owns n C k p q
    Monotone2 C → (∃ u v, E u v) →
    (∀ c : Fin n, ∃ u v, E u v ∧ u ≠ c ∧ v ≠ c) →
    (∃ u : Fin n, Owns n C k u u) ∨
      (∀ u : Fin n, ¬Owns n C k u u) ∧
      ∃ A B : Finset (Fin n), Disjoint A B ∧ A.Nontrivial ∧ B.Nontrivial ∧
        (∀ p q, E p q → (p ∈ A ∧ q ∈ B) ∨ (q ∈ A ∧ p ∈ B)) ∧
        ∀ p ∈ A, ∀ q ∈ B, gateVal n C k (pairInput p q) = true)
  (singleton : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → TopForm.NoFourCycle G →
    have E : Circuit → ℕ → Fin n → Fin n → Prop := fun D j u v => G.Adj u v ∧ Owns n D j u v
    have Q : Circuit → Prop := fun D => IsMinimalMonoCircuit n D ∧ circuitFun n D = NestedCover.graphFun G ∅ ∧ ∀ j,
      (∀ p q, ¬ E D j p q) ∨
      (∃ p q, E D j p q ∧ ∀ u v, E D j u v → u=p ∨ v=p ∨ u=q ∨ v=q) ∨
      ∃ t : Fin 5 → Fin n, (∀ i, E D j (t i) (t (i+1))) ∧
        (∀ u v, E D j u v → u ∈ Set.range t) ∧ gateVal n D j (pairInput (t 0) (t 0)) = true
    have S : Circuit → ℕ → Prop := fun D k => ∀ i < k, (∀ u v, ¬ E D i u v) ∨ ∃ r, ∀ u v, E D i u v → u=r ∨ v=r
    ∀ C k, Q C → k < C.size → S C k → (∃ u : Fin n, Owns n C k u u) → ∃ D, Q D ∧ S D (k+1))
  (rectangle : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a) → TopForm.NoFourCycle G →
    have E : Circuit → ℕ → Fin n → Fin n → Prop := fun D j u v => G.Adj u v ∧ Owns n D j u v
    have Q : Circuit → Prop := fun D => IsMinimalMonoCircuit n D ∧ circuitFun n D = NestedCover.graphFun G ∅ ∧ ∀ j,
      (∀ p q, ¬ E D j p q) ∨
      (∃ p q, E D j p q ∧ ∀ u v, E D j u v → u=p ∨ v=p ∨ u=q ∨ v=q) ∨
      ∃ t : Fin 5 → Fin n, (∀ i, E D j (t i) (t (i+1))) ∧
        (∀ u v, E D j u v → u ∈ Set.range t) ∧ gateVal n D j (pairInput (t 0) (t 0)) = true
    have S : Circuit → ℕ → Prop := fun D k => ∀ i < k, (∀ u v, ¬ E D i u v) ∨ ∃ r, ∀ u v, E D i u v → u=r ∨ v=r
    ∀ C k, Q C → k < C.size → S C k → ((∀ u : Fin n, ¬Owns n C k u u) ∧ ∃ A B : Finset (Fin n), Disjoint A B ∧ A.Nontrivial ∧ B.Nontrivial ∧
      (∀ u v, E C k u v → (u∈A ∧ v∈B) ∨ (v∈A ∧ u∈B)) ∧
      ∀ u∈A, ∀ v∈B, gateVal n C k (pairInput u v) = true) → ∃ D, Q D ∧ S D (k+1)) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin x1 → Fin x1 → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 x9 : Fin x1) => x2.Adj x8 x9 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x8 x9;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 ∧ PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ (x8 : ℕ), (∀ (x9 x10 : Fin x1), ¬x6 x7 x8 x9 x10) ∨ (∃ (x9 : Fin x1) (x10 : Fin x1), x6 x7 x8 x9 x10 ∧ ∀ (x11 x12 : Fin x1), x6 x7 x8 x11 x12 → x11 = x9 ∨ x12 = x9 ∨ x11 = x10 ∨ x12 = x10) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1), x6 x7 x8 x9 x10 ∧ x6 x7 x8 x10 x11 ∧ x6 x7 x8 x11 x12 ∧ x6 x7 x8 x12 x13 ∧ x6 x7 x8 x13 x9 ∧ (∀ (x14 x15 : Fin x1), x6 x7 x8 x14 x15 → x14 = x9 ∨ x14 = x10 ∨ x14 = x11 ∨ x14 = x12 ∨ x14 = x13) ∧ PEqualNP.EdgeOwnership.gateVal x1 x7 x8 (PEqualNP.EdgeOwnership.pairInput x9 x9) = Bool.true;       have x8 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) => ∀ x10 < x9, (∀ (x12 x13 : Fin x1), ¬x6 x8 x10 x12 x13) ∨ ∃ (x12 : Fin x1), ∀ (x13 x14 : Fin x1), x6 x8 x10 x13 x14 → x13 = x12 ∨ x14 = x12;       ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ), x7 x9 → x10 < x9.size → x8 x9 x10 → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), x7 x14 ∧ x8 x14 (x10 + (1 : ℕ)) := by
  intro n G inst tri h4 E Q S C k hQ hk hS
  classical
  let P : Circuit → Prop := fun D => IsMinimalMonoCircuit n D ∧ circuitFun n D = NestedCover.graphFun G ∅ ∧ ∀ j,
      (∀ p q, ¬ E D j p q) ∨
      (∃ p q, E D j p q ∧ ∀ u v, E D j u v → u=p ∨ v=p ∨ u=q ∨ v=q) ∨
      ∃ t : Fin 5 → Fin n, (∀ i, E D j (t i) (t (i+1))) ∧
        (∀ u v, E D j u v → u ∈ Set.range t) ∧ gateVal n D j (pairInput (t 0) (t 0)) = true
  have profile (D : Circuit) : Q D ↔ P D := by
    constructor
    · intro h
      refine ⟨h.1,h.2.1,?_⟩
      intro j
      rcases h.2.2 j with h0|hh|hc
      · exact Or.inl h0
      · exact Or.inr (Or.inl hh)
      · right; right
        obtain ⟨a,b,c,d,e,hab,hbc,hcd,hde,hea,hcover,hs⟩ := hc
        let t : Fin 5 → Fin n := ![a,b,c,d,e]
        refine ⟨t,?_,?_,hs⟩
        · intro i
          fin_cases i
          · exact hab
          · exact hbc
          · exact hcd
          · exact hde
          · exact hea
        · intro u v huv
          rcases hcover u v huv with h|h|h|h|h
          · exact ⟨0,h.symm⟩
          · exact ⟨1,h.symm⟩
          · exact ⟨2,h.symm⟩
          · exact ⟨3,h.symm⟩
          · exact ⟨4,h.symm⟩
    · intro h
      refine ⟨h.1,h.2.1,?_⟩
      intro j
      rcases h.2.2 j with h0|hh|hc
      · exact Or.inl h0
      · exact Or.inr (Or.inl hh)
      · right; right
        obtain ⟨t,hedges,hcover,hs⟩ := hc
        refine ⟨t 0,t 1,t 2,t 3,t 4,hedges 0,hedges 1,hedges 2,hedges 3,hedges 4,?_,hs⟩
        intro u v huv
        obtain ⟨i,hi⟩ := hcover u v huv
        fin_cases i
        · exact Or.inl hi.symm
        · exact Or.inr (Or.inl hi.symm)
        · exact Or.inr (Or.inr (Or.inl hi.symm))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hi.symm)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr hi.symm)))
  by_cases good : (∀ p q, ¬ E C k p q) ∨ ∃ r, ∀ u v, E C k u v → u=r ∨ v=r
  · refine ⟨C,hQ,?_⟩
    intro j hj
    by_cases hj' : j < k
    · exact hS j hj'
    · have eq : j=k := by omega
      subst j
      exact good
  have someEdge : ∃ p q, E C k p q := by
    by_contra! noEdge
    exact good (Or.inl noEdge)
  have nonstar : ∀ r, ∃ u v, E C k u v ∧ u ≠ r ∧ v ≠ r := by
    intro r
    by_contra no
    apply good
    right
    refine ⟨r,?_⟩
    intro u v he
    by_contra! hn
    exact no ⟨u,v,he,hn.1,hn.2⟩
  rcases decomp n G C k hQ.1.1 someEdge nonstar with hsingle|hrect
  · obtain ⟨D,hD,hS'⟩ := singleton n G tri h4 C k ((profile C).mp hQ) hk hS hsingle
    exact ⟨D,(profile D).mpr hD,hS'⟩
  · obtain ⟨D,hD,hS'⟩ := rectangle n G tri h4 C k ((profile C).mp hQ) hk hS hrect
    exact ⟨D,(profile D).mpr hD,hS'⟩
