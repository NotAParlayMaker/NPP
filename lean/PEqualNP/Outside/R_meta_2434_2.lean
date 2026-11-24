import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2434_2
    (h1 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C → j < C.size →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧ D.size < C.size ∧
        (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D x ≤ PEqualNP.MetaComplexity.circuitFun n C x) ∧
        (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D x =
          PEqualNP.MetaComplexity.circuitFun n
            ⟨PEqualNP.NotPremium.replaceByConst C.gates j Bool.false, C.output⟩ x))
    (h2 : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.Nonempty →
      (∀ v : Fin n, G.degree v = (0 : ℕ) ∨ (3 : ℕ) ≤ G.degree v) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → (5 : ℕ) ≤ w.length) →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = Bool.true →
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = Bool.true) →
        (∀ C' : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.Monotone2 C' →
          (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C' x = Bool.true →
            PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = Bool.true) →
          C'.size < C.size →
          ({e ∈ G.edgeFinset | (PEqualNP.MetaComplexity.circuitFun n C' fun v => Decidable.decide (v ∈ e)) = Bool.true}).card <
          ({e ∈ G.edgeFinset | (PEqualNP.MetaComplexity.circuitFun n C fun v => Decidable.decide (v ∈ e)) = Bool.true}).card) →
        (∃ j < C.size,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∃ u v : Fin n, ¬G.Adj u v ∧
            PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = Bool.true) →
        ∃ j < C.size,
          ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
            ∃ u v : Fin n, ¬G.Adj u v ∧
              PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = Bool.true) ∧
          ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
            PEqualNP.MetaComplexity.Monotone2 D ∧
            (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D x = Bool.true →
              PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = Bool.true) ∧
            D.size < C.size ∧
            {e ∈ G.edgeFinset | (PEqualNP.MetaComplexity.circuitFun n D fun v => Decidable.decide (v ∈ e)) = Bool.true} =
              {e ∈ G.edgeFinset | (PEqualNP.MetaComplexity.circuitFun n ⟨PEqualNP.NotPremium.replaceByConst C.gates j Bool.false, C.output⟩ fun v => Decidable.decide (v ∈ e)) = Bool.true} ∧
            ({e ∈ G.edgeFinset | (PEqualNP.MetaComplexity.circuitFun n C fun v => Decidable.decide (v ∈ e)) = Bool.true}).card ≤
              ({e ∈ G.edgeFinset | (PEqualNP.MetaComplexity.circuitFun n D fun v => Decidable.decide (v ∈ e)) = Bool.true}).card + k * (C.size - D.size)) :
    ∃ (x1 : ℕ),   ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],     (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) →       (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →         have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x8 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x7 x8 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅ x8 = Bool.true;         have x8 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Sym2 (Fin x2)) := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => {x9 ∈ x3.edgeFinset | (PEqualNP.MetaComplexity.circuitFun x2 x8 fun (x10 : Fin x2) => Decidable.decide (x10 ∈ x9)) = Bool.true};         have x9 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x11 : Fin x2) (x12 : Fin x2), ¬x3.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.gateVal x2 x9 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true;         ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 → x7 x10 → (∀ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 → x7 x13 → x13.size < x10.size → (x8 x13).card < (x8 x10).card) → (∃ (x14 : ℕ), x9 x10 x14) → ∃ (x15 : ℕ), x9 x10 x15 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x16 ∧ x7 x16 ∧ x16.size < x10.size ∧ x8 x16 = x8 { gates := PEqualNP.NotPremium.replaceByConst x10.gates x15 Bool.false, output := x10.output : PEqualNP.CircuitLowerBounds.Circuit } ∧ (x8 x10).card ≤ (x8 x16).card + x1 * (x10.size - x16.size) := by
  obtain ⟨k, hk⟩ := h2
  refine ⟨k, ?_⟩
  intro x2 x3 x4 hdeg hcyc
  dsimp only
  intro x10 hmono hsafe hrec hbad
  obtain ⟨x14, hx14⟩ := hbad
  have hx14_lt : x14 < x10.size := by
    by_contra hge
    have hge' : x10.gates.length ≤ x14 := Nat.le_of_not_lt hge
    have hop : PEqualNP.MetaComplexity.NestedCover.gateAt x10 x14 = ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none hge']
    have hand := hx14.1
    rw [hop] at hand
    cases hand
  by_cases hne : x3.edgeFinset.Nonempty
  · obtain ⟨x15, _, hx15bad, x16, h16m, h16s, h16sz, h16eq, h16card⟩ :=
      hk x2 x3 hne hdeg hcyc x10 hmono hsafe hrec ⟨x14, hx14_lt, hx14⟩
    exact ⟨x15, hx15bad, x16, h16m, h16s, h16sz, h16eq, h16card⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    obtain ⟨D, hDm, hDsz, hDle, hDeq⟩ := h1 x2 x10 x14 hmono hx14_lt
    refine ⟨x14, hx14, D, hDm, ?_, hDsz, ?_, ?_⟩
    · intro x hx
      apply hsafe x
      have hle := hDle x
      rw [hx] at hle
      exact Bool.eq_true_of_true_le hle
    · apply Finset.filter_congr
      intro e _
      rw [hDeq]
    · have h0 : ({x9 ∈ x3.edgeFinset | (PEqualNP.MetaComplexity.circuitFun x2 x10 fun x10_1 => Decidable.decide (x10_1 ∈ x9)) = Bool.true} : Finset (Sym2 (Fin x2))).card = 0 := by
        simp [hne]
      omega
