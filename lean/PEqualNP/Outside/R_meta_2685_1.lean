import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2685_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C' ∧
        PEqualNP.TopForm.TopForm G C' ∧
        C'.size ≤ C.size ∧
        (PEqualNP.TopForm.junk G C' = ∅ →
          ∃ K : Finset (Fin n), G.IsVertexCover (K : Set (Fin n)) ∧
            G.edgeFinset.card + K.card ≤ C'.size + 1))
    (h2 : ∀ (Np Nl : ℕ) (G : SimpleGraph (Fin (Np + Nl))) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ),
      (∀ u v : Fin (Np + Nl), G.Adj u v → (u.val < Np ∧ Np ≤ v.val) ∨ (v.val < Np ∧ Np ≤ u.val)) →
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      PEqualNP.TopForm.junk G C = {g} →
      ∃ K : Finset (Fin (Np + Nl)), G.IsVertexCover (K : Set (Fin (Np + Nl))) ∧
        G.edgeFinset.card + K.card ≤ C.size + 1)
    (h3 : ∀ (Np Nl : ℕ) (G : SimpleGraph (Fin (Np + Nl))) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ u v : Fin (Np + Nl), G.Adj u v → (u.val < Np ∧ Np ≤ v.val) ∨ (v.val < Np ∧ Np ≤ u.val)) →
      PEqualNP.TopForm.NoFourCycle G →
      G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      2 ≤ (PEqualNP.TopForm.junk G C).card →
      ∃ K : Finset (Fin (Np + Nl)), G.IsVertexCover (K : Set (Fin (Np + Nl))) ∧
        G.edgeFinset.card + K.card ≤ C.size + 1)
    (h4 : ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
      (Kp : Finset (Fin Np)) (Kl : Finset (Fin Nl)),
      (∃ p : Fin Np, ∃ l : Fin Nl, I p l) →
      (∀ p : Fin Np, ∀ l : Fin Nl, I p l → p ∈ Kp ∨ l ∈ Kl) →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ),
        PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧
        (∀ y : Fin (Np + Nl) → Bool,
          PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y =
            decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧
              y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧
        D.size + 1 ≤ Fintype.card {e : Fin Np × Fin Nl // I e.1 e.2} +
          Kp.card + Kl.card ∧
        (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧
        (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧
        ∀ i < D.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧
            ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  intro Np Nl I _ C hNo4I hAO2C hFunC
  by_cases hEx : ∃ p : Fin Np, ∃ l : Fin Nl, I p l
  · let G : SimpleGraph (Fin (Np + Nl)) :=
      { Adj := fun u v =>
          (∃ (p : Fin Np) (l : Fin Nl), I p l ∧ u = Fin.castAdd Nl p ∧ v = Fin.natAdd Np l) ∨
          (∃ (p : Fin Np) (l : Fin Nl), I p l ∧ v = Fin.castAdd Nl p ∧ u = Fin.natAdd Np l)
        symm := ⟨fun _ _ h => h.symm⟩
        loopless := ⟨by
          rintro u (⟨p, l, _, hu1, hu2⟩ | ⟨p, l, _, hu1, hu2⟩)
          · have hlt : u.val < Np := by rw [hu1]; exact p.isLt
            have hge : Np ≤ u.val := by rw [hu2]; simp
            omega
          · have hlt : u.val < Np := by rw [hu1]; exact p.isLt
            have hge : Np ≤ u.val := by rw [hu2]; simp
            omega⟩ }
    let instG : DecidableRel G.Adj := fun u v =>
      inferInstanceAs (Decidable (
        (∃ (p : Fin Np) (l : Fin Nl), I p l ∧ u = Fin.castAdd Nl p ∧ v = Fin.natAdd Np l) ∨
        (∃ (p : Fin Np) (l : Fin Nl), I p l ∧ v = Fin.castAdd Nl p ∧ u = Fin.natAdd Np l)))
    haveI : DecidableRel G.Adj := instG
    have hBip : ∀ u v : Fin (Np + Nl), G.Adj u v →
        (u.val < Np ∧ Np ≤ v.val) ∨ (v.val < Np ∧ Np ≤ u.val) := by
      rintro u v (⟨p, l, _, rfl, rfl⟩ | ⟨p, l, _, rfl, rfl⟩)
      · exact Or.inl ⟨p.isLt, by simp⟩
      · exact Or.inr ⟨p.isLt, by simp⟩
    have hGne : G.edgeFinset.Nonempty := by
      obtain ⟨p0, l0, h0⟩ := hEx
      refine ⟨s(Fin.castAdd Nl p0, Fin.natAdd Np l0), ?_⟩
      rw [SimpleGraph.mem_edgeFinset]
      exact Or.inl ⟨p0, l0, h0, rfl, rfl⟩
    have hNo4G : PEqualNP.TopForm.NoFourCycle G := by
      intro a b hab
      rw [Finset.card_le_one]
      intro w1 hw1 w2 hw2
      rw [Finset.mem_filter] at hw1 hw2
      by_contra hw12
      rcases hw1.2.1 with ⟨p1, l1, hp1l1, rfl, rfl⟩ | ⟨p1, l1, hp1l1, rfl, rfl⟩
      · rcases hw1.2.2 with ⟨p2, l1', hp2l1, rfl, heq1⟩ | ⟨p2, l1', _, heq1, _⟩
        · have hl1 : l1' = l1 := Fin.ext (by have := congrArg Fin.val heq1; simp at this; omega)
          rw [hl1] at hp2l1
          have hp12 : p1 ≠ p2 := fun h => hab (h ▸ rfl)
          rcases hw2.2.1 with ⟨p1', l2, hp1l2, heq2, rfl⟩ | ⟨_, _, _, _, heq2⟩
          · have hp1' : p1' = p1 := Fin.ext (by have := congrArg Fin.val heq2; simp at this; omega)
            rw [hp1'] at hp1l2
            have hl12 : l1 ≠ l2 := fun h => hw12 (h ▸ rfl)
            rcases hw2.2.2 with ⟨p2', l2', hp2l2, heq3, heq4⟩ | ⟨_, _, _, heq3, _⟩
            · have hp2' : p2' = p2 := Fin.ext (by have := congrArg Fin.val heq3; simp at this; omega)
              have hl2' : l2' = l2 := Fin.ext (by have := congrArg Fin.val heq4; simp at this; omega)
              rw [hp2', hl2'] at hp2l2
              exact hNo4I p1 p2 l1 l2 hp12 hl12 ⟨hp1l1, hp1l2, hp2l1, hp2l2⟩
            · have := congrArg Fin.val heq3; simp at this; omega
          · have := congrArg Fin.val heq2; simp at this; omega
        · have := congrArg Fin.val heq1; simp at this; omega
      · rcases hw1.2.2 with ⟨_, _, _, _, heq1⟩ | ⟨p1', l2, hp1l2, heq1, rfl⟩
        · have := congrArg Fin.val heq1; simp at this; omega
        · have hp1' : p1' = p1 := Fin.ext (by have := congrArg Fin.val heq1; simp at this; omega)
          rw [hp1'] at hp1l2
          have hl12 : l1 ≠ l2 := fun h => hab (h ▸ rfl)
          rcases hw2.2.1 with ⟨_, _, _, heq2, _⟩ | ⟨p2, l1', hp2l1, rfl, heq2⟩
          · have := congrArg Fin.val heq2; simp at this; omega
          · have hl1' : l1' = l1 := Fin.ext (by have := congrArg Fin.val heq2; simp at this; omega)
            rw [hl1'] at hp2l1
            have hp12 : p1 ≠ p2 := fun h => hw12 (h ▸ rfl)
            rcases hw2.2.2 with ⟨_, _, _, _, heq3⟩ | ⟨p2', l2', hp2l2, heq3, heq4⟩
            · have := congrArg Fin.val heq3; simp at this; omega
            · have hp2' : p2' = p2 := Fin.ext (by have := congrArg Fin.val heq3; simp at this; omega)
              have hl2' : l2' = l2 := Fin.ext (by have := congrArg Fin.val heq4; simp at this; omega)
              rw [hp2', hl2'] at hp2l2
              exact hNo4I p1 p2 l1 l2 hp12 hl12 ⟨hp1l1, hp1l2, hp2l1, hp2l2⟩
    have hFunCG : PEqualNP.MetaComplexity.circuitFun (Np + Nl) C =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
      funext z
      rw [hFunC z]
      unfold PEqualNP.MetaComplexity.NestedCover.graphFun
      have hemp : decide (∃ a ∈ (∅ : Finset (Fin (Np + Nl))), z a = true) = false := by simp
      rw [hemp, Bool.false_or]
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨p, l, hpl, hp, hl⟩
        exact ⟨Fin.castAdd Nl p, Fin.natAdd Np l, Or.inl ⟨p, l, hpl, rfl, rfl⟩, hp, hl⟩
      · rintro ⟨u, v, (⟨p, l, hpl, rfl, rfl⟩ | ⟨p, l, hpl, rfl, rfl⟩), hu, hv⟩
        · exact ⟨p, l, hpl, hu, hv⟩
        · exact ⟨p, l, hpl, hv, hu⟩
    obtain ⟨C', hLeast, hTF, hSize', hZero⟩ := h1 (Np + Nl) G C hNo4G hGne hAO2C hFunCG
    have hCoverEx : ∃ K : Finset (Fin (Np + Nl)), G.IsVertexCover (K : Set (Fin (Np + Nl))) ∧
        G.edgeFinset.card + K.card ≤ C'.size + 1 := by
      by_cases hj0 : (PEqualNP.TopForm.junk G C').card = 0
      · exact hZero (Finset.card_eq_zero.mp hj0)
      · by_cases hj1 : (PEqualNP.TopForm.junk G C').card = 1
        · obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hj1
          exact h2 Np Nl G C' g hBip hNo4G hGne hLeast hTF hg
        · exact h3 Np Nl G C' hBip hNo4G hGne hLeast hTF (by omega)
    obtain ⟨K, hCovK, hBoundK⟩ := hCoverEx
    let Kp : Finset (Fin Np) := Finset.univ.filter (fun p => Fin.castAdd Nl p ∈ K)
    let Kl : Finset (Fin Nl) := Finset.univ.filter (fun l => Fin.natAdd Np l ∈ K)
    have hCovI : ∀ p : Fin Np, ∀ l : Fin Nl, I p l → p ∈ Kp ∨ l ∈ Kl := by
      intro p l hpl
      have hadj : G.Adj (Fin.castAdd Nl p) (Fin.natAdd Np l) := Or.inl ⟨p, l, hpl, rfl, rfl⟩
      rcases hCovK hadj with hp | hl
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩)
    have hCardK : Kp.card + Kl.card ≤ K.card := by
      have hinjP : Function.Injective (Fin.castAdd Nl : Fin Np → Fin (Np + Nl)) :=
        fun a b h => Fin.ext (by have := congrArg Fin.val h; simpa using this)
      have hinjL : Function.Injective (Fin.natAdd Np : Fin Nl → Fin (Np + Nl)) :=
        fun a b h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
      have hdisj : Disjoint (Kp.image (Fin.castAdd Nl)) (Kl.image (Fin.natAdd Np)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [Finset.mem_image] at hx1 hx2
        obtain ⟨p, _, rfl⟩ := hx1
        obtain ⟨l, _, heq⟩ := hx2
        have := congrArg Fin.val heq
        simp at this
        omega
      have hsub : Kp.image (Fin.castAdd Nl) ∪ Kl.image (Fin.natAdd Np) ⊆ K := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx1 | hx2
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx1
          exact (Finset.mem_filter.mp hp).2
        · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hx2
          exact (Finset.mem_filter.mp hl).2
      calc Kp.card + Kl.card
          = (Kp.image (Fin.castAdd Nl)).card + (Kl.image (Fin.natAdd Np)).card := by
            rw [Finset.card_image_of_injective _ hinjP, Finset.card_image_of_injective _ hinjL]
        _ = (Kp.image (Fin.castAdd Nl) ∪ Kl.image (Fin.natAdd Np)).card :=
            (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ K.card := Finset.card_le_card hsub
    have hCardE : Fintype.card {e : Fin Np × Fin Nl // I e.1 e.2} ≤
        G.edgeFinset.card := by
      rw [Fintype.card_subtype]
      refine Finset.card_le_card_of_injOn
        (fun e : Fin Np × Fin Nl => s(Fin.castAdd Nl e.1, Fin.natAdd Np e.2)) ?_ ?_
      · intro e he
        rw [Finset.mem_coe, Finset.mem_filter] at he
        rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset]
        exact Or.inl ⟨e.1, e.2, he.2, rfl, rfl⟩
      · intro e1 _ e2 _ heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨ha, hb⟩ | ⟨ha, _⟩
        · ext
          · have := congrArg Fin.val ha; simpa using this
          · have := congrArg Fin.val hb; simp at this; omega
        · exfalso
          have := congrArg Fin.val ha
          simp at this
          omega
    obtain ⟨D, P, L, hDAO, hDFun, hDSize, hDP, hDL, hDAnd⟩ := h4 Np Nl I Kp Kl hEx hCovI
    exact ⟨D, P, L, hDAO, hDFun, by omega, hDP, hDL, hDAnd⟩
  · refine ⟨⟨[], Np + Nl⟩, ∅, ∅, ?_, ?_, Nat.zero_le _, by simp, by simp, by simp⟩
    · exact And.intro (fun _ hg => False.elim (List.not_mem_nil hg))
        (And.intro (fun _ hj => absurd hj (Nat.not_lt_zero _))
          (fun _ hg => False.elim (List.not_mem_nil hg)))
    · intro y
      have hR : decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧
          y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true) = false := by
        rw [decide_eq_false_iff_not]
        rintro ⟨p, l, hpl, _, _⟩
        exact hEx ⟨p, l, hpl⟩
      rw [hR]
      show ((List.ofFn y).getD (Np + Nl) false) = false
      simp
