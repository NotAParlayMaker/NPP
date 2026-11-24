import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2976_1
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
        G.edgeFinset.card + K.card ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x10 ∧ x16 ∈ x11 := by
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
    let E : Finset (Fin Np × Fin Nl) := Finset.univ.filter (fun e => I e.1 e.2)
    have hCardE : E.card ≤ G.edgeFinset.card := by
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
    let stepW : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let wiresFrom : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool :=
      fun gs w => gs.foldl stepW w
    have wiresFrom_append : ∀ (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
      intro gs1 gs2 w; dsimp only [wiresFrom]; exact List.foldl_append
    have wiresFrom_prefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
      intro gs
      induction gs with
      | nil => intro w; exact ⟨[], by dsimp only [wiresFrom]; simp, rfl⟩
      | cons g gs ih =>
        intro w
        obtain ⟨t, ht, hl⟩ := ih (stepW w g)
        refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
        change wiresFrom gs (stepW w g) = _
        rw [ht]; dsimp only [stepW]; simp
    have length_wiresFrom : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        (wiresFrom gs w).length = w.length + gs.length := by
      intro gs w
      obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
      rw [ht]; simp [hl]
    have getD_wiresFrom : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
        i < w.length → (wiresFrom gs w).getD i false = w.getD i false := by
      intro gs w i h
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
      rw [ht, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    have getD_snoc : ∀ (u : List Bool) (b : Bool), (u ++ [b]).getD u.length false = b := by
      intro u b; simp [List.getD_eq_getElem?_getD]
    let AO2Seg : ℕ → List PEqualNP.CircuitLowerBounds.Gate → Prop :=
      fun m gs => ∀ j (hj : j < gs.length),
        ((gs[j]).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (gs[j]).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (gs[j]).inputs.length = 2 ∧ ∀ u ∈ (gs[j]).inputs, u < m + j
    have ao2Seg_append : ∀ {m : ℕ} {gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate},
        AO2Seg m gs1 → AO2Seg (m + gs1.length) gs2 → AO2Seg m (gs1 ++ gs2) := by
      intro m gs1 gs2 ha1 ha2 j hj
      rw [List.length_append] at hj
      by_cases hlt : j < gs1.length
      · simpa [List.getElem_append_left hlt] using ha1 j hlt
      · have hk : j - gs1.length < gs2.length := by omega
        have h := ha2 (j - gs1.length) hk
        have heq : m + gs1.length + (j - gs1.length) = m + j := by omega
        rw [heq] at h
        simpa [List.getElem_append_right (Nat.le_of_not_lt hlt)] using h
    let PureWire : ℕ → Bool → List PEqualNP.CircuitLowerBounds.Gate → Finset ℕ → Prop :=
      fun m sideL gs W => (∀ w ∈ W, w < m + gs.length) ∧
        ∀ w ∈ W, (if sideL then Np ≤ w ∧ w < Np + Nl else w < Np) ∨
          ∃ j, ∃ hj : j < gs.length, w = m + j ∧
            (gs[j]).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (gs[j]).inputs, u ∈ W
    have pureWire_append_left : ∀ {m : ℕ} {sideL : Bool}
        {gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate} {W : Finset ℕ},
        PureWire m sideL gs1 W → PureWire m sideL (gs1 ++ gs2) W := by
      intro m sideL gs1 gs2 W h
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · have := h.1 w hw; rw [List.length_append]; omega
      · rcases h.2 w hw with h0 | ⟨j, hj, rfl, hop, hin⟩
        · exact Or.inl h0
        · refine Or.inr ⟨j, by rw [List.length_append]; omega, rfl, ?_, ?_⟩
          · rw [List.getElem_append_left hj]; exact hop
          · rw [List.getElem_append_left hj]; exact hin
    have pureWire_append_right : ∀ {m : ℕ} {sideL : Bool}
        {gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate} {W : Finset ℕ},
        PureWire (m + gs1.length) sideL gs2 W → PureWire m sideL (gs1 ++ gs2) W := by
      intro m sideL gs1 gs2 W h
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · have := h.1 w hw; rw [List.length_append]; omega
      · rcases h.2 w hw with h0 | ⟨j, hj, rfl, hop, hin⟩
        · exact Or.inl h0
        · refine Or.inr ⟨gs1.length + j, by rw [List.length_append]; omega, by omega, ?_, ?_⟩
          · simpa [List.getElem_append_right (Nat.le_add_right _ _)] using hop
          · simpa [List.getElem_append_right (Nat.le_add_right _ _)] using hin
    have pureWire_union : ∀ {m : ℕ} {sideL : Bool}
        {gs : List PEqualNP.CircuitLowerBounds.Gate} {W1 W2 : Finset ℕ},
        PureWire m sideL gs W1 → PureWire m sideL gs W2 → PureWire m sideL gs (W1 ∪ W2) := by
      intro m sideL gs W1 W2 h1' h2'
      refine ⟨fun w hw => ?_, fun w hw => ?_⟩
      · rcases Finset.mem_union.mp hw with hw1 | hw2
        · exact h1'.1 w hw1
        · exact h2'.1 w hw2
      · rcases Finset.mem_union.mp hw with hw1 | hw2
        · rcases h1'.2 w hw1 with h0 | ⟨j, hj, rfl, hop, hin⟩
          · exact Or.inl h0
          · exact Or.inr ⟨j, hj, rfl, hop, fun u hu => Finset.mem_union_left _ (hin u hu)⟩
        · rcases h2'.2 w hw2 with h0 | ⟨j, hj, rfl, hop, hin⟩
          · exact Or.inl h0
          · exact Or.inr ⟨j, hj, rfl, hop, fun u hu => Finset.mem_union_right _ (hin u hu)⟩
    let AndPure : List PEqualNP.CircuitLowerBounds.Gate → Finset ℕ → Finset ℕ → Prop :=
      fun gs P L => ∀ j (hj : j < gs.length),
        (gs[j]).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ a b, (gs[j]).inputs = [a, b] ∧ a ∈ P ∧ b ∈ L
    have andPure_mono : ∀ {gs : List PEqualNP.CircuitLowerBounds.Gate} {P P' L L' : Finset ℕ},
        P ⊆ P' → L ⊆ L' → AndPure gs P L → AndPure gs P' L' := by
      intro gs P P' L L' hP hL h j hj hand
      obtain ⟨a, b, hin, ha, hb⟩ := h j hj hand
      exact ⟨a, b, hin, hP ha, hL hb⟩
    have andPure_append : ∀ {gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate} {P L : Finset ℕ},
        AndPure gs1 P L → AndPure gs2 P L → AndPure (gs1 ++ gs2) P L := by
      intro gs1 gs2 P L ha1 ha2 j hj hand
      rw [List.length_append] at hj
      by_cases hlt : j < gs1.length
      · rw [List.getElem_append_left hlt] at hand ⊢
        exact ha1 j hlt hand
      · have hk : j - gs1.length < gs2.length := by omega
        rw [List.getElem_append_right (Nat.le_of_not_lt hlt)] at hand ⊢
        exact ha2 (j - gs1.length) hk hand
    let BldPure : Bool → ((Fin (Np + Nl) → Bool) → Bool) → ℕ → Prop :=
      fun sideL F s => ∀ m, Np + Nl ≤ m →
        ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ) (W : Finset ℕ),
          AO2Seg m gs ∧
          (∀ j (hj : j < gs.length), (gs[j]).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          gs.length ≤ s ∧ out ∈ W ∧ PureWire m sideL gs W ∧
          ∀ v : List Bool, v.length = m →
            (wiresFrom gs v).getD out false = F (fun i => v.getD i false)
    have bldPure_mono : ∀ (sideL : Bool) (F : (Fin (Np + Nl) → Bool) → Bool) (s s' : ℕ),
        BldPure sideL F s → s ≤ s' → BldPure sideL F s' := by
      intro sideL F s s' h hs m hm
      obtain ⟨gs, out, W, hao, hor, hlen, hout, hpw, hev⟩ := h m hm
      exact ⟨gs, out, W, hao, hor, le_trans hlen hs, hout, hpw, hev⟩
    have bldPure_congr : ∀ (sideL : Bool) (F H : (Fin (Np + Nl) → Bool) → Bool) (s : ℕ),
        BldPure sideL F s → (∀ x, F x = H x) → BldPure sideL H s := by
      intro sideL F H s h he m hm
      obtain ⟨gs, out, W, hao, hor, hlen, hout, hpw, hev⟩ := h m hm
      exact ⟨gs, out, W, hao, hor, hlen, hout, hpw, fun v hv => by rw [hev v hv, he]⟩
    have bldPure_point : ∀ p : Fin Np,
        BldPure false (fun x => x (Fin.castAdd Nl p)) 0 := by
      intro p m hm
      refine ⟨[], p.val, {p.val}, fun j hj => by simp at hj, fun j hj => by simp at hj,
        le_rfl, Finset.mem_singleton_self _, ?_, ?_⟩
      · refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · rw [Finset.mem_singleton.mp hw]; simp; have := p.isLt; omega
        · rw [Finset.mem_singleton.mp hw]; exact Or.inl p.isLt
      · intro v _; dsimp only [wiresFrom]; simp
    have bldPure_line : ∀ l : Fin Nl,
        BldPure true (fun x => x (Fin.natAdd Np l)) 0 := by
      intro l m hm
      refine ⟨[], Np + l.val, {Np + l.val}, fun j hj => by simp at hj, fun j hj => by simp at hj,
        le_rfl, Finset.mem_singleton_self _, ?_, ?_⟩
      · refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · rw [Finset.mem_singleton.mp hw]; simp; have := l.isLt; omega
        · rw [Finset.mem_singleton.mp hw]; exact Or.inl ⟨by omega, by have := l.isLt; omega⟩
      · intro v _; dsimp only [wiresFrom]; simp
    have bldPure_or : ∀ (sideL : Bool) (F1 F2 : (Fin (Np + Nl) → Bool) → Bool) (s1 s2 : ℕ),
        BldPure sideL F1 s1 → BldPure sideL F2 s2 →
        BldPure sideL (fun x => F1 x || F2 x) (s1 + s2 + 1) := by
      intro sideL F1 F2 s1 s2 hb1 hb2 m hm
      obtain ⟨gs1, o1, W1, hao1, hor1, hlen1, ho1, hpw1, hev1⟩ := hb1 m hm
      obtain ⟨gs2, o2, W2, hao2, hor2, hlen2, ho2, hpw2, hev2⟩ := hb2 (m + gs1.length) (by omega)
      let out := m + gs1.length + gs2.length
      let g := PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [o1, o2]
      have ho1lt : o1 < m + gs1.length := hpw1.1 o1 ho1
      have ho2lt : o2 < m + gs1.length + gs2.length := hpw2.1 o2 ho2
      have hao12 : AO2Seg m (gs1 ++ gs2) := ao2Seg_append hao1 hao2
      have haoG : AO2Seg (m + (gs1 ++ gs2).length) [g] := by
        intro j hj
        have hj0 : j = 0 := by simp at hj; exact hj
        subst hj0
        refine ⟨Or.inr rfl, rfl, ?_⟩
        intro u hu
        dsimp only [g] at hu
        simp only [List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
        rw [List.length_append]
        rcases hu with rfl | rfl <;> omega
      have hpw12 : PureWire m sideL (gs1 ++ gs2) (W1 ∪ W2) :=
        pureWire_union (pureWire_append_left hpw1) (pureWire_append_right hpw2)
      refine ⟨(gs1 ++ gs2) ++ [g], out, insert out (W1 ∪ W2), ao2Seg_append hao12 haoG, ?_,
        by simp; omega, Finset.mem_insert_self _ _, ?_, ?_⟩
      · intro j hj
        have hj' := hj
        simp only [List.length_append, List.length_singleton] at hj'
        by_cases hlt12 : j < (gs1 ++ gs2).length
        · rw [List.getElem_append_left hlt12]
          by_cases hlt1 : j < gs1.length
          · rw [List.getElem_append_left hlt1]; exact hor1 j hlt1
          · rw [List.getElem_append_right (Nat.le_of_not_lt hlt1)]
            exact hor2 (j - gs1.length) (by rw [List.length_append] at hlt12; omega)
        · have hge12 : (gs1 ++ gs2).length ≤ j := Nat.le_of_not_lt hlt12
          have hjlast : j = (gs1 ++ gs2).length := by rw [List.length_append] at hge12 ⊢; omega
          subst hjlast
          dsimp only [g]; simp
      · refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · rcases Finset.mem_insert.mp hw with rfl | hw'
          · dsimp only [out]; simp; omega
          · have := hpw12.1 w hw'; simp [List.length_append] at this ⊢; omega
        · rcases Finset.mem_insert.mp hw with rfl | hw'
          · refine Or.inr ⟨(gs1 ++ gs2).length, by simp,
              by dsimp only [out]; simp [Nat.add_assoc], by dsimp only [g]; simp, ?_⟩
            intro u hu
            dsimp only [g] at hu
            simp only [List.getElem_append_right (le_refl _), Nat.sub_self,
              List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ ho1)
            · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ ho2)
          · rcases hpw12.2 w hw' with h0 | ⟨j, hj, rfl, hop, hin⟩
            · exact Or.inl h0
            · refine Or.inr ⟨j, by simp [List.length_append] at hj ⊢; omega, rfl, ?_, ?_⟩
              · rw [List.getElem_append_left hj]; exact hop
              · intro u hu
                rw [List.getElem_append_left hj] at hu
                exact Finset.mem_insert_of_mem (hin u hu)
      · intro v hv
        rw [wiresFrom_append, wiresFrom_append]
        set u1 := wiresFrom gs1 v with hu1
        have lu1 : u1.length = m + gs1.length := by rw [hu1, length_wiresFrom, hv]
        set u2 := wiresFrom gs2 u1 with hu2
        have lu2 : u2.length = out := by rw [hu2, length_wiresFrom, lu1]
        change (u2 ++ [(u2.getD o1 false || (u2.getD o2 false || false))]).getD out false = _
        rw [← lu2, getD_snoc, Bool.or_false]
        have e1 : u2.getD o1 false = F1 (fun i => v.getD i false) := by
          rw [hu2, getD_wiresFrom _ _ _ (by omega), hu1, hev1 v hv]
        have e2 : u2.getD o2 false = F2 (fun i => v.getD i false) := by
          rw [hu2, hev2 u1 lu1]
          congr 1; funext i
          rw [hu1, getD_wiresFrom _ _ _ (by have := i.isLt; omega)]
        rw [e1, e2]
    have bldPure_points : ∀ (S : Finset (Fin Np)), S.Nonempty →
        BldPure false (fun x => decide (∃ p ∈ S, x (Fin.castAdd Nl p) = true)) (S.card - 1) := by
      intro S hS
      have hlist : ∀ (ps : List (Fin Np)) (p0 : Fin Np),
          BldPure false (fun x => (p0 :: ps).any fun p => x (Fin.castAdd Nl p)) ps.length := by
        intro ps
        induction ps with
        | nil =>
          intro p0
          exact bldPure_congr false (fun x => x (Fin.castAdd Nl p0))
            (fun x => [p0].any fun p => x (Fin.castAdd Nl p)) 0
            (bldPure_point p0) (by intro x; simp)
        | cons p1 ps ih =>
          intro p0
          exact bldPure_congr false
            (fun x => x (Fin.castAdd Nl p0) || ((p1 :: ps).any fun p => x (Fin.castAdd Nl p)))
            (fun x => (p0 :: p1 :: ps).any fun p => x (Fin.castAdd Nl p)) ((p1 :: ps).length)
            (bldPure_mono false
              (fun x => x (Fin.castAdd Nl p0) || ((p1 :: ps).any fun p => x (Fin.castAdd Nl p)))
              (0 + ps.length + 1) (p1 :: ps).length
              (bldPure_or false (fun x => x (Fin.castAdd Nl p0))
                (fun x => (p1 :: ps).any fun p => x (Fin.castAdd Nl p)) 0 ps.length
                (bldPure_point p0) (ih p1)) (by simp))
            (by intro x; simp)
      obtain ⟨p0, ps, hl⟩ : ∃ p0 ps, S.toList = p0 :: ps := by
        cases h : S.toList with
        | nil => simp at h; exact absurd h hS.ne_empty
        | cons p0 ps => exact ⟨p0, ps, rfl⟩
      have hc : S.card = ps.length + 1 := by rw [← Finset.length_toList, hl]; rfl
      refine bldPure_congr false
        (fun x => (p0 :: ps).any fun p => x (Fin.castAdd Nl p))
        (fun x => decide (∃ p ∈ S, x (Fin.castAdd Nl p) = true)) (S.card - 1)
        (bldPure_mono false (fun x => (p0 :: ps).any fun p => x (Fin.castAdd Nl p))
          ps.length (S.card - 1) (hlist ps p0) (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
      simp
    have bldPure_lines : ∀ (S : Finset (Fin Nl)), S.Nonempty →
        BldPure true (fun x => decide (∃ l ∈ S, x (Fin.natAdd Np l) = true)) (S.card - 1) := by
      intro S hS
      have hlist : ∀ (ls : List (Fin Nl)) (l0 : Fin Nl),
          BldPure true (fun x => (l0 :: ls).any fun l => x (Fin.natAdd Np l)) ls.length := by
        intro ls
        induction ls with
        | nil =>
          intro l0
          exact bldPure_congr true (fun x => x (Fin.natAdd Np l0))
            (fun x => [l0].any fun l => x (Fin.natAdd Np l)) 0
            (bldPure_line l0) (by intro x; simp)
        | cons l1 ls ih =>
          intro l0
          exact bldPure_congr true
            (fun x => x (Fin.natAdd Np l0) || ((l1 :: ls).any fun l => x (Fin.natAdd Np l)))
            (fun x => (l0 :: l1 :: ls).any fun l => x (Fin.natAdd Np l)) ((l1 :: ls).length)
            (bldPure_mono true
              (fun x => x (Fin.natAdd Np l0) || ((l1 :: ls).any fun l => x (Fin.natAdd Np l)))
              (0 + ls.length + 1) (l1 :: ls).length
              (bldPure_or true (fun x => x (Fin.natAdd Np l0))
                (fun x => (l1 :: ls).any fun l => x (Fin.natAdd Np l)) 0 ls.length
                (bldPure_line l0) (ih l1)) (by simp))
            (by intro x; simp)
      obtain ⟨l0, ls, hl⟩ : ∃ l0 ls, S.toList = l0 :: ls := by
        cases h : S.toList with
        | nil => simp at h; exact absurd h hS.ne_empty
        | cons l0 ls => exact ⟨l0, ls, rfl⟩
      have hc : S.card = ls.length + 1 := by rw [← Finset.length_toList, hl]; rfl
      refine bldPure_congr true
        (fun x => (l0 :: ls).any fun l => x (Fin.natAdd Np l))
        (fun x => decide (∃ l ∈ S, x (Fin.natAdd Np l) = true)) (S.card - 1)
        (bldPure_mono true (fun x => (l0 :: ls).any fun l => x (Fin.natAdd Np l))
          ls.length (S.card - 1) (hlist ls l0) (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
      simp
    let BldTop : ((Fin (Np + Nl) → Bool) → Bool) → ℕ → Prop :=
      fun F s => ∀ m, Np + Nl ≤ m →
        ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ) (P L : Finset ℕ),
          AO2Seg m gs ∧ gs.length ≤ s ∧ out < m + gs.length ∧
          PureWire m false gs P ∧ PureWire m true gs L ∧ AndPure gs P L ∧
          ∀ v : List Bool, v.length = m →
            (wiresFrom gs v).getD out false = F (fun i => v.getD i false)
    have bldTop_mono : ∀ (F : (Fin (Np + Nl) → Bool) → Bool) (s s' : ℕ),
        BldTop F s → s ≤ s' → BldTop F s' := by
      intro F s s' h hs m hm
      obtain ⟨gs, out, P, L, hao, hlen, hout, hp, hl, hand, hev⟩ := h m hm
      exact ⟨gs, out, P, L, hao, le_trans hlen hs, hout, hp, hl, hand, hev⟩
    have bldTop_congr : ∀ (F H : (Fin (Np + Nl) → Bool) → Bool) (s : ℕ),
        BldTop F s → (∀ x, F x = H x) → BldTop H s := by
      intro F H s h he m hm
      obtain ⟨gs, out, P, L, hao, hlen, hout, hp, hl, hand, hev⟩ := h m hm
      exact ⟨gs, out, P, L, hao, hlen, hout, hp, hl, hand, fun v hv => by rw [hev v hv, he]⟩
    have bldTop_and : ∀ (FP FL : (Fin (Np + Nl) → Bool) → Bool) (s1 s2 : ℕ),
        BldPure false FP s1 → BldPure true FL s2 →
        BldTop (fun x => FP x && FL x) (s1 + s2 + 1) := by
      intro FP FL s1 s2 hP hL m hm
      obtain ⟨gs1, o1, P, hao1, hor1, hlen1, ho1, hp, hev1⟩ := hP m hm
      obtain ⟨gs2, o2, L, hao2, hor2, hlen2, ho2, hl, hev2⟩ := hL (m + gs1.length) (by omega)
      let out := m + gs1.length + gs2.length
      let g := PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [o1, o2]
      have ho1lt : o1 < m + gs1.length := hp.1 o1 ho1
      have ho2lt : o2 < out := hl.1 o2 ho2
      have haoG : AO2Seg (m + (gs1 ++ gs2).length) [g] := by
        intro j hj
        have hj0 : j = 0 := by simp at hj; exact hj
        subst hj0
        refine ⟨Or.inl rfl, rfl, ?_⟩
        intro u hu
        dsimp only [g] at hu
        simp only [List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
        rw [List.length_append]
        rcases hu with rfl | rfl <;> omega
      have hand1 : AndPure gs1 P L := fun j hj h => absurd (hor1 j hj) (by rw [h]; simp)
      have hand2 : AndPure gs2 P L := fun j hj h => absurd (hor2 j hj) (by rw [h]; simp)
      have handG : AndPure [g] P L := by
        intro j hj _
        have hj0 : j = 0 := by simp at hj; exact hj
        subst hj0
        exact ⟨o1, o2, rfl, ho1, ho2⟩
      refine ⟨(gs1 ++ gs2) ++ [g], out, P, L,
        ao2Seg_append (ao2Seg_append hao1 hao2) haoG, by simp; omega, by dsimp only [out]; simp; omega,
        pureWire_append_left (pureWire_append_left hp),
        pureWire_append_left (pureWire_append_right hl),
        andPure_append (andPure_append hand1 hand2) handG, ?_⟩
      intro v hv
      rw [wiresFrom_append, wiresFrom_append]
      set u1 := wiresFrom gs1 v with hu1
      have lu1 : u1.length = m + gs1.length := by rw [hu1, length_wiresFrom, hv]
      set u2 := wiresFrom gs2 u1 with hu2
      have lu2 : u2.length = out := by rw [hu2, length_wiresFrom, lu1]
      change (u2 ++ [(u2.getD o1 false && (u2.getD o2 false && true))]).getD out false = _
      rw [← lu2, getD_snoc, Bool.and_true]
      have e1 : u2.getD o1 false = FP (fun i => v.getD i false) := by
        rw [hu2, getD_wiresFrom _ _ _ (by omega), hu1, hev1 v hv]
      have e2 : u2.getD o2 false = FL (fun i => v.getD i false) := by
        rw [hu2, hev2 u1 lu1]
        congr 1; funext i
        rw [hu1, getD_wiresFrom _ _ _ (by have := i.isLt; omega)]
      rw [e1, e2]
    have bldTop_or : ∀ (F1 F2 : (Fin (Np + Nl) → Bool) → Bool) (s1 s2 : ℕ),
        BldTop F1 s1 → BldTop F2 s2 → BldTop (fun x => F1 x || F2 x) (s1 + s2 + 1) := by
      intro F1 F2 s1 s2 ht1 ht2 m hm
      obtain ⟨gs1, o1, P1, L1, hao1, hlen1, ho1lt, hp1, hl1, hand1, hev1⟩ := ht1 m hm
      obtain ⟨gs2, o2, P2, L2, hao2, hlen2, ho2lt, hp2, hl2, hand2, hev2⟩ :=
        ht2 (m + gs1.length) (by omega)
      let out := m + gs1.length + gs2.length
      let g := PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [o1, o2]
      have haoG : AO2Seg (m + (gs1 ++ gs2).length) [g] := by
        intro j hj
        have hj0 : j = 0 := by simp at hj; exact hj
        subst hj0
        refine ⟨Or.inr rfl, rfl, ?_⟩
        intro u hu
        dsimp only [g] at hu
        simp only [List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
        rw [List.length_append]
        rcases hu with rfl | rfl <;> omega
      have handG : AndPure [g] (P1 ∪ P2) (L1 ∪ L2) := by
        intro j hj h
        have hj0 : j = 0 := by simp at hj; exact hj
        subst hj0
        dsimp only [g] at h; simp at h
      refine ⟨(gs1 ++ gs2) ++ [g], out, P1 ∪ P2, L1 ∪ L2,
        ao2Seg_append (ao2Seg_append hao1 hao2) haoG, by simp; omega, by dsimp only [out]; simp; omega,
        pureWire_append_left (pureWire_union (pureWire_append_left hp1) (pureWire_append_right hp2)),
        pureWire_append_left (pureWire_union (pureWire_append_left hl1) (pureWire_append_right hl2)),
        andPure_append (andPure_append
          (andPure_mono Finset.subset_union_left Finset.subset_union_left hand1)
          (andPure_mono Finset.subset_union_right Finset.subset_union_right hand2)) handG, ?_⟩
      intro v hv
      rw [wiresFrom_append, wiresFrom_append]
      set u1 := wiresFrom gs1 v with hu1
      have lu1 : u1.length = m + gs1.length := by rw [hu1, length_wiresFrom, hv]
      set u2 := wiresFrom gs2 u1 with hu2
      have lu2 : u2.length = out := by rw [hu2, length_wiresFrom, lu1]
      change (u2 ++ [(u2.getD o1 false || (u2.getD o2 false || false))]).getD out false = _
      rw [← lu2, getD_snoc, Bool.or_false]
      have e1 : u2.getD o1 false = F1 (fun i => v.getD i false) := by
        rw [hu2, getD_wiresFrom _ _ _ (by omega), hu1, hev1 v hv]
      have e2 : u2.getD o2 false = F2 (fun i => v.getD i false) := by
        rw [hu2, hev2 u1 lu1]
        congr 1; funext i
        rw [hu1, getD_wiresFrom _ _ _ (by have := i.isLt; omega)]
      rw [e1, e2]
    classical
    have bldTop_edges : ∀ (T : Finset (Fin Np ⊕ Fin Nl)) (E0 : Finset (Fin Np × Fin Nl)),
        E0.Nonempty → (∀ e ∈ E0, Sum.inl e.1 ∈ T ∨ Sum.inr e.2 ∈ T) →
        BldTop (fun x => decide (∃ e ∈ E0,
          x (Fin.castAdd Nl e.1) = true ∧ x (Fin.natAdd Np e.2) = true)) (E0.card + T.card - 1) := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        intro E0 hE0 hc
        obtain ⟨e, he⟩ := hE0
        have := hc e he
        simp at this
      | @insert t T0 htT ih =>
        intro E0 hE0 hc
        let matchT : Fin Np × Fin Nl → Prop := fun e =>
          Sum.elim (fun p => e.1 = p) (fun l => e.2 = l) t
        set E1 := E0.filter matchT with hE1
        set E2 := E0.filter (fun e => ¬ matchT e) with hE2
        have hsplit : E1.card + E2.card = E0.card := Finset.card_filter_add_card_filter_not _
        have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
        have hc2 : ∀ e ∈ E2, Sum.inl e.1 ∈ T0 ∨ Sum.inr e.2 ∈ T0 := by
          intro e he
          rw [hE2, Finset.mem_filter] at he
          rcases hc e he.1 with h | h
          · rcases Finset.mem_insert.mp h with heq | h0
            · cases t with
              | inl p => cases heq; exact absurd rfl he.2
              | inr l => cases heq
            · exact Or.inl h0
          · rcases Finset.mem_insert.mp h with heq | h0
            · cases t with
              | inl p => cases heq
              | inr l => cases heq; exact absurd rfl he.2
            · exact Or.inr h0
        have hmem1 : ∀ e, e ∈ E1 ↔ e ∈ E0 ∧ matchT e := fun e => by rw [hE1, Finset.mem_filter]
        have hstar : E1.Nonempty → BldTop (fun x => decide (∃ e ∈ E1,
            x (Fin.castAdd Nl e.1) = true ∧ x (Fin.natAdd Np e.2) = true)) E1.card := by
          intro h1'
          cases t with
          | inl p =>
            let S : Finset (Fin Nl) := E1.image Prod.snd
            have hSne : S.Nonempty := h1'.image _
            have hSc : S.card ≤ E1.card := Finset.card_image_le
            have hpos : 1 ≤ S.card := hSne.card_pos
            refine bldTop_congr
              (fun x => x (Fin.castAdd Nl p) && decide (∃ l ∈ S, x (Fin.natAdd Np l) = true))
              (fun x => decide (∃ e ∈ E1,
                x (Fin.castAdd Nl e.1) = true ∧ x (Fin.natAdd Np e.2) = true))
              E1.card
              (bldTop_mono
                (fun x => x (Fin.castAdd Nl p) && decide (∃ l ∈ S, x (Fin.natAdd Np l) = true))
                (0 + (S.card - 1) + 1) E1.card
                (bldTop_and (fun x => x (Fin.castAdd Nl p))
                  (fun x => decide (∃ l ∈ S, x (Fin.natAdd Np l) = true)) 0 (S.card - 1)
                  (bldPure_point p) (bldPure_lines S hSne)) (by omega)) ?_
            intro x
            rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
            constructor
            · rintro ⟨hp, l, hl, hxl⟩
              obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hl
              have hm := ((hmem1 e).mp he).2
              change e.1 = p at hm
              exact ⟨e, he, hm ▸ hp, hxl⟩
            · rintro ⟨e, he, hxp, hxl⟩
              have hm := ((hmem1 e).mp he).2
              change e.1 = p at hm
              exact ⟨hm ▸ hxp, e.2, Finset.mem_image_of_mem _ he, hxl⟩
          | inr l =>
            let S : Finset (Fin Np) := E1.image Prod.fst
            have hSne : S.Nonempty := h1'.image _
            have hSc : S.card ≤ E1.card := Finset.card_image_le
            have hpos : 1 ≤ S.card := hSne.card_pos
            refine bldTop_congr
              (fun x => decide (∃ p ∈ S, x (Fin.castAdd Nl p) = true) && x (Fin.natAdd Np l))
              (fun x => decide (∃ e ∈ E1,
                x (Fin.castAdd Nl e.1) = true ∧ x (Fin.natAdd Np e.2) = true))
              E1.card
              (bldTop_mono
                (fun x => decide (∃ p ∈ S, x (Fin.castAdd Nl p) = true) && x (Fin.natAdd Np l))
                ((S.card - 1) + 0 + 1) E1.card
                (bldTop_and (fun x => decide (∃ p ∈ S, x (Fin.castAdd Nl p) = true))
                  (fun x => x (Fin.natAdd Np l)) (S.card - 1) 0
                  (bldPure_points S hSne) (bldPure_line l)) (by omega)) ?_
            intro x
            rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
            constructor
            · rintro ⟨⟨p, hp, hxp⟩, hxl⟩
              obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
              have hm := ((hmem1 e).mp he).2
              change e.2 = l at hm
              exact ⟨e, he, hxp, hm ▸ hxl⟩
            · rintro ⟨e, he, hxp, hxl⟩
              have hm := ((hmem1 e).mp he).2
              change e.2 = l at hm
              exact ⟨⟨e.1, Finset.mem_image_of_mem _ he, hxp⟩, hm ▸ hxl⟩
        have key : ∀ x : Fin (Np + Nl) → Bool,
            decide (∃ e ∈ E0, x (Fin.castAdd Nl e.1) = true ∧ x (Fin.natAdd Np e.2) = true) =
            (decide (∃ e ∈ E1, x (Fin.castAdd Nl e.1) = true ∧ x (Fin.natAdd Np e.2) = true) ||
              decide (∃ e ∈ E2, x (Fin.castAdd Nl e.1) = true ∧ x (Fin.natAdd Np e.2) = true)) := by
          intro x
          rw [Bool.eq_iff_iff]
          simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
          constructor
          · rintro ⟨e, he, h⟩
            by_cases hm : matchT e
            · exact Or.inl ⟨e, ⟨he, hm⟩, h⟩
            · exact Or.inr ⟨e, ⟨he, hm⟩, h⟩
          · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
        rw [hcard]
        let FE : Finset (Fin Np × Fin Nl) → (Fin (Np + Nl) → Bool) → Bool :=
          fun S x => decide (∃ e ∈ S, x (Fin.castAdd Nl e.1) = true ∧ x (Fin.natAdd Np e.2) = true)
        by_cases he1 : E1.Nonempty
        · by_cases he2 : E2.Nonempty
          · have hp2 := he2.card_pos
            refine bldTop_congr (fun x => FE E1 x || FE E2 x) (FE E0) (E0.card + (T0.card + 1) - 1)
              (bldTop_mono (fun x => FE E1 x || FE E2 x)
                (E1.card + (E2.card + T0.card - 1) + 1) (E0.card + (T0.card + 1) - 1)
                (bldTop_or (FE E1) (FE E2) E1.card (E2.card + T0.card - 1)
                  (hstar he1) (ih E2 he2 hc2)) (by omega)) ?_
            intro x; exact (key x).symm
          · rw [Finset.not_nonempty_iff_eq_empty] at he2
            refine bldTop_congr (FE E1) (FE E0) (E0.card + (T0.card + 1) - 1)
              (bldTop_mono (FE E1) E1.card (E0.card + (T0.card + 1) - 1) (hstar he1) (by omega)) ?_
            intro x; dsimp only [FE]; rw [key, he2]; simp
        · rw [Finset.not_nonempty_iff_eq_empty] at he1
          have he2 : E2.Nonempty := by
            by_contra he2
            rw [Finset.not_nonempty_iff_eq_empty] at he2
            have := hE0.card_pos
            rw [he1, he2] at hsplit; simp at hsplit; omega
          refine bldTop_congr (FE E2) (FE E0) (E0.card + (T0.card + 1) - 1)
            (bldTop_mono (FE E2) (E2.card + T0.card - 1) (E0.card + (T0.card + 1) - 1)
              (ih E2 he2 hc2) (by omega)) ?_
          intro x; dsimp only [FE]; rw [key, he1]; simp
    let T : Finset (Fin Np ⊕ Fin Nl) := Kp.image Sum.inl ∪ Kl.image Sum.inr
    obtain ⟨p0, l0, h0⟩ := hEx
    have hEne : E.Nonempty := ⟨(p0, l0), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩
    have hEpos : 1 ≤ E.card := hEne.card_pos
    have hCovT : ∀ e ∈ E, Sum.inl e.1 ∈ T ∨ Sum.inr e.2 ∈ T := by
      intro e he
      rcases hCovI e.1 e.2 (Finset.mem_filter.mp he).2 with hp | hl
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
      · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hl))
    have hTcard : T.card ≤ Kp.card + Kl.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    obtain ⟨gs, out, P, L, hao, hlen, _, hp, hl, hand, hev⟩ :=
      bldTop_edges T E hEne hCovT (Np + Nl) le_rfl
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs, out⟩
    have hga : ∀ i (hi : i < gs.length),
        PEqualNP.MetaComplexity.NestedCover.gateAt D i = gs[i] := by
      intro i hi
      change gs.getD i ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = gs[i]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    refine ⟨D, P, L, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact And.intro
        (fun g hg => by
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
          exact (hao j hj).1)
        (And.intro
          (fun j hj u hu => by
            rw [hga j hj] at hu
            exact (hao j hj).2.2 u hu)
          (fun g hg => by
            obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
            exact (hao j hj).2.1))
    · intro y
      have e := hev (List.ofFn y) (by simp)
      have hfun : (fun i : Fin (Np + Nl) => (List.ofFn y).getD i false) = y := by
        funext i; simp [List.getD_eq_getElem?_getD]
      rw [hfun] at e
      change (wiresFrom gs (List.ofFn y)).getD out false = _
      rw [e]
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨⟨p, l⟩, he, hyp, hyl⟩
        exact ⟨p, l, (Finset.mem_filter.mp he).2, hyp, hyl⟩
      · rintro ⟨p, l, hpl, hyp, hyl⟩
        exact ⟨(p, l), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩, hyp, hyl⟩
    · change gs.length ≤ C.gates.length
      have hCs : C'.size = C'.gates.length := rfl
      have hCs0 : C.size = C.gates.length := rfl
      omega
    · intro w hw
      rcases hp.2 w hw with h0 | ⟨j, hj, rfl, hop, hin⟩
      · exact Or.inl h0
      · refine Or.inr ⟨j, hj, rfl, ?_, ?_⟩
        · rw [hga j hj]; exact hop
        · rw [hga j hj]; exact hin
    · intro w hw
      rcases hl.2 w hw with h0 | ⟨j, hj, rfl, hop, hin⟩
      · exact Or.inl h0
      · refine Or.inr ⟨j, hj, rfl, ?_, ?_⟩
        · rw [hga j hj]; exact hop
        · rw [hga j hj]; exact hin
    · intro i hi hop
      rw [hga i hi] at hop ⊢
      exact hand i hi hop
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
