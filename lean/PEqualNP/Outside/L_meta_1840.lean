import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1840 : (∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size) → ∀ (qlv17c Nlv17c Rlv17c : ℕ) (Ilv17c : Fin Nlv17c → Fin Nlv17c → Prop) [DecidableRel Ilv17c] (Xlv17c : PEqualNP.CircuitLowerBounds.Circuit) (pslv17c : Fin Nlv17c → ℕ) (Slv17c Wlv17c : Finset (Fin Nlv17c)), 2 ≤ qlv17c → Nlv17c = qlv17c ^ 2 + qlv17c + 1 → (∀ llv17c : Fin Nlv17c, (Finset.univ.filter (fun plv17cx2 => Ilv17c plv17cx2 llv17c)).card = qlv17c + 1) → (∀ palv17c pblv17c : Fin Nlv17c, palv17c ≠ pblv17c → ∃! lblv17c : Fin Nlv17c, Ilv17c palv17c lblv17c ∧ Ilv17c pblv17c lblv17c) → 1 ≤ Rlv17c → Rlv17c ≤ qlv17c → ((∀ glv17c ∈ Xlv17c.gates, (glv17c.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17c.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17c.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack Nlv17c Xlv17c) → (∀ (wlv17c : Fin Nlv17c) (xlv17c xlv17cx1 : Fin Nlv17c → Bool), (∀ plv17c ∈ Slv17c, xlv17c plv17c = xlv17cx1 plv17c) → (Xlv17c.wires (List.ofFn xlv17c)).getD (pslv17c wlv17c) false = (Xlv17c.wires (List.ofFn xlv17cx1)).getD (pslv17c wlv17c) false) → (∀ wlv17cx1 ∈ Wlv17c, ∀ Xslv17c : Finset (Fin Nlv17c), Xslv17c ⊆ Slv17c → (∀ plv17cx1 ∈ Xslv17c, ¬ Ilv17c plv17cx1 wlv17cx1) → Xslv17c.card ≤ Rlv17c → (Xlv17c.wires (List.ofFn (fun alv17c : Fin Nlv17c => decide (alv17c ∈ Xslv17c)))).getD (pslv17c wlv17cx1) false = false) → Rlv17c * ∑ wlv17cx2 ∈ Wlv17c, (Slv17c.filter (fun ulv17c : Fin Nlv17c => (Xlv17c.wires (List.ofFn (fun alv17cx1 : Fin Nlv17c => decide (alv17cx1 = ulv17c)))).getD (pslv17c wlv17cx2) false = true)).card ≤ Rlv17c * Wlv17c.card + qlv17c * Xlv17c.size := by
  intro H q N R I _ X ps S W hq hN hline huniq hR1 hRq hX hdep hzero
  -- an output is false on any input with at most R true points, none on its line
  have hout : ∀ w ∈ W, ∀ x : Fin N → Bool,
      (Finset.univ.filter (fun b : Fin N => x b = true)).card ≤ R → (∀ p, I p w → x p = false) →
      (X.wires (List.ofFn x)).getD (ps w) false = false := by
    intro w hw x hx hoff
    rw [hdep w x (fun a => decide (a ∈ S.filter (fun p => x p = true))) (by
      intro p hp
      by_cases h : x p = true
      · simp [hp, h]
      · simp [hp, h])]
    apply hzero w hw (S.filter (fun p => x p = true)) (Finset.filter_subset _ _)
    · intro p hp hI
      rw [Finset.mem_filter, hoff p hI] at hp
      exact absurd hp.2 (by simp)
    · refine le_trans (Finset.card_le_card ?_) hx
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Finset.mem_univ _, hp.2⟩
  let T : Fin N → Finset (Fin N) := fun w => S.filter (fun u =>
    (X.wires (List.ofFn (fun a : Fin N => decide (a = u)))).getD (ps w) false = true)
  show R * ∑ w ∈ W, (T w).card ≤ R * W.card + q * X.size
  have hmemT : ∀ w u, u ∈ T w ↔ u ∈ S ∧
      (X.wires (List.ofFn (fun a : Fin N => decide (a = u)))).getD (ps w) false = true :=
    fun w u => Finset.mem_filter
  have hsingle : ∀ w ∈ W, ∀ u : Fin N, ¬ I u w →
      (X.wires (List.ofFn (fun a : Fin N => decide (a = u)))).getD (ps w) false = false := by
    intro w hw u hu
    apply hout w hw
    · refine le_trans (Finset.card_le_one.mpr ?_) hR1
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hb
      rw [ha, hb]
    · intro p hp
      simp only [decide_eq_false_iff_not]
      rintro rfl
      exact hu hp
  have hTsub : ∀ w ∈ W, T w ⊆ Finset.univ.filter (fun p => I p w) := by
    intro w hw u hu
    rw [hmemT] at hu
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra h
    rw [hsingle w hw u h] at hu
    exact absurd hu.2 (by simp)
  have hTcard : ∀ w ∈ W, (T w).card ≤ q + 1 :=
    fun w hw => (Finset.card_le_card (hTsub w hw)).trans (hline w).le
  let W' := W.filter (fun w => 2 ≤ (T w).card)
  let c : Fin N → ℕ := fun w => min R ((T w).card - 1)
  let e := W'.equivFin.symm
  have hW'W : ∀ i : Fin W'.card, (e i).1 ∈ W := fun i => (Finset.mem_filter.mp (e i).2).1
  have hW'2 : ∀ i : Fin W'.card, 2 ≤ (T (e i).1).card :=
    fun i => (Finset.mem_filter.mp (e i).2).2
  have h1 : ∀ i j : Fin W'.card, i ≠ j →
      (Finset.univ.filter (fun p => I p (e i).1) ∩
        Finset.univ.filter (fun p => I p (e j).1)).card ≤ 1 := by
    intro i j hij
    have hne : (e i).1 ≠ (e j).1 := fun h => hij (e.injective (Subtype.ext h))
    by_contra hc
    rw [not_le] at hc
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    obtain ⟨l, _, hl⟩ := huniq a b hab
    exact hne ((hl _ ⟨ha.1, hb.1⟩).trans (hl _ ⟨ha.2, hb.2⟩).symm)
  have h2 : ∀ i : Fin W'.card, T (e i).1 ⊆ Finset.univ.filter (fun p => I p (e i).1) :=
    fun i => hTsub _ (hW'W i)
  have h4 : ∀ (i : Fin W'.card) (p : Fin N),
      (X.wires (List.ofFn (fun a : Fin N => decide (a = p)))).getD (ps (e i).1) false = true ↔
        p ∈ T (e i).1 := by
    intro i p
    rw [hmemT]
    constructor
    · intro h
      refine ⟨?_, h⟩
      by_contra hp
      have h0 : (X.wires (List.ofFn (fun a : Fin N => decide (a = p)))).getD (ps (e i).1) false =
          (X.wires (List.ofFn (fun a : Fin N => decide (a ∈ (∅ : Finset (Fin N)))))).getD
            (ps (e i).1) false := by
        apply hdep
        intro a ha
        have hap : a ≠ p := fun h => hp (h ▸ ha)
        simp [hap]
      rw [h0, hzero _ (hW'W i) ∅ (Finset.empty_subset _) (by simp) (by simp)] at h
      exact absurd h (by simp)
    · exact fun h => h.2
  have h5 : ∀ (i : Fin W'.card) (x : Fin N → Bool),
      (Finset.univ.filter (fun b : Fin N => x b = true)).card ≤ R →
      (∀ b ∈ Finset.univ.filter (fun p => I p (e i).1), x b = false) →
      (X.wires (List.ofFn x)).getD (ps (e i).1) false = false := by
    intro i x hx hU
    exact hout _ (hW'W i) x hx (fun p hp => hU p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩))
  have h6 : ∀ i : Fin W'.card, c (e i).1 ≤ R := fun i => min_le_left _ _
  have h7 : ∀ i : Fin W'.card, c (e i).1 + 1 ≤ (T (e i).1).card := by
    intro i
    have hm := min_le_right R ((T (e i).1).card - 1)
    have hc2 := hW'2 i
    show min R ((T (e i).1).card - 1) + 1 ≤ (T (e i).1).card
    omega
  have key := H N W'.card R (fun i => Finset.univ.filter (fun p => I p (e i).1))
    (fun i => T (e i).1) X (fun i => ps (e i).1) (fun i => c (e i).1)
    h1 h2 hW'2 hX.1 hX.2 h4 h5 h6 h7
  have hsum : ∑ i : Fin W'.card, c (e i).1 = ∑ w ∈ W', c w := by
    rw [← Finset.sum_coe_sort W' c]
    exact Equiv.sum_comp e (fun x => c x.1)
  have hf : ∑ w ∈ W', c w = ∑ w ∈ W, if 2 ≤ (T w).card then c w else 0 :=
    Finset.sum_filter _ _
  calc R * ∑ w ∈ W, (T w).card = ∑ w ∈ W, R * (T w).card := Finset.mul_sum _ _ _
    _ ≤ ∑ w ∈ W, (R + q * (if 2 ≤ (T w).card then c w else 0)) := by
        apply Finset.sum_le_sum
        intro w hw
        have hb := hTcard w hw
        split_ifs with hc2
        · show R * (T w).card ≤ R + q * min R ((T w).card - 1)
          obtain ⟨t, ht⟩ : ∃ t, (T w).card = t + 1 := ⟨(T w).card - 1, by omega⟩
          rw [ht, Nat.add_sub_cancel]
          rw [ht] at hb
          rcases le_total R t with h | h
          · rw [min_eq_left h]
            nlinarith
          · rw [min_eq_right h]
            nlinarith
        · have h01 : (T w).card ≤ 1 := by omega
          calc R * (T w).card ≤ R * 1 := Nat.mul_le_mul_left _ h01
            _ = R + q * 0 := by ring
    _ = R * W.card + q * ∑ w ∈ W', c w := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum, hf]
        ring
    _ ≤ R * W.card + q * X.size := by
        rw [← hsum]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left _ key) _
