import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1840 : (∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size) → ∀ (qlv17c Nlv17c Rlv17c : ℕ) (Ilv17c : Fin Nlv17c → Fin Nlv17c → Prop) [DecidableRel Ilv17c] (Xlv17c : PEqualNP.CircuitLowerBounds.Circuit) (pslv17c : Fin Nlv17c → ℕ) (Slv17c Wlv17c : Finset (Fin Nlv17c)), 2 ≤ qlv17c → Nlv17c = qlv17c ^ 2 + qlv17c + 1 → (∀ llv17c : Fin Nlv17c, (Finset.univ.filter (fun plv17cx2 => Ilv17c plv17cx2 llv17c)).card = qlv17c + 1) → (∀ palv17c pblv17c : Fin Nlv17c, palv17c ≠ pblv17c → ∃! lblv17c : Fin Nlv17c, Ilv17c palv17c lblv17c ∧ Ilv17c pblv17c lblv17c) → 1 ≤ Rlv17c → Rlv17c ≤ qlv17c → ((∀ glv17c ∈ Xlv17c.gates, (glv17c.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv17c.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv17c.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack Nlv17c Xlv17c) → (∀ (wlv17c : Fin Nlv17c) (xlv17c xlv17cx1 : Fin Nlv17c → Bool), (∀ plv17c ∈ Slv17c, xlv17c plv17c = xlv17cx1 plv17c) → (Xlv17c.wires (List.ofFn xlv17c)).getD (pslv17c wlv17c) false = (Xlv17c.wires (List.ofFn xlv17cx1)).getD (pslv17c wlv17c) false) → (∀ wlv17cx1 ∈ Wlv17c, ∀ Xslv17c : Finset (Fin Nlv17c), Xslv17c ⊆ Slv17c → (∀ plv17cx1 ∈ Xslv17c, ¬ Ilv17c plv17cx1 wlv17cx1) → Xslv17c.card ≤ Rlv17c → (Xlv17c.wires (List.ofFn (fun alv17c : Fin Nlv17c => decide (alv17c ∈ Xslv17c)))).getD (pslv17c wlv17cx1) false = false) → Rlv17c * ∑ wlv17cx2 ∈ Wlv17c, (Slv17c.filter (fun ulv17c : Fin Nlv17c => (Xlv17c.wires (List.ofFn (fun alv17cx1 : Fin Nlv17c => decide (alv17cx1 = ulv17c)))).getD (pslv17c wlv17cx2) false = true)).card ≤ Rlv17c * Wlv17c.card + qlv17c * Xlv17c.size := by
  intro H q N R I _ X ps S W hq hN hline hpts hR1 hRq hXC hdep hzero
  obtain ⟨hgates, hrb⟩ := hXC
  set sw : Fin N → Finset (Fin N) := fun w => S.filter (fun u : Fin N =>
    (X.wires (List.ofFn (fun a : Fin N => decide (a = u)))).getD (ps w) false = true) with hsw
  have hsub : ∀ w ∈ W, sw w ⊆ Finset.univ.filter (fun p => I p w) := by
    intro w hw u hu
    rw [hsw, Finset.mem_filter] at hu
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hnot
    have h0 := hzero w hw {u} (Finset.singleton_subset_iff.mpr hu.1)
      (by intro p hp; rw [Finset.mem_singleton] at hp; subst hp; exact hnot)
      (by rw [Finset.card_singleton]; exact hR1)
    have hfun : (fun a : Fin N => decide (a ∈ ({u} : Finset (Fin N)))) =
        (fun a : Fin N => decide (a = u)) := by
      funext a; simp only [Finset.mem_singleton]
    rw [hfun] at h0
    rw [h0] at hu
    exact Bool.false_ne_true hu.2
  have hcard : ∀ w ∈ W, (sw w).card ≤ q + 1 := by
    intro w hw
    calc (sw w).card ≤ (Finset.univ.filter (fun p => I p w)).card := Finset.card_le_card (hsub w hw)
      _ = q + 1 := hline w
  have key : ∀ s : ℕ, s ≤ q + 1 → R * s ≤ R + q * min R (s - 1) := by
    intro s hs
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0; simp
    · obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      rcases le_total R t with h | h
      · rw [min_eq_left h]
        have : R * t ≤ R * q := Nat.mul_le_mul_left R (by omega)
        calc R * (t + 1) = R * t + R := by ring
          _ ≤ R * q + R := by omega
          _ = R + q * R := by ring
      · rw [min_eq_right h]
        have : R * t ≤ q * t := Nat.mul_le_mul_right t hRq
        calc R * (t + 1) = R * t + R := by ring
          _ ≤ q * t + R := by omega
          _ = R + q * t := by ring
  set W' := W.filter (fun w => 2 ≤ (sw w).card) with hW'
  set e : Fin W'.card → Fin N := fun i => (W'.equivFin.symm i).1 with he
  have heW' : ∀ i, e i ∈ W' := fun i => (W'.equivFin.symm i).2
  have heW : ∀ i, e i ∈ W := fun i => (Finset.mem_filter.mp (heW' i)).1
  have he2 : ∀ i, 2 ≤ (sw (e i)).card := fun i => (Finset.mem_filter.mp (heW' i)).2
  have heinj : ∀ i j, e i = e j → i = j := by
    intro i j hij
    exact W'.equivFin.symm.injective (Subtype.ext hij)
  have hH := H N W'.card R (fun i => Finset.univ.filter (fun p => I p (e i))) (fun i => sw (e i)) X
    (fun i => ps (e i)) (fun i => min R ((sw (e i)).card - 1))
    (by
      intro i j hij
      by_contra hc
      obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.mp (not_le.mp hc)
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hp1 hp2
      obtain ⟨l, _, hl⟩ := hpts p1 p2 hne
      have h1 := hl (e i) ⟨hp1.1.2, hp2.1.2⟩
      have h2 := hl (e j) ⟨hp1.2.2, hp2.2.2⟩
      exact hij (heinj i j (h1.trans h2.symm)))
    (fun i => hsub (e i) (heW i))
    he2
    hgates hrb
    (by
      intro i p
      constructor
      · intro hp
        rw [hsw, Finset.mem_filter]
        refine ⟨?_, hp⟩
        by_contra hpS
        have hagree := hdep (e i) (fun a : Fin N => decide (a = p))
          (fun a : Fin N => decide (a ∈ (∅ : Finset (Fin N))))
          (by
            intro p' hp'
            have hne : p' ≠ p := fun h => hpS (h ▸ hp')
            simp [hne])
        have h0 := hzero (e i) (heW i) ∅ (Finset.empty_subset _)
          (by intro p' hp'; exact absurd hp' (Finset.notMem_empty _))
          (by rw [Finset.card_empty]; exact Nat.zero_le _)
        rw [hagree, h0] at hp
        exact Bool.false_ne_true hp
      · intro hp
        rw [hsw, Finset.mem_filter] at hp
        exact hp.2)
    (by
      intro i x hx hU
      have hagree := hdep (e i) x
        (fun a : Fin N => decide (a ∈ S.filter (fun b => x b = true)))
        (by
          intro p hp
          cases hxp : x p
          · simp [hxp]
          · simp [hxp, hp])
      rw [hagree]
      apply hzero (e i) (heW i) (S.filter (fun b => x b = true)) (Finset.filter_subset _ _)
      · intro p hp hI
        rw [Finset.mem_filter] at hp
        have := hU p (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hI⟩)
        rw [this] at hp
        exact Bool.false_ne_true hp.2
      · calc (S.filter (fun b => x b = true)).card
            ≤ (Finset.univ.filter (fun b => x b = true)).card :=
              Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
          _ ≤ R := hx)
    (fun i => min_le_left _ _)
    (by
      intro i
      have := he2 i
      have : min R ((sw (e i)).card - 1) ≤ (sw (e i)).card - 1 := min_le_right _ _
      omega)
  have hsumW' : ∑ i : Fin W'.card, min R ((sw (e i)).card - 1) =
      ∑ w ∈ W', min R ((sw w).card - 1) := by
    rw [← Finset.sum_coe_sort W']
    exact Equiv.sum_comp W'.equivFin.symm (fun x : W' => min R ((sw x.1).card - 1))
  have hsumW : ∑ w ∈ W', min R ((sw w).card - 1) = ∑ w ∈ W, min R ((sw w).card - 1) := by
    rw [hW', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w _
    split_ifs with h
    · rfl
    · have : (sw w).card - 1 = 0 := by omega
      rw [this, min_eq_right (Nat.zero_le _)]
  calc R * ∑ w ∈ W, (sw w).card = ∑ w ∈ W, R * (sw w).card := Finset.mul_sum _ _ _
    _ ≤ ∑ w ∈ W, (R + q * min R ((sw w).card - 1)) :=
        Finset.sum_le_sum (fun w hw => key _ (hcard w hw))
    _ = R * W.card + q * ∑ w ∈ W, min R ((sw w).card - 1) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ R * W.card + q * X.size := by
        rw [← hsumW, ← hsumW']
        exact Nat.add_le_add_left (Nat.mul_le_mul_left q hH) _
