import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

/-- Reduction of L-meta-5030:
    Internally proves:
    1. `F.card ≤ D.size`, closing the case `N * q ≤ 100 * (F.card + 1)` immediately.
    2. Total number of incident pairs `{(p, l) | I p l}` equals `N * (q + 1)`.
    3. Every wire `w ∈ F` is either a star (all accepted incidences share one point or one line)
       or accepts a 2-matching `(p1, l1), (p2, l2)` with `p1 ≠ p2` and `l1 ≠ l2`.
    Splits the remaining small-`F` regime (`100 * (F.card + 1) < N * q`) by whether the star wires
    or the 2-matching wires cover at least half of all `N * (q + 1)` incident pairs. -/
theorem PEqualNP.Outside.R_meta_5030_512
    (star_heavy :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (D : Circuit) (F : Finset ℕ),
        let v (x : Fin (N + N) → Bool) (w : ℕ) := wireValue D (List.ofFn x) w
        let pair (p l : Fin N) (i : Fin (N + N)) :=
          decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
        let neg (Y : Finset (Fin N)) := Fin.addCases
          (fun p => decide (∀ l ∈ Y, ¬ I p l)) (fun l => decide (l ∈ Y))
        300 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
        (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) →
        Monotone2 D →
        (∀ (i : ℕ) (g : Gate), D.gates[i]? = some g →
          ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i) →
        100 * (F.card + 1) < N * q →
        (∀ w ∈ F, N + N ≤ w ∧ w < N + N + D.size ∧
          (gateAt D (w - (N + N))).op = .and ∧
          (∃ p l, I p l ∧ v (pair p l) w = true) ∧
          ((∃ p0, ∀ p l, I p l → v (pair p l) w = true → p = p0) ∨
           (∃ l0, ∀ p l, I p l → v (pair p l) w = true → l = l0))) →
        N * (q + 1) ≤ 2 * (Finset.univ.filter (fun pl : Fin N × Fin N =>
          I pl.1 pl.2 ∧ ∃ w ∈ F, v (pair pl.1 pl.2) w = true)).card →
        (∀ (Y : Finset (Fin N)), Y.card ≤ q → ∀ w ∈ F, v (neg Y) w = false) →
        N * q ≤ 100 * (D.size + 1))
    (nonstar_heavy :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (D : Circuit) (F : Finset ℕ),
        let v (x : Fin (N + N) → Bool) (w : ℕ) := wireValue D (List.ofFn x) w
        let pair (p l : Fin N) (i : Fin (N + N)) :=
          decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
        let neg (Y : Finset (Fin N)) := Fin.addCases
          (fun p => decide (∀ l ∈ Y, ¬ I p l)) (fun l => decide (l ∈ Y))
        300 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
        (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) →
        Monotone2 D →
        (∀ (i : ℕ) (g : Gate), D.gates[i]? = some g →
          ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + i) →
        100 * (F.card + 1) < N * q →
        (∀ w ∈ F, N + N ≤ w ∧ w < N + N + D.size ∧
          (gateAt D (w - (N + N))).op = .and ∧
          ∃ p1 l1 p2 l2, I p1 l1 ∧ I p2 l2 ∧ p1 ≠ p2 ∧ l1 ≠ l2 ∧
            v (pair p1 l1) w = true ∧ v (pair p2 l2) w = true) →
        N * (q + 1) ≤ 2 * (Finset.univ.filter (fun pl : Fin N × Fin N =>
          I pl.1 pl.2 ∧ ∃ w ∈ F, v (pair pl.1 pl.2) w = true)).card →
        (∀ (Y : Finset (Fin N)), Y.card ≤ q → ∀ w ∈ F, v (neg Y) w = false) →
        N * q ≤ 100 * (D.size + 1)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3]
      (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset ℕ),
      have x7 : (Fin (x2 + x2) → Bool) → ℕ → Bool :=
        fun (x7 : Fin (x2 + x2) → Bool) (x8 : ℕ) => PEqualNP.CircuitLowerBounds.wireValue x5 (List.ofFn x7) x8;
      have x8 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool :=
        fun (x8 x9 : Fin x2) (x10 : Fin (x2 + x2)) => Decidable.decide (x10 = Fin.castAdd x2 x8 ∨ x10 = Fin.natAdd x2 x9);
      have x9 : Finset (Fin x2) → Fin (x2 + x2) → Bool :=
        fun (x9 : Finset (Fin x2)) (x10 : Fin (x2 + x2)) =>
          Fin.addCases (fun (x11 : Fin x2) => Decidable.decide (∀ x12 ∈ x9, ¬x3 x11 x12))
            (fun (x11 : Fin x2) => Decidable.decide (x11 ∈ x9)) x10;
      (300 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x12 : Fin x2), Fintype.card { x13 : Fin x2 // x3 x13 x12 } = x1 + (1 : ℕ)) →
      (∀ (x13 x14 : Fin x2), x13 ≠ x14 → ∃! x16 : Fin x2, x3 x13 x16 ∧ x3 x14 x16) →
      PEqualNP.MetaComplexity.Monotone2 x5 →
      (∀ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x15]? = Option.some x16 →
        ∃ (x18 : ℕ) (x19 : ℕ), x16.inputs = [x18, x19] ∧ x18 < x19 ∧ x19 < x2 + x2 + x15) →
      (∀ x16 ∈ x6, x2 + x2 ≤ x16 ∧ x16 < x2 + x2 + x5.size ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt x5 (x16 - (x2 + x2))).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∃ (x18 : Fin x2) (x19 : Fin x2), x3 x18 x19 ∧ x7 (x8 x18 x19) x16 = Bool.true) →
      (∀ (x17 x18 : Fin x2), x3 x17 x18 → ∃ x20 ∈ x6, x7 (x8 x17 x18) x20 = Bool.true) →
      (∀ (x18 : Finset (Fin x2)), x18.card ≤ x1 → ∀ x20 ∈ x6, x7 (x9 x18) x20 = Bool.false) →
      x2 * x1 ≤ (100 : ℕ) * (x5.size + (1 : ℕ)) := by
  intro q N I _ D F v pair neg hq hN hdeg huniq hmono hshape hF hcov hneg
  -- Step 1: F.card ≤ D.size, so N * q ≤ 100 * (F.card + 1) closes immediately
  have hF_sub : F ⊆ Finset.Ico (N + N) (N + N + D.size) := by
    intro w hw
    rcases hF w hw with ⟨hlo, hhi, _, _⟩
    exact Finset.mem_Ico.mpr ⟨hlo, hhi⟩
  have hF_le : F.card ≤ D.size := by
    have h1 := Finset.card_le_card hF_sub
    rw [Nat.card_Ico] at h1
    omega
  by_cases hbigF : N * q ≤ 100 * (F.card + 1)
  · omega
  · have hsmallF : 100 * (F.card + 1) < N * q := by omega
    -- Step 2: Total number of incident pairs is N * (q + 1)
    let Eall : Finset (Fin N × Fin N) := Finset.univ.filter (fun pl => I pl.1 pl.2)
    have hEall_card : Eall.card = N * (q + 1) := by
      have h1 : Eall.card = ∑ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card := by
        dsimp only [Eall]
        rw [Finset.card_filter, Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.card_filter]
      rw [h1]
      have hline : ∀ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := by
        intro l
        rw [← Fintype.card_subtype]
        exact hdeg l
      simp [hline]
    -- Step 3: Partition F into star wires and 2-matching wires
    let isStar : ℕ → Prop := fun w =>
      (∃ p0, ∀ p l, I p l → v (pair p l) w = true → p = p0) ∨
      (∃ l0, ∀ p l, I p l → v (pair p l) w = true → l = l0)
    let _ : DecidablePred isStar := Classical.decPred isStar
    let Fstar : Finset ℕ := F.filter isStar
    let Fnon : Finset ℕ := F.filter (fun w => ¬ isStar w)
    have hnon_match : ∀ w ∈ Fnon,
        ∃ p1 l1 p2 l2, I p1 l1 ∧ I p2 l2 ∧ p1 ≠ p2 ∧ l1 ≠ l2 ∧
          v (pair p1 l1) w = true ∧ v (pair p2 l2) w = true := by
      intro w hw
      have hwF : w ∈ F := (Finset.mem_filter.mp hw).1
      have hns : ¬ isStar w := (Finset.mem_filter.mp hw).2
      rcases (hF w hwF).2.2.2 with ⟨p1, l1, hI1, hv1⟩
      have hnotP : ¬ (∀ p l, I p l → v (pair p l) w = true → p = p1) :=
        fun h => hns (Or.inl ⟨p1, h⟩)
      have hnotL : ¬ (∀ p l, I p l → v (pair p l) w = true → l = l1) :=
        fun h => hns (Or.inr ⟨l1, h⟩)
      push Not at hnotP hnotL
      rcases hnotP with ⟨p2, l2, hI2, hv2, hp2⟩
      by_cases hl2 : l2 = l1
      · rcases hnotL with ⟨p3, l3, hI3, hv3, hl3⟩
        by_cases hp3 : p3 = p1
        · exact ⟨p2, l2, p3, l3, hI2, hI3, fun h => hp2 (h.trans hp3), by rw [hl2]; exact Ne.symm hl3, hv2, hv3⟩
        · exact ⟨p1, l1, p3, l3, hI1, hI3, Ne.symm hp3, Ne.symm hl3, hv1, hv3⟩
      · exact ⟨p1, l1, p2, l2, hI1, hI2, Ne.symm hp2, Ne.symm hl2, hv1, hv2⟩
    -- Step 4: Every incident pair is covered by Fstar or Fnon
    let Estar : Finset (Fin N × Fin N) :=
      Finset.univ.filter (fun pl => I pl.1 pl.2 ∧ ∃ w ∈ Fstar, v (pair pl.1 pl.2) w = true)
    let Enon : Finset (Fin N × Fin N) :=
      Finset.univ.filter (fun pl => I pl.1 pl.2 ∧ ∃ w ∈ Fnon, v (pair pl.1 pl.2) w = true)
    have hEsub : Eall ⊆ Estar ∪ Enon := by
      intro pl hpl
      have hIpl : I pl.1 pl.2 := (Finset.mem_filter.mp hpl).2
      rcases hcov pl.1 pl.2 hIpl with ⟨w, hwF, hvw⟩
      by_cases hs : isStar w
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hIpl, w, Finset.mem_filter.mpr ⟨hwF, hs⟩, hvw⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hIpl, w, Finset.mem_filter.mpr ⟨hwF, hs⟩, hvw⟩)
    have hEsum : N * (q + 1) ≤ Estar.card + Enon.card := by
      have h1 := Finset.card_le_card hEsub
      have h2 := Finset.card_union_le Estar Enon
      omega
    have hFstar_le : Fstar.card ≤ F.card := Finset.card_filter_le F isStar
    have hFnon_le : Fnon.card ≤ F.card := Finset.card_filter_le F (fun w => ¬ isStar w)
    by_cases hhalf : N * (q + 1) ≤ 2 * Estar.card
    · apply star_heavy q N I D Fstar hq hN hdeg huniq hmono hshape (by omega)
      · intro w hw
        have hwF := (Finset.mem_filter.mp hw).1
        have hws := (Finset.mem_filter.mp hw).2
        rcases hF w hwF with ⟨h1, h2, h3, h4⟩
        exact ⟨h1, h2, h3, h4, hws⟩
      · exact hhalf
      · intro Y hY w hw
        exact hneg Y hY w (Finset.mem_filter.mp hw).1
    · apply nonstar_heavy q N I D Fnon hq hN hdeg huniq hmono hshape (by omega)
      · intro w hw
        have hwF := (Finset.mem_filter.mp hw).1
        rcases hF w hwF with ⟨h1, h2, h3, _⟩
        exact ⟨h1, h2, h3, hnon_match w hw⟩
      · change N * (q + 1) ≤ 2 * Enon.card
        omega
      · intro Y hY w hw
        exact hneg Y hY w (Finset.mem_filter.mp hw).1
