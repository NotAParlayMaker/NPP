import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_1721

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped BigOperators

abbrev ReferenceSetBound : Prop :=
  ∀ (n m k : ℕ) (U S : Fin m → Finset (Fin n)) (C : Circuit)
      (o c : Fin m → ℕ),
    (∀ i j : Fin m, i ≠ j → (U i ∩ U j).card ≤ 1) →
    (∀ i : Fin m, S i ⊆ U i) →
    (∀ i : Fin m, 2 ≤ (S i).card) →
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length = 2) →
    NestedCover.ReadsBack n C →
    (∀ (i : Fin m) (p : Fin n),
      (C.wires (List.ofFn (fun a : Fin n => decide (a = p)))).getD (o i) false = true ↔
        p ∈ S i) →
    (∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun b : Fin n => x b = true)).card ≤ k →
      (∀ b ∈ U i, x b = false) →
      (C.wires (List.ofFn x)).getD (o i) false = false) →
    (∀ i : Fin m, c i ≤ k) →
    (∀ i : Fin m, c i + 1 ≤ (S i).card) →
    ∑ i : Fin m, c i ≤ C.size

lemma reference_all_cards (hRef : ReferenceSetBound)
    {n m k : ℕ} (U S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (hU : ∀ i j : Fin m, i ≠ j → (U i ∩ U j).card ≤ 1)
    (hS : ∀ i : Fin m, S i ⊆ U i)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length = 2)
    (hBack : NestedCover.ReadsBack n C)
    (hSingleton : ∀ (i : Fin m) (p : Fin n),
      (C.wires (List.ofFn (fun a : Fin n => decide (a = p)))).getD (o i) false = true ↔
        p ∈ S i)
    (hSound : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun b : Fin n => x b = true)).card ≤ k →
      (∀ b ∈ U i, x b = false) →
      (C.wires (List.ofFn x)).getD (o i) false = false) :
    ∑ i : Fin m, min k ((S i).card - 1) ≤ C.size := by
  classical
  let A : Set (Fin m) := {i | 2 ≤ (S i).card}
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let f : Fin (Fintype.card A) → Fin m := fun j => (e.symm j).val
  have hf : Function.Injective f := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  have hlarge : ∀ j : Fin (Fintype.card A), 2 ≤ (S (f j)).card := by
    intro j
    exact (e.symm j).property
  have hbound :
      (∑ j : Fin (Fintype.card A), min k ((S (f j)).card - 1)) ≤ C.size := by
    apply hRef n (Fintype.card A) k (fun j => U (f j)) (fun j => S (f j)) C
      (fun j => o (f j)) (fun j => min k ((S (f j)).card - 1))
    · intro i j hij
      exact hU (f i) (f j) (fun h => hij (hf h))
    · intro j
      exact hS (f j)
    · exact hlarge
    · exact hG
    · exact hBack
    · intro j p
      exact hSingleton (f j) p
    · intro j x hx hz
      exact hSound (f j) x hx hz
    · intro j
      exact min_le_left _ _
    · intro j
      have hc := min_le_right k ((S (f j)).card - 1)
      have hs := hlarge j
      omega
  calc
    (∑ i : Fin m, min k ((S i).card - 1)) =
        ∑ i : A, min k ((S i.val).card - 1) := by
      apply Finset.sum_congr_set A
        (fun i : Fin m => min k ((S i).card - 1))
        (fun i : A => min k ((S i.val).card - 1))
      · intro i hi
        rfl
      · intro i hi
        have hsmall : (S i).card ≤ 1 := by
          change ¬ 2 ≤ (S i).card at hi
          omega
        simp [Nat.sub_eq_zero_of_le hsmall]
    _ = ∑ j : Fin (Fintype.card A), min k ((S (f j)).card - 1) := by
      exact (e.symm.sum_comp (fun i : A => min k ((S i.val).card - 1))).symm
    _ ≤ C.size := hbound

lemma min_cost_pointwise (q k a : ℕ) (ha : a ≤ q + 1) :
    min k q * a ≤ q * min k (a - 1) + min k q := by
  by_cases hka : k ≤ a - 1
  · rw [min_eq_left hka]
    calc
      min k q * a ≤ min k q * (q + 1) := Nat.mul_le_mul_left _ ha
      _ = q * min k q + min k q := by ring
      _ ≤ q * k + min k q :=
        Nat.add_le_add_right (Nat.mul_le_mul_left q (min_le_left k q)) _
  · have hak : a - 1 ≤ k := by omega
    rw [min_eq_right hak]
    by_cases hz : a = 0
    · simp [hz]
    · have hpos : 1 ≤ a := by omega
      calc
        min k q * a = min k q * ((a - 1) + 1) :=
          congrArg (fun b => min k q * b) (Nat.sub_add_cancel hpos).symm
        _ = min k q * (a - 1) + min k q := by ring
        _ ≤ q * (a - 1) + min k q :=
          Nat.add_le_add_right (Nat.mul_le_mul_right (a - 1) (min_le_right k q)) _

end PEqualNP.Outside.L_meta_1721


namespace PEqualNP.Outside.L_meta_1721

theorem geom_line_inter_card_le_one {N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hpair : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (l l' : Fin N) (hne : l ≠ l') :
    ((Finset.univ.filter (fun p => I p l)) ∩
      (Finset.univ.filter (fun p => I p l'))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra hab
  obtain ⟨u, hu, huniq⟩ := hpair a b hab
  have hal := (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2
  have hal' := (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2
  have hbl := (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).2
  have hbl' := (Finset.mem_filter.mp (Finset.mem_inter.mp hb).2).2
  exact hne ((huniq l ⟨hal, hbl⟩).trans (huniq l' ⟨hal', hbl'⟩).symm)

theorem geom_point_inter_card_le_one {N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hpair : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (p p' : Fin N) (hne : p ≠ p') :
    ((Finset.univ.filter (fun l => I p l)) ∩
      (Finset.univ.filter (fun l => I p' l))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro l hl l' hl'
  obtain ⟨u, hu, huniq⟩ := hpair p p' hne
  have hpl := (Finset.mem_filter.mp (Finset.mem_inter.mp hl).1).2
  have hp'l := (Finset.mem_filter.mp (Finset.mem_inter.mp hl).2).2
  have hpl' := (Finset.mem_filter.mp (Finset.mem_inter.mp hl').1).2
  have hp'l' := (Finset.mem_filter.mp (Finset.mem_inter.mp hl').2).2
  exact (huniq l ⟨hpl, hp'l⟩).trans (huniq l' ⟨hpl', hp'l'⟩).symm

theorem geom_point_degree {q N : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpair : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (p : Fin N) : (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  classical
  let R : Finset (Fin N) := Finset.univ.filter (fun l => I p l)
  let A : Fin N → Finset (Fin N) :=
    fun l => (Finset.univ.filter (fun a => I a l)).erase p
  have hc : ∀ l ∈ R, (A l).card = q := by
    intro l hl
    have hpl : I p l := (Finset.mem_filter.mp hl).2
    change ((Finset.univ.filter (fun a => I a l)).erase p).card = q
    rw [Finset.card_erase_of_mem (by simpa using hpl), hline]
    omega
  have hd : (R : Set (Fin N)).PairwiseDisjoint A := by
    intro l hl l' hl' hne
    apply Finset.disjoint_left.mpr
    intro a ha ha'
    have hpl : I p l := (Finset.mem_filter.mp hl).2
    have hpl' : I p l' := (Finset.mem_filter.mp hl').2
    have hap : a ≠ p := (Finset.mem_erase.mp ha).1
    have hal : I a l := (Finset.mem_filter.mp (Finset.mem_erase.mp ha).2).2
    have hal' : I a l' := (Finset.mem_filter.mp (Finset.mem_erase.mp ha').2).2
    obtain ⟨u, hu, huniq⟩ := hpair a p hap
    exact hne ((huniq l ⟨hal, hpl⟩).trans (huniq l' ⟨hal', hpl'⟩).symm)
  have hu : R.biUnion A = Finset.univ.erase p := by
    ext a
    constructor
    · intro ha
      obtain ⟨l, hl, hal⟩ := Finset.mem_biUnion.mp ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hal).1, Finset.mem_univ a⟩
    · intro ha
      have hap : a ≠ p := (Finset.mem_erase.mp ha).1
      obtain ⟨l, hl, huniq⟩ := hpair p a hap.symm
      apply Finset.mem_biUnion.mpr
      refine ⟨l, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl.1⟩
      · exact Finset.mem_erase.mpr
          ⟨hap, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hl.2⟩⟩
  have hcard : (Finset.univ.erase p : Finset (Fin N)).card = R.card * q := by
    rw [← hu, Finset.card_biUnion hd]
    exact Finset.sum_const_nat hc
  have htotal : (Finset.univ.erase p : Finset (Fin N)).card + 1 = N := by
    simpa using (Finset.card_erase_add_one
      (s := (Finset.univ : Finset (Fin N))) (a := p) (Finset.mem_univ p))
  rw [hcard] at htotal
  change R.card = q + 1
  apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < q)
  nlinarith

end PEqualNP.Outside.L_meta_1721


namespace PEqualNP.Outside.L_meta_1721

lemma sum_incidence_covered {n m : ℕ}
    (I : Fin n → Fin m → Prop) [DecidableRel I]
    (S : Fin m → Finset (Fin n)) (T : Fin n → Finset (Fin m))
    (hcover : ∀ p l, I p l → p ∈ S l ∨ l ∈ T p) :
    (∑ l : Fin m, (Finset.univ.filter (fun p => I p l)).card) ≤
      (∑ l : Fin m, (S l).card) + (∑ p : Fin n, (T p).card) := by
  classical
  have hpoint (l : Fin m) :
      (Finset.univ.filter (fun p => I p l)).card ≤
        (S l).card + (Finset.univ.filter (fun p => l ∈ T p)).card := by
    calc
      (Finset.univ.filter (fun p => I p l)).card ≤
          (S l ∪ Finset.univ.filter (fun p => l ∈ T p)).card := by
        apply Finset.card_le_card
        intro p hp
        have hi : I p l := (Finset.mem_filter.mp hp).2
        rcases hcover p l hi with hs | ht
        · exact Finset.mem_union_left _ hs
        · exact Finset.mem_union_right _ (by simp [ht])
      _ ≤ (S l).card + (Finset.univ.filter (fun p => l ∈ T p)).card :=
        Finset.card_union_le _ _
  have hsum := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin m))) =>
    hpoint l)
  rw [Finset.sum_add_distrib] at hsum
  have htranspose :
      (∑ l : Fin m, (Finset.univ.filter (fun p : Fin n => l ∈ T p)).card) =
        ∑ p : Fin n, (T p).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [← Finset.card_filter]
    congr 1
    ext l
    simp
  rwa [htranspose] at hsum

lemma finish_count (N q k a b sx sy size : ℕ)
    (hinc : N * (q + 1) ≤ a + b)
    (hx : min k q * a ≤ q * sx + N * min k q)
    (hy : min k q * b ≤ q * sy + N * min k q)
    (hsizes : sx + sy ≤ 5 * size) :
    N * q * min k q ≤ 5 * q * size + N * min k q := by
  nlinarith [Nat.mul_le_mul_left (min k q) hinc,
    Nat.mul_le_mul_left q hsizes]

end PEqualNP.Outside.L_meta_1721

open PEqualNP.Outside.L_meta_1721

theorem PEqualNP.Outside.L_meta_1721 : (∀ (n1 m1 k1 : ℕ) (U1 S1 : Fin m1 → Finset (Fin n1)) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (o1 c1 : Fin m1 → ℕ), (∀ i1 j1 : Fin m1, i1 ≠ j1 → (U1 i1 ∩ U1 j1).card ≤ 1) → (∀ i1a : Fin m1, S1 i1a ⊆ U1 i1a) → (∀ i1b : Fin m1, 2 ≤ (S1 i1b).card) → (∀ g1 ∈ C1.gates, (g1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g1.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack n1 C1 → (∀ (i1c : Fin m1) (p1 : Fin n1), (C1.wires (List.ofFn (fun a1 : Fin n1 => decide (a1 = p1)))).getD (o1 i1c) false = true ↔ p1 ∈ S1 i1c) → (∀ (i1d : Fin m1) (x1 : Fin n1 → Bool), (Finset.univ.filter (fun b1 : Fin n1 => x1 b1 = true)).card ≤ k1 → (∀ b1a ∈ U1 i1d, x1 b1a = false) → (C1.wires (List.ofFn x1)).getD (o1 i1d) false = false) → (∀ i1e : Fin m1, c1 i1e ≤ k1) → (∀ i1f : Fin m1, c1 i1f + 1 ≤ (S1 i1f).card) → ∑ i1g : Fin m1, c1 i1g ≤ C1.size) → (∀ (q20 N20 k20 : ℕ) (I20 : Fin N20 → Fin N20 → Prop) [DecidableRel I20] (C20 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q20 → N20 = q20 ^ 2 + q20 + 1 → (∀ l20c : Fin N20, (Finset.univ.filter (fun p20f => I20 p20f l20c)).card = q20 + 1) → (∀ pa20 pb20 : Fin N20, pa20 ≠ pb20 → ∃! lb20 : Fin N20, I20 pa20 lb20 ∧ I20 pb20 lb20) → 1 ≤ k20 → (∀ g20 ∈ C20.gates, (g20.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N20 + N20) C20 → (∀ j20 < C20.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.Ico N20 (N20 + N20))).getD i20 0 = 0) ∨ (∀ h20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.range N20)).getD h20 0 = 0)) → (∀ p20g l20d : Fin N20, I20 p20g l20d → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 (fun i20a => decide (i20a = Fin.castAdd N20 p20g ∨ i20a = Fin.natAdd N20 l20d)) = true) → (∀ z20 : Fin (N20 + N20) → Bool, (Finset.univ.filter (fun l20e : Fin N20 => z20 (Fin.natAdd N20 l20e) = true)).card ≤ k20 → (¬ ∃ p20h l20f : Fin N20, I20 p20h l20f ∧ z20 (Fin.castAdd N20 p20h) = true ∧ z20 (Fin.natAdd N20 l20f) = true) → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 z20 = false) → ∃ (X20 Y20 : PEqualNP.CircuitLowerBounds.Circuit) (ps20 rh20 : Fin N20 → ℕ), ((∀ g20a ∈ X20.gates, (g20a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 X20) ∧ ((∀ g20b ∈ Y20.gates, (g20b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 Y20) ∧ X20.size + Y20.size ≤ 5 * C20.size ∧ (∀ w20 p20 : Fin N20, (X20.wires (List.ofFn (fun a20 => decide (a20 = p20)))).getD (ps20 w20) false = true → I20 p20 w20) ∧ (∀ (w20a : Fin N20) (x20 : Fin N20 → Bool), (∀ p20a : Fin N20, I20 p20a w20a → x20 p20a = false) → (X20.wires (List.ofFn x20)).getD (ps20 w20a) false = false) ∧ (∀ p20b l20 : Fin N20, (Y20.wires (List.ofFn (fun a20a => decide (a20a = l20)))).getD (rh20 p20b) false = true → I20 p20b l20) ∧ (∀ (p20c : Fin N20) (y20 : Fin N20 → Bool), (Finset.univ.filter (fun l20a : Fin N20 => y20 l20a = true)).card ≤ k20 → (∀ l20b : Fin N20, I20 p20c l20b → y20 l20b = false) → (Y20.wires (List.ofFn y20)).getD (rh20 p20c) false = false) ∧ (∀ p20d w20b : Fin N20, I20 p20d w20b → (X20.wires (List.ofFn (fun a20b => decide (a20b = p20d)))).getD (ps20 w20b) false = true ∨ (Y20.wires (List.ofFn (fun a20c => decide (a20c = w20b)))).getD (rh20 p20d) false = true)) → ∀ (q3 N3 k3 : ℕ) (I3 : Fin N3 → Fin N3 → Prop) [DecidableRel I3] (C3 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q3 → N3 = q3 ^ 2 + q3 + 1 → (∀ l3 : Fin N3, (Finset.univ.filter (fun p3 => I3 p3 l3)).card = q3 + 1) → (∀ pa3 pb3 : Fin N3, pa3 ≠ pb3 → ∃! lb3 : Fin N3, I3 pa3 lb3 ∧ I3 pb3 lb3) → (∀ g3 ∈ C3.gates, (g3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g3.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N3 + N3) C3 → (∀ j3 < C3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C3 j3).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C3 j3).inputs, (C3.lineDegrees (N3 + N3) (Finset.Ico N3 (N3 + N3))).getD i3 0 = 0) ∨ (∀ h3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C3 j3).inputs, (C3.lineDegrees (N3 + N3) (Finset.range N3)).getD h3 0 = 0)) → (∀ p3a l3a : Fin N3, I3 p3a l3a → PEqualNP.MetaComplexity.circuitFun (N3 + N3) C3 (fun i3a => decide (i3a = Fin.castAdd N3 p3a ∨ i3a = Fin.natAdd N3 l3a)) = true) → (∀ z3 : Fin (N3 + N3) → Bool, (Finset.univ.filter (fun l3b : Fin N3 => z3 (Fin.natAdd N3 l3b) = true)).card ≤ k3 → (¬ ∃ p3b l3c : Fin N3, I3 p3b l3c ∧ z3 (Fin.castAdd N3 p3b) = true ∧ z3 (Fin.natAdd N3 l3c) = true) → PEqualNP.MetaComplexity.circuitFun (N3 + N3) C3 z3 = false) → N3 * q3 * min k3 q3 ≤ 5 * q3 * C3.size + N3 * min k3 q3 := by
  classical
  intro hRef hSplit q N k I _ C hq hN hline hpair hmono hback hKM haccept hsound
  by_cases hk : k = 0
  · simp [hk]
  have hkpos : 1 ≤ k := by omega
  obtain ⟨X, Y, ps, rh, ⟨hXm, hXb⟩, ⟨hYm, hYb⟩, hsizes,
    hXsingle, hXsound, hYsingle, hYsound, hcover⟩ :=
    hSplit q N k I C hq hN hline hpair hkpos hmono hback hKM haccept hsound
  let U : Fin N → Finset (Fin N) := fun l =>
    Finset.univ.filter (fun p => I p l)
  let V : Fin N → Finset (Fin N) := fun p =>
    Finset.univ.filter (fun l => I p l)
  let S : Fin N → Finset (Fin N) := fun l =>
    Finset.univ.filter (fun p =>
      (X.wires (List.ofFn (fun a : Fin N => decide (a = p)))).getD (ps l) false = true)
  let T : Fin N → Finset (Fin N) := fun p =>
    Finset.univ.filter (fun l =>
      (Y.wires (List.ofFn (fun a : Fin N => decide (a = l)))).getD (rh p) false = true)
  have hU : ∀ i j : Fin N, i ≠ j → (U i ∩ U j).card ≤ 1 := by
    intro i j hij
    exact geom_line_inter_card_le_one I hpair i j hij
  have hV : ∀ i j : Fin N, i ≠ j → (V i ∩ V j).card ≤ 1 := by
    intro i j hij
    exact geom_point_inter_card_le_one I hpair i j hij
  have hSU : ∀ i : Fin N, S i ⊆ U i := by
    intro i p hp
    have hs := hXsingle i p (by simpa [S] using hp)
    simpa [U] using hs
  have hTV : ∀ i : Fin N, T i ⊆ V i := by
    intro i l hl
    have ht := hYsingle i l (by simpa [T] using hl)
    simpa [V] using ht
  have hScard : ∀ i : Fin N, (S i).card ≤ q + 1 := by
    intro i
    calc
      (S i).card ≤ (U i).card := Finset.card_le_card (hSU i)
      _ = q + 1 := hline i
  have hTcard : ∀ i : Fin N, (T i).card ≤ q + 1 := by
    intro i
    calc
      (T i).card ≤ (V i).card := Finset.card_le_card (hTV i)
      _ = q + 1 := geom_point_degree I hq hN hline hpair i
  have hXcost : (∑ i : Fin N, min k ((S i).card - 1)) ≤ X.size := by
    apply reference_all_cards hRef (k := k) U S X ps hU hSU hXm hXb
    · intro i p
      simp [S]
    · intro i x _ hz
      apply hXsound i x
      intro p hp
      exact hz p (by simpa [U] using hp)
  have hYcost : (∑ i : Fin N, min k ((T i).card - 1)) ≤ Y.size := by
    apply reference_all_cards hRef (k := k) V T Y rh hV hTV hYm hYb
    · intro i l
      simp [T]
    · intro i x hx hz
      apply hYsound i x hx
      intro l hl
      exact hz l (by simpa [V] using hl)
  have hcovered : N * (q + 1) ≤
      (∑ i : Fin N, (S i).card) + (∑ i : Fin N, (T i).card) := by
    have h := sum_incidence_covered I S T (by
      intro p l hp
      rcases hcover p l hp with hs | ht
      · exact Or.inl (by simpa [S] using hs)
      · exact Or.inr (by simpa [T] using ht))
    simpa only [hline, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul] using h
  have hweighted (a : Fin N → ℕ) (s : ℕ)
      (ha : ∀ i : Fin N, a i ≤ q + 1)
      (hcost : (∑ i : Fin N, min k (a i - 1)) ≤ s) :
      min k q * (∑ i : Fin N, a i) ≤ q * s + N * min k q := by
    calc
      min k q * (∑ i : Fin N, a i) =
          ∑ i : Fin N, min k q * a i := Finset.mul_sum _ _ _
      _ ≤ ∑ i : Fin N, (q * min k (a i - 1) + min k q) := by
        apply Finset.sum_le_sum
        intro i _
        exact min_cost_pointwise q k (a i) (ha i)
      _ = q * (∑ i : Fin N, min k (a i - 1)) + N * min k q := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
      _ ≤ q * s + N * min k q :=
        Nat.add_le_add_right (Nat.mul_le_mul_left q hcost) _
  exact finish_count N q k (∑ i : Fin N, (S i).card)
    (∑ i : Fin N, (T i).card) X.size Y.size C.size hcovered
    (hweighted (fun i => (S i).card) X.size hScard hXcost)
    (hweighted (fun i => (T i).card) Y.size hTcard hYcost) hsizes
