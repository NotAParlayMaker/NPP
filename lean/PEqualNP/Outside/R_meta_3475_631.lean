import Mathlib.Data.Finset.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_3475_631
    (degree : ∀ (N : ℕ) (E : Finset (Fin N × Fin N)),
      (∀ p r l m, p ≠ r → l ≠ m →
        ¬ ((p,l) ∈ E ∧ (p,m) ∈ E ∧ (r,l) ∈ E ∧ (r,m) ∈ E)) →
      (∀ e ∈ E, 24 < (E.filter fun f => f.1 = e.1).card ∧
        24 < (E.filter fun f => f.2 = e.2).card) →
      E.Nonempty → 601 ≤ (E.image Prod.fst).card ∧ 601 ≤ (E.image Prod.snd).card ∧
        15025 ≤ E.card)
    (support : ∀ (N : ℕ) (C : Circuit) (E : Finset (Fin N × Fin N)),
      PEqualNP.TopForm.IsAO2 (N+N) C →
      (∀ e ∈ E, circuitFun (N+N) C
        (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd N e.1) (Fin.natAdd N e.2)) = true) →
      (∀ w : Fin (N+N), circuitFun (N+N) C (fun i => decide (i = w)) = false) →
      (E.image Prod.fst).card + (E.image Prod.snd).card ≤ 2 * C.size)
    (large : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit) (E : Finset (Fin N × Fin N)),
      87 ≤ q → N = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) → PEqualNP.TopForm.IsAO2 (N+N) C →
      (∀ z, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      let hits := fun (v : Fin (N+N)) (e : Fin N × Fin N) =>
        v = Fin.castAdd N e.1 ∨ v = Fin.natAdd N e.2
      (∀ e ∈ E, I e.1 e.2 ∧ circuitFun (N+N) C (fun i => decide (hits i e)) = true ∧
        PEqualNP.ReadK.lineSingle C (N+N) (fun i => decide (N ≤ i)) e.1.val (N+e.2.val) = false ∧
        PEqualNP.ReadK.lineSingle C (N+N) (fun i => decide (i < N)) e.1.val (N+e.2.val) = false) →
      (∀ e ∈ E, ∀ v, hits v e → 24 < (E.filter (hits v)).card) →
      601 ≤ (E.image Prod.fst).card → 601 ≤ (E.image Prod.snd).card →
      15025 ≤ E.card → 601 ≤ C.size → 24 * C.size < (E.image Prod.snd).card * (q+1) →
      E.card ≤ 24 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x2 × Fin x2)),   (87 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →               let x13 : Fin (x2 + x2) → Fin x2 × Fin x2 → Prop := fun (x13 : Fin (x2 + x2)) (x14 : Fin x2 × Fin x2) => x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2;               (∀ x14 ∈ x6, x3 x14.1 x14.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x13 x16 x14)) = Bool.true ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x2 ≤ x16)) (↑x14.1) (x2 + ↑x14.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x16 : ℕ) => Decidable.decide (x16 < x2)) (↑x14.1) (x2 + ↑x14.2) = Bool.false) → (∀ x15 ∈ x6, ∀ (x17 : Fin (x2 + x2)), x13 x17 x15 → (24 : ℕ) < (Finset.filter (x13 x17) x6).card) → x6.card ≤ (24 : ℕ) * x5.size := by
  intro q N I inst C E hq hN hcol huniq ao sound hits good dense
  classical
  by_cases empty : E = ∅
  · simp [empty]
  let lines := E.image Prod.snd
  have edgeBound : E.card ≤ lines.card * (q+1) := by
    let row (l : Fin N) :=
      (Finset.univ.filter fun p : Fin N => I p l).image (fun p => (p,l))
    have covered : E ⊆ lines.biUnion row := by
      intro e he
      refine Finset.mem_biUnion.mpr ⟨e.2, Finset.mem_image_of_mem Prod.snd he, ?_⟩
      exact Finset.mem_image.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (good e he).1⟩, rfl⟩
    calc
      E.card ≤ ∑ l ∈ lines, (row l).card :=
        (Finset.card_le_card covered).trans Finset.card_biUnion_le
      _ ≤ ∑ _l ∈ lines, (q+1) := by
        apply Finset.sum_le_sum
        intro l _
        exact (Finset.card_image_le (s := Finset.univ.filter fun p : Fin N => I p l)).trans_eq
          (by simpa only [Fintype.card_subtype] using hcol l)
      _ = lines.card * (q+1) := by simp
  by_cases largeSize : lines.card * (q+1) ≤ 24 * C.size
  · exact edgeBound.trans largeSize
  have separate (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h
    have := p.isLt
    omega
  have leftEq (p r : Fin N) (e : Fin.castAdd N p = Fin.castAdd N r) : p = r := by
    have vals := congrArg (fun i : Fin (N+N) => i.val) e
    exact Fin.ext vals
  have rightEq (l m : Fin N) (e : Fin.natAdd N l = Fin.natAdd N m) : l = m :=
    Fin.ext (Nat.add_left_cancel (congrArg Fin.val e))
  have pointHit (e f : Fin N × Fin N) : hits (Fin.castAdd N e.1) f ↔ f.1 = e.1 := by
    constructor
    · intro h
      rcases h with h | h
      · exact (leftEq _ _ h).symm
      · exact (separate _ _ h).elim
    · intro h
      exact Or.inl (congrArg (Fin.castAdd N) h.symm)
  have lineHit (e f : Fin N × Fin N) : hits (Fin.natAdd N e.2) f ↔ f.2 = e.2 := by
    constructor
    · intro h
      rcases h with h | h
      · exact (separate _ _ h.symm).elim
      · exact (rightEq _ _ h).symm
    · intro h
      exact Or.inr (congrArg (Fin.natAdd N) h.symm)
  have four : ∀ p r l m : Fin N, p ≠ r → l ≠ m →
      ¬ ((p,l) ∈ E ∧ (p,m) ∈ E ∧ (r,l) ∈ E ∧ (r,m) ∈ E) := by
    intro p r l m different separateLines h
    obtain ⟨t, _, unique⟩ := huniq p r different
    have hi (a b : Fin N) (h : (a,b) ∈ E) : I a b := (good (a,b) h).1
    exact separateLines ((unique l ⟨hi _ _ h.1, hi _ _ h.2.2.1⟩).trans
      (unique m ⟨hi _ _ h.2.1, hi _ _ h.2.2.2⟩).symm)
  have each (e : Fin N × Fin N) (he : e ∈ E) :
      24 < (E.filter fun f => f.1 = e.1).card ∧ 24 < (E.filter fun f => f.2 = e.2).card := by
    exact ⟨by simpa only [pointHit] using dense e he _ (Or.inl rfl),
      by simpa only [lineHit] using dense e he _ (Or.inr rfl)⟩
  obtain ⟨pc, lc, ec⟩ := degree N E four each (Finset.nonempty_iff_ne_empty.mpr empty)
  have singletonOff (w : Fin (N+N)) : circuitFun (N+N) C (fun i => decide (i = w)) = false := by
    apply sound
    · rw [Fintype.card_subtype]
      apply Nat.le_trans (Finset.card_le_one.mpr ?_) (by omega)
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hb
      exact rightEq _ _ (ha.trans hb.symm)
    · rintro ⟨p, l, _, hp, hl⟩
      exact separate p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  have accepted (e : Fin N × Fin N) (he : e ∈ E) :
      circuitFun (N+N) C (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd N e.1) (Fin.natAdd N e.2)) = true :=
    (good e he).2.1
  have reads := support N C E ao accepted singletonOff
  have largeCircuit : 601 ≤ C.size := by omega
  exact large q N I C E hq hN hcol huniq ao sound good dense pc lc ec largeCircuit
    (Nat.lt_of_not_ge largeSize)
