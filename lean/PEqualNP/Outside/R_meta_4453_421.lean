import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Apply the sparse-shore estimate from PR #5770 (Devin) independently to vertex-disjoint blocks.
The partition may have multiple components when both global shores are large. -/
theorem PEqualNP.Outside.R_meta_4453_421
    (blocks : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (F : Finset (Finset (Fin n × Fin n))),
      (∀ p r l m : Fin n, p ≠ r → l ≠ m →
        ¬ ((p,l) ∈ E ∧ (r,l) ∈ E ∧ (p,m) ∈ E ∧ (r,m) ∈ E)) →
      F.biUnion id = E →
      (∀ H ∈ F, H.Nonempty ∧ min (H.image Prod.fst).card (H.image Prod.snd).card ≤ 7656) →
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B →
        Disjoint (A.image Prod.fst) (B.image Prod.fst) ∧
        Disjoint (A.image Prod.snd) (B.image Prod.snd)) →
      E.card ≤ 44 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1))
    (support : ∀ (n : ℕ) (C : Circuit) (S : Finset (Fin n)), PEqualNP.TopForm.IsAO2 n C →
      (∀ i ∈ S, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
        circuitFun n C x ≠ circuitFun n C y) → S.card ≤ C.size+1)
    (remaining : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I] (C : Circuit),
      131 ≤ q → n = q ^ 2 + q + 1 →
      (∀ l : Fin n, Fintype.card {p : Fin n // I p l} = q + 1) →
      (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, I p l ∧ I r l) →
      PEqualNP.TopForm.IsAO2 (n+n) C →
      (∀ x : Fin (n+n) → Bool, Fintype.card {l : Fin n // x (Fin.natAdd n l) = true} ≤ q →
        (¬∃ p l : Fin n, I p l ∧ x (Fin.castAdd n p) = true ∧ x (Fin.natAdd n l) = true) →
        circuitFun (n+n) C x = false) →
      let E : Finset (Fin n × Fin n) := Finset.univ.filter (fun e =>
        I e.1 e.2 ∧ circuitFun (n+n) C
          (fun i => decide (i = Fin.castAdd n e.1 ∨ i = Fin.natAdd n e.2)) = true)
      (∀ v : Fin (n+n), let d := (E.filter (fun e =>
        v = Fin.castAdd n e.1 ∨ v = Fin.natAdd n e.2)).card
        d = 0 ∨ 44 < d) →
      (¬ ∃ F : Finset (Finset (Fin n × Fin n)), F.biUnion id = E ∧
        (∀ H ∈ F, H.Nonempty ∧ min (H.image Prod.fst).card (H.image Prod.snd).card ≤ 7656) ∧
        (∀ A ∈ F, ∀ B ∈ F, A ≠ B →
          Disjoint (A.image Prod.fst) (B.image Prod.fst) ∧
          Disjoint (A.image Prod.snd) (B.image Prod.snd))) →
      E.card ≤ 44 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (131 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x5 →             (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →               have x12 : Finset (Fin x2 × Fin x2) := {x12 : Fin x2 × Fin x2 | x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true};               (∀ (x13 : Fin (x2 + x2)),                   have x14 : ℕ := {x14 ∈ x12 | x13 = Fin.castAdd x2 x14.1 ∨ x13 = Fin.natAdd x2 x14.2}.card;                   x14 = (0 : ℕ) ∨ (44 : ℕ) < x14) →                 x12.card ≤ (44 : ℕ) * x5.size := by
  classical
  intro q n I _ C hq hn hLine hPairs hAO hSound
  dsimp only
  intro hDegree
  let pair (p l : Fin n) : Fin (n+n) → Bool :=
    fun i => decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)
  let single (v : Fin (n+n)) : Fin (n+n) → Bool := fun i => decide (i = v)
  let E : Finset (Fin n × Fin n) := Finset.univ.filter (fun e =>
    I e.1 e.2 ∧ circuitFun (n+n) C (pair e.1 e.2) = true)
  change E.card ≤ 44 * C.size
  let partition := ∃ F : Finset (Finset (Fin n × Fin n)), F.biUnion id = E ∧
    (∀ H ∈ F, H.Nonempty ∧ min (H.image Prod.fst).card (H.image Prod.snd).card ≤ 7656) ∧
    (∀ A ∈ F, ∀ B ∈ F, A ≠ B →
          Disjoint (A.image Prod.fst) (B.image Prod.fst) ∧
          Disjoint (A.image Prod.snd) (B.image Prod.snd))
  by_cases hPart : partition
  · obtain ⟨F, hUnion, hThin, hSides⟩ := hPart
    have edgeInfo {p l : Fin n} (h : (p,l) ∈ E) :
        I p l ∧ circuitFun (n+n) C (pair p l) = true := (Finset.mem_filter.mp h).2
    have free : ∀ p r l m : Fin n, p ≠ r → l ≠ m →
        ¬ ((p,l) ∈ E ∧ (r,l) ∈ E ∧ (p,m) ∈ E ∧ (r,m) ∈ E) := by
      intro p r l m hpr hlm fourEdges
      have a := fourEdges.1
      have b := fourEdges.2.1
      have c := fourEdges.2.2.1
      have d := fourEdges.2.2.2
      obtain ⟨k, _, hu⟩ := hPairs p r hpr
      exact hlm ((hu l ⟨(edgeInfo a).1, (edgeInfo b).1⟩).trans
        (hu m ⟨(edgeInfo c).1, (edgeInfo d).1⟩).symm)
    have hCharge := blocks n E F free hUnion hThin hSides
    have hSingle (v : Fin (n+n)) : circuitFun (n+n) C (single v) = false := by
      have hx (j : Fin (n+n)) (h : single v j = true) : j = v := of_decide_eq_true h
      have hsub : Subsingleton {l : Fin n // single v (Fin.natAdd n l) = true} := by
        constructor
        intro l k
        apply Subtype.ext
        apply Fin.ext
        have hv := congrArg Fin.val ((hx _ l.property).trans (hx _ k.property).symm)
        simp only [Fin.val_natAdd] at hv
        omega
      apply hSound _ (le_trans (Fintype.card_le_one_iff_subsingleton.mpr hsub) (by omega))
      rintro ⟨p,l,_,hp,hl⟩
      have hv := congrArg Fin.val ((hx _ hp).trans (hx _ hl).symm)
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    let P := (E.image Prod.fst).image (Fin.castAdd n)
    let L := (E.image Prod.snd).image (Fin.natAdd n)
    have hDisj : Disjoint P L := by
      apply Finset.disjoint_left.mpr
      intro v hp hl
      obtain ⟨p, _, he⟩ := Finset.mem_image.mp hp
      obtain ⟨l, _, hf⟩ := Finset.mem_image.mp hl
      have hv := congrArg Fin.val (he.trans hf.symm)
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
      omega
    have hPI : Function.Injective (Fin.castAdd n : Fin n → Fin (n+n)) := by
      intro a b h
      exact Fin.ext (congrArg (fun v : Fin (n+n) => v.val) h)
    have hLI : Function.Injective (Fin.natAdd n : Fin n → Fin (n+n)) := by
      intro a b h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      omega
    have pinCount : (P ∪ L).card = (E.image Prod.fst).card + (E.image Prod.snd).card := by
      rw [Finset.card_union_of_disjoint hDisj]
      unfold P L
      rw [Finset.card_image_of_injective _ hPI, Finset.card_image_of_injective _ hLI]
    have hPins := support (n+n) C (P ∪ L) hAO (by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨⟨r,l⟩, he, hr⟩ := Finset.mem_image.mp hp
        change r = p at hr
        subst r
        refine ⟨pair p l, single (Fin.natAdd n l), ?_, ?_⟩
        · intro j hj
          simp only [pair, single, hj, false_or, or_false]
        · rw [(edgeInfo he).2,hSingle]
          decide
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨⟨p,r⟩, he, hr⟩ := Finset.mem_image.mp hl
        change r = l at hr
        subst r
        refine ⟨pair p l, single (Fin.castAdd n p), ?_, ?_⟩
        · intro j hj
          simp only [pair, single, hj, false_or, or_false]
        · rw [(edgeInfo he).2,hSingle]
          decide)
    rw [pinCount] at hPins
    omega
  · exact remaining q n I C hq hn hLine hPairs hAO hSound hDegree hPart
