import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 2200 in
set_option maxHeartbeats 2200000 in
theorem PEqualNP.Outside.R_meta_4578_421
    (relabel : ∀ (n : ℕ) (π : Equiv.Perm (Fin n)) (C : Circuit), Monotone2 C →
      ∃ D : Circuit, D.size = C.size ∧ Monotone2 D ∧
        (∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C (x ∘ π)) ∧
        ∀ S T : Finset ℕ, (∀ i : Fin n, (π i).val ∈ S ↔ i.val ∈ T) →
          D.lineDeg n S = C.lineDeg n T)
    (residual : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset (Fin (13 : ℕ))) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x5 : Fin (26 : ℕ)) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x4)) x5; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x3 x4 : Finset (Fin (13 : ℕ))) => ∃ x5 ∈ x3, ∃ x6 ∈ x4, x1 x5 x6; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 → x2 x4 {x6} {x7} = Bool.true) → (∀ (x7 x8 : Finset (Fin (13 : ℕ))), x2 x4 x7 x8 = Bool.true → x3 x7 x8) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x4 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x4 (1 : ℕ) → x4.lineDeg (26 : ℕ) (Finset.range (13 : ℕ)) ≤ x4.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (64 : ℕ) ≤ x4.size) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Finset (Fin (13 : ℕ))) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x5 : Fin (26 : ℕ)) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x4)) x5; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x3 x4 : Finset (Fin (13 : ℕ))) => ∃ x5 ∈ x3, ∃ x6 ∈ x4, x1 x5 x6; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 → x2 x4 {x6} {x7} = Bool.true) → (∀ (x7 x8 : Finset (Fin (13 : ℕ))), x2 x4 x7 x8 = Bool.true → x3 x7 x8) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x4 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x4 (1 : ℕ) → (64 : ℕ) ≤ x4.size := by
  intro inc eval ok C hC hpos hneg hP hL
  have incFlip : ∀ p l : Fin 13, inc p l ↔ inc (-l) (-p) := by
    change ∀ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ↔
      (-l = -p ∨ -l = -p + 1 ∨ -l = -p + 3 ∨ -l = -p + 9)
    decide
  let swap (i : Fin 26) : Fin 26 := Fin.addCases (fun (p : Fin 13) => Fin.natAdd 13 (-p)) (fun (l : Fin 13) => Fin.castAdd 13 (-l)) i
  have invol : Function.Involutive swap := by
    intro i
    refine Fin.addCases (m := 13) (n := 13) (motive := fun i => swap (swap i) = i) ?_ ?_ i
    · intro p
      simp only [swap, Fin.addCases_left, Fin.addCases_right, neg_neg]
    · intro l
      simp only [swap, Fin.addCases_right, Fin.addCases_left, neg_neg]
  let perm : Equiv.Perm (Fin 26) := ⟨swap, swap, invol, invol⟩
  have markP : ∀ i : Fin 26, (perm i).val ∈ Finset.range 13 ↔ i.val ∈ Finset.Ico 13 26 := by
    change ∀ i : Fin 26, (Fin.addCases (motive := fun _ => Fin 26)
      (fun (p : Fin 13) => Fin.natAdd 13 (-p)) (fun (l : Fin 13) => Fin.castAdd 13 (-l)) i).val ∈
      Finset.range 13 ↔ i.val ∈ Finset.Ico 13 26
    decide
  have markL : ∀ i : Fin 26, (perm i).val ∈ Finset.Ico 13 26 ↔ i.val ∈ Finset.range 13 := by
    change ∀ i : Fin 26, (Fin.addCases (motive := fun _ => Fin 26)
      (fun (p : Fin 13) => Fin.natAdd 13 (-p)) (fun (l : Fin 13) => Fin.castAdd 13 (-l)) i).val ∈
      Finset.Ico 13 26 ↔ i.val ∈ Finset.range 13
    decide
  by_cases order : C.lineDeg 26 (Finset.range 13) ≤ C.lineDeg 26 (Finset.Ico 13 26)
  · exact residual C hC hpos hneg hP hL order
  · obtain ⟨D, sizeD, hD, funD, degreesD⟩ := relabel 26 perm C hC
    let flip (S : Finset (Fin 13)) : Finset (Fin 13) := Finset.univ.filter fun a => -a ∈ S
    have flipMem (S : Finset (Fin 13)) (a : Fin 13) : a ∈ flip S ↔ -a ∈ S := by
      simp [flip]
    have flipSingleton (a : Fin 13) : flip {a} = {-a} := by
      ext b
      simp only [flipMem, Finset.mem_singleton]
      constructor
      · intro h
        have he := congrArg (fun v : Fin 13 => -v) h
        simpa only [neg_neg] using he
      · rintro rfl
        exact neg_neg a
    let input (P L : Finset (Fin 13)) (i : Fin 26) : Bool :=
      Fin.addCases (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L)) i
    have inputSwap (P L : Finset (Fin 13)) (i : Fin 26) :
        input P L (perm i) = input (flip L) (flip P) i := by
      change input P L (swap i) = _
      refine Fin.addCases (m := 13) (n := 13)
        (motive := fun k => input P L (swap k) = input (flip L) (flip P) k) ?_ ?_ i
      · intro p
        simp only [input, swap, Fin.addCases_left, Fin.addCases_right, flipMem]
      · intro l
        simp only [input, swap, Fin.addCases_left, Fin.addCases_right, flipMem]
    have evalD (P L : Finset (Fin 13)) : eval D P L = eval C (flip L) (flip P) := by
      change circuitFun 26 D (input P L) = circuitFun 26 C (input (flip L) (flip P))
      rw [funD]
      apply congrArg (circuitFun 26 C)
      funext i
      exact inputSwap P L i
    have posD (p l : Fin 13) (h : inc p l) : eval D {p} {l} = true := by
      rw [evalD, flipSingleton, flipSingleton]
      exact hpos (-l) (-p) ((incFlip p l).mp h)
    have negD (P L : Finset (Fin 13)) (h : eval D P L = true) : ok P L := by
      rw [evalD] at h
      obtain ⟨p, hp, l, hl, hi⟩ := hneg (flip L) (flip P) h
      exact ⟨-l, (flipMem P l).mp hl, -p, (flipMem L p).mp hp, (incFlip p l).mp hi⟩
    have dP := degreesD (Finset.range 13) (Finset.Ico 13 26) markP
    have dL := degreesD (Finset.Ico 13 26) (Finset.range 13) markL
    have pD : ¬ HasLineDegree 26 (Finset.range 13) D 1 := by
      change ¬ D.lineDeg 26 (Finset.range 13) ≤ 1
      rw [dP]
      exact hL
    have lD : ¬ HasLineDegree 26 (Finset.Ico 13 26) D 1 := by
      change ¬ D.lineDeg 26 (Finset.Ico 13 26) ≤ 1
      rw [dL]
      exact hP
    have sorted : D.lineDeg 26 (Finset.range 13) ≤ D.lineDeg 26 (Finset.Ico 13 26) := by
      rw [dP, dL]
      omega
    rw [← sizeD]
    exact residual D hD posD negD pD lD sorted
