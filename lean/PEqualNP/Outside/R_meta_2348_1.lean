import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm in
theorem PEqualNP.Outside.R_meta_2348_1
    (hsensitivity :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ) → Bool) (x4 : ℕ → Bool), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (14 : ℕ) + x5 ∧ x9 < (14 : ℕ) + x5) → (∀ (x6 : Fin (14 : ℕ)), x4 ↑x6 = Decidable.decide (x2 = x6)) → (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ), x1.gates[x7]? = Option.some x8 → x8.inputs = [x9, x10] → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x4 ((14 : ℕ) + x7) = ((x1.wires (List.ofFn x3)).getD x9 Bool.false && x4 x10 || x4 x9 && (x1.wires (List.ofFn x3)).getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ((14 : ℕ) + x7) = (x4 x9 || x4 x10))) → x1.eval (List.ofFn x3) = Bool.false → x1.eval (List.ofFn fun (x9 : Fin (14 : ℕ)) => if x2 = x9 then Bool.true else x3 x9) = Bool.true → x4 x1.output = Bool.false → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {↑x2})
    (htrace :
      ∀ (C : Circuit) (s : Bool) (d : ℕ → Bool),
        let W := C.wires (List.ofFn fun i : Fin 14 => decide (i = if s then 0 else 7))
        IsAO2 14 C →
        (∀ i < 14, d i = decide (i = if s then 7 else 0)) →
        (∀ j < C.size,
          let g := gateAt C j
          let a := opnd C j 0
          let b := opnd C j 1
          (g.op = .and → d (14 + j) = (W.getD a false && d b || d a && W.getD b false)) ∧
          (g.op = .or → d (14 + j) = (d a || d b))) →
        d C.output = false →
        PEqualNP.ReadK.lineSingle C 14
          (fun i => if s then decide (7 ≤ i) else decide (i < 7)) 0 7 = false)
    (hcore :
      let f := fun x : Fin 14 → Bool =>
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
      ∀ C : Circuit,
        C.size ≤ 27 → IsAO2 14 C →
        (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
        (gateAt C 0).op = .or →
        (∀ x : Fin 14 → Bool,
          ((f x ∧ ∀ y : Fin 14 → Bool, y ≤ x → f y → y = x) ∨
            (¬ f x ∧ ∀ y : Fin 14 → Bool, x ≤ y → ¬ f y → y = x)) →
          (C.eval (List.ofFn x) = true ↔ f x)) →
        2 ≤ C.lineDeg 14 {0} → 2 ≤ C.lineDeg 14 {7} →
        PEqualNP.ReadK.lineSingle C 14 (fun i => decide (i < 7)) 0 7 = false →
        PEqualNP.ReadK.lineSingle C 14 (fun i => decide (7 ≤ i)) 0 7 = false → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  dsimp only
  intro C hsize hao hdistinct hfirst hval hreads
  have hlen (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) : j < C.size :=
    (List.getElem?_eq_some_iff.mp hj).choose
  have hget (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) : gateAt C j = g := by
    change C.gates.getD j ⟨.or, []⟩ = g
    rw [List.getD_eq_getElem?_getD, hj] <;> rfl
  have hslots (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g)
      (a b : ℕ) (hab : g.inputs = [a, b]) : opnd C j 0 = a ∧ opnd C j 1 = b := by
    change (gateAt C j).inputs.getD 0 0 = a ∧ (gateAt C j).inputs.getD 1 0 = b
    rw [hget j g hj, hab]
    exact ⟨rfl, rfl⟩
  have hindexed (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) :
      (g.op = .and ∨ g.op = .or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j := by
    have hgmem : g ∈ C.gates := List.mem_iff_getElem?.mpr ⟨j, hj⟩
    have hpair := List.eq_getElem_of_length_eq_two g.inputs (hao.2.2 g hgmem)
    obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := ⟨_, _, hpair⟩
    have hdiff := hdistinct j (hlen j g hj)
    obtain ⟨ha, hb⟩ := hslots j g hj a b hab
    rw [ha, hb] at hdiff
    refine ⟨hao.1 g hgmem, a, b, hab, hdiff, ?_, ?_⟩
    · exact hao.2.1 j (hlen j g hj) a (by simp [hget j g hj, hab])
    · exact hao.2.1 j (hlen j g hj) b (by simp [hget j g hj, hab])
  have hmarked (s : Bool) :
      2 ≤ C.lineDeg 14 {if s then 7 else 0} ∧
        PEqualNP.ReadK.lineSingle C 14
          (fun i => if s then decide (7 ≤ i) else decide (i < 7)) 0 7 = false := by
    obtain ⟨d, hseed, hrec, hout⟩ := hreads s
    refine ⟨?_, htrace C s d hao hseed hrec hout⟩
    let source : Fin 14 := if s then 7 else 0
    let one : Fin 14 → Bool := fun i => decide (i = if s then 0 else 7)
    have hseedFin (i : Fin 14) : d i.val = decide (source = i) := by
      refine (hseed i.val i.isLt).trans ?_
      have hsource : source.val = (if s then 7 else 0) := by
        cases s <;> rfl
      have hequiv : i.val = (if s then 7 else 0) ↔ source = i :=
        ⟨fun h => Fin.ext (hsource.trans h.symm),
          fun h => (congrArg Fin.val h).symm.trans hsource⟩
      by_cases h : i.val = (if s then 7 else 0)
      · exact (decide_eq_true h).trans (decide_eq_true (hequiv.mp h)).symm
      · exact (decide_eq_false h).trans (decide_eq_false (mt hequiv.mpr h)).symm
    have honeNot : C.eval (List.ofFn one) ≠ true := by
      intro h
      obtain ⟨p, l, _, hp, hl⟩ := (hval one).1 h
      cases s
      · have hpoint : (Fin.castAdd 7 p : Fin 14) = 7 := of_decide_eq_true hp
        have hbad := congrArg Fin.val hpoint
        change p.val = 7 at hbad
        have hpbound := p.isLt
        omega
      · have hline : (Fin.natAdd 7 l : Fin 14) = 0 := of_decide_eq_true hl
        have hbad := congrArg Fin.val hline
        change 7 + l.val = 0 at hbad
        omega
    have hone : C.eval (List.ofFn one) = false := by
      cases h : C.eval (List.ofFn one) with
      | false => rfl
      | true => exact (honeNot h).elim
    have htwo : C.eval (List.ofFn fun i => if source = i then true else one i) = true := by
      apply (hval _).2
      refine ⟨0, 0, Or.inl rfl, ?_, ?_⟩
      · cases s <;> decide
      · cases s <;> decide
    have hdegree := hsensitivity C source one d hindexed hseedFin
      (fun j g a b hj hab => by
        have hstep := hrec j (hlen j g hj)
        have hs := hslots j g hj a b hab
        simpa only [one, hget j g hj, hs.1, hs.2] using hstep)
      hone htwo hout
    cases s <;> exact hdegree
  obtain ⟨hdegree0, hpart0⟩ := hmarked false
  obtain ⟨hdegree7, hpart7⟩ := hmarked true
  exact hcore C hsize hao hdistinct hfirst (fun x _ => hval x) hdegree0 hdegree7 hpart0 hpart7
