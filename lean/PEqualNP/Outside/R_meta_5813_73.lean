import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_5813_73
    (hElimNorm :
      let S := singerLines3
      let X := incidenceInput
      let Qs := quadrangles S
      let N := fun Q : Finset (Fin 13) => X Q (missLines S Q)
      ∀ (C : Circuit) (r s : Fin 13) (b : Bool), Monotone2 C → ReadsBack 27 C →
      C.size ≤ 62 →
      (∀ p l : Fin 13, p ∈ S l → p ≠ r ∨ l ≠ s → C.eval (X {p} {l} ++ [b]) = true) →
      (∀ Q ∈ Qs, C.eval (N Q ++ [b]) = false) →
      ∃ E : Circuit, IsAO2 26 E ∧ E.size ≤ C.size ∧ 26 ≤ E.output ∧ E.output < 26 + E.size ∧
        (∀ g ∈ E.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) ∧
        (∀ p l : Fin 13, p ∈ S l → p ≠ 0 ∨ l ≠ 0 → E.eval (X {p} {l}) = true) ∧
        (∀ Q ∈ Qs, E.eval (N Q) = false) ∧
        (∀ p a l b : Fin 13, p ∉ S l → p ∉ S b → a ∉ S l → a ∉ S b → E.eval (X {p, a} {l, b}) = false) ∧
        (∀ p l : Fin 13, p ∉ S l → E.eval (X {p} {l}) = false) ∧
        (∀ p : Fin 13, E.eval (X {p} (∅ : Finset (Fin 13))) = false) ∧
        (∀ l : Fin 13, E.eval (X (∅ : Finset (Fin 13)) {l}) = false) ∧
        (∀ j < E.size, (gateAt E j).op = GateOp.and → ∀ w ∈ (gateAt E j).inputs,
          ∃ Q ∈ Qs, (E.wires (N Q)).getD (26 + j) false ≠ (E.wires (N Q)).getD w false) ∧
        (∀ j < E.size, ∃ p l : Fin 13, p ∈ S l ∧
          (E.eval (X {(0 : Fin 13)} {(0 : Fin 13)}) = false → p ≠ 0 ∨ l ≠ 0) ∧
          ({ gates := E.gates.set j ⟨GateOp.or, []⟩, output := E.output } : Circuit).eval (X {p} {l}) = false))
    (hFull :
      let S := singerLines3
      let X := incidenceInput
      let Qs := quadrangles S
      let N := fun Q : Finset (Fin 13) => X Q (missLines S Q)
      ∀ C : Circuit, IsAO2 26 C → C.size ≤ 62 → 26 ≤ C.output → C.output < 26 + C.size →
      (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
      (∀ p l : Fin 13, p ∈ S l → C.eval (X {p} {l}) = true) →
      (∀ Q ∈ Qs, C.eval (N Q) = false) →
      (∀ p a l b : Fin 13, p ∉ S l → p ∉ S b → a ∉ S l → a ∉ S b → C.eval (X {p, a} {l, b}) = false) →
      (∀ p l : Fin 13, p ∉ S l → C.eval (X {p} {l}) = false) →
      (∀ p : Fin 13, C.eval (X {p} (∅ : Finset (Fin 13))) = false) →
      (∀ l : Fin 13, C.eval (X (∅ : Finset (Fin 13)) {l}) = false) →
      (∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ w ∈ (gateAt C j).inputs,
        ∃ Q ∈ Qs, (C.wires (N Q)).getD (26 + j) false ≠ (C.wires (N Q)).getD w false) →
      (∀ j < C.size, ∃ p l : Fin 13, p ∈ S l ∧
        ({ gates := C.gates.set j ⟨GateOp.or, []⟩, output := C.output } : Circuit).eval (X {p} {l}) = false) →
      False)
    (hPunctLow :
      let S := singerLines3
      let X := incidenceInput
      let Qs := quadrangles S
      let N := fun Q : Finset (Fin 13) => X Q (missLines S Q)
      ∀ C : Circuit, IsAO2 26 C → C.size ≤ 62 → 26 ≤ C.output → C.output < 26 + C.size →
      (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
      (∀ p l : Fin 13, p ∈ S l → p ≠ 0 ∨ l ≠ 0 → C.eval (X {p} {l}) = true) →
      C.eval (X {(0 : Fin 13)} {(0 : Fin 13)}) = false →
      (∀ Q ∈ Qs, C.eval (N Q) = false) →
      (∀ p a l b : Fin 13, p ∉ S l → p ∉ S b → a ∉ S l → a ∉ S b → C.eval (X {p, a} {l, b}) = false) →
      (∀ p l : Fin 13, p ∉ S l → C.eval (X {p} {l}) = false) →
      (∀ p : Fin 13, C.eval (X {p} (∅ : Finset (Fin 13))) = false) →
      (∀ l : Fin 13, C.eval (X (∅ : Finset (Fin 13)) {l}) = false) →
      (∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ w ∈ (gateAt C j).inputs,
        ∃ Q ∈ Qs, (C.wires (N Q)).getD (26 + j) false ≠ (C.wires (N Q)).getD w false) →
      (∀ j < C.size, ∃ p l : Fin 13, p ∈ S l ∧ (p ≠ 0 ∨ l ≠ 0) ∧
        ({ gates := C.gates.set j ⟨GateOp.or, []⟩, output := C.output } : Circuit).eval (X {p} {l}) = false) →
      andPairs 26 C ≤ 2 → False)
    (hPunctHigh :
      let S := singerLines3
      let X := incidenceInput
      let Qs := quadrangles S
      let N := fun Q : Finset (Fin 13) => X Q (missLines S Q)
      ∀ C : Circuit, IsAO2 26 C → C.size ≤ 62 → 26 ≤ C.output → C.output < 26 + C.size →
      (∀ g ∈ C.gates, g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) →
      (∀ p l : Fin 13, p ∈ S l → p ≠ 0 ∨ l ≠ 0 → C.eval (X {p} {l}) = true) →
      C.eval (X {(0 : Fin 13)} {(0 : Fin 13)}) = false →
      (∀ Q ∈ Qs, C.eval (N Q) = false) →
      (∀ p a l b : Fin 13, p ∉ S l → p ∉ S b → a ∉ S l → a ∉ S b → C.eval (X {p, a} {l, b}) = false) →
      (∀ p l : Fin 13, p ∉ S l → C.eval (X {p} {l}) = false) →
      (∀ p : Fin 13, C.eval (X {p} (∅ : Finset (Fin 13))) = false) →
      (∀ l : Fin 13, C.eval (X (∅ : Finset (Fin 13)) {l}) = false) →
      (∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ w ∈ (gateAt C j).inputs,
        ∃ Q ∈ Qs, (C.wires (N Q)).getD (26 + j) false ≠ (C.wires (N Q)).getD w false) →
      (∀ j < C.size, ∃ p l : Fin 13, p ∈ S l ∧ (p ≠ 0 ∨ l ≠ 0) ∧
        ({ gates := C.gates.set j ⟨GateOp.or, []⟩, output := C.output } : Circuit).eval (X {p} {l}) = false) →
      3 ≤ andPairs 26 C → False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →       (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) x1 →         have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];         (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) → (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) → (63 : ℕ) ≤ x1.size) := by
  intro C r s b hm hr _ D X27 hpos hquad _
  by_cases h63 : 63 ≤ C.size
  · exact h63
  have hInc : ∀ p l : Fin 13, p - l ∈ D ↔ p ∈ singerLines3 l :=
    of_decide_eq_true (rfl : decide (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔ p ∈ singerLines3 l) = true)
  have hQuadIff (Q : Finset (Fin 13)) :
      Q ∈ quadrangles singerLines3 ↔ Q.card = 4 ∧ ∀ k : Fin 13, {p ∈ Q | p - k ∈ D}.card ≤ 2 := by
    have heq (k : Fin 13) : Q ∩ singerLines3 k = {p ∈ Q | p - k ∈ D} := by
      ext p; rw [Finset.mem_inter, Finset.mem_filter]; exact and_congr_right fun _ => (hInc p k).symm
    change Q ∈ (Finset.univ.powersetCard 4).filter (fun A => ∀ l : Fin 13, (A ∩ singerLines3 l).card ≤ 2) ↔ _
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨h.1.2, fun k => by rw [← heq k]; exact h.2 k⟩,
      fun h => ⟨⟨Finset.subset_univ _, h.1⟩, fun k => by rw [heq k]; exact h.2 k⟩⟩
  have hMiss (Q : Finset (Fin 13)) :
      missLines singerLines3 Q = Finset.univ.filter (fun l : Fin 13 => ∀ p ∈ Q, p - l ∉ D) := by
    ext l; change l ∈ Finset.univ.filter (fun l => Disjoint (singerLines3 l) Q) ↔ _
    rw [Finset.mem_filter, Finset.mem_filter]; refine and_congr_right fun _ => ?_; rw [Finset.disjoint_left]
    exact ⟨fun h p hp hi => h ((hInc p l).mp hi) hp, fun h p hi hp => h p hp ((hInc p l).mpr hi)⟩
  have hszC : C.size ≤ 62 := Nat.le_of_lt_succ (Nat.lt_of_not_le h63)
  obtain ⟨E, hmE, hszE, hlo, hhi, hdist, hpE, hqE, hrcE, hneE, hptE, hlnE, hessE, hndE⟩ :=
    hElimNorm C r s b hm hr hszC
      (fun p l hpl hne => hpos p l ((hInc p l).mpr hpl) hne)
      (fun Q hQ => by dsimp only; rw [hMiss]; exact hquad Q ((hQuadIff Q).mp hQ).1 ((hQuadIff Q).mp hQ).2)
  exfalso
  have hszE' : E.size ≤ 62 := Nat.le_trans hszE hszC
  by_cases hE00 : E.eval (incidenceInput {(0 : Fin 13)} {(0 : Fin 13)}) = true
  · refine hFull E hmE hszE' hlo hhi hdist ?_ hqE hrcE hneE hptE hlnE hessE ?_
    · intro p l hpl; by_cases hne0 : p ≠ 0 ∨ l ≠ 0; · exact hpE p l hpl hne0
      rw [by_contra fun h : p ≠ 0 => hne0 (Or.inl h), by_contra fun h : l ≠ 0 => hne0 (Or.inr h)]; exact hE00
    · intro j hj
      exact Exists.elim (hndE j hj) fun p hp => Exists.elim hp fun l hl => ⟨p, l, hl.1, hl.2.2⟩
  · have hE00f : E.eval (incidenceInput {(0 : Fin 13)} {(0 : Fin 13)}) = false := Bool.eq_false_iff.mpr hE00
    have hndP : ∀ j < E.size, ∃ p l : Fin 13, p ∈ singerLines3 l ∧ (p ≠ 0 ∨ l ≠ 0) ∧
        ({ gates := E.gates.set j ⟨GateOp.or, []⟩, output := E.output } : Circuit).eval (incidenceInput {p} {l}) = false :=
      fun j hj => Exists.elim (hndE j hj) fun p hp => Exists.elim hp fun l hl => ⟨p, l, hl.1, hl.2.1 hE00f, hl.2.2⟩
    by_cases hlow : andPairs 26 E ≤ 2
    · exact hPunctLow E hmE hszE' hlo hhi hdist hpE hE00f hqE hrcE hneE hptE hlnE hessE hndP hlow
    · exact hPunctHigh E hmE hszE' hlo hhi hdist hpE hE00f hqE hrcE hneE hptE hlnE hessE hndP (Nat.succ_le_of_lt (Nat.lt_of_not_le hlow))
