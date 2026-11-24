import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

-- Each double reread has an exact (2, 2) witness. The charging estimate
-- needs only rejection on independent inputs with at most two from each side.
theorem PEqualNP.Outside.R_meta_2466_2
    (shadow : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      IsReadK (N + N) C 2 → ∀ p l : Fin N, I p l →
      lineSingle C (N + N) (fun i => decide (N ≤ i)) p.val (N + l.val) = false →
      lineSingle C (N + N) (fun i => decide (i < N)) p.val (N + l.val) = false →
      [2, 2] ∈ (readVectors C (N + N) [p.val, N + l.val] 2).getD C.output [])
    (charge : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      PEqualNP.TopForm.IsAO2 (N + N) C →
      PEqualNP.ReadTwo.Lin I →
      PEqualNP.ReadTwo.Snd22 (N + N) C Fin.val (fun l => N + l.val) I →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
        lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false ∧
        [2, 2] ∈ (readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []} ≤ 34 * C.size) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x3 x12 x13 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x2 x13) = Bool.true)) → PEqualNP.ReadK.IsReadK (x2 + x2) x5 (2 : ℕ) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x14 : ℕ) => Decidable.decide (x2 ≤ x14)) (↑x13.1) (x2 + ↑x13.2) = Bool.false ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x14 : ℕ) => Decidable.decide (x14 < x2)) (↑x13.1) (x2 + ↑x13.2) = Bool.false } ≤ (34 : ℕ) * x5.size := by
  intro _ N I inst C _ _ _ joins binary computes read
  have free : PEqualNP.ReadTwo.Lin I := by
    intro p p' l l' hd hl four
    obtain ⟨j, _, unique⟩ := joins p p' hd
    exact hl ((unique l ⟨four.1, four.2.1⟩).trans (unique l' ⟨four.2.2.1, four.2.2.2⟩).symm)
  have sound : PEqualNP.ReadTwo.Snd22 (N + N) C Fin.val (fun l => N + l.val) I := by
    intro P L _ _ independent
    rw [computes, decide_eq_false_iff_not]
    rintro ⟨p, l, he, hp, hl⟩
    have pmem : p.val ∈ P.image Fin.val ∪ L.image (fun u => N + u.val) := of_decide_eq_true hp
    have lmem : N + l.val ∈ P.image Fin.val ∪ L.image (fun u => N + u.val) := of_decide_eq_true hl
    have pmem' : p ∈ P := by
      rcases Finset.mem_union.mp pmem with yes | bad
      · obtain ⟨u, hu, eq⟩ := Finset.mem_image.mp yes
        exact (Fin.ext eq : u = p) ▸ hu
      · obtain ⟨u, _, eq⟩ := Finset.mem_image.mp bad
        omega
    have lmem' : l ∈ L := by
      rcases Finset.mem_union.mp lmem with bad | yes
      · obtain ⟨u, _, eq⟩ := Finset.mem_image.mp bad
        omega
      · obtain ⟨u, hu, eq⟩ := Finset.mem_image.mp yes
        exact (Fin.ext (by omega) : u = l) ▸ hu
    exact independent p pmem' l lmem' he
  let A := {e : Fin N × Fin N // I e.1 e.2 ∧
    lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
    lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false}
  let B := {e : Fin N × Fin N // I e.1 e.2 ∧
    lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
    lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false ∧
    [2, 2] ∈ (readVectors C (N + N) [e.1.val, N + e.2.val] 2).getD C.output []}
  let liftEdge : A → B := fun e =>
    ⟨e.val, e.property.1, e.property.2.1, e.property.2.2,
      shadow N I C binary computes read e.val.1 e.val.2 e.property.1 e.property.2.1 e.property.2.2⟩
  exact (Fintype.card_le_of_injective liftEdge (fun a b h => Subtype.ext (congrArg (fun e : B => e.val) h))).trans
    (charge N I C binary free sound)
