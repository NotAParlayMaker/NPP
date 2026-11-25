import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5262_7
    (small : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : Circuit), IsLeastAO G C → TopForm G C →
      ({e ∈ Ustar G C | (¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin (2 : ℕ)),
          (2 : ℕ) ≤ (orIn n C (n + h)).card ∧ (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v}) ∧
        ∃ a ∈ centreless G C, e ∈ gammaE G C a ∧
          (Finset.image (fun p : Fin n => p) (side C a 0)).card ≤ 1 ∧
          (Finset.image (fun p : Fin n => p) (side C a 1)).card ≤ 1}).card ≤
        k * (C.size + 1))
    (meet : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : Circuit), IsLeastAO G C → TopForm G C →
      ({e ∈ Ustar G C | (¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin (2 : ℕ)),
          (2 : ℕ) ≤ (orIn n C (n + h)).card ∧ (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v}) ∧
        ∃ a ∈ centreless G C, e ∈ gammaE G C a ∧
          (((Finset.image (fun t : Fin n => t) (side C a 0)) = ∅ ∧
              (2 : ℕ) ≤ (Finset.image (fun p : Fin n => p) (side C a 1)).card ∧
              ∃ w ∈ Finset.image (fun t : Fin n => t) (side C a 1), w ∈ e) ∨
            ((Finset.image (fun t : Fin n => t) (side C a 1)) = ∅ ∧
              (2 : ℕ) ≤ (Finset.image (fun p : Fin n => p) (side C a 0)).card ∧
              ∃ w ∈ Finset.image (fun t : Fin n => t) (side C a 0), w ∈ e))}).card ≤
        k * (C.size + 1))
    (miss : ∃ k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : Circuit), IsLeastAO G C → TopForm G C →
      ({e ∈ Ustar G C | (¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin (2 : ℕ)),
          (2 : ℕ) ≤ (orIn n C (n + h)).card ∧ (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
          orIn n C (opnd C h b) = {v}) ∧
        ∃ a ∈ centreless G C, e ∈ gammaE G C a ∧
          (((Finset.image (fun t : Fin n => t) (side C a 0)) = ∅ ∧
              (2 : ℕ) ≤ (Finset.image (fun p : Fin n => p) (side C a 1)).card ∧
              ∀ w ∈ Finset.image (fun t : Fin n => t) (side C a 1), w ∉ e) ∨
            ((Finset.image (fun t : Fin n => t) (side C a 1)) = ∅ ∧
              (2 : ℕ) ≤ (Finset.image (fun p : Fin n => p) (side C a 0)).card ∧
              ∀ w ∈ Finset.image (fun t : Fin n => t) (side C a 0), w ∉ e))}).card ≤
        k * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → {x10 ∈ PEqualNP.TopForm.Ustar x3 x7 | (¬∃ (x11 : Fin x2) (x12 : Fin x2), x10 = s(x11, x12) ∧ ∃ x13 < x7.gates.length, ∃ (x14 : Fin (2 : ℕ)), (2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 (x2 + x13)).card ∧ (∀ x15 ∈ PEqualNP.TopForm.orIn x2 x7 (x2 + x13), x3.Adj x11 x15) ∧ PEqualNP.TopForm.orIn x2 x7 (PEqualNP.TopForm.opnd x7 x13 x14) = {x12}) ∧ ∃ x11 ∈ PEqualNP.TopForm.centreless x3 x7, x10 ∈ PEqualNP.TopForm.gammaE x3 x7 x11}.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k1, hk1⟩ := small
  obtain ⟨k2, hk2⟩ := meet
  obtain ⟨k3, hk3⟩ := miss
  refine ⟨k1 + k2 + k3, ?_⟩
  intro n G _ hgirth hne C hleast htop
  classical
  let P : Sym2 (Fin n) → Prop := fun e =>
    ¬∃ (u v : Fin n), e = s(u, v) ∧ ∃ h < C.gates.length, ∃ (b : Fin (2 : ℕ)),
      (2 : ℕ) ≤ (orIn n C (n + h)).card ∧ (∀ w ∈ orIn n C (n + h), G.Adj u w) ∧
      orIn n C (opnd C h b) = {v}
  let Bad := {e ∈ Ustar G C | P e ∧ ∃ a ∈ centreless G C, e ∈ gammaE G C a}
  let S1 := {e ∈ Ustar G C | P e ∧ ∃ a ∈ centreless G C, e ∈ gammaE G C a ∧
    (Finset.image (fun p : Fin n => p) (side C a 0)).card ≤ 1 ∧
    (Finset.image (fun p : Fin n => p) (side C a 1)).card ≤ 1}
  let S2 := {e ∈ Ustar G C | P e ∧ ∃ a ∈ centreless G C, e ∈ gammaE G C a ∧
    (((Finset.image (fun t : Fin n => t) (side C a 0)) = ∅ ∧
        (2 : ℕ) ≤ (Finset.image (fun p : Fin n => p) (side C a 1)).card ∧
        ∃ w ∈ Finset.image (fun t : Fin n => t) (side C a 1), w ∈ e) ∨
      ((Finset.image (fun t : Fin n => t) (side C a 1)) = ∅ ∧
        (2 : ℕ) ≤ (Finset.image (fun p : Fin n => p) (side C a 0)).card ∧
        ∃ w ∈ Finset.image (fun t : Fin n => t) (side C a 0), w ∈ e))}
  let S3 := {e ∈ Ustar G C | P e ∧ ∃ a ∈ centreless G C, e ∈ gammaE G C a ∧
    (((Finset.image (fun t : Fin n => t) (side C a 0)) = ∅ ∧
        (2 : ℕ) ≤ (Finset.image (fun p : Fin n => p) (side C a 1)).card ∧
        ∀ w ∈ Finset.image (fun t : Fin n => t) (side C a 1), w ∉ e) ∨
      ((Finset.image (fun t : Fin n => t) (side C a 1)) = ∅ ∧
        (2 : ℕ) ≤ (Finset.image (fun p : Fin n => p) (side C a 0)).card ∧
        ∀ w ∈ Finset.image (fun t : Fin n => t) (side C a 0), w ∉ e))}
  have hS1 : S1.card ≤ k1 * (C.size + 1) := by
    refine (Finset.card_le_card ?_).trans (hk1 n G hgirth hne C hleast htop)
    intro e he
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp he)
  have hS2 : S2.card ≤ k2 * (C.size + 1) := by
    refine (Finset.card_le_card ?_).trans (hk2 n G hgirth hne C hleast htop)
    intro e he
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp he)
  have hS3 : S3.card ≤ k3 * (C.size + 1) := by
    refine (Finset.card_le_card ?_).trans (hk3 n G hgirth hne C hleast htop)
    intro e he
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp he)
  have hsub : Bad ⊆ S1 ∪ (S2 ∪ S3) := by
    intro e he
    obtain ⟨heU, hP, a, ha, hgam⟩ := Finset.mem_filter.mp he
    have box_eq (b : Fin 2) :
        Finset.image (fun p : Fin n => p) (side (n := n) C a b) = side (n := n) C a b :=
      Finset.image_id
    have hempty : side (n := n) C a 0 = ∅ ∨ side (n := n) C a 1 = ∅ :=
      (Finset.mem_filter.mp ha).2
    by_cases hsm : (side (n := n) C a 0).card ≤ 1 ∧ (side (n := n) C a 1).card ≤ 1
    · have h0c : (Finset.image (fun p : Fin n => p) (side C a 0)).card ≤ 1 := by
        rw [box_eq 0]; exact hsm.1
      have h1c : (Finset.image (fun p : Fin n => p) (side C a 1)).card ≤ 1 := by
        rw [box_eq 1]; exact hsm.2
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heU, hP, a, ha, hgam, h0c, h1c⟩)
    · rcases hempty with h0 | h1
      · have hem0 : (Finset.image (fun t : Fin n => t) (side C a 0)) = ∅ := by
          rw [box_eq 0]; exact h0
        have hbig : (2 : ℕ) ≤ (side (n := n) C a 1).card := by
          by_contra hlt
          have hc0 : (side (n := n) C a 0).card = 0 := Finset.card_eq_zero.mpr h0
          exact hsm ⟨by omega, by omega⟩
        have hbigf : (2 : ℕ) ≤ (Finset.image (fun p : Fin n => p) (side C a 1)).card := by
          rw [box_eq 1]; exact hbig
        by_cases hhit : ∃ w ∈ side (n := n) C a 1, w ∈ e
        · obtain ⟨w, hw, hwe⟩ := hhit
          have hmem : w ∈ Finset.image (fun t : Fin n => t) (side C a 1) := by
            rw [box_eq 1]; exact hw
          exact Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨heU, hP, a, ha, hgam, Or.inl ⟨hem0, hbigf, w, hmem, hwe⟩⟩))
        · have hall : ∀ w ∈ Finset.image (fun t : Fin n => t) (side C a 1), w ∉ e := by
            intro w hw hwe
            rw [box_eq 1] at hw
            exact hhit ⟨w, hw, hwe⟩
          exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨heU, hP, a, ha, hgam, Or.inl ⟨hem0, hbigf, hall⟩⟩))
      · have hem1 : (Finset.image (fun t : Fin n => t) (side C a 1)) = ∅ := by
          rw [box_eq 1]; exact h1
        have hbig : (2 : ℕ) ≤ (side (n := n) C a 0).card := by
          by_contra hlt
          have hc1 : (side (n := n) C a 1).card = 0 := Finset.card_eq_zero.mpr h1
          exact hsm ⟨by omega, by omega⟩
        have hbigf : (2 : ℕ) ≤ (Finset.image (fun p : Fin n => p) (side C a 0)).card := by
          rw [box_eq 0]; exact hbig
        by_cases hhit : ∃ w ∈ side (n := n) C a 0, w ∈ e
        · obtain ⟨w, hw, hwe⟩ := hhit
          have hmem : w ∈ Finset.image (fun t : Fin n => t) (side C a 0) := by
            rw [box_eq 0]; exact hw
          exact Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨heU, hP, a, ha, hgam, Or.inr ⟨hem1, hbigf, w, hmem, hwe⟩⟩))
        · have hall : ∀ w ∈ Finset.image (fun t : Fin n => t) (side C a 0), w ∉ e := by
            intro w hw hwe
            rw [box_eq 0] at hw
            exact hhit ⟨w, hw, hwe⟩
          exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨heU, hP, a, ha, hgam, Or.inr ⟨hem1, hbigf, hall⟩⟩))
  have hcard : Bad.card ≤ S1.card + S2.card + S3.card := by
    have h1u := Finset.card_le_card hsub
    have h2u := Finset.card_union_le S1 (S2 ∪ S3)
    have h3u := Finset.card_union_le S2 S3
    omega
  have hmul : k1 * (C.size + 1) + k2 * (C.size + 1) + k3 * (C.size + 1) =
      (k1 + k2 + k3) * (C.size + 1) := by
    rw [← Nat.add_mul k1 k2 (C.size + 1), ← Nat.add_mul (k1 + k2) k3 (C.size + 1)]
  calc
    _ ≤ S1.card + S2.card + S3.card := hcard
    _ ≤ k1 * (C.size + 1) + k2 * (C.size + 1) + k3 * (C.size + 1) := by omega
    _ = (k1 + k2 + k3) * (C.size + 1) := hmul
