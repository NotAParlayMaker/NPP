import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2874_1
    (singleStar : ∀ n m : ℕ,
      let Good := fun (E : Finset (Fin n × Fin m)) (s : ℕ) =>
      ∃ (C : Circuit) (W : Bool → Finset ℕ), IsAO2 (n + m) C ∧ C.size ≤ s ∧
        (∀ x : Fin (n + m) → Bool, circuitFun (n + m) C x =
          decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) ∧
        (∀ b, ∀ i ∈ W b, i < n + m ∧ decide (n ≤ i) = b ∨
          ∃ j < C.size, i = n + m + j ∧ (gateAt C j).op = GateOp.or ∧
            ∀ k ∈ (gateAt C j).inputs, k ∈ W b) ∧
        ∀ j < C.size, (gateAt C j).op = GateOp.and →
          ∃ u v b, (gateAt C j).inputs = [u, v] ∧ u ∈ W b ∧ v ∈ W (!b)
      ∀ E, E.Nonempty →
        ((∃ p, ∀ e ∈ E, e.1 = p) ∨ (∃ l, ∀ e ∈ E, e.2 = l)) →
        Good E E.card)
    (merge : ∀ n m : ℕ,
      let Good := fun (E : Finset (Fin n × Fin m)) (s : ℕ) =>
      ∃ (C : Circuit) (W : Bool → Finset ℕ), IsAO2 (n + m) C ∧ C.size ≤ s ∧
        (∀ x : Fin (n + m) → Bool, circuitFun (n + m) C x =
          decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) ∧
        (∀ b, ∀ i ∈ W b, i < n + m ∧ decide (n ≤ i) = b ∨
          ∃ j < C.size, i = n + m + j ∧ (gateAt C j).op = GateOp.or ∧
            ∀ k ∈ (gateAt C j).inputs, k ∈ W b) ∧
        ∀ j < C.size, (gateAt C j).op = GateOp.and →
          ∃ u v b, (gateAt C j).inputs = [u, v] ∧ u ∈ W b ∧ v ∈ W (!b)
      ∀ E F s t, Good E s → Good F t → Good (E ∪ F) (s + t + 1)) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),   (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),       PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧         x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧           (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧             have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;             (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧ ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Bool), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 x15 ∧ x14 ∈ x8 !x15 := by
  intro n m E P L hCover
  let Good := fun (E : Finset (Fin n × Fin m)) (s : ℕ) =>
      ∃ (C : Circuit) (W : Bool → Finset ℕ), IsAO2 (n + m) C ∧ C.size ≤ s ∧
        (∀ x : Fin (n + m) → Bool, circuitFun (n + m) C x =
          decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) ∧
        (∀ b, ∀ i ∈ W b, i < n + m ∧ decide (n ≤ i) = b ∨
          ∃ j < C.size, i = n + m + j ∧ (gateAt C j).op = GateOp.or ∧
            ∀ k ∈ (gateAt C j).inputs, k ∈ W b) ∧
        ∀ j < C.size, (gateAt C j).op = GateOp.and →
          ∃ u v b, (gateAt C j).inputs = [u, v] ∧ u ∈ W b ∧ v ∈ W (!b)
  change Good E (E.card + P.card + L.card - 1)
  have emptyGood : Good ∅ 0 := by
    refine ⟨⟨[], n + m⟩, fun _ => ∅, ?_, by simp [Circuit.size], ?_, ?_, ?_⟩
    · exact ⟨by simp [PEqualNP.EdgeOwnership.AndOrOnly], by simp [ReadsBack], by simp⟩
    · intro x
      simp [circuitFun, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
    · simp
    · simp [Circuit.size]
  have glue (E S R : Finset (Fin n × Fin m)) (k t : ℕ)
      (he : S ∪ R = E) (hc : S.card + R.card = E.card)
      (hk : t + 1 = k) (hgS : Good S S.card) (hgR : Good R (R.card + t - 1))
      (hRest : R.Nonempty → 0 < t) : Good E (E.card + k - 1) := by
    by_cases h : R.Nonempty
    · have hpos : 0 < t := hRest h
      have h := merge n m S R S.card (R.card + t - 1) hgS hgR
      rw [he] at h
      have eqn : S.card + (R.card + t - 1) + 1 = E.card + k - 1 := by omega
      exact eqn ▸ h
    · have hR : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hES : E = S := by simpa [hR] using he.symm
      rw [hES]
      obtain ⟨C, W, hm, hs, hf, hw, ha⟩ := hgS
      exact ⟨C, W, hm, by omega, hf, hw, ha⟩
  have build : ∀ k : ℕ, ∀ (E : Finset (Fin n × Fin m)) (P : Finset (Fin n))
      (L : Finset (Fin m)), P.card + L.card = k →
      (∀ e ∈ E, e.1 ∈ P ∨ e.2 ∈ L) → Good E (E.card + k - 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k smaller =>
      intro E P L hK hC
      by_cases hE : E.Nonempty
      · obtain ⟨e, he⟩ := hE
        rcases hC e he with hp | hl
        · let S := E.filter (fun f => f.1 = e.1)
          let R := E.filter (fun f => f.1 ≠ e.1)
          let t := (P.erase e.1).card + L.card
          have hk : t + 1 = k := by
            have h := Finset.card_erase_add_one hp
            dsimp [t]; omega
          have hR : ∀ f ∈ R, f.1 ∈ P.erase e.1 ∨ f.2 ∈ L := by
            intro f hf
            obtain ⟨hf, hne⟩ := Finset.mem_filter.mp hf
            exact (hC f hf).imp (fun h => Finset.mem_erase.mpr ⟨hne, h⟩) id
          have hgS : Good S S.card :=
            singleStar n m S ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
              (Or.inl ⟨e.1, fun f hf => (Finset.mem_filter.mp hf).2⟩)
          have hgR := smaller t (by omega) R (P.erase e.1) L rfl hR
          refine glue E S R k t ?_ ?_ hk hgS hgR ?_
          · exact Finset.filter_union_filter_not_eq _ _
          · exact Finset.card_filter_add_card_filter_not _
          · rintro ⟨f, hf⟩
            rcases hR f hf with h | h
            · have := Finset.card_pos.mpr ⟨_, h⟩
              dsimp [t]; omega
            · have := Finset.card_pos.mpr ⟨_, h⟩
              dsimp [t]; omega
        · let S := E.filter (fun f => f.2 = e.2)
          let R := E.filter (fun f => f.2 ≠ e.2)
          let t := P.card + (L.erase e.2).card
          have hk : t + 1 = k := by
            have h := Finset.card_erase_add_one hl
            dsimp [t]; omega
          have hR : ∀ f ∈ R, f.1 ∈ P ∨ f.2 ∈ L.erase e.2 := by
            intro f hf
            obtain ⟨hf, hne⟩ := Finset.mem_filter.mp hf
            exact (hC f hf).imp id (fun h => Finset.mem_erase.mpr ⟨hne, h⟩)
          have hgS : Good S S.card :=
            singleStar n m S ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
              (Or.inr ⟨e.2, fun f hf => (Finset.mem_filter.mp hf).2⟩)
          have hgR := smaller t (by omega) R P (L.erase e.2) rfl hR
          refine glue E S R k t ?_ ?_ hk hgS hgR ?_
          · exact Finset.filter_union_filter_not_eq _ _
          · exact Finset.card_filter_add_card_filter_not _
          · rintro ⟨f, hf⟩
            rcases hR f hf with h | h
            · have := Finset.card_pos.mpr ⟨_, h⟩
              dsimp [t]; omega
            · have := Finset.card_pos.mpr ⟨_, h⟩
              dsimp [t]; omega
      · have he : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
        subst E
        obtain ⟨C, W, hm, hs, hf, hw, ha⟩ := emptyGood
        exact ⟨C, W, hm, by omega, hf, hw, ha⟩
  simpa only [Nat.add_assoc] using build (P.card + L.card) E P L rfl hCover
