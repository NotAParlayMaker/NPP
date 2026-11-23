import Mathlib

theorem PEqualNP.Outside.L_meta_686 : ∀ (m n r : ℕ) (S : Fin m → Finset (Fin n)),
    (∀ x y : Fin n, x ≠ y → ∃ i : Fin m, x ∈ S i ∧ y ∈ S i) →
    (∀ x : Fin n, (Finset.univ.filter (fun i : Fin m => x ∈ S i)).card = r) →
    ∀ B : Finset (Fin n),
      (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)).card + B.card ≤ B.card * r + 1 := by
  classical
  intro m n r S hpair hregular B
  let U : Finset (Fin n) → Finset (Fin m) := fun B => Finset.univ.filter (fun i => ∃ x ∈ B, x ∈ S i)
  change (U B).card + B.card ≤ B.card * r + 1
  induction B using Finset.induction_on with
  | empty => simp [U]
  | @insert a B ha ih =>
    have hu : U (insert a B) = (Finset.univ.filter (fun i => a ∈ S i)) ∪ U B := by
      ext i
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_insert]
      aesop
    rw [hu, Finset.card_insert_of_notMem ha]
    by_cases hb : B = ∅
    · subst B
      simpa [U, hregular] using (Nat.le_refl (r + 1))
    · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hb
      have hab : a ≠ b := by intro h; subst b; exact ha hb
      obtain ⟨i, hai, hbi⟩ := hpair a b hab
      have hi : i ∈ (Finset.univ.filter (fun i => a ∈ S i)) ∩ U B := by
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, U]
        exact ⟨hai, b, hb, hbi⟩
      have hc := Finset.card_pos.mpr ⟨i, hi⟩
      have he := Finset.card_union_add_card_inter (Finset.univ.filter (fun i => a ∈ S i)) (U B)
      rw [hregular a] at he
      rw [Nat.add_mul, Nat.one_mul]
      omega
