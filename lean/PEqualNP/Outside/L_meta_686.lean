import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_686 : ∀ (m n r : ℕ) (S : Fin m → Finset (Fin n)),
    (∀ x y : Fin n, x ≠ y → ∃ i : Fin m, x ∈ S i ∧ y ∈ S i) →
    (∀ x : Fin n, (Finset.univ.filter (fun i : Fin m => x ∈ S i)).card = r) →
    ∀ B : Finset (Fin n),
      (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)).card + B.card ≤ B.card * r + 1 := by
  intro m n r S hcov hr B
  induction B using Finset.induction_on with
  | empty => simp
  | insert a B ha ih =>
    have hN : Finset.univ.filter (fun i : Fin m => ∃ x ∈ insert a B, x ∈ S i)
        = Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)
          ∪ Finset.univ.filter (fun i : Fin m => a ∈ S i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.exists_mem_insert]
      exact or_comm
    rw [hN, Finset.card_insert_of_notMem ha, add_mul, one_mul]
    have h1 := Finset.card_union_add_card_inter
      (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i))
      (Finset.univ.filter (fun i : Fin m => a ∈ S i))
    have h2 := hr a
    rcases B.eq_empty_or_nonempty with hB | ⟨y, hy⟩
    · have hNB : (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)).card = 0 := by
        rw [hB]
        simp
      have hB0 : B.card = 0 := by
        rw [hB]
        rfl
      have hB1 : B.card * r = 0 := by
        rw [hB0, Nat.zero_mul]
      omega
    · have hya : a ≠ y := by
        rintro rfl
        exact ha hy
      obtain ⟨i, hai, hyi⟩ := hcov a y hya
      have h3 : 0 < (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)
          ∩ Finset.univ.filter (fun i : Fin m => a ∈ S i)).card := by
        apply Finset.card_pos.mpr
        exact ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hy, hyi⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩⟩⟩
      omega
