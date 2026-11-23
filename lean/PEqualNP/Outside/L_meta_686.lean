import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_686 : ∀ (m n r : ℕ) (S : Fin m → Finset (Fin n)),
    (∀ x y : Fin n, x ≠ y → ∃ i : Fin m, x ∈ S i ∧ y ∈ S i) →
    (∀ x : Fin n, (Finset.univ.filter (fun i : Fin m => x ∈ S i)).card = r) →
    ∀ B : Finset (Fin n),
      (Finset.univ.filter (fun i : Fin m => ∃ x ∈ B, x ∈ S i)).card + B.card ≤ B.card * r + 1 := by
  classical
  intro m n r S hpair hregular B
  induction B using Finset.induction_on with
  | empty => simp
  | @insert x B hx ih =>
    by_cases hB : B = ∅
    · subst B
      simp [hregular]
    · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hB
      have hxy : x ≠ y := by
        intro h
        subst y
        exact hx hy
      obtain ⟨i, hxi, hyi⟩ := hpair x y hxy
      let U := Finset.univ.filter (fun i : Fin m => ∃ z ∈ B, z ∈ S i)
      let V := Finset.univ.filter (fun i : Fin m => x ∈ S i)
      have hunion :
          Finset.univ.filter (fun i : Fin m => ∃ z ∈ insert x B, z ∈ S i) = V ∪ U := by
        ext j
        simp [U, V]
      have hinter : 0 < (V ∩ U).card := by
        apply Finset.card_pos.mpr
        refine ⟨i, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
        · simp [V, hxi]
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, y, hy, hyi⟩
      have hcard := Finset.card_union_add_card_inter V U
      have hV : V.card = r := hregular x
      change U.card + B.card ≤ B.card * r + 1 at ih
      rw [hunion, Finset.card_insert_of_notMem hx, Nat.add_mul, one_mul]
      omega
