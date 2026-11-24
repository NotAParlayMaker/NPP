import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2702 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj],   have x3 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};   have x4 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};   (∀ (x5 x6 : Fin (11 : ℕ)), x1.Adj x5 x6 → x5 ∈ x3 ∨ x6 ∈ x3 ∨ (x5, x6) ∈ x4 ∨ (x6, x5) ∈ x4) →     ∀ (x6 : Finset (Fin (11 : ℕ))),       PEqualNP.MetaComplexity.NestedCover.IsMinCover x1 x6 →         ∃ x8 ⊆ x3,           (∀ x9 ∈ x3 \ x8, ∀ x11 ∈ x3 \ x8, ¬x1.Adj x9 x11) ∧             have x9 : Finset (Fin (11 : ℕ)) := {x9 ∈ Finset.univ \ x3 | ∃ x10 ∈ x3 \ x8, x1.Adj x10 x9};             have x10 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x10 ∈ x4 | x1.Adj x10.1 x10.2 ∧ x10.1 ∉ x9 ∧ x10.2 ∉ x9};             x6.card = x8.card + x9.card + x10.card := by
  intro G inst S matching hedge C hC
  classical
  let A := C ∩ S
  let B := (Finset.univ \ S).filter (fun v => ∃ u ∈ S \ A, G.Adj u v)
  let E := matching.filter (fun e => G.Adj e.1 e.2 ∧ e.1 ∉ B ∧ e.2 ∉ B)
  have cover {u v : Fin 11} (h : G.Adj u v) : u ∈ C ∨ v ∈ C := hC.1 h
  have hA : A ⊆ S := Finset.inter_subset_right
  have hA_C : A ⊆ C := Finset.inter_subset_left
  have uncovered {u : Fin 11} (hu : u ∈ S \ A) : u ∉ C := by
    intro hc
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_inter.mpr ⟨hc, (Finset.mem_sdiff.mp hu).1⟩)
  have independent : ∀ u ∈ S \ A, ∀ v ∈ S \ A, ¬G.Adj u v := by
    intro u hu v hv hadj
    exact (cover hadj).elim (uncovered hu) (uncovered hv)
  have hB_out {v : Fin 11} (hv : v ∈ B) : v ∉ S :=
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
  have hB_C : B ⊆ C := by
    intro v hv
    obtain ⟨u, hu, hadj⟩ := (Finset.mem_filter.mp hv).2
    exact (cover hadj).resolve_left (uncovered hu)
  have force {u v : Fin 11} (hu : u ∈ S) (ha : u ∉ A) (hv : v ∉ S)
      (hadj : G.Adj u v) : v ∈ B :=
    Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩,
      u, Finset.mem_sdiff.mpr ⟨hu, ha⟩, hadj⟩
  let pick (e : Fin 11 × Fin 11) := if e.1 ∈ C then e.1 else e.2
  have picked (e : Fin 11 × Fin 11) : pick e = e.1 ∨ pick e = e.2 := by
    by_cases he : e.1 ∈ C <;> simp [pick, he]
  have ends (e : Fin 11 × Fin 11) (he : e ∈ matching) : e.1 ∉ S ∧ e.2 ∉ S := by
    change e ∈ ({(1, 4), (2, 5), (6, 7)} : Finset (Fin 11 × Fin 11)) at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> decide
  have distinct (e f : Fin 11 × Fin 11) (he : e ∈ matching) (hf : f ∈ matching) :
      e ≠ f → e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
    change e ∈ ({(1, 4), (2, 5), (6, 7)} : Finset (Fin 11 × Fin 11)) at he
    change f ∈ ({(1, 4), (2, 5), (6, 7)} : Finset (Fin 11 × Fin 11)) at hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at he hf
    rcases he with rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl <;> decide
  let D := E.image pick
  have hD_C : D ⊆ C := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    by_cases hp : e.1 ∈ C
    · simp [pick, hp]
    · simpa [pick, hp] using (cover (Finset.mem_filter.mp he).2.1).resolve_left hp
  have hD_out {v : Fin 11} (hv : v ∈ D) : v ∉ S ∧ v ∉ B := by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hm, _, h₁, h₂⟩ := Finset.mem_filter.mp he
    obtain ⟨hs₁, hs₂⟩ := ends e hm
    rcases picked e with hp | hp
    · rw [hp]; exact ⟨hs₁, h₁⟩
    · rw [hp]; exact ⟨hs₂, h₂⟩
  have hD_card : D.card = E.card := by
    apply Finset.card_image_of_injOn
    intro e he f hf hp
    by_contra hne
    obtain ⟨h₁, h₂, h₃, h₄⟩ := distinct e f (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 hne
    rcases picked e with ha | ha <;> rcases picked f with hb | hb <;> rw [ha, hb] at hp
    · exact h₁ hp
    · exact h₂ hp
    · exact h₃ hp
    · exact h₄ hp
  have select {u v : Fin 11} (hm : (u,v) ∈ matching) (hadj : G.Adj u v) :
      u ∈ B ∨ v ∈ B ∨ u ∈ D ∨ v ∈ D := by
    by_cases hu : u ∈ B
    · exact Or.inl hu
    by_cases hv : v ∈ B
    · exact Or.inr (Or.inl hv)
    have hpair : (u,v) ∈ E := Finset.mem_filter.mpr ⟨hm, hadj, hu, hv⟩
    have hp : pick (u,v) ∈ D := Finset.mem_image_of_mem _ hpair
    rcases picked (u,v) with he | he
    · change pick (u,v) = u at he
      rw [he] at hp
      exact Or.inr (Or.inr (Or.inl hp))
    · change pick (u,v) = v at he
      rw [he] at hp
      exact Or.inr (Or.inr (Or.inr hp))
  let C' := (A ∪ B) ∪ D
  have hC' : G.IsVertexCover (C' : Set (Fin 11)) := by
    intro u v huv
    change u ∈ C' ∨ v ∈ C'
    by_cases hu : u ∈ A
    · exact Or.inl (by simp [C', hu])
    by_cases hv : v ∈ A
    · exact Or.inr (by simp [C', hv])
    by_cases huS : u ∈ S
    · by_cases hvS : v ∈ S
      · exact (independent u (Finset.mem_sdiff.mpr ⟨huS, hu⟩)
          v (Finset.mem_sdiff.mpr ⟨hvS, hv⟩) huv).elim
      · have hb := force huS hu hvS huv
        exact Or.inr (by simp [C', hb])
    by_cases hvS : v ∈ S
    · have hb := force hvS hv huS huv.symm
      exact Or.inl (by simp [C', hb])
    rcases hedge u v huv with h | h | h | h
    · exact (huS h).elim
    · exact (hvS h).elim
    · rcases select h huv with hp | hp | hp | hp
      · exact Or.inl (by simp [C', hp])
      · exact Or.inr (by simp [C', hp])
      · exact Or.inl (by simp [C', hp])
      · exact Or.inr (by simp [C', hp])
    · rcases select h huv.symm with hp | hp | hp | hp
      · exact Or.inr (by simp [C', hp])
      · exact Or.inl (by simp [C', hp])
      · exact Or.inr (by simp [C', hp])
      · exact Or.inl (by simp [C', hp])
  have hsub : C' ⊆ C := Finset.union_subset (Finset.union_subset hA_C hB_C) hD_C
  have hAB : Disjoint A B := Finset.disjoint_left.mpr (fun _ ha hb => hB_out hb (hA ha))
  have hABD : Disjoint (A ∪ B) D := by
    apply Finset.disjoint_left.mpr
    intro v hv hd
    rcases Finset.mem_union.mp hv with ha | hb
    · exact (hD_out hd).1 (hA ha)
    · exact (hD_out hd).2 hb
  refine ⟨A, hA, independent, ?_⟩
  change C.card = A.card + B.card + E.card
  have heq : C.card = C'.card := Nat.le_antisymm (hC.2 C' hC') (Finset.card_le_card hsub)
  rw [heq]
  change ((A ∪ B) ∪ D).card = _
  rw [Finset.card_union_of_disjoint hABD, Finset.card_union_of_disjoint hAB, hD_card]
