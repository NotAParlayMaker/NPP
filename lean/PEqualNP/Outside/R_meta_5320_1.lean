import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5320_1
    (card22 : ∀ (x1 : Finset ((Fin (9 : ℕ) → Bool) → Bool)),
      Relation.ReflTransGen (fun (x2 x3 : Finset ((Fin (9 : ℕ) → Bool) → Bool)) =>
        ∃ x4 ∈ x2, ∃ x5 ∈ x2,
          x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 && x5 x6) x2 ∨
          x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 || x5 x6) x2 ∨
          x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => !x4 x6) x2)
        (Insert.insert (fun (_ : Fin (9 : ℕ) → Bool) => Bool.false)
          (Insert.insert (fun (_ : Fin (9 : ℕ) → Bool) => Bool.true)
            (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => !x2 (0 : Fin (9 : ℕ)))
              (Finset.image (fun (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => x3 x2) Finset.univ)))) x1 →
      x1.card ≤ (26 : ℕ) →
      (Finset.image (fun (x4 : (Fin (9 : ℕ) → Bool) → Bool) (x5 : Fin (8 : ℕ) → Bool) => x4 (Fin.cons Bool.false x5)) x1).card = (22 : ℕ) →
      (fun (x5 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) ∉ x1)
    (card23 : ∀ (x1 : Finset ((Fin (9 : ℕ) → Bool) → Bool)),
      Relation.ReflTransGen (fun (x2 x3 : Finset ((Fin (9 : ℕ) → Bool) → Bool)) =>
        ∃ x4 ∈ x2, ∃ x5 ∈ x2,
          x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 && x5 x6) x2 ∨
          x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 || x5 x6) x2 ∨
          x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => !x4 x6) x2)
        (Insert.insert (fun (_ : Fin (9 : ℕ) → Bool) => Bool.false)
          (Insert.insert (fun (_ : Fin (9 : ℕ) → Bool) => Bool.true)
            (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => !x2 (0 : Fin (9 : ℕ)))
              (Finset.image (fun (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => x3 x2) Finset.univ)))) x1 →
      (25 : ℕ) ≤ x1.card → x1.card ≤ (26 : ℕ) →
      (Finset.image (fun (x4 : (Fin (9 : ℕ) → Bool) → Bool) (x5 : Fin (8 : ℕ) → Bool) => x4 (Fin.cons Bool.false x5)) x1).card = (23 : ℕ) →
      (fun (x5 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) ∉ x1)
    (card24 : ∀ (x1 : Finset ((Fin (9 : ℕ) → Bool) → Bool)),
      Relation.ReflTransGen (fun (x2 x3 : Finset ((Fin (9 : ℕ) → Bool) → Bool)) =>
        ∃ x4 ∈ x2, ∃ x5 ∈ x2,
          x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 && x5 x6) x2 ∨
          x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 || x5 x6) x2 ∨
          x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => !x4 x6) x2)
        (Insert.insert (fun (_ : Fin (9 : ℕ) → Bool) => Bool.false)
          (Insert.insert (fun (_ : Fin (9 : ℕ) → Bool) => Bool.true)
            (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => !x2 (0 : Fin (9 : ℕ)))
              (Finset.image (fun (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => x3 x2) Finset.univ)))) x1 →
      x1.card = (26 : ℕ) →
      (Finset.image (fun (x4 : (Fin (9 : ℕ) → Bool) → Bool) (x5 : Fin (8 : ℕ) → Bool) => x4 (Fin.cons Bool.false x5)) x1).card = (24 : ℕ) →
      (fun (x5 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) ∉ x1) :
    ∀ (x1 : Finset ((Fin (9 : ℕ) → Bool) → Bool)), Relation.ReflTransGen (fun (x2 x3 : Finset ((Fin (9 : ℕ) → Bool) → Bool)) => ∃ x4 ∈ x2, ∃ x5 ∈ x2, x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 && x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 || x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => !x4 x6) x2) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.false) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.true) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => !x2 (0 : Fin (9 : ℕ))) (Finset.image (fun (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => x3 x2) Finset.univ)))) x1 → x1.card ≤ (26 : ℕ) → (22 : ℕ) ≤ (Finset.image (fun (x4 : (Fin (9 : ℕ) → Bool) → Bool) (x5 : Fin (8 : ℕ) → Bool) => x4 (Fin.cons Bool.false x5)) x1).card → (fun (x5 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) ∉ x1 := by
  classical
  intro s hreach hcard hcut
  let BF := (Fin 9 → Bool) → Bool
  let cut (f : BF) (x : Fin 8 → Bool) : Bool := f (Fin.cons false x)
  let vars : Finset BF := Finset.univ.image (fun (i : Fin 9) (x : Fin 9 → Bool) => x i)
  let init : Finset BF := insert (fun _ => false) (insert (fun _ => true) (insert (fun x => !(x 0)) vars))
  have hsub_gen : ∀ {t : Finset BF},
      Relation.ReflTransGen (fun (x2 x3 : Finset BF) =>
        ∃ x4 ∈ x2, ∃ x5 ∈ x2,
          x3 = Insert.insert (fun (x6 : Fin 9 → Bool) => x4 x6 && x5 x6) x2 ∨
          x3 = Insert.insert (fun (x6 : Fin 9 → Bool) => x4 x6 || x5 x6) x2 ∨
          x3 = Insert.insert (fun (x6 : Fin 9 → Bool) => !x4 x6) x2) init t → init ⊆ t := by
    intro t ht
    induction ht with
    | refl => exact Finset.Subset.refl _
    | tail _ step prev =>
      obtain ⟨_, _, _, _, eq | eq | eq⟩ := step <;> rw [eq] <;> exact prev.trans (Finset.subset_insert ..)
  have hsub : init ⊆ s := hsub_gen hreach
  have hvars_inj : Function.Injective (fun (i : Fin 9) (x : Fin 9 → Bool) => x i) := by
    intro i j hij
    have h := congrFun hij (fun k => decide (k = i))
    have hji : j = i := by simpa using h.symm
    exact hji.symm
  have hvars_card : vars.card = 9 := by
    rw [Finset.card_image_of_injective _ hvars_inj]
    simp
  have hnot_mem : (fun x : Fin 9 → Bool => !(x 0)) ∉ vars := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    have h0 := congrFun hi (fun _ => false)
    simp at h0
  have htrue_not : (fun _ : Fin 9 → Bool => true) ∉ insert (fun x : Fin 9 → Bool => !(x 0)) vars := by
    intro h
    rcases Finset.mem_insert.mp h with h1 | h2
    · have := congrFun h1 (fun _ => true); simp at this
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h2
      have := congrFun hi (fun _ => false); simp at this
  have hfalse_not : (fun _ : Fin 9 → Bool => false) ∉ insert (fun _ : Fin 9 → Bool => true) (insert (fun x : Fin 9 → Bool => !(x 0)) vars) := by
    intro h
    rcases Finset.mem_insert.mp h with h1 | h2
    · have := congrFun h1 (fun _ => false); simp at this
    · rcases Finset.mem_insert.mp h2 with h3 | h4
      · have := congrFun h3 (fun _ => false); simp at this
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h4
        have := congrFun hi (fun _ => true); simp at this
  have hinit_card : init.card = 12 := by
    dsimp only [init]
    rw [Finset.card_insert_of_notMem hfalse_not, Finset.card_insert_of_notMem htrue_not,
      Finset.card_insert_of_notMem hnot_mem, hvars_card]
  have hinit_cut_sub : init.image cut ⊆
      insert (fun _ => false) (insert (fun _ => true) (Finset.univ.image (fun (i : Fin 8) (x : Fin 8 → Bool) => x i))) := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
    simp only [init, vars, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hg ⊢
    rcases hg with rfl | rfl | rfl | ⟨i, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl (by funext x; simp [cut]))
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact Or.inl (by funext x; simp [cut])
      · exact Or.inr (Or.inr ⟨j, by funext x; simp [cut]⟩)
  have hinit_cut_card : (init.image cut).card ≤ 10 := by
    have h1 := Finset.card_le_card hinit_cut_sub
    have h2 := Finset.card_insert_le (fun _ : Fin 8 → Bool => false)
      (insert (fun _ : Fin 8 → Bool => true) (Finset.univ.image (fun (i : Fin 8) (x : Fin 8 → Bool) => x i)))
    have h3 := Finset.card_insert_le (fun _ : Fin 8 → Bool => true)
      (Finset.univ.image (fun (i : Fin 8) (x : Fin 8 → Bool) => x i))
    have h4 : (Finset.univ.image (fun (i : Fin 8) (x : Fin 8 → Bool) => x i)).card ≤ 8 :=
      (Finset.card_image_le).trans (by simp)
    omega
  have hsplit : s = init ∪ (s \ init) := (Finset.union_sdiff_of_subset hsub).symm
  have hcut_le : (s.image cut).card + 2 ≤ s.card := by
    have himg : s.image cut = (init.image cut) ∪ ((s \ init).image cut) := by
      conv_lhs => rw [hsplit]
      exact Finset.image_union _ _
    have h1 : (s.image cut).card ≤ (init.image cut).card + ((s \ init).image cut).card := by
      rw [himg]; exact Finset.card_union_le _ _
    have h2 : ((s \ init).image cut).card ≤ (s \ init).card := Finset.card_image_le
    have h3 : (s \ init).card + init.card = s.card := Finset.card_sdiff_add_card_eq_card hsub
    omega
  change 22 ≤ (s.image cut).card at hcut
  have hle24 : (s.image cut).card ≤ 24 := by omega
  have hcases : (s.image cut).card = 22 ∨ (s.image cut).card = 23 ∨ (s.image cut).card = 24 := by omega
  rcases hcases with h22 | h23 | h24
  · exact card22 s hreach hcard h22
  · exact card23 s hreach (by omega) hcard h23
  · exact card24 s hreach (by omega) h24
