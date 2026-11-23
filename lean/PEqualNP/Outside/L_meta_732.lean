import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_732

def eList : List (Nat × Nat) :=
  [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
    (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)]

def dList : List (Nat × Nat) :=
  [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
    (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]

abbrev E0 (u v : Fin 8) : Prop :=
  (u.val, v.val) ∈ eList ∨ (v.val, u.val) ∈ eList

abbrev D0 (u v : Fin 8) : Prop :=
  (u.val, v.val) ∈ dList

lemma edge_iff : ∀ u v : Fin 8, E0 u v ↔ (D0 u v ∨ D0 v u) := by
  decide

lemma orient_asym : ∀ u v : Fin 8, D0 u v → ¬ D0 v u := by
  decide

lemma fin8_forall {P : Fin 8 → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) : ∀ k : Fin 8, P k := by
  rintro ⟨k, hk⟩
  match k with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | 5 => exact h5
  | 6 => exact h6
  | 7 => exact h7
  | _ + 8 => omega

lemma witness_of_subset (W K : Set (Fin 8))
    (hW : ∀ u ∈ W, ∀ v ∈ W, ¬ E0 u v)
    (S : List (Fin 8)) (a b : Fin 8)
    (hKsub : ∀ k ∈ K, k ∈ S)
    (hcheck : E0 a b ∧ S.elem a = false ∧ S.elem b = false ∧
      S.all (fun k => !decide (D0 a k)) = true ∧
      S.all (fun k => !decide (D0 b k)) = true) :
    ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D0 v k := by
  rcases hcheck with ⟨hab, haS, hbS, haD, hbD⟩
  have haM : a ∉ S := fun h => by
    have ht := List.elem_eq_true_of_mem h
    rw [haS] at ht
    cases ht
  have hbM : b ∉ S := fun h => by
    have ht := List.elem_eq_true_of_mem h
    rw [hbS] at ht
    cases ht
  by_cases haW : a ∈ W
  · refine ⟨b, fun hbW => hW a haW b hbW hab, fun h => hbM (hKsub b h), fun k hk => ?_⟩
    have hdk := List.all_eq_true.mp hbD k (hKsub k hk)
    simpa using hdk
  · refine ⟨a, haW, fun h => haM (hKsub a h), fun k hk => ?_⟩
    have hdk := List.all_eq_true.mp haD k (hKsub k hk)
    simpa using hdk

lemma no_kernel (W K : Set (Fin 8))
    (hW : ∀ u ∈ W, ∀ v ∈ W, ¬ E0 u v)
    (hK : ∀ u ∈ K, ∀ v ∈ K, ¬ E0 u v) :
    ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D0 v k := by
  have ne : ∀ {u v : Fin 8}, u ∈ K → E0 u v → v ∉ K :=
    fun hu huv hv => hK _ hu _ hv huv
  by_cases h4 : (4 : Fin 8) ∈ K
  · refine witness_of_subset W K hW [4] 1 3 ?_ (by decide)
    refine fin8_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first
      | (intro _; decide)
      | (intro h; exact absurd h (ne h4 (by decide)))
  · by_cases h0 : (0 : Fin 8) ∈ K
    · by_cases h7 : (7 : Fin 8) ∈ K
      · refine witness_of_subset W K hW [0, 7] 2 4 ?_ (by decide)
        refine fin8_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        all_goals first
          | (intro _; decide)
          | (intro h; exact absurd h h4)
          | (intro h; exact absurd h (ne h0 (by decide)))
          | (intro h; exact absurd h (ne h7 (by decide)))
      · refine witness_of_subset W K hW [0, 2] 3 4 ?_ (by decide)
        refine fin8_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        all_goals first
          | (intro _; decide)
          | (intro h; exact absurd h h4)
          | (intro h; exact absurd h h7)
          | (intro h; exact absurd h (ne h0 (by decide)))
    · by_cases h1 : (1 : Fin 8) ∈ K
      · by_cases h7 : (7 : Fin 8) ∈ K
        · refine witness_of_subset W K hW [1, 7] 0 6 ?_ (by decide)
          refine fin8_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          all_goals first
            | (intro _; decide)
            | (intro h; exact absurd h h4)
            | (intro h; exact absurd h h0)
            | (intro h; exact absurd h (ne h1 (by decide)))
            | (intro h; exact absurd h (ne h7 (by decide)))
        · refine witness_of_subset W K hW [1, 2, 5] 0 6 ?_ (by decide)
          refine fin8_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          all_goals first
            | (intro _; decide)
            | (intro h; exact absurd h h4)
            | (intro h; exact absurd h h0)
            | (intro h; exact absurd h h7)
            | (intro h; exact absurd h (ne h1 (by decide)))
      · by_cases h3 : (3 : Fin 8) ∈ K
        · by_cases h6 : (6 : Fin 8) ∈ K
          · refine witness_of_subset W K hW [3, 6] 5 7 ?_ (by decide)
            refine fin8_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            all_goals first
              | (intro _; decide)
              | (intro h; exact absurd h h4)
              | (intro h; exact absurd h h0)
              | (intro h; exact absurd h h1)
              | (intro h; exact absurd h (ne h3 (by decide)))
              | (intro h; exact absurd h (ne h6 (by decide)))
          · refine witness_of_subset W K hW [2, 3] 1 6 ?_ (by decide)
            refine fin8_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
            all_goals first
              | (intro _; decide)
              | (intro h; exact absurd h h4)
              | (intro h; exact absurd h h0)
              | (intro h; exact absurd h h1)
              | (intro h; exact absurd h h6)
              | (intro h; exact absurd h (ne h3 (by decide)))
        · by_cases h6 : (6 : Fin 8) ∈ K
          · by_cases h7 : (7 : Fin 8) ∈ K
            · refine witness_of_subset W K hW [6, 7] 0 4 ?_ (by decide)
              refine fin8_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
              all_goals first
                | (intro _; decide)
                | (intro h; exact absurd h h4)
                | (intro h; exact absurd h h0)
                | (intro h; exact absurd h h1)
                | (intro h; exact absurd h h3)
                | (intro h; exact absurd h (ne h6 (by decide)))
                | (intro h; exact absurd h (ne h7 (by decide)))
            · refine witness_of_subset W K hW [5, 6] 0 4 ?_ (by decide)
              refine fin8_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
              all_goals first
                | (intro _; decide)
                | (intro h; exact absurd h h4)
                | (intro h; exact absurd h h0)
                | (intro h; exact absurd h h1)
                | (intro h; exact absurd h h3)
                | (intro h; exact absurd h h7)
                | (intro h; exact absurd h (ne h6 (by decide)))
          · by_cases h7 : (7 : Fin 8) ∈ K
            · refine witness_of_subset W K hW [1, 7] 0 6 ?_ (by decide)
              refine fin8_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
              all_goals first
                | (intro _; decide)
                | (intro h; exact absurd h h4)
                | (intro h; exact absurd h h0)
                | (intro h; exact absurd h h1)
                | (intro h; exact absurd h h3)
                | (intro h; exact absurd h h6)
                | (intro h; exact absurd h (ne h7 (by decide)))
            · refine witness_of_subset W K hW [1, 2, 5] 0 6 ?_ (by decide)
              refine fin8_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
              all_goals first
                | (intro _; decide)
                | (intro h; exact absurd h h4)
                | (intro h; exact absurd h h0)
                | (intro h; exact absurd h h1)
                | (intro h; exact absurd h h3)
                | (intro h; exact absurd h h6)
                | (intro h; exact absurd h h7)

end PEqualNP.Outside.L_meta_732

theorem PEqualNP.Outside.L_meta_732 :
∀ (E D : Fin 8 → Fin 8 → Prop),
  (∀ u v, E u v ↔ ((u.val, v.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
      (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)] ∨
    (v.val, u.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
      (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)])) →
  (∀ u v, D u v ↔ (u.val, v.val) ∈ [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
      (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]) →
  (∀ u v, E u v ↔ (D u v ∨ D v u)) ∧ (∀ u v, D u v → ¬ D v u) ∧
  ∀ W K : Set (Fin 8),
    (∀ u ∈ W, ∀ v ∈ W, ¬ E u v) → Disjoint K W → (∀ u ∈ K, ∀ v ∈ K, ¬ E u v) →
    ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D v k := by
  intro E D hE hD
  have hE' : ∀ u v, E u v ↔ PEqualNP.Outside.L_meta_732.E0 u v := hE
  have hD' : ∀ u v, D u v ↔ PEqualNP.Outside.L_meta_732.D0 u v := hD
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    rw [hE' u v, hD' u v, hD' v u]
    exact PEqualNP.Outside.L_meta_732.edge_iff u v
  · intro u v h
    rw [hD' u v] at h
    rw [hD' v u]
    exact PEqualNP.Outside.L_meta_732.orient_asym u v h
  · intro W K hW _ hK
    have hW0 : ∀ u ∈ W, ∀ v ∈ W, ¬ PEqualNP.Outside.L_meta_732.E0 u v :=
      fun u hu v hv h => hW u hu v hv ((hE' u v).2 h)
    have hK0 : ∀ u ∈ K, ∀ v ∈ K, ¬ PEqualNP.Outside.L_meta_732.E0 u v :=
      fun u hu v hv h => hK u hu v hv ((hE' u v).2 h)
    obtain ⟨v, hvW, hvK, hvD⟩ := PEqualNP.Outside.L_meta_732.no_kernel W K hW0 hK0
    exact ⟨v, hvW, hvK, fun k hk h => hvD k hk ((hD' v k).1 h)⟩
