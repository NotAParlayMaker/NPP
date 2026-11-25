import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4955_427
    (meet :
      let bits : List ℕ := [8193, 8194, 8200, 8704, 21233693, 3211303, 7340103, 23068749, 5275731, 22020181, 19923045, 18890857, 6357127, 6553741, 6324419, 6308041, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877]
      let src := (List.range 26).map fun k =>
        ((List.finRange 285).filter fun j =>
          (bits.getD ((j.val+1)/13) 0).testBit (k/13*13+(k+13-(j.val+1)%13)%13)).toFinset
      let T := ((List.finRange 285).filter fun j => decide (j.val < 51)).toFinset
      ∀ gs : List (Finset (Fin 285)), gs.length ≤ 60 →
        (∀ j : Fin gs.length, let P := src ++ gs.take j.val
          ∃ u ∈ P, ∃ v ∈ P, ¬ u ⊆ v ∧ ¬ v ⊆ u ∧ gs.get j ∉ P ∧
            (gs.get j = u ∩ v ∨ gs.get j = u ∪ v)) →
        let P := src ++ gs
        ∀ a ∈ P, ∀ u ∈ P, ∀ v ∈ P, T ⊂ a ∩ u → T ⊂ a ∩ v → T ⊂ u ∩ v →
          a ∩ (u ∩ v) ≠ T)
    (join :
      let bits : List ℕ := [8193, 8194, 8200, 8704, 21233693, 3211303, 7340103, 23068749, 5275731, 22020181, 19923045, 18890857, 6357127, 6553741, 6324419, 6308041, 4751635, 21496089, 17318185, 20988233, 21004625, 17891877]
      let src := (List.range 26).map fun k =>
        ((List.finRange 285).filter fun j =>
          (bits.getD ((j.val+1)/13) 0).testBit (k/13*13+(k+13-(j.val+1)%13)%13)).toFinset
      let T := ((List.finRange 285).filter fun j => decide (j.val < 51)).toFinset
      ∀ gs : List (Finset (Fin 285)), gs.length ≤ 60 →
        (∀ j : Fin gs.length, let P := src ++ gs.take j.val
          ∃ u ∈ P, ∃ v ∈ P, ¬ u ⊆ v ∧ ¬ v ⊆ u ∧ gs.get j ∉ P ∧
            (gs.get j = u ∩ v ∨ gs.get j = u ∪ v)) →
        let P := src ++ gs
        ∀ a ∈ P, ∀ u ∈ P, ∀ v ∈ P, ¬ T ⊂ u → ¬ T ⊂ v → ¬ u ⊆ v → ¬ v ⊆ u →
          ¬ a ⊆ u ∪ v → ¬ u ∪ v ⊆ a → (a ∩ u) ∪ (a ∩ v) ≠ T) :
    (have x1 : List ℕ := [(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ), (21233693 : ℕ), (3211303 : ℕ), (7340103 : ℕ), (23068749 : ℕ), (5275731 : ℕ), (22020181 : ℕ), (19923045 : ℕ), (18890857 : ℕ), (6357127 : ℕ), (6553741 : ℕ), (6324419 : ℕ), (6308041 : ℕ), (4751635 : ℕ), (21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)]; have x2 : List (Finset (Fin (285 : ℕ))) := List.map (fun (x2 : ℕ) => (List.filter (fun (x3 : Fin (285 : ℕ)) => (x1.getD ((↑x3 + (1 : ℕ)) / (13 : ℕ)) (0 : ℕ)).testBit (x2 / (13 : ℕ) * (13 : ℕ) + (x2 + (13 : ℕ) - (↑x3 + (1 : ℕ)) % (13 : ℕ)) % (13 : ℕ))) (List.finRange (285 : ℕ))).toFinset) (List.range (26 : ℕ)); ∀ (x3 : List (Finset (Fin (285 : ℕ)))),   x3.length ≤ (61 : ℕ) →     (∀ (x5 : Fin x3.length),         have x6 : List (Finset (Fin (285 : ℕ))) := x2 ++ List.take (↑x5) x3;         ∃ x7 ∈ x6, ∃ x8 ∈ x6, ¬x7 ⊆ x8 ∧ ¬x8 ⊆ x7 ∧ x3.get x5 ∉ x6 ∧ (x3.get x5 = x7 ∩ x8 ∨ x3.get x5 = x7 ∪ x8)) →       ∀ x6 ∈ x2 ++ x3, ∀ x8 ∈ x2 ++ x3, ¬x6 ⊆ x8 → ¬x8 ⊆ x6 → x6 ∩ x8 ≠ (List.filter (fun (x12 : Fin (285 : ℕ)) => Decidable.decide (↑x12 < (51 : ℕ))) (List.finRange (285 : ℕ))).toFinset) := by
  classical
  intro bits src
  let T := ((List.finRange 285).filter fun j => decide (j.val < 51)).toFinset
  let ok (gs : List (Finset (Fin 285))) := ∀ j : Fin gs.length, let P := src ++ gs.take j.val
    ∃ u ∈ P, ∃ v ∈ P, ¬ u ⊆ v ∧ ¬ v ⊆ u ∧ gs.get j ∉ P ∧
      (gs.get j = u ∩ v ∨ gs.get j = u ∪ v)
  let safe (P : List (Finset (Fin 285))) := ∀ a ∈ P, ∀ b ∈ P,
    ¬ a ⊆ b → ¬ b ⊆ a → a ∩ b ≠ T
  have zero : (0 : Fin 285) ∈ T := by simp [T]
  have one : (1 : Fin 285) ∈ T := by simp [T]
  have separated : ∀ a ∈ src, ¬ ((0 : Fin 285) ∈ a ∧ (1 : Fin 285) ∈ a) := by
    intro a ha
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
    have hlt : k < 26 := List.mem_range.mp hk
    have check : ∀ i : Fin 26, ¬ ((8193 : ℕ).testBit (i.val / 13 * 13 + (i.val+13-1)%13) = true ∧
        (8193 : ℕ).testBit (i.val / 13 * 13 + (i.val+13-2)%13) = true) := by decide
    intro h
    apply check ⟨k,hlt⟩
    have p := (List.mem_filter.mp (List.mem_toFinset.mp h.1)).2
    have q := (List.mem_filter.mp (List.mem_toFinset.mp h.2)).2
    exact ⟨p,q⟩
  have main (gs : List (Finset (Fin 285))) : gs.length ≤ 61 → ok gs → safe (src ++ gs) := by
    induction gs using List.reverseRecOn with
    | nil =>
      intro _ _ a ha b _ _ _ eq
      simp only [List.append_nil] at ha
      rw [←eq] at zero one
      exact separated a ha ⟨(Finset.mem_inter.mp zero).1,(Finset.mem_inter.mp one).1⟩
    | append_singleton xs z ih =>
      intro budget legal
      have cost : xs.length ≤ 60 := by simp at budget; omega
      have prev : ok xs := by
        intro i
        have h := legal ⟨i.val,by simp⟩
        simpa [List.take_append_of_le_length (Nat.le_of_lt i.isLt), List.get_eq_getElem, i.isLt] using h
      have earlier := ih (by omega) prev
      have last := legal ⟨xs.length,by simp⟩
      change ∃ u ∈ src ++ (xs ++ [z]).take xs.length, ∃ v ∈ src ++ (xs ++ [z]).take xs.length,
        ¬u ⊆ v ∧ ¬v ⊆ u ∧ _ ∧ (_ = u ∩ v ∨ _ = u ∪ v) at last
      simp [List.get_eq_getElem] at last
      obtain ⟨u,hu,v,hv,huv,hvu,_,how⟩ := last
      replace hu : u ∈ src ++ xs := List.mem_append.mpr hu
      replace hv : v ∈ src ++ xs := List.mem_append.mpr hv
      have lastPair (a : Finset (Fin 285)) (ha : a ∈ src ++ xs)
          (haz : ¬a ⊆ z) (hza : ¬z ⊆ a) (eq : a ∩ z = T) : False := by
        have ta : T ⊂ a := by rw [←eq,Finset.ssubset_def]; exact ⟨Finset.inter_subset_left, fun h => haz (h.trans Finset.inter_subset_right)⟩
        have tz : T ⊂ z := by rw [←eq,Finset.ssubset_def]; exact ⟨Finset.inter_subset_right, fun h => hza (h.trans Finset.inter_subset_left)⟩
        have larger (w : Finset (Fin 285)) (hw : w ∈ src ++ xs) (tw : T ⊂ w) : T ⊂ a ∩ w := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_inter (Finset.ssubset_def.mp ta).1 (Finset.ssubset_def.mp tw).1,?_⟩
          intro e
          apply earlier a ha w hw _ _ e.symm
          · intro sub
            rw [Finset.inter_eq_left.mpr sub] at e
            exact (Finset.ssubset_iff_subset_ne.mp ta).2 e
          · intro sub
            rw [Finset.inter_eq_right.mpr sub] at e
            exact (Finset.ssubset_iff_subset_ne.mp tw).2 e
        rcases how with e | e
        · subst z
          exact meet xs cost prev a ha u hu v hv
            (larger u hu (Finset.ssubset_of_ssubset_of_subset tz Finset.inter_subset_left))
            (larger v hv (Finset.ssubset_of_ssubset_of_subset tz Finset.inter_subset_right)) tz eq
        · subst z
          have small (w : Finset (Fin 285)) (hw : w ∈ src ++ xs) (sub : w ⊆ u ∪ v) : ¬ T ⊂ w := by
            intro tw
            apply (Finset.ssubset_def.mp (larger w hw tw)).2
            rw [←eq]
            exact Finset.inter_subset_inter (fun _ h => h) sub
          apply join xs cost prev a ha u hu v hv (small u hu Finset.subset_union_left)
            (small v hv Finset.subset_union_right) huv hvu haz hza
          rwa [←Finset.inter_union_distrib_left]
      intro a ha b hb hab hba eq
      rw [←List.append_assoc,List.mem_append,List.mem_singleton] at ha hb
      rcases ha with ha | rfl <;> rcases hb with hb | rfl
      · exact earlier a ha b hb hab hba eq
      · exact lastPair a ha hab hba eq
      · exact lastPair b hb hba hab ((Finset.inter_comm _ _).trans eq)
      · exact hab (fun _ h => h)
  exact main
