import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3574

private lemma card_image_comp_le_one {α : Type*} [DecidableEq α]
    (s : Finset α) (c : α → ℕ) (f : ℕ → ℕ) (h : (s.image c).card ≤ 1) :
    (s.image (fun x => f (c x))).card ≤ 1 := by
  have hcomp : s.image (fun x => f (c x)) = (s.image c).image f := by
    rw [Finset.image_image]
    rfl
  rw [hcomp]
  exact le_trans Finset.card_image_le h

private lemma merge_step {α : Type*} [DecidableEq α]
    (A x6 x7 : Finset α) (c : α → ℕ)
    (h6 : (x6.image c).card ≤ 1) (h7 : (x7.image c).card ≤ 1) :
    ∃ c' : α → ℕ,
      (A.image c).card ≤ (A.image c').card + 1 ∧
      ((x6 ∪ x7).image c').card ≤ 1 ∧
      ∀ Y : Finset α, (Y.image c).card ≤ 1 → (Y.image c').card ≤ 1 := by
  by_cases h6ne : x6.Nonempty
  · by_cases h7ne : x7.Nonempty
    · obtain ⟨a, ha⟩ := h6ne
      obtain ⟨b, hb⟩ := h7ne
      let v1 := c a
      let v2 := c b
      let f : ℕ → ℕ := fun v => if v = v2 then v1 else v
      refine ⟨fun x => f (c x), ?_, ?_, fun Y hY => card_image_comp_le_one Y c f hY⟩
      · have hsub : A.image c ⊆ insert v2 (A.image (fun x => f (c x))) := by
          intro y hy
          obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp hy
          by_cases hEq : c x = v2
          · rw [hEq]
            exact Finset.mem_insert_self v2 _
          · apply Finset.mem_insert_of_mem
            refine Finset.mem_image.mpr ⟨x, hxA, ?_⟩
            dsimp [f]
            simp [hEq]
        exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)
      · have hsub : (x6 ∪ x7).image (fun x => f (c x)) ⊆ {v1} := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          rw [Finset.mem_singleton]
          rcases Finset.mem_union.mp hx with hx6 | hx7
          · have hca : c x = v1 :=
              Finset.card_le_one.mp h6 (c x) (Finset.mem_image_of_mem c hx6)
                (c a) (Finset.mem_image_of_mem c ha)
            dsimp [f]
            rw [hca]
            split_ifs <;> rfl
          · have hcb : c x = v2 :=
              Finset.card_le_one.mp h7 (c x) (Finset.mem_image_of_mem c hx7)
                (c b) (Finset.mem_image_of_mem c hb)
            dsimp [f]
            simp [hcb]
        exact le_trans (Finset.card_le_card hsub) (by simp)
    · rw [Finset.not_nonempty_iff_eq_empty] at h7ne
      subst h7ne
      exact ⟨c, Nat.le_succ _, by simpa using h6, fun _ hY => hY⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at h6ne
    subst h6ne
    exact ⟨c, Nat.le_succ _, by simpa using h7, fun _ hY => hY⟩

private lemma exists_coloring (x1 : ℕ) (x2 : List (Finset (Fin x1)))
    (hstep : ∀ (x3 : ℕ) (x4 : Finset (Fin x1)), x2[x3]? = Option.some x4 →
      ∃ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x1)),
        x4 = x6 ∪ x7 ∧
        (x6.card ≤ 1 ∨ x6 ∈ List.take x3 x2) ∧
        (x7.card ≤ 1 ∨ x7 ∈ List.take x3 x2))
    (A : Finset (Fin x1)) :
    ∀ k ≤ x2.length,
      ∃ c : Fin x1 → ℕ,
        A.card ≤ (A.image c).card +
          (Finset.univ.filter fun i : Fin x2.length =>
            i.val < k ∧ 1 < (x2.get i).card ∧ x2.get i ⊆ A).card ∧
        ∀ B : Finset (Fin x1), (B.card ≤ 1 ∨ B ∈ List.take k x2) → B ⊆ A →
          (B.image c).card ≤ 1 := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨fun a => a.val, ?_, ?_⟩
    · rw [Finset.card_image_of_injective A Fin.val_injective]
      omega
    · intro B hB _
      rcases hB with hB1 | hBmem
      · exact le_trans Finset.card_image_le hB1
      · simp at hBmem
  | succ k ih =>
    have hklt : k < x2.length := Nat.lt_of_succ_le hk
    obtain ⟨c, hcard, hinv⟩ := ih (Nat.le_of_lt hklt)
    let fk : Fin x2.length := ⟨k, hklt⟩
    let B := x2[k]
    have htake : List.take (k + 1) x2 = List.take k x2 ++ [B] :=
      List.take_succ_eq_append_getElem hklt
    by_cases hB : 1 < B.card ∧ B ⊆ A
    · obtain ⟨x6, x7, hBeq, hx6, hx7⟩ := hstep k B (List.getElem?_eq_getElem hklt)
      have hx6_sub : x6 ⊆ A := le_trans (by rw [hBeq]; exact Finset.subset_union_left) hB.2
      have hx7_sub : x7 ⊆ A := le_trans (by rw [hBeq]; exact Finset.subset_union_right) hB.2
      have h6c : (x6.image c).card ≤ 1 := hinv x6 hx6 hx6_sub
      have h7c : (x7.image c).card ≤ 1 := hinv x7 hx7 hx7_sub
      obtain ⟨c', hAc', hBc', hpres⟩ := merge_step A x6 x7 c h6c h7c
      refine ⟨c', ?_, ?_⟩
      · let S1 := Finset.univ.filter fun i : Fin x2.length =>
          i.val < k ∧ 1 < (x2.get i).card ∧ x2.get i ⊆ A
        let S2 := Finset.univ.filter fun i : Fin x2.length =>
          i.val < k + 1 ∧ 1 < (x2.get i).card ∧ x2.get i ⊆ A
        have hfk_not : fk ∉ S1 := by
          simp [S1, fk]
        have hS2 : S2 = insert fk S1 := by
          ext i
          simp only [S1, S2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hlt, h1, hsub⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
            · exact Or.inr ⟨hlt', h1, hsub⟩
            · exact Or.inl (Fin.ext heq)
          · rintro (rfl | ⟨hlt', h1, hsub⟩)
            · exact ⟨Nat.lt_succ_self k, hB.1, hB.2⟩
            · exact ⟨Nat.lt_succ_of_lt hlt', h1, hsub⟩
        have hS2_card : S2.card = S1.card + 1 := by
          rw [hS2, Finset.card_insert_of_notMem hfk_not]
        change A.card ≤ (A.image c').card + S2.card
        change A.card ≤ (A.image c).card + S1.card at hcard
        omega
      · intro Y hY hYA
        rcases hY with hY1 | hYmem
        · exact le_trans Finset.card_image_le hY1
        · rw [htake, List.mem_append, List.mem_singleton] at hYmem
          rcases hYmem with hYold | rfl
          · exact hpres Y (hinv Y (Or.inr hYold) hYA)
          · rwa [hBeq]
    · refine ⟨c, ?_, ?_⟩
      · have hsub :
            (Finset.univ.filter fun i : Fin x2.length =>
              i.val < k ∧ 1 < (x2.get i).card ∧ x2.get i ⊆ A) ⊆
            (Finset.univ.filter fun i : Fin x2.length =>
              i.val < k + 1 ∧ 1 < (x2.get i).card ∧ x2.get i ⊆ A) := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact ⟨Nat.lt_succ_of_lt hi.1, hi.2.1, hi.2.2⟩
        have hle := Finset.card_le_card hsub
        omega
      · intro Y hY hYA
        rcases hY with hY1 | hYmem
        · exact le_trans Finset.card_image_le hY1
        · rw [htake, List.mem_append, List.mem_singleton] at hYmem
          rcases hYmem with hYold | rfl
          · exact hinv Y (Or.inr hYold) hYA
          · have hB1 : B.card ≤ 1 := by
              by_contra hgt
              exact hB ⟨Nat.lt_of_not_ge hgt, hYA⟩
            exact le_trans Finset.card_image_le hB1

end PEqualNP.Outside.L_meta_3574

theorem PEqualNP.Outside.L_meta_3574 : ∀ (x1 : ℕ) (x2 : List (Finset (Fin x1))), (∀ (x3 : ℕ) (x4 : Finset (Fin x1)), x2[x3]? = Option.some x4 → ∃ (x6 : Finset (Fin x1)) (x7 : Finset (Fin x1)), x4 = x6 ∪ x7 ∧ (x6.card ≤ (1 : ℕ) ∨ x6 ∈ List.take x3 x2) ∧ (x7.card ≤ (1 : ℕ) ∨ x7 ∈ List.take x3 x2)) → ∀ x4 ∈ x2, x4.card ≤ Fintype.card { x6 : Fin x2.length // (1 : ℕ) < (x2.get x6).card ∧ x2.get x6 ⊆ x4 } + (1 : ℕ) := by
  intro x1 x2 hstep x4 hx4
  obtain ⟨c, hcard, hinv⟩ := PEqualNP.Outside.L_meta_3574.exists_coloring x1 x2 hstep x4 x2.length le_rfl
  have hx4_take : x4 ∈ List.take x2.length x2 := by
    rwa [List.take_length]
  have hAc : (x4.image c).card ≤ 1 := hinv x4 (Or.inr hx4_take) Finset.Subset.rfl
  have hfilt :
      (Finset.univ.filter fun i : Fin x2.length =>
        i.val < x2.length ∧ 1 < (x2.get i).card ∧ x2.get i ⊆ x4) =
      (Finset.univ.filter fun i : Fin x2.length =>
        1 < (x2.get i).card ∧ x2.get i ⊆ x4) := by
    ext i
    simp
  rw [hfilt, ← Fintype.card_subtype] at hcard
  omega
