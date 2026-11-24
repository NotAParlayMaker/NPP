import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3765

def gstep (k : Fin 4) (A B : Finset ℕ) (c : Bool) : Finset ℕ :=
  match k with
  | 0 => A ∪ B
  | 1 => A ∪ A
  | 2 => ∅
  | _ => if c = true then A else B

def ev (x1 x2 : ℕ) (L R : Fin x2 → ℕ) (hL : ∀ j : Fin x2, L j < x1 + j)
    (hR : ∀ j : Fin x2, R j < x1 + j) (k : Fin x2 → Fin 4) (b : Fin x2 → Bool) (w : ℕ) :
    Finset ℕ :=
  if _hw : w < x1 then {w} else
  if h : w - x1 < x2 then
    gstep (k ⟨w - x1, h⟩) (ev x1 x2 L R hL hR k b (L ⟨w - x1, h⟩))
      (ev x1 x2 L R hL hR k b (R ⟨w - x1, h⟩)) (b ⟨w - x1, h⟩)
  else ∅
termination_by w
decreasing_by
  · have := hL ⟨w - x1, h⟩
    simp only at this
    omega
  · have := hR ⟨w - x1, h⟩
    simp only at this
    omega

theorem ev_in (x1 x2 : ℕ) (L R : Fin x2 → ℕ) (hL : ∀ j : Fin x2, L j < x1 + j)
    (hR : ∀ j : Fin x2, R j < x1 + j) (k : Fin x2 → Fin 4) (b : Fin x2 → Bool) (w : ℕ)
    (hw : w < x1) : ev x1 x2 L R hL hR k b w = {w} := by
  rw [ev, dif_pos hw]

theorem ev_gate (x1 x2 : ℕ) (L R : Fin x2 → ℕ) (hL : ∀ j : Fin x2, L j < x1 + j)
    (hR : ∀ j : Fin x2, R j < x1 + j) (k : Fin x2 → Fin 4) (b : Fin x2 → Bool) (j : Fin x2) :
    ev x1 x2 L R hL hR k b (x1 + j) =
      gstep (k j) (ev x1 x2 L R hL hR k b (L j)) (ev x1 x2 L R hL hR k b (R j)) (b j) := by
  rw [ev, dif_neg (by omega), dif_pos (by simp)]
  have e : (⟨x1 + ↑j - x1, by simp⟩ : Fin x2) = j := Fin.ext (by simp)
  simp only [Nat.add_sub_cancel_left]

end PEqualNP.Outside.L_meta_3765

theorem PEqualNP.Outside.L_meta_3765 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set (Finset ℕ)), x3 < x1 + x2 → (∀ x6 < x1, x4 x6 = {{x6}}) → (∀ x7 < x2, ∃ x9 < x1 + x7, ∃ x10 < x1 + x7, x4 (x1 + x7) = Set.image2 (fun (x11 x12 : Finset ℕ) => x11 ∪ x12) (x4 x9) (x4 x10) ∨ x4 (x1 + x7) = x4 x9 ∨ x4 (x1 + x7) = {∅} ∨ x4 (x1 + x7) = x4 x9 ∪ x4 x10) → ∃ (x8 : (Fin x2 → Bool) → ℕ → Finset ℕ), (∀ (x9 : Fin x2 → Bool), ∀ x10 < x1, x8 x9 x10 = {x10}) ∧ (∀ (x9 : Fin x2), ∃ x10 < x1 + ↑x9, ∃ x11 < x1 + ↑x9, (∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = x8 x12 x10 ∪ x8 x12 x11) ∨ (∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = if x12 x9 = Bool.true then x8 x12 x10 else x8 x12 x11) ∨ ∀ (x12 : Fin x2 → Bool), x8 x12 (x1 + ↑x9) = ∅) ∧ (∀ (x9 : Fin x2 → Bool), x8 x9 x3 ∈ x4 x3) ∧ ∀ x9 ∈ x4 x3, ∃ (x11 : Fin x2 → Bool), x8 x11 x3 ⊆ x9 := by
  intro x1 x2 x3 x4 hx3 hin hg
  have H : ∀ j : Fin x2, ∃ p : ℕ × ℕ × Fin 4, p.1 < x1 + j ∧ p.2.1 < x1 + j ∧
      ((p.2.2 = 0 ∧ x4 (x1 + j) = Set.image2 (fun (a c : Finset ℕ) => a ∪ c) (x4 p.1) (x4 p.2.1)) ∨
       (p.2.2 = 1 ∧ x4 (x1 + j) = x4 p.1) ∨
       (p.2.2 = 2 ∧ x4 (x1 + j) = {∅}) ∨
       (p.2.2 = 3 ∧ x4 (x1 + j) = x4 p.1 ∪ x4 p.2.1)) := by
    intro j
    obtain ⟨a, ha, c, hc, h⟩ := hg j j.isLt
    rcases h with h | h | h | h
    · exact ⟨(a, c, 0), ha, hc, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨(a, c, 1), ha, hc, Or.inr (Or.inl ⟨rfl, h⟩)⟩
    · exact ⟨(a, c, 2), ha, hc, Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))⟩
    · exact ⟨(a, c, 3), ha, hc, Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))⟩
  choose f hfL hfR hf using H
  set L : Fin x2 → ℕ := fun j => (f j).1 with hLdef
  set R : Fin x2 → ℕ := fun j => (f j).2.1 with hRdef
  set k : Fin x2 → Fin 4 := fun j => (f j).2.2 with hkdef
  have hL : ∀ j : Fin x2, L j < x1 + j := hfL
  have hR : ∀ j : Fin x2, R j < x1 + j := hfR
  have hcase : ∀ j : Fin x2,
      (k j = 0 ∧ x4 (x1 + j) = Set.image2 (fun (a c : Finset ℕ) => a ∪ c) (x4 (L j)) (x4 (R j))) ∨
      (k j = 1 ∧ x4 (x1 + j) = x4 (L j)) ∨
      (k j = 2 ∧ x4 (x1 + j) = {∅}) ∨
      (k j = 3 ∧ x4 (x1 + j) = x4 (L j) ∪ x4 (R j)) := hf
  let E := PEqualNP.Outside.L_meta_3765.ev x1 x2 L R hL hR k
  have split : ∀ w, x1 ≤ w → w < x1 + x2 → ∃ j : Fin x2, w = x1 + j := by
    intro w h1 h2
    exact ⟨⟨w - x1, by omega⟩, by simp; omega⟩
  have mem : ∀ w, w < x1 + x2 → ∀ b, E b w ∈ x4 w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw b
      by_cases h1 : w < x1
      · rw [show E b w = {w} from PEqualNP.Outside.L_meta_3765.ev_in _ _ _ _ _ _ _ _ _ h1, hin w h1]
        rfl
      · obtain ⟨j, rfl⟩ := split w (by omega) hw
        have eg := PEqualNP.Outside.L_meta_3765.ev_gate x1 x2 L R hL hR k b j
        have iL := ih (L j) (hL j) (by have := hL j; omega) b
        have iR := ih (R j) (hR j) (by have := hR j; omega) b
        show E b (x1 + j) ∈ x4 (x1 + j)
        rw [show E b (x1 + j) = _ from eg]
        rcases hcase j with ⟨hk, hx⟩ | ⟨hk, hx⟩ | ⟨hk, hx⟩ | ⟨hk, hx⟩
        · rw [hk, hx]
          exact Set.mem_image2_of_mem iL iR
        · rw [hk, hx]
          simpa [PEqualNP.Outside.L_meta_3765.gstep] using iL
        · rw [hk, hx]
          simp [PEqualNP.Outside.L_meta_3765.gstep]
        · rw [hk, hx]
          simp only [PEqualNP.Outside.L_meta_3765.gstep]
          split_ifs
          · exact Or.inl iL
          · exact Or.inr iR
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro b w hw
    exact PEqualNP.Outside.L_meta_3765.ev_in _ _ _ _ _ _ _ _ _ hw
  · intro j
    have eg := fun b => PEqualNP.Outside.L_meta_3765.ev_gate x1 x2 L R hL hR k b j
    rcases hcase j with ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩
    · refine ⟨L j, hL j, R j, hR j, Or.inl ?_⟩
      intro b
      rw [show E b (x1 + j) = _ from eg b, hk]
      rfl
    · refine ⟨L j, hL j, L j, hL j, Or.inl ?_⟩
      intro b
      rw [show E b (x1 + j) = _ from eg b, hk]
      rfl
    · refine ⟨L j, hL j, R j, hR j, Or.inr (Or.inr ?_)⟩
      intro b
      rw [show E b (x1 + j) = _ from eg b, hk]
      rfl
    · refine ⟨L j, hL j, R j, hR j, Or.inr (Or.inl ?_)⟩
      intro b
      rw [show E b (x1 + j) = _ from eg b, hk]
      rfl
  · intro b
    exact mem x3 hx3 b
  · intro S hS
    let val : ℕ → Prop := fun w => ∃ T ∈ x4 w, T ⊆ S
    let b : Fin x2 → Bool := fun j => @decide (val (L j)) (Classical.propDecidable _)
    have key : ∀ w, w < x1 + x2 → val w → E b w ⊆ S := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hv
        obtain ⟨T, hT, hTS⟩ := hv
        by_cases h1 : w < x1
        · rw [show E b w = {w} from PEqualNP.Outside.L_meta_3765.ev_in _ _ _ _ _ _ _ _ _ h1]
          rw [hin w h1] at hT
          rw [Set.mem_singleton_iff] at hT
          rw [← hT]
          exact hTS
        · obtain ⟨j, rfl⟩ := split w (by omega) hw
          have eg := PEqualNP.Outside.L_meta_3765.ev_gate x1 x2 L R hL hR k b j
          have iL := ih (L j) (hL j) (by have := hL j; omega)
          have iR := ih (R j) (hR j) (by have := hR j; omega)
          show E b (x1 + j) ⊆ S
          rw [show E b (x1 + j) = _ from eg]
          rcases hcase j with ⟨hk, hx⟩ | ⟨hk, hx⟩ | ⟨hk, hx⟩ | ⟨hk, hx⟩
          · rw [hx] at hT
            obtain ⟨A, hA, B, hB, rfl⟩ := hT
            rw [hk]
            exact Finset.union_subset (iL ⟨A, hA, fun _ h => hTS (Finset.mem_union_left _ h)⟩)
              (iR ⟨B, hB, fun _ h => hTS (Finset.mem_union_right _ h)⟩)
          · rw [hx] at hT
            rw [hk]
            have := iL ⟨T, hT, hTS⟩
            simpa [PEqualNP.Outside.L_meta_3765.gstep] using this
          · rw [hk]
            simp [PEqualNP.Outside.L_meta_3765.gstep]
          · rw [hx] at hT
            rw [hk]
            simp only [PEqualNP.Outside.L_meta_3765.gstep]
            by_cases hv : val (L j)
            · have hb : b j = true := by
                simp only [b]
                exact (@decide_eq_true_iff _ (Classical.propDecidable _)).2 hv
              rw [if_pos hb]
              exact iL hv
            · have hb : ¬ b j = true := by
                simp only [b]
                intro hc
                exact hv ((@decide_eq_true_iff _ (Classical.propDecidable _)).1 hc)
              rw [if_neg hb]
              rcases hT with hT | hT
              · exact absurd ⟨T, hT, hTS⟩ hv
              · exact iR ⟨T, hT, hTS⟩
    exact ⟨b, key x3 hx3 ⟨S, hS, le_refl S⟩⟩
