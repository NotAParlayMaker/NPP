import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1555_aux

def Lc (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def T (t p : Fin 13) : Finset (Fin 13) :=
  match t.val, p.val with
  | 0, 0 => {4, 8} | 0, 1 => {8} | 0, 3 => {8} | 0, 9 => {8}
  | 1, 1 => {5} | 1, 2 => {5} | 1, 4 => {8} | 1, 10 => {5}
  | 2, 2 => {9} | 2, 3 => {8} | 2, 5 => {8} | 2, 11 => {8}
  | 3, 3 => {11} | 3, 4 => {11} | 3, 6 => {2} | 3, 12 => {11}
  | 4, 0 => {3, 12} | 4, 4 => {12} | 4, 5 => {12} | 4, 7 => {12}
  | 5, 1 => {7} | 5, 5 => {12} | 5, 6 => {7} | 5, 8 => {7}
  | 6, 2 => {4} | 6, 6 => {4} | 6, 7 => {3} | 6, 9 => {4}
  | 7, 3 => {12} | 7, 7 => {12} | 7, 8 => {6} | 7, 10 => {12}
  | 8, 4 => {10} | 8, 8 => {10} | 8, 9 => {10} | 8, 11 => {5}
  | 9, 5 => {6} | 9, 9 => {6} | 9, 10 => {1} | 9, 12 => {6}
  | 10, 0 => {1, 2} | 10, 6 => {1} | 10, 10 => {1} | 10, 11 => {1}
  | 11, 1 => {2} | 11, 7 => {2} | 11, 11 => {2} | 11, 12 => {9}
  | 12, 0 => {6, 9} | 12, 2 => {6} | 12, 8 => {6} | 12, 12 => {6}
  | _, _ => ∅

theorem q1 : ∀ t : Fin 13, ∀ p ∈ Lc t, T t p ∩ Lc t = ∅ ∧
    (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ Lc t ∧ b ∈ Lc t) ∧
      (a = p ∨ a ∈ T t p) ∧ (b = p ∨ b ∈ T t p)) := by
  decide

theorem q2 : ∀ s s' : Fin 13, s ≠ 12 → s' ≠ 12 → s ≠ s' →
    ¬ ((∃ p ∈ Lc s \ Lc s', (T s p ∩ Lc s').Nonempty) ∧ (∃ p ∈ Lc s' \ Lc s, (T s' p ∩ Lc s).Nonempty)) := by
  intro s s'
  fin_cases s <;> fin_cases s' <;> decide

theorem q3 : ∀ s : Fin 13, s ≠ 12 → (((∃ p ∈ Lc 12 \ Lc s, (T 12 p ∩ Lc s).Nonempty) ∧
    (∃ p ∈ Lc s \ Lc 12, (T s p ∩ Lc 12).Nonempty)) ↔ s = 3 ∨ s = 5) := by
  decide

theorem q4 : ((Lc 3 \ Lc 12).filter (fun p => (T 3 p ∩ Lc 12).Nonempty)) = {6} ∧
    ((Lc 12 \ Lc 3).filter (fun p => (T 12 p ∩ Lc 3).Nonempty)) = {0, 2, 8} ∧
    ((Lc 5 \ Lc 12).filter (fun p => (T 5 p ∩ Lc 12).Nonempty)) = {5} ∧
    ((Lc 12 \ Lc 5).filter (fun p => (T 12 p ∩ Lc 5).Nonempty)) = {0, 2, 12} := by
  decide

end PEqualNP.Outside.L_meta_1555_aux

open PEqualNP.Outside.L_meta_1555_aux in
theorem PEqualNP.Outside.L_meta_1555 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ B : Fin 13 → Fin 13 → Finset (Fin 13),
    (B 0 0 = {4, 8} ∧ B 0 1 = {8} ∧ B 0 3 = {8} ∧ B 0 9 = {8}) →
    (B 1 1 = {5} ∧ B 1 2 = {5} ∧ B 1 4 = {8} ∧ B 1 10 = {5}) →
    (B 2 2 = {9} ∧ B 2 3 = {8} ∧ B 2 5 = {8} ∧ B 2 11 = {8}) →
    (B 3 3 = {11} ∧ B 3 4 = {11} ∧ B 3 6 = {2} ∧ B 3 12 = {11}) →
    (B 4 0 = {3, 12} ∧ B 4 4 = {12} ∧ B 4 5 = {12} ∧ B 4 7 = {12}) →
    (B 5 1 = {7} ∧ B 5 5 = {12} ∧ B 5 6 = {7} ∧ B 5 8 = {7}) →
    (B 6 2 = {4} ∧ B 6 6 = {4} ∧ B 6 7 = {3} ∧ B 6 9 = {4}) →
    (B 7 3 = {12} ∧ B 7 7 = {12} ∧ B 7 8 = {6} ∧ B 7 10 = {12}) →
    (B 8 4 = {10} ∧ B 8 8 = {10} ∧ B 8 9 = {10} ∧ B 8 11 = {5}) →
    (B 9 5 = {6} ∧ B 9 9 = {6} ∧ B 9 10 = {1} ∧ B 9 12 = {6}) →
    (B 10 0 = {1, 2} ∧ B 10 6 = {1} ∧ B 10 10 = {1} ∧ B 10 11 = {1}) →
    (B 11 1 = {2} ∧ B 11 7 = {2} ∧ B 11 11 = {2} ∧ B 11 12 = {9}) →
    (B 12 0 = {6, 9} ∧ B 12 2 = {6} ∧ B 12 8 = {6} ∧ B 12 12 = {6}) →
    (∀ t : Fin 13, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ (∀ v ∈ L t, decide (v = p ∨ v ∈ B t p) = true ↔ v = p) ∧
      (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p)) a = true ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p)) b = true)) ∧
    (∀ s s' : Fin 13, s ≠ 12 → s' ≠ 12 → s ≠ s' → ¬ ((∃ p ∈ L s \ L s', (B s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B s' p ∩ L s).Nonempty))) ∧
    (∀ s : Fin 13, s ≠ 12 → (((∃ p ∈ L 12 \ L s, (B 12 p ∩ L s).Nonempty) ∧ (∃ p ∈ L s \ L 12, (B s p ∩ L 12).Nonempty)) ↔ s = 3 ∨ s = 5)) ∧
    ((L 3 \ L 12).filter (fun p => (B 3 p ∩ L 12).Nonempty)) = {6} ∧ ((L 12 \ L 3).filter (fun p => (B 12 p ∩ L 3).Nonempty)) = {0, 2, 8} ∧
    ((L 5 \ L 12).filter (fun p => (B 5 p ∩ L 12).Nonempty)) = {5} ∧ ((L 12 \ L 5).filter (fun p => (B 12 p ∩ L 5).Nonempty)) = {0, 2, 12} := by
  intro L hL B h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hLe : L = Lc := funext fun t => by rw [hL t]; rfl
  subst hLe
  have hBT : ∀ t p, p ∈ Lc t → B t p = T t p := by
    obtain ⟨a0_1, a0_2, a0_3, a0_4⟩ := h0
    obtain ⟨a1_1, a1_2, a1_3, a1_4⟩ := h1
    obtain ⟨a2_1, a2_2, a2_3, a2_4⟩ := h2
    obtain ⟨a3_1, a3_2, a3_3, a3_4⟩ := h3
    obtain ⟨a4_1, a4_2, a4_3, a4_4⟩ := h4
    obtain ⟨a5_1, a5_2, a5_3, a5_4⟩ := h5
    obtain ⟨a6_1, a6_2, a6_3, a6_4⟩ := h6
    obtain ⟨a7_1, a7_2, a7_3, a7_4⟩ := h7
    obtain ⟨a8_1, a8_2, a8_3, a8_4⟩ := h8
    obtain ⟨a9_1, a9_2, a9_3, a9_4⟩ := h9
    obtain ⟨a10_1, a10_2, a10_3, a10_4⟩ := h10
    obtain ⟨a11_1, a11_2, a11_3, a11_4⟩ := h11
    obtain ⟨a12_1, a12_2, a12_3, a12_4⟩ := h12
    intro t p hp
    fin_cases t <;> fin_cases p <;> first | exact absurd hp (by decide) | assumption
  have E : ∀ s s', ((∃ p ∈ Lc s \ Lc s', (B s p ∩ Lc s').Nonempty) ↔
      (∃ p ∈ Lc s \ Lc s', (T s p ∩ Lc s').Nonempty)) := by
    intro s s'
    constructor
    · rintro ⟨p, hp, hn⟩
      exact ⟨p, hp, by rwa [← hBT s p (Finset.mem_sdiff.1 hp).1]⟩
    · rintro ⟨p, hp, hn⟩
      exact ⟨p, hp, by rwa [hBT s p (Finset.mem_sdiff.1 hp).1]⟩
  have hF : ∀ s s', (Lc s \ Lc s').filter (fun p => (B s p ∩ Lc s').Nonempty) =
      (Lc s \ Lc s').filter (fun p => (T s p ∩ Lc s').Nonempty) := fun s s' =>
    Finset.filter_congr fun p hp => by rw [hBT s p (Finset.mem_sdiff.1 hp).1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t p hp
    obtain ⟨e, a, b, hab, ha, hb⟩ := q1 t p hp
    rw [hBT t p hp]
    refine ⟨e, ?_, a, b, hab, by simpa using ha, by simpa using hb⟩
    intro v hv
    simp only [decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact h
      · have hm := Finset.mem_inter.2 ⟨h, hv⟩
        rw [e] at hm
        simp at hm
    · exact Or.inl
  · intro s s' a b c
    rw [E, E]
    exact q2 s s' a b c
  · intro s hs
    rw [E, E]
    exact q3 s hs
  · rw [hF, hF, hF, hF]
    exact q4
