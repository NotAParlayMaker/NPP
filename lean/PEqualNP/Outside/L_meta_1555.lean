import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1555

def L0 (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

def B0 (t p : Fin 13) : Finset (Fin 13) :=
  match t.val, p.val with
  | 0, 0 => {4, 8}
  | 0, 1 => {8}
  | 0, 3 => {8}
  | 0, 9 => {8}
  | 1, 1 => {5}
  | 1, 2 => {5}
  | 1, 4 => {8}
  | 1, 10 => {5}
  | 2, 2 => {9}
  | 2, 3 => {8}
  | 2, 5 => {8}
  | 2, 11 => {8}
  | 3, 3 => {11}
  | 3, 4 => {11}
  | 3, 6 => {2}
  | 3, 12 => {11}
  | 4, 0 => {3, 12}
  | 4, 4 => {12}
  | 4, 5 => {12}
  | 4, 7 => {12}
  | 5, 1 => {7}
  | 5, 5 => {12}
  | 5, 6 => {7}
  | 5, 8 => {7}
  | 6, 2 => {4}
  | 6, 6 => {4}
  | 6, 7 => {3}
  | 6, 9 => {4}
  | 7, 3 => {12}
  | 7, 7 => {12}
  | 7, 8 => {6}
  | 7, 10 => {12}
  | 8, 4 => {10}
  | 8, 8 => {10}
  | 8, 9 => {10}
  | 8, 11 => {5}
  | 9, 5 => {6}
  | 9, 9 => {6}
  | 9, 10 => {1}
  | 9, 12 => {6}
  | 10, 0 => {1, 2}
  | 10, 6 => {1}
  | 10, 10 => {1}
  | 10, 11 => {1}
  | 11, 1 => {2}
  | 11, 7 => {2}
  | 11, 11 => {2}
  | 11, 12 => {9}
  | 12, 0 => {6, 9}
  | 12, 2 => {6}
  | 12, 8 => {6}
  | 12, 12 => {6}
  | _, _ => ∅

lemma part1 : ∀ t : Fin 13, ∀ p ∈ L0 t, B0 t p ∩ L0 t = ∅ ∧ (∀ v ∈ L0 t, decide (v = p ∨ v ∈ B0 t p) = true ↔ v = p) ∧
    (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L0 t ∧ b ∈ L0 t) ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B0 t p)) a = true ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B0 t p)) b = true) := by
  intro t
  fin_cases t <;> decide

lemma part2 : ∀ s s' : Fin 13, s ≠ 12 → s' ≠ 12 → s ≠ s' → ¬ ((∃ p ∈ L0 s \ L0 s', (B0 s p ∩ L0 s').Nonempty) ∧ (∃ p ∈ L0 s' \ L0 s, (B0 s' p ∩ L0 s).Nonempty)) := by
  intro s
  fin_cases s <;> decide

lemma part3 : ∀ s : Fin 13, s ≠ 12 → (((∃ p ∈ L0 12 \ L0 s, (B0 12 p ∩ L0 s).Nonempty) ∧ (∃ p ∈ L0 s \ L0 12, (B0 s p ∩ L0 12).Nonempty)) ↔ s = 3 ∨ s = 5) := by
  intro s
  fin_cases s <;> decide

lemma part4 :
    ((L0 3 \ L0 12).filter (fun p => (B0 3 p ∩ L0 12).Nonempty)) = {6} ∧
    ((L0 12 \ L0 3).filter (fun p => (B0 12 p ∩ L0 3).Nonempty)) = {0, 2, 8} ∧
    ((L0 5 \ L0 12).filter (fun p => (B0 5 p ∩ L0 12).Nonempty)) = {5} ∧
    ((L0 12 \ L0 5).filter (fun p => (B0 12 p ∩ L0 5).Nonempty)) = {0, 2, 12} := by
  decide

end PEqualNP.Outside.L_meta_1555

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
  have hLeq : L = PEqualNP.Outside.L_meta_1555.L0 := funext hL
  subst hLeq
  have hBeq : ∀ t : Fin 13, ∀ p ∈ PEqualNP.Outside.L_meta_1555.L0 t, B t p = PEqualNP.Outside.L_meta_1555.B0 t p := by
    intro t p hp
    fin_cases t <;> simp only [PEqualNP.Outside.L_meta_1555.L0, Finset.mem_insert, Finset.mem_singleton] at hp <;> rcases hp with rfl | rfl | rfl | rfl
    · exact h0.1
    · exact h0.2.1
    · exact h0.2.2.1
    · exact h0.2.2.2
    · exact h1.1
    · exact h1.2.1
    · exact h1.2.2.1
    · exact h1.2.2.2
    · exact h2.1
    · exact h2.2.1
    · exact h2.2.2.1
    · exact h2.2.2.2
    · exact h3.1
    · exact h3.2.1
    · exact h3.2.2.1
    · exact h3.2.2.2
    · exact h4.2.1
    · exact h4.2.2.1
    · exact h4.2.2.2
    · exact h4.1
    · exact h5.2.1
    · exact h5.2.2.1
    · exact h5.2.2.2
    · exact h5.1
    · exact h6.2.1
    · exact h6.2.2.1
    · exact h6.2.2.2
    · exact h6.1
    · exact h7.2.1
    · exact h7.2.2.1
    · exact h7.2.2.2
    · exact h7.1
    · exact h8.2.1
    · exact h8.2.2.1
    · exact h8.2.2.2
    · exact h8.1
    · exact h9.2.1
    · exact h9.2.2.1
    · exact h9.2.2.2
    · exact h9.1
    · exact h10.2.2.1
    · exact h10.2.2.2
    · exact h10.1
    · exact h10.2.1
    · exact h11.2.2.1
    · exact h11.2.2.2
    · exact h11.1
    · exact h11.2.1
    · exact h12.2.2.2
    · exact h12.1
    · exact h12.2.1
    · exact h12.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t p hp
    rw [hBeq t p hp]
    exact PEqualNP.Outside.L_meta_1555.part1 t p hp
  · intro s s' hs hs' hne
    have h := PEqualNP.Outside.L_meta_1555.part2 s s' hs hs' hne
    intro ⟨⟨p, hp, hne1⟩, ⟨q, hq, hne2⟩⟩
    apply h
    refine ⟨⟨p, hp, ?_⟩, ⟨q, hq, ?_⟩⟩
    · rwa [← hBeq s p (Finset.mem_sdiff.mp hp).1]
    · rwa [← hBeq s' q (Finset.mem_sdiff.mp hq).1]
  · intro s hs
    have h := PEqualNP.Outside.L_meta_1555.part3 s hs
    constructor
    · intro ⟨⟨p, hp, hne1⟩, ⟨q, hq, hne2⟩⟩
      apply h.mp
      refine ⟨⟨p, hp, ?_⟩, ⟨q, hq, ?_⟩⟩
      · rwa [← hBeq 12 p (Finset.mem_sdiff.mp hp).1]
      · rwa [← hBeq s q (Finset.mem_sdiff.mp hq).1]
    · intro hs35
      obtain ⟨⟨p, hp, hne1⟩, ⟨q, hq, hne2⟩⟩ := h.mpr hs35
      refine ⟨⟨p, hp, ?_⟩, ⟨q, hq, ?_⟩⟩
      · rwa [hBeq 12 p (Finset.mem_sdiff.mp hp).1]
      · rwa [hBeq s q (Finset.mem_sdiff.mp hq).1]
  · convert PEqualNP.Outside.L_meta_1555.part4.1 using 1
    apply Finset.filter_congr
    intro p hp
    rw [hBeq 3 p (Finset.mem_sdiff.mp hp).1]
  · convert PEqualNP.Outside.L_meta_1555.part4.2.1 using 1
    apply Finset.filter_congr
    intro p hp
    rw [hBeq 12 p (Finset.mem_sdiff.mp hp).1]
  · convert PEqualNP.Outside.L_meta_1555.part4.2.2.1 using 1
    apply Finset.filter_congr
    intro p hp
    rw [hBeq 5 p (Finset.mem_sdiff.mp hp).1]
  · convert PEqualNP.Outside.L_meta_1555.part4.2.2.2 using 1
    apply Finset.filter_congr
    intro p hp
    rw [hBeq 12 p (Finset.mem_sdiff.mp hp).1]
