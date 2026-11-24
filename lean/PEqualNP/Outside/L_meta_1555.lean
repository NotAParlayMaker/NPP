import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1555

def L0 : Fin 13 → Finset (Fin 13) := fun t => {t, t + 1, t + 3, t + 9}

def B0 (t p : Fin 13) : Finset (Fin 13) :=
  if t = 0 then (if p = 0 then {4, 8} else {8})
  else if t = 1 then (if p = 4 then {8} else {5})
  else if t = 2 then (if p = 2 then {9} else {8})
  else if t = 3 then (if p = 6 then {2} else {11})
  else if t = 4 then (if p = 0 then {3, 12} else {12})
  else if t = 5 then (if p = 5 then {12} else {7})
  else if t = 6 then (if p = 7 then {3} else {4})
  else if t = 7 then (if p = 8 then {6} else {12})
  else if t = 8 then (if p = 11 then {5} else {10})
  else if t = 9 then (if p = 10 then {1} else {6})
  else if t = 10 then (if p = 0 then {1, 2} else {1})
  else if t = 11 then (if p = 12 then {9} else {2})
  else (if p = 0 then {6, 9} else {6})

theorem F1 : ∀ t : Fin 13, ∀ p ∈ L0 t, B0 t p ∩ L0 t = ∅ ∧ (∀ v ∈ L0 t, decide (v = p ∨ v ∈ B0 t p) = true ↔ v = p) ∧
      (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L0 t ∧ b ∈ L0 t) ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B0 t p)) a = true ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B0 t p)) b = true) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem F2 : ∀ s s' : Fin 13, s ≠ 12 → s' ≠ 12 → s ≠ s' → ¬ ((∃ p ∈ L0 s \ L0 s', (B0 s p ∩ L0 s').Nonempty) ∧ (∃ p ∈ L0 s' \ L0 s, (B0 s' p ∩ L0 s).Nonempty)) := by
  decide +kernel

theorem F3 : ∀ s : Fin 13, s ≠ 12 → (((∃ p ∈ L0 12 \ L0 s, (B0 12 p ∩ L0 s).Nonempty) ∧ (∃ p ∈ L0 s \ L0 12, (B0 s p ∩ L0 12).Nonempty)) ↔ s = 3 ∨ s = 5) := by
  decide +kernel

theorem F4 : ((L0 3 \ L0 12).filter (fun p => (B0 3 p ∩ L0 12).Nonempty)) = {6} ∧ ((L0 12 \ L0 3).filter (fun p => (B0 12 p ∩ L0 3).Nonempty)) = {0, 2, 8} ∧
    ((L0 5 \ L0 12).filter (fun p => (B0 5 p ∩ L0 12).Nonempty)) = {5} ∧ ((L0 12 \ L0 5).filter (fun p => (B0 12 p ∩ L0 5).Nonempty)) = {0, 2, 12} := by
  decide +kernel

theorem exC (B : Fin 13 → Fin 13 → Finset (Fin 13)) (hB : ∀ t, ∀ p ∈ L0 t, B t p = B0 t p) (s s' : Fin 13) :
    (∃ p ∈ L0 s \ L0 s', (B s p ∩ L0 s').Nonempty) ↔ (∃ p ∈ L0 s \ L0 s', (B0 s p ∩ L0 s').Nonempty) := by
  constructor
  · rintro ⟨p, hp, h⟩
    refine ⟨p, hp, ?_⟩
    rw [hB s p (Finset.mem_sdiff.1 hp).1] at h
    exact h
  · rintro ⟨p, hp, h⟩
    refine ⟨p, hp, ?_⟩
    rw [hB s p (Finset.mem_sdiff.1 hp).1]
    exact h

theorem filtC (B : Fin 13 → Fin 13 → Finset (Fin 13)) (hB : ∀ t, ∀ p ∈ L0 t, B t p = B0 t p) (s s' : Fin 13) :
    ((L0 s \ L0 s').filter (fun p => (B s p ∩ L0 s').Nonempty)) = ((L0 s \ L0 s').filter (fun p => (B0 s p ∩ L0 s').Nonempty)) := by
  apply Finset.filter_congr
  intro p hp
  rw [hB s p (Finset.mem_sdiff.1 hp).1]

theorem row (B : Fin 13 → Fin 13 → Finset (Fin 13)) {t a b c d : Fin 13} {x1 x2 x3 x4 : Finset (Fin 13)}
    (h : B t a = x1 ∧ B t b = x2 ∧ B t c = x3 ∧ B t d = x4)
    (hl : ∀ p ∈ L0 t, p = a ∨ p = b ∨ p = c ∨ p = d)
    (hx : x1 = B0 t a ∧ x2 = B0 t b ∧ x3 = B0 t c ∧ x4 = B0 t d) :
    ∀ p ∈ L0 t, B t p = B0 t p := by
  intro p hp
  rcases hl p hp with rfl | rfl | rfl | rfl
  exacts [h.1.trans hx.1, h.2.1.trans hx.2.1, h.2.2.1.trans hx.2.2.1, h.2.2.2.trans hx.2.2.2]

theorem key (B : Fin 13 → Fin 13 → Finset (Fin 13)) (hB : ∀ t, ∀ p ∈ L0 t, B t p = B0 t p) :
    (∀ t : Fin 13, ∀ p ∈ L0 t, B t p ∩ L0 t = ∅ ∧ (∀ v ∈ L0 t, decide (v = p ∨ v ∈ B t p) = true ↔ v = p) ∧
      (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L0 t ∧ b ∈ L0 t) ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p)) a = true ∧ (fun v : Fin 13 => decide (v = p ∨ v ∈ B t p)) b = true)) ∧
    (∀ s s' : Fin 13, s ≠ 12 → s' ≠ 12 → s ≠ s' → ¬ ((∃ p ∈ L0 s \ L0 s', (B s p ∩ L0 s').Nonempty) ∧ (∃ p ∈ L0 s' \ L0 s, (B s' p ∩ L0 s).Nonempty))) ∧
    (∀ s : Fin 13, s ≠ 12 → (((∃ p ∈ L0 12 \ L0 s, (B 12 p ∩ L0 s).Nonempty) ∧ (∃ p ∈ L0 s \ L0 12, (B s p ∩ L0 12).Nonempty)) ↔ s = 3 ∨ s = 5)) ∧
    ((L0 3 \ L0 12).filter (fun p => (B 3 p ∩ L0 12).Nonempty)) = {6} ∧ ((L0 12 \ L0 3).filter (fun p => (B 12 p ∩ L0 3).Nonempty)) = {0, 2, 8} ∧
    ((L0 5 \ L0 12).filter (fun p => (B 5 p ∩ L0 12).Nonempty)) = {5} ∧ ((L0 12 \ L0 5).filter (fun p => (B 12 p ∩ L0 5).Nonempty)) = {0, 2, 12} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t p hp
    rw [hB t p hp]
    exact F1 t p hp
  · intro s s' h1 h2 h3
    rw [exC B hB s s', exC B hB s' s]
    exact F2 s s' h1 h2 h3
  · intro s h
    rw [exC B hB 12 s, exC B hB s 12]
    exact F3 s h
  · exact (filtC B hB 3 12).trans F4.1
  · exact (filtC B hB 12 3).trans F4.2.1
  · exact (filtC B hB 5 12).trans F4.2.2.1
  · exact (filtC B hB 12 5).trans F4.2.2.2

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
  intro L hL
  obtain rfl : L = PEqualNP.Outside.L_meta_1555.L0 := funext hL
  intro B h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  refine PEqualNP.Outside.L_meta_1555.key B ?_
  intro t
  have ht : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨ t = 12 := by
    revert t
    decide
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_1555.row B h0 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h1 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h2 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h3 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h4 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h5 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h6 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h7 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h8 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h9 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h10 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h11 (by decide) (by decide)
  · exact PEqualNP.Outside.L_meta_1555.row B h12 (by decide) (by decide)
