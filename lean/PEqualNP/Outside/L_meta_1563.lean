import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1563

def Lz (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cnt1 : (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ Lz 0 → x v = true))).card = 6148 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem colines : ∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ Lz t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ Lz t)) 1 = true ∨ ∀ v : Fin 13, v ∉ Lz 0 → (fun v : Fin 13 => decide (v ∉ Lz t)) v = true) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cnt2 : (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chars : ∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ Lz 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ Lz 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ Lz 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ Lz 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ Lz 0 ∨ v = 3 ∨ v = 9))) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1563

theorem PEqualNP.Outside.L_meta_1563 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)))) := by
  intro L hL
  obtain rfl : L = PEqualNP.Outside.L_meta_1563.Lz := funext hL
  refine ⟨?_, PEqualNP.Outside.L_meta_1563.cnt1, PEqualNP.Outside.L_meta_1563.colines,
    PEqualNP.Outside.L_meta_1563.cnt2, PEqualNP.Outside.L_meta_1563.chars⟩
  intro x y hx hxy
  rcases hx with h | h | h
  · exact Or.inl (hxy _ h)
  · exact Or.inr (Or.inl (hxy _ h))
  · exact Or.inr (Or.inr (fun v hv => hxy _ (h v hv)))
