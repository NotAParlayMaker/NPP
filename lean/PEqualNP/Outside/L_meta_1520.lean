import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1520 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) ↔
      ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)))) ∧
    (∀ x : Fin 13 → Bool, (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) → x ≠ (fun v : Fin 13 => decide (v ∉ L 0)) ∧ x ≠ (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9))) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s))).card = 7170 ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s)).card = 157 ∧
    (∀ x y : Fin 13 → Bool, ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) → (∀ v : Fin 13, x v = true → y v = true) → ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), y v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, y v = false → v ∈ L s)) := by
  decide
