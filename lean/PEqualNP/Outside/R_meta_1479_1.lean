import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_1479_1
    (h1 : ∃ C : Circuit, C.size ≤ 25 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
          x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true))
    (h2 : let shape := fun C : Circuit =>
        ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j
      let recP := fun (C : Circuit) (P : Fin 14 → Bool) (v : ℕ → Bool) =>
        ∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a, b] →
          (g.op = GateOp.and → v (14 + j) = (((C.wires (List.ofFn P)).getD a false && v b) || (v a && (C.wires (List.ofFn P)).getD b false))) ∧
          (g.op = GateOp.or → v (14 + j) = (v a || v b))
      ∀ (C : Circuit), shape C →
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧
            x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
        ∃ D : Circuit, D.size ≤ C.size + 2 ∧ shape D ∧
          ((∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
          (∃ v : ℕ → Bool,
            (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = 0)) ∧
            recP D (fun i : Fin 14 => decide (i = Fin.castAdd 7 (0 : Fin 7))) v ∧
            v D.output = false) ∧
          (∃ w : ℕ → Bool,
            (∀ mx : Fin 7, w mx.val = decide (mx = 0) ∧ w (7 + mx.val) = false) ∧
            recP D (fun i : Fin 14 => decide (i = Fin.natAdd 7 (0 : Fin 7))) w ∧
            w D.output = false)))
    : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false) := by
  obtain ⟨C, hsize, hstruct, hfun⟩ := h1
  obtain ⟨D, hDsize, hDstruct, hDeq, ⟨v, hvbase, hvrec, hvout⟩, ⟨w, hwbase, hwrec, hwout⟩⟩ := h2 C hstruct hfun
  exact ⟨D, by omega, hDstruct, by intro x; rw [hDeq x]; exact hfun x, 0, 0, Or.inl rfl, ⟨v, hvbase, hvrec, hvout⟩, ⟨w, hwbase, hwrec, hwout⟩⟩
