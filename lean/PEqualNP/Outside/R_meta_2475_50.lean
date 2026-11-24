import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2475_50
    (hSens :
      ∀ (n : ℕ) (C : Circuit), Monotone2 C →
        (∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
          circuitFun n C x ≠ circuitFun n C y) →
        n ≤ C.size + 1)
    (hLarge :
      ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
        200 ≤ q → N = q ^ 2 + q + 1 →
        (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
        (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) →
        Monotone2 C → C.output < N + N + C.size →
        (∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs = [a, b] ∧ a < b ∧ b < N + N + j) →
        (∀ p l, I p l → circuitFun (N + N) C (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) = true) →
        (∀ x : Fin (N + N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
          (¬(∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true)) →
          circuitFun (N + N) C x = false) →
        ∀ U, U ⊆ Finset.range C.size →
          (∀ j g, C.gates[j]? = some g →
            (j ∈ U ↔ g.op = GateOp.and ∧
              ((∀ w, w ∈ g.inputs → ∃ t : Fin N → Bool,
                  (C.wires (List.ofFn t ++ List.replicate N false)).getD w false ≠
                    (C.wires (List.ofFn t ++ List.replicate N true)).getD w false) ∨
                ∀ w, w ∈ g.inputs → ∃ t : Fin N → Bool,
                  (C.wires (List.replicate N false ++ List.ofFn t)).getD w false ≠
                    (C.wires (List.replicate N true ++ List.ofFn t)).getD w false))) →
          100 * U.card < N * q → N * q ≤ 100 * C.size) :
    have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (∀ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x18]? = Option.some x19 → (x18 ∈ x16 ↔ x1 x3 x6 x19)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  intro Cross q N I dec C hq hN hdeg huniq hmono hout horder haccept hreject U hUsub hExact hfew
  by_cases hsmall : q < 200
  · have hN2 : 2 ≤ N := by nlinarith [hN, hq]
    have hcast_ne_nat : ∀ (p l : Fin N), Fin.castAdd N p ≠ Fin.natAdd N l := by
      intro p l h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    have hess : ∀ k : Fin (N + N), ∃ x y : Fin (N + N) → Bool,
        (∀ j : Fin (N + N), j ≠ k → x j = y j) ∧
        circuitFun (N + N) C x ≠ circuitFun (N + N) C y := by
      intro k
      by_cases hk : k.val < N
      · let p : Fin N := ⟨k.val, hk⟩
        have hkp : k = Fin.castAdd N p := Fin.ext rfl
        let pother : Fin N := if p.val = 0 then ⟨1, by have := hN2; omega⟩ else ⟨0, by omega⟩
        have hne : p ≠ pother := by
          intro h
          have hv := congrArg Fin.val h
          by_cases hp0 : p.val = 0 <;> simp [pother, hp0] at hv
        obtain ⟨l, ⟨hIpl, _⟩, _⟩ := huniq p pother hne
        let x : Fin (N + N) → Bool := fun j => decide (j = Fin.natAdd N l)
        let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
        refine ⟨x, y, ?_, ?_⟩
        · intro j hj
          rw [hkp] at hj
          simp only [x, y, hj, false_or]
        · have hy : circuitFun (N + N) C y = true := haccept p l hIpl
          have hcard : Fintype.card {l0 : Fin N // x (Fin.natAdd N l0) = true} ≤ q := by
            have hle : Fintype.card {l0 : Fin N // x (Fin.natAdd N l0) = true} ≤ 1 := by
              rw [Fintype.card_le_one_iff]
              intro a b
              have ha : Fin.natAdd N a.1 = Fin.natAdd N l := by
                simpa [x, decide_eq_true_eq] using a.2
              have hb : Fin.natAdd N b.1 = Fin.natAdd N l := by
                simpa [x, decide_eq_true_eq] using b.2
              have hv := congrArg Fin.val (ha.trans hb.symm)
              simp only [Fin.val_natAdd] at hv
              exact Subtype.ext (Fin.ext (by omega))
            omega
          have hx : circuitFun (N + N) C x = false :=
            hreject x hcard (by
              rintro ⟨p0, l0, _, hp0, _⟩
              simp only [x, decide_eq_true_eq] at hp0
              exact hcast_ne_nat p0 l hp0)
          rw [hx, hy]
          decide
      · let l : Fin N := ⟨k.val - N, by omega⟩
        have hkl : k = Fin.natAdd N l := Fin.ext (by simp [l]; omega)
        have hpos : 0 < Fintype.card {p : Fin N // I p l} := by
          have hc := hdeg l
          omega
        obtain ⟨p, hpI⟩ := Fintype.card_pos_iff.mp hpos
        let x : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p)
        let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
        refine ⟨x, y, ?_, ?_⟩
        · intro j hj
          rw [hkl] at hj
          simp only [x, y, hj, or_false]
        · have hy : circuitFun (N + N) C y = true := haccept p l hpI
          have hcard : Fintype.card {l0 : Fin N // x (Fin.natAdd N l0) = true} ≤ q := by
            have h0 : Fintype.card {l0 : Fin N // x (Fin.natAdd N l0) = true} = 0 := by
              rw [Fintype.card_eq_zero_iff]
              exact ⟨fun ⟨l0, hl0⟩ => by
                have heq : Fin.natAdd N l0 = Fin.castAdd N p := by
                  simpa [x, decide_eq_true_eq] using hl0
                exact hcast_ne_nat p l0 heq.symm⟩
            omega
          have hx : circuitFun (N + N) C x = false :=
            hreject x hcard (by
              rintro ⟨p0, l0, _, _, hl0⟩
              simp only [x, decide_eq_true_eq] at hl0
              exact hcast_ne_nat p l0 hl0.symm)
          rw [hx, hy]
          decide
    have hsz : N + N ≤ C.size + 1 := hSens (N + N) C hmono hess
    have hlow : 2 * N - 1 ≤ C.size := by omega
    have hqle : q ≤ 199 := by omega
    have hstep : N * q ≤ N * 199 := Nat.mul_le_mul_left _ hqle
    have hfit : N * 199 ≤ 200 * N - 100 :=
      (Nat.le_sub_iff_add_le (by nlinarith : (100 : ℕ) ≤ 200 * N)).mpr (by
        have hcomm : N * 200 = 200 * N := Nat.mul_comm _ _
        have hadd : N * 199 + N = N * 200 := by ring
        omega)
    have hid : 100 * (2 * N - 1) = 200 * N - 100 := by
      have hsub : 100 * (2 * N - 1) = 100 * (2 * N) - 100 := Nat.mul_sub 100 (2 * N) 1
      omega
    have hbound : N * q ≤ 100 * (2 * N - 1) := by
      rw [hid]
      exact hstep.trans hfit
    exact hbound.trans (Nat.mul_le_mul_left 100 hlow)
  · have hq200 : 200 ≤ q := by omega
    have hmem : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (j ∈ U ↔ g.op = GateOp.and ∧
          ((∀ w ∈ g.inputs, ∃ t : Fin N → Bool,
              (C.wires (List.ofFn t ++ List.replicate N false)).getD w false ≠
                (C.wires (List.ofFn t ++ List.replicate N true)).getD w false) ∨
            ∀ w ∈ g.inputs, ∃ t : Fin N → Bool,
              (C.wires (List.replicate N false ++ List.ofFn t)).getD w false ≠
                (C.wires (List.replicate N true ++ List.ofFn t)).getD w false)) := by
      intro j g hg
      rw [hExact j g hg]
    exact hLarge q N I C hq200 hN hdeg huniq hmono hout horder haccept hreject U hUsub hmem hfew
