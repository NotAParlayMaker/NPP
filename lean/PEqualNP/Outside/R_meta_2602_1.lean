import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.R_meta_2602_1 :
    (let trace := fun (C : Circuit) (i k : ℕ) (v : ℕ → Bool) =>
      (∀ j < 26, v j = decide (j = k)) ∧
      (∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a, b] →
        let p := C.wires (List.ofFn fun x : Fin 26 => decide (x.val = i))
        (g.op = GateOp.and → v (26 + j) = (p.getD a false && v b || v a && p.getD b false)) ∧
        (g.op = GateOp.or → v (26 + j) = (v a || v b))) ∧ v C.output = false
    let dirty := fun C : Circuit => ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
      ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + j) false = true ∧
        C.eval (List.ofFn x) = false
    ∀ (C : Circuit) (v w : ℕ → Bool), C.size = 64 →
      (∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ (fun x : Fin 26 → Bool => ∃ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) x) →
      trace C 0 13 v → trace C 13 0 w → ¬ dirty C → False) →
    (let trace := fun (C : Circuit) (i k : ℕ) (v : ℕ → Bool) =>
      (∀ j < 26, v j = decide (j = k)) ∧
      (∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a, b] →
        let p := C.wires (List.ofFn fun x : Fin 26 => decide (x.val = i))
        (g.op = GateOp.and → v (26 + j) = (p.getD a false && v b || v a && p.getD b false)) ∧
        (g.op = GateOp.or → v (26 + j) = (v a || v b))) ∧ v C.output = false
    let dirty := fun C : Circuit => ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
      ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + j) false = true ∧
        C.eval (List.ofFn x) = false
    ∀ (C : Circuit) (v w : ℕ → Bool), C.size = 64 →
      (∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) →
      (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ (fun x : Fin 26 → Bool => ∃ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) x) →
      trace C 0 13 v → trace C 13 0 w → dirty C → False) →
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (63 : ℕ) ≤ x1.size ∧ x1.size ≤ (64 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (26 : ℕ) + x2 ∧ x6 < (26 : ℕ) + x2) ∧ (∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) ∧ (∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (13 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false) ∧ ∃ (x2 : ℕ → Bool), (∀ x3 < (26 : ℕ), x2 x3 = Decidable.decide (x3 = (0 : ℕ))) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ), x1.gates[x3]? = Option.some x4 → x4.inputs = [x5, x6] → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x2 ((26 : ℕ) + x3) = ((x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x5 Bool.false && x2 x6 || x2 x5 && (x1.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)))).getD x6 Bool.false)) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → x2 ((26 : ℕ) + x3) = (x2 x5 || x2 x6))) ∧ x2 x1.output = Bool.false := by
  intro cleanCase dirtyCase
  let trace := fun (C : Circuit) (i k : ℕ) (v : ℕ → Bool) =>
      (∀ j < 26, v j = decide (j = k)) ∧
      (∀ j (g : Gate) a b, C.gates[j]? = some g → g.inputs = [a, b] →
        let p := C.wires (List.ofFn fun x : Fin 26 => decide (x.val = i))
        (g.op = GateOp.and → v (26 + j) = (p.getD a false && v b || v a && p.getD b false)) ∧
        (g.op = GateOp.or → v (26 + j) = (v a || v b))) ∧ v C.output = false
  let dirty := fun C : Circuit => ∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
      ∃ x : Fin 26 → Bool, (C.wires (List.ofFn x)).getD (26 + j) false = true ∧
        C.eval (List.ofFn x) = false
  let legal (C : Circuit) := ∀ j (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j
  let target := (fun x : Fin 26 → Bool => ∃ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  have exact64 (C : Circuit) (v w : ℕ → Bool) (hs : C.size = 64) (hg : legal C)
      (hf : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ target x)
      (hv : trace C 0 13 v) (hw : trace C 13 0 w) : False := by
    by_cases hd : dirty C
    · exact dirtyCase C v w hs hg hf hv hw hd
    · exact cleanCase C v w hs hg hf hv hw hd
  rintro ⟨C, hmin, hmax, hg, hf, ⟨v, hv⟩, ⟨w, hw⟩⟩
  by_cases h64 : C.size = 64
  · exact exact64 C v w h64 hg hf hv hw
  have h63 : C.size = 63 := by omega
  let extra : Gate := ⟨GateOp.or, [0, 13]⟩
  let D : Circuit := ⟨C.gates ++ [extra], C.output⟩
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have lengthOf (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]; omega
  have preserve (x : Fin 26 → Bool) (i : ℕ) (hi : i < 26 + C.gates.length) :
      (D.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD i false := by
    change ((C.gates ++ [extra]).foldl step (List.ofFn x)).getD i false =
      (C.gates.foldl step (List.ofFn x)).getD i false
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, step]
    apply List.getD_append
    change i < (C.gates.foldl step (List.ofFn x)).length
    simpa only [lengthOf, List.length_ofFn] using hi
  have outBound : C.output < 26 + C.gates.length := by
    have htrue : C.eval (List.ofFn (fun _ : Fin 26 => true)) = true :=
      (hf _).mpr ⟨0, 0, Or.inl rfl, rfl, rfl⟩
    by_contra! ho
    change (C.gates.foldl step (List.ofFn (fun _ : Fin 26 => true))).getD
      C.output false = true at htrue
    rw [List.getD_eq_default _ _ (by simpa only [lengthOf, List.length_ofFn] using ho)] at htrue
    cases htrue
  have gates (j : ℕ) (g : Gate) (h : D.gates[j]? = some g) :
      (j < C.gates.length ∧ C.gates[j]? = some g) ∨
      (j = C.gates.length ∧ g = extra) := by
    by_cases hj : j < C.gates.length
    · exact Or.inl ⟨hj, by simpa only [D, List.getElem?_append_left hj] using h⟩
    · have hlen : j < D.gates.length := List.getElem?_eq_some_iff.mp h |>.1
      have hj' : j = C.gates.length := by
        simp [D] at hlen
        omega
      subst j
      exact Or.inr ⟨rfl, by
        simpa [D, List.getElem?_append_right (Nat.le_refl _), eq_comm] using h⟩
  have hDlegal : legal D := by
    intro j g h
    rcases gates j g h with ⟨hj, hC⟩ | ⟨rfl, rfl⟩
    · exact hg j g hC
    · exact ⟨Or.inr rfl, 0, 13, rfl, by decide, by omega, by omega⟩
  have hDcorrect (x : Fin 26 → Bool) : D.eval (List.ofFn x) = true ↔ target x := by
    change (D.wires (List.ofFn x)).getD C.output false = true ↔ target x
    rw [preserve x _ outBound]
    exact hf x
  have extTrace (i k : ℕ) (v : ℕ → Bool) (h : trace C i k v) :
      ∃ v', trace D i k v' := by
    let v' := Function.update v (26 + C.gates.length) (v 0 || v 13)
    have old (j : ℕ) (hj : j < 26 + C.gates.length) : v' j = v j := by
      simp [v', show j ≠ 26 + C.gates.length by omega]
    refine ⟨v', ?_, ?_, ?_⟩
    · intro j hj
      rw [old j (by omega)]
      exact h.1 j hj
    · intro j g a b hget hin
      dsimp only
      rcases gates j g hget with ⟨hj, hc⟩ | ⟨rfl, rfl⟩
      · obtain ⟨-, c, d, hcd, -, hcle, hdle⟩ := hg j g hc
        rw [hin] at hcd
        simp only [List.cons.injEq, and_true] at hcd
        obtain ⟨rfl, rfl⟩ := hcd
        have ha : a < 26 + C.gates.length := by omega
        have hb : b < 26 + C.gates.length := by omega
        rw [old _ (by omega), old a ha, old b hb, preserve _ a ha, preserve _ b hb]
        exact h.2.1 j g a b hc hin
      · change [0, 13] = [a, b] at hin
        simp only [List.cons.injEq, and_true] at hin
        obtain ⟨rfl, rfl⟩ := hin
        refine ⟨fun he => ?_, fun _ => ?_⟩
        · cases he
        · rw [old 0 (by omega), old 13 (by omega)]
          simp [v']
    · change v' C.output = false
      rw [old _ outBound]
      exact h.2.2
  obtain ⟨v', hv'⟩ := extTrace 0 13 v hv
  obtain ⟨w', hw'⟩ := extTrace 13 0 w hw
  have hDsize : D.size = 64 := by
    change (C.gates ++ [extra]).length = 64
    change C.gates.length = 63 at h63
    simp [h63]
  exact exact64 D v' w' hDsize hDlegal hDcorrect hv' hw'
