import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Two wires are distinguishable when they disagree on a retained input.
-- Retain every thin input and every input rejected by the original circuit.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2418_862
    (mergeWires : ∀ (n : ℕ) (C : Circuit) (S : (Fin n → Bool) → Prop), Monotone2 C →
      (∃ i j : ℕ, i < j ∧ j < n + C.size ∧
        ∀ x, S x → (C.wires (List.ofFn x)).getD i false = (C.wires (List.ofFn x)).getD j false) →
      (∀ i j : Fin n, i ≠ j → ∃ x, S x ∧ x i ≠ x j) →
      ∃ D : Circuit, Monotone2 D ∧ D.size < C.size ∧
        ∀ x, S x → circuitFun n D x = circuitFun n C x)
    (distinct :
      let V := Fin 13
      let Input := Fin 26 → Bool
      let evaluate := circuitFun 26
      let point : V → Fin 26 := Fin.castAdd 13
      let line : V → Fin 26 := Fin.natAdd 13
      let diff : Finset (V) := {0, 1, 3, 9}
      let inc := fun p w : V => ∃ d ∈ diff, p = w + d
      let avoids := fun (P : Finset (V)) (w : V) => ∀ p ∈ P, ¬inc p w
      let good := fun C : Circuit =>
        (∀ p w : V, inc p w → evaluate C
          (fun k => decide (k = point p ∨ k = line w)) = true) ∧
        (∀ P : Finset (V), (∀ v ∉ P, ∃ w, avoids P w ∧ inc v w) →
          ((∃ w, ∀ p ∈ P, inc p w) ∨ (∃ v, ∀ w, avoids P w → inc v w)) →
          evaluate C (fun k => decide ((∃ p ∈ P, k = point p) ∨
            (∃ w, k = line w ∧ avoids P w))) = false)
      let thin := fun x : Input =>
        ∃ w₀ : V, ∀ w : V, x (line w) = true → w = w₀
      ∀ C, Monotone2 C → C.size ≤ 63 → good C →
        (∀ i j : ℕ, i < j → j < 26 + C.size → ∃ x : Input,
          (thin x ∨ evaluate C x = false) ∧
          let w := C.wires (List.ofFn x)
          w.getD i false ≠ w.getD j false) →
        ∃ D, Monotone2 D ∧ D.size ≤ C.size ∧ HasLineDegree 26 (Finset.Ico 13 26) D 1 ∧
          ∀ x, thin x → evaluate D x = evaluate C x) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; let x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x2 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∉ x5, ∃ (x8 : Fin (13 : ℕ)), x3 x5 x8 ∧ x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ (x8 : Fin (13 : ℕ)), x3 x5 x8 → x2 x7 x8) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x5, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x3 x5 x9)) = Bool.false; have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true → x7 = x6; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ (63 : ℕ) → x4 x6 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x6.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x10 (1 : ℕ) ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), x5 x11 → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x10 x11 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 x11 := by
  let diff : Finset (Fin 13) := {0, 1, 3, 9}
  let inc := fun p w : Fin 13 => ∃ d ∈ diff, p = w + d
  let avoids := fun (P : Finset (Fin 13)) (w : Fin 13) => ∀ p ∈ P, ¬inc p w
  let good := fun C : Circuit =>
    (∀ p w : Fin 13, inc p w → circuitFun 26 C
      (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
    (∀ P : Finset (Fin 13), (∀ v ∉ P, ∃ w, avoids P w ∧ inc v w) →
      ((∃ w, ∀ p ∈ P, inc p w) ∨ (∃ v, ∀ w, avoids P w → inc v w)) →
      circuitFun 26 C (fun k => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
        (∃ w, k = Fin.natAdd 13 w ∧ avoids P w))) = false)
  let thin := fun x : Fin 26 → Bool =>
    ∃ w₀ : Fin 13, ∀ w : Fin 13, x (Fin.natAdd 13 w) = true → w = w₀
  change ∀ C, Monotone2 C → C.size ≤ 63 → good C → ∃ D, Monotone2 D ∧ D.size ≤ C.size ∧ HasLineDegree 26 (Finset.Ico 13 26) D 1 ∧ ∀ x, thin x → circuitFun 26 D x = circuitFun 26 C x
  intro C mono small tested

  let keep := fun x => thin x ∨ circuitFun 26 C x = false
  let feasible := fun k : ℕ => ∃ D : Circuit, Monotone2 D ∧ D.size = k ∧
    ∀ x, keep x → circuitFun 26 D x = circuitFun 26 C x
  have existsSize : ∃ k, feasible k := ⟨C.size, C, mono, rfl, fun _ _ => rfl⟩
  classical
  obtain ⟨E, hE, sizeE, agrees⟩ := Nat.find_spec existsSize
  have leSize : E.size ≤ C.size := sizeE.trans_le (Nat.find_min' existsSize
    (show feasible C.size from ⟨C, mono, rfl, fun _ _ => rfl⟩))
  have separate : ∀ p t : Fin 13, Fin.natAdd 13 t ≠ Fin.castAdd 13 p := by decide
  have identify : ∀ t w : Fin 13, Fin.natAdd 13 t = Fin.natAdd 13 w → t = w := by decide
  have thinPoint (i : Fin 26) : thin (fun j => decide (j = i)) := by
    by_cases h : ∃ w : Fin 13, Fin.natAdd 13 w = i
    · obtain ⟨w, rfl⟩ := h
      exact ⟨w, fun v hv => identify v w (of_decide_eq_true hv)⟩
    · refine ⟨0, ?_⟩
      intro v hv
      exact (h ⟨v, of_decide_eq_true hv⟩).elim
  have inputs : ∀ i j : Fin 26, i ≠ j → ∃ x, keep x ∧ x i ≠ x j := by
    intro i j h
    refine ⟨fun k => decide (k = i), Or.inl (thinPoint i), ?_⟩
    simp [Ne.symm h]
  have inj (i j : ℕ) (lt : i < j) (bound : j < 26 + E.size) :
      ∃ x, keep x ∧ (E.wires (List.ofFn x)).getD i false ≠ (E.wires (List.ofFn x)).getD j false := by
    by_contra! bad
    obtain ⟨D, hD, smaller, equal⟩ := mergeWires 26 E keep hE ⟨i,j,lt,bound,bad⟩ inputs
    have hf : feasible D.size := ⟨D, hD, rfl, fun x hx => (equal x hx).trans (agrees x hx)⟩
    have := Nat.find_min' existsSize hf
    omega
  have goodE : good E := by
    constructor
    · intro p w hp
      apply Eq.trans (agrees _ (Or.inl ⟨w, ?_⟩)) (tested.1 p w hp)
      intro t ht
      exact identify t w ((of_decide_eq_true ht).resolve_left (separate p t))
    · intro P hmax hdeg
      have rejected := tested.2 P hmax hdeg
      exact (agrees _ (Or.inr rejected)).trans rejected
  have larger (x) (hx : keep x) : thin x ∨ circuitFun 26 E x = false := by
    rcases hx with ht | hf
    · exact Or.inl ht
    · exact Or.inr ((agrees x (Or.inr hf)).trans hf)
  have separated (i j : ℕ) (lt : i < j) (bound : j < 26 + E.size) :
      ∃ x : Fin 26 → Bool, (thin x ∨ circuitFun 26 E x = false) ∧
        let w := E.wires (List.ofFn x)
        w.getD i false ≠ w.getD j false := by
    obtain ⟨x,hx,hne⟩ := inj i j lt bound
    exact ⟨x,larger x hx,hne⟩
  obtain ⟨D, hD, hLen, hDeg, hAgree⟩ := distinct E hE (leSize.trans small) goodE separated
  exact ⟨D, hD, hLen.trans leSize, hDeg, fun x hx => (hAgree x hx).trans (agrees x (Or.inl hx))⟩
