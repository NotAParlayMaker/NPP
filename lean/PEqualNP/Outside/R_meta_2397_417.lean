import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.SingleLevel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2397_417
    (certificates :
      ∀ C : Circuit, Monotone2 C → (andDepths C 26).getD C.output 0 ≤ 1 →
        ∀ x : Fin 26 → Bool, circuitFun 26 C x = true →
          ∃ S : Finset (Fin 26), S.card ≤ 2 ∧ (∀ i ∈ S, x i = true) ∧
            ∀ y : Fin 26 → Bool, (∀ i ∈ S, y i = true) → circuitFun 26 C y = true)
    (shallow :
      let I : Fin 13 → Fin 13 → Prop := fun p w => p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
      ∀ C : Circuit, Monotone2 C → (andDepths C 26).getD C.output 0 ≤ 1 →
        (∀ x : Fin 26 → Bool, circuitFun 26 C x = true ↔
          ∃ p w : Fin 13, I p w ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true) →
        64 ≤ C.size)
    (deep :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → 2 ≤ (andDepths x2 26).getD x2.output 0 → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ ∀ (x8 : Fin (26 : ℕ) → Bool), (∀ x9 ∈ x6, x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true) → (∀ x10 ∈ x7, x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x8 = Bool.true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x5 ∨ x8 = Fin.natAdd (13 : ℕ) x6)) = Bool.true) → ∃ (x6 : Finset (Fin (13 : ℕ))) (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x6 | x1 x9 x8}.card ≤ (2 : ℕ)) ∧ (∀ (x8 : Fin (13 : ℕ)), {x9 ∈ x7 | x1 x8 x9}.card ≤ (2 : ℕ)) ∧ ∀ (x8 : Fin (26 : ℕ) → Bool), (∀ x9 ∈ x6, x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true) → (∀ x10 ∈ x7, x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x8 = Bool.true := by
  classical
  dsimp only
  intro C hMono hSize hPairs
  by_cases hDepth : (andDepths C 26).getD C.output 0 ≤ 1
  · by_contra noViolation
    let I : Fin 13 → Fin 13 → Prop := fun p w => p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
    have hc := certificates C hMono hDepth
    have hExact (x : Fin 26 → Bool) : circuitFun 26 C x = true ↔
        ∃ p w : Fin 13, I p w ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true := by
      constructor
      · intro hx
        by_contra noEdge
        obtain ⟨s, hs, hsx, hForce⟩ := hc x hx
        let ps := Finset.univ.filter (fun p : Fin 13 => Fin.castAdd 13 p ∈ s)
        let ws := Finset.univ.filter (fun w : Fin 13 => Fin.natAdd 13 w ∈ s)
        have hPoint (p : Fin 13) : p ∈ ps ↔ Fin.castAdd 13 p ∈ s := by simp [ps]
        have hLine (w : Fin 13) : w ∈ ws ↔ Fin.natAdd 13 w ∈ s := by simp [ws]
        have hpSize : ps.card ≤ 2 := by
          apply (Finset.card_le_card_of_injOn (Fin.castAdd 13) ?_ ?_).trans hs
          · intro p hp
            exact (hPoint p).mp hp
          · intro a ha b hb h
            exact Fin.ext (congrArg (fun i : Fin 26 => i.val) h)
        have hwSize : ws.card ≤ 2 := by
          apply (Finset.card_le_card_of_injOn (Fin.natAdd 13) ?_ ?_).trans hs
          · intro w hw
            exact (hLine w).mp hw
          · intro a ha b hb h
            have hv : 13 + a.val = 13 + b.val := congrArg (fun i : Fin 26 => i.val) h
            exact Fin.ext (by omega)
        apply noViolation
        refine ⟨ps, ws, ?_, ?_, ?_, ?_⟩
        · intro p hp w hw hInc
          exact noEdge ⟨p, w, hInc, hsx _ ((hPoint p).mp hp), hsx _ ((hLine w).mp hw)⟩
        · intro w
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hpSize
        · intro p
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hwSize
        · intro y hyP hyW
          apply hForce
          intro i hi
          by_cases hlo : i.val < 13
          · let p : Fin 13 := ⟨i.val, hlo⟩
            have heq : Fin.castAdd 13 p = i := Fin.ext rfl
            rw [← heq]
            apply hyP p
            exact (hPoint p).mpr (heq ▸ hi)
          · let w : Fin 13 := ⟨i.val - 13, by omega⟩
            have heq : Fin.natAdd 13 w = i := Fin.ext (by change 13 + (i.val - 13) = i.val; omega)
            rw [← heq]
            apply hyW w
            exact (hLine w).mpr (heq ▸ hi)
      · rintro ⟨p, w, hInc, hp, hw⟩
        obtain ⟨s, _, hs, hForce⟩ := hc _ (hPairs p w hInc)
        apply hForce
        intro i hi
        rcases of_decide_eq_true (hs i hi) with h | h
        · exact h ▸ hp
        · exact h ▸ hw
    have hLower := shallow C hMono hDepth hExact
    omega
  · exact deep C hMono hSize hPairs (by omega)
