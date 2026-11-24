import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2567_1
    (hPos : ∃ (x1 : GateOp) (x2 x3 : Fin 26) (x4 : Circuit),
      (x1 = GateOp.and ∨ x1 = GateOp.or) ∧
      (x2, x3) ∈ ([(0, 1), (0, 13), (0, 15)] : List (Fin 26 × Fin 26)) ∧
      Monotone2 x4 ∧ x4.size ≤ 62 ∧
      let x5 : Fin 13 → Fin 13 → Prop := fun a b => (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      let x6 : Finset (Fin 13) → Finset (Fin 13) → Fin 26 → Bool :=
        fun s t i => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      let x7 : Finset (Fin 13) → Finset (Fin 13) := fun s => {l : Fin 13 | ∀ p ∈ s, ¬ x5 p l}
      let x8 : Finset (Fin 13) → Finset (Fin 13) → Bool :=
        fun s t => x4.eval (List.ofFn (x6 s t) ++ [x1.eval [x6 s t x2, x6 s t x3]])
      ∀ (p l : Fin 13), x5 p l → x8 {p} {l} = true)
    (hNegFromPos : ∀ (x1 : GateOp) (x2 x3 : Fin 26) (x4 : Circuit),
      (x1 = GateOp.and ∨ x1 = GateOp.or) →
      (x2, x3) ∈ ([(0, 1), (0, 13), (0, 15)] : List (Fin 26 × Fin 26)) →
      Monotone2 x4 →
      x4.size ≤ 62 →
      let x5 : Fin 13 → Fin 13 → Prop := fun a b => (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      let x6 : Finset (Fin 13) → Finset (Fin 13) → Fin 26 → Bool :=
        fun s t i => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      let x7 : Finset (Fin 13) → Finset (Fin 13) := fun s => {l : Fin 13 | ∀ p ∈ s, ¬ x5 p l}
      let x8 : Finset (Fin 13) → Finset (Fin 13) → Bool :=
        fun s t => x4.eval (List.ofFn (x6 s t) ++ [x1.eval [x6 s t x2, x6 s t x3]])
      (∀ (p l : Fin 13), x5 p l → x8 {p} {l} = true) →
      ∀ (s : Finset (Fin 13)), s.card ≤ 3 → x8 s (x7 s) = false ∧ x8 (x7 s) s = false) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.GateOp) (x2 : Fin (26 : ℕ)) (x3 : Fin (26 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x1 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧     (x2, x3) ∈ [((0 : Fin (26 : ℕ)), (1 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)))] ∧       PEqualNP.MetaComplexity.Monotone2 x4 ∧         x4.size ≤ (62 : ℕ) ∧           let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];           have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);           have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};           have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => x4.eval (List.ofFn (x6 x8 x9) ++ [x1.eval [x6 x8 x9 x2, x6 x8 x9 x3]]);           (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false := by
  rcases hPos with ⟨x1, x2, x3, x4, hOp, hPair, hMono, hSize, hPosRows⟩
  refine ⟨x1, x2, x3, x4, hOp, hPair, hMono, hSize, ?_⟩
  let x5 : Fin 13 → Fin 13 → Prop := fun a b => (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let x6 : Finset (Fin 13) → Finset (Fin 13) → Fin 26 → Bool :=
    fun s t i => if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let x7 : Finset (Fin 13) → Finset (Fin 13) := fun s => {l : Fin 13 | ∀ p ∈ s, ¬ x5 p l}
  let x8 : Finset (Fin 13) → Finset (Fin 13) → Bool :=
    fun s t => x4.eval (List.ofFn (x6 s t) ++ [x1.eval [x6 s t x2, x6 s t x3]])
  have hNegRows : ∀ (s : Finset (Fin 13)), s.card ≤ 3 → x8 s (x7 s) = false ∧ x8 (x7 s) s = false := by
    exact hNegFromPos x1 x2 x3 x4 hOp hPair hMono hSize (by simpa [x5, x6, x7, x8] using hPosRows)
  refine And.intro ?_ ?_
  · simpa [x5, x6, x7, x8] using hPosRows
  · intro s hs
    exact hNegRows s hs
