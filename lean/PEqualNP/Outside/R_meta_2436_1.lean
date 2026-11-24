import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
set_option synthInstance.maxSize 512 in
theorem PEqualNP.Outside.R_meta_2436_1
    (core : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 21 C ∧ C.size ≤ 34 ∧
      ∀ y : Fin 21 → Bool, C.eval (List.ofFn y) = true ↔
        ∃ p l : Fin 21, (p.val, l.val) ∈ ([(0,15), (0,19), (1,15), (1,16), (2,16), (2,17), (3,17), (3,18), (4,15), (4,18), (5,16), (5,19), (6,17), (6,19), (7,18), (7,20), (8,19), (8,20), (9,15), (9,20), (10,16), (10,20), (11,15), (11,17), (12,16), (12,18), (13,17), (13,20), (14,18), (14,19)] : List (ℕ × ℕ)) ∧
          y p = true ∧ y l = true)
    (appendRest : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 21 C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack 44 D ∧ D.size ≤ C.size + 88 ∧
        (∀ i : Fin 42, List.count i.val ([0, 1, 4, 42] : List ℕ) = 1 →
          ∃ g ∈ D.gates, i.val ∈ g.inputs) ∧
        ∀ x : Fin 42 → Bool,
          let y : Fin 43 → Bool := Fin.lastCases (x 0 || x 1) x
          D.eval (List.ofFn (Fin.lastCases (y 4 || y 42) y)) =
            (C.eval (List.ofFn (fun i : Fin 21 =>
                x (([1, 2, 3, 4, 5, 6, 7, 8, 10, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 27, 36] : List (Fin 42)).getD i.val 0))) ||
              decide (∃ p l : Fin 42, p.val < 21 ∧ 21 ≤ l.val ∧
                (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ) ∧
                l.val ∉ ([22, 23, 24, 25, 27, 36] : List ℕ) ∧ x p = true ∧ x l = true))) :
    ∃ (x1 : Fin (42 : ℕ)) (x2 : Fin (43 : ℕ)) (x3 : Fin (43 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = (1 : Fin (42 : ℕ)) ∨ x1 = (21 : Fin (42 : ℕ)) ∨ x1 = (22 : Fin (42 : ℕ))) ∧     x2 < x3 ∧       (x2, x3) ≠ ((0 : Fin (43 : ℕ)), x1.castSucc) ∧         (x3 = Fin.last (42 : ℕ) → x2 ≠ (0 : Fin (43 : ℕ)) ∧ x2 ≠ x1.castSucc) ∧           (∀ (x5 : Fin (42 : ℕ)), List.count ↑x5 [(0 : ℕ), ↑x1, ↑x2, ↑x3] = (1 : ℕ) → ∃ x7 ∈ x4.gates, ↑x5 ∈ x7.inputs) ∧             PEqualNP.MetaComplexity.Monotone2 x4 ∧               PEqualNP.MetaComplexity.NestedCover.ReadsBack (44 : ℕ) x4 ∧                 x4.size ≤ (122 : ℕ) ∧                   ∀ (x5 : Fin (42 : ℕ) → Bool),                     have x6 : Fin (43 : ℕ) → Bool := fun (x6 : Fin ((42 : ℕ) + (1 : ℕ))) => Fin.lastCases (x5 (0 : Fin (42 : ℕ)) || x5 x1) x5 x6;                     x4.eval (List.ofFn fun (x7 : Fin ((43 : ℕ) + (1 : ℕ))) => Fin.lastCases (x6 x2 || x6 x3) x6 x7) = Bool.true ↔ ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x7 = Bool.true ∧ x5 x8 = Bool.true := by
  obtain ⟨C, hcMono, hcBack, hcSize, hcEval⟩ := core
  obtain ⟨D, hdMono, hdBack, hdSize, hdUsed, hdEval⟩ := appendRest C hcMono hcBack
  refine ⟨1, 4, 42, D, Or.inl rfl, by decide, by decide, by decide,
    hdUsed, hdMono, hdBack, by omega, ?_⟩
  let embed (i : Fin 21) : Fin 42 := ([1, 2, 3, 4, 5, 6, 7, 8, 10, 15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 27, 36] : List (Fin 42)).getD i.val 0
  let inverse (i : Fin 42) : Fin 21 := ([0, 0, 1, 2, 3, 4, 5, 6, 7, 0, 8, 0, 0, 0, 0, 9, 10, 11, 12, 13, 14, 0, 15, 16, 17, 18, 0, 19, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0] : List (Fin 21)).getD i.val 0
  let selected : List ℕ := [22, 23, 24, 25, 27, 36]
  let pairs : List (ℕ × ℕ) := [(0,15), (0,19), (1,15), (1,16), (2,16), (2,17), (3,17), (3,18), (4,15), (4,18), (5,16), (5,19), (6,17), (6,19), (7,18), (7,20), (8,19), (8,20), (9,15), (9,20), (10,16), (10,20), (11,15), (11,17), (12,16), (12,18), (13,17), (13,20), (14,18), (14,19)]
  let incident (p l : Fin 42) : Prop :=
    p.val < 21 ∧ 21 ≤ l.val ∧ (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
  have forward : ∀ p l : Fin 21, (p.val, l.val) ∈ pairs → incident (embed p) (embed l) := by
    decide +kernel
  have backward : ∀ p l : Fin 42, incident p l ∧ l.val ∈ selected →
      embed (inverse p) = p ∧ embed (inverse l) = l ∧ ((inverse p).val, (inverse l).val) ∈ pairs := by
    decide +kernel
  intro x
  have hCoreX := hcEval (fun i => x (embed i))
  dsimp only
  rw [hdEval x, Bool.or_eq_true_iff, hCoreX, decide_eq_true_eq]
  constructor
  · rintro (⟨p, l, hpl, hp, hl⟩ | ⟨p, l, h₁, h₂, h₃, _, hp, hl⟩)
    · exact ⟨embed p, embed l, forward p l hpl, hp, hl⟩
    · exact ⟨p, l, ⟨h₁, h₂, h₃⟩, hp, hl⟩
  · rintro ⟨p, l, hpl, hp, hl⟩
    by_cases h : l.val ∈ selected
    · obtain ⟨hp', hl', hPair⟩ := backward p l ⟨hpl, h⟩
      exact Or.inl ⟨inverse p, inverse l, hPair, by simpa only [hp'] using hp,
        by simpa only [hl'] using hl⟩
    · exact Or.inr ⟨p, l, hpl.1, hpl.2.1, hpl.2.2, h, hp, hl⟩
