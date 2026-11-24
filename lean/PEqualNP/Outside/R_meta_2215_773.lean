import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2215_773
    (search :
      let I := fun p l : Fin 25 => p.val < 12 ∧ 12 ≤ l.val ∧
        (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ)
      let B : Finset (Fin 25) := {12,13,15,21}
      let independent := fun s : Finset (Fin 25) => ∀ p ∈ s, ∀ l ∈ s, ¬ I p l
      let maximal := fun s u : Finset (Fin 25) =>
        s ⊆ u ∧ independent s ∧ ∀ t : Finset (Fin 25), s ⊆ t → t ⊆ u → independent t → t = s
      ∃ (C : Circuit) (j : ℕ), Monotone2 C ∧ C.size ≤ 61 ∧
        C.output < 25 + C.size ∧ j < 25 + C.size ∧
        let read := fun (w : ℕ) (s : Finset (Fin 25)) =>
          (C.wires (List.ofFn fun i : Fin 25 => decide (i ∈ s))).getD w false
        (∀ p l, I p l → read C.output {p,l} = true) ∧
        (∀ s, maximal s Finset.univ → read C.output s = false) ∧
        (∀ i ∈ B, read j {i} = true) ∧
        (∀ s, maximal s (Finset.univ \ B) → read j s = false))
    (monotone : ∀ (n : ℕ) (C : Circuit), Monotone2 C → ∀ x y : Fin n → Bool,
      (∀ u, x u = true → y u = true) → ∀ j : ℕ,
      (C.wires (List.ofFn x)).getD j false = true → (C.wires (List.ofFn y)).getD j false = true)
    (extend : ∀ (n : ℕ) (I : Fin n → Fin n → Prop) (U S : Finset (Fin n)),
      S ⊆ U → (∀ a ∈ S, ∀ b ∈ S, ¬ I a b) →
      ∃ T, S ⊆ T ∧ T ⊆ U ∧ (∀ a ∈ T, ∀ b ∈ T, ¬ I a b) ∧
        ∀ T' : Finset (Fin n), T ⊆ T' → T' ⊆ U → (∀ a ∈ T', ∀ b ∈ T', ¬ I a b) → T' = T) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  let I := fun p l : Fin 25 => p.val < 12 ∧ 12 ≤ l.val ∧
    (p.val + l.val + 2) % 13 ∈ ([0,1,3,9] : List ℕ)
  let B : Finset (Fin 25) := {12,13,15,21}
  let independent := fun s : Finset (Fin 25) => ∀ p ∈ s, ∀ l ∈ s, ¬ I p l
  let maximal := fun s u : Finset (Fin 25) =>
    s ⊆ u ∧ independent s ∧ ∀ t : Finset (Fin 25), s ⊆ t → t ⊆ u → independent t → t = s
  obtain ⟨C, j, mono, size, outputBound, auxBound, tests⟩ := search
  let bits := fun (s : Finset (Fin 25)) (i : Fin 25) => decide (i ∈ s)
  let read := fun (w : ℕ) (s : Finset (Fin 25)) => (C.wires (List.ofFn (bits s))).getD w false
  change (∀ p l, I p l → read C.output {p,l} = true) ∧
    (∀ s, maximal s Finset.univ → read C.output s = false) ∧
    (∀ i ∈ B, read j {i} = true) ∧
    (∀ s, maximal s (Finset.univ \ B) → read j s = false) at tests
  have lift (s t : Finset (Fin 25)) (sub : s ⊆ t) (w : ℕ) :
      read w s = true → read w t = true := by
    apply monotone 25 C mono (bits s) (bits t) _ w
    intro i hi
    exact decide_eq_true (sub (of_decide_eq_true hi))
  have main (s : Finset (Fin 25)) : read C.output s = true ↔
      ∃ p l, I p l ∧ p ∈ s ∧ l ∈ s := by
    constructor
    · intro yes
      by_contra absent
      have indep : independent s := fun p hp l hl e => absent ⟨p, l, e, hp, hl⟩
      obtain ⟨t, sub, allowed, indepT, largest⟩ := extend 25 I Finset.univ s (Finset.subset_univ _) indep
      have no := tests.2.1 t ⟨allowed, indepT, largest⟩
      exact Bool.false_ne_true (no.symm.trans (lift s t sub C.output yes))
    · rintro ⟨p, l, e, hp, hl⟩
      have sub : ({p,l} : Finset (Fin 25)) ⊆ s := by
        simp [Finset.insert_subset_iff, hp, hl]
      exact lift {p,l} s sub C.output (tests.1 p l e)
  refine ⟨C, j, mono, size, outputBound, auxBound, ?_⟩
  intro x
  let s := Finset.univ.filter fun i : Fin 25 => x i = true
  have mem (i : Fin 25) : i ∈ s ↔ x i = true := by simp [s]
  have input : bits s = x := by
    funext i
    cases hi : x i <;> simp [bits, mem, hi]
  have readEq (w : ℕ) : read w s = (C.wires (List.ofFn x)).getD w false := by
    change (C.wires (List.ofFn (bits s))).getD w false = _
    rw [input]
  change ((C.wires (List.ofFn x)).getD C.output false = true ↔
      ∃ p l, I p l ∧ x p = true ∧ x l = true) ∧
    ((C.wires (List.ofFn x)).getD C.output false = false →
      (C.wires (List.ofFn x)).getD j false = (x 12 || x 13 || x 15 || x 21))
  rw [← readEq C.output, ← readEq j]
  constructor
  · simpa only [mem] using main s
  · intro noEdge
    have indep : independent s := by
      intro p hp l hl e
      have yes := (main s).mpr ⟨p, l, e, hp, hl⟩
      exact Bool.false_ne_true (noEdge.symm.trans yes)
    have found : (x 12 || x 13 || x 15 || x 21) = true ↔ ∃ i ∈ B, i ∈ s := by
      simp [B, mem, Bool.or_eq_true, or_assoc]
    by_cases hit : ∃ i ∈ B, i ∈ s
    · obtain ⟨i, hiB, hiS⟩ := hit
      rw [found.mpr ⟨i, hiB, hiS⟩]
      exact lift {i} s (Finset.singleton_subset_iff.mpr hiS) j (tests.2.2.1 i hiB)
    · have allowed : s ⊆ Finset.univ \ B := by
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hb => hit ⟨i, hb, hi⟩⟩
      obtain ⟨t, sub, allowedT, indepT, largest⟩ := extend 25 I (Finset.univ \ B) s allowed indep
      have no := tests.2.2.2 t ⟨allowedT, indepT, largest⟩
      have rhs : (x 12 || x 13 || x 15 || x 21) = false :=
        Bool.eq_false_iff.mpr (fun yes => hit (found.mp yes))
      rw [rhs]
      exact Bool.eq_false_iff.mpr (fun yes => Bool.false_ne_true (no.symm.trans (lift s t sub j yes)))
