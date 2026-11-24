import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2056_677
    (small : ∃ (D : Circuit) (j : ℕ), Monotone2 D ∧ D.size ≤ 19 ∧
      D.output < 26 + D.size ∧ j < 26 + D.size ∧
      (∀ g ∈ D.gates, ∀ w ∈ g.inputs, w < 26 →
        w ∈ ([0,1,2,5,13,14,15,16,17,20,21,22,24,25] : List ℕ)) ∧
      let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
      let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
        if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
      ∀ s t : Finset (Fin 13),
        let u := List.ofFn (vec s t)
        (D.eval u = true ↔ ∃ p ∈ s, p.val ∈ ([0,1,2,5] : List ℕ) ∧ ∃ l ∈ t, near p l) ∧
        (D.eval u = false → (D.wires u).getD j false = decide ((0 : Fin 13) ∈ t ∨ (11 : Fin 13) ∈ t)))
    (extend : ∀ (D : Circuit) (j : ℕ), Monotone2 D → D.output < 26 + D.size → j < 26 + D.size →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ D.size + 44 ∧
        let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
        let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
          if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
        ∀ s t : Finset (Fin 13),
          let u := List.ofFn (vec s t)
          C.eval u = (D.eval u ||
            ((decide ((3 : Fin 13) ∈ s) &&
              ((D.wires u).getD j false || (decide ((6 : Fin 13) ∈ t) || decide ((10 : Fin 13) ∈ t)))) ||
              decide (∃ p ∈ s, p.val ∉ ([0,1,2,3,5] : List ℕ) ∧ ∃ l ∈ t, near p l)))) :

∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (63 : ℕ) ∧       let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => x1.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := by
  obtain ⟨D, j, hD, sizeD, outD, inD, _, core⟩ := small
  obtain ⟨C, hC, sizeC, extension⟩ := extend D j hD outD inD
  refine ⟨C, hC, by omega, ?_⟩
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) =>
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off := fun s : Finset (Fin 13) => Finset.univ.filter fun l => ∀ p ∈ s, ¬near p l
  have split : ∀ p : Fin 13, p.val ∈ ([0,1,2,3,5] : List ℕ) ↔
      p.val ∈ ([0,1,2,5] : List ℕ) ∨ p = 3 := by decide
  have star : ∀ l : Fin 13, near 3 l ↔ l = 0 ∨ l = 11 ∨ l = 6 ∨ l = 10 := by decide
  have bonus (s t : Finset (Fin 13)) :
      (decide ((3 : Fin 13) ∈ s) &&
        (decide ((0 : Fin 13) ∈ t ∨ (11 : Fin 13) ∈ t) ||
          (decide ((6 : Fin 13) ∈ t) || decide ((10 : Fin 13) ∈ t)))) = true ↔
      3 ∈ s ∧ ∃ l ∈ t, near 3 l := by
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hp, (h | h) | (h | h)⟩
      · exact ⟨hp, 0, h, (star 0).2 (Or.inl rfl)⟩
      · exact ⟨hp, 11, h, (star 11).2 (Or.inr (Or.inl rfl))⟩
      · exact ⟨hp, 6, h, (star 6).2 (Or.inr (Or.inr (Or.inl rfl)))⟩
      · exact ⟨hp, 10, h, (star 10).2 (Or.inr (Or.inr (Or.inr rfl)))⟩
    · rintro ⟨hp, l, hl, hnear⟩
      rcases (star l).1 hnear with rfl | rfl | rfl | rfl <;> tauto
  have exactEval (s t : Finset (Fin 13)) :
      C.eval (List.ofFn (vec s t)) = true ↔ ∃ p ∈ s, ∃ l ∈ t, near p l := by
    let u := List.ofFn (vec s t)
    have ext := extension s t
    change C.eval u = (D.eval u ||
      ((decide ((3 : Fin 13) ∈ s) &&
        ((D.wires u).getD j false || (decide ((6 : Fin 13) ∈ t) || decide ((10 : Fin 13) ∈ t)))) ||
        decide (∃ p ∈ s, p.val ∉ ([0,1,2,3,5] : List ℕ) ∧ ∃ l ∈ t, near p l))) at ext
    have tests := core s t
    change (D.eval u = true ↔ ∃ p ∈ s, p.val ∈ ([0,1,2,5] : List ℕ) ∧ ∃ l ∈ t, near p l) ∧
      (D.eval u = false → (D.wires u).getD j false = decide ((0 : Fin 13) ∈ t ∨ (11 : Fin 13) ∈ t))
      at tests
    change C.eval u = true ↔ _
    rw [ext]
    cases eq : D.eval u with
    | true =>
      obtain ⟨p, hp, _, l, hl, hnear⟩ := tests.1.1 eq
      exact ⟨fun _ => ⟨p, hp, l, hl, hnear⟩, fun _ => rfl⟩
    | false =>
      rw [tests.2 eq]
      simp only [Bool.false_or, Bool.or_eq_true, decide_eq_true_eq]
      rw [bonus]
      constructor
      · rintro (⟨hp, l, hl, hn⟩ | ⟨p, hp, _, l, hl, hn⟩)
        · exact ⟨3, hp, l, hl, hn⟩
        · exact ⟨p, hp, l, hl, hn⟩
      · rintro ⟨p, hp, l, hl, hn⟩
        by_cases hmember : p.val ∈ ([0,1,2,3,5] : List ℕ)
        · rcases (split p).1 hmember with hcore | rfl
          · have he := tests.1.2 ⟨p, hp, hcore, l, hl, hn⟩
            rw [eq] at he
            cases he
          · exact Or.inl ⟨hp, l, hl, hn⟩
        · exact Or.inr ⟨p, hp, hmember, l, hl, hn⟩
  change (∀ p l : Fin 13, near p l → C.eval (List.ofFn (vec {p} {l})) = true) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 →
      C.eval (List.ofFn (vec s (off s))) = false ∧ C.eval (List.ofFn (vec (off s) s)) = false
  constructor
  · intro p l incident
    exact (exactEval _ _).2 ⟨p, by simp, l, by simp, incident⟩
  · intro s _
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p, hp, l, hl, incident⟩ := (exactEval _ _).1 h
      exact (Finset.mem_filter.mp hl).2 p hp incident
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨p, hp, l, hl, incident⟩ := (exactEval _ _).1 h
      apply (Finset.mem_filter.mp hp).2 l hl
      simpa [near, Nat.add_comm] using incident
