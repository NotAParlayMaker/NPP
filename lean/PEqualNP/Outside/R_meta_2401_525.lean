import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2401_525
    (complete : ∀ (P : Finset (Fin 13)) (W : Fin 13 → Prop) [DecidablePred W]
      (x : Fin 26 → Bool),
      (∀ i, x i = true ↔ (∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ w, i = Fin.natAdd 13 w ∧ W w) →
      x = Fin.append (fun p => decide (p ∈ P)) (fun w => decide (W w)))
    (classify :
      let D : Finset (Fin 13) := {0,1,3,9}
      let I := fun p w : Fin 13 => ∃ d ∈ D, p = w + d
      let reps : List (ℕ × ℕ) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
      let orbit := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
        let bit := fun (a b : ℕ) (i : Fin 13) =>
          if dual then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
        Fin.append (bit z.1 z.2) (bit z.2 z.1)
      ∀ P : Finset (Fin 13),
      let W := fun w : Fin 13 => ∀ p ∈ P, ¬ I p w
      (∀ p ∉ P, ∃ w, W w ∧ I p w) →
      (¬ (∃ w, ∀ p ∈ P, I p w) ∧ ¬ (∃ p, ∀ w, W w → I p w)) →
      ∃ z ∈ reps, ∃ m ∈ ([1,3,9] : List (Fin 13)), ∃ t d,
        Fin.append (fun p => decide (p ∈ P)) (fun w => decide (W w)) = orbit z m t d)
    (search :
      let D : Finset (Fin 13) := {0,1,3,9}
      let I := fun p w : Fin 13 => ∃ d ∈ D, p = w + d
      let reps : List (ℕ × ℕ) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
      let orbit := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
        let bit := fun (a b : ℕ) (i : Fin 13) =>
          if dual then b.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
        Fin.append (bit z.1 z.2) (bit z.2 z.1)
      ∃ (q : Fin 4) (C : Circuit), Monotone2 C ∧ NestedCover.ReadsBack 27 C ∧ C.size ≤ 62 ∧
        let j : Fin 26 := if q.val = 1 then 1 else if q.val = 3 then 14 else 13
        let aug := fun (x : Fin 26 → Bool) =>
          Fin.lastCases (if decide (q.val = 0) = true then x 0 && x j else x 0 || x j) x
        (∀ p w, I p w → circuitFun 27 C
          (aug fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
        ∀ z ∈ reps, ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ t d,
          circuitFun 27 C (aug (orbit z m t d)) = false) :∃ (x1 : Fin (4 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x2 ∧       x2.size ≤ (62 : ℕ) ∧         have x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => ∃ x6 ∈ x3, x4 = x5 + x6;         have x5 : Fin (26 : ℕ) := if ↑x1 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x1 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x6 : Bool := Decidable.decide (↑x1 = (0 : ℕ));         have x7 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x6 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x5 else x7 (0 : Fin (26 : ℕ)) || x7 x5) x7 x8;         (∀ (x8 x9 : Fin (13 : ℕ)), x4 x8 x9 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x8 ∨ x11 = Fin.natAdd (13 : ℕ) x9)) = Bool.true) ∧           ∀ (x8 : Finset (Fin (13 : ℕ))),             have x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => ∀ x10 ∈ x8, ¬x4 x10 x9;             (∀ x10 ∉ x8, ∃ (x12 : Fin (13 : ℕ)), x9 x12 ∧ x4 x10 x12) → ((¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x8, x4 x12 x11) ∧ ¬∃ (x11 : Fin (13 : ℕ)), ∀ (x12 : Fin (13 : ℕ)), x9 x12 → x4 x11 x12) → ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ (x13 : Fin (26 : ℕ)), x12 x13 = Bool.true ↔ (∃ x14 ∈ x8, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ (x14 : Fin (13 : ℕ)), x13 = Fin.natAdd (13 : ℕ) x14 ∧ x9 x14) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 x12) = Bool.false := by
  dsimp only at search classify ⊢
  obtain ⟨q,C,mono,back,size,positive,negative⟩ := search
  refine ⟨q,C,mono,back,size,positive,?_⟩
  intro P closed generic x hx
  let D : Finset (Fin 13) := {0,1,3,9}
  let I := fun p w : Fin 13 => ∃ d ∈ D, p = w + d
  let W := fun w : Fin 13 => ∀ p ∈ P, ¬ I p w
  have cx := complete P W x hx
  obtain ⟨z,hz,m,hm,t,d,row⟩ := classify P closed generic
  rw [cx, row]
  exact negative z hz m hm t d
