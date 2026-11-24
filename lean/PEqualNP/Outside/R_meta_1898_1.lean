import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1898_1
    (compress : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∃ x y, PEqualNP.MetaComplexity.circuitFun 26 C x ≠
        PEqualNP.MetaComplexity.circuitFun 26 C y) →
      ∃ D : PEqualNP.AndCount.AndCountCircuit 26, D.WellFormed ∧
        D.size ≤ {i : Fin C.gates.length | (C.gates.get i).op = .and}.ncard ∧
        ∀ U : Finset (Fin 26), D.eval U =
          PEqualNP.MetaComplexity.circuitFun 26 C (fun i => decide (i ∈ U)))
    (geometry :
      let inc (p w : Fin 13) := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
      ∀ P : Finset (Fin 13),
        let W := Finset.univ.filter (fun w => ∀ p ∈ P, ¬ inc p w)
        (P.card = 3 ∧ W.card = 4 ∨ P.card = 4 ∧ W.card = 3) →
        (∀ p ∉ P, ∃ w ∈ W, inc p w) ∧
        (¬ ∃ w, ∀ p ∈ P, inc p w) ∧ (¬ ∃ p, ∀ w ∈ W, inc p w))
    (bound :
      let inc (p w : Fin 13) := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26, D.WellFormed →
        (∀ p w : Fin 13, inc p w → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 w} = true) →
        (∀ P : Finset (Fin 13),
          let W := Finset.univ.filter (fun w => ∀ p ∈ P, ¬ inc p w)
          (P.card = 3 ∧ W.card = 4 ∨ P.card = 4 ∧ W.card = 3) →
          D.eval ((P.image (Fin.castAdd 13)) ∪ (W.image (Fin.natAdd 13))) = false) →
        13 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (13 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  intro C hmono hpos hneg
  let inc (p w : Fin 13) := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
  let avoid (P : Finset (Fin 13)) := Finset.univ.filter (fun w => ∀ p ∈ P, ¬ inc p w)
  let row (P : Finset (Fin 13)) := (P.image (Fin.castAdd 13)) ∪ ((avoid P).image (Fin.natAdd 13))
  have positive (p w : Fin 13) (h : inc p w) :
      PEqualNP.MetaComplexity.circuitFun 26 C
        (fun i => decide (i ∈ ({Fin.castAdd 13 p, Fin.natAdd 13 w} : Finset (Fin 26)))) = true := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hpos p w h
  have negative (P : Finset (Fin 13))
      (h : P.card = 3 ∧ (avoid P).card = 4 ∨ P.card = 4 ∧ (avoid P).card = 3) :
      PEqualNP.MetaComplexity.circuitFun 26 C (fun i => decide (i ∈ row P)) = false := by
    obtain ⟨closed, hpoints, hlines⟩ := geometry P h
    have hw (w : Fin 13) : w ∈ avoid P ↔ ∀ p ∈ P, ¬ inc p w := by
      simp only [avoid, Finset.mem_filter, Finset.mem_univ, true_and]
    have hr (i : Fin 26) : i ∈ row P ↔
        (∃ p ∈ P, i = Fin.castAdd 13 p) ∨ ∃ w : Fin 13,
          i = Fin.natAdd 13 w ∧ ∀ p ∈ P, ¬ inc p w := by
      simp only [row, Finset.mem_union, Finset.mem_image, hw]
      constructor
      · rintro (⟨p, hp, rfl⟩ | ⟨w, hw, rfl⟩)
        · exact Or.inl ⟨p, hp, rfl⟩
        · exact Or.inr ⟨w, rfl, hw⟩
      · rintro (⟨p, hp, rfl⟩ | ⟨w, rfl, hw⟩)
        · exact Or.inl ⟨p, hp, rfl⟩
        · exact Or.inr ⟨w, hw, rfl⟩
    simp only [hr]
    apply hneg P
    · intro p hp
      obtain ⟨w, hW, hi⟩ := closed p hp
      exact ⟨w, (hw w).mp hW, hi⟩
    · exact ⟨hpoints, fun ⟨p, hp⟩ => hlines ⟨p, fun w hW => hp w ((hw w).mp hW)⟩⟩
  let P : Finset (Fin 13) := {0, 1, 2}
  have hP : P.card = 3 ∧ (avoid P).card = 4 ∨ P.card = 4 ∧ (avoid P).card = 3 := by
    decide +kernel
  obtain ⟨D, hD, hsize, heval⟩ := compress C hmono
    ⟨(fun i => decide (i ∈ ({Fin.castAdd 13 (0 : Fin 13), Fin.natAdd 13 (0 : Fin 13)} : Finset (Fin 26)))),
      (fun i => decide (i ∈ row P)), by
        rw [positive 0 0 (Or.inl rfl), negative P hP]
        decide⟩
  apply (bound D hD ?_ ?_).trans hsize
  · intro p w h
    rw [heval]
    exact positive p w h
  · intro Q
    dsimp only
    intro h
    change D.eval (row Q) = false
    rw [heval]
    exact negative Q h
