import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Lines one, two, three and six form a quadrangle. Their six intersection
-- points and four private points support the remaining incidence test.
-- Nine other lines each supply a shared point pair to the small circuit.
set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_2567_319
    (small : ∃ (p : Fin 9 → Fin 4 → Fin 13) (D : Circuit),
      p 0 0 = 0 ∧ p 0 1 = 1 ∧
      (∀ (r : Fin 9) (a : Fin 13), (a.val + (([0,4,5,7,8,9,10,11,12] : List (Fin 13)).getD r.val 0).val) % 13 ∈ ([0,1,3,9] : List ℕ) ↔ ∃ j, p r j = a) ∧
      Monotone2 D ∧ D.output < 35 + D.size ∧ D.size ≤ 18 ∧
      ∀ s t : Finset (Fin 13),
        D.eval ((List.ofFn (fun i : Fin 13 => decide (i ∈ s)) ++ List.ofFn (fun i : Fin 13 => decide (i ∈ t))) ++ List.ofFn (fun r : Fin 9 => decide (p r 0 ∈ s ∨ p r 1 ∈ s))) = true ↔
          ∃ a ∈ s, ∃ l ∈ t, l ∈ ([1,2,3,6] : List (Fin 13)) ∧ (a.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ))
    (extend : ∀ (p : Fin 9 → Fin 4 → Fin 13) (D : Circuit),
      p 0 0 = 0 → p 0 1 = 1 → Monotone2 D → D.output < 35 + D.size →
      ∃ A : Circuit, Monotone2 A ∧ A.size ≤ D.size + 44 ∧ ∀ s t : Finset (Fin 13),
        let x := List.ofFn (fun i : Fin 13 => decide (i ∈ s)) ++ List.ofFn (fun i : Fin 13 => decide (i ∈ t))
        A.eval (x ++ [decide ((0 : Fin 13) ∈ s ∨ (1 : Fin 13) ∈ s)]) = true ↔
          D.eval (x ++ List.ofFn (fun r : Fin 9 => decide (p r 0 ∈ s ∨ p r 1 ∈ s))) = true ∨
            ∃ r : Fin 9, ([0,4,5,7,8,9,10,11,12] : List (Fin 13)).getD r.val 0 ∈ t ∧ ∃ j : Fin 4, p r j ∈ s) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.GateOp) (x2 : Fin (26 : ℕ)) (x3 : Fin (26 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (x1 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x1 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧     (x2, x3) ∈ [((0 : Fin (26 : ℕ)), (1 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (13 : Fin (26 : ℕ))), ((0 : Fin (26 : ℕ)), (15 : Fin (26 : ℕ)))] ∧       PEqualNP.MetaComplexity.Monotone2 x4 ∧         x4.size ≤ (62 : ℕ) ∧           let x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => (↑x5 + ↑x6) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];           have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x7);           have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x7 : Finset (Fin (13 : ℕ))) => {x8 : Fin (13 : ℕ) | ∀ x9 ∈ x7, ¬x5 x9 x8};           have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x8 x9 : Finset (Fin (13 : ℕ))) => x4.eval (List.ofFn (x6 x8 x9) ++ [x1.eval [x6 x8 x9 x2, x6 x8 x9 x3]]);           (∀ (x9 x10 : Fin (13 : ℕ)), x5 x9 x10 → x8 {x9} {x10} = Bool.true) ∧ ∀ (x9 : Finset (Fin (13 : ℕ))), x9.card ≤ (3 : ℕ) → x8 x9 (x7 x9) = Bool.false ∧ x8 (x7 x9) x9 = Bool.false := by
  obtain ⟨p, D, p0, p1, block, mono, live, short, test⟩ := small
  obtain ⟨A, am, ac, eval⟩ := extend p D p0 p1 mono live
  refine ⟨.or, 0, 1, A, Or.inr rfl, by decide, am, by omega, ?_⟩
  let near (a l : Fin 13) := (a.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let row (r : Fin 9) := ([0,4,5,7,8,9,10,11,12] : List (Fin 13)).getD r.val 0
  let vector (s t : Finset (Fin 13)) (i : Fin 26) :=
    if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ s) else decide (Fin.ofNat 13 i.val ∈ t)
  let off (s : Finset (Fin 13)) := Finset.univ.filter (fun l => ∀ a ∈ s, ¬near a l)
  let read (s t : Finset (Fin 13)) := A.eval (List.ofFn (vector s t) ++
    [GateOp.or.eval [vector s t 0, vector s t 1]])
  change (∀ a l : Fin 13, near a l → read {a} {l} = true) ∧
    ∀ s : Finset (Fin 13), s.card ≤ 3 → read s (off s) = false ∧ read (off s) s = false
  have split (s t : Finset (Fin 13)) :
      List.ofFn (vector s t) = List.ofFn (fun i : Fin 13 => decide (i ∈ s)) ++ List.ofFn (fun i : Fin 13 => decide (i ∈ t)) := by
    rfl
  have first (s t : Finset (Fin 13)) :
      GateOp.or.eval [vector s t 0, vector s t 1] = decide ((0 : Fin 13) ∈ s ∨ (1 : Fin 13) ∈ s) := by
    change ((decide ((0 : Fin 13) ∈ s)) || ((decide ((1 : Fin 13) ∈ s)) || false)) = _
    simp
  have allLines : ∀ l : Fin 13, l ∈ ([1,2,3,6] : List (Fin 13)) ∨ ∃ r : Fin 9, row r = l := by
    dsimp [row]
    decide +kernel
  have computes (s t : Finset (Fin 13)) : read s t = true ↔ ∃ a ∈ s, ∃ l ∈ t, near a l := by
    dsimp only [read]
    have ev := eval s t
    dsimp only at ev
    rw [split, first, ev, test]
    constructor
    · rintro (⟨a, ha, l, hl, _, h⟩ | ⟨r, hr, j, hj⟩)
      · exact ⟨a, ha, l, hl, h⟩
      · exact ⟨p r j, hj, row r, hr, (block r _).2 ⟨j,rfl⟩⟩
    · rintro ⟨a, ha, l, hl, h⟩
      rcases allLines l with hcore | ⟨r,rfl⟩
      · exact Or.inl ⟨a,ha,l,hl,hcore,h⟩
      · obtain ⟨j,hj⟩ := (block r a).1 h
        exact Or.inr ⟨r,hl,j,hj ▸ ha⟩
  constructor
  · intro a l h
    exact (computes _ _).2 ⟨a, by simp, l, by simp, h⟩
  · intro s _
    constructor
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨a,ha,l,hl,e⟩ := (computes _ _).1 h
      exact (Finset.mem_filter.mp hl).2 a ha e
    · apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨a,ha,l,hl,e⟩ := (computes _ _).1 h
      have symm : near l a := by simpa only [near, Nat.add_comm] using e
      exact (Finset.mem_filter.mp ha).2 l hl symm
