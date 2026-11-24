import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2373_3
    (geometry : ∀ (A B : Finset (Fin 10)), (∀ e ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10)),
      (e.1 ∈ A ∧ e.2 ∈ A) ∨ (e.1 ∈ B ∧ e.2 ∈ B)) →
      10 ≤ max A.card B.card ∨ (4 ≤ min A.card B.card ∧ 9 ≤ max A.card B.card) ∨ (6 ≤ min A.card B.card ∧ 8 ≤ max A.card B.card))
    (core : ∀ (D : Circuit) (a b : ℕ) (A B : Finset (Fin 10)), FanInTwo D → D.size ≤ 18 →
      (10 ≤ max A.card B.card ∨ (4 ≤ min A.card B.card ∧ 9 ≤ max A.card B.card) ∨ (6 ≤ min A.card B.card ∧ 8 ≤ max A.card B.card)) →
      let W := fun (x : Fin 10 → Bool) (w : ℕ) => (D.wires (List.ofFn x)).getD w false
      (∀ i ∈ A, ∃ j : Fin 10, i ≠ j ∧ W (fun k => decide (k = i ∨ k = j)) a = true) →
      (∀ i ∈ B, ∃ j : Fin 10, i ≠ j ∧ W (fun k => decide (k = i ∨ k = j)) b = true) →
      (∃ x, W x a = true ∧ W x b = false) → (∃ x, W x a = false ∧ W x b = true) →
      ¬ ∀ x, (W x a || W x b) = (fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) x) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  classical
  intro gate C a b first fan limit
  dsimp only
  intro onlyA onlyB off
  let D : Circuit := ⟨gate :: C.gates, C.output⟩
  let W := fun (x : Fin 10 → Bool) (w : ℕ) => (D.wires (List.ofFn x)).getD w false
  let E := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)] : List (Fin 10 × Fin 10))
  let G := (fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))))
  have dFan : FanInTwo D := by
    intro q h
    rcases List.mem_cons.mp h with rfl | tail
    · exact first q (by simp)
    · exact fan q tail
  have dSize : D.size ≤ 18 := by
    change (gate :: C.gates).length ≤ 18
    change C.gates.length ≤ 17 at limit
    simpa only [List.length_cons] using Nat.succ_le_succ limit
  have agree (x : Fin 10 → Bool) : G x = E.any (fun e => x e.1 && x e.2) := rfl
  have value (x : Fin 10 → Bool) : G x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    rw [agree]
    simp only [E, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  by_contra missing
  have allRows (x : Fin 10 → Bool) : (W x a || W x b) = G x := by
    cases truth : G x
    · have h := off x ((value x).symm.trans truth)
      change W x a = false ∧ W x b = false at h
      simp [h.1, h.2]
    · cases left : W x a
      · cases right : W x b
        · exact False.elim (missing ⟨x, (value x).symm.trans truth, left, right⟩)
        · rfl
      · rfl
  let S (w : ℕ) := Finset.univ.filter (fun i : Fin 10 => ∃ j : Fin 10, i ≠ j ∧ W (fun k => decide (k = i ∨ k = j)) w = true)
  have both (w : ℕ) (i j : Fin 10) (ne : i ≠ j) (h : W (fun k => decide (k = i ∨ k = j)) w = true) :
      i ∈ S w ∧ j ∈ S w := by
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, ne, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, ne.symm, ?_⟩⟩
    simpa only [or_comm] using h
  have count := geometry (S a) (S b) (by
    intro e he
    have distinct : ∀ e ∈ E, e.1 ≠ e.2 := by decide
    let x := fun k : Fin 10 => decide (k = e.1 ∨ k = e.2)
    have hit : G x = true := by
      rw [agree]
      exact List.any_eq_true.mpr ⟨e, he, by simp [x]⟩
    have h := (allRows x).trans hit
    rcases Bool.or_eq_true_iff.mp h with l | r
    · exact Or.inl (both a _ _ (distinct e he) l)
    · exact Or.inr (both b _ _ (distinct e he) r))
  exact core D a b (S a) (S b) dFan dSize count
    (fun _ h => (Finset.mem_filter.mp h).2) (fun _ h => (Finset.mem_filter.mp h).2) onlyA onlyB allRows

