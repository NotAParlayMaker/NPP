import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3064_1
  (h1 :
    let W := fun (x : Fin 512) (i : Fin 10) => if i.val = 9 then x.val.testBit 4 || x.val.testBit 6 else x.val.testBit i.val
    let small := fun (c : Fin 512 → Bool) => ∃ S : Finset (Fin 10), S.card ≤ 8 ∧ ∀ u v, (∀ i ∈ S, W u i = W v i) → c u = c v
    let target := fun (x : Fin 512) => ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any (fun m => (x.val &&& m) == m)
    ∀ a b : Fin 512 → Bool, (∀ x, (a x && b x) = target x) → ¬(small a ∧ small b))
  (h2 :
    let W := fun (x : Fin 512) (i : Fin 10) => if i.val = 9 then x.val.testBit 4 || x.val.testBit 6 else x.val.testBit i.val
    let small := fun (c : Fin 512 → Bool) => ∃ S : Finset (Fin 10), S.card ≤ 8 ∧ ∀ u v, (∀ i ∈ S, W u i = W v i) → c u = c v
    let target := fun (x : Fin 512) => ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any (fun m => (x.val &&& m) == m)
    ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
      gs.length ≤ 13 → PEqualNP.MetaComplexity.FanInTwo ⟨gs,0⟩ →
      (∀ g ∈ gs, ∀ i ∈ g.inputs, i ≤ 23) →
      let v := fun (i : Fin 24) (x : Fin 512) =>
        (((⟨gs,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
          (List.ofFn (fun j : Fin 9 => x.val.testBit j.val) ++ [W x 9])).getD i.val false)
      ∀ i j, ¬(small (v i) ∧ small (v j)) → ∃ x, (v i x && v j x) ≠ target x) :
  ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro gs js len fan valid argc
  by_contra! good
  let assignment := fun (x : Fin 512) (i : Fin 9) => x.val.testBit i.val
  let v := fun (i : Fin 24) (x : Fin 512) =>
    (((⟨gs,0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
      (List.ofFn (assignment x) ++ [assignment x 4 || assignment x 6])).getD i.val false)
  let targ := fun (x : Fin 512) => ([3,6,12,24,17,33,66,132,264,160,320,288] : List Nat).any (fun m => (x.val &&& m) == m)
  have graph : ∀ x : Fin 512, targ x = (assignment x 0 && assignment x 1 ||
      assignment x 1 && assignment x 2 || assignment x 2 && assignment x 3 ||
      assignment x 3 && assignment x 4 || assignment x 4 && assignment x 0 ||
      assignment x 0 && assignment x 5 || assignment x 1 && assignment x 6 ||
      assignment x 2 && assignment x 7 || assignment x 3 && assignment x 8 ||
      assignment x 5 && assignment x 7 || assignment x 6 && assignment x 8 ||
      assignment x 8 && assignment x 5) := by decide +kernel
  have bad (i j : Fin 24) (ok : ∀ x, (v i x && v j x) = targ x) : False := by
    obtain ⟨x, hx⟩ := h2 gs len fan valid i j (h1 (v i) (v j) ok)
    exact hx (ok x)
  cases js with
  | nil =>
    have e := good (assignment 0)
    exact e (show true ≠ false by decide)
  | cons i tail =>
    cases tail with
    | nil =>
      apply bad i i
      intro x
      rw [graph]
      have h := Classical.not_not.mp (good (assignment x))
      change ((v i x) && true) = _ at h
      simpa only [Bool.and_true, Bool.and_self] using h
    | cons j tail =>
      have nil : tail = [] := by
        have total : tail.length + 1 + 1 ≤ 2 := argc
        have z : tail.length = 0 := by omega
        simpa using z
      subst tail
      apply bad i j
      intro x
      rw [graph]
      have h := Classical.not_not.mp (good (assignment x))
      change ((v i x) && ((v j x) && true)) = _ at h
      simpa only [Bool.and_true] using h
