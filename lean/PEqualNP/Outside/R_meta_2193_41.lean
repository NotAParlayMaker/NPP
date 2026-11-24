import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A nonredundant final conjunction must have two distinct factors.
-- Each factor can change while any four specified raw inputs stay fixed.
-- Every set of four vertices misses an edge. Switching on both endpoints
-- forces both factors true while preserving the four specified inputs.
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_2193_41
    (single : ∀ (gs : List Gate) (a : Fin 13), gs.length = 13 → FanInTwo ⟨gs,0⟩ →
      (∀ j : Fin gs.length, ∀ i ∈ (gs.get j).inputs, i < 10+j.val) →
      (∀ p : Fin 9, ∃ g ∈ gs, p.val ∈ g.inputs) →
      let w := fun (i : Nat) (x : Fin 9 → Bool) => ((Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 1])).getD i false
      ∃ x, w (10+a.val) x ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (pair : ∀ (gs : List Gate) (a : Fin 13), gs.length = 13 → FanInTwo ⟨gs,0⟩ →
      (∀ j : Fin gs.length, ∀ i ∈ (gs.get j).inputs, i < 10+j.val) →
      (∀ p : Fin 9, ∃ g ∈ gs, p.val ∈ g.inputs) →
      let w := fun (i : Nat) (x : Fin 9 → Bool) => ((Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 1])).getD i false
      let changes := fun i : Nat => ∀ v : Fin 4 → Fin 9, ∃ x y,
        (∀ t, x (v t) = y (v t)) ∧ w i x ≠ w i y
      a.val < 12 → changes (10+a.val) → changes 22 →
      ∃ x, (w (10+a.val) x && w 22 x) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : Fin (13 : ℕ)),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ (x5 : Fin x1.length), ∀ x6 ∈ (x1.get x5).inputs, x6 < (10 : ℕ) + ↑x5) →         (∀ (x6 : Fin (9 : ℕ)), ∃ x7 ∈ x1, ↑x6 ∈ x7.inputs) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ))]);             (x8.getD ((10 : ℕ) + ↑x2) Bool.false && x8.getD (22 : ℕ) Bool.false) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro gs a size fan legal used
  let w := fun (i : Nat) (x : Fin 9 → Bool) => ((Circuit.mk gs 0).wires (List.ofFn x ++ [x 0 || x 1])).getD i false
  let goal := fun x : Fin 9 → Bool => (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)
  let es := ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9))
  change ∃ x, (w (10+a.val) x && w 22 x) ≠ goal x
  by_contra! good
  have full (x : Fin 9 → Bool) (hx : goal x = true) :
      w (10+a.val) x = true ∧ w 22 x = true :=
    Bool.and_eq_true_iff.mp ((good x).trans hx)
  have one (i : Fin 13) : ∃ x, w (10+i.val) x ≠ goal x :=
    single gs i size fan legal used
  have properA : ∃ x, w (10+a.val) x = false := by
    obtain ⟨x,hx⟩ := one 12
    have g := good x
    change w 22 x ≠ goal x at hx
    exact ⟨x, by cases h : w (10+a.val) x <;> simp_all only [Bool.true_and]⟩
  have properB : ∃ x, w 22 x = false := by
    obtain ⟨x,hx⟩ := one a
    have g := good x
    exact ⟨x, by cases h : w 22 x <;> simp_all only [Bool.and_true]⟩
  have distinct : a.val < 12 := by
    by_contra! h
    have e : 10+a.val = 22 := by omega
    obtain ⟨x,hx⟩ := one a
    have g := good x
    rw [e] at g hx
    simp_all
  have missed : ∀ a b c d : Fin 9, ∃ e ∈ es,
      a ≠ e.1 ∧ a ≠ e.2 ∧ b ≠ e.1 ∧ b ≠ e.2 ∧
      c ≠ e.1 ∧ c ≠ e.2 ∧ d ≠ e.1 ∧ d ≠ e.2 := by decide
  have changeWire (i : Nat) (reject : ∃ z, w i z = false)
      (accept : ∀ z, goal z = true → w i z = true) (v : Fin 4 → Fin 9) :
      ∃ x y, (∀ t, x (v t) = y (v t)) ∧ w i x ≠ w i y := by
    obtain ⟨z,hz⟩ := reject
    obtain ⟨e,he,h0,h1,h2,h3,h4,h5,h6,h7⟩ := missed (v 0) (v 1) (v 2) (v 3)
    let y := fun p => if p = e.1 ∨ p = e.2 then true else z p
    have hy1 : y e.1 = true := by simp [y]
    have hy2 : y e.2 = true := by simp [y]
    have hits : goal y = true := by
      simp only [es, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Prod.fst, Prod.snd] at hy1 hy2 <;> simp [goal,hy1,hy2]
    refine ⟨z,y,?_, by rw [hz,accept y hits]; decide⟩
    intro t
    fin_cases t <;> simp [y,h0,h1,h2,h3,h4,h5,h6,h7]
  obtain ⟨x,hx⟩ := pair gs a size fan legal used distinct
    (changeWire _ properA (fun z h => (full z h).1))
    (changeWire _ properB (fun z h => (full z h).2))
  exact hx (good x)

