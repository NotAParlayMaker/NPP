import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Cut after six gates. The tail can observe at most one more boundary wire
than it has gates; all other boundary signals may be set to false. -/
theorem PEqualNP.Outside.R_meta_1866_601
    (support : ∀ (C : Circuit) (n : ℕ), FanInTwo C → ∃ T : Finset ℕ, T.card ≤ C.size + 1 ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ T, x.getD i false = y.getD i false) → C.eval x = C.eval y)
    (search : ∀ (P D : Circuit) (s : List (Fin 11)) (T : Finset ℕ),
      FanInTwo P → FanInTwo D → P.size ≤ 6 → D.size ≤ 7 → s.length ≤ 2 → T.card ≤ D.size + 1 →
      ∃ r : ℕ, r < 512 ∧
        let x := fun i : Fin 9 => r.testBit i.val
        let w := List.ofFn x ++ [x 0 && x 3]
        let z := P.wires (w ++ [GateOp.and.eval (s.map fun j => w.getD j.val false)])
        D.eval (List.ofFn fun i : Fin z.length => decide (i.val ∈ T) && z.getD i.val false) ≠
          (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit r) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (Fin (11 : ℕ))),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x2.length ≤ (2 : ℕ) →
      (∀ (x5 : Fin (9 : ℕ) → Bool),
      have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ))];
      x1.eval (x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : Fin (11 : ℕ)) => x6.getD (↑x7) Bool.false) x2)]) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) →
      (14 : ℕ) ≤ x1.size := by
  intro C s hC hs hc
  by_contra! small
  let P : Circuit := ⟨C.gates.take 6, 0⟩
  let D : Circuit := ⟨C.gates.drop 6, C.output⟩
  have splitG : P.gates ++ D.gates = C.gates := List.take_append_drop ..
  have hp : FanInTwo P := fun g hg => hC g (splitG ▸ List.mem_append_left _ hg)
  have hd : FanInTwo D := fun g hg => hC g (splitG ▸ List.mem_append_right _ hg)
  have lp : P.size ≤ 6 := by
    change (C.gates.take 6).length ≤ 6
    simp
  have ld : D.size ≤ 7 := by
    change (C.gates.drop 6).length ≤ 7
    rw [List.length_drop]
    change C.gates.length < 14 at small
    omega
  obtain ⟨T, hT, agree⟩ := support D (11 + P.size) hd
  obtain ⟨r, hr, bad⟩ := search P D s T hp hd lp ld hs hT
  let x := fun i : Fin 9 => r.testBit i.val
  let w := List.ofFn x ++ [x 0 && x 3]
  let u := w ++ [GateOp.and.eval (s.map fun j => w.getD j.val false)]
  let z := P.wires u
  let masked := List.ofFn fun i : Fin z.length => decide (i.val ∈ T) && z.getD i.val false
  change D.eval masked ≠ _ at bad
  have lengths (gs : List Gate) (v : List Bool) :
      (Circuit.wires ⟨gs, 0⟩ v).length = v.length + gs.length := by
    delta Circuit.wires
    induction gs generalizing v with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp; omega
  have hz : z.length = 11 + P.size := by
    change (Circuit.wires ⟨P.gates, 0⟩ u).length = _
    rw [lengths]
    change u.length + P.gates.length = 11 + P.gates.length
    simp [u, w]
  have he : D.eval masked = D.eval z := by
    apply agree masked z (by simpa [masked] using hz) hz
    intro i hi
    by_cases h : i < z.length
    · simp [masked, List.getD_eq_getElem?_getD, h, hi]
    · simp [masked, List.getD_eq_getElem?_getD, h]
  have joint : D.eval z = C.eval u := by
    dsimp only [z]
    delta Circuit.eval Circuit.wires
    rw [← List.foldl_append]
    change ((P.gates ++ D.gates).foldl _ u).getD C.output false = _
    rw [splitG]
  apply bad
  rw [he, joint, show C.eval u = _ from hc x]
  have table : ∀ k : Fin 512,
      (let v := fun i : Fin 9 => k.val.testBit i.val
       v 0 && v 1 || v 1 && v 2 || v 2 && v 3 || v 3 && v 4 || v 4 && v 0 || v 0 && v 5 || v 1 && v 6 || v 2 && v 7 || v 3 && v 8 || v 5 && v 7 || v 6 && v 8 || v 8 && v 5) = (13407807929942597099574024998205833215954161342674683743641748147961386925543098525491161778167860937561653934618390979850991987668714682019968625024891080 : ℕ).testBit k.val := by
    decide +kernel
  exact table ⟨r, hr⟩
