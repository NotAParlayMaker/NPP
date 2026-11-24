import Mathlib
import PEqualNP.Defs

-- Collapse any fan-in-2 monotone circuit for PG(2, 3) generic maximal false inputs into a stripped
-- well-formed AndCountCircuit of size at most the AND-gate count, then apply a 5-level recursive
-- gate-elimination ladder (2pt+1line >= 5, 2pt >= 6, 1pt+1line >= 7, 1pt >= 9, full >= 11) with
-- cyclic symmetry and point-line duality to prove 11 <= size and tight single/pair read-degree
-- bounds, leaving only the size-11 and size-12 constrained AndCountCircuit cases.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_1898_3
    (hSize11 :
      let E (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let G (D : PEqualNP.AndCount.AndCountCircuit 26) (v : Fin 26) : Finset (Fin D.size) :=
        Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26,
        D.WellFormed → D.size = 11 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 26), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        (∀ p l : Fin 13, E p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) →
        (∀ P : Finset (Fin 13),
          (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ E q l) ∧ E p l) →
          ((¬∃ l : Fin 13, ∀ p ∈ P, E p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ E q l) → E p l) →
          D.eval (Finset.univ.filter fun k : Fin 26 =>
            (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ E q l) = false) →
        (∀ v : Fin 26, (G D v).card ≤ 2) →
        (∀ p l : Fin 13, ¬ E p l → (G D (Fin.castAdd 13 p) ∪ G D (Fin.natAdd 13 l)).card ≤ 4) →
        (∀ p1 p2 : Fin 13, p1 ≠ p2 → (G D (Fin.castAdd 13 p1) ∪ G D (Fin.castAdd 13 p2)).card ≤ 5) →
        (∀ l1 l2 : Fin 13, l1 ≠ l2 → (G D (Fin.natAdd 13 l1) ∪ G D (Fin.natAdd 13 l2)).card ≤ 5) →
        False)
    (hSize12 :
      let E (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let G (D : PEqualNP.AndCount.AndCountCircuit 26) (v : Fin 26) : Finset (Fin D.size) :=
        Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i
      ∀ D : PEqualNP.AndCount.AndCountCircuit 26,
        D.WellFormed → D.size = 12 → D.outVars = ∅ →
        (∀ (i : Fin D.size) (v : Fin 26), D.gateVal {v} i = false) →
        (∀ i : Fin D.size, Disjoint (D.leftVars i) (D.rightVars i)) →
        (∀ p l : Fin 13, E p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) →
        (∀ P : Finset (Fin 13),
          (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ E q l) ∧ E p l) →
          ((¬∃ l : Fin 13, ∀ p ∈ P, E p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ E q l) → E p l) →
          D.eval (Finset.univ.filter fun k : Fin 26 =>
            (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ E q l) = false) →
        (∀ v : Fin 26, (G D v).card ≤ 3) →
        (∀ p l : Fin 13, ¬ E p l → (G D (Fin.castAdd 13 p) ∪ G D (Fin.natAdd 13 l)).card ≤ 5) →
        (∀ p1 p2 : Fin 13, p1 ≠ p2 → (G D (Fin.castAdd 13 p1) ∪ G D (Fin.castAdd 13 p2)).card ≤ 6) →
        (∀ l1 l2 : Fin 13, l1 ≠ l2 → (G D (Fin.natAdd 13 l1) ∪ G D (Fin.natAdd 13 l2)).card ≤ 6) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x3 ∨ x6 = Fin.natAdd (13 : ℕ) x4)) = Bool.true) → (∀ (x4 : Finset (Fin (13 : ℕ))), (∀ x5 ∉ x4, ∃ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) ∧ (x5 = x7 ∨ x5 = x7 + (1 : Fin (13 : ℕ)) ∨ x5 = x7 + (3 : Fin (13 : ℕ)) ∨ x5 = x7 + (9 : Fin (13 : ℕ)))) → ((¬∃ (x6 : Fin (13 : ℕ)), ∀ x7 ∈ x4, x7 = x6 ∨ x7 = x6 + (1 : Fin (13 : ℕ)) ∨ x7 = x6 + (3 : Fin (13 : ℕ)) ∨ x7 = x6 + (9 : Fin (13 : ℕ))) ∧ ¬∃ (x6 : Fin (13 : ℕ)), ∀ (x7 : Fin (13 : ℕ)), (∀ x8 ∈ x4, ¬(x8 = x7 ∨ x8 = x7 + (1 : Fin (13 : ℕ)) ∨ x8 = x7 + (3 : Fin (13 : ℕ)) ∨ x8 = x7 + (9 : Fin (13 : ℕ)))) → x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun ((13 : ℕ) + (13 : ℕ)) x1 fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ (x8 : Fin (13 : ℕ)), x7 = Fin.natAdd (13 : ℕ) x8 ∧ ∀ x9 ∈ x4, ¬(x9 = x8 ∨ x9 = x8 + (1 : Fin (13 : ℕ)) ∨ x9 = x8 + (3 : Fin (13 : ℕ)) ∨ x9 = x8 + (9 : Fin (13 : ℕ))))) = Bool.false) → (13 : ℕ) ≤ {x5 : Fin x1.gates.length | (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
  -- Part 0: Pure decidable Fin 13 arithmetic and PG(2, 3) orbit geometry (before classical)
  have f13_sub_add : ∀ a b : Fin 13, a - b + b = a := by decide
  have f13_add_sub : ∀ a b : Fin 13, a + b - b = a := by decide
  have f13_add_neg : ∀ a b : Fin 13, a + b + (-b) = a := by decide
  have f13_neg_add : ∀ a b : Fin 13, a + (-b) + b = a := by decide
  have f13_neg_add2 : ∀ p l : Fin 13, -l + (p + l) = p := by decide
  have f13_neg_add3 : ∀ p l : Fin 13, -p + (p + l) = l := by decide
  have f13_sub_sub : ∀ a b c : Fin 13, a - b - c = a - (c + b) := by decide
  have f13_add_sub_sub : ∀ a b c : Fin 13, a + b - c = a - (c - b) := by decide
  have f13_sub_eq_add_neg : ∀ a b : Fin 13, a - b = a + (-b) := by decide
  have f13_neg_neg : ∀ a : Fin 13, -(-a) = a := by decide
  have f13_zero_add : ∀ a : Fin 13, 0 + a = a := by decide
  have f13_sub_zero : ∀ a b : Fin 13, a - b = 0 ↔ a = b := by decide
  have f13_neg_inj : ∀ a b : Fin 13, -a = -b ↔ a = b := by decide
  let incB (p l : Fin 13) : Bool := decide (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)
  let orbsP : List ℕ :=
    [29, 39, 71, 77, 83, 85, 101, 105, 135, 141, 195, 201, 275, 281, 297, 329, 337, 549,
     7, 13, 19, 21, 25, 35, 37, 41, 67, 69, 73, 81, 97, 131, 133, 137, 265, 273]
  let orbsW : List ℕ :=
    [2592, 392, 896, 2816, 644, 2688, 2432, 2306, 776, 800, 772, 770, 580, 2624, 2114, 2562, 2564, 2184,
     904, 2848, 708, 2720, 2656, 456, 2440, 2370, 900, 2944, 2818, 2692, 2434, 780, 808, 802, 2626, 2628]
  let orbP (r : Fin 36) (p : Fin 13) : Bool := (orbsP.getD r.val 0).testBit p.val
  let orbW (r : Fin 36) (l : Fin 13) : Bool := (orbsW.getD r.val 0).testBit l.val
  have horb_w_spec : ∀ (r : Fin 36) (l : Fin 13),
      orbW r l = (List.finRange 13).all (fun p => !(orbP r p && incB p l)) := by
    decide +kernel
  have horb_max : ∀ (r : Fin 36) (p : Fin 13),
      orbP r p = false → ∃ l : Fin 13, orbW r l = true ∧ incB p l = true := by
    decide +kernel
  have horb_noncoll : ∀ (r : Fin 36) (l : Fin 13),
      ∃ p : Fin 13, orbP r p = true ∧ incB p l = false := by
    decide +kernel
  have horb_nonconc : ∀ (r : Fin 36) (p : Fin 13),
      ∃ l : Fin 13, orbW r l = true ∧ incB p l = false := by
    decide +kernel
  have horb_ne : ∀ (r1 r2 : Fin 36) (c : Fin 13),
      (r1 ≠ r2 ∨ c ≠ 0) → ∃ p : Fin 13, orbP r1 p ≠ orbP r2 (p - c) := by
    decide +kernel
  let rows0 : List (Fin 36 × Fin 13) := [(0, 0), (0, 9), (0, 10), (0, 11), (1, 0), (1, 8), (1, 11), (1, 12), (2, 0), (2, 7), (2, 11), (2, 12), (3, 0), (3, 7), (3, 10), (3, 11), (4, 0), (4, 7), (4, 9), (4, 12), (5, 0), (5, 7), (5, 9), (5, 11), (6, 0), (6, 7), (6, 8), (6, 11), (7, 0), (7, 7), (7, 8), (7, 10), (8, 0), (8, 6), (8, 11), (8, 12), (9, 0), (9, 6), (9, 10), (9, 11), (10, 0), (10, 6), (10, 7), (10, 12), (11, 0), (11, 6), (11, 7), (11, 10), (12, 0), (12, 5), (12, 9), (12, 12), (13, 0), (13, 5), (13, 9), (13, 10), (14, 0), (14, 5), (14, 8), (14, 10), (15, 0), (15, 5), (15, 7), (15, 10), (16, 0), (16, 5), (16, 7), (16, 9), (17, 0), (17, 4), (17, 8), (17, 11), (18, 0), (18, 11), (18, 12), (19, 0), (19, 10), (19, 11), (20, 0), (20, 9), (20, 12), (21, 0), (21, 9), (21, 11), (22, 0), (22, 9), (22, 10), (23, 0), (23, 8), (23, 12), (24, 0), (24, 8), (24, 11), (25, 0), (25, 8), (25, 10), (26, 0), (26, 7), (26, 12), (27, 0), (27, 7), (27, 11), (28, 0), (28, 7), (28, 10), (29, 0), (29, 7), (29, 9), (30, 0), (30, 7), (30, 8), (31, 0), (31, 6), (31, 12), (32, 0), (32, 6), (32, 11), (33, 0), (33, 6), (33, 10), (34, 0), (34, 5), (34, 10), (35, 0), (35, 5), (35, 9)]
  have rows0_nodup : rows0.Nodup := by
    decide +kernel
  have rows0_ok : rows0.all (fun rc => orbP rc.1 (0 - rc.2)) = true := by
    decide +kernel
  have hL5_bool :
      (List.finRange 13).all (fun p2 =>
        (List.finRange 13).all (fun l =>
          (p2 == 0) || incB 0 l || incB p2 l ||
          (let Y := (List.finRange 13).filter (fun m => (m != l) && !incB 0 m && !incB p2 m)
           let R := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2) && orbW rc.1 (l - rc.2))
           (Y.length == 5) &&
           Y.all (fun m => Nat.ble 5 (R.filter (fun rc => orbW rc.1 (m - rc.2))).length) &&
           Y.all (fun m => R.any (fun rc => !orbW rc.1 (m - rc.2))) &&
           Y.all (fun m1 => Y.all (fun m2 => (m1 == m2) ||
             (R.any (fun rc => orbW rc.1 (m1 - rc.2) && !orbW rc.1 (m2 - rc.2)) &&
              R.any (fun rc => !orbW rc.1 (m1 - rc.2) && !orbW rc.1 (m2 - rc.2)))))))) = true := by
    decide +kernel
  have hL4_bool :
      (List.finRange 13).all (fun p2 =>
        (p2 == 0) ||
        (let Y := (List.finRange 13).filter (fun m => !incB 0 m && !incB p2 m)
         let R := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2))
         (Y.length == 6) &&
         Y.all (fun m => Nat.ble 9 (R.filter (fun rc => orbW rc.1 (m - rc.2))).length) &&
         Y.all (fun m => R.any (fun rc => !orbW rc.1 (m - rc.2))) &&
         Y.all (fun m1 => Y.all (fun m2 => (m1 == m2) ||
           (R.any (fun rc => orbW rc.1 (m1 - rc.2) && !orbW rc.1 (m2 - rc.2)) &&
            R.any (fun rc => !orbW rc.1 (m1 - rc.2) && !orbW rc.1 (m2 - rc.2))))))) = true := by
    decide +kernel
  have hL3_bool :
      (List.finRange 13).all (fun l0 =>
        incB 0 l0 ||
        (let X := (List.finRange 13).filter (fun q => (q != 0) && !incB q l0)
         let R := rows0.filter (fun rc => orbW rc.1 (l0 - rc.2))
         (X.length == 8) &&
         X.all (fun q => R.any (fun rc => orbP rc.1 (q - rc.2))) &&
         X.all (fun q => R.any (fun rc => !orbP rc.1 (q - rc.2))) &&
         X.all (fun q1 => X.all (fun q2 => (q1 == q2) ||
           (R.any (fun rc => orbP rc.1 (q1 - rc.2) && !orbP rc.1 (q2 - rc.2)) &&
            R.any (fun rc => !orbP rc.1 (q1 - rc.2) && !orbP rc.1 (q2 - rc.2))))))) = true := by
    decide +kernel
  have hL2_bool :
      (let Y := (List.finRange 13).filter (fun l => !incB 0 l)
       (Y.length == 9) &&
       Y.all (fun l => rows0.any (fun rc => orbW rc.1 (l - rc.2))) &&
       Y.all (fun l => rows0.any (fun rc => !orbW rc.1 (l - rc.2))) &&
       Y.all (fun l1 => Y.all (fun l2 => (l1 == l2) ||
         (rows0.any (fun rc => orbW rc.1 (l1 - rc.2) && !orbW rc.1 (l2 - rc.2)) &&
          rows0.any (fun rc => !orbW rc.1 (l1 - rc.2) && !orbW rc.1 (l2 - rc.2)))))) = true := by
    decide +kernel
  have hL1_geom :
      let R := (List.finRange 36).flatMap fun r => (List.finRange 13).map fun c => (r, c)
      (∀ p : Fin 13, ∃ rc ∈ R, orbP rc.1 (p - rc.2) = true) ∧
      (∀ p : Fin 13, ∃ rc ∈ R, orbP rc.1 (p - rc.2) = false) ∧
      (∀ l : Fin 13, ∃ rc ∈ R, orbW rc.1 (l - rc.2) = true) ∧
      (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃ rc ∈ R, orbP rc.1 (p1 - rc.2) = true ∧ orbP rc.1 (p2 - rc.2) = false) ∧
      (∀ p1 p2 : Fin 13, p1 ≠ p2 → ∃ rc ∈ R, orbP rc.1 (p1 - rc.2) = false ∧ orbP rc.1 (p2 - rc.2) = false) := by
    decide +kernel
  classical
  intro C hm hPos hNeg
  have op_and_eval : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun _ => rfl
  have op_or_eval : ∀ l : List Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun _ => rfl
  have sideTrue_def : ∀ {k : ℕ} (U B : Finset (Fin 26)) (F : Finset (Fin k)) (i : Fin k) (val : Fin k → Bool),
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
        decide ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ val j = true) := fun _ _ _ _ _ => rfl
  have eval_def : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)),
      E.eval U = decide ((∃ v ∈ E.outVars, v ∈ U) ∨ ∃ j ∈ E.outGates, E.gateVal U j = true) := fun _ _ => rfl
  -- Part 1: Basic AndCountCircuit 26 evaluation helpers
  have sideTrue_congr : ∀ {k : ℕ} (U B : Finset (Fin 26)) (F : Finset (Fin k)) (i : Fin k)
      (val val' : Fin k → Bool), (∀ j : Fin k, j < i → val j = val' j) →
      PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val =
        PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i val' := by
    intro k U B F i val val' h
    rw [sideTrue_def, sideTrue_def, decide_eq_decide]
    constructor
    · intro h1
      rcases h1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, by rw [← h j hlt]; exact hv⟩
    · intro h1
      rcases h1 with h1 | h2
      · exact Or.inl h1
      · rcases h2 with ⟨j, hj, hlt, hv⟩
        exact Or.inr ⟨j, hj, hlt, by rw [h j hlt]; exact hv⟩
  have fuel_indep : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (d d' : ℕ) (i : Fin E.size), i.val < d → i.val < d' →
      E.gateValFuel U d i = E.gateValFuel U d' i := by
    intro E U d
    induction d with
    | zero =>
      intro d' i h
      exact absurd h (Nat.not_lt_zero _)
    | succ e ih =>
      intro d' i h h'
      cases d' with
      | zero => exact absurd h' (Nat.not_lt_zero _)
      | succ e' =>
        have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateValFuel U e' j := by
          intro j hj
          have hji : j.val < i.val := hj
          exact ih e' j (by omega) (by omega)
        show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) =
             (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e') &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e'))
        rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
            sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
  have gateVal_eq : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)) (i : Fin E.size),
      E.gateVal U i =
        (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateVal U) &&
         PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateVal U)) := by
    intro E U i
    have hi : i.val < E.size := i.2
    obtain ⟨e, he⟩ : ∃ e, E.size = e + 1 := ⟨E.size - 1, by omega⟩
    have key : ∀ j : Fin E.size, j < i → E.gateValFuel U e j = E.gateVal U j := by
      intro j hj
      have hji : j.val < i.val := hj
      exact fuel_indep E U e E.size j (by omega) j.2
    have h1 : E.gateVal U i = E.gateValFuel U (e + 1) i :=
      fuel_indep E U E.size (e + 1) i i.2 (by omega)
    rw [h1]
    show (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U e) &&
          PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U e)) = _
    rw [sideTrue_congr U (E.leftVars i) (E.leftGates i) i _ _ key,
        sideTrue_congr U (E.rightVars i) (E.rightGates i) i _ _ key]
  have gateValFuel_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → ∀ (d : ℕ) (i : Fin E.size), E.gateValFuel U d i = true → E.gateValFuel V d i = true := by
    intro E U V hUV d
    induction d with
    | zero => intro i h; cases h
    | succ d ih =>
      intro i h
      change (PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.leftVars i) (E.leftGates i) i (E.gateValFuel U d) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue U (E.rightVars i) (E.rightGates i) i (E.gateValFuel U d)) = true at h
      change (PEqualNP.AndCount.AndCountCircuit.sideTrue V (E.leftVars i) (E.leftGates i) i (E.gateValFuel V d) &&
              PEqualNP.AndCount.AndCountCircuit.sideTrue V (E.rightVars i) (E.rightGates i) i (E.gateValFuel V d)) = true
      rw [Bool.and_eq_true] at h ⊢
      constructor
      · have hL := h.1
        rw [sideTrue_def] at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with h1 | h2
        · rcases h1 with ⟨v, hv, hu⟩
          exact Or.inl ⟨v, hv, hUV hu⟩
        · rcases h2 with ⟨j, hj, hlt, hv⟩
          exact Or.inr ⟨j, hj, hlt, ih j hv⟩
      · have hR := h.2
        rw [sideTrue_def] at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with h1 | h2
        · rcases h1 with ⟨v, hv, hu⟩
          exact Or.inl ⟨v, hv, hUV hu⟩
        · rcases h2 with ⟨j, hj, hlt, hv⟩
          exact Or.inr ⟨j, hj, hlt, ih j hv⟩
  have gateVal_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → ∀ i : Fin E.size, E.gateVal U i = true → E.gateVal V i = true := by
    intro E U V hUV i h
    exact gateValFuel_mono E hUV E.size i h
  have eval_mono : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) {U V : Finset (Fin 26)},
      U ⊆ V → E.eval U = true → E.eval V = true := by
    intro E U V hUV h
    rw [eval_def] at h ⊢
    rw [decide_eq_true_eq] at h ⊢
    rcases h with h1 | h2
    · rcases h1 with ⟨v, hv, hu⟩
      exact Or.inl ⟨v, hv, hUV hu⟩
    · rcases h2 with ⟨j, hj, hv⟩
      exact Or.inr ⟨j, hj, gateVal_mono E hUV j hv⟩

  -- Part 2: Collapse Monotone2 C into a well-formed AndCountCircuit 26 D0
  let wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
    gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
  have wiresFrom_append : ∀ (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
    intro gs1 gs2 w; simp [wiresFrom, List.foldl_append]
  have wiresFrom_ext : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
    | cons g gs ih =>
      intro w
      let v := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
      refine ⟨v :: t, ?_, by simp [hl]⟩
      have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
      rw [hstep, ht]
      simp
  have length_wiresFrom : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (wiresFrom gs w).length = w.length + gs.length := by
    intro gs w
    obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
    rw [ht, List.length_append, hl]
  have getD_wiresFrom_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ),
      i < w.length → (wiresFrom gs w).getD i false = w.getD i false := by
    intro gs w i h
    obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
    rw [ht, List.getD_append _ _ _ _ h]
  have getD_wiresFrom_take : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k i : ℕ),
      k ≤ gs.length →
      (wiresFrom (gs.take k) w).getD i false =
        if i < w.length + k then (wiresFrom gs w).getD i false else false := by
    intro gs w k i hk
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left hk]
    split_ifs with hi
    · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
      conv_rhs => rw [hsplit, wiresFrom_append]
      exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
    · rw [List.getD_eq_default]
      omega
  have getD_wiresFrom_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (k : ℕ)
      (hk : k < gs.length),
      (wiresFrom gs w).getD (w.length + k) false =
        (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i =>
          if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
    intro gs w k hk
    have hsplit : gs = gs.take k ++ gs[k]'hk :: gs.drop (k + 1) := by
      have h1 := (List.take_append_drop k gs).symm
      rw [List.drop_eq_getElem_cons hk] at h1
      exact h1
    have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
      rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
    have heq : wiresFrom gs w =
        wiresFrom (gs.drop (k + 1))
          (wiresFrom (gs.take k) w ++
            [(gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
      conv_lhs => rw [hsplit, wiresFrom_append]
      rfl
    have hsnoc : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := fun l b => by simp
    rw [heq, getD_wiresFrom_lt]
    · conv_lhs => rw [← hlen, hsnoc]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
    · rw [List.length_append, hlen]; simp
  let T_and : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j : Fin C.gates.length => (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  let A_and : Finset ℕ := T_and.image Fin.val
  have hA_card : A_and.card = {x5 : Fin C.gates.length | (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard := by
    have h1 : A_and.card = T_and.card := Finset.card_image_of_injective T_and Fin.val_injective
    have h2 : (T_and : Set (Fin C.gates.length)) =
        {x5 : Fin C.gates.length | (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
      ext j; simp [T_and]
    rw [h1, ← h2, Set.ncard_coe_finset]
  let k0 : ℕ := A_and.card
  let ord : Fin k0 ↪o ℕ := A_and.orderEmbOfFin rfl
  have memOrd : ∀ i : Fin k0, ord i ∈ A_and := fun i => A_and.orderEmbOfFin_mem rfl i
  have allAnd : ∀ (j : ℕ) (hj : j < C.gates.length), C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∃ i : Fin k0, ord i = j := by
    intro j hj ha
    have hT : (⟨j, hj⟩ : Fin C.gates.length) ∈ T_and := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    have hA : j ∈ A_and := Finset.mem_image.mpr ⟨⟨j, hj⟩, hT, rfl⟩
    change j ∈ Set.range (A_and.orderEmbOfFin rfl)
    rwa [Finset.range_orderEmbOfFin]
  have okOrd : ∀ i : Fin k0, ∃ h : ord i < C.gates.length, C.gates[ord i].op = PEqualNP.CircuitLowerBounds.GateOp.and := by
    intro i
    obtain ⟨j, hjT, hjv⟩ := Finset.mem_image.mp (memOrd i)
    have hop := (Finset.mem_filter.mp hjT).2
    refine ⟨hjv ▸ j.isLt, ?_⟩
    simpa [← hjv] using hop
  let collVal (U : Finset (Fin 26)) (v : Fin k0 → Bool) (s : Finset (Fin 26) × Finset (Fin k0)) : Bool :=
    decide ((∃ x ∈ s.1, x ∈ U) ∨ ∃ i ∈ s.2, v i = true)
  let collCollect (L : List ℕ) (s : ℕ → Finset (Fin 26) × Finset (Fin k0)) : Finset (Fin 26) × Finset (Fin k0) :=
    (L.toFinset.biUnion (fun j => (s j).1), L.toFinset.biUnion (fun j => (s j).2))
  have collCollect_true : ∀ (U : Finset (Fin 26)) (v : Fin k0 → Bool) (L : List ℕ)
      (s : ℕ → Finset (Fin 26) × Finset (Fin k0)),
      collVal U v (collCollect L s) = true ↔ ∃ j ∈ L, collVal U v (s j) = true := by
    intro U v L s
    simp only [collVal, collCollect, decide_eq_true_eq, Finset.mem_biUnion, List.mem_toFinset]
    constructor
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨x, ⟨j, hjL, hxs⟩, hxU⟩
        exact ⟨j, hjL, Or.inl ⟨x, hxs, hxU⟩⟩
      · rcases h2 with ⟨i, ⟨j, hjL, his⟩, hvi⟩
        exact ⟨j, hjL, Or.inr ⟨i, his, hvi⟩⟩
    · intro h
      rcases h with ⟨j, hjL, hjv⟩
      rcases hjv with h1 | h2
      · rcases h1 with ⟨x, hxs, hxU⟩
        exact Or.inl ⟨x, ⟨j, hjL, hxs⟩, hxU⟩
      · rcases h2 with ⟨i, his, hvi⟩
        exact Or.inr ⟨i, ⟨j, hjL, his⟩, hvi⟩
  let collOrig (U : Finset (Fin 26)) (w : ℕ) : Bool :=
    (wiresFrom C.gates (List.ofFn (fun i : Fin 26 => decide (i ∈ U)))).getD w false
  have coll_gate : ∀ (U : Finset (Fin 26)) (j : ℕ) (h : j < C.gates.length),
      collOrig U (26 + j) = (C.gates[j]'h).op.eval ((C.gates[j]'h).inputs.map
        (fun i => if i < 26 + j then collOrig U i else false)) := by
    intro U j h
    simpa only [collOrig, List.length_ofFn] using
      getD_wiresFrom_gate C.gates (List.ofFn (fun i : Fin 26 => decide (i ∈ U))) j h
  let collV (U : Finset (Fin 26)) (j : Fin k0) : Bool := collOrig U (26 + ord j)
  have coll_prior : ∀ (w : ℕ),
      (∀ i < w, ∃ s : Finset (Fin 26) × Finset (Fin k0), (∀ j ∈ s.2, 26 + ord j ≤ i) ∧
        ∀ U : Finset (Fin 26), collVal U (collV U) s = collOrig U i) →
      ∃ f : ℕ → Finset (Fin 26) × Finset (Fin k0), (∀ i j, j ∈ (f i).2 → 26 + ord j < w) ∧
        ∀ i (U : Finset (Fin 26)), collVal U (collV U) (f i) = if i < w then collOrig U i else false := by
    intro w ih
    let f (i : ℕ) : Finset (Fin 26) × Finset (Fin k0) := if hi : i < w then (ih i hi).choose else (∅, ∅)
    refine ⟨f, ?_, ?_⟩
    · intro i j hj
      by_cases hi : i < w
      · simp only [f, dite_eq_left hi] at hj
        exact Nat.lt_of_le_of_lt ((ih i hi).choose_spec.1 _ hj) hi
      · simp [f, hi] at hj
    · intro i U
      by_cases hi : i < w
      · simpa only [f, dite_eq_left hi, ite_eq_left hi] using (ih i hi).choose_spec.2 U
      · simp [f, hi, collVal]
  have coll_wires : ∀ w : ℕ, ∃ s : Finset (Fin 26) × Finset (Fin k0),
      (∀ j ∈ s.2, 26 + ord j ≤ w) ∧ ∀ U : Finset (Fin 26), collVal U (collV U) s = collOrig U w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hinput : w < 26
      · let p : Fin 26 := ⟨w, hinput⟩
        refine ⟨({p}, ∅), by simp, ?_⟩
        intro U
        unfold collOrig
        rw [getD_wiresFrom_lt _ _ _ (by simpa using hinput)]
        rw [List.getD_eq_getElem _ _ (by simpa using hinput), List.getElem_ofFn]
        simp [collVal, p]
      let j := w - 26
      have hw : 26 + j = w := by dsimp [j]; omega
      by_cases hj : j < C.gates.length
      · obtain h | h := (hm C.gates[j] (List.getElem_mem hj)).1
        · obtain ⟨z, hz⟩ := allAnd j hj h
          exact ⟨(∅, {z}), by simp [hz, hw], fun U => by simp [collVal, collV, hz, hw]⟩
        · obtain ⟨f, hf, he⟩ := coll_prior w ih
          refine ⟨collCollect C.gates[j].inputs f, ?_, ?_⟩
          · intro z hz
            obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
            exact Nat.le_of_lt (hf i z hi)
          · intro U
            rw [← hw, coll_gate U j hj, show C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or from h]
            apply Bool.eq_iff_iff.mpr
            rw [collCollect_true]
            rw [op_or_eval]
            simp only [List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
            simp_rw [he, hw]
      · refine ⟨(∅, ∅), by simp, ?_⟩
        intro U
        unfold collOrig
        rw [List.getD_eq_default _ _ (by simp only [length_wiresFrom, List.length_ofFn]; omega)]
        simp [collVal]
  have coll_sides : ∀ i : Fin k0, ∃ l r : Finset (Fin 26) × Finset (Fin k0),
      (∀ z ∈ l.2, z < i) ∧ (∀ z ∈ r.2, z < i) ∧
      ∀ U : Finset (Fin 26), U.Nonempty →
        (collVal U (collV U) l && collVal U (collV U) r) = collV U i := by
    intro i
    obtain ⟨h, hop⟩ := okOrd i
    let g := C.gates[ord i]
    have hlen := (hm g (List.getElem_mem h)).2
    obtain ⟨f, hf, he⟩ := coll_prior (26 + ord i) (fun w _ => coll_wires w)
    have ltj : ∀ (a : ℕ) (z : Fin k0), z ∈ (f a).2 → z < i := fun a z hz =>
      ord.lt_iff_lt.mp (Nat.lt_of_add_lt_add_left (hf _ _ hz))
    have gate : ∀ U : Finset (Fin 26),
        collV U i = (g.inputs.map fun j => collVal U (collV U) (f j)).all id := by
      intro U
      dsimp only [collV]
      rw [coll_gate U (ord i) h, hop]
      rw [op_and_eval]; dsimp only [g]
      congr 1
      apply List.map_congr_left
      intro a _
      exact (he a U).symm
    cases hL : g.inputs with
    | nil =>
      refine ⟨(Finset.univ, ∅), (Finset.univ, ∅), by simp, by simp, ?_⟩
      intro U hu
      rw [gate, hL]
      simpa [collVal] using (show ∃ x, x ∈ U from hu)
    | cons a L =>
      cases L with
      | nil =>
        refine ⟨f a, f a, ltj a, ltj a, ?_⟩
        intro U _
        simp [gate, hL]
      | cons b L =>
        have hem : L = [] := by rw [hL] at hlen; simpa using hlen
        subst L
        refine ⟨f a, f b, ltj a, ltj b, ?_⟩
        intro U _
        simp [gate, hL]
  choose lSide rSide hlSide hrSide hvSide using coll_sides
  obtain ⟨oSide, _, hoSide⟩ := coll_wires C.output
  let D0 : PEqualNP.AndCount.AndCountCircuit 26 :=
    ⟨k0, fun i => (lSide i).1, fun i => (lSide i).2,
         fun i => (rSide i).1, fun i => (rSide i).2, oSide.1, oSide.2⟩
  have hD0_size : D0.size = {x5 : Fin C.gates.length | (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
    hA_card
  have hD0_wf : D0.WellFormed := fun i => ⟨hlSide i, hrSide i⟩
  have hD0_eval : ∀ U : Finset (Fin 26), U.Nonempty →
      D0.eval U = PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => Decidable.decide (k ∈ U)) := by
    intro U hU
    have fuel : ∀ (d : ℕ) (i : Fin k0), i.val < d → D0.gateValFuel U d i = collV U i := by
      intro d
      induction d with
      | zero => intro i h; omega
      | succ d ih =>
        intro i hd
        have eqSide : ∀ (s : Finset (Fin 26) × Finset (Fin k0)), (∀ z ∈ s.2, z < i) →
            PEqualNP.AndCount.AndCountCircuit.sideTrue U s.1 s.2 i (D0.gateValFuel U d) = collVal U (collV U) s := by
          intro s hs
          rw [sideTrue_def]; dsimp only [collVal]
          congr 1
          apply propext
          apply or_congr_right
          constructor
          · intro h1
            rcases h1 with ⟨j, hj, hji, hval⟩
            exact ⟨j, hj, (ih j (by have := hji; change j.val < i.val at this; omega)).symm.trans hval⟩
          · intro h1
            rcases h1 with ⟨j, hj, hval⟩
            have hji := hs j hj
            exact ⟨j, hj, hji, (ih j (by change j.val < i.val at hji; omega)).trans hval⟩
        change (PEqualNP.AndCount.AndCountCircuit.sideTrue U (lSide i).1 (lSide i).2 i (D0.gateValFuel U d) &&
                PEqualNP.AndCount.AndCountCircuit.sideTrue U (rSide i).1 (rSide i).2 i (D0.gateValFuel U d)) = _
        rw [eqSide _ (hlSide i), eqSide _ (hrSide i), hvSide i U hU]
    have hgate : ∀ i : Fin k0, D0.gateVal U i = collV U i := fun i => fuel k0 i i.isLt
    have hev : D0.eval U = collOrig U C.output := by
      have h1 : D0.eval U = collVal U (collV U) oSide := by
        rw [eval_def]; simp only [hgate, collVal, D0]
      rw [h1, hoSide U]
    rw [hev]
    show (wiresFrom C.gates (List.ofFn fun i : Fin 26 => decide (i ∈ U))).getD C.output false =
         (C.wires (List.ofFn fun k : Fin 26 => Decidable.decide (k ∈ U))).getD C.output false
    rfl

  -- Part 3: stripCircuit on AndCountCircuit 26
  let stripCircuit (E : PEqualNP.AndCount.AndCountCircuit 26) : PEqualNP.AndCount.AndCountCircuit 26 :=
    ⟨E.size,
     fun i => Finset.univ.filter (fun v =>
       (v ∈ E.leftVars i ∨ ∃ j ∈ E.leftGates i, j < i ∧ E.gateVal {v} j = true) ∧ E.gateVal {v} i = false),
     E.leftGates,
     fun i => Finset.univ.filter (fun v =>
       (v ∈ E.rightVars i ∨ ∃ j ∈ E.rightGates i, j < i ∧ E.gateVal {v} j = true) ∧ E.gateVal {v} i = false),
     E.rightGates,
     Finset.univ.filter (fun v => v ∈ E.outVars ∨ ∃ j ∈ E.outGates, E.gateVal {v} j = true),
     E.outGates⟩
  have strip_wf : ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed → (stripCircuit E).WellFormed :=
    fun _ hw => hw
  have strip_disj : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (i : Fin (stripCircuit E).size),
      Disjoint ((stripCircuit E).leftVars i) ((stripCircuit E).rightVars i) := by
    intro E i
    rw [Finset.disjoint_left]
    intro v hL hR
    have hL' := (Finset.mem_filter.mp hL).2
    have hR' := (Finset.mem_filter.mp hR).2
    have hvL : PEqualNP.AndCount.AndCountCircuit.sideTrue {v} (E.leftVars i) (E.leftGates i) i (E.gateVal {v}) = true := by
      rw [sideTrue_def]
      rw [decide_eq_true_eq]
      rcases hL'.1 with h1 | h2
      · exact Or.inl ⟨v, h1, Finset.mem_singleton_self v⟩
      · exact Or.inr h2
    have hvR : PEqualNP.AndCount.AndCountCircuit.sideTrue {v} (E.rightVars i) (E.rightGates i) i (E.gateVal {v}) = true := by
      rw [sideTrue_def]
      rw [decide_eq_true_eq]
      rcases hR'.1 with h1 | h2
      · exact Or.inl ⟨v, h1, Finset.mem_singleton_self v⟩
      · exact Or.inr h2
    have htrue : E.gateVal {v} i = true := by
      rw [gateVal_eq E {v} i, hvL, hvR]; rfl
    rw [hL'.2] at htrue
    cases htrue
  have strip_gateVal_le : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (k : ℕ) (i : Fin E.size), i.val < k → (stripCircuit E).gateVal U i = true → E.gateVal U i = true := by
    intro E U k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hval
      rw [gateVal_eq (stripCircuit E) U i, Bool.and_eq_true] at hval
      rw [gateVal_eq E U i, Bool.and_eq_true]
      constructor
      · have hL := hval.1
        rw [sideTrue_def] at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with h1 | h2
        · rcases h1 with ⟨v, hv, hvU⟩
          have hv' := (Finset.mem_filter.mp hv).2.1
          rcases hv' with hvB | hjs
          · exact Or.inl ⟨v, hvB, hvU⟩
          · rcases hjs with ⟨j, hjF, hji, hvs⟩
            exact Or.inr ⟨j, hjF, hji, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
        · rcases h2 with ⟨j, hjF, hji, hjv⟩
          exact Or.inr ⟨j, hjF, hji, ih j (by have := hji; change j.val < i.val at this; omega) hjv⟩
      · have hR := hval.2
        rw [sideTrue_def] at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with h1 | h2
        · rcases h1 with ⟨v, hv, hvU⟩
          have hv' := (Finset.mem_filter.mp hv).2.1
          rcases hv' with hvB | hjs
          · exact Or.inl ⟨v, hvB, hvU⟩
          · rcases hjs with ⟨j, hjF, hji, hvs⟩
            exact Or.inr ⟨j, hjF, hji, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
        · rcases h2 with ⟨j, hjF, hji, hjv⟩
          exact Or.inr ⟨j, hjF, hji, ih j (by have := hji; change j.val < i.val at this; omega) hjv⟩
  have strip_gateVal_ge : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26))
      (k : ℕ) (i : Fin E.size), i.val < k → E.gateVal U i = true →
      (∃ v ∈ U, E.gateVal {v} i = true) ∨ (stripCircuit E).gateVal U i = true := by
    intro E U k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi hval
      by_cases hsing : ∃ v ∈ U, E.gateVal {v} i = true
      · exact Or.inl hsing
      · right
        have hno : ∀ v ∈ U, E.gateVal {v} i = false := fun v hvU =>
          Bool.eq_false_iff.mpr (fun hv => hsing ⟨v, hvU, hv⟩)
        rw [gateVal_eq E U i, Bool.and_eq_true] at hval
        rw [gateVal_eq (stripCircuit E) U i, Bool.and_eq_true]
        constructor
        · have hL := hval.1
          rw [sideTrue_def] at hL ⊢
          rw [decide_eq_true_eq] at hL ⊢
          rcases hL with h1 | h2
          · rcases h1 with ⟨v, hvB, hvU⟩
            exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvB, hno v hvU⟩, hvU⟩
          · rcases h2 with ⟨j, hjF, hji, hjv⟩
            rcases ih j (by have := hji; change j.val < i.val at this; omega) hjv with h3 | hj'
            · rcases h3 with ⟨v, hvU, hvs⟩
              exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, hj'⟩
        · have hR := hval.2
          rw [sideTrue_def] at hR ⊢
          rw [decide_eq_true_eq] at hR ⊢
          rcases hR with h1 | h2
          · rcases h1 with ⟨v, hvB, hvU⟩
            exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvB, hno v hvU⟩, hvU⟩
          · rcases h2 with ⟨j, hjF, hji, hjv⟩
            rcases ih j (by have := hji; change j.val < i.val at this; omega) hjv with h3 | hj'
            · rcases h3 with ⟨v, hvU, hvs⟩
              exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
            · exact Or.inr ⟨j, hjF, hji, hj'⟩
  have strip_eval_eq : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)),
      (stripCircuit E).eval U = E.eval U := by
    intro E U
    rw [eval_def, eval_def]
    refine decide_eq_decide.mpr ?_
    constructor
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hvO, hvU⟩
        rcases (Finset.mem_filter.mp hvO).2 with hvC | hjs
        · exact Or.inl ⟨v, hvC, hvU⟩
        · rcases hjs with ⟨j, hjO, hvs⟩
          exact Or.inr ⟨j, hjO, gateVal_mono E (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        exact Or.inr ⟨j, hjO, strip_gateVal_le E U E.size j j.isLt hjv⟩
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hvO, hvU⟩
        exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inl hvO⟩, hvU⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        rcases strip_gateVal_ge E U E.size j j.isLt hjv with h3 | hj'
        · rcases h3 with ⟨v, hvU, hvs⟩
          exact Or.inl ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, Or.inr ⟨j, hjO, hvs⟩⟩, hvU⟩
        · exact Or.inr ⟨j, hjO, hj'⟩
  have strip_gateVal_singleton : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26)
      (i : Fin (stripCircuit E).size) (v : Fin 26), (stripCircuit E).gateVal {v} i = false := by
    intro E i v
    induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin E.size → Fin E.size → Prop)).induction with
    | h i ih =>
      rw [Bool.eq_false_iff]
      intro htrue
      rw [gateVal_eq (stripCircuit E) {v} i, Bool.and_eq_true] at htrue
      have getL : v ∈ (stripCircuit E).leftVars i := by
        have hL := htrue.1
        rw [sideTrue_def] at hL
        rw [decide_eq_true_eq] at hL
        rcases hL with h1 | h2
        · rcases h1 with ⟨u, hu, huv⟩
          rw [Finset.mem_singleton.mp huv] at hu
          exact hu
        · rcases h2 with ⟨j, _, hji, hjv⟩
          rw [ih j hji] at hjv; cases hjv
      have getR : v ∈ (stripCircuit E).rightVars i := by
        have hR := htrue.2
        rw [sideTrue_def] at hR
        rw [decide_eq_true_eq] at hR
        rcases hR with h1 | h2
        · rcases h1 with ⟨u, hu, huv⟩
          rw [Finset.mem_singleton.mp huv] at hu
          exact hu
        · rcases h2 with ⟨j, _, hji, hjv⟩
          rw [ih j hji] at hjv; cases hjv
      exact Finset.disjoint_left.mp (strip_disj E i) getL getR
  have strip_exists : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      ∃ D : PEqualNP.AndCount.AndCountCircuit 26,
        D.size = E.size ∧ D.WellFormed ∧
        (∀ i, Disjoint (D.leftVars i) (D.rightVars i)) ∧
        (∀ (i : Fin D.size) (v : Fin 26), D.gateVal {v} i = false) ∧
        (∀ U, D.eval U = E.eval U) :=
    fun E hw => ⟨stripCircuit E, rfl, strip_wf E hw, strip_disj E, strip_gateVal_singleton E, strip_eval_eq E⟩

  -- Part 4: Gate elimination (L_meta_707 engine)
  let signal {k : ℕ} (U A : Finset (Fin 26)) (P : Finset (Fin k)) (val : Fin k → Bool) : Prop :=
    (∃ v ∈ A, v ∈ U) ∨ ∃ j ∈ P, val j = true
  have gate_spec : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      ∀ (U : Finset (Fin 26)) (i : Fin E.size),
        E.gateVal U i = true ↔
          signal U (E.leftVars i) (E.leftGates i) (E.gateVal U) ∧
          signal U (E.rightVars i) (E.rightGates i) (E.gateVal U) := by
    intro E hw U i
    rw [gateVal_eq, Bool.and_eq_true]
    rw [sideTrue_def, sideTrue_def]; simp only [signal, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rcases h.1 with h1 | h2
        · exact Or.inl h1
        · rcases h2 with ⟨j, hj, _, hv⟩; exact Or.inr ⟨j, hj, hv⟩
      · rcases h.2 with h1 | h2
        · exact Or.inl h1
        · rcases h2 with ⟨j, hj, _, hv⟩; exact Or.inr ⟨j, hj, hv⟩
    · intro h
      refine ⟨?_, ?_⟩
      · rcases h.1 with h1 | h2
        · exact Or.inl h1
        · rcases h2 with ⟨j, hj, hv⟩; exact Or.inr ⟨j, hj, (hw i).1 j hj, hv⟩
      · rcases h.2 with h1 | h2
        · exact Or.inl h1
        · rcases h2 with ⟨j, hj, hv⟩; exact Or.inr ⟨j, hj, (hw i).2 j hj, hv⟩
  let expandVars {m : ℕ} (i : Fin (m + 1)) (B A : Finset (Fin 26)) (P : Finset (Fin (m + 1))) : Finset (Fin 26) :=
    A ∪ if i ∈ P then B else ∅
  let expandRefs {m : ℕ} (i : Fin (m + 1)) (F P : Finset (Fin (m + 1))) : Finset (Fin m) :=
    Finset.univ.filter (fun k => i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F)
  have signal_expand : ∀ {m : ℕ} (i : Fin (m + 1)) (U B A : Finset (Fin 26))
      (F P : Finset (Fin (m + 1))) (val : Fin (m + 1) → Bool) (val' : Fin m → Bool),
      (∀ j ∈ F, j < i) → (val i = true ↔ signal U B F val) →
      (∀ k ∈ expandRefs i F P, val' k = val (i.succAbove k)) →
      (signal U (expandVars i B A P) (expandRefs i F P) val' ↔ signal U A P val) := by
    intro m i U B A F P val val' before expand agree
    have memV : ∀ v : Fin 26, v ∈ expandVars i B A P ↔ v ∈ A ∨ i ∈ P ∧ v ∈ B := by
      intro v; by_cases h : i ∈ P <;> simp [expandVars, h]
    have memR : ∀ k : Fin m, k ∈ expandRefs i F P ↔ i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F := by
      intro k; simp [expandRefs]
    constructor
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hv, hu⟩
        rcases (memV v).mp hv with hvA | hB
        · exact Or.inl ⟨v, hvA, hu⟩
        · exact Or.inr ⟨i, hB.1, expand.mpr (Or.inl ⟨v, hB.2, hu⟩)⟩
      · rcases h2 with ⟨k, hk, ht⟩
        rw [agree k hk] at ht
        rcases (memR k).mp hk with hP | hF
        · exact Or.inr ⟨_, hP, ht⟩
        · exact Or.inr ⟨i, hF.1, expand.mpr (Or.inr ⟨_, hF.2, ht⟩)⟩
    · intro h
      rcases h with h1 | h2
      · rcases h1 with ⟨v, hv, hu⟩
        exact Or.inl ⟨v, (memV v).mpr (Or.inl hv), hu⟩
      · rcases h2 with ⟨j, hj, ht⟩
        by_cases hji : j = i
        · subst j
          rcases expand.mp ht with h3 | h4
          · rcases h3 with ⟨v, hv, hu⟩
            exact Or.inl ⟨v, (memV v).mpr (Or.inr ⟨hj, hv⟩), hu⟩
          · rcases h4 with ⟨l, hl, ht'⟩
            obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (ne_of_lt (before l hl))
            have hk := (memR k).mpr (Or.inr ⟨hj, hl⟩)
            exact Or.inr ⟨k, hk, (agree k hk).trans ht'⟩
        · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
          have hk := (memR k).mpr (Or.inl hj)
          exact Or.inr ⟨k, hk, (agree k hk).trans ht⟩
  let Expandable (E : PEqualNP.AndCount.AndCountCircuit 26) (Dom : Set (Finset (Fin 26))) (i : Fin E.size) : Prop :=
    ∃ B : Finset (Fin 26), ∃ F : Finset (Fin E.size), (∀ j ∈ F, j < i) ∧
      ∀ U ∈ Dom, E.gateVal U i = true ↔ signal U B F (E.gateVal U)
  have remove_one : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (Dom : Set (Finset (Fin 26))) (i : Fin E.size),
      E.WellFormed → Expandable E Dom i →
      ∃ E' : PEqualNP.AndCount.AndCountCircuit 26, ∃ f : Fin E'.size → Fin E.size,
        E'.WellFormed ∧ E'.size + 1 = E.size ∧ StrictMono f ∧
        (∀ j, j ≠ i ↔ ∃ k, f k = j) ∧
        ∀ U ∈ Dom, E'.eval U = E.eval U ∧ ∀ j, E'.gateVal U j = E.gateVal U (f j) := by
    intro E Dom i hw hexp
    obtain ⟨B, F, before, same⟩ := hexp
    rcases E with ⟨s, lv, lg, rv, rg, ov, og⟩
    cases s with
    | zero => exact Fin.elim0 i
    | succ m =>
      let E0 : PEqualNP.AndCount.AndCountCircuit 26 := ⟨m + 1, lv, lg, rv, rg, ov, og⟩
      let E' : PEqualNP.AndCount.AndCountCircuit 26 :=
        ⟨m, fun j => expandVars i B (lv (i.succAbove j)) (lg (i.succAbove j)),
            fun j => expandRefs i F (lg (i.succAbove j)),
            fun j => expandVars i B (rv (i.succAbove j)) (rg (i.succAbove j)),
            fun j => expandRefs i F (rg (i.succAbove j)),
            expandVars i B ov og, expandRefs i F og⟩
      have lt_ref : ∀ (j k : Fin m) (P : Finset (Fin (m + 1))),
          (∀ l ∈ P, l < i.succAbove j) → k ∈ expandRefs i F P → k < j := by
        intro j k P old hk
        apply Fin.succAbove_lt_succAbove_iff.mp
        have hk' : i.succAbove k ∈ P ∨ i ∈ P ∧ i.succAbove k ∈ F := (Finset.mem_filter.mp hk).2
        rcases hk' with hp | hif
        · exact old _ hp
        · exact (before _ hif.2).trans (old i hif.1)
      have hw' : E'.WellFormed := fun j =>
        ⟨fun k hk => lt_ref j k _ (hw (i.succAbove j)).1 hk,
         fun k hk => lt_ref j k _ (hw (i.succAbove j)).2 hk⟩
      refine ⟨E', i.succAbove, hw', rfl, fun j k hjk => Fin.succAbove_lt_succAbove_iff.mpr hjk, ?_, ?_⟩
      · intro j
        refine ⟨Fin.exists_succAbove_eq, ?_⟩
        intro hex; rcases hex with ⟨k, rfl⟩; exact Fin.succAbove_ne i k
      · intro U hU
        have values : ∀ j : Fin m, E'.gateVal U j = E0.gateVal U (i.succAbove j) := by
          intro j
          induction j using (wellFounded_lt : WellFounded ((· < ·) : Fin m → Fin m → Prop)).induction with
          | h j ih =>
            rw [Bool.eq_iff_iff, gate_spec E' hw', gate_spec E0 hw]
            exact and_congr
              (signal_expand i U B _ F _ _ _ before (same U hU)
                (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).1 hk)))
              (signal_expand i U B _ F _ _ _ before (same U hU)
                (fun k hk => ih k (lt_ref j k _ (hw (i.succAbove j)).2 hk)))
        refine ⟨?_, values⟩
        rw [eval_def, eval_def]
        rw [decide_eq_decide]
        exact signal_expand i U B ov F og _ _ before (same U hU) (fun k _ => values k)
  have remove_many : ∀ (Dom : Set (Finset (Fin 26))) (k : ℕ) (E : PEqualNP.AndCount.AndCountCircuit 26),
      E.WellFormed → ∀ (S : Finset (Fin E.size)), S.card = k → (∀ i ∈ S, Expandable E Dom i) →
      ∃ E' : PEqualNP.AndCount.AndCountCircuit 26, E'.WellFormed ∧ E'.size + S.card ≤ E.size ∧
        ∀ U ∈ Dom, E'.eval U = E.eval U := by
    intro Dom k
    induction k with
    | zero =>
      intro E hw S hS _
      exact ⟨E, hw, by simp [hS], fun _ _ => rfl⟩
    | succ k ih =>
      intro E hw S hS expands
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      let i := S.max' hne
      have hi : i ∈ S := S.max'_mem hne
      obtain ⟨E', f, hw', hsize, hmono, hran, hsem⟩ := remove_one E Dom i hw (expands i hi)
      let S' : Finset (Fin E'.size) := Finset.univ.filter (fun j => f j ∈ S)
      have lift_mem : ∀ j : Fin E'.size, j ∈ S' ↔ f j ∈ S := fun j => by simp [S']
      have himg : S'.image f = S.erase i := by
        ext r
        simp only [Finset.mem_image, Finset.mem_erase]
        constructor
        · intro h; rcases h with ⟨j, hj, rfl⟩
          exact ⟨(hran _).mpr ⟨j, rfl⟩, (lift_mem j).mp hj⟩
        · intro h
          obtain ⟨j, rfl⟩ := (hran r).mp h.1
          exact ⟨j, (lift_mem j).mpr h.2, rfl⟩
      have hcard : S'.card = k := by
        have hc := Finset.card_image_of_injective S' hmono.injective
        rw [himg, Finset.card_erase_of_mem hi] at hc
        omega
      have hexp' : ∀ j ∈ S', Expandable E' Dom j := by
        intro j hj
        have hjS := (lift_mem j).mp hj
        obtain ⟨B, F, before, same⟩ := expands (f j) hjS
        let F' : Finset (Fin E'.size) := Finset.univ.filter (fun l => f l ∈ F)
        have hF' : ∀ l : Fin E'.size, l ∈ F' ↔ f l ∈ F := fun l => by simp [F']
        have hnotrem : i ∉ F := fun h =>
          (not_lt_of_ge (Finset.le_max' S (f j) hjS)) (before i h)
        refine ⟨B, F', ?_, ?_⟩
        · intro l hl
          exact hmono.lt_iff_lt.mp (before _ ((hF' l).mp hl))
        · intro U hU
          have values := (hsem U hU).2
          rw [values j, same U hU]
          constructor
          · intro h
            rcases h with h1 | h2
            · exact Or.inl h1
            · rcases h2 with ⟨l, hl, ht⟩
              have hli : l ≠ i := fun he => hnotrem (he ▸ hl)
              obtain ⟨q, rfl⟩ := (hran l).mp hli
              exact Or.inr ⟨q, (hF' q).mpr hl, (values q).trans ht⟩
          · intro h
            rcases h with h1 | h2
            · exact Or.inl h1
            · rcases h2 with ⟨l, hl, ht⟩
              exact Or.inr ⟨f l, (hF' l).mp hl, (values l).symm.trans ht⟩
      obtain ⟨E'', hw'', hbd, hout⟩ := ih E' hw' S' hcard hexp'
      exact ⟨E'', hw'', by omega, fun U hU => (hout U hU).trans (hsem U hU).1⟩
  have elim_vertices : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      ∀ (V0 : Finset (Fin 26)),
        let T := Finset.univ.filter (fun i : Fin E.size => ∃ v ∈ V0, v ∈ E.leftVars i ∨ v ∈ E.rightVars i)
        ∃ E' : PEqualNP.AndCount.AndCountCircuit 26, E'.WellFormed ∧ E'.size + T.card ≤ E.size ∧
          ∀ U : Finset (Fin 26), V0 ⊆ U → E'.eval U = E.eval U := by
    intro E hw V0 T
    let Dom : Set (Finset (Fin 26)) := {U : Finset (Fin 26) | V0 ⊆ U}
    apply remove_many Dom T.card E hw T rfl
    intro i hi
    obtain ⟨v, hv0, hvlr⟩ := (Finset.mem_filter.mp hi).2
    rcases hvlr with hvL | hvR
    · refine ⟨E.rightVars i, E.rightGates i, (hw i).2, ?_⟩
      intro U hU
      rw [gate_spec E hw U i]
      have hLtrue : signal U (E.leftVars i) (E.leftGates i) (E.gateVal U) := Or.inl ⟨v, hvL, hU hv0⟩
      exact ⟨fun h => h.2, fun h => ⟨hLtrue, h⟩⟩
    · refine ⟨E.leftVars i, E.leftGates i, (hw i).1, ?_⟩
      intro U hU
      rw [gate_spec E hw U i]
      have hRtrue : signal U (E.rightVars i) (E.rightGates i) (E.gateVal U) := Or.inl ⟨v, hvR, hU hv0⟩
      exact ⟨fun h => h.1, fun h => ⟨h, hRtrue⟩⟩

  -- Part 5: Separates, mergeInput, free_bound_gen, mis_cover_gen, card_le_size_of_deg_le_one
  let Separates (E : PEqualNP.AndCount.AndCountCircuit 26) (Rows : Finset (Finset (Fin 26))) : Prop :=
    ∀ I ∈ Rows, E.eval I = false ∧ ∀ w : Fin 26, w ∉ I → E.eval (insert w I) = true
  let Free (E : PEqualNP.AndCount.AndCountCircuit 26) (v : Fin 26) : Finset (Fin E.size) :=
    Finset.univ.filter (fun i => v ∉ E.leftVars i ∧ v ∉ E.rightVars i)
  let sideL (E : PEqualNP.AndCount.AndCountCircuit 26) (I : Finset (Fin 26)) (i : Fin E.size) : Bool :=
    PEqualNP.AndCount.AndCountCircuit.sideTrue I (E.leftVars i) (E.leftGates i) i (E.gateVal I)
  let sideR (E : PEqualNP.AndCount.AndCountCircuit 26) (I : Finset (Fin 26)) (i : Fin E.size) : Bool :=
    PEqualNP.AndCount.AndCountCircuit.sideTrue I (E.rightVars i) (E.rightGates i) i (E.gateVal I)
  let litSet (E : PEqualNP.AndCount.AndCountCircuit 26) (v : Fin 26) : Finset (Fin E.size × Bool) :=
    Finset.univ.filter (fun p => if p.2 then v ∈ E.rightVars p.1 else v ∈ E.leftVars p.1)
  have litSet_touch_card : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26),
      (∀ i, Disjoint (E.leftVars i) (E.rightVars i)) →
      ∀ v : Fin 26,
        (litSet E v).card = (Finset.univ.filter (fun i : Fin E.size => v ∈ E.leftVars i ∨ v ∈ E.rightVars i)).card ∧
        (litSet E v).card + (Free E v).card = E.size := by
    intro E hdisj v
    have hinj : Set.InjOn Prod.fst (litSet E v : Set (Fin E.size × Bool)) := by
      intro p1 hp1 p2 hp2 heq
      rcases p1 with ⟨g1, b1⟩; rcases p2 with ⟨g2, b2⟩
      dsimp at heq; subst heq
      have h1 := (Finset.mem_filter.mp hp1).2
      have h2 := (Finset.mem_filter.mp hp2).2
      cases b1 <;> cases b2
      · rfl
      · exact (Finset.disjoint_left.mp (hdisj g1) h1 h2).elim
      · exact (Finset.disjoint_left.mp (hdisj g1) h2 h1).elim
      · rfl
    have himg : (litSet E v).image Prod.fst =
        Finset.univ.filter (fun i : Fin E.size => v ∈ E.leftVars i ∨ v ∈ E.rightVars i) := by
      ext g
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, litSet]
      constructor
      · intro h; rcases h with ⟨⟨g', b⟩, hb, rfl⟩
        cases b
        · exact Or.inl hb
        · exact Or.inr hb
      · intro h; rcases h with hL | hR
        · exact ⟨(g, false), hL, rfl⟩
        · exact ⟨(g, true), hR, rfl⟩
    have hc1 : (litSet E v).card =
        (Finset.univ.filter (fun i : Fin E.size => v ∈ E.leftVars i ∨ v ∈ E.rightVars i)).card := by
      rw [← himg, Finset.card_image_of_injOn hinj]
    have hcomp : Finset.univ.filter (fun i : Fin E.size => v ∈ E.leftVars i ∨ v ∈ E.rightVars i) =
        Finset.univ \ Free E v := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Free]
      tauto
    have htot := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Free E v))
    simp only [Finset.card_univ, Fintype.card_fin] at htot
    rw [← hcomp, ← hc1] at htot
    exact ⟨hc1, htot⟩
  have mergeInput : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26) (I J U : Finset (Fin 26)) (v : Fin 26),
      v ∈ I → v ∈ J → U ⊆ I ∪ J → (∀ i ∈ Free E v, sideL E I i = sideL E J i) →
      E.eval U = true → E.eval I = true ∨ E.eval J = true := by
    intro E I J U v hi hj hU hs hev
    have unionSide : ∀ (B : Finset (Fin 26)) (F : Finset (Fin E.size)) (i : Fin E.size),
        (∀ j < i, E.gateVal U j = true → E.gateVal I j = true ∨ E.gateVal J j = true) →
        PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i (E.gateVal U) = true →
        PEqualNP.AndCount.AndCountCircuit.sideTrue I B F i (E.gateVal I) = true ∨
        PEqualNP.AndCount.AndCountCircuit.sideTrue J B F i (E.gateVal J) = true := by
      intro B F i ih hst
      rw [sideTrue_def] at hst; rw [sideTrue_def, sideTrue_def]; simp only [decide_eq_true_eq] at hst ⊢
      rcases hst with h1 | h2
      · rcases h1 with ⟨w, hw, hu⟩
        rcases Finset.mem_union.mp (hU hu) with hI | hJ
        · exact Or.inl (Or.inl ⟨w, hw, hI⟩)
        · exact Or.inr (Or.inl ⟨w, hw, hJ⟩)
      · rcases h2 with ⟨j, hjF, hji, ht⟩
        rcases ih j hji ht with hI | hJ
        · exact Or.inl (Or.inr ⟨j, hjF, hji, hI⟩)
        · exact Or.inr (Or.inr ⟨j, hjF, hji, hJ⟩)
    have gate : ∀ i : Fin E.size, E.gateVal U i = true → E.gateVal I i = true ∨ E.gateVal J i = true := by
      intro i
      induction i using (wellFounded_lt : WellFounded ((· < ·) : Fin E.size → Fin E.size → Prop)).induction with
      | h i ih =>
        intro ht
        rw [gateVal_eq, Bool.and_eq_true] at ht
        rw [gateVal_eq E I, gateVal_eq E J]
        change (sideL E I i && sideR E I i) = true ∨ (sideL E J i && sideR E J i) = true
        have hl : sideL E I i = true ∨ sideL E J i = true := unionSide _ _ i ih ht.1
        have hr : sideR E I i = true ∨ sideR E J i = true := unionSide _ _ i ih ht.2
        simp only [Bool.and_eq_true]
        by_cases h1 : v ∈ E.leftVars i
        · have a : sideL E I i = true := decide_eq_true (Or.inl ⟨v, h1, hi⟩)
          have b : sideL E J i = true := decide_eq_true (Or.inl ⟨v, h1, hj⟩)
          rcases hr with hr | hr
          · exact Or.inl ⟨a, hr⟩
          · exact Or.inr ⟨b, hr⟩
        by_cases h2 : v ∈ E.rightVars i
        · have a : sideR E I i = true := decide_eq_true (Or.inl ⟨v, h2, hi⟩)
          have b : sideR E J i = true := decide_eq_true (Or.inl ⟨v, h2, hj⟩)
          rcases hl with hl | hl
          · exact Or.inl ⟨hl, a⟩
          · exact Or.inr ⟨hl, b⟩
        have hh := hs i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩)
        have hlj : sideL E J i = true := by
          rcases hl with hl | hl
          · exact hh.symm.trans hl
          · exact hl
        have hli : sideL E I i = true := hh.trans hlj
        rcases hr with hr | hr
        · exact Or.inl ⟨hli, hr⟩
        · exact Or.inr ⟨hlj, hr⟩
    rw [eval_def] at hev; rw [eval_def, eval_def]; simp only [decide_eq_true_eq] at hev ⊢
    rcases hev with h1 | h2
    · rcases h1 with ⟨w, hw, hwu⟩
      rcases Finset.mem_union.mp (hU hwu) with hI | hJ
      · exact Or.inl (Or.inl ⟨w, hw, hI⟩)
      · exact Or.inr (Or.inl ⟨w, hw, hJ⟩)
    · rcases h2 with ⟨i, hi', hgt⟩
      rcases gate i hgt with hI | hJ
      · exact Or.inl (Or.inr ⟨i, hi', hI⟩)
      · exact Or.inr (Or.inr ⟨i, hi', hJ⟩)
  have free_bound_gen : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26)
      (Rows : Finset (Finset (Fin 26))) (v : Fin 26),
      Separates E Rows →
      (∀ I ∈ Rows, ∀ J ∈ Rows, I ≠ J → ∃ w ∈ I, w ∉ J) →
      (Rows.filter (fun I => v ∈ I)).card ≤ 2 ^ (Free E v).card := by
    intro E Rows v hsep hincomp
    let Rv := Rows.filter (fun I => v ∈ I)
    let code (x : ↥Rv) (i : ↥(Free E v)) : Bool := sideL E x.1 i.1
    have hinj : Function.Injective code := by
      intro a b hab
      by_contra hne
      have hne1 : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
      have haR : a.1 ∈ Rows := (Finset.mem_filter.mp a.2).1
      have hbR : b.1 ∈ Rows := (Finset.mem_filter.mp b.2).1
      have hav : v ∈ a.1 := (Finset.mem_filter.mp a.2).2
      have hbv : v ∈ b.1 := (Finset.mem_filter.mp b.2).2
      obtain ⟨w, hwa, hwb⟩ := hincomp a.1 haR b.1 hbR hne1
      have he := mergeInput E a.1 b.1 (insert w b.1) v hav hbv
        (Finset.insert_subset (Finset.mem_union_left b.1 hwa) Finset.subset_union_right)
        (fun i hi => congrFun hab ⟨i, hi⟩) ((hsep b.1 hbR).2 w hwb)
      rw [(hsep a.1 haR).1, (hsep b.1 hbR).1] at he
      simp at he
    have hc := Fintype.card_le_of_injective code hinj
    simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool] using hc
  have mis_cover_gen : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26)
      (Rows : Finset (Finset (Fin 26))) (Active : Finset (Fin 26)),
      Separates E Rows → (∀ u ∈ Active, ∃ J ∈ Rows, u ∈ J) →
      ∀ I ∈ Rows, ∃ f : Fin E.size → Option Bool,
        (∀ v ∈ I, ∀ l ∈ litSet E v, f l.1 ≠ some l.2) ∧
        (∀ w ∈ Active, w ∉ I → ∃ l ∈ litSet E w, f l.1 = some l.2) := by
    intro E Rows Active hsep hact I hI
    let f : Fin E.size → Option Bool := fun i =>
      if sideL E I i = false then some false
      else if sideR E I i = false then some true
      else none
    refine ⟨f, ?_, ?_⟩
    · intro v hv l hl
      rcases l with ⟨g, b⟩
      have hlb := (Finset.mem_filter.mp hl).2
      cases b
      · have hsL : sideL E I g = true := decide_eq_true (Or.inl ⟨v, hlb, hv⟩)
        simp only [f, hsL, Bool.true_eq_false, ↓reduceIte]
        split_ifs <;> simp
      · have hsR : sideR E I g = true := decide_eq_true (Or.inl ⟨v, hlb, hv⟩)
        simp only [f, hsR, Bool.true_eq_false, ↓reduceIte]
        split_ifs <;> simp
    · intro w hwA hwI
      have hev : E.eval (insert w I) = true := (hsep I hI).2 w hwI
      have hfl : E.eval I = false := (hsep I hI).1
      let S : Finset (Fin E.size) :=
        Finset.univ.filter (fun i => E.gateVal I i = false ∧ E.gateVal (insert w I) i = true)
      have hSne : S.Nonempty := by
        rw [eval_def] at hev
        rw [decide_eq_true_eq] at hev
        rcases hev with h1 | h2
        · rcases h1 with ⟨u, huO, huIn⟩
          rcases Finset.mem_insert.mp huIn with rfl | huI
          · obtain ⟨J, hJR, hwJ⟩ := hact u hwA
            have het : E.eval J = true := decide_eq_true (Or.inl ⟨u, huO, hwJ⟩)
            rw [(hsep J hJR).1] at het; cases het
          · have het : E.eval I = true := decide_eq_true (Or.inl ⟨u, huO, huI⟩)
            rw [hfl] at het; cases het
        · rcases h2 with ⟨i, hiO, hit⟩
          refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hit⟩⟩
          rw [Bool.eq_false_iff]
          intro hti
          have het : E.eval I = true := decide_eq_true (Or.inr ⟨i, hiO, hti⟩)
          rw [hfl] at het; cases het
      let g := S.min' hSne
      have hgS : g ∈ S := S.min'_mem hSne
      have hgF : E.gateVal I g = false := (Finset.mem_filter.mp hgS).2.1
      have hgT : E.gateVal (insert w I) g = true := (Finset.mem_filter.mp hgS).2.2
      have hmin : ∀ j : Fin E.size, j < g → E.gateVal (insert w I) j = true → E.gateVal I j = true := by
        intro j hj hjt
        by_contra hnf
        have hjf : E.gateVal I j = false := Bool.eq_false_iff.mpr hnf
        have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjf, hjt⟩
        exact (not_le_of_gt hj) (S.min'_le j hjS)
      rw [gateVal_eq E (insert w I) g, Bool.and_eq_true] at hgT
      rw [gateVal_eq E I g] at hgF
      change (sideL E I g && sideR E I g) = false at hgF
      change sideL E (insert w I) g = true ∧ sideR E (insert w I) g = true at hgT
      by_cases hL : sideL E I g = false
      · refine ⟨(g, false), ?_, by simp [f, hL]⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hLT : sideL E (insert w I) g = true := hgT.1
        dsimp only [sideL] at hLT hL; rw [sideTrue_def] at hLT hL
        rw [decide_eq_true_eq] at hLT
        rcases hLT with h1 | h2
        · rcases h1 with ⟨v, hv, hvI⟩
          rcases Finset.mem_insert.mp hvI with rfl | hvi
          · exact hv
          · have ht : decide ((∃ u ∈ E.leftVars g, u ∈ I) ∨
                ∃ j ∈ E.leftGates g, j < g ∧ E.gateVal I j = true) = true :=
              decide_eq_true (Or.inl ⟨v, hv, hvi⟩)
            rw [hL] at ht; cases ht
        · rcases h2 with ⟨j, hj, hji, hjt⟩
          have hjiT := hmin j hji hjt
          have ht : decide ((∃ u ∈ E.leftVars g, u ∈ I) ∨
              ∃ j ∈ E.leftGates g, j < g ∧ E.gateVal I j = true) = true :=
            decide_eq_true (Or.inr ⟨j, hj, hji, hjiT⟩)
          rw [hL] at ht; cases ht
      · have hLt : sideL E I g = true := by
          cases h' : sideL E I g
          · exact (hL h').elim
          · rfl
        have hR : sideR E I g = false := by simp [hLt] at hgF; exact hgF
        refine ⟨(g, true), ?_, by simp [f, hLt, hR]⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hRT : sideR E (insert w I) g = true := hgT.2
        dsimp only [sideR] at hRT hR; rw [sideTrue_def] at hRT hR
        rw [decide_eq_true_eq] at hRT
        rcases hRT with h1 | h2
        · rcases h1 with ⟨v, hv, hvI⟩
          rcases Finset.mem_insert.mp hvI with rfl | hvi
          · exact hv
          · have ht : decide ((∃ u ∈ E.rightVars g, u ∈ I) ∨
                ∃ j ∈ E.rightGates g, j < g ∧ E.gateVal I j = true) = true :=
              decide_eq_true (Or.inl ⟨v, hv, hvi⟩)
            rw [hR] at ht; cases ht
        · rcases h2 with ⟨j, hj, hji, hjt⟩
          have hjiT := hmin j hji hjt
          have ht : decide ((∃ u ∈ E.rightVars g, u ∈ I) ∨
              ∃ j ∈ E.rightGates g, j < g ∧ E.gateVal I j = true) = true :=
            decide_eq_true (Or.inr ⟨j, hj, hji, hjiT⟩)
          rw [hR] at ht; cases ht
  have card_le_size_of_deg_le_one : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26)
      (Rows : Finset (Finset (Fin 26))) (Z : Finset (Fin 26)),
      Separates E Rows →
      (∀ z ∈ Z, ∃ I ∈ Rows, z ∈ I) →
      (∀ z ∈ Z, ∃ I ∈ Rows, z ∉ I) →
      (∀ z1 ∈ Z, ∀ z2 ∈ Z, z1 ≠ z2 → ∃ I ∈ Rows, z1 ∈ I ∧ z2 ∉ I) →
      (∀ z1 ∈ Z, ∀ z2 ∈ Z, z1 ≠ z2 → ∃ I ∈ Rows, z1 ∉ I ∧ z2 ∉ I) →
      (∀ z ∈ Z, (litSet E z).card ≤ 1) →
      Z.card ≤ E.size := by
    intro E Rows Z hsep hmem hout hsame hopp hdeg1
    have hexLit : ∀ z : ↥Z, ∃ l : Fin E.size × Bool, l ∈ litSet E z.1 := by
      intro z
      obtain ⟨I, hIR, hzI⟩ := hout z.1 z.2
      obtain ⟨f, _, hfhit⟩ := mis_cover_gen E Rows Z hsep hmem I hIR
      obtain ⟨l, hl, _⟩ := hfhit z.1 z.2 hzI
      exact ⟨l, hl⟩
    choose pickL hpickL using hexLit
    have huniq : ∀ (z : ↥Z) (l : Fin E.size × Bool), l ∈ litSet E z.1 → l = pickL z := by
      intro z l hl
      exact Finset.card_le_one.mp (hdeg1 z.1 z.2) l hl (pickL z) (hpickL z)
    let phi (z : ↥Z) : Fin E.size := (pickL z).1
    have hinj : Function.Injective phi := by
      intro z1 z2 hphi
      by_contra hne
      have hneV : z1.1 ≠ z2.1 := fun h => hne (Subtype.ext h)
      by_cases hb : (pickL z1).2 = (pickL z2).2
      · have hleq : pickL z1 = pickL z2 := Prod.ext hphi hb
        obtain ⟨I, hIR, hz1I, hz2nI⟩ := hsame z1.1 z1.2 z2.1 z2.2 hneV
        obtain ⟨f, hfav, hfhit⟩ := mis_cover_gen E Rows Z hsep hmem I hIR
        obtain ⟨l, hl2, hfl⟩ := hfhit z2.1 z2.2 hz2nI
        have hl_eq : l = pickL z1 := (huniq z2 l hl2).trans hleq.symm
        exact hfav z1.1 hz1I (pickL z1) (hpickL z1) (hl_eq ▸ hfl)
      · obtain ⟨I, hIR, hz1nI, hz2nI⟩ := hopp z1.1 z1.2 z2.1 z2.2 hneV
        obtain ⟨f, _, hfhit⟩ := mis_cover_gen E Rows Z hsep hmem I hIR
        obtain ⟨l1, hl1, hfl1⟩ := hfhit z1.1 z1.2 hz1nI
        obtain ⟨l2, hl2, hfl2⟩ := hfhit z2.1 z2.2 hz2nI
        rw [huniq z1 l1 hl1] at hfl1
        rw [huniq z2 l2 hl2] at hfl2
        have h1 : f (pickL z2).1 = some (pickL z1).2 := by dsimp only [phi] at hphi; rw [← hphi]; exact hfl1
        have h2 : some (pickL z1).2 = some (pickL z2).2 := h1.symm.trans hfl2
        exact hb (Option.some.inj h2)
    have hc := Fintype.card_le_of_injective phi hinj
    simpa only [Fintype.card_coe, Fintype.card_fin] using hc

  -- Part 6: Circuit automorphism (mapCirc) for cyclic shifts and point-line duality
  let mapCirc (σ : Fin 26 ≃ Fin 26) (E : PEqualNP.AndCount.AndCountCircuit 26) :
      PEqualNP.AndCount.AndCountCircuit 26 :=
    ⟨E.size,
     fun i => (E.leftVars i).map σ.toEmbedding,
     E.leftGates,
     fun i => (E.rightVars i).map σ.toEmbedding,
     E.rightGates,
     E.outVars.map σ.toEmbedding,
     E.outGates⟩
  have mapCirc_wf : ∀ (σ : Fin 26 ≃ Fin 26) (E : PEqualNP.AndCount.AndCountCircuit 26),
      E.WellFormed → (mapCirc σ E).WellFormed := fun _ _ hw => hw
  have mapCirc_gateValFuel : ∀ (σ : Fin 26 ≃ Fin 26) (E : PEqualNP.AndCount.AndCountCircuit 26)
      (U : Finset (Fin 26)) (d : ℕ) (i : Fin E.size),
      (mapCirc σ E).gateValFuel (U.map σ.toEmbedding) d i = E.gateValFuel U d i := by
    intro σ E U d
    induction d with
    | zero => intro i; rfl
    | succ d ih =>
      intro i
      have hside : ∀ (B : Finset (Fin 26)) (F : Finset (Fin E.size)),
          PEqualNP.AndCount.AndCountCircuit.sideTrue (U.map σ.toEmbedding) (B.map σ.toEmbedding) F i
            ((mapCirc σ E).gateValFuel (U.map σ.toEmbedding) d) =
          PEqualNP.AndCount.AndCountCircuit.sideTrue U B F i (E.gateValFuel U d) := by
        intro B F
        rw [sideTrue_def, sideTrue_def, decide_eq_decide]
        constructor
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨v, hvB, hvU⟩
            obtain ⟨u, huB, rfl⟩ := Finset.mem_map.mp hvB
            exact Or.inl ⟨u, huB, by simpa using Finset.mem_map_equiv.mp hvU⟩
          · rcases h2 with ⟨j, hjF, hji, hv⟩
            exact Or.inr ⟨j, hjF, hji, (ih j).symm.trans hv⟩
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨u, huB, huU⟩
            exact Or.inl ⟨σ u, Finset.mem_map.mpr ⟨u, huB, rfl⟩, Finset.mem_map.mpr ⟨u, huU, rfl⟩⟩
          · rcases h2 with ⟨j, hjF, hji, hv⟩
            exact Or.inr ⟨j, hjF, hji, (ih j).trans hv⟩
      show (PEqualNP.AndCount.AndCountCircuit.sideTrue (U.map σ.toEmbedding) ((E.leftVars i).map σ.toEmbedding)
              (E.leftGates i) i ((mapCirc σ E).gateValFuel (U.map σ.toEmbedding) d) &&
            PEqualNP.AndCount.AndCountCircuit.sideTrue (U.map σ.toEmbedding) ((E.rightVars i).map σ.toEmbedding)
              (E.rightGates i) i ((mapCirc σ E).gateValFuel (U.map σ.toEmbedding) d)) = _
      rw [hside (E.leftVars i) (E.leftGates i), hside (E.rightVars i) (E.rightGates i)]
      rfl
  have mapCirc_eval : ∀ (σ : Fin 26 ≃ Fin 26) (E : PEqualNP.AndCount.AndCountCircuit 26) (U : Finset (Fin 26)),
      (mapCirc σ E).eval (U.map σ.toEmbedding) = E.eval U := by
    intro σ E U
    rw [eval_def, eval_def]
    rw [decide_eq_decide]
    have hg : ∀ j : Fin E.size, (mapCirc σ E).gateVal (U.map σ.toEmbedding) j = E.gateVal U j :=
      fun j => mapCirc_gateValFuel σ E U E.size j
    constructor
    · intro h; rcases h with h1 | h2
      · rcases h1 with ⟨v, hvO, hvU⟩
        obtain ⟨u, huO, rfl⟩ := Finset.mem_map.mp hvO
        exact Or.inl ⟨u, huO, by simpa using Finset.mem_map_equiv.mp hvU⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        exact Or.inr ⟨j, hjO, (hg j).symm.trans hjv⟩
    · intro h; rcases h with h1 | h2
      · rcases h1 with ⟨u, huO, huU⟩
        exact Or.inl ⟨σ u, Finset.mem_map.mpr ⟨u, huO, rfl⟩, Finset.mem_map.mpr ⟨u, huU, rfl⟩⟩
      · rcases h2 with ⟨j, hjO, hjv⟩
        exact Or.inr ⟨j, hjO, (hg j).trans hjv⟩

  -- Part 7: PG(2, 3) incidence, 36 cyclic orbits (468 generic max-false rows), and symmetries
  let inc (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
  have inc_iff : ∀ p l : Fin 13, incB p l = true ↔ inc p l := by
    intro p l; simp only [incB, inc, decide_eq_true_eq]
  have inc_shift : ∀ (p l c : Fin 13), inc (p + c) (l + c) ↔ inc p l := by
    intro p l c
    simp only [inc]
    have h1 : p + c = l + c ↔ p = l := add_left_inj c
    have h2 : p + c = l + c + 1 ↔ p = l + 1 := by
      rw [add_right_comm l c 1]; exact add_left_inj c
    have h3 : p + c = l + c + 3 ↔ p = l + 3 := by
      rw [add_right_comm l c 3]; exact add_left_inj c
    have h4 : p + c = l + c + 9 ↔ p = l + 9 := by
      rw [add_right_comm l c 9]; exact add_left_inj c
    rw [h1, h2, h3, h4]
  have inc_sub : ∀ (p l c : Fin 13), inc (p - c) (l - c) ↔ inc p l := by
    intro p l c
    rw [f13_sub_eq_add_neg p c, f13_sub_eq_add_neg l c]
    exact inc_shift p l (-c)
  have inc_neg : ∀ (p l : Fin 13), inc (-l) (-p) ↔ inc p l := by
    intro p l
    have h := inc_shift (-l) (-p) (p + l)
    rw [f13_neg_add2 p l, f13_neg_add3 p l] at h
    exact h.symm
  let rowP (rc : Fin 36 × Fin 13) (p : Fin 13) : Bool := orbP rc.1 (p - rc.2)
  let rowW (rc : Fin 36 × Fin 13) (l : Fin 13) : Bool := orbW rc.1 (l - rc.2)
  let rowPSet (rc : Fin 36 × Fin 13) : Finset (Fin 13) :=
    Finset.univ.filter (fun p => rowP rc p = true)
  let liftRow (P : Finset (Fin 13)) : Finset (Fin 26) :=
    Finset.univ.filter fun k : Fin 26 =>
      (∃ p ∈ P, k = Fin.castAdd 13 p) ∨
      ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ ∀ q ∈ P, ¬ inc q l
  let rowSet (rc : Fin 36 × Fin 13) : Finset (Fin 26) := liftRow (rowPSet rc)
  have rowW_iff : ∀ (rc : Fin 36 × Fin 13) (l : Fin 13),
      rowW rc l = true ↔ ∀ q ∈ rowPSet rc, ¬ inc q l := by
    intro rc l
    dsimp only [rowW]
    rw [horb_w_spec rc.1 (l - rc.2), List.all_eq_true]
    constructor
    · intro hall q hq hinc
      have hqp : orbP rc.1 (q - rc.2) = true := (Finset.mem_filter.mp hq).2
      have h1 := hall (q - rc.2) (List.mem_finRange _)
      have hinc' : incB (q - rc.2) (l - rc.2) = true := (inc_iff _ _).mpr ((inc_sub q l rc.2).mpr hinc)
      simp [hqp, hinc'] at h1
    · intro hall p _
      by_cases hp : orbP rc.1 p = true
      · have hq : p + rc.2 ∈ rowPSet rc := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          simpa [rowP] using hp
        have hni : ¬ inc (p + rc.2) l := hall (p + rc.2) hq
        have hni' : ¬ inc p (l - rc.2) := by
          intro h
          have h' := (inc_shift p (l - rc.2) rc.2).mpr h
          rw [f13_sub_add] at h'; exact hni h'
        have hbf : incB p (l - rc.2) = false := Bool.eq_false_iff.mpr (fun ht => hni' ((inc_iff _ _).mp ht))
        simp [hp, hbf]
      · have hpf : orbP rc.1 p = false := Bool.eq_false_iff.mpr hp
        simp [hpf]
  have mem_rowSet_cast : ∀ (rc : Fin 36 × Fin 13) (p : Fin 13),
      Fin.castAdd 13 p ∈ rowSet rc ↔ rowP rc p = true := by
    intro rc p
    simp only [rowSet, liftRow, Finset.mem_filter, Finset.mem_univ, true_and, rowPSet]
    constructor
    · intro h; rcases h with h1 | h2
      · rcases h1 with ⟨q, hq, heq⟩
        have hpq : p = q := by
          have hv := congrArg Fin.val heq
          exact Fin.ext hv
        exact hpq ▸ hq
      · rcases h2 with ⟨l, heq, _⟩
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
    · intro hp
      exact Or.inl ⟨p, hp, rfl⟩
  have mem_rowSet_nat : ∀ (rc : Fin 36 × Fin 13) (l : Fin 13),
      Fin.natAdd 13 l ∈ rowSet rc ↔ rowW rc l = true := by
    intro rc l
    rw [rowW_iff]
    simp only [rowSet, liftRow, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rcases h with h1 | h2
      · rcases h1 with ⟨p, _, heq⟩
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      · rcases h2 with ⟨l', heq, hall⟩
        have hll : l = l' := by
          have hv := congrArg Fin.val heq
          simp only [Fin.val_natAdd] at hv
          exact Fin.ext (by omega)
        exact hll ▸ hall
    · intro hall
      exact Or.inr ⟨l, rfl, hall⟩
  have row_max : ∀ (rc : Fin 36 × Fin 13) (p : Fin 13),
      p ∉ rowPSet rc → ∃ l : Fin 13, (∀ q ∈ rowPSet rc, ¬ inc q l) ∧ inc p l := by
    intro rc p hp
    have hpf : orbP rc.1 (p - rc.2) = false := by
      rw [Bool.eq_false_iff]
      intro ht
      exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
    obtain ⟨l0, hl0W, hl0inc⟩ := horb_max rc.1 (p - rc.2) hpf
    refine ⟨l0 + rc.2, ?_, ?_⟩
    · rw [← rowW_iff]
      simpa [rowW] using hl0W
    · have h1 := (inc_shift (p - rc.2) l0 rc.2).mpr ((inc_iff _ _).mp hl0inc)
      rw [f13_sub_add] at h1; exact h1
  have row_generic : ∀ (rc : Fin 36 × Fin 13),
      (¬∃ l : Fin 13, ∀ p ∈ rowPSet rc, inc p l) ∧
      (¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ rowPSet rc, ¬ inc q l) → inc p l) := by
    intro rc
    constructor
    · intro hex; rcases hex with ⟨l, hl⟩
      obtain ⟨p0, hp0, hni⟩ := horb_noncoll rc.1 (l - rc.2)
      have hp : p0 + rc.2 ∈ rowPSet rc := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa [rowP] using hp0
      have hinc : inc (p0 + rc.2) l := hl (p0 + rc.2) hp
      have hinc' : inc p0 (l - rc.2) := by
        have h1 := (inc_sub (p0 + rc.2) l rc.2).mpr hinc
        rw [f13_add_sub] at h1; exact h1
      have ht : incB p0 (l - rc.2) = true := (inc_iff _ _).mpr hinc'
      rw [hni] at ht; cases ht
    · intro hex; rcases hex with ⟨p, hp⟩
      obtain ⟨l0, hl0, hni⟩ := horb_nonconc rc.1 (p - rc.2)
      have hlW : rowW rc (l0 + rc.2) = true := by simpa [rowW] using hl0
      have hinc : inc p (l0 + rc.2) := hp (l0 + rc.2) ((rowW_iff rc (l0 + rc.2)).mp hlW)
      have hinc' : inc (p - rc.2) l0 := by
        have h1 := (inc_sub p (l0 + rc.2) rc.2).mpr hinc
        rw [f13_add_sub] at h1; exact h1
      have ht : incB (p - rc.2) l0 = true := (inc_iff _ _).mpr hinc'
      rw [hni] at ht; cases ht
  have row_inj : Function.Injective rowSet := by
    intro a b hab
    by_contra hne
    have hcase : a.1 ≠ b.1 ∨ (b.2 - a.2) ≠ 0 := by
      by_cases h1 : a.1 = b.1
      · right
        intro h2
        apply hne
        have hc : b.2 = a.2 := (f13_sub_zero b.2 a.2).mp h2
        exact Prod.ext h1 hc.symm
      · exact Or.inl h1
    obtain ⟨p0, hdiff⟩ := horb_ne a.1 b.1 (b.2 - a.2) hcase
    have hma := mem_rowSet_cast a (p0 + a.2)
    have hmb := mem_rowSet_cast b (p0 + a.2)
    rw [hab] at hma
    have heq : rowP a (p0 + a.2) = rowP b (p0 + a.2) := Bool.eq_iff_iff.mpr (hma.symm.trans hmb)
    dsimp only [rowP] at heq
    have hs1 : p0 + a.2 - a.2 = p0 := f13_add_sub p0 a.2
    have hs2 : p0 + a.2 - b.2 = p0 - (b.2 - a.2) := f13_add_sub_sub p0 a.2 b.2
    rw [hs1, hs2] at heq
    exact hdiff heq
  let allRows : Finset (Finset (Fin 26)) := Finset.univ.image rowSet
  have row_incomp : ∀ I ∈ allRows, ∀ J ∈ allRows, I ≠ J → ∃ w ∈ I, w ∉ J := by
    intro I hI J hJ hne
    by_contra hall
    push Not at hall
    have hsub : I ⊆ J := hall
    have hssub : ∃ w ∈ J, w ∉ I := by
      by_contra h2
      push Not at h2
      exact hne (Finset.Subset.antisymm hsub h2)
    obtain ⟨w, hwJ, hwnI⟩ := hssub
    obtain ⟨rcI, _, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨rcJ, _, rfl⟩ := Finset.mem_image.mp hJ
    by_cases hlt : w.val < 13
    · let p : Fin 13 := ⟨w.val, hlt⟩
      have hw_eq : w = Fin.castAdd 13 p := Fin.ext rfl
      rw [hw_eq] at hwJ hwnI
      have hpJ : p ∈ rowPSet rcJ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_rowSet_cast rcJ p).mp hwJ⟩
      have hpnI : p ∉ rowPSet rcI := fun h => hwnI ((mem_rowSet_cast rcI p).mpr (Finset.mem_filter.mp h).2)
      obtain ⟨l, hlWI, hinc⟩ := row_max rcI p hpnI
      have hlI : Fin.natAdd 13 l ∈ rowSet rcI := (mem_rowSet_nat rcI l).mpr ((rowW_iff rcI l).mpr hlWI)
      have hlJ : Fin.natAdd 13 l ∈ rowSet rcJ := hsub hlI
      exact (rowW_iff rcJ l).mp ((mem_rowSet_nat rcJ l).mp hlJ) p hpJ hinc
    · let l : Fin 13 := ⟨w.val - 13, by omega⟩
      have hw_eq : w = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
      rw [hw_eq] at hwJ hwnI
      have hlJ : ∀ q ∈ rowPSet rcJ, ¬ inc q l := (rowW_iff rcJ l).mp ((mem_rowSet_nat rcJ l).mp hwJ)
      have hlnI : ¬ ∀ q ∈ rowPSet rcI, ¬ inc q l := fun h =>
        hwnI ((mem_rowSet_nat rcI l).mpr ((rowW_iff rcI l).mpr h))
      push Not at hlnI
      obtain ⟨q, hqI, hinc⟩ := hlnI
      have hqInI : Fin.castAdd 13 q ∈ rowSet rcI := (mem_rowSet_cast rcI q).mpr (Finset.mem_filter.mp hqI).2
      have hqInJ : Fin.castAdd 13 q ∈ rowSet rcJ := hsub hqInI
      have hqJ : q ∈ rowPSet rcJ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_rowSet_cast rcJ q).mp hqInJ⟩
      exact hlJ q hqJ hinc

  -- Define cyclic shift and point-line duality equivalences on Fin 26
  let shiftFn (c : Fin 13) (k : Fin 26) : Fin 26 :=
    if h : k.val < 13 then Fin.castAdd 13 (⟨k.val, h⟩ + c)
    else Fin.natAdd 13 (⟨k.val - 13, by omega⟩ + c)
  have shiftFn_cast : ∀ (c p : Fin 13), shiftFn c (Fin.castAdd 13 p) = Fin.castAdd 13 (p + c) := by
    intro c p
    have hlt : (Fin.castAdd 13 p).val < 13 := p.isLt
    simp only [shiftFn, hlt, ↓reduceDIte]
    rfl
  have shiftFn_nat : ∀ (c l : Fin 13), shiftFn c (Fin.natAdd 13 l) = Fin.natAdd 13 (l + c) := by
    intro c l
    have hlt : ¬ (Fin.natAdd 13 l).val < 13 := by simp
    simp only [shiftFn, hlt, ↓reduceDIte]
    apply Fin.ext
    simp
  let shiftEquiv (c : Fin 13) : Fin 26 ≃ Fin 26 :=
    { toFun := shiftFn c
      invFun := shiftFn (-c)
      left_inv := by
        intro k
        by_cases h : k.val < 13
        · let p : Fin 13 := ⟨k.val, h⟩
          have hk : k = Fin.castAdd 13 p := Fin.ext rfl
          rw [hk, shiftFn_cast, shiftFn_cast, f13_add_neg]
        · let l : Fin 13 := ⟨k.val - 13, by omega⟩
          have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
          rw [hk, shiftFn_nat, shiftFn_nat, f13_add_neg]
      right_inv := by
        intro k
        by_cases h : k.val < 13
        · let p : Fin 13 := ⟨k.val, h⟩
          have hk : k = Fin.castAdd 13 p := Fin.ext rfl
          rw [hk, shiftFn_cast, shiftFn_cast, f13_neg_add]
        · let l : Fin 13 := ⟨k.val - 13, by omega⟩
          have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
          rw [hk, shiftFn_nat, shiftFn_nat, f13_neg_add] }
  have shift_rowSet : ∀ (c : Fin 13) (rc : Fin 36 × Fin 13),
      (rowSet rc).map (shiftEquiv c).toEmbedding = rowSet (rc.1, rc.2 + c) := by
    intro c rc
    ext k
    by_cases h : k.val < 13
    · let p : Fin 13 := ⟨k.val, h⟩
      have hk : k = Fin.castAdd 13 p := Fin.ext rfl
      rw [hk, Finset.mem_map_equiv, mem_rowSet_cast]
      have hinv : (shiftEquiv c).symm (Fin.castAdd 13 p) = Fin.castAdd 13 (p - c) := by
        change shiftFn (-c) (Fin.castAdd 13 p) = Fin.castAdd 13 (p - c)
        rw [shiftFn_cast, f13_sub_eq_add_neg]
      rw [hinv, mem_rowSet_cast]
      dsimp only [rowP]
      have hs : p - c - rc.2 = p - (rc.2 + c) := f13_sub_sub p c rc.2
      rw [hs]
    · let l : Fin 13 := ⟨k.val - 13, by omega⟩
      have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
      rw [hk, Finset.mem_map_equiv, mem_rowSet_nat]
      have hinv : (shiftEquiv c).symm (Fin.natAdd 13 l) = Fin.natAdd 13 (l - c) := by
        change shiftFn (-c) (Fin.natAdd 13 l) = Fin.natAdd 13 (l - c)
        rw [shiftFn_nat, f13_sub_eq_add_neg]
      rw [hinv, mem_rowSet_nat]
      dsimp only [rowW]
      have hs : l - c - rc.2 = l - (rc.2 + c) := f13_sub_sub l c rc.2
      rw [hs]
  have shift_allRows : ∀ (c : Fin 13) (I : Finset (Fin 26)),
      I ∈ allRows → I.map (shiftEquiv c).toEmbedding ∈ allRows := by
    intro c I hI
    obtain ⟨rc, _, rfl⟩ := Finset.mem_image.mp hI
    rw [shift_rowSet c rc]
    exact Finset.mem_image.mpr ⟨(rc.1, rc.2 + c), Finset.mem_univ _, rfl⟩

  -- Part 8: Helper for rows0 membership
  have rows0_mem_0 : ∀ rc ∈ rows0, rowP rc 0 = true := by
    intro rc hrc
    exact List.all_eq_true.mp rows0_ok rc hrc
  have hL5_geom : ∀ (p2 l : Fin 13), p2 ≠ 0 → incB 0 l = false → incB p2 l = false →
      let Y := (List.finRange 13).filter (fun m => (m != l) && !incB 0 m && !incB p2 m)
      let R := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2) && orbW rc.1 (l - rc.2))
      Y.length = 5 ∧
      (∀ m ∈ Y, 5 ≤ (R.filter (fun rc => orbW rc.1 (m - rc.2))).length) ∧
      (∀ m ∈ Y, ∃ rc ∈ R, orbW rc.1 (m - rc.2) = false) ∧
      (∀ m1 ∈ Y, ∀ m2 ∈ Y, m1 ≠ m2 → ∃ rc ∈ R, orbW rc.1 (m1 - rc.2) = true ∧ orbW rc.1 (m2 - rc.2) = false) ∧
      (∀ m1 ∈ Y, ∀ m2 ∈ Y, m1 ≠ m2 → ∃ rc ∈ R, orbW rc.1 (m1 - rc.2) = false ∧ orbW rc.1 (m2 - rc.2) = false) := by
    intro p2 l hp2 h0l hp2l
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp hL5_bool p2 (List.mem_finRange p2)) l (List.mem_finRange l)
    have hne0 : (p2 == 0) = false := beq_false_of_ne hp2
    rw [hne0, h0l, hp2l] at h1
    simp only [Bool.false_or, Bool.and_eq_true] at h1
    refine ⟨beq_iff_eq.mp h1.1.1.1, ?_, ?_, ?_, ?_⟩
    · intro m hm
      exact Nat.ble_eq.mp (List.all_eq_true.mp h1.1.1.2 m hm)
    · intro m hm
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp (List.all_eq_true.mp h1.1.2 m hm)
      exact ⟨rc, hrc, by simpa using hf⟩
    · intro m1 hm1 m2 hm2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 m1 hm1) m2 hm2
      have hne' : (m1 == m2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.1
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
    · intro m1 hm1 m2 hm2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 m1 hm1) m2 hm2
      have hne' : (m1 == m2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
  have hL4_geom : ∀ (p2 : Fin 13), p2 ≠ 0 →
      let Y := (List.finRange 13).filter (fun m => !incB 0 m && !incB p2 m)
      let R := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2))
      Y.length = 6 ∧
      (∀ m ∈ Y, 9 ≤ (R.filter (fun rc => orbW rc.1 (m - rc.2))).length) ∧
      (∀ m ∈ Y, ∃ rc ∈ R, orbW rc.1 (m - rc.2) = false) ∧
      (∀ m1 ∈ Y, ∀ m2 ∈ Y, m1 ≠ m2 → ∃ rc ∈ R, orbW rc.1 (m1 - rc.2) = true ∧ orbW rc.1 (m2 - rc.2) = false) ∧
      (∀ m1 ∈ Y, ∀ m2 ∈ Y, m1 ≠ m2 → ∃ rc ∈ R, orbW rc.1 (m1 - rc.2) = false ∧ orbW rc.1 (m2 - rc.2) = false) := by
    intro p2 hp2
    have h1 := List.all_eq_true.mp hL4_bool p2 (List.mem_finRange p2)
    have hne0 : (p2 == 0) = false := beq_false_of_ne hp2
    rw [hne0] at h1
    simp only [Bool.false_or, Bool.and_eq_true] at h1
    refine ⟨beq_iff_eq.mp h1.1.1.1, ?_, ?_, ?_, ?_⟩
    · intro m hm
      exact Nat.ble_eq.mp (List.all_eq_true.mp h1.1.1.2 m hm)
    · intro m hm
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp (List.all_eq_true.mp h1.1.2 m hm)
      exact ⟨rc, hrc, by simpa using hf⟩
    · intro m1 hm1 m2 hm2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 m1 hm1) m2 hm2
      have hne' : (m1 == m2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.1
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
    · intro m1 hm1 m2 hm2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 m1 hm1) m2 hm2
      have hne' : (m1 == m2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
  have hL3_geom : ∀ (l0 : Fin 13), incB 0 l0 = false →
      let X := (List.finRange 13).filter (fun q => (q != 0) && !incB q l0)
      let R := rows0.filter (fun rc => orbW rc.1 (l0 - rc.2))
      X.length = 8 ∧
      (∀ q ∈ X, ∃ rc ∈ R, orbP rc.1 (q - rc.2) = true) ∧
      (∀ q ∈ X, ∃ rc ∈ R, orbP rc.1 (q - rc.2) = false) ∧
      (∀ q1 ∈ X, ∀ q2 ∈ X, q1 ≠ q2 → ∃ rc ∈ R, orbP rc.1 (q1 - rc.2) = true ∧ orbP rc.1 (q2 - rc.2) = false) ∧
      (∀ q1 ∈ X, ∀ q2 ∈ X, q1 ≠ q2 → ∃ rc ∈ R, orbP rc.1 (q1 - rc.2) = false ∧ orbP rc.1 (q2 - rc.2) = false) := by
    intro l0 h0l
    have h1 := List.all_eq_true.mp hL3_bool l0 (List.mem_finRange l0)
    rw [h0l] at h1
    simp only [Bool.false_or, Bool.and_eq_true] at h1
    refine ⟨beq_iff_eq.mp h1.1.1.1, ?_, ?_, ?_, ?_⟩
    · intro q hq
      exact List.any_eq_true.mp (List.all_eq_true.mp h1.1.1.2 q hq)
    · intro q hq
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp (List.all_eq_true.mp h1.1.2 q hq)
      exact ⟨rc, hrc, by simpa using hf⟩
    · intro q1 hq1 q2 hq2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 q1 hq1) q2 hq2
      have hne' : (q1 == q2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.1
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
    · intro q1 hq1 q2 hq2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 q1 hq1) q2 hq2
      have hne' : (q1 == q2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
  have hL2_geom :
      let Y := (List.finRange 13).filter (fun l => !incB 0 l)
      Y.length = 9 ∧
      (∀ l ∈ Y, ∃ rc ∈ rows0, orbW rc.1 (l - rc.2) = true) ∧
      (∀ l ∈ Y, ∃ rc ∈ rows0, orbW rc.1 (l - rc.2) = false) ∧
      (∀ l1 ∈ Y, ∀ l2 ∈ Y, l1 ≠ l2 → ∃ rc ∈ rows0, orbW rc.1 (l1 - rc.2) = true ∧ orbW rc.1 (l2 - rc.2) = false) ∧
      (∀ l1 ∈ Y, ∀ l2 ∈ Y, l1 ≠ l2 → ∃ rc ∈ rows0, orbW rc.1 (l1 - rc.2) = false ∧ orbW rc.1 (l2 - rc.2) = false) := by
    have h1 := hL2_bool
    simp only [Bool.and_eq_true] at h1
    refine ⟨beq_iff_eq.mp h1.1.1.1, ?_, ?_, ?_, ?_⟩
    · intro l hl
      exact List.any_eq_true.mp (List.all_eq_true.mp h1.1.1.2 l hl)
    · intro l hl
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp (List.all_eq_true.mp h1.1.2 l hl)
      exact ⟨rc, hrc, by simpa using hf⟩
    · intro l1 hl1 l2 hl2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 l1 hl1) l2 hl2
      have hne' : (l1 == l2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.1
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩
    · intro l1 hl1 l2 hl2 hne
      have h2 := List.all_eq_true.mp (List.all_eq_true.mp h1.2 l1 hl1) l2 hl2
      have hne' : (l1 == l2) = false := beq_false_of_ne hne
      rw [hne'] at h2
      simp only [Bool.false_or, Bool.and_eq_true] at h2
      obtain ⟨rc, hrc, hf⟩ := List.any_eq_true.mp h2.2
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
      exact ⟨rc, hrc, hf.1, hf.2⟩

  -- Part 9: 5-level recursive elimination ladder!
  -- Helper: from a nodup list of Fin 36 x Fin 13 matching a predicate on rowSet, lower-bound Finset.card
  have list_to_rows_card : ∀ (L : List (Fin 36 × Fin 13)) (Rows : Finset (Finset (Fin 26))),
      L.Nodup → (∀ rc ∈ L, rowSet rc ∈ Rows) → L.length ≤ Rows.card := by
    intro L Rows hnd hsub
    have h1 : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
    have h2 : (L.toFinset.image rowSet).card = L.toFinset.card :=
      Finset.card_image_of_injective L.toFinset row_inj
    have h3 : L.toFinset.image rowSet ⊆ Rows := by
      intro I hI
      obtain ⟨rc, hrc, rfl⟩ := Finset.mem_image.mp hI
      exact hsub rc (List.mem_toFinset.mp hrc)
    calc L.length = (L.toFinset.image rowSet).card := by rw [h2, h1]
      _ ≤ Rows.card := Finset.card_le_card h3

  -- Level 5: f(2pt + 1l) >= 5 (at p1 = 0)
  have hLevel5_0 : ∀ (p2 l : Fin 13), p2 ≠ 0 → ¬ inc 0 l → ¬ inc p2 l →
      ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
        Separates E (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 p2 ∈ I ∧ Fin.natAdd 13 l ∈ I) →
        5 ≤ E.size := by
    intro p2 l hp2 hni0 hnip2 E hw hsep
    by_contra! hlt
    have hsz : E.size ≤ 4 := by omega
    obtain ⟨D, hDsz, _, hDdisj, _, hDeval⟩ := strip_exists E hw
    let Rows := allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 p2 ∈ I ∧ Fin.natAdd 13 l ∈ I
    have hDsep : Separates D Rows := by
      intro I hI
      have h := hsep I hI
      exact ⟨by rw [hDeval]; exact h.1, fun w hw => by rw [hDeval]; exact h.2 w hw⟩
    have hbi0 : incB 0 l = false := Bool.eq_false_iff.mpr (fun ht => hni0 ((inc_iff _ _).mp ht))
    have hbip2 : incB p2 l = false := Bool.eq_false_iff.mpr (fun ht => hnip2 ((inc_iff _ _).mp ht))
    obtain ⟨hYlen, hYcnt, hYout, hYsame, hYopp⟩ := hL5_geom p2 l hp2 hbi0 hbip2
    let Ylist := (List.finRange 13).filter (fun m => (m != l) && !incB 0 m && !incB p2 m)
    let Rlist := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2) && orbW rc.1 (l - rc.2))
    let Z : Finset (Fin 26) := Ylist.toFinset.image (Fin.natAdd 13)
    have hZcard : Z.card = 5 := by
      have hnd : Ylist.Nodup := List.Nodup.filter _ (List.nodup_finRange 13)
      have hinj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := fun a b h => by
        have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; exact Fin.ext (by omega)
      rw [Finset.card_image_of_injective _ hinj, List.toFinset_card_of_nodup hnd, hYlen]
    have hRmem : ∀ rc ∈ Rlist, rowSet rc ∈ Rows := by
      intro rc hrc
      have h1 := List.mem_filter.mp hrc
      have h0 : rowP rc 0 = true := rows0_mem_0 rc h1.1
      have h2 := Bool.and_eq_true _ _ |>.mp h1.2
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, ?_, ?_, ?_⟩
      · exact (mem_rowSet_cast rc 0).mpr h0
      · exact (mem_rowSet_cast rc p2).mpr h2.1
      · exact (mem_rowSet_nat rc l).mpr h2.2
    have hZdeg1 : ∀ z ∈ Z, (litSet D z).card ≤ 1 := by
      intro z hz
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
      have hmL : m ∈ Ylist := List.mem_toFinset.mp hm
      have hcnt5 : 5 ≤ (Rlist.filter (fun rc => orbW rc.1 (m - rc.2))).length := hYcnt m hmL
      have hndR : (Rlist.filter (fun rc => orbW rc.1 (m - rc.2))).Nodup :=
        List.Nodup.filter _ (List.Nodup.filter _ rows0_nodup)
      have hcard5 : 5 ≤ (Rows.filter (fun I => Fin.natAdd 13 m ∈ I)).card := by
        refine hcnt5.trans (list_to_rows_card _ _ hndR ?_)
        intro rc hrc
        have hf := List.mem_filter.mp hrc
        exact Finset.mem_filter.mpr ⟨hRmem rc hf.1, (mem_rowSet_nat rc m).mpr hf.2⟩
      have hfb := free_bound_gen D Rows (Fin.natAdd 13 m) hDsep
        (fun I hI J hJ hne => row_incomp I (Finset.mem_filter.mp hI).1 J (Finset.mem_filter.mp hJ).1 hne)
      have hpow : 3 ≤ (Free D (Fin.natAdd 13 m)).card := by
        by_contra! hlt3
        have hp : 2 ^ (Free D (Fin.natAdd 13 m)).card ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hsum := (litSet_touch_card D hDdisj (Fin.natAdd 13 m)).2
      omega
    have hZle := card_le_size_of_deg_le_one D Rows Z hDsep
      (fun z hz => by
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
        have hcnt5 := hYcnt m (List.mem_toFinset.mp hm)
        obtain ⟨rc, hrc⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos (Nat.lt_of_lt_of_le (by decide : 0 < 5) (by exact hcnt5)))
        have hf := List.mem_filter.mp hrc
        exact ⟨rowSet rc, hRmem rc hf.1, (mem_rowSet_nat rc m).mpr hf.2⟩)
      (fun z hz => by
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hmf⟩ := hYout m (List.mem_toFinset.mp hm)
        exact ⟨rowSet rc, hRmem rc hrc, (fun hmem => by have ht := (mem_rowSet_nat rc m).mp hmem; dsimp only [rowW] at ht; rw [hmf] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨m2, hm2, rfl⟩ := Finset.mem_image.mp hz2
        have hmn : m1 ≠ m2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYsame m1 (List.mem_toFinset.mp hm1) m2 (List.mem_toFinset.mp hm2) hmn
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_nat rc m1).mpr h1, (fun hmem => by have ht := (mem_rowSet_nat rc m2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨m2, hm2, rfl⟩ := Finset.mem_image.mp hz2
        have hmn : m1 ≠ m2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYopp m1 (List.mem_toFinset.mp hm1) m2 (List.mem_toFinset.mp hm2) hmn
        exact ⟨rowSet rc, hRmem rc hrc,
          (fun hmem => by have ht := (mem_rowSet_nat rc m1).mp hmem; dsimp only [rowW] at ht; rw [h1] at ht; cases ht),
          (fun hmem => by have ht := (mem_rowSet_nat rc m2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      hZdeg1
    omega

  -- Level 4: f(2pt) >= 6 (at p1 = 0)
  have hLevel4_0 : ∀ (p2 : Fin 13), p2 ≠ 0 →
      ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
        Separates E (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 p2 ∈ I) →
        6 ≤ E.size := by
    intro p2 hp2 E hw hsep
    by_contra! hlt
    have hsz : E.size ≤ 5 := by omega
    obtain ⟨D, hDsz, _, hDdisj, _, hDeval⟩ := strip_exists E hw
    let Rows := allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 p2 ∈ I
    have hDsep : Separates D Rows := by
      intro I hI
      have h := hsep I hI
      exact ⟨by rw [hDeval]; exact h.1, fun w hw => by rw [hDeval]; exact h.2 w hw⟩
    obtain ⟨hYlen, hYcnt, hYout, hYsame, hYopp⟩ := hL4_geom p2 hp2
    let Ylist := (List.finRange 13).filter (fun m => !incB 0 m && !incB p2 m)
    let Rlist := rows0.filter (fun rc => orbP rc.1 (p2 - rc.2))
    let Z : Finset (Fin 26) := Ylist.toFinset.image (Fin.natAdd 13)
    have hZcard : Z.card = 6 := by
      have hnd : Ylist.Nodup := List.Nodup.filter _ (List.nodup_finRange 13)
      have hinj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := fun a b h => by
        have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; exact Fin.ext (by omega)
      rw [Finset.card_image_of_injective _ hinj, List.toFinset_card_of_nodup hnd, hYlen]
    have hRmem : ∀ rc ∈ Rlist, rowSet rc ∈ Rows := by
      intro rc hrc
      have h1 := List.mem_filter.mp hrc
      have h0 : rowP rc 0 = true := rows0_mem_0 rc h1.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, ?_, ?_⟩
      · exact (mem_rowSet_cast rc 0).mpr h0
      · exact (mem_rowSet_cast rc p2).mpr h1.2
    have hZdeg1 : ∀ z ∈ Z, (litSet D z).card ≤ 1 := by
      intro z hz
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
      have hmL : m ∈ Ylist := List.mem_toFinset.mp hm
      have hcnt9 : 9 ≤ (Rlist.filter (fun rc => orbW rc.1 (m - rc.2))).length := hYcnt m hmL
      have hndR : (Rlist.filter (fun rc => orbW rc.1 (m - rc.2))).Nodup :=
        List.Nodup.filter _ (List.Nodup.filter _ rows0_nodup)
      have hcard9 : 9 ≤ (Rows.filter (fun I => Fin.natAdd 13 m ∈ I)).card := by
        refine hcnt9.trans (list_to_rows_card _ _ hndR ?_)
        intro rc hrc
        have hf := List.mem_filter.mp hrc
        exact Finset.mem_filter.mpr ⟨hRmem rc hf.1, (mem_rowSet_nat rc m).mpr hf.2⟩
      have hfb := free_bound_gen D Rows (Fin.natAdd 13 m) hDsep
        (fun I hI J hJ hne => row_incomp I (Finset.mem_filter.mp hI).1 J (Finset.mem_filter.mp hJ).1 hne)
      have hpow : 4 ≤ (Free D (Fin.natAdd 13 m)).card := by
        by_contra! hlt4
        have hp : 2 ^ (Free D (Fin.natAdd 13 m)).card ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      have hsum := (litSet_touch_card D hDdisj (Fin.natAdd 13 m)).2
      omega
    have hZle := card_le_size_of_deg_le_one D Rows Z hDsep
      (fun z hz => by
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
        have hcnt9 := hYcnt m (List.mem_toFinset.mp hm)
        obtain ⟨rc, hrc⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos (Nat.lt_of_lt_of_le (by decide : 0 < 9) (by exact hcnt9)))
        have hf := List.mem_filter.mp hrc
        exact ⟨rowSet rc, hRmem rc hf.1, (mem_rowSet_nat rc m).mpr hf.2⟩)
      (fun z hz => by
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hmf⟩ := hYout m (List.mem_toFinset.mp hm)
        exact ⟨rowSet rc, hRmem rc hrc, (fun hmem => by have ht := (mem_rowSet_nat rc m).mp hmem; dsimp only [rowW] at ht; rw [hmf] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨m2, hm2, rfl⟩ := Finset.mem_image.mp hz2
        have hmn : m1 ≠ m2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYsame m1 (List.mem_toFinset.mp hm1) m2 (List.mem_toFinset.mp hm2) hmn
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_nat rc m1).mpr h1, (fun hmem => by have ht := (mem_rowSet_nat rc m2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨m2, hm2, rfl⟩ := Finset.mem_image.mp hz2
        have hmn : m1 ≠ m2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYopp m1 (List.mem_toFinset.mp hm1) m2 (List.mem_toFinset.mp hm2) hmn
        exact ⟨rowSet rc, hRmem rc hrc,
          (fun hmem => by have ht := (mem_rowSet_nat rc m1).mp hmem; dsimp only [rowW] at ht; rw [h1] at ht; cases ht),
          (fun hmem => by have ht := (mem_rowSet_nat rc m2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      hZdeg1
    omega

  -- Level 3: f(1pt + 1l) >= 7 (at p0 = 0)
  have hLevel3_0 : ∀ (l0 : Fin 13), ¬ inc 0 l0 →
      ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
        Separates E (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.natAdd 13 l0 ∈ I) →
        7 ≤ E.size := by
    intro l0 hni0 E hw hsep
    by_contra! hlt
    have hsz : E.size ≤ 6 := by omega
    obtain ⟨D, hDsz, hDwf, hDdisj, _, hDeval⟩ := strip_exists E hw
    let Rows := allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.natAdd 13 l0 ∈ I
    have hDsep : Separates D Rows := by
      intro I hI
      have h := hsep I hI
      exact ⟨by rw [hDeval]; exact h.1, fun w hw => by rw [hDeval]; exact h.2 w hw⟩
    have hbi0 : incB 0 l0 = false := Bool.eq_false_iff.mpr (fun ht => hni0 ((inc_iff _ _).mp ht))
    obtain ⟨hXlen, hXin, hXout, hXsame, hXopp⟩ := hL3_geom l0 hbi0
    let Xlist := (List.finRange 13).filter (fun q => (q != 0) && !incB q l0)
    let Rlist := rows0.filter (fun rc => orbW rc.1 (l0 - rc.2))
    let Z : Finset (Fin 26) := Xlist.toFinset.image (Fin.castAdd 13)
    have hZcard : Z.card = 8 := by
      have hnd : Xlist.Nodup := List.Nodup.filter _ (List.nodup_finRange 13)
      have hinj : Function.Injective (Fin.castAdd 13 : Fin 13 → Fin 26) := fun a b h => Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val h)
      rw [Finset.card_image_of_injective _ hinj, List.toFinset_card_of_nodup hnd, hXlen]
    have hRmem : ∀ rc ∈ Rlist, rowSet rc ∈ Rows := by
      intro rc hrc
      have h1 := List.mem_filter.mp hrc
      have h0 : rowP rc 0 = true := rows0_mem_0 rc h1.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, ?_, ?_⟩
      · exact (mem_rowSet_cast rc 0).mpr h0
      · exact (mem_rowSet_nat rc l0).mpr h1.2
    have hZdeg1 : ∀ z ∈ Z, (litSet D z).card ≤ 1 := by
      intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      have hqL : q ∈ Xlist := List.mem_toFinset.mp hq
      have hqcond := Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp hqL).2
      have hqne : q ≠ 0 := bne_iff_ne.mp hqcond.1
      have hqni : ¬ inc q l0 := by
        intro h
        have ht : incB q l0 = true := (inc_iff _ _).mpr h
        have hf := hqcond.2
        rw [ht] at hf; cases hf
      obtain ⟨E', hw', hbd, heq⟩ := elim_vertices D hDwf {Fin.castAdd 13 q}
      have hsep' : Separates E' (allRows.filter fun I =>
          Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 q ∈ I ∧ Fin.natAdd 13 l0 ∈ I) := by
        intro I hI
        have hf := Finset.mem_filter.mp hI
        have hIR : I ∈ Rows := Finset.mem_filter.mpr ⟨hf.1, hf.2.1, hf.2.2.2⟩
        have hsub : ({Fin.castAdd 13 q} : Finset (Fin 26)) ⊆ I := Finset.singleton_subset_iff.mpr hf.2.2.1
        refine ⟨(heq I hsub).trans (hDsep I hIR).1, fun w hw => ?_⟩
        exact (heq (insert w I) (hsub.trans (Finset.subset_insert w I))).trans ((hDsep I hIR).2 w hw)
      have h5 : 5 ≤ E'.size := hLevel5_0 q l0 hqne hni0 hqni E' hw' hsep'
      have htc : (litSet D (Fin.castAdd 13 q)).card =
          (Finset.univ.filter fun i : Fin D.size =>
            ∃ v ∈ ({Fin.castAdd 13 q} : Finset (Fin 26)), v ∈ D.leftVars i ∨ v ∈ D.rightVars i).card := by
        rw [(litSet_touch_card D hDdisj (Fin.castAdd 13 q)).1]
        apply congrArg Finset.card; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, exists_eq_left]
      rw [← htc] at hbd
      omega
    have hZle := card_le_size_of_deg_le_one D Rows Z hDsep
      (fun z hz => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hqt⟩ := hXin q (List.mem_toFinset.mp hq)
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_cast rc q).mpr hqt⟩)
      (fun z hz => by
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hqf⟩ := hXout q (List.mem_toFinset.mp hq)
        exact ⟨rowSet rc, hRmem rc hrc, (fun hmem => by have ht := (mem_rowSet_cast rc q).mp hmem; dsimp only [rowP] at ht; rw [hqf] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨q1, hq1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨q2, hq2, rfl⟩ := Finset.mem_image.mp hz2
        have hqn : q1 ≠ q2 := fun h => hne (congrArg (Fin.castAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hXsame q1 (List.mem_toFinset.mp hq1) q2 (List.mem_toFinset.mp hq2) hqn
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_cast rc q1).mpr h1, (fun hmem => by have ht := (mem_rowSet_cast rc q2).mp hmem; dsimp only [rowP] at ht; rw [h2] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨q1, hq1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨q2, hq2, rfl⟩ := Finset.mem_image.mp hz2
        have hqn : q1 ≠ q2 := fun h => hne (congrArg (Fin.castAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hXopp q1 (List.mem_toFinset.mp hq1) q2 (List.mem_toFinset.mp hq2) hqn
        exact ⟨rowSet rc, hRmem rc hrc,
          (fun hmem => by have ht := (mem_rowSet_cast rc q1).mp hmem; dsimp only [rowP] at ht; rw [h1] at ht; cases ht),
          (fun hmem => by have ht := (mem_rowSet_cast rc q2).mp hmem; dsimp only [rowP] at ht; rw [h2] at ht; cases ht)⟩)
      hZdeg1
    omega

  -- Level 2: f(1pt) >= 9 (at p0 = 0)
  have hLevel2_0 : ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
      Separates E (allRows.filter fun I => Fin.castAdd 13 0 ∈ I) →
      9 ≤ E.size := by
    intro E hw hsep
    by_contra! hlt
    have hsz : E.size ≤ 8 := by omega
    obtain ⟨D, hDsz, hDwf, hDdisj, _, hDeval⟩ := strip_exists E hw
    let Rows := allRows.filter fun I => Fin.castAdd 13 0 ∈ I
    have hDsep : Separates D Rows := by
      intro I hI
      have h := hsep I hI
      exact ⟨by rw [hDeval]; exact h.1, fun w hw => by rw [hDeval]; exact h.2 w hw⟩
    obtain ⟨hYlen, hYin, hYout, hYsame, hYopp⟩ := hL2_geom
    let Ylist := (List.finRange 13).filter (fun l => !incB 0 l)
    let Z : Finset (Fin 26) := Ylist.toFinset.image (Fin.natAdd 13)
    have hZcard : Z.card = 9 := by
      have hnd : Ylist.Nodup := List.Nodup.filter _ (List.nodup_finRange 13)
      have hinj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := fun a b h => by
        have hv := congrArg Fin.val h; simp only [Fin.val_natAdd] at hv; exact Fin.ext (by omega)
      rw [Finset.card_image_of_injective _ hinj, List.toFinset_card_of_nodup hnd, hYlen]
    have hRmem : ∀ rc ∈ rows0, rowSet rc ∈ Rows := by
      intro rc hrc
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, (mem_rowSet_cast rc 0).mpr (rows0_mem_0 rc hrc)⟩
    have hZdeg1 : ∀ z ∈ Z, (litSet D z).card ≤ 1 := by
      intro z hz
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
      have hlL : l ∈ Ylist := List.mem_toFinset.mp hl
      have hlni : ¬ inc 0 l := by
        intro h
        have ht : incB 0 l = true := (inc_iff _ _).mpr h
        have hf := (List.mem_filter.mp hlL).2
        rw [ht] at hf; cases hf
      obtain ⟨E', hw', hbd, heq⟩ := elim_vertices D hDwf {Fin.natAdd 13 l}
      have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.natAdd 13 l ∈ I) := by
        intro I hI
        have hf := Finset.mem_filter.mp hI
        have hIR : I ∈ Rows := Finset.mem_filter.mpr ⟨hf.1, hf.2.1⟩
        have hsub : ({Fin.natAdd 13 l} : Finset (Fin 26)) ⊆ I := Finset.singleton_subset_iff.mpr hf.2.2
        refine ⟨(heq I hsub).trans (hDsep I hIR).1, fun w hw => ?_⟩
        exact (heq (insert w I) (hsub.trans (Finset.subset_insert w I))).trans ((hDsep I hIR).2 w hw)
      have h7 : 7 ≤ E'.size := hLevel3_0 l hlni E' hw' hsep'
      have htc : (litSet D (Fin.natAdd 13 l)).card =
          (Finset.univ.filter fun i : Fin D.size =>
            ∃ v ∈ ({Fin.natAdd 13 l} : Finset (Fin 26)), v ∈ D.leftVars i ∨ v ∈ D.rightVars i).card := by
        rw [(litSet_touch_card D hDdisj (Fin.natAdd 13 l)).1]
        apply congrArg Finset.card; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, exists_eq_left]
      rw [← htc] at hbd
      omega
    have hZle := card_le_size_of_deg_le_one D Rows Z hDsep
      (fun z hz => by
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hlt'⟩ := hYin l (List.mem_toFinset.mp hl)
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_nat rc l).mpr hlt'⟩)
      (fun z hz => by
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨rc, hrc, hlf⟩ := hYout l (List.mem_toFinset.mp hl)
        exact ⟨rowSet rc, hRmem rc hrc, (fun hmem => by have ht := (mem_rowSet_nat rc l).mp hmem; dsimp only [rowW] at ht; rw [hlf] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨l1, hl1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨l2, hl2, rfl⟩ := Finset.mem_image.mp hz2
        have hln : l1 ≠ l2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYsame l1 (List.mem_toFinset.mp hl1) l2 (List.mem_toFinset.mp hl2) hln
        exact ⟨rowSet rc, hRmem rc hrc, (mem_rowSet_nat rc l1).mpr h1, (fun hmem => by have ht := (mem_rowSet_nat rc l2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      (fun z1 hz1 z2 hz2 hne => by
        obtain ⟨l1, hl1, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨l2, hl2, rfl⟩ := Finset.mem_image.mp hz2
        have hln : l1 ≠ l2 := fun h => hne (congrArg (Fin.natAdd 13) h)
        obtain ⟨rc, hrc, h1, h2⟩ := hYopp l1 (List.mem_toFinset.mp hl1) l2 (List.mem_toFinset.mp hl2) hln
        exact ⟨rowSet rc, hRmem rc hrc,
          (fun hmem => by have ht := (mem_rowSet_nat rc l1).mp hmem; dsimp only [rowW] at ht; rw [h1] at ht; cases ht),
          (fun hmem => by have ht := (mem_rowSet_nat rc l2).mp hmem; dsimp only [rowW] at ht; rw [h2] at ht; cases ht)⟩)
      hZdeg1
    omega

  -- Lift Levels 2, 3, 4 from p0 = 0 to arbitrary p0 : Fin 13 via cyclic shift!
  have hShift_sep : ∀ (c : Fin 13) (E : PEqualNP.AndCount.AndCountCircuit 26)
      (Rows : Finset (Finset (Fin 26))),
      Separates E Rows →
      Separates (mapCirc (shiftEquiv c) E) (Rows.image fun I => I.map (shiftEquiv c).toEmbedding) := by
    intro c E Rows hsep J hJ
    obtain ⟨I, hIR, rfl⟩ := Finset.mem_image.mp hJ
    have hI := hsep I hIR
    refine ⟨(mapCirc_eval (shiftEquiv c) E I).trans hI.1, ?_⟩
    intro w hw
    let u := (shiftEquiv c).symm w
    have hu : u ∉ I := fun h => hw (by
      have hm : (shiftEquiv c) u ∈ I.map (shiftEquiv c).toEmbedding := Finset.mem_map.mpr ⟨u, h, rfl⟩
      simpa only [u, Equiv.apply_symm_apply] using hm)
    have hmap : insert w (I.map (shiftEquiv c).toEmbedding) = (insert u I).map (shiftEquiv c).toEmbedding := by
      have huw : (shiftEquiv c).toEmbedding u = w := (shiftEquiv c).apply_symm_apply w
      rw [Finset.map_insert, huw]
    rw [hmap, mapCirc_eval]
    exact hI.2 u hu
  have hLevel2 : ∀ (p0 : Fin 13) (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      Separates E (allRows.filter fun I => Fin.castAdd 13 p0 ∈ I) → 9 ≤ E.size := by
    intro p0 E hw hsep
    let E' := mapCirc (shiftEquiv (-p0)) E
    have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 0 ∈ I) := by
      intro J hJ
      have hJf := Finset.mem_filter.mp hJ
      let I := J.map (shiftEquiv p0).toEmbedding
      have hIR : I ∈ allRows.filter (fun K => Fin.castAdd 13 p0 ∈ K) := by
        refine Finset.mem_filter.mpr ⟨shift_allRows p0 J hJf.1, ?_⟩
        have hm : (shiftEquiv p0) (Fin.castAdd 13 0) ∈ I := Finset.mem_map.mpr ⟨Fin.castAdd 13 0, hJf.2, rfl⟩
        have h0p : (shiftEquiv p0) (Fin.castAdd 13 0) = Fin.castAdd 13 p0 := by
          change shiftFn p0 (Fin.castAdd 13 0) = Fin.castAdd 13 p0
          rw [shiftFn_cast, f13_zero_add]
        exact h0p ▸ hm
      have hJeq : I.map (shiftEquiv (-p0)).toEmbedding = J := by
        ext k; simp only [I, Finset.mem_map_equiv]
        have he : (shiftEquiv p0).symm ((shiftEquiv (-p0)).symm k) = k := by
          change shiftFn (-p0) (shiftFn (- -p0) k) = k
          rw [f13_neg_neg]
          exact (shiftEquiv p0).left_inv k
        rw [he]
      have h := hShift_sep (-p0) E (allRows.filter fun K => Fin.castAdd 13 p0 ∈ K) hsep J
        (Finset.mem_image.mpr ⟨I, hIR, hJeq⟩)
      exact h
    exact hLevel2_0 E' (mapCirc_wf _ E hw) hsep'
  have hLevel3 : ∀ (p0 l0 : Fin 13), ¬ inc p0 l0 →
      ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
        Separates E (allRows.filter fun I => Fin.castAdd 13 p0 ∈ I ∧ Fin.natAdd 13 l0 ∈ I) → 7 ≤ E.size := by
    intro p0 l0 hni E hw hsep
    let E' := mapCirc (shiftEquiv (-p0)) E
    have hni' : ¬ inc 0 (l0 - p0) := by
      intro h
      have h1 := (inc_shift 0 (l0 - p0) p0).mpr h
      rw [f13_zero_add, f13_sub_add] at h1; exact hni h1
    have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.natAdd 13 (l0 - p0) ∈ I) := by
      intro J hJ
      have hJf := Finset.mem_filter.mp hJ
      let I := J.map (shiftEquiv p0).toEmbedding
      have hIR : I ∈ allRows.filter (fun K => Fin.castAdd 13 p0 ∈ K ∧ Fin.natAdd 13 l0 ∈ K) := by
        refine Finset.mem_filter.mpr ⟨shift_allRows p0 J hJf.1, ?_, ?_⟩
        · have hm : (shiftEquiv p0) (Fin.castAdd 13 0) ∈ I := Finset.mem_map.mpr ⟨Fin.castAdd 13 0, hJf.2.1, rfl⟩
          have h0p : (shiftEquiv p0) (Fin.castAdd 13 0) = Fin.castAdd 13 p0 := by
            change shiftFn p0 (Fin.castAdd 13 0) = Fin.castAdd 13 p0; rw [shiftFn_cast, f13_zero_add]
          exact h0p ▸ hm
        · have hm : (shiftEquiv p0) (Fin.natAdd 13 (l0 - p0)) ∈ I :=
            Finset.mem_map.mpr ⟨Fin.natAdd 13 (l0 - p0), hJf.2.2, rfl⟩
          have hlp : (shiftEquiv p0) (Fin.natAdd 13 (l0 - p0)) = Fin.natAdd 13 l0 := by
            change shiftFn p0 (Fin.natAdd 13 (l0 - p0)) = Fin.natAdd 13 l0
            rw [shiftFn_nat, f13_sub_add]
          exact hlp ▸ hm
      have hJeq : I.map (shiftEquiv (-p0)).toEmbedding = J := by
        ext k; simp only [I, Finset.mem_map_equiv]
        have he : (shiftEquiv p0).symm ((shiftEquiv (-p0)).symm k) = k := by
          change shiftFn (-p0) (shiftFn (- -p0) k) = k; rw [f13_neg_neg]; exact (shiftEquiv p0).left_inv k
        rw [he]
      exact hShift_sep (-p0) E _ hsep J (Finset.mem_image.mpr ⟨I, hIR, hJeq⟩)
    exact hLevel3_0 (l0 - p0) hni' E' (mapCirc_wf _ E hw) hsep'
  have hLevel4 : ∀ (p1 p2 : Fin 13), p1 ≠ p2 →
      ∀ E : PEqualNP.AndCount.AndCountCircuit 26, E.WellFormed →
        Separates E (allRows.filter fun I => Fin.castAdd 13 p1 ∈ I ∧ Fin.castAdd 13 p2 ∈ I) → 6 ≤ E.size := by
    intro p1 p2 hne E hw hsep
    let E' := mapCirc (shiftEquiv (-p1)) E
    have hne' : p2 - p1 ≠ 0 := fun h => hne ((f13_sub_zero p2 p1).mp h).symm
    have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 0 ∈ I ∧ Fin.castAdd 13 (p2 - p1) ∈ I) := by
      intro J hJ
      have hJf := Finset.mem_filter.mp hJ
      let I := J.map (shiftEquiv p1).toEmbedding
      have hIR : I ∈ allRows.filter (fun K => Fin.castAdd 13 p1 ∈ K ∧ Fin.castAdd 13 p2 ∈ K) := by
        refine Finset.mem_filter.mpr ⟨shift_allRows p1 J hJf.1, ?_, ?_⟩
        · have hm : (shiftEquiv p1) (Fin.castAdd 13 0) ∈ I := Finset.mem_map.mpr ⟨Fin.castAdd 13 0, hJf.2.1, rfl⟩
          have h0p : (shiftEquiv p1) (Fin.castAdd 13 0) = Fin.castAdd 13 p1 := by
            change shiftFn p1 (Fin.castAdd 13 0) = Fin.castAdd 13 p1; rw [shiftFn_cast, f13_zero_add]
          exact h0p ▸ hm
        · have hm : (shiftEquiv p1) (Fin.castAdd 13 (p2 - p1)) ∈ I :=
            Finset.mem_map.mpr ⟨Fin.castAdd 13 (p2 - p1), hJf.2.2, rfl⟩
          have hpp : (shiftEquiv p1) (Fin.castAdd 13 (p2 - p1)) = Fin.castAdd 13 p2 := by
            change shiftFn p1 (Fin.castAdd 13 (p2 - p1)) = Fin.castAdd 13 p2
            rw [shiftFn_cast, f13_sub_add]
          exact hpp ▸ hm
      have hJeq : I.map (shiftEquiv (-p1)).toEmbedding = J := by
        ext k; simp only [I, Finset.mem_map_equiv]
        have he : (shiftEquiv p1).symm ((shiftEquiv (-p1)).symm k) = k := by
          change shiftFn (-p1) (shiftFn (- -p1) k) = k; rw [f13_neg_neg]; exact (shiftEquiv p1).left_inv k
        rw [he]
      exact hShift_sep (-p1) E _ hsep J (Finset.mem_image.mpr ⟨I, hIR, hJeq⟩)
    exact hLevel4_0 (p2 - p1) hne' E' (mapCirc_wf _ E hw) hsep'

  -- Level 1 + degree/pair bounds for any stripped WellFormed circuit separating allRows
  have hMainBounds : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26), E.WellFormed →
      (∀ i, Disjoint (E.leftVars i) (E.rightVars i)) → Separates E allRows →
      11 ≤ E.size ∧
      (∀ p : Fin 13, (Finset.univ.filter fun i : Fin E.size =>
          Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i).card + 9 ≤ E.size) ∧
      (∀ p l : Fin 13, ¬ inc p l → (Finset.univ.filter fun i : Fin E.size =>
          Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i ∨
          Fin.natAdd 13 l ∈ E.leftVars i ∨ Fin.natAdd 13 l ∈ E.rightVars i).card + 7 ≤ E.size) ∧
      (∀ p1 p2 : Fin 13, p1 ≠ p2 → (Finset.univ.filter fun i : Fin E.size =>
          Fin.castAdd 13 p1 ∈ E.leftVars i ∨ Fin.castAdd 13 p1 ∈ E.rightVars i ∨
          Fin.castAdd 13 p2 ∈ E.leftVars i ∨ Fin.castAdd 13 p2 ∈ E.rightVars i).card + 6 ≤ E.size) := by
    intro E hw hdisj hsep
    have hdegP : ∀ p : Fin 13, (Finset.univ.filter fun i : Fin E.size =>
        Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i).card + 9 ≤ E.size := by
      intro p
      obtain ⟨E', hw', hbd, heq⟩ := elim_vertices E hw {Fin.castAdd 13 p}
      have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 p ∈ I) := by
        intro I hI
        have hf := Finset.mem_filter.mp hI
        have hsub : ({Fin.castAdd 13 p} : Finset (Fin 26)) ⊆ I := Finset.singleton_subset_iff.mpr hf.2
        refine ⟨(heq I hsub).trans (hsep I hf.1).1, fun w hw => ?_⟩
        exact (heq (insert w I) (hsub.trans (Finset.subset_insert w I))).trans ((hsep I hf.1).2 w hw)
      have h9 : 9 ≤ E'.size := hLevel2 p E' hw' hsep'
      have hfeq : (Finset.univ.filter fun i : Fin E.size =>
          ∃ v ∈ ({Fin.castAdd 13 p} : Finset (Fin 26)), v ∈ E.leftVars i ∨ v ∈ E.rightVars i) =
          (Finset.univ.filter fun i : Fin E.size =>
            Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, exists_eq_left]
      rw [hfeq] at hbd
      omega
    have hpairPL : ∀ p l : Fin 13, ¬ inc p l → (Finset.univ.filter fun i : Fin E.size =>
        Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i ∨
        Fin.natAdd 13 l ∈ E.leftVars i ∨ Fin.natAdd 13 l ∈ E.rightVars i).card + 7 ≤ E.size := by
      intro p l hni
      obtain ⟨E', hw', hbd, heq⟩ := elim_vertices E hw {Fin.castAdd 13 p, Fin.natAdd 13 l}
      have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 p ∈ I ∧ Fin.natAdd 13 l ∈ I) := by
        intro I hI
        have hf := Finset.mem_filter.mp hI
        have hsub : ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin 26)) ⊆ I :=
          Finset.insert_subset hf.2.1 (Finset.singleton_subset_iff.mpr hf.2.2)
        refine ⟨(heq I hsub).trans (hsep I hf.1).1, fun w hw => ?_⟩
        exact (heq (insert w I) (hsub.trans (Finset.subset_insert w I))).trans ((hsep I hf.1).2 w hw)
      have h7 : 7 ≤ E'.size := hLevel3 p l hni E' hw' hsep'
      have hfeq : (Finset.univ.filter fun i : Fin E.size =>
          ∃ v ∈ ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin 26)), v ∈ E.leftVars i ∨ v ∈ E.rightVars i) =
          (Finset.univ.filter fun i : Fin E.size =>
            Fin.castAdd 13 p ∈ E.leftVars i ∨ Fin.castAdd 13 p ∈ E.rightVars i ∨
            Fin.natAdd 13 l ∈ E.leftVars i ∨ Fin.natAdd 13 l ∈ E.rightVars i) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]; tauto
      rw [hfeq] at hbd
      omega
    have hpairPP : ∀ p1 p2 : Fin 13, p1 ≠ p2 → (Finset.univ.filter fun i : Fin E.size =>
        Fin.castAdd 13 p1 ∈ E.leftVars i ∨ Fin.castAdd 13 p1 ∈ E.rightVars i ∨
        Fin.castAdd 13 p2 ∈ E.leftVars i ∨ Fin.castAdd 13 p2 ∈ E.rightVars i).card + 6 ≤ E.size := by
      intro p1 p2 hne
      obtain ⟨E', hw', hbd, heq⟩ := elim_vertices E hw {Fin.castAdd 13 p1, Fin.castAdd 13 p2}
      have hsep' : Separates E' (allRows.filter fun I => Fin.castAdd 13 p1 ∈ I ∧ Fin.castAdd 13 p2 ∈ I) := by
        intro I hI
        have hf := Finset.mem_filter.mp hI
        have hsub : ({Fin.castAdd 13 p1, Fin.castAdd 13 p2} : Finset (Fin 26)) ⊆ I :=
          Finset.insert_subset hf.2.1 (Finset.singleton_subset_iff.mpr hf.2.2)
        refine ⟨(heq I hsub).trans (hsep I hf.1).1, fun w hw => ?_⟩
        exact (heq (insert w I) (hsub.trans (Finset.subset_insert w I))).trans ((hsep I hf.1).2 w hw)
      have h6 : 6 ≤ E'.size := hLevel4 p1 p2 hne E' hw' hsep'
      have hfeq : (Finset.univ.filter fun i : Fin E.size =>
          ∃ v ∈ ({Fin.castAdd 13 p1, Fin.castAdd 13 p2} : Finset (Fin 26)), v ∈ E.leftVars i ∨ v ∈ E.rightVars i) =
          (Finset.univ.filter fun i : Fin E.size =>
            Fin.castAdd 13 p1 ∈ E.leftVars i ∨ Fin.castAdd 13 p1 ∈ E.rightVars i ∨
            Fin.castAdd 13 p2 ∈ E.leftVars i ∨ Fin.castAdd 13 p2 ∈ E.rightVars i) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]; tauto
      rw [hfeq] at hbd
      omega
    have h11 : 11 ≤ E.size := by
      by_contra! hlt
      have hsz : E.size ≤ 10 := by omega
      let Z : Finset (Fin 26) := Finset.univ.image (Fin.castAdd 13)
      have hZcard : Z.card = 13 := by
        have hinj : Function.Injective (Fin.castAdd 13 : Fin 13 → Fin 26) := fun a b h => Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val h)
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      obtain ⟨hPin, hPout, _, hPsame, hPopp⟩ := hL1_geom
      have hZle := card_le_size_of_deg_le_one E allRows Z hsep
        (fun z hz => by
          obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨rc, _, hpt⟩ := hPin p
          exact ⟨rowSet rc, Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, (mem_rowSet_cast rc p).mpr hpt⟩)
        (fun z hz => by
          obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
          obtain ⟨rc, _, hpf⟩ := hPout p
          exact ⟨rowSet rc, Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩, (fun hmem => by have ht := (mem_rowSet_cast rc p).mp hmem; dsimp only [rowP] at ht; rw [hpf] at ht; cases ht)⟩)
        (fun z1 hz1 z2 hz2 hne => by
          obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp hz1
          obtain ⟨p2, _, rfl⟩ := Finset.mem_image.mp hz2
          have hpn : p1 ≠ p2 := fun h => hne (congrArg (Fin.castAdd 13) h)
          obtain ⟨rc, _, h1, h2⟩ := hPsame p1 p2 hpn
          exact ⟨rowSet rc, Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩,
            (mem_rowSet_cast rc p1).mpr h1, (fun hmem => by have ht := (mem_rowSet_cast rc p2).mp hmem; dsimp only [rowP] at ht; rw [h2] at ht; cases ht)⟩)
        (fun z1 hz1 z2 hz2 hne => by
          obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp hz1
          obtain ⟨p2, _, rfl⟩ := Finset.mem_image.mp hz2
          have hpn : p1 ≠ p2 := fun h => hne (congrArg (Fin.castAdd 13) h)
          obtain ⟨rc, _, h1, h2⟩ := hPopp p1 p2 hpn
          exact ⟨rowSet rc, Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩,
            (fun hmem => by have ht := (mem_rowSet_cast rc p1).mp hmem; dsimp only [rowP] at ht; rw [h1] at ht; cases ht),
            (fun hmem => by have ht := (mem_rowSet_cast rc p2).mp hmem; dsimp only [rowP] at ht; rw [h2] at ht; cases ht)⟩)
        (fun z hz => by
          obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
          rw [(litSet_touch_card E hdisj (Fin.castAdd 13 p)).1]
          have h9 := hdegP p
          omega)
      omega
    exact ⟨h11, hdegP, hpairPL, hpairPP⟩

  -- Part 10: Apply to D := stripCircuit D0 and its point-line dual dualCirc D, then dispatch to hSize11 / hSize12
  obtain ⟨D, hD_sz0, hD_wf, hD_disj, hD_sing, hD_ev0⟩ := strip_exists D0 hD0_wf
  have hD_pos : ∀ p l : Fin 13, inc p l → D.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true := by
    intro p l hinc
    rw [hD_ev0, hD0_eval _ (Finset.insert_nonempty _ _)]
    have hp := hPos p l hinc
    refine Eq.trans ?_ hp
    congr 1; funext k
    exact decide_eq_decide.mpr (by simp only [Finset.mem_insert, Finset.mem_singleton])
  have hD_neg : ∀ P : Finset (Fin 13),
      (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ inc q l) ∧ inc p l) →
      ((¬∃ l : Fin 13, ∀ p ∈ P, inc p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ inc q l) → inc p l) →
      D.eval (liftRow P) = false := by
    intro P hmx hgen
    have hne : (liftRow P).Nonempty := by
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      have hP0 : P = ∅ := by
        ext p; simp only [Finset.notMem_empty, iff_false]
        intro hp
        have hm : Fin.castAdd 13 p ∈ liftRow P :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨p, hp, rfl⟩⟩
        rw [hem] at hm; exact Finset.notMem_empty _ hm
      exact hgen.1 ⟨0, fun p hp => by rw [hP0] at hp; exact (Finset.notMem_empty _ hp).elim⟩
    rw [hD_ev0, hD0_eval _ hne]
    have hn := hNeg P hmx hgen
    refine Eq.trans ?_ hn
    congr 1; funext k
    exact decide_eq_decide.mpr (by simp only [liftRow, inc, Finset.mem_filter, Finset.mem_univ, true_and])
  have hSep_of_pos_neg : ∀ (E : PEqualNP.AndCount.AndCountCircuit 26),
      (∀ p l : Fin 13, inc p l → E.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true) →
      (∀ P : Finset (Fin 13),
        (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ inc q l) ∧ inc p l) →
        ((¬∃ l : Fin 13, ∀ p ∈ P, inc p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ inc q l) → inc p l) →
        E.eval (liftRow P) = false) →
      Separates E allRows := by
    intro E hEp hEn I hI
    obtain ⟨rc, _, rfl⟩ := Finset.mem_image.mp hI
    refine ⟨hEn (rowPSet rc) (row_max rc) (row_generic rc), ?_⟩
    intro w hw
    by_cases hlt : w.val < 13
    · let p : Fin 13 := ⟨w.val, hlt⟩
      have hw_eq : w = Fin.castAdd 13 p := Fin.ext rfl
      rw [hw_eq] at hw ⊢
      have hpn : p ∉ rowPSet rc := fun h => hw ((mem_rowSet_cast rc p).mpr (Finset.mem_filter.mp h).2)
      obtain ⟨l, hlW, hinc⟩ := row_max rc p hpn
      have hlI : Fin.natAdd 13 l ∈ rowSet rc := (mem_rowSet_nat rc l).mpr ((rowW_iff rc l).mpr hlW)
      have hsub : ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin 26)) ⊆ insert (Fin.castAdd 13 p) (rowSet rc) :=
        Finset.insert_subset (Finset.mem_insert_self _ _) (Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem hlI))
      exact eval_mono E hsub (hEp p l hinc)
    · let l : Fin 13 := ⟨w.val - 13, by omega⟩
      have hw_eq : w = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
      rw [hw_eq] at hw ⊢
      have hln : ¬ ∀ q ∈ rowPSet rc, ¬ inc q l := fun h =>
        hw ((mem_rowSet_nat rc l).mpr ((rowW_iff rc l).mpr h))
      push Not at hln
      obtain ⟨p, hp, hinc⟩ := hln
      have hpI : Fin.castAdd 13 p ∈ rowSet rc := (mem_rowSet_cast rc p).mpr (Finset.mem_filter.mp hp).2
      have hsub : ({Fin.castAdd 13 p, Fin.natAdd 13 l} : Finset (Fin 26)) ⊆ insert (Fin.natAdd 13 l) (rowSet rc) :=
        Finset.insert_subset (Finset.mem_insert_of_mem hpI) (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
      exact eval_mono E hsub (hEp p l hinc)
  have hD_sep : Separates D allRows := hSep_of_pos_neg D hD_pos hD_neg
  have hD_outVars : D.outVars = ∅ := by
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    obtain ⟨hPin, _, hLin, _, _⟩ := hL1_geom
    by_cases hlt : v.val < 13
    · let p : Fin 13 := ⟨v.val, hlt⟩
      have hv_eq : v = Fin.castAdd 13 p := Fin.ext rfl
      obtain ⟨rc, _, hpt⟩ := hPin p
      have hm : v ∈ rowSet rc := hv_eq ▸ (mem_rowSet_cast rc p).mpr hpt
      have ht : D.eval (rowSet rc) = true := decide_eq_true (Or.inl ⟨v, hv, hm⟩)
      have hf := (hD_sep (rowSet rc) (Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩)).1
      rw [hf] at ht; cases ht
    · let l : Fin 13 := ⟨v.val - 13, by omega⟩
      have hv_eq : v = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
      obtain ⟨rc, _, hlt'⟩ := hLin l
      have hm : v ∈ rowSet rc := hv_eq ▸ (mem_rowSet_nat rc l).mpr hlt'
      have ht : D.eval (rowSet rc) = true := decide_eq_true (Or.inl ⟨v, hv, hm⟩)
      have hf := (hD_sep (rowSet rc) (Finset.mem_image.mpr ⟨rc, Finset.mem_univ _, rfl⟩)).1
      rw [hf] at ht; cases ht
  obtain ⟨hD_ge11, hD_degP, hD_pairPL, hD_pairPP⟩ := hMainBounds D hD_wf hD_disj hD_sep

  -- Point-line duality equivalence on Fin 26: castAdd 13 p <-> natAdd 13 (-p)
  let dualFn (k : Fin 26) : Fin 26 :=
    if h : k.val < 13 then Fin.natAdd 13 (-⟨k.val, h⟩)
    else Fin.castAdd 13 (-⟨k.val - 13, by omega⟩)
  have dualFn_cast : ∀ p : Fin 13, dualFn (Fin.castAdd 13 p) = Fin.natAdd 13 (-p) := by
    intro p
    have hlt : (Fin.castAdd 13 p).val < 13 := p.isLt
    simp only [dualFn, hlt, ↓reduceDIte]
    rfl
  have dualFn_nat : ∀ l : Fin 13, dualFn (Fin.natAdd 13 l) = Fin.castAdd 13 (-l) := by
    intro l
    have hlt : ¬ (Fin.natAdd 13 l).val < 13 := by simp only [Fin.val_natAdd, not_lt]; omega
    simp only [dualFn, hlt, ↓reduceDIte]
    have h1 : (⟨(Fin.natAdd 13 l).val - 13, by omega⟩ : Fin 13) = l :=
      Fin.ext (by simp only [Fin.val_natAdd, Nat.add_sub_cancel_left])
    rw [h1]
  let dualEquiv : Fin 26 ≃ Fin 26 :=
    { toFun := dualFn
      invFun := dualFn
      left_inv := by
        intro k
        by_cases h : k.val < 13
        · let p : Fin 13 := ⟨k.val, h⟩
          have hk : k = Fin.castAdd 13 p := Fin.ext rfl
          rw [hk, dualFn_cast, dualFn_nat, f13_neg_neg]
        · let l : Fin 13 := ⟨k.val - 13, by omega⟩
          have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
          rw [hk, dualFn_nat, dualFn_cast, f13_neg_neg]
      right_inv := by
        intro k
        by_cases h : k.val < 13
        · let p : Fin 13 := ⟨k.val, h⟩
          have hk : k = Fin.castAdd 13 p := Fin.ext rfl
          rw [hk, dualFn_cast, dualFn_nat, f13_neg_neg]
        · let l : Fin 13 := ⟨k.val - 13, by omega⟩
          have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
          rw [hk, dualFn_nat, dualFn_cast, f13_neg_neg] }
  let Ddual := mapCirc dualEquiv D
  have hDdual_wf : Ddual.WellFormed := mapCirc_wf dualEquiv D hD_wf
  have hDdual_disj : ∀ i, Disjoint (Ddual.leftVars i) (Ddual.rightVars i) := fun i =>
    Finset.disjoint_map dualEquiv.toEmbedding |>.mpr (hD_disj i)
  have hDdual_pos : ∀ p l : Fin 13, inc p l → Ddual.eval {Fin.castAdd 13 p, Fin.natAdd 13 l} = true := by
    intro p l hinc
    have hmap : ({Fin.castAdd 13 (-l), Fin.natAdd 13 (-p)} : Finset (Fin 26)).map dualEquiv.toEmbedding =
        {Fin.castAdd 13 p, Fin.natAdd 13 l} := by
      ext k
      simp only [Finset.mem_map, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h; rcases h with ⟨u, hu, rfl⟩
        rcases hu with rfl | rfl
        · right; change dualFn (Fin.castAdd 13 (-l)) = _; rw [dualFn_cast, f13_neg_neg]
        · left; change dualFn (Fin.natAdd 13 (-p)) = _; rw [dualFn_nat, f13_neg_neg]
      · intro h; rcases h with rfl | rfl
        · refine ⟨Fin.natAdd 13 (-p), Or.inr rfl, ?_⟩
          change dualFn (Fin.natAdd 13 (-p)) = _; rw [dualFn_nat, f13_neg_neg]
        · refine ⟨Fin.castAdd 13 (-l), Or.inl rfl, ?_⟩
          change dualFn (Fin.castAdd 13 (-l)) = _; rw [dualFn_cast, f13_neg_neg]
    rw [← hmap, mapCirc_eval]
    exact hD_pos (-l) (-p) ((inc_neg p l).mpr hinc)
  have hDdual_neg : ∀ P : Finset (Fin 13),
      (∀ p ∉ P, ∃ l : Fin 13, (∀ q ∈ P, ¬ inc q l) ∧ inc p l) →
      ((¬∃ l : Fin 13, ∀ p ∈ P, inc p l) ∧ ¬∃ p : Fin 13, ∀ l : Fin 13, (∀ q ∈ P, ¬ inc q l) → inc p l) →
      Ddual.eval (liftRow P) = false := by
    intro P hmx hgen
    let P' : Finset (Fin 13) := Finset.univ.filter fun q : Fin 13 => ∀ p ∈ P, ¬ inc p (-q)
    have hW' : ∀ l : Fin 13, (∀ q ∈ P', ¬ inc q l) ↔ -l ∈ P := by
      intro l
      constructor
      · intro hall
        by_contra hn
        obtain ⟨w, hw, hinc⟩ := hmx (-l) hn
        have hwm : -w ∈ P' := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          intro p hp; rw [f13_neg_neg]; exact hw p hp
        exact hall (-w) hwm (by simpa only [f13_neg_neg] using (inc_neg (-l) w).mpr hinc)
      · intro hml q hq hinc
        have hq' := (Finset.mem_filter.mp hq).2 (-l) hml
        have h1 : inc (-l) (-q) := (inc_neg q l).mpr hinc
        exact hq' h1
    have hmx' : ∀ q ∉ P', ∃ l : Fin 13, (∀ r ∈ P', ¬ inc r l) ∧ inc q l := by
      intro q hqn
      have hex : ∃ p ∈ P, inc p (-q) := by
        by_contra h; push Not at h
        exact hqn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      obtain ⟨p, hp, hinc⟩ := hex
      refine ⟨-p, (hW' (-p)).mpr (by rw [f13_neg_neg]; exact hp), ?_⟩
      simpa only [f13_neg_neg] using (inc_neg p (-q)).mpr hinc
    have hgen' : (¬∃ l : Fin 13, ∀ q ∈ P', inc q l) ∧
        ¬∃ q : Fin 13, ∀ l : Fin 13, (∀ r ∈ P', ¬ inc r l) → inc q l := by
      constructor
      · intro hex; rcases hex with ⟨l, hl⟩
        apply hgen.2
        refine ⟨-l, fun w hw => ?_⟩
        have hwm : -w ∈ P' := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => by rw [f13_neg_neg]; exact hw p hp⟩
        exact (inc_neg (-l) w).mp (by simpa only [f13_neg_neg] using hl (-w) hwm)
      · intro hex; rcases hex with ⟨q, hq⟩
        apply hgen.1
        refine ⟨-q, fun p hp => ?_⟩
        have hinc : inc q (-p) := hq (-p) ((hW' (-p)).mpr (by rw [f13_neg_neg]; exact hp))
        exact (inc_neg p (-q)).mp (by simpa only [f13_neg_neg] using hinc)
    have hmap : (liftRow P').map dualEquiv.toEmbedding = liftRow P := by
      ext k
      rw [Finset.mem_map_equiv]
      by_cases hlt : k.val < 13
      · let p : Fin 13 := ⟨k.val, hlt⟩
        have hk : k = Fin.castAdd 13 p := Fin.ext rfl
        rw [hk]
        have hsym : dualEquiv.symm (Fin.castAdd 13 p) = Fin.natAdd 13 (-p) := dualFn_cast p
        rw [hsym]
        simp only [liftRow, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨q, _, heq⟩
            have hv := congrArg Fin.val heq; simp only [Fin.val_castAdd, Fin.val_natAdd] at hv; omega
          · rcases h2 with ⟨l, heq, hall⟩
            have hlp : l = -p := by
              have hv := congrArg Fin.val heq; simp only [Fin.val_natAdd] at hv; exact Fin.ext (by omega)
            subst hlp
            have hpP : p ∈ P := by simpa only [f13_neg_neg] using (hW' (-p)).mp hall
            exact Or.inl ⟨p, hpP, rfl⟩
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨p', hp', heq⟩
            have hpp : p = p' := Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val heq)
            subst hpp
            exact Or.inr ⟨-p, rfl, (hW' (-p)).mpr (by simpa only [f13_neg_neg] using hp')⟩
          · rcases h2 with ⟨l, heq, _⟩
            have hv := congrArg Fin.val heq; simp only [Fin.val_castAdd, Fin.val_natAdd] at hv; omega
      · let l : Fin 13 := ⟨k.val - 13, by omega⟩
        have hk : k = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
        rw [hk]
        have hsym : dualEquiv.symm (Fin.natAdd 13 l) = Fin.castAdd 13 (-l) := dualFn_nat l
        rw [hsym]
        simp only [liftRow, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨q, hq, heq⟩
            have hql : -l = q := Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val heq)
            rw [← hql] at hq
            have hq' := (Finset.mem_filter.mp hq).2
            exact Or.inr ⟨l, rfl, fun p hp => by simpa only [f13_neg_neg] using hq' p hp⟩
          · rcases h2 with ⟨w, heq, _⟩
            have hv := congrArg Fin.val heq; simp only [Fin.val_castAdd, Fin.val_natAdd] at hv; omega
        · intro h; rcases h with h1 | h2
          · rcases h1 with ⟨p, _, heq⟩
            have hv := congrArg Fin.val heq; simp only [Fin.val_castAdd, Fin.val_natAdd] at hv; omega
          · rcases h2 with ⟨l', heq, hall⟩
            have hll : l = l' := by
              have hv := congrArg Fin.val heq; simp only [Fin.val_natAdd] at hv; exact Fin.ext (by omega)
            subst hll
            exact Or.inl ⟨-l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => by
              rw [f13_neg_neg]; exact hall p hp⟩, rfl⟩
    rw [← hmap, mapCirc_eval]
    exact hD_neg P' hmx' hgen'
  have hDdual_sep : Separates Ddual allRows := hSep_of_pos_neg Ddual hDdual_pos hDdual_neg
  obtain ⟨_, hDdual_degP, _, hDdual_pairPP⟩ := hMainBounds Ddual hDdual_wf hDdual_disj hDdual_sep
  have hD_degL : ∀ l : Fin 13, (Finset.univ.filter fun i : Fin D.size =>
      Fin.natAdd 13 l ∈ D.leftVars i ∨ Fin.natAdd 13 l ∈ D.rightVars i).card + 9 ≤ D.size := by
    intro l
    have h := hDdual_degP (-l)
    have heq : (Finset.univ.filter fun i : Fin Ddual.size =>
        Fin.castAdd 13 (-l) ∈ Ddual.leftVars i ∨ Fin.castAdd 13 (-l) ∈ Ddual.rightVars i) =
        (Finset.univ.filter fun i : Fin D.size =>
          Fin.natAdd 13 l ∈ D.leftVars i ∨ Fin.natAdd 13 l ∈ D.rightVars i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ddual, mapCirc, Finset.mem_map_equiv]
      have hsym : dualEquiv.symm (Fin.castAdd 13 (-l)) = Fin.natAdd 13 l := by
        change dualFn (Fin.castAdd 13 (-l)) = _; rw [dualFn_cast, f13_neg_neg]
      rw [hsym]
    simpa only [heq] using h
  have hD_pairLL : ∀ l1 l2 : Fin 13, l1 ≠ l2 → (Finset.univ.filter fun i : Fin D.size =>
      Fin.natAdd 13 l1 ∈ D.leftVars i ∨ Fin.natAdd 13 l1 ∈ D.rightVars i ∨
      Fin.natAdd 13 l2 ∈ D.leftVars i ∨ Fin.natAdd 13 l2 ∈ D.rightVars i).card + 6 ≤ D.size := by
    intro l1 l2 hne
    have h := hDdual_pairPP (-l1) (-l2) (fun h => hne ((f13_neg_inj l1 l2).mp h))
    have heq : (Finset.univ.filter fun i : Fin Ddual.size =>
        Fin.castAdd 13 (-l1) ∈ Ddual.leftVars i ∨ Fin.castAdd 13 (-l1) ∈ Ddual.rightVars i ∨
        Fin.castAdd 13 (-l2) ∈ Ddual.leftVars i ∨ Fin.castAdd 13 (-l2) ∈ Ddual.rightVars i) =
        (Finset.univ.filter fun i : Fin D.size =>
          Fin.natAdd 13 l1 ∈ D.leftVars i ∨ Fin.natAdd 13 l1 ∈ D.rightVars i ∨
          Fin.natAdd 13 l2 ∈ D.leftVars i ∨ Fin.natAdd 13 l2 ∈ D.rightVars i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Ddual, mapCirc, Finset.mem_map_equiv]
      have h1 : dualEquiv.symm (Fin.castAdd 13 (-l1)) = Fin.natAdd 13 l1 := by
        change dualFn (Fin.castAdd 13 (-l1)) = _; rw [dualFn_cast, f13_neg_neg]
      have h2 : dualEquiv.symm (Fin.castAdd 13 (-l2)) = Fin.natAdd 13 l2 := by
        change dualFn (Fin.castAdd 13 (-l2)) = _; rw [dualFn_cast, f13_neg_neg]
      rw [h1, h2]
    simpa only [heq] using h
  have hD_degAll : ∀ v : Fin 26, (Finset.univ.filter fun i : Fin D.size =>
      v ∈ D.leftVars i ∨ v ∈ D.rightVars i).card + 9 ≤ D.size := by
    intro v
    by_cases hlt : v.val < 13
    · let p : Fin 13 := ⟨v.val, hlt⟩
      have hv : v = Fin.castAdd 13 p := Fin.ext rfl
      rw [hv]; exact hD_degP p
    · let l : Fin 13 := ⟨v.val - 13, by omega⟩
      have hv : v = Fin.natAdd 13 l := Fin.ext (by dsimp [l]; omega)
      rw [hv]; exact hD_degL l

  -- Final dispatch: since D.size = AND count of C and 11 <= D.size, either 13 <= AND count of C or D.size in {11, 12}
  have hD_eq_ncard : D.size = {x5 : Fin C.gates.length | (C.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard :=
    hD_sz0.trans hD0_size
  rw [← hD_eq_ncard]
  by_contra! hlt13
  have hcases : D.size = 11 ∨ D.size = 12 := by omega
  have hUnion_eq : ∀ (u v : Fin 26),
      (Finset.univ.filter fun i : Fin D.size => u ∈ D.leftVars i ∨ u ∈ D.rightVars i) ∪
      (Finset.univ.filter fun i : Fin D.size => v ∈ D.leftVars i ∨ v ∈ D.rightVars i) =
      (Finset.univ.filter fun i : Fin D.size =>
        u ∈ D.leftVars i ∨ u ∈ D.rightVars i ∨ v ∈ D.leftVars i ∨ v ∈ D.rightVars i) := by
    intro u v; ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  rcases hcases with h11 | h12
  · exact hSize11 D hD_wf h11 hD_outVars hD_sing hD_disj hD_pos hD_neg
      (fun v => by dsimp only; have := hD_degAll v; omega)
      (fun p l hni => by dsimp only; rw [hUnion_eq]; have := hD_pairPL p l hni; omega)
      (fun p1 p2 hne => by dsimp only; rw [hUnion_eq]; have := hD_pairPP p1 p2 hne; omega)
      (fun l1 l2 hne => by dsimp only; rw [hUnion_eq]; have := hD_pairLL l1 l2 hne; omega)
  · exact hSize12 D hD_wf h12 hD_outVars hD_sing hD_disj hD_pos hD_neg
      (fun v => by dsimp only; have := hD_degAll v; omega)
      (fun p l hni => by dsimp only; rw [hUnion_eq]; have := hD_pairPL p l hni; omega)
      (fun p1 p2 hne => by dsimp only; rw [hUnion_eq]; have := hD_pairPP p1 p2 hne; omega)
      (fun l1 l2 hne => by dsimp only; rw [hUnion_eq]; have := hD_pairLL l1 l2 hne; omega)
