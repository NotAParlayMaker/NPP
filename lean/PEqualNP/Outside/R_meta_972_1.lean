import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_972_1
    (hnormalize :
      let mark := fun d : Fin 13 => decide (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9)
      let quad := fun Q : Finset (Fin 13) =>
        Q.card = 4 ∧ ∀ l : Fin 13, {p ∈ Q | mark (p - l) = true}.card ≤ 2
      let row := fun Q : Finset (Fin 13) =>
        (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
          List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, mark (p - l) = false)
      let tests := fun C : Circuit =>
        (∀ p l : Fin 13, mark (p - l) = true →
          C.eval ((List.ofFn fun u : Fin 13 => decide (u = p)) ++
            List.ofFn fun v : Fin 13 => decide (v = l)) = true) ∧
        ∀ Q : Finset (Fin 13), quad Q → C.eval (row Q) = false
      let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
      ∀ C : Circuit, Monotone2 C →
        (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 13, near p l ∧ x (Fin.castAdd 13 p) = true ∧
            x (Fin.natAdd 13 l) = true) →
        ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ tests D ∧ D.size ≤ C.size)
    (hflat :
      have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x1 (x3 - x4) = Bool.true → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x1 (x6 - x5) = Bool.true}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x1 (x7 - x6) = Bool.false)) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → x2 x3 → (¬∃ (x7 : ℕ) (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x7 x8) → (64 : ℕ) ≤ x3.size)
    (hsimplify :
      have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → x4 x5 → (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x9 x10 ∧ ∀ (x11 : Finset (Fin (13 : ℕ))), x2 x11 → (x5.wires (x3 x11)).getD ((26 : ℕ) + x9) Bool.false = Bool.false) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x10 ∧ x4 x10 ∧ (x10.size < x5.size ∨ x10.size = x5.size ∧ PEqualNP.TopForm.andPairs (26 : ℕ) x10 < PEqualNP.TopForm.andPairs (26 : ℕ) x5))
    (hremaining :
      let mark := fun d : Fin 13 => decide (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9)
      let quad := fun Q : Finset (Fin 13) =>
        Q.card = 4 ∧ ∀ l : Fin 13, {p ∈ Q | mark (p - l) = true}.card ≤ 2
      let row := fun Q : Finset (Fin 13) =>
        (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
          List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, mark (p - l) = false)
      let tests := fun C : Circuit =>
        (∀ p l : Fin 13, mark (p - l) = true →
          C.eval ((List.ofFn fun u : Fin 13 => decide (u = p)) ++
            List.ofFn fun v : Fin 13 => decide (v = l)) = true) ∧
        ∀ Q : Finset (Fin 13), quad Q → C.eval (row Q) = false
      let nested := fun C : Circuit => fun i j : ℕ =>
        (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j
      ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → tests C → C.size < 64 →
        (∃ i j : ℕ, nested C i j) →
        (∀ i j : ℕ, nested C i j →
          ∃ Q : Finset (Fin 13), quad Q ∧ (C.wires (row Q)).getD (26 + i) false = true) →
        False) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) → 64 ≤ C.size := by
  classical
  intro C hmono hval
  by_contra hnot
  have hsmall : C.size < 64 := by omega
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  let edges : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
  let pt (p : Fin 13) : Fin 26 := Fin.castAdd 13 p
  let ln (l : Fin 13) : Fin 26 := Fin.natAdd 13 l
  have table : ∀ u v : Fin 26, (u.val, v.val) ∈ edges ↔
      u.val < 13 ∧ 13 ≤ v.val ∧ near (Fin.ofNat 13 u.val) (Fin.ofNat 13 v.val) := by
    dsimp only [edges, near]
    decide +kernel
  have pointInv (u : Fin 26) (hu : u.val < 13) : pt (Fin.ofNat 13 u.val) = u := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt hu
  have lineInv (v : Fin 26) (hv : 13 ≤ v.val) : ln (Fin.ofNat 13 v.val) = v := by
    apply Fin.ext
    change 13 + v.val % 13 = v.val
    have := v.isLt
    omega
  have ptRaw (p : Fin 13) : Fin.ofNat 13 (pt p).val = p := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt p.isLt
  have lnRaw (l : Fin 13) : Fin.ofNat 13 (ln l).val = l := by
    apply Fin.ext
    change (13 + l.val) % 13 = l.val
    have := l.isLt
    omega
  have hsum (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, near p l ∧ x (pt p) = true ∧ x (ln l) = true := by
    rw [hval x]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨hU, hV, hrel⟩ := (table u v).1 huv
      exact ⟨Fin.ofNat 13 u.val, Fin.ofNat 13 v.val, hrel,
        by simpa only [pointInv u hU] using hu,
        by simpa only [lineInv v hV] using hv⟩
    · rintro ⟨p, l, hrel, hp, hl⟩
      refine ⟨pt p, ln l, (table (pt p) (ln l)).2 ⟨p.isLt, ?_, ?_⟩, hp, hl⟩
      · change 13 ≤ 13 + l.val
        omega
      · simpa only [ptRaw, lnRaw] using hrel
  obtain ⟨C1, hM1, hR1, hT1, hsize1⟩ := hnormalize C hmono hsum
  let mark := fun d : Fin 13 => decide (d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9)
  let quad := fun Q : Finset (Fin 13) =>
    Q.card = 4 ∧ ∀ l : Fin 13, {p ∈ Q | mark (p - l) = true}.card ≤ 2
  let row := fun Q : Finset (Fin 13) =>
    (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
      List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, mark (p - l) = false)
  let tests := fun C : Circuit =>
    (∀ p l : Fin 13, mark (p - l) = true →
      C.eval ((List.ofFn fun u : Fin 13 => decide (u = p)) ++
        List.ofFn fun v : Fin 13 => decide (v = l)) = true) ∧
    ∀ Q : Finset (Fin 13), quad Q → C.eval (row Q) = false
  let good := fun D : Circuit => Monotone2 D ∧ ReadsBack 26 D ∧ tests D
  let sizes := fun k : ℕ => ∃ D : Circuit, good D ∧ D.size = k
  have hexSize : ∃ k, sizes k := ⟨C1.size, C1, ⟨hM1, hR1, hT1⟩, rfl⟩
  obtain ⟨D0, hgood0, hsize0⟩ := Nat.find_spec hexSize
  let counts := fun k : ℕ =>
    ∃ D : Circuit, good D ∧ D.size = Nat.find hexSize ∧ andPairs 26 D = k
  have hexCount : ∃ k, counts k := ⟨andPairs 26 D0, D0, hgood0, hsize0, rfl⟩
  obtain ⟨D, ⟨hM, hR, hT⟩, hsize, hcount⟩ := Nat.find_spec hexCount
  have hminSize (W : Circuit) (hgood : good W) : D.size ≤ W.size := by
    rw [hsize]
    exact Nat.find_min' hexSize (show sizes W.size from ⟨W, hgood, rfl⟩)
  have hDsmall : D.size < 64 :=
    lt_of_le_of_lt ((hminSize C1 ⟨hM1, hR1, hT1⟩).trans hsize1) hsmall
  let nested := fun i j : ℕ =>
    (gateAt D i).op = .and ∧ (gateAt D j).op = .and ∧ InCone 26 D i j
  by_cases hnest : ∃ i j : ℕ, nested i j
  · by_cases hsafe : ∃ i j : ℕ, nested i j ∧
        ∀ Q : Finset (Fin 13), quad Q → (D.wires (row Q)).getD (26 + i) false = false
    · obtain ⟨i, j, ⟨hi, hj, hpath⟩, hsound⟩ := hsafe
      obtain ⟨W, hWM, hWR, hWT, hdrop⟩ :=
        hsimplify D hM hR hT ⟨i, j, hi, hj, hpath, hsound⟩
      rcases hdrop with hlt | ⟨heq, hdec⟩
      · exact (Nat.not_lt_of_ge (hminSize W ⟨hWM, hWR, hWT⟩)) hlt
      · have hw : counts (andPairs 26 W) :=
          ⟨W, ⟨hWM, hWR, hWT⟩, heq.trans hsize, rfl⟩
        have hp := Nat.find_min' hexCount hw
        rw [← hcount] at hp
        exact (Nat.not_lt_of_ge hp) hdec
    · apply hremaining D hM hR hT hDsmall hnest
      intro i j hij
      by_contra hnone
      apply hsafe
      refine ⟨i, j, hij, ?_⟩
      intro Q hQ
      cases hrow : (D.wires (row Q)).getD (26 + i) false
      · rfl
      · exact (hnone ⟨Q, hQ, hrow⟩).elim
  · have hfloor := hflat D hM hR ⟨hT.1, fun Q hcard hlines => hT.2 Q ⟨hcard, hlines⟩⟩ hnest
    exact (Nat.not_lt_of_ge hfloor) hDsmall
