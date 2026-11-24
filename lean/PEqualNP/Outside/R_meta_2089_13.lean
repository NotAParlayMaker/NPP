import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Wire monotonicity is card02_mono in the project library.
-- On the negative row anchored at p, only point p and lines missing p are on.
-- Every two coordinates are both off on some such row. Raising either one then contains
-- a positive incidence pair. Thus one operand has a sensitivity witness for every coordinate.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_2089_13
    (wireMono : ∀ (n : ℕ) (C : Circuit) (o : ℕ), IsMonotoneCircuit C →
      ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      (C.wires (List.ofFn x)).getD o false = true →
      (C.wires (List.ofFn y)).getD o false = true)
    (fullOperand :
      let diff : Finset (Fin 13) := {0, 1, 3, 9}
      let inc := fun p l : Fin 13 => ∃ d ∈ diff, p = l + d
      let avoids := fun (P : Finset (Fin 13)) (l : Fin 13) => ∀ p ∈ P, ¬inc p l
      let pair := fun (p l : Fin 13) (k : Fin 26) =>
        decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 l)
      let row := fun (P : Finset (Fin 13)) (k : Fin 26) =>
        decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨ ∃ l, k = Fin.natAdd 13 l ∧ avoids P l)
      let wire := fun (C : Circuit) (w : ℕ) (x : Fin 26 → Bool) =>
        (C.wires (List.ofFn x)).getD w false
      ∀ C : Circuit, Monotone2 C → C.size ≤ 62 →
      ∀ a b : Fin (26 + C.size), a ≠ b →
      (∀ i : Fin 26, ∃ p : Fin 13, wire C a (row {p}) = false ∧
        wire C a (Function.update (row {p}) i true) = true) →
      (∀ p l, inc p l → (wire C a (pair p l) && wire C b (pair p l)) = true) →
      (∀ P, (∀ v ∉ P, ∃ l, avoids P l ∧ inc v l) →
        ((∃ l, ∀ p ∈ P, inc p l) ∨ ∃ p, ∀ l, avoids P l → inc p l) →
        (wire C a (row P) && wire C b (row P)) = false) → False) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) (x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (13 : ℕ) x4 ∨ x6 = Fin.natAdd (13 : ℕ) x5); have x5 : Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x5 : Finset (Fin (13 : ℕ))) (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x7 ∈ x5, x6 = Fin.castAdd (13 : ℕ) x7) ∨ ∃ (x7 : Fin (13 : ℕ)), x6 = Fin.natAdd (13 : ℕ) x7 ∧ ∀ x8 ∈ x5, ¬∃ x10 ∈ x1, x8 = x7 + x10); have x6 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : Fin (26 : ℕ) → Bool) => (x6.wires (List.ofFn x8)).getD x7 Bool.false; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (62 : ℕ) → ∀ (x10 x11 : Fin ((26 : ℕ) + x7.size)), x10 ≠ x11 → (∀ (x13 x14 : Fin (13 : ℕ)), x2 x13 x14 → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x4 x13 x14), x6 x7 (↑x11) (x4 x13 x14)] = Bool.true) → (∀ (x14 : Finset (Fin (13 : ℕ))), (∀ x15 ∉ x14, ∃ (x17 : Fin (13 : ℕ)), x3 x14 x17 ∧ x2 x15 x17) → ((∃ (x16 : Fin (13 : ℕ)), ∀ x17 ∈ x14, x2 x17 x16) ∨ ∃ (x16 : Fin (13 : ℕ)), ∀ (x17 : Fin (13 : ℕ)), x3 x14 x17 → x2 x16 x17) → PEqualNP.CircuitLowerBounds.GateOp.and.eval [x6 x7 (↑x10) (x5 x14), x6 x7 (↑x11) (x5 x14)] = Bool.false) → False := by
  intro diff inc avoids pair row wire C hm hsize a b hab hp hn
  have hmono : IsMonotoneCircuit C := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hm g hg).1
  have andEval (x y : Bool) : GateOp.and.eval [x, y] = (x && y) := by
    cases x <;> cases y <;> rfl
  have positives (u l : Fin 13) (h : inc u l) :
      wire C a (pair u l) = true ∧ wire C b (pair u l) = true := by
    simpa only [andEval, Bool.and_eq_true] using hp u l h
  have maximal : ∀ p : Fin 13, ∀ v ∉ ({p} : Finset (Fin 13)),
      ∃ l, avoids {p} l ∧ inc v l := by decide +kernel
  have collinear : ∀ p : Fin 13, ∃ l, ∀ v ∈ ({p} : Finset (Fin 13)), inc v l := by
    decide +kernel
  let masks : List ℕ := [25018369, 50036738, 32972804, 65945608, 64790544, 62480416, 57860160, 48619648, 30138624, 60277248, 53453824, 39806976, 12513280]
  let bit := fun (p : Fin 13) (i : Fin 26) => (masks.getD p.val 0).testBit i.val
  have rowBit : ∀ (p : Fin 13) (i : Fin 26), row {p} i = bit p i := by
    decide +kernel
  have common : ∀ i j : Fin 26, ∃ p : Fin 13, row {p} i = false ∧ row {p} j = false := by
    simp_rw [rowBit]
    decide +kernel
  have contact : ∀ (p : Fin 13) (i : Fin 26), row {p} i = false →
      ∃ u l : Fin 13, inc u l ∧
        (Fin.castAdd 13 u = i ∨ row {p} (Fin.castAdd 13 u) = true) ∧
        (Fin.natAdd 13 l = i ∨ row {p} (Fin.natAdd 13 l) = true) := by
    simp_rw [rowBit]
    decide +kernel
  let sensitive := fun (w : ℕ) (i : Fin 26) =>
    ∃ p : Fin 13, wire C w (row {p}) = false ∧
      wire C w (Function.update (row {p}) i true) = true
  have force (w : ℕ) (hw : ∀ u l, inc u l → wire C w (pair u l) = true)
      (p : Fin 13) (i : Fin 26) (missing : row {p} i = false)
      (reject : wire C w (row {p}) = false) : sensitive w i := by
    obtain ⟨u, l, edge, hu, hl⟩ := contact p i missing
    refine ⟨p, reject, wireMono 26 C w hmono _ _ ?_ (hw u l edge)⟩
    intro v hv
    change decide (v = Fin.castAdd 13 u ∨ v = Fin.natAdd 13 l) = true at hv
    rcases of_decide_eq_true hv with rfl | rfl
    · by_cases eq : Fin.castAdd 13 u = i
      · simp only [eq, Function.update_self]
      · simpa only [Function.update_of_ne eq] using hu.resolve_left eq
    · by_cases eq : Fin.natAdd 13 l = i
      · simp only [eq, Function.update_self]
      · simpa only [Function.update_of_ne eq] using hl.resolve_left eq
  have either : (∀ i, sensitive a i) ∨ ∀ i, sensitive b i := by
    by_contra! losing
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := losing
    obtain ⟨p, hpi, hpj⟩ := common i j
    have h := hn {p} (maximal p) (Or.inl (collinear p))
    rw [andEval] at h
    cases ha : wire C a (row {p}) with
    | false => exact hi (force a (fun u l e => (positives u l e).1) p i hpi ha)
    | true =>
      have hb : wire C b (row {p}) = false := by simpa [ha] using h
      exact hj (force b (fun u l e => (positives u l e).2) p j hpj hb)
  rcases either with left | right
  · apply fullOperand C hm hsize a b hab left
    · intro u l h
      simpa only [andEval] using hp u l h
    · intro P hP hD
      simpa only [andEval] using hn P hP hD
  · apply fullOperand C hm hsize b a hab.symm right
    · intro u l h
      simpa only [andEval, Bool.and_comm] using hp u l h
    · intro P hP hD
      simpa only [andEval, Bool.and_comm] using hn P hP hD
