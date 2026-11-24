import PEqualNP.Defs

-- A three-hypothesis cut for the meta-complexity step. A two-pin circuit
-- on nine inputs with a hint wire is separated from the printed Boolean
-- polynomial by an assignment reading only the input wires, except that a
-- pin on the hint wire or a pin pair on an edge of the printed graph is
-- routed to the added hypotheses (which state exactly those obstructions
-- for the set of pins, the head pin, and the tail pin).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.R_meta_1912_1_aux

private theorem prefix_preserves : ∀ (t : List Gate) (b : List Bool) (j : ℕ),
    j < b.length → ((Circuit.mk t 0).wires b).getD j false = b.getD j false := by
  intro t
  induction t with
  | nil => intro b j _; rfl
  | cons g ts ih =>
    intro b j hj
    show ((Circuit.mk ts 0).wires
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)])).getD j false = _
    rw [ih _ _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hj

private theorem base_len (w : Fin 9 → Bool) : (List.ofFn w).length = 9 := by
  rw [List.length_ofFn]

private theorem get_wires (t : List Gate) (w : Fin 9 → Bool) (p : Fin 24) (hp : (p:ℕ) < 9) :
    ((Circuit.mk t 0).wires (List.ofFn w ++ [w (4:Fin 9) && w (6:Fin 9)])).getD (p:ℕ) false =
    w ⟨p, hp⟩ := by
  have h10 : (p:ℕ) < (List.ofFn w ++ [w (4:Fin 9) && w (6:Fin 9)]).length := by
    rw [List.length_append, base_len, List.length_cons, List.length_nil]; omega
  have h9 : (p:ℕ) < (List.ofFn w).length := by
    rw [base_len]; exact hp
  rw [prefix_preserves _ _ _ h10, List.getD_append _ _ _ _ h9,
    List.getD_eq_getElem (hn := h9), List.getElem_ofFn (h := h9)]

private theorem get_hint (t : List Gate) (w : Fin 9 → Bool) :
    ((Circuit.mk t 0).wires (List.ofFn w ++ [w (4:Fin 9) && w (6:Fin 9)])).getD 9 false =
    (w (4:Fin 9) && w (6:Fin 9)) := by
  have h10 : (9 : ℕ) < (List.ofFn w ++ [w (4:Fin 9) && w (6:Fin 9)]).length := by
    rw [List.length_append, base_len, List.length_cons, List.length_nil]; omega
  have hle : (List.ofFn w).length ≤ (9 : ℕ) := by
    rw [base_len]
  have hsub : (9 : ℕ) - (List.ofFn w).length = 0 := by
    rw [base_len]
  rw [prefix_preserves _ _ _ h10, List.getD_eq_getElem?_getD,
    List.getElem?_append_right hle, hsub, List.getElem?_cons_zero, Option.getD_some]

private theorem get_wiresN (t : List Gate) (w : Fin 9 → Bool) (j : ℕ) (hj : j < 9) :
    ((Circuit.mk t 0).wires (List.ofFn w ++ [w (4:Fin 9) && w (6:Fin 9)])).getD j false =
    w ⟨j, hj⟩ :=
  get_wires t w (⟨j, by omega⟩ : Fin 24) (by omega)

private theorem get_hintN (t : List Gate) (w : Fin 9 → Bool) (j : ℕ) (hj : j = 9) :
    ((Circuit.mk t 0).wires (List.ofFn w ++ [w (4:Fin 9) && w (6:Fin 9)])).getD j false =
    (w (4:Fin 9) && w (6:Fin 9)) := by
  subst hj
  exact get_hint t w

private theorem siteEq (t : List Gate) (w : Fin 9 → Bool) (j : Fin 24) :
    ((Circuit.mk t 0).wires (List.ofFn w ++ [w (4:Fin 9) && w (6:Fin 9)])).getD (j:ℕ) false =
    if h : (j:ℕ) < 9 then w ⟨j, h⟩
    else if h : (j:ℕ) = 9 then (w (4:Fin 9) && w (6:Fin 9))
    else ((Circuit.mk t 0).wires (List.ofFn w ++ [w (4:Fin 9) && w (6:Fin 9)])).getD (j:ℕ) false := by
  by_cases h9 : (j:ℕ) < 9
  · rw [dif_pos h9]
    exact get_wiresN t w (j:ℕ) h9
  · rw [dif_neg h9]
    by_cases h99 : (j:ℕ) = 9
    · rw [dif_pos h99]
      exact get_hintN t w (j:ℕ) h99
    · rw [dif_neg h99]

private def W1 (p : Fin 24) : Fin 9 → Bool :=
  if (p : ℕ) = 9
  then fun k => decide ((k : ℕ) = 4 ∨ (k : ℕ) = 6)
  else fun k => decide ((k : ℕ) = (p : ℕ))

private def W2 (p q : Fin 24) : Fin 9 → Bool :=
  if (p : ℕ) = 9 ∨ (q : ℕ) = 9
  then fun k => decide ((k : ℕ) = 1 ∨ (k : ℕ) = 2)
  else if p = q
  then fun k => decide ((k : ℕ) = (p : ℕ))
  else if ((p.val = 0 ∧ q.val = 1) ∨ (p.val = 1 ∧ q.val = 0) ∨ (p.val = 1 ∧ q.val = 2) ∨ (p.val = 2 ∧ q.val = 1) ∨ (p.val = 2 ∧ q.val = 3) ∨ (p.val = 3 ∧ q.val = 2) ∨ (p.val = 3 ∧ q.val = 4) ∨ (p.val = 4 ∧ q.val = 3) ∨ (p.val = 4 ∧ q.val = 0) ∨ (p.val = 0 ∧ q.val = 4) ∨ (p.val = 0 ∧ q.val = 5) ∨ (p.val = 5 ∧ q.val = 0) ∨ (p.val = 1 ∧ q.val = 6) ∨ (p.val = 6 ∧ q.val = 1) ∨ (p.val = 2 ∧ q.val = 7) ∨ (p.val = 7 ∧ q.val = 2) ∨ (p.val = 3 ∧ q.val = 8) ∨ (p.val = 8 ∧ q.val = 3) ∨ (p.val = 5 ∧ q.val = 7) ∨ (p.val = 7 ∧ q.val = 5) ∨ (p.val = 6 ∧ q.val = 8) ∨ (p.val = 8 ∧ q.val = 6) ∨ (p.val = 8 ∧ q.val = 5) ∨ (p.val = 5 ∧ q.val = 8))
  then fun k => decide ((k : ℕ) = (if (p.val = 1 ∧ q.val = 2) ∨ (p.val = 2 ∧ q.val = 1) then (3 : ℕ) else (1 : ℕ)) ∨ (k : ℕ) = (if (p.val = 1 ∧ q.val = 2) ∨ (p.val = 2 ∧ q.val = 1) then (4 : ℕ) else (2 : ℕ)))
  else fun k => decide ((k : ℕ) = (p : ℕ) ∨ (k : ℕ) = (q : ℕ))

private theorem refute_nil (x1 : List Gate) :
    GateOp.and.eval (List.map (fun (x9 : Fin (24 : ℕ)) =>
            ({ gates := x1, output := (0 : ℕ) : Circuit }.wires
              (List.ofFn (fun (_ : Fin (9 : ℕ)) => false) ++ [(fun (_ : Fin (9 : ℕ)) => false) (4 : Fin 9) && (fun (_ : Fin (9 : ℕ)) => false) (6 : Fin 9)])).getD (↑x9) Bool.false)
            []) ≠ ((((fun (_ : Fin (9 : ℕ)) => false)) (0 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (1 : Fin (9 : ℕ)) || ((fun (_ : Fin (9 : ℕ)) => false)) (1 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (2 : Fin (9 : ℕ)) || ((fun (_ : Fin (9 : ℕ)) => false)) (2 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (3 : Fin (9 : ℕ)) || ((fun (_ : Fin (9 : ℕ)) => false)) (3 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (4 : Fin (9 : ℕ)) || ((fun (_ : Fin (9 : ℕ)) => false)) (4 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (0 : Fin (9 : ℕ)) || ((fun (_ : Fin (9 : ℕ)) => false)) (0 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (5 : Fin (9 : ℕ)) || ((fun (_ : Fin (9 : ℕ)) => false)) (1 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (6 : Fin (9 : ℕ)) || ((fun (_ : Fin (9 : ℕ)) => false)) (2 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (7 : Fin (9 : ℕ)) || ((fun (_ : Fin (9 : ℕ)) => false)) (3 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (8 : Fin (9 : ℕ)) || ((fun (_ : Fin (9 : ℕ)) => false)) (5 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (7 : Fin (9 : ℕ)) || ((fun (_ : Fin (9 : ℕ)) => false)) (6 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (8 : Fin (9 : ℕ)) || ((fun (_ : Fin (9 : ℕ)) => false)) (8 : Fin (9 : ℕ)) && ((fun (_ : Fin (9 : ℕ)) => false)) (5 : Fin (9 : ℕ)))) := by
  simp only [List.map_nil]
  decide

private theorem refute_single (x1 : List Gate) (p : Fin 24) (hp : (p : ℕ) < 10) :
    GateOp.and.eval (List.map (fun (x9 : Fin (24 : ℕ)) =>
            ({ gates := x1, output := (0 : ℕ) : Circuit }.wires
              (List.ofFn (W1 p) ++ [(W1 p) (4 : Fin 9) && (W1 p) (6 : Fin 9)])).getD (↑x9) Bool.false)
            [p]) ≠ ((((W1 p)) (0 : Fin (9 : ℕ)) && ((W1 p)) (1 : Fin (9 : ℕ)) || ((W1 p)) (1 : Fin (9 : ℕ)) && ((W1 p)) (2 : Fin (9 : ℕ)) || ((W1 p)) (2 : Fin (9 : ℕ)) && ((W1 p)) (3 : Fin (9 : ℕ)) || ((W1 p)) (3 : Fin (9 : ℕ)) && ((W1 p)) (4 : Fin (9 : ℕ)) || ((W1 p)) (4 : Fin (9 : ℕ)) && ((W1 p)) (0 : Fin (9 : ℕ)) || ((W1 p)) (0 : Fin (9 : ℕ)) && ((W1 p)) (5 : Fin (9 : ℕ)) || ((W1 p)) (1 : Fin (9 : ℕ)) && ((W1 p)) (6 : Fin (9 : ℕ)) || ((W1 p)) (2 : Fin (9 : ℕ)) && ((W1 p)) (7 : Fin (9 : ℕ)) || ((W1 p)) (3 : Fin (9 : ℕ)) && ((W1 p)) (8 : Fin (9 : ℕ)) || ((W1 p)) (5 : Fin (9 : ℕ)) && ((W1 p)) (7 : Fin (9 : ℕ)) || ((W1 p)) (6 : Fin (9 : ℕ)) && ((W1 p)) (8 : Fin (9 : ℕ)) || ((W1 p)) (8 : Fin (9 : ℕ)) && ((W1 p)) (5 : Fin (9 : ℕ)))) := by
  simp only [List.map_cons, List.map_nil]
  rw [siteEq x1 (W1 p) p]
  have hb : p ∈ Finset.Iio (10 : Fin (24 : ℕ)) := by rw [Finset.mem_Iio]; omega
  clear hp
  fin_cases hb <;> exact of_decide_eq_true (Eq.refl true)

private theorem refute_pair (x1 : List Gate) (p q : Fin 24)
    (hp : (p : ℕ) < 10) (hq : (q : ℕ) < 10) :
    GateOp.and.eval (List.map (fun (x9 : Fin (24 : ℕ)) =>
            ({ gates := x1, output := (0 : ℕ) : Circuit }.wires
              (List.ofFn (W2 p q) ++ [(W2 p q) (4 : Fin 9) && (W2 p q) (6 : Fin 9)])).getD (↑x9) Bool.false)
            [p, q]) ≠ ((((W2 p q)) (0 : Fin (9 : ℕ)) && ((W2 p q)) (1 : Fin (9 : ℕ)) || ((W2 p q)) (1 : Fin (9 : ℕ)) && ((W2 p q)) (2 : Fin (9 : ℕ)) || ((W2 p q)) (2 : Fin (9 : ℕ)) && ((W2 p q)) (3 : Fin (9 : ℕ)) || ((W2 p q)) (3 : Fin (9 : ℕ)) && ((W2 p q)) (4 : Fin (9 : ℕ)) || ((W2 p q)) (4 : Fin (9 : ℕ)) && ((W2 p q)) (0 : Fin (9 : ℕ)) || ((W2 p q)) (0 : Fin (9 : ℕ)) && ((W2 p q)) (5 : Fin (9 : ℕ)) || ((W2 p q)) (1 : Fin (9 : ℕ)) && ((W2 p q)) (6 : Fin (9 : ℕ)) || ((W2 p q)) (2 : Fin (9 : ℕ)) && ((W2 p q)) (7 : Fin (9 : ℕ)) || ((W2 p q)) (3 : Fin (9 : ℕ)) && ((W2 p q)) (8 : Fin (9 : ℕ)) || ((W2 p q)) (5 : Fin (9 : ℕ)) && ((W2 p q)) (7 : Fin (9 : ℕ)) || ((W2 p q)) (6 : Fin (9 : ℕ)) && ((W2 p q)) (8 : Fin (9 : ℕ)) || ((W2 p q)) (8 : Fin (9 : ℕ)) && ((W2 p q)) (5 : Fin (9 : ℕ)))) := by
  simp only [List.map_cons, List.map_nil]
  rw [siteEq x1 (W2 p q) p, siteEq x1 (W2 p q) q]
  have hb : p ∈ Finset.Iio (10 : Fin (24 : ℕ)) := by rw [Finset.mem_Iio]; omega
  have hc : q ∈ Finset.Iio (10 : Fin (24 : ℕ)) := by rw [Finset.mem_Iio]; omega
  clear hp hq
  fin_cases hb <;> fin_cases hc <;> exact of_decide_eq_true (Eq.refl true)

end PEqualNP.Outside.R_meta_1912_1_aux

open PEqualNP.Outside.R_meta_1912_1_aux

theorem PEqualNP.Outside.R_meta_1912_1 :
    (∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))), (∃ u ∈ x2, (10 : ℕ) ≤ ↑u) → x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) →
    (∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))), (10 : ℕ) ≤ (x2.getD (0 : ℕ) (0 : Fin (24 : ℕ))).val → x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) →
    (∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))), (10 : ℕ) ≤ (x2.getD (1 : ℕ) (0 : Fin (24 : ℕ))).val → x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) →
    (∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List (Fin (24 : ℕ))),   x1.length ≤ (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ x5 ∈ x1, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) →         x2.length ≤ (2 : ℕ) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (4 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ))]);             PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x9 : Fin (24 : ℕ)) => x8.getD (↑x9) Bool.false) x2) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)))) := by
  intro hAny hHead hTail x1 x2 hLen hFan hBound hLen2
  rcases x2 with (_ | ⟨p, pt⟩)
  · exact ⟨fun _ => false, refute_nil x1⟩
  · rcases pt with (_ | ⟨q, qt⟩)
    · by_cases hp10 : (10 : ℕ) ≤ p.val
      · refine hHead x1 [p] ?_ hLen hFan hBound ?_
        · simpa using hp10
        · simp
      · have hp : (p : ℕ) < 10 := by omega
        exact ⟨W1 p, refute_single x1 p hp⟩
    · rcases qt with (_ | ⟨r, _ | ⟨s, t⟩⟩)
      · by_cases hp10 : (10 : ℕ) ≤ p.val
        · refine hHead x1 [p, q] ?_ hLen hFan hBound ?_
          · simpa using hp10
          · simp
        · by_cases hq10 : (10 : ℕ) ≤ q.val
          · refine hTail x1 [p, q] ?_ hLen hFan hBound ?_
            · simpa using hq10
            · simp
          · have hp : (p : ℕ) < 10 := by omega
            have hq : (q : ℕ) < 10 := by omega
            exact ⟨W2 p q, refute_pair x1 p q hp hq⟩
      · exact absurd hLen2 (by simp only [List.length_cons, List.length_nil]; omega)
      · exact absurd hLen2 (by simp only [List.length_cons, List.length_nil]; omega)
