import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Cut through the theta graph left when x0 and x4 are set to false.
-- normalForm: a correct circuit never reads x0 and reads NOT x0 at one AND gate only.
-- transfer: such a circuit restricts to a theta circuit with at most 10 gates, or with at
-- most 11 gates one of which is a NOT gate.
-- thetaBound and thetaMonotone: the theta edge function needs 11 gates, and 11 gates leave
-- no room for a NOT gate.
theorem PEqualNP.Outside.R_meta_3178_2
    (normalForm : ∀ b : Fin 9, b ≠ 0 → ∀ C : Circuit, FanInTwo C → C.size ≤ 13 →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 0 || x b]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size ≤ 13 ∧
        (List.countP (fun g : Gate => decide (0 ∈ g.inputs ∨ 9 ∈ g.inputs)) D.gates = 1 ∧
        ∀ g ∈ D.gates, 0 ∈ g.inputs ∨ 9 ∈ g.inputs →
          g.op = GateOp.and ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [9, w] ∨ g.inputs = [w, 9])) ∧
        ∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0, x 0 || x b]) =
          C.eval (List.ofFn x ++ [!x 0, x 0 || x b]))
    (transfer : ∀ b : Fin 9, b ≠ 0 → ∀ D : Circuit, FanInTwo D → D.size ≤ 13 →
      (List.countP (fun g : Gate => decide (0 ∈ g.inputs ∨ 9 ∈ g.inputs)) D.gates = 1 ∧
        ∀ g ∈ D.gates, 0 ∈ g.inputs ∨ 9 ∈ g.inputs →
          g.op = GateOp.and ∧ ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧ (g.inputs = [9, w] ∨ g.inputs = [w, 9])) →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x ++ [!x 0, x 0 || x b]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
          x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
          x 6 && x 8 || x 8 && x 5)) →
      ∃ E : Circuit, FanInTwo E ∧
        (∀ y : Fin 7 → Bool, E.eval (List.ofFn y) =
          (y 0 && y 2 || y 2 && y 1 || y 0 && y 3 || y 3 && y 4 || y 4 && y 1 || y 0 && y 5 || y 5 && y 6 || y 6 && y 1)) ∧
        (E.size ≤ 10 ∨ E.size ≤ 11 ∧ ∃ g ∈ E.gates, g.op = GateOp.not))
    (thetaBound : ¬ HasCircuitSize 7 (fun y : Fin 7 → Bool =>
      (y 0 && y 2 || y 2 && y 1 || y 0 && y 3 || y 3 && y 4 || y 4 && y 1 || y 0 && y 5 || y 5 && y 6 || y 6 && y 1)) 10)
    (thetaMonotone : ∀ E : Circuit, FanInTwo E → E.size ≤ 11 →
      (∀ y : Fin 7 → Bool, E.eval (List.ofFn y) =
        (y 0 && y 2 || y 2 && y 1 || y 0 && y 3 || y 3 && y 4 || y 4 && y 1 || y 0 && y 5 || y 5 && y 6 || y 6 && y 1)) →
      ∀ g ∈ E.gates, g.op ≠ GateOp.not) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         (¬∀ x5 ∈ x1, x5 = (0 : ℕ) ∨ x5 = (9 : ℕ)) ∧ (0 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen hlt _ hspec C hfan hsize
  let F (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  have hget : ∀ (x : Fin 9 → Bool) (k : Fin 9),
      (List.ofFn x ++ [!x 0]).getD k.val false = x k := by
    intro x k
    fin_cases k <;> rfl
  have hget0 : ∀ (x : Fin 9 → Bool), (List.ofFn x ++ [!x 0]).getD 0 false = x 0 := fun _ => rfl
  have hex : ∃ b : Fin 9, b ≠ 0 ∧ ∀ x : Fin 9 → Bool,
      GateOp.or.eval (x1.map fun i => (List.ofFn x ++ [!x 0]).getD i false) = (x 0 || x b) := by
    obtain ⟨hnotall, h0mem⟩ := hspec
    cases x1 with
    | nil => cases hlen
    | cons u rest =>
      cases rest with
      | nil => cases hlen
      | cons w rest2 =>
        cases rest2 with
        | cons _ _ => cases hlen
        | nil =>
          by_cases hu : u = 0
          · subst hu
            have hw0 : w ≠ 0 := fun hw => hnotall (by subst hw; simp)
            have hw9 : w ≠ 9 := fun hw => hnotall (by subst hw; simp)
            have hw10 : w < 10 := hlt w (by simp)
            have hwlt : w < 9 := by omega
            refine ⟨⟨w, hwlt⟩, fun h => hw0 (congrArg Fin.val h), fun x => ?_⟩
            change ((List.ofFn x ++ [!x 0]).getD 0 false ||
              ((List.ofFn x ++ [!x 0]).getD w false || false)) = (x 0 || x ⟨w, hwlt⟩)
            rw [Bool.or_false, hget0 x, hget x ⟨w, hwlt⟩]
          · have hw : w = 0 := by simp at h0mem; omega
            subst hw
            have hu9 : u ≠ 9 := fun hu9' => hnotall (by subst hu9'; simp)
            have hu10 : u < 10 := hlt u (by simp)
            have hult : u < 9 := by omega
            refine ⟨⟨u, hult⟩, fun h => hu (congrArg Fin.val h), fun x => ?_⟩
            change ((List.ofFn x ++ [!x 0]).getD u false ||
              ((List.ofFn x ++ [!x 0]).getD 0 false || false)) = (x 0 || x ⟨u, hult⟩)
            rw [Bool.or_false, hget x ⟨u, hult⟩, hget0 x, Bool.or_comm]
  obtain ⟨b, hb0, hpair⟩ := hex
  change ∃ x, C.eval ((List.ofFn x ++ [!x 0]) ++
    [GateOp.or.eval (x1.map fun i => (List.ofFn x ++ [!x 0]).getD i false)]) ≠ F x
  simp_rw [hpair, List.append_assoc, List.cons_append, List.nil_append]
  by_contra hno
  have hall : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0, x 0 || x b]) = F x := by
    intro x
    by_contra hx
    exact hno ⟨x, hx⟩
  obtain ⟨D, hD, hDs, hDn, hDe⟩ := normalForm b hb0 C hfan hsize hall
  obtain ⟨E, hE, hEv, hEs⟩ := transfer b hb0 D hD hDs hDn (fun x => (hDe x).trans (hall x))
  rcases hEs with small | ⟨small, g, hg, hnot⟩
  · exact thetaBound ⟨E, hE, small, hEv⟩
  · exact thetaMonotone E hE small hEv g hg hnot
