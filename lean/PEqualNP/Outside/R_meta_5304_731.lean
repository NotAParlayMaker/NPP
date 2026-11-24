import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 700000 in
theorem PEqualNP.Outside.R_meta_5304_731
    (propagate : ∀ (C : Circuit) (x y : List Bool) (i : ℕ),
      x.length = y.length → (∀ j : ℕ, j ≠ i → x.getD j false = y.getD j false) →
      C.output ≠ i → C.eval x ≠ C.eval y →
      ∃ (p t : List Gate) (g : Gate), C.gates = p ++ g :: t ∧ i ∈ g.inputs ∧
        (C.wires x).getD (x.length + p.length) false ≠
          (C.wires y).getD (x.length + p.length) false)
    (remaining : ∀ (x1 x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → x1.length + x2.length + x3.length = (12 : ℕ) → x6 < (24 : ℕ) → (∀ x11 ∈ x7.gates, (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not → x11.inputs.length ≤ (1 : ℕ)) ∧ ∀ x13 ∈ x11.inputs, x13 ≤ (24 : ℕ)) → (∀ x12 ∈ x1 ++ x2 ++ x3, (0 : ℕ) ∉ x12.inputs ∧ (9 : ℕ) ∉ x12.inputs) → (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.inputs.contains (4 : ℕ)) (x1 ++ x2 ++ x3)).length = (1 : ℕ) → (∀ x14 ∈ [x4, x5], (0 : ℕ) ∈ x14.inputs ∨ (9 : ℕ) ∈ x14.inputs) → (15 : ℕ) ≤ (List.foldl (fun (x15 : List ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate) => x15 ++ [(1 : ℕ) + (List.map (fun (x17 : ℕ) => x15.getD x17 (0 : ℕ)) x16.inputs).sum]) (List.replicate (10 : ℕ) (0 : ℕ)) x7.gates).getD x7.output (0 : ℕ) → (∀ (x16 : Fin (9 : ℕ) → Bool), x7.eval (List.ofFn x16 ++ [!x16 (0 : Fin (9 : ℕ))]) = [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x17 : ℕ) => x16 (Fin.ofNat (9 : ℕ) (x17 / (9 : ℕ))) && x16 (Fin.ofNat (9 : ℕ) (x17 % (9 : ℕ)))) →
  (∀ b : Bool, ∃ j : Fin x7.gates.length, 4 ∈ (x7.gates.get j).inputs ∧
     Function.Injective (fun v : Bool =>
       (x7.wires [b,false,false,!b,v,false,false,false,false,!b]).getD (10+j.val) false)) → False) :
    ∀ (x1 x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ x4 :: (x2 ++ x5 :: x3), output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → x1.length + x2.length + x3.length = (12 : ℕ) → x6 < (24 : ℕ) → (∀ x11 ∈ x7.gates, (x11.op = PEqualNP.CircuitLowerBounds.GateOp.not → x11.inputs.length ≤ (1 : ℕ)) ∧ ∀ x13 ∈ x11.inputs, x13 ≤ (24 : ℕ)) → (∀ x12 ∈ x1 ++ x2 ++ x3, (0 : ℕ) ∉ x12.inputs ∧ (9 : ℕ) ∉ x12.inputs) → (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.inputs.contains (4 : ℕ)) (x1 ++ x2 ++ x3)).length = (1 : ℕ) → (∀ x14 ∈ [x4, x5], (0 : ℕ) ∈ x14.inputs ∨ (9 : ℕ) ∈ x14.inputs) → (15 : ℕ) ≤ (List.foldl (fun (x15 : List ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate) => x15 ++ [(1 : ℕ) + (List.map (fun (x17 : ℕ) => x15.getD x17 (0 : ℕ)) x16.inputs).sum]) (List.replicate (10 : ℕ) (0 : ℕ)) x7.gates).getD x7.output (0 : ℕ) → (∀ (x16 : Fin (9 : ℕ) → Bool), x7.eval (List.ofFn x16 ++ [!x16 (0 : Fin (9 : ℕ))]) = [(1 : ℕ), (11 : ℕ), (21 : ℕ), (31 : ℕ), (36 : ℕ), (5 : ℕ), (15 : ℕ), (25 : ℕ), (35 : ℕ), (52 : ℕ), (62 : ℕ), (77 : ℕ)].any fun (x17 : ℕ) => x16 (Fin.ofNat (9 : ℕ) (x17 / (9 : ℕ))) && x16 (Fin.ofNat (9 : ℕ) (x17 % (9 : ℕ)))) → False := by
  intro a b c g h o
  dsimp only
  intro fan count bound shape ordinary single control unfolded computes
  let C : Circuit := ⟨a ++ g :: (b ++ h :: c), o⟩
  change ∀ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) =
    ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 (e % 9))) at computes
  apply remaining a b c g h o fan count bound shape ordinary single control unfolded computes
  have keepInput (gs : List Gate) (w : List Bool) (before : 4 < w.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD 4 false =
      w.getD 4 false := by
    induction gs generalizing w with
    | nil => rfl
    | cons first rest ih =>
      simp only [List.foldl_cons]
      rw [ih _ (by simp; omega)]
      exact List.getD_append _ _ _ _ before
  have output : C.output ≠ 4 := by
    intro out
    let only : Fin 9 → Bool := ![false,false,false,false,true,false,false,false,false]
    have label : ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
        (fun e => only (Fin.ofNat 9 (e / 9)) && only (Fin.ofNat 9 (e % 9))) = false := by decide
    have hf := (computes only).trans label
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn only ++ [!only 0])).getD C.output false = false at hf
    rw [out, keepInput _ _ (by simp)] at hf
    have ht : (List.ofFn only ++ [!only 0]).getD 4 false = true := by decide
    rw [ht] at hf
    contradiction
  intro q
  let w (v : Bool) := [q,false,false,!q,v,false,false,false,false,!q]
  let x (v : Bool) : Fin 9 → Bool := ![q,false,false,!q,v,false,false,false,false]
  have form (v : Bool) : List.ofFn (x v) ++ [!x v 0] = w v := by
    cases q <;> cases v <;> decide
  have label (v : Bool) : ([1,11,21,31,36,5,15,25,35,52,62,77] : List ℕ).any
      (fun e => x v (Fin.ofNat 9 (e / 9)) && x v (Fin.ofNat 9 (e % 9))) = v := by
    cases q <;> cases v <;> decide
  have evalAt (v : Bool) : C.eval (w v) = v := by
    rw [← form v]
    exact (computes (x v)).trans (label v)
  have same (i : ℕ) (hi : i ≠ 4) : (w false).getD i false = (w true).getD i false := by
    by_cases small : i < 10
    · interval_cases i
      all_goals first | exact (hi rfl).elim | cases q <;> decide
    · have past (v : Bool) : (w v).length ≤ i := Nat.le_of_not_gt small
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (past false), List.getElem?_eq_none (past true)]
  have outputChanges : C.eval (w false) ≠ C.eval (w true) := by
    intro equal
    have impossible : false = true := (evalAt false).symm.trans (equal.trans (evalAt true))
    cases impossible
  obtain ⟨p,t,g',formG,read,diff⟩ := propagate C (w false) (w true) 4
    rfl same output outputChanges
  let j : Fin C.gates.length := ⟨p.length, by rw [formG]; simp⟩
  have found : C.gates[j.val]? = some g' := by
    change C.gates[p.length]? = some g'
    rw [formG, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  rw [getElem?_pos C.gates j.val j.isLt] at found
  have atGate : C.gates.get j = g' := Option.some.inj found
  refine ⟨j, atGate.symm ▸ read, ?_⟩
  intro u v sameValue
  cases u <;> cases v
  · rfl
  · exact (diff sameValue).elim
  · exact (diff sameValue.symm).elim
  · rfl
