import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_695

open PEqualNP.CircuitLowerBounds Relation

private def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true

private def privateGate {n : ℕ} (S : Finset (Fin n)) (C : Circuit) (j : ℕ) : Prop :=
  j < C.size ∧ support C (n + j) ⊆ S ∧ 2 ≤ (support (n := n) C (n + j)).card

private def reads (n : ℕ) (C : Circuit) (j k : ℕ) : Prop :=
  ∃ g : Gate, C.gates[j]? = some g ∧ n + k ∈ g.inputs

private def step {n : ℕ} (S : Finset (Fin n)) (C : Circuit) (j k : ℕ) : Prop :=
  k < j ∧ reads n C j k ∧ privateGate S C k

private lemma reached_private {n r j : ℕ} {S : Finset (Fin n)} {C : Circuit}
    (hr : privateGate S C r) (hj : ReflTransGen (step S C) r j) : privateGate S C j := by
  cases hj with
  | refl => exact hr
  | tail _ h => exact h.2.2

private noncomputable def label {n : ℕ} (S : Finset (Fin n)) (C : Circuit)
    (Q : Finset ℕ) (w : ℕ) : Bool := by
  classical
  exact if w ∈ Q.image (n + ·) then
    match C.gates[w - n]? with
    | some g =>
      g.op.eval (g.inputs.map (fun u => if hu : u < w then label S C Q u else false))
    | none => false
  else decide (¬ support C w ⊆ S)
termination_by w

private lemma label_at_gate {n : ℕ} (S : Finset (Fin n)) (C : Circuit)
    (Q : Finset ℕ) (j : ℕ) (hj : j ∈ Q) (g : Gate) (hg : C.gates[j]? = some g) :
    label S C Q (n + j) =
      g.op.eval (g.inputs.map (fun u => if u < n + j then label S C Q u else false)) := by
  have hm : n + j ∈ Q.image (n + ·) := Finset.mem_image_of_mem _ hj
  conv_lhs => rw [label]
  simp only [ite_eq_left hm, Nat.add_sub_cancel_left, hg, dite_eq_ite]

private lemma label_off_gates {n : ℕ} (S : Finset (Fin n)) (C : Circuit)
    (Q : Finset ℕ) (w : ℕ) (hw : ∀ j ∈ Q, w ≠ n + j) :
    label S C Q w = true ↔ ¬ support C w ⊆ S := by
  have hm : w ∉ Q.image (n + ·) := by
    intro h
    obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp h
    exact hw j hj eq.symm
  conv_lhs => rw [label]
  simp only [ite_eq_right hm, decide_eq_true_eq]

theorem construction {n r : ℕ} (S : Finset (Fin n)) (C : Circuit)
    (hr : privateGate S C r) :
    ∃ Q : Finset ℕ, ∃ ψ : ℕ → Bool,
      r ∈ Q ∧
      (∀ j ∈ Q, privateGate S C j) ∧
      (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ reads n C j' j) ∧
      (∀ j ∈ Q, ∀ j' : ℕ, j' < j → reads n C j j' →
        support C (n + j') ⊆ S → 2 ≤ (support (n := n) C (n + j')).card → j' ∈ Q) ∧
      (∀ j ∈ Q, ∀ g : Gate, C.gates[j]? = some g →
        ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧
      (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → (ψ w = true ↔ ¬ support C w ⊆ S)) := by
  classical
  let Q := (Finset.range C.size).filter (fun j => ReflTransGen (step S C) r j)
  have membership (j : ℕ) : j ∈ Q ↔ ReflTransGen (step S C) r j := by
    dsimp only [Q]
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun hp => ⟨(reached_private hr hp).1, hp⟩⟩
  refine ⟨Q,label S C Q,(membership r).mpr .refl,?_,?_,?_,?_,?_⟩
  · intro j hj
    exact reached_private hr ((membership j).mp hj)
  · intro j hj hne
    rcases ReflTransGen.cases_tail ((membership j).mp hj) with eq | ⟨j',hpath,hstep⟩
    · exact (hne eq).elim
    · exact ⟨j',(membership j').mpr hpath,hstep.1,hstep.2.1⟩
  · intro j hj j' hlt hread hs hc
    have path := (membership j).mp hj
    have loc : privateGate S C j' := ⟨hlt.trans (reached_private hr path).1,hs,hc⟩
    exact (membership j').mpr (path.tail ⟨hlt,hread,loc⟩)
  · exact label_at_gate S C Q
  · exact label_off_gates S C Q

end PEqualNP.Outside.L_meta_695

theorem PEqualNP.Outside.L_meta_695 :
    ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      r < C.size →
      (Finset.univ.filter (fun p : Fin n =>
        (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)) ⊆ S →
      2 ≤ (Finset.univ.filter (fun p : Fin n =>
        (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)).card →
      ∃ (Q : Finset ℕ) (ψ : ℕ → Bool), r ∈ Q ∧
        (∀ j ∈ Q, j < C.size ∧
          (Finset.univ.filter (fun p : Fin n =>
            (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧
          2 ≤ (Finset.univ.filter (fun p : Fin n =>
            (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) ∧
        (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧
          ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) ∧
        (∀ j ∈ Q, ∀ j' : ℕ, j' < j →
          (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) →
          (Finset.univ.filter (fun p : Fin n =>
            (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S →
          2 ≤ (Finset.univ.filter (fun p : Fin n =>
            (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card →
          j' ∈ Q) ∧
        (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g →
          ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧
        (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) →
          (ψ w = true ↔ ¬ (Finset.univ.filter (fun p : Fin n =>
            (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S)) := by
  intro n r S C _ hr hs hc
  exact PEqualNP.Outside.L_meta_695.construction S C ⟨hr,hs,hc⟩
