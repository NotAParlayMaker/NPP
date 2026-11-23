import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_695

open PEqualNP.CircuitLowerBounds

def support (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)

def label (n : ℕ) (C : Circuit) (Q : Finset ℕ) (S : Finset (Fin n)) (w : ℕ) : Bool :=
  if n ≤ w ∧ w - n ∈ Q then
    let g := C.gates.getD (w - n) ⟨GateOp.and, []⟩
    g.op.eval (g.inputs.map (fun v => if _hv : v < w then label n C Q S v else false))
  else decide (¬ support n C w ⊆ S)
termination_by w

theorem label_gate (n : ℕ) (C : Circuit) (Q : Finset ℕ) (S : Finset (Fin n))
    (j : ℕ) (hj : j ∈ Q) (g : Gate) (hg : C.gates[j]? = some g) :
    label n C Q S (n + j) =
      g.op.eval (g.inputs.map (fun w => if w < n + j then label n C Q S w else false)) := by
  rw [label]
  simp only [Nat.le_add_right, Nat.add_sub_cancel_left, hj, and_self, ite_true]
  have hget : C.gates.getD j ⟨GateOp.and, []⟩ = g := by
    simp [List.getD, hg]
  rw [hget]
  simp only [dite_eq_ite]

theorem label_exit (n : ℕ) (C : Circuit) (Q : Finset ℕ) (S : Finset (Fin n))
    (w : ℕ) (hw : ∀ j ∈ Q, w ≠ n + j) :
    label n C Q S w = true ↔ ¬ support n C w ⊆ S := by
  rw [label]
  have hn : ¬ (n ≤ w ∧ w - n ∈ Q) := by
    rintro ⟨hn, hq⟩
    exact hw (w - n) hq (by omega)
  simp [hn]

end PEqualNP.Outside.L_meta_695

theorem PEqualNP.Outside.L_meta_695 : ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → r < C.size → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)).card → ∃ (Q : Finset ℕ) (ψ : ℕ → Bool), r ∈ Q ∧ (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) ∧ (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) ∧ (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) ∧ (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧ (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → (ψ w = true ↔ ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S)) := by
  classical
  intro n r S C _hmono hr hsub hcard
  let P : ℕ → Prop := fun j => j < C.size ∧
    PEqualNP.Outside.L_meta_695.support n C (n + j) ⊆ S ∧
    2 ≤ (PEqualNP.Outside.L_meta_695.support n C (n + j)).card
  let E : ℕ → ℕ → Prop := fun a b => b < a ∧ P b ∧
    ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[a]? = some g ∧ n + b ∈ g.inputs
  have hPr : P r := ⟨hr, hsub, hcard⟩
  have hp : ∀ j, Relation.ReflTransGen E r j → P j := by
    intro j h
    induction h with
    | refl => exact hPr
    | tail h e ih => exact e.2.1
  let Q := (Finset.range C.size).filter (fun j => Relation.ReflTransGen E r j)
  have memQ : ∀ j, j ∈ Q ↔ Relation.ReflTransGen E r j := by
    intro j
    simp only [Q, Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨(hp j h).1, h⟩⟩
  refine ⟨Q, PEqualNP.Outside.L_meta_695.label n C Q S,
    (memQ r).mpr Relation.ReflTransGen.refl, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact hp j ((memQ j).mp hj)
  · intro j hj hne
    rcases ((memQ j).mp hj).cases_tail with heq | ⟨a, ha, he⟩
    · exact (hne heq).elim
    · exact ⟨a, (memQ a).mpr ha, he.1, he.2.2⟩
  · intro j hj b hbj hwire hsubb hcardb
    apply (memQ b).mpr
    apply Relation.ReflTransGen.tail ((memQ j).mp hj)
    exact ⟨hbj, ⟨lt_trans hbj (hp j ((memQ j).mp hj)).1, hsubb, hcardb⟩, hwire⟩
  · intro j hj g hg
    exact PEqualNP.Outside.L_meta_695.label_gate n C Q S j hj g hg
  · intro w hw
    exact PEqualNP.Outside.L_meta_695.label_exit n C Q S w hw
