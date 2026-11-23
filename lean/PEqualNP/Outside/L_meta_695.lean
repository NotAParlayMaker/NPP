import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_695_aux

open PEqualNP.CircuitLowerBounds

def singleSet (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)

def isPriv (n : ℕ) (S : Finset (Fin n)) (C : Circuit) (j : ℕ) : Prop :=
  j < C.size ∧ singleSet n C (n + j) ⊆ S ∧ 2 ≤ (singleSet n C (n + j)).card

inductive Reach (n r : ℕ) (S : Finset (Fin n)) (C : Circuit) : ℕ → Prop
  | root : Reach n r S C r
  | step {j j' : ℕ} :
      Reach n r S C j →
      j' < j →
      isPriv n S C j' →
      (∃ g : Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) →
      Reach n r S C j'

lemma reach_priv {n r : ℕ} {S : Finset (Fin n)} {C : Circuit}
    (hr : isPriv n S C r) {j : ℕ} (h : Reach n r S C j) : isPriv n S C j := by
  induction h with
  | root => exact hr
  | step _ _ hpriv _ _ => exact hpriv

noncomputable def reachSet (n r : ℕ) (S : Finset (Fin n)) (C : Circuit) : Finset ℕ :=
  @Finset.filter ℕ (fun j => Reach n r S C j) (Classical.decPred _) (Finset.range C.size)

lemma mem_reachSet_iff {n r : ℕ} {S : Finset (Fin n)} {C : Circuit}
    (hr : isPriv n S C r) {j : ℕ} :
    j ∈ reachSet n r S C ↔ Reach n r S C j := by
  simp only [reachSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(reach_priv hr h).1, h⟩

noncomputable def psi (n : ℕ) (S : Finset (Fin n)) (C : Circuit) (Q : Finset ℕ) : ℕ → Bool :=
  WellFounded.fix Nat.lt_wfRel.wf fun w rec =>
    if _hQ : n ≤ w ∧ w - n ∈ Q then
      match C.gates[w - n]? with
      | some g => g.op.eval (g.inputs.map (fun u => if hu : u < w then rec u hu else false))
      | none => false
    else
      decide (¬ singleSet n C w ⊆ S)

lemma psi_eq (n : ℕ) (S : Finset (Fin n)) (C : Circuit) (Q : Finset ℕ) (w : ℕ) :
    psi n S C Q w =
      if n ≤ w ∧ w - n ∈ Q then
        match C.gates[w - n]? with
        | some g => g.op.eval (g.inputs.map (fun u => if u < w then psi n S C Q u else false))
        | none => false
      else
        decide (¬ singleSet n C w ⊆ S) := by
  conv_lhs => rw [psi, WellFounded.fix_eq]
  simp only [psi, dite_eq_ite]

lemma psi_gate {n : ℕ} {S : Finset (Fin n)} {C : Circuit} {Q : Finset ℕ}
    {j : ℕ} (hj : j ∈ Q) {g : Gate} (hg : C.gates[j]? = some g) :
    psi n S C Q (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then psi n S C Q w else false)) := by
  rw [psi_eq]
  simp only [Nat.le_add_right, Nat.add_sub_cancel_left, hj, and_self, ↓reduceIte, hg]

lemma psi_outside {n : ℕ} {S : Finset (Fin n)} {C : Circuit} {Q : Finset ℕ}
    {w : ℕ} (hw : ∀ j ∈ Q, w ≠ n + j) :
    psi n S C Q w = true ↔ ¬ singleSet n C w ⊆ S := by
  rw [psi_eq]
  have hnot : ¬ (n ≤ w ∧ w - n ∈ Q) := by
    rintro ⟨hle, hmem⟩
    exact hw (w - n) hmem (by omega)
  simp only [hnot, ↓reduceIte, decide_eq_true_eq]

theorem main_proof :
    ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      r < C.size →
      (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)) ⊆ S →
      2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)).card →
      ∃ (Q : Finset ℕ) (ψ : ℕ → Bool),
        r ∈ Q ∧
        (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) ∧
        (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) ∧
        (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) ∧
        (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧
        (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → (ψ w = true ↔ ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S)) := by
  intro n r S C _hC hr_lt hr_sub hr_card
  have hr : isPriv n S C r := ⟨hr_lt, hr_sub, hr_card⟩
  refine ⟨reachSet n r S C, psi n S C (reachSet n r S C), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (mem_reachSet_iff hr).mpr Reach.root
  · intro j hj
    exact reach_priv hr ((mem_reachSet_iff hr).mp hj)
  · intro j hj hjne
    have hreach : Reach n r S C j := (mem_reachSet_iff hr).mp hj
    cases hreach with
    | root => exact absurd rfl hjne
    | step hpar hlt _ hgate =>
      exact ⟨_, (mem_reachSet_iff hr).mpr hpar, hlt, hgate⟩
  · intro j hj j' hjlt hgate hj'sub hj'card
    have hreach : Reach n r S C j := (mem_reachSet_iff hr).mp hj
    have hj_lt : j < C.size := (reach_priv hr hreach).1
    have hj'priv : isPriv n S C j' := ⟨lt_trans hjlt hj_lt, hj'sub, hj'card⟩
    exact (mem_reachSet_iff hr).mpr (Reach.step hreach hjlt hj'priv hgate)
  · intro j hj g hg
    exact psi_gate hj hg
  · intro w hw
    exact psi_outside hw

end PEqualNP.Outside.L_meta_695_aux

theorem PEqualNP.Outside.L_meta_695 : ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → r < C.size → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)).card → ∃ (Q : Finset ℕ) (ψ : ℕ → Bool), r ∈ Q ∧ (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) ∧ (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) ∧ (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) ∧ (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧ (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → (ψ w = true ↔ ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S)) :=
  PEqualNP.Outside.L_meta_695_aux.main_proof
