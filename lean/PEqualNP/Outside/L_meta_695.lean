import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_695

open PEqualNP.CircuitLowerBounds

def ones (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)

def Priv (n : ℕ) (S : Finset (Fin n)) (C : Circuit) (j : ℕ) : Prop :=
  ones n C (n + j) ⊆ S ∧ 2 ≤ (ones n C (n + j)).card

def Step (n : ℕ) (S : Finset (Fin n)) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ (∃ g : Gate, C.gates[b]? = some g ∧ n + a ∈ g.inputs) ∧ Priv n S C b

noncomputable def Qset (n r : ℕ) (S : Finset (Fin n)) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter (fun j => Priv n S C j ∧ Relation.ReflTransGen (Step n S C) j r)

theorem mem_Q {n r : ℕ} {S : Finset (Fin n)} {C : Circuit} {j : ℕ} :
    j ∈ Qset n r S C ↔ j < C.size ∧ Priv n S C j ∧ Relation.ReflTransGen (Step n S C) j r := by
  classical
  unfold Qset
  rw [Finset.mem_filter, Finset.mem_range]

noncomputable def psi (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (Q : Finset ℕ) (w : ℕ) : Bool :=
  if n ≤ w ∧ w - n ∈ Q then
    match C.gates[w - n]? with
    | some g => g.op.eval (g.inputs.map (fun u => if _h : u < w then psi n C S Q u else false))
    | none => false
  else decide ¬ (ones n C w ⊆ S)
termination_by w

theorem psi_gate (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (Q : Finset ℕ) (j : ℕ) (hj : j ∈ Q)
    (g : Gate) (hg : C.gates[j]? = some g) :
    psi n C S Q (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then psi n C S Q w else false)) := by
  rw [psi]
  have hc : n ≤ n + j ∧ n + j - n ∈ Q := ⟨Nat.le_add_right n j, by rw [Nat.add_sub_cancel_left]; exact hj⟩
  rw [if_pos hc]
  simp only [Nat.add_sub_cancel_left, hg, dite_eq_ite]

theorem psi_other (n : ℕ) (C : Circuit) (S : Finset (Fin n)) (Q : Finset ℕ) (w : ℕ)
    (hw : ∀ j ∈ Q, w ≠ n + j) : (psi n C S Q w = true ↔ ¬ ones n C w ⊆ S) := by
  rw [psi]
  have hc : ¬ (n ≤ w ∧ w - n ∈ Q) := by
    rintro ⟨h1, h2⟩
    exact hw (w - n) h2 (by omega)
  rw [if_neg hc]
  simp

end PEqualNP.Outside.L_meta_695

open PEqualNP.Outside.L_meta_695 in
theorem PEqualNP.Outside.L_meta_695 : ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → r < C.size → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)).card → ∃ (Q : Finset ℕ) (ψ : ℕ → Bool), r ∈ Q ∧ (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) ∧ (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) ∧ (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) ∧ (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧ (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → (ψ w = true ↔ ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S)) := by
  intro n r S C _ hr hsub hcard
  refine ⟨Qset n r S C, psi n C S (Qset n r S C), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact mem_Q.mpr ⟨hr, ⟨hsub, hcard⟩, Relation.ReflTransGen.refl⟩
  · intro j hj
    obtain ⟨h1, ⟨h2, h3⟩, -⟩ := mem_Q.mp hj
    exact ⟨h1, h2, h3⟩
  · intro j hj hne
    obtain ⟨-, -, hreach⟩ := mem_Q.mp hj
    rcases hreach.cases_head with h | ⟨c, ⟨hjc, ⟨g, hg, hin⟩, hpc⟩, hcr⟩
    · exact absurd h hne
    · refine ⟨c, mem_Q.mpr ⟨?_, hpc, hcr⟩, hjc, g, hg, hin⟩
      exact (List.getElem?_eq_some_iff.mp hg).1
  · intro j hj j' hj' hread hs hc
    obtain ⟨hjs, hpj, hreach⟩ := mem_Q.mp hj
    exact mem_Q.mpr ⟨by omega, ⟨hs, hc⟩, Relation.ReflTransGen.head ⟨hj', hread, hpj⟩ hreach⟩
  · intro j hj g hg
    exact psi_gate n C S _ j hj g hg
  · intro w hw
    exact psi_other n C S _ w hw
