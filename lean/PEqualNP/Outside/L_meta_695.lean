import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_695

open PEqualNP.CircuitLowerBounds

def psi (n : ℕ) (gates : List Gate) (Q : Finset ℕ) (base : ℕ → Bool) (w : ℕ) : Bool :=
  if n ≤ w ∧ w - n ∈ Q then
    match gates[w - n]? with
    | some g => g.op.eval (g.inputs.map (fun v => if _h : v < w then psi n gates Q base v else false))
    | none => base w
  else base w
termination_by w

theorem psi_gate (n : ℕ) (gates : List Gate) (Q : Finset ℕ) (base : ℕ → Bool) (j : ℕ) (hj : j ∈ Q)
    (g : Gate) (hg : gates[j]? = some g) :
    psi n gates Q base (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then psi n gates Q base w else false)) := by
  rw [psi]
  have h1 : n ≤ n + j ∧ n + j - n ∈ Q := ⟨by omega, by simpa using hj⟩
  rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  have h2 : n + j - n = j := by omega
  simp only [h2, hg, dite_eq_ite]

theorem psi_base (n : ℕ) (gates : List Gate) (Q : Finset ℕ) (base : ℕ → Bool) (w : ℕ)
    (hw : ∀ j ∈ Q, w ≠ n + j) : psi n gates Q base w = base w := by
  rw [psi]
  have h1 : ¬ (n ≤ w ∧ w - n ∈ Q) := by
    rintro ⟨h1, h2⟩
    exact hw (w - n) h2 (by omega)
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]

theorem core (n r : ℕ) (gates : List Gate) (priv : ℕ → Prop) (base : ℕ → Bool)
    (hr : r < gates.length) (hpr : priv r) :
    ∃ (Q : Finset ℕ) (ψ : ℕ → Bool), r ∈ Q ∧ (∀ j ∈ Q, j < gates.length ∧ priv j) ∧
      (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : Gate, gates[j']? = some g ∧ n + j ∈ g.inputs) ∧
      (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : Gate, gates[j]? = some g ∧ n + j' ∈ g.inputs) → priv j' → j' ∈ Q) ∧
      (∀ j ∈ Q, ∀ g : Gate, gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧
      (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → ψ w = base w) := by
  classical
  let E : ℕ → ℕ → Prop := fun a b => b < a ∧ (∃ g : Gate, gates[a]? = some g ∧ n + b ∈ g.inputs) ∧ priv b
  let Q : Finset ℕ := (Finset.range gates.length).filter (fun j => Relation.ReflTransGen E r j)
  have memQ : ∀ j, j ∈ Q ↔ j < gates.length ∧ Relation.ReflTransGen E r j := by
    intro j
    simp [Q]
  refine ⟨Q, psi n gates Q base, (memQ r).2 ⟨hr, Relation.ReflTransGen.refl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨hlt, hrj⟩ := (memQ j).1 hj
    refine ⟨hlt, ?_⟩
    rcases Relation.ReflTransGen.cases_tail hrj with h | ⟨c, _, hc⟩
    · rw [h]
      exact hpr
    · exact hc.2.2
  · intro j hj hne
    obtain ⟨_, hrj⟩ := (memQ j).1 hj
    rcases Relation.ReflTransGen.cases_tail hrj with h | ⟨c, hrc, hc⟩
    · exact absurd h hne
    · obtain ⟨hlt, ⟨g, hg, hin⟩, _⟩ := hc
      have hcl : c < gates.length := (List.getElem?_eq_some_iff.mp hg).1
      exact ⟨c, (memQ c).2 ⟨hcl, hrc⟩, hlt, g, hg, hin⟩
  · intro j hj j' hlt hread hpriv
    obtain ⟨hjl, hrj⟩ := (memQ j).1 hj
    exact (memQ j').2 ⟨by omega, Relation.ReflTransGen.tail hrj ⟨hlt, hread, hpriv⟩⟩
  · intro j hj g hg
    exact psi_gate n gates Q base j hj g hg
  · intro w hw
    exact psi_base n gates Q base w hw

end PEqualNP.Outside.L_meta_695

theorem PEqualNP.Outside.L_meta_695 : ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → r < C.size → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)).card → ∃ (Q : Finset ℕ) (ψ : ℕ → Bool), r ∈ Q ∧ (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) ∧ (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) ∧ (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) → (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S → 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) ∧ (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧ (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → (ψ w = true ↔ ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S)) := by
  intro n r S C _ hr hS h2
  obtain ⟨Q, ψ, hrQ, hQ, hpar, hcl, hev, hbase⟩ := PEqualNP.Outside.L_meta_695.core n r C.gates
    (fun j => (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card)
    (fun w => decide (¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S))
    hr ⟨hS, h2⟩
  refine ⟨Q, ψ, hrQ, ?_, hpar, ?_, hev, ?_⟩
  · intro j hj
    obtain ⟨h1, h3, h4⟩ := hQ j hj
    exact ⟨h1, h3, h4⟩
  · intro j hj j' hlt hread hs hc
    exact hcl j hj j' hlt hread ⟨hs, hc⟩
  · intro w hw
    rw [hbase w hw]
    exact decide_eq_true_iff
