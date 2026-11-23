import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_695_aux

theorem chooseClosure (P : ℕ → Prop) (R : ℕ → ℕ → Prop) (r bound : ℕ)
    (hr : P r) (hbound : ∀ j, P j → j < bound) :
    ∃ Q : Finset ℕ, r ∈ Q ∧ (∀ j ∈ Q, P j) ∧
      (∀ j ∈ Q, j ≠ r → ∃ t ∈ Q, j < t ∧ R j t) ∧
      (∀ j ∈ Q, ∀ i, i < j → R i j → P i → i ∈ Q) := by
  classical
  let step (j i : ℕ) : Prop := i < j ∧ R i j ∧ P i
  let reached := Relation.ReflTransGen step r
  have hprivate {j : ℕ} (hj : reached j) : P j := by
    obtain heq | ⟨t, _, hstep⟩ := hj.cases_tail
    · exact heq ▸ hr
    · exact hstep.2.2
  let Q := (Finset.range bound).filter reached
  have hmem (j : ℕ) : j ∈ Q ↔ reached j := by
    change j ∈ (Finset.range bound).filter reached ↔ _
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun hj => ⟨hbound j (hprivate hj), hj⟩⟩
  refine ⟨Q, (hmem r).mpr .refl, fun j hj => hprivate ((hmem j).mp hj), ?_, ?_⟩
  · intro j hj hne
    obtain heq | ⟨t, ht, hstep⟩ := ((hmem j).mp hj).cases_tail
    · exact (hne heq).elim
    · exact ⟨t, (hmem t).mpr ht, hstep.1, hstep.2.1⟩
  · intro j hj i hij hR hp
    exact (hmem i).mpr (((hmem j).mp hj).tail ⟨hij, hR, hp⟩)

end PEqualNP.Outside.L_meta_695_aux

namespace PEqualNP.Outside.L_meta_695_aux

open PEqualNP.CircuitLowerBounds

def label (n : ℕ) (C : Circuit) (Q : Finset ℕ) (outside : ℕ → Bool) (w : ℕ) : Bool :=
  if n ≤ w ∧ w - n ∈ Q then
    match C.gates[w - n]? with
    | some g => g.op.eval (g.inputs.map fun k => if h : k < w then label n C Q outside k else false)
    | none => false
  else outside w
termination_by w

theorem label_at_gate {n j : ℕ} {C : Circuit} {Q : Finset ℕ} {outside : ℕ → Bool}
    (hj : j ∈ Q) (g : Gate) (hg : C.gates[j]? = some g) :
    label n C Q outside (n+j) =
      g.op.eval (g.inputs.map (fun k => if k < n+j then label n C Q outside k else false)) := by
  rw [label]
  simp [hj, hg]

theorem label_outside {n w : ℕ} {C : Circuit} {Q : Finset ℕ} {outside : ℕ → Bool}
    (hw : ∀ j ∈ Q, w ≠ n+j) : label n C Q outside w = outside w := by
  have h : ¬ (n ≤ w ∧ w - n ∈ Q) := by
    rintro ⟨hn, hj⟩
    exact hw (w-n) hj (by omega)
  rw [label]
  simp [h]

end PEqualNP.Outside.L_meta_695_aux

open PEqualNP.Outside.L_meta_695_aux in
theorem PEqualNP.Outside.L_meta_695 :
    ∀ (n r : ℕ) (S : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
    r < C.size →
    (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)) ⊆ S →
    2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + r) false = true)).card →
    ∃ (Q : Finset ℕ) (ψ : ℕ → Bool), r ∈ Q ∧
      (∀ j ∈ Q, j < C.size ∧ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)) ⊆ S ∧ 2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j) false = true)).card) ∧
      (∀ j ∈ Q, j ≠ r → ∃ j' ∈ Q, j < j' ∧ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j']? = some g ∧ n + j ∈ g.inputs) ∧
      (∀ j ∈ Q, ∀ j' : ℕ, j' < j → (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ n + j' ∈ g.inputs) →
    (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)) ⊆ S →
    2 ≤ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (n + j') false = true)).card → j' ∈ Q) ∧
      (∀ j ∈ Q, ∀ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g → ψ (n + j) = g.op.eval (g.inputs.map (fun w => if w < n + j then ψ w else false))) ∧
      (∀ w : ℕ, (∀ j ∈ Q, w ≠ n + j) → (ψ w = true ↔ ¬ (Finset.univ.filter (fun p : Fin n => (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (w) false = true)) ⊆ S)) := by
  classical
  intro n r S C _ hr hsub hcard
  let supp (w : ℕ) := Finset.univ.filter (fun p : Fin n =>
    (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD w false = true)
  let P (j : ℕ) := j < C.size ∧ supp (n+j) ⊆ S ∧ 2 ≤ (supp (n+j)).card
  let R (i j : ℕ) := ∃ g : PEqualNP.CircuitLowerBounds.Gate,
    C.gates[j]? = some g ∧ n+i ∈ g.inputs
  obtain ⟨Q, hroot, hpriv, hparent, hclosed⟩ := chooseClosure P R r C.size
    ⟨hr, hsub, hcard⟩ (fun _ hj => hj.1)
  let outside (w : ℕ) := decide (¬ supp w ⊆ S)
  refine ⟨Q, label n C Q outside, hroot, hpriv, hparent, ?_, ?_, ?_⟩
  · intro j hj i hij hread hi hc
    exact hclosed j hj i hij hread ⟨hij.trans (hpriv j hj).1, hi, hc⟩
  · intro j hj g hg
    exact label_at_gate hj g hg
  · intro w hw
    rw [label_outside hw]
    exact decide_eq_true_iff
