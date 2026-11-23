import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_697
open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append w _ false i hi

lemma gate_value (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) (hread : ∀ i ∈ g.inputs, i < w.length + j) :
    (gs.foldl step w).getD (w.length+j) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl step w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons k gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst k
      simp only [Nat.add_zero, List.foldl_cons]
      calc
        (gs.foldl step (step w g)).getD w.length false = (step w g).getD w.length false :=
          keep gs (step w g) w.length (by simp [step])
        _ = g.op.eval (g.inputs.map fun i => w.getD i false) := by simp [step, List.getD]
        _ = g.op.eval (g.inputs.map fun i => (gs.foldl step (step w g)).getD i false) := by
          congr 1
          apply List.map_congr_left
          intro i hi
          have hilt : i < w.length := by simpa using hread i hi
          symm
          rw [keep gs (step w g) i (by simp [step]; omega)]
          exact List.getD_append w _ false i hilt
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      have h := ih (step w k) j hj (by intro i hi; simpa [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hread i hi)
      simpa [step, List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

lemma or_value (C : Circuit) (x : List Bool) (g a b : ℕ) (hn : x.length ≤ g)
    (ha : a < g) (hb : b < g) (hg : C.gates[g-x.length]? = some ⟨GateOp.or,[a,b]⟩) :
    wireVal C x g = (wireVal C x a || wireVal C x b) := by
  have he : x.length + (g-x.length) = g := by omega
  have h := gate_value C.gates x (g-x.length) ⟨GateOp.or,[a,b]⟩ hg (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega)
  change (C.gates.foldl step x).getD g false =
    ((C.gates.foldl step x).getD a false || (C.gates.foldl step x).getD b false)
  simpa only [he, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false] using h

lemma low_alive {P L : ℕ} {inc : Fin P → Fin L → Bool} {C : Circuit} {g : ℕ} {w : Fin L}
    (hlow : IsLow P L inc C g w) (p : Fin P) (hp : p ∈ aliveSet P L C g w) :
    inc p w = true := by
  have h := hlow (fun q => decide (q = p)) (Finset.mem_filter.mp hp).2
  simpa [lineSum] using h

lemma alive_union {P L : ℕ} {C : Circuit} {g a b : ℕ} (w : Fin L) (hn : P+L ≤ g)
    (ha : a < g) (hb : b < g) (hg : C.gates[g-(P+L)]? = some ⟨GateOp.or,[a,b]⟩) :
    aliveSet P L C g w = aliveSet P L C a w ∪ aliveSet P L C b w := by
  ext p
  simp only [aliveSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  rw [or_value C (pointLineInput P L p w) g a b (by simpa [pointLineInput,restrictInput] using hn)
    ha hb (by simpa [pointLineInput,restrictInput] using hg)]
  simp only [Bool.or_eq_true]

end PEqualNP.Outside.L_meta_697

theorem PEqualNP.Outside.L_meta_697 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ), (∀ (p p' : Fin P) (w w' : Fin L), p ≠ p' → w ≠ w' → ¬ (inc p w = true ∧ inc p w' = true ∧ inc p' w = true ∧ inc p' w' = true)) → (∀ (x : Fin P → Bool) (y y' : Fin L → Bool), (C.wires (List.ofFn x ++ List.ofFn y)).getD g false = (C.wires (List.ofFn x ++ List.ofFn y')).getD g false) → ∀ (w w' : Fin L), PEqualNP.LowMerge.IsLowMerge P L inc C g w → PEqualNP.LowMerge.IsLowMerge P L inc C g w' → w = w' := by
  classical
  intro P L inc C g hinc hignore w w' hw hw'
  by_contra hww
  obtain ⟨hn,a,ha,b,hb,hgate,hlow,hab,hba⟩ := hw
  obtain ⟨_,_,_,_,_,_,hlow',_,_⟩ := hw'
  obtain ⟨p,hpa,hpnb⟩ := Finset.not_subset.mp hab
  obtain ⟨q,hqb,hqna⟩ := Finset.not_subset.mp hba
  have hpq : p ≠ q := by
    intro h
    apply hqna
    simpa [h] using hpa
  have hunion := PEqualNP.Outside.L_meta_697.alive_union w hn ha hb hgate
  have hpg : p ∈ PEqualNP.LowMerge.aliveSet P L C g w := by rw [hunion]; exact Finset.mem_union_left _ hpa
  have hqg : q ∈ PEqualNP.LowMerge.aliveSet P L C g w := by rw [hunion]; exact Finset.mem_union_right _ hqb
  have hsame : PEqualNP.LowMerge.aliveSet P L C g w = PEqualNP.LowMerge.aliveSet P L C g w' := by
    ext t
    simp only [PEqualNP.LowMerge.aliveSet, Finset.mem_filter, Finset.mem_univ, true_and]
    change (C.wires (List.ofFn (fun q => decide (q = t)) ++ List.ofFn (fun v => decide (v = w)))).getD g false = true ↔
      (C.wires (List.ofFn (fun q => decide (q = t)) ++ List.ofFn (fun v => decide (v = w')))).getD g false = true
    rw [hignore (fun q => decide (q = t)) (fun v => decide (v = w)) (fun v => decide (v = w'))]
  exact hinc p q w w' hpq hww ⟨PEqualNP.Outside.L_meta_697.low_alive hlow p hpg,
    PEqualNP.Outside.L_meta_697.low_alive hlow' p (hsame ▸ hpg),
    PEqualNP.Outside.L_meta_697.low_alive hlow q hqg,
    PEqualNP.Outside.L_meta_697.low_alive hlow' q (hsame ▸ hqg)⟩
