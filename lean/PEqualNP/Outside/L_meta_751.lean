import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_751

open PEqualNP.CircuitLowerBounds

private def wireRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma wireRun_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wireRun (g :: gs) x = wireRun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma wireRun_length (gs : List Gate) (x : List Bool) :
    (wireRun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wireRun]
  | cons g gs ih => rw [wireRun_cons, ih]; simp; omega

private lemma wireRun_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (wireRun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [wireRun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma wireRun_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    wireRun gs x = wireRun (gs.drop j) (wireRun (gs.take j) x) := by
  simpa only [wireRun, List.foldl_append] using
    congrArg (fun l : List Gate => wireRun l x) (List.take_append_drop j gs).symm

theorem wire_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < n) :
    (C.wires (List.ofFn x)).getD k false = x ⟨k,hk⟩ := by
  change (wireRun C.gates (List.ofFn x)).getD k false = _
  have hp : k < (List.ofFn x).length := by simpa using hk
  rw [wireRun_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

theorem wire_missing {n : ℕ} (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : n + C.gates.length ≤ k) : (C.wires (List.ofFn x)).getD k false = false := by
  change (wireRun C.gates (List.ofFn x)).getD k false = false
  exact List.getD_eq_default _ _ (by simpa [wireRun_length] using hk)

theorem wire_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun q =>
        if q < n + j then (C.wires (List.ofFn x)).getD q false else false) := by
  obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
  subst g
  let earlier := wireRun (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = n + j := by
    simp [earlier, wireRun_length, Nat.min_eq_left hj.le]
  have hsplit : wireRun C.gates (List.ofFn x) =
      wireRun (C.gates[j] :: C.gates.drop (j + 1)) earlier := by
    rw [wireRun_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (q : ℕ) : earlier.getD q false =
      if q < n + j then (C.wires (List.ofFn x)).getD q false else false := by
    by_cases hq : q < n + j
    · rw [ite_eq_left hq]
      change earlier.getD q false = (wireRun C.gates (List.ofFn x)).getD q false
      rw [hsplit]
      exact (wireRun_getD _ earlier q (by simpa only [plen] using hq)).symm
    · rw [ite_eq_right hq]
      exact List.getD_eq_default _ _ (by omega)
  change (wireRun C.gates (List.ofFn x)).getD (n + j) false = _
  rw (occs := [1]) [hsplit]
  rw (occs := [1]) [wireRun_cons]
  rw [wireRun_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

end PEqualNP.Outside.L_meta_751

namespace PEqualNP.Outside.L_meta_751

open PEqualNP.CircuitLowerBounds

lemma gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w w' : ℕ → Bool)
    (hw : ∀ q ∈ g.inputs, w q = true → w' q = true) :
    g.op.eval (g.inputs.map w) = true → g.op.eval (g.inputs.map w') = true := by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, List.all_map, Function.comp_def, List.all_eq_true,
      id_eq]
    intro h q hq
    exact hw q hq (h q hq)
  · simp only [hg, GateOp.eval, List.any_map, Function.comp_def, List.any_eq_true,
      id_eq]
    rintro ⟨q, hq, h⟩
    exact ⟨q, hq, hw q hq h⟩

end PEqualNP.Outside.L_meta_751

theorem PEqualNP.Outside.L_meta_751 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i : ℕ), (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → Relation.ReflTransGen (fun a b : ℕ => ∃ (k : ℕ) (e : PEqualNP.CircuitLowerBounds.Gate), a = n + k ∧ C.gates[k]? = some e ∧ b ∈ e.inputs ∧ b < a) i (n + j) → g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ x x' : Fin n → Bool, (∀ q : Fin n, x q = true → x' q = true) → (PEqualNP.CircuitLowerBounds.Circuit.wires C (List.ofFn x)).getD i false = true → (PEqualNP.CircuitLowerBounds.Circuit.wires C (List.ofFn x')).getD i false = true := by
  intro n C i hcone x x' hxx' hi
  classical
  have all (k : ℕ) :
      Relation.ReflTransGen (fun a b : ℕ => ∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        a = n+j ∧ C.gates[j]? = some g ∧ b ∈ g.inputs ∧ b<a) i k →
      (C.wires (List.ofFn x)).getD k false = true →
      (C.wires (List.ofFn x')).getD k false = true := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk hval
      by_cases hkn : k<n
      · rw [PEqualNP.Outside.L_meta_751.wire_input C x k hkn] at hval
        rw [PEqualNP.Outside.L_meta_751.wire_input C x' k hkn]
        exact hxx' ⟨k,hkn⟩ hval
      · by_cases hmiss : n+C.gates.length≤k
        · rw [PEqualNP.Outside.L_meta_751.wire_missing C x k hmiss] at hval
          contradiction
        · let j := k-n
          have hj : j<C.gates.length := by dsimp [j]; omega
          let g := C.gates[j]
          have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hj
          have hkj : k=n+j := by dsimp [j]; omega
          have hop := hcone j g hg (by simpa only [← hkj] using hk)
          rw [hkj, PEqualNP.Outside.L_meta_751.wire_gate C x j g hg] at hval
          rw [hkj, PEqualNP.Outside.L_meta_751.wire_gate C x' j g hg]
          apply PEqualNP.Outside.L_meta_751.gate_mono g hop
            (fun q => if q<n+j then (C.wires (List.ofFn x)).getD q false else false)
            (fun q => if q<n+j then (C.wires (List.ofFn x')).getD q false else false)
            ?_ hval
          intro q hq htrue
          by_cases hqk : q<n+j
          · simp only [if_pos hqk] at htrue ⊢
            apply ih q (by omega) ?_ htrue
            exact hk.trans (Relation.ReflTransGen.single ⟨j,g,hkj,hg,hq,by omega⟩)
          · simp only [if_neg hqk] at htrue
            contradiction
  exact all i Relation.ReflTransGen.refl hi
