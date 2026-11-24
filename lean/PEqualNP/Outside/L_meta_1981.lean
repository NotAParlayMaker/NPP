import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_1981_aux

private def normalizeGate (k : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and =>
    if ∀ i ∈ g.inputs, i < k then g else ⟨.or, []⟩
  | _ => ⟨.or, g.inputs.filter (fun i => i < k)⟩

private def allowed (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem normalizedGate_allowed (k : ℕ) (g : Gate) (hg : allowed g) :
    allowed (normalizeGate k g) := by
  unfold normalizeGate
  split
  · split
    · exact hg
    · simp [allowed]
  · exact ⟨by simp, (List.length_filter_le _ _).trans hg.2⟩

private theorem normalizedGate_back (k : ℕ) (g : Gate) :
    ∀ i ∈ (normalizeGate k g).inputs, i < k := by
  unfold normalizeGate
  split
  · split
    · assumption
    · simp
  · intro i hi
    have h := (List.mem_filter.mp hi).2
    simpa using h

private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

private theorem or_filter (w : List Bool) (ins : List ℕ) :
    GateOp.or.eval ((ins.filter (fun i => i < w.length)).map (fun i => w.getD i false)) =
      GateOp.or.eval (ins.map (fun i => w.getD i false)) := by
  induction ins with
  | nil => rfl
  | cons i ins ih =>
    by_cases h : i < w.length
    · simp [List.filter_cons, h, GateOp.eval] at ih ⊢
      rw [ih]
    · have hz := List.getD_eq_default w false (Nat.le_of_not_lt h)
      simp [List.filter_cons, h, GateOp.eval, hz] at ih ⊢
      exact ih

private theorem normalizedGate_value (w : List Bool) (g : Gate) (hg : allowed g) :
    value (normalizeGate w.length g) w = value g w := by
  have hop : g.op = .and ∨ g.op = .or := by simpa using hg.1
  unfold normalizeGate
  split
  · rename_i hand
    split
    · rfl
    · rename_i hn
      push Not at hn
      obtain ⟨i, hi, hout⟩ := hn
      have hfalse : w.getD i false = false := List.getD_eq_default _ _ hout
      simp only [value, hand, GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [← Bool.not_eq_true]
      intro ht
      have hp := List.all_eq_true.mp ht (w.getD i false) (List.mem_map_of_mem hi)
      change w.getD i false = true at hp
      exact Bool.noConfusion (hfalse.symm.trans hp)
  · rename_i h
    have hor : g.op = .or := hop.resolve_left h
    simpa only [value, hor] using or_filter w g.inputs

private def normalize (k : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => normalizeGate k g :: normalize (k + 1) gs

private theorem norm_length (gs : List Gate) (k : ℕ) :
    (normalize k gs).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [normalize, ih]

private theorem norm_allowed (gs : List Gate) (k : ℕ)
    (h : ∀ g ∈ gs, allowed g) : ∀ g ∈ normalize k gs, allowed g := by
  induction gs generalizing k with
  | nil => simp [normalize]
  | cons g gs ih =>
    intro a ha
    rcases List.mem_cons.mp ha with he | ha
    · rw [he]
      exact normalizedGate_allowed k g (h g List.mem_cons_self)
    · exact ih (k + 1) (fun b hb => h b (List.mem_cons_of_mem _ hb)) a ha

private theorem norm_back (gs : List Gate) (k : ℕ) (j : ℕ)
    (hj : j < (normalize k gs).length) :
    ∀ i ∈ ((normalize k gs).getD j ⟨.or, []⟩).inputs, i < k + j := by
  induction gs generalizing k j with
  | nil => simp [normalize] at hj
  | cons g gs ih =>
    cases j with
    | zero => simpa [normalize, List.getD] using normalizedGate_back k g
    | succ j =>
      have hj' : j < (normalize (k + 1) gs).length := by simpa [normalize] using hj
      have he : k + (j + 1) = k + 1 + j := by omega
      simpa [normalize, List.getD, Nat.succ_eq_add_one, he] using ih (k + 1) j hj'

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

private theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [value g w]) := rfl

private theorem norm_run (gs : List Gate) (w : List Bool)
    (h : ∀ g ∈ gs, allowed g) : run (normalize w.length gs) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [normalize, run_cons, run_cons, normalizedGate_value w g (h g List.mem_cons_self)]
    simpa using ih (w ++ [value g w]) (fun a ha => h a (List.mem_cons_of_mem _ ha))

end PEqualNP.Outside.L_meta_1981_aux

theorem PEqualNP.Outside.L_meta_1981 :
    ∀ C : Circuit, Monotone2 C →
      ∃ D : Circuit, Monotone2 D ∧ ReadsBack 14 D ∧ D.size ≤ C.size ∧
        ∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro C hC
  refine ⟨⟨L_meta_1981_aux.normalize 14 C.gates, C.output⟩, ?_, ?_, ?_, ?_⟩
  · exact L_meta_1981_aux.norm_allowed C.gates 14 hC
  · exact L_meta_1981_aux.norm_back C.gates 14
  · simp [Circuit.size, L_meta_1981_aux.norm_length]
  · intro x
    have h := L_meta_1981_aux.norm_run C.gates (List.ofFn x) hC
    change (L_meta_1981_aux.run (L_meta_1981_aux.normalize 14 C.gates) (List.ofFn x)).getD
      C.output false = (L_meta_1981_aux.run C.gates (List.ofFn x)).getD C.output false
    rw [show (List.ofFn x).length = 14 from List.length_ofFn] at h
    rw [h]
