import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3266

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def effective (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

private lemma effective_bound (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (effective g).length ≤ 1 + (if !g.op.eval [false] then 1 else 0) := by
  rcases g with ⟨op, inputs⟩
  cases op <;> simp_all [effective, GateOp.eval, List.length_take] <;> omega

private lemma effective_eval (g : Gate) (x y : List Bool)
    (h : (effective g).map (fun i => x.getD i false) =
         (effective g).map (fun i => y.getD i false)) :
    g.op.eval (g.inputs.map (fun i => x.getD i false)) =
      g.op.eval (g.inputs.map (fun i => y.getD i false)) := by
  rcases g with ⟨op, inputs⟩
  cases op with
  | not => cases inputs <;> simp_all [effective, GateOp.eval, List.headD]
  | and => simp only [effective] at h; rw [h]
  | or => simp only [effective] at h; rw [h]
  | mod m => simp only [effective] at h; rw [h]
  | maj => simp only [effective] at h; rw [h]

private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private def run (gs : List Gate) (xs : List Bool) : List Bool :=
  evalFrom false GateOp.eval gs xs

private lemma run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++ [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
  simp [run, evalFrom, List.foldl_append]

private lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length :=
  evalFrom_length false GateOp.eval gs xs

private lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.countP (fun g => !g.op.eval [false]) ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ (effective g).toFinset else F
    have hb : B.card ≤ F.card + (if !g.op.eval [false] then 1 else 0) := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) (effective g).toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le (effective g)).trans (effective_bound g (hg g (by simp)))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.countP_append, List.countP_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (run gs x).length = j := by simp [run_length, hx, j]
    have ey : (run gs y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left (effective g).toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      apply effective_eval
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_3266

theorem PEqualNP.Outside.L_meta_3266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : Finset ℕ), x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧ ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 → (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6 := by
  intro n C h
  obtain ⟨S, hS, hs⟩ := PEqualNP.Outside.L_meta_3266.supports n C.gates h {C.output}
  refine ⟨S, by simpa [Nat.add_comm] using hS, ?_⟩
  intro x y hx hy ha
  exact hs x y hx hy ha C.output (by simp)
