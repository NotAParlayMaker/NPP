import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4457_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih


lemma add_one (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) (a : Fin n)
    (h : HasCircuitSize n f s) :
    HasCircuitSize n (fun x => x a || f x) (s + 1) := by
  obtain ⟨C, hF, hs, hC⟩ := h
  refine ⟨⟨C.gates ++ [Gate.mk GateOp.or [(a : ℕ), C.output]], n + C.gates.length⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hF g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      simp
  · have hs' : C.gates.length ≤ s := hs
    show (C.gates ++ [Gate.mk GateOp.or [(a : ℕ), C.output]]).length ≤ s + 1
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro x
    have hC' : val C.gates x C.output = f x := hC x
    show val (C.gates ++ [Gate.mk GateOp.or [(a : ℕ), C.output]]) x (n + C.gates.length) = (x a || f x)
    rw [val_snoc, if_pos rfl]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false, id_eq]
    rw [val_lt C.gates x (a : ℕ) a.isLt, hC']

theorem main (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) (h : HasCircuitSize n f s) :
    ∀ A : Finset (Fin n),
      HasCircuitSize n (fun x => decide (∃ v ∈ A, x v = true) || f x) (s + A.card) := by
  classical
  intro A
  induction A using Finset.induction_on with
  | empty =>
    have e : (fun x : Fin n → Bool => decide (∃ v ∈ (∅ : Finset (Fin n)), x v = true) || f x) = f := by
      funext x
      simp
    rw [e]
    simpa using h
  | insert a A ha ih =>
    have h1 := add_one n _ _ a ih
    have e : (fun x : Fin n → Bool => decide (∃ v ∈ insert a A, x v = true) || f x) =
        (fun x => x a || (decide (∃ v ∈ A, x v = true) || f x)) := by
      funext x
      by_cases hxa : x a = true
      · simp [hxa]
      · simp [hxa]
    rw [e, Finset.card_insert_of_notMem ha, ← Nat.add_assoc]
    exact h1

end PEqualNP.Outside.L_meta_4457_aux

theorem PEqualNP.Outside.L_meta_4457 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1)) (x3 : (Fin x1 → Bool) → Bool) (x4 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x4 → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x6 : Fin x1 → Bool) => Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true) || x3 x6) (x4 + x2.card) := by
  intro x1 x2 x3 x4 h
  exact PEqualNP.Outside.L_meta_4457_aux.main x1 x3 x4 h x2
