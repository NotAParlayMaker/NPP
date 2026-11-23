import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_542_aux

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
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

def rho (n i : ℕ) : ℕ := if i < n then i else i + 1

def mg (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho n)⟩

theorem val_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val gs x i = x ⟨i, h⟩ := by
  induction gs using List.reverseRecOn with
  | nil => rw [val_nil]; simp [h]
  | append_singleton gs g ih => rw [val_snoc, if_neg (by omega), ih]

theorem val_oob {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (h : n + gs.length ≤ i) : val gs x i = false := by
  unfold val
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [fold_length]; simp; omega)]
  rfl

theorem val_map {n : ℕ} (gs : List Gate) (x : Fin (n + 1) → Bool) (i : ℕ) :
    val (gs.map (mg n)) x (rho n i) = val gs (fun j : Fin n => x j.castSucc) i := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    simp only [List.map_nil]
    rw [val_nil, val_nil]
    unfold rho
    by_cases h : i < n
    · have h' : i < n + 1 := by omega
      simp only [h, if_true, dif_pos, h']
      rfl
    · have h' : ¬ (i + 1 < n + 1) := by omega
      simp only [h, if_false, dif_neg, h', not_false_eq_true]
  | append_singleton gs g ih =>
    rw [List.map_append, List.map_cons, List.map_nil, val_snoc, val_snoc, List.length_map]
    by_cases h : i = n + gs.length
    · have h' : rho n i = n + 1 + gs.length := by
        unfold rho
        rw [if_neg (by omega)]
        omega
      rw [if_pos h', if_pos h]
      simp only [mg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih j
    · have h' : rho n i ≠ n + 1 + gs.length := by
        unfold rho
        split_ifs <;> omega
      rw [if_neg h', if_neg h]
      exact ih i

end PEqualNP.Outside.L_meta_542_aux

open PEqualNP.Outside.L_meta_542_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_542 : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool) (v : Fin n), PEqualNP.MetaComplexity.HasCircuitSize n f s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => f (fun i : Fin n => x i.castSucc) || (x v.castSucc && x (Fin.last n))) (s + 2) := by
  rintro n s f v ⟨⟨gs, out⟩, hfan, hsize, hev⟩
  change gs.length ≤ s at hsize
  have hev' : ∀ x : Fin n → Bool, val gs x out = f x := hev
  refine ⟨⟨(gs.map (mg n) ++ [⟨GateOp.and, [v.val, n]⟩]) ++
      [⟨GateOp.or, if out < n + gs.length then [rho n out, n + 1 + gs.length]
        else [n + 1 + gs.length]⟩], n + 1 + (gs.length + 1)⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with (⟨g0, hg0, rfl⟩ | rfl) | rfl
    · obtain ⟨h1, h2⟩ := hfan g0 hg0
      exact ⟨h1, by simpa [mg] using h2⟩
    · simp
    · constructor
      · simp
      · split_ifs <;> simp
  · change ((gs.map (mg n) ++ [_]) ++ [_]).length ≤ s + 2
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  · intro x
    change val ((gs.map (mg n) ++ [⟨GateOp.and, [v.val, n]⟩]) ++
      [⟨GateOp.or, if out < n + gs.length then [rho n out, n + 1 + gs.length]
        else [n + 1 + gs.length]⟩]) x (n + 1 + (gs.length + 1)) = _
    have hA : val (gs.map (mg n) ++ [⟨GateOp.and, [v.val, n]⟩]) x (n + 1 + gs.length) =
        (x v.castSucc && x (Fin.last n)) := by
      rw [val_snoc, if_pos (by simp)]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        Bool.and_true, id_eq]
      rw [val_input _ x v.val (by omega), val_input _ x n (by omega)]
      rfl
    rw [val_snoc, if_pos (by simp)]
    by_cases h : out < n + gs.length
    · have hB : val (gs.map (mg n) ++ [⟨GateOp.and, [v.val, n]⟩]) x (rho n out) =
          f (fun i : Fin n => x i.castSucc) := by
        have hne : rho n out ≠ n + 1 + (gs.map (mg n)).length := by
          rw [List.length_map]
          unfold rho
          split_ifs <;> omega
        rw [val_snoc, if_neg hne, val_map, hev']
      simp only [h, if_true, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
        List.any_nil, Bool.or_false, id_eq, hA, hB]
    · have hF : f (fun i : Fin n => x i.castSucc) = false := by
        rw [← hev']
        exact val_oob gs _ out (by omega)
      simp only [h, if_false, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
        List.any_nil, Bool.or_false, id_eq, hA, hF, Bool.false_or]
