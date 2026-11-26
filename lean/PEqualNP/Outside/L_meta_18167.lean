import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_18167

private def next (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem afterAppend (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  induction w generalizing i with
  | nil => cases i <;> simp
  | cons a w ih => cases i with
    | zero => simp
    | succ i => simpa only [List.cons_append, List.length_cons, Nat.succ_inj, List.getD_cons_succ] using ih i

private theorem anyJoin (args : List ℕ) (a b c : ℕ → Bool) (h : ∀ i, c i = (a i || b i)) :
    (args.map c).any id = ((args.map a).any id || (args.map b).any id) := by
  induction args with
  | nil => rfl
  | cons i t ih =>
    simp only [List.map_cons, List.any_cons, id_eq, h, ih]
    ac_rfl

private theorem propagate (gs : List Gate) (onlyOr : ∀ g ∈ gs, g.op = .or)
    (a b c : List Bool) (ha : a.length = c.length) (hb : b.length = c.length)
    (hv : ∀ i, c.getD i false = (a.getD i false || b.getD i false)) :
    ∀ i, (gs.foldl next c).getD i false =
      ((gs.foldl next a).getD i false || (gs.foldl next b).getD i false) := by
  induction gs generalizing a b c with
  | nil => exact hv
  | cons g gs ih =>
    apply ih (fun v hv => onlyOr v (List.mem_cons_of_mem _ hv)) (next a g) (next b g) (next c g)
      (by simp [next, ha]) (by simp [next, hb])
    intro i
    simp only [next, afterAppend, ha, hb]
    by_cases h : i = c.length
    · simpa only [h, ↓reduceIte, onlyOr g List.mem_cons_self, GateOp.eval] using
        anyJoin g.inputs (fun j => a.getD j false) (fun j => b.getD j false)
          (fun j => c.getD j false) hv
    · simpa only [h, ↓reduceIte] using hv i

private theorem joinEval {n : ℕ} (C : Circuit) (onlyOr : ∀ g ∈ C.gates, g.op = .or)
    (a b : Fin n → Bool) :
    C.eval (List.ofFn fun i => a i || b i) = (C.eval (List.ofFn a) || C.eval (List.ofFn b)) := by
  apply propagate C.gates onlyOr (List.ofFn a) (List.ofFn b) (List.ofFn fun i => a i || b i)
    (by simp) (by simp) _ C.output
  intro i
  by_cases hi : i < n
  · simp only [List.getD_eq_getElem _ _ (by simpa using hi : i < (List.ofFn a).length),
      List.getD_eq_getElem _ _ (by simpa using hi : i < (List.ofFn b).length),
      List.getD_eq_getElem _ _ (by simpa using hi : i < (List.ofFn fun j => a j || b j).length),
      List.getElem_ofFn]
  · simp [List.getD_eq_getElem?_getD, hi]

end PEqualNP.Outside.L_meta_18167

theorem PEqualNP.Outside.L_meta_18167 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (18 : ℕ) → (¬∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ (x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)))) := by
  intro C hm _ hno
  have onlyOr (g : Gate) (hg : g ∈ C.gates) : g.op = .or := by
    have hop : g.op = .and ∨ g.op = .or := (hm g hg).1
    rcases hop with h | h
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hj
      exact (hno ⟨⟨j, hlt⟩, (congrArg Gate.op heq).trans h⟩).elim
    · exact h
  by_contra! hagree
  let a : Fin 10 → Bool := fun i => decide (i = 0)
  let b : Fin 10 → Bool := fun i => decide (i = 1)
  have ha := hagree a
  have hb := hagree b
  have hab := hagree (fun i => a i || b i)
  change C.eval (List.ofFn a) = false at ha
  change C.eval (List.ofFn b) = false at hb
  change C.eval (List.ofFn fun i => a i || b i) = true at hab
  rw [PEqualNP.Outside.L_meta_18167.joinEval C onlyOr a b, ha, hb] at hab
  contradiction
