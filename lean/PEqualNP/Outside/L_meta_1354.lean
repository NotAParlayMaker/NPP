import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1354_aux

open PEqualNP.CircuitLowerBounds

def remap (n N : ℕ) (w : ℕ) : ℕ :=
  if w < n then w else if w = n then n + N + 1 else w - 1

def remapGate (n N : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap n N)⟩

theorem map_op (n N : ℕ) (gates : List Gate) :
    (gates.map (remapGate n N)).map Gate.op = gates.map Gate.op := by
  simp [remapGate]

theorem map_len (n N : ℕ) (gates : List Gate) :
    (gates.map (remapGate n N)).map (fun g => g.inputs.length) =
      gates.map (fun g => g.inputs.length) := by
  simp [remapGate]

theorem eraseIdx_snoc_false (x : List Bool) :
    (x ++ [false]).eraseIdx x.length = x := by
  induction x with
  | nil => simp
  | cons _ x ih => simpa [List.eraseIdx] using ih

theorem length_foldl (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons _ gs ih =>
    rw [List.foldl_cons, ih]
    simp; omega

theorem getD_eraseIdx_lt (w : List Bool) (n i : ℕ) (hn : n < w.length) (hi : i < n) :
    (w.eraseIdx n).getD i false = w.getD i false := by
  have hiL : i < w.length := Nat.lt_trans hi hn
  have hlen : (w.eraseIdx n).length = w.length - 1 := by
    simp [List.length_eraseIdx, hn]
  have hiS : i < (w.eraseIdx n).length := by omega
  rw [List.getD_eq_getElem _ false hiS, List.getD_eq_getElem _ false hiL]
  exact List.getElem_eraseIdx_of_lt hiS hi

theorem getD_eraseIdx_ge (w : List Bool) (n i : ℕ) (hn : n < w.length) (hi : n ≤ i) :
    (w.eraseIdx n).getD i false = w.getD (i + 1) false := by
  have hlen : (w.eraseIdx n).length = w.length - 1 := by
    simp [List.length_eraseIdx, hn]
  by_cases hS : i < (w.eraseIdx n).length
  · have hL : i + 1 < w.length := by omega
    rw [List.getD_eq_getElem _ false hS, List.getD_eq_getElem _ false hL]
    exact List.getElem_eraseIdx_of_ge hS hi
  · have hL : w.length ≤ i + 1 := by omega
    rw [List.getD_eq_default _ _ (Nat.not_lt.1 hS), List.getD_eq_default _ _ hL]

theorem getD_remap (n N : ℕ) (w : List Bool) (hn : n < w.length)
    (hbound : w.length ≤ n + N + 1) (hfalse : w.getD n false = false) (i : ℕ) :
    (w.eraseIdx n).getD (remap n N i) false = w.getD i false := by
  by_cases hlt : i < n
  · simp [remap, hlt]
    exact getD_eraseIdx_lt w n i hn hlt
  · by_cases heq : i = n
    · have hmap : remap n N i = n + N + 1 := by simp [remap, heq]
      have hOOB : (w.eraseIdx n).length ≤ n + N + 1 := by
        simp [List.length_eraseIdx, hn]; omega
      rw [hmap, List.getD_eq_default _ _ hOOB, heq, hfalse]
    · have hgt : n < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
      have hmap : remap n N i = i - 1 := by simp [remap, hlt, heq]
      have hge : n ≤ i - 1 := by omega
      have hget := getD_eraseIdx_ge w n (i - 1) hn hge
      have hi : i - 1 + 1 = i := by omega
      rw [hmap, hget, hi]

theorem eval_remapGate (n N : ℕ) (g : Gate) (w : List Bool) (hn : n < w.length)
    (hbound : w.length ≤ n + N + 1) (hfalse : w.getD n false = false) :
    (remapGate n N g).op.eval
        ((remapGate n N g).inputs.map fun i => (w.eraseIdx n).getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  change g.op.eval ((remapGate n N g).inputs.map fun i => (w.eraseIdx n).getD i false) =
    g.op.eval (g.inputs.map fun i => w.getD i false)
  congr 1
  simp only [remapGate, List.map_map]
  refine List.map_congr_left ?_
  intro i _
  exact getD_remap n N w hn hbound hfalse i

theorem eraseIdx_append_gate (n N : ℕ) (g : Gate) (w : List Bool) (hn : n < w.length)
    (hbound : w.length ≤ n + N + 1) (hfalse : w.getD n false = false) :
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).eraseIdx n =
      w.eraseIdx n ++
        [(remapGate n N g).op.eval
            ((remapGate n N g).inputs.map fun i => (w.eraseIdx n).getD i false)] := by
  rw [List.eraseIdx_append_of_lt_length hn]
  congr 1
  exact congrArg (fun b => [b]) (eval_remapGate n N g w hn hbound hfalse).symm

theorem foldl_remap (n N : ℕ) (gates : List Gate) (x : List Bool) (hx : x.length = n)
    (hN : gates.length ≤ N) :
    (gates.map (remapGate n N)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x =
      (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (x ++ [false])).eraseIdx n := by
  have key : ∀ (gs : List Gate) (w : List Bool),
      n < w.length → w.length + gs.length ≤ n + N + 1 → w.getD n false = false →
      (gs.map (remapGate n N)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.eraseIdx n) =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).eraseIdx
          n := by
    intro gs w hn hbound hf
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      have hwbound : w.length ≤ n + N + 1 := by omega
      have hstep := eraseIdx_append_gate n N g w hn hwbound hf
      have hn' : n < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
        simp; omega
      have hf' :
          (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD n false = false := by
        rw [List.getD_append _ _ _ _ hn]; exact hf
      have hbound' :
          (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length + gs.length ≤
            n + N + 1 := by
        have hlen :
            (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1 := by
          simp
        have hgs : (g :: gs).length = gs.length + 1 := by simp
        omega
      rw [← hstep]
      exact ih _ hn' hbound' hf'
  have hn0 : n < (x ++ [false]).length := by simp [hx]
  have hf0 : (x ++ [false]).getD n false = false := by
    have : n = x.length := hx.symm
    subst this
    have hlt : x.length < (x ++ [false]).length := by simp
    rw [List.getD_eq_getElem _ false hlt]
    simp [List.getElem_append_right]
  have herase : (x ++ [false]).eraseIdx n = x := by
    simpa [hx.symm] using eraseIdx_snoc_false x
  have hbound0 : (x ++ [false]).length + gates.length ≤ n + N + 1 := by
    simp [hx]; omega
  exact (by simpa [herase] using key gates (x ++ [false]) hn0 hbound0 hf0)

theorem wires_eq (n : ℕ) (gates : List Gate) (x : List Bool) (hx : x.length = n) :
    Circuit.wires ⟨gates.map (remapGate n gates.length), 0⟩ x =
      (Circuit.wires ⟨gates, 0⟩ (x ++ [false])).eraseIdx n := by
  simpa [Circuit.wires] using foldl_remap n gates.length gates x hx le_rfl

theorem wires_ignore_output (gates : List Gate) (out out' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gates, out⟩ x = Circuit.wires ⟨gates, out'⟩ x := rfl

theorem eval_fix (n : ℕ) (gates : List Gate) (j : ℕ) (x : Fin n → Bool)
    (_hj : j < gates.length) :
    Circuit.eval ⟨gates.map (remapGate n gates.length), n + j⟩ (List.ofFn x) =
      Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  have hx : (List.ofFn x).length = n := by simp
  simp only [Circuit.eval]
  have hw := wires_eq n gates (List.ofFn x) hx
  have hlen : (Circuit.wires ⟨gates, 0⟩ (List.ofFn x ++ [false])).length =
      n + 1 + gates.length := by
    change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x ++ [false])).length = n + 1 + gates.length
    rw [length_foldl]
    simp [hx]
  have hn : n < (Circuit.wires ⟨gates, 0⟩ (List.ofFn x ++ [false])).length := by omega
  have hge : n ≤ n + j := Nat.le_add_right _ _
  rw [wires_ignore_output (gates.map (remapGate n gates.length)) (n + j) 0,
    wires_ignore_output gates (n + 1 + j) 0, hw]
  have hget :=
    getD_eraseIdx_ge (Circuit.wires ⟨gates, 0⟩ (List.ofFn x ++ [false])) n (n + j) hn hge
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hget

theorem exists_remap (n : ℕ) (gates : List Gate) :
    ∃ gates' : List Gate,
      gates'.map Gate.op = gates.map Gate.op ∧
        gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧
          ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length →
            Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) =
              Circuit.eval ⟨gates, n + 1 + j⟩ (List.ofFn x ++ [false]) := by
  refine ⟨gates.map (remapGate n gates.length), map_op _ _ _, map_len _ _ _, ?_⟩
  intro j x hj
  exact eval_fix n gates j x hj

end PEqualNP.Outside.L_meta_1354_aux

theorem PEqualNP.Outside.L_meta_1354 :
    ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate),
      ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate,
        gates'.map PEqualNP.CircuitLowerBounds.Gate.op =
            gates.map PEqualNP.CircuitLowerBounds.Gate.op ∧
          gates'.map (fun g => g.inputs.length) = gates.map (fun g => g.inputs.length) ∧
            ∀ (j : ℕ) (x : Fin n → Bool), j < gates.length →
              PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', n + j⟩ (List.ofFn x) =
                PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + 1 + j⟩
                  (List.ofFn x ++ [false]) := by
  intro n gates
  exact PEqualNP.Outside.L_meta_1354_aux.exists_remap n gates
