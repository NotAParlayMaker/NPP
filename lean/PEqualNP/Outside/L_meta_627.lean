import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_627_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append,
      List.length_cons, List.length_nil]; omega

private lemma run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi


private def saved (k o : ℕ) := if o < k then o else k + 100

private lemma read_saved (w p : List Bool) (o : ℕ) (hp : p.length ≤ 8) :
    (w ++ p).getD (saved w.length o) false = w.getD o false := by
  unfold saved
  split
  · exact List.getD_append _ _ _ _ (by assumption)
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma read_offset (w p : List Bool) (k : ℕ) :
    (w ++ p).getD (w.length + k) false = p.getD k false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

private def gates (u v k a b : ℕ) : List Gate :=
  [⟨.or, [u, v]⟩, ⟨.and, [u, v]⟩, ⟨.not, [k+1]⟩, ⟨.and, [k, k+2]⟩,
   ⟨.not, [k+3]⟩, ⟨.and, [saved k a, k+4]⟩,
   ⟨.and, [saved k b, k+3]⟩, ⟨.or, [k+5, k+6]⟩]

private lemma eval_tail (w : List Bool) (u v a b : ℕ)
    (hu : u < w.length) (hv : v < w.length) :
    ((gates u v w.length a b).foldl step w).getD (w.length + 7) false =
      (if w.getD u false = w.getD v false then w.getD a false else w.getD b false) := by
  let U := w.getD u false
  let V := w.getD v false
  let A := w.getD a false
  let B := w.getD b false
  let z0 := U || V
  have h0 : step w ⟨.or, [u, v]⟩ = (w ++ [z0]) := by
    simp [step, GateOp.eval, z0, U, V]
  let z1 := U && V
  have h1 : step (w ++ [z0]) ⟨.and, [u, v]⟩ = (w ++ [z0, z1]) := by
    simp [step, GateOp.eval, z1, U, V, List.append_assoc]
    exact congrArg₂ (· && ·) (List.getD_append w [z0] false u hu) (List.getD_append w [z0] false v hv)
  let z2 := !z1
  have h2 : step (w ++ [z0, z1]) ⟨.not, [w.length+1]⟩ = (w ++ [z0, z1, z2]) := by
    simp [step, GateOp.eval, z2, List.getD, List.append_assoc]
  let z3 := z0 && z2
  have h3 : step (w ++ [z0, z1, z2]) ⟨.and, [w.length, w.length+2]⟩ = (w ++ [z0, z1, z2, z3]) := by
    simp [step, GateOp.eval, z3, List.getD, List.append_assoc]
  let z4 := !z3
  have h4 : step (w ++ [z0, z1, z2, z3]) ⟨.not, [w.length+3]⟩ = (w ++ [z0, z1, z2, z3, z4]) := by
    simp [step, GateOp.eval, z4, List.getD, List.append_assoc]
  let z5 := A && z4
  have h5 : step (w ++ [z0, z1, z2, z3, z4]) ⟨.and, [saved w.length a, w.length+4]⟩ = (w ++ [z0, z1, z2, z3, z4, z5]) := by
    simp [step, GateOp.eval, z5, A, List.getD, List.append_assoc]
    exact congrArg (fun t => t && z4) (read_saved w [z0, z1, z2, z3, z4] a (by simp))
  let z6 := B && z3
  have h6 : step (w ++ [z0, z1, z2, z3, z4, z5]) ⟨.and, [saved w.length b, w.length+3]⟩ = (w ++ [z0, z1, z2, z3, z4, z5, z6]) := by
    simp [step, GateOp.eval, z6, B, List.getD, List.append_assoc]
    exact congrArg (fun t => t && z3) (read_saved w [z0, z1, z2, z3, z4, z5] b (by simp))
  let z7 := z5 || z6
  have h7 : step (w ++ [z0, z1, z2, z3, z4, z5, z6]) ⟨.or, [w.length+5, w.length+6]⟩ = (w ++ [z0, z1, z2, z3, z4, z5, z6, z7]) := by
    simp [step, GateOp.eval, z7, List.getD, List.append_assoc]

  simp only [gates, List.foldl_cons, List.foldl_nil, h0, h1, h2, h3, h4, h5, h6, h7,
    read_offset]
  change z7 = (if U = V then A else B)
  dsimp [z7, z6, z5, z4, z3, z2, z1, z0]
  cases U <;> cases V <;> simp

end PEqualNP.Outside.L_meta_627_aux

open PEqualNP.Outside.L_meta_627_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_627 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n), (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o1 false = F (Function.update x u (x v)) ∧ (C.wires (List.ofFn x)).getD o2 false = F (Function.update x u (!(x v)))) → PEqualNP.MetaComplexity.HasCircuitSize n F (s + 8) := by
  intro n s F u v h
  obtain ⟨C, hok, hsize, a, b, hab⟩ := h
  let k := n + C.gates.length
  refine ⟨⟨C.gates ++ gates u v k a b, k+7⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hok g h
    · simp only [gates, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h | h | h | h <;> subst g <;> simp
  · change (C.gates ++ gates u v k a b).length ≤ s + 8
    have hs : C.gates.length ≤ s := hsize
    simp [gates]
    omega
  · intro x
    let w := C.gates.foldl step (List.ofFn x)
    have hk : w.length = k := by simp [w, run_length, k]
    have hinput (i : Fin n) : w.getD i.val false = x i := by
      rw [show w.getD i.val false = (List.ofFn x).getD i.val false from
        run_keep _ _ _ (by simp)]
      simp
    obtain ⟨ha, hb⟩ := hab x
    change w.getD a false = _ at ha
    change w.getD b false = _ at hb
    change ((C.gates ++ gates u v k a b).foldl step (List.ofFn x)).getD (k+7) false = _
    rw [List.foldl_append]
    change ((gates u v k a b).foldl step w).getD (k+7) false = _
    rw [← hk, eval_tail _ _ _ _ _ (by rw [hk]; exact Nat.lt_of_lt_of_le u.isLt (by dsimp [k]; omega))
      (by rw [hk]; exact Nat.lt_of_lt_of_le v.isLt (by dsimp [k]; omega)), hinput, hinput]
    split
    · rename_i he
      simpa [← he] using ha
    · rename_i he
      have hn : (!(x v)) = x u := by cases h₁ : x u <;> cases h₂ : x v <;> simp_all
      simpa [hn] using hb
