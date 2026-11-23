import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_716

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

private def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

private def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

private def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

private lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

private lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

private lemma run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, step, List.length_append,
      List.length_cons, List.length_nil]; omega

private def outputRead (k o : ℕ) : ℕ := if o < k then o else k + 4

private def xorGates (neg : Bool) (z o k : ℕ) : List Gate :=
  [⟨if neg then .and else .or, [z, outputRead k o]⟩,
   ⟨if neg then .or else .and, [z, outputRead k o]⟩,
   ⟨.not, [k + 1]⟩,
   ⟨if neg then .or else .and, [k, k + 2]⟩]

private lemma xorGates_eval (neg : Bool) (w : List Bool) (z o : ℕ) (hz : z < w.length) :
    ((xorGates neg z o w.length).foldl step w).getD (w.length + 3) false =
      xor (w.getD z false) (if neg then !(w.getD o false) else w.getD o false) := by
  let x := w.getD z false
  let y := w.getD o false
  let a := if neg then x && y else x || y
  let b := if neg then x || y else x && y
  let d := if neg then a || !b else a && !b
  have read (t : List Bool) (ht : t.length ≤ 4) :
      (w ++ t).getD (outputRead w.length o) false = y := by
    unfold outputRead
    split
    · exact List.getD_append _ _ _ _ (by assumption)
    · rw [List.getD_eq_default _ _ (by simp; omega),
          show y = false from List.getD_eq_default _ _ (by omega)]
  have first : step w ⟨if neg then .and else .or, [z, outputRead w.length o]⟩ =
      w ++ [a] := by
    have h := read [] (by simp)
    simp only [List.append_nil, List.getD_eq_getElem?_getD] at h
    cases neg <;> simp [step, GateOp.eval, h, a, x]
  have second : step (w ++ [a]) ⟨if neg then .or else .and, [z, outputRead w.length o]⟩ =
      w ++ [a, b] := by
    have h := read [a] (by simp)
    have hz' : (w ++ [a]).getD z false = w.getD z false :=
      List.getD_append _ _ _ _ hz
    simp only [List.getD_eq_getElem?_getD] at h hz'
    cases neg <;> simp [step, GateOp.eval, hz', h, b, x, List.append_assoc]
  have third : step (w ++ [a, b]) ⟨.not, [w.length + 1]⟩ = w ++ [a, b, !b] := by
    have hb : (w ++ [a, b]).getD (w.length + 1) false = b := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    simp only [List.getD_eq_getElem?_getD] at hb
    simp [step, GateOp.eval, hb, List.append_assoc]
  have fourth : step (w ++ [a, b, !b]) ⟨if neg then .or else .and, [w.length, w.length + 2]⟩ =
      w ++ [a, b, !b, d] := by
    have ha : (w ++ [a, b, !b]).getD w.length false = a := by simp
    have hb : (w ++ [a, b, !b]).getD (w.length + 2) false = !b := by
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp
    simp only [List.getD_eq_getElem?_getD] at ha hb
    cases neg <;> simp [step, GateOp.eval, ha, hb, d, List.append_assoc]
  simp only [xorGates, List.foldl_cons, List.foldl_nil, first, second, third, fourth]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  have hindex : w.length + 3 - w.length = 3 := by omega
  rw [hindex]
  have truth (m u v : Bool) :
      (let a := if m then u && v else u || v
       let b := if m then u || v else u && v
       if m then a || !b else a && !b) =
        xor u (if m then !v else v) := by
    cases m <;> cases u <;> cases v <;> rfl
  exact truth neg x y

private lemma extendXor (neg : Bool) {n s : ℕ} (g : (Fin n → Bool) → Bool)
    (h : HasCircuitSize n (fun y => if neg then !(g y) else g y) s) :
    HasCircuitSize (n + 1) (fun x => xor (x (Fin.last n)) (g (fun i => x i.castSucc))) (s + 4) := by
  obtain ⟨C, hfan, hsize, heval⟩ := h
  let C' := relabel n (n + 1) Fin.castSucc C
  let k := n + 1 + C'.gates.length
  refine ⟨⟨C'.gates ++ xorGates neg n C'.output k, k + 3⟩, ?_, ?_, ?_⟩
  · intro gate hg
    change gate ∈ C'.gates ++ xorGates neg n C'.output k at hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨original, horig, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan original horig).1, by simpa [relGate] using (hfan original horig).2⟩
    · cases neg <;> simp [xorGates] at hg <;>
        rcases hg with rfl | rfl | rfl | rfl <;> simp
  · simpa [Circuit.size, C', relabel, xorGates] using Nat.add_le_add_right hsize 4
  · intro x
    let w := C'.gates.foldl step (List.ofFn x)
    have hw : w.length = k := by simp [w, run_length, k]
    have hC : w.getD C'.output false = (if neg then !(g (fun i => x i.castSucc)) else g (fun i => x i.castSucc)) :=
      ((rel_fold n (n + 1) Fin.castSucc C.gates _ _ (rel_init n (n + 1) Fin.castSucc x)).2.2 C.output).trans
        (heval (fun i => x i.castSucc))
    have hz : w.getD n false = x (Fin.last n) := by
      have keep (gs : List Gate) (v : List Bool) (i : ℕ) (hi : i < v.length) :
          (gs.foldl step v).getD i false = v.getD i false := by
        induction gs generalizing v with
        | nil => rfl
        | cons gate gs ih =>
          rw [List.foldl_cons, ih (step v gate) (by simp [step]; omega)]
          exact List.getD_append _ _ _ _ hi
      rw [keep C'.gates (List.ofFn x) n (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      rfl
    change ((C'.gates ++ xorGates neg n C'.output k).foldl step (List.ofFn x)).getD (k + 3) false = _
    rw [List.foldl_append]
    change ((xorGates neg n C'.output k).foldl step w).getD (k + 3) false = _
    rw [← hw, xorGates_eval _ _ _ _ (by omega), hz, hC]
    cases neg <;> simp

end PEqualNP.Outside.L_meta_716

theorem PEqualNP.Outside.L_meta_716 :
    ∀ (n s : ℕ) (g : (Fin n → Bool) → Bool),
      (PEqualNP.MetaComplexity.HasCircuitSize n g s → PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) ∧
      (PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s →
        PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
          (fun x : Fin (n + 1) → Bool => xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))) (s + 4)) := by
  intro n s g
  exact ⟨PEqualNP.Outside.L_meta_716.extendXor false g,
    PEqualNP.Outside.L_meta_716.extendXor true g⟩
