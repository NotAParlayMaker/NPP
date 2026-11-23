import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta591

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_wiresStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
    (w ++ [b]).getD m false = b := by
  subst hm
  simp [List.getD_eq_getElem?_getD]

private lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

private def remapUV {n : ℕ} (u v : Fin n) (i : ℕ) : ℕ :=
  if i = u.val then v.val else i

private def identifyCircuit {n : ℕ} (u v : Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map fun g => Gate.mk g.op (g.inputs.map (remapUV u v)), remapUV u v C.output⟩

private lemma identify_wires {n : ℕ} (u v : Fin n) (gs : List Gate) (x : Fin n → Bool) :
    let x' := Function.update x u (x v)
    ∀ i : ℕ,
      ((gs.map fun g => Gate.mk g.op (g.inputs.map (remapUV u v))).foldl wiresStep
        (List.ofFn x)).getD (remapUV u v i) false =
      (gs.foldl wiresStep (List.ofFn x')).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro x' i
    simp only [List.map_nil, List.foldl_nil]
    by_cases hin : i < n
    · by_cases hiu : i = u.val
      · have hr : remapUV u v i = v.val := by simp [remapUV, hiu]
        rw [hr, getD_ofFn x v.val v.isLt, getD_ofFn x' i hin]
        have heq : (⟨i, hin⟩ : Fin n) = u := Fin.ext hiu
        rw [heq]
        simp [x']
      · have hr : remapUV u v i = i := by simp [remapUV, hiu]
        rw [hr, getD_ofFn x i hin, getD_ofFn x' i hin]
        have hne : (⟨i, hin⟩ : Fin n) ≠ u := fun h => hiu (congrArg Fin.val h)
        simp [x', Function.update, hne]
    · have hne : i ≠ u.val := by have := u.isLt; omega
      have hr : remapUV u v i = i := by simp [remapUV, hne]
      rw [hr, getD_ge_length (List.ofFn x) i (by simp; omega),
        getD_ge_length (List.ofFn x') i (by simp; omega)]
  | append_singleton gs g ih =>
    intro x' i
    rw [List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
      List.foldl_nil, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set a := (gs.map fun g => Gate.mk g.op (g.inputs.map (remapUV u v))).foldl wiresStep (List.ofFn x)
    set b := gs.foldl wiresStep (List.ofFn x')
    have ha : a.length = n + gs.length := by
      rw [foldl_wiresStep_length, List.length_ofFn, List.length_map]
    have hb : b.length = n + gs.length := by
      rw [foldl_wiresStep_length, List.length_ofFn]
    have hval : g.op.eval ((g.inputs.map (remapUV u v)).map fun k => a.getD k false) =
        g.op.eval (g.inputs.map fun k => b.getD k false) := by
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      exact ih k
    change (a ++ [g.op.eval ((g.inputs.map (remapUV u v)).map fun k => a.getD k false)]).getD
        (remapUV u v i) false =
      (b ++ [g.op.eval (g.inputs.map fun k => b.getD k false)]).getD i false
    rw [hval]
    set w := g.op.eval (g.inputs.map fun k => b.getD k false)
    by_cases hlt : i < n + gs.length
    · have hlt' : remapUV u v i < n + gs.length := by
        unfold remapUV; have := v.isLt; split_ifs <;> omega
      rw [show (a ++ [w]).getD (remapUV u v i) false = a.getD (remapUV u v i) false by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : remapUV u v i < a.length)]]
      rw [show (b ++ [w]).getD i false = b.getD i false by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < b.length)]]
      exact ih i
    · by_cases heq : i = n + gs.length
      · subst heq
        have hne : n + gs.length ≠ u.val := by have := u.isLt; omega
        have hr : remapUV u v (n + gs.length) = n + gs.length := by simp [remapUV, hne]
        rw [hr, getD_append_last_eq a w _ ha, getD_append_last_eq b w _ hb]
      · have hne : i ≠ u.val := by have := u.isLt; omega
        have hr : remapUV u v i = i := by simp [remapUV, hne]
        rw [hr, getD_ge_length (a ++ [w]) i (by simp [ha]; omega),
          getD_ge_length (b ++ [w]) i (by simp [hb]; omega)]

end PEqualNP.Outside.LMeta591

theorem PEqualNP.Outside.L_meta_591 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (u v : Fin n), PEqualNP.MetaComplexity.HasCircuitSize n F s → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => F (Function.update x u (x v))) s := by
  rintro n s F u v ⟨C, hF, hsize, heval⟩
  refine ⟨PEqualNP.Outside.LMeta591.identifyCircuit u v C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.LMeta591.identifyCircuit, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨hop, hlen⟩ := hF g0 hg0
    exact ⟨hop, by simp [hlen]⟩
  · simpa [PEqualNP.Outside.LMeta591.identifyCircuit, PEqualNP.CircuitLowerBounds.Circuit.size] using hsize
  · intro x
    change ((C.gates.map fun g => PEqualNP.CircuitLowerBounds.Gate.mk g.op
      (g.inputs.map (PEqualNP.Outside.LMeta591.remapUV u v))).foldl
      PEqualNP.Outside.LMeta591.wiresStep (List.ofFn x)).getD
        (PEqualNP.Outside.LMeta591.remapUV u v C.output) false =
      F (Function.update x u (x v))
    rw [PEqualNP.Outside.LMeta591.identify_wires u v C.gates x C.output]
    exact heval (Function.update x u (x v))
