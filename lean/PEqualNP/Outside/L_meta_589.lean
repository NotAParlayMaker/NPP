import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta589

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

private lemma foldl_wiresStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl wiresStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (wiresStep w g).length := by
      simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (wiresStep w g) hlt]
    simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

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

private lemma getD_append_left (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private def muxCircuit {n : ℕ} (i : Fin n) (C : Circuit) (o1 o2 : ℕ) : Circuit :=
  let L := n + C.gates.length
  let o1' := if o1 < L then o1 else L + 5
  let o2' := if o2 < L then o2 else L + 5
  ⟨C.gates ++
    [Gate.mk GateOp.not [i.val],
     Gate.mk GateOp.and [L, o1'],
     Gate.mk GateOp.and [i.val, o2'],
     Gate.mk GateOp.or [L + 1, L + 2]],
    L + 3⟩

end PEqualNP.Outside.LMeta589

theorem PEqualNP.Outside.L_meta_589 : ∀ (n s : ℕ) (F : (Fin n → Bool) → Bool) (i : Fin n), (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧ ∃ o1 o2 : ℕ, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o1 false = F (Function.update x i false) ∧ (C.wires (List.ofFn x)).getD o2 false = F (Function.update x i true)) → PEqualNP.MetaComplexity.HasCircuitSize n F (s + 4) := by
  rintro n s F i ⟨C, hF, hsize, o1, o2, ho⟩
  refine ⟨PEqualNP.Outside.LMeta589.muxCircuit i C o1 o2, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.LMeta589.muxCircuit, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl | rfl | rfl | rfl
    · exact hF g h
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, by simp⟩
  · simp only [PEqualNP.Outside.LMeta589.muxCircuit, PEqualNP.CircuitLowerBounds.Circuit.size,
      List.length_append, List.length_cons, List.length_nil]
    change C.gates.length ≤ s at hsize
    omega
  · intro x
    set L := n + C.gates.length
    set o1' := if o1 < L then o1 else L + 5
    set o2' := if o2 < L then o2 else L + 5
    change ((C.gates ++
      [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.not [i.val],
       PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [L, o1'],
       PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [i.val, o2'],
       PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [L + 1, L + 2]]).foldl
        PEqualNP.Outside.LMeta589.wiresStep (List.ofFn x)).getD (L + 3) false = F x
    rw [List.foldl_append]
    set w0 := C.gates.foldl PEqualNP.Outside.LMeta589.wiresStep (List.ofFn x)
    have hw0 : w0.length = L := by
      rw [PEqualNP.Outside.LMeta589.foldl_wiresStep_length, List.length_ofFn]
    have hxi0 : w0.getD i.val false = x i := by
      rw [PEqualNP.Outside.LMeta589.foldl_wiresStep_getD_lt C.gates (List.ofFn x) i.val (by simp),
        PEqualNP.Outside.LMeta589.getD_ofFn x i.val i.isLt]
    obtain ⟨ho1_eq, ho2_eq⟩ := ho x
    change w0.getD o1 false = F (Function.update x i false) at ho1_eq
    change w0.getD o2 false = F (Function.update x i true) at ho2_eq
    simp only [List.foldl_cons, List.foldl_nil]
    have hs1 : PEqualNP.Outside.LMeta589.wiresStep w0
        (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.not [i.val]) =
        w0 ++ [!(x i)] := by
      rw [PEqualNP.Outside.LMeta589.wiresStep]
      simp only [List.map_cons, List.map_nil, hxi0, PEqualNP.CircuitLowerBounds.GateOp.eval,
        List.headD_cons]
    rw [hs1]
    set w1 := w0 ++ [!(x i)]
    have hw1 : w1.length = L + 1 := by simp [w1, hw0]
    have hL1 : w1.getD L false = !(x i) :=
      PEqualNP.Outside.LMeta589.getD_append_last_eq w0 (!(x i)) L hw0
    have ho1_1 : w1.getD o1' false = F (Function.update x i false) := by
      by_cases hlt : o1 < L
      · simp only [o1', hlt, ite_true]
        rw [PEqualNP.Outside.LMeta589.getD_append_left w0 _ o1 (by omega), ho1_eq]
      · simp only [o1', hlt, ite_false]
        rw [PEqualNP.Outside.LMeta589.getD_ge_length w1 (L + 5) (by omega),
          ← ho1_eq, PEqualNP.Outside.LMeta589.getD_ge_length w0 o1 (by omega)]
    set v2 := !(x i) && F (Function.update x i false)
    have hs2 : PEqualNP.Outside.LMeta589.wiresStep w1
        (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [L, o1']) =
        w1 ++ [v2] := by
      rw [PEqualNP.Outside.LMeta589.wiresStep]
      simp only [List.map_cons, List.map_nil, hL1, ho1_1, PEqualNP.CircuitLowerBounds.GateOp.eval,
        List.all_cons, List.all_nil, id_eq, Bool.and_true, v2]
    rw [hs2]
    set w2 := w1 ++ [v2]
    have hw2 : w2.length = L + 2 := by simp [w2, hw1]
    have hxi2 : w2.getD i.val false = x i := by
      rw [PEqualNP.Outside.LMeta589.getD_append_left w1 _ i.val (by have := i.isLt; omega),
        PEqualNP.Outside.LMeta589.getD_append_left w0 _ i.val (by have := i.isLt; omega), hxi0]
    have ho2_2 : w2.getD o2' false = F (Function.update x i true) := by
      by_cases hlt : o2 < L
      · simp only [o2', hlt, ite_true]
        rw [PEqualNP.Outside.LMeta589.getD_append_left w1 _ o2 (by omega),
          PEqualNP.Outside.LMeta589.getD_append_left w0 _ o2 (by omega), ho2_eq]
      · simp only [o2', hlt, ite_false]
        rw [PEqualNP.Outside.LMeta589.getD_ge_length w2 (L + 5) (by omega),
          ← ho2_eq, PEqualNP.Outside.LMeta589.getD_ge_length w0 o2 (by omega)]
    set v3 := x i && F (Function.update x i true)
    have hs3 : PEqualNP.Outside.LMeta589.wiresStep w2
        (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [i.val, o2']) =
        w2 ++ [v3] := by
      rw [PEqualNP.Outside.LMeta589.wiresStep]
      simp only [List.map_cons, List.map_nil, hxi2, ho2_2, PEqualNP.CircuitLowerBounds.GateOp.eval,
        List.all_cons, List.all_nil, id_eq, Bool.and_true, v3]
    rw [hs3]
    set w3 := w2 ++ [v3]
    have hw3 : w3.length = L + 3 := by simp [w3, hw2]
    have hv2_3 : w3.getD (L + 1) false = v2 := by
      rw [PEqualNP.Outside.LMeta589.getD_append_left w2 _ (L + 1) (by omega),
        PEqualNP.Outside.LMeta589.getD_append_last_eq w1 v2 (L + 1) hw1]
    have hv3_3 : w3.getD (L + 2) false = v3 :=
      PEqualNP.Outside.LMeta589.getD_append_last_eq w2 v3 (L + 2) hw2
    have hs4 : PEqualNP.Outside.LMeta589.wiresStep w3
        (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [L + 1, L + 2]) =
        w3 ++ [v2 || v3] := by
      rw [PEqualNP.Outside.LMeta589.wiresStep]
      simp only [List.map_cons, List.map_nil, hv2_3, hv3_3, PEqualNP.CircuitLowerBounds.GateOp.eval,
        List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [hs4, PEqualNP.Outside.LMeta589.getD_append_last_eq w3 (v2 || v3) (L + 3) hw3]
    cases hxi : x i
    · have hupd : Function.update x i false = x := by
        funext k; by_cases hk : k = i
        · subst hk; simp [hxi]
        · simp [Function.update, hk]
      simp [v2, v3, hxi, hupd]
    · have hupd : Function.update x i true = x := by
        funext k; by_cases hk : k = i
        · subst hk; simp [hxi]
        · simp [Function.update, hk]
      simp [v2, v3, hxi, hupd]
