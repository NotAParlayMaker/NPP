import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2861
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem gate_full (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length)
    (hrb : ∀ i ∈ gates[k].inputs, i < X.length + k) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf gates X).getD i false) := by
  rw [gate_val gates X k hk]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (wire_take gates X k i (hrb i hi) (le_of_lt hk)).symm

end PEqualNP.Outside.L_meta_2861

open PEqualNP.Outside.L_meta_2861 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2861 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i j a b c : ℕ), PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → j < C.gates.length → i < j → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs = [a, b] → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [n + i, c] → c < n + i → (∀ k < C.gates.length, k ≠ j → n + i ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → C.output ≠ n + i → PEqualNP.MetaComplexity.NestedCover.ReadsBack n (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ ∀ x : Fin n → Bool, (⟨(C.gates.set i ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, c]⟩).set j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [n + i, b]⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C i j a b c hrb hj hij hopi hini hopj hinj hc hread hout
  have hi : i < C.gates.length := by omega
  have hG : ∀ k (hk : k < C.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
    intro k hk
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk]
  rw [hG i hi] at hopi hini
  rw [hG j hj] at hopj hinj
  have hab : ∀ t ∈ [a, b], t < n + i := by
    intro t ht
    have := hrb i hi t
    rw [hG i hi, hini] at this
    exact this ht
  have ha := hab a (by simp)
  have hb := hab b (by simp)
  generalize hG' : (C.gates.set i ⟨GateOp.and, [a, c]⟩).set j ⟨GateOp.and, [n + i, b]⟩ = G'
  have hlen : G'.length = C.gates.length := by rw [← hG']; simp
  have hget : ∀ k (hk : k < C.gates.length), G'[k]'(by omega) =
      if k = j then ⟨GateOp.and, [n + i, b]⟩ else if k = i then ⟨GateOp.and, [a, c]⟩ else C.gates[k] := by
    intro k hk
    subst hG'
    rw [List.getElem_set]
    by_cases h1 : j = k
    · simp [h1]
    · rw [if_neg h1, if_neg (fun h => h1 h.symm), List.getElem_set]
      by_cases h2 : i = k
      · simp [h2]
      · rw [if_neg h2, if_neg (fun h => h2 h.symm)]
  have hbound : ∀ k (hk : k < C.gates.length), ∀ t ∈ (G'[k]'(by omega)).inputs, t < n + k := by
    intro k hk t ht
    rw [hget k hk] at ht
    by_cases h1 : k = j
    · rw [if_pos h1] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> omega
    · rw [if_neg h1] at ht
      by_cases h2 : k = i
      · rw [if_pos h2] at ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> omega
      · rw [if_neg h2] at ht
        have := hrb k hk t
        rw [hG k hk] at this
        exact this ht
  refine ⟨?_, ?_, ?_⟩
  · intro k hk t ht
    have hk' : k < C.gates.length := by
      have : k < G'.length := hk
      omega
    have e : PEqualNP.MetaComplexity.NestedCover.gateAt (⟨G', C.output⟩ : Circuit) k = G'[k]'(by omega) := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ (by omega)]
    rw [e] at ht
    exact hbound k hk' t ht
  · show G'.length = C.gates.length
    exact hlen
  · intro x
    have va : ∀ k (hk : k < C.gates.length), (wf G' (List.ofFn x)).getD (n + k) false
        = (G'[k]'(by omega)).op.eval ((G'[k]'(by omega)).inputs.map fun t => (wf G' (List.ofFn x)).getD t false) := by
      intro k hk
      have := gate_full G' (List.ofFn x) k (by omega) (by
        intro t ht; rw [List.length_ofFn]; exact hbound k hk t ht)
      rw [List.length_ofFn] at this
      exact this
    have vb : ∀ k (hk : k < C.gates.length), (wf C.gates (List.ofFn x)).getD (n + k) false
        = C.gates[k].op.eval (C.gates[k].inputs.map fun t => (wf C.gates (List.ofFn x)).getD t false) := by
      intro k hk
      have := gate_full C.gates (List.ofFn x) k hk (by
        intro t ht; rw [List.length_ofFn]
        have := hrb k hk t
        rw [hG k hk] at this
        exact this ht)
      rw [List.length_ofFn] at this
      exact this
    have weq : ∀ k, (∀ k' < k, k' < C.gates.length → k' ≠ i →
          (wf G' (List.ofFn x)).getD (n + k') false = (wf C.gates (List.ofFn x)).getD (n + k') false) →
        ∀ w < n + k, w ≠ n + i →
          (wf G' (List.ofFn x)).getD w false = (wf C.gates (List.ofFn x)).getD w false := by
      intro k ih w hw hwi
      by_cases hwn : w < n
      · rw [wf_keep _ _ _ (by simpa using hwn), wf_keep _ _ _ (by simpa using hwn)]
      · obtain ⟨k', rfl⟩ : ∃ k', w = n + k' := ⟨w - n, by omega⟩
        by_cases hk' : k' < C.gates.length
        · exact ih k' (by omega) hk' (by omega)
        · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_ofFn]; omega),
            List.getD_eq_default _ _ (by rw [wf_len, List.length_ofFn]; omega)]
    have main : ∀ k, k < C.gates.length → k ≠ i →
        (wf G' (List.ofFn x)).getD (n + k) false = (wf C.gates (List.ofFn x)).getD (n + k) false := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk hki
        have W := weq k ih
        by_cases hkj : k = j
        · subst hkj
          rw [va k hk, hget k hk, if_pos rfl, vb k hk, hinj, hopj]
          simp only [List.map_cons, List.map_nil]
          rw [va i hi, hget i hi, if_neg (by omega), if_pos rfl, vb i hi, hini, hopi]
          simp only [List.map_cons, List.map_nil]
          rw [W a (by omega) (by omega), W b (by omega) (by omega), W c (by omega) (by omega)]
          simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true]
          cases (wf C.gates (List.ofFn x)).getD a false <;>
            cases (wf C.gates (List.ofFn x)).getD b false <;>
            cases (wf C.gates (List.ofFn x)).getD c false <;> rfl
        · rw [va k hk, hget k hk, if_neg hkj, if_neg hki, vb k hk]
          congr 1
          apply List.map_congr_left
          intro t ht
          have h1 := hrb k hk t
          rw [hG k hk] at h1
          refine W t (h1 ht) ?_
          intro hte
          have := hread k hk hkj
          rw [hG k hk] at this
          exact this (hte ▸ ht)
    show (wf G' (List.ofFn x)).getD C.output false = (wf C.gates (List.ofFn x)).getD C.output false
    by_cases hlt : C.output < n + C.gates.length
    · exact weq C.gates.length (fun k' _ hk' hne => main k' hk' hne) C.output hlt hout
    · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_ofFn]; omega),
        List.getD_eq_default _ _ (by rw [wf_len, List.length_ofFn]; omega)]
