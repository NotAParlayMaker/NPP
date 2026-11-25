import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7602

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CarriedProduct PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]


def F (n : ℕ) (C : Circuit) (vals : List Bool) (m : ℕ) (L : List ℕ) : List ℕ :=
  ((List.range m).reverse).foldl (liveStep n C vals) L

lemma F_zero (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) :
    F n C vals 0 L = L := by
  simp [F]

lemma F_succ (n : ℕ) (C : Circuit) (vals : List Bool) (m : ℕ) (L : List ℕ) :
    F n C vals (m + 1) L = F n C vals m (liveStep n C vals L m) := by
  simp [F, List.range_succ]

lemma step_sub (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ) (hw : w ∈ L) :
    w ∈ liveStep n C vals L j := by
  unfold liveStep
  split_ifs
  · exact List.mem_append_left _ hw
  · exact hw

lemma step_mem (n : ℕ) (C : Circuit) (vals : List Bool) (L : List ℕ) (j w : ℕ)
    (h : w ∈ liveStep n C vals L j) :
    w ∈ L ∨ (n + j ∈ L ∧ w ∈ (gateAt C j).inputs ∧ w < n + j ∧ vals.getD w false = true) := by
  unfold liveStep at h
  split_ifs at h with hj
  · rcases List.mem_append.1 h with h | h
    · exact Or.inl h
    · simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
      exact Or.inr ⟨hj, h.1, h.2.1, h.2.2⟩
  · exact Or.inl h

lemma F_sub (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (w : ℕ), w ∈ L → w ∈ F n C vals m L := by
  intro m
  induction m with
  | zero => intro L w hw; rw [F_zero]; exact hw
  | succ m ih => intro L w hw; rw [F_succ]; exact ih _ w (step_sub n C vals L m w hw)

lemma F_mem (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (w : ℕ), w ∈ F n C vals m L → w ∈ L ∨ w < n + m := by
  intro m
  induction m with
  | zero => intro L w hw; rw [F_zero] at hw; exact Or.inl hw
  | succ m ih =>
    intro L w hw
    rw [F_succ] at hw
    rcases ih _ w hw with h | h
    · rcases step_mem n C vals L m w h with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · exact Or.inr (by omega)

lemma F_true (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ), (∀ w ∈ L, vals.getD w false = true) →
      ∀ w ∈ F n C vals m L, vals.getD w false = true := by
  intro m
  induction m with
  | zero => intro L hL w hw; rw [F_zero] at hw; exact hL w hw
  | succ m ih =>
    intro L hL w hw
    rw [F_succ] at hw
    refine ih _ ?_ w hw
    intro w2 hw2
    rcases step_mem n C vals L m w2 hw2 with h | h
    · exact hL w2 h
    · exact h.2.2.2

lemma F_back (n : ℕ) (C : Circuit) (vals : List Bool) :
    ∀ (m : ℕ) (L : List ℕ) (j : ℕ), j < m → n + j ∈ F n C vals m L →
      ∀ a ∈ (gateAt C j).inputs, a < n + j → vals.getD a false = true →
        a ∈ F n C vals m L := by
  intro m
  induction m with
  | zero => intro L j hj; omega
  | succ m ih =>
    intro L j hj hmem a ha hlt hv
    rw [F_succ] at hmem ⊢
    by_cases hjm : j < m
    · exact ih _ j hjm hmem a ha hlt hv
    · have hjeq : j = m := by omega
      subst hjeq
      have h1 : n + j ∈ liveStep n C vals L j := by
        rcases F_mem n C vals j _ _ hmem with h | h
        · exact h
        · omega
      have h2 : n + j ∈ L := by
        rcases step_mem n C vals L j _ h1 with h | h
        · exact h
        · exact h.1
      apply F_sub
      unfold liveStep
      rw [if_pos h2]
      refine List.mem_append_right _ ?_
      simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ha, hlt, hv⟩

lemma liveWires_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    liveWires n C x = F n C (C.wires (List.ofFn x)) C.gates.length
      (if (C.wires (List.ofFn x)).getD C.output false then [C.output] else []) := rfl

lemma live_true (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (h : IsLive n C x w) :
    W n C x w = true := by
  unfold IsLive at h
  rw [liveWires_eq] at h
  refine F_true n C _ _ _ ?_ w h
  intro w2 hw2
  split_ifs at hw2 with hc
  · simp only [List.mem_singleton] at hw2
    rw [hw2]; exact hc
  · simp at hw2

lemma live_back (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length)
    (h : IsLive n C x (n + j)) (a : ℕ) (ha : a ∈ (gateAt C j).inputs) (hlt : a < n + j)
    (hv : W n C x a = true) : IsLive n C x a := by
  unfold IsLive at h ⊢
  rw [liveWires_eq] at h ⊢
  exact F_back n C _ _ _ j hj h a ha hlt hv

lemma live_out (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : W n C x C.output = true) :
    IsLive n C x C.output := by
  unfold IsLive
  rw [liveWires_eq]
  apply F_sub
  unfold W at h
  rw [if_pos h]
  simp

lemma gateAt_set (C : Circuit) (q k : ℕ) (b : Bool) (hkq : k ≠ q) :
    gateAt ⟨PEqualNP.NotPremium.replaceByConst C.gates q b, C.output⟩ k = gateAt C k := by
  simp only [gateAt, PEqualNP.NotPremium.replaceByConst, List.getD_eq_getElem?_getD]
  rw [List.getElem?_set_ne (Ne.symm hkq)]

theorem closure (n : ℕ) (C : Circuit) (hM : Monotone2 C) (q : ℕ) (x : Fin n → Bool)
    (hno : ¬ IsLive n C x (n + q)) :
    ∀ w, IsLive n C x w →
      W n ⟨PEqualNP.NotPremium.replaceByConst C.gates q false, C.output⟩ x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hlive
    have hw := live_true n C _ w hlive
    by_cases hwn : w < n
    · rw [W_input n C _ w hwn] at hw
      rw [W_input n _ _ w hwn]
      exact hw
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k < C.gates.length
      · have hkq : k ≠ q := by
          rintro rfl
          exact hno hlive
        have hk2 : k < (Circuit.mk (PEqualNP.NotPremium.replaceByConst C.gates q false)
            C.output).gates.length := by
          simp only [PEqualNP.NotPremium.replaceByConst, List.length_set]
          exact hk
        have hmem : gateAt C k ∈ C.gates := by
          rw [gateAt_eq C k hk]
          exact List.getElem_mem hk
        have hops := (hM _ hmem).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hops
        rw [W_gate n _ _ k hk2, gateAt_set C q k false hkq]
        rw [W_gate n C _ k hk] at hw
        rcases hops with hop | hop
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at hw ⊢
          intro i hi
          have hv := hw i hi
          have hlt : i < n + k := by
            by_contra hc
            simp [hc] at hv
          simp only [hlt, ite_true] at hv ⊢
          exact ih i hlt (live_back n C _ k hk hlive i hi hlt hv)
        · rw [hop] at hw ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at hw ⊢
          obtain ⟨i, hi, hv⟩ := hw
          have hlt : i < n + k := by
            by_contra hc
            simp [hc] at hv
          simp only [hlt, ite_true] at hv
          refine ⟨i, hi, ?_⟩
          simp only [hlt, ite_true]
          exact ih i hlt (live_back n C _ k hk hlive i hi hlt hv)
      · exfalso
        have : W n C x (n + k) = false := by
          simp only [W]
          exact getD_ge_length _ _ (by rw [wires_length]; omega)
        rw [this] at hw
        exact Bool.false_ne_true hw

theorem main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ), PEqualNP.MetaComplexity.Monotone2 x2 → x3 < x2.size → ∀ (x6 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x6 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x2.gates x3 Bool.false, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit } x6 = Bool.false → PEqualNP.CarriedProduct.IsLive x1 x2 x6 (x1 + x3) := by
  intro n C q hM _ x h1 h2
  by_contra hno
  have hout : IsLive n C x C.output := live_out n C x h1
  have h3 := closure n C hM q x hno C.output hout
  have h4 : W n ⟨PEqualNP.NotPremium.replaceByConst C.gates q false, C.output⟩ x C.output = false := h2
  rw [h4] at h3
  exact Bool.false_ne_true h3

end PEqualNP.Outside.L_meta_7602

theorem PEqualNP.Outside.L_meta_7602 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ), PEqualNP.MetaComplexity.Monotone2 x2 → x3 < x2.size → ∀ (x6 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x6 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 { gates := PEqualNP.NotPremium.replaceByConst x2.gates x3 Bool.false, output := x2.output : PEqualNP.CircuitLowerBounds.Circuit } x6 = Bool.false → PEqualNP.CarriedProduct.IsLive x1 x2 x6 (x1 + x3) :=
  PEqualNP.Outside.L_meta_7602.main
