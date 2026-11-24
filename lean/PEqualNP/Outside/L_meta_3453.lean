import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3453

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.FactorSubst
open PEqualNP.TopForm

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlen]
    exact getD_append_left_lt w _ i hi

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_len (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_step_len C.gates x

lemma wires_input_lt (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_step_getD_lt C.gates x i hi

lemma wires_gate_val (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hrb : ReadsBack x.length C) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun a => (C.wires x).getD a false) := by
  rw [wires_eq_foldl]
  have hget : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = gateAt C j :: C.gates.drop (j + 1) := by
      rw [hget, List.drop_eq_getElem_cons hj]
    rw [h2] at h1
    exact h1.symm
  set pref := (C.gates.take j).foldl step x with hpref_def
  have hpref_len : pref.length = x.length + j := by
    rw [hpref_def, foldl_step_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hfold : C.gates.foldl step x = (C.gates.drop (j + 1)).foldl step (step pref (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons, ← hpref_def]
  have hlt_step : x.length + j < (step pref (gateAt C j)).length := by
    simp only [step, List.length_append, List.length_cons, List.length_nil, hpref_len]
    omega
  rw [hfold, foldl_step_getD_lt _ _ _ hlt_step]
  have hself : (step pref (gateAt C j)).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun a => pref.getD a false) := by
    rw [← hpref_len]
    exact getD_append_self pref _
  rw [hself]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < pref.length := by
    rw [hpref_len]
    exact hrb j hj a ha
  have ha_eq : ((C.gates.drop (j + 1)).foldl step (step pref (gateAt C j))).getD a false =
      pref.getD a false := by
    have ha_lt2 : a < (step pref (gateAt C j)).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [foldl_step_getD_lt _ _ _ ha_lt2]
    exact getD_append_left_lt pref _ a halt
  exact ha_eq.symm

lemma mono_eval_op (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hle : ∀ k (hk1 : k < l1.length) (hk2 : k < l2.length), l1[k] = true → l2[k] = true) :
    op.eval l1 = true → op.eval l2 = true := by
  rcases hop with rfl | rfl
  · intro h1
    simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro b hb
    obtain ⟨k, hk2, rfl⟩ := List.mem_iff_getElem.mp hb
    have hk1 : k < l1.length := by omega
    exact hle k hk1 hk2 (h1 l1[k] (List.getElem_mem hk1))
  · intro h1
    simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    obtain ⟨b, hb, rfl⟩ := h1
    obtain ⟨k, hk1, hbk⟩ := List.mem_iff_getElem.mp hb
    have hk2 : k < l2.length := by omega
    exact ⟨l2[k], List.getElem_mem hk2, hle k hk1 hk2 hbk⟩

lemma substReads_len (C : Circuit) (n u : ℕ) (sigma : ℕ → ℕ) :
    (substReads C n u sigma).gates.length = C.gates.length := by
  simp [substReads]

lemma substReads_gateAt (C : Circuit) (n u : ℕ) (sigma : ℕ → ℕ) (r : ℕ) (hr : r < C.gates.length) :
    gateAt (substReads C n u sigma) r =
      ⟨(gateAt C r).op, (gateAt C r).inputs.map fun i => if i = n + u then sigma r else i⟩ := by
  have hr' : r < (substReads C n u sigma).gates.length := by rw [substReads_len]; exact hr
  simp only [gateAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hr', List.getElem?_eq_getElem hr]
  simp [substReads]

lemma substReads_rb (C : Circuit) (n u : ℕ) (sigma : ℕ → ℕ)
    (hrb : ReadsBack n C) (hsigma : ∀ r : ℕ, sigma r < n + u) :
    ReadsBack n (substReads C n u sigma) := by
  intro r hr a ha
  have hrC : r < C.gates.length := by rwa [substReads_len] at hr
  rw [substReads_gateAt C n u sigma r hrC] at ha
  simp only [List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hblt : b < n + r := hrb r hrC b hb
  split_ifs with hbu
  · have hsig : sigma r < n + u := hsigma r
    omega
  · exact hblt

lemma substReads_le (n : ℕ) (C : Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool)
    (hAO2 : IsAO2 n C) (hsigma : ∀ r : ℕ, sigma r < n + u)
    (hle : ∀ r < C.gates.length, n + u ∈ (gateAt C r).inputs →
      (C.wires (List.ofFn x)).getD (sigma r) false = true →
      (C.wires (List.ofFn x)).getD (n + u) false = true) :
    ∀ i : ℕ, ((substReads C n u sigma).wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn x)).getD i false = true := by
  have hrbC : ReadsBack (List.ofFn x).length C := by simp; exact hAO2.2.1
  have hrbS : ReadsBack (List.ofFn x).length (substReads C n u sigma) := by
    simp; exact substReads_rb C n u sigma hAO2.2.1 hsigma
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases hltN : i < n
    · have h1 := wires_input_lt (substReads C n u sigma) (List.ofFn x) i (by simp; exact hltN)
      have h2 := wires_input_lt C (List.ofFn x) i (by simp; exact hltN)
      rw [h1] at hi
      rw [h2]
      exact hi
    · by_cases hltG : i < n + C.gates.length
      · let r : ℕ := i - n
        have hr : r < C.gates.length := by omega
        have hrS : r < (substReads C n u sigma).gates.length := by rw [substReads_len]; exact hr
        have hir : i = (List.ofFn x).length + r := by simp [r]; omega
        rw [hir] at hi ⊢
        rw [wires_gate_val (substReads C n u sigma) (List.ofFn x) r hrS hrbS] at hi
        rw [wires_gate_val C (List.ofFn x) r hr hrbC]
        rw [substReads_gateAt C n u sigma r hr] at hi
        have hg_mem : gateAt C r ∈ C.gates := by
          simp [gateAt, List.getD_eq_getElem?_getD, hr]
        refine mono_eval_op (gateAt C r).op (hAO2.1 (gateAt C r) hg_mem) _ _ (by simp) ?_ hi
        intro k hk1 hk2 hk
        have hk' : k < (gateAt C r).inputs.length := by simpa using hk2
        simp only [List.map_map, List.getElem_map, Function.comp_apply] at hk ⊢
        have hk_in : (gateAt C r).inputs[k] ∈ (gateAt C r).inputs := List.getElem_mem hk'
        have hk_lt : (gateAt C r).inputs[k] < i := by
          have := hAO2.2.1 r hr _ hk_in
          omega
        split_ifs at hk with heq
        · have hsig_lt : sigma r < i := by
            have := hsigma r
            omega
          have hC_sig := ih (sigma r) hsig_lt hk
          rw [heq]
          exact hle r hr (heq ▸ hk_in) hC_sig
        · exact ih _ hk_lt hk
      · have hge : ((substReads C n u sigma).wires (List.ofFn x)).length ≤ i := by
          rw [wires_len, List.length_ofFn, substReads_len]; omega
        rw [getD_ge_len _ _ hge] at hi
        exact absurd hi (by decide)

lemma substReads_eq (n : ℕ) (C : Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool)
    (hAO2 : IsAO2 n C) (hsigma : ∀ r : ℕ, sigma r < n + u)
    (heq : ∀ r < C.gates.length, n + u ∈ (gateAt C r).inputs →
      (C.wires (List.ofFn x)).getD (sigma r) false =
      (C.wires (List.ofFn x)).getD (n + u) false) :
    (substReads C n u sigma).wires (List.ofFn x) = C.wires (List.ofFn x) := by
  have hrbC : ReadsBack (List.ofFn x).length C := by simp; exact hAO2.2.1
  have hrbS : ReadsBack (List.ofFn x).length (substReads C n u sigma) := by
    simp; exact substReads_rb C n u sigma hAO2.2.1 hsigma
  have hpt : ∀ i : ℕ,
      ((substReads C n u sigma).wires (List.ofFn x)).getD i false =
      (C.wires (List.ofFn x)).getD i false := by
    intro i
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      by_cases hltN : i < n
      · rw [wires_input_lt (substReads C n u sigma) (List.ofFn x) i (by simp; exact hltN)]
        rw [wires_input_lt C (List.ofFn x) i (by simp; exact hltN)]
      · by_cases hltG : i < n + C.gates.length
        · let r : ℕ := i - n
          have hr : r < C.gates.length := by omega
          have hrS : r < (substReads C n u sigma).gates.length := by rw [substReads_len]; exact hr
          have hir : i = (List.ofFn x).length + r := by simp [r]; omega
          rw [hir]
          rw [wires_gate_val (substReads C n u sigma) (List.ofFn x) r hrS hrbS]
          rw [wires_gate_val C (List.ofFn x) r hr hrbC]
          rw [substReads_gateAt C n u sigma r hr]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro b hb
          simp only [Function.comp_apply]
          have hb_lt : b < i := by
            have := hAO2.2.1 r hr b hb
            omega
          split_ifs with hbu
          · have hsig_lt : sigma r < i := by
              have := hsigma r
              omega
            rw [ih (sigma r) hsig_lt, hbu]
            exact heq r hr (hbu ▸ hb)
          · exact ih b hb_lt
        · have hge1 : ((substReads C n u sigma).wires (List.ofFn x)).length ≤ i := by
            rw [wires_len, List.length_ofFn, substReads_len]; omega
          have hge2 : (C.wires (List.ofFn x)).length ≤ i := by
            rw [wires_len, List.length_ofFn]; omega
          rw [getD_ge_len _ _ hge1, getD_ge_len _ _ hge2]
  apply List.ext_getElem
  · rw [wires_len, wires_len, substReads_len]
  · intro i hi1 hi2
    have h := hpt i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1,
      List.getElem?_eq_getElem hi2, Option.getD_some] at h
    exact h

end PEqualNP.Outside.L_meta_3453

theorem PEqualNP.Outside.L_meta_3453 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool), PEqualNP.TopForm.IsAO2 n C → u < C.gates.length → (∀ r : ℕ, sigma r < n + u) → ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = true → (C.wires (List.ofFn x)).getD (n + u) false = true) → ∀ i : ℕ, ((PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn x)).getD i false = true) ∧ ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = (C.wires (List.ofFn x)).getD (n + u) false) → (PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x) = C.wires (List.ofFn x)) := by
  intro n C u sigma x hAO2 _ hsigma
  exact ⟨PEqualNP.Outside.L_meta_3453.substReads_le n C u sigma x hAO2 hsigma,
    PEqualNP.Outside.L_meta_3453.substReads_eq n C u sigma x hAO2 hsigma⟩
