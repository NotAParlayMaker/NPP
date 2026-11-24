import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2245

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

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

def remap (n j w k : ℕ) : ℕ :=
  if k < n + j then k else if k = n + j then w else k - 1

def remapGate (n j w : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap n j w)⟩

def deleteGate (n j w : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (remapGate n j w), remap n j w C.output⟩

lemma deleteGate_len (n j w : ℕ) (C : Circuit) (hj : j < C.gates.length) :
    (deleteGate n j w C).gates.length = C.gates.length - 1 := by
  simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma deleteGate_monotone2 (n j w : ℕ) (C : Circuit) (hm : Monotone2 C) :
    Monotone2 (deleteGate n j w C) := by
  intro g hg
  simp only [deleteGate, List.mem_append, List.mem_map] at hg
  rcases hg with h1 | ⟨g0, hg0, rfl⟩
  · exact hm g (List.mem_of_mem_take h1)
  · have h0 := hm g0 (List.mem_of_mem_drop hg0)
    simpa [remapGate] using h0

lemma deleteGate_gateAt_lt (n j w : ℕ) (C : Circuit) (i : ℕ) (hi : i < j) (hj : j < C.gates.length) :
    gateAt (deleteGate n j w C) i = gateAt C i := by
  have hiC : i < C.gates.length := lt_trans hi hj
  have hiD : i < (deleteGate n j w C).gates.length := by
    rw [deleteGate_len n j w C hj]; omega
  simp only [gateAt, List.getD_eq_getElem?_getD, deleteGate]
  have htake : i < (C.gates.take j).length := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; exact hi
  rw [List.getElem?_append_left htake, List.getElem?_take_of_lt hi]

lemma deleteGate_gateAt_ge (n j w : ℕ) (C : Circuit) (i : ℕ)
    (hge : j ≤ i) (hi : i < (deleteGate n j w C).gates.length) (hj : j < C.gates.length) :
    gateAt (deleteGate n j w C) i = remapGate n j w (gateAt C (i + 1)) := by
  have hlen := deleteGate_len n j w C hj
  have hi1 : i + 1 < C.gates.length := by omega
  simp only [gateAt, List.getD_eq_getElem?_getD, deleteGate]
  have htake_len : (C.gates.take j).length = j := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [List.getElem?_append_right (by omega), htake_len]
  rw [List.getElem?_map, List.getElem?_drop]
  have hidx : j + 1 + (i - j) = i + 1 := by omega
  rw [hidx, List.getElem?_eq_getElem hi1]
  simp

lemma deleteGate_readsBack (n j w : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (hw : w < n + j) (hrb : ReadsBack n C) :
    ReadsBack n (deleteGate n j w C) := by
  intro i hi a ha
  by_cases hij : i < j
  · rw [deleteGate_gateAt_lt n j w C i hij hj] at ha
    exact hrb i (lt_trans hij hj) a ha
  · have hge : j ≤ i := Nat.le_of_not_lt hij
    rw [deleteGate_gateAt_ge n j w C i hge hi hj] at ha
    simp only [remapGate, List.mem_map] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hlen := deleteGate_len n j w C hj
    have hblt : b < n + (i + 1) := hrb (i + 1) (by omega) b hb
    unfold remap
    split_ifs <;> omega

lemma eval_op_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
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

lemma deleteGate_wires_prefix (n j w : ℕ) (C : Circuit) (x : List Bool)
    (hx : x.length = n) (hj : j < C.gates.length) (k : ℕ) (hk : k < n + j) :
    ((deleteGate n j w C).wires x).getD k false = (C.wires x).getD k false := by
  rw [wires_eq_foldl, wires_eq_foldl]
  have hC : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  have hlen : ((C.gates.take j).foldl step x).length = n + j := by
    rw [foldl_step_len, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have h1 : ((deleteGate n j w C).gates.foldl step x).getD k false =
      ((C.gates.take j).foldl step x).getD k false := by
    simp only [deleteGate, List.foldl_append]
    exact foldl_step_getD_lt _ _ k (by omega)
  have h2 : (C.gates.foldl step x).getD k false =
      ((C.gates.take j).foldl step x).getD k false := by
    conv_lhs => rw [hC, List.foldl_append]
    exact foldl_step_getD_lt _ _ k (by omega)
  rw [h1, h2]

lemma deleteGate_wires_le (n j w : ℕ) (C : Circuit) (x : List Bool)
    (hx : x.length = n) (hj : j < C.gates.length) (hw : w < n + j)
    (hm : Monotone2 C) (hrb : ReadsBack n C)
    (hstep : (C.wires x).getD w false = true → (C.wires x).getD (n + j) false = true) :
    ∀ k : ℕ, ((deleteGate n j w C).wires x).getD (remap n j w k) false = true →
      (C.wires x).getD k false = true := by
  have hrb' : ReadsBack x.length (deleteGate n j w C) := by
    rw [hx]; exact deleteGate_readsBack n j w C hj hw hrb
  have hrbC : ReadsBack x.length C := by rw [hx]; exact hrb
  have hlenD := deleteGate_len n j w C hj
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro htrue
    by_cases hlt : k < n + j
    · have hrem : remap n j w k = k := by simp [remap, hlt]
      rw [hrem, deleteGate_wires_prefix n j w C x hx hj k hlt] at htrue
      exact htrue
    · by_cases heq : k = n + j
      · subst heq
        have hrem : remap n j w (n + j) = w := by simp [remap]
        rw [hrem, deleteGate_wires_prefix n j w C x hx hj w hw] at htrue
        exact hstep htrue
      · by_cases hltC : k < n + C.gates.length
        · have hgt : n + j < k := by omega
          let i := k - n - 1
          have hi_ge : j ≤ i := by omega
          have hi_lt : i < (deleteGate n j w C).gates.length := by omega
          have hk_eq : k = x.length + (i + 1) := by omega
          have hrem : remap n j w k = x.length + i := by
            simp only [remap]
            rw [if_neg (by omega), if_neg (by omega)]
            omega
          rw [hrem, wires_gate_val (deleteGate n j w C) x i hi_lt hrb'] at htrue
          rw [hk_eq, wires_gate_val C x (i + 1) (by omega) hrbC]
          rw [deleteGate_gateAt_ge n j w C i hi_ge hi_lt hj] at htrue
          have hop : (gateAt C (i + 1)).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
            have hmem : gateAt C (i + 1) ∈ C.gates := by
              have hi1 : i + 1 < C.gates.length := by omega
              simp [gateAt, List.getD_eq_getElem?_getD, hi1]
            exact (hm _ hmem).1
          refine eval_op_mono _ hop _ _ (by simp [remapGate]) ?_ htrue
          intro idx hidx1 hidx2 h1
          simp only [remapGate, List.map_map, List.getElem_map, Function.comp_apply] at h1
          simp only [List.getElem_map]
          have hmem_in : (gateAt C (i + 1)).inputs[idx]'(by simp [remapGate] at hidx1; exact hidx1) ∈
              (gateAt C (i + 1)).inputs := List.getElem_mem _
          have halt : (gateAt C (i + 1)).inputs[idx]'(by simp [remapGate] at hidx1; exact hidx1) < k := by
            have := hrb (i + 1) (by omega) _ hmem_in
            omega
          exact ih _ halt h1
        · have hge : ((deleteGate n j w C).wires x).length ≤ remap n j w k := by
            rw [wires_len, hx, hlenD]
            unfold remap
            rw [if_neg hlt, if_neg heq]
            omega
          rw [getD_ge_len _ _ hge] at htrue
          exact absurd htrue (by decide)

lemma deleteGate_wires_ge (n j w : ℕ) (C : Circuit) (x : List Bool)
    (hx : x.length = n) (hj : j < C.gates.length) (hw : w < n + j)
    (hm : Monotone2 C) (hrb : ReadsBack n C)
    (hstep : (C.wires x).getD (n + j) false = true → (C.wires x).getD w false = true) :
    ∀ k : ℕ, (C.wires x).getD k false = true →
      ((deleteGate n j w C).wires x).getD (remap n j w k) false = true := by
  have hrb' : ReadsBack x.length (deleteGate n j w C) := by
    rw [hx]; exact deleteGate_readsBack n j w C hj hw hrb
  have hrbC : ReadsBack x.length C := by rw [hx]; exact hrb
  have hlenD := deleteGate_len n j w C hj
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro htrue
    by_cases hlt : k < n + j
    · have hrem : remap n j w k = k := by simp [remap, hlt]
      rw [hrem, deleteGate_wires_prefix n j w C x hx hj k hlt]
      exact htrue
    · by_cases heq : k = n + j
      · subst heq
        have hrem : remap n j w (n + j) = w := by simp [remap]
        rw [hrem, deleteGate_wires_prefix n j w C x hx hj w hw]
        exact hstep htrue
      · by_cases hltC : k < n + C.gates.length
        · have hgt : n + j < k := by omega
          let i := k - n - 1
          have hi_ge : j ≤ i := by omega
          have hi_lt : i < (deleteGate n j w C).gates.length := by omega
          have hk_eq : k = x.length + (i + 1) := by omega
          have hrem : remap n j w k = x.length + i := by
            simp only [remap]
            rw [if_neg (by omega), if_neg (by omega)]
            omega
          rw [hk_eq, wires_gate_val C x (i + 1) (by omega) hrbC] at htrue
          rw [hrem, wires_gate_val (deleteGate n j w C) x i hi_lt hrb']
          rw [deleteGate_gateAt_ge n j w C i hi_ge hi_lt hj]
          have hop : (gateAt C (i + 1)).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
            have hmem : gateAt C (i + 1) ∈ C.gates := by
              have hi1 : i + 1 < C.gates.length := by omega
              simp [gateAt, List.getD_eq_getElem?_getD, hi1]
            exact (hm _ hmem).1
          refine eval_op_mono _ hop _ _ (by simp [remapGate]) ?_ htrue
          intro idx hidx1 hidx2 h1
          simp only [List.getElem_map] at h1
          simp only [remapGate, List.map_map, List.getElem_map, Function.comp_apply]
          have hmem_in : (gateAt C (i + 1)).inputs[idx]'(by simp at hidx1; exact hidx1) ∈
              (gateAt C (i + 1)).inputs := List.getElem_mem _
          have halt : (gateAt C (i + 1)).inputs[idx]'(by simp at hidx1; exact hidx1) < k := by
            have := hrb (i + 1) (by omega) _ hmem_in
            omega
          exact ih _ halt h1
        · have hge : (C.wires x).length ≤ k := by
            rw [wires_len, hx]; omega
          rw [getD_ge_len _ _ hge] at htrue
          exact absurd htrue (by decide)

lemma main_elim (n : ℕ) (P : Bool → List Bool → Prop)
    (hlenP : ∀ b x, P b x → x.length = n)
    (C : Circuit) (hm : Monotone2 C) (hrb : ReadsBack n C)
    (heval : ∀ b x, P b x → C.eval x = b) :
    (∃ C' : Circuit, (Monotone2 C' ∧ ReadsBack n C' ∧ ∀ b x, P b x → C'.eval x = b) ∧ C'.size < C.size) ∨
    (∀ j < C.gates.length,
      ∀ w ∈ (gateAt C j).inputs, ∃ x : List Bool, P (!(gateAt C j).op.eval []) x ∧
        (C.wires x).getD w false = !(!(gateAt C j).op.eval []) ∧
        (C.wires x).getD (n + j) false = !(gateAt C j).op.eval []) := by
  by_cases h5 : ∀ j < C.gates.length,
      ∀ w ∈ (gateAt C j).inputs, ∃ x : List Bool, P (!(gateAt C j).op.eval []) x ∧
        (C.wires x).getD w false = !(!(gateAt C j).op.eval []) ∧
        (C.wires x).getD (n + j) false = !(gateAt C j).op.eval []
  · exact Or.inr h5
  · left
    push Not at h5
    obtain ⟨j, hj, w, hw_in, hno⟩ := h5
    have hw_lt : w < n + j := hrb j hj w hw_in
    let C' := deleteGate n j w C
    refine ⟨C', ⟨deleteGate_monotone2 n j w C hm, deleteGate_readsBack n j w C hj hw_lt hrb, ?_⟩, ?_⟩
    · intro b x hPx
      have hxlen : x.length = n := hlenP b x hPx
      have hrbC : ReadsBack x.length C := by rw [hxlen]; exact hrb
      have hgate_mem : gateAt C j ∈ C.gates := by
        simp [gateAt, List.getD_eq_getElem?_getD, hj]
      rcases (hm _ hgate_mem).1 with hand | hor
      · have hb0 : (!(gateAt C j).op.eval []) = false := by rw [hand]; rfl
        have hstep_ge : (C.wires x).getD (n + j) false = true → (C.wires x).getD w false = true := by
          intro ht
          rw [← hxlen, wires_gate_val C x j hj hrbC, hand] at ht
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at ht
          exact ht ((C.wires x).getD w false) ⟨w, hw_in, rfl⟩
        cases b
        · have hstep_le : (C.wires x).getD w false = true → (C.wires x).getD (n + j) false = true := by
            intro hwt
            have h1 := hno x (hb0.symm ▸ hPx)
            rw [hb0] at h1
            cases hnj : (C.wires x).getD (n + j) false
            · exact absurd hnj (h1 hwt)
            · rfl
          have hCe : (C.wires x).getD C.output false = false := heval false x hPx
          cases hC'e : C'.eval x
          · rfl
          · have hCtrue := deleteGate_wires_le n j w C x hxlen hj hw_lt hm hrb hstep_le C.output hC'e
            rw [hCe] at hCtrue
            exact absurd hCtrue (by decide)
        · have hCe : (C.wires x).getD C.output false = true := heval true x hPx
          exact deleteGate_wires_ge n j w C x hxlen hj hw_lt hm hrb hstep_ge C.output hCe
      · rw [Set.mem_singleton_iff] at hor
        have hb0 : (!(gateAt C j).op.eval []) = true := by rw [hor]; rfl
        have hstep_le : (C.wires x).getD w false = true → (C.wires x).getD (n + j) false = true := by
          intro hwt
          rw [← hxlen, wires_gate_val C x j hj hrbC, hor]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          exact ⟨true, ⟨w, hw_in, hwt⟩, rfl⟩
        cases b
        · have hCe : (C.wires x).getD C.output false = false := heval false x hPx
          cases hC'e : C'.eval x
          · rfl
          · have hCtrue := deleteGate_wires_le n j w C x hxlen hj hw_lt hm hrb hstep_le C.output hC'e
            rw [hCe] at hCtrue
            exact absurd hCtrue (by decide)
        · have hstep_ge : (C.wires x).getD (n + j) false = true → (C.wires x).getD w false = true := by
            intro ht
            have h1 := hno x (hb0.symm ▸ hPx)
            rw [hb0] at h1
            cases hwt : (C.wires x).getD w false
            · exact absurd ht (h1 hwt)
            · rfl
          have hCe : (C.wires x).getD C.output false = true := heval true x hPx
          exact deleteGate_wires_ge n j w C x hxlen hj hw_lt hm hrb hstep_ge C.output hCe
    · show (deleteGate n j w C).gates.length < C.gates.length
      rw [deleteGate_len n j w C hj]
      omega

end PEqualNP.Outside.L_meta_2245

theorem PEqualNP.Outside.L_meta_2245 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 ∧ x5.size < x4.size; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ x6 < x5.gates.length,     have x8 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6;     have x9 : Bool := !x8.op.eval [];     ∀ x10 ∈ x8.inputs, ∃ (x12 : List Bool), x2 x9 x12 ∧ (x5.wires x12).getD x10 Bool.false = !x9 ∧ (x5.wires x12).getD ((26 : ℕ) + x6) Bool.false = x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x4 x6 ∨ x5 x6 := by
  intro x1 x2 x3 x4 x5 C hC
  refine PEqualNP.Outside.L_meta_2245.main_elim 26 x2 ?_ C hC.1 hC.2.1 hC.2.2
  intro b x hx
  cases b
  · simp only [x2, Bool.false_eq_true, ↓reduceIte] at hx
    obtain ⟨_, _, _, rfl⟩ := hx
    simp
  · simp only [x2, ↓reduceIte] at hx
    obtain ⟨_, _, _, rfl⟩ := hx
    simp
