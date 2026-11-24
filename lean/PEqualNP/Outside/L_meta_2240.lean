import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2240

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK

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

lemma eval_input_lt (gs : List Gate) (N : ℕ) (f : Fin N → Bool) (p : Fin N) :
    (gs.foldl step (List.ofFn f)).getD p.val false = f p := by
  have hlt : p.val < (List.ofFn f).length := by simp
  rw [foldl_step_getD_lt gs (List.ofFn f) p.val hlt]
  simp [List.getD_eq_getElem?_getD]

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

lemma wires_mono (N : ℕ) (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin N → Bool) (hxy : ∀ p : Fin N, x p = true → y p = true) :
    ∀ w : ℕ, (gs.foldl step (List.ofFn x)).getD w false = true →
      (gs.foldl step (List.ofFn y)).getD w false = true := by
  have key : ∀ (gs0 : List Gate) (wx wy : List Bool),
      (∀ g ∈ gs0, g.op = GateOp.and ∨ g.op = GateOp.or) →
      wx.length = wy.length →
      (∀ w : ℕ, wx.getD w false = true → wy.getD w false = true) →
      ∀ w : ℕ, (gs0.foldl step wx).getD w false = true → (gs0.foldl step wy).getD w false = true := by
    intro gs0
    induction gs0 with
    | nil => intro wx wy _ _ hle w hw; exact hle w hw
    | cons g gs0 ih =>
      intro wx wy hm hlen hle
      apply ih (step wx g) (step wy g) (fun g' hg' => hm g' (List.mem_cons_of_mem g hg'))
      · simp [step, hlen]
      · intro w hw
        by_cases hlt : w < wx.length
        · simp only [step] at hw ⊢
          rw [getD_append_left_lt wx _ w hlt] at hw
          rw [getD_append_left_lt wy _ w (by omega)]
          exact hle w hw
        · by_cases heq : w = wx.length
          · subst heq
            simp only [step] at hw ⊢
            rw [getD_append_self] at hw
            rw [hlen, getD_append_self]
            refine mono_eval_op g.op (hm g List.mem_cons_self) _ _ (by simp) ?_ hw
            intro k hk1 hk2 hk
            simp only [List.getElem_map] at hk ⊢
            exact hle _ hk
          · have hge : (step wx g).length ≤ w := by
              simp only [step, List.length_append, List.length_cons, List.length_nil]
              omega
            rw [getD_ge_len _ _ hge] at hw
            exact absurd hw (by decide)
  apply key gs (List.ofFn x) (List.ofFn y) hmono (by simp)
  intro w hw
  by_cases hlt : w < N
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true, Option.getD_some] at hw ⊢
    exact hxy ⟨w, hlt⟩ hw
  · have hge : (List.ofFn x).length ≤ w := by simp; omega
    rw [getD_ge_len _ _ hge] at hw
    exact absurd hw (by decide)

def lpStep (w : List (Bool × Bool)) (g : Gate) : List (Bool × Bool) :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  w ++ [match g.op with
    | GateOp.or => (ins.any (·.1), ins.any (·.2))
    | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
          (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
    | _ => (false, false)]

lemma lpStep_len (gs : List Gate) (w : List (Bool × Bool)) :
    (gs.foldl lpStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, lpStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma lp_getD_append_left (w t : List (Bool × Bool)) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i (false, false) = w.getD i (false, false) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma lp_getD_append_self (w : List (Bool × Bool)) (b : Bool × Bool) :
    (w ++ [b]).getD w.length (false, false) = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma lp_getD_ge_len (w : List (Bool × Bool)) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i (false, false) = (false, false) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_lpStep_getD_lt (gs : List Gate) (w : List (Bool × Bool)) (i : ℕ) (hi : i < w.length) :
    (gs.foldl lpStep w).getD i (false, false) = w.getD i (false, false) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : i < (lpStep w g).length := by
      simp only [lpStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (lpStep w g) hlen]
    exact lp_getD_append_left w _ i hi

lemma linearParts_eq_foldl (C : Circuit) (isLin : ℕ → Bool) (x : List Bool) :
    linearParts C isLin x =
      C.gates.foldl lpStep
        ((x.zipIdx).map fun (b, i) => if isLin i then (false, b) else (b, false)) := rfl

lemma linearParts_len (C : Circuit) (isLin : ℕ → Bool) (x : List Bool) :
    (linearParts C isLin x).length = x.length + C.gates.length := by
  rw [linearParts_eq_foldl, lpStep_len]
  simp

lemma linearParts_input (C : Circuit) (isLin : ℕ → Bool) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (linearParts C isLin x).getD i (false, false) =
      if isLin i then (false, x.getD i false) else (x.getD i false, false) := by
  rw [linearParts_eq_foldl]
  have hlen : ((x.zipIdx).map fun (b, i) => if isLin i then (false, b) else (b, false)).length = x.length := by
    simp
  rw [foldl_lpStep_getD_lt _ _ i (by omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, hi,
    List.getElem?_eq_getElem, Option.map_some, Option.getD_some, zero_add]

lemma linearParts_gate (C : Circuit) (isLin : ℕ → Bool) (x : List Bool) (j : ℕ)
    (hj : j < C.gates.length) (hrb : ReadsBack x.length C) :
    let lp := linearParts C isLin x
    let g := gateAt C j
    let ins := g.inputs.map fun a => lp.getD a (false, false)
    lp.getD (x.length + j) (false, false) =
      match g.op with
      | GateOp.or => (ins.any (·.1), ins.any (·.2))
      | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
            (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
      | _ => (false, false) := by
  rw [linearParts_eq_foldl]
  set init := (x.zipIdx).map fun (b, i) => if isLin i then (false, b) else (b, false) with hinit_def
  have hinit_len : init.length = x.length := by simp [hinit_def]
  have hget : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = gateAt C j :: C.gates.drop (j + 1) := by
      rw [hget, List.drop_eq_getElem_cons hj]
    rw [h2] at h1
    exact h1.symm
  set pref := (C.gates.take j).foldl lpStep init with hpref_def
  have hpref_len : pref.length = x.length + j := by
    rw [hpref_def, lpStep_len, hinit_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hfold : C.gates.foldl lpStep init =
      (C.gates.drop (j + 1)).foldl lpStep (lpStep pref (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons, ← hpref_def]
  have hlt_step : x.length + j < (lpStep pref (gateAt C j)).length := by
    simp only [lpStep, List.length_append, List.length_cons, List.length_nil, hpref_len]
    omega
  dsimp only
  rw [hfold, foldl_lpStep_getD_lt _ _ _ hlt_step]
  have hself : (lpStep pref (gateAt C j)).getD (x.length + j) (false, false) =
      match (gateAt C j).op with
      | GateOp.or => ((gateAt C j).inputs.map (fun i => pref.getD i (false, false)) |>.any (·.1),
                      (gateAt C j).inputs.map (fun i => pref.getD i (false, false)) |>.any (·.2))
      | GateOp.and => ((gateAt C j).inputs.map (fun i => pref.getD i (false, false))).foldl
            (fun (acc : Bool × Bool) p => (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
      | _ => (false, false) := by
    rw [← hpref_len]
    exact lp_getD_append_self pref _
  rw [hself]
  have hmap_eq : (gateAt C j).inputs.map (fun i => pref.getD i (false, false)) =
      (gateAt C j).inputs.map (fun a => ((C.gates.drop (j + 1)).foldl lpStep (lpStep pref (gateAt C j))).getD a (false, false)) := by
    apply List.map_congr_left
    intro a ha
    have halt : a < pref.length := by rw [hpref_len]; exact hrb j hj a ha
    have ha_lt2 : a < (lpStep pref (gateAt C j)).length := by
      simp only [lpStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [foldl_lpStep_getD_lt _ _ _ ha_lt2]
    simp only [lpStep]
    exact (lp_getD_append_left pref _ a halt).symm
  rw [hmap_eq]

lemma linearParts_le_wires (C : Circuit) (isLin : ℕ → Bool) (x : List Bool) :
    ∀ i : ℕ, ((linearParts C isLin x).getD i (false, false)).1 = true ∨
      ((linearParts C isLin x).getD i (false, false)).2 = true →
      (C.wires x).getD i false = true := by
  rw [linearParts_eq_foldl, wires_eq_foldl]
  have key : ∀ (gs : List Gate) (lp : List (Bool × Bool)) (w : List Bool),
      lp.length = w.length →
      (∀ i, (lp.getD i (false, false)).1 = true ∨ (lp.getD i (false, false)).2 = true →
        w.getD i false = true) →
      ∀ i, ((gs.foldl lpStep lp).getD i (false, false)).1 = true ∨
        ((gs.foldl lpStep lp).getD i (false, false)).2 = true →
        (gs.foldl step w).getD i false = true := by
    intro gs
    induction gs with
    | nil => intro lp w _ hle i hi; exact hle i hi
    | cons g gs ih =>
      intro lp w hlen hle
      apply ih (lpStep lp g) (step w g) (by simp [lpStep, step, hlen])
      intro i hi
      by_cases hlt : i < lp.length
      · simp only [lpStep] at hi
        simp only [step]
        rw [lp_getD_append_left lp _ i hlt] at hi
        rw [getD_append_left_lt w _ i (by omega)]
        exact hle i hi
      · by_cases heq : i = lp.length
        · subst heq
          simp only [lpStep] at hi
          simp only [step]
          rw [lp_getD_append_self] at hi
          rw [hlen, getD_append_self]
          cases hg : g.op with
          | or =>
            simp only [hg, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
            rcases hi with ⟨p, ⟨a, ha, rfl⟩, hp⟩ | ⟨p, ⟨a, ha, rfl⟩, hp⟩
            · exact ⟨true, ⟨a, ha, hle a (Or.inl hp)⟩, rfl⟩
            · exact ⟨true, ⟨a, ha, hle a (Or.inr hp)⟩, rfl⟩
          | and =>
            simp only [hg, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
            have hfold_and : ∀ (l : List ℕ) (acc : Bool × Bool),
                (acc.1 = true ∨ acc.2 = true → True) →
                ((l.map fun a => lp.getD a (false, false)).foldl
                  (fun (acc : Bool × Bool) p => (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) acc).1 = true ∨
                ((l.map fun a => lp.getD a (false, false)).foldl
                  (fun (acc : Bool × Bool) p => (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) acc).2 = true →
                ∀ a ∈ l, w.getD a false = true := by
              intro l
              induction l with
              | nil => intro _ _ _ _ ha; cases ha
              | cons u us ihu =>
                intro acc _ hres a ha
                simp only [List.map_cons, List.foldl_cons] at hres
                have hnext : ∀ (l' : List (Bool × Bool)) (a0 : Bool × Bool),
                    (l'.foldl (fun (acc : Bool × Bool) p => (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) a0).1 = true ∨
                    (l'.foldl (fun (acc : Bool × Bool) p => (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) a0).2 = true →
                    a0.1 = true ∨ a0.2 = true := by
                  intro l'
                  induction l' with
                  | nil => intro a0 h0; exact h0
                  | cons q qs ihq =>
                    intro a0 h0
                    have h1 := ihq _ h0
                    rcases h1 with h1 | h1
                    · simp only [Bool.and_eq_true] at h1; exact Or.inl h1.1
                    · simp only [Bool.or_eq_true, Bool.and_eq_true] at h1
                      rcases h1 with ⟨h1a, _⟩ | ⟨h1a, _⟩
                      · exact Or.inl h1a
                      · exact Or.inr h1a
                rcases List.mem_cons.mp ha with rfl | haus
                · have h1 := hnext _ _ hres
                  rcases h1 with h1 | h1
                  · simp only [Bool.and_eq_true] at h1; exact hle a (Or.inl h1.2)
                  · simp only [Bool.or_eq_true, Bool.and_eq_true] at h1
                    rcases h1 with ⟨_, h1b⟩ | ⟨_, h1b⟩
                    · exact hle a (Or.inr h1b)
                    · exact hle a (Or.inl h1b)
                · exact ihu _ (fun _ => trivial) hres a haus
            intro b hb
            obtain ⟨a, ha, rfl⟩ := hb
            exact hfold_and g.inputs (true, false) (fun _ => trivial) hi a ha
          | not => simp [hg] at hi
          | mod m => simp [hg] at hi
          | maj => simp [hg] at hi
        · have hge : (lpStep lp g).length ≤ i := by
            simp only [lpStep, List.length_append, List.length_cons, List.length_nil]
            omega
          rw [lp_getD_ge_len _ _ hge] at hi
          simp at hi
  apply key C.gates _ x (by simp)
  intro i hi
  by_cases hlt : i < x.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx, hlt,
      List.getElem?_eq_getElem, Option.map_some, Option.getD_some, zero_add] at hi ⊢
    cases hlin : isLin i <;> simp [hlin] at hi <;> exact hi
  · have hge : ((x.zipIdx).map fun (b, i) => if isLin i then (false, b) else (b, false)).length ≤ i := by
      simp; omega
    rw [lp_getD_ge_len _ _ hge] at hi
    simp at hi

lemma card_image_merge {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ) (c1 c2 : ℕ) :
    (S.image f).card ≤ (S.image (fun x => if f x = c1 then c2 else f x)).card + 1 := by
  let g (x : α) : ℕ := if f x = c1 then c2 else f x
  have hsub : S.image f ⊆ insert c1 (S.image g) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    by_cases h : f x = c1
    · rw [h]; exact Finset.mem_insert_self c1 _
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, by simp [g, h]⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le c1 (S.image g))

lemma monoOrCount (N : ℕ) (R : Fin N → Fin N → Prop) [DecidableRel R]
    (gs : List Gate) (out : Fin N → ℕ)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hrb : ReadsBack N ⟨gs, 0⟩)
    (hnoC4 : ∀ l1 l2 : Fin N, l1 ≠ l2 → (Finset.univ.filter (fun p => R p l1 ∧ R p l2)).card ≤ 1)
    (hsound : ∀ l : Fin N, (gs.foldl step (List.ofFn fun p : Fin N => decide (¬ R p l))).getD (out l) false = false)
    (Ehit : Fin N → Finset (Fin N))
    (hEhit : ∀ l : Fin N, ∀ p ∈ Ehit l,
      (gs.foldl step (List.ofFn fun v : Fin N => decide (v = p))).getD (out l) false = true) :
    ∑ l : Fin N, (Ehit l).card ≤ gs.length + N := by
  classical
  let evalW (w : ℕ) (x : Fin N → Bool) : Bool := (gs.foldl step (List.ofFn x)).getD w false
  let xCol (l : Fin N) : Fin N → Bool := fun p => decide (¬ R p l)
  let ePt (p : Fin N) : Fin N → Bool := fun v => decide (v = p)
  let T (w : ℕ) : Finset (Fin N) := Finset.univ.filter (fun p : Fin N => evalW w (ePt p) = true)
  let A (l : Fin N) : Finset (Fin gs.length) :=
    Finset.univ.filter (fun j : Fin gs.length =>
      (gs.get j).op = GateOp.or ∧ evalW (N + j.val) (xCol l) = false ∧ 2 ≤ (T (N + j.val)).card)
  have hT_sub : ∀ l w, evalW w (xCol l) = false → ∀ p ∈ T w, R p l := by
    intro l w hwf p hp
    have hpt : evalW w (ePt p) = true := (Finset.mem_filter.mp hp).2
    by_contra hnot
    have hle : ∀ v : Fin N, ePt p v = true → xCol l v = true := by
      intro v hv
      simp only [ePt, decide_eq_true_eq] at hv
      subst hv
      simp [xCol, hnot]
    have hwt := wires_mono N gs (fun g hg => (hmono g hg).1) (ePt p) (xCol l) hle w hpt
    change evalW w (xCol l) = true at hwt
    rw [hwf] at hwt
    exact absurd hwt (by decide)
  have hA_disj : ∀ l1 l2 : Fin N, l1 ≠ l2 → Disjoint (A l1) (A l2) := by
    intro l1 l2 hne
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := (Finset.mem_filter.mp hj1).2
    have h2 := (Finset.mem_filter.mp hj2).2
    have hsub : T (N + j.val) ⊆ Finset.univ.filter (fun p => R p l1 ∧ R p l2) := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hT_sub l1 _ h1.2.1 p hp, hT_sub l2 _ h2.2.1 p hp⟩
    have hc := Finset.card_le_card hsub
    have hle1 := hnoC4 l1 l2 hne
    omega
  have hper_line : ∀ l : Fin N, (Ehit l).card ≤ (A l).card + 1 := by
    intro l
    have hE_sub_T : Ehit l ⊆ T (out l) := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hEhit l p hp⟩
    let prefA (k : ℕ) : Finset (Fin gs.length) := (A l).filter (fun j => j.val < k)
    have hstep : ∀ k ≤ gs.length,
        ∃ col : Fin N → ℕ,
          (Ehit l).card ≤ ((Ehit l).image col).card + (prefA k).card ∧
          ∀ w < N + k, evalW w (xCol l) = false →
            ∀ p1 ∈ T w, ∀ p2 ∈ T w, col p1 = col p2 := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨fun p => p.val, ?_, ?_⟩
        · rw [Finset.card_image_of_injective _ Fin.val_injective]
          omega
        · intro w hw _ p1 hp1 p2 hp2
          have h1 : evalW w (ePt p1) = true := (Finset.mem_filter.mp hp1).2
          have h2 : evalW w (ePt p2) = true := (Finset.mem_filter.mp hp2).2
          have he1 : evalW w (ePt p1) = ePt p1 ⟨w, by omega⟩ := eval_input_lt gs N (ePt p1) ⟨w, by omega⟩
          have he2 : evalW w (ePt p2) = ePt p2 ⟨w, by omega⟩ := eval_input_lt gs N (ePt p2) ⟨w, by omega⟩
          rw [he1] at h1
          rw [he2] at h2
          simp only [ePt, decide_eq_true_eq] at h1 h2
          rw [← h1, ← h2]
      | succ k ih =>
        intro hk
        obtain ⟨col, hcard, hconst⟩ := ih (by omega)
        have hpref_sub : prefA k ⊆ prefA (k + 1) := by
          intro j hj
          have hjm := Finset.mem_filter.mp hj
          exact Finset.mem_filter.mpr ⟨hjm.1, by omega⟩
        have hpref_le : (prefA k).card ≤ (prefA (k + 1)).card := Finset.card_le_card hpref_sub
        let j : Fin gs.length := ⟨k, by omega⟩
        let w : ℕ := N + k
        have hget : gateAt ⟨gs, 0⟩ j.val = gs.get j := by
          simp [gateAt, List.getD_eq_getElem?_getD, j.isLt]
        by_cases hcond : evalW w (xCol l) = false ∧ 2 ≤ (T w).card
        · rcases hcond with ⟨hwf, hTw2⟩
          have hrb' : ReadsBack (List.ofFn (xCol l)).length ⟨gs, 0⟩ := by simp; exact hrb
          have hval_x : evalW w (xCol l) =
              (gs.get j).op.eval ((gs.get j).inputs.map fun a => evalW a (xCol l)) := by
            have := wires_gate_val ⟨gs, 0⟩ (List.ofFn (xCol l)) j.val j.isLt hrb'
            simp only [List.length_ofFn, hget] at this
            simpa [evalW, wires_eq_foldl, w, j] using this
          have hval_p : ∀ p : Fin N, evalW w (ePt p) =
              (gs.get j).op.eval ((gs.get j).inputs.map fun a => evalW a (ePt p)) := by
            intro p
            have hrb_p : ReadsBack (List.ofFn (ePt p)).length ⟨gs, 0⟩ := by simp; exact hrb
            have := wires_gate_val ⟨gs, 0⟩ (List.ofFn (ePt p)) j.val j.isLt hrb_p
            simp only [List.length_ofFn, hget] at this
            simpa [evalW, wires_eq_foldl, w, j] using this
          have hrb_j : ∀ a ∈ (gs.get j).inputs, a < N + k := by
            intro a ha
            have := hrb j.val j.isLt a (by rwa [hget])
            simpa [j] using this
          have hgj_mem : gs.get j ∈ gs := List.get_mem gs j
          rcases (hmono (gs.get j) hgj_mem).1 with hand | hor
          · refine ⟨col, by omega, ?_⟩
            intro u hu huf p1 hp1 p2 hp2
            by_cases hult : u < N + k
            · exact hconst u hult huf p1 hp1 p2 hp2
            · have hueq : u = w := by simp [w]; omega
              subst hueq
              have hex : ∃ a ∈ (gs.get j).inputs, evalW a (xCol l) = false := by
                have h1 := hval_x
                rw [hwf, hand] at h1
                have h2 := h1.symm
                simp only [GateOp.eval, List.all_eq_false, List.mem_map, id_eq] at h2
                obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := h2
                exact ⟨a, ha, Bool.eq_false_iff.mpr hb⟩
              obtain ⟨a, ha_in, ha_f⟩ := hex
              have hsubT : T w ⊆ T a := by
                intro p hp
                have hpt : evalW w (ePt p) = true := (Finset.mem_filter.mp hp).2
                rw [hval_p p, hand] at hpt
                simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hpt
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpt _ ⟨a, ha_in, rfl⟩⟩
              exact hconst a (hrb_j a ha_in) ha_f p1 (hsubT hp1) p2 (hsubT hp2)
          · have hall_f : ∀ a ∈ (gs.get j).inputs, evalW a (xCol l) = false := by
              intro a ha
              have h1 := hval_x
              rw [hwf, hor] at h1
              have h2 := h1.symm
              simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq] at h2
              exact Bool.eq_false_iff.mpr (h2 _ ⟨a, ha, rfl⟩)
            have hlen2 : (gs.get j).inputs.length ≤ 2 := (hmono (gs.get j) hgj_mem).2
            match hinputs : (gs.get j).inputs with
            | [] =>
              have hT0 : T w = ∅ := by
                ext p
                simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                rw [hval_p p, hor, hinputs]
                simp [GateOp.eval]
              rw [hT0] at hTw2; simp at hTw2
            | [a] =>
              have ha_in : a ∈ (gs.get j).inputs := by rw [hinputs]; simp
              have hsubT : T w ⊆ T a := by
                intro p hp
                have hpt : evalW w (ePt p) = true := (Finset.mem_filter.mp hp).2
                rw [hval_p p, hor, hinputs] at hpt
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false] at hpt
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpt⟩
              refine ⟨col, by omega, ?_⟩
              intro u hu huf p1 hp1 p2 hp2
              by_cases hult : u < N + k
              · exact hconst u hult huf p1 hp1 p2 hp2
              · have hueq : u = w := by simp [w]; omega
                subst hueq
                exact hconst a (hrb_j a ha_in) (hall_f a ha_in) p1 (hsubT hp1) p2 (hsubT hp2)
            | [a, b] =>
              have ha_in : a ∈ (gs.get j).inputs := by rw [hinputs]; simp
              have hb_in : b ∈ (gs.get j).inputs := by rw [hinputs]; simp
              have hsubT : T w ⊆ T a ∪ T b := by
                intro p hp
                have hpt : evalW w (ePt p) = true := (Finset.mem_filter.mp hp).2
                rw [hval_p p, hor, hinputs] at hpt
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                  id_eq, Bool.or_false, Bool.or_eq_true] at hpt
                rcases hpt with ha' | hb'
                · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ p, ha'⟩)
                · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hb'⟩)
              by_cases hTa : (T a).Nonempty
              · by_cases hTb : (T b).Nonempty
                · obtain ⟨pa, hpa⟩ := hTa
                  obtain ⟨pb, hpb⟩ := hTb
                  let col' : Fin N → ℕ := fun p => if col p = col pa then col pb else col p
                  have hj_mem : j ∈ prefA (k + 1) := by
                    refine Finset.mem_filter.mpr ⟨?_, by simp [j]⟩
                    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hor, hwf, hTw2⟩
                  have hj_not : j ∉ prefA k := by
                    intro hjm
                    have := (Finset.mem_filter.mp hjm).2
                    simp [j] at this
                  have hsub_ins : insert j (prefA k) ⊆ prefA (k + 1) := by
                    intro x hx
                    rcases Finset.mem_insert.mp hx with rfl | hxk
                    · exact hj_mem
                    · exact hpref_sub hxk
                  have hcard_pref : (prefA k).card + 1 ≤ (prefA (k + 1)).card := by
                    have h1 := Finset.card_le_card hsub_ins
                    rw [Finset.card_insert_of_notMem hj_not] at h1
                    exact h1
                  have hmerge := card_image_merge (Ehit l) col (col pa) (col pb)
                  refine ⟨col', ?_, ?_⟩
                  · dsimp only [col']
                    omega
                  · intro u hu huf p1 hp1 p2 hp2
                    by_cases hult : u < N + k
                    · have hpeq := hconst u hult huf p1 hp1 p2 hp2
                      simp [col', hpeq]
                    · have hueq : u = w := by simp [w]; omega
                      subst hueq
                      have hcol_pb : ∀ p ∈ T w, col' p = col pb := by
                        intro p hp
                        rcases Finset.mem_union.mp (hsubT hp) with hpa' | hpb'
                        · have heq := hconst a (hrb_j a ha_in) (hall_f a ha_in) p hpa' pa hpa
                          simp [col', heq]
                        · have heq := hconst b (hrb_j b hb_in) (hall_f b hb_in) p hpb' pb hpb
                          simp [col', heq]
                      rw [hcol_pb p1 hp1, hcol_pb p2 hp2]
                · rw [Finset.not_nonempty_iff_eq_empty] at hTb
                  have hsubTa : T w ⊆ T a := by simpa [hTb] using hsubT
                  refine ⟨col, by omega, ?_⟩
                  intro u hu huf p1 hp1 p2 hp2
                  by_cases hult : u < N + k
                  · exact hconst u hult huf p1 hp1 p2 hp2
                  · have hueq : u = w := by simp [w]; omega
                    subst hueq
                    exact hconst a (hrb_j a ha_in) (hall_f a ha_in) p1 (hsubTa hp1) p2 (hsubTa hp2)
              · rw [Finset.not_nonempty_iff_eq_empty] at hTa
                have hsubTb : T w ⊆ T b := by simpa [hTa] using hsubT
                refine ⟨col, by omega, ?_⟩
                intro u hu huf p1 hp1 p2 hp2
                by_cases hult : u < N + k
                · exact hconst u hult huf p1 hp1 p2 hp2
                · have hueq : u = w := by simp [w]; omega
                  subst hueq
                  exact hconst b (hrb_j b hb_in) (hall_f b hb_in) p1 (hsubTb hp1) p2 (hsubTb hp2)
            | _ :: _ :: _ :: _ =>
              have hlen_gt : 3 ≤ (gs.get j).inputs.length := by rw [hinputs]; simp
              have : (gs.get j).inputs.length ≤ 2 := hlen2
              omega
        · refine ⟨col, by omega, ?_⟩
          intro u hu huf p1 hp1 p2 hp2
          by_cases hult : u < N + k
          · exact hconst u hult huf p1 hp1 p2 hp2
          · have hueq : u = w := by simp [w]; omega
            subst hueq
            have hle1 : (T w).card ≤ 1 := by
              by_contra hgt
              exact hcond ⟨huf, by omega⟩
            have hpeq : p1 = p2 := Finset.card_le_one.mp hle1 p1 hp1 p2 hp2
            rw [hpeq]
    by_cases hout_lt : out l < N + gs.length
    · obtain ⟨col, hcard, hconst⟩ := hstep gs.length (le_refl _)
      have hpref_sub_A : prefA gs.length ⊆ A l := Finset.filter_subset _ _
      have hpref_card : (prefA gs.length).card ≤ (A l).card := Finset.card_le_card hpref_sub_A
      have himg_le1 : ((Ehit l).image col).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro y1 hy1 y2 hy2
        rcases Finset.mem_image.mp hy1 with ⟨p1, hp1, rfl⟩
        rcases Finset.mem_image.mp hy2 with ⟨p2, hp2, rfl⟩
        exact hconst (out l) hout_lt (hsound l) p1 (hE_sub_T hp1) p2 (hE_sub_T hp2)
      omega
    · have hT0 : T (out l) = ∅ := by
        ext p
        simp only [T, evalW, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        have hge : (gs.foldl step (List.ofFn (ePt p))).length ≤ out l := by
          rw [foldl_step_len, List.length_ofFn]; omega
        rw [getD_ge_len _ _ hge]
        decide
      have hE0 : Ehit l = ∅ := Finset.subset_empty.mp (hT0 ▸ hE_sub_T)
      rw [hE0]
      simp
  have hsum_le : ∑ l : Fin N, (Ehit l).card ≤ (∑ l : Fin N, (A l).card) + N := by
    calc ∑ l : Fin N, (Ehit l).card
        ≤ ∑ l : Fin N, ((A l).card + 1) := Finset.sum_le_sum fun l _ => hper_line l
      _ = (∑ l : Fin N, (A l).card) + ∑ _l : Fin N, 1 := Finset.sum_add_distrib
      _ = (∑ l : Fin N, (A l).card) + N := by simp
  have hsumA_le : ∑ l : Fin N, (A l).card ≤ gs.length := by
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N))) A := by
      intro l1 _ l2 _ hne
      exact hA_disj l1 l2 hne
    rw [← Finset.card_biUnion hdisj]
    have hle := Finset.card_le_card (Finset.subset_univ (Finset.univ.biUnion A))
    simpa using hle
  omega

def isLinFn (N : ℕ) (swap : Bool) (w : ℕ) : Bool :=
  if swap then !decide (N ≤ w) else decide (N ≤ w)

def nonLinIdx (N : ℕ) (swap : Bool) (p : Fin N) : ℕ :=
  if swap then N + p.val else p.val

def linIdx (N : ℕ) (swap : Bool) (l : Fin N) : ℕ :=
  if swap then l.val else N + l.val

def combineInput (N : ℕ) (swap : Bool) (x y : Fin N → Bool) : List Bool :=
  List.ofFn fun i : Fin (N + N) =>
    if h : i.val < N then
      if swap then y ⟨i.val, h⟩ else x ⟨i.val, h⟩
    else
      if swap then x ⟨i.val - N, by omega⟩ else y ⟨i.val - N, by omega⟩

lemma combineInput_len (N : ℕ) (swap : Bool) (x y : Fin N → Bool) :
    (combineInput N swap x y).length = N + N := by
  simp [combineInput]

lemma combineInput_nonLin (N : ℕ) (swap : Bool) (x y : Fin N → Bool) (p : Fin N) :
    (combineInput N swap x y).getD (nonLinIdx N swap p) false = x p := by
  cases swap
  · have hlt : p.val < N + N := by omega
    simp [combineInput, nonLinIdx, List.getD_eq_getElem?_getD, p.isLt, hlt]
  · have h1 : ¬ (N + p.val < N) := by omega
    have h2 : N + p.val < N + N := by omega
    simp [combineInput, nonLinIdx, List.getD_eq_getElem?_getD, h1, h2]

lemma combineInput_lin (N : ℕ) (swap : Bool) (x y : Fin N → Bool) (l : Fin N) :
    (combineInput N swap x y).getD (linIdx N swap l) false = y l := by
  cases swap
  · have h1 : ¬ (N + l.val < N) := by omega
    have h2 : N + l.val < N + N := by omega
    simp [combineInput, linIdx, List.getD_eq_getElem?_getD, h1, h2]
  · have hlt : l.val < N + N := by omega
    simp [combineInput, linIdx, List.getD_eq_getElem?_getD, l.isLt, hlt]

lemma combineInput_eq_pair (N : ℕ) (swap : Bool) (p l : Fin N) :
    combineInput N swap (fun v => decide (v = p)) (fun v => decide (v = l)) =
      (List.range (N + N)).map fun i => i == nonLinIdx N swap p || i == linIdx N swap l := by
  apply List.ext_getElem
  · simp [combineInput]
  · intro i hi1 hi2
    have hi : i < N + N := by simpa [combineInput] using hi1
    cases swap
    · simp only [combineInput, nonLinIdx, linIdx, List.getElem_ofFn, List.getElem_map,
        List.getElem_range, Bool.false_eq_true, ↓reduceIte]
      by_cases h : i < N
      · have hne : (i == N + l.val) = false := by
          simp only [beq_eq_false_iff_ne]; omega
        simp only [h, ↓reduceDIte, hne, Bool.or_false, Fin.ext_iff]
        by_cases he : i = p.val <;> simp [he]
      · have hne : (i == p.val) = false := by
          simp only [beq_eq_false_iff_ne]; omega
        have heq : (i - N = l.val) ↔ (i = N + l.val) := by omega
        simp only [h, ↓reduceDIte, hne, Bool.false_or, Fin.ext_iff, heq]
        by_cases he : i = N + l.val <;> simp [he]
    · simp only [combineInput, nonLinIdx, linIdx, List.getElem_ofFn, List.getElem_map,
        List.getElem_range, ↓reduceIte]
      by_cases h : i < N
      · have hne : (i == N + p.val) = false := by
          simp only [beq_eq_false_iff_ne]; omega
        simp only [h, ↓reduceDIte, hne, Bool.false_or, Fin.ext_iff]
        by_cases he : i = l.val <;> simp [he]
      · have hne : (i == l.val) = false := by
          simp only [beq_eq_false_iff_ne]; omega
        have heq : (i - N = p.val) ↔ (i = N + p.val) := by omega
        simp only [h, ↓reduceDIte, hne, Bool.or_false, Fin.ext_iff, heq]
        by_cases he : i = N + p.val <;> simp [he]

def aWire (N : ℕ) (swap : Bool) (w : ℕ) : ℕ :=
  if w < N then (if swap then N else w)
  else if w < N + N then (if swap then w - N else N)
  else N + 2 + (w - (N + N))

def fwdGates (N : ℕ) (swap : Bool) (C : Circuit) : List Gate :=
  [⟨GateOp.or, []⟩, ⟨GateOp.and, []⟩] ++ C.gates.map fun g => ⟨g.op, g.inputs.map (aWire N swap)⟩

lemma fwdGates_len (N : ℕ) (swap : Bool) (C : Circuit) :
    (fwdGates N swap C).length = 2 + C.gates.length := by
  simp [fwdGates]; omega

lemma aWire_lt (N : ℕ) (swap : Bool) (j a : ℕ) (ha : a < N + N + j) :
    aWire N swap a < N + 2 + j := by
  unfold aWire
  split_ifs <;> omega

lemma fwdGates_mono (N : ℕ) (swap : Bool) (C : Circuit) (hfan : AndOrFanInTwo C) :
    ∀ g ∈ fwdGates N swap C, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [fwdGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hg
  rcases hg with (rfl | rfl) | ⟨g0, hg0, rfl⟩
  · exact ⟨Or.inr rfl, by simp⟩
  · exact ⟨Or.inl rfl, by simp⟩
  · refine ⟨?_, ?_⟩
    · have hm := hfan.1 g0 hg0
      cases hop : g0.op <;> simp [hop] at hm ⊢
    · simpa using hfan.2 g0 hg0

lemma fwdGates_rb (N : ℕ) (swap : Bool) (C : Circuit) (hrb : ReadsBack (N + N) C) :
    ReadsBack N ⟨fwdGates N swap C, 0⟩ := by
  intro j hj a ha
  have hget : gateAt ⟨fwdGates N swap C, 0⟩ j = (fwdGates N swap C)[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hget] at ha
  match j with
  | 0 => simp [fwdGates] at ha
  | 1 => simp [fwdGates] at ha
  | j' + 2 =>
    have hj' : j' < C.gates.length := by simp [fwdGates] at hj; omega
    have hgate : (fwdGates N swap C)[j' + 2] =
        ⟨(gateAt C j').op, (gateAt C j').inputs.map (aWire N swap)⟩ := by
      simp [fwdGates, gateAt, List.getD_eq_getElem?_getD, hj']
    rw [hgate] at ha
    simp only [List.mem_map] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    have hult : u < N + N + j' := hrb j' hj' u hu
    have hlt := aWire_lt N swap j' u hult
    omega

lemma foldl_step_append_lt (gs extra : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + gs.length) :
    ((gs ++ extra).foldl step w).getD i false = (gs.foldl step w).getD i false := by
  rw [List.foldl_append]
  apply foldl_step_getD_lt
  rw [foldl_step_len]
  exact hi

lemma lp_and_fst (l : List (Bool × Bool)) (acc : Bool × Bool) :
    (l.foldl (fun (a : Bool × Bool) p => (a.1 && p.1, (a.1 && p.2) || (a.2 && p.1))) acc).1 =
      (acc.1 && l.all (·.1)) := by
  induction l generalizing acc with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl_cons, List.all_cons, ih, Bool.and_assoc]

lemma fwdGates_eval_aWire (N : ℕ) (swap : Bool) (C : Circuit)
    (hfan : AndOrFanInTwo C) (hrb : ReadsBack (N + N) C)
    (x y : Fin N → Bool) :
    ∀ w < N + N + C.gates.length,
      ((fwdGates N swap C).foldl step (List.ofFn x)).getD (aWire N swap w) false =
        ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD w (false, false)).1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    have hrb_f : ReadsBack (List.ofFn x).length ⟨fwdGates N swap C, 0⟩ := by
      simp; exact fwdGates_rb N swap C hrb
    have hfalse : ((fwdGates N swap C).foldl step (List.ofFn x)).getD N false = false := by
      have h0 : 0 < (fwdGates N swap C).length := by simp [fwdGates]
      have hv := wires_gate_val ⟨fwdGates N swap C, 0⟩ (List.ofFn x) 0 h0 hrb_f
      simp only [wires_eq_foldl, List.length_ofFn, add_zero, gateAt, fwdGates,
        List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
        List.map_nil, GateOp.eval, List.any_nil] at hv
      exact hv
    by_cases hlt1 : w < N
    · have hlt_ci : w < (combineInput N swap x y).length := by rw [combineInput_len]; omega
      rw [linearParts_input C (isLinFn N swap) (combineInput N swap x y) w hlt_ci]
      cases swap
      · have his : isLinFn N false w = false := by simp [isLinFn]; omega
        simp only [aWire, hlt1, ↓reduceIte, Bool.false_eq_true, his]
        rw [eval_input_lt (fwdGates N false C) N x ⟨w, hlt1⟩]
        have hci := combineInput_nonLin N false x y ⟨w, hlt1⟩
        simpa [nonLinIdx] using hci.symm
      · have his : isLinFn N true w = true := by simp [isLinFn]; omega
        simp only [aWire, hlt1, ↓reduceIte, his]
        exact hfalse
    · by_cases hlt2 : w < N + N
      · have hlt_ci : w < (combineInput N swap x y).length := by rw [combineInput_len]; omega
        rw [linearParts_input C (isLinFn N swap) (combineInput N swap x y) w hlt_ci]
        cases swap
        · have his : isLinFn N false w = true := by simp [isLinFn]; omega
          simp only [aWire, hlt1, hlt2, ↓reduceIte, Bool.false_eq_true, his]
          exact hfalse
        · have his : isLinFn N true w = false := by simp [isLinFn]; omega
          simp only [aWire, hlt1, hlt2, ↓reduceIte, his]
          rw [eval_input_lt (fwdGates N true C) N x ⟨w - N, by omega⟩]
          have hci := combineInput_nonLin N true x y ⟨w - N, by omega⟩
          have hidx : nonLinIdx N true ⟨w - N, by omega⟩ = w := by simp [nonLinIdx]; omega
          rw [hidx] at hci
          exact hci.symm
      · let j : ℕ := w - (N + N)
        have hj : j < C.gates.length := by omega
        have hwj : w = (combineInput N swap x y).length + j := by rw [combineInput_len]; omega
        have haw : aWire N swap w = N + (j + 2) := by
          simp only [aWire, hlt1, hlt2, ↓reduceIte, j]; omega
        have hrb_c : ReadsBack (combineInput N swap x y).length C := by
          rw [combineInput_len]; exact hrb
        have hlp := linearParts_gate C (isLinFn N swap) (combineInput N swap x y) j hj hrb_c
        dsimp only at hlp
        rw [← hwj] at hlp
        have hj2 : j + 2 < (fwdGates N swap C).length := by simp [fwdGates]; omega
        have hfg := wires_gate_val ⟨fwdGates N swap C, 0⟩ (List.ofFn x) (j + 2) hj2 hrb_f
        simp only [wires_eq_foldl, List.length_ofFn] at hfg
        have hgate : gateAt ⟨fwdGates N swap C, 0⟩ (j + 2) =
            ⟨(gateAt C j).op, (gateAt C j).inputs.map (aWire N swap)⟩ := by
          simp [fwdGates, gateAt, List.getD_eq_getElem?_getD, hj]
        rw [haw, hfg, hgate, hlp]
        have hmap_eq : ((gateAt C j).inputs.map (aWire N swap)).map
            (fun a => ((fwdGates N swap C).foldl step (List.ofFn x)).getD a false) =
            ((gateAt C j).inputs.map fun a => (linearParts C (isLinFn N swap) (combineInput N swap x y)).getD a (false, false)).map (·.1) := by
          rw [List.map_map, List.map_map]
          apply List.map_congr_left
          intro a ha
          have halt : a < w := by
            have := hrb j hj a ha
            omega
          exact ih a halt (by omega)
        have hg_mem : gateAt C j ∈ C.gates := by
          simp [gateAt, List.getD_eq_getElem?_getD, hj]
        have hm := hfan.1 (gateAt C j) hg_mem
        cases hop : (gateAt C j).op with
        | or =>
          simp only [GateOp.eval, hmap_eq, List.any_map]
          rfl
        | and =>
          simp only [GateOp.eval, hmap_eq, lp_and_fst, Bool.true_and, List.all_map]
          rfl
        | not => simp [hop] at hm
        | mod m => simp [hop] at hm
        | maj => simp [hop] at hm

def revStep (N : ℕ) (swap : Bool) (C : Circuit) (j : ℕ) (st : List Gate × (ℕ → ℕ)) :
    List Gate × (ℕ → ℕ) :=
  let gs := st.1
  let adj := st.2
  let g := gateAt C j
  let w := N + N + j
  let base := N + gs.length
  match g.op with
  | GateOp.or =>
    match g.inputs with
    | [u] =>
      (gs ++ [⟨GateOp.or, [adj u, adj w]⟩], fun k => if k = u then base else adj k)
    | [u, v] =>
      (gs ++ [⟨GateOp.or, [adj u, adj w]⟩, ⟨GateOp.or, [adj v, adj w]⟩],
        fun k => if k = u then base else if k = v then base + 1 else adj k)
    | _ => (gs, adj)
  | GateOp.and =>
    match g.inputs with
    | [u] =>
      (gs ++ [⟨GateOp.or, [adj u, adj w]⟩], fun k => if k = u then base else adj k)
    | [u, v] =>
      (gs ++ [⟨GateOp.and, [adj w, aWire N swap v]⟩,
              ⟨GateOp.or, [adj u, base]⟩,
              ⟨GateOp.and, [adj w, aWire N swap u]⟩,
              ⟨GateOp.or, [adj v, base + 2]⟩],
        fun k => if k = u then base + 1 else if k = v then base + 3 else adj k)
    | _ => (gs, adj)
  | _ => (gs, adj)

def revLoop (N : ℕ) (swap : Bool) (C : Circuit) : ℕ → List Gate × (ℕ → ℕ)
  | 0 => (fwdGates N swap C, fun w => if w = C.output then N + 1 else N)
  | m + 1 => revStep N swap C (C.gates.length - 1 - m) (revLoop N swap C m)

lemma revStep_props (N : ℕ) (swap : Bool) (C : Circuit)
    (hfan : AndOrFanInTwo C) (hrb : ReadsBack (N + N) C)
    (j : ℕ) (hj : j < C.gates.length)
    (gs : List Gate) (adj : ℕ → ℕ)
    (hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hrb_gs : ReadsBack N ⟨gs, 0⟩)
    (hglen : 2 + C.gates.length ≤ gs.length)
    (hadj_lt : ∀ k, adj k < N + gs.length)
    (haW_eq : ∀ x y : Fin N → Bool, ∀ w < N + N + C.gates.length,
      (gs.foldl step (List.ofFn x)).getD (aWire N swap w) false =
        ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD w (false, false)).1) :
    let res := revStep N swap C j (gs, adj)
    res.1.length ≤ gs.length + 4 ∧
    gs.length ≤ res.1.length ∧
    (∀ g ∈ res.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    ReadsBack N ⟨res.1, 0⟩ ∧
    (∀ k, res.2 k < N + res.1.length) ∧
    (∀ x y : Fin N → Bool, ∀ w < N + N + C.gates.length,
      (res.1.foldl step (List.ofFn x)).getD (aWire N swap w) false =
        ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD w (false, false)).1) ∧
    (∀ x y : Fin N → Bool,
      (∃ w < N + N + j, (res.1.foldl step (List.ofFn x)).getD (res.2 w) false = true ∧
        ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD w (false, false)).2 = true) ↔
      (∃ w < N + N + (j + 1), (gs.foldl step (List.ofFn x)).getD (adj w) false = true ∧
        ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD w (false, false)).2 = true)) := by
  have hg_mem : gateAt C j ∈ C.gates := by simp [gateAt, List.getD_eq_getElem?_getD, hj]
  have hlen2 : (gateAt C j).inputs.length ≤ 2 := hfan.2 (gateAt C j) hg_mem
  have hm_op := hfan.1 (gateAt C j) hg_mem
  have hrb_c : ∀ x y : Fin N → Bool, ReadsBack (combineInput N swap x y).length C := by
    intro x y; rw [combineInput_len]; exact hrb
  have hlp_gate : ∀ x y : Fin N → Bool,
      let lp := linearParts C (isLinFn N swap) (combineInput N swap x y)
      let ins := (gateAt C j).inputs.map fun a => lp.getD a (false, false)
      lp.getD (N + N + j) (false, false) =
        match (gateAt C j).op with
        | GateOp.or => (ins.any (·.1), ins.any (·.2))
        | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
              (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
        | _ => (false, false) := by
    intro x y
    have h1 := linearParts_gate C (isLinFn N swap) (combineInput N swap x y) j hj (hrb_c x y)
    rwa [combineInput_len] at h1
  have hpres_aW : ∀ extra : List Gate, ∀ x y : Fin N → Bool, ∀ w < N + N + C.gates.length,
      ((gs ++ extra).foldl step (List.ofFn x)).getD (aWire N swap w) false =
        ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD w (false, false)).1 := by
    intro extra x y w hw
    have haw_lt : aWire N swap w < (List.ofFn x).length + gs.length := by
      have h1 := aWire_lt N swap C.gates.length w hw
      simp only [List.length_ofFn]; omega
    rw [foldl_step_append_lt gs extra (List.ofFn x) (aWire N swap w) haw_lt]
    exact haW_eq x y w hw
  have hrb_append : ∀ extra : List Gate,
      (∀ t (ht : t < extra.length), ∀ a ∈ extra[t].inputs, a < N + gs.length + t) →
      ReadsBack N ⟨gs ++ extra, 0⟩ := by
    intro extra hextra k hk a ha
    have hk' : k < (gs ++ extra).length := hk
    have hget : gateAt ⟨gs ++ extra, 0⟩ k = (gs ++ extra)[k] := by
      simp only [gateAt, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem hk']
      rfl
    rw [hget] at ha
    by_cases hlt : k < gs.length
    · rw [List.getElem_append_left hlt] at ha
      have hget0 : gateAt ⟨gs, 0⟩ k = gs[k] := by
        simp [gateAt, List.getD_eq_getElem?_getD, hlt]
      exact hrb_gs k hlt a (by rwa [hget0])
    · rw [List.getElem_append_right (by omega)] at ha
      have ht : k - gs.length < extra.length := by simp at hk; omega
      have h1 := hextra (k - gs.length) ht a ha
      omega
  dsimp only [revStep]
  cases hop : (gateAt C j).op with
  | or =>
    match hinp : (gateAt C j).inputs with
    | [] =>
      dsimp only
      refine ⟨by omega, by omega, hmono, hrb_gs, hadj_lt, haW_eq, ?_⟩
      intro x y
      have hB : ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD (N + N + j) (false, false)).2 = false := by
        have h1 := hlp_gate x y
        simp only [hop, hinp, List.map_nil, List.any_nil] at h1
        rw [h1]
      constructor
      · rintro ⟨w, hw, h1, h2⟩; exact ⟨w, by omega, h1, h2⟩
      · rintro ⟨w, hw, h1, h2⟩
        by_cases hlt : w < N + N + j
        · exact ⟨w, hlt, h1, h2⟩
        · have heq : w = N + N + j := by omega
          subst heq; rw [hB] at h2; exact absurd h2 (by decide)
    | [u] =>
      have hu_lt : u < N + N + j := hrb j hj u (by rw [hinp]; simp)
      set g1 : Gate := ⟨GateOp.or, [adj u, adj (N + N + j)]⟩
      have hrb1 : ReadsBack N ⟨gs ++ [g1], 0⟩ := by
        apply hrb_append [g1]
        intro t ht a ha
        have ht0 : t = 0 := by simp at ht; omega
        subst ht0
        simp only [g1, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · have := hadj_lt u; omega
        · have := hadj_lt (N + N + j); omega
      refine ⟨by simp, by simp, ?_, hrb1, ?_, hpres_aW [g1], ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hmono g hg
        · exact ⟨Or.inr rfl, by simp [g1]⟩
      · intro k
        simp only [List.length_append, List.length_singleton]
        split_ifs
        · omega
        · have := hadj_lt k; omega
      · intro x y
        let eval0 (z : ℕ) := (gs.foldl step (List.ofFn x)).getD z false
        let eval1 (z : ℕ) := ((gs ++ [g1]).foldl step (List.ofFn x)).getD z false
        have heq_lt : ∀ z < N + gs.length, eval1 z = eval0 z := fun z hz =>
          foldl_step_append_lt gs [g1] (List.ofFn x) z (by simp; omega)
        have hbase : eval1 (N + gs.length) = (eval0 (adj u) || eval0 (adj (N + N + j))) := by
          simp only [eval1, List.foldl_append, List.foldl_cons, List.foldl_nil, step]
          have hlen_w : (gs.foldl step (List.ofFn x)).length = N + gs.length := by
            rw [foldl_step_len, List.length_ofFn]
          rw [← hlen_w, getD_append_self]
          simp [g1, GateOp.eval, eval0]
        have hB : ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD (N + N + j) (false, false)).2 =
            ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD u (false, false)).2 := by
          have h1 := hlp_gate x y
          simp only [hop, hinp, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false] at h1
          rw [h1]
        constructor
        · rintro ⟨w, hw, h1, h2⟩
          by_cases hwu : w = u
          · subst hwu
            simp only [↓reduceIte] at h1
            change eval1 (N + gs.length) = true at h1
            rw [hbase, Bool.or_eq_true] at h1
            rcases h1 with h1a | h1b
            · exact ⟨w, by omega, h1a, h2⟩
            · exact ⟨N + N + j, by omega, h1b, by rw [hB]; exact h2⟩
          · simp only [hwu, ↓reduceIte] at h1
            change eval1 (adj w) = true at h1
            rw [heq_lt (adj w) (hadj_lt w)] at h1
            exact ⟨w, by omega, h1, h2⟩
        · rintro ⟨w, hw, h1, h2⟩
          change eval0 (adj w) = true at h1
          by_cases hlt : w < N + N + j
          · refine ⟨w, hlt, ?_, h2⟩
            by_cases hwu : w = u
            · subst hwu
              simp only [↓reduceIte]
              change eval1 (N + gs.length) = true
              rw [hbase, h1]; rfl
            · simp only [hwu, ↓reduceIte]
              change eval1 (adj w) = true
              rw [heq_lt (adj w) (hadj_lt w)]
              exact h1
          · have heq : w = N + N + j := by omega
            subst heq
            refine ⟨u, hu_lt, ?_, by rw [← hB]; exact h2⟩
            simp only [↓reduceIte]
            change eval1 (N + gs.length) = true
            rw [hbase, h1, Bool.or_true]
    | [u, v] =>
      have hu_lt : u < N + N + j := hrb j hj u (by rw [hinp]; simp)
      have hv_lt : v < N + N + j := hrb j hj v (by rw [hinp]; simp)
      set g1 : Gate := ⟨GateOp.or, [adj u, adj (N + N + j)]⟩
      set g2 : Gate := ⟨GateOp.or, [adj v, adj (N + N + j)]⟩
      have hrb2 : ReadsBack N ⟨gs ++ [g1, g2], 0⟩ := by
        apply hrb_append [g1, g2]
        intro t ht a ha
        match t with
        | 0 =>
          simp only [g1, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · have := hadj_lt u; omega
          · have := hadj_lt (N + N + j); omega
        | 1 =>
          simp only [g2, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · have := hadj_lt v; omega
          · have := hadj_lt (N + N + j); omega
        | _ + 2 => simp at ht
      refine ⟨by simp, by simp, ?_, hrb2, ?_, hpres_aW [g1, g2], ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with hg | rfl | rfl
        · exact hmono g hg
        · exact ⟨Or.inr rfl, by simp [g1]⟩
        · exact ⟨Or.inr rfl, by simp [g2]⟩
      · intro k
        simp only [List.length_append, List.length_cons, List.length_nil]
        split_ifs
        · omega
        · omega
        · have := hadj_lt k; omega
      · intro x y
        let eval0 (z : ℕ) := (gs.foldl step (List.ofFn x)).getD z false
        let eval1 (z : ℕ) := ((gs ++ [g1, g2]).foldl step (List.ofFn x)).getD z false
        have heq_lt : ∀ z < N + gs.length, eval1 z = eval0 z := fun z hz =>
          foldl_step_append_lt gs [g1, g2] (List.ofFn x) z (by simp; omega)
        have hlen_w : (gs.foldl step (List.ofFn x)).length = N + gs.length := by
          rw [foldl_step_len, List.length_ofFn]
        have hbase0 : eval1 (N + gs.length) = (eval0 (adj u) || eval0 (adj (N + N + j))) := by
          simp only [eval1, List.foldl_append, List.foldl_cons, List.foldl_nil]
          set w1 := step (gs.foldl step (List.ofFn x)) g1 with hw1_def
          have hlt1 : N + gs.length < w1.length := by
            simp [hw1_def, step, hlen_w]
          change (w1 ++ _).getD (N + gs.length) false = _
          rw [getD_append_left_lt w1 _ _ hlt1]
          rw [hw1_def]
          simp only [step]
          rw [← hlen_w, getD_append_self]
          simp [g1, GateOp.eval, eval0]
        have hbase1 : eval1 (N + gs.length + 1) = (eval0 (adj v) || eval0 (adj (N + N + j))) := by
          simp only [eval1, List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hlen1 : (step (gs.foldl step (List.ofFn x)) g1).length = N + gs.length + 1 := by
            simp [step, hlen_w]
          simp only [step]
          have hlen1' : (gs.foldl step (List.ofFn x) ++
              [g1.op.eval (g1.inputs.map fun i => (gs.foldl step (List.ofFn x)).getD i false)]).length =
              N + gs.length + 1 := hlen1
          rw [← hlen1', getD_append_self]
          simp only [g2, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
            id_eq, Bool.or_false]
          rw [getD_append_left_lt _ _ (adj v) (by rw [hlen_w]; exact hadj_lt v)]
          rw [getD_append_left_lt _ _ (adj (N + N + j)) (by rw [hlen_w]; exact hadj_lt (N + N + j))]
        have hB : ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD (N + N + j) (false, false)).2 =
            (((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD u (false, false)).2 ||
             ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD v (false, false)).2) := by
          have h1 := hlp_gate x y
          simp only [hop, hinp, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false] at h1
          rw [h1]
        constructor
        · rintro ⟨w, hw, h1, h2⟩
          by_cases hwu : w = u
          · subst hwu
            simp only [↓reduceIte] at h1
            change eval1 (N + gs.length) = true at h1
            rw [hbase0, Bool.or_eq_true] at h1
            rcases h1 with h1a | h1b
            · exact ⟨w, by omega, h1a, h2⟩
            · exact ⟨N + N + j, by omega, h1b, by rw [hB, h2]; rfl⟩
          · by_cases hwv : w = v
            · subst hwv
              simp only [hwu, ↓reduceIte] at h1
              change eval1 (N + gs.length + 1) = true at h1
              rw [hbase1, Bool.or_eq_true] at h1
              rcases h1 with h1a | h1b
              · exact ⟨w, by omega, h1a, h2⟩
              · exact ⟨N + N + j, by omega, h1b, by rw [hB, h2, Bool.or_true]⟩
            · simp only [hwu, hwv, ↓reduceIte] at h1
              change eval1 (adj w) = true at h1
              rw [heq_lt (adj w) (hadj_lt w)] at h1
              exact ⟨w, by omega, h1, h2⟩
        · rintro ⟨w, hw, h1, h2⟩
          change eval0 (adj w) = true at h1
          by_cases hlt : w < N + N + j
          · refine ⟨w, hlt, ?_, h2⟩
            by_cases hwu : w = u
            · subst hwu
              simp only [↓reduceIte]
              change eval1 (N + gs.length) = true
              rw [hbase0, h1]; rfl
            · by_cases hwv : w = v
              · subst hwv
                simp only [hwu, ↓reduceIte]
                change eval1 (N + gs.length + 1) = true
                rw [hbase1, h1]; rfl
              · simp only [hwu, hwv, ↓reduceIte]
                change eval1 (adj w) = true
                rw [heq_lt (adj w) (hadj_lt w)]
                exact h1
          · have heq : w = N + N + j := by omega
            subst heq
            rw [hB, Bool.or_eq_true] at h2
            rcases h2 with hBu | hBv
            · refine ⟨u, hu_lt, ?_, hBu⟩
              simp only [↓reduceIte]
              change eval1 (N + gs.length) = true
              rw [hbase0, h1, Bool.or_true]
            · by_cases huv : v = u
              · subst huv
                refine ⟨v, hv_lt, ?_, hBv⟩
                simp only [↓reduceIte]
                change eval1 (N + gs.length) = true
                rw [hbase0, h1, Bool.or_true]
              · refine ⟨v, hv_lt, ?_, hBv⟩
                simp only [huv, ↓reduceIte]
                change eval1 (N + gs.length + 1) = true
                rw [hbase1, h1, Bool.or_true]
    | _ :: _ :: _ :: _ => simp [hinp] at hlen2
  | and =>
    match hinp : (gateAt C j).inputs with
    | [] =>
      dsimp only
      refine ⟨by omega, by omega, hmono, hrb_gs, hadj_lt, haW_eq, ?_⟩
      intro x y
      have hB : ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD (N + N + j) (false, false)).2 = false := by
        have h1 := hlp_gate x y
        simp only [hop, hinp, List.map_nil, List.foldl_nil] at h1
        rw [h1]
      constructor
      · rintro ⟨w, hw, h1, h2⟩; exact ⟨w, by omega, h1, h2⟩
      · rintro ⟨w, hw, h1, h2⟩
        by_cases hlt : w < N + N + j
        · exact ⟨w, hlt, h1, h2⟩
        · have heq : w = N + N + j := by omega
          subst heq; rw [hB] at h2; exact absurd h2 (by decide)
    | [u] =>
      have hu_lt : u < N + N + j := hrb j hj u (by rw [hinp]; simp)
      set g1 : Gate := ⟨GateOp.or, [adj u, adj (N + N + j)]⟩
      have hrb1 : ReadsBack N ⟨gs ++ [g1], 0⟩ := by
        apply hrb_append [g1]
        intro t ht a ha
        have ht0 : t = 0 := by simp at ht; omega
        subst ht0
        simp only [g1, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · have := hadj_lt u; omega
        · have := hadj_lt (N + N + j); omega
      refine ⟨by simp, by simp, ?_, hrb1, ?_, hpres_aW [g1], ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hmono g hg
        · exact ⟨Or.inr rfl, by simp [g1]⟩
      · intro k
        simp only [List.length_append, List.length_singleton]
        split_ifs
        · omega
        · have := hadj_lt k; omega
      · intro x y
        let eval0 (z : ℕ) := (gs.foldl step (List.ofFn x)).getD z false
        let eval1 (z : ℕ) := ((gs ++ [g1]).foldl step (List.ofFn x)).getD z false
        have heq_lt : ∀ z < N + gs.length, eval1 z = eval0 z := fun z hz =>
          foldl_step_append_lt gs [g1] (List.ofFn x) z (by simp; omega)
        have hbase : eval1 (N + gs.length) = (eval0 (adj u) || eval0 (adj (N + N + j))) := by
          simp only [eval1, List.foldl_append, List.foldl_cons, List.foldl_nil, step]
          have hlen_w : (gs.foldl step (List.ofFn x)).length = N + gs.length := by
            rw [foldl_step_len, List.length_ofFn]
          rw [← hlen_w, getD_append_self]
          simp [g1, GateOp.eval, eval0]
        have hB : ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD (N + N + j) (false, false)).2 =
            ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD u (false, false)).2 := by
          have h1 := hlp_gate x y
          simp only [hop, hinp, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
            Bool.true_and, Bool.false_and, Bool.or_false] at h1
          rw [h1]
        constructor
        · rintro ⟨w, hw, h1, h2⟩
          by_cases hwu : w = u
          · subst hwu
            simp only [↓reduceIte] at h1
            change eval1 (N + gs.length) = true at h1
            rw [hbase, Bool.or_eq_true] at h1
            rcases h1 with h1a | h1b
            · exact ⟨w, by omega, h1a, h2⟩
            · exact ⟨N + N + j, by omega, h1b, by rw [hB]; exact h2⟩
          · simp only [hwu, ↓reduceIte] at h1
            change eval1 (adj w) = true at h1
            rw [heq_lt (adj w) (hadj_lt w)] at h1
            exact ⟨w, by omega, h1, h2⟩
        · rintro ⟨w, hw, h1, h2⟩
          change eval0 (adj w) = true at h1
          by_cases hlt : w < N + N + j
          · refine ⟨w, hlt, ?_, h2⟩
            by_cases hwu : w = u
            · subst hwu
              simp only [↓reduceIte]
              change eval1 (N + gs.length) = true
              rw [hbase, h1]; rfl
            · simp only [hwu, ↓reduceIte]
              change eval1 (adj w) = true
              rw [heq_lt (adj w) (hadj_lt w)]
              exact h1
          · have heq : w = N + N + j := by omega
            subst heq
            refine ⟨u, hu_lt, ?_, by rw [← hB]; exact h2⟩
            simp only [↓reduceIte]
            change eval1 (N + gs.length) = true
            rw [hbase, h1, Bool.or_true]
    | [u, v] =>
      have hu_lt : u < N + N + j := hrb j hj u (by rw [hinp]; simp)
      have hv_lt : v < N + N + j := hrb j hj v (by rw [hinp]; simp)
      have hau_lt : aWire N swap u < N + gs.length := by
        have := aWire_lt N swap j u hu_lt; omega
      have hav_lt : aWire N swap v < N + gs.length := by
        have := aWire_lt N swap j v hv_lt; omega
      set base := N + gs.length
      set g1 : Gate := ⟨GateOp.and, [adj (N + N + j), aWire N swap v]⟩
      set g2 : Gate := ⟨GateOp.or, [adj u, base]⟩
      set g3 : Gate := ⟨GateOp.and, [adj (N + N + j), aWire N swap u]⟩
      set g4 : Gate := ⟨GateOp.or, [adj v, base + 2]⟩
      have hrb4 : ReadsBack N ⟨gs ++ [g1, g2, g3, g4], 0⟩ := by
        apply hrb_append [g1, g2, g3, g4]
        intro t ht a ha
        match t with
        | 0 =>
          simp only [g1, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · have := hadj_lt (N + N + j); omega
          · omega
        | 1 =>
          simp only [g2, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · have := hadj_lt u; omega
          · omega
        | 2 =>
          simp only [g3, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · have := hadj_lt (N + N + j); omega
          · omega
        | 3 =>
          simp only [g4, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · have := hadj_lt v; omega
          · omega
        | _ + 4 => simp at ht
      refine ⟨by simp, by simp, ?_, hrb4, ?_, hpres_aW [g1, g2, g3, g4], ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with hg | rfl | rfl | rfl | rfl
        · exact hmono g hg
        · exact ⟨Or.inl rfl, by simp [g1]⟩
        · exact ⟨Or.inr rfl, by simp [g2]⟩
        · exact ⟨Or.inl rfl, by simp [g3]⟩
        · exact ⟨Or.inr rfl, by simp [g4]⟩
      · intro k
        simp only [List.length_append, List.length_cons, List.length_nil]
        split_ifs
        · omega
        · omega
        · have := hadj_lt k; omega
      · intro x y
        let w0 := gs.foldl step (List.ofFn x)
        let eval0 (z : ℕ) := w0.getD z false
        let eval4 (z : ℕ) := ((gs ++ [g1, g2, g3, g4]).foldl step (List.ofFn x)).getD z false
        have hlen0 : w0.length = base := by simp [w0, base, foldl_step_len]
        have heq_lt : ∀ z < base, eval4 z = eval0 z := fun z hz =>
          foldl_step_append_lt gs [g1, g2, g3, g4] (List.ofFn x) z (by simp [base] at hz ⊢; omega)
        have hrb4' : ReadsBack (List.ofFn x).length ⟨gs ++ [g1, g2, g3, g4], 0⟩ := by
          simp; exact hrb4
        have hg_val : ∀ t (ht : t < 4),
            eval4 (base + t) = ([g1, g2, g3, g4][t]'ht).op.eval
              (([g1, g2, g3, g4][t]'ht).inputs.map eval4) := by
          intro t ht
          have hkt : gs.length + t < (gs ++ [g1, g2, g3, g4]).length := by simp; omega
          have hv := wires_gate_val ⟨gs ++ [g1, g2, g3, g4], 0⟩ (List.ofFn x) (gs.length + t) hkt hrb4'
          simp only [wires_eq_foldl, List.length_ofFn] at hv
          have hidx : N + (gs.length + t) = base + t := by simp [base]; omega
          have hgt : gateAt ⟨gs ++ [g1, g2, g3, g4], 0⟩ (gs.length + t) = [g1, g2, g3, g4][t]'ht := by
            simp only [gateAt, List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_getElem hkt, Option.getD_some, List.getElem_append_right (by omega)]
            simp
          rw [hidx, hgt] at hv
          exact hv
        have hb0 : eval4 base = (eval0 (adj (N + N + j)) && eval0 (aWire N swap v)) := by
          have h := hg_val 0 (by omega)
          simp only [add_zero, List.getElem_cons_zero, g1, GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, id_eq, Bool.and_true] at h
          rw [h, heq_lt (adj (N + N + j)) (hadj_lt _), heq_lt (aWire N swap v) hav_lt]
        have hb1 : eval4 (base + 1) = (eval0 (adj u) || (eval0 (adj (N + N + j)) && eval0 (aWire N swap v))) := by
          have h := hg_val 1 (by omega)
          simp only [List.getElem_cons_succ, List.getElem_cons_zero, g2, GateOp.eval, List.map_cons,
            List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false] at h
          rw [h, heq_lt (adj u) (hadj_lt u), hb0]
        have hb2 : eval4 (base + 2) = (eval0 (adj (N + N + j)) && eval0 (aWire N swap u)) := by
          have h := hg_val 2 (by omega)
          simp only [List.getElem_cons_succ, List.getElem_cons_zero, g3, GateOp.eval, List.map_cons,
            List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true] at h
          rw [h, heq_lt (adj (N + N + j)) (hadj_lt _), heq_lt (aWire N swap u) hau_lt]
        have hb3 : eval4 (base + 3) = (eval0 (adj v) || (eval0 (adj (N + N + j)) && eval0 (aWire N swap u))) := by
          have h := hg_val 3 (by omega)
          simp only [List.getElem_cons_succ, List.getElem_cons_zero, g4, GateOp.eval, List.map_cons,
            List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false] at h
          rw [h, heq_lt (adj v) (hadj_lt v), hb2]
        have hAu : eval0 (aWire N swap u) =
            ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD u (false, false)).1 :=
          haW_eq x y u (by omega)
        have hAv : eval0 (aWire N swap v) =
            ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD v (false, false)).1 :=
          haW_eq x y v (by omega)
        have hB : ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD (N + N + j) (false, false)).2 =
            ((((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD u (false, false)).1 &&
              ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD v (false, false)).2) ||
             (((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD u (false, false)).2 &&
              ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD v (false, false)).1)) := by
          have h1 := hlp_gate x y
          simp only [hop, hinp, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
            Bool.true_and, Bool.false_and, Bool.or_false] at h1
          rw [h1]
        constructor
        · rintro ⟨w, hw, h1, h2⟩
          by_cases hwu : w = u
          · subst hwu
            simp only [↓reduceIte] at h1
            change eval4 (base + 1) = true at h1
            rw [hb1, Bool.or_eq_true, Bool.and_eq_true] at h1
            rcases h1 with h1a | ⟨h1b, h1c⟩
            · exact ⟨w, by omega, h1a, h2⟩
            · refine ⟨N + N + j, by omega, h1b, ?_⟩
              rw [hB, h2, ← hAv, h1c]; simp
          · by_cases hwv : w = v
            · subst hwv
              simp only [hwu, ↓reduceIte] at h1
              change eval4 (base + 3) = true at h1
              rw [hb3, Bool.or_eq_true, Bool.and_eq_true] at h1
              rcases h1 with h1a | ⟨h1b, h1c⟩
              · exact ⟨w, by omega, h1a, h2⟩
              · refine ⟨N + N + j, by omega, h1b, ?_⟩
                rw [hB, h2, ← hAu, h1c]; simp
            · simp only [hwu, hwv, ↓reduceIte] at h1
              change eval4 (adj w) = true at h1
              rw [heq_lt (adj w) (hadj_lt w)] at h1
              exact ⟨w, by omega, h1, h2⟩
        · rintro ⟨w, hw, h1, h2⟩
          change eval0 (adj w) = true at h1
          by_cases hlt : w < N + N + j
          · refine ⟨w, hlt, ?_, h2⟩
            by_cases hwu : w = u
            · subst hwu
              simp only [↓reduceIte]
              change eval4 (base + 1) = true
              rw [hb1, h1]; rfl
            · by_cases hwv : w = v
              · subst hwv
                simp only [hwu, ↓reduceIte]
                change eval4 (base + 3) = true
                rw [hb3, h1]; rfl
              · simp only [hwu, hwv, ↓reduceIte]
                change eval4 (adj w) = true
                rw [heq_lt (adj w) (hadj_lt w)]
                exact h1
          · have heq : w = N + N + j := by omega
            subst heq
            rw [hB, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2
            rcases h2 with ⟨hAu1, hBv1⟩ | ⟨hBu1, hAv1⟩
            · by_cases huv : v = u
              · subst huv
                refine ⟨v, hv_lt, ?_, hBv1⟩
                simp only [↓reduceIte]
                change eval4 (base + 1) = true
                rw [hb1, h1, hAv, hAu1]; simp
              · refine ⟨v, hv_lt, ?_, hBv1⟩
                simp only [huv, ↓reduceIte]
                change eval4 (base + 3) = true
                rw [hb3, h1, hAu, hAu1]; simp
            · refine ⟨u, hu_lt, ?_, hBu1⟩
              simp only [↓reduceIte]
              change eval4 (base + 1) = true
              rw [hb1, h1, hAv, hAv1]; simp
    | _ :: _ :: _ :: _ => simp [hinp] at hlen2
  | not => simp [hop] at hm_op
  | mod m => simp [hop] at hm_op
  | maj => simp [hop] at hm_op

lemma revLoop_props (N : ℕ) (swap : Bool) (C : Circuit)
    (hfan : AndOrFanInTwo C) (hrb : ReadsBack (N + N) C)
    (hOut : C.output < N + N + C.gates.length) :
    ∀ m ≤ C.gates.length,
      let res := revLoop N swap C m
      res.1.length ≤ 2 + C.gates.length + 4 * m ∧
      2 + C.gates.length ≤ res.1.length ∧
      (∀ g ∈ res.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ReadsBack N ⟨res.1, 0⟩ ∧
      (∀ k, res.2 k < N + res.1.length) ∧
      (∀ x y : Fin N → Bool, ∀ w < N + N + C.gates.length,
        (res.1.foldl step (List.ofFn x)).getD (aWire N swap w) false =
          ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD w (false, false)).1) ∧
      (∀ x y : Fin N → Bool,
        (∃ w < N + N + (C.gates.length - m),
          (res.1.foldl step (List.ofFn x)).getD (res.2 w) false = true ∧
          ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD w (false, false)).2 = true) ↔
        ((linearParts C (isLinFn N swap) (combineInput N swap x y)).getD C.output (false, false)).2 = true) := by
  intro m
  induction m with
  | zero =>
    intro _
    have hrb_f := fwdGates_rb N swap C hrb
    refine ⟨by simp [revLoop, fwdGates_len], by simp [revLoop, fwdGates_len],
      fwdGates_mono N swap C hfan, hrb_f, ?_, fwdGates_eval_aWire N swap C hfan hrb, ?_⟩
    · intro k
      simp only [revLoop, fwdGates_len]
      split_ifs <;> omega
    · intro x y
      have hrb_x : ReadsBack (List.ofFn x).length ⟨fwdGates N swap C, 0⟩ := by simp; exact hrb_f
      have hfalse : ((fwdGates N swap C).foldl step (List.ofFn x)).getD N false = false := by
        have h0 : 0 < (fwdGates N swap C).length := by simp [fwdGates]
        have hv := wires_gate_val ⟨fwdGates N swap C, 0⟩ (List.ofFn x) 0 h0 hrb_x
        simp only [wires_eq_foldl, List.length_ofFn, add_zero, gateAt, fwdGates,
          List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
          List.map_nil, GateOp.eval, List.any_nil] at hv
        exact hv
      have htrue : ((fwdGates N swap C).foldl step (List.ofFn x)).getD (N + 1) false = true := by
        have h1 : 1 < (fwdGates N swap C).length := by simp [fwdGates]
        have hv := wires_gate_val ⟨fwdGates N swap C, 0⟩ (List.ofFn x) 1 h1 hrb_x
        simp only [wires_eq_foldl, List.length_ofFn, gateAt, fwdGates,
          List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.getD_some, List.map_nil, GateOp.eval, List.all_nil] at hv
        exact hv
      simp only [revLoop, Nat.sub_zero]
      constructor
      · rintro ⟨w, _, h1, h2⟩
        by_cases hw : w = C.output
        · subst hw; exact h2
        · simp only [hw, ↓reduceIte] at h1
          rw [hfalse] at h1; exact absurd h1 (by decide)
      · intro hB
        refine ⟨C.output, hOut, ?_, hB⟩
        simp only [↓reduceIte]
        exact htrue
  | succ m ih =>
    intro hm
    obtain ⟨hlen_le, hlen_ge, hmono, hrb_gs, hadj_lt, haW, hinv⟩ := ih (by omega)
    let j : ℕ := C.gates.length - 1 - m
    have hj : j < C.gates.length := by omega
    have hstep := revStep_props N swap C hfan hrb j hj
      (revLoop N swap C m).1 (revLoop N swap C m).2 hmono hrb_gs hlen_ge hadj_lt haW
    rcases hstep with ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have heta : revLoop N swap C (m + 1) = revStep N swap C j ((revLoop N swap C m).1, (revLoop N swap C m).2) := rfl
    rw [heta]
    refine ⟨by omega, by omega, h3, h4, h5, h6, ?_⟩
    intro x y
    have hsub1 : C.gates.length - (m + 1) = j := by simp [j]; omega
    have hsub0 : C.gates.length - m = j + 1 := by simp [j]; omega
    rw [hsub1]
    exact (h7 x y).trans (by rw [← hsub0]; exact hinv x y)

lemma one_side_bound (N : ℕ) (swap : Bool) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hfan : AndOrFanInTwo C) (hrb : ReadsBack (N + N) C)
    (hcomp : ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (R : Fin N → Fin N → Prop) [DecidableRel R]
    (hR : ∀ p l : Fin N, R p l ↔ (if swap then I l p else I p l))
    (hnoC4 : ∀ l1 l2 : Fin N, l1 ≠ l2 → (Finset.univ.filter (fun p => R p l1 ∧ R p l2)).card ≤ 1) :
    ∑ l : Fin N, (Finset.univ.filter fun p : Fin N =>
      R p l ∧ lineSingle C (N + N) (isLinFn N swap) (nonLinIdx N swap p) (linIdx N swap l) = true).card ≤
      5 * C.size + 2 + N := by
  by_cases hOut : C.output < N + N + C.gates.length
  · obtain ⟨hlen_le, _, hmono, hrb_f, _, _, hinv⟩ :=
      revLoop_props N swap C hfan hrb hOut C.gates.length (le_refl _)
    let res := revLoop N swap C C.gates.length
    let out : Fin N → ℕ := fun l => res.2 (linIdx N swap l)
    let Ehit : Fin N → Finset (Fin N) := fun l =>
      Finset.univ.filter fun p : Fin N =>
        R p l ∧ lineSingle C (N + N) (isLinFn N swap) (nonLinIdx N swap p) (linIdx N swap l) = true
    have heval_iff : ∀ (x : Fin N → Bool) (l : Fin N),
        (res.1.foldl step (List.ofFn x)).getD (out l) false = true ↔
        ((linearParts C (isLinFn N swap) (combineInput N swap x (fun v => decide (v = l)))).getD C.output (false, false)).2 = true := by
      intro x l
      have h0 := hinv x (fun v => decide (v = l))
      simp only [Nat.sub_self, add_zero] at h0
      rw [← h0]
      constructor
      · intro h1
        refine ⟨linIdx N swap l, ?_, h1, ?_⟩
        · cases swap <;> simp [linIdx] <;> omega
        · have hlt_ci : linIdx N swap l < (combineInput N swap x (fun v => decide (v = l))).length := by
            rw [combineInput_len]; cases swap <;> simp [linIdx] <;> omega
          rw [linearParts_input C (isLinFn N swap) _ _ hlt_ci]
          have his : isLinFn N swap (linIdx N swap l) = true := by
            cases swap <;> simp [isLinFn, linIdx] <;> omega
          simp only [his, ↓reduceIte]
          rw [combineInput_lin]
          simp
      · rintro ⟨w, hw, h1, h2⟩
        have hlt_ci : w < (combineInput N swap x (fun v => decide (v = l))).length := by
          rw [combineInput_len]; exact hw
        rw [linearParts_input C (isLinFn N swap) _ w hlt_ci] at h2
        have hweq : w = linIdx N swap l := by
          cases hsw : swap
          · by_cases hltN : w < N
            · have his : isLinFn N false w = false := by simp [isLinFn]; omega
              simp [hsw, his] at h2
            · have his : isLinFn N false w = true := by simp [isLinFn]; omega
              simp only [hsw, his, ↓reduceIte] at h2
              have hci : (combineInput N false x (fun v => decide (v = l))).getD w false = decide (⟨w - N, by omega⟩ = l) := by
                have := combineInput_lin N false x (fun v => decide (v = l)) ⟨w - N, by omega⟩
                have hidx : linIdx N false ⟨w - N, by omega⟩ = w := by simp [linIdx]; omega
                rwa [hidx] at this
              rw [hci, decide_eq_true_eq, Fin.ext_iff] at h2
              dsimp only at h2
              simp [linIdx]; omega
          · by_cases hltN : w < N
            · have his : isLinFn N true w = true := by simp [isLinFn]; omega
              simp only [hsw, his, ↓reduceIte] at h2
              have hci : (combineInput N true x (fun v => decide (v = l))).getD w false = decide (⟨w, hltN⟩ = l) := by
                have := combineInput_lin N true x (fun v => decide (v = l)) ⟨w, hltN⟩
                simpa [linIdx] using this
              rw [hci, decide_eq_true_eq, Fin.ext_iff] at h2
              dsimp only at h2
              simp [linIdx]; omega
            · have his : isLinFn N true w = false := by simp [isLinFn]; omega
              simp [hsw, his] at h2
        rwa [hweq] at h1
    have hsound : ∀ l : Fin N,
        (res.1.foldl step (List.ofFn fun p : Fin N => decide (¬ R p l))).getD (out l) false = false := by
      intro l
      by_contra hne
      have htr : (res.1.foldl step (List.ofFn fun p : Fin N => decide (¬ R p l))).getD (out l) false = true := by
        cases h : (res.1.foldl step (List.ofFn fun p : Fin N => decide (¬ R p l))).getD (out l) false
        · exact absurd h hne
        · rfl
      have hB := (heval_iff (fun p => decide (¬ R p l)) l).mp htr
      have hw := linearParts_le_wires C (isLinFn N swap)
        (combineInput N swap (fun p => decide (¬ R p l)) (fun v => decide (v = l))) C.output (Or.inr hB)
      let z : Fin (N + N) → Bool := fun i =>
        if h : i.val < N then
          if swap then decide (⟨i.val, h⟩ = l) else decide (¬ R ⟨i.val, h⟩ l)
        else
          if swap then decide (¬ R ⟨i.val - N, by omega⟩ l) else decide (⟨i.val - N, by omega⟩ = l)
      have hcf : circuitFun (N + N) C z = true := by
        simpa [circuitFun, Circuit.eval, combineInput, z] using hw
      rw [hcomp z, decide_eq_true_eq] at hcf
      obtain ⟨p3, l3, hI3, hp3, hl3⟩ := hcf
      cases hsw : swap
      · simp only [z, hsw, Fin.val_castAdd, Fin.val_natAdd, p3.isLt, ↓reduceDIte,
          Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hp3 hl3
        have hnotN : ¬ (N + l3.val < N) := by omega
        simp only [hnotN, ↓reduceDIte, decide_eq_true_eq] at hl3
        have hl3_eq : l3 = l := by ext; simpa using congrArg Fin.val hl3
        subst hl3_eq
        exact hp3 ((hR p3 l3).mpr (by simpa [hsw] using hI3))
      · simp only [z, hsw, Fin.val_castAdd, Fin.val_natAdd, p3.isLt, ↓reduceDIte,
          ↓reduceIte, decide_eq_true_eq] at hp3 hl3
        have hnotN : ¬ (N + l3.val < N) := by omega
        simp only [hnotN, ↓reduceDIte, decide_eq_true_eq] at hl3
        have hp3_eq : p3 = l := by ext; simpa using congrArg Fin.val hp3
        subst hp3_eq
        have hsub_l3 : (⟨N + l3.val - N, by omega⟩ : Fin N) = l3 := by ext; dsimp only; omega
        rw [hsub_l3] at hl3
        exact hl3 ((hR l3 p3).mpr (by simpa [hsw] using hI3))
    have hEhit : ∀ l : Fin N, ∀ p ∈ Ehit l,
        (res.1.foldl step (List.ofFn fun v : Fin N => decide (v = p))).getD (out l) false = true := by
      intro l p hp
      have hls : lineSingle C (N + N) (isLinFn N swap) (nonLinIdx N swap p) (linIdx N swap l) = true :=
        (Finset.mem_filter.mp hp).2.2
      rw [heval_iff]
      rw [combineInput_eq_pair]
      exact hls
    have hcnt := monoOrCount N R res.1 out hmono hrb_f hnoC4 hsound Ehit hEhit
    have hsz : res.1.length ≤ 5 * C.size + 2 := by
      dsimp only [res]
      simp only [Circuit.size] at hlen_le ⊢
      omega
    dsimp only [Ehit] at hcnt
    omega
  · have hzero : ∀ l : Fin N, (Finset.univ.filter fun p : Fin N =>
        R p l ∧ lineSingle C (N + N) (isLinFn N swap) (nonLinIdx N swap p) (linIdx N swap l) = true) = ∅ := by
      intro l
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
      intro _ hls
      simp only [lineSingle] at hls
      have hge : (linearParts C (isLinFn N swap)
          ((List.range (N + N)).map fun i => i == nonLinIdx N swap p || i == linIdx N swap l)).length ≤ C.output := by
        rw [linearParts_len, List.length_map, List.length_range]; omega
      rw [lp_getD_ge_len _ _ hge] at hls
      exact absurd hls (by decide)
    simp [hzero]

lemma lineSingle_symm (C : Circuit) (n : ℕ) (isLin : ℕ → Bool) (a b : ℕ) :
    lineSingle C n isLin a b = lineSingle C n isLin b a := by
  simp only [lineSingle]
  have heq : ((List.range n).map fun i => i == a || i == b) =
      ((List.range n).map fun i => i == b || i == a) := by
    apply List.map_congr_left
    intro i _
    exact Bool.or_comm _ _
  rw [heq]

end PEqualNP.Outside.L_meta_2240

theorem PEqualNP.Outside.L_meta_2240 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l1 : Fin N, I p1 l1 ∧ I p2 l1) → PEqualNP.ReadK.AndOrFanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p3 l3 : Fin N, I p3 l3 ∧ z (Fin.castAdd N p3) = true ∧ z (Fin.natAdd N l3) = true)) → PEqualNP.ReadK.IsSingleRead C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val)))) → N * q ≤ 32 * C.size + 3 * N := by
  intro q N I _ C hq hN hdeg huniq hfan hrb hcomp hsr
  have hnoC4_lines : ∀ l1 l2 : Fin N, l1 ≠ l2 → (Finset.univ.filter (fun p => I p l1 ∧ I p l2)).card ≤ 1 := by
    intro l1 l2 hne
    rw [Finset.card_le_one]
    intro p1 hp1 p2 hp2
    by_contra hpne
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    obtain ⟨l0, _, hl0u⟩ := huniq p1 p2 hpne
    exact hne ((hl0u l1 ⟨h1.1, h2.1⟩).trans (hl0u l2 ⟨h1.2, h2.2⟩).symm)
  have hnoC4_pts : ∀ p1 p2 : Fin N, p1 ≠ p2 → (Finset.univ.filter (fun l => I p1 l ∧ I p2 l)).card ≤ 1 := by
    intro p1 p2 hne
    rw [Finset.card_le_one]
    intro l1 hl1 l2 hl2
    have h1 := (Finset.mem_filter.mp hl1).2
    have h2 := (Finset.mem_filter.mp hl2).2
    obtain ⟨l0, _, hl0u⟩ := huniq p1 p2 hne
    exact (hl0u l1 h1).trans (hl0u l2 h2).symm
  have hb1 := PEqualNP.Outside.L_meta_2240.one_side_bound N false I C hfan hrb hcomp
    (fun p l => I p l) (fun p l => by simp) hnoC4_lines
  have hb2 := PEqualNP.Outside.L_meta_2240.one_side_bound N true I C hfan hrb hcomp
    (fun l p => I p l) (fun l p => by simp) hnoC4_pts
  have hsingle : ∀ p l : Fin N, I p l →
      PEqualNP.ReadK.lineSingle C (N + N) (fun w => decide (N ≤ w)) p.val (N + l.val) = true ∨
      PEqualNP.ReadK.lineSingle C (N + N) (fun w => !decide (N ≤ w)) p.val (N + l.val) = true := by
    intro p l hI
    have hmemE : (p.val, N + l.val) ∈ (List.finRange N).flatMap
        (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))) := by
      rw [List.mem_flatMap]
      refine ⟨p, List.mem_finRange p, ?_⟩
      rw [List.mem_map]
      refine ⟨l, ?_, rfl⟩
      exact List.mem_filter.mpr ⟨List.mem_finRange l, decide_eq_true hI⟩
    by_contra hnot
    push_neg at hnot
    have h1 : PEqualNP.ReadK.lineSingle C (N + N) (fun w => decide (N ≤ w)) p.val (N + l.val) = false :=
      Bool.eq_false_iff.mpr hnot.1
    have h2 : PEqualNP.ReadK.lineSingle C (N + N) (fun w => !decide (N ≤ w)) p.val (N + l.val) = false :=
      Bool.eq_false_iff.mpr hnot.2
    have hmemDR : (p.val, N + l.val) ∈ PEqualNP.ReadK.doubleReread C (N + N) (fun w => decide (N ≤ w))
        ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val)))) := by
      simp only [PEqualNP.ReadK.doubleReread, List.mem_filter]
      exact ⟨hmemE, by simp [h1, h2]⟩
    rw [hsr] at hmemDR
    simp at hmemDR
  let S1 : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
    I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun w => decide (N ≤ w)) e.1.val (N + e.2.val) = true
  let S2 : Finset (Fin N × Fin N) := Finset.univ.filter fun e =>
    I e.1 e.2 ∧ PEqualNP.ReadK.lineSingle C (N + N) (fun w => !decide (N ≤ w)) e.1.val (N + e.2.val) = true
  let S0 : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2
  have hS0_sub : S0 ⊆ S1 ∪ S2 := by
    intro e he
    have hI : I e.1 e.2 := (Finset.mem_filter.mp he).2
    rcases hsingle e.1 e.2 hI with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ e, hI, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ e, hI, h2⟩)
  have hcard_S0 : S0.card = N * (q + 1) := by
    have h1 : S0.card = ∑ l : Fin N, (Finset.univ.filter fun p : Fin N => I p l).card := by
      simp only [S0, Finset.card_filter, Fintype.sum_prod_type_right]
    rw [h1]
    simp [hdeg]
  have hcard_S1 : S1.card ≤ 5 * C.size + 2 + N := by
    have his0 : PEqualNP.Outside.L_meta_2240.isLinFn N false = fun w => decide (N ≤ w) := by
      funext w; rfl
    have h1 : S1.card = ∑ l : Fin N, (Finset.univ.filter fun p : Fin N =>
        I p l ∧ PEqualNP.ReadK.lineSingle C (N + N) (PEqualNP.Outside.L_meta_2240.isLinFn N false)
          (PEqualNP.Outside.L_meta_2240.nonLinIdx N false p)
          (PEqualNP.Outside.L_meta_2240.linIdx N false l) = true).card := by
      rw [his0]
      simp only [S1, Finset.card_filter, Fintype.sum_prod_type_right,
        PEqualNP.Outside.L_meta_2240.nonLinIdx,
        PEqualNP.Outside.L_meta_2240.linIdx, Bool.false_eq_true, ↓reduceIte]
    rw [h1]
    exact hb1
  have hcard_S2 : S2.card ≤ 5 * C.size + 2 + N := by
    have his1 : PEqualNP.Outside.L_meta_2240.isLinFn N true = fun w => !decide (N ≤ w) := by
      funext w; rfl
    have h1 : S2.card = ∑ p : Fin N, (Finset.univ.filter fun l : Fin N =>
        I p l ∧ PEqualNP.ReadK.lineSingle C (N + N) (PEqualNP.Outside.L_meta_2240.isLinFn N true)
          (PEqualNP.Outside.L_meta_2240.nonLinIdx N true l)
          (PEqualNP.Outside.L_meta_2240.linIdx N true p) = true).card := by
      rw [his1]
      simp only [S2, Finset.card_filter, Fintype.sum_prod_type,
        PEqualNP.Outside.L_meta_2240.nonLinIdx,
        PEqualNP.Outside.L_meta_2240.linIdx, ↓reduceIte]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro l _
      rw [PEqualNP.Outside.L_meta_2240.lineSingle_symm]
    rw [h1]
    exact hb2
  have htot : S0.card ≤ S1.card + S2.card :=
    le_trans (Finset.card_le_card hS0_sub) (Finset.card_union_le S1 S2)
  have hN4 : 4 ≤ N := by nlinarith
  nlinarith
