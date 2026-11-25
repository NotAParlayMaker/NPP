import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import PEqualNP.Defs
import PEqualNP.Defs.Represents

namespace PEqualNP.Outside.L_meta_10181

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def targetA (u v : Fin 5) : Bool := (16223379 : ℕ).testBit (5 * u.val + v.val)

def wstep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

lemma wfold_len (gs : List Gate) (xs : List Bool) :
    (gs.foldl wstep xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons, ih, wstep, List.length_append, List.length_nil]
    omega

lemma wfold_prefix (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (gs.foldl wstep xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hlen : i < (wstep xs g).length := by simp [wstep]; omega
    rw [ih (wstep xs g) hlen, List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ hi]
    simp [wstep, List.getElem_append_left hi]

lemma wfold_gate (gs : List Gate) (xs : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl wstep xs).getD (xs.length + j) false =
      (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i => (gs.take j |>.foldl wstep xs).getD i false) := by
  induction gs generalizing xs j with
  | nil => simp at hj
  | cons g rest ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, Nat.add_zero, List.getElem_cons_zero, List.take_zero, List.foldl_nil]
      have hlt : xs.length < (wstep xs g).length := by simp [wstep]
      rw [wfold_prefix rest (wstep xs g) xs.length hlt, List.getD_eq_getElem _ _ hlt]
      simp [wstep]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ, List.take_succ_cons]
      have hlen : (wstep xs g).length = xs.length + 1 := by simp [wstep]
      have hj' : j' < rest.length := by simp at hj; omega
      have := ih (wstep xs g) j' hj'
      rw [hlen] at this
      simpa [Nat.add_assoc, Nat.add_comm 1 j'] using this

lemma eval_mono_op (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ (l1 l2 : List Bool), l1.length = l2.length →
      (∀ i < l1.length, l1[i]! = true → l2[i]! = true) →
      op.eval l1 = true → op.eval l2 = true := by
  intro l1 l2 hlen hle h1
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq] at h1 ⊢
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi1 : i < l1.length := by omega
    have h1i : l1[i]'hi1 = true := h1 _ (List.getElem_mem hi1)
    have h2i := hle i hi1 (by simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1] using h1i)
    simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h2i
  · simp only [GateOp.eval, List.any_eq_true, id_eq] at h1 ⊢
    obtain ⟨x, hx, rfl⟩ := h1
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    have hi2 : i < l2.length := by omega
    have h2i := hle i hi (by simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hix)
    exact ⟨l2[i]'hi2, List.getElem_mem hi2, by simpa [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi2] using h2i⟩

lemma wires_mono (gs : List Gate) (hM : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (hlen : xs.length = ys.length)
    (hle : ∀ i, xs.getD i false = true → ys.getD i false = true) :
    ∀ i, (gs.foldl wstep xs).getD i false = true → (gs.foldl wstep ys).getD i false = true := by
  induction gs generalizing xs ys with
  | nil => exact hle
  | cons g rest ih =>
    simp only [List.foldl_cons]
    refine ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (wstep xs g) (wstep ys g)
      (by simp [wstep, hlen]) ?_
    intro i hi
    by_cases hlt : i < xs.length
    · have h1 : (wstep xs g).getD i false = xs.getD i false := by
        rw [List.getD_eq_getElem _ _ (by simp [wstep]; omega), List.getD_eq_getElem _ _ hlt]
        simp [wstep, List.getElem_append_left hlt]
      have h2 : (wstep ys g).getD i false = ys.getD i false := by
        rw [List.getD_eq_getElem _ _ (by simp [wstep]; omega), List.getD_eq_getElem _ _ (by omega)]
        simp [wstep, List.getElem_append_left (by omega : i < ys.length)]
      rw [h1] at hi; rw [h2]; exact hle i hi
    · by_cases heq : i = xs.length
      · subst heq
        have h1 : (wstep xs g).getD xs.length false = g.op.eval (g.inputs.map fun k => xs.getD k false) := by
          rw [List.getD_eq_getElem _ _ (by simp [wstep])]; simp [wstep]
        have h2 : (wstep ys g).getD xs.length false = g.op.eval (g.inputs.map fun k => ys.getD k false) := by
          rw [hlen, List.getD_eq_getElem _ _ (by simp [wstep])]; simp [wstep]
        rw [h1] at hi; rw [h2]
        refine eval_mono_op g.op (hM g List.mem_cons_self) _ _ (by simp) ?_ hi
        intro k hk
        simp only [List.length_map] at hk
        simp only [List.getElem!_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp; exact hk : k < (g.inputs.map _).length),
          List.getElem_map, Option.getD_some]
        exact hle _
      · have hge : (wstep xs g).length ≤ i := by simp [wstep]; omega
        rw [List.getD_eq_default _ _ hge] at hi; cases hi

-- ============================================================
-- Part 1: Constant-false wire restriction (peeling 1 gate per essential input)
-- ============================================================

def rfStep (st : List Gate × List (Option ℕ)) (g : Gate) : List Gate × List (Option ℕ) :=
  let out := st.1
  let env := st.2
  match g.op with
  | GateOp.and =>
    if g.inputs.any (fun i => (env.getD i none).isNone) then
      (out, env ++ [none])
    else
      let ins' := g.inputs.filterMap (fun i => env.getD i none)
      (out ++ [{ op := GateOp.and, inputs := ins' }], env ++ [some (10 + out.length)])
  | GateOp.or =>
    let ins' := g.inputs.filterMap (fun i => env.getD i none)
    match ins' with
    | [] => (out, env ++ [none])
    | [w'] => (out, env ++ [some w'])
    | _ => (out ++ [{ op := GateOp.or, inputs := ins' }], env ++ [some (10 + out.length)])
  | _ => (out, env ++ [none])

def rfInit (k : ℕ) : List Gate × List (Option ℕ) :=
  ([], List.ofFn fun i : Fin 10 => if i.val = k then none else some i.val)

def restrictFalse (C : Circuit) (k : ℕ) : Circuit :=
  let res := C.gates.foldl rfStep (rfInit k)
  let outWire := match res.2.getD C.output none with
    | some w' => w'
    | none => 10 + res.1.length
  { gates := res.1, output := outWire }

lemma list_filterMap_len_le {α β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases h : f a <;> simp [h] <;> omega

lemma list_filterMap_len_lt {α β : Type} (f : α → Option β) (l : List α)
    (x : α) (hx : x ∈ l) (hnone : f x = none) :
    (l.filterMap f).length < l.length := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · simp only [List.filterMap_cons, hnone, List.length_cons]
      have := list_filterMap_len_le f t
      omega
    · have hlt := ih hxt
      cases h : f a with
      | none => simp only [List.filterMap_cons, h, List.length_cons]; omega
      | some b => simp only [List.filterMap_cons, h, List.length_cons]; omega

lemma rfStep_mono (st : List Gate × List (Option ℕ)) (g : Gate)
    (h1 : ∀ g' ∈ st.1, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g' ∈ (rfStep st g).1, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
  rcases st with ⟨out, env⟩
  rcases hg with ⟨hop, hlen⟩
  rcases hop with hop | hop
  · simp only [rfStep, hop]
    split_ifs
    · exact h1
    · intro g' hg'
      simp only [List.mem_append, List.mem_singleton] at hg'
      rcases hg' with h | rfl
      · exact h1 g' h
      · exact ⟨Or.inl rfl, (list_filterMap_len_le _ _).trans hlen⟩
  · simp only [rfStep, hop]
    cases hins : g.inputs.filterMap (fun i => env.getD i none) with
    | nil => exact h1
    | cons a t =>
      cases t with
      | nil => exact h1
      | cons b t2 =>
        intro g' hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with h | rfl
        · exact h1 g' h
        · have hl := list_filterMap_len_le (fun i => env.getD i none) g.inputs
          rw [hins] at hl
          exact ⟨Or.inr rfl, hl.trans hlen⟩

lemma rfStep_len_le (st : List Gate × List (Option ℕ)) (g : Gate) :
    (rfStep st g).1.length ≤ st.1.length + 1 := by
  rcases st with ⟨out, env⟩
  cases h : g.op
  · simp only [rfStep, h]; split_ifs <;> simp
  · simp only [rfStep, h]
    cases g.inputs.filterMap (fun i => env.getD i none) with
    | nil => simp
    | cons a t => cases t <;> simp
  · simp [rfStep, h]
  · simp [rfStep, h]
  · simp [rfStep, h]

lemma rfStep_env_len (st : List Gate × List (Option ℕ)) (g : Gate) :
    (rfStep st g).2.length = st.2.length + 1 := by
  rcases st with ⟨out, env⟩
  cases h : g.op
  · simp only [rfStep, h]; split_ifs <;> simp
  · simp only [rfStep, h]
    cases g.inputs.filterMap (fun i => env.getD i none) with
    | nil => simp
    | cons a t => cases t <;> simp
  · simp [rfStep, h]
  · simp [rfStep, h]
  · simp [rfStep, h]

lemma rfStep_env_prefix (st : List Gate × List (Option ℕ)) (g : Gate)
    (i : ℕ) (hi : i < st.2.length) :
    (rfStep st g).2.getD i none = st.2.getD i none := by
  rcases st with ⟨out, env⟩
  dsimp only at hi ⊢
  have hget : ∀ (x : Option ℕ), (env ++ [x]).getD i none = env.getD i none := fun x => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
    simp [List.getElem_append_left hi]
  cases h : g.op
  · simp only [rfStep, h]; split_ifs <;> exact hget _
  · simp only [rfStep, h]
    cases g.inputs.filterMap (fun i => env.getD i none) with
    | nil => exact hget _
    | cons a t => cases t <;> exact hget _
  · simp only [rfStep, h]; exact hget _
  · simp only [rfStep, h]; exact hget _
  · simp only [rfStep, h]; exact hget _

lemma rfStep_drop (st : List Gate × List (Option ℕ)) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (hk : k ∈ g.inputs) (hnone : st.2.getD k none = none) :
    (rfStep st g).1.length = st.1.length := by
  rcases st with ⟨out, env⟩
  dsimp only at hnone ⊢
  rcases hg with ⟨hop, hlen⟩
  rcases hop with hop | hop
  · simp only [rfStep, hop]
    have hany : g.inputs.any (fun i => (env.getD i none).isNone) = true := by
      rw [List.any_eq_true]
      exact ⟨k, hk, by rw [hnone]; rfl⟩
    simp only [hany, ite_true]
  · simp only [rfStep, hop]
    have hlt := list_filterMap_len_lt (fun i => env.getD i none) g.inputs k hk hnone
    cases hins : g.inputs.filterMap (fun i => env.getD i none) with
    | nil => rfl
    | cons a t =>
      cases t with
      | nil => rfl
      | cons b t2 =>
        rw [hins] at hlt
        simp only [List.length_cons] at hlt
        omega

lemma rfFold_env_prefix (gs : List Gate) (st : List Gate × List (Option ℕ))
    (i : ℕ) (hi : i < st.2.length) :
    (gs.foldl rfStep st).2.getD i none = st.2.getD i none := by
  induction gs generalizing st with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hi' : i < (rfStep st g).2.length := by rw [rfStep_env_len]; omega
    rw [ih (rfStep st g) hi', rfStep_env_prefix st g i hi]

lemma rfFold_len_le (gs : List Gate) (st : List Gate × List (Option ℕ)) :
    (gs.foldl rfStep st).1.length ≤ st.1.length + gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (rfStep st g)
    have h2 := rfStep_len_le st g
    omega

lemma rfFold_len_lt (gs : List Gate) (st : List Gate × List (Option ℕ))
    (hM : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (hklen : k < st.2.length) (hknone : st.2.getD k none = none)
    (hmem : ∃ g ∈ gs, k ∈ g.inputs) :
    (gs.foldl rfStep st).1.length + 1 ≤ st.1.length + gs.length := by
  induction gs generalizing st with
  | nil => obtain ⟨_, hg, _⟩ := hmem; cases hg
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    obtain ⟨g0, hg0, hkg0⟩ := hmem
    simp only [List.mem_cons] at hg0
    rcases hg0 with rfl | hrest
    · have h1 := rfFold_len_le rest (rfStep st g0)
      have h2 := rfStep_drop st g0 (hM g0 List.mem_cons_self) k hkg0 hknone
      omega
    · have h1 := ih (rfStep st g) (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg'))
        (by rw [rfStep_env_len]; omega)
        (by rw [rfStep_env_prefix st g k hklen]; exact hknone)
        ⟨g0, hrest, hkg0⟩
      have h2 := rfStep_len_le st g
      omega

lemma rfFold_mono (gs : List Gate) (st : List Gate × List (Option ℕ))
    (h1 : ∀ g' ∈ st.1, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2)
    (hM : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g' ∈ (gs.foldl rfStep st).1, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
  induction gs generalizing st with
  | nil => exact h1
  | cons g rest ih =>
    simp only [List.foldl_cons]
    exact ih (rfStep st g) (rfStep_mono st g h1 (hM g List.mem_cons_self))
      (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg'))

lemma rfFold_eval_inv (gs : List Gate) (xs : List Bool) (hxl : xs.length = 10)
    (hM : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ws : List Bool) (st : List Gate × List (Option ℕ))
    (hlen_ws : ws.length = st.2.length)
    (hinv : ∀ i, match st.2.getD i none with
      | none => ws.getD i false = false
      | some w' => w' < 10 + st.1.length ∧ ws.getD i false = (st.1.foldl wstep xs).getD w' false) :
    let ws' := gs.foldl wstep ws
    let st' := gs.foldl rfStep st
    ws'.length = st'.2.length ∧
    ∀ i, match st'.2.getD i none with
      | none => ws'.getD i false = false
      | some w' => w' < 10 + st'.1.length ∧ ws'.getD i false = (st'.1.foldl wstep xs).getD w' false := by
  induction gs generalizing ws st with
  | nil => exact ⟨hlen_ws, hinv⟩
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hg := hM g List.mem_cons_self
    rcases st with ⟨out, env⟩
    dsimp only at hlen_ws hinv
    have hws'_len : (wstep ws g).length = env.length + 1 := by simp [wstep, hlen_ws]
    have hget_old : ∀ i < env.length, (wstep ws g).getD i false = ws.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [wstep]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [wstep, List.getElem_append_left (by omega : i < ws.length)]
    have hget_last : (wstep ws g).getD env.length false = g.op.eval (g.inputs.map fun i => ws.getD i false) := by
      rw [← hlen_ws, List.getD_eq_getElem _ _ (by simp [wstep])]; simp [wstep]
    have hget_hi : ∀ i, env.length + 1 ≤ i → (wstep ws g).getD i false = false := fun i hi =>
      List.getD_eq_default _ _ (by omega)
    have hstep_inv :
        (wstep ws g).length = (rfStep (out, env) g).2.length ∧
        ∀ i, match (rfStep (out, env) g).2.getD i none with
          | none => (wstep ws g).getD i false = false
          | some w' => w' < 10 + (rfStep (out, env) g).1.length ∧
              (wstep ws g).getD i false = ((rfStep (out, env) g).1.foldl wstep xs).getD w' false := by
      constructor
      · rw [rfStep_env_len]; exact hws'_len
      · have hfold_app : ∀ (gnew : Gate),
            ((out ++ [gnew]).foldl wstep xs) = wstep (out.foldl wstep xs) gnew := fun gnew => by
          rw [List.foldl_append]; rfl
        have hkeep_old : ∀ (x : Option ℕ) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i none with
            | none => (wstep ws g).getD i false = false
            | some w' => w' < 10 + out.length ∧ (wstep ws g).getD i false = (out.foldl wstep xs).getD w' false := by
          intro x i hi
          have h1 : (env ++ [x]).getD i none = env.getD i none := by
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
            simp [List.getElem_append_left hi]
          rw [h1, hget_old i hi]
          exact hinv i
        have hkeep_old_app : ∀ (x : Option ℕ) (gnew : Gate) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i none with
            | none => (wstep ws g).getD i false = false
            | some w' => w' < 10 + (out ++ [gnew]).length ∧
                (wstep ws g).getD i false = ((out ++ [gnew]).foldl wstep xs).getD w' false := by
          intro x gnew i hi
          have hk := hkeep_old x i hi
          cases hm : (env ++ [x]).getD i none with
          | none => rw [hm] at hk; exact hk
          | some w' =>
            rw [hm] at hk
            dsimp only at hk
            have hw' : w' < 10 + out.length := hk.1
            refine ⟨by simp; omega, ?_⟩
            rw [hk.2, hfold_app gnew]
            have hlen_out : (out.foldl wstep xs).length = 10 + out.length := by rw [wfold_len, hxl]
            have hlen_w : (wstep (out.foldl wstep xs) gnew).length = 10 + out.length + 1 := by simp [wstep, hlen_out]
            rw [List.getD_eq_getElem _ _ (by omega : w' < (out.foldl wstep xs).length),
                List.getD_eq_getElem _ _ (by omega : w' < (wstep (out.foldl wstep xs) gnew).length)]
            simp [wstep, List.getElem_append_left (by omega : w' < (out.foldl wstep xs).length)]
        have hkeep_hi : ∀ (x : Option ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
            (env ++ [x]).getD i none = none := fun x i hi =>
          List.getD_eq_default _ _ (by simp; omega)
        have hget_env_last : ∀ (x : Option ℕ), (env ++ [x]).getD env.length none = x := fun x => by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        rcases hg.1 with hop | hop
        · simp only [rfStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old none i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last none, hget_last, hop]
                simp only [GateOp.eval, List.all_eq_false, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjnone⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j none with
                | none =>
                  rw [hm] at hj'
                  dsimp only at hj'
                  exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, by rw [hj']; decide⟩
                | some w' =>
                  rw [hm] at hjnone
                  simp at hjnone
              · rw [hkeep_hi none i (by omega)]; exact hget_hi i (by omega)
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old_app (some (10 + out.length)) _ i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (some (10 + out.length))]
                refine ⟨by simp, ?_⟩
                rw [hget_last, hop, hfold_app]
                have hlen_out : (out.foldl wstep xs).length = 10 + out.length := by rw [wfold_len, hxl]
                rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [wstep])]
                simp only [wstep, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                congr 1
                have hall_some : ∀ j ∈ g.inputs, (env.getD j none).isSome = true := by
                  intro j hj
                  cases h : env.getD j none with
                  | some w' => rfl
                  | none =>
                    exfalso
                    apply hany
                    rw [List.any_eq_true]
                    exact ⟨j, hj, by rw [h]; rfl⟩
                have hlist : ∀ l : List ℕ, (∀ j ∈ l, (env.getD j none).isSome = true) →
                    (l.map fun i => ws.getD i false) =
                    ((l.filterMap fun i => env.getD i none).map fun i => (out.foldl wstep xs).getD i false) := by
                  intro l
                  induction l with
                  | nil => intro _; rfl
                  | cons a t iht =>
                    intro hall
                    have ha := hall a List.mem_cons_self
                    have hia := hinv a
                    cases hm : env.getD a none with
                    | none => rw [hm] at ha; simp at ha
                    | some w' =>
                      rw [hm] at hia
                      dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, hia.2]
                      congr 1
                      exact iht (fun j hj => hall j (List.mem_cons_of_mem _ hj))
                exact hlist g.inputs hall_some
              · rw [hkeep_hi (some (10 + out.length)) i (by omega)]; exact hget_hi i (by omega)
        · simp only [rfStep, hop]
          have hor_eq : (g.inputs.map fun j => ws.getD j false).any id =
              ((g.inputs.filterMap fun j => env.getD j none).map fun w' => (out.foldl wstep xs).getD w' false).any id := by
            have hlist : ∀ l : List ℕ, (l.map fun j => ws.getD j false).any id =
                ((l.filterMap fun j => env.getD j none).map fun w' => (out.foldl wstep xs).getD w' false).any id := by
              intro l
              induction l with
              | nil => rfl
              | cons a t iht =>
                have hia := hinv a
                cases hm : env.getD a none with
                | none =>
                  rw [hm] at hia
                  dsimp only at hia
                  simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia, Bool.false_or, iht]
                | some w' =>
                  rw [hm] at hia
                  dsimp only at hia
                  simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia.2, iht]
            exact hlist g.inputs
          have hmem_bound : ∀ w' ∈ g.inputs.filterMap (fun j => env.getD j none), w' < 10 + out.length := by
            intro w' hw'
            obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw'
            have hij := hinv j
            rw [hj] at hij
            exact hij.1
          cases hins : g.inputs.filterMap (fun j => env.getD j none) with
          | nil =>
            rw [hins] at hor_eq
            intro i
            by_cases hi : i < env.length
            · exact hkeep_old none i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last none, hget_last, hop]
                simpa [GateOp.eval] using hor_eq
              · rw [hkeep_hi none i (by omega)]; exact hget_hi i (by omega)
          | cons a t =>
            cases t with
            | nil =>
              rw [hins] at hor_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (some a) i hi
              · by_cases heq : i = env.length
                · subst heq
                  rw [hget_env_last (some a)]
                  refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                  rw [hget_last, hop]
                  simpa [GateOp.eval] using hor_eq
                · rw [hkeep_hi (some a) i (by omega)]; exact hget_hi i (by omega)
            | cons b t2 =>
              rw [hins] at hor_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old_app (some (10 + out.length)) _ i hi
              · by_cases heq : i = env.length
                · subst heq
                  rw [hget_env_last (some (10 + out.length))]
                  refine ⟨by simp, ?_⟩
                  rw [hget_last, hop, hfold_app]
                  have hlen_out : (out.foldl wstep xs).length = 10 + out.length := by rw [wfold_len, hxl]
                  rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [wstep])]
                  simp only [wstep, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                  simpa [GateOp.eval] using hor_eq
                · rw [hkeep_hi (some (10 + out.length)) i (by omega)]; exact hget_hi i (by omega)
    exact ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (wstep ws g) (rfStep (out, env) g)
      hstep_inv.1 hstep_inv.2

lemma restrictFalse_mono (C : Circuit) (hM : Monotone2 C) (k : ℕ) :
    Monotone2 (restrictFalse C k) := by
  intro g hg
  have h1 := rfFold_mono C.gates (rfInit k) (by intro g' h; cases h)
    (fun g' hg' => ⟨by simpa using (hM g' hg').1, (hM g' hg').2⟩) g hg
  exact ⟨by simpa using h1.1, h1.2⟩

lemma restrictFalse_eval (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < 10)
    (xs : List Bool) (hxl : xs.length = 10) (hxk : xs.getD k false = false) :
    (restrictFalse C k).eval xs = C.eval xs := by
  have hinit : ∀ i, match (rfInit k).2.getD i none with
      | none => xs.getD i false = false
      | some w' => w' < 10 + (rfInit k).1.length ∧ xs.getD i false = ((rfInit k).1.foldl wstep xs).getD w' false := by
    intro i
    by_cases hi : i < 10
    · have hlen : i < (rfInit k).2.length := by simp [rfInit, hi]
      rw [List.getD_eq_getElem _ _ hlen]
      change match (List.ofFn fun j : Fin 10 => if j.val = k then none else some j.val)[i]'(by simp [hi]) with
        | none => xs.getD i false = false
        | some w' => w' < 10 + 0 ∧ xs.getD i false = xs.getD w' false
      rw [List.getElem_ofFn]
      by_cases hik : i = k
      · subst hik; simp only [ite_true]; exact hxk
      · simp [hik, hi]
    · have hge : (rfInit k).2.length ≤ i := by simp [rfInit]; omega
      rw [List.getD_eq_default _ _ hge]
      exact List.getD_eq_default _ _ (by omega)
  have hinv := rfFold_eval_inv C.gates xs hxl
    (fun g' hg' => ⟨by simpa using (hM g' hg').1, (hM g' hg').2⟩)
    xs (rfInit k) (by simp [rfInit, hxl]) hinit
  have hres := hinv.2 C.output
  change ((C.gates.foldl rfStep (rfInit k)).1.foldl wstep xs).getD
      (match (C.gates.foldl rfStep (rfInit k)).2.getD C.output none with
        | some w' => w' | none => 10 + (C.gates.foldl rfStep (rfInit k)).1.length) false =
      (C.gates.foldl wstep xs).getD C.output false
  cases hm : (C.gates.foldl rfStep (rfInit k)).2.getD C.output none with
  | none =>
    rw [hm] at hres
    rw [hres]
    exact List.getD_eq_default _ _ (by rw [wfold_len, hxl])
  | some w' =>
    rw [hm] at hres
    exact hres.2.symm

lemma restrictFalse_size_lt (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < 10)
    (hmem : ∃ g ∈ C.gates, k ∈ g.inputs) :
    (restrictFalse C k).size + 1 ≤ C.size := by
  have hklen : k < (rfInit k).2.length := by simp [rfInit, hk]
  have hknone : (rfInit k).2.getD k none = none := by
    rw [List.getD_eq_getElem _ _ hklen]
    change (List.ofFn fun j : Fin 10 => if j.val = k then none else some j.val)[k]'(by simp [hk]) = none
    rw [List.getElem_ofFn]; simp
  have h := rfFold_len_lt C.gates (rfInit k)
    (fun g' hg' => ⟨by simpa using (hM g' hg').1, (hM g' hg').2⟩)
    k hklen hknone hmem
  simpa [restrictFalse, Circuit.size, rfInit] using h

lemma wires_agree_ignoring_k (gs : List Gate) (k : ℕ)
    (hno : ∀ g ∈ gs, k ∉ g.inputs)
    (xs ys : List Bool) (hxl : xs.length = ys.length)
    (hagree : ∀ i, i ≠ k → xs.getD i false = ys.getD i false) :
    ∀ i, i ≠ k → (gs.foldl wstep xs).getD i false = (gs.foldl wstep ys).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact hagree
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hgk : k ∉ g.inputs := hno g List.mem_cons_self
    refine ih (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (wstep xs g) (wstep ys g)
      (by simp [wstep, hxl]) ?_
    intro i hik
    by_cases hlt : i < xs.length
    · rw [List.getD_eq_getElem _ _ (by simp [wstep]; omega),
          List.getD_eq_getElem _ _ (by simp [wstep]; omega)]
      simp only [wstep, List.getElem_append_left hlt, List.getElem_append_left (by omega : i < ys.length)]
      have := hagree i hik
      rwa [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ (by omega : i < ys.length)] at this
    · by_cases heq : i = xs.length
      · subst heq
        have h1 : (wstep xs g).getD xs.length false = g.op.eval (g.inputs.map fun j => xs.getD j false) := by
          rw [List.getD_eq_getElem _ _ (by simp [wstep])]; simp [wstep]
        have h2 : (wstep ys g).getD xs.length false = g.op.eval (g.inputs.map fun j => ys.getD j false) := by
          rw [hxl, List.getD_eq_getElem _ _ (by simp [wstep])]; simp [wstep]
        rw [h1, h2]
        congr 1
        apply List.map_congr_left
        intro j hj
        exact hagree j (fun e => hgk (e ▸ hj))
      · rw [List.getD_eq_default _ _ (by simp [wstep]; omega),
            List.getD_eq_default _ _ (by simp [wstep]; omega)]

lemma essential_in_gates (C : Circuit) (hM : Monotone2 C) (k : ℕ) (hk : k < 10)
    (xs ys zs : List Bool) (hxl : xs.length = 10) (hyl : ys.length = 10) (hzl : zs.length = 10)
    (hxs : C.eval xs = true) (hys : C.eval ys = false)
    (hzs_k : zs.getD k false = true) (hzs_f : C.eval zs = false)
    (hdom : ∀ i < 10, i ≠ k → xs.getD i false = true → ys.getD i false = true) :
    ∃ g ∈ C.gates, k ∈ g.inputs := by
  have hout_ne : C.output ≠ k := by
    intro heq
    have h1 : C.eval zs = zs.getD k false := by
      change (C.gates.foldl wstep zs).getD C.output false = zs.getD k false
      rw [heq, wfold_prefix _ _ _ (by omega)]
    rw [hzs_f, hzs_k] at h1; cases h1
  by_contra hno_ex
  have hno : ∀ g ∈ C.gates, k ∉ g.inputs := fun g hg hk => hno_ex ⟨g, hg, hk⟩
  let xs0 := List.ofFn fun j : Fin 10 => if j.val = k then false else xs.getD j.val false
  have hxs0_len : xs0.length = 10 := by simp [xs0]
  have hag : ∀ i, i ≠ k → xs.getD i false = xs0.getD i false := by
    intro i hik
    by_cases hi : i < 10
    · rw [List.getD_eq_getElem xs0 false (by simp [xs0, hi])]
      change xs.getD i false = (List.ofFn fun j : Fin 10 => if j.val = k then false else xs.getD j.val false)[i]'(by simp [hi])
      rw [List.getElem_ofFn]; simp [hik]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  have heq : C.eval xs = C.eval xs0 :=
    wires_agree_ignoring_k C.gates k hno xs xs0 (by omega) hag C.output hout_ne
  have hxs0_t : C.eval xs0 = true := by rw [← heq, hxs]
  have hle : ∀ i, xs0.getD i false = true → ys.getD i false = true := by
    intro i hi
    by_cases hi10 : i < 10
    · rw [List.getD_eq_getElem xs0 false (by simp [xs0, hi10])] at hi
      change (List.ofFn fun j : Fin 10 => if j.val = k then false else xs.getD j.val false)[i]'(by simp [hi10]) = true at hi
      rw [List.getElem_ofFn] at hi
      by_cases hik : i = k
      · simp [hik] at hi
      · simp only [hik, ite_false] at hi
        exact hdom i hi10 hik hi
    · rw [List.getD_eq_default _ _ (by omega)] at hi; cases hi
  have hyt : C.eval ys = true :=
    wires_mono C.gates (fun g hg => by simpa using (hM g hg).1) xs0 ys (by omega) hle C.output hxs0_t
  rw [hys] at hyt; cases hyt

-- ============================================================
-- Part 2: 1-Reused-Wire Dominator + no_P4_gen + no_MAJ3_with_Z on 10 wires
-- ============================================================

def gateIns (gs : List Gate) (w : ℕ) : Finset ℕ :=
  if 10 ≤ w then
    match gs[w - 10]? with
    | some g => (g.inputs.filter fun i => decide (i < w)).toFinset
    | none => ∅
  else ∅

def stepReach (gs : List Gate) (S : Finset ℕ) : Finset ℕ :=
  S ∪ S.biUnion (gateIns gs)

def reachN (gs : List Gate) (out : ℕ) : ℕ → Finset ℕ
  | 0 => {out}
  | n + 1 => stepReach gs (reachN gs out n)

lemma reachN_sub (gs : List Gate) (out n : ℕ) : reachN gs out n ⊆ reachN gs out (n + 1) :=
  Finset.subset_union_left

lemma reachN_mono (gs : List Gate) (out : ℕ) {a b : ℕ} (h : a ≤ b) :
    reachN gs out a ⊆ reachN gs out b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    exact Finset.Subset.refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · exact (ih hab).trans (reachN_sub gs out b)
    · have ha : a = b + 1 := by omega
      subst ha
      exact Finset.Subset.refl _

lemma out_mem_reachN (gs : List Gate) (out n : ℕ) : out ∈ reachN gs out n :=
  reachN_mono gs out (Nat.zero_le n) (by simp [reachN])

lemma gateIns_lt (gs : List Gate) (w i : ℕ) (hi : i ∈ gateIns gs w) : i < w := by
  unfold gateIns at hi
  split_ifs at hi with h10
  · cases hg : gs[w - 10]? with
    | none => rw [hg] at hi; cases hi
    | some g =>
      rw [hg] at hi
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hi
      exact hi.2
  · cases hi

lemma gateIns_sub_gt (gs : List Gate) (w i : ℕ) (hi : i ∈ gateIns gs w) : 10 ≤ w ∧ w < 10 + gs.length := by
  unfold gateIns at hi
  split_ifs at hi with h10
  · cases hg : gs[w - 10]? with
    | none => rw [hg] at hi; cases hi
    | some g =>
      have hlt : w - 10 < gs.length := by
        by_contra hge
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hg; cases hg
      omega
  · cases hi

lemma reachN_le_out (gs : List Gate) (out n w : ℕ) (hw : w ∈ reachN gs out n) : w ≤ out := by
  induction n generalizing w with
  | zero => simp [reachN] at hw; omega
  | succ n ih =>
    simp only [reachN, stepReach, Finset.mem_union, Finset.mem_biUnion] at hw
    rcases hw with h | ⟨u, hu, hiu⟩
    · exact ih w h
    · exact le_trans (Nat.le_of_lt (gateIns_lt gs u w hiu)) (ih u hu)

lemma reachN_gate_dist (gs : List Gate) (out n w : ℕ) (hw : w ∈ reachN gs out n)
    (h10 : 10 ≤ w) (hlt : w < 10 + gs.length) :
    w ∈ reachN gs out ((10 + gs.length - 1) - w) := by
  induction n generalizing w with
  | zero =>
    simp only [reachN, Finset.mem_singleton] at hw; subst hw
    exact out_mem_reachN gs w _
  | succ n ih =>
    simp only [reachN, stepReach, Finset.mem_union, Finset.mem_biUnion] at hw
    rcases hw with h | ⟨u, hu, hiu⟩
    · exact ih w h h10 hlt
    · have ⟨hu10, hult⟩ := gateIns_sub_gt gs u w hiu
      have hwlt : w < u := gateIns_lt gs u w hiu
      have hu_in : u ∈ reachN gs out ((10 + gs.length - 1) - u) := ih u hu hu10 hult
      have hstep : w ∈ reachN gs out (((10 + gs.length - 1) - u) + 1) :=
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨u, hu_in, hiu⟩)
      exact reachN_mono gs out (by omega) hstep

lemma reachN_closed (gs : List Gate) (out w i : ℕ)
    (hw : w ∈ reachN gs out (gs.length + 1)) (hi : i ∈ gateIns gs w) :
    i ∈ reachN gs out (gs.length + 1) := by
  have ⟨hw10, hwlt⟩ := gateIns_sub_gt gs w i hi
  have hw' : w ∈ reachN gs out ((10 + gs.length - 1) - w) := reachN_gate_dist gs out _ w hw hw10 hwlt
  have hstep : i ∈ reachN gs out (((10 + gs.length - 1) - w) + 1) :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hw', hi⟩)
  exact reachN_mono gs out (by omega) hstep

lemma reachN_sub_of_mem (gs : List Gate) (out u : ℕ)
    (hu : u ∈ reachN gs out (gs.length + 1)) (m : ℕ) :
    reachN gs u m ⊆ reachN gs out (gs.length + 1) := by
  induction m with
  | zero => intro x hx; simp [reachN] at hx; subst hx; exact hu
  | succ m ih =>
    intro x hx
    simp only [reachN, stepReach, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with h | ⟨y, hy, hxy⟩
    · exact ih h
    · exact reachN_closed gs out y x (ih hy) hxy

lemma reachN_erase_sub_biUnion (gs : List Gate) (out n : ℕ) :
    (reachN gs out n).erase out ⊆
      ((reachN gs out n).filter fun w => 10 ≤ w ∧ w < 10 + gs.length).biUnion (gateIns gs) := by
  intro i hi
  rw [Finset.mem_erase] at hi
  obtain ⟨hne, hmem⟩ := hi
  induction n with
  | zero => simp [reachN] at hmem; exact absurd hmem hne
  | succ n ih =>
    simp only [reachN, stepReach, Finset.mem_union, Finset.mem_biUnion] at hmem
    rcases hmem with h | ⟨u, hu, hiu⟩
    · have h1 := ih h
      rw [Finset.mem_biUnion] at h1 ⊢
      obtain ⟨u, hu, hiu⟩ := h1
      rw [Finset.mem_filter] at hu
      exact ⟨u, Finset.mem_filter.mpr ⟨reachN_sub gs out n hu.1, hu.2⟩, hiu⟩
    · have ⟨hu10, hult⟩ := gateIns_sub_gt gs u i hiu
      exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_filter.mpr ⟨reachN_sub gs out n hu, hu10, hult⟩, hiu⟩

lemma wires_agree_on_reach (gs : List Gate) (out : ℕ) (xs ys : List Bool)
    (hxl : xs.length = 10) (hyl : ys.length = 10)
    (hagree : ∀ i < 10, i ∈ reachN gs out (gs.length + 1) →
      xs.getD i false = ys.getD i false) :
    ∀ w, w ∈ reachN gs out (gs.length + 1) →
      (gs.foldl wstep xs).getD w false = (gs.foldl wstep ys).getD w false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases h10 : w < 10
    · rw [wfold_prefix _ _ _ (by omega), wfold_prefix _ _ _ (by omega)]
      exact hagree w h10 hw
    · by_cases hlt : w < 10 + gs.length
      · have hj : w - 10 < gs.length := by omega
        have hwx : w = xs.length + (w - 10) := by omega
        have hwy : w = ys.length + (w - 10) := by omega
        have hx1 := wfold_gate gs xs (w - 10) hj
        have hy1 := wfold_gate gs ys (w - 10) hj
        rw [← hwx] at hx1; rw [← hwy] at hy1
        rw [hx1, hy1]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hlenx : ((gs.take (w - 10)).foldl wstep xs).length = w := by
          rw [wfold_len, hxl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
        have hleny : ((gs.take (w - 10)).foldl wstep ys).length = w := by
          rw [wfold_len, hyl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
        by_cases hiw : i < w
        · have hi_ins : i ∈ gateIns gs w := by
            unfold gateIns
            rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega : 10 ≤ w)), List.getElem?_eq_getElem hj]
            simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
            exact ⟨hi, hiw⟩
          have hi_reach := reachN_closed gs out w i hw hi_ins
          have heq := ih i hiw hi_reach
          have hsp : gs = gs.take (w - 10) ++ gs.drop (w - 10) := (List.take_append_drop _ _).symm
          conv at heq => lhs; rw [hsp, List.foldl_append]
          conv at heq => rhs; rw [hsp, List.foldl_append]
          rw [wfold_prefix (gs.drop (w - 10)) _ _ (by omega),
              wfold_prefix (gs.drop (w - 10)) _ _ (by omega)] at heq
          exact heq
        · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · rw [List.getD_eq_default _ _ (by rw [wfold_len, hxl]; omega),
            List.getD_eq_default _ _ (by rw [wfold_len, hyl]; omega)]

lemma sum_card_eq_biUnion_add_excess (G : Finset ℕ) (f : ℕ → Finset ℕ) :
    ∑ w ∈ G, (f w).card =
      (G.biUnion f).card + ∑ x ∈ G.biUnion f, ((G.filter fun w => x ∈ f w).card - 1) := by
  have h1 : ∑ w ∈ G, (f w).card = ∑ w ∈ G, ∑ x ∈ G.biUnion f, if x ∈ f w then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.sum_boole]
    have hsub : (G.biUnion f).filter (fun x => x ∈ f w) = f w := by
      ext x; simp only [Finset.mem_filter, Finset.mem_biUnion, and_iff_right_iff_imp]
      intro hx; exact ⟨w, hw, hx⟩
    simp [hsub]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ x ∈ G.biUnion f, (∑ w ∈ G, if x ∈ f w then 1 else 0) =
      1 + ((G.filter fun w => x ∈ f w).card - 1) := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := Finset.mem_biUnion.mp hx
    have hpos : 1 ≤ (G.filter fun w => x ∈ f w).card :=
      Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hxw⟩⟩
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    omega
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  simp

lemma biUnion_disjoint_of_card_eq {G : Finset ℕ} {f : ℕ → Finset ℕ}
    (heq : (G.biUnion f).card = ∑ w ∈ G, (f w).card) :
    ∀ w1 ∈ G, ∀ w2 ∈ G, w1 ≠ w2 → Disjoint (f w1) (f w2) := by
  intro w1 hw1 w2 hw2 hne
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  have hex := sum_card_eq_biUnion_add_excess G f
  have hxbi : x ∈ G.biUnion f := Finset.mem_biUnion.mpr ⟨w1, hw1, hx1⟩
  have h2 : 2 ≤ (G.filter fun w => x ∈ f w).card := by
    have hsub : ({w1, w2} : Finset ℕ) ⊆ G.filter fun w => x ∈ f w := by
      intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hw1, hx1⟩
      · exact Finset.mem_filter.mpr ⟨hw2, hx2⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at hc; exact hc
  have hge1 : 1 ≤ ∑ y ∈ G.biUnion f, ((G.filter fun w => y ∈ f w).card - 1) := by
    have hle := Finset.single_le_sum (f := fun y => (G.filter fun w => y ∈ f w).card - 1)
      (fun _ _ => Nat.zero_le _) hxbi
    omega
  omega

lemma biUnion_at_most_one_overlap {G : Finset ℕ} {f : ℕ → Finset ℕ}
    (hle : ∑ w ∈ G, (f w).card ≤ (G.biUnion f).card + 1) :
    (∀ w1 ∈ G, ∀ w2 ∈ G, w1 ≠ w2 → Disjoint (f w1) (f w2)) ∨
    (∃ z ∈ G.biUnion f,
      (∃ w1 ∈ G, ∃ w2 ∈ G, w1 ≠ w2 ∧ z ∈ f w1 ∧ z ∈ f w2) ∧
      ∀ w1 ∈ G, ∀ w2 ∈ G, w1 ≠ w2 → ∀ x, x ∈ f w1 → x ∈ f w2 → x = z) := by
  by_cases hd : ∀ w1 ∈ G, ∀ w2 ∈ G, w1 ≠ w2 → Disjoint (f w1) (f w2)
  · exact Or.inl hd
  · right
    have hex : ∃ w1 ∈ G, ∃ w2 ∈ G, w1 ≠ w2 ∧ ∃ z, z ∈ f w1 ∧ z ∈ f w2 := by
      by_contra hnone
      apply hd
      intro w1 hw1 w2 hw2 hne
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      exact hnone ⟨w1, hw1, w2, hw2, hne, z, hz1, hz2⟩
    obtain ⟨w1, hw1, w2, hw2, hne, z, hz1, hz2⟩ := hex
    refine ⟨z, Finset.mem_biUnion.mpr ⟨w1, hw1, hz1⟩, ⟨w1, hw1, w2, hw2, hne, hz1, hz2⟩, ?_⟩
    intro u1 hu1 u2 hu2 hune x hx1 hx2
    by_contra hxz
    have hsum := sum_card_eq_biUnion_add_excess G f
    have hzbi : z ∈ G.biUnion f := Finset.mem_biUnion.mpr ⟨w1, hw1, hz1⟩
    have hxbi : x ∈ G.biUnion f := Finset.mem_biUnion.mpr ⟨u1, hu1, hx1⟩
    have hz2c : 2 ≤ (G.filter fun w => z ∈ f w).card := by
      have hsub : ({w1, w2} : Finset ℕ) ⊆ G.filter fun w => z ∈ f w := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hw1, hz1⟩
        · exact Finset.mem_filter.mpr ⟨hw2, hz2⟩
      have hc := Finset.card_le_card hsub; rw [Finset.card_pair hne] at hc; exact hc
    have hx2c : 2 ≤ (G.filter fun w => x ∈ f w).card := by
      have hsub : ({u1, u2} : Finset ℕ) ⊆ G.filter fun w => x ∈ f w := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hu1, hx1⟩
        · exact Finset.mem_filter.mpr ⟨hu2, hx2⟩
      have hc := Finset.card_le_card hsub; rw [Finset.card_pair hune] at hc; exact hc
    have hpair : ({x, z} : Finset ℕ) ⊆ G.biUnion f := by
      intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> assumption
    have hge2 : ∑ y ∈ ({x, z} : Finset ℕ), ((G.filter fun w => y ∈ f w).card - 1) ≤
        ∑ y ∈ G.biUnion f, ((G.filter fun w => y ∈ f w).card - 1) :=
      Finset.sum_le_sum_of_subset hpair
    rw [Finset.sum_pair hxz] at hge2
    omega

lemma sum_eq_two_mul_imp {G : Finset ℕ} {f : ℕ → ℕ}
    (hle : ∀ w ∈ G, f w ≤ 2) (heq : ∑ w ∈ G, f w = 2 * G.card) :
    ∀ w ∈ G, f w = 2 := by
  intro w hw
  have hsum : ∑ u ∈ G, f u = f w + ∑ u ∈ G.erase w, f u := (Finset.add_sum_erase G f hw).symm
  have hrest : ∑ u ∈ G.erase w, f u ≤ ∑ _u ∈ G.erase w, 2 :=
    Finset.sum_le_sum fun u hu => hle u (Finset.mem_of_mem_erase hu)
  simp only [Finset.sum_const, smul_eq_mul] at hrest
  have hcard : (G.erase w).card + 1 = G.card := Finset.card_erase_add_one hw
  have hw2 := hle w hw
  omega

lemma sum_eq_two_mul_sub_one_imp {G : Finset ℕ} {f : ℕ → ℕ}
    (hle : ∀ w ∈ G, f w ≤ 2) (heq : ∑ w ∈ G, f w = 2 * G.card - 1) :
    ∀ w ∈ G, f w = 1 ∨ f w = 2 := by
  intro w hw
  have hsum : ∑ u ∈ G, f u = f w + ∑ u ∈ G.erase w, f u := (Finset.add_sum_erase G f hw).symm
  have hrest : ∑ u ∈ G.erase w, f u ≤ ∑ _u ∈ G.erase w, 2 :=
    Finset.sum_le_sum fun u hu => hle u (Finset.mem_of_mem_erase hu)
  simp only [Finset.sum_const, smul_eq_mul] at hrest
  have hcard : (G.erase w).card + 1 = G.card := Finset.card_erase_add_one hw
  have hw2 := hle w hw
  omega

lemma gateIns_card_two (C : Circuit) (hM : Monotone2 C) (w : ℕ)
    (h10 : 10 ≤ w) (hlt : w < 10 + C.gates.length) (hcard : (gateIns C.gates w).card = 2) :
    ∃ a b, (C.gates[w - 10]'(by omega)).inputs = [a, b] ∧ a < w ∧ b < w ∧ a ≠ b ∧
      gateIns C.gates w = {a, b} := by
  have hj : w - 10 < C.gates.length := by omega
  obtain ⟨_, hlen⟩ := hM _ (List.getElem_mem hj)
  unfold gateIns at hcard
  rw [ite_eq_left_of_eq_true _ _ (eq_true h10), List.getElem?_eq_getElem hj] at hcard
  dsimp only at hcard
  match hins : (C.gates[w - 10]'hj).inputs with
  | [] => rw [hins] at hcard; simp at hcard
  | [a] =>
    rw [hins] at hcard
    have := (List.toFinset_card_le ([a].filter fun i => decide (i < w))).trans (List.length_filter_le _ _)
    simp only [List.length_singleton] at this; omega
  | [a, b] =>
    rw [hins] at hcard
    have haw : a < w := by
      by_contra hna
      have h1 : ([a, b].filter fun i => decide (i < w)).length ≤ 1 := by
        rw [List.filter_cons_of_neg (by simp [hna])]
        exact List.length_filter_le _ [b]
      have := (List.toFinset_card_le ([a, b].filter fun i => decide (i < w))).trans h1; omega
    have hbw : b < w := by
      by_contra hnb
      have h1 : ([a, b].filter fun i => decide (i < w)).length ≤ 1 := by
        by_cases ha : a < w <;> simp [ha, hnb]
      have := (List.toFinset_card_le ([a, b].filter fun i => decide (i < w))).trans h1; omega
    have hne : a ≠ b := by
      intro hab; subst hab
      simp [haw] at hcard
    refine ⟨a, b, rfl, haw, hbw, hne, ?_⟩
    unfold gateIns
    rw [ite_eq_left_of_eq_true _ _ (eq_true h10), List.getElem?_eq_getElem hj]
    dsimp only
    rw [hins]
    ext x; simp [haw, hbw]
  | _ :: _ :: _ :: _ => rw [hins] at hlen; simp at hlen

lemma gateIns_card_one (C : Circuit) (hM : Monotone2 C) (w : ℕ)
    (h10 : 10 ≤ w) (hlt : w < 10 + C.gates.length) (hcard : (gateIns C.gates w).card = 1) :
    ∃ a, a < w ∧ gateIns C.gates w = {a} ∧
      ((∀ (xs : List Bool), xs.length = 10 →
        (C.gates.foldl wstep xs).getD w false = (C.gates.foldl wstep xs).getD a false) ∨
       (∀ (xs : List Bool), xs.length = 10 →
        (C.gates.foldl wstep xs).getD w false = false)) := by
  have hj : w - 10 < C.gates.length := by omega
  obtain ⟨hop, hlen⟩ := hM _ (List.getElem_mem hj)
  obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp hcard
  have ha_mem : a ∈ gateIns C.gates w := by rw [ha_eq]; simp
  have haw : a < w := gateIns_lt C.gates w a ha_mem
  refine ⟨a, haw, ha_eq, ?_⟩
  have hmem_a : ∀ i ∈ (C.gates[w - 10]'hj).inputs, i < w → i = a := by
    intro i hi hiw
    have : i ∈ gateIns C.gates w := by
      unfold gateIns
      rw [ite_eq_left_of_eq_true _ _ (eq_true h10), List.getElem?_eq_getElem hj]
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨hi, hiw⟩
    rw [ha_eq, Finset.mem_singleton] at this; exact this
  have hop2 : (C.gates[w - 10]'hj).op = GateOp.and ∨ (C.gates[w - 10]'hj).op = GateOp.or := by
    simpa using hop
  have hev_step : ∀ (xs : List Bool), xs.length = 10 →
      (C.gates.foldl wstep xs).getD w false =
        (C.gates[w - 10]'hj).op.eval ((C.gates[w - 10]'hj).inputs.map fun i =>
          if i < w then (C.gates.foldl wstep xs).getD i false else false) := by
    intro xs hxl
    have hwx : w = xs.length + (w - 10) := by omega
    have hw1 := wfold_gate C.gates xs (w - 10) hj
    rw [← hwx] at hw1; rw [hw1]; congr 1
    apply List.map_congr_left
    intro i _
    have hlenT : ((C.gates.take (w - 10)).foldl wstep xs).length = w := by
      rw [wfold_len, hxl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
    have hsp : C.gates = C.gates.take (w - 10) ++ C.gates.drop (w - 10) := (List.take_append_drop _ _).symm
    by_cases hiw : i < w
    · simp only [hiw, ite_true]
      conv_rhs => rw [hsp, List.foldl_append]
      exact (wfold_prefix (C.gates.drop (w - 10)) _ i (by omega)).symm
    · simp only [hiw, ite_false]
      exact List.getD_eq_default _ _ (by omega)
  match hins : (C.gates[w - 10]'hj).inputs with
  | [] =>
    unfold gateIns at ha_eq
    rw [ite_eq_left_of_eq_true _ _ (eq_true h10), List.getElem?_eq_getElem hj] at ha_eq
    dsimp only at ha_eq; rw [hins] at ha_eq; simp at ha_eq
  | [x] =>
    have hxw : x < w := by
      by_contra hnx
      unfold gateIns at ha_eq
      rw [ite_eq_left_of_eq_true _ _ (eq_true h10), List.getElem?_eq_getElem hj] at ha_eq
      dsimp only at ha_eq; rw [hins] at ha_eq; simp [hnx] at ha_eq
    have hxa : x = a := hmem_a x (by rw [hins]; simp) hxw
    subst hxa
    left; intro xs hxl; rw [hev_step xs hxl, hins]
    rcases hop2 with h | h <;> simp [h, GateOp.eval, hxw]
  | [x, y] =>
    by_cases hxw : x < w <;> by_cases hyw : y < w
    · have hxa : x = a := hmem_a x (by rw [hins]; simp) hxw
      have hya : y = a := hmem_a y (by rw [hins]; simp) hyw
      subst hxa; subst hya
      left; intro xs hxl; rw [hev_step xs hxl, hins]
      rcases hop2 with h | h <;> simp [h, GateOp.eval, hxw]
    · have hxa : x = a := hmem_a x (by rw [hins]; simp) hxw
      subst hxa
      rcases hop2 with h | h
      · right; intro xs hxl; rw [hev_step xs hxl, hins]; simp [h, GateOp.eval, hxw, hyw]
      · left; intro xs hxl; rw [hev_step xs hxl, hins]; simp [h, GateOp.eval, hxw, hyw]
    · have hya : y = a := hmem_a y (by rw [hins]; simp) hyw
      subst hya
      rcases hop2 with h | h
      · right; intro xs hxl; rw [hev_step xs hxl, hins]; simp [h, GateOp.eval, hxw, hyw]
      · left; intro xs hxl; rw [hev_step xs hxl, hins]; simp [h, GateOp.eval, hxw, hyw]
    · unfold gateIns at ha_eq
      rw [ite_eq_left_of_eq_true _ _ (eq_true h10), List.getElem?_eq_getElem hj] at ha_eq
      dsimp only at ha_eq; rw [hins] at ha_eq; simp [hxw, hyw] at ha_eq
  | _ :: _ :: _ :: _ => rw [hins] at hlen; simp at hlen

def vecOf (S : Finset ℕ) : List Bool :=
  List.ofFn fun j : Fin 10 => decide (j.val ∈ S)

lemma vecOf_len (S : Finset ℕ) : (vecOf S).length = 10 := by simp [vecOf]

lemma vecOf_getD (S : Finset ℕ) (i : ℕ) (hi : i < 10) :
    (vecOf S).getD i false = decide (i ∈ S) := by
  have hlen : i < (vecOf S).length := by simp [vecOf, hi]
  rw [List.getD_eq_getElem (vecOf S) false hlen]
  change (List.ofFn fun j : Fin 10 => decide (j.val ∈ S))[i]'(by simp [hi]) = _
  rw [List.getElem_ofFn]

lemma vecOf_pair_eq_oneEach (u v : Fin 5) : vecOf {u.val, 5 + v.val} = oneEach u v := by
  revert u v; decide

lemma eval_bin_gate (C : Circuit) (w a b : ℕ) (h10 : 10 ≤ w) (hlt : w < 10 + C.gates.length)
    (hins : (C.gates[w - 10]'(by omega)).inputs = [a, b]) (haw : a < w) (hbw : b < w)
    (xs : List Bool) (hxl : xs.length = 10) :
    (C.gates.foldl wstep xs).getD w false =
      (C.gates[w - 10]'(by omega)).op.eval [(C.gates.foldl wstep xs).getD a false,
        (C.gates.foldl wstep xs).getD b false] := by
  have hj : w - 10 < C.gates.length := by omega
  have hwx : w = xs.length + (w - 10) := by omega
  have hw1 := wfold_gate C.gates xs (w - 10) hj
  rw [← hwx] at hw1
  rw [hw1, hins]
  simp only [List.map]
  have hlen : ((C.gates.take (w - 10)).foldl wstep xs).length = w := by
    rw [wfold_len, hxl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
  have hsp : C.gates = C.gates.take (w - 10) ++ C.gates.drop (w - 10) := (List.take_append_drop _ _).symm
  have ha_eq : (C.gates.foldl wstep xs).getD a false = ((C.gates.take (w - 10)).foldl wstep xs).getD a false := by
    conv_lhs => rw [hsp, List.foldl_append]
    exact wfold_prefix (C.gates.drop (w - 10)) _ a (by omega)
  have hb_eq : (C.gates.foldl wstep xs).getD b false = ((C.gates.take (w - 10)).foldl wstep xs).getD b false := by
    conv_lhs => rw [hsp, List.foldl_append]
    exact wfold_prefix (C.gates.drop (w - 10)) _ b (by omega)
  rw [ha_eq, hb_eq]

lemma eval_empty_false (C : Circuit) (hM : Monotone2 C) (root : ℕ)
    (hRsub : reachN C.gates root (C.gates.length + 1) ⊆
      (reachN C.gates root (C.gates.length + 1)).filter (· < 10) ∪
      (reachN C.gates root (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length))
    (hcard12 : ∀ w ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length),
      (gateIns C.gates w).card = 1 ∨ (gateIns C.gates w).card = 2) :
    ∀ w ∈ reachN C.gates root (C.gates.length + 1),
      (C.gates.foldl wstep (vecOf ∅)).getD w false = false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    rcases Finset.mem_union.mp (hRsub hw) with hwU | hwG
    · have hw10 : w < 10 := (Finset.mem_filter.mp hwU).2
      rw [wfold_prefix _ _ _ (by rw [vecOf_len]; exact hw10), vecOf_getD ∅ w hw10]; simp
    · obtain ⟨_, hw10, hwlt⟩ := Finset.mem_filter.mp hwG
      rcases hcard12 w hwG with hc1 | hc2
      · obtain ⟨a, haw, hgi, hev⟩ := gateIns_card_one C hM w hw10 hwlt hc1
        have haR : a ∈ reachN C.gates root (C.gates.length + 1) :=
          reachN_closed C.gates root w a hw (by rw [hgi]; simp)
        rcases hev with h | h
        · rw [h (vecOf ∅) (vecOf_len ∅)]; exact ih a haw haR
        · exact h (vecOf ∅) (vecOf_len ∅)
      · obtain ⟨a, b, hins, haw, hbw, _, hgi⟩ := gateIns_card_two C hM w hw10 hwlt hc2
        have haR : a ∈ reachN C.gates root (C.gates.length + 1) :=
          reachN_closed C.gates root w a hw (by rw [hgi]; simp)
        have hbR : b ∈ reachN C.gates root (C.gates.length + 1) :=
          reachN_closed C.gates root w b hw (by rw [hgi]; simp)
        rw [eval_bin_gate C w a b hw10 hwlt hins haw hbw (vecOf ∅) (vecOf_len ∅),
            ih a haw haR, ih b hbw hbR]
        rcases (by simpa using (hM _ (List.getElem_mem (by omega : w - 10 < C.gates.length))).1 :
            (C.gates[w - 10]'(by omega)).op = GateOp.and ∨ (C.gates[w - 10]'(by omega)).op = GateOp.or) with hop | hop <;>
          simp [hop, GateOp.eval]

lemma reachN_inter_sub_z (C : Circuit) (root z : ℕ)
    (hunique : ∀ w1 ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length),
      ∀ w2 ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length),
      w1 ≠ w2 → ∀ x, x ∈ gateIns C.gates w1 → x ∈ gateIns C.gates w2 → x = z)
    (w a b : ℕ)
    (hw : w ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length))
    (ha : a ∈ gateIns C.gates w) (hb : b ∈ gateIns C.gates w) (hne : a ≠ b) :
    reachN C.gates a (C.gates.length + 1) ∩ reachN C.gates b (C.gates.length + 1) ⊆
      reachN C.gates z (C.gates.length + 1) := by
  let N := C.gates.length + 1
  let R := reachN C.gates root N
  let G := R.filter fun u => 10 ≤ u ∧ u < 10 + C.gates.length
  have haR : a ∈ R := reachN_closed C.gates root w a (Finset.mem_filter.mp hw).1 ha
  have hbR : b ∈ R := reachN_closed C.gates root w b (Finset.mem_filter.mp hw).1 hb
  have hsubA : reachN C.gates a N ⊆ R := reachN_sub_of_mem C.gates root a haR N
  have hsubB : reachN C.gates b N ⊆ R := reachN_sub_of_mem C.gates root b hbR N
  intro x hx
  by_contra hxz
  let S := (reachN C.gates a N ∩ reachN C.gates b N) \ reachN C.gates z N
  have hS : S.Nonempty := ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxz⟩⟩
  let m := S.max' hS
  have hmS : m ∈ S := Finset.max'_mem S hS
  have ⟨hmAB, hmz⟩ := Finset.mem_sdiff.mp hmS
  have ⟨hma, hmb⟩ := Finset.mem_inter.mp hmAB
  have hm_ne_z : m ≠ z := fun h => hmz (h ▸ out_mem_reachN _ _ _)
  have hma_ne : m ≠ a := by
    intro hmeq
    rw [hmeq] at hmb
    have hab_er : a ∈ (reachN C.gates b N).erase b := Finset.mem_erase.mpr ⟨hne, hmb⟩
    have hbi := reachN_erase_sub_biUnion C.gates b N hab_er
    obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp hbi
    obtain ⟨huB, hu10, hult⟩ := Finset.mem_filter.mp hu
    have huG : u ∈ G := Finset.mem_filter.mpr ⟨hsubB huB, hu10, hult⟩
    have hule : u ≤ b := reachN_le_out C.gates b N u huB
    have hblt : b < w := gateIns_lt C.gates w b hb
    have haz : a = z := hunique w hw u huG (by omega) a ha hau
    exact hm_ne_z (hmeq.trans haz)
  have hmb_ne : m ≠ b := by
    intro hmeq
    rw [hmeq] at hma
    have hba_er : b ∈ (reachN C.gates a N).erase a := Finset.mem_erase.mpr ⟨hne.symm, hma⟩
    have hbi := reachN_erase_sub_biUnion C.gates a N hba_er
    obtain ⟨u, hu, hbu⟩ := Finset.mem_biUnion.mp hbi
    obtain ⟨huA, hu10, hult⟩ := Finset.mem_filter.mp hu
    have huG : u ∈ G := Finset.mem_filter.mpr ⟨hsubA huA, hu10, hult⟩
    have hule : u ≤ a := reachN_le_out C.gates a N u huA
    have halt : a < w := gateIns_lt C.gates w a ha
    have hbz : b = z := hunique w hw u huG (by omega) b hb hbu
    exact hm_ne_z (hmeq.trans hbz)
  have h1 := reachN_erase_sub_biUnion C.gates a N (Finset.mem_erase.mpr ⟨hma_ne, hma⟩)
  have h2 := reachN_erase_sub_biUnion C.gates b N (Finset.mem_erase.mpr ⟨hmb_ne, hmb⟩)
  obtain ⟨u1, hu1, hmu1⟩ := Finset.mem_biUnion.mp h1
  obtain ⟨u2, hu2, hmu2⟩ := Finset.mem_biUnion.mp h2
  obtain ⟨hu1A, hu110, hu1lt⟩ := Finset.mem_filter.mp hu1
  obtain ⟨hu2B, hu210, hu2lt⟩ := Finset.mem_filter.mp hu2
  have hu1G : u1 ∈ G := Finset.mem_filter.mpr ⟨hsubA hu1A, hu110, hu1lt⟩
  have hu2G : u2 ∈ G := Finset.mem_filter.mpr ⟨hsubB hu2B, hu210, hu2lt⟩
  have hu_eq : u1 = u2 := by
    by_contra hune
    exact hm_ne_z (hunique u1 hu1G u2 hu2G hune m hmu1 hmu2)
  subst hu_eq
  have hu1_nz : u1 ∉ reachN C.gates z N := fun huz =>
    hmz (reachN_closed C.gates z u1 m huz hmu1)
  have hu1S : u1 ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hu1A, hu2B⟩, hu1_nz⟩
  have hle : u1 ≤ m := Finset.le_max' S u1 hu1S
  have hlt : m < u1 := gateIns_lt C.gates u1 m hmu1
  omega

lemma dominator_z (C : Circuit) (z : ℕ)
    (hzR : z ∈ reachN C.gates C.output (C.gates.length + 1))
    (hunique : ∀ w1 ∈ (reachN C.gates C.output (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length),
      ∀ w2 ∈ (reachN C.gates C.output (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length),
      w1 ≠ w2 → ∀ x, x ∈ gateIns C.gates w1 → x ∈ gateIns C.gates w2 → x = z)
    (xs ys : List Bool) (hxl : xs.length = 10) (hyl : ys.length = 10)
    (hagree : ∀ i < 10, i ∉ reachN C.gates z (C.gates.length + 1) → xs.getD i false = ys.getD i false)
    (hz_eq : (C.gates.foldl wstep xs).getD z false = (C.gates.foldl wstep ys).getD z false) :
    ∀ w ∈ reachN C.gates C.output (C.gates.length + 1),
      w ∉ (reachN C.gates z (C.gates.length + 1)).erase z →
      (C.gates.foldl wstep xs).getD w false = (C.gates.foldl wstep ys).getD w false := by
  let N := C.gates.length + 1
  let R := reachN C.gates C.output N
  let G := R.filter fun u => 10 ≤ u ∧ u < 10 + C.gates.length
  have hsubZ : reachN C.gates z N ⊆ R := reachN_sub_of_mem C.gates C.output z hzR N
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hw_ne_er
    by_cases hwz : w = z
    · subst hwz; exact hz_eq
    · have hw_nz : w ∉ reachN C.gates z N := fun hz =>
        hw_ne_er (Finset.mem_erase.mpr ⟨hwz, hz⟩)
      by_cases h10 : w < 10
      · rw [wfold_prefix _ _ _ (by omega), wfold_prefix _ _ _ (by omega)]
        exact hagree w h10 hw_nz
      · by_cases hlt : w < 10 + C.gates.length
        · have hj : w - 10 < C.gates.length := by omega
          have hwG : w ∈ G := Finset.mem_filter.mpr ⟨hw, by omega, hlt⟩
          have hwx : w = xs.length + (w - 10) := by omega
          have hwy : w = ys.length + (w - 10) := by omega
          have hx1 := wfold_gate C.gates xs (w - 10) hj
          have hy1 := wfold_gate C.gates ys (w - 10) hj
          rw [← hwx] at hx1; rw [← hwy] at hy1
          rw [hx1, hy1]
          congr 1
          apply List.map_congr_left
          intro i hi
          have hlenx : ((C.gates.take (w - 10)).foldl wstep xs).length = w := by
            rw [wfold_len, hxl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
          have hleny : ((C.gates.take (w - 10)).foldl wstep ys).length = w := by
            rw [wfold_len, hyl, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]; omega
          by_cases hiw : i < w
          · have hi_ins : i ∈ gateIns C.gates w := by
              unfold gateIns
              rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega : 10 ≤ w)), List.getElem?_eq_getElem hj]
              simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
              exact ⟨hi, hiw⟩
            have hiR : i ∈ R := reachN_closed C.gates C.output w i hw hi_ins
            have hi_ner : i ∉ (reachN C.gates z N).erase z := by
              intro hier
              have ⟨hiz, _⟩ := Finset.mem_erase.mp hier
              have hbi := reachN_erase_sub_biUnion C.gates z N hier
              obtain ⟨u, hu, hiu⟩ := Finset.mem_biUnion.mp hbi
              obtain ⟨huZ, hu10, hult⟩ := Finset.mem_filter.mp hu
              have huG : u ∈ G := Finset.mem_filter.mpr ⟨hsubZ huZ, hu10, hult⟩
              have hne : w ≠ u := fun e => hw_nz (e ▸ huZ)
              exact hiz (hunique w hwG u huG hne i hi_ins hiu)
            have heq := ih i hiw hiR hi_ner
            have hsp : C.gates = C.gates.take (w - 10) ++ C.gates.drop (w - 10) := (List.take_append_drop _ _).symm
            conv at heq => lhs; rw [hsp, List.foldl_append]
            conv at heq => rhs; rw [hsp, List.foldl_append]
            rw [wfold_prefix (C.gates.drop (w - 10)) _ _ (by omega),
                wfold_prefix (C.gates.drop (w - 10)) _ _ (by omega)] at heq
            exact heq
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by rw [wfold_len, hxl]; omega),
              List.getD_eq_default _ _ (by rw [wfold_len, hyl]; omega)]

lemma no_P4_gen (C : Circuit) (hM : Monotone2 C) (root : ℕ)
    (hRsub : reachN C.gates root (C.gates.length + 1) ⊆
      (reachN C.gates root (C.gates.length + 1)).filter (· < 10) ∪
      (reachN C.gates root (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length))
    (hcard12 : ∀ w ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length),
      (gateIns C.gates w).card = 1 ∨ (gateIns C.gates w).card = 2)
    (p q r t : ℕ)
    (hdisj4 : ∀ w ∈ (reachN C.gates root (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length),
      ∀ a b, a ∈ gateIns C.gates w → b ∈ gateIns C.gates w → a ≠ b →
      ∀ x ∈ ({p, q, r, t} : Finset ℕ),
        ¬ (x ∈ reachN C.gates a (C.gates.length + 1) ∧ x ∈ reachN C.gates b (C.gates.length + 1))) :
    ∀ w ∈ reachN C.gates root (C.gates.length + 1),
      (C.gates.foldl wstep (vecOf {p, r})).getD w false = true →
      (C.gates.foldl wstep (vecOf {p, t})).getD w false = true →
      (C.gates.foldl wstep (vecOf {q, r})).getD w false = true →
      (C.gates.foldl wstep (vecOf {q, t})).getD w false = false →
      (C.gates.foldl wstep (vecOf {p})).getD w false = false →
      (C.gates.foldl wstep (vecOf {r})).getD w false = false →
      False := by
  let N := C.gates.length + 1
  have hmonoS : ∀ (S T : Finset ℕ), S ⊆ T → ∀ u,
      (C.gates.foldl wstep (vecOf S)).getD u false = true →
      (C.gates.foldl wstep (vecOf T)).getD u false = true := by
    intro S T hST u hu
    refine wires_mono C.gates (fun g hg => by simpa using (hM g hg).1) (vecOf S) (vecOf T) (by simp [vecOf_len]) ?_ u hu
    intro i hi
    by_cases hi10 : i < 10
    · rw [vecOf_getD S i hi10] at hi
      rw [vecOf_getD T i hi10]
      simp only [decide_eq_true_eq] at hi ⊢
      exact hST hi
    · rw [List.getD_eq_default _ _ (by rw [vecOf_len]; omega)] at hi; cases hi
  have hagreeW : ∀ u (S T : Finset ℕ),
      (∀ i < 10, i ∈ reachN C.gates u N → (i ∈ S ↔ i ∈ T)) →
      (C.gates.foldl wstep (vecOf S)).getD u false = (C.gates.foldl wstep (vecOf T)).getD u false := by
    intro u S T hST
    refine wires_agree_on_reach C.gates u (vecOf S) (vecOf T) (vecOf_len S) (vecOf_len T) ?_ u (out_mem_reachN _ _ _)
    intro i hi hir
    rw [vecOf_getD S i hi, vecOf_getD T i hi, decide_eq_decide]
    exact hST i hi hir
  have hpair_in : ∀ u x y,
      (C.gates.foldl wstep (vecOf {x, y})).getD u false = true →
      (C.gates.foldl wstep (vecOf {x})).getD u false = false →
      (C.gates.foldl wstep (vecOf {y})).getD u false = false →
      x ∈ reachN C.gates u N ∧ y ∈ reachN C.gates u N := by
    intro u x y hxy hx hy
    constructor
    · by_contra hnx
      have heq := hagreeW u {x, y} {y} fun i _ hir => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl); exact absurd hir hnx; rfl
        · intro h; exact Or.inr h
      rw [heq, hy] at hxy; cases hxy
    · by_contra hny
      have heq := hagreeW u {x, y} {x} fun i _ hir => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl); rfl; exact absurd hir hny
        · intro h; exact Or.inl h
      rw [heq, hx] at hxy; cases hxy
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hpr hpt hqr hqt hp hr
    have hq : (C.gates.foldl wstep (vecOf {q})).getD w false = false := by
      cases hv : (C.gates.foldl wstep (vecOf {q})).getD w false
      · rfl
      · have := hmonoS {q} {q, t} (by simp) w hv; rw [hqt] at this; cases this
    have ht : (C.gates.foldl wstep (vecOf {t})).getD w false = false := by
      cases hv : (C.gates.foldl wstep (vecOf {t})).getD w false
      · rfl
      · have := hmonoS {t} {q, t} (by simp) w hv; rw [hqt] at this; cases this
    rcases Finset.mem_union.mp (hRsub hw) with hwU | hwG
    · have hw10 : w < 10 := (Finset.mem_filter.mp hwU).2
      rw [wfold_prefix _ _ _ (by rw [vecOf_len]; exact hw10), vecOf_getD _ w hw10] at hpr hp hr
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, Finset.mem_insert, Finset.mem_singleton] at hpr hp hr
      rcases hpr with rfl | rfl
      · exact hp rfl
      · exact hr rfl
    · obtain ⟨_, hw10, hwlt⟩ := Finset.mem_filter.mp hwG
      rcases hcard12 w hwG with hc1 | hc2
      · obtain ⟨a, haw, hgi, hev⟩ := gateIns_card_one C hM w hw10 hwlt hc1
        have haR : a ∈ reachN C.gates root N := reachN_closed C.gates root w a hw (by rw [hgi]; simp)
        rcases hev with h | h
        · rw [h (vecOf {p, r}) (vecOf_len _)] at hpr
          rw [h (vecOf {p, t}) (vecOf_len _)] at hpt
          rw [h (vecOf {q, r}) (vecOf_len _)] at hqr
          rw [h (vecOf {q, t}) (vecOf_len _)] at hqt
          rw [h (vecOf {p}) (vecOf_len _)] at hp
          rw [h (vecOf {r}) (vecOf_len _)] at hr
          exact ih a haw haR hpr hpt hqr hqt hp hr
        · rw [h (vecOf {p, r}) (vecOf_len _)] at hpr; cases hpr
      · obtain ⟨a, b, hins, haw, hbw, hab, hgi⟩ := gateIns_card_two C hM w hw10 hwlt hc2
        have ha_ins : a ∈ gateIns C.gates w := by rw [hgi]; simp
        have hb_ins : b ∈ gateIns C.gates w := by rw [hgi]; simp
        have haR : a ∈ reachN C.gates root N := reachN_closed C.gates root w a hw ha_ins
        have hbR : b ∈ reachN C.gates root N := reachN_closed C.gates root w b hw hb_ins
        have hnd : ∀ x ∈ ({p, q, r, t} : Finset ℕ),
            ¬ (x ∈ reachN C.gates a N ∧ x ∈ reachN C.gates b N) :=
          hdisj4 w hwG a b ha_ins hb_ins hab
        have hev := fun S => eval_bin_gate C w a b hw10 hwlt hins haw hbw (vecOf S) (vecOf_len S)
        rcases (by simpa using (hM _ (List.getElem_mem (by omega : w - 10 < C.gates.length))).1 :
            (C.gates[w - 10]'(by omega)).op = GateOp.and ∨ (C.gates[w - 10]'(by omega)).op = GateOp.or) with hop | hop
        · have hand : ∀ S, (C.gates.foldl wstep (vecOf S)).getD w false =
              ((C.gates.foldl wstep (vecOf S)).getD a false && (C.gates.foldl wstep (vecOf S)).getD b false) := by
            intro S; rw [hev S, hop]; simp [GateOp.eval]
          rw [hand] at hpr hpt hqr hqt
          simp only [Bool.and_eq_true] at hpr hpt hqr
          have ha0 := eval_empty_false C hM root hRsub hcard12 a haR
          have hb0 := eval_empty_false C hM root hRsub hcard12 b hbR
          have hit : ∀ u x y, (C.gates.foldl wstep (vecOf ∅)).getD u false = false →
              (C.gates.foldl wstep (vecOf {x, y})).getD u false = true →
              x ∈ reachN C.gates u N ∨ y ∈ reachN C.gates u N := by
            intro u x y hu0 hxy
            by_contra hneither
            have ⟨hnx, hny⟩ := not_or.mp hneither
            have heq := hagreeW u {x, y} ∅ fun i _ hir => by
              simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
              rintro (rfl | rfl)
              · exact hnx hir
              · exact hny hir
            rw [heq, hu0] at hxy; cases hxy
          have h1a := hit a p r ha0 hpr.1
          have h1b := hit b p r hb0 hpr.2
          have h2a := hit a p t ha0 hpt.1
          have h2b := hit b p t hb0 hpt.2
          have h3a := hit a q r ha0 hqr.1
          have h3b := hit b q r hb0 hqr.2
          rcases h1a with hpa | hra
          · have hpb : p ∉ reachN C.gates b N := fun h => hnd p (by simp) ⟨hpa, h⟩
            have hrb : r ∈ reachN C.gates b N := h1b.resolve_left hpb
            have hra' : r ∉ reachN C.gates a N := fun h => hnd r (by simp) ⟨h, hrb⟩
            have htb : t ∈ reachN C.gates b N := h2b.resolve_left hpb
            have hta' : t ∉ reachN C.gates a N := fun h => hnd t (by simp) ⟨h, htb⟩
            have hqa : q ∈ reachN C.gates a N := h3a.resolve_right hra'
            have hqb : q ∉ reachN C.gates b N := fun h => hnd q (by simp) ⟨hqa, h⟩
            have hqta : (C.gates.foldl wstep (vecOf {q, t})).getD a false = true := by
              rw [hagreeW a {q, t} {q, r} fun i _ hir => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (rfl | rfl); exact Or.inl rfl; exact absurd hir hta'
                · rintro (rfl | rfl); exact Or.inl rfl; exact absurd hir hra']
              exact hqr.1
            have hqtb : (C.gates.foldl wstep (vecOf {q, t})).getD b false = true := by
              rw [hagreeW b {q, t} {p, t} fun i _ hir => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (rfl | rfl); exact absurd hir hqb; exact Or.inr rfl
                · rintro (rfl | rfl); exact absurd hir hpb; exact Or.inr rfl]
              exact hpt.2
            rw [hqta, hqtb] at hqt; cases hqt
          · have hrb : r ∉ reachN C.gates b N := fun h => hnd r (by simp) ⟨hra, h⟩
            have hpb : p ∈ reachN C.gates b N := h1b.resolve_right hrb
            have hpa' : p ∉ reachN C.gates a N := fun h => hnd p (by simp) ⟨h, hpb⟩
            have hta : t ∈ reachN C.gates a N := h2a.resolve_left hpa'
            have htb' : t ∉ reachN C.gates b N := fun h => hnd t (by simp) ⟨hta, h⟩
            have hqb : q ∈ reachN C.gates b N := h3b.resolve_right hrb
            have hqa' : q ∉ reachN C.gates a N := fun h => hnd q (by simp) ⟨h, hqb⟩
            have hqta : (C.gates.foldl wstep (vecOf {q, t})).getD a false = true := by
              rw [hagreeW a {q, t} {p, t} fun i _ hir => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (rfl | rfl); exact absurd hir hqa'; exact Or.inr rfl
                · rintro (rfl | rfl); exact absurd hir hpa'; exact Or.inr rfl]
              exact hpt.1
            have hqtb : (C.gates.foldl wstep (vecOf {q, t})).getD b false = true := by
              rw [hagreeW b {q, t} {q, r} fun i _ hir => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro (rfl | rfl); exact Or.inl rfl; exact absurd hir htb'
                · rintro (rfl | rfl); exact Or.inl rfl; exact absurd hir hrb]
              exact hqr.2
            rw [hqta, hqtb] at hqt; cases hqt
        · have hor : ∀ S, (C.gates.foldl wstep (vecOf S)).getD w false =
              ((C.gates.foldl wstep (vecOf S)).getD a false || (C.gates.foldl wstep (vecOf S)).getD b false) := by
            intro S; rw [hev S, hop]; simp [GateOp.eval]
          rw [hor] at hpr hpt hqr hqt hp hq hr ht
          simp only [Bool.or_eq_false_iff] at hqt hp hq hr ht
          simp only [Bool.or_eq_true] at hpr hpt hqr
          rcases hpr with hpra | hprb
          · have ⟨hpa, hra⟩ := hpair_in a p r hpra hp.1 hr.1
            have hpb : p ∉ reachN C.gates b N := fun h => hnd p (by simp) ⟨hpa, h⟩
            have hrb : r ∉ reachN C.gates b N := fun h => hnd r (by simp) ⟨hra, h⟩
            have hpta : (C.gates.foldl wstep (vecOf {p, t})).getD a false = true :=
              hpt.resolve_right fun hptb => hpb (hpair_in b p t hptb hp.2 ht.2).1
            have hqra : (C.gates.foldl wstep (vecOf {q, r})).getD a false = true :=
              hqr.resolve_right fun hqrb => hrb (hpair_in b q r hqrb hq.2 hr.2).2
            exact ih a haw haR hpra hpta hqra hqt.1 hp.1 hr.1
          · have ⟨hpb, hrb⟩ := hpair_in b p r hprb hp.2 hr.2
            have hpa : p ∉ reachN C.gates a N := fun h => hnd p (by simp) ⟨h, hpb⟩
            have hra : r ∉ reachN C.gates a N := fun h => hnd r (by simp) ⟨h, hrb⟩
            have hptb : (C.gates.foldl wstep (vecOf {p, t})).getD b false = true :=
              hpt.resolve_left fun hpta => hpa (hpair_in a p t hpta hp.1 ht.1).1
            have hqrb : (C.gates.foldl wstep (vecOf {q, r})).getD b false = true :=
              hqr.resolve_left fun hqra => hra (hpair_in a q r hqra hq.1 hr.1).2
            exact ih b hbw hbR hprb hptb hqrb hqt.2 hp.2 hr.2

/-- If `x` and `y` are read-once (never shared across two branches of any gate),
    no wire can compute MAJ(x, y, Z) (true on {x,y}, {x}∪Z, {y}∪Z and false on Z, {x}, {y}). -/
lemma no_MAJ3_with_Z (C : Circuit) (hM : Monotone2 C) (x y : ℕ) (Z : Finset ℕ)
    (hRsub : reachN C.gates C.output (C.gates.length + 1) ⊆
      (reachN C.gates C.output (C.gates.length + 1)).filter (· < 10) ∪
      (reachN C.gates C.output (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length))
    (hcard2 : ∀ w ∈ (reachN C.gates C.output (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length),
      (gateIns C.gates w).card = 2)
    (hdisj2 : ∀ w ∈ (reachN C.gates C.output (C.gates.length + 1)).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length),
      ∀ a b, a ∈ gateIns C.gates w → b ∈ gateIns C.gates w → a ≠ b →
      ∀ u ∈ ({x, y} : Finset ℕ),
        ¬ (u ∈ reachN C.gates a (C.gates.length + 1) ∧ u ∈ reachN C.gates b (C.gates.length + 1))) :
    ∀ w ∈ reachN C.gates C.output (C.gates.length + 1),
      (C.gates.foldl wstep (vecOf {x, y})).getD w false = true →
      (C.gates.foldl wstep (vecOf (insert x Z))).getD w false = true →
      (C.gates.foldl wstep (vecOf (insert y Z))).getD w false = true →
      (C.gates.foldl wstep (vecOf Z)).getD w false = false →
      (C.gates.foldl wstep (vecOf {x})).getD w false = false →
      (C.gates.foldl wstep (vecOf {y})).getD w false = false →
      False := by
  let N := C.gates.length + 1
  have hcard12 : ∀ w ∈ (reachN C.gates C.output N).filter (fun w => 10 ≤ w ∧ w < 10 + C.gates.length),
      (gateIns C.gates w).card = 1 ∨ (gateIns C.gates w).card = 2 :=
    fun w hw => Or.inr (hcard2 w hw)
  have hagreeW : ∀ u (S T : Finset ℕ),
      (∀ i < 10, i ∈ reachN C.gates u N → (i ∈ S ↔ i ∈ T)) →
      (C.gates.foldl wstep (vecOf S)).getD u false = (C.gates.foldl wstep (vecOf T)).getD u false := by
    intro u S T hST
    refine wires_agree_on_reach C.gates u (vecOf S) (vecOf T) (vecOf_len S) (vecOf_len T) ?_ u (out_mem_reachN _ _ _)
    intro i hi hir
    rw [vecOf_getD S i hi, vecOf_getD T i hi, decide_eq_decide]
    exact hST i hi hir
  have hpair_in : ∀ u p q,
      (C.gates.foldl wstep (vecOf {p, q})).getD u false = true →
      (C.gates.foldl wstep (vecOf {p})).getD u false = false →
      (C.gates.foldl wstep (vecOf {q})).getD u false = false →
      p ∈ reachN C.gates u N ∧ q ∈ reachN C.gates u N := by
    intro u p q hpq hp hq
    constructor
    · by_contra hnp
      have heq := hagreeW u {p, q} {q} fun i _ hir => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun h => h.elim (fun e => absurd (e ▸ hir) hnp) id, Or.inr⟩
      rw [heq, hq] at hpq; cases hpq
    · by_contra hnq
      have heq := hagreeW u {p, q} {p} fun i _ hir => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact ⟨fun h => h.elim id (fun e => absurd (e ▸ hir) hnq), Or.inl⟩
      rw [heq, hp] at hpq; cases hpq
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hxy hxZ hyZ hZ hx hy
    rcases Finset.mem_union.mp (hRsub hw) with hwU | hwG
    · have hw10 : w < 10 := (Finset.mem_filter.mp hwU).2
      rw [wfold_prefix _ _ _ (by rw [vecOf_len]; exact hw10), vecOf_getD _ w hw10] at hxy hx hy
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, Finset.mem_insert, Finset.mem_singleton] at hxy hx hy
      rcases hxy with rfl | rfl
      · exact hx rfl
      · exact hy rfl
    · obtain ⟨_, hw10, hwlt⟩ := Finset.mem_filter.mp hwG
      obtain ⟨a, b, hins, haw, hbw, hab, hgi⟩ := gateIns_card_two C hM w hw10 hwlt (hcard2 w hwG)
      have ha_ins : a ∈ gateIns C.gates w := by rw [hgi]; simp
      have hb_ins : b ∈ gateIns C.gates w := by rw [hgi]; simp
      have haR : a ∈ reachN C.gates C.output N := reachN_closed C.gates C.output w a hw ha_ins
      have hbR : b ∈ reachN C.gates C.output N := reachN_closed C.gates C.output w b hw hb_ins
      have hnd := hdisj2 w hwG a b ha_ins hb_ins hab
      have hev := fun S => eval_bin_gate C w a b hw10 hwlt hins haw hbw (vecOf S) (vecOf_len S)
      rcases (by simpa using (hM _ (List.getElem_mem (by omega : w - 10 < C.gates.length))).1 :
          (C.gates[w - 10]'(by omega)).op = GateOp.and ∨ (C.gates[w - 10]'(by omega)).op = GateOp.or) with hop | hop
      · have hand : ∀ S, (C.gates.foldl wstep (vecOf S)).getD w false =
            ((C.gates.foldl wstep (vecOf S)).getD a false && (C.gates.foldl wstep (vecOf S)).getD b false) := by
          intro S; rw [hev S, hop]; simp [GateOp.eval]
        rw [hand] at hxy hxZ hyZ hZ
        simp only [Bool.and_eq_true] at hxy hxZ hyZ
        have ha0 := eval_empty_false C hM C.output hRsub hcard12 a haR
        have hb0 := eval_empty_false C hM C.output hRsub hcard12 b hbR
        have hit : ∀ u, (C.gates.foldl wstep (vecOf ∅)).getD u false = false →
            (C.gates.foldl wstep (vecOf {x, y})).getD u false = true →
            x ∈ reachN C.gates u N ∨ y ∈ reachN C.gates u N := by
          intro u hu0 h1
          by_contra hneither
          have ⟨hnx, hny⟩ := not_or.mp hneither
          have heq := hagreeW u {x, y} ∅ fun i _ hir => by
            simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
            rintro (rfl | rfl)
            · exact hnx hir
            · exact hny hir
          rw [heq, hu0] at h1; cases h1
        have hxa_or := hit a ha0 hxy.1
        have hxb_or := hit b hb0 hxy.2
        rcases hxa_or with hxa | hya
        · have hxb : x ∉ reachN C.gates b N := fun h => hnd x (by simp) ⟨hxa, h⟩
          have hyb : y ∈ reachN C.gates b N := hxb_or.resolve_left hxb
          have hya' : y ∉ reachN C.gates a N := fun h => hnd y (by simp) ⟨h, hyb⟩
          have hZa : (C.gates.foldl wstep (vecOf Z)).getD a false = true := by
            rw [hagreeW a Z (insert y Z) fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨Or.inr, fun h => h.elim (fun e => absurd (e ▸ hir) hya') id⟩]
            exact hyZ.1
          have hZb : (C.gates.foldl wstep (vecOf Z)).getD b false = true := by
            rw [hagreeW b Z (insert x Z) fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨Or.inr, fun h => h.elim (fun e => absurd (e ▸ hir) hxb) id⟩]
            exact hxZ.2
          rw [hZa, hZb] at hZ; cases hZ
        · have hyb : y ∉ reachN C.gates b N := fun h => hnd y (by simp) ⟨hya, h⟩
          have hxb : x ∈ reachN C.gates b N := hxb_or.resolve_right hyb
          have hxa' : x ∉ reachN C.gates a N := fun h => hnd x (by simp) ⟨h, hxb⟩
          have hZa : (C.gates.foldl wstep (vecOf Z)).getD a false = true := by
            rw [hagreeW a Z (insert x Z) fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨Or.inr, fun h => h.elim (fun e => absurd (e ▸ hir) hxa') id⟩]
            exact hxZ.1
          have hZb : (C.gates.foldl wstep (vecOf Z)).getD b false = true := by
            rw [hagreeW b Z (insert y Z) fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨Or.inr, fun h => h.elim (fun e => absurd (e ▸ hir) hyb) id⟩]
            exact hyZ.2
          rw [hZa, hZb] at hZ; cases hZ
      · have hor : ∀ S, (C.gates.foldl wstep (vecOf S)).getD w false =
            ((C.gates.foldl wstep (vecOf S)).getD a false || (C.gates.foldl wstep (vecOf S)).getD b false) := by
          intro S; rw [hev S, hop]; simp [GateOp.eval]
        rw [hor] at hxy hxZ hyZ hZ hx hy
        simp only [Bool.or_eq_false_iff] at hZ hx hy
        simp only [Bool.or_eq_true] at hxy hxZ hyZ
        rcases hxy with hxya | hxyb
        · have ⟨hxa, hya⟩ := hpair_in a x y hxya hx.1 hy.1
          have hxb : x ∉ reachN C.gates b N := fun h => hnd x (by simp) ⟨hxa, h⟩
          have hyb : y ∉ reachN C.gates b N := fun h => hnd y (by simp) ⟨hya, h⟩
          have hxZb : (C.gates.foldl wstep (vecOf (insert x Z))).getD b false = false := by
            rw [hagreeW b (insert x Z) Z fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ hir) hxb) id, Or.inr⟩]
            exact hZ.2
          have hyZb : (C.gates.foldl wstep (vecOf (insert y Z))).getD b false = false := by
            rw [hagreeW b (insert y Z) Z fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ hir) hyb) id, Or.inr⟩]
            exact hZ.2
          have hxZa := hxZ.resolve_right (by rw [hxZb]; decide)
          have hyZa := hyZ.resolve_right (by rw [hyZb]; decide)
          exact ih a haw haR hxya hxZa hyZa hZ.1 hx.1 hy.1
        · have ⟨hxb, hyb⟩ := hpair_in b x y hxyb hx.2 hy.2
          have hxa : x ∉ reachN C.gates a N := fun h => hnd x (by simp) ⟨h, hxb⟩
          have hya : y ∉ reachN C.gates a N := fun h => hnd y (by simp) ⟨h, hyb⟩
          have hxZa : (C.gates.foldl wstep (vecOf (insert x Z))).getD a false = false := by
            rw [hagreeW a (insert x Z) Z fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ hir) hxa) id, Or.inr⟩]
            exact hZ.1
          have hyZa : (C.gates.foldl wstep (vecOf (insert y Z))).getD a false = false := by
            rw [hagreeW a (insert y Z) Z fun i _ hir => by
              simp only [Finset.mem_insert]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ hir) hya) id, Or.inr⟩]
            exact hZ.1
          have hxZb := hxZ.resolve_left (by rw [hxZa]; decide)
          have hyZb := hyZ.resolve_left (by rw [hyZa]; decide)
          exact ih b hbw hbR hxyb hxZb hyZb hZ.2 hx.2 hy.2

-- ============================================================
-- Part 3: Core impossibility on the 3x3 induced P_6 ({0,1,3} x {5,7,9}) at size <= 6
-- ============================================================

lemma no_P6_size_6 (C : Circuit) (hM : Monotone2 C) (hsz : C.size ≤ 6)
    (hrep : ∀ (u v : Fin 5), u.val ∈ ({0, 1, 3} : Finset ℕ) → v.val ∈ ({0, 2, 4} : Finset ℕ) →
      C.eval (oneEach u v) = targetA u v) : False := by
  have hclen : C.gates.length ≤ 6 := hsz
  let N := C.gates.length + 1
  let R := reachN C.gates C.output N
  let U := R.filter (· < 10)
  let G := R.filter fun w => 10 ≤ w ∧ w < 10 + C.gates.length
  have hout : C.output ∈ R := out_mem_reachN _ _ _
  have hev_pair : ∀ (u v : Fin 5), u.val ∈ ({0, 1, 3} : Finset ℕ) → v.val ∈ ({0, 2, 4} : Finset ℕ) →
      (C.gates.foldl wstep (vecOf {u.val, 5 + v.val})).getD C.output false = targetA u v := by
    intro u v hu hv
    rw [vecOf_pair_eq_oneEach u v]
    exact hrep u v hu hv
  have hmono_out : ∀ (S T : Finset ℕ), S ⊆ T →
      (C.gates.foldl wstep (vecOf S)).getD C.output false = true →
      (C.gates.foldl wstep (vecOf T)).getD C.output false = true := by
    intro S T hST hS
    refine wires_mono C.gates (fun g hg => by simpa using (hM g hg).1) (vecOf S) (vecOf T) (by simp [vecOf_len]) ?_ C.output hS
    intro i hi
    by_cases hi10 : i < 10
    · rw [vecOf_getD S i hi10] at hi
      rw [vecOf_getD T i hi10]
      simp only [decide_eq_true_eq] at hi ⊢
      exact hST hi
    · rw [List.getD_eq_default _ _ (by rw [vecOf_len]; omega)] at hi; cases hi
  have hsing_false : ∀ i ∈ ({0, 1, 3, 5, 7, 9} : Finset ℕ),
      (C.gates.foldl wstep (vecOf {i})).getD C.output false = false := by
    intro i hi
    cases hv : (C.gates.foldl wstep (vecOf {i})).getD C.output false
    · rfl
    · exfalso
      have hkill : ∀ (u v : Fin 5), u.val ∈ ({0, 1, 3} : Finset ℕ) → v.val ∈ ({0, 2, 4} : Finset ℕ) →
          i ∈ ({u.val, 5 + v.val} : Finset ℕ) → targetA u v = false → False := by
        intro u v hu hv' him h0
        have h1 := hmono_out {i} {u.val, 5 + v.val} (by simp [him]) hv
        rw [hev_pair u v hu hv', h0] at h1; cases h1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hkill 0 2 (by decide) (by decide) (by decide) (by decide)
      · exact hkill 1 0 (by decide) (by decide) (by decide) (by decide)
      · exact hkill 3 4 (by decide) (by decide) (by decide) (by decide)
      · exact hkill 1 0 (by decide) (by decide) (by decide) (by decide)
      · exact hkill 0 2 (by decide) (by decide) (by decide) (by decide)
      · exact hkill 3 4 (by decide) (by decide) (by decide) (by decide)
  have hess : ∀ (i : ℕ) (u v u' v' : Fin 5),
      u.val ∈ ({0, 1, 3} : Finset ℕ) → v.val ∈ ({0, 2, 4} : Finset ℕ) →
      u'.val ∈ ({0, 1, 3} : Finset ℕ) → v'.val ∈ ({0, 2, 4} : Finset ℕ) →
      targetA u v = true → targetA u' v' = false →
      (∀ j < 10, j ≠ i → (oneEach u v).getD j false = true → (oneEach u' v').getD j false = true) →
      i ∈ R := by
    intro i u v u' v' hu hv hu' hv' h1 h0 hdom
    by_contra hni
    let xs := List.ofFn fun j : Fin 10 => if j.val = i then false else (oneEach u v).getD j.val false
    have hagree : ∀ j < 10, j ∈ R → (oneEach u v).getD j false = xs.getD j false := by
      intro j hj hjr
      have hne : j ≠ i := fun e => hni (e ▸ hjr)
      rw [List.getD_eq_getElem xs false (by simp [xs, hj])]
      change (oneEach u v).getD j false =
        (List.ofFn fun k : Fin 10 => if k.val = i then false else (oneEach u v).getD k.val false)[j]'(by simp [hj])
      rw [List.getElem_ofFn]; simp [hne]
    have heq : C.eval (oneEach u v) = C.eval xs :=
      wires_agree_on_reach C.gates C.output (oneEach u v) xs (by simp [oneEach]) (by simp [xs]) hagree C.output hout
    have hxt : C.eval xs = true := by rw [← heq, hrep u v hu hv, h1]
    have hle : ∀ j, xs.getD j false = true → (oneEach u' v').getD j false = true := by
      intro j hj
      by_cases hj10 : j < 10
      · rw [List.getD_eq_getElem xs false (by simp [xs, hj10])] at hj
        change (List.ofFn fun k : Fin 10 => if k.val = i then false else (oneEach u v).getD k.val false)[j]'(by simp [hj10]) = true at hj
        rw [List.getElem_ofFn] at hj
        by_cases hji : j = i
        · simp [hji] at hj
        · simp only [hji, ite_false] at hj
          exact hdom j hj10 hji hj
      · rw [List.getD_eq_default _ _ (by simp [xs]; omega)] at hj; cases hj
    have hyt : C.eval (oneEach u' v') = true :=
      wires_mono C.gates (fun g hg => by simpa using (hM g hg).1) xs (oneEach u' v') (by simp [xs, oneEach]) hle C.output hxt
    rw [hrep u' v' hu' hv', h0] at hyt; cases hyt
  have hP_sub : ({0, 1, 3, 5, 7, 9} : Finset ℕ) ⊆ U := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hess 0 0 0 1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by decide⟩
    · exact Finset.mem_filter.mpr ⟨hess 1 1 2 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by decide⟩
    · exact Finset.mem_filter.mpr ⟨hess 3 3 0 1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by decide⟩
    · exact Finset.mem_filter.mpr ⟨hess 5 0 0 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by decide⟩
    · exact Finset.mem_filter.mpr ⟨hess 7 3 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by decide⟩
    · exact Finset.mem_filter.mpr ⟨hess 9 0 4 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by decide⟩
  have hU_card : 6 ≤ U.card := by
    have := Finset.card_le_card hP_sub
    simpa using this
  have hdisj : Disjoint U G := by
    rw [Finset.disjoint_left]; intro w hwU hwG
    have a := (Finset.mem_filter.mp hwU).2; have b := (Finset.mem_filter.mp hwG).2.1; omega
  have hsubR : U ∪ G ⊆ R := fun w hw =>
    (Finset.mem_union.mp hw).elim (fun h => (Finset.mem_filter.mp h).1) (fun h => (Finset.mem_filter.mp h).1)
  have hR_card : U.card + G.card ≤ R.card := by
    rw [← Finset.card_union_of_disjoint hdisj]; exact Finset.card_le_card hsubR
  have hG_le6 : G.card ≤ 6 := by
    have hsub : G ⊆ Finset.Ico 10 (10 + C.gates.length) := by
      intro w hw; have h := (Finset.mem_filter.mp hw).2; exact Finset.mem_Ico.mpr h
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hc
    have : C.gates.length ≤ 6 := hsz
    omega
  have hgate_le2 : ∀ w ∈ G, (gateIns C.gates w).card ≤ 2 := by
    intro w hw
    obtain ⟨_, hw10, hwlt⟩ := Finset.mem_filter.mp hw
    have hj : w - 10 < C.gates.length := by omega
    have hlen := (hM _ (List.getElem_mem hj)).2
    unfold gateIns
    rw [ite_eq_left_of_eq_true _ _ (eq_true hw10), List.getElem?_eq_getElem hj]
    dsimp only
    exact ((List.toFinset_card_le _).trans (List.length_filter_le _ _)).trans hlen
  have herase_le : (R.erase C.output).card ≤ (G.biUnion (gateIns C.gates)).card :=
    Finset.card_le_card (reachN_erase_sub_biUnion C.gates C.output N)
  have hbi_le_sum : (G.biUnion (gateIns C.gates)).card ≤ ∑ w ∈ G, (gateIns C.gates w).card :=
    Finset.card_biUnion_le
  have hsum_le : ∑ w ∈ G, (gateIns C.gates w).card ≤ 2 * G.card := by
    have h := Finset.sum_le_sum hgate_le2
    simp only [Finset.sum_const, smul_eq_mul] at h; omega
  have hcard_erase : (R.erase C.output).card + 1 = R.card := Finset.card_erase_add_one hout
  have hRsub : R ⊆ U ∪ G := by
    intro w hw
    by_cases hwout : w = C.output
    · subst hwout
      have h0R : 0 ∈ R := (Finset.mem_filter.mp (hP_sub (by decide))).1
      by_cases hlt : C.output < 10 + C.gates.length
      · by_cases h10 : C.output < 10
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h10⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, by omega, hlt⟩)
      · exfalso
        have hstep : ∀ m, reachN C.gates C.output m = {C.output} := by
          intro m; induction m with
          | zero => rfl
          | succ m ih =>
            simp only [reachN, stepReach, ih]
            have hem : gateIns C.gates C.output = ∅ := by
              unfold gateIns
              by_cases h10 : 10 ≤ C.output
              · rw [ite_eq_left_of_eq_true _ _ (eq_true h10), List.getElem?_eq_none (by omega)]
              · rw [ite_eq_right_of_eq_false _ _ (eq_false h10)]
            simp [hem]
        rw [show R = {C.output} from hstep N, Finset.mem_singleton] at h0R
        omega
    · have hbi := reachN_erase_sub_biUnion C.gates C.output N (Finset.mem_erase.mpr ⟨hwout, hw⟩)
      obtain ⟨u, _, hwu⟩ := Finset.mem_biUnion.mp hbi
      have ⟨_, hult⟩ := gateIns_sub_gt C.gates u w hwu
      have hwlt : w < u := gateIns_lt C.gates u w hwu
      by_cases h10 : w < 10
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h10⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, by omega, by omega⟩)
  -- Kill read-once (pairwise disjoint gateIns) via P_4 on {0, 3, 5, 7} (u0, u3, v0, v2):
  -- (0,5)=1, (0,9)=1, (3,5)=1, (3,9)=0? Wait: check P4 {0, 3, 5, 7}:
  -- (3,5)=1, (3,7)=1, (0,5)=1, (0,7)=0! So p=3, q=0, r=5, t=7!
  have hkill_disj :
      (∀ w ∈ G, (gateIns C.gates w).card = 1 ∨ (gateIns C.gates w).card = 2) →
      (∀ w1 ∈ G, ∀ w2 ∈ G, w1 ≠ w2 → Disjoint (gateIns C.gates w1) (gateIns C.gates w2)) → False := by
    intro hcard12 hdisj_ins
    have hdisj4 : ∀ w ∈ G, ∀ a b, a ∈ gateIns C.gates w → b ∈ gateIns C.gates w → a ≠ b →
        ∀ x ∈ ({3, 0, 5, 7} : Finset ℕ), ¬ (x ∈ reachN C.gates a N ∧ x ∈ reachN C.gates b N) := by
      intro w hw a b ha hb hab x _ ⟨hxa, hxb⟩
      have hunique : ∀ u1 ∈ G, ∀ u2 ∈ G, u1 ≠ u2 → ∀ y, y ∈ gateIns C.gates u1 → y ∈ gateIns C.gates u2 → y = 99 := by
        intro u1 hu1 u2 hu2 hune y hy1 hy2
        exact absurd hy2 (Finset.disjoint_left.mp (hdisj_ins u1 hu1 u2 hu2 hune) hy1)
      have hsub := reachN_inter_sub_z C C.output 99 hunique w a b hw ha hb hab
      have hx99 := hsub (Finset.mem_inter.mpr ⟨hxa, hxb⟩)
      have h99 : reachN C.gates 99 N = {99} := by
        have hstep : ∀ m, reachN C.gates 99 m = {99} := by
          intro m; induction m with
          | zero => rfl
          | succ m ih =>
            simp only [reachN, stepReach, ih]
            have hem : gateIns C.gates 99 = ∅ := by
              unfold gateIns; simp [List.getElem?_eq_none (by omega : C.gates.length ≤ 99 - 10)]
            simp [hem]
        exact hstep N
      rw [h99, Finset.mem_singleton] at hx99
      have hle := reachN_le_out C.gates a N x hxa
      have halt := gateIns_lt C.gates w a ha
      have hwlt := (Finset.mem_filter.mp hw).2.2
      omega
    exact no_P4_gen C hM C.output hRsub hcard12 3 0 5 7 hdisj4 C.output hout
      ((hev_pair 3 0 (by decide) (by decide)).trans (by decide))
      ((hev_pair 3 2 (by decide) (by decide)).trans (by decide))
      ((hev_pair 0 0 (by decide) (by decide)).trans (by decide))
      ((hev_pair 0 2 (by decide) (by decide)).trans (by decide))
      (hsing_false 3 (by decide)) (hsing_false 5 (by decide))
  -- Now split on excess overlap (at most 1!)
  by_cases hsum_eq : ∑ w ∈ G, (gateIns C.gates w).card = (G.biUnion (gateIns C.gates)).card
  · have hdisj_ins := biUnion_disjoint_of_card_eq hsum_eq.symm
    have hcard12 : ∀ w ∈ G, (gateIns C.gates w).card = 1 ∨ (gateIns C.gates w).card = 2 := by
      by_cases hfull : ∑ w ∈ G, (gateIns C.gates w).card = 2 * G.card
      · exact fun w hw => Or.inr (sum_eq_two_mul_imp hgate_le2 hfull w hw)
      · exact sum_eq_two_mul_sub_one_imp hgate_le2 (by omega)
    exact hkill_disj hcard12 hdisj_ins
  · -- Exactly 1 excess overlap: sum = 12, G.card = 6, U.card = 6, biUnion.card = 11!
    have hcard2 : ∀ w ∈ G, (gateIns C.gates w).card = 2 :=
      sum_eq_two_mul_imp hgate_le2 (by omega)
    rcases biUnion_at_most_one_overlap (by omega : ∑ w ∈ G, (gateIns C.gates w).card ≤ (G.biUnion (gateIns C.gates)).card + 1) with
        hdisj_ins | ⟨z, _, ⟨w1, hw1, w2, hw2, hw12, hzw1, hzw2⟩, hunique⟩
    · exact hkill_disj (fun w hw => Or.inr (hcard2 w hw)) hdisj_ins
    · have hzR : z ∈ R := reachN_closed C.gates C.output w1 z (Finset.mem_filter.mp hw1).1 hzw1
      have hout_ner : C.output ∉ (reachN C.gates z N).erase z := by
        intro hmem
        have ⟨_, hin⟩ := Finset.mem_erase.mp hmem
        have hle1 : C.output ≤ z := reachN_le_out C.gates z N C.output hin
        have hlt1 : z < w1 := gateIns_lt C.gates w1 z hzw1
        have hle2 : w1 ≤ C.output := reachN_le_out C.gates C.output N w1 (Finset.mem_filter.mp hw1).1
        omega
      let L := (reachN C.gates z N).filter (· < 10)
      have hdom : ∀ (S T : Finset ℕ),
          (∀ i < 10, i ∉ L → (i ∈ S ↔ i ∈ T)) →
          (C.gates.foldl wstep (vecOf S)).getD z false = (C.gates.foldl wstep (vecOf T)).getD z false →
          (C.gates.foldl wstep (vecOf S)).getD C.output false = (C.gates.foldl wstep (vecOf T)).getD C.output false := by
        intro S T hST hz_eq
        refine dominator_z C z hzR hunique (vecOf S) (vecOf T) (vecOf_len S) (vecOf_len T) ?_ hz_eq C.output hout hout_ner
        intro i hi hiz
        rw [vecOf_getD S i hi, vecOf_getD T i hi, decide_eq_decide]
        exact hST i hi (fun h => hiz (Finset.mem_filter.mp h).1)
      have hagreeZ : ∀ (S T : Finset ℕ),
          (∀ i < 10, i ∈ L → (i ∈ S ↔ i ∈ T)) →
          (C.gates.foldl wstep (vecOf S)).getD z false = (C.gates.foldl wstep (vecOf T)).getD z false := by
        intro S T hST
        refine wires_agree_on_reach C.gates z (vecOf S) (vecOf T) (vecOf_len S) (vecOf_len T) ?_ z (out_mem_reachN _ _ _)
        intro i hi hiz
        rw [vecOf_getD S i hi, vecOf_getD T i hi, decide_eq_decide]
        exact hST i hi (Finset.mem_filter.mpr ⟨hiz, hi⟩)
      have hz_empty : (C.gates.foldl wstep (vecOf ∅)).getD z false = false :=
        eval_empty_false C hM C.output hRsub (fun w hw => Or.inr (hcard2 w hw)) z hzR
      have hout_empty : (C.gates.foldl wstep (vecOf ∅)).getD C.output false = false :=
        eval_empty_false C hM C.output hRsub (fun w hw => Or.inr (hcard2 w hw)) C.output hout
      have hU_eq : U = {0, 1, 3, 5, 7, 9} := by
        have hU6 : U.card = 6 := by omega
        exact (Finset.eq_of_subset_of_card_le hP_sub (by simpa using hU6.le)).symm
      have hL_sub_P : L ⊆ {0, 1, 3, 5, 7, 9} := by
        rw [← hU_eq]
        intro i hi
        have ⟨hiz, hi10⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨reachN_sub_of_mem C.gates C.output z hzR N hiz, hi10⟩
      by_cases hT : ∃ i0 ∈ L, (C.gates.foldl wstep (vecOf {i0})).getD z false = true
      · -- Case T ≠ ∅: killed cleanly by no_MAJ3_with_Z on 3 cases!
        obtain ⟨i0, hi0L, hi0t⟩ := hT
        have hi0P : i0 ∈ ({0, 1, 3, 5, 7, 9} : Finset ℕ) := hL_sub_P hi0L
        have hsubL_false : ∀ (S : Finset ℕ), S ⊆ L → (C.gates.foldl wstep (vecOf S)).getD C.output false = false := by
          intro S hSL
          cases hv : (C.gates.foldl wstep (vecOf S)).getD z false
          · rw [hdom S ∅ (fun i _ hiL => by simp; intro h; exact absurd (hSL h) hiL) (hv.trans hz_empty.symm)]
            exact hout_empty
          · rw [hdom S {i0} (fun i _ hiL => by
              simp only [Finset.mem_singleton]
              exact ⟨fun h => absurd (hSL h) hiL, fun e => absurd (e ▸ hi0L) hiL⟩) (hv.trans hi0t.symm)]
            exact hsing_false i0 hi0P
        have hno_edge_L : ∀ (u v : Fin 5), u.val ∈ ({0, 1, 3} : Finset ℕ) → v.val ∈ ({0, 2, 4} : Finset ℕ) →
            targetA u v = true → ¬ (u.val ∈ L ∧ 5 + v.val ∈ L) := by
          rintro u v hu hv h1 ⟨huL, hvL⟩
          have h0 := hsubL_false {u.val, 5 + v.val} (by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> assumption)
          rw [hev_pair u v hu hv, h1] at h0; cases h0
        have hall_T : ∀ i ∈ L, (C.gates.foldl wstep (vecOf {i})).getD z false = true := by
          intro i hiL
          cases hv : (C.gates.foldl wstep (vecOf {i})).getD z false
          · exfalso
            have hiP := hL_sub_P hiL
            have hzero : ∀ (u v : Fin 5), u.val ∈ ({0, 1, 3} : Finset ℕ) → v.val ∈ ({0, 2, 4} : Finset ℕ) →
                i ∈ ({u.val, 5 + v.val} : Finset ℕ) → targetA u v = true → False := by
              intro u v hu hv' him h1
              have hother : ∃ k, {u.val, 5 + v.val} = ({i, k} : Finset ℕ) ∧ k ∈ ({0, 1, 3, 5, 7, 9} : Finset ℕ) := by
                simp only [Finset.mem_insert, Finset.mem_singleton] at him
                rcases him with rfl | rfl
                · refine ⟨5 + v.val, rfl, ?_⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hv' ⊢
                  rcases hv' with h | h | h <;> omega
                · refine ⟨u.val, Finset.pair_comm _ _, ?_⟩
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
                  rcases hu with h | h | h <;> omega
              obtain ⟨k, heq, hkP⟩ := hother
              by_cases hkL : k ∈ L
              · have h0 := hsubL_false {u.val, 5 + v.val} (by
                  rw [heq]; intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl <;> assumption)
                rw [hev_pair u v hu hv', h1] at h0; cases h0
              · have hzk : (C.gates.foldl wstep (vecOf {i, k})).getD z false =
                    (C.gates.foldl wstep (vecOf {k})).getD z false := by
                  have h1' : (C.gates.foldl wstep (vecOf {i, k})).getD z false =
                      (C.gates.foldl wstep (vecOf {i})).getD z false :=
                    hagreeZ {i, k} {i} fun x _ hxL => by
                      simp only [Finset.mem_insert, Finset.mem_singleton]
                      exact ⟨fun h => h.elim id (fun e => absurd (e ▸ hxL) hkL), Or.inl⟩
                  have h2' : (C.gates.foldl wstep (vecOf {k})).getD z false =
                      (C.gates.foldl wstep (vecOf ∅)).getD z false :=
                    hagreeZ {k} ∅ fun x _ hxL => by
                      simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
                      intro e; exact hkL (e ▸ hxL)
                  rw [h1', hv, h2', hz_empty]
                have h0 := hdom {i, k} {k} (fun x _ hxL => by
                  simp only [Finset.mem_insert, Finset.mem_singleton]
                  exact ⟨fun h => h.elim (fun e => absurd (e ▸ hiL) hxL) id, Or.inr⟩) hzk
                rw [← heq, hev_pair u v hu hv', h1, hsing_false k hkP] at h0; cases h0
            simp only [Finset.mem_insert, Finset.mem_singleton] at hiP
            rcases hiP with rfl | rfl | rfl | rfl | rfl | rfl
            · exact hzero 0 0 (by decide) (by decide) (by decide) (by decide)
            · exact hzero 1 2 (by decide) (by decide) (by decide) (by decide)
            · exact hzero 3 0 (by decide) (by decide) (by decide) (by decide)
            · exact hzero 0 0 (by decide) (by decide) (by decide) (by decide)
            · exact hzero 3 2 (by decide) (by decide) (by decide) (by decide)
            · exact hzero 0 4 (by decide) (by decide) (by decide) (by decide)
          · rfl
        have hno_pair_L : ∀ (u1 u2 v : Fin 5),
            u1.val ∈ ({0, 1, 3} : Finset ℕ) → u2.val ∈ ({0, 1, 3} : Finset ℕ) → v.val ∈ ({0, 2, 4} : Finset ℕ) →
            targetA u1 v = true → targetA u2 v = false → ¬ (u1.val ∈ L ∧ u2.val ∈ L) := by
          rintro u1 u2 v hu1 hu2 hv h1 h0 ⟨hu1L, hu2L⟩
          have hvL : 5 + v.val ∉ L := fun h => hno_edge_L u1 v hu1 hv h1 ⟨hu1L, h⟩
          have hz1 : (C.gates.foldl wstep (vecOf {u1.val, 5 + v.val})).getD z false = true := by
            rw [hagreeZ {u1.val, 5 + v.val} {u1.val} fun x _ hxL => by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact ⟨fun h => h.elim id (fun e => absurd (e ▸ hxL) hvL), Or.inl⟩]
            exact hall_T u1.val hu1L
          have hz2 : (C.gates.foldl wstep (vecOf {u2.val, 5 + v.val})).getD z false = true := by
            rw [hagreeZ {u2.val, 5 + v.val} {u2.val} fun x _ hxL => by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact ⟨fun h => h.elim id (fun e => absurd (e ▸ hxL) hvL), Or.inl⟩]
            exact hall_T u2.val hu2L
          have heq := hdom {u1.val, 5 + v.val} {u2.val, 5 + v.val} (fun x _ hxL => by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            exact ⟨fun h => h.elim (fun e => absurd (e ▸ hu1L) hxL) Or.inr,
                   fun h => h.elim (fun e => absurd (e ▸ hu2L) hxL) Or.inr⟩) (hz1.trans hz2.symm)
          rw [hev_pair u1 v hu1 hv, hev_pair u2 v hu2 hv, h1, h0] at heq; cases heq
        have hno_pair_R : ∀ (u v1 v2 : Fin 5),
            u.val ∈ ({0, 1, 3} : Finset ℕ) → v1.val ∈ ({0, 2, 4} : Finset ℕ) → v2.val ∈ ({0, 2, 4} : Finset ℕ) →
            targetA u v1 = true → targetA u v2 = false → ¬ (5 + v1.val ∈ L ∧ 5 + v2.val ∈ L) := by
          rintro u v1 v2 hu hv1 hv2 h1 h0 ⟨hv1L, hv2L⟩
          have huL : u.val ∉ L := fun h => hno_edge_L u v1 hu hv1 h1 ⟨h, hv1L⟩
          have hz1 : (C.gates.foldl wstep (vecOf {u.val, 5 + v1.val})).getD z false = true := by
            rw [hagreeZ {u.val, 5 + v1.val} {5 + v1.val} fun x _ hxL => by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ hxL) huL) id, Or.inr⟩]
            exact hall_T (5 + v1.val) hv1L
          have hz2 : (C.gates.foldl wstep (vecOf {u.val, 5 + v2.val})).getD z false = true := by
            rw [hagreeZ {u.val, 5 + v2.val} {5 + v2.val} fun x _ hxL => by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ hxL) huL) id, Or.inr⟩]
            exact hall_T (5 + v2.val) hv2L
          have heq := hdom {u.val, 5 + v1.val} {u.val, 5 + v2.val} (fun x _ hxL => by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            exact ⟨fun h => h.elim Or.inl (fun e => absurd (e ▸ hv1L) hxL),
                   fun h => h.elim Or.inl (fun e => absurd (e ▸ hv2L) hxL)⟩) (hz1.trans hz2.symm)
          rw [hev_pair u v1 hu hv1, hev_pair u v2 hu hv2, h1, h0] at heq; cases heq
        have hdisj_pair : ∀ x y, x < 10 → y < 10 → x ∉ L → y ∉ L →
            ∀ w ∈ G, ∀ a b, a ∈ gateIns C.gates w → b ∈ gateIns C.gates w → a ≠ b →
            ∀ u ∈ ({x, y} : Finset ℕ), ¬ (u ∈ reachN C.gates a N ∧ u ∈ reachN C.gates b N) := by
          intro x y hx10 hy10 hxL hyL w hw a b ha hb hab u hu ⟨hua, hub⟩
          have huz : u ∈ reachN C.gates z N :=
            reachN_inter_sub_z C C.output z hunique w a b hw ha hb hab (Finset.mem_inter.mpr ⟨hua, hub⟩)
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact hxL (Finset.mem_filter.mpr ⟨huz, hx10⟩)
          · exact hyL (Finset.mem_filter.mpr ⟨huz, hy10⟩)
        have hkill_05 : ¬ (0 ∉ L ∧ 5 ∉ L) := fun ⟨h0n, h5n⟩ =>
          no_MAJ3_with_Z C hM 0 5 {3, 9} hRsub hcard2
            (hdisj_pair 0 5 (by decide) (by decide) h0n h5n) C.output hout
            ((hev_pair 0 0 (by decide) (by decide)).trans (by decide))
            (hmono_out {0, 9} (insert 0 {3, 9}) (by decide) ((hev_pair 0 4 (by decide) (by decide)).trans (by decide)))
            (hmono_out {3, 5} (insert 5 {3, 9}) (by decide) ((hev_pair 3 0 (by decide) (by decide)).trans (by decide)))
            ((hev_pair 3 4 (by decide) (by decide)).trans (by decide))
            (hsing_false 0 (by decide)) (hsing_false 5 (by decide))
        have hkill_37 : ¬ (3 ∉ L ∧ 7 ∉ L) := fun ⟨h3n, h7n⟩ =>
          no_MAJ3_with_Z C hM 3 7 {1, 5} hRsub hcard2
            (hdisj_pair 3 7 (by decide) (by decide) h3n h7n) C.output hout
            ((hev_pair 3 2 (by decide) (by decide)).trans (by decide))
            (hmono_out {3, 5} (insert 3 {1, 5}) (by decide) ((hev_pair 3 0 (by decide) (by decide)).trans (by decide)))
            (hmono_out {1, 7} (insert 7 {1, 5}) (by decide) ((hev_pair 1 2 (by decide) (by decide)).trans (by decide)))
            ((hev_pair 1 0 (by decide) (by decide)).trans (by decide))
            (hsing_false 3 (by decide)) (hsing_false 7 (by decide))
        have hkill_35 : ¬ (3 ∉ L ∧ 5 ∉ L) := fun ⟨h3n, h5n⟩ =>
          no_MAJ3_with_Z C hM 3 5 {0, 7} hRsub hcard2
            (hdisj_pair 3 5 (by decide) (by decide) h3n h5n) C.output hout
            ((hev_pair 3 0 (by decide) (by decide)).trans (by decide))
            (hmono_out {3, 7} (insert 3 {0, 7}) (by decide) ((hev_pair 3 2 (by decide) (by decide)).trans (by decide)))
            (hmono_out {0, 5} (insert 5 {0, 7}) (by decide) ((hev_pair 0 0 (by decide) (by decide)).trans (by decide)))
            ((hev_pair 0 2 (by decide) (by decide)).trans (by decide))
            (hsing_false 3 (by decide)) (hsing_false 5 (by decide))
        by_cases h3L : 3 ∈ L
        · have h5n : 5 ∉ L := fun h5L => hno_edge_L 3 0 (by decide) (by decide) (by decide) ⟨h3L, h5L⟩
          have h0L : 0 ∈ L := by by_contra h0n; exact hkill_05 ⟨h0n, h5n⟩
          exact hno_pair_L 0 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨h0L, h3L⟩
        · have h5L : 5 ∈ L := by by_contra h5n; exact hkill_35 ⟨h3L, h5n⟩
          have h7L : 7 ∈ L := by by_contra h7n; exact hkill_37 ⟨h3L, h7n⟩
          exact hno_pair_R 0 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) ⟨h5L, h7L⟩
      · -- Case T = ∅: P_6 is connected, so either L = ∅ (P_4 contradiction) or L = all 6 inputs (|G| >= 7 > 6)!
        have hall_F : ∀ i ∈ L, (C.gates.foldl wstep (vecOf {i})).getD z false = false := by
          intro i hiL
          cases hv : (C.gates.foldl wstep (vecOf {i})).getD z false
          · rfl
          · exact absurd ⟨i, hiL, hv⟩ hT
        have hcomp : ∀ (u v : Fin 5), u.val ∈ ({0, 1, 3} : Finset ℕ) → v.val ∈ ({0, 2, 4} : Finset ℕ) →
            targetA u v = true → (u.val ∈ L ↔ 5 + v.val ∈ L) := by
          intro u v hu hv h1
          constructor
          · intro huL
            by_contra hvL
            have hzeq : (C.gates.foldl wstep (vecOf {u.val, 5 + v.val})).getD z false =
                (C.gates.foldl wstep (vecOf {5 + v.val})).getD z false := by
              have h1' := hagreeZ {u.val, 5 + v.val} {u.val} fun x _ hxL => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                exact ⟨fun h => h.elim id (fun e => absurd (e ▸ hxL) hvL), Or.inl⟩
              have h2' := hagreeZ {5 + v.val} ∅ fun x _ hxL => by
                simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
                intro e; exact hvL (e ▸ hxL)
              rw [h1', hall_F u.val huL, h2', hz_empty]
            have h0 := hdom {u.val, 5 + v.val} {5 + v.val} (fun x _ hxL => by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact ⟨fun h => h.elim (fun e => absurd (e ▸ huL) hxL) id, Or.inr⟩) hzeq
            have hvP : 5 + v.val ∈ ({0, 1, 3, 5, 7, 9} : Finset ℕ) := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
              rcases hv with h | h | h <;> omega
            rw [hev_pair u v hu hv, h1, hsing_false (5 + v.val) hvP] at h0; cases h0
          · intro hvL
            by_contra huL
            have hzeq : (C.gates.foldl wstep (vecOf {u.val, 5 + v.val})).getD z false =
                (C.gates.foldl wstep (vecOf {u.val})).getD z false := by
              have h1' := hagreeZ {u.val, 5 + v.val} {5 + v.val} fun x _ hxL => by
                simp only [Finset.mem_insert, Finset.mem_singleton]
                exact ⟨fun h => h.elim (fun e => absurd (e ▸ hxL) huL) id, Or.inr⟩
              have h2' := hagreeZ {u.val} ∅ fun x _ hxL => by
                simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
                intro e; exact huL (e ▸ hxL)
              rw [h1', hall_F (5 + v.val) hvL, h2', hz_empty]
            have h0 := hdom {u.val, 5 + v.val} {u.val} (fun x _ hxL => by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              exact ⟨fun h => h.elim id (fun e => absurd (e ▸ hvL) hxL), Or.inl⟩) hzeq
            have huP : u.val ∈ ({0, 1, 3, 5, 7, 9} : Finset ℕ) := by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hu ⊢
              rcases hu with h | h | h <;> omega
            rw [hev_pair u v hu hv, h1, hsing_false u.val huP] at h0; cases h0
        have hc09 : 0 ∈ L ↔ 9 ∈ L := by simpa using hcomp 0 4 (by decide) (by decide) (by decide)
        have hc05 : 0 ∈ L ↔ 5 ∈ L := by simpa using hcomp 0 0 (by decide) (by decide) (by decide)
        have hc35 : 3 ∈ L ↔ 5 ∈ L := by simpa using hcomp 3 0 (by decide) (by decide) (by decide)
        have hc37 : 3 ∈ L ↔ 7 ∈ L := by simpa using hcomp 3 2 (by decide) (by decide) (by decide)
        have hc17 : 1 ∈ L ↔ 7 ∈ L := by simpa using hcomp 1 2 (by decide) (by decide) (by decide)
        by_cases h0L : 0 ∈ L
        · -- All 6 inputs in L => |Gz| >= 5, plus w1 != w2 outside Rz => |G| >= 7 > 6!
          have h9L : 9 ∈ L := hc09.mp h0L
          have h5L : 5 ∈ L := hc05.mp h0L
          have h3L : 3 ∈ L := hc35.mpr h5L
          have h7L : 7 ∈ L := hc37.mp h3L
          have h1L : 1 ∈ L := hc17.mpr h7L
          let Rz := reachN C.gates z N
          let Gz := Rz.filter fun w => 10 ≤ w ∧ w < 10 + C.gates.length
          have hL6 : 6 ≤ L.card := by
            have hsub : ({0, 1, 3, 5, 7, 9} : Finset ℕ) ⊆ L := by
              intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
              rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
            have := Finset.card_le_card hsub; simpa using this
          have hdisjZ : Disjoint L Gz := by
            rw [Finset.disjoint_left]; intro w hw1 hw2
            have a := (Finset.mem_filter.mp hw1).2; have b := (Finset.mem_filter.mp hw2).2.1; omega
          have hsubRz : L ∪ Gz ⊆ Rz := fun w hw =>
            (Finset.mem_union.mp hw).elim (fun h => (Finset.mem_filter.mp h).1) (fun h => (Finset.mem_filter.mp h).1)
          have hRzcard : L.card + Gz.card ≤ Rz.card := by
            rw [← Finset.card_union_of_disjoint hdisjZ]; exact Finset.card_le_card hsubRz
          have herZ : (Rz.erase z).card ≤ ∑ w ∈ Gz, (gateIns C.gates w).card :=
            (Finset.card_le_card (reachN_erase_sub_biUnion C.gates z N)).trans Finset.card_biUnion_le
          have hsumZ : ∑ w ∈ Gz, (gateIns C.gates w).card ≤ 2 * Gz.card := by
            have hle : ∀ w ∈ Gz, (gateIns C.gates w).card ≤ 2 := fun w hw =>
              hgate_le2 w (Finset.mem_filter.mpr ⟨reachN_sub_of_mem C.gates C.output z hzR N (Finset.mem_filter.mp hw).1,
                (Finset.mem_filter.mp hw).2⟩)
            have h := Finset.sum_le_sum hle; simp only [Finset.sum_const, smul_eq_mul] at h; omega
          have hcardEZ : (Rz.erase z).card + 1 = Rz.card := Finset.card_erase_add_one (out_mem_reachN _ _ _)
          have hGz5 : 5 ≤ Gz.card := by omega
          have hw1_not : w1 ∉ Gz := fun h => by
            have := reachN_le_out C.gates z N w1 (Finset.mem_filter.mp h).1
            have := gateIns_lt C.gates w1 z hzw1; omega
          have hw2_not : w2 ∉ Gz := fun h => by
            have := reachN_le_out C.gates z N w2 (Finset.mem_filter.mp h).1
            have := gateIns_lt C.gates w2 z hzw2; omega
          have hGz_sub : Gz ∪ {w1, w2} ⊆ G := by
            intro w hw; rcases Finset.mem_union.mp hw with h | h
            · exact Finset.mem_filter.mpr ⟨reachN_sub_of_mem C.gates C.output z hzR N (Finset.mem_filter.mp h).1,
                (Finset.mem_filter.mp h).2⟩
            · simp only [Finset.mem_insert, Finset.mem_singleton] at h; rcases h with rfl | rfl <;> assumption
          have hdisj12 : Disjoint Gz {w1, w2} := by
            rw [Finset.disjoint_right]; intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl <;> assumption
          have hcard7 := Finset.card_le_card hGz_sub
          rw [Finset.card_union_of_disjoint hdisj12, Finset.card_pair hw12] at hcard7
          omega
        · -- 0 ∉ L => 3, 0, 5, 7 ∉ L => P_4 on {3, 0, 5, 7}!
          have h5n : 5 ∉ L := fun h => h0L (hc05.mpr h)
          have h3n : 3 ∉ L := fun h => h5n (hc35.mp h)
          have h7n : 7 ∉ L := fun h => h3n (hc37.mpr h)
          have hdisj4 : ∀ w ∈ G, ∀ a b, a ∈ gateIns C.gates w → b ∈ gateIns C.gates w → a ≠ b →
              ∀ x ∈ ({3, 0, 5, 7} : Finset ℕ), ¬ (x ∈ reachN C.gates a N ∧ x ∈ reachN C.gates b N) := by
            intro w hw a b ha hb hab x hx ⟨hxa, hxb⟩
            have hxz : x ∈ reachN C.gates z N :=
              reachN_inter_sub_z C C.output z hunique w a b hw ha hb hab (Finset.mem_inter.mpr ⟨hxa, hxb⟩)
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl | rfl
            · exact h3n (Finset.mem_filter.mpr ⟨hxz, by decide⟩)
            · exact h0L (Finset.mem_filter.mpr ⟨hxz, by decide⟩)
            · exact h5n (Finset.mem_filter.mpr ⟨hxz, by decide⟩)
            · exact h7n (Finset.mem_filter.mpr ⟨hxz, by decide⟩)
          exact no_P4_gen C hM C.output hRsub (fun w hw => Or.inr (hcard2 w hw)) 3 0 5 7 hdisj4 C.output hout
            ((hev_pair 3 0 (by decide) (by decide)).trans (by decide))
            ((hev_pair 3 2 (by decide) (by decide)).trans (by decide))
            ((hev_pair 0 0 (by decide) (by decide)).trans (by decide))
            ((hev_pair 0 2 (by decide) (by decide)).trans (by decide))
            (hsing_false 3 (by decide)) (hsing_false 5 (by decide))

-- ============================================================
-- Part 4: Peel 4 essential inputs (u4=4, u2=2, v1=6, v3=8): 10 -> 9 -> 8 -> 7 -> 6
-- ============================================================

lemma main_proof : ¬ RepSizeAtMost targetA 10 := by
  rintro ⟨C0, hM0, hsz0, hrep0⟩
  -- Peel 1: wire 4 (u4) using (4, 0)=1, (1, 0)=0, (4, 4)=0
  have hmem4 : ∃ g ∈ C0.gates, 4 ∈ g.inputs :=
    essential_in_gates C0 hM0 4 (by decide) (oneEach 4 0) (oneEach 1 0) (oneEach 4 4)
      (by decide) (by decide) (by decide)
      ((hrep0 4 0).trans (by decide)) ((hrep0 1 0).trans (by decide))
      (by decide) ((hrep0 4 4).trans (by decide)) (by decide)
  let C1 := restrictFalse C0 4
  have hM1 : Monotone2 C1 := restrictFalse_mono C0 hM0 4
  have hsz1 : C1.size ≤ 9 := by
    have hlt := restrictFalse_size_lt C0 hM0 4 (by decide) hmem4
    change (restrictFalse C0 4).size ≤ 9; omega
  have hrep1 : ∀ (u v : Fin 5), u.val ≠ 4 → C1.eval (oneEach u v) = targetA u v := by
    intro u v hu
    have h4f : (oneEach u v).getD 4 false = false := by
      revert u v hu; decide
    rw [restrictFalse_eval C0 hM0 4 (by decide) (oneEach u v) (by simp [oneEach]) h4f, hrep0 u v]
  -- Peel 2: wire 2 (u2) using (2, 0)=1, (1, 0)=0, (2, 4)=0
  have hmem2 : ∃ g ∈ C1.gates, 2 ∈ g.inputs :=
    essential_in_gates C1 hM1 2 (by decide) (oneEach 2 0) (oneEach 1 0) (oneEach 2 4)
      (by decide) (by decide) (by decide)
      ((hrep1 2 0 (by decide)).trans (by decide)) ((hrep1 1 0 (by decide)).trans (by decide))
      (by decide) ((hrep1 2 4 (by decide)).trans (by decide)) (by decide)
  let C2 := restrictFalse C1 2
  have hM2 : Monotone2 C2 := restrictFalse_mono C1 hM1 2
  have hsz2 : C2.size ≤ 8 := by
    have hlt := restrictFalse_size_lt C1 hM1 2 (by decide) hmem2
    change (restrictFalse C1 2).size ≤ 8; omega
  have hrep2 : ∀ (u v : Fin 5), u.val ≠ 4 → u.val ≠ 2 → C2.eval (oneEach u v) = targetA u v := by
    intro u v hu4 hu2
    have h2f : (oneEach u v).getD 2 false = false := by
      revert u v hu2; decide
    rw [restrictFalse_eval C1 hM1 2 (by decide) (oneEach u v) (by simp [oneEach]) h2f, hrep1 u v hu4]
  -- Peel 3: wire 6 (v1) using (0, 1)=1, (0, 2)=0, (1, 1)=0
  have hmem6 : ∃ g ∈ C2.gates, 6 ∈ g.inputs :=
    essential_in_gates C2 hM2 6 (by decide) (oneEach 0 1) (oneEach 0 2) (oneEach 1 1)
      (by decide) (by decide) (by decide)
      ((hrep2 0 1 (by decide) (by decide)).trans (by decide))
      ((hrep2 0 2 (by decide) (by decide)).trans (by decide))
      (by decide) ((hrep2 1 1 (by decide) (by decide)).trans (by decide)) (by decide)
  let C3 := restrictFalse C2 6
  have hM3 : Monotone2 C3 := restrictFalse_mono C2 hM2 6
  have hsz3 : C3.size ≤ 7 := by
    have hlt := restrictFalse_size_lt C2 hM2 6 (by decide) hmem6
    change (restrictFalse C2 6).size ≤ 7; omega
  have hrep3 : ∀ (u v : Fin 5), u.val ≠ 4 → u.val ≠ 2 → v.val ≠ 1 → C3.eval (oneEach u v) = targetA u v := by
    intro u v hu4 hu2 hv1
    have h6f : (oneEach u v).getD 6 false = false := by
      revert u v hv1; decide
    rw [restrictFalse_eval C2 hM2 6 (by decide) (oneEach u v) (by simp [oneEach]) h6f, hrep2 u v hu4 hu2]
  -- Peel 4: wire 8 (v3) using (3, 3)=1, (3, 4)=0, (0, 3)=0
  have hmem8 : ∃ g ∈ C3.gates, 8 ∈ g.inputs :=
    essential_in_gates C3 hM3 8 (by decide) (oneEach 3 3) (oneEach 3 4) (oneEach 0 3)
      (by decide) (by decide) (by decide)
      ((hrep3 3 3 (by decide) (by decide) (by decide)).trans (by decide))
      ((hrep3 3 4 (by decide) (by decide) (by decide)).trans (by decide))
      (by decide) ((hrep3 0 3 (by decide) (by decide) (by decide)).trans (by decide)) (by decide)
  let C4 := restrictFalse C3 8
  have hM4 : Monotone2 C4 := restrictFalse_mono C3 hM3 8
  have hsz4 : C4.size ≤ 6 := by
    have hlt := restrictFalse_size_lt C3 hM3 8 (by decide) hmem8
    change (restrictFalse C3 8).size ≤ 6; omega
  have hrep4 : ∀ (u v : Fin 5), u.val ∈ ({0, 1, 3} : Finset ℕ) → v.val ∈ ({0, 2, 4} : Finset ℕ) →
      C4.eval (oneEach u v) = targetA u v := by
    intro u v hu hv
    have hu4 : u.val ≠ 4 := by revert u hu; decide
    have hu2 : u.val ≠ 2 := by revert u hu; decide
    have hv1 : v.val ≠ 1 := by revert v hv; decide
    have h8f : (oneEach u v).getD 8 false = false := by revert u v hv; decide
    rw [restrictFalse_eval C3 hM3 8 (by decide) (oneEach u v) (by simp [oneEach]) h8f, hrep3 u v hu4 hu2 hv1]
  exact no_P6_size_6 C4 hM4 hsz4 hrep4

end PEqualNP.Outside.L_meta_10181

theorem PEqualNP.Outside.L_meta_10181 : (¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16223379 : ℕ).testBit (5 * u.val + v.val)) 10)) :=
  PEqualNP.Outside.L_meta_10181.main_proof
