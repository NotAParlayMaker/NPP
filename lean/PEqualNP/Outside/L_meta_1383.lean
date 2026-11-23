import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1383

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def Dg (gs : List Gate) (n : ℕ) (marked : Finset ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d])
    ((List.range n).map fun i => if i ∈ marked then 1 else 0)

def wval {n : ℕ} (gs : List Gate) (z : Fin n → Bool) (i : ℕ) : Bool :=
  (W gs (List.ofFn z)).getD i false

def wdeg (n : ℕ) (marked : Finset ℕ) (gs : List Gate) (i : ℕ) : ℕ :=
  (Dg gs n marked).getD i 0

lemma W_eq_wires (C : Circuit) (x : List Bool) : W C.gates x = C.wires x := rfl

lemma Dg_eq_lineDegrees (C : Circuit) (n : ℕ) (marked : Finset ℕ) :
    Dg C.gates n marked = C.lineDegrees n marked := rfl

lemma W_append (gs ext : List Gate) (x : List Bool) :
    W (gs ++ ext) x = W ext (W gs x) := by
  simp [W, List.foldl_append]

lemma Dg_append (gs ext : List Gate) (n : ℕ) (marked : Finset ℕ) :
    Dg (gs ++ ext) n marked =
      ext.foldl (fun d g => d ++ [g.lineDegree d]) (Dg gs n marked) := by
  simp [Dg, List.foldl_append]

lemma W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

lemma Dg_snoc (gs : List Gate) (g : Gate) (n : ℕ) (marked : Finset ℕ) :
    Dg (gs ++ [g]) n marked = Dg gs n marked ++ [g.lineDegree (Dg gs n marked)] := by
  simp [Dg, List.foldl_append]

lemma W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc, List.length_append, ih]; simp; omega

lemma Dg_length (gs : List Gate) (n : ℕ) (marked : Finset ℕ) :
    (Dg gs n marked).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Dg]
  | append_singleton gs g ih => rw [Dg_snoc, List.length_append, ih]; simp; omega

lemma getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have hne : t - l.length ≠ 0 := by omega
      cases h : t - l.length with
      | zero => omega
      | succ m => simp [List.getElem?_cons_succ]

lemma getD_of_ge {α : Type} (l : List α) (d : α) {t : ℕ} (ht : l.length ≤ t) :
    l.getD t d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ht]
  rfl

lemma W_getD_prefix (gs ext : List Gate) (x : List Bool) {i : ℕ}
    (hi : i < x.length + gs.length) :
    (W (gs ++ ext) x).getD i false = (W gs x).getD i false := by
  induction ext using List.reverseRecOn with
  | nil => simp
  | append_singleton ext g ih =>
    rw [← List.append_assoc, W_snoc, getD_snoc, W_length]
    have hlt : i < x.length + (gs ++ ext).length := by simp; omega
    rw [if_pos hlt]
    exact ih

lemma Dg_getD_prefix (gs ext : List Gate) (n : ℕ) (marked : Finset ℕ) {i : ℕ}
    (hi : i < n + gs.length) :
    (Dg (gs ++ ext) n marked).getD i 0 = (Dg gs n marked).getD i 0 := by
  induction ext using List.reverseRecOn with
  | nil => simp
  | append_singleton ext g ih =>
    rw [← List.append_assoc, Dg_snoc, getD_snoc, Dg_length]
    have hlt : i < n + (gs ++ ext).length := by simp; omega
    rw [if_pos hlt]
    exact ih

lemma wval_snoc_self {n : ℕ} (gs : List Gate) (g : Gate) (z : Fin n → Bool) :
    wval (gs ++ [g]) z (n + gs.length) =
      g.op.eval (g.inputs.map fun i => wval gs z i) := by
  unfold wval
  rw [W_snoc, getD_snoc, W_length, List.length_ofFn]
  simp

lemma wdeg_snoc_self (n : ℕ) (marked : Finset ℕ) (gs : List Gate) (g : Gate) :
    wdeg n marked (gs ++ [g]) (n + gs.length) = g.lineDegree (Dg gs n marked) := by
  unfold wdeg
  rw [Dg_snoc, getD_snoc, Dg_length]
  simp

lemma wval_of_ge {n : ℕ} (gs : List Gate) (z : Fin n → Bool) {i : ℕ}
    (hi : n + gs.length ≤ i) : wval gs z i = false := by
  unfold wval
  exact getD_of_ge _ _ (by rw [W_length, List.length_ofFn]; exact hi)

lemma wdeg_of_ge (n : ℕ) (marked : Finset ℕ) (gs : List Gate) {i : ℕ}
    (hi : n + gs.length ≤ i) : wdeg n marked gs i = 0 := by
  unfold wdeg
  exact getD_of_ge _ _ (by rw [Dg_length]; exact hi)

lemma wdeg_input_le_one (n : ℕ) (marked : Finset ℕ) (gs : List Gate) {i : ℕ} (hi : i < n) :
    wdeg n marked gs i ≤ 1 := by
  have h1 : wdeg n marked gs i = wdeg n marked [] i := by
    simpa [wdeg] using Dg_getD_prefix [] gs n marked (by simp; exact hi)
  rw [h1]
  unfold wdeg Dg
  simp only [List.foldl_nil, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]
  split_ifs <;> omega

lemma gate_eval_at {n : ℕ} (gs : List Gate) (z : Fin n → Bool) {k : ℕ} (hk : k < gs.length) :
    wval gs z (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun i => if i < n + k then wval gs z i else false) := by
  have hsplit : gs = gs.take k ++ [gs[k]] ++ gs.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop_succ_eq_drop hk,
      List.take_append_drop]
  have hlen : (gs.take k).length = k := List.length_take_of_le hk.le
  have hpre1 : wval gs z (n + k) = wval (gs.take k ++ [gs[k]]) z (n + k) := by
    unfold wval
    conv_lhs => rw [hsplit]
    rw [W_getD_prefix (gs.take k ++ [gs[k]]) (gs.drop (k + 1)) (List.ofFn z)
      (by rw [List.length_ofFn, List.length_append, hlen]; simp)]
  rw [hpre1]
  have hself : wval (gs.take k ++ [gs[k]]) z (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun i => wval (gs.take k) z i) := by
    have h1 := wval_snoc_self (gs.take k) gs[k] z
    rw [hlen] at h1
    exact h1
  rw [hself]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < n + k
  · rw [if_pos hi]
    unfold wval
    have hsp : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsp]
    rw [W_getD_prefix (gs.take k) (gs.drop k) (List.ofFn z) (by rw [List.length_ofFn, hlen]; exact hi)]
  · rw [if_neg hi]
    exact wval_of_ge (gs.take k) z (by rw [hlen]; omega)

lemma gate_deg_at (n : ℕ) (marked : Finset ℕ) (gs : List Gate) {k : ℕ} (hk : k < gs.length) :
    wdeg n marked gs (n + k) =
      match gs[k].op with
      | GateOp.and =>
        (gs[k].inputs.map fun i => if i < n + k then wdeg n marked gs i else 0).sum
      | _ =>
        (gs[k].inputs.map fun i => if i < n + k then wdeg n marked gs i else 0).foldr max 0 := by
  have hsplit : gs = gs.take k ++ [gs[k]] ++ gs.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop_succ_eq_drop hk,
      List.take_append_drop]
  have hlen : (gs.take k).length = k := List.length_take_of_le hk.le
  have hpre1 : wdeg n marked gs (n + k) = wdeg n marked (gs.take k ++ [gs[k]]) (n + k) := by
    unfold wdeg
    conv_lhs => rw [hsplit]
    rw [Dg_getD_prefix (gs.take k ++ [gs[k]]) (gs.drop (k + 1)) n marked
      (by rw [List.length_append, hlen]; simp)]
  rw [hpre1]
  have hself : wdeg n marked (gs.take k ++ [gs[k]]) (n + k) =
      gs[k].lineDegree (Dg (gs.take k) n marked) := by
    have h1 := wdeg_snoc_self n marked (gs.take k) gs[k]
    rw [hlen] at h1
    exact h1
  rw [hself]
  unfold Gate.lineDegree
  have hmap :
      (gs[k].inputs.map fun i => (Dg (gs.take k) n marked).getD i 0) =
      (gs[k].inputs.map fun i => if i < n + k then wdeg n marked gs i else 0) := by
    apply List.map_congr_left
    intro i _
    by_cases hi : i < n + k
    · rw [if_pos hi]
      unfold wdeg
      have hsp : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
      conv_rhs => rw [hsp]
      rw [Dg_getD_prefix (gs.take k) (gs.drop k) n marked (by rw [hlen]; exact hi)]
    · rw [if_neg hi]
      exact getD_of_ge _ _ (by rw [Dg_length, hlen]; omega)
  rw [hmap]
  cases h : gs[k].op <;> simp [h]

lemma lineDegree_and_nil (d : List ℕ) :
    Gate.lineDegree { op := GateOp.and, inputs := [] } d = 0 := by
  simp [Gate.lineDegree]

lemma lineDegree_and_pair (a b : ℕ) (d : List ℕ) :
    Gate.lineDegree { op := GateOp.and, inputs := [a, b] } d = d.getD a 0 + d.getD b 0 := by
  simp [Gate.lineDegree]

lemma lineDegree_or_pair (a b : ℕ) (d : List ℕ) :
    Gate.lineDegree { op := GateOp.or, inputs := [a, b] } d = max (d.getD a 0) (d.getD b 0) := by
  have hne : GateOp.or ≠ GateOp.and := by intro h; cases h
  simp [Gate.lineDegree, hne]

lemma eval_and_nil : GateOp.eval GateOp.and [] = true := rfl

lemma eval_and_pair (a b : Bool) : GateOp.eval GateOp.and [a, b] = (a && b) := by
  simp [GateOp.eval]

lemma eval_or_pair (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  simp [GateOp.eval]

lemma eval_and_single (a : Bool) : GateOp.eval GateOp.and [a] = a := by
  simp [GateOp.eval]

lemma eval_or_single (a : Bool) : GateOp.eval GateOp.or [a] = a := by
  simp [GateOp.eval]

def Valid (n dead : ℕ) (gs : List Gate) (w : ℕ) : Prop :=
  w < n + gs.length ∨ w = dead

lemma valid_dead (n dead : ℕ) (gs : List Gate) : Valid n dead gs dead := Or.inr rfl

lemma valid_mono {n dead : ℕ} {gs ext : List Gate} {w : ℕ} (hv : Valid n dead gs w) :
    Valid n dead (gs ++ ext) w := by
  rcases hv with hlt | rfl
  · exact Or.inl (by simp; omega)
  · exact Or.inr rfl

lemma valid_new (n dead : ℕ) (gs : List Gate) (g : Gate) :
    Valid n dead (gs ++ [g]) (n + gs.length) :=
  Or.inl (by simp)

lemma valid_wval_append {n dead : ℕ} {gs ext : List Gate} {w : ℕ}
    (hv : Valid n dead gs w) (hdead : n + (gs ++ ext).length ≤ dead) (z : Fin n → Bool) :
    wval (gs ++ ext) z w = wval gs z w := by
  rcases hv with hlt | rfl
  · unfold wval
    exact W_getD_prefix gs ext (List.ofFn z) (by rw [List.length_ofFn]; exact hlt)
  · rw [wval_of_ge (gs ++ ext) z hdead, wval_of_ge gs z (by simp at hdead; omega)]

lemma valid_wdeg_append {n dead : ℕ} (marked : Finset ℕ) {gs ext : List Gate} {w : ℕ}
    (hv : Valid n dead gs w) (hdead : n + (gs ++ ext).length ≤ dead) :
    wdeg n marked (gs ++ ext) w = wdeg n marked gs w := by
  rcases hv with hlt | rfl
  · unfold wdeg
    exact Dg_getD_prefix gs ext n marked hlt
  · rw [wdeg_of_ge n marked (gs ++ ext) hdead, wdeg_of_ge n marked gs (by simp at hdead; omega)]

def MonoList (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma monoList_snoc_and2 {gs : List Gate} (h : MonoList gs) (a b : ℕ) :
    MonoList (gs ++ [{ op := GateOp.and, inputs := [a, b] }]) := by
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact h g hg
  · exact ⟨Or.inl rfl, by simp⟩

lemma monoList_snoc_or2 {gs : List Gate} (h : MonoList gs) (a b : ℕ) :
    MonoList (gs ++ [{ op := GateOp.or, inputs := [a, b] }]) := by
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact h g hg
  · exact ⟨Or.inr rfl, by simp⟩

lemma monoList_snoc_true {gs : List Gate} (h : MonoList gs) :
    MonoList (gs ++ [{ op := GateOp.and, inputs := [] }]) := by
  intro g hg
  simp only [List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact h g hg
  · exact ⟨Or.inl rfl, by simp⟩

def St := List Gate × (ℕ → ℕ) × ℕ × ℕ × List (ℕ × ℕ)

def stGs (st : St) : List Gate := st.1
def stCtx (st : St) : ℕ → ℕ := st.2.1
def stR (st : St) : ℕ := st.2.2.1
def stU (st : St) : ℕ := st.2.2.2.1
def stPairs (st : St) : List (ℕ × ℕ) := st.2.2.2.2

def pushCtx (n : ℕ) (c valW : ℕ) (st : St) : St :=
  let gs := stGs st
  let nw := n + gs.length
  let g : Gate := { op := GateOp.or, inputs := [stCtx st c, valW] }
  (gs ++ [g], fun t => if t = c then nw else stCtx st t, stR st, stU st, stPairs st)

def pushR (n : ℕ) (cw c : ℕ) (st : St) : St :=
  let gs := stGs st
  let tW := n + gs.length
  let g1 : Gate := { op := GateOp.and, inputs := [cw, c] }
  let rW := n + gs.length + 1
  let g2 : Gate := { op := GateOp.or, inputs := [stR st, tW] }
  (gs ++ [g1, g2], stCtx st, rW, stU st, stPairs st)

def procOrChild (n : ℕ) (degC : ℕ → ℕ) (cw c : ℕ) (st : St) : St :=
  if 3 ≤ degC c then pushCtx n c cw st else pushR n cw c st

def procInternalAnd (n : ℕ) (cw child sib : ℕ) (st : St) : St :=
  let gs := stGs st
  let tW := n + gs.length
  let g1 : Gate := { op := GateOp.and, inputs := [cw, sib] }
  let nw := n + gs.length + 1
  let g2 : Gate := { op := GateOp.or, inputs := [stCtx st child, tW] }
  (gs ++ [g1, g2], fun t => if t = child then nw else stCtx st t, stR st, stU st, stPairs st)

def procLeafAnd (n : ℕ) (degC : ℕ → ℕ) (cw i' j' : ℕ) (st : St) : St :=
  let gs := stGs st
  if degC i' ≤ 1 then
    let aW := n + gs.length
    let g1 : Gate := { op := GateOp.and, inputs := [i', cw] }
    let pW := n + gs.length + 1
    let g2 : Gate := { op := GateOp.and, inputs := [aW, j'] }
    let uW := n + gs.length + 2
    let g3 : Gate := { op := GateOp.or, inputs := [stU st, pW] }
    (gs ++ [g1, g2, g3], stCtx st, stR st, uW, stPairs st ++ [(aW, j')])
  else
    let bW := n + gs.length
    let g1 : Gate := { op := GateOp.and, inputs := [j', cw] }
    let pW := n + gs.length + 1
    let g2 : Gate := { op := GateOp.and, inputs := [i', bW] }
    let uW := n + gs.length + 2
    let g3 : Gate := { op := GateOp.or, inputs := [stU st, pW] }
    (gs ++ [g1, g2, g3], stCtx st, stR st, uW, stPairs st ++ [(i', bW)])

def stepGate (n dead : ℕ) (degC : ℕ → ℕ) (C : Circuit) (k : ℕ) (st : St) : St :=
  let w0 := n + k
  let cw := stCtx st w0
  if cw = dead then st
  else
    match C.gates[k]? with
    | none => st
    | some g =>
      let clean (i : ℕ) : ℕ := if i < w0 then i else dead
      match g.inputs with
      | [] => st
      | [i] =>
        let i' := clean i
        if 3 ≤ degC i' then pushCtx n i' cw st else st
      | [i, j] =>
        let i' := clean i
        let j' := clean j
        match g.op with
        | GateOp.or =>
          let st1 := procOrChild n degC cw i' st
          procOrChild n degC cw j' st1
        | GateOp.and =>
          if 3 ≤ degC i' then procInternalAnd n cw i' j' st
          else if 3 ≤ degC j' then procInternalAnd n cw j' i' st
          else procLeafAnd n degC cw i' j' st
        | _ => st
      | _ => st

def runDown (n dead : ℕ) (degC : ℕ → ℕ) (C : Circuit) : ℕ → St → St
  | 0, st => st
  | k + 1, st => runDown n dead degC C k (stepGate n dead degC C k st)

def Inv (n dead : ℕ) (marked : Finset ℕ) (C : Circuit) (k : ℕ) (st : St) : Prop :=
  let s := C.gates.length
  let out := C.output
  let gs := stGs st
  (∃ ext, gs = C.gates ++ ext) ∧
  MonoList gs ∧
  gs.length ≤ s + 1 + 4 * (s - k) ∧
  (stPairs st).length ≤ s - k ∧
  Valid n dead gs (stR st) ∧
  Valid n dead gs (stU st) ∧
  (∀ w, Valid n dead gs (stCtx st w)) ∧
  (∀ p ∈ stPairs st, Valid n dead gs p.1 ∧ Valid n dead gs p.2) ∧
  wdeg n marked gs (stR st) ≤ 3 ∧
  wdeg n marked gs (stU st) ≤ 4 ∧
  (∀ p ∈ stPairs st, wdeg n marked gs p.1 ≤ 2 ∧ wdeg n marked gs p.2 ≤ 2) ∧
  (∀ w, stCtx st w ≠ dead →
    n ≤ w ∧ w < n + s ∧ 3 ≤ wdeg n marked C.gates w ∧ wdeg n marked C.gates w ≤ 4 ∧
    wdeg n marked gs (stCtx st w) + wdeg n marked C.gates w ≤ 4) ∧
  (∀ z : Fin n → Bool,
    (wval gs z (stU st) = true ↔
      ∃ p ∈ stPairs st, wval gs z p.1 = true ∧ wval gs z p.2 = true) ∧
    (wval gs z (stR st) = true → wval C.gates z out = true) ∧
    (wval gs z (stU st) = true → wval C.gates z out = true) ∧
    (∀ w, wval gs z (stCtx st w) = true → wval C.gates z w = true → wval C.gates z out = true) ∧
    (wval C.gates z out = true →
      wval gs z (stU st) = true ∨ wval gs z (stR st) = true ∨
      ∃ w < n + k, wval gs z (stCtx st w) = true ∧ wval C.gates z w = true))

lemma wval_eq_C {n : ℕ} {C : Circuit} {gs : List Gate} (hpre : ∃ ext, gs = C.gates ++ ext)
    {w : ℕ} (hw : w < n + C.gates.length) (z : Fin n → Bool) :
    wval gs z w = wval C.gates z w := by
  obtain ⟨ext, rfl⟩ := hpre
  unfold wval
  exact W_getD_prefix C.gates ext (List.ofFn z) (by rw [List.length_ofFn]; exact hw)

lemma wdeg_eq_C {n : ℕ} {marked : Finset ℕ} {C : Circuit} {gs : List Gate}
    (hpre : ∃ ext, gs = C.gates ++ ext) {w : ℕ} (hw : w < n + C.gates.length) :
    wdeg n marked gs w = wdeg n marked C.gates w := by
  obtain ⟨ext, rfl⟩ := hpre
  unfold wdeg
  exact Dg_getD_prefix C.gates ext n marked hw

lemma valid_clean {n dead : ℕ} {C : Circuit} {gs : List Gate}
    (hpre : ∃ ext, gs = C.gates ++ ext) {w0 : ℕ} (hw0 : w0 ≤ n + C.gates.length) (i : ℕ) :
    Valid n dead gs (if i < w0 then i else dead) := by
  by_cases hi : i < w0
  · rw [if_pos hi]
    obtain ⟨ext, rfl⟩ := hpre
    exact Or.inl (by simp; omega)
  · rw [if_neg hi]
    exact Or.inr rfl

lemma wval_clean {n dead : ℕ} {C : Circuit} {gs : List Gate}
    (hpre : ∃ ext, gs = C.gates ++ ext) (hdead : n + gs.length ≤ dead)
    {w0 : ℕ} (hw0 : w0 ≤ n + C.gates.length) (i : ℕ) (z : Fin n → Bool) :
    wval gs z (if i < w0 then i else dead) =
      if i < w0 then wval C.gates z i else false := by
  by_cases hi : i < w0
  · rw [if_pos hi, if_pos hi]
    exact wval_eq_C hpre (by omega) z
  · rw [if_neg hi, if_neg hi]
    exact wval_of_ge gs z hdead

lemma wdeg_clean {n dead : ℕ} {marked : Finset ℕ} {C : Circuit} {gs : List Gate}
    (hpre : ∃ ext, gs = C.gates ++ ext) (hdead : n + gs.length ≤ dead)
    {w0 : ℕ} (hw0 : w0 ≤ n + C.gates.length) (i : ℕ) :
    wdeg n marked gs (if i < w0 then i else dead) =
      if i < w0 then wdeg n marked C.gates i else 0 := by
  by_cases hi : i < w0
  · rw [if_pos hi, if_pos hi]
    exact wdeg_eq_C hpre (by omega)
  · rw [if_neg hi, if_neg hi]
    exact wdeg_of_ge n marked gs hdead

lemma wdeg_C_clean {n dead : ℕ} {marked : Finset ℕ} {C : Circuit}
    (hdead : n + C.gates.length ≤ dead)
    {w0 : ℕ} (hw0 : w0 ≤ n + C.gates.length) (i : ℕ) :
    wdeg n marked C.gates (if i < w0 then i else dead) =
      if i < w0 then wdeg n marked C.gates i else 0 := by
  by_cases hi : i < w0
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]
    exact wdeg_of_ge n marked C.gates hdead

lemma inv_init (n : ℕ) (marked : Finset ℕ) (C : Circuit)
    (hM : Monotone2 C) (hdeg : wdeg n marked C.gates C.output = 4) :
    let s := C.gates.length
    let dead := n + 7 * s + 10
    let wTrue := n + s
    let gs0 := C.gates ++ [{ op := GateOp.and, inputs := [] }]
    let ctx0 : ℕ → ℕ := fun w => if w = C.output then wTrue else dead
    Inv n dead marked C s (gs0, ctx0, dead, dead, []) := by
  intro s dead wTrue gs0 ctx0
  have hout_ge : n ≤ C.output := by
    by_contra hlt
    have := wdeg_input_le_one n marked C.gates (i := C.output) (by omega)
    omega
  have hout_lt : C.output < n + s := by
    by_contra hge
    have := wdeg_of_ge n marked C.gates (i := C.output) (by omega)
    omega
  have hlen0 : gs0.length = s + 1 := by simp [gs0, s]
  have hdead0 : n + gs0.length ≤ dead := by omega
  have hpre : ∃ ext, gs0 = C.gates ++ ext := ⟨_, rfl⟩
  have htrue_deg : wdeg n marked gs0 wTrue = 0 := by
    simpa [gs0, wTrue, s, lineDegree_and_nil] using
      wdeg_snoc_self n marked C.gates { op := GateOp.and, inputs := [] }
  have htrue_val : ∀ z : Fin n → Bool, wval gs0 z wTrue = true := by
    intro z
    simpa [gs0, wTrue, s, eval_and_nil] using
      wval_snoc_self C.gates { op := GateOp.and, inputs := [] } z
  refine ⟨hpre, monoList_snoc_true hM, by dsimp only [stGs]; omega, by simp [stPairs],
    valid_dead _ _ _, valid_dead _ _ _,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    by_cases hw : w = C.output
    · simp only [stGs, stCtx, ctx0, if_pos hw]
      exact Or.inl (by simp [wTrue, gs0, s])
    · simp only [stGs, stCtx, ctx0, if_neg hw]
      exact Or.inr rfl
  · intro p hp; simp [stPairs] at hp
  · simp [stGs, stR, wdeg_of_ge n marked gs0 hdead0]
  · simp [stGs, stU, wdeg_of_ge n marked gs0 hdead0]
  · intro p hp; simp [stPairs] at hp
  · intro w hw
    by_cases heq : w = C.output
    · subst heq
      simp only [stGs, stCtx, ctx0, ite_true]
      refine ⟨hout_ge, hout_lt, by omega, by omega, by omega⟩
    · simp [stCtx, ctx0, heq] at hw
  · intro z
    have hr_f : wval gs0 z dead = false := wval_of_ge gs0 z hdead0
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [stGs, stU, stPairs, hr_f]
    · simp [stGs, stR, hr_f]
    · simp [stGs, stU, hr_f]
    · intro w hcw hvw
      by_cases heq : w = C.output
      · subst heq; exact hvw
      · simp [stGs, stCtx, ctx0, heq, hr_f] at hcw
    · intro hout
      right; right
      refine ⟨C.output, hout_lt, ?_, hout⟩
      simp [stGs, stCtx, ctx0, htrue_val z]

-- Core properties of a single primitive update (ignoring completeness, which is checked per stepGate)
def CoreInv (n dead : ℕ) (marked : Finset ℕ) (C : Circuit) (st : St) : Prop :=
  let s := C.gates.length
  let out := C.output
  let gs := stGs st
  (∃ ext, gs = C.gates ++ ext) ∧
  MonoList gs ∧
  Valid n dead gs (stR st) ∧
  Valid n dead gs (stU st) ∧
  (∀ w, Valid n dead gs (stCtx st w)) ∧
  (∀ p ∈ stPairs st, Valid n dead gs p.1 ∧ Valid n dead gs p.2) ∧
  wdeg n marked gs (stR st) ≤ 3 ∧
  wdeg n marked gs (stU st) ≤ 4 ∧
  (∀ p ∈ stPairs st, wdeg n marked gs p.1 ≤ 2 ∧ wdeg n marked gs p.2 ≤ 2) ∧
  (∀ w, stCtx st w ≠ dead →
    n ≤ w ∧ w < n + s ∧ 3 ≤ wdeg n marked C.gates w ∧ wdeg n marked C.gates w ≤ 4 ∧
    wdeg n marked gs (stCtx st w) + wdeg n marked C.gates w ≤ 4) ∧
  (∀ z : Fin n → Bool,
    (wval gs z (stU st) = true ↔
      ∃ p ∈ stPairs st, wval gs z p.1 = true ∧ wval gs z p.2 = true) ∧
    (wval gs z (stR st) = true → wval C.gates z out = true) ∧
    (wval gs z (stU st) = true → wval C.gates z out = true) ∧
    (∀ w, wval gs z (stCtx st w) = true → wval C.gates z w = true → wval C.gates z out = true))

-- Generic preservation of CoreInv under pushCtx
lemma core_pushCtx {n dead : ℕ} {marked : Finset ℕ} {C : Circuit} {st : St}
    (hc : CoreInv n dead marked C st)
    (hdead : n + (stGs st).length + 1 ≤ dead)
    {c valW : ℕ}
    (hc_ge : n ≤ c) (hc_lt : c < n + C.gates.length)
    (hc_d3 : 3 ≤ wdeg n marked C.gates c) (hc_d4 : wdeg n marked C.gates c ≤ 4)
    (hvW : Valid n dead (stGs st) valW)
    (hdegW : wdeg n marked (stGs st) valW + wdeg n marked C.gates c ≤ 4)
    (hsoundW : ∀ z : Fin n → Bool,
      wval (stGs st) z valW = true → wval C.gates z c = true → wval C.gates z C.output = true) :
    let st' := pushCtx n c valW st
    CoreInv n dead marked C st' ∧
    (stGs st').length = (stGs st).length + 1 ∧
    (stPairs st').length = (stPairs st).length ∧
    (∀ z : Fin n → Bool, wval (stGs st') z (stU st') = wval (stGs st) z (stU st)) ∧
    (∀ z : Fin n → Bool, wval (stGs st') z (stR st') = wval (stGs st) z (stR st)) ∧
    (∀ (z : Fin n → Bool) w, wval (stGs st) z (stCtx st w) = true → wval (stGs st') z (stCtx st' w) = true) ∧
    (∀ z : Fin n → Bool, wval (stGs st) z valW = true → wval (stGs st') z (stCtx st' c) = true) ∧
    (∀ w, Valid n dead (stGs st) w → Valid n dead (stGs st') w ∧
      wdeg n marked (stGs st') w = wdeg n marked (stGs st) w ∧
      ∀ z : Fin n → Bool, wval (stGs st') z w = wval (stGs st) z w) := by
  rcases hc with ⟨hpre, hmono, hvR, hvU, hvCtx, hvP, hdR, hdU, hdP, hdCtx, hsem⟩
  set gs := stGs st
  set g : Gate := { op := GateOp.or, inputs := [stCtx st c, valW] }
  set gs' := gs ++ [g]
  set nw := n + gs.length
  have hlen' : gs'.length = gs.length + 1 := by simp [gs']
  have hdead' : n + gs'.length ≤ dead := by omega
  have hpres : ∀ w, Valid n dead gs w → Valid n dead gs' w ∧
      wdeg n marked gs' w = wdeg n marked gs w ∧
      ∀ z : Fin n → Bool, wval gs' z w = wval gs z w := by
    intro w hw
    exact ⟨valid_mono hw, valid_wdeg_append marked hw hdead',
      fun z => valid_wval_append hw hdead' z⟩
  have hnw_val : ∀ z : Fin n → Bool,
      wval gs' z nw = (wval gs z (stCtx st c) || wval gs z valW) := by
    intro z
    simpa [gs', nw, g, eval_or_pair] using wval_snoc_self gs g z
  have hnw_deg : wdeg n marked gs' nw = max (wdeg n marked gs (stCtx st c)) (wdeg n marked gs valW) := by
    simpa [gs', nw, g, lineDegree_or_pair, wdeg] using wdeg_snoc_self n marked gs g
  have hctx_c_deg : wdeg n marked gs (stCtx st c) + wdeg n marked C.gates c ≤ 4 := by
    by_cases hcd : stCtx st c = dead
    · rw [hcd, wdeg_of_ge n marked gs (by omega)]; omega
    · exact (hdCtx c hcd).2.2.2.2
  have hpre' : ∃ ext, gs' = C.gates ++ ext := by
    obtain ⟨ext, hext⟩ := hpre
    exact ⟨ext ++ [g], by simp [gs', hext]⟩
  refine ⟨⟨hpre', monoList_snoc_or2 hmono _ _, valid_mono hvR, valid_mono hvU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hlen', rfl, ?_, ?_, ?_, ?_, hpres⟩
  · intro w
    change Valid n dead gs' (if w = c then nw else stCtx st w)
    split_ifs
    · exact valid_new n dead gs g
    · exact valid_mono (hvCtx w)
  · intro p hp
    exact ⟨valid_mono (hvP p hp).1, valid_mono (hvP p hp).2⟩
  · change wdeg n marked gs' (stR st) ≤ 3
    rw [(hpres _ hvR).2.1]; exact hdR
  · change wdeg n marked gs' (stU st) ≤ 4
    rw [(hpres _ hvU).2.1]; exact hdU
  · intro p hp
    change wdeg n marked gs' p.1 ≤ 2 ∧ wdeg n marked gs' p.2 ≤ 2
    rw [(hpres _ (hvP p hp).1).2.1, (hpres _ (hvP p hp).2).2.1]
    exact hdP p hp
  · intro w hw
    change (if w = c then nw else stCtx st w) ≠ dead at hw
    by_cases hwc : w = c
    · subst hwc
      change n ≤ w ∧ w < n + C.gates.length ∧ 3 ≤ wdeg n marked C.gates w ∧
        wdeg n marked C.gates w ≤ 4 ∧
        wdeg n marked gs' (if w = w then nw else stCtx st w) + wdeg n marked C.gates w ≤ 4
      rw [if_pos rfl, hnw_deg]
      refine ⟨hc_ge, hc_lt, hc_d3, hc_d4, by omega⟩
    · rw [if_neg hwc] at hw
      change n ≤ w ∧ w < n + C.gates.length ∧ 3 ≤ wdeg n marked C.gates w ∧
        wdeg n marked C.gates w ≤ 4 ∧
        wdeg n marked gs' (if w = c then nw else stCtx st w) + wdeg n marked C.gates w ≤ 4
      rw [if_neg hwc, (hpres _ (hvCtx w)).2.1]
      exact hdCtx w hw
  · intro z
    rcases hsem z with ⟨huP, hrS, huS, hctxS⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change wval gs' z (stU st) = true ↔ ∃ p ∈ stPairs st, wval gs' z p.1 = true ∧ wval gs' z p.2 = true
      rw [(hpres _ hvU).2.2 z, huP]
      constructor <;> rintro ⟨p, hp, h1, h2⟩
      · exact ⟨p, hp, by rwa [(hpres _ (hvP p hp).1).2.2 z], by rwa [(hpres _ (hvP p hp).2).2.2 z]⟩
      · exact ⟨p, hp, by rwa [← (hpres _ (hvP p hp).1).2.2 z], by rwa [← (hpres _ (hvP p hp).2).2.2 z]⟩
    · intro h
      change wval gs' z (stR st) = true at h
      rw [(hpres _ hvR).2.2 z] at h
      exact hrS h
    · intro h
      change wval gs' z (stU st) = true at h
      rw [(hpres _ hvU).2.2 z] at h
      exact huS h
    · intro w hcw hvw
      change wval gs' z (if w = c then nw else stCtx st w) = true at hcw
      by_cases hwc : w = c
      · subst hwc
        rw [if_pos rfl, hnw_val z, Bool.or_eq_true] at hcw
        rcases hcw with h1 | h2
        · exact hctxS w h1 hvw
        · exact hsoundW z h2 hvw
      · rw [if_neg hwc, (hpres _ (hvCtx w)).2.2 z] at hcw
        exact hctxS w hcw hvw
  · intro z; exact (hpres _ hvU).2.2 z
  · intro z; exact (hpres _ hvR).2.2 z
  · intro z w hw
    change wval gs' z (if w = c then nw else stCtx st w) = true
    by_cases hwc : w = c
    · subst hwc; rw [if_pos rfl, hnw_val z, hw]; rfl
    · rw [if_neg hwc, (hpres _ (hvCtx w)).2.2 z]; exact hw
  · intro z hv
    change wval gs' z (if c = c then nw else stCtx st c) = true
    rw [if_pos rfl, hnw_val z, hv]; simp

-- Generic preservation of CoreInv under pushR
lemma core_pushR {n dead : ℕ} {marked : Finset ℕ} {C : Circuit} {st : St}
    (hc : CoreInv n dead marked C st)
    (hdead : n + (stGs st).length + 2 ≤ dead)
    {cw c : ℕ}
    (hvcw : Valid n dead (stGs st) cw) (hvc : Valid n dead (stGs st) c)
    (hdeg : wdeg n marked (stGs st) cw + wdeg n marked (stGs st) c ≤ 3)
    (hsound : ∀ z : Fin n → Bool,
      wval (stGs st) z cw = true → wval (stGs st) z c = true → wval C.gates z C.output = true) :
    let st' := pushR n cw c st
    CoreInv n dead marked C st' ∧
    (stGs st').length = (stGs st).length + 2 ∧
    (stPairs st').length = (stPairs st).length ∧
    (∀ z : Fin n → Bool, wval (stGs st') z (stU st') = wval (stGs st) z (stU st)) ∧
    (∀ z : Fin n → Bool, wval (stGs st) z (stR st) = true → wval (stGs st') z (stR st') = true) ∧
    (∀ z : Fin n → Bool, wval (stGs st) z cw = true → wval (stGs st) z c = true → wval (stGs st') z (stR st') = true) ∧
    (∀ (z : Fin n → Bool) w, wval (stGs st') z (stCtx st' w) = wval (stGs st) z (stCtx st w)) ∧
    (∀ w, Valid n dead (stGs st) w → Valid n dead (stGs st') w ∧
      wdeg n marked (stGs st') w = wdeg n marked (stGs st) w ∧
      ∀ z : Fin n → Bool, wval (stGs st') z w = wval (stGs st) z w) := by
  rcases hc with ⟨hpre, hmono, hvR, hvU, hvCtx, hvP, hdR, hdU, hdP, hdCtx, hsem⟩
  set gs := stGs st
  set g1 : Gate := { op := GateOp.and, inputs := [cw, c] }
  set gs1 := gs ++ [g1]
  set tW := n + gs.length
  set g2 : Gate := { op := GateOp.or, inputs := [stR st, tW] }
  set gs2 := gs1 ++ [g2]
  set rW := n + gs.length + 1
  have hgs2 : gs2 = gs ++ [g1, g2] := by simp [gs2, gs1]
  have hlen1 : gs1.length = gs.length + 1 := by simp [gs1]
  have hlen2 : gs2.length = gs.length + 2 := by simp [gs2, gs1]
  have hdead1 : n + gs1.length ≤ dead := by omega
  have hdead2 : n + gs2.length ≤ dead := by omega
  have hpres : ∀ w, Valid n dead gs w → Valid n dead gs2 w ∧
      wdeg n marked gs2 w = wdeg n marked gs w ∧
      ∀ z : Fin n → Bool, wval gs2 z w = wval gs z w := by
    intro w hw
    rw [hgs2]
    exact ⟨valid_mono hw, valid_wdeg_append marked hw (by rw [← hgs2]; exact hdead2),
      fun z => valid_wval_append hw (by rw [← hgs2]; exact hdead2) z⟩
  have htW_val : ∀ z : Fin n → Bool, wval gs1 z tW = (wval gs z cw && wval gs z c) := by
    intro z
    simpa [gs1, tW, g1, eval_and_pair] using wval_snoc_self gs g1 z
  have htW_deg : wdeg n marked gs1 tW = wdeg n marked gs cw + wdeg n marked gs c := by
    simpa [gs1, tW, g1, lineDegree_and_pair, wdeg] using wdeg_snoc_self n marked gs g1
  have hrW_val : ∀ z : Fin n → Bool,
      wval gs2 z rW = (wval gs z (stR st) || (wval gs z cw && wval gs z c)) := by
    intro z
    have h1 : wval gs2 z rW = (wval gs1 z (stR st) || wval gs1 z tW) := by
      have : rW = n + gs1.length := by omega
      rw [this]
      simpa [gs2, g2, eval_or_pair] using wval_snoc_self gs1 g2 z
    rw [h1, valid_wval_append hvR hdead1 z, htW_val z]
  have hrW_deg : wdeg n marked gs2 rW = max (wdeg n marked gs (stR st)) (wdeg n marked gs cw + wdeg n marked gs c) := by
    have h1 : wdeg n marked gs2 rW = max (wdeg n marked gs1 (stR st)) (wdeg n marked gs1 tW) := by
      have : rW = n + gs1.length := by omega
      rw [this]
      simpa [gs2, g2, lineDegree_or_pair, wdeg] using wdeg_snoc_self n marked gs1 g2
    rw [h1, valid_wdeg_append marked hvR hdead1, htW_deg]
  have hpre' : ∃ ext, gs2 = C.gates ++ ext := by
    obtain ⟨ext, hext⟩ := hpre
    exact ⟨ext ++ [g1, g2], by simp [hgs2, hext]⟩
  have hmono' : MonoList gs2 := monoList_snoc_or2 (monoList_snoc_and2 hmono _ _) _ _
  have hst' : pushR n cw c st = (gs2, stCtx st, rW, stU st, stPairs st) := by
    unfold pushR
    rw [hgs2]
  rw [hst']
  refine ⟨⟨hpre', hmono', ?_, (hpres _ hvU).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hlen2, rfl, ?_, ?_, ?_, ?_, hpres⟩
  · change Valid n dead gs2 rW; exact Or.inl (by omega)
  · intro w; exact (hpres _ (hvCtx w)).1
  · intro p hp; exact ⟨(hpres _ (hvP p hp).1).1, (hpres _ (hvP p hp).2).1⟩
  · change wdeg n marked gs2 rW ≤ 3
    rw [hrW_deg]; omega
  · change wdeg n marked gs2 (stU st) ≤ 4
    rw [(hpres _ hvU).2.1]; exact hdU
  · intro p hp
    change wdeg n marked gs2 p.1 ≤ 2 ∧ wdeg n marked gs2 p.2 ≤ 2
    rw [(hpres _ (hvP p hp).1).2.1, (hpres _ (hvP p hp).2).2.1]
    exact hdP p hp
  · intro w hw
    change n ≤ w ∧ w < n + C.gates.length ∧ 3 ≤ wdeg n marked C.gates w ∧
      wdeg n marked C.gates w ≤ 4 ∧
      wdeg n marked gs2 (stCtx st w) + wdeg n marked C.gates w ≤ 4
    rw [(hpres _ (hvCtx w)).2.1]
    exact hdCtx w hw
  · intro z
    rcases hsem z with ⟨huP, hrS, huS, hctxS⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change wval gs2 z (stU st) = true ↔ ∃ p ∈ stPairs st, wval gs2 z p.1 = true ∧ wval gs2 z p.2 = true
      rw [(hpres _ hvU).2.2 z, huP]
      constructor <;> rintro ⟨p, hp, h1, h2⟩
      · exact ⟨p, hp, by rwa [(hpres _ (hvP p hp).1).2.2 z], by rwa [(hpres _ (hvP p hp).2).2.2 z]⟩
      · exact ⟨p, hp, by rwa [← (hpres _ (hvP p hp).1).2.2 z], by rwa [← (hpres _ (hvP p hp).2).2.2 z]⟩
    · intro h
      change wval gs2 z rW = true at h
      rw [hrW_val z, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h1 | ⟨h2, h3⟩
      · exact hrS h1
      · exact hsound z h2 h3
    · intro h
      change wval gs2 z (stU st) = true at h
      rw [(hpres _ hvU).2.2 z] at h
      exact huS h
    · intro w hcw hvw
      change wval gs2 z (stCtx st w) = true at hcw
      rw [(hpres _ (hvCtx w)).2.2 z] at hcw
      exact hctxS w hcw hvw
  · intro z; exact (hpres _ hvU).2.2 z
  · intro z hr; change wval gs2 z rW = true; rw [hrW_val z, hr]; rfl
  · intro z h1 h2; change wval gs2 z rW = true; rw [hrW_val z, h1, h2]; simp
  · intro z w; exact (hpres _ (hvCtx w)).2.2 z

-- Preservation of CoreInv under procInternalAnd
lemma core_internalAnd {n dead : ℕ} {marked : Finset ℕ} {C : Circuit} {st : St}
    (hc : CoreInv n dead marked C st)
    (hdead : n + (stGs st).length + 2 ≤ dead)
    {cw child sib : ℕ}
    (hvcw : Valid n dead (stGs st) cw) (hvsib : Valid n dead (stGs st) sib)
    (hch_ge : n ≤ child) (hch_lt : child < n + C.gates.length)
    (hch_d3 : 3 ≤ wdeg n marked C.gates child) (hch_d4 : wdeg n marked C.gates child ≤ 4)
    (hdeg : wdeg n marked (stGs st) cw + wdeg n marked (stGs st) sib + wdeg n marked C.gates child ≤ 4)
    (hsound : ∀ z : Fin n → Bool,
      wval (stGs st) z cw = true → wval (stGs st) z sib = true →
      wval C.gates z child = true → wval C.gates z C.output = true) :
    let st' := procInternalAnd n cw child sib st
    CoreInv n dead marked C st' ∧
    (stGs st').length = (stGs st).length + 2 ∧
    (stPairs st').length = (stPairs st).length ∧
    (∀ z : Fin n → Bool, wval (stGs st') z (stU st') = wval (stGs st) z (stU st)) ∧
    (∀ z : Fin n → Bool, wval (stGs st') z (stR st') = wval (stGs st) z (stR st)) ∧
    (∀ (z : Fin n → Bool) w, wval (stGs st) z (stCtx st w) = true → wval (stGs st') z (stCtx st' w) = true) ∧
    (∀ z : Fin n → Bool, wval (stGs st) z cw = true → wval (stGs st) z sib = true →
      wval (stGs st') z (stCtx st' child) = true) := by
  rcases hc with ⟨hpre, hmono, hvR, hvU, hvCtx, hvP, hdR, hdU, hdP, hdCtx, hsem⟩
  set gs := stGs st
  set g1 : Gate := { op := GateOp.and, inputs := [cw, sib] }
  set gs1 := gs ++ [g1]
  set tW := n + gs.length
  set g2 : Gate := { op := GateOp.or, inputs := [stCtx st child, tW] }
  set gs2 := gs1 ++ [g2]
  set nw := n + gs.length + 1
  have hgs2 : gs2 = gs ++ [g1, g2] := by simp [gs2, gs1]
  have hlen1 : gs1.length = gs.length + 1 := by simp [gs1]
  have hlen2 : gs2.length = gs.length + 2 := by simp [gs2, gs1]
  have hdead1 : n + gs1.length ≤ dead := by omega
  have hdead2 : n + gs2.length ≤ dead := by omega
  have hpres : ∀ w, Valid n dead gs w → Valid n dead gs2 w ∧
      wdeg n marked gs2 w = wdeg n marked gs w ∧
      ∀ z : Fin n → Bool, wval gs2 z w = wval gs z w := by
    intro w hw
    rw [hgs2]
    exact ⟨valid_mono hw, valid_wdeg_append marked hw (by rw [← hgs2]; exact hdead2),
      fun z => valid_wval_append hw (by rw [← hgs2]; exact hdead2) z⟩
  have htW_val : ∀ z : Fin n → Bool, wval gs1 z tW = (wval gs z cw && wval gs z sib) := by
    intro z; simpa [gs1, tW, g1, eval_and_pair] using wval_snoc_self gs g1 z
  have htW_deg : wdeg n marked gs1 tW = wdeg n marked gs cw + wdeg n marked gs sib := by
    simpa [gs1, tW, g1, lineDegree_and_pair, wdeg] using wdeg_snoc_self n marked gs g1
  have hnw_val : ∀ z : Fin n → Bool,
      wval gs2 z nw = (wval gs z (stCtx st child) || (wval gs z cw && wval gs z sib)) := by
    intro z
    have h1 : wval gs2 z nw = (wval gs1 z (stCtx st child) || wval gs1 z tW) := by
      have : nw = n + gs1.length := by omega
      rw [this]; simpa [gs2, g2, eval_or_pair] using wval_snoc_self gs1 g2 z
    rw [h1, valid_wval_append (hvCtx child) hdead1 z, htW_val z]
  have hnw_deg : wdeg n marked gs2 nw =
      max (wdeg n marked gs (stCtx st child)) (wdeg n marked gs cw + wdeg n marked gs sib) := by
    have h1 : wdeg n marked gs2 nw = max (wdeg n marked gs1 (stCtx st child)) (wdeg n marked gs1 tW) := by
      have : nw = n + gs1.length := by omega
      rw [this]; simpa [gs2, g2, lineDegree_or_pair, wdeg] using wdeg_snoc_self n marked gs1 g2
    rw [h1, valid_wdeg_append marked (hvCtx child) hdead1, htW_deg]
  have hctx_ch_deg : wdeg n marked gs (stCtx st child) + wdeg n marked C.gates child ≤ 4 := by
    by_cases hcd : stCtx st child = dead
    · rw [hcd, wdeg_of_ge n marked gs (by omega)]; omega
    · exact (hdCtx child hcd).2.2.2.2
  have hpre' : ∃ ext, gs2 = C.gates ++ ext := by
    obtain ⟨ext, hext⟩ := hpre
    exact ⟨ext ++ [g1, g2], by simp [hgs2, hext]⟩
  have hmono' : MonoList gs2 := monoList_snoc_or2 (monoList_snoc_and2 hmono _ _) _ _
  have hst' : procInternalAnd n cw child sib st =
      (gs2, fun t => if t = child then nw else stCtx st t, stR st, stU st, stPairs st) := by
    unfold procInternalAnd
    rw [hgs2]
  rw [hst']
  refine ⟨⟨hpre', hmono', (hpres _ hvR).1, (hpres _ hvU).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hlen2, rfl, ?_, ?_, ?_, ?_⟩
  · intro w
    change Valid n dead gs2 (if w = child then nw else stCtx st w)
    split_ifs
    · exact Or.inl (by omega)
    · exact (hpres _ (hvCtx w)).1
  · intro p hp; exact ⟨(hpres _ (hvP p hp).1).1, (hpres _ (hvP p hp).2).1⟩
  · change wdeg n marked gs2 (stR st) ≤ 3; rw [(hpres _ hvR).2.1]; exact hdR
  · change wdeg n marked gs2 (stU st) ≤ 4; rw [(hpres _ hvU).2.1]; exact hdU
  · intro p hp
    change wdeg n marked gs2 p.1 ≤ 2 ∧ wdeg n marked gs2 p.2 ≤ 2
    rw [(hpres _ (hvP p hp).1).2.1, (hpres _ (hvP p hp).2).2.1]
    exact hdP p hp
  · intro w hw
    change (if w = child then nw else stCtx st w) ≠ dead at hw
    by_cases hwc : w = child
    · subst hwc
      change n ≤ w ∧ w < n + C.gates.length ∧ 3 ≤ wdeg n marked C.gates w ∧
        wdeg n marked C.gates w ≤ 4 ∧
        wdeg n marked gs2 (if w = w then nw else stCtx st w) + wdeg n marked C.gates w ≤ 4
      rw [if_pos rfl, hnw_deg]
      exact ⟨hch_ge, hch_lt, hch_d3, hch_d4, by omega⟩
    · rw [if_neg hwc] at hw
      change n ≤ w ∧ w < n + C.gates.length ∧ 3 ≤ wdeg n marked C.gates w ∧
        wdeg n marked C.gates w ≤ 4 ∧
        wdeg n marked gs2 (if w = child then nw else stCtx st w) + wdeg n marked C.gates w ≤ 4
      rw [if_neg hwc, (hpres _ (hvCtx w)).2.1]
      exact hdCtx w hw
  · intro z
    rcases hsem z with ⟨huP, hrS, huS, hctxS⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change wval gs2 z (stU st) = true ↔ ∃ p ∈ stPairs st, wval gs2 z p.1 = true ∧ wval gs2 z p.2 = true
      rw [(hpres _ hvU).2.2 z, huP]
      constructor <;> rintro ⟨p, hp, h1, h2⟩
      · exact ⟨p, hp, by rwa [(hpres _ (hvP p hp).1).2.2 z], by rwa [(hpres _ (hvP p hp).2).2.2 z]⟩
      · exact ⟨p, hp, by rwa [← (hpres _ (hvP p hp).1).2.2 z], by rwa [← (hpres _ (hvP p hp).2).2.2 z]⟩
    · intro h; change wval gs2 z (stR st) = true at h
      rw [(hpres _ hvR).2.2 z] at h; exact hrS h
    · intro h; change wval gs2 z (stU st) = true at h
      rw [(hpres _ hvU).2.2 z] at h; exact huS h
    · intro w hcw hvw
      change wval gs2 z (if w = child then nw else stCtx st w) = true at hcw
      by_cases hwc : w = child
      · subst hwc
        rw [if_pos rfl, hnw_val z, Bool.or_eq_true, Bool.and_eq_true] at hcw
        rcases hcw with h1 | ⟨h2, h3⟩
        · exact hctxS w h1 hvw
        · exact hsound z h2 h3 hvw
      · rw [if_neg hwc, (hpres _ (hvCtx w)).2.2 z] at hcw
        exact hctxS w hcw hvw
  · intro z; exact (hpres _ hvU).2.2 z
  · intro z; exact (hpres _ hvR).2.2 z
  · intro z w hw
    change wval gs2 z (if w = child then nw else stCtx st w) = true
    by_cases hwc : w = child
    · subst hwc; rw [if_pos rfl, hnw_val z, hw]; rfl
    · rw [if_neg hwc, (hpres _ (hvCtx w)).2.2 z]; exact hw
  · intro z h1 h2
    change wval gs2 z (if child = child then nw else stCtx st child) = true
    rw [if_pos rfl, hnw_val z, h1, h2]; simp

-- Preservation of CoreInv under procLeafAnd
lemma core_leafAnd {n dead : ℕ} {marked : Finset ℕ} {C : Circuit} {st : St}
    (hc : CoreInv n dead marked C st)
    (hdead : n + (stGs st).length + 3 ≤ dead)
    {cw i' j' : ℕ}
    (hvcw : Valid n dead (stGs st) cw)
    (hvi : Valid n dead (stGs st) i') (hvj : Valid n dead (stGs st) j')
    (hdi : wdeg n marked (stGs st) i' = wdeg n marked C.gates i')
    (hdj : wdeg n marked (stGs st) j' = wdeg n marked C.gates j')
    (hdi2 : wdeg n marked C.gates i' ≤ 2) (hdj2 : wdeg n marked C.gates j' ≤ 2)
    (hsum3 : 3 ≤ wdeg n marked C.gates i' + wdeg n marked C.gates j')
    (hsum4 : wdeg n marked (stGs st) cw + (wdeg n marked C.gates i' + wdeg n marked C.gates j') ≤ 4)
    (hsound : ∀ z : Fin n → Bool,
      wval (stGs st) z cw = true → wval (stGs st) z i' = true →
      wval (stGs st) z j' = true → wval C.gates z C.output = true) :
    let st' := procLeafAnd n (wdeg n marked C.gates) cw i' j' st
    CoreInv n dead marked C st' ∧
    (stGs st').length = (stGs st).length + 3 ∧
    (stPairs st').length = (stPairs st).length + 1 ∧
    (∀ z : Fin n → Bool, wval (stGs st) z (stU st) = true → wval (stGs st') z (stU st') = true) ∧
    (∀ z : Fin n → Bool, wval (stGs st) z cw = true → wval (stGs st) z i' = true →
      wval (stGs st) z j' = true → wval (stGs st') z (stU st') = true) ∧
    (∀ z : Fin n → Bool, wval (stGs st') z (stR st') = wval (stGs st) z (stR st)) ∧
    (∀ (z : Fin n → Bool) w, wval (stGs st') z (stCtx st' w) = wval (stGs st) z (stCtx st w)) := by
  rcases hc with ⟨hpre, hmono, hvR, hvU, hvCtx, hvP, hdR, hdU, hdP, hdCtx, hsem⟩
  set gs := stGs st
  have hcommon : ∀ (x y : ℕ) (hvx : Valid n dead gs x) (hvy : Valid n dead gs y)
      (hdx : wdeg n marked gs x + wdeg n marked gs cw ≤ 2)
      (hdy : wdeg n marked gs y ≤ 2)
      (hxy : ∀ z : Fin n → Bool, (wval gs z x && wval gs z cw && wval gs z y) =
        (wval gs z cw && wval gs z i' && wval gs z j'))
      (aW1 bW1 : ℕ) (isFirst : Bool)
      (hab : if isFirst then aW1 = n + gs.length ∧ bW1 = y else aW1 = y ∧ bW1 = n + gs.length),
      let g1 : Gate := { op := GateOp.and, inputs := [x, cw] }
      let g2 : Gate := { op := GateOp.and, inputs := [aW1, bW1] }
      let g3 : Gate := { op := GateOp.or, inputs := [stU st, n + gs.length + 1] }
      let st' : St := (gs ++ [g1, g2, g3], stCtx st, stR st, n + gs.length + 2, stPairs st ++ [(aW1, bW1)])
      CoreInv n dead marked C st' ∧
      (stGs st').length = gs.length + 3 ∧
      (stPairs st').length = (stPairs st).length + 1 ∧
      (∀ z : Fin n → Bool, wval gs z (stU st) = true → wval (stGs st') z (stU st') = true) ∧
      (∀ z : Fin n → Bool, wval gs z cw = true → wval gs z i' = true →
        wval gs z j' = true → wval (stGs st') z (stU st') = true) ∧
      (∀ z : Fin n → Bool, wval (stGs st') z (stR st') = wval gs z (stR st)) ∧
      (∀ (z : Fin n → Bool) w, wval (stGs st') z (stCtx st' w) = wval gs z (stCtx st w)) := by
    intro x y hvx hvy hdx hdy hxy aW1 bW1 isFirst hab g1 g2 g3 st'
    set gs1 := gs ++ [g1]
    set gs2 := gs1 ++ [g2]
    set gs3 := gs2 ++ [g3]
    set fW := n + gs.length
    set pW := n + gs.length + 1
    set uW := n + gs.length + 2
    have hgs3 : gs3 = gs ++ [g1, g2, g3] := by simp [gs3, gs2, gs1]
    have hlen1 : gs1.length = gs.length + 1 := by simp [gs1]
    have hlen2 : gs2.length = gs.length + 2 := by simp [gs2, gs1]
    have hlen3 : gs3.length = gs.length + 3 := by simp [gs3, gs2, gs1]
    have hdead1 : n + gs1.length ≤ dead := by omega
    have hdead2 : n + gs2.length ≤ dead := by omega
    have hdead3 : n + gs3.length ≤ dead := by omega
    have hpres : ∀ w, Valid n dead gs w → Valid n dead gs3 w ∧
        wdeg n marked gs3 w = wdeg n marked gs w ∧
        ∀ z : Fin n → Bool, wval gs3 z w = wval gs z w := by
      intro w hw
      rw [hgs3]
      exact ⟨valid_mono hw, valid_wdeg_append marked hw (by rw [← hgs3]; exact hdead3),
        fun z => valid_wval_append hw (by rw [← hgs3]; exact hdead3) z⟩
    have hfW_val1 : ∀ z : Fin n → Bool, wval gs1 z fW = (wval gs z x && wval gs z cw) := by
      intro z; simpa [gs1, fW, g1, eval_and_pair] using wval_snoc_self gs g1 z
    have hfW_deg1 : wdeg n marked gs1 fW = wdeg n marked gs x + wdeg n marked gs cw := by
      simpa [gs1, fW, g1, lineDegree_and_pair, wdeg] using wdeg_snoc_self n marked gs g1
    have hfW_valid1 : Valid n dead gs1 fW := Or.inl (by omega)
    have hfW_pres3 : wdeg n marked gs3 fW = wdeg n marked gs1 fW ∧
        ∀ z : Fin n → Bool, wval gs3 z fW = wval gs1 z fW := by
      have heq : gs3 = gs1 ++ [g2, g3] := by simp [gs3, gs2]
      rw [heq]
      exact ⟨valid_wdeg_append marked hfW_valid1 (by rw [← heq]; exact hdead3),
        fun z => valid_wval_append hfW_valid1 (by rw [← heq]; exact hdead3) z⟩
    have ha_b : Valid n dead gs1 aW1 ∧ Valid n dead gs1 bW1 ∧
        wdeg n marked gs1 aW1 ≤ 2 ∧ wdeg n marked gs1 bW1 ≤ 2 ∧
        wdeg n marked gs3 aW1 = wdeg n marked gs1 aW1 ∧
        wdeg n marked gs3 bW1 = wdeg n marked gs1 bW1 ∧
        (∀ z : Fin n → Bool, wval gs3 z aW1 = wval gs1 z aW1 ∧ wval gs3 z bW1 = wval gs1 z bW1) ∧
        (∀ z : Fin n → Bool, (wval gs1 z aW1 && wval gs1 z bW1) = (wval gs z cw && wval gs z i' && wval gs z j')) := by
      have hvy1 : Valid n dead gs1 y := valid_mono hvy
      have hvy_deg1 : wdeg n marked gs1 y = wdeg n marked gs y := valid_wdeg_append marked hvy hdead1
      have hvy_val1 : ∀ z : Fin n → Bool, wval gs1 z y = wval gs z y := fun z => valid_wval_append hvy hdead1 z
      have hvy_pres3 : wdeg n marked gs3 y = wdeg n marked gs1 y ∧ ∀ z : Fin n → Bool, wval gs3 z y = wval gs1 z y := by
        rw [(hpres y hvy).2.1, hvy_deg1]
        exact ⟨rfl, fun z => by rw [(hpres y hvy).2.2 z, hvy_val1 z]⟩
      cases isFirst
      · simp only [Bool.false_eq_true, ↓reduceIte] at hab
        rcases hab with ⟨rfl, rfl⟩
        refine ⟨hvy1, hfW_valid1, by omega, by omega, hvy_pres3.1, hfW_pres3.1,
          fun z => ⟨hvy_pres3.2 z, hfW_pres3.2 z⟩, ?_⟩
        intro z
        rw [hvy_val1 z, hfW_val1 z, Bool.and_comm, hxy z]
      · simp only [↓reduceIte] at hab
        rcases hab with ⟨rfl, rfl⟩
        refine ⟨hfW_valid1, hvy1, by omega, by omega, hfW_pres3.1, hvy_pres3.1,
          fun z => ⟨hfW_pres3.2 z, hvy_pres3.2 z⟩, ?_⟩
        intro z
        rw [hfW_val1 z, hvy_val1 z, hxy z]
    rcases ha_b with ⟨hva1, hvb1, hda1, hdb1, hda3, hdb3, hab_val3, hab_prod⟩
    have hpW_val2 : ∀ z : Fin n → Bool, wval gs2 z pW = (wval gs1 z aW1 && wval gs1 z bW1) := by
      intro z
      have : pW = n + gs1.length := by omega
      rw [this]; simpa [gs2, g2, eval_and_pair] using wval_snoc_self gs1 g2 z
    have hpW_deg2 : wdeg n marked gs2 pW = wdeg n marked gs1 aW1 + wdeg n marked gs1 bW1 := by
      have : pW = n + gs1.length := by omega
      rw [this]; simpa [gs2, g2, lineDegree_and_pair, wdeg] using wdeg_snoc_self n marked gs1 g2
    have huW_val : ∀ z : Fin n → Bool, wval gs3 z uW = (wval gs z (stU st) || (wval gs1 z aW1 && wval gs1 z bW1)) := by
      intro z
      have h1 : wval gs3 z uW = (wval gs2 z (stU st) || wval gs2 z pW) := by
        have : uW = n + gs2.length := by omega
        rw [this]; simpa [gs3, g3, eval_or_pair] using wval_snoc_self gs2 g3 z
      have hu2 : wval gs2 z (stU st) = wval gs z (stU st) := by
        have : gs2 = gs ++ [g1, g2] := by simp [gs2, gs1]
        rw [this]; exact valid_wval_append hvU (by rw [← this]; exact hdead2) z
      rw [h1, hu2, hpW_val2 z]
    have huW_deg : wdeg n marked gs3 uW = max (wdeg n marked gs (stU st)) (wdeg n marked gs1 aW1 + wdeg n marked gs1 bW1) := by
      have h1 : wdeg n marked gs3 uW = max (wdeg n marked gs2 (stU st)) (wdeg n marked gs2 pW) := by
        have : uW = n + gs2.length := by omega
        rw [this]; simpa [gs3, g3, lineDegree_or_pair, wdeg] using wdeg_snoc_self n marked gs2 g3
      have hu2 : wdeg n marked gs2 (stU st) = wdeg n marked gs (stU st) := by
        have : gs2 = gs ++ [g1, g2] := by simp [gs2, gs1]
        rw [this]; exact valid_wdeg_append marked hvU (by rw [← this]; exact hdead2)
      rw [h1, hu2, hpW_deg2]
    have hpre' : ∃ ext, gs3 = C.gates ++ ext := by
      obtain ⟨ext, hext⟩ := hpre
      exact ⟨ext ++ [g1, g2, g3], by simp [hgs3, hext]⟩
    have hmono' : MonoList gs3 :=
      monoList_snoc_or2 (monoList_snoc_and2 (monoList_snoc_and2 hmono _ _) _ _) _ _
    have hgs_eq : stGs st' = gs3 := hgs3.symm
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hgs_eq]; exact hpre'
    · rw [hgs_eq]; exact hmono'
    · rw [hgs_eq]; exact (hpres _ hvR).1
    · rw [hgs_eq]; change Valid n dead gs3 uW; exact Or.inl (by omega)
    · intro w; rw [hgs_eq]; exact (hpres _ (hvCtx w)).1
    · intro p hp
      rw [hgs_eq]
      simp only [st', stPairs, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact ⟨(hpres _ (hvP p hp).1).1, (hpres _ (hvP p hp).2).1⟩
      · have h31 : gs3 = gs1 ++ [g2, g3] := by simp [gs3, gs2]
        rw [h31]
        exact ⟨valid_mono hva1, valid_mono hvb1⟩
    · rw [hgs_eq]; change wdeg n marked gs3 (stR st) ≤ 3; rw [(hpres _ hvR).2.1]; exact hdR
    · rw [hgs_eq]; change wdeg n marked gs3 uW ≤ 4; rw [huW_deg]; omega
    · intro p hp
      rw [hgs_eq]
      simp only [st', stPairs, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · rw [(hpres _ (hvP p hp).1).2.1, (hpres _ (hvP p hp).2).2.1]
        exact hdP p hp
      · rw [hda3, hdb3]; exact ⟨hda1, hdb1⟩
    · intro w hw
      rw [hgs_eq]
      change n ≤ w ∧ w < n + C.gates.length ∧ 3 ≤ wdeg n marked C.gates w ∧
        wdeg n marked C.gates w ≤ 4 ∧
        wdeg n marked gs3 (stCtx st w) + wdeg n marked C.gates w ≤ 4
      rw [(hpres _ (hvCtx w)).2.1]
      exact hdCtx w hw
    · intro z
      rw [hgs_eq]
      rcases hsem z with ⟨huP, hrS, huS, hctxS⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · change wval gs3 z uW = true ↔ ∃ p ∈ stPairs st ++ [(aW1, bW1)],
          wval gs3 z p.1 = true ∧ wval gs3 z p.2 = true
        rw [huW_val z, Bool.or_eq_true, Bool.and_eq_true, huP]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (⟨p, hp, h1, h2⟩ | ⟨ha, hb⟩)
          · exact ⟨p, Or.inl hp, by rwa [(hpres _ (hvP p hp).1).2.2 z],
              by rwa [(hpres _ (hvP p hp).2).2.2 z]⟩
          · exact ⟨(aW1, bW1), Or.inr rfl, by rwa [(hab_val3 z).1], by rwa [(hab_val3 z).2]⟩
        · rintro ⟨p, hp | rfl, h1, h2⟩
          · exact Or.inl ⟨p, hp, by rwa [← (hpres _ (hvP p hp).1).2.2 z],
              by rwa [← (hpres _ (hvP p hp).2).2.2 z]⟩
          · exact Or.inr ⟨by rwa [← (hab_val3 z).1], by rwa [← (hab_val3 z).2]⟩
      · intro h; change wval gs3 z (stR st) = true at h
        rw [(hpres _ hvR).2.2 z] at h; exact hrS h
      · intro h; change wval gs3 z uW = true at h
        rw [huW_val z, Bool.or_eq_true] at h
        rcases h with h1 | h2
        · exact huS h1
        · rw [hab_prod z, Bool.and_eq_true, Bool.and_eq_true] at h2
          exact hsound z h2.1.1 h2.1.2 h2.2
      · intro w hcw hvw
        change wval gs3 z (stCtx st w) = true at hcw
        rw [(hpres _ (hvCtx w)).2.2 z] at hcw
        exact hctxS w hcw hvw
    · rw [hgs_eq]; exact hlen3
    · simp [st', stPairs]
    · intro z hu; rw [hgs_eq]; change wval gs3 z uW = true; rw [huW_val z, hu]; rfl
    · intro z h1 h2 h3; rw [hgs_eq]; change wval gs3 z uW = true
      rw [huW_val z, hab_prod z, h1, h2, h3]; simp
    · intro z; rw [hgs_eq]; exact (hpres _ hvR).2.2 z
    · intro z w; rw [hgs_eq]; exact (hpres _ (hvCtx w)).2.2 z
  -- Split on `degC i' ≤ 1`
  by_cases h1 : wdeg n marked C.gates i' ≤ 1
  · have hres := hcommon i' j' hvi hvj (by omega) (by omega)
      (fun z => by cases wval gs z cw <;> cases wval gs z i' <;> cases wval gs z j' <;> rfl)
      (n + gs.length) j' true ⟨rfl, rfl⟩
    have heq : procLeafAnd n (wdeg n marked C.gates) cw i' j' st =
        (gs ++ [{ op := GateOp.and, inputs := [i', cw] },
                { op := GateOp.and, inputs := [n + gs.length, j'] },
                { op := GateOp.or, inputs := [stU st, n + gs.length + 1] }],
         stCtx st, stR st, n + gs.length + 2, stPairs st ++ [(n + gs.length, j')]) := by
      unfold procLeafAnd
      simp only [h1, ↓reduceIte]
      rfl
    simpa only [heq] using hres
  · have hres := hcommon j' i' hvj hvi (by omega) (by omega)
      (fun z => by cases wval gs z cw <;> cases wval gs z i' <;> cases wval gs z j' <;> rfl)
      i' (n + gs.length) false ⟨rfl, rfl⟩
    have heq : procLeafAnd n (wdeg n marked C.gates) cw i' j' st =
        (gs ++ [{ op := GateOp.and, inputs := [j', cw] },
                { op := GateOp.and, inputs := [i', n + gs.length] },
                { op := GateOp.or, inputs := [stU st, n + gs.length + 1] }],
         stCtx st, stR st, n + gs.length + 2, stPairs st ++ [(i', n + gs.length)]) := by
      unfold procLeafAnd
      simp only [h1, ↓reduceIte]
      rfl
    simpa only [heq] using hres

lemma inv_step {n : ℕ} {marked : Finset ℕ} {C : Circuit}
    (hM : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) {st : St}
    (hinv : Inv n (n + 7 * C.gates.length + 10) marked C (k + 1) st) :
    Inv n (n + 7 * C.gates.length + 10) marked C k
      (stepGate n (n + 7 * C.gates.length + 10) (wdeg n marked C.gates) C k st) := by
  set s := C.gates.length
  set dead := n + 7 * s + 10
  set w0 := n + k
  set cw := stCtx st w0
  rcases hinv with ⟨hpre, hmono, hlen, hplen, hvR, hvU, hvCtx, hvP, hdR, hdU, hdP, hdCtx, hsem⟩
  have hcore : CoreInv n dead marked C st :=
    ⟨hpre, hmono, hvR, hvU, hvCtx, hvP, hdR, hdU, hdP, hdCtx,
      fun z => ⟨(hsem z).1, (hsem z).2.1, (hsem z).2.2.1, (hsem z).2.2.2.1⟩⟩
  have hdead_gs : n + (stGs st).length + 4 ≤ dead := by omega
  have hdead_C : n + s ≤ dead := by omega
  -- Case cw = dead
  by_cases hcw_dead : cw = dead
  · have hstep : stepGate n dead (wdeg n marked C.gates) C k st = st := by
      simp [stepGate, w0, cw, hcw_dead]
    rw [hstep]
    refine ⟨hpre, hmono, by omega, by omega, hvR, hvU, hvCtx, hvP, hdR, hdU, hdP, hdCtx, ?_⟩
    intro z
    rcases hsem z with ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    intro hout
    rcases h5 hout with hu | hr | ⟨w, hwlt, hcw_w, hvw⟩
    · exact Or.inl hu
    · exact Or.inr (Or.inl hr)
    · right; right
      have hne : w ≠ w0 := by
        intro heq; subst heq
        have hfalse : wval (stGs st) z dead = false := wval_of_ge _ z (by omega)
        change wval (stGs st) z cw = true at hcw_w
        rw [hcw_dead, hfalse] at hcw_w
        cases hcw_w
      exact ⟨w, by omega, hcw_w, hvw⟩
  -- Case cw ≠ dead
  have hcw_info := hdCtx w0 hcw_dead
  have hw0_d3 : 3 ≤ wdeg n marked C.gates w0 := hcw_info.2.2.1
  have hw0_d4 : wdeg n marked C.gates w0 ≤ 4 := hcw_info.2.2.2.1
  have hcw_deg_sum : wdeg n marked (stGs st) cw + wdeg n marked C.gates w0 ≤ 4 := hcw_info.2.2.2.2
  set g := C.gates[k]
  have hg_mem : g ∈ C.gates := List.getElem_mem hk
  have hg_M := hM g hg_mem
  have hg_op : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg_M.1
  have hg_len : g.inputs.length ≤ 2 := hg_M.2
  have hget : C.gates[k]? = some g := List.getElem?_eq_getElem hk
  have hstep_eq :
      stepGate n dead (wdeg n marked C.gates) C k st =
        let clean (i : ℕ) : ℕ := if i < w0 then i else dead
        match g.inputs with
        | [] => st
        | [i] =>
          let i' := clean i
          if 3 ≤ wdeg n marked C.gates i' then pushCtx n i' cw st else st
        | [i, j] =>
          let i' := clean i
          let j' := clean j
          match g.op with
          | GateOp.or =>
            let st1 := procOrChild n (wdeg n marked C.gates) cw i' st
            procOrChild n (wdeg n marked C.gates) cw j' st1
          | GateOp.and =>
            if 3 ≤ wdeg n marked C.gates i' then procInternalAnd n cw i' j' st
            else if 3 ≤ wdeg n marked C.gates j' then procInternalAnd n cw j' i' st
            else procLeafAnd n (wdeg n marked C.gates) cw i' j' st
          | _ => st
        | _ => st := by
    unfold stepGate
    simp only [w0, cw, if_neg hcw_dead, hget]
  rw [hstep_eq]
  -- Helper: finish Inv from CoreInv + size + pairs + monotonicity + w0 completeness
  have hfinish : ∀ (st' : St),
      CoreInv n dead marked C st' →
      (stGs st').length ≤ (stGs st).length + 4 →
      (stPairs st').length ≤ (stPairs st).length + 1 →
      (∀ z : Fin n → Bool, wval (stGs st) z (stU st) = true → wval (stGs st') z (stU st') = true) →
      (∀ z : Fin n → Bool, wval (stGs st) z (stR st) = true → wval (stGs st') z (stR st') = true) →
      (∀ (z : Fin n → Bool) w, wval (stGs st) z (stCtx st w) = true → wval (stGs st') z (stCtx st' w) = true) →
      (∀ z : Fin n → Bool, wval (stGs st) z cw = true → wval C.gates z w0 = true →
        wval (stGs st') z (stU st') = true ∨ wval (stGs st') z (stR st') = true ∨
        ∃ w < n + k, wval (stGs st') z (stCtx st' w) = true ∧ wval C.gates z w = true) →
      Inv n dead marked C k st' := by
    intro st' hc' hlen' hplen' hUmono hRmono hCtxmono hw0_comp
    rcases hc' with ⟨hp', hm', hvR', hvU', hvCtx', hvP', hdR', hdU', hdP', hdCtx', hsem'⟩
    refine ⟨hp', hm', by omega, by omega, hvR', hvU', hvCtx', hvP', hdR', hdU', hdP', hdCtx', ?_⟩
    intro z
    rcases hsem' z with ⟨h1', h2', h3', h4'⟩
    refine ⟨h1', h2', h3', h4', ?_⟩
    intro hout
    rcases (hsem z).2.2.2.2 hout with hu | hr | ⟨w, hwlt, hcw_w, hvw⟩
    · exact Or.inl (hUmono z hu)
    · exact Or.inr (Or.inl (hRmono z hr))
    · by_cases hweq : w = w0
      · subst hweq; exact hw0_comp z hcw_w hvw
      · exact Or.inr (Or.inr ⟨w, by omega, hCtxmono z w hcw_w, hvw⟩)
  -- Split on g.inputs
  cases hginp : g.inputs with
  | nil =>
    have hd0 : wdeg n marked C.gates w0 = 0 := by
      have := gate_deg_at n marked C.gates hk
      simp only [g] at hginp
      rw [hginp] at this
      cases hop0 : C.gates[k].op <;> simpa [w0, hop0] using this
    omega
  | cons i rest =>
    cases rest with
    | nil =>
      -- Fan-in 1 gate [i]
      dsimp only
      set i' := if i < w0 then i else dead
      have hdeg_eq : wdeg n marked C.gates w0 = wdeg n marked C.gates i' := by
        have := gate_deg_at n marked C.gates hk
        simp only [g] at hginp
        rw [hginp] at this
        have hcl := wdeg_C_clean (marked := marked) hdead_C (w0 := w0) (by omega) i
        rcases hg_op with hop | hop
        · simp only [g] at hop; rw [hop] at this; simpa [w0, i', hcl] using this
        · simp only [g] at hop; rw [hop] at this; simpa [w0, i', hcl] using this
      have hval_eq : ∀ z : Fin n → Bool, wval C.gates z w0 = wval (stGs st) z i' := by
        intro z
        have := gate_eval_at C.gates z hk
        simp only [g] at hginp
        rw [hginp] at this
        have hcl := wval_clean (dead := dead) hpre (by omega) (w0 := w0) (by omega) i z
        rcases hg_op with hop | hop
        · simp only [g] at hop; rw [hop, List.map_cons, List.map_nil, eval_and_single] at this
          rw [hcl]; exact this
        · simp only [g] at hop; rw [hop, List.map_cons, List.map_nil, eval_or_single] at this
          rw [hcl]; exact this
      have hi'_d3 : 3 ≤ wdeg n marked C.gates i' := by omega
      have hi'_d4 : wdeg n marked C.gates i' ≤ 4 := by omega
      have hi'_lt_w0 : i < w0 := by
        by_contra hge
        have : i' = dead := by simp [i', hge]
        rw [this, wdeg_of_ge n marked C.gates hdead_C] at hi'_d3
        omega
      have hi'_eq : i' = i := by simp [i', hi'_lt_w0]
      have hi'_ge : n ≤ i' := by
        by_contra hlt
        have := wdeg_input_le_one n marked C.gates (i := i') (by omega)
        omega
      have hi'_lt_ns : i' < n + s := by omega
      have hres := core_pushCtx hcore (by omega) hi'_ge hi'_lt_ns hi'_d3 hi'_d4
        (hvCtx w0) (by omega) (fun z h1 h2 => by
          apply (hsem z).2.2.2.1 w0 h1
          rw [hval_eq z, wval_eq_C hpre hi'_lt_ns z]
          exact h2)
      rw [if_pos hi'_d3]
      refine hfinish _ hres.1
        (by rw [hres.2.1]; omega)
        (by rw [hres.2.2.1]; omega)
        (fun z h => by rw [hres.2.2.2.1 z]; exact h)
        (fun z h => by rw [hres.2.2.2.2.1 z]; exact h)
        hres.2.2.2.2.2.1 ?_
      intro z hcw_t hvw0
      right; right
      refine ⟨i', by omega, hres.2.2.2.2.2.2.1 z hcw_t, ?_⟩
      rw [hval_eq z, wval_eq_C hpre hi'_lt_ns z] at hvw0
      exact hvw0
    | cons j tail =>
      cases tail with
      | cons _ _ =>
        simp [hginp] at hg_len
      | nil =>
        -- Fan-in 2 gate [i, j]
        dsimp only
        set i' := if i < w0 then i else dead
        set j' := if j < w0 then j else dead
        have hvi' : Valid n dead (stGs st) i' := valid_clean hpre (w0 := w0) (by omega) i
        have hvj' : Valid n dead (stGs st) j' := valid_clean hpre (w0 := w0) (by omega) j
        have hdi'_eq : wdeg n marked (stGs st) i' = wdeg n marked C.gates i' := by
          rw [wdeg_clean hpre (by omega) (w0 := w0) (by omega) i,
              wdeg_C_clean hdead_C (w0 := w0) (by omega) i]
        have hdj'_eq : wdeg n marked (stGs st) j' = wdeg n marked C.gates j' := by
          rw [wdeg_clean hpre (by omega) (w0 := w0) (by omega) j,
              wdeg_C_clean hdead_C (w0 := w0) (by omega) j]
        have hvi'_C : ∀ z : Fin n → Bool, wval (stGs st) z i' = (if i < w0 then wval C.gates z i else false) :=
          fun z => wval_clean hpre (by omega) (w0 := w0) (by omega) i z
        have hvj'_C : ∀ z : Fin n → Bool, wval (stGs st) z j' = (if j < w0 then wval C.gates z j else false) :=
          fun z => wval_clean hpre (by omega) (w0 := w0) (by omega) j z
        rcases hg_op with hop | hop
        · -- g.op = GateOp.and
          rw [hop]
          dsimp only
          have hdeg_and : wdeg n marked C.gates w0 =
              wdeg n marked C.gates i' + wdeg n marked C.gates j' := by
            have := gate_deg_at n marked C.gates hk
            simp only [g] at hginp hop
            rw [hginp, hop] at this
            have hcli := wdeg_C_clean (marked := marked) hdead_C (w0 := w0) (by omega) i
            have hclj := wdeg_C_clean (marked := marked) hdead_C (w0 := w0) (by omega) j
            simpa [w0, i', j', hcli, hclj] using this
          have hval_and : ∀ z : Fin n → Bool, wval C.gates z w0 = (wval (stGs st) z i' && wval (stGs st) z j') := by
            intro z
            have := gate_eval_at C.gates z hk
            simp only [g] at hginp hop
            rw [hginp, hop, List.map_cons, List.map_cons, List.map_nil, eval_and_pair] at this
            rw [hvi'_C z, hvj'_C z]; exact this
          by_cases hi3 : 3 ≤ wdeg n marked C.gates i'
          · rw [if_pos hi3]
            have hi_lt_w0 : i < w0 := by
              by_contra hge
              have : i' = dead := by simp [i', hge]
              rw [this, wdeg_of_ge n marked C.gates hdead_C] at hi3; omega
            have hi'_eq : i' = i := by simp [i', hi_lt_w0]
            have hi'_ge : n ≤ i' := by
              by_contra hlt; have := wdeg_input_le_one n marked C.gates (i := i') (by omega); omega
            have hi'_lt_ns : i' < n + s := by omega
            have hres := core_internalAnd hcore (by omega) (hvCtx w0) hvj'
              hi'_ge hi'_lt_ns hi3 (by omega) (by omega) (fun z h1 h2 h3 => by
                apply (hsem z).2.2.2.1 w0 h1
                rw [hval_and z, wval_eq_C hpre hi'_lt_ns z, h3, h2]; rfl)
            refine hfinish _ hres.1
              (by rw [hres.2.1]; omega)
              (by rw [hres.2.2.1]; omega)
              (fun z h => by rw [hres.2.2.2.1 z]; exact h)
              (fun z h => by rw [hres.2.2.2.2.1 z]; exact h)
              hres.2.2.2.2.2.1 ?_
            intro z hcw_t hvw0
            rw [hval_and z, Bool.and_eq_true] at hvw0
            right; right
            refine ⟨i', by omega, hres.2.2.2.2.2.2 z hcw_t hvw0.2, ?_⟩
            rw [← wval_eq_C hpre hi'_lt_ns z]; exact hvw0.1
          · rw [if_neg hi3]
            by_cases hj3 : 3 ≤ wdeg n marked C.gates j'
            · rw [if_pos hj3]
              have hj_lt_w0 : j < w0 := by
                by_contra hge
                have : j' = dead := by simp [j', hge]
                rw [this, wdeg_of_ge n marked C.gates hdead_C] at hj3; omega
              have hj'_eq : j' = j := by simp [j', hj_lt_w0]
              have hj'_ge : n ≤ j' := by
                by_contra hlt; have := wdeg_input_le_one n marked C.gates (i := j') (by omega); omega
              have hj'_lt_ns : j' < n + s := by omega
              have hres := core_internalAnd hcore (by omega) (hvCtx w0) hvi'
                hj'_ge hj'_lt_ns hj3 (by omega) (by omega) (fun z h1 h2 h3 => by
                  apply (hsem z).2.2.2.1 w0 h1
                  rw [hval_and z, wval_eq_C hpre hj'_lt_ns z, h2, h3]; rfl)
              refine hfinish _ hres.1
                (by rw [hres.2.1]; omega)
                (by rw [hres.2.2.1]; omega)
                (fun z h => by rw [hres.2.2.2.1 z]; exact h)
                (fun z h => by rw [hres.2.2.2.2.1 z]; exact h)
                hres.2.2.2.2.2.1 ?_
              intro z hcw_t hvw0
              rw [hval_and z, Bool.and_eq_true] at hvw0
              right; right
              refine ⟨j', by omega, hres.2.2.2.2.2.2 z hcw_t hvw0.1, ?_⟩
              rw [← wval_eq_C hpre hj'_lt_ns z]; exact hvw0.2
            · rw [if_neg hj3]
              have hres := core_leafAnd hcore (by omega) (hvCtx w0) hvi' hvj'
                hdi'_eq hdj'_eq (by omega) (by omega) (by omega) (by omega)
                (fun z h1 h2 h3 => by
                  apply (hsem z).2.2.2.1 w0 h1
                  rw [hval_and z, h2, h3]; rfl)
              refine hfinish _ hres.1
                (by rw [hres.2.1]; omega)
                (by rw [hres.2.2.1])
                hres.2.2.2.1
                (fun z h => by rw [hres.2.2.2.2.2.1 z]; exact h)
                (fun z w h => by rw [hres.2.2.2.2.2.2 z w]; exact h) ?_
              intro z hcw_t hvw0
              rw [hval_and z, Bool.and_eq_true] at hvw0
              exact Or.inl (hres.2.2.2.2.1 z hcw_t hvw0.1 hvw0.2)
        · -- g.op = GateOp.or
          rw [hop]
          dsimp only
          have hdeg_or : wdeg n marked C.gates w0 =
              max (wdeg n marked C.gates i') (wdeg n marked C.gates j') := by
            have := gate_deg_at n marked C.gates hk
            simp only [g] at hginp hop
            rw [hginp, hop] at this
            have hcli := wdeg_C_clean (marked := marked) hdead_C (w0 := w0) (by omega) i
            have hclj := wdeg_C_clean (marked := marked) hdead_C (w0 := w0) (by omega) j
            simpa [w0, i', j', hcli, hclj] using this
          have hval_or : ∀ z : Fin n → Bool, wval C.gates z w0 = (wval (stGs st) z i' || wval (stGs st) z j') := by
            intro z
            have := gate_eval_at C.gates z hk
            simp only [g] at hginp hop
            rw [hginp, hop, List.map_cons, List.map_cons, List.map_nil, eval_or_pair] at this
            rw [hvi'_C z, hvj'_C z]; exact this
          -- Helper lemma for one procOrChild call
          have hproc : ∀ (stA : St) (c : ℕ) (ci : ℕ),
              c = (if ci < w0 then ci else dead) →
              CoreInv n dead marked C stA →
              n + (stGs stA).length + 2 ≤ dead →
              Valid n dead (stGs stA) cw →
              Valid n dead (stGs stA) c →
              wdeg n marked (stGs stA) cw = wdeg n marked (stGs st) cw →
              wdeg n marked (stGs stA) c = wdeg n marked C.gates c →
              wdeg n marked C.gates c ≤ wdeg n marked C.gates w0 →
              (∀ z : Fin n → Bool, wval (stGs stA) z cw = wval (stGs st) z cw) →
              (∀ z : Fin n → Bool, wval (stGs stA) z c = true → wval C.gates z w0 = true) →
              let stB := procOrChild n (wdeg n marked C.gates) cw c stA
              CoreInv n dead marked C stB ∧
              (stGs stB).length ≤ (stGs stA).length + 2 ∧
              (stPairs stB).length = (stPairs stA).length ∧
              (∀ z : Fin n → Bool, wval (stGs stB) z (stU stB) = wval (stGs stA) z (stU stA)) ∧
              (∀ z : Fin n → Bool, wval (stGs stA) z (stR stA) = true → wval (stGs stB) z (stR stB) = true) ∧
              (∀ (z : Fin n → Bool) w, wval (stGs stA) z (stCtx stA w) = true → wval (stGs stB) z (stCtx stB w) = true) ∧
              (∀ z : Fin n → Bool, wval (stGs stA) z cw = true → wval (stGs stA) z c = true →
                wval (stGs stB) z (stR stB) = true ∨
                ∃ w < n + k, wval (stGs stB) z (stCtx stB w) = true ∧ wval C.gates z w = true) ∧
              (∀ w, Valid n dead (stGs stA) w → Valid n dead (stGs stB) w ∧
                wdeg n marked (stGs stB) w = wdeg n marked (stGs stA) w ∧
                ∀ z : Fin n → Bool, wval (stGs stB) z w = wval (stGs stA) z w) := by
            intro stA c ci hceq hcA hdeadA hvcwA hvcA hdcwA hdcA hdcle hvalcwA hvalc_w0
            unfold procOrChild
            by_cases hc3 : 3 ≤ wdeg n marked C.gates c
            · rw [if_pos hc3]
              have hci_lt : ci < w0 := by
                by_contra hge
                have : c = dead := by simp [hceq, hge]
                rw [this, wdeg_of_ge n marked C.gates hdead_C] at hc3; omega
              have hc_eq_ci : c = ci := by simp [hceq, hci_lt]
              have hc_ge : n ≤ c := by
                by_contra hlt; have := wdeg_input_le_one n marked C.gates (i := c) (by omega); omega
              have hc_lt_ns : c < n + s := by omega
              have hres := core_pushCtx hcA (by omega) hc_ge hc_lt_ns hc3 (by omega)
                hvcwA (by omega) (fun z h1 h2 => by
                  apply (hsem z).2.2.2.1 w0 (by rwa [← hvalcwA z])
                  apply hvalc_w0 z
                  rw [wval_eq_C hcA.1 hc_lt_ns z]; exact h2)
              refine ⟨hres.1, by omega, hres.2.2.1, hres.2.2.2.1,
                fun z hr => by rw [hres.2.2.2.2.1 z]; exact hr,
                hres.2.2.2.2.2.1, ?_, hres.2.2.2.2.2.2.2⟩
              intro z hcw_t hvc_t
              right
              refine ⟨c, by omega, hres.2.2.2.2.2.2.1 z hcw_t, ?_⟩
              rw [← wval_eq_C hcA.1 hc_lt_ns z]; exact hvc_t
            · rw [if_neg hc3]
              have hres := core_pushR hcA hdeadA hvcwA hvcA (by omega)
                (fun z h1 h2 => (hsem z).2.2.2.1 w0 (by rwa [← hvalcwA z]) (hvalc_w0 z h2))
              refine ⟨hres.1, by omega, hres.2.2.1, hres.2.2.2.1,
                hres.2.2.2.2.1,
                fun z w h => by rw [hres.2.2.2.2.2.2.1 z w]; exact h,
                fun z h1 h2 => Or.inl (hres.2.2.2.2.2.1 z h1 h2),
                hres.2.2.2.2.2.2.2⟩
          -- Apply hproc to i', then to j'
          set st1 := procOrChild n (wdeg n marked C.gates) cw i' st
          have h1 := hproc st i' i rfl hcore (by omega) (hvCtx w0) hvi' rfl hdi'_eq (by omega)
            (fun _ => rfl) (fun z hi => by rw [hval_or z, hi]; rfl)
          have hlen1 : (stGs st1).length ≤ (stGs st).length + 2 := h1.2.1
          have hplen1 : (stPairs st1).length = (stPairs st).length := h1.2.2.1
          have hpres_cw := h1.2.2.2.2.2.2.2 cw (hvCtx w0)
          have hpres_j := h1.2.2.2.2.2.2.2 j' hvj'
          have h2 := hproc st1 j' j rfl h1.1 (by omega) hpres_cw.1 hpres_j.1
            hpres_cw.2.1 (by rw [hpres_j.2.1, hdj'_eq]) (by omega)
            hpres_cw.2.2 (fun z hj => by rw [hpres_j.2.2 z] at hj; rw [hval_or z, hj]; simp)
          have hlen2 : (stGs (procOrChild n (wdeg n marked C.gates) cw j' st1)).length ≤ (stGs st1).length + 2 := h2.2.1
          have hplen2 : (stPairs (procOrChild n (wdeg n marked C.gates) cw j' st1)).length = (stPairs st1).length := h2.2.2.1
          refine hfinish _ h2.1
            (by change (stGs (procOrChild n (wdeg n marked C.gates) cw j' st1)).length ≤ _; omega)
            (by change (stPairs (procOrChild n (wdeg n marked C.gates) cw j' st1)).length ≤ _; omega)
            (fun z h => by rw [h2.2.2.2.1 z, h1.2.2.2.1 z]; exact h)
            (fun z h => h2.2.2.2.2.1 z (h1.2.2.2.2.1 z h))
            (fun z w h => h2.2.2.2.2.2.1 z w (h1.2.2.2.2.2.1 z w h)) ?_
          intro z hcw_t hvw0
          rw [hval_or z, Bool.or_eq_true] at hvw0
          rcases hvw0 with hi | hj
          · rcases h1.2.2.2.2.2.2.1 z hcw_t hi with hr1 | ⟨w, hwlt, hctx1, hvw⟩
            · exact Or.inr (Or.inl (h2.2.2.2.2.1 z hr1))
            · exact Or.inr (Or.inr ⟨w, hwlt, h2.2.2.2.2.2.1 z w hctx1, hvw⟩)
          · have hcw1 : wval (stGs st1) z cw = true := by rw [hpres_cw.2.2 z]; exact hcw_t
            have hj1 : wval (stGs st1) z j' = true := by rw [hpres_j.2.2 z]; exact hj
            rcases h2.2.2.2.2.2.2.1 z hcw1 hj1 with hr2 | ⟨w, hwlt, hctx2, hvw⟩
            · exact Or.inr (Or.inl hr2)
            · exact Or.inr (Or.inr ⟨w, hwlt, hctx2, hvw⟩)

lemma inv_runDown {n : ℕ} {marked : Finset ℕ} {C : Circuit}
    (hM : Monotone2 C) :
    ∀ k ≤ C.gates.length, ∀ st : St,
      Inv n (n + 7 * C.gates.length + 10) marked C k st →
      Inv n (n + 7 * C.gates.length + 10) marked C 0
        (runDown n (n + 7 * C.gates.length + 10) (wdeg n marked C.gates) C k st) := by
  intro k
  induction k with
  | zero => intro _ st h; exact h
  | succ k ih =>
    intro hk st h
    exact ih (by omega) _ (inv_step hM (by omega) h)

theorem main (Np Nl : ℕ) (C : Circuit) (hM : Monotone2 C)
    (hDeg : HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) C 4) :
    ∃ (D : Circuit) (J : ℕ) (a b : Fin J → ℕ) (u r : ℕ),
      Monotone2 D ∧
      D.size ≤ 7 * C.size + 1 ∧
      J ≤ D.size ∧
      HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) D 4 ∧
      D.gates.getLast? = some { op := GateOp.or, inputs := [u, r] } ∧
      D.output + 1 = Np + Nl + D.gates.length ∧
      (∀ j : Fin J,
        (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (a j) 0 ≤ 2 ∧
        (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (b j) 0 ≤ 2) ∧
      (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD r 0 ≤ 3 ∧
      ∀ z : Fin (Np + Nl) → Bool,
        circuitFun (Np + Nl) D z = circuitFun (Np + Nl) C z ∧
        ((D.wires (List.ofFn z)).getD u false = true ↔
          ∃ i : Fin J,
            (D.wires (List.ofFn z)).getD (a i) false = true ∧
            (D.wires (List.ofFn z)).getD (b i) false = true) := by
  set n := Np + Nl
  set marked := Finset.Ico Np (Np + Nl)
  set s := C.gates.length
  have hDeg' : wdeg n marked C.gates C.output ≤ 4 := hDeg
  by_cases hle3 : wdeg n marked C.gates C.output ≤ 3
  · -- Easy case: output already has degree at most 3
    set dead := n + s + 1
    set rW := if C.output < n + s then C.output else dead
    set gLast : Gate := { op := GateOp.or, inputs := [dead, rW] }
    set D : Circuit := { gates := C.gates ++ [gLast], output := n + s }
    have hDlen : D.gates.length = s + 1 := by simp [D, s]
    have hdead_D : n + D.gates.length ≤ dead := by omega
    have hr_val_C : ∀ z : Fin n → Bool, wval C.gates z rW = wval C.gates z C.output := by
      intro z
      by_cases ho : C.output < n + s
      · simp [rW, ho]
      · simp only [rW, if_neg ho]
        rw [wval_of_ge C.gates z (by omega), wval_of_ge C.gates z (by omega)]
    have hr_deg_C : wdeg n marked C.gates rW ≤ 3 := by
      by_cases ho : C.output < n + s
      · simp [rW, ho, hle3]
      · simp only [rW, if_neg ho]
        rw [wdeg_of_ge n marked C.gates (by omega)]; omega
    have hr_valid : Valid n dead C.gates rW := by
      by_cases ho : C.output < n + s
      · simp only [rW, if_pos ho]; exact Or.inl ho
      · simp only [rW, if_neg ho]; exact Or.inr rfl
    have hD_deg_last : wdeg n marked D.gates (n + s) ≤ 4 := by
      have h1 := wdeg_snoc_self n marked C.gates gLast
      simp only [gLast, lineDegree_or_pair] at h1
      change wdeg n marked (C.gates ++ [gLast]) (n + s) ≤ 4
      rw [h1]
      have hd1 : (Dg C.gates n marked).getD dead 0 = 0 :=
        wdeg_of_ge n marked C.gates (by omega)
      have hd2 : (Dg C.gates n marked).getD rW 0 ≤ 3 := hr_deg_C
      omega
    have hD_deg_r : wdeg n marked D.gates rW ≤ 3 := by
      change wdeg n marked (C.gates ++ [gLast]) rW ≤ 3
      rw [valid_wdeg_append marked hr_valid (by simp; omega)]
      exact hr_deg_C
    refine ⟨D, 0, Fin.elim0, Fin.elim0, dead, rW,
      monoList_snoc_or2 hM _ _, by simp [Circuit.size, hDlen]; omega, by omega,
      hD_deg_last, by simp [D, gLast], by dsimp only [D]; rw [hDlen]; omega,
      fun j => Fin.elim0 j, hD_deg_r, ?_⟩
    intro z
    have hdead_f : wval D.gates z dead = false := wval_of_ge D.gates z hdead_D
    refine ⟨?_, ?_⟩
    · change wval (C.gates ++ [gLast]) z (n + s) = wval C.gates z C.output
      rw [wval_snoc_self]
      simp only [gLast, List.map_cons, List.map_nil, eval_or_pair]
      rw [wval_of_ge C.gates z (by omega), hr_val_C z]
      simp
    · change wval D.gates z dead = true ↔ _
      rw [hdead_f]
      simp
  · -- Main case: output has degree 4
    have hdeg4 : wdeg n marked C.gates C.output = 4 := by omega
    have hs_pos : 1 ≤ s := by
      by_contra h0
      have hs0 : s = 0 := by omega
      by_cases ho : C.output < n
      · have := wdeg_input_le_one n marked C.gates ho; omega
      · have := wdeg_of_ge n marked C.gates (i := C.output) (by omega); omega
    set dead := n + 7 * s + 10
    set gs0 := C.gates ++ [{ op := GateOp.and, inputs := [] }]
    set ctx0 : ℕ → ℕ := fun w => if w = C.output then n + s else dead
    set st0 : St := (gs0, ctx0, dead, dead, [])
    have hinv0 : Inv n dead marked C s st0 := inv_init n marked C hM hdeg4
    set stF := runDown n dead (wdeg n marked C.gates) C s st0
    have hinvF : Inv n dead marked C 0 stF := inv_runDown hM s (le_refl s) st0 hinv0
    rcases hinvF with ⟨hpre, hmono, hlen, hplen, hvR, hvU, hvCtx, hvP, hdR, hdU, hdP, hdCtx, hsem⟩
    set gsF := stGs stF
    set uW := stU stF
    set rW := stR stF
    set ps := stPairs stF
    set gLast : Gate := { op := GateOp.or, inputs := [uW, rW] }
    set D : Circuit := { gates := gsF ++ [gLast], output := n + gsF.length }
    have hDlen : D.gates.length = gsF.length + 1 := by simp [D]
    have hgsF_ge : s ≤ gsF.length := by
      obtain ⟨ext, hext⟩ := hpre
      have : gsF.length = (C.gates ++ ext).length := congrArg List.length hext
      simp only [List.length_append] at this
      omega
    have hDsize : D.size ≤ 7 * C.size + 1 := by
      change D.gates.length ≤ 7 * s + 1
      omega
    have hdead_D : n + D.gates.length ≤ dead := by omega
    have hJ : ps.length ≤ D.size := by
      change ps.length ≤ D.gates.length
      omega
    have hD_deg_out : wdeg n marked D.gates (n + gsF.length) ≤ 4 := by
      change wdeg n marked (gsF ++ [gLast]) (n + gsF.length) ≤ 4
      rw [wdeg_snoc_self]
      simp only [gLast, lineDegree_or_pair]
      change max (wdeg n marked gsF uW) (wdeg n marked gsF rW) ≤ 4
      omega
    have hD_deg_r : wdeg n marked D.gates rW ≤ 3 := by
      change wdeg n marked (gsF ++ [gLast]) rW ≤ 3
      rw [valid_wdeg_append marked hvR (by simpa [D] using hdead_D)]
      exact hdR
    refine ⟨D, ps.length, fun j => ps[j].1, fun j => ps[j].2, uW, rW,
      monoList_snoc_or2 hmono _ _, hDsize, hJ, hD_deg_out, by simp [D, gLast],
      by dsimp only [D]; rw [hDlen]; omega,
      ?_, hD_deg_r, ?_⟩
    · intro j
      have hmem : ps[j] ∈ ps := List.getElem_mem j.isLt
      change wdeg n marked (gsF ++ [gLast]) ps[j].1 ≤ 2 ∧
        wdeg n marked (gsF ++ [gLast]) ps[j].2 ≤ 2
      rw [valid_wdeg_append marked (hvP _ hmem).1 (by simpa [D] using hdead_D),
          valid_wdeg_append marked (hvP _ hmem).2 (by simpa [D] using hdead_D)]
      exact hdP _ hmem
    · intro z
      rcases hsem z with ⟨huP, hrS, huS, _, hcomp⟩
      have hDu : wval D.gates z uW = wval gsF z uW :=
        valid_wval_append hvU (by simpa [D] using hdead_D) z
      have hDr : wval D.gates z rW = wval gsF z rW :=
        valid_wval_append hvR (by simpa [D] using hdead_D) z
      refine ⟨?_, ?_⟩
      · change wval (gsF ++ [gLast]) z (n + gsF.length) = wval C.gates z C.output
        rw [wval_snoc_self]
        simp only [gLast, List.map_cons, List.map_nil, eval_or_pair]
        apply Bool.eq_iff_iff.mpr
        rw [Bool.or_eq_true]
        constructor
        · rintro (hu | hr)
          · exact huS hu
          · exact hrS hr
        · intro hout
          rcases hcomp hout with hu | hr | ⟨w, hwlt, hcw, _⟩
          · exact Or.inl hu
          · exact Or.inr hr
          · exfalso
            have hne : stCtx stF w ≠ dead := by
              intro heq
              rw [heq, wval_of_ge gsF z (by omega)] at hcw
              cases hcw
            have hge := (hdCtx w hne).1
            omega
      · change wval D.gates z uW = true ↔ _
        rw [hDu, huP]
        constructor
        · rintro ⟨p, hp, h1, h2⟩
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
          refine ⟨⟨i, hi⟩, ?_, ?_⟩
          · change wval D.gates z ps[i].1 = true
            rw [valid_wval_append (hvP _ hp).1 (by simpa [D] using hdead_D) z]; exact h1
          · change wval D.gates z ps[i].2 = true
            rw [valid_wval_append (hvP _ hp).2 (by simpa [D] using hdead_D) z]; exact h2
        · rintro ⟨i, h1, h2⟩
          have hmem : ps[i] ∈ ps := List.getElem_mem i.isLt
          refine ⟨ps[i], hmem, ?_, ?_⟩
          · change wval D.gates z ps[i].1 = true at h1
            rwa [valid_wval_append (hvP _ hmem).1 (by simpa [D] using hdead_D) z] at h1
          · change wval D.gates z ps[i].2 = true at h2
            rwa [valid_wval_append (hvP _ hmem).2 (by simpa [D] using hdead_D) z] at h2

end PEqualNP.Outside.L_meta_1383

theorem PEqualNP.Outside.L_meta_1383 : ∀ (Np Nl : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) C 4 → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (J : ℕ) (a b : Fin J → ℕ) (u r : ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 7 * C.size + 1 ∧ J ≤ D.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) D 4 ∧ D.gates.getLast? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, r] } ∧ D.output + 1 = Np + Nl + D.gates.length ∧ (∀ j : Fin J, (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (a j) 0 ≤ 2 ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (b j) 0 ≤ 2) ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (r) 0 ≤ 3 ∧ ∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z ∧ ((D.wires (List.ofFn z)).getD u false = true ↔ ∃ i : Fin J, (D.wires (List.ofFn z)).getD (a i) false = true ∧ (D.wires (List.ofFn z)).getD (b i) false = true) := by
  exact PEqualNP.Outside.L_meta_1383.main
