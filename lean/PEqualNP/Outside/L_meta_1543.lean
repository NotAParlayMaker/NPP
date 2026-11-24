import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1543_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The wire list of a gate list: the inputs, then one value per gate in order.
def wf (gs : List Gate) (v : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) v

-- The value of wire w of the circuit (gates, output) on input x.
def val (gs : List Gate) (x : Fin 10 → Bool) (w : ℕ) : Bool :=
  (wf gs (List.ofFn x)).getD w false

lemma wf_cons (g : Gate) (gs : List Gate) (v : List Bool) :
    wf (g :: gs) v = wf gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) := rfl

lemma wf_len (gs : List Gate) (v : List Bool) : (wf gs v).length = v.length + gs.length := by
  induction gs generalizing v with
  | nil => simp [wf]
  | cons g gs ih => rw [wf_cons, ih]; simp; omega

lemma wf_getD (gs : List Gate) (v : List Bool) (w : ℕ) (hw : w < v.length) :
    (wf gs v).getD w false = v.getD w false := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    rw [wf_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma wf_split (gs : List Gate) (v : List Bool) (j : ℕ) :
    wf gs v = wf (gs.drop j) (wf (gs.take j) v) := by
  simpa only [wf, List.foldl_append] using
    congrArg (fun l : List Gate => wf l v) (List.take_append_drop j gs).symm

lemma val_input (gs : List Gate) (x : Fin 10 → Bool) (w : ℕ) (h : w < 10) :
    val gs x w = x (Fin.mk w h) := by
  change (wf gs (List.ofFn x)).getD w false = x (Fin.mk w h)
  have hw : w < (List.ofFn x).length := by simpa using h
  rw [wf_getD _ _ _ hw, List.getD_eq_getElem _ _ hw, List.getElem_ofFn]

lemma val_beyond (gs : List Gate) (x : Fin 10 → Bool) (w : ℕ) (h : 10 + gs.length ≤ w) :
    val gs x w = false := by
  change (wf gs (List.ofFn x)).getD w false = false
  have hl : (wf gs (List.ofFn x)).length = 10 + gs.length := by rw [wf_len]; simp
  exact List.getD_eq_default _ _ (by rw [hl]; exact h)

lemma val_gate (gs : List Gate) (x : Fin 10 → Bool) (w : ℕ)
    (hn : 10 ≤ w) (hw : w < 10 + gs.length) :
    val gs x w =
      (gs[w - 10]'(by omega)).op.eval
        ((gs[w - 10]'(by omega)).inputs.map fun r => if r < w then val gs x r else false) := by
  let j := w - 10
  have hj : j < gs.length := by omega
  let g := gs[j]
  let earlier := wf (gs.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp only [earlier, wf_len, List.length_ofFn, List.length_take, j]
    omega
  have split : wf gs (List.ofFn x) = wf (g :: gs.drop (j + 1)) earlier := by
    rw [wf_split (gs := gs) (v := List.ofFn x) (j := j), List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then val gs x r else false := by
    by_cases hr : r < w
    · rw [if_pos hr]
      change earlier.getD r false = (wf gs (List.ofFn x)).getD r false
      rw [split]
      exact (wf_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [if_neg hr]
      exact List.getD_eq_default _ _ (by omega)
  change (wf gs (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then val gs x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [wf_cons]
  rw [wf_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]
lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma gate_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (hn : 10 ≤ w) (hk : w < 10 + gs.length) (x y : Fin 10 → Bool)
    (h : ∀ i, i < w → val gs x i = true → val gs y i = true) :
    val gs x w = true → val gs y w = true := by
  rw [val_gate _ _ _ hn hk, val_gate _ _ _ hn hk]
  have key : ∀ i ∈ (gs[w - 10]'(by omega)).inputs,
      (if i < w then val gs x i else false) = true →
      (if i < w then val gs y i else false) = true := by
    intro i _ hb
    by_cases hi : i < w
    · rw [if_pos hi] at hb ⊢
      exact h i hi hb
    · rw [if_neg hi] at hb ⊢
      exact hb
  have hmem := hAO _ (List.getElem_mem (show w - 10 < gs.length by omega))
  rcases hmem with hmem | hmem
  · rw [hmem]
    simp only [GateOp.eval, List.all_map, List.all_eq_true, id_eq]
    intro hall b hb
    exact key b hb (hall b hb)
  · rw [hmem]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, id_eq]
    rintro ⟨b, hb, hb2⟩
    exact ⟨b, hb, key b hb hb2⟩

lemma val_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin 10 → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) :
    val gs x w = true → val gs y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < 10
    · rw [val_input _ _ _ hw, val_input _ _ _ hw]
      exact hxy _
    by_cases hk : w < 10 + gs.length
    · have hn : 10 ≤ w := by omega
      exact gate_mono gs hAO w hn hk x y (fun i hi => ih i (by omega))
    · rw [val_beyond _ _ _ (by omega), val_beyond _ _ _ (by omega)]
      intro h; exact h

-- map of a wire index when the gate at position p is erased
def mur (p z : ℕ) : ℕ := if z < 10 + p then z else z - 1

-- the gate with every wire remapped by mur p
def mg (p : ℕ) (g : Gate) : Gate := Gate.mk g.op (g.inputs.map (mur p))

-- the gate list with the gate at position p erased and the later wires shifted down
def emap (p : ℕ) (gs : List Gate) : List Gate := (gs.map (mg p)).eraseIdx p

lemma emap_eq (p : ℕ) (gs : List Gate) : emap p gs = (gs.eraseIdx p).map (mg p) := by
  unfold emap
  rw [List.eraseIdx_map]

lemma eraseIdx_getElem? (l : List Gate) : ∀ (p j : ℕ), (l.eraseIdx p)[j]? =
    if j < p then l[j]? else l[j + 1]? := by
  induction l with
  | nil => intro p j; simp
  | cons a l ih =>
    intro p j
    cases p with
    | zero => simp
    | succ p =>
      cases j with
      | zero => simp
      | succ j => simpa using ih p j

lemma emap_getElem? (p k : ℕ) (gs : List Gate) (hne : k ≠ p) :
    (emap p gs)[if k < p then k else k - 1]? = (gs[k]?).map (mg p) := by
  rw [emap_eq, List.getElem?_map]
  by_cases hkp : k < p
  · rw [if_pos hkp, eraseIdx_getElem?, if_pos hkp]
  · rw [if_neg hkp, eraseIdx_getElem?, if_neg (by omega), show k - 1 + 1 = k by omega]

lemma emap_length (p : ℕ) (gs : List Gate) (hp : p < gs.length) :
    (emap p gs).length + 1 = gs.length := by
  unfold emap
  rw [List.eraseIdx_map, List.length_map]
  exact List.length_eraseIdx_add_one hp

lemma val_gate? (gs : List Gate) (x : Fin 10 → Bool) (w : ℕ) (hn : 10 ≤ w)
    (hk : w < 10 + gs.length) :
    val gs x w = ((gs[w - 10]?).getD (Gate.mk GateOp.and [])).op.eval
      (((gs[w - 10]?).getD (Gate.mk GateOp.and [])).inputs.map fun r =>
        if r < w then val gs x r else false) := by
  rw [val_gate _ _ _ hn hk, List.getElem?_eq_getElem (by omega), Option.getD_some]

lemma mur_le (p r : ℕ) : mur p r ≤ r := by
  unfold mur; split_ifs <;> omega

lemma mur_mono (p : ℕ) {a b : ℕ} (h : a ≤ b) : mur p a ≤ mur p b := by
  have ha := mur_le p a
  unfold mur
  split_ifs <;> omega

lemma val_erase (gs : List Gate) (x : Fin 10 → Bool) (p : ℕ) (hp : p < gs.length)
    (hdead : ∀ (j : ℕ) (hj : j < gs.length), j ≠ p → 10 + p ∉ (gs[j]'hj).inputs) :
    ∀ z : ℕ, z ≠ 10 + p → val (emap p gs) x (mur p z) = val gs x z := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro hz
    by_cases h10 : z < 10
    · have hm : mur p z = z := by simp [mur]; omega
      rw [hm, val_input _ _ _ h10, val_input _ _ _ h10]
    have hge : 10 ≤ z := by omega
    have hfl : (emap p gs).length + 1 = gs.length := emap_length p gs hp
    by_cases hcase : z < 10 + p
    · have hmur : mur p z = z := by simp [mur, hcase]
      by_cases hzlen : z < 10 + gs.length
      · have hk : z - 10 < gs.length := by omega
        have hne : z - 10 ≠ p := by intro h; exact hz (by omega)
        have hlt : mur p z < 10 + (emap p gs).length := by rw [hmur]; omega
        rw [val_gate? (emap p gs) x (mur p z) (by omega) hlt, val_gate? gs x z hge hzlen]
        have h1 : (emap p gs)[mur p z - 10]? = (gs[z - 10]?).map (mg p) := by
          rw [show mur p z - 10 = (if z - 10 < p then z - 10 else z - 10 - 1) from by
            rw [hmur, if_pos (by omega)]]
          exact emap_getElem? p (z - 10) gs hne
        rw [h1, List.getElem?_eq_getElem hk]
        simp only [Option.map_some, Option.getD_some, mg, List.map_map, Function.comp_def]
        congr 1
        apply List.map_congr_left
        intro r hrin
        have hrne : r ≠ 10 + p := by
          intro h; exact hdead (z - 10) hk hne (h ▸ hrin)
        by_cases hr : r < z
        · have hb : mur p r ≤ r := mur_le p r
          have h2 : mur p r < mur p z := by omega
          rw [if_pos hr, if_pos h2]
          exact ih r (by omega) hrne
        · have hb : mur p z ≤ mur p r := mur_mono p (by omega)
          have h2 : ¬ mur p r < mur p z := by omega
          rw [if_neg hr, if_neg h2]
      · have ho1 : 10 + (emap p gs).length ≤ mur p z := by rw [hmur]; omega
        have ho2 : 10 + gs.length ≤ z := by omega
        rw [val_beyond _ _ _ ho1, val_beyond _ _ _ ho2]
    · have hmur : mur p z = z - 1 := by simp [mur, hcase]
      by_cases hzlen : z < 10 + gs.length
      · have hk : z - 10 < gs.length := by omega
        have hne : z - 10 ≠ p := by intro h; exact hz (by omega)
        have hlt : mur p z < 10 + (emap p gs).length := by rw [hmur]; omega
        rw [val_gate? (emap p gs) x (mur p z) (by omega) hlt, val_gate? gs x z hge hzlen]
        have h1 : (emap p gs)[mur p z - 10]? = (gs[z - 10]?).map (mg p) := by
          rw [show mur p z - 10 = (if z - 10 < p then z - 10 else z - 10 - 1) from by
            rw [hmur, if_neg (by omega)]; omega]
          exact emap_getElem? p (z - 10) gs hne
        rw [h1, List.getElem?_eq_getElem hk]
        simp only [Option.map_some, Option.getD_some, mg, List.map_map, Function.comp_def]
        congr 1
        apply List.map_congr_left
        intro r hrin
        have hrne : r ≠ 10 + p := by
          intro h; exact hdead (z - 10) hk hne (h ▸ hrin)
        by_cases hr : r < z
        · have h2 : mur p r < mur p z := by
            rw [hmur]
            by_cases h : r < 10 + p
            · simp [mur, h]; omega
            · simp [mur, h]; omega
          rw [if_pos hr, if_pos h2]
          exact ih r (by omega) hrne
        · have hb : mur p z ≤ mur p r := mur_mono p (by omega)
          have h2 : ¬ mur p r < mur p z := by omega
          rw [if_neg hr, if_neg h2]
      · have ho1 : 10 + (emap p gs).length ≤ mur p z := by rw [hmur]; omega
        have ho2 : 10 + gs.length ≤ z := by omega
        rw [val_beyond _ _ _ ho1, val_beyond _ _ _ ho2]

-- status of a wire during the pruning pass: a constant, or the new wire that carries it
inductive St where
  | cst (b : Bool)
  | nrm (j : ℕ)

def St.j : St → ℕ
  | .nrm j => j
  | .cst _ => 0

def St.c : St → Option Bool
  | .cst b => some b
  | .nrm _ => none

structure PSt where
  st : List St
  gs : List Gate
  sv : ℕ

-- one pruning step at the gate g, input t fixed to false
def pst (s : PSt) (g : Gate) : PSt :=
  let a := s.st.getD (g.inputs.getD 0 0) (.nrm 0)
  let b := s.st.getD (g.inputs.getD 1 0) (.nrm 0)
  let rd := fun i => (s.st.getD i (.nrm i)).j
  match g.op, g.inputs.length with
  | .and, 0 => { s with st := s.st ++ [.cst true], sv := s.sv + 1 }
  | .and, 1 => { s with st := s.st ++ [a], sv := s.sv + 1 }
  | .and, _ =>
      match a.c, b.c with
      | some false, _ => { s with st := s.st ++ [.cst false], sv := s.sv + 1 }
      | _, some false => { s with st := s.st ++ [.cst false], sv := s.sv + 1 }
      | some true, _ => { s with st := s.st ++ [b], sv := s.sv + 1 }
      | _, some true => { s with st := s.st ++ [a], sv := s.sv + 1 }
      | none, none =>
          { s with
            st := s.st ++ [.nrm (10 + s.gs.length)]
            gs := s.gs ++ [Gate.mk .and [a.j, b.j]] }
  | .or, 0 => { s with st := s.st ++ [.cst false], sv := s.sv + 1 }
  | .or, 1 => { s with st := s.st ++ [a], sv := s.sv + 1 }
  | .or, _ =>
      match a.c, b.c with
      | some true, _ => { s with st := s.st ++ [.cst true], sv := s.sv + 1 }
      | _, some true => { s with st := s.st ++ [.cst true], sv := s.sv + 1 }
      | some false, _ => { s with st := s.st ++ [b], sv := s.sv + 1 }
      | _, some false => { s with st := s.st ++ [a], sv := s.sv + 1 }
      | none, none =>
          { s with
            st := s.st ++ [.nrm (10 + s.gs.length)]
            gs := s.gs ++ [Gate.mk .or [a.j, b.j]] }
  | .not, 0 => { s with st := s.st ++ [.cst true], sv := s.sv + 1 }
  | .not, _ =>
      match a.c with
      | some true => { s with st := s.st ++ [.cst false], sv := s.sv + 1 }
      | some false => { s with st := s.st ++ [.cst true], sv := s.sv + 1 }
      | none =>
          { s with
            st := s.st ++ [.nrm (10 + s.gs.length)]
            gs := s.gs ++ [Gate.mk .not ([a.j] ++ (g.inputs.drop 1).map rd)] }
  | _, _ =>
      { s with
        st := s.st ++ [.nrm (10 + s.gs.length)]
        gs := s.gs ++ [Gate.mk g.op (g.inputs.map rd)] }

def pinit (t : ℕ) : PSt :=
  { st := List.ofFn (fun i : Fin 10 => if (i : ℕ) = t then .cst false else .nrm (i : ℕ)),
    gs := [], sv := 0 }

def prune (t : ℕ) (gs : List Gate) : PSt := gs.foldl pst (pinit t)
