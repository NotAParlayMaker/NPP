import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4025

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma getD_map_fst (ws : List (Bool × Bool)) (i : ℕ) :
    (ws.map (·.1)).getD i false = (ws.getD i (false, false)).1 := by
  by_cases hi : i < ws.length
  · simp [hi]
  · have hle : ws.length ≤ i := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hle)]

lemma boolStep_fst_linStep (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (ws : List (Bool × Bool)) :
    (linStep ws g).1 = boolStep (ws.map (·.1)) g := by
  rcases hg with hop | hop
  · simp only [linStep, boolStep, hop, GateOp.eval]
    have hfold : ∀ (l : List (Bool × Bool)) (b c : Bool),
        (l.foldl (fun (acc : Bool × Bool) p =>
          (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (b, c)).1 =
        (b && l.all (·.1)) := by
      intro l
      induction l with
      | nil => intro b c; simp
      | cons x xs ih =>
        intro b c
        simp only [List.foldl_cons, List.all_cons]
        rw [ih, Bool.and_assoc]
    rw [hfold, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi; rw [getD_map_fst]; exact h i hi
    · intro h i hi; rw [← getD_map_fst]; exact h i hi
  · simp only [linStep, boolStep, hop, GateOp.eval]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro ⟨i, hi, hit⟩; exact ⟨i, hi, by rw [getD_map_fst]; exact hit⟩
    · intro ⟨i, hi, hit⟩; exact ⟨i, hi, by rw [← getD_map_fst]; exact hit⟩

lemma scan_lin_fst (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ws : List (Bool × Bool)) :
    (scan linStep gs ws).map (·.1) = scan boolStep gs (ws.map (·.1)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hAO g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or :=
      fun g' hg' => hAO g' (by simp [hg'])
    rw [scan_cons, scan_cons, ih hgs]
    simp [boolStep_fst_linStep g hg ws]

def init (n a b : ℕ) : List (Bool × Bool) :=
  (((List.range n).map fun i => i == a || i == b).zipIdx).map
    fun (c, i) => if decide (i = a) then (false, c) else (c, false)

lemma init_length (n a b : ℕ) : (init n a b).length = n := by
  simp [init]

lemma init_fst (n a b : ℕ) (hab : a ≠ b) :
    (init n a b).map (·.1) = List.ofFn fun i : Fin n => decide (i.val = b) := by
  apply List.ext_getElem
  · simp [init_length]
  · intro i h1 h2
    simp only [init, List.getElem_map, List.getElem_zipIdx, List.getElem_range, List.getElem_ofFn]
    by_cases hia : i = a
    · subst hia
      simp [hab]
    · by_cases hib : i = b <;> simp [hia, hib, Ne.symm hab]

lemma lin_fst (n a b : ℕ) (hab : a ≠ b) (C : Circuit) (hAO : AndOrOnly C) (w : ℕ) :
    ((linearParts C (fun i => decide (i = a)) ((List.range n).map fun i => i == a || i == b)).getD
      w (false, false)).1 =
    (C.wires (List.ofFn fun i : Fin n => decide (i.val = b))).getD w false := by
  change ((scan linStep C.gates (init n a b)).getD w (false, false)).1 =
    (scan boolStep C.gates (List.ofFn fun i : Fin n => decide (i.val = b))).getD w false
  rw [← getD_map_fst, scan_lin_fst C.gates hAO, init_fst n a b hab]

lemma lin_gate (n a b : ℕ) (C : Circuit) (hAO2 : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    (linearParts C (fun i => decide (i = a)) ((List.range n).map fun i => i == a || i == b)).getD
      (n + j) (false, false) =
    linStep (linearParts C (fun i => decide (i = a))
      ((List.range n).map fun i => i == a || i == b)) C.gates[j] := by
  change (scan linStep C.gates (init n a b)).getD (n + j) (false, false) =
    linStep (scan linStep C.gates (init n a b)) C.gates[j]
  have hlen := init_length n a b
  rw [show n + j = (init n a b).length + j by rw [hlen]]
  apply scan_gate linStep C.gates (init n a b) (false, false) j hj
  intro q1 q2 hq
  simp only [linStep]
  have hrb := hAO2.2.1 j hj
  have hg : gateAt C j = C.gates[j] := by simp [gateAt, hj]
  have hcongr : C.gates[j].inputs.map (fun i => q1.getD i (false, false)) =
      C.gates[j].inputs.map (fun i => q2.getD i (false, false)) := by
    apply List.map_congr_left
    intro i hi
    apply hq
    rw [hlen]
    exact hrb i (by rw [hg]; exact hi)
  rw [hcongr]

end PEqualNP.Outside.L_meta_4025


theorem PEqualNP.Outside.L_meta_4025 : ∀ (x1 x2 x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x2 < x1 →     x3 < x1 →       x2 ≠ x3 →         PEqualNP.TopForm.IsAO2 x1 x4 →           have x9 : List (Bool × Bool) := PEqualNP.ReadK.linearParts x4 (fun (x9 : ℕ) => Decidable.decide (x9 = x2)) (List.map (fun (x9 : ℕ) => x9 == x2 || x9 == x3) (List.range x1));           have x10 : ℕ → Bool := fun (x10 : ℕ) => (x9.getD x10 (Bool.false, Bool.false)).2;           have x11 : List Bool := x4.wires (List.ofFn fun (x11 : Fin x1) => Decidable.decide (↑x11 = x3));           ∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 x15 : ℕ), x4.gates[x12]? = Option.some x13 → x13.inputs = [x14, x15] → (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and → x10 (x1 + x12) = (x11.getD x14 Bool.false && x10 x15 || x10 x14 && x11.getD x15 Bool.false)) ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10 (x1 + x12) = (x10 x14 || x10 x15)) := by
  intro x1 x2 x3 C _ _ hne hAO
  dsimp only
  intro k g a b hk hin
  have hj : k < C.gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hk
    cases hk
  have hgk : C.gates[k] = g := by
    rw [List.getElem?_eq_getElem hj] at hk
    exact Option.some.inj hk
  have hgate := L_meta_4025.lin_gate x1 x2 x3 C hAO k hj
  rw [hgk] at hgate
  constructor
  · intro hop
    rw [hgate]
    simp only [L_meta_4025.linStep, hop, hin, List.map_cons, List.map_nil, List.foldl_cons,
      List.foldl_nil, Bool.true_and, Bool.false_and, Bool.or_false]
    rw [← L_meta_4025.lin_fst x1 x2 x3 hne C hAO.1 a, ← L_meta_4025.lin_fst x1 x2 x3 hne C hAO.1 b]
  · intro hop
    rw [hgate]
    simp [L_meta_4025.linStep, hop, hin]
