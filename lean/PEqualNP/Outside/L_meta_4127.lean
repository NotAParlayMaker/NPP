import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4127_aux

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

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

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

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
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => hAO g' (by simp [hg'])
    rw [scan_cons, scan_cons, ih hgs]
    simp [boolStep_fst_linStep g hg ws]


lemma gate_ok (C : Circuit)
    (h : ∀ (x2 : ℕ) (x3 : Gate), C.gates[x2]? = Option.some x3 →
      (x3.op = GateOp.and ∨ x3.op = GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ),
        x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < 14 + x2 ∧ x6 < 14 + x2) :
    ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  exact (h j _ (List.getElem?_eq_getElem hj)).1

end PEqualNP.Outside.L_meta_4127_aux

open PEqualNP.Outside.L_meta_4127_aux PEqualNP.ReadK PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4127 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) →     ∀ (x3 : Bool),       ((PEqualNP.ReadK.linearParts x1 (fun (x4 : ℕ) => Decidable.decide (x4 = if x3 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.ofFn fun (x4 : Fin (14 : ℕ)) => Decidable.decide (↑x4 = (0 : ℕ) ∨ ↑x4 = (7 : ℕ)))).getD x1.output (Bool.false, Bool.false)).2 = Bool.false →         ∃ (x5 : ℕ → Bool),           (∀ (x6 : Fin (7 : ℕ)), (x5 ↑x6 = if x3 = Bool.true then Bool.false else Decidable.decide (x6 = (0 : Fin (7 : ℕ)))) ∧ x5 ((7 : ℕ) + ↑x6) = if x3 = Bool.true then Decidable.decide (x6 = (0 : Fin (7 : ℕ))) else Bool.false) ∧             (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                 x1.gates[x6]? = Option.some x7 →                   x7.inputs = [x8, x9] →                     have x12 : List Bool := x1.wires (List.ofFn fun (x12 : Fin (14 : ℕ)) => Decidable.decide (x12 = if x3 = Bool.true then Fin.castAdd (7 : ℕ) (0 : Fin (7 : ℕ)) else Fin.natAdd (7 : ℕ) (0 : Fin (7 : ℕ))));                     (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((14 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((14 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧               x5 x1.output = Bool.false := by
  intro C hC b hout
  set isL : ℕ → Bool := fun (x4 : ℕ) => decide (x4 = if b = true then 7 else 0) with hisL
  set x0 : List Bool := List.ofFn fun (x4 : Fin 14) => decide ((x4 : ℕ) = 0 ∨ (x4 : ℕ) = 7) with hx0
  set ini : List (Bool × Bool) := (x0.zipIdx).map fun (p : Bool × ℕ) => if isL p.2 then (false, p.1) else (p.1, false) with hini
  set y : List Bool := List.ofFn fun (x12 : Fin 14) => decide (x12 = if b = true then Fin.castAdd 7 (0 : Fin 7) else Fin.natAdd 7 (0 : Fin 7)) with hy
  have hLP : linearParts C isL x0 = scan linStep C.gates ini := rfl
  have hinilen : ini.length = 14 := by simp [hini, hx0]
  have hfst : ini.map (·.1) = y := by
    rw [hini, hx0, hy, hisL]; cases b <;> decide
  have hAO := gate_ok C hC
  have hW : ∀ i, (C.wires y).getD i false = ((linearParts C isL x0).getD i (false, false)).1 := by
    intro i
    rw [hLP, ← getD_map_fst, scan_lin_fst _ hAO, hfst]; rfl
  refine ⟨fun i => ((linearParts C isL x0).getD i (false, false)).2, ?_, ?_, hout⟩
  · intro j
    have h1 : (j : ℕ) < ini.length := by omega
    have h2 : 7 + (j : ℕ) < ini.length := by omega
    simp only [hLP]
    rw [scan_prefix _ _ _ _ _ h1, scan_prefix _ _ _ _ _ h2]
    rw [hini, hx0, hisL]
    revert j; cases b <;> decide
  · intro j g a c hg hin
    have hj : j < C.gates.length := by
      by_contra hh; rw [List.getElem?_eq_none (by omega)] at hg; cases hg
    have hgj : C.gates[j] = g := by
      rw [List.getElem?_eq_getElem hj] at hg; exact Option.some.inj hg
    obtain ⟨-, a', c', hin', -, ha, hc⟩ := hC j g hg
    rw [hin] at hin'
    simp only [List.cons.injEq, and_true] at hin'
    obtain ⟨rfl, rfl⟩ := hin'
    have key : (scan linStep C.gates ini).getD (ini.length + j) (false, false) =
        linStep (scan linStep C.gates ini) C.gates[j] := by
      apply scan_gate _ _ _ _ _ hj
      intro p p' hp
      rw [hgj]
      have e1 := hp a (by omega)
      have e2 := hp c (by omega)
      simp only [linStep, hin, List.map_cons, List.map_nil, e1, e2]
    rw [hinilen, hgj] at key
    simp only [hW]
    rw [← hLP] at key
    constructor
    · intro hop
      show ((linearParts C isL x0).getD (14 + j) (false, false)).2 = _
      rw [key]
      simp only [linStep, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      cases ((linearParts C isL x0).getD a (false, false)).1 <;>
        cases ((linearParts C isL x0).getD a (false, false)).2 <;> simp
    · intro hop
      show ((linearParts C isL x0).getD (14 + j) (false, false)).2 = _
      rw [key]
      simp [linStep, hop, hin]
