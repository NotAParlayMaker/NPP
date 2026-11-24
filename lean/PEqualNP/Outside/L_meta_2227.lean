import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2227

open PEqualNP.CircuitLowerBounds

def fd {α : Type} (f : Gate → List α → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun w g => w ++ [f g w]) init

theorem fd_snoc {α : Type} (f : Gate → List α → α) (init : List α) (gs : List Gate) (g : Gate) :
    fd f init (gs ++ [g]) = fd f init gs ++ [f g (fd f init gs)] := by
  simp [fd, List.foldl_append]

theorem fd_spec {α : Type} (f : Gate → List α → α) (init : List α) (gs : List Gate) :
    (fd f init gs).length = init.length + gs.length ∧
    (∀ i, i < init.length → (fd f init gs)[i]? = init[i]?) ∧
    (∀ j g, gs[j]? = some g →
      (fd f init gs)[init.length + j]? = some (f g ((fd f init gs).take (init.length + j)))) := by
  induction gs using List.reverseRecOn with
  | nil => simp [fd]
  | append_singleton gs g ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [fd_snoc]
    refine ⟨by simp [h1]; omega, ?_, ?_⟩
    · intro i hi
      rw [List.getElem?_append_left (by omega)]
      exact h2 i hi
    · intro j g' hj
      by_cases hjl : j < gs.length
      · rw [List.getElem?_append_left hjl] at hj
        rw [List.getElem?_append_left (by omega), List.take_append_of_le_length (by omega)]
        exact h3 j g' hj
      · have hlt : j < (gs ++ [g]).length := (List.getElem?_eq_some_iff.1 hj).1
        have hj2 : j = gs.length := by
          simp at hlt
          omega
        subst hj2
        simp at hj
        subst hj
        have e : init.length + gs.length = (fd f init gs).length := h1.symm
        rw [e]
        simp

theorem getD_take {α : Type} (l : List α) (n i : ℕ) (d : α) (h : i < n) :
    (l.take n).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

def evf (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def ldf (g : Gate) (d : List ℕ) : ℕ := g.lineDegree d

theorem wires_eq (C : Circuit) (X : List Bool) : C.wires X = fd evf X C.gates := rfl

theorem ld_eq (C : Circuit) (n : ℕ) (M : Finset ℕ) :
    C.lineDegrees n M = fd ldf ((List.range n).map fun i => if i ∈ M then 1 else 0) C.gates := rfl

theorem val_at (C : Circuit) (X : List Bool) (n : ℕ) (hn : X.length = n) (j : ℕ) (g : Gate)
    (a b : ℕ) (hg : C.gates[j]? = some g) (hin : g.inputs = [a, b]) (ha : a < n + j)
    (hb : b < n + j) :
    (C.wires X).getD (n + j) false
      = g.op.eval [(C.wires X).getD a false, (C.wires X).getD b false] := by
  subst hn
  have s := (fd_spec evf X C.gates).2.2 j g hg
  rw [wires_eq, List.getD_eq_getElem?_getD, s]
  show g.op.eval (g.inputs.map fun i =>
    (List.take (X.length + j) (fd evf X C.gates)).getD i false) = _
  rw [hin]
  simp only [List.map_cons, List.map_nil]
  rw [getD_take _ _ _ _ ha, getD_take _ _ _ _ hb]

theorem deg_at (C : Circuit) (n : ℕ) (M : Finset ℕ) (j : ℕ) (g : Gate)
    (a b : ℕ) (hg : C.gates[j]? = some g) (hin : g.inputs = [a, b]) (ha : a < n + j)
    (hb : b < n + j) :
    (g.op = GateOp.and → (C.lineDegrees n M).getD (n + j) 0
      = (C.lineDegrees n M).getD a 0 + (C.lineDegrees n M).getD b 0) ∧
    (g.op = GateOp.or → (C.lineDegrees n M).getD (n + j) 0
      = max ((C.lineDegrees n M).getD a 0) ((C.lineDegrees n M).getD b 0)) := by
  have hl : ((List.range n).map fun i => if i ∈ M then 1 else 0).length = n := by simp
  have s := (fd_spec ldf ((List.range n).map fun i => if i ∈ M then 1 else 0) C.gates).2.2 j g hg
  rw [hl] at s
  rw [ld_eq, List.getD_eq_getElem?_getD, s]
  obtain ⟨op, ins⟩ := g
  simp only at hin
  subst hin
  constructor
  · intro h
    simp only at h
    subst h
    simp [ldf, Gate.lineDegree, List.getD_eq_getElem?_getD, List.getElem?_take, ha, hb]
  · intro h
    simp only at h
    subst h
    simp [ldf, Gate.lineDegree, List.getD_eq_getElem?_getD, List.getElem?_take, ha, hb]

theorem band (va vb ta tb va' vb' : Bool) (da db : ℕ)
    (ia : (da ≤ 1 → va' = (va || ta)) ∧ (da = 0 → ta = false))
    (ib : (db ≤ 1 → vb' = (vb || tb)) ∧ (db = 0 → tb = false)) :
    (da + db ≤ 1 → (va' && vb') = ((va && vb) || (va && tb || ta && vb))) ∧
    (da + db = 0 → (va && tb || ta && vb) = false) := by
  constructor
  · intro h
    have h1 := ia.1 (by omega)
    have h2 := ib.1 (by omega)
    subst h1
    subst h2
    rcases Nat.eq_zero_or_pos da with h0 | h0
    · have h3 := ia.2 h0
      subst h3
      cases va <;> cases vb <;> cases tb <;> rfl
    · have h3 := ib.2 (by omega)
      subst h3
      cases va <;> cases vb <;> cases ta <;> rfl
  · intro h
    have h3 := ia.2 (by omega)
    have h4 := ib.2 (by omega)
    subst h3
    subst h4
    cases va <;> cases vb <;> rfl

theorem bor (va vb ta tb va' vb' : Bool) (da db : ℕ)
    (ia : (da ≤ 1 → va' = (va || ta)) ∧ (da = 0 → ta = false))
    (ib : (db ≤ 1 → vb' = (vb || tb)) ∧ (db = 0 → tb = false)) :
    (max da db ≤ 1 → (va' || vb') = ((va || vb) || (ta || tb))) ∧
    (max da db = 0 → (ta || tb) = false) := by
  constructor
  · intro h
    have h1 := ia.1 (le_trans (le_max_left _ _) h)
    have h2 := ib.1 (le_trans (le_max_right _ _) h)
    subst h1
    subst h2
    cases va <;> cases vb <;> cases ta <;> cases tb <;> rfl
  · intro h
    have h3 := ia.2 (Nat.le_zero.1 (le_trans (le_max_left _ _) (le_of_eq h)))
    have h4 := ib.2 (Nat.le_zero.1 (le_trans (le_max_right _ _) (le_of_eq h)))
    subst h3
    subst h4
    rfl

theorem ev_and (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by simp [GateOp.eval]

theorem ev_or (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by simp [GateOp.eval]

theorem ofFn_get {α : Type} {n : ℕ} (f : Fin n → α) (w : ℕ) (h : w < n) :
    (List.ofFn f)[w]? = some (f ⟨w, h⟩) := by
  simp [h]

theorem range_get {α : Type} {n : ℕ} (f : ℕ → α) (w : ℕ) (h : w < n) :
    ((List.range n).map f)[w]? = some (f w) := by
  simp [h]

theorem ifp {α : Type} (c : Prop) [Decidable c] (a b : α) (h : c) :
    (if c then a else b) = a := by
  simp [h]

theorem ifn {α : Type} (c : Prop) [Decidable c] (a b : α) (h : ¬ c) :
    (if c then a else b) = b := by
  simp [h]

theorem main (C : Circuit) (v : Fin 14) (x : Fin 14 → Bool) (t : ℕ → Bool)
    (H : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j)
    (T0 : ∀ (i : Fin 14), t ↑i = decide (v = i))
    (T : ∀ (j : ℕ) (g : Gate) (a b : ℕ), C.gates[j]? = some g → g.inputs = [a, b] →
      (g.op = GateOp.and → t (14 + j) = ((C.wires (List.ofFn x)).getD a false && t b
        || t a && (C.wires (List.ofFn x)).getD b false)) ∧
      (g.op = GateOp.or → t (14 + j) = (t a || t b))) :
    ∀ w, w < 14 + C.gates.length →
      (((C.lineDegrees 14 {↑v}).getD w 0 ≤ 1 →
        (C.wires (List.ofFn fun i => if v = i then true else x i)).getD w false
          = ((C.wires (List.ofFn x)).getD w false || t w)) ∧
       ((C.lineDegrees 14 {↑v}).getD w 0 = 0 → t w = false)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h14 : w < 14
    · have hV : (C.wires (List.ofFn x)).getD w false = x ⟨w, h14⟩ := by
        rw [wires_eq, List.getD_eq_getElem?_getD,
          (fd_spec evf (List.ofFn x) C.gates).2.1 w (by simpa using h14), ofFn_get _ w h14]
        rfl
      have hV2 : (C.wires (List.ofFn fun i => if v = i then true else x i)).getD w false
          = if v = ⟨w, h14⟩ then true else x ⟨w, h14⟩ := by
        rw [wires_eq, List.getD_eq_getElem?_getD,
          (fd_spec evf (List.ofFn fun i => if v = i then true else x i) C.gates).2.1 w
            (by simpa using h14), ofFn_get _ w h14]
        rfl
      have hD : (C.lineDegrees 14 {↑v}).getD w 0 = if w = ↑v then 1 else 0 := by
        rw [ld_eq, List.getD_eq_getElem?_getD,
          (fd_spec ldf _ C.gates).2.1 w (by simpa using h14), range_get _ w h14]
        simp
      have hT : t w = decide (v = ⟨w, h14⟩) := T0 ⟨w, h14⟩
      rw [hV, hV2, hD, hT]
      by_cases e : v = ⟨w, h14⟩
      · have e2 : w = ↑v := by rw [e]
        rw [ifp _ _ _ e2, ifp _ _ _ e]
        refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
        simp [e]
      · have e2 : ¬ w = ↑v := fun h' => e (Fin.ext h'.symm)
        rw [ifn _ _ _ e2, ifn _ _ _ e]
        exact ⟨fun _ => by simp [e], fun _ => by simp [e]⟩
    · obtain ⟨j, rfl⟩ : ∃ j, w = 14 + j := ⟨w - 14, by omega⟩
      have hj : j < C.gates.length := by omega
      have hg : C.gates[j]? = some (C.gates[j]) := List.getElem?_eq_getElem hj
      obtain ⟨hop, a, b, hin, -, ha, hb⟩ := H j _ hg
      have hV := val_at C (List.ofFn x) 14 (by simp) j _ a b hg hin ha hb
      have hV' := val_at C (List.ofFn fun i => if v = i then true else x i) 14 (by simp)
        j _ a b hg hin ha hb
      have hD := deg_at C 14 {↑v} j _ a b hg hin ha hb
      have hT := T j _ a b hg hin
      have ia := ih a (by omega) (by omega)
      have ib := ih b (by omega) (by omega)
      rcases hop with hop | hop
      · rw [hV, hV', hD.1 hop, hT.1 hop, hop, ev_and, ev_and]
        exact band _ _ _ _ _ _ _ _ ia ib
      · rw [hV, hV', hD.2 hop, hT.2 hop, hop, ev_or, ev_or]
        exact bor _ _ _ _ _ _ _ _ ia ib

end PEqualNP.Outside.L_meta_2227

theorem PEqualNP.Outside.L_meta_2227 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ)) (x3 : Fin (14 : ℕ) → Bool) (x4 : ℕ → Bool), (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (14 : ℕ) + x5 ∧ x9 < (14 : ℕ) + x5) → (∀ (x6 : Fin (14 : ℕ)), x4 ↑x6 = Decidable.decide (x2 = x6)) → (∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ), x1.gates[x7]? = Option.some x8 → x8.inputs = [x9, x10] → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x4 ((14 : ℕ) + x7) = ((x1.wires (List.ofFn x3)).getD x9 Bool.false && x4 x10 || x4 x9 && (x1.wires (List.ofFn x3)).getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ((14 : ℕ) + x7) = (x4 x9 || x4 x10))) → x1.eval (List.ofFn x3) = Bool.false → x1.eval (List.ofFn fun (x9 : Fin (14 : ℕ)) => if x2 = x9 then Bool.true else x3 x9) = Bool.true → x4 x1.output = Bool.false → (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {↑x2} := by
  intro x1 x2 x3 x4 H T0 T e0 e1 ho
  by_contra hc
  have hc2 : (x1.lineDegrees 14 {↑x2}).getD x1.output 0 ≤ 1 := by
    have hc3 : x1.lineDeg 14 {↑x2} ≤ 1 := by omega
    exact hc3
  have e0' : (x1.wires (List.ofFn x3)).getD x1.output false = false := e0
  have e1' : (x1.wires (List.ofFn fun (x9 : Fin 14) => if x2 = x9 then true else x3 x9)).getD
      x1.output false = true := e1
  by_cases hout : x1.output < 14 + x1.gates.length
  · have m := (PEqualNP.Outside.L_meta_2227.main x1 x2 x3 x4 H T0 T x1.output hout).1 hc2
    rw [e1', e0', ho] at m
    exact absurd m (by decide)
  · have hlen := (PEqualNP.Outside.L_meta_2227.fd_spec PEqualNP.Outside.L_meta_2227.evf
      (List.ofFn fun (x9 : Fin 14) => if x2 = x9 then true else x3 x9) x1.gates).1
    have hle : (x1.wires (List.ofFn fun (x9 : Fin 14) =>
        if x2 = x9 then true else x3 x9)).length ≤ x1.output := by
      rw [PEqualNP.Outside.L_meta_2227.wires_eq, hlen]
      simp
      omega
    rw [List.getD_eq_default _ _ hle] at e1'
    exact absurd e1' (by decide)
