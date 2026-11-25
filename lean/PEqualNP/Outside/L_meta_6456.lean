import Mathlib
import PEqualNP.Defs

/- The first helper lemmas below are the ones of our earlier file L_meta_5474.lean. -/
namespace PEqualNP.Outside.L_meta_6456

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One evaluation step of the root model: append the value of the next gate.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (stepWire w g).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false)
      else false := by
  unfold stepWire
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepWire w g) (by simp [stepWire]; omega), step_getD, if_pos hi]

lemma main (C : Circuit) (l : List ℕ) (x y : Fin 26 → Bool) (hne : l ≠ []) (hlen : l.length ≤ 2)
    (hdisj : ∀ i : Fin 26, x i = false ∨ y i = false)
    (hboth : ∀ z ∈ [x, y], GateOp.and.eval
      (List.map (fun k : ℕ => (C.wires (List.ofFn z)).getD k false) l) = true) :
    ∃ (a b : Fin C.size), a ≤ b ∧ ∀ z : Fin 26 → Bool,
      GateOp.and.eval (List.map (fun k : ℕ => (C.wires (List.ofFn z)).getD k false) l) =
        ((C.wires (List.ofFn z)).getD (26 + a.val) false &&
          (C.wires (List.ofFn z)).getD (26 + b.val) false) := by
  have hw : ∀ z : Fin 26 → Bool,
      C.wires (List.ofFn z) = C.gates.foldl stepWire (List.ofFn z) := fun _ => rfl
  have hidx : ∀ i ∈ l, ∃ j : Fin C.size, i = 26 + j.val := by
    intro i hi
    have hx := hboth x (by simp)
    have hy := hboth y (by simp)
    rw [show ∀ L : List Bool, GateOp.and.eval L = L.all id from fun _ => rfl,
      List.all_eq_true] at hx hy
    have hxi : (C.wires (List.ofFn x)).getD i false = true :=
      hx _ (List.mem_map_of_mem hi)
    have hyi : (C.wires (List.ofFn y)).getD i false = true :=
      hy _ (List.mem_map_of_mem hi)
    by_cases h1 : i < 26
    · exfalso
      rw [hw, foldl_getD_lt _ _ _ (by simpa using h1),
        List.getD_eq_getElem _ _ (by simpa using h1), List.getElem_ofFn] at hxi hyi
      rcases hdisj ⟨i, h1⟩ with h | h
      · rw [h] at hxi
        exact Bool.noConfusion hxi
      · rw [h] at hyi
        exact Bool.noConfusion hyi
    · by_cases h2 : i < 26 + C.size
      · exact ⟨⟨i - 26, by omega⟩, by simp only []; omega⟩
      · exfalso
        rw [List.getD_eq_default _ _ (by
          rw [hw, foldl_len]
          simp only [List.length_ofFn]
          unfold Circuit.size at h2
          omega)] at hxi
        exact Bool.noConfusion hxi
  match l, hne, hlen, hidx with
  | [i], _, _, hidx =>
    obtain ⟨j, rfl⟩ := hidx i (by simp)
    exact ⟨j, j, le_rfl, fun z => by simp [GateOp.eval]⟩
  | [i, k], _, _, hidx =>
    obtain ⟨j, rfl⟩ := hidx i (by simp)
    obtain ⟨j', rfl⟩ := hidx k (by simp)
    rcases le_total j j' with h | h
    · exact ⟨j, j', h, fun z => by simp [GateOp.eval]⟩
    · exact ⟨j', j, h, fun z => by simp [GateOp.eval, Bool.and_comm]⟩
  | [], h, _, _ => exact absurd rfl h
  | _ :: _ :: _ :: _, _, h, _ => exact absurd h (by simp)

end PEqualNP.Outside.L_meta_6456

theorem PEqualNP.Outside.L_meta_6456 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ) (x3 x4 : Fin (26 : ℕ) → Bool), x2 ≠ [] → x2.length ≤ (2 : ℕ) → (∀ (x7 : Fin (26 : ℕ)), x3 x7 = Bool.false ∨ x4 x7 = Bool.false) → (∀ x8 ∈ [x3, x4], PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x10 : ℕ) => (x1.wires (List.ofFn x8)).getD x10 Bool.false) x2) = Bool.true) → ∃ (x9 : Fin x1.size) (x10 : Fin x1.size), x9 ≤ x10 ∧ ∀ (x11 : Fin (26 : ℕ) → Bool), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x12 : ℕ) => (x1.wires (List.ofFn x11)).getD x12 Bool.false) x2) = ((x1.wires (List.ofFn x11)).getD ((26 : ℕ) + ↑x9) Bool.false && (x1.wires (List.ofFn x11)).getD ((26 : ℕ) + ↑x10) Bool.false) := by
  intro C l x y hne hlen hdisj hboth
  exact PEqualNP.Outside.L_meta_6456.main C l x y hne hlen hdisj hboth
