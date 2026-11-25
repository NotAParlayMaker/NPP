import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_8279

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def fin89 (x : ℕ) : Fin 89 := ⟨x % 89, Nat.mod_lt _ (by norm_num)⟩

def enc (g : Gate) : Bool × Fin 89 × Fin 89 :=
  (isAnd g.op, fin89 (min (g.inputs.getD 0 0) (g.inputs.getD 1 0)),
    fin89 (max (g.inputs.getD 0 0) (g.inputs.getD 1 0)))

def stepE (x5 : List Bool) (x6 : Bool × Fin 89 × Fin 89) : List Bool :=
  x5 ++ [bif x6.1 then x5.getD (↑x6.2.1) Bool.false && x5.getD (↑x6.2.2) Bool.false else x5.getD (↑x6.2.1) Bool.false || x5.getD (↑x6.2.2) Bool.false]

def Good (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a < 89 ∧ b < 89

theorem step_eq (g : Gate) (hg : Good g) (w : List Bool) :
    stepE w (enc g) = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hg
  have ha' : a % 89 = a := Nat.mod_eq_of_lt ha
  have hb' : b % 89 = b := Nat.mod_eq_of_lt hb
  rcases le_total a b with h | h <;> rcases hop with ho | ho <;>
    simp [stepE, enc, isAnd, fin89, hin, ho, GateOp.eval, ha', hb', min_eq_left h, max_eq_right h,
      min_eq_right h, max_eq_left h, Bool.and_comm, Bool.or_comm]

theorem fold_eq (gs : List Gate) (hg : ∀ g ∈ gs, Good g) (w : List Bool) :
    List.foldl stepE w (gs.map enc)
      = List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w gs := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [step_eq g (hg g (by simp)) w]
    exact ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) _

theorem ofFn_eq (gs : List Gate) (hlen : gs.length = 63) :
    List.ofFn (fun i : Fin 63 => ((enc (gs.getD i ⟨GateOp.or, []⟩)).1,
      (enc (gs.getD i ⟨GateOp.or, []⟩)).2.1, (enc (gs.getD i ⟨GateOp.or, []⟩)).2.2))
      = gs.map enc := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    have h3 : i < gs.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h3, Option.getD_some]

theorem main : ∀ (C : Circuit), PEqualNP.TopForm.IsAO2 26 C → C.size = 63 → C.output = 88 →
    ∃ (x6 : Fin 63 → Bool) (x7 : Fin 63 → Fin 89) (x8 : Fin 63 → Fin 89),
      (∀ (x9 : Fin 63), (x7 x9 : ℕ) < 26 + (x9 : ℕ) ∧ (x8 x9 : ℕ) < 26 + (x9 : ℕ) ∧ x7 x9 ≤ x8 x9) ∧
      ∀ (x9 : Fin 26 → Bool),
        (List.foldl stepE (List.ofFn x9)
          (List.ofFn fun (x5 : Fin 63) => (x6 x5, x7 x5, x8 x5))).getD 88 Bool.false
          = PEqualNP.MetaComplexity.circuitFun 26 C x9 := by
  intro C h hs ho
  obtain ⟨hao, hrb, hl2⟩ := h
  have hlen : C.gates.length = 63 := hs
  have key : ∀ i, i < 63 → ((C.gates.getD i ⟨GateOp.or, []⟩) ∈ C.gates) ∧
      ∃ a b, (C.gates.getD i ⟨GateOp.or, []⟩).inputs = [a, b] ∧ a < 26 + i ∧ b < 26 + i := by
    intro i hi
    have hi' : i < C.gates.length := by omega
    have e : (C.gates.getD i ⟨GateOp.or, []⟩) = C.gates[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      rfl
    have hmem : (C.gates.getD i ⟨GateOp.or, []⟩) ∈ C.gates := by
      rw [e]
      exact List.getElem_mem hi'
    refine ⟨hmem, ?_⟩
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (hl2 _ hmem)
    have hr : ∀ x ∈ (C.gates.getD i ⟨GateOp.or, []⟩).inputs, x < 26 + i := hrb i hi'
    rw [hab] at hr
    exact ⟨a, b, hab, hr a (by simp), hr b (by simp)⟩
  have hgood : ∀ g ∈ C.gates, Good g := by
    intro g hg
    obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
    obtain ⟨hmem, a, b, hab, ha, hb⟩ := key i (by omega)
    have e : (C.gates.getD i ⟨GateOp.or, []⟩) = g := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, ← hgi]
      rfl
    rw [e] at hab
    exact ⟨hao g hg, a, b, hab, by omega, by omega⟩
  refine ⟨fun i => (enc (C.gates.getD i ⟨GateOp.or, []⟩)).1, fun i => (enc (C.gates.getD i ⟨GateOp.or, []⟩)).2.1, fun i => (enc (C.gates.getD i ⟨GateOp.or, []⟩)).2.2, ?_, ?_⟩
  · intro i
    obtain ⟨hmem, a, b, hab, ha, hb⟩ := key i i.2
    have hi := i.2
    have ha' : a % 89 = a := Nat.mod_eq_of_lt (by omega)
    have hb' : b % 89 = b := Nat.mod_eq_of_lt (by omega)
    simp only [enc, fin89, hab]
    rcases le_total a b with hle | hle <;>
      simp [Fin.le_def, ha', hb', min_eq_left hle, max_eq_right hle,
        min_eq_right hle, max_eq_left hle] <;> omega
  · intro x9
    have e := ofFn_eq C.gates hlen
    show (List.foldl stepE (List.ofFn x9) (List.ofFn fun i : Fin 63 =>
      ((enc (C.gates.getD i ⟨GateOp.or, []⟩)).1, (enc (C.gates.getD i ⟨GateOp.or, []⟩)).2.1, (enc (C.gates.getD i ⟨GateOp.or, []⟩)).2.2))).getD 88 false = _
    rw [e, fold_eq C.gates hgood]
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires, ho]

end PEqualNP.Outside.L_meta_8279

theorem PEqualNP.Outside.L_meta_8279 : have x1 : (Fin (63 : ℕ) → Bool) → (Fin (63 : ℕ) → Fin (89 : ℕ)) → (Fin (63 : ℕ) → Fin (89 : ℕ)) → (Fin (26 : ℕ) → Bool) → Bool := fun (x1 : Fin (63 : ℕ) → Bool) (x2 x3 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x4 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x5 : List Bool) (x6 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x5 ++ [bif x6.1 then x5.getD (↑x6.2.1) Bool.false && x5.getD (↑x6.2.2) Bool.false else x5.getD (↑x6.2.1) Bool.false || x5.getD (↑x6.2.2) Bool.false]) (List.ofFn x4) (List.ofFn fun (x5 : Fin (63 : ℕ)) => (x1 x5, x2 x5, x3 x5))).getD (88 : ℕ) Bool.false; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → x2.size = (63 : ℕ) → x2.output = (88 : ℕ) → ∃ (x6 : Fin (63 : ℕ) → Bool) (x7 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x8 : Fin (63 : ℕ) → Fin (89 : ℕ)), (∀ (x9 : Fin (63 : ℕ)), ↑(x7 x9) < (26 : ℕ) + ↑x9 ∧ ↑(x8 x9) < (26 : ℕ) + ↑x9 ∧ x7 x9 ≤ x8 x9) ∧ ∀ (x9 : Fin (26 : ℕ) → Bool), x1 x6 x7 x8 x9 = PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x9 :=
  PEqualNP.Outside.L_meta_8279.main
