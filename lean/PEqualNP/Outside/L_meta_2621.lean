import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2621_aux

-- The value of the derived wire of a gate, from the values of the derived wires so far.
def val (w : List Bool) (V : List Bool) (g : Gate) : Bool :=
  match g.inputs with
  | [a, b] =>
    match g.op with
    | GateOp.and => (w.getD a false && V.getD b false) || (V.getD a false && w.getD b false)
    | _ => V.getD a false || V.getD b false
  | _ => false

def run (w : List Bool) (gs : List Gate) (V : List Bool) : List Bool :=
  gs.foldl (fun V g => V ++ [val w V g]) V

lemma run_cons (w : List Bool) (g : Gate) (gs : List Gate) (V : List Bool) :
    run w (g :: gs) V = run w gs (V ++ [val w V g]) := rfl

lemma run_append (w : List Bool) (A B : List Gate) (V : List Bool) :
    run w (A ++ B) V = run w B (run w A V) := by
  simp [run, List.foldl_append]

lemma run_length (w : List Bool) (gs : List Gate) (V : List Bool) :
    (run w gs V).length = V.length + gs.length := by
  induction gs generalizing V with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (w : List Bool) (gs : List Gate) (V : List Bool) (i : ℕ) (hi : i < V.length) :
    (run w gs V).getD i false = V.getD i false := by
  induction gs generalizing V with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma run_at (w : List Bool) (gs : List Gate) (V : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run w gs V).getD (V.length + j) false = val w (run w (gs.take j) V) gs[j] := by
  have hl : (run w (gs.take j) V).length = V.length + j := by
    rw [run_length, List.length_take]
    omega
  conv_lhs => rw [← List.take_append_drop j gs, run_append, List.drop_eq_getElem_cons hj, run_cons]
  rw [run_getD _ _ _ _ (by simp only [List.length_append, List.length_singleton]; omega),
    List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self, List.getD_cons_zero]

lemma run_prefix (w : List Bool) (gs : List Gate) (V : List Bool) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < V.length + j) :
    (run w (gs.take j) V).getD i false = (run w gs V).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  rw [run_getD w (gs.drop j) (run w (gs.take j) V) i (by rw [run_length, List.length_take]; omega)]

theorem m21 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → ∀ (x3 : ℕ) (x4 : List Bool), ∃ (x5 : ℕ → Bool), (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = x3)) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x4.getD x8 Bool.false && x5 x9 || x5 x8 && x4.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9)) := by
  intro C hC v w
  obtain ⟨_, hrb, _⟩ := hC
  obtain ⟨V0, hV0⟩ : ∃ V0 : List Bool, V0 = (List.range 26).map (fun i => decide (i = v)) :=
    ⟨_, rfl⟩
  have hl0 : V0.length = 26 := by rw [hV0]; simp
  refine ⟨fun n => (run w C.gates V0).getD n false, ?_, ?_⟩
  · intro i hi
    show (run w C.gates V0).getD i false = decide (i = v)
    rw [run_getD _ _ _ _ (by rw [hl0]; exact hi), hV0,
      List.getD_eq_getElem _ _ (by simp; exact hi)]
    simp
  · intro j g a b hg hin
    obtain ⟨hj, hgj⟩ := List.getElem?_eq_some_iff.mp hg
    have hat := run_at w C.gates V0 j hj
    rw [hl0, hgj] at hat
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      rw [List.getD_eq_getElem _ _ hj, hgj]
    have ha : a < 26 + j := hrb j hj a (by rw [hga, hin]; simp)
    have hb : b < 26 + j := hrb j hj b (by rw [hga, hin]; simp)
    have pa := run_prefix w C.gates V0 j a hj.le (by rw [hl0]; exact ha)
    have pb := run_prefix w C.gates V0 j b hj.le (by rw [hl0]; exact hb)
    constructor
    · intro hop
      show (run w C.gates V0).getD (26 + j) false = _
      rw [hat]
      unfold val
      rw [hin, hop]
      simp only
      rw [pa, pb]
    · intro hop
      show (run w C.gates V0).getD (26 + j) false = _
      rw [hat]
      unfold val
      rw [hin, hop]
      simp only
      rw [pa, pb]

end PEqualNP.Outside.L_meta_2621_aux

theorem PEqualNP.Outside.L_meta_2621 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → ∀ (x3 : ℕ) (x4 : List Bool), ∃ (x5 : ℕ → Bool), (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = x3)) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x4.getD x8 Bool.false && x5 x9 || x5 x8 && x4.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9)) :=
  PEqualNP.Outside.L_meta_2621_aux.m21
