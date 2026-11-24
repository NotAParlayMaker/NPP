import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2754Aux

open PEqualNP.CircuitLowerBounds

def edge : (Fin 9 → Bool) → Bool := fun x =>
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
  x 6 && x 8 || x 8 && x 5

lemma edge_ne_proj (i : Fin 9) : edge ≠ fun x => x i := by
  decide +kernel +revert

lemma edge_ne_not_proj (i : Fin 9) : edge ≠ fun x => !(x i) := by
  decide +kernel +revert

lemma edge_ne_or : edge ≠ fun x : Fin 9 → Bool => x 0 || x 4 := by
  decide +kernel

lemma edge_ne_not_or : edge ≠ fun x : Fin 9 → Bool => !(x 0 || x 4) := by
  decide +kernel

lemma edge_ne_true : edge ≠ fun _ : Fin 9 → Bool => true := by
  decide +kernel

lemma edge_ne_false : edge ≠ fun _ : Fin 9 → Bool => false := by
  decide +kernel

lemma input_getD (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i false = x i := by
  decide +kernel +revert

lemma prefix_getD_lt (x : Fin 9 → Bool) (tail : List Bool) (i : Fin 9) :
    (List.ofFn x ++ tail).getD i false = x i := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simpa only [List.length_ofFn] using i.isLt),
    List.getElem?_eq_getElem i.isLt]
  simpa [List.getD_eq_getElem?_getD] using input_getD x i

lemma prefix_getD_nine (x : Fin 9 → Bool) (v w : Bool) :
    (List.ofFn x ++ [v, w]).getD 9 false = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

lemma prefix_getD_ten (x : Fin 9 → Bool) (v w : Bool) :
    (List.ofFn x ++ [v, w]).getD 10 false = w := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

lemma prefix_getD_gt (x : Fin 9 → Bool) (v w : Bool) (a : ℕ) (ha : 10 < a) :
    (List.ofFn x ++ [v, w]).getD a false = false := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp only [List.length_ofFn]; omega),
    List.getElem?_eq_none (by simp only [List.length_ofFn, List.length_cons, List.length_nil]; omega)]
  rfl

lemma input_append_getD_nine (x : Fin 9 → Bool) (v : Bool) :
    (List.ofFn x ++ [v]).getD 9 false = v := by
  simp

lemma input_append_getD_gt (x : Fin 9 → Bool) (v : Bool) (a : ℕ) (ha : 9 < a) :
    (List.ofFn x ++ [v]).getD a false = false := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simpa only [List.length_ofFn] using Nat.le_of_lt ha),
    List.getElem?_eq_none (by
      simp only [List.length_ofFn, List.length_singleton]
      omega)]
  rfl

def form (o a : ℕ) : (Fin 9 → Bool) → Bool := fun x =>
  (List.ofFn x ++ [x 0 || x 4,
    !((List.ofFn x ++ [x 0 || x 4]).getD a false)]).getD o false

lemma form_ne_edge (o a : ℕ) : form o a ≠ edge := by
  by_cases ho : o < 9
  · have h : form o a = fun x => x ⟨o, ho⟩ := by
      funext x
      simpa only [form] using prefix_getD_lt x _ ⟨o, ho⟩
    rw [h]
    exact (edge_ne_proj ⟨o, ho⟩).symm
  · by_cases ho9 : o = 9
    · subst o
      have h : form 9 a = fun x : Fin 9 → Bool => x 0 || x 4 := by
        funext x
        simpa only [form] using prefix_getD_nine x _ _
      rw [h]
      exact edge_ne_or.symm
    · by_cases ho10 : o = 10
      · subst o
        by_cases ha : a < 9
        · have h : form 10 a = fun x => !(x ⟨a, ha⟩) := by
            funext x
            rw [form, prefix_getD_ten]
            congr 1
            exact prefix_getD_lt x _ ⟨a, ha⟩
          rw [h]
          exact (edge_ne_not_proj ⟨a, ha⟩).symm
        · by_cases ha9 : a = 9
          · subst a
            have h : form 10 9 = fun x : Fin 9 → Bool => !(x 0 || x 4) := by
              funext x
              rw [form, prefix_getD_ten, input_append_getD_nine]
            rw [h]
            exact edge_ne_not_or.symm
          · have ha10 : 9 < a := by omega
            have h : form 10 a = fun _ : Fin 9 → Bool => true := by
              funext x
              rw [form, prefix_getD_ten, input_append_getD_gt x _ a ha10]
              simp
            rw [h]
            exact edge_ne_true.symm
      · have ho11 : 10 < o := by omega
        have h : form o a = fun _ : Fin 9 → Bool => false := by
          funext x
          simpa only [form] using prefix_getD_gt x _ _ o ho11
        rw [h]
        exact edge_ne_false.symm

end PEqualNP.Outside.L_meta_2754Aux

open PEqualNP.Outside.L_meta_2754Aux PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_2754 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → x1.gates[(2 : ℕ)]? = Option.none → (16 : ℕ) ≤ x1.size := by
  intro C hfan hfirst hfun hnot hnone
  have hlenle : C.gates.length ≤ 2 := List.getElem?_eq_none_iff.mp hnone
  simp only [Option.map_eq_some_iff] at hnot
  obtain ⟨g1, hget, hop⟩ := hnot
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hget
  have hlenge : 2 ≤ C.gates.length := by omega
  have hlen : C.gates.length = 2 := by omega
  obtain ⟨g0, g1', hgates⟩ := List.length_eq_two.mp hlen
  have hg1eq : g1' = g1 := by
    have hh := congrArg (fun l : List PEqualNP.CircuitLowerBounds.Gate => l[1]?) hgates
    simpa [hget] using hh.symm
  subst g1'
  have hop1 : g1.op = GateOp.not := hop
  let a : ℕ := if g1.inputs = [] then 10 else g1.inputs.headD 9
  have hform : PEqualNP.MetaComplexity.circuitFun 9 C = form C.output a := by
    funext x
    have hg1eval :
        g1.op.eval (g1.inputs.map fun i =>
          (List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]).getD i false) =
        !((List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]).getD
          a false) := by
      rw [hop1]
      cases hi : g1.inputs with
      | nil => simp [GateOp.eval, hi, a, List.headD]
      | cons b l => simp [GateOp.eval, hi, a, List.headD]
    have hw : C.wires (List.ofFn x) =
        List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false),
          !((List.ofFn x ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false)]).getD
            a false)] := by
      simp only [Circuit.wires, hgates, List.foldl_cons, List.foldl_nil, List.singleton_append,
        List.append_assoc]
      rw [hg1eval]
    have hw0 : g0.op.eval (g0.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 4) := by
      have hh := hfirst x
      rw [hw] at hh
      simpa using hh
    simp only [MetaComplexity.circuitFun, Circuit.eval, hw, hw0, form]
  apply False.elim
  apply form_ne_edge C.output a
  exact hform.symm.trans hfun
