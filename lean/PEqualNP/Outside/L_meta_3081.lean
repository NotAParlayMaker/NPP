import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3081

open PEqualNP.CircuitLowerBounds

def reads (g : Gate) (p : ℕ) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some p) ∨
  (g.op ≠ GateOp.not ∧ p ∈ g.inputs)

def gateValue (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [gateValue g w]) w

lemma run_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [gateValue g w])).getD i false = _
    have hi' : i < (w ++ [gateValue g w]).length := by
      simpa only [List.length_append, List.length_singleton] using Nat.lt_succ_of_lt hi
    rw [ih _ hi', List.getD_append _ _ _ _ hi]

lemma gateValue_eq {p : ℕ} {w z : List Bool} (g : Gate) (hg : ¬ reads g p)
    (h : ∀ i, i ≠ p → w.getD i false = z.getD i false) :
    gateValue g w = gateValue g z := by
  by_cases hn : g.op = GateOp.not
  · cases hinputs : g.inputs with
    | nil => simp [gateValue, hinputs]
    | cons i is =>
      have hi : i ≠ p := by
        rintro rfl
        exact hg (Or.inl ⟨hn, by simp [hinputs]⟩)
      unfold gateValue
      rw [hn, hinputs]
      change (!w.getD i false) = (!z.getD i false)
      rw [h i hi]
  · unfold gateValue
    congr 1
    apply List.map_congr_left
    intro i hi
    apply h
    rintro rfl
    exact hg (Or.inr ⟨hn, hi⟩)

lemma append_agree {p : ℕ} {w z : List Bool} (b : Bool) (hl : w.length = z.length)
    (h : ∀ i, i ≠ p → w.getD i false = z.getD i false) :
    ∀ i, i ≠ p → (w ++ [b]).getD i false = (z ++ [b]).getD i false := by
  intro i hi
  by_cases hw : i < w.length
  · rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ (hl ▸ hw)]
    exact h i hi
  · have hw' := Nat.le_of_not_gt hw
    rw [List.getD_append_right _ _ _ _ hw', List.getD_append_right _ _ _ _ (hl ▸ hw'), hl]

lemma run_agree {p : ℕ} (gs : List Gate) (hgs : ∀ g ∈ gs, ¬ reads g p)
    {w z : List Bool} (hl : w.length = z.length)
    (h : ∀ i, i ≠ p → w.getD i false = z.getD i false) :
    ∀ i, i ≠ p → (run gs w).getD i false = (run gs z).getD i false := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    have he := gateValue_eq g (hgs g (by simp)) h
    change ∀ i, i ≠ p → (run gs (w ++ [gateValue g w])).getD i false =
      (run gs (z ++ [gateValue g z])).getD i false
    rw [he]
    exact ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) (by simp [hl])
      (append_agree (gateValue g z) hl h)

lemma input_getD {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma input_update_agree {n : ℕ} (x : Fin n → Bool) (p : Fin n) :
    ∀ i, i ≠ p.val →
      (List.ofFn x).getD i false = (List.ofFn (Function.update x p true)).getD i false := by
  intro i hi
  by_cases hn : i < n
  · let j : Fin n := ⟨i, hn⟩
    have hj : j ≠ p := fun h => hi (congrArg Fin.val h)
    change (List.ofFn x).getD j.val false =
      (List.ofFn (Function.update x p true)).getD j.val false
    rw [input_getD, input_getD, Function.update_of_ne hj]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hn),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hn)]

def edgeFunction (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
    x 5 && x 7 || x 6 && x 8 || x 8 && x 5

-- Each initial support is a nonedge and contains the other input of the first OR.
lemma distinguishing_inputs (p : Fin 9) (hp : p = 0 ∨ p = 2) :
    ∃ x : Fin 9 → Bool, edgeFunction x = false ∧
      edgeFunction (Function.update x p true) = true ∧
      (x 0 || x 2) = (Function.update x p true 0 || Function.update x p true 2) := by
  rcases hp with rfl | rfl
  · exact ⟨fun i => decide (i = 2 ∨ i = 4), rfl, rfl, rfl⟩
  · exact ⟨fun i => decide (i = 0 ∨ i = 3), rfl, rfl, rfl⟩

lemma mandatory_reader (C : Circuit)
    (hFirst : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2))
    (hFun : PEqualNP.MetaComplexity.circuitFun 9 C = edgeFunction)
    (p : Fin 9) (hp : p = 0 ∨ p = 2) :
    ∃ g ∈ C.gates.drop 1, reads g p.val := by
  classical
  rcases C with ⟨gs, output⟩
  have eval_eq (x : Fin 9 → Bool) :
      (run gs (List.ofFn x)).getD output false = edgeFunction x := congrFun hFun x
  -- The edge function is false on a singleton, so the output cannot be this input wire.
  have hout : output ≠ p.val := by
    intro he
    let x : Fin 9 → Bool := fun i => decide (i = p)
    have hz : edgeFunction x = false := by
      rcases hp with rfl | rfl <;> rfl
    have h := eval_eq x
    rw [he, run_getD _ _ _ (by simp), input_getD, hz] at h
    simp [x] at h
  obtain ⟨x, hx, hy, hor⟩ := distinguishing_inputs p hp
  let y := Function.update x p true
  change edgeFunction y = true at hy
  change (x 0 || x 2) = (y 0 || y 2) at hor
  by_contra hnone
  cases gs with
  | nil =>
    have h := hFirst (fun i : Fin 9 => decide (i = 0))
    change false = true at h
    exact Bool.noConfusion h
  | cons g gs =>
    have hgs (g' : Gate) (hg' : g' ∈ gs) : ¬ reads g' p.val :=
      fun hr => hnone ⟨g', hg', hr⟩
    have first_value (a : Fin 9 → Bool) : gateValue g (List.ofFn a) = (a 0 || a 2) := by
      have h := hFirst a
      change (run gs (List.ofFn a ++ [gateValue g (List.ofFn a)])).getD 9 false = _ at h
      rw [run_getD _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp),
        List.length_ofFn] at h
      exact h
    have he : gateValue g (List.ofFn x) = gateValue g (List.ofFn y) :=
      (first_value x).trans (hor.trans (first_value y).symm)
    have hagree := run_agree gs hgs
      (w := List.ofFn x ++ [gateValue g (List.ofFn y)])
      (z := List.ofFn y ++ [gateValue g (List.ofFn y)]) (by simp)
      (append_agree _ (by simp) (input_update_agree x p)) output hout
    have hout_eq : (run (g :: gs) (List.ofFn x)).getD output false =
        (run (g :: gs) (List.ofFn y)).getD output false := by
      change (run gs (List.ofFn x ++ [gateValue g (List.ofFn x)])).getD output false = _
      rw [he]
      exact hagree
    rw [eval_eq x, eval_eq y, hx, hy] at hout_eq
    exact Bool.noConfusion hout_eq

end PEqualNP.Outside.L_meta_3081

theorem PEqualNP.Outside.L_meta_3081 : have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x3 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → ∀ (x5 : ℕ), x5 = (0 : ℕ) ∨ x5 = (2 : ℕ) → ∃ x7 ∈ List.drop (1 : ℕ) x2.gates, x1 x7 x5 := by
  dsimp only
  intro C hFirst hFun v hv
  rcases hv with rfl | rfl
  · exact PEqualNP.Outside.L_meta_3081.mandatory_reader C hFirst hFun 0 (Or.inl rfl)
  · exact PEqualNP.Outside.L_meta_3081.mandatory_reader C hFirst hFun 2 (Or.inr rfl)
