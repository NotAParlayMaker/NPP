import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1454
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

/-- With the only NOT gate true on every input false on `T`, every wire of every prefix is
monotone on the inputs false on `T`. -/
theorem mono (n : ℕ) (T : Finset (Fin n)) (gates : List Gate) (j : Fin gates.length)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hout : ∀ x : Fin n → Bool, (∀ v ∈ T, x v = false) →
      Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = true)
    (x y : Fin n → Bool) (hy : ∀ v ∈ T, y v = false) (hxy : ∀ v : Fin n, x v = true → y v = true) :
    ∀ k, k ≤ gates.length → ∀ w, (wf (gates.take k) (List.ofFn x)).getD w false = true →
      (wf (gates.take k) (List.ofFn y)).getD w false = true := by
  intro k
  induction k with
  | zero =>
    intro _ w
    simpa [wf] using ofFn_mono n x y hxy w
  | succ k ih =>
    intro hk w
    have hk' : k < gates.length := hk
    have ih' := ih (Nat.le_of_lt hk')
    have htake : gates.take (k + 1) = gates.take k ++ [gates[k]] := by
      rw [List.take_succ_eq_append_getElem hk']
    have hlenx : (wf (gates.take k) (List.ofFn x)).length = n + k := by
      rw [wf_len]; simp; omega
    have hleny : (wf (gates.take k) (List.ofFn y)).length = n + k := by
      rw [wf_len]; simp; omega
    rw [htake, wf_snoc, wf_snoc]
    rcases Nat.lt_trichotomy w (n + k) with hw | hw | hw
    · rw [getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
      exact ih' w
    · subst hw
      have e1 := getD_snoc_eq (wf (gates.take k) (List.ofFn x))
        (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) (List.ofFn x)).getD i false))
      have e2 := getD_snoc_eq (wf (gates.take k) (List.ofFn y))
        (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) (List.ofFn y)).getD i false))
      rw [hlenx] at e1; rw [hleny] at e2
      rw [e1, e2]
      rcases (hleg gates[k] (List.getElem_mem hk')).1 with hop | hop | hop
      · exact eval_mono _ (Or.inl hop) _ _ _ ih'
      · exact eval_mono _ (Or.inr hop) _ _ _ ih'
      · intro _
        have hj : (⟨k, hk'⟩ : Fin gates.length) = j := hnot ⟨k, hk'⟩ hop
        have hv : (j : ℕ) = k := by rw [← hj]
        have h1 := hout y hy
        rw [eval_eq, hv] at h1
        have h2 : (wf gates (List.ofFn y)).getD (n + k) false
            = (wf (gates.take (k + 1)) (List.ofFn y)).getD (n + k) false := by
          conv_lhs => rw [← List.take_append_drop (k + 1) gates]
          exact wf_prefix _ _ _ _ (by simp; omega)
        rw [h2, htake, wf_snoc, e2] at h1
        exact h1
    · rw [getD_snoc_gt _ _ _ (by omega)]
      intro h; exact absurd h (by simp)

end PEqualNP.Outside.L_meta_1454

theorem PEqualNP.Outside.L_meta_1454 : ∀ (n : ℕ) (T : Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate)
    (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ x : Fin n → Bool, (∀ v ∈ T, x v = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = true) →
    ∀ (w : ℕ) (x y : Fin n → Bool), (∀ v ∈ T, y v = false) → (∀ v : Fin n, x v = true → y v = true) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn y) = true := by
  intro n T gates j hleg hnot hout w x y hy hxy h
  rw [PEqualNP.Outside.L_meta_1454.eval_eq] at h ⊢
  have := PEqualNP.Outside.L_meta_1454.mono n T gates j hleg hnot hout x y hy hxy
    gates.length le_rfl w
  rw [List.take_length] at this
  exact this h
