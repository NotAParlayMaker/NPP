import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2859
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

theorem wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def ren (n m p i : ℕ) : ℕ := if i = n + m then p else if n + m < i then i - 1 else i

def rg (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (ren n m p)⟩

theorem sim (n m p : ℕ) (hp : p < n + m) (B : List Gate) : ∀ U U' : List Bool, U.length = U'.length + 1 →
    n + m < U.length → (∀ i, U.getD i false = U'.getD (ren n m p i) false) →
    ∀ i, (wf B U).getD i false = (wf (B.map (rg n m p)) U').getD (ren n m p i) false := by
  induction B with
  | nil => intro U U' _ _ h i; exact h i
  | cons g B ih =>
    intro U U' hlen hbig h i
    rw [List.map_cons, wf_cons, wf_cons]
    refine ih _ _ (by simp [hlen]) (by simp; omega) ?_ i
    intro t
    have hv : g.op.eval (g.inputs.map fun i => U.getD i false)
        = (rg n m p g).op.eval ((rg n m p g).inputs.map fun i => U'.getD i false) := by
      show _ = g.op.eval ((g.inputs.map (ren n m p)).map fun i => U'.getD i false)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    rw [← hv]
    rcases Nat.lt_trichotomy t U.length with ht | ht | ht
    · have h1 : ren n m p t < U'.length := by
        unfold ren
        split
        · omega
        · split <;> omega
      rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ h1]
      exact h t
    · subst ht
      rw [getD_snoc_eq]
      have e : ren n m p U.length = U'.length := by
        unfold ren
        rw [ite_eq_right (by omega), ite_eq_left hbig]
        omega
      rw [e, getD_snoc_eq]
    · rw [getD_snoc_gt _ _ _ ht]
      have e : U'.length < ren n m p t := by
        unfold ren
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        omega
      rw [getD_snoc_gt _ _ _ e]

end PEqualNP.Outside.L_meta_2859

open PEqualNP.Outside.L_meta_2859 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2859 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (m p : ℕ), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → m < C.gates.length → p < n + m → PEqualNP.MetaComplexity.Monotone2 (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n (PEqualNP.CircuitMoves.eraseGate n C m p) ∧ (PEqualNP.CircuitMoves.eraseGate n C m p).size + 1 = C.size ∧ ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD p false = (C.wires (List.ofFn x)).getD (n + m) false → (PEqualNP.CircuitMoves.eraseGate n C m p).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  intro n C m p hmono hrb hm hp
  have hE : PEqualNP.CircuitMoves.eraseGate n C m p
      = ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p), ren n m p C.output⟩ := by
    unfold PEqualNP.CircuitMoves.eraseGate
    rw [if_pos hm]
    rfl
  rw [hE]
  have hG : ∀ j (hj : j < C.gates.length),
      PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    intro j hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩
    · exact hmono g (List.mem_of_mem_take hg)
    · have := hmono g0 (List.mem_of_mem_drop hg0)
      exact ⟨this.1, by simpa [rg] using this.2⟩
  · intro j hj i hi
    have hlen : (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)).length = C.gates.length - 1 := by
      simp; omega
    have hj' : j < C.gates.length - 1 := by
      have : j < (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)).length := hj
      omega
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    by_cases hjm : j < m
    · have e : (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)).getD j ⟨GateOp.or, []⟩ = C.gates[j]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append, hjm, List.getElem?_take, (by omega : j < C.gates.length)]
      rw [e] at hi
      have := hrb j (by omega) i
      rw [hG j (by omega)] at this
      exact this hi
    · have e : (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)).getD j ⟨GateOp.or, []⟩ = rg n m p (C.gates[j + 1]'(by omega)) := by
        have h1 : m + 1 + (j - m) = j + 1 := by omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_append, hjm, List.getElem?_take, List.getElem?_drop, h1, (by omega : j + 1 < C.gates.length), (by omega : min m C.gates.length = m)]
      rw [e] at hi
      simp only [rg, List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have := hrb (j + 1) (by omega) i0
      rw [hG (j + 1) (by omega)] at this
      have h0 := this hi0
      unfold ren
      split
      · omega
      · split <;> omega
  · simp [Circuit.size]; omega
  · intro x hx
    have h2 : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
      rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
    have hWlen : (wf (C.gates.take m) (List.ofFn x)).length = n + m := by
      rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hm)]
    have e1 : wf C.gates (List.ofFn x) = wf (C.gates.drop (m + 1))
        (wf (C.gates.take m) (List.ofFn x) ++ [C.gates[m].op.eval (C.gates[m].inputs.map fun i => (wf (C.gates.take m) (List.ofFn x)).getD i false)]) := by
      conv_lhs => rw [h2]
      rw [wf_append, wf_cons]
    show (wf (C.gates.take m ++ (C.gates.drop (m + 1)).map (rg n m p)) (List.ofFn x)).getD (ren n m p C.output) false
      = (wf C.gates (List.ofFn x)).getD C.output false
    have hx' : (wf C.gates (List.ofFn x)).getD p false = (wf C.gates (List.ofFn x)).getD (n + m) false := hx
    rw [wf_append, e1]
    rw [e1] at hx'
    generalize wf (C.gates.take m) (List.ofFn x) = W at *
    generalize C.gates[m].op.eval (C.gates[m].inputs.map fun i => W.getD i false) = v at *
    rw [wf_keep _ _ _ (by simp; omega), wf_keep _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)] at hx'
    have hv : (W ++ [v]).getD (n + m) false = v := by rw [← hWlen, getD_snoc_eq]
    rw [hv] at hx'
    refine (sim n m p hp (C.gates.drop (m + 1)) (W ++ [v]) W (by simp) (by simp; omega) ?_ C.output).symm
    intro i
    unfold ren
    split
    · rename_i h; rw [h, hv, hx']
    · split
      · rw [getD_snoc_gt _ _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · rw [getD_snoc_lt _ _ _ (by omega)]
