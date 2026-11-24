import PEqualNP.Defs

-- Circuit evaluation and single-input contraction from project theorem L-meta-2535, Apache-2.0.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_4457_aux.Erase

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_ofFn_lt {α : Type} {n : ℕ} (x : Fin n → α) (d : α) (j : ℕ) (h : j < n) :
    (List.ofFn x).getD j d = x ⟨j, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

end PEqualNP.Outside.L_meta_4457_aux.Erase

open PEqualNP.Outside.L_meta_4457_aux.Erase

namespace PEqualNP.Outside.L_meta_4457_aux.Literals

theorem appendOne {n s : ℕ} (i : Fin n) {f : (Fin n → Bool) → Bool}
    (h : HasCircuitSize n f s) :
    HasCircuitSize n (fun x => x i || f x) (s+1) := by
  obtain ⟨C,legal,size,correct⟩ := h
  let g : Gate := ⟨GateOp.or,[i.val,C.output]⟩
  refine ⟨⟨C.gates ++ [g], n+C.gates.length⟩, ?_, ?_, ?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact legal z hz
    · obtain rfl : z = g := by simpa using hz
      simp [g]
  · change (C.gates ++ [g]).length ≤ s+1
    simpa [Circuit.size] using Nat.add_le_add_right size 1
  · intro x
    let w := wiresFrom C.gates (List.ofFn x)
    have len : w.length = n+C.gates.length := by simp [w,length_wiresFrom]
    have left : w.getD i.val false = x i := by
      rw [show w = wiresFrom C.gates (List.ofFn x) from rfl,getD_wiresFrom _ _ _ (by simp)]
      exact getD_ofFn_lt _ _ _ i.isLt
    have right : w.getD C.output false = f x := correct x
    change (wiresFrom (C.gates ++ [g]) (List.ofFn x)).getD (n+C.gates.length) false = _
    rw [wiresFrom_append]
    change (w ++ [GateOp.or.eval [w.getD i.val false,w.getD C.output false]]).getD (n+C.gates.length) false = _
    rw [← len,getD_snoc_eq,left,right]
    simp [GateOp.eval]

theorem appendSet {n t : ℕ} (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
    (h : HasCircuitSize n f t) :
    HasCircuitSize n (fun x => decide (∃ v ∈ A, x v = true) || f x) (t+A.card) := by
  induction A using Finset.induction_on with
  | empty => simpa using h
  | @insert i A hi ih =>
    have next := appendOne i ih
    convert next using 1
    · funext x
      apply Bool.eq_iff_iff.mpr
      simp [or_assoc]
    · rw [Finset.card_insert_of_notMem hi]; omega

end PEqualNP.Outside.L_meta_4457_aux.Literals

theorem PEqualNP.Outside.L_meta_4457 :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1)) (x3 : (Fin x1 → Bool) → Bool) (x4 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x4 → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x6 : Fin x1 → Bool) => Decidable.decide (∃ x7 ∈ x2, x6 x7 = Bool.true) || x3 x6) (x4 + x2.card) :=
  fun _ A f _ size => PEqualNP.Outside.L_meta_4457_aux.Literals.appendSet A f size
