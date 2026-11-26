import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18244_aux

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w

theorem or_true {g : Gate} (w : List Bool) (hop : g.op = GateOp.or)
    {j : ℕ} (mem : j ∈ g.inputs) (on : w.getD j false = true) :
    g.op.eval (g.inputs.map (fun i => w.getD i false)) = true := by
  rw [hop]
  apply List.any_eq_true.mpr
  exact ⟨true, List.mem_map.mpr ⟨j, mem, on⟩, rfl⟩

theorem getD_snoc (L : List Bool) (b : Bool) (j : ℕ) :
    (L ++ [b]).getD j false = if j = L.length then b else L.getD j false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h1 | h1
    · rw [List.getD_append _ _ _ _ h1]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]


theorem compareWires (a b c : ℕ) (ab : a ≠ b) (ac : a ≠ c) (gs : List Gate)
    (shape : ∀ g ∈ gs, a ∈ g.inputs → g.op = GateOp.or ∧ (b ∈ g.inputs ∨ c ∈ g.inputs)) :
    ∀ (x y : List Bool), x.length = y.length → b < x.length → c < x.length →
      x.getD b false = true → x.getD c false = true →
      (∀ i, i ≠ a → x.getD i false = y.getD i false) →
      ∀ i, i ≠ a → (run gs x).getD i false = (run gs y).getD i false := by
  induction gs with
  | nil => intro x y _ _ _ _ _ eq i hi; exact eq i hi
  | cons g t ih =>
    intro x y len hb hc xb xc eq
    let vx := g.op.eval (g.inputs.map fun i => x.getD i false)
    let vy := g.op.eval (g.inputs.map fun i => y.getD i false)
    have same : vx = vy := by
      by_cases ha : a ∈ g.inputs
      · obtain ⟨hop, hm | hm⟩ := shape g (by simp) ha
        · exact (or_true x hop hm xb).trans (or_true y hop hm ((eq b ab.symm).symm.trans xb)).symm
        · exact (or_true x hop hm xc).trans (or_true y hop hm ((eq c ac.symm).symm.trans xc)).symm
      · apply congrArg g.op.eval
        apply List.map_congr_left
        intro i hi
        exact eq i (fun e => ha (e ▸ hi))
    change ∀ i, i ≠ a → (run t (x ++ [vx])).getD i false = (run t (y ++ [vy])).getD i false
    apply ih (fun w hw => shape w (by simp [hw])) _ _ (by simp [len]) (by simp; omega) (by simp; omega)
    · rw [getD_snoc, if_neg (Nat.ne_of_lt hb)]; exact xb
    · rw [getD_snoc, if_neg (Nat.ne_of_lt hc)]; exact xc
    · intro i hi
      simp only [getD_snoc, len, same, eq i hi]

theorem readInput {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

end PEqualNP.Outside.L_meta_18244_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_18244_aux

theorem PEqualNP.Outside.L_meta_18244 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → x3 ≠ x4 → x3 ≠ x5 → (∀ x9 < x2.size, ↑x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (↑x4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).inputs ∨ ↑x5 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).inputs)) → (∀ (x10 : Fin x1 → Bool), x2.eval (List.ofFn x10) = x10 x3) ∨ ∀ (x10 x11 : Fin x1 → Bool), x10 x4 = Bool.true → x10 x5 = Bool.true → (∀ (x14 : Fin x1), x14 ≠ x3 → x10 x14 = x11 x14) → x2.eval (List.ofFn x10) = x2.eval (List.ofFn x11) := by
  intro n C a b c _ ab ac h
  by_cases ho : C.output = a.val
  · left
    intro x
    change (run C.gates (List.ofFn x)).getD C.output false = x a
    rw [ho]
    suffices key : ∀ (gs : List Gate) (w : List Bool) (j : ℕ), j < w.length → (run gs w).getD j false = w.getD j false by
      rw [key _ _ _ (by simp), readInput]
    intro gs
    induction gs with
    | nil => intros; rfl
    | cons g t ih =>
      intro w j hj
      change (run t (w ++ [_])).getD j false = _
      rw [ih _ _ (by simp; omega), getD_snoc, if_neg (Nat.ne_of_lt hj)]
  · right
    intro x y xb xc eq
    apply compareWires a b c (fun e => ab (Fin.ext e)) (fun e => ac (Fin.ext e)) C.gates _ _ _ (by simp) (by simp) (by simp)
      ((readInput x b).trans xb) ((readInput x c).trans xc) _ _ ho
    · intro g hg
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hg
      have atj : gateAt C j = g := by simpa [gateAt, List.getD_eq_getElem _ _ j.isLt] using hj
      simpa only [atj] using h j j.isLt
    · intro i hi
      by_cases hin : i < n
      · let t : Fin n := ⟨i, hin⟩
        exact (readInput x t).trans ((eq t (fun e => hi (congrArg Fin.val e))).trans (readInput y t).symm)
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
