import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4069

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases Nat.lt_trichotomy i W.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stp W1).getD i false = true → (gs.foldl stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stp W1 g) (stp W2 g) (by simp [stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stp, getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [ev_and g _ ha, ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [ev_or g _ ho, ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem all_idx (n : ℕ) (x y : List Bool) (hx : x.length = n)
    (H : ∀ i < n, x.getD i false = true → y.getD i false = true) :
    ∀ i, x.getD i false = true → y.getD i false = true := by
  intro i hi
  by_cases h : i < n
  · exact H i h hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
    exact Bool.noConfusion hi

end PEqualNP.Outside.L_meta_4069

open PEqualNP.Outside.L_meta_4069 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_4069 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x2 →
      ∀ (x4 x5 : Fin x1 → Bool),
        (∀ (x6 : Fin x1), x4 x6 = Bool.true → x5 x6 = Bool.true) →
        PEqualNP.MetaComplexity.circuitFun x1 x2 x4 = Bool.true →
        PEqualNP.MetaComplexity.circuitFun x1 x2 x5 = Bool.true := by
  intro n C hM x4 x5 hle hval
  have hM' : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h := hM g hg
    rcases h.1 with h1 | h1
    · left; simpa using h1
    · right; simpa using h1
  have hpt : ∀ i < n, (List.ofFn x4).getD i false = true → (List.ofFn x5).getD i false = true := by
    intro i hi h
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi]
    exact hle ⟨i, hi⟩ h
  have hval' : C.eval (List.ofFn x4) = true := hval
  rw [eval_eq] at hval'
  have hres := mono C.gates (List.ofFn x4) (List.ofFn x5) (by simp)
    hM' (all_idx n (List.ofFn x4) (List.ofFn x5) (by simp) hpt) C.output hval'
  exact hres
