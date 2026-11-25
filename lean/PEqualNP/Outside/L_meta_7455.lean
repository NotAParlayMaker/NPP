import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7455_aux


open PEqualNP.CircuitLowerBounds

theorem getD_app_lt (l : List Bool) (b : Bool) (i : ℕ) (h : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_eq (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

theorem getD_app_gt (l : List Bool) (b : Bool) (i : ℕ) (h : l.length < i) :
    (l ++ [b]).getD i false = false := by
  rw [List.getD_eq_default]
  simp; omega

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_default _ _ h]

theorem wires_len (gs : List Gate) : ∀ (d : List Bool),
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d).length
      = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp
  | cons g gs ih => intro d; rw [List.foldl_cons, ih]; simp; omega

theorem reach_len (X : ℕ) (gs : List Gate) : ∀ (d : List Bool),
    (gs.foldl (fun (d : List Bool) (g : Gate) =>
        d ++ [decide (d.length ≠ X) && g.inputs.any fun i => d.getD i false]) d).length
      = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp
  | cons g gs ih => intro d; rw [List.foldl_cons, ih]; simp; omega

theorem wires_prefix (gs : List Gate) : ∀ (d : List Bool) (i : ℕ), i < d.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d).getD i false
      = d.getD i false := by
  induction gs with
  | nil => intro d i _; simp
  | cons g gs ih =>
    intro d i hi
    rw [List.foldl_cons, ih _ _ (by simp; omega), getD_app_lt _ _ _ hi]

theorem indep (X : ℕ) (gs : List Gate) : ∀ (d e r : List Bool),
    d.length = r.length → e.length = r.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d).getD X false
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) e).getD X false →
    (∀ i, i ≠ X → r.getD i false = false → d.getD i false = e.getD i false) →
    ∀ i, (gs.foldl (fun (d : List Bool) (g : Gate) =>
        d ++ [decide (d.length ≠ X) && g.inputs.any fun i => d.getD i false]) r).getD i false = false →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d).getD i false
      = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) e).getD i false := by
  induction gs with
  | nil =>
    intro d e r _ _ hX hinv i hi
    simp only [List.foldl_nil] at hX hi ⊢
    by_cases hiX : i = X
    · subst hiX; exact hX
    · exact hinv i hiX hi
  | cons g gs ih =>
    intro d e r hd he hX hinv
    have hdX : d.getD X false = e.getD X false := by
      by_cases hlt : X < d.length
      · rw [← wires_prefix (g :: gs) d X hlt, ← wires_prefix (g :: gs) e X (by omega)]
        exact hX
      · rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
    have hall : ∀ j, r.getD j false = false → d.getD j false = e.getD j false := by
      intro j hj
      by_cases hjX : j = X
      · subst hjX; exact hdX
      · exact hinv j hjX hj
    rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
    apply ih
    · simp [hd]
    · simp [he]
    · rw [List.foldl_cons, List.foldl_cons] at hX; exact hX
    · intro i hiX hri
      rcases lt_trichotomy i r.length with h | h | h
      · rw [getD_app_lt _ _ _ h] at hri
        rw [getD_app_lt _ _ _ (by omega), getD_app_lt _ _ _ (by omega)]
        exact hinv i hiX hri
      · subst h
        rw [getD_app_eq] at hri
        rw [← hd, getD_app_eq, hd, ← he, getD_app_eq]
        have hne : decide (r.length ≠ X) = true := by simp; exact hiX
        rw [hne, Bool.true_and] at hri
        have hmap : (g.inputs.map fun i => d.getD i false) = (g.inputs.map fun i => e.getD i false) := by
          apply List.map_congr_left
          intro j hj
          apply hall
          have := List.any_eq_false.mp hri j hj
          simpa using this
        rw [hmap]
      · rw [getD_app_gt _ _ _ (by omega), getD_app_gt _ _ _ (by omega)]

theorem mono (gs : List Gate) (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (d e : List Bool), d.length = e.length →
    (∀ i, d.getD i false = true → e.getD i false = true) →
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d).getD i false = true →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) e).getD i false = true := by
  induction gs with
  | nil => intro d e _ h i; simpa using h i
  | cons g gs ih =>
    intro d e hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · intro i hi
      rcases lt_trichotomy i d.length with hh | hh | hh
      · rw [getD_app_lt _ _ _ hh] at hi
        rw [getD_app_lt _ _ _ (by omega)]
        exact h i hi
      · subst hh
        rw [getD_app_eq] at hi
        rw [hl, getD_app_eq]
        rcases hop g (List.mem_cons_self) with ho | ho
        · rw [ho] at hi ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map] at hi ⊢
          rintro _ ⟨j, hj, rfl⟩
          exact h j (by simpa using hi _ ⟨j, hj, rfl⟩)
        · rw [ho] at hi ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map] at hi ⊢
          obtain ⟨_, ⟨j, hj, rfl⟩, hv⟩ := hi
          exact ⟨_, ⟨j, hj, rfl⟩, by simpa using h j (by simpa using hv)⟩
      · rw [getD_app_gt _ _ _ hh] at hi
        exact absurd hi (by simp)


open PEqualNP.MetaComplexity.NestedCover

theorem getD_snoc (L : List Bool) (v : Bool) (i : ℕ) : (L ++ [v]).getD i false =
    if i < L.length then L.getD i false else if i = L.length then v else false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem main : ∀ (x1 : ℕ) (x2 x3 : Fin x1) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4 → x4.output < x1 + x4.size → x5 < x1 + x4.size → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x10 ∧ x10.size = x4.size + (3 : ℕ) ∧ x10.output < x1 + x10.size ∧ (∀ x11 < x1 + x4.size, ∀ (x13 : Fin x1 → Bool), (x10.wires (List.ofFn x13)).getD x11 Bool.false = (x4.wires (List.ofFn x13)).getD x11 Bool.false) ∧ ∀ (x11 : Fin x1 → Bool), x10.eval (List.ofFn x11) = (x4.eval (List.ofFn x11) || x11 x3 && (x11 x2 || (x4.wires (List.ofFn x11)).getD x5 Bool.false)) := by
  intro n a b C s hM hRB ho hs
  let T : List Gate := [⟨GateOp.or, [a.val, s]⟩, ⟨GateOp.and, [b.val, n + C.size]⟩,
    ⟨GateOp.or, [C.output, n + C.size + 1]⟩]
  have hw : ∀ x, Circuit.wires ⟨C.gates ++ T, n + C.size + 2⟩ x =
      T.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (C.wires x) := by
    intro x; show List.foldl _ _ _ = _; rw [List.foldl_append]; rfl
  have hW : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).length = n + C.size := by
    intro x; unfold Circuit.wires; rw [wires_len]; simp [Circuit.size]
  refine ⟨⟨C.gates ++ T, n + C.size + 2⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hM g hg
    · simp only [T, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl <;> simp
  · intro j hj i hi
    simp only [T, List.length_append, List.length_cons, List.length_nil] at hj
    by_cases hjl : j < C.gates.length
    · have he : gateAt ⟨C.gates ++ T, n + C.size + 2⟩ j = gateAt C j := by
        simp only [gateAt, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left hjl]
      rw [he] at hi
      have := hRB j hjl i hi
      omega
    · have hj3 : j = C.gates.length ∨ j = C.gates.length + 1 ∨ j = C.gates.length + 2 := by omega
      have hb := b.isLt
      have ha := a.isLt
      simp only [Circuit.size] at hs ho ⊢
      rcases hj3 with rfl | rfl | rfl <;>
        simp [gateAt, T, List.getD_eq_getElem?_getD, List.getElem?_append_right, Circuit.size] at hi <;>
        rcases hi with rfl | rfl <;> omega
  · simp [Circuit.size, T]
  · simp only [Circuit.size, T, List.length_append, List.length_cons, List.length_nil]; omega
  · intro i hi x
    rw [hw]
    exact wires_prefix T _ i (by rw [hW]; exact hi)
  · intro x
    have hin : ∀ i : Fin n, (C.wires (List.ofFn x)).getD i false = x i := by
      intro i; unfold Circuit.wires; rw [wires_prefix _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    have hb := b.isLt
    have ha := a.isLt
    have hoe : C.eval (List.ofFn x) = (C.wires (List.ofFn x)).getD C.output false := rfl
    unfold Circuit.eval
    rw [hw, ← hin a, ← hin b]
    have hl := hW x
    generalize C.wires (List.ofFn x) = W at hl ⊢
    simp only [T, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, getD_snoc,
      List.length_append, List.length_singleton, hl]
    split_ifs <;> (try omega) <;> simp [GateOp.eval]

end PEqualNP.Outside.L_meta_7455_aux

theorem PEqualNP.Outside.L_meta_7455 : ∀ (x1 : ℕ) (x2 x3 : Fin x1) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x4 → x4.output < x1 + x4.size → x5 < x1 + x4.size → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x10 ∧ x10.size = x4.size + (3 : ℕ) ∧ x10.output < x1 + x10.size ∧ (∀ x11 < x1 + x4.size, ∀ (x13 : Fin x1 → Bool), (x10.wires (List.ofFn x13)).getD x11 Bool.false = (x4.wires (List.ofFn x13)).getD x11 Bool.false) ∧ ∀ (x11 : Fin x1 → Bool), x10.eval (List.ofFn x11) = (x4.eval (List.ofFn x11) || x11 x3 && (x11 x2 || (x4.wires (List.ofFn x11)).getD x5 Bool.false)) := by
  exact PEqualNP.Outside.L_meta_7455_aux.main
