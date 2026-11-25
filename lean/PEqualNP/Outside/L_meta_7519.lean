import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7519_aux


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

def P (B L : List ℕ) : Prop := ∀ i : Fin L.length, ∃ x ∈ B ++ L.take i, ∃ y ∈ B ++ L.take i,
  L.get i = x &&& y ∨ L.get i = x ||| y

theorem snoc_l (B l : List ℕ) (a : ℕ) (h : P B (l ++ [a])) :
    P B l ∧ ∃ x ∈ B ++ l, ∃ y ∈ B ++ l, a = x &&& y ∨ a = x ||| y := by
  constructor
  · intro i
    obtain ⟨x, hx, y, hy, h⟩ := h ⟨i, by simp⟩
    have ht : (l ++ [a]).take i = l.take i := List.take_append_of_le_length (by omega)
    refine ⟨x, by simpa [ht] using hx, y, by simpa [ht] using hy, ?_⟩
    simpa [List.getElem_append_left i.isLt] using h
  · obtain ⟨x, hx, y, hy, h⟩ := h ⟨l.length, by simp⟩
    refine ⟨x, by simpa using hx, y, by simpa using hy, by simpa using h⟩

theorem snoc_r (C m : List ℕ) (b : ℕ) (h : P C m)
    (hb : ∃ x ∈ C ++ m, ∃ y ∈ C ++ m, b = x &&& y ∨ b = x ||| y) : P C (m ++ [b]) := by
  intro i
  by_cases hi : (i : ℕ) < m.length
  · obtain ⟨x, hx, y, hy, h⟩ := h ⟨i, hi⟩
    have ht : (m ++ [b]).take i = m.take i := List.take_append_of_le_length (by omega)
    refine ⟨x, by simpa [ht] using hx, y, by simpa [ht] using hy, ?_⟩
    simpa [List.getElem_append_left hi] using h
  · rcases i with ⟨i, hi'⟩
    have hi2 : i = m.length := by simp at hi hi'; omega
    subst hi2
    obtain ⟨x, hx, y, hy, h⟩ := hb
    exact ⟨x, by simpa using hx, y, by simpa using hy, by simpa using h⟩

theorem core : ∀ (B C : List ℕ) (R : ℕ → ℕ → Prop), (∀ v ∈ B, ∃ w ∈ C, R v w) →
    (∀ a b c d : ℕ, R a c → R b d → R (a &&& b) (c &&& d) ∧ R (a ||| b) (c ||| d)) →
    ∀ L : List ℕ, P B L → ∃ M : List ℕ, M.length = L.length ∧ P C M ∧ ∀ v ∈ L, ∃ w ∈ M, R v w := by
  intro B C R hBC hcl L
  induction L using List.reverseRecOn with
  | nil => intro _; exact ⟨[], rfl, fun i => absurd i.isLt (by simp), by simp⟩
  | append_singleton l a ih =>
    intro h
    obtain ⟨hl, x, hx, y, hy, ha⟩ := snoc_l B l a h
    obtain ⟨m, hm, hPm, hrel⟩ := ih hl
    have part : ∀ v ∈ B ++ l, ∃ w ∈ C ++ m, R v w := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨w, hw, hr⟩ := hBC v hv; exact ⟨w, List.mem_append_left _ hw, hr⟩
      · obtain ⟨w, hw, hr⟩ := hrel v hv; exact ⟨w, List.mem_append_right _ hw, hr⟩
    obtain ⟨x', hx', hxr⟩ := part x hx
    obtain ⟨y', hy', hyr⟩ := part y hy
    rcases ha with ha | ha
    · refine ⟨m ++ [x' &&& y'], by simp [hm], snoc_r C m _ hPm ⟨x', hx', y', hy', Or.inl rfl⟩, ?_⟩
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨w, hw, hr⟩ := hrel v hv; exact ⟨w, List.mem_append_left _ hw, hr⟩
      · simp at hv; subst hv; subst ha; exact ⟨_, by simp, (hcl _ _ _ _ hxr hyr).1⟩
    · refine ⟨m ++ [x' ||| y'], by simp [hm], snoc_r C m _ hPm ⟨x', hx', y', hy', Or.inr rfl⟩, ?_⟩
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨w, hw, hr⟩ := hrel v hv; exact ⟨w, List.mem_append_left _ hw, hr⟩
      · simp at hv; subst hv; subst ha; exact ⟨_, by simp, (hcl _ _ _ _ hxr hyr).2⟩

theorem main : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 : List ℕ) (x4 : ℕ → ℕ → Prop), (∀ x5 ∈ x2, ∃ x7 ∈ x3, x4 x5 x7) → (∀ (x6 x7 x8 x9 : ℕ), x4 x6 x8 → x4 x7 x9 → x4 (x6 &&& x7) (x8 &&& x9) ∧ x4 (x6 ||| x7) (x8 ||| x9)) → ∀ (x7 : List ℕ), x1 x2 x7 → ∃ (x9 : List ℕ), x9.length = x7.length ∧ x1 x3 x9 ∧ ∀ x10 ∈ x7, ∃ x12 ∈ x9, x4 x10 x12 := by
  intro x1
  exact core

end PEqualNP.Outside.L_meta_7519_aux

theorem PEqualNP.Outside.L_meta_7519 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 x3 : List ℕ) (x4 : ℕ → ℕ → Prop), (∀ x5 ∈ x2, ∃ x7 ∈ x3, x4 x5 x7) → (∀ (x6 x7 x8 x9 : ℕ), x4 x6 x8 → x4 x7 x9 → x4 (x6 &&& x7) (x8 &&& x9) ∧ x4 (x6 ||| x7) (x8 ||| x9)) → ∀ (x7 : List ℕ), x1 x2 x7 → ∃ (x9 : List ℕ), x9.length = x7.length ∧ x1 x3 x9 ∧ ∀ x10 ∈ x7, ∃ x12 ∈ x9, x4 x10 x12 := by
  exact PEqualNP.Outside.L_meta_7519_aux.main
