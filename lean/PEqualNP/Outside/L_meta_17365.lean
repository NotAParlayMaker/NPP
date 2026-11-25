import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.RepInduced
import PEqualNP.Outside.L_meta_7626

-- The double crown on 2k + 2k vertices: keep the even rows and columns (RepInduced.induced saves
-- 2k gates), relabel them onto the crown on k + k vertices (same size), and use L-meta-7626.

namespace PEqualNP.Outside.L_meta_17365

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- One gate step, as in `Circuit.wires`. -/
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- Rename the wires a gate reads. -/
def rn (φ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map φ⟩

theorem getD_app (W : List Bool) (b : Bool) (i : ℕ) :
    (W ++ [b]).getD i false = if i < W.length then W.getD i false
      else if i = W.length then b else false := by
  by_cases h1 : i < W.length
  · rw [if_pos h1, List.getD_append _ _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : i = W.length
    · subst h2; simp
    · rw [if_neg h2, List.getD_eq_default _ _ (by simp; omega)]

theorem relabel (n1 n2 : ℕ) (φ : ℕ → ℕ) (hφ : ∀ i, n1 ≤ i → φ i + n1 = i + n2) :
    ∀ (gs : List Gate) (W W' : List Bool), n1 ≤ W.length →
      W.length + n2 = W'.length + n1 →
      (∀ i, i < n1 → φ i < n2 ∨ W'.length + gs.length ≤ φ i) →
      (∀ i, W.getD i false = W'.getD (φ i) false) →
      ∀ i, (gs.foldl stp W).getD i false = ((gs.map (rn φ)).foldl stp W').getD (φ i) false := by
  intro gs
  induction gs with
  | nil => intro W W' _ _ _ h i; simpa using h i
  | cons g rest ih =>
    intro W W' h1 h2 h3 h4
    have hl : (g :: rest).length = rest.length + 1 := rfl
    simp only [List.foldl_cons, List.map_cons]
    have hb : (rn φ g).op.eval ((rn φ g).inputs.map fun i => W'.getD i false) =
        g.op.eval (g.inputs.map fun i => W.getD i false) := by
      simp only [rn, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (h4 i).symm
    apply ih
    · simp [stp]; omega
    · simp [stp]; omega
    · intro i hi
      rcases h3 i hi with h | h
      · exact Or.inl h
      · right; simp only [stp, List.length_append, List.length_singleton]; omega
    · intro i
      simp only [stp]
      rw [getD_app, getD_app, hb]
      by_cases hi : i < W.length
      · rw [if_pos hi]
        by_cases hn : i < n1
        · rcases h3 i hn with h | h
          · rw [if_pos (by omega)]; exact h4 i
          · rw [if_neg (show ¬ φ i < W'.length by omega),
              if_neg (show ¬ φ i = W'.length by omega), h4 i, List.getD_eq_default]; omega
        · have := hφ i (by omega)
          rw [if_pos (by omega)]; exact h4 i
      · have := hφ i (by omega)
        rw [if_neg hi, if_neg (show ¬ φ i < W'.length by omega)]
        by_cases he : i = W.length
        · rw [if_pos he, if_pos (show φ i = W'.length by omega)]
        · rw [if_neg he, if_neg (show ¬ φ i = W'.length by omega)]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ (n ≤ i ∧ i = n + v.val)) := by
  unfold oneEach
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp only [List.getElem_ofFn]
    by_cases hu : i = u.val
    · simp [hu, Fin.ext_iff]
    · have : ¬ (⟨i, h⟩ : Fin n) = u := fun e => hu (by rw [← e])
      simp [this, hu]; omega
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    by_cases h2 : i - n < m
    · rw [List.getD_eq_getElem _ _ (by simpa using h2)]
      simp only [List.getElem_ofFn]
      by_cases hv : i - n = v.val
      · have : (⟨i - n, h2⟩ : Fin m) = v := Fin.ext hv
        simp [this]; omega
      · have : ¬ (⟨i - n, h2⟩ : Fin m) = v := fun e => hv (by rw [← e])
        simp [this]; omega
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp; omega

/-- The renaming from the double crown inputs (4k wires) onto the crown inputs (2k wires). -/
def phi (k B : ℕ) (i : ℕ) : ℕ :=
  if i < 2 * k then (if i % 2 = 0 then i / 2 else B)
  else if i < 4 * k then (if (i - 2 * k) % 2 = 0 then k + (i - 2 * k) / 2 else B)
  else i - 2 * k

/-- The kept part of the double crown relabels onto the crown on `k + k` vertices. -/
theorem shrink (k s : ℕ)
    (h : RepSizeAtMost (fun u v : Fin (2 * k) =>
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k)) && decide (u.val % 2 = 0) &&
        decide (v.val % 2 = 0)) s) :
    RepSizeAtMost (fun u v : Fin k => decide (u ≠ v)) s := by
  obtain ⟨C, hC, hs, hr⟩ := h
  set B := 2 * k + C.gates.length with hBdef
  have hB : 2 * k ≤ B := by omega
  refine ⟨⟨C.gates.map (rn (phi k B)), phi k B C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have := hC g0 hg0
    simpa [rn] using this
  · simpa [Circuit.size] using hs
  · intro t t'
    have ht : 2 * t.val < 2 * k := by omega
    have ht' : 2 * t'.val < 2 * k := by omega
    have key := hr ⟨2 * t.val, ht⟩ ⟨2 * t'.val, ht'⟩
    have hx : (oneEach (⟨2 * t.val, ht⟩ : Fin (2 * k)) (⟨2 * t'.val, ht'⟩ : Fin (2 * k))).length
        = 2 * k + 2 * k := by simp [oneEach]
    have hy : (oneEach t t').length = k + k := by simp [oneEach]
    have R := relabel (2 * k + 2 * k) (k + k) (phi k B)
      (by intro i hi; unfold phi; rw [if_neg (by omega), if_neg (by omega)]; omega)
      C.gates (oneEach (⟨2 * t.val, ht⟩ : Fin (2 * k)) (⟨2 * t'.val, ht'⟩ : Fin (2 * k)))
      (oneEach t t') (by omega) (by omega)
      (by
        intro i hi
        unfold phi
        rw [hy]
        by_cases a : i < 2 * k
        · rw [if_pos a]; split_ifs <;> omega
        · rw [if_neg a, if_pos (by omega)]; split_ifs <;> omega)
      (by
        intro i
        rw [oneEach_getD, oneEach_getD]
        simp only [Fin.val_mk, decide_eq_decide]
        unfold phi
        by_cases a : i < 2 * k
        · rw [if_pos a]
          split_ifs with e <;> omega
        · rw [if_neg a]
          by_cases b : i < 4 * k
          · rw [if_pos b]
            split_ifs with e <;> omega
          · rw [if_neg b]
            omega)
      C.output
    have e1 : C.eval (oneEach (⟨2 * t.val, ht⟩ : Fin (2 * k)) (⟨2 * t'.val, ht'⟩ : Fin (2 * k))) =
        (C.gates.foldl stp
          (oneEach (⟨2 * t.val, ht⟩ : Fin (2 * k)) (⟨2 * t'.val, ht'⟩ : Fin (2 * k)))).getD
          C.output false := rfl
    show ((C.gates.map (rn (phi k B))).foldl stp (oneEach t t')).getD (phi k B C.output) false = _
    rw [← R, ← e1, key]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have hm : (2 * t.val + 1) % (2 * k) % 2 = 1 := by
      rcases Nat.lt_or_ge (2 * t.val + 1) (2 * k) with c | c
      · rw [Nat.mod_eq_of_lt c]; omega
      · have : 2 * t.val + 1 = 2 * k := by omega
        omega
    have hne : 2 * t'.val ≠ (2 * t.val + 1) % (2 * k) := by
      intro e
      have : 2 * t'.val % 2 = (2 * t.val + 1) % (2 * k) % 2 := by rw [e]
      omega
    by_cases q : t = t'
    · subst q; simp
    · have : t.val ≠ t'.val := fun e => q (Fin.ext e)
      simp [q, hne]; omega

theorem count_rows (k : ℕ) (hk : 2 ≤ k) :
    (Finset.univ.filter (fun a : Fin (2 * k) => ∃ b : Fin (2 * k),
      decide (b.val ≠ a.val ∧ b.val ≠ (a.val + 1) % (2 * k)) = true ∧
      ∃ a' : Fin (2 * k), decide (b.val ≠ a'.val ∧ b.val ≠ (a'.val + 1) % (2 * k)) = false)).card
      = 2 * k := by
  rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
  intro a _
  have h2 : (a.val + 2) % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
  refine ⟨⟨(a.val + 2) % (2 * k), h2⟩, ?_, ⟨(a.val + 2) % (2 * k), h2⟩, by simp⟩
  have ha := a.isLt
  simp only [decide_eq_true_eq]
  rcases Nat.lt_or_ge (a.val + 2) (2 * k) with c | c
  · rw [Nat.mod_eq_of_lt c]
    rcases Nat.lt_or_ge (a.val + 1) (2 * k) with d | d
    · rw [Nat.mod_eq_of_lt d]; omega
    · omega
  · have e : (a.val + 2) % (2 * k) = a.val + 2 - 2 * k := by
      rw [Nat.mod_eq_sub_mod c, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    rcases Nat.lt_or_ge (a.val + 1) (2 * k) with d | d
    · rw [Nat.mod_eq_of_lt d]; omega
    · have e2 : (a.val + 1) % (2 * k) = a.val + 1 - 2 * k := by
        rw [Nat.mod_eq_sub_mod d, Nat.mod_eq_of_lt (by omega)]
      rw [e2]; omega

theorem count_cols (k : ℕ) (hk : 2 ≤ k) :
    (Finset.univ.filter (fun b : Fin (2 * k) => ∃ a : Fin (2 * k),
      decide (b.val ≠ a.val ∧ b.val ≠ (a.val + 1) % (2 * k)) = true ∧
      ∃ b' : Fin (2 * k), decide (b'.val ≠ a.val ∧ b'.val ≠ (a.val + 1) % (2 * k)) = false)).card
      = 2 * k := by
  rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
  intro b _
  have h2 : (b.val + 2) % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
  refine ⟨⟨(b.val + 2) % (2 * k), h2⟩, ?_, ⟨(b.val + 2) % (2 * k), h2⟩, by simp⟩
  have hb := b.isLt
  simp only [decide_eq_true_eq]
  rcases Nat.lt_or_ge (b.val + 3) (2 * k) with c | c
  · rw [Nat.mod_eq_of_lt (by omega : b.val + 2 < 2 * k)]
    rw [Nat.mod_eq_of_lt (by omega : b.val + 2 + 1 < 2 * k)]; omega
  · rcases Nat.lt_or_ge (b.val + 2) (2 * k) with d | d
    · rw [Nat.mod_eq_of_lt d]
      have e2 : (b.val + 2 + 1) % (2 * k) = b.val + 3 - 2 * k := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e2]; omega
    · have e : (b.val + 2) % (2 * k) = b.val + 2 - 2 * k := by
        rw [Nat.mod_eq_sub_mod d, Nat.mod_eq_of_lt (by omega)]
      rw [e]
      rw [Nat.mod_eq_of_lt (by omega : b.val + 2 - 2 * k + 1 < 2 * k)]; omega

theorem evens_card (k : ℕ) :
    (Finset.univ.filter (fun u : Fin (2 * k) => u.val % 2 = 0)).card ≤ k := by
  have : Finset.univ.filter (fun u : Fin (2 * k) => u.val % 2 = 0) ⊆
      (Finset.univ : Finset (Fin k)).image (fun t => (⟨2 * t.val, by omega⟩ : Fin (2 * k))) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨u.val / 2, by omega⟩, Fin.ext (by simp; omega)⟩
  calc _ ≤ _ := Finset.card_le_card this
    _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by simp

theorem main (k s : ℕ) (hk : 2 ≤ k)
    (h : RepSizeAtMost (fun u v : Fin (2 * k) =>
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k))) s) : 5 * k - 3 ≤ s := by
  set R := Finset.univ.filter (fun u : Fin (2 * k) => u.val % 2 = 0)
  have hev : ∀ u : Fin (2 * k), u.val % 2 = 0 → u ∈ R := by
    intro u hu; simp [R, hu]
  obtain ⟨s', hs', hle⟩ := PEqualNP.MetaComplexity.RepInduced.induced (2 * k) (2 * k) s
    (fun u v : Fin (2 * k) => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k))) R R
    (by
      intro u hu
      exact ⟨u, hu, by simp⟩)
    (by
      intro v hv
      exact ⟨v, hv, by simp⟩)
    (by
      refine ⟨⟨0, by omega⟩, hev _ (by simp), ⟨2, by omega⟩, hev _ (by simp), ?_⟩
      simp only [decide_eq_true_eq]
      rw [Nat.mod_eq_of_lt (by omega)]; omega)
    h
  rw [count_rows k hk, count_cols k hk] at hle
  have c1 := (Finset.card_filter_le R (fun a => ∃ b ∈ R, decide (b.val ≠ a.val ∧
    b.val ≠ (a.val + 1) % (2 * k)) = true)).trans (evens_card k)
  have c2 := (Finset.card_filter_le R (fun b => ∃ a ∈ R, decide (b.val ≠ a.val ∧
    b.val ≠ (a.val + 1) % (2 * k)) = true)).trans (evens_card k)
  have hs2 : RepSizeAtMost (fun u v : Fin (2 * k) =>
      decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k)) && decide (u.val % 2 = 0) &&
        decide (v.val % 2 = 0)) s' := by
    have e : (fun u v : Fin (2 * k) =>
        decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k)) && decide (u ∈ R) &&
          decide (v ∈ R)) = (fun u v : Fin (2 * k) =>
        decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k)) && decide (u.val % 2 = 0) &&
          decide (v.val % 2 = 0)) := by
      funext u v; simp [R]
    rw [← e]; exact hs'
  have hc := PEqualNP.Outside.L_meta_7626 k s' (shrink k s' hs2)
  omega

end PEqualNP.Outside.L_meta_17365

theorem PEqualNP.Outside.L_meta_17365 : ∀ k s : ℕ, 2 ≤ k → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (2 * k) => decide (v.val ≠ u.val ∧ v.val ≠ (u.val + 1) % (2 * k))) s → 5 * k - 3 ≤ s :=
  fun k s hk h => PEqualNP.Outside.L_meta_17365.main k s hk h
