import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1798

open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
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

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getElem?_eq_none (by simpa using h)]
    rfl

theorem len_fold : ∀ (gs : List Gate) (W : List Bool),
    (gs.foldl stp W).length = W.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro W; simp
  | cons g gs ih =>
    intro W
    rw [List.foldl_cons, ih]
    simp [stp]
    omega

theorem pre_stable : ∀ (gs : List Gate) (W : List Bool) (i : ℕ), i < W.length →
    (gs.foldl stp W).getD i false = W.getD i false := by
  intro gs
  induction gs with
  | nil => intro W i _; rfl
  | cons g gs ih =>
    intro W i hi
    rw [List.foldl_cons, ih (stp W g) i (by simp [stp]; omega)]
    simp only [stp, getD_snoc]
    rw [if_neg (by omega)]

theorem gate_val (gs : List Gate) (x : List Bool) (j a b : ℕ)
    (hj : gs[j]? = some ⟨GateOp.and, [a, b]⟩) (ha : a < x.length + j) (hb : b < x.length + j) :
    (gs.foldl stp x).getD (x.length + j) false
      = ((gs.foldl stp x).getD a false && (gs.foldl stp x).getD b false) := by
  obtain ⟨hjl, hg⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨pre, post, hs, hpl⟩ : ∃ pre post : List Gate,
      gs = pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post ∧ pre.length = j := by
    refine ⟨gs.take j, gs.drop (j + 1), ?_, ?_⟩
    · rw [← hg, ← List.drop_eq_getElem_cons hjl, List.take_append_drop]
    · rw [List.length_take]
      omega
  subst hs
  rw [List.foldl_append, List.foldl_cons]
  have hWl : (pre.foldl stp x).length = x.length + j := by rw [len_fold, hpl]
  rw [pre_stable _ _ _ (by simp [stp]; omega), pre_stable _ _ a (by simp [stp]; omega),
    pre_stable _ _ b (by simp [stp]; omega)]
  simp only [stp, getD_snoc]
  rw [if_pos hWl.symm, if_neg (by omega), if_neg (by omega)]
  simp [GateOp.eval]

theorem app_mono (l1 l1' l2 : List Bool) (hl : l1.length = l1'.length)
    (H : ∀ i, l1.getD i false = true → l1'.getD i false = true) :
    ∀ i, (l1 ++ l2).getD i false = true → (l1' ++ l2).getD i false = true := by
  intro i
  simp only [List.getD_eq_getElem?_getD] at H ⊢
  by_cases h : i < l1.length
  · rw [List.getElem?_append_left h, List.getElem?_append_left (hl ▸ h)]
    exact H i
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hl]
    exact id

theorem rlen (P L : ℕ) (w : Fin L) (pts : Fin P → Bool) :
    (restrictInput P L w pts).length = P + L := by
  simp [restrictInput]

theorem wv_and (P L : ℕ) (C : Circuit) (j a b : ℕ)
    (hj : C.gates[j]? = some ⟨GateOp.and, [a, b]⟩) (ha : a < P + L + j) (hb : b < P + L + j)
    (w : Fin L) (pts : Fin P → Bool) :
    wireVal C (restrictInput P L w pts) (P + L + j)
      = (wireVal C (restrictInput P L w pts) a && wireVal C (restrictInput P L w pts) b) := by
  have h := gate_val C.gates (restrictInput P L w pts) j a b hj
    (by rw [rlen]; exact ha) (by rw [rlen]; exact hb)
  rw [rlen] at h
  exact h

theorem wv_mono (P L : ℕ) (C : Circuit) (hC : IsMonotoneCircuit C) (w : Fin L)
    (p1 p2 : Fin P → Bool) (H : ∀ p, p1 p = true → p2 p = true) (g : ℕ)
    (h : wireVal C (restrictInput P L w p1) g = true) :
    wireVal C (restrictInput P L w p2) g = true := by
  refine mono C.gates (restrictInput P L w p1) (restrictInput P L w p2)
    (by rw [rlen, rlen]) hC ?_ g h
  unfold restrictInput
  apply app_mono _ _ _ (by simp)
  intro i
  rw [ofFn_getD, ofFn_getD]
  split_ifs
  · exact H _
  · exact id

end PEqualNP.Outside.L_meta_1798

open PEqualNP.Outside.L_meta_1798 in
theorem PEqualNP.Outside.L_meta_1798 : ∀ (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C → ∀ (j a b : ℕ), C.gates[j]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ → a < P + L + j → b < P + L + j → ∀ w : Fin L, PEqualNP.LowMerge.IsLow P L inc C (P + L + j) w → PEqualNP.LowMerge.IsLow P L inc C a w ∨ PEqualNP.LowMerge.IsLow P L inc C b w := by
  intro P L inc C hC j a b hj ha hb w hlow
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hna, hnb⟩ := hcon
  unfold PEqualNP.LowMerge.IsLow at hna hnb
  rw [not_forall] at hna hnb
  obtain ⟨p1, h1⟩ := hna
  obtain ⟨p2, h2⟩ := hnb
  rw [Classical.not_imp] at h1 h2
  obtain ⟨h1, hl1⟩ := h1
  obtain ⟨h2, hl2⟩ := h2
  have key := hlow (fun p => p1 p || p2 p) (by
    rw [wv_and P L C j a b hj ha hb w]
    rw [wv_mono P L C hC w p1 _ (fun p hp => by simp [hp]) a h1,
      wv_mono P L C hC w p2 _ (fun p hp => by simp [hp]) b h2]
    rfl)
  unfold PEqualNP.LowMerge.lineSum at key hl1 hl2
  rw [decide_eq_true_eq] at key hl1 hl2
  obtain ⟨p, hp, hpp⟩ := key
  rw [Bool.or_eq_true] at hpp
  rcases hpp with hpp | hpp
  · exact hl1 ⟨p, hp, hpp⟩
  · exact hl2 ⟨p, hp, hpp⟩
