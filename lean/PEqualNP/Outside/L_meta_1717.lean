import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1717

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl stp x).getD C.output false := rfl

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

theorem eval_mono_fn {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (o : ℕ)
    (h : Circuit.eval ⟨gates, o⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  refine mono gates _ _ (by simp) hg ?_ o h
  intro i
  rw [ofFn_getD, ofFn_getD]
  split_ifs with hi
  · exact hxy _
  · exact id

theorem app_mono {N : ℕ} (X X' Y Y' : Finset (Fin N)) (hX : X ⊆ X') (hY : Y ⊆ Y') :
    ∀ v : Fin (N + N), Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ Y)) v = true →
      Fin.append (fun a => decide (a ∈ X')) (fun b => decide (b ∈ Y')) v = true := by
  intro v
  refine Fin.addCases ?_ ?_ v
  · intro i
    rw [Fin.append_left, Fin.append_left]
    intro h
    exact decide_eq_true (hX (of_decide_eq_true h))
  · intro i
    rw [Fin.append_right, Fin.append_right]
    intro h
    exact decide_eq_true (hY (of_decide_eq_true h))

theorem cf_mono {N : ℕ} (C : Circuit) (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (X X' Y Y' : Finset (Fin N)) (hX : X ⊆ X') (hY : Y ⊆ Y')
    (h : PEqualNP.MetaComplexity.circuitFun (N + N) C
      (Fin.append (fun a => decide (a ∈ X)) (fun b => decide (b ∈ Y))) = true) :
    PEqualNP.MetaComplexity.circuitFun (N + N) C
      (Fin.append (fun a => decide (a ∈ X')) (fun b => decide (b ∈ Y'))) = true :=
  eval_mono_fn C.gates hg _ _ (app_mono X X' Y Y' hX hY) C.output h

end PEqualNP.Outside.L_meta_1717

open PEqualNP.Outside.L_meta_1717 in
theorem PEqualNP.Outside.L_meta_1717 : ∀ (N82 K82 v82 : ℕ) (I82 : Fin N82 → Fin N82 → Prop) [DecidableRel I82] (Cs82 : Fin v82 → PEqualNP.CircuitLowerBounds.Circuit) (A82 : Finset (Fin v82)) (iz82 : Fin v82) (S82 W82 B82 : Finset (Fin N82)), (∀ i82 : Fin v82, (∀ g82 ∈ (Cs82 i82).gates, (g82.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g82.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g82.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N82 + N82) (Cs82 i82)) → iz82 ∈ A82 → Disjoint W82 B82 → (∀ p82 ∈ S82, ∀ l82 ∈ B82, ¬ I82 p82 l82) → (∀ X82 Y82 : Finset (Fin N82), X82 ⊆ S82 → Y82 ⊆ W82 → Y82.card ≤ K82 → (∀ p82a ∈ X82, ∀ l82a ∈ Y82, ¬ I82 p82a l82a) → ∃ i82a ∈ A82, PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 i82a) (Fin.append (fun a82 => decide (a82 ∈ X82)) (fun b82 => decide (b82 ∈ (Y82 ∪ B82)))) = false) → (∀ pz82 ∈ S82, ∀ T82 ⊆ W82, (∀ l82b ∈ T82, ¬ I82 pz82 l82b) → T82.card ≤ K82 → PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 iz82) (Fin.append (fun a82a => decide (a82a ∈ ({pz82} : Finset (Fin N82)))) (fun b82a => decide (b82a ∈ (T82 ∪ B82)))) = true → ∀ X82a Y82a : Finset (Fin N82), X82a ⊆ S82.filter (fun u82 => u82 ≠ pz82 ∧ ∀ l82c ∈ T82, ¬ I82 u82 l82c) → Y82a ⊆ W82.filter (fun l82d => ¬ I82 pz82 l82d ∧ l82d ∉ T82) → Y82a.card + T82.card ≤ K82 → (∀ p82b ∈ X82a, ∀ l82e ∈ Y82a, ¬ I82 p82b l82e) → ∃ i82b ∈ A82.erase iz82, PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 i82b) (Fin.append (fun a82b => decide (a82b ∈ X82a)) (fun b82b => decide (b82b ∈ (Y82a ∪ (T82 ∪ B82))))) = false) ∧ (∀ wz82 ∈ W82, ∀ Q82 ⊆ S82, (∀ p82c ∈ Q82, ¬ I82 p82c wz82) → PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 iz82) (Fin.append (fun a82c => decide (a82c ∈ Q82)) (fun b82c => decide (b82c ∈ (insert wz82 B82)))) = true → ∀ X82b Y82b : Finset (Fin N82), X82b ⊆ S82.filter (fun u82a => ¬ I82 u82a wz82 ∧ u82a ∉ Q82) → Y82b ⊆ W82.filter (fun l82f => l82f ≠ wz82 ∧ ∀ p82d ∈ Q82, ¬ I82 p82d l82f) → Y82b.card + 1 ≤ K82 → (∀ p82e ∈ X82b, ∀ l82g ∈ Y82b, ¬ I82 p82e l82g) → ∃ i82c ∈ A82.erase iz82, PEqualNP.MetaComplexity.circuitFun (N82 + N82) (Cs82 i82c) (Fin.append (fun a82d => decide (a82d ∈ X82b)) (fun b82d => decide (b82d ∈ (Y82b ∪ insert wz82 B82)))) = false) := by
  intro N K v I _ Cs A iz S W B hC hiz _ _ H
  have hg : ∀ i, ∀ g ∈ (Cs i).gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun i g hgm => ((hC i).1 g hgm).1
  refine ⟨?_, ?_⟩
  · intro pz hpz T hT hTI hTc hacc X Y hX hY hc hXY
    have hX1 : insert pz X ⊆ S := by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hpz
      · exact (Finset.mem_filter.1 (hX ha)).1
    have hY1 : Y ∪ T ⊆ W := by
      intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · exact (Finset.mem_filter.1 (hY ha)).1
      · exact hT ha
    have hc1 : (Y ∪ T).card ≤ K := le_trans (Finset.card_union_le _ _) hc
    have hI1 : ∀ p ∈ insert pz X, ∀ l ∈ Y ∪ T, ¬ I p l := by
      intro p hp l hl
      rcases Finset.mem_insert.1 hp with rfl | hp <;> rcases Finset.mem_union.1 hl with hl | hl
      · exact (Finset.mem_filter.1 (hY hl)).2.1
      · exact hTI l hl
      · exact hXY p hp l hl
      · exact (Finset.mem_filter.1 (hX hp)).2.2 l hl
    obtain ⟨i, hiA, hi⟩ := H _ _ hX1 hY1 hc1 hI1
    have hne : i ≠ iz := by
      intro he
      rw [he] at hi
      have h2 := cf_mono (Cs iz) (hg iz) {pz} (insert pz X) (T ∪ B) (Y ∪ T ∪ B)
        (by intro a ha; simp only [Finset.mem_singleton, Finset.mem_insert] at ha ⊢; tauto)
        (by intro a ha; simp only [Finset.mem_union] at ha ⊢; tauto) hacc
      exact absurd (hi.symm.trans h2) (by decide)
    refine ⟨i, Finset.mem_erase.2 ⟨hne, hiA⟩, ?_⟩
    by_contra hcon
    have h2 := cf_mono (Cs i) (hg i) X (insert pz X) (Y ∪ (T ∪ B)) (Y ∪ T ∪ B)
      (Finset.subset_insert _ _)
      (by intro a ha; simp only [Finset.mem_union] at ha ⊢; tauto)
      (Bool.eq_true_of_not_eq_false hcon)
    exact absurd (hi.symm.trans h2) (by decide)
  · intro wz hwz Q hQ hQI hacc X Y hX hY hc hXY
    have hX1 : X ∪ Q ⊆ S := by
      intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · exact (Finset.mem_filter.1 (hX ha)).1
      · exact hQ ha
    have hY1 : insert wz Y ⊆ W := by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hwz
      · exact (Finset.mem_filter.1 (hY ha)).1
    have hc1 : (insert wz Y).card ≤ K := le_trans (Finset.card_insert_le _ _) hc
    have hI1 : ∀ p ∈ X ∪ Q, ∀ l ∈ insert wz Y, ¬ I p l := by
      intro p hp l hl
      rcases Finset.mem_union.1 hp with hp | hp <;> rcases Finset.mem_insert.1 hl with rfl | hl
      · exact (Finset.mem_filter.1 (hX hp)).2.1
      · exact hXY p hp l hl
      · exact hQI p hp
      · exact (Finset.mem_filter.1 (hY hl)).2.2 p hp
    obtain ⟨i, hiA, hi⟩ := H _ _ hX1 hY1 hc1 hI1
    have hne : i ≠ iz := by
      intro he
      rw [he] at hi
      have h2 := cf_mono (Cs iz) (hg iz) Q (X ∪ Q) (insert wz B) (insert wz Y ∪ B)
        Finset.subset_union_right
        (by intro a ha; simp only [Finset.mem_union, Finset.mem_insert] at ha ⊢; tauto) hacc
      exact absurd (hi.symm.trans h2) (by decide)
    refine ⟨i, Finset.mem_erase.2 ⟨hne, hiA⟩, ?_⟩
    by_contra hcon
    have h2 := cf_mono (Cs i) (hg i) X (X ∪ Q) (Y ∪ insert wz B) (insert wz Y ∪ B)
      Finset.subset_union_left
      (by intro a ha; simp only [Finset.mem_union, Finset.mem_insert] at ha ⊢; tauto)
      (Bool.eq_true_of_not_eq_false hcon)
    exact absurd (hi.symm.trans h2) (by decide)
