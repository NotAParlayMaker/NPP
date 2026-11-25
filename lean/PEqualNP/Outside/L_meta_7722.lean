import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7722_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem fold_inv (gs : List Gate) (k : ℕ) (hk : ∀ g ∈ gs, k ∉ g.inputs) :
    ∀ (w w' : List Bool), w.length = w'.length →
      (∀ i, i ≠ k → w.getD i false = w'.getD i false) →
      ∀ i, i ≠ k →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
          = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w').getD i false := by
  induction gs with
  | nil => intro w w' _ h i hi; exact h i hi
  | cons g gs ih =>
    intro w w' hl h
    have hb : g.op.eval (g.inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (by rintro rfl; exact hk g (by simp) hi)
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hk g' (by simp [hg']))
    · simp [hl]
    · intro i hi
      have h1 := h i hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append, hl] at h1 ⊢
      split_ifs
      · exact h1
      · simp only [List.getD_eq_getElem?_getD] at hb
        rw [hb]

theorem eval_inv (C : Circuit) (k : ℕ) (hk : ∀ g ∈ C.gates, k ∉ g.inputs) (ho : C.output ≠ k)
    (w w' : List Bool) (hl : w.length = w'.length)
    (h : ∀ i, i ≠ k → w.getD i false = w'.getD i false) : C.eval w = C.eval w' :=
  fold_inv C.gates k hk w w' hl h C.output ho

def readSet (C : Circuit) : Finset ℕ :=
  (C.gates.flatMap (fun g => g.inputs)).toFinset ∪ {C.output}

theorem flat_len (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap (fun g => g.inputs)).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have h1 := h g (by simp)
    have h2 := ih (fun g' hg' => h g' (by simp [hg']))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem readSet_card (C : Circuit) (h : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (readSet C).card ≤ 2 * C.size + 1 := by
  unfold readSet Circuit.size
  have h1 := Finset.card_union_le (C.gates.flatMap (fun g => g.inputs)).toFinset {C.output}
  have h2 := List.toFinset_card_le (C.gates.flatMap (fun g => g.inputs))
  have h3 := flat_len C.gates h
  simp only [Finset.card_singleton] at h1
  omega

theorem ess (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (v w : Fin n) (hvw : G.Adj v w) : v.val ∈ readSet C := by
  by_contra hv
  have hk : ∀ g ∈ C.gates, v.val ∉ g.inputs := by
    intro g hg hin
    apply hv
    unfold readSet
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_flatMap]
    exact Or.inl ⟨g, hg, hin⟩
  have ho : C.output ≠ v.val := by
    intro h
    apply hv
    unfold readSet
    simp [h]
  have he := eval_inv C v.val hk ho (List.ofFn (fun u : Fin n => decide (u = v ∨ u = w)))
    (List.ofFn (fun u : Fin n => decide (u = w))) (by simp) (by
      intro i hi
      simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      split_ifs with hlt
      · have : (⟨i, hlt⟩ : Fin n) ≠ v := by
          intro h
          apply hi
          rw [← h]
        simp [this]
      · rfl)
  rw [hC, hC] at he
  have h1 : graphFun G ∅ (fun u : Fin n => decide (u = v ∨ u = w)) = true := by
    unfold graphFun
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨v, w, hvw, by simp, by simp⟩
  have h2 : graphFun G ∅ (fun u : Fin n => decide (u = w)) = false := by
    unfold graphFun
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq]
    refine ⟨by simp, ?_⟩
    rintro ⟨a, b, hab, ha, hb⟩
    subst ha
    subst hb
    exact hab.ne rfl
  rw [h1, h2] at he
  exact Bool.noConfusion he

end PEqualNP.Outside.L_meta_7722_aux

open PEqualNP.Outside.L_meta_7722_aux in
theorem PEqualNP.Outside.L_meta_7722 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1 → Bool), x4.eval (List.ofFn x5) = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ x5) → (∀ x6 ∈ x4.gates, x6.inputs.length ≤ (2 : ℕ)) → ∀ (x7 : Finset (Sym2 (Fin x1))), (∀ x8 ∈ x7, ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x2.degree x10 ≤ (3 : ℕ) ∧ x8 = s(x10, x11)) → x7.card ≤ (3 : ℕ) * ((2 : ℕ) * x4.size + (1 : ℕ)) := by
  intro n G _ C hC hg E hE
  classical
  let T : Finset (Fin n) := Finset.univ.filter (fun v => v.val ∈ readSet C ∧ G.degree v ≤ 3)
  have hT : T.card ≤ 2 * C.size + 1 := by
    refine le_trans ?_ (readSet_card C hg)
    apply Finset.card_le_card_of_injOn (fun v => v.val)
    · intro v hv
      exact (Finset.mem_filter.mp hv).2.1
    · intro a _ b _ hab
      exact Fin.ext hab
  have hsub : E ⊆ T.biUnion (fun v => (G.neighborFinset v).image (fun w => s(v, w))) := by
    intro e he
    obtain ⟨v, w, hvw, hd, rfl⟩ := hE e he
    simp only [Finset.mem_biUnion, Finset.mem_image, SimpleGraph.mem_neighborFinset]
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ess n G C hC v w hvw, hd⟩, w, hvw, rfl⟩
  calc E.card ≤ (T.biUnion (fun v => (G.neighborFinset v).image (fun w => s(v, w)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ v ∈ T, ((G.neighborFinset v).image (fun w => s(v, w))).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ T, 3 := by
        apply Finset.sum_le_sum
        intro v hv
        refine le_trans Finset.card_image_le ?_
        rw [SimpleGraph.card_neighborFinset_eq_degree]
        exact (Finset.mem_filter.mp hv).2.2
    _ = T.card * 3 := by simp
    _ ≤ 3 * (2 * C.size + 1) := by omega
