import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5399_aux

open PEqualNP.CircuitLowerBounds

theorem fold_len (f : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ d : List Bool, (gs.foldl (fun w g => w ++ [f w g]) d).length = d.length + gs.length := by
  induction gs with
  | nil => intro d; simp
  | cons g gs ih => intro d; simp only [List.foldl_cons]; rw [ih]; simp; omega

theorem fold_pre (f : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ d : List Bool, ∀ i, i < d.length →
      (gs.foldl (fun w g => w ++ [f w g]) d).getD i false = d.getD i false := by
  induction gs with
  | nil => intro d i _; simp
  | cons g gs ih =>
    intro d i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp; omega), List.getD_append _ _ _ _ hi]

theorem cut (X : ℕ) (gs : List Gate) :
    ∀ d1 d2 r : List Bool, d1.length = d2.length → r.length = d1.length →
      (∀ i, i ≠ X → r.getD i false = false → d1.getD i false = d2.getD i false) →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d1).getD X false =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d2).getD X false →
      ∀ i, i ≠ X →
        (gs.foldl (fun (d : List Bool) (g : Gate) =>
            d ++ [decide (d.length ≠ X) && g.inputs.any fun i => d.getD i false]) r).getD i false = false →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d1).getD i false =
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) d2).getD i false := by
  induction gs with
  | nil => intro d1 d2 r _ _ hinv _ i hi hr; simpa using hinv i hi (by simpa using hr)
  | cons g gs ih =>
    intro d1 d2 r hl hr hinv hX
    simp only [List.foldl_cons] at hX ⊢
    apply ih
    · simp [hl]
    · simp [hr]
    · intro i hi hri
      have hXv : ∀ j ∈ g.inputs, r.getD j false = false → d1.getD j false = d2.getD j false := by
        intro j _ hj
        by_cases hjX : j = X
        · subst hjX
          by_cases hlt : j < d1.length
          · have e1 := fold_pre (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) gs
              (d1 ++ [g.op.eval (g.inputs.map fun i => d1.getD i false)]) j (by simp; omega)
            have e2 := fold_pre (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) gs
              (d2 ++ [g.op.eval (g.inputs.map fun i => d2.getD i false)]) j (by simp; omega)
            rw [e1, e2, List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hl ▸ hlt)] at hX
            exact hX
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · exact hinv j hjX hj
      rcases Nat.lt_trichotomy i d1.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ (hr ▸ hlt)] at hri
        rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact hinv i hi hri
      · subst heq
        rw [← hr, List.getD_append_right _ _ _ _ (le_refl _)] at hri
        rw [List.getD_append_right _ _ _ _ (le_refl _), hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero] at hri ⊢
        have hne : decide (r.length ≠ X) = true := by
          rw [hr]; exact decide_eq_true hi
        rw [hne, Bool.true_and, List.any_eq_false] at hri
        congr 1
        apply List.map_congr_left
        intro j hj
        exact hXv j hj (by simpa using hri j hj)
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · exact hX

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w1 w2 : List Bool, w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD i false = true := by
  induction gs with
  | nil => intro w1 w2 _ h; simpa using h
  | cons g gs ih =>
    intro w1 w2 hl h
    simp only [List.foldl_cons]
    apply ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    · simp [hl]
    · have hv : g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
          g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
        rcases hgs g (List.mem_cons_self) with ho | ho <;> rw [ho] <;> simp only [GateOp.eval]
        · simp only [List.all_eq_true, List.mem_map, id]
          rintro hall _ ⟨a, ha, rfl⟩
          exact h a (hall _ ⟨a, ha, rfl⟩)
        · simp only [List.any_eq_true, List.mem_map, id]
          rintro ⟨_, ⟨a, ha, rfl⟩, hb⟩
          exact ⟨_, ⟨a, ha, rfl⟩, h a hb⟩
      intro i hi
      rcases Nat.lt_trichotomy i w1.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h i hi
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
        rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp at hi ⊢
        exact hv hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact absurd hi (by simp)

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (a c : Fin n) (X : ℕ)
    (hAO : PEqualNP.ReadK.AndOrFanInTwo C)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (hac : G.Adj a c)
    (hcut : (C.gates.foldl (fun (d : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
        d ++ [decide (d.length ≠ X) && g.inputs.any fun i => d.getD i false])
        (List.ofFn fun i : Fin n => decide (i = a ∧ i.val ≠ X))).getD C.output false = false)
    (J : Finset (Fin n)) (hJ : ∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v) (hcJ : c ∈ J) :
    PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) = false ∧
      PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) = true := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := hAO.1
  have hmono : PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) = true →
      PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) = true := by
    unfold PEqualNP.CleanedNonEdge.wireVal Circuit.wires
    apply fold_mono C.gates hops _ _ (by simp)
    intro i hi
    by_cases hn : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hn)] at hi ⊢
      simp only [List.getElem_ofFn, PEqualNP.ReadK.setInput, decide_eq_true_eq] at hi ⊢
      exact Finset.mem_insert_of_mem hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)
  have hout1 : PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.ReadK.setInput J) = false := by
    rw [hF]
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_false_iff_not, not_exists, not_and]
    intro u v huv hu hv
    simp only [PEqualNP.ReadK.setInput, decide_eq_true_eq] at hu hv
    exact hJ u hu v hv huv
  have hout2 : PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.ReadK.setInput (insert a J)) = true := by
    rw [hF]
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    right
    refine ⟨a, c, hac, ?_, ?_⟩ <;> simp [PEqualNP.ReadK.setInput, hcJ]
  have key : PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) =
      PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) →
      PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.ReadK.setInput J) =
      PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.ReadK.setInput (insert a J)) := by
    intro hX
    unfold PEqualNP.CleanedNonEdge.wireVal at hX
    unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
    by_cases ho : C.output = X
    · rw [ho]; exact hX
    unfold Circuit.wires at hX ⊢
    apply cut X C.gates _ _ _ (by simp) (by simp) _ hX C.output ho hcut
    intro i hi hri
    by_cases hn : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hn)] at hri ⊢
      rw [List.getD_eq_getElem _ _ (by simpa using hn)]
      simp only [List.getElem_ofFn, PEqualNP.ReadK.setInput] at hri ⊢
      have hia : (⟨i, hn⟩ : Fin n) ≠ a := by
        intro h
        apply hi
        by_contra hne
        rw [decide_eq_false_iff_not] at hri
        exact hri ⟨h, by simpa using hne⟩
      simp [Finset.mem_insert, hia]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  rcases hv1 : PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) <;>
    rcases hv2 : PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J))
  · have := key (by rw [hv1, hv2]); rw [hout1, hout2] at this; exact absurd this (by simp)
  · exact ⟨rfl, rfl⟩
  · exact absurd (hmono hv1) (by rw [hv2]; simp)
  · have := key (by rw [hv1, hv2]); rw [hout1, hout2] at this; exact absurd this (by simp)

end PEqualNP.Outside.L_meta_5399_aux

set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_5399 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (a c : Fin n) (X : ℕ), PEqualNP.ReadK.AndOrFanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → G.Adj a c → (C.gates.foldl (fun (d : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) => d ++ [decide (d.length ≠ X) && g.inputs.any fun i => d.getD i false]) (List.ofFn fun i : Fin n => decide (i = a ∧ i.val ≠ X))).getD C.output false = false → ∀ J : Finset (Fin n), (∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v) → c ∈ J → PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput J) = false ∧ PEqualNP.CleanedNonEdge.wireVal n C X (PEqualNP.ReadK.setInput (insert a J)) = true := by
  intro n G _ C a c X hAO _ hF hac hcut J hJ hcJ
  exact PEqualNP.Outside.L_meta_5399_aux.main n G C a c X hAO hF hac hcut J hJ hcJ
