import Mathlib
import PEqualNP.Defs

/- The helper lemmas up to wiresFrom_mono are copied from the checked file L_meta_1018.lean of this repository (Apache-2.0). -/
namespace PEqualNP.Outside.L_meta_6893

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma cmono (n : ℕ) (C : Circuit) (hM : Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ w, x w = true → y w = true) (h : circuitFun n C x = true) :
    circuitFun n C y = true := by
  have h' : (wiresFrom C.gates (List.ofFn x)).getD C.output false = true := h
  show (wiresFrom C.gates (List.ofFn y)).getD C.output false = true
  refine wiresFrom_mono C.gates (fun g hg => by simpa using (hM g hg).1) (List.ofFn x)
    (List.ofFn y) (by simp) ?_ _ h'
  intro i hi
  by_cases hlt : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hi ⊢
    simp only [List.getElem_ofFn] at hi ⊢
    exact hxy _ hi
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hlt)] at hi
    exact Bool.noConfusion hi

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hM : Monotone2 C)
    (hE : ∀ u v : Fin n, G.Adj u v → circuitFun n C (pairInput u v) = true)
    (hI : ∀ I : Finset (Fin n), Maximal (fun J : Finset (Fin n) => G.IsIndepSet ↑J) I →
      circuitFun n C (fun w => decide (w ∈ I)) = false) :
    circuitFun n C = graphFun G ∅ := by
  funext x
  unfold graphFun
  by_cases h : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  · obtain ⟨u, v, huv, hu, hv⟩ := h
    have h1 := cmono n C hM (pairInput u v) x (by
      intro w hw
      simp only [pairInput, decide_eq_true_eq] at hw
      rcases hw with rfl | rfl <;> assumption) (hE u v huv)
    have hex : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := ⟨u, v, huv, hu, hv⟩
    rw [h1, decide_eq_true hex]
    simp
  · have hind : G.IsIndepSet ↑(Finset.univ.filter (fun w => x w = true)) := by
      intro a ha b hb _ hab
      exact h ⟨a, b, hab, by simpa using ha, by simpa using hb⟩
    obtain ⟨I, hsub, hmax⟩ :=
      Finite.exists_le_maximal (p := fun J : Finset (Fin n) => G.IsIndepSet ↑J) hind
    have hf := hI I hmax
    have hx : circuitFun n C x = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      have h2 := cmono n C hM x (fun w => decide (w ∈ I)) (by
        intro w hw
        simp only [decide_eq_true_eq]
        exact hsub (by simp [hw])) hc
      rw [hf] at h2
      exact Bool.noConfusion h2
    rw [hx, decide_eq_false h]
    simp

end PEqualNP.Outside.L_meta_6893

theorem PEqualNP.Outside.L_meta_6893 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 x7 : Fin x1), x2.Adj x6 x7 → PEqualNP.MetaComplexity.circuitFun x1 x4 (PEqualNP.EdgeOwnership.pairInput x6 x7) = Bool.true) → (∀ (x7 : Finset (Fin x1)), Maximal (fun (x8 : Finset (Fin x1)) => x2.IsIndepSet ↑x8) x7 → (PEqualNP.MetaComplexity.circuitFun x1 x4 fun (x9 : Fin x1) => Decidable.decide (x9 ∈ x7)) = Bool.false) → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ := by
  intro n G _ C hM hE hI
  exact PEqualNP.Outside.L_meta_6893.main n G C hM hE hI
