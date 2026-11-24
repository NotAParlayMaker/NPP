import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1584

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
lemma eval_mono_ofFn {N : ℕ} (gates : List Gate) (g : ℕ)
    (hmono : ∀ g' ∈ gates, g'.op = GateOp.and ∨ g'.op = GateOp.or)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true)
    (h : Circuit.eval ⟨gates, g⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, g⟩ (List.ofFn y) = true := by
  have key := wiresFrom_mono gates hmono (List.ofFn x) (List.ofFn y) (by simp) (by
    intro i hi
    by_cases hlt : i < N
    · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hi
      rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
      simp only [List.getElem_ofFn] at hi ⊢
      exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hlt)] at hi
      exact Bool.noConfusion hi) g
  exact key h

end PEqualNP.Outside.L_meta_1584

theorem PEqualNP.Outside.L_meta_1584 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 2 ≤ m → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (a b : Fin N),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    a ∈ T0 → b ∈ T0 → a ≠ b → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin N => decide (v = a))) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin N => decide (v = b))) = true →
    ∀ s : Fin N, s ≠ i0 → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L s))) = true := by
  intro q m N L i0 T0 _ _ _ _ hint _ hT0 _ gates g a b hg ha hb hab hea heb s hs
  have hmono : ∀ g' ∈ gates, g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g'.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g' hg' => (hg g' hg').1
  have hor : a ∉ L s ∨ b ∉ L s := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    have hsub : ({a, b} : Finset (Fin N)) ⊆ L s ∩ L i0 := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hcon.1, hT0 ha⟩
      · exact Finset.mem_inter.mpr ⟨hcon.2, hT0 hb⟩
    have hc := Finset.card_le_card hsub
    rw [hint s i0 hs, Finset.card_pair hab] at hc
    omega
  rcases hor with h | h
  · refine PEqualNP.Outside.L_meta_1584.eval_mono_ofFn gates g hmono _ _ ?_ hea
    intro v hv
    have : v = a := by simpa using hv
    subst this
    simpa using h
  · refine PEqualNP.Outside.L_meta_1584.eval_mono_ofFn gates g hmono _ _ ?_ heb
    intro v hv
    have : v = b := by simpa using hv
    subst this
    simpa using h
