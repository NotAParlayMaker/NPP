import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1573

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

lemma ofFn_getD (z : Fin 13 → Bool) (j : ℕ) (hj : j < 13) :
    (List.ofFn z).getD j false = z ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_ofFn]

-- An AND/OR list is monotone: more true inputs never turn a wire false.
lemma eval_mono (gs : List Gate) (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (j : ℕ) (x y : Fin 13 → Bool) (hle : ∀ w, x w = true → y w = true)
    (h : Circuit.eval ⟨gs, j⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gs, j⟩ (List.ofFn y) = true := by
  refine wiresFrom_mono gs hmono (List.ofFn x) (List.ofFn y) (by simp) ?_ j h
  intro i hi
  by_cases hi13 : i < 13
  · rw [ofFn_getD x i hi13] at hi
    rw [ofFn_getD y i hi13]
    exact hle _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact Bool.noConfusion hi

-- Every test input of a line l lies below the complement of line m or of line l2.
lemma comb1 : ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)),
    ∀ p ∈ ({l, l + 1, l + 3, l + 9} : Finset (Fin 13)), ∀ l2 ∈ ({4, 10, 12} : Finset (Fin 13)),
    l2 ≠ l →
    (∀ v : Fin 13, (v = p ∨ (p ≠ 0 ∧ v = 1)) → v ∉ ({m, m + 1, m + 3, m + 9} : Finset (Fin 13))) ∨
    (∀ v : Fin 13, (v = p ∨ (p ≠ 0 ∧ v = 1)) → v ∉ ({l2, l2 + 1, l2 + 3, l2 + 9} : Finset (Fin 13))) := by
  decide

lemma comb2 : ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)),
    ∀ p ∈ ({m, m + 1, m + 3, m + 9} : Finset (Fin 13)), ∀ m2 ∈ ({1, 5, 11} : Finset (Fin 13)),
    m2 ≠ m →
    (∀ v : Fin 13, (v = p ∨ (p ≠ 1 ∧ v = 0)) → v ∉ ({l, l + 1, l + 3, l + 9} : Finset (Fin 13))) ∨
    (∀ v : Fin 13, (v = p ∨ (p ≠ 1 ∧ v = 0)) → v ∉ ({m2, m2 + 1, m2 + 3, m2 + 9} : Finset (Fin 13))) := by
  decide

end PEqualNP.Outside.L_meta_1573

theorem PEqualNP.Outside.L_meta_1573 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), ∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false → (∃ p ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 0 ∧ v = 1)))) = true) →
      ∀ l' ∈ ({4, 10, 12} : Finset (Fin 13)), l' ≠ l → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l'))) = true) ∧
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), ∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false → (∃ p ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ (p ≠ 1 ∧ v = 0)))) = true) →
      ∀ m' ∈ ({1, 5, 11} : Finset (Fin 13)), m' ≠ m → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m'))) = true) := by
  intro L hL gates g hgates
  have hmono : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => (hgates g hg).1
  constructor
  · intro m hm l hl hfalse ⟨p, hp, htrue⟩ l' hl' hne
    rw [hL] at hp
    rcases PEqualNP.Outside.L_meta_1573.comb1 m hm l hl p hp l' hl' hne with h | h
    · have hm' := PEqualNP.Outside.L_meta_1573.eval_mono gates hmono g _
        (fun v : Fin 13 => decide (v ∉ L m)) (fun v hv => by
          rw [hL]
          simp only [decide_eq_true_eq] at hv ⊢
          exact h v hv) htrue
      rw [hfalse] at hm'
      exact absurd hm' Bool.false_ne_true
    · exact PEqualNP.Outside.L_meta_1573.eval_mono gates hmono g _ _ (fun v hv => by
        rw [hL]
        simp only [decide_eq_true_eq] at hv ⊢
        exact h v hv) htrue
  · intro l hl m hm hfalse ⟨p, hp, htrue⟩ m' hm' hne
    rw [hL] at hp
    rcases PEqualNP.Outside.L_meta_1573.comb2 l hl m hm p hp m' hm' hne with h | h
    · have hl' := PEqualNP.Outside.L_meta_1573.eval_mono gates hmono g _
        (fun v : Fin 13 => decide (v ∉ L l)) (fun v hv => by
          rw [hL]
          simp only [decide_eq_true_eq] at hv ⊢
          exact h v hv) htrue
      rw [hfalse] at hl'
      exact absurd hl' Bool.false_ne_true
    · exact PEqualNP.Outside.L_meta_1573.eval_mono gates hmono g _ _ (fun v hv => by
        rw [hL]
        simp only [decide_eq_true_eq] at hv ⊢
        exact h v hv) htrue
