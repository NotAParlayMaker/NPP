import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1654

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


lemma ofFn_mono {n : ℕ} (f g : Fin n → Bool) (h : ∀ u, f u = true → g u = true) :
    ∀ i, (List.ofFn f).getD i false = true → (List.ofFn g).getD i false = true := by
  intro i hi
  by_cases hlt : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
    simp only [List.getElem_ofFn] at hi ⊢
    exact h _ hi
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hlt)] at hi
    exact Bool.noConfusion hi

lemma wires_mono {n : ℕ} (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (f g : Fin n → Bool) (h : ∀ u, f u = true → g u = true) (i : ℕ) :
    (Circuit.wires ⟨gates, 0⟩ (List.ofFn f)).getD i false = true →
    (Circuit.wires ⟨gates, 0⟩ (List.ofFn g)).getD i false = true :=
  wiresFrom_mono gates hmono _ _ (by simp) (ofFn_mono f g h) i

end PEqualNP.Outside.L_meta_1654

theorem PEqualNP.Outside.L_meta_1654 : ∀ (n L : ℕ) (line : Fin L → Finset (Fin n)) (l : Fin L) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G K : ℕ) (I : Finset (Fin n)),
  (∀ p r : Fin n, p ≠ r → ∃! j : Fin L, p ∈ line j ∧ r ∈ line j) →
  (∀ j j' : Fin L, j ≠ j' → (line j ∩ line j').card = 1) →
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  (¬ ∃ X : Finset (Fin n), Disjoint X (line l) ∧
      (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD G false = true ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD K false = true) →
  Disjoint I (line l) →
  (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) →
  (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ I)))).getD K false = true →
  ∀ v : Fin n, v ∉ line l →
    (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u = v)))).getD G false = true →
    v ∉ I ∧ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ v ∈ line j := by
  
  intro n L line l gates G K I _ _ hgates _ hno hdisj harc hK v hv hG
  have hm : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => (hgates g hg).1
  have hvI : v ∉ I := by
    intro hvI
    apply hno
    refine ⟨I, hdisj, harc, ?_, hK⟩
    refine PEqualNP.Outside.L_meta_1654.wires_mono gates hm _ _ ?_ G hG
    intro u hu
    simp only [decide_eq_true_eq] at hu ⊢
    rw [hu]; exact hvI
  refine ⟨hvI, ?_⟩
  by_contra hcon
  have hc : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → ∀ j : Fin L, a ∈ line j → b ∈ line j → v ∉ line j := by
    intro a ha b hb hab j haj hbj hvj
    exact hcon ⟨a, ha, b, hb, hab, j, haj, hbj, hvj⟩
  apply hno
  refine ⟨insert v I, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_insert_left]
    exact ⟨hv, hdisj⟩
  · intro a ha b hb c hc' hab hac hbc hex
    obtain ⟨j, haj, hbj, hcj⟩ := hex
    rw [Finset.mem_insert] at ha hb hc'
    rcases ha with rfl | ha
    · have hb' : b ∈ I := by
        rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact hb
      have hc2 : c ∈ I := by
        rcases hc' with rfl | hc'
        · exact absurd rfl hac
        · exact hc'
      exact hc b hb' c hc2 hbc j hbj hcj haj
    · rcases hb with rfl | hb
      · have hc2 : c ∈ I := by
          rcases hc' with rfl | hc'
          · exact absurd rfl hbc
          · exact hc'
        exact hc a ha c hc2 hac j haj hcj hbj
      · rcases hc' with rfl | hc'
        · exact hc a ha b hb hab j haj hbj hcj
        · exact harc a ha b hb c hc' hab hac hbc ⟨j, haj, hbj, hcj⟩
  · refine PEqualNP.Outside.L_meta_1654.wires_mono gates hm _ _ ?_ G hG
    intro u hu
    simp only [decide_eq_true_eq] at hu ⊢
    rw [hu]; exact Finset.mem_insert_self _ _
  · refine PEqualNP.Outside.L_meta_1654.wires_mono gates hm _ _ ?_ K hK
    intro u hu
    simp only [decide_eq_true_eq] at hu ⊢
    exact Finset.mem_insert_of_mem hu
