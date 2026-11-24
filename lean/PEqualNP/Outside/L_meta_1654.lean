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

lemma ofFn_getD {n : ℕ} (z : Fin n → Bool) (j : ℕ) (hj : j < n) :
    (List.ofFn z).getD j false = z ⟨j, hj⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_ofFn]

lemma W_mono {n : ℕ} (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (j : ℕ)
    (x y : Fin n → Bool) (hle : ∀ w, x w = true → y w = true)
    (h : (wiresFrom gs (List.ofFn x)).getD j false = true) :
    (wiresFrom gs (List.ofFn y)).getD j false = true := by
  refine wiresFrom_mono gs hmono (List.ofFn x) (List.ofFn y) (by simp) ?_ j h
  intro i hi
  by_cases hin : i < n
  · rw [ofFn_getD x i hin] at hi
    rw [ofFn_getD y i hin]
    exact hle _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact Bool.noConfusion hi

end PEqualNP.Outside.L_meta_1654

theorem PEqualNP.Outside.L_meta_1654 :
    ∀ (n L : ℕ) (line : Fin L → Finset (Fin n)) (l : Fin L)
      (gates : List PEqualNP.CircuitLowerBounds.Gate) (G K : ℕ) (I : Finset (Fin n)),
      (∀ p r : Fin n, p ≠ r → ∃! j : Fin L, p ∈ line j ∧ r ∈ line j) →
      (∀ j j' : Fin L, j ≠ j' → (line j ∩ line j').card = 1) →
      (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g →
          ∀ i ∈ g.inputs, i < n + k) →
      (¬ ∃ X : Finset (Fin n), Disjoint X (line l) ∧
          (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c →
            ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩
            (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD G false = true ∧
          (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩
            (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD K false = true) →
      Disjoint I (line l) →
      (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, a ≠ b → a ≠ c → b ≠ c →
        ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) →
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩
        (List.ofFn (fun u : Fin n => decide (u ∈ I)))).getD K false = true →
      ∀ v : Fin n, v ∉ line l →
        (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩
          (List.ofFn (fun u : Fin n => decide (u = v)))).getD G false = true →
        v ∉ I ∧ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧
          ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ v ∈ line j := by
  intro n L line l gates G K I hspace hmeet hops href hnoarc hI_disj hI_arc hIK v hvoff hvG
  have hmono : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or :=
    fun g hg => (hops g hg).1
  have hvI : v ∉ I := by
    intro hv
    apply hnoarc
    refine ⟨I, hI_disj, hI_arc, ?_, hIK⟩
    have hle : ∀ w : Fin n, (decide (w = v) : Bool) = true →
        (decide (w ∈ I) : Bool) = true := by
      intro w hw
      rw [decide_eq_true_eq] at hw ⊢
      rw [hw]
      exact hv
    exact PEqualNP.Outside.L_meta_1654.W_mono gates hmono G _ _ hle hvG
  refine ⟨hvI, ?_⟩
  by_contra hcon
  apply hnoarc
  refine ⟨insert v I, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_insert_left]
    exact ⟨hvoff, hI_disj⟩
  · intro a ha b hb c hc hab hac hbc
    intro ⟨j, haj, hbj, hcj⟩
    rw [Finset.mem_insert] at ha hb hc
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact (hab rfl).elim
      · rcases hc with rfl | hc
        · exact (hac rfl).elim
        · exact hcon ⟨b, hb, c, hc, hbc, j, hbj, hcj, haj⟩
    · rcases hb with rfl | hb
      · rcases hc with rfl | hc
        · exact (hbc rfl).elim
        · exact hcon ⟨a, ha, c, hc, hac, j, haj, hcj, hbj⟩
      · rcases hc with rfl | hc
        · exact hcon ⟨a, ha, b, hb, hab, j, haj, hbj, hcj⟩
        · exact hI_arc a ha b hb c hc hab hac hbc ⟨j, haj, hbj, hcj⟩
  · have hle : ∀ w : Fin n, (decide (w = v) : Bool) = true →
        (decide (w ∈ insert v I) : Bool) = true := by
      intro w hw
      rw [decide_eq_true_eq] at hw ⊢
      rw [hw]
      exact Finset.mem_insert_self v I
    exact PEqualNP.Outside.L_meta_1654.W_mono gates hmono G _ _ hle hvG
  · have hle : ∀ w : Fin n, (decide (w ∈ I) : Bool) = true →
        (decide (w ∈ insert v I) : Bool) = true := by
      intro w hw
      rw [decide_eq_true_eq] at hw ⊢
      exact Finset.mem_insert_of_mem hw
    exact PEqualNP.Outside.L_meta_1654.W_mono gates hmono K _ _ hle hIK
