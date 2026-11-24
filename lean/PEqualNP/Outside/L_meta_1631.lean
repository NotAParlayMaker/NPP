import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1631

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

lemma eval_mono' {N : ℕ} (gates : List Gate)
    (hmono : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : ℕ) (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = true → Circuit.eval ⟨gates, w⟩ (List.ofFn y) = true := by
  intro h
  have hle : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i hi
    by_cases hlt : i < N
    · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hi
      rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
      simp only [List.getElem_ofFn] at hi ⊢
      exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hlt)] at hi
      exact Bool.noConfusion hi
  exact wiresFrom_mono gates hmono (List.ofFn x) (List.ofFn y) (by simp) hle w h

end PEqualNP.Outside.L_meta_1631

theorem PEqualNP.Outside.L_meta_1631 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, ((∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) ↔
    ∀ t : Fin N, ev (o t) (fun v : Fin N => decide (v ∉ L t)) = false ∧ (p0 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p0)) = true) ∧ (p1 ∈ L t → ev (o t) (fun v : Fin N => decide (v = p1)) = true) ∧
      (∀ p ∈ L t, ev (o t) (fun v : Fin N => decide (v = p0 ∨ v = p)) = true ∧ ev (o t) (fun v : Fin N => decide (v = p1 ∨ v = p)) = true) ∧ (t ≠ i0 → ev (o t) (fun v : Fin N => decide (v ∉ L i0)) = true) ∧
      (∀ w ∈ L t ∩ L i0, w ≠ p0 → w ≠ p1 → ev (o t) (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)) = true)) := by
  intro q N L i0 p0 p1 hq hN hcard hint hjoin h01 hp0 hp1 gates hg hpos hw ev hev o
  have mono : ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v, x v = true → y v = true) →
      ev w x = true → ev w y = true := by
    intro w x y hxy h
    rw [hev] at h
    rw [hev]
    exact PEqualNP.Outside.L_meta_1631.eval_mono' gates (fun g hg' => (hg g hg').1) w x y hxy h
  constructor
  · intro H t
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hF : ((fun v : Fin N => decide (v ∉ L t)) p0 = true ∨
          (fun v : Fin N => decide (v ∉ L t)) p1 = true ∨
          ∀ u : Fin N, u ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) u = true) := by
        by_cases hti : t = i0
        · right; right
          intro u hu
          rw [hti]
          exact decide_eq_true hu
        · by_cases h0 : p0 ∈ L t
          · by_cases h1 : p1 ∈ L t
            · exfalso
              have h2 := hint t i0 hti
              have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
                intro v hv
                rw [Finset.mem_insert, Finset.mem_singleton] at hv
                rcases hv with hv | hv
                · rw [hv]; exact Finset.mem_inter.mpr ⟨h0, hp0⟩
                · rw [hv]; exact Finset.mem_inter.mpr ⟨h1, hp1⟩
              have h3 := Finset.card_le_card hsub
              rw [Finset.card_pair h01] at h3
              omega
            · right; left
              exact decide_eq_true h1
          · left
            exact decide_eq_true h0
      rw [H t _ hF]
      refine decide_eq_false ?_
      rintro ⟨v, hv, hv'⟩
      exact (of_decide_eq_true hv') hv
    · intro h0
      rw [H t _ (Or.inl (decide_eq_true rfl))]
      exact decide_eq_true ⟨p0, h0, decide_eq_true rfl⟩
    · intro h1
      rw [H t _ (Or.inr (Or.inl (decide_eq_true rfl)))]
      exact decide_eq_true ⟨p1, h1, decide_eq_true rfl⟩
    · intro p hp
      constructor
      · rw [H t _ (Or.inl (decide_eq_true (Or.inl rfl)))]
        exact decide_eq_true ⟨p, hp, decide_eq_true (Or.inr rfl)⟩
      · rw [H t _ (Or.inr (Or.inl (decide_eq_true (Or.inl rfl))))]
        exact decide_eq_true ⟨p, hp, decide_eq_true (Or.inr rfl)⟩
    · intro hti
      rw [H t _ (Or.inr (Or.inr (fun u hu => decide_eq_true hu)))]
      have hex : ∃ v ∈ L t, v ∉ L i0 := by
        by_contra hno
        have hno2 : ∀ v ∈ L t, v ∈ L i0 := fun v hv => by_contra (fun hc => hno ⟨v, hv, hc⟩)
        have hsub : L t ⊆ L t ∩ L i0 := fun v hv => Finset.mem_inter.mpr ⟨hv, hno2 v hv⟩
        have h3 := Finset.card_le_card hsub
        rw [hcard, hint t i0 hti] at h3
        omega
      obtain ⟨v, hv, hv'⟩ := hex
      exact decide_eq_true ⟨v, hv, decide_eq_true hv'⟩
    · intro w hw' _ _
      rw [H t _ (Or.inr (Or.inr (fun u hu => decide_eq_true (Or.inl hu))))]
      exact decide_eq_true ⟨w, (Finset.mem_inter.mp hw').1, decide_eq_true (Or.inr rfl)⟩
  · intro H t x hF
    obtain ⟨hz, he0, he1, hpair, hzi, hzw⟩ := H t
    by_cases hex : ∃ v ∈ L t, x v = true
    · have hd : decide (∃ v ∈ L t, x v = true) = true := decide_eq_true hex
      rw [hd]
      obtain ⟨p, hp, hxp⟩ := hex
      have key0 : x p0 = true → ev (o t) x = true := by
        intro h
        refine mono (o t) _ x ?_ (hpair p hp).1
        intro v hv
        have hv' : v = p0 ∨ v = p := of_decide_eq_true hv
        rcases hv' with hv' | hv'
        · rw [hv']; exact h
        · rw [hv']; exact hxp
      have key1 : x p1 = true → ev (o t) x = true := by
        intro h
        refine mono (o t) _ x ?_ (hpair p hp).2
        intro v hv
        have hv' : v = p1 ∨ v = p := of_decide_eq_true hv
        rcases hv' with hv' | hv'
        · rw [hv']; exact h
        · rw [hv']; exact hxp
      rcases hF with h | h | h
      · exact key0 h
      · exact key1 h
      · by_cases hti : t = i0
        · by_cases hpp0 : p = p0
          · exact key0 (hpp0 ▸ hxp)
          · by_cases hpp1 : p = p1
            · exact key1 (hpp1 ▸ hxp)
            · have hpi : p ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨hp, hti ▸ hp⟩
              refine mono (o t) _ x ?_ (hzw p hpi hpp0 hpp1)
              intro v hv
              have hv' : v ∉ L i0 ∨ v = p := of_decide_eq_true hv
              rcases hv' with hv' | hv'
              · exact h v hv'
              · rw [hv']; exact hxp
        · refine mono (o t) _ x ?_ (hzi hti)
          intro v hv
          exact h v (of_decide_eq_true hv)
    · have hd : decide (∃ v ∈ L t, x v = true) = false := decide_eq_false hex
      rw [hd]
      by_contra hne
      have htrue : ev (o t) x = true := by
        cases hc : ev (o t) x
        · exact absurd hc hne
        · rfl
      have h4 := mono (o t) x (fun v : Fin N => decide (v ∉ L t))
        (fun v hv => decide_eq_true (fun hvl => hex ⟨v, hvl, hv⟩)) htrue
      rw [hz] at h4
      exact Bool.noConfusion h4
