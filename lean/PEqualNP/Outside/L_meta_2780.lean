import Mathlib
import PEqualNP.Defs

-- Circuit evaluation helpers adapted from trimbe, PR #2080 (L-meta-1042).
namespace PEqualNP.Outside.L_meta_2780

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

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

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

def V {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (w : ℕ) : Bool :=
  wireValue C (List.ofFn x ++ List.ofFn y) w

lemma ofFn_mono {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi] using h ⟨i, hi⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]

lemma V_mono {n : ℕ} (C : Circuit) (hC : IsAO2 (n+n) C)
    (x x' y y' : Fin n → Bool)
    (hx : ∀ i, x i = true → x' i = true) (hy : ∀ i, y i = true → y' i = true)
    (w : ℕ) : V C x y w = true → V C x' y' w = true := by
  apply wiresFrom_mono C.gates hC.1 _ _ (by simp)
  intro i hi
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h)] at hi
    rw [List.getD_append _ _ _ _ (by simpa using h)]
    exact ofFn_mono x x' hx i hi
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simpa using ofFn_mono y y' hy (i-n) (by simpa using hi)

lemma V_right {n : ℕ} (C : Circuit) (hC : IsAO2 (n+n) C) (w : ℕ)
    (h : ∀ x : Fin n → Bool, V C x (fun _ => false) w = V C x (fun _ => true) w)
    (x y : Fin n → Bool) : V C x y w = V C x (fun _ => false) w := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    rw [h x]
    exact V_mono C hC x x y (fun _ => true) (by simp) (by simp) w hv
  · exact V_mono C hC x x (fun _ => false) y (by simp) (by simp) w

lemma V_left {n : ℕ} (C : Circuit) (hC : IsAO2 (n+n) C) (w : ℕ)
    (h : ∀ y : Fin n → Bool, V C (fun _ => false) y w = V C (fun _ => true) y w)
    (x y : Fin n → Bool) : V C x y w = V C (fun _ => false) y w := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    rw [h y]
    exact V_mono C hC x (fun _ => true) y y (by simp) (by simp) w hv
  · exact V_mono C hC (fun _ => false) x y y (by simp) (by simp) w

lemma wiresFrom_zero (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : List Bool) (hz : ∀ i, w.getD i false = false) :
    ∀ i, (wiresFrom gs w).getD i false = false := by
  induction gs generalizing w with
  | nil => exact hz
  | cons g gs ih =>
    have hg := hgs g List.mem_cons_self
    obtain ⟨a,b,hab⟩ := List.length_eq_two.mp hg.2
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) = false := by
      simp only [hab, List.map_cons, List.map_nil, hz]
      rcases hg.1 with h | h <;> simp [h, GateOp.eval]
    change ∀ i, (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD i false = false
    rw [hv]
    apply ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
    intro i
    by_cases hi : i < w.length
    · rw [List.getD_append _ _ _ _ hi, hz]
    · rw [List.getD_append_right _ _ _ _ (by omega)]
      simp

lemma V_zero {n : ℕ} (C : Circuit) (hC : IsAO2 (n+n) C) (w : ℕ) :
    V C (fun _ : Fin n => false) (fun _ => false) w = false := by
  apply wiresFrom_zero C.gates (fun g hg => ⟨hC.1 g hg, hC.2.2 g hg⟩)
  intro i
  simp [List.ofFn_const, ← List.replicate_add]

lemma gate_and {n : ℕ} (C : Circuit) (hC : IsAO2 (n+n) C) (j : ℕ)
    (hj : j < C.size) (hop : (gateAt C j).op = GateOp.and) (x y : Fin n → Bool) :
    V C x y (n+n+j) = true ↔ ∀ w ∈ (gateAt C j).inputs, V C x y w = true := by
  have hj' : j < C.gates.length := hj
  have hg : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj'
  unfold V wireValue Circuit.wires
  change (wiresFrom C.gates (List.ofFn x ++ List.ofFn y)).getD (n+n+j) false = true ↔ _
  have hl : (List.ofFn x ++ List.ofFn y).length = n+n := by simp
  rw [← hl, getD_wiresFrom_gate C.gates _ j hj']
  rw [← hg, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, id_eq]
  apply forall₂_congr
  intro w hw
  rw [if_pos (by rw [hl]; exact hC.2.1 j hj' w hw)]
  rfl

lemma pair_cover {l : List ℕ} (hl : l.length = 2) {a b : ℕ}
    (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) : ∀ w ∈ l, w = a ∨ w = b := by
  obtain ⟨u,v,huv⟩ := List.length_eq_two.mp hl
  subst l
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb ⊢
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> aesop

end PEqualNP.Outside.L_meta_2780

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.Outside.L_meta_2780 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_2780 : have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x6 ++ List.replicate x1 Bool.false) x4 ≠ PEqualNP.CircuitLowerBounds.wireValue x2 (List.ofFn x6 ++ List.replicate x1 Bool.true) x4) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), PEqualNP.CircuitLowerBounds.wireValue x2 (List.replicate x1 Bool.false ++ List.ofFn x6) x4 ≠ PEqualNP.CircuitLowerBounds.wireValue x2 (List.replicate x1 Bool.true ++ List.ofFn x6) x4); ∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x2 + x2) x3 → (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x6]? = Option.some x7 → x1 x2 x3 x7 → x6 ∈ x4) → ∀ x7 < x3.size, x7 ∉ x4 → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x11 : Finset (Fin x2) → Bool) (x12 : Finset (Fin x2) → Bool), ∀ (x13 x14 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x3 (PEqualNP.GenericRejection.incidenceInput x13 x14) (x2 + x2 + x7) = (x11 x13 && x12 x14) := by
  classical
  dsimp only
  intro n C X hC hMarked j hj hnj hop
  have hj' : j < C.gates.length := hj
  let g := gateAt C j
  have hg : g = C.gates[j] := List.getD_eq_getElem _ _ hj'
  have hgmem : g ∈ C.gates := by rw [hg]; exact List.getElem_mem hj'
  have hgopt : C.gates[j]? = some g := by simp [List.getElem?_eq_getElem hj', hg]
  have hnR : ¬ ∀ w ∈ g.inputs, ∃ x : Fin n → Bool,
      wireValue C (List.ofFn x ++ List.replicate n false) w ≠
        wireValue C (List.ofFn x ++ List.replicate n true) w := by
    intro h
    exact hnj (hMarked j g hgopt ⟨hop, Or.inl h⟩)
  have hnL : ¬ ∀ w ∈ g.inputs, ∃ y : Fin n → Bool,
      wireValue C (List.replicate n false ++ List.ofFn y) w ≠
        wireValue C (List.replicate n true ++ List.ofFn y) w := by
    intro h
    exact hnj (hMarked j g hgopt ⟨hop, Or.inr h⟩)
  push_neg at hnR hnL
  obtain ⟨a, ha, hRa⟩ := hnR
  obtain ⟨b, hb, hLb⟩ := hnL
  have hr : ∀ x : Fin n → Bool, V C x (fun _ => false) a = V C x (fun _ => true) a := by
    intro x
    simpa [V, List.ofFn_const] using hRa x
  have hl : ∀ y : Fin n → Bool, V C (fun _ => false) y b = V C (fun _ => true) y b := by
    intro y
    simpa [V, List.ofFn_const] using hLb y
  by_cases hab : a = b
  · subst b
    refine ⟨fun _ => false, fun _ => false, ?_⟩
    intro S T
    let x : Fin n → Bool := fun p => decide (p ∈ S)
    let y : Fin n → Bool := fun l => decide (l ∈ T)
    change V C x y (n+n+j) = false
    have hz : V C x y a = false := by
      rw [V_right C hC a hr, V_left C hC a hl, V_zero C hC]
    cases he : V C x y (n+n+j) with
    | false => rfl
    | true =>
      have hv := (gate_and C hC j hj hop x y).mp he a ha
      rw [hz] at hv
      contradiction
  · refine ⟨fun S => V C (fun p => decide (p ∈ S)) (fun _ => false) a,
      fun T => V C (fun _ => false) (fun l => decide (l ∈ T)) b, ?_⟩
    intro S T
    let x : Fin n → Bool := fun p => decide (p ∈ S)
    let y : Fin n → Bool := fun l => decide (l ∈ T)
    change V C x y (n+n+j) = (V C x (fun _ => false) a && V C (fun _ => false) y b)
    apply Bool.eq_iff_iff.mpr
    rw [gate_and C hC j hj hop x y, Bool.and_eq_true]
    constructor
    · intro h
      constructor
      · rw [← V_right C hC a hr x y]; exact h a ha
      · rw [← V_left C hC b hl x y]; exact h b hb
    · rintro ⟨h1,h2⟩ w hw
      rcases pair_cover (hC.2.2 g hgmem) ha hb hab w hw with hw | hw
      · rw [hw, V_right C hC a hr]; exact h1
      · rw [hw, V_left C hC b hl]; exact h2
