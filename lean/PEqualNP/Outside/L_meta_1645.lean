import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1645

open PEqualNP.CircuitLowerBounds

-- The wires of a gate list on a start list, as in Circuit.wires.
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

-- Values of the wires on an input of length N: input wires, gate wires, missing wires.
lemma input_val {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (i : ℕ) (hi : i < N) :
    (wiresFrom gates (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [getD_wiresFrom_lt _ _ _ (by rw [List.length_ofFn]; exact hi),
    List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi), List.getElem_ofFn]

lemma gate_val {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (k : ℕ) (hk : k < gates.length) :
    (wiresFrom gates (List.ofFn x)).getD (N + k) false =
      (gates[k]).op.eval ((gates[k]).inputs.map fun i =>
        if i < N + k then (wiresFrom gates (List.ofFn x)).getD i false else false) := by
  have := getD_wiresFrom_gate gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  exact this

lemma beyond_val {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (i : ℕ)
    (hi : N + gates.length ≤ i) : (wiresFrom gates (List.ofFn x)).getD i false = false := by
  rw [List.getD_eq_default]
  rw [length_wiresFrom, List.length_ofFn]
  exact hi

-- The NOT gate reading wire N + h first.
lemma not_val {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (j h : ℕ) (hj : j < gates.length)
    (hhj : h < j) (hop : (gates[j]).op = GateOp.not) (r : List ℕ)
    (hin : (gates[j]).inputs = (N + h) :: r) :
    (wiresFrom gates (List.ofFn x)).getD (N + j) false =
      !((wiresFrom gates (List.ofFn x)).getD (N + h) false) := by
  rw [gate_val gates x j hj, hop, hin]
  have hc : N + h < N + j := by omega
  simp only [GateOp.eval, List.map_cons, List.headD_cons, hc, ↓reduceIte]

-- Monotonicity along a relation R below the pointwise order, for all wires under a bound B,
-- given that every NOT gate under the bound is monotone along R.
theorem mono_gen {N : ℕ} (gates : List Gate) (B : ℕ)
    (R : (Fin N → Bool) → (Fin N → Bool) → Prop)
    (hR : ∀ x y, R x y → ∀ v, x v = true → y v = true)
    (hops : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : ∀ (k : ℕ) (hk : k < gates.length), N + k < B → (gates[k]).op = GateOp.not →
      ∀ x y, R x y → (wiresFrom gates (List.ofFn x)).getD (N + k) false = true →
        (wiresFrom gates (List.ofFn y)).getD (N + k) false = true) :
    ∀ i, i < B → ∀ x y, R x y → (wiresFrom gates (List.ofFn x)).getD i false = true →
      (wiresFrom gates (List.ofFn y)).getD i false = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hiB x y hxy hx
    by_cases hiN : i < N
    · rw [input_val gates x i hiN] at hx
      rw [input_val gates y i hiN]
      exact hR x y hxy _ hx
    · by_cases hiL : i < N + gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, i = N + k := ⟨i - N, by omega⟩
        have hk : k < gates.length := by omega
        rcases hops (gates[k]) (List.getElem_mem hk) with hop | hop | hop
        · rw [gate_val gates x k hk] at hx
          rw [gate_val gates y k hk]
          refine gateOp_eval_mono _ (Or.inl hop) _ _ (by simp) ?_ hx
          intro t ht
          have htl : t < (gates[k]).inputs.length := by
            by_contra hcon
            rw [List.getD_eq_default _ _ (by simp; omega)] at ht
            exact absurd ht (by simp)
          rw [List.getD_eq_getElem _ _ (by simpa using htl)] at ht ⊢
          simp only [List.getElem_map] at ht ⊢
          split_ifs at ht ⊢ with hm
          · exact ih _ hm (by omega) x y hxy ht
        · rw [gate_val gates x k hk] at hx
          rw [gate_val gates y k hk]
          refine gateOp_eval_mono _ (Or.inr hop) _ _ (by simp) ?_ hx
          intro t ht
          have htl : t < (gates[k]).inputs.length := by
            by_contra hcon
            rw [List.getD_eq_default _ _ (by simp; omega)] at ht
            exact absurd ht (by simp)
          rw [List.getD_eq_getElem _ _ (by simpa using htl)] at ht ⊢
          simp only [List.getElem_map] at ht ⊢
          split_ifs at ht ⊢ with hm
          · exact ih _ hm (by omega) x y hxy ht
        · exact hnot k hk hiB hop x y hxy hx
      · rw [beyond_val gates x i (by omega)] at hx
        exact absurd hx (by simp)

end PEqualNP.Outside.L_meta_1645

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1645 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p0)) = true → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p1)) = true → (∀ p : Fin N, p ≠ p0 → p ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = p)) = false) →
    ev (N + (h : ℕ)) (fun v : Fin N => decide (v ∉ L i0)) = false →
    (∀ x : Fin N → Bool, (∀ v : Fin N, x v = true → v ∉ L i0) → ev (N + (h : ℕ)) x = false ∧ ev (N + (j : ℕ)) x = true) ∧
    (∀ w ∈ L i0, w ≠ p0 → w ≠ p1 → ev (N + (h : ℕ)) (fun v : Fin N => decide (v = w)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = w)) = true) ∧
    ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p0)) = false ∧ ev (N + (j : ℕ)) (fun v : Fin N => decide (v = p1)) = false ∧
    ∀ (w : ℕ) (x y : Fin N → Bool), (∀ v : Fin N, x v = true → v ∉ L i0) → (∀ v : Fin N, y v = true → v ∉ L i0) → (∀ v : Fin N, x v = true → y v = true) → ev w x = true → ev w y = true := by
  intro q N L i0 p0 p1 _ _ _ _ _ _ _ _ gates o j h hops _ hjnot huniq hhj hjin _ ev hev hp0 hp1 hpo hoff
  have hev' : ∀ (w : ℕ) (x : Fin N → Bool),
      ev w x = (PEqualNP.Outside.L_meta_1645.wiresFrom gates (List.ofFn x)).getD w false :=
    fun w x => hev w x
  have hops' : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hops g hg).1
  have hhj' : (h : ℕ) < (j : ℕ) := hhj
  have hjop : (gates[(j : ℕ)]).op = GateOp.not := by
    rw [← List.get_eq_getElem]; exact hjnot
  obtain ⟨r, hr⟩ := hjin
  have hjin' : (gates[(j : ℕ)]).inputs = (N + (h : ℕ)) :: r := by
    rw [← List.get_eq_getElem]; exact hr
  -- the NOT wire is the negation of wire h
  have hneg : ∀ x : Fin N → Bool, ev (N + (j : ℕ)) x = !ev (N + (h : ℕ)) x := by
    intro x
    rw [hev', hev']
    exact PEqualNP.Outside.L_meta_1645.not_val gates x j h j.isLt hhj' hjop r hjin'
  -- no NOT gate comes before j
  have honly : ∀ (k : ℕ) (hk : k < gates.length), (gates[k]).op = GateOp.not → k = (j : ℕ) := by
    intro k hk hop
    have := huniq ⟨k, hk⟩ (by rw [List.get_eq_getElem]; exact hop)
    exact congrArg Fin.val this
  -- wire h is monotone on all inputs
  have hmonoh : ∀ x y : Fin N → Bool, (∀ v, x v = true → y v = true) →
      ev (N + (h : ℕ)) x = true → ev (N + (h : ℕ)) y = true := by
    intro x y hxy hx
    rw [hev'] at hx ⊢
    refine PEqualNP.Outside.L_meta_1645.mono_gen gates (N + (j : ℕ))
      (fun x y => ∀ v, x v = true → y v = true) (fun _ _ hxy => hxy) hops' ?_
      (N + (h : ℕ)) (by omega) x y hxy hx
    intro k hk hkB hop
    have := honly k hk hop
    omega
  -- wire h is false on every input off the line i0
  have hoffh : ∀ x : Fin N → Bool, (∀ v, x v = true → v ∉ L i0) → ev (N + (h : ℕ)) x = false := by
    intro x hx
    by_contra hne
    have htrue : ev (N + (h : ℕ)) x = true := by simpa using hne
    have := hmonoh x (fun v : Fin N => decide (v ∉ L i0))
      (fun v hv => by simpa using hx v hv) htrue
    rw [hoff] at this
    exact absurd this (by simp)
  have hoffj : ∀ x : Fin N → Bool, (∀ v, x v = true → v ∉ L i0) → ev (N + (j : ℕ)) x = true := by
    intro x hx
    rw [hneg, hoffh x hx]
    rfl
  refine ⟨fun x hx => ⟨hoffh x hx, hoffj x hx⟩, ?_, ?_, ?_, ?_⟩
  · intro w _ hw0 hw1
    have h1 := hpo w hw0 hw1
    refine ⟨h1, ?_⟩
    rw [hneg, h1]
    rfl
  · rw [hneg, hp0]
    rfl
  · rw [hneg, hp1]
    rfl
  · intro w x y hx hy hxy hw
    rw [hev'] at hw ⊢
    refine PEqualNP.Outside.L_meta_1645.mono_gen gates (w + 1)
      (fun x y => (∀ v, x v = true → v ∉ L i0) ∧ (∀ v, y v = true → v ∉ L i0) ∧
        (∀ v, x v = true → y v = true))
      (fun _ _ hR => hR.2.2) hops' ?_ w (by omega) x y ⟨hx, hy, hxy⟩ hw
    intro k hk _ hop x' y' hR _
    have hkj := honly k hk hop
    subst hkj
    have := hoffj y' hR.2.1
    rw [hev'] at this
    exact this
