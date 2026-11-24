import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2413_aux

open PEqualNP.CircuitLowerBounds

/-- The value read off a one-element wire list. -/
lemma getD_singleton (v : Bool) (m : ℕ) :
    [v].getD m false = if m = 0 then v else false := by
  cases m with
  | zero => rfl
  | succ m =>
    cases m with
    | zero => rfl
    | succ m => rfl

/-- The value read off the wire list of an input function. -/
lemma getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · simp
  · simp

/-- For an AND or an OR gate, if every wire value that is `true` under `w₁` is
also `true` under `w₂`, then a `true` output under `w₁` stays `true` under `w₂`. -/
lemma eval_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {inputs : List ℕ} {w₁ w₂ : List Bool}
    (h : ∀ i : ℕ, w₁.getD i false = true → w₂.getD i false = true) :
    op.eval (inputs.map fun i => w₁.getD i false) = true →
    op.eval (inputs.map fun i => w₂.getD i false) = true := by
  intro hev
  rcases hop with rfl | rfl
  · have hall : ∀ b ∈ inputs.map (fun i => w₁.getD i false), b = true :=
      List.all_eq_true.mp hev
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h i (hall _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · obtain ⟨b, hb, hbt⟩ := List.any_eq_true.mp hev
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    apply List.any_eq_true.mpr
    exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, h i hbt⟩

/-- Monotonicity of the wire fold: pointwise-`true` inclusion of the input
lists (of the same length) is preserved through any list of AND/OR gates. -/
lemma foldl_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ {x y : List Bool}, x.length = y.length →
    (∀ i : ℕ, x.getD i false = true → y.getD i false = true) →
    ∀ i : ℕ, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x).getD i false = true →
             (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) y).getD i false = true := by
  intro gs
  induction gs with
  | nil =>
    intro _ x y _ hxy i hi
    exact hxy i hi
  | cons g gs ih =>
    intro hgs x y hlen hxy i hi
    simp only [List.foldl_cons] at hi ⊢
    refine ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) ?_ ?_ i hi
    · simp [hlen]
    · intro k hk
      by_cases hk1 : k < x.length
      · rw [List.getD_append _ _ _ _ hk1] at hk
        rw [List.getD_append _ _ _ _ (show k < y.length from hlen ▸ hk1)]
        exact hxy k hk
      · have hkx : x.length ≤ k := by omega
        have hky : y.length ≤ k := hlen ▸ hkx
        rw [List.getD_append_right _ _ _ _ hkx] at hk
        rw [List.getD_append_right _ _ _ _ hky]
        have hsub : k - x.length = k - y.length := by rw [hlen]
        rw [hsub] at hk
        by_cases hm : k - y.length = 0
        · have hk' : g.op.eval (g.inputs.map fun j => x.getD j false) = true := by
            have hkk := hk
            rw [hm, getD_singleton] at hkk
            simpa using hkk
          have hy' : g.op.eval (g.inputs.map fun j => y.getD j false) = true :=
            eval_mono (hgs g (List.mem_cons_self)) hxy hk'
          rw [hm, getD_singleton]
          simpa using hy'
        · have hcontra : [g.op.eval (g.inputs.map fun j => x.getD j false)].getD (k - y.length) false = false := by
            rw [getD_singleton]
            simp [hm]
          rw [hcontra] at hk
          exact absurd hk (by decide)

end PEqualNP.Outside.L_meta_2413_aux

theorem PEqualNP.Outside.L_meta_2413 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ (j a b : ℕ) (p p' : Fin N), (j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = a))) → a ≠ b → (∀ z1 : Fin n → Bool, (∃ h1 : pw p < n, z1 ⟨pw p, h1⟩ = true) → (C.wires (List.ofFn z1)).getD (b) false = true → PEqualNP.MetaComplexity.circuitFun n C z1 = true) → (C.wires (List.ofFn (fun k5 : Fin n => decide (k5.val = pw p)))).getD (a) false = true → (∀ z2 : Fin n → Bool, (∃ h2 : pw p' < n, z2 ⟨pw p', h2⟩ = true) → (C.wires (List.ofFn z2)).getD (a) false = true → PEqualNP.MetaComplexity.circuitFun n C z2 = true) → (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val = pw p')))).getD (b) false = true → False := by
  intro n N M pw lw I C hAO2 _hinjpw _hinjlw _hdisj hltp _hltl hsound j a b p p' _hjgate _hab
    hservep _hsingp _hservep' hsingp'
  obtain ⟨hao, -, -⟩ := hAO2
  -- The two-point input: only the wires of `p` and `p'` are on.
  set z : Fin n → Bool := fun k3 : Fin n =>
    decide (k3.val ∈ ({p, p'} : Finset (Fin N)).image pw ∪ (∅ : Finset (Fin M)).image lw) with hz
  -- Soundness on two points and no line: the circuit is `false` at `z`.
  have hfalse : PEqualNP.MetaComplexity.circuitFun n C z = false := by
    apply hsound
    · have h1 : ({p, p'} : Finset (Fin N)).card ≤ ({p'} : Finset (Fin N)).card + 1 :=
        Finset.card_insert_le _ _
      have h2 : ({p'} : Finset (Fin N)).card = 1 := Finset.card_singleton p'
      omega
    · simp
    · intro p3 _ l3 hl3
      simp at hl3
  -- Monotonicity transfer along `C`, specialized to the target input `z`.
  have hmono : ∀ (s : Fin n → Bool) (w : ℕ),
      (∀ k : Fin n, s k = true → z k = true) →
      (C.wires (List.ofFn s)).getD w false = true →
      (C.wires (List.ofFn z)).getD w false = true := by
    intro s w hst hw
    refine PEqualNP.Outside.L_meta_2413_aux.foldl_mono C.gates hao ?_ ?_ w hw
    · simp
    · intro i hi
      by_cases hi2 : i < n
      · rw [PEqualNP.Outside.L_meta_2413_aux.getD_ofFn s i, dif_pos hi2] at hi
        rw [PEqualNP.Outside.L_meta_2413_aux.getD_ofFn z i, dif_pos hi2]
        exact hst ⟨i, hi2⟩ hi
      · rw [PEqualNP.Outside.L_meta_2413_aux.getD_ofFn s i, dif_neg hi2] at hi
        exact absurd hi (by decide)
  -- Wire `b` of `z` is `true`: it is already `true` at the singleton input `p'`.
  have hw_b : (C.wires (List.ofFn z)).getD b false = true := by
    apply hmono _ b _ hsingp'
    intro k hk
    have hk' : decide (k.val = pw p') = true := hk
    rw [decide_eq_true_eq] at hk'
    have hmem : k.val ∈ ({p, p'} : Finset (Fin N)).image pw ∪ (∅ : Finset (Fin M)).image lw :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨p', by simp, hk'.symm⟩))
    exact decide_eq_true_eq.mpr hmem
  -- Serving `p` through `b` now forces the circuit to be `true` at `z`.
  have htrue : PEqualNP.MetaComplexity.circuitFun n C z = true := by
    apply hservep
    · exact ⟨hltp p, decide_eq_true_eq.mpr (Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨p, by simp, rfl⟩)))⟩
    · exact hw_b
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue
