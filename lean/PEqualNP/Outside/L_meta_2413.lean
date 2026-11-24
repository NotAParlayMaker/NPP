import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2413

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

def WireLe (u v : List Bool) : Prop :=
  ∀ j, u.getD j false = true → v.getD j false = true

lemma gate_mono (g : Gate) (hg : g.op = .and ∨ g.op = .or) (u v : List Bool)
    (h : WireLe u v) :
    g.op.eval (g.inputs.map fun j => u.getD j false) = true →
      g.op.eval (g.inputs.map fun j => v.getD j false) = true := by
  intro he
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro j hj
    exact h j (he j hj)
  · obtain ⟨j, hj, ht⟩ := he
    exact ⟨j, hj, h j ht⟩

lemma snoc_getD (w : List Bool) (b : Bool) (j : ℕ) :
    (w ++ [b]).getD j false =
      if j < w.length then w.getD j false else if j = w.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases hlt : j < w.length
  · simp [hlt, List.getElem?_append_left hlt]
  · rw [ite_eq_right hlt, List.getElem?_append_right (by omega)]
    by_cases heq : j = w.length
    · subst j
      simp
    · have hn : j - w.length ≠ 0 := by omega
      simp [heq, hn]

lemma fold_mono (gates : List Gate) (hgate : ∀ g ∈ gates, g.op = .and ∨ g.op = .or)
    (u v : List Bool) (hlen : u.length = v.length) (hle : WireLe u v) :
    WireLe (gates.foldl step u) (gates.foldl step v) := by
  induction gates generalizing u v with
  | nil => exact hle
  | cons g gs ih =>
    apply ih (fun g' hg' => hgate g' (List.mem_cons_of_mem g hg'))
    · simp [step, hlen]
    · intro j hj
      simp only [step, snoc_getD, ← hlen] at hj ⊢
      by_cases hlt : j < u.length
      · simpa [hlt] using hle j (by simpa [hlt] using hj)
      by_cases hj_eq : j = u.length
      · simp only [ite_eq_right hlt, ite_eq_left hj_eq] at hj ⊢
        exact gate_mono g (hgate g List.mem_cons_self) u v hle hj
      · simp [hlt, hj_eq] at hj

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (j : ℕ) :
    (List.ofFn x).getD j false = if h : j < n then x ⟨j, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : j < n <;> simp [h]

lemma wires_mono {n : ℕ} (C : Circuit) (h : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    {x y : Fin n → Bool} (hxy : x ≤ y) :
    WireLe (C.wires (List.ofFn x)) (C.wires (List.ofFn y)) := by
  have hin : WireLe (List.ofFn x) (List.ofFn y) := by
    intro j hj
    rw [ofFn_getD] at hj ⊢
    by_cases hn : j < n
    · simp only [dite_eq_left hn] at hj ⊢
      exact Bool.le_iff_imp.mp (hxy ⟨j, hn⟩) hj
    · simp [hn] at hj
  exact fold_mono C.gates h (List.ofFn x) (List.ofFn y) (by simp) hin

end PEqualNP.Outside.L_meta_2413

open PEqualNP.Outside.L_meta_2413

theorem PEqualNP.Outside.L_meta_2413 :
    ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C :
    PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw →
    Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) →
    (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2
    → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n =>
    decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ (j a b : ℕ) (p p' : Fin N), (j <
    C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
    PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C
    j).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = b)
    ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = b ∧
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = a))) → a ≠ b → (∀ z1 : Fin n
    → Bool, (∃ h1 : pw p < n, z1 ⟨pw p, h1⟩ = true) → (C.wires (List.ofFn z1)).getD (b) false = true →
    PEqualNP.MetaComplexity.circuitFun n C z1 = true) → (C.wires (List.ofFn (fun k5 : Fin n => decide
    (k5.val = pw p)))).getD (a) false = true → (∀ z2 : Fin n → Bool, (∃ h2 : pw p' < n, z2 ⟨pw p', h2⟩
    = true) → (C.wires (List.ofFn z2)).getD (a) false = true → PEqualNP.MetaComplexity.circuitFun n C
    z2 = true) → (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val = pw p')))).getD (b) false =
    true → False := by
  classical
  intro n N M pw lw I C hC _ _ _ hpw _ hsound _ _ b p p' _ _ hserve _ _ hb
  let P : Finset (Fin N) := {p, p'}
  let Y : Finset (Fin M) := ∅
  let z : Fin n → Bool := fun k => decide (k.val ∈ P.image pw ∪ Y.image lw)
  have hmem (q : Fin N) (hq : q ∈ P) : pw q ∈ P.image pw ∪ Y.image lw :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem pw hq)
  have hp : p ∈ P := by simp [P]
  have hp' : p' ∈ P := by simp [P]
  have hsub : (fun k : Fin n => decide (k.val = pw p')) ≤ z := by
    intro k
    apply Bool.le_iff_imp.mpr
    intro hk
    have he : k.val = pw p' := of_decide_eq_true hk
    exact decide_eq_true (he ▸ hmem p' hp')
  have hbz : (C.wires (List.ofFn z)).getD b false = true := wires_mono C hC.1 hsub b hb
  have htrue := hserve z ⟨hpw p, decide_eq_true (hmem p hp)⟩ hbz
  have hcard : P.card ≤ 2 := by
    simpa only [P, Finset.card_singleton] using Finset.card_insert_le p ({p'} : Finset (Fin N))
  have hfalse : PEqualNP.MetaComplexity.circuitFun n C z = false :=
    hsound P Y hcard (by simp [Y]) (by simp [Y])
  rw [hfalse] at htrue
  cases htrue
