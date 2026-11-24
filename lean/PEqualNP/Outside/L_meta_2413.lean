import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2413

def R (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true)
    (he : op.eval (l.map fun i => w.getD i false) = true) :
    op.eval (l.map fun i => w'.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at he ⊢
    rintro _ ⟨i, hi, rfl⟩
    exact h i (he _ ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at he ⊢
    obtain ⟨_, ⟨i, hi, rfl⟩, hv⟩ := he
    exact ⟨_, ⟨i, hi, rfl⟩, h i hv⟩

theorem R_snoc (w w' : List Bool) (b b' : Bool) (h : R w w') (hb : b = true → b' = true) :
    R (w ++ [b]) (w' ++ [b']) := by
  obtain ⟨hl, h⟩ := h
  refine ⟨by simp [hl], fun i hi => ?_⟩
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  rcases Nat.lt_or_ge i w.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by omega)]
    have := h i
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
    exact this hi
  · rw [List.getElem?_append_right hge] at hi
    rw [List.getElem?_append_right (by omega)]
    rcases Nat.lt_or_ge (i - w.length) 1 with h1 | h1
    · have e1 : i - w.length = 0 := by omega
      have e2 : i - w'.length = 0 := by omega
      rw [e1] at hi
      rw [e2]
      simpa using hb (by simpa using hi)
    · rw [List.getElem?_eq_none (by simp; omega)] at hi
      simp at hi

theorem fold_mono (G : List Gate) (hG : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ x y : List Bool, R x y →
      R (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x)
        (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y) := by
  induction G with
  | nil => intro x y h; exact h
  | cons g G ih =>
    intro x y h
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg'))
    exact R_snoc _ _ _ _ h
      (eval_mono g.op (hG g (List.mem_cons_self ..)) g.inputs x y h.2)

theorem wires_mono (n : ℕ) (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ k, x k = true → y k = true) (i : ℕ)
    (h : (C.wires (List.ofFn x)).getD i false = true) :
    (C.wires (List.ofFn y)).getD i false = true := by
  have hR : R (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, fun k hk => ?_⟩
    rw [List.getD_eq_getElem?_getD] at hk ⊢
    rcases Nat.lt_or_ge k n with hlt | hge
    · rw [List.getElem?_ofFn] at hk ⊢
      simp only [hlt, dite_true, Option.getD_some] at hk ⊢
      exact hxy _ hk
    · rw [List.getElem?_eq_none (by simp; omega)] at hk
      simp at hk
  exact (fold_mono C.gates hC _ _ hR).2 i h

end PEqualNP.Outside.L_meta_2413

open PEqualNP.Outside.L_meta_2413
theorem PEqualNP.Outside.L_meta_2413 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ (j a b : ℕ) (p p' : Fin N), (j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = a))) → a ≠ b → (∀ z1 : Fin n → Bool, (∃ h1 : pw p < n, z1 ⟨pw p, h1⟩ = true) → (C.wires (List.ofFn z1)).getD (b) false = true → PEqualNP.MetaComplexity.circuitFun n C z1 = true) → (C.wires (List.ofFn (fun k5 : Fin n => decide (k5.val = pw p)))).getD (a) false = true → (∀ z2 : Fin n → Bool, (∃ h2 : pw p' < n, z2 ⟨pw p', h2⟩ = true) → (C.wires (List.ofFn z2)).getD (a) false = true → PEqualNP.MetaComplexity.circuitFun n C z2 = true) → (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val = pw p')))).getD (b) false = true → False := by
  intro n N M pw lw I C hC _ _ _ hpn _ hsound j a b p p' _ _ _ hap hdom2 _
  have hs := hsound {p, p'} ∅ (Finset.card_le_two) (by simp) (by simp)
  have hmono : ∀ k : Fin n, decide (k.val = pw p) = true →
      decide (k.val ∈ (({p, p'} : Finset (Fin N)).image pw ∪ (∅ : Finset (Fin M)).image lw)) = true := by
    intro k hk
    simp only [decide_eq_true_eq] at hk ⊢
    simp [hk]
  have ha := wires_mono n C hC.1 _ _ hmono a hap
  have ht := hdom2 _ ⟨hpn p', by simp⟩ ha
  rw [hs] at ht
  exact Bool.false_ne_true ht
