import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2413

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem snoc_rel {α : Type} (R : α → α → Prop) (z : α) (hz : R z z) {l l' : List α} {a b : α}
    (hl : l.length = l'.length) (h : ∀ i, R (l.getD i z) (l'.getD i z)) (hab : R a b) (i : ℕ) :
    R ((l ++ [a]).getD i z) ((l' ++ [b]).getD i z) := by
  by_cases hi : i < l'.length
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    by_cases h0 : i - l'.length = 0
    · rw [h0]
      simp only [List.getD_cons_zero]
      exact hab
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      exact hz

theorem all_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).all id = true → (ins.map fun i => w'.getD i false).all id = true := by
  induction ins with
  | nil => intro _; rfl
  | cons a t ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id_eq]
    exact fun hh => ⟨h a hh.1, ih hh.2⟩

theorem any_mono (w w' : List Bool) (h : ∀ i, w.getD i false = true → w'.getD i false = true) (ins : List ℕ) :
    (ins.map fun i => w.getD i false).any id = true → (ins.map fun i => w'.getD i false).any id = true := by
  induction ins with
  | nil => intro hh; exact hh
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id_eq]
    exact fun hh => hh.elim (fun h1 => Or.inl (h a h1)) (fun h2 => Or.inr (ih h2))

def evg (g : Gate) (w : List Bool) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def runW (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem evg_mono (w w' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    evg g w = true → evg g w' = true := by
  rcases hg with hg | hg
  · unfold evg
    rw [hg]
    exact all_mono w w' h g.inputs
  · unfold evg
    rw [hg]
    exact any_mono w w' h g.inputs

theorem run_mono : ∀ (gs : List Gate) (w w' : List Bool),
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
      (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
        ∀ i, (runW gs w).getD i false = true → (runW gs w').getD i false = true
  | [], _, _, _, h, _ => h
  | g :: gs, w, w', hl, h, hg => by
    have h1 := evg_mono w w' g (hg g (by simp)) h
    exact run_mono gs (w ++ [evg g w]) (w' ++ [evg g w'])
      (by simp [hl]) (snoc_rel (fun a b : Bool => a = true → b = true) false (fun hh => hh) hl h h1)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))

theorem wires_mono (C : Circuit) (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {n : ℕ} (x y : Fin n → Bool) (h : ∀ k, x k = true → y k = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn y)).getD i false = true := by
  refine run_mono C.gates (List.ofFn x) (List.ofFn y) (by simp) ?_ hC i
  intro k
  by_cases hk : k < n
  · have e : ∀ z : Fin n → Bool, (List.ofFn z).getD k false = z ⟨k, hk⟩ := fun z => by
      simp [List.getD_eq_getElem?_getD, hk]
    rw [e x, e y]
    exact h _
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    intro hh
    exact (Bool.false_ne_true hh).elim

end PEqualNP.Outside.L_meta_2413

theorem PEqualNP.Outside.L_meta_2413 : ∀ (n N M : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → Function.Injective pw → Function.Injective lw → (∀ (p1 : Fin N) (l1 : Fin M), pw p1 ≠ lw l1) → (∀ p2 : Fin N, pw p2 < n) → (∀ l2 : Fin M, lw l2 < n) → (∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 → (∀ p3 ∈ P, ∀ l3 ∈ Y, ¬ I p3 l3) → PEqualNP.MetaComplexity.circuitFun n C (fun k3 : Fin n => decide (k3.val ∈ P.image pw ∪ Y.image lw)) = false) → ∀ (j a b : ℕ) (p p' : Fin N), (j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = a ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = b) ∨ (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0) = b ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0) = a))) → a ≠ b → (∀ z1 : Fin n → Bool, (∃ h1 : pw p < n, z1 ⟨pw p, h1⟩ = true) → (C.wires (List.ofFn z1)).getD (b) false = true → PEqualNP.MetaComplexity.circuitFun n C z1 = true) → (C.wires (List.ofFn (fun k5 : Fin n => decide (k5.val = pw p)))).getD (a) false = true → (∀ z2 : Fin n → Bool, (∃ h2 : pw p' < n, z2 ⟨pw p', h2⟩ = true) → (C.wires (List.ofFn z2)).getD (a) false = true → PEqualNP.MetaComplexity.circuitFun n C z2 = true) → (C.wires (List.ofFn (fun k6 : Fin n => decide (k6.val = pw p')))).getD (b) false = true → False := by
  intro n N M pw lw I C hC _ _ _ hpw _ hS j a b p p' _ _ _ ha h3 _
  have hz := hS {p, p'} ∅ Finset.card_le_two (by simp) (by simp)
  have hm := PEqualNP.Outside.L_meta_2413.wires_mono C hC.1
    (fun k5 : Fin n => decide (k5.val = pw p))
    (fun k3 : Fin n => decide (k3.val ∈ ({p, p'} : Finset (Fin N)).image pw ∪ (∅ : Finset (Fin M)).image lw))
    (by
      intro k hk
      have hk' : k.val = pw p := by simpa using hk
      simp [hk']) a ha
  have h := h3 (fun k3 : Fin n => decide (k3.val ∈ ({p, p'} : Finset (Fin N)).image pw ∪ (∅ : Finset (Fin M)).image lw))
    ⟨hpw p', by simp⟩ hm
  rw [hz] at h
  exact Bool.false_ne_true h
