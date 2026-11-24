import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1837

open PEqualNP.CircuitLowerBounds

def Le (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma op_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : ∀ i, a.getD i false = true → b.getD i false = true) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
  · simp only [List.all_map, List.all_eq_true, Function.comp, id]
    exact fun ha j hj => h j (ha j hj)
  · simp only [List.any_map, List.any_eq_true, Function.comp, id]
    rintro ⟨j, hj, ha⟩
    exact ⟨j, hj, h j ha⟩

lemma step_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : List Bool)
    (h : Le a b) :
    Le (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]) := by
  obtain ⟨hlen, hle⟩ := h
  refine ⟨by simp [hlen], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  rcases lt_trichotomy i a.length with hlt | heq | hgt
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (hlen ▸ hlt)]
    have := hle i (by rw [List.getD_eq_getElem?_getD]; exact hi)
    rwa [List.getD_eq_getElem?_getD] at this
  · subst heq
    rw [List.getElem?_append_right (le_refl _)] at hi
    rw [hlen, List.getElem?_append_right (le_refl _)]
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
    exact op_mono g hg a b hle hi
  · rw [List.getElem?_eq_none (by simp; omega)] at hi
    simp at hi

lemma foldl_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, Le a b →
      Le (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b) := by
  induction gs with
  | nil => intro a b h; exact h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons]
    exact ih (fun z hz => hgs z (by simp [hz])) _ _ (step_le g (hgs g (by simp)) a b h)

lemma fun_mono {n : ℕ} (C : Circuit) (hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true →
      PEqualNP.MetaComplexity.circuitFun n C y = true := by
  have base : Le (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases h : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using h)] at hi ⊢
      simp only [List.getElem_ofFn] at hi ⊢
      exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact absurd hi (by simp)
  intro hx
  exact (foldl_le C.gates hgs _ _ base).2 C.output hx

lemma append_mono {N : ℕ} (a a' b b' : Fin N → Bool) (ha : ∀ p, a p = true → a' p = true)
    (hb : ∀ l, b l = true → b' l = true) :
    ∀ i : Fin (N + N), Fin.append a b i = true → Fin.append a' b' i = true := by
  intro i
  refine Fin.addCases (fun p h => ?_) (fun l h => ?_) i
  · rw [Fin.append_left] at h ⊢; exact ha p h
  · rw [Fin.append_right] at h ⊢; exact hb l h

end PEqualNP.Outside.L_meta_1837

theorem PEqualNP.Outside.L_meta_1837 : (∀ (Nlv15 mlv15 : ℕ) (Clv15 : PEqualNP.CircuitLowerBounds.Circuit) (Slv15 Wlv15 : Finset (Fin Nlv15)) (pilv15 nulv15 : Fin Nlv15 → Bool) (sglv15 : ℕ → Fin 2), ((∀ glv15 ∈ Clv15.gates, (glv15.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Clv15) → Set.ncard {jlv15 : ℕ | jlv15 < Clv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15 0 = 0) ∨ (∀ hlv15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15 0 = 0))} ≤ mlv15 + 1 → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv15x1 : Fin Clv15.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x1 0 = 0) ∨ (∀ hlv15x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs, (Clv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val).inputs.getD (sglv15 jlv15x1.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15 jlv15x1.val))) Clv15.output) (Fin.append (fun plv15 : Fin Nlv15 => if plv15 ∈ Slv15 then (fun ulv15 : Fin Nlv15 => false) plv15 else pilv15 plv15) (fun llv15 : Fin Nlv15 => if llv15 ∈ Wlv15 then (fun ulv15x1 : Fin Nlv15 => false) llv15 else nulv15 llv15)) = true → PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x1 : Fin Nlv15 => if plv15x1 ∈ Slv15 then (fun ulv15x2 : Fin Nlv15 => false) plv15x1 else pilv15 plv15x1) (fun llv15x1 : Fin Nlv15 => if llv15x1 ∈ Wlv15 then (fun ulv15x3 : Fin Nlv15 => false) llv15x1 else nulv15 llv15x1)) = false → (∃ xlv15 ylv15 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x2 : Fin Nlv15 => if plv15x2 ∈ Slv15 then xlv15 plv15x2 else pilv15 plv15x2) (fun llv15x2 : Fin Nlv15 => if llv15x2 ∈ Wlv15 then ylv15 llv15x2 else nulv15 llv15x2)) = true) → ∃ Dlv15 : PEqualNP.CircuitLowerBounds.Circuit, ((∀ glv15x1 ∈ Dlv15.gates, (glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15x1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15x1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15 + Nlv15) Dlv15) ∧ Set.ncard {jlv15x2 : ℕ | jlv15x2 < Dlv15.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.Ico Nlv15 (Nlv15 + Nlv15))).getD ilv15x2 0 = 0) ∨ (∀ hlv15x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x2).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.range Nlv15)).getD hlv15x2 0 = 0))} ≤ mlv15 ∧ Dlv15.size ≤ Clv15.size ∧ (0 < Dlv15.gates.length ∧ (∀ jlv15x3 < Dlv15.gates.length, ∀ ilv15x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15 jlv15x3).inputs, (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x3 : Fin Nlv15 => (plv15x3 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x3 : Fin Nlv15 => Nlv15 + (llv15x3 : ℕ)) (Wlv15)ᶜ)).getD ilv15x3 0 = 0) ∧ (Dlv15.lineDegrees (Nlv15 + Nlv15) (Finset.image (fun plv15x4 : Fin Nlv15 => (plv15x4 : ℕ)) (Slv15)ᶜ ∪ Finset.image (fun llv15x4 : Fin Nlv15 => Nlv15 + (llv15x4 : ℕ)) (Wlv15)ᶜ)).getD Dlv15.output 0 = 0) ∧ ∀ xlv15x1 ylv15x1 : Fin Nlv15 → Bool, PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Dlv15 (Fin.append xlv15x1 ylv15x1) = PEqualNP.MetaComplexity.circuitFun (Nlv15 + Nlv15) Clv15 (Fin.append (fun plv15x5 : Fin Nlv15 => if plv15x5 ∈ Slv15 then xlv15x1 plv15x5 else pilv15 plv15x5) (fun llv15x5 : Fin Nlv15 => if llv15x5 ∈ Wlv15 then ylv15x1 llv15x5 else nulv15 llv15x5))) → ∀ (Nlv15b Klv15b mlv15b : ℕ) (Ilv15b : Fin Nlv15b → Fin Nlv15b → Prop) [DecidableRel Ilv15b] (Clv15b : PEqualNP.CircuitLowerBounds.Circuit) (Slv15b Wlv15b Xlv15b : Finset (Fin Nlv15b)) (wlv15b : Fin Nlv15b) (sglv15b : ℕ → Fin 2) (Splv15b Wplv15b : Finset (Fin Nlv15b)), ((∀ glv15b ∈ Clv15b.gates, (glv15b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15b + Nlv15b) Clv15b) → Set.ncard {jlv15b : ℕ | jlv15b < Clv15b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15b 0 = 0) ∨ (∀ hlv15b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15b).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15b 0 = 0))} ≤ mlv15b + 1 → ((0 < Clv15b.gates.length ∧ (∀ jlv15bx1 < Clv15b.gates.length, ∀ ilv15bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx1).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx5 : Fin Nlv15b => (plv15bx5 : ℕ)) (Slv15b)ᶜ ∪ Finset.image (fun llv15bx4 : Fin Nlv15b => Nlv15b + (llv15bx4 : ℕ)) (Wlv15b)ᶜ)).getD ilv15bx1 0 = 0) ∧ (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx6 : Fin Nlv15b => (plv15bx6 : ℕ)) (Slv15b)ᶜ ∪ Finset.image (fun llv15bx5 : Fin Nlv15b => Nlv15b + (llv15bx5 : ℕ)) (Wlv15b)ᶜ)).getD Clv15b.output 0 = 0) ∧ (∀ plv15bx3 ∈ Slv15b, ∀ llv15bx2 ∈ Wlv15b, Ilv15b plv15bx3 llv15bx2 → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Clv15b (Fin.append (fun plv15bx7 : Fin Nlv15b => decide (plv15bx7 ∈ ({plv15bx3} : Finset (Fin Nlv15b)))) (fun llv15bx6 : Fin Nlv15b => decide (llv15bx6 ∈ ({llv15bx2} : Finset (Fin Nlv15b))))) = true) ∧ (∀ Xlv15bx1 Ylv15b : Finset (Fin Nlv15b), Xlv15bx1 ⊆ Slv15b → Ylv15b ⊆ Wlv15b → Ylv15b.card ≤ Klv15b + 1 → (∀ plv15bx4 ∈ Xlv15bx1, ∀ llv15bx3 ∈ Ylv15b, ¬ Ilv15b plv15bx4 llv15bx3) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Clv15b (Fin.append (fun plv15bx8 : Fin Nlv15b => decide (plv15bx8 ∈ Xlv15bx1)) (fun llv15bx7 : Fin Nlv15b => decide (llv15bx7 ∈ Ylv15b))) = false)) → wlv15b ∈ Wlv15b → Xlv15b ⊆ Slv15b → (∀ plv15bx1 ∈ Xlv15b, ¬ Ilv15b plv15bx1 wlv15b) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) (PEqualNP.CircuitLowerBounds.Circuit.mk (List.ofFn (fun jlv15bx2 : Fin Clv15b.gates.length => @ite PEqualNP.CircuitLowerBounds.Gate ((PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15bx2 0 = 0) ∨ (∀ hlv15bx1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs, (Clv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15bx1 0 = 0))) (Classical.propDecidable _) (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [(PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs.getD (sglv15b jlv15bx2.val).val 0, (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val).inputs.getD (sglv15b jlv15bx2.val).val 0]) (PEqualNP.MetaComplexity.NestedCover.gateAt Clv15b jlv15bx2.val))) Clv15b.output) (Fin.append (fun plv15bx9 : Fin Nlv15b => decide (plv15bx9 ∈ Xlv15b)) (fun llv15bx8 : Fin Nlv15b => decide (llv15bx8 ∈ ({wlv15b} : Finset (Fin Nlv15b))))) = true → Splv15b = Slv15b.filter (fun ulv15b : Fin Nlv15b => ¬ Ilv15b ulv15b wlv15b ∧ ulv15b ∉ Xlv15b) → Wplv15b = Wlv15b.filter (fun llv15bx1 : Fin Nlv15b => llv15bx1 ≠ wlv15b ∧ ∀ plv15bx2 ∈ Xlv15b, ¬ Ilv15b plv15bx2 llv15bx1) → (∃ plv15b ∈ Splv15b, ∃ llv15b ∈ Wplv15b, Ilv15b plv15b llv15b) → ∃ Dlv15b : PEqualNP.CircuitLowerBounds.Circuit, ((∀ glv15bx1 ∈ Dlv15b.gates, (glv15bx1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ glv15bx1.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ glv15bx1.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (Nlv15b + Nlv15b) Dlv15b) ∧ Set.ncard {jlv15bx3 : ℕ | jlv15bx3 < Dlv15b.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ ((∃ ilv15bx3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.Ico Nlv15b (Nlv15b + Nlv15b))).getD ilv15bx3 0 = 0) ∨ (∀ hlv15bx2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx3).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.range Nlv15b)).getD hlv15bx2 0 = 0))} ≤ mlv15b ∧ Dlv15b.size ≤ Clv15b.size ∧ ((0 < Dlv15b.gates.length ∧ (∀ jlv15bx4 < Dlv15b.gates.length, ∀ ilv15bx4 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt Dlv15b jlv15bx4).inputs, (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx12 : Fin Nlv15b => (plv15bx12 : ℕ)) (Splv15b)ᶜ ∪ Finset.image (fun llv15bx11 : Fin Nlv15b => Nlv15b + (llv15bx11 : ℕ)) (Wplv15b)ᶜ)).getD ilv15bx4 0 = 0) ∧ (Dlv15b.lineDegrees (Nlv15b + Nlv15b) (Finset.image (fun plv15bx13 : Fin Nlv15b => (plv15bx13 : ℕ)) (Splv15b)ᶜ ∪ Finset.image (fun llv15bx12 : Fin Nlv15b => Nlv15b + (llv15bx12 : ℕ)) (Wplv15b)ᶜ)).getD Dlv15b.output 0 = 0) ∧ (∀ plv15bx10 ∈ Splv15b, ∀ llv15bx9 ∈ Wplv15b, Ilv15b plv15bx10 llv15bx9 → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Dlv15b (Fin.append (fun plv15bx14 : Fin Nlv15b => decide (plv15bx14 ∈ ({plv15bx10} : Finset (Fin Nlv15b)))) (fun llv15bx13 : Fin Nlv15b => decide (llv15bx13 ∈ ({llv15bx9} : Finset (Fin Nlv15b))))) = true) ∧ (∀ Xlv15bx2 Ylv15bx1 : Finset (Fin Nlv15b), Xlv15bx2 ⊆ Splv15b → Ylv15bx1 ⊆ Wplv15b → Ylv15bx1.card ≤ Klv15b → (∀ plv15bx11 ∈ Xlv15bx2, ∀ llv15bx10 ∈ Ylv15bx1, ¬ Ilv15b plv15bx11 llv15bx10) → PEqualNP.MetaComplexity.circuitFun (Nlv15b + Nlv15b) Dlv15b (Fin.append (fun plv15bx15 : Fin Nlv15b => decide (plv15bx15 ∈ Xlv15bx2)) (fun llv15bx14 : Fin Nlv15b => decide (llv15bx14 ∈ Ylv15bx1))) = false)) := by
  intro hkill N K m I _ C S W X w sg Sp Wp hC hcross hinst hw hXS hXw hacc hSp hWp hex
  obtain ⟨⟨hpos, hreads, hout⟩, hcomp, hsound⟩ := hinst
  have hops : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => (hC.1 g hg).1
  have hSpX : ∀ p ∈ Sp, p ∉ X := by
    intro p hp; rw [hSp, Finset.mem_filter] at hp; exact hp.2.2
  have hSpS : Sp ⊆ S := by
    intro p hp; rw [hSp, Finset.mem_filter] at hp; exact hp.1
  have hSpw : ∀ p ∈ Sp, ¬ I p w := by
    intro p hp; rw [hSp, Finset.mem_filter] at hp; exact hp.2.1
  have hWpw : ∀ l ∈ Wp, l ≠ w := by
    intro l hl; rw [hWp, Finset.mem_filter] at hl; exact hl.2.1
  have hWpW : Wp ⊆ W := by
    intro l hl; rw [hWp, Finset.mem_filter] at hl; exact hl.1
  have hWpX : ∀ l ∈ Wp, ∀ p ∈ X, ¬ I p l := by
    intro l hl; rw [hWp, Finset.mem_filter] at hl; exact hl.2.2
  -- the fixed input with nothing free switched on is the input (X, w)
  have eP : (fun p : Fin N => if p ∈ Sp then (fun _ : Fin N => false) p else decide (p ∈ X)) =
      (fun p : Fin N => decide (p ∈ X)) := by
    funext p
    by_cases hp : p ∈ Sp
    · simp [hp, hSpX p hp]
    · simp [hp]
  have eL : (fun l : Fin N => if l ∈ Wp then (fun _ : Fin N => false) l else
      decide (l ∈ ({w} : Finset (Fin N)))) = (fun l : Fin N => decide (l ∈ ({w} : Finset (Fin N)))) := by
    funext l
    by_cases hl : l ∈ Wp
    · simp [hl, hWpw l hl]
    · simp [hl]
  -- substituting free values into the fixed input
  have eX : ∀ X2 : Finset (Fin N), X2 ⊆ Sp →
      (fun p : Fin N => if p ∈ Sp then decide (p ∈ X2) else decide (p ∈ X)) =
        (fun p : Fin N => decide (p ∈ X ∪ X2)) := by
    intro X2 hX2
    funext p
    by_cases hp : p ∈ Sp
    · simp [hp, hSpX p hp]
    · have : p ∉ X2 := fun h => hp (hX2 h)
      simp [hp, this]
  have eY : ∀ Y : Finset (Fin N), Y ⊆ Wp →
      (fun l : Fin N => if l ∈ Wp then decide (l ∈ Y) else decide (l ∈ ({w} : Finset (Fin N)))) =
        (fun l : Fin N => decide (l ∈ insert w Y)) := by
    intro Y hY
    funext l
    by_cases hl : l ∈ Wp
    · have : l ≠ w := hWpw l hl
      simp [hl, this]
    · have : l ∉ Y := fun h => hl (hY h)
      simp [hl, this]
  -- the original circuit is false at (X, w)
  have hfalse : PEqualNP.MetaComplexity.circuitFun (N + N) C
      (Fin.append (fun p : Fin N => decide (p ∈ X)) (fun l : Fin N => decide (l ∈ ({w} : Finset (Fin N))))) = false :=
    hsound X {w} hXS (by simpa using hw) (by simp) (fun p hp l hl => by
      rw [Finset.mem_singleton] at hl; rw [hl]; exact hXw p hp)
  -- completeness transported: a free incident pair switches the circuit on
  have hon : ∀ p ∈ Sp, ∀ l ∈ Wp, I p l →
      PEqualNP.MetaComplexity.circuitFun (N + N) C
        (Fin.append (fun q : Fin N => if q ∈ Sp then decide (q ∈ ({p} : Finset (Fin N))) else decide (q ∈ X))
          (fun l' : Fin N => if l' ∈ Wp then decide (l' ∈ ({l} : Finset (Fin N))) else
            decide (l' ∈ ({w} : Finset (Fin N))))) = true := by
    intro p hp l hl hpl
    refine PEqualNP.Outside.L_meta_1837.fun_mono C hops _ _ ?_ (hcomp p (hSpS hp) l (hWpW hl) hpl)
    apply PEqualNP.Outside.L_meta_1837.append_mono
    · intro q hq
      have : q = p := by simpa using hq
      subst this
      simp [hp]
    · intro l' hl'
      have : l' = l := by simpa using hl'
      subst this
      simp [hl]
  obtain ⟨D, hD, hDcross, hDsize, hDreads, hDfun⟩ := hkill N m C Sp Wp
    (fun p : Fin N => decide (p ∈ X)) (fun l : Fin N => decide (l ∈ ({w} : Finset (Fin N)))) sg hC hcross
    (by rw [eP, eL]; exact hacc) (by rw [eP, eL]; exact hfalse)
    (by
      obtain ⟨p, hp, l, hl, hpl⟩ := hex
      exact ⟨fun q => decide (q ∈ ({p} : Finset (Fin N))), fun l' => decide (l' ∈ ({l} : Finset (Fin N))),
        hon p hp l hl hpl⟩)
  refine ⟨D, hD, hDcross, hDsize, ⟨hDreads, ?_, ?_⟩⟩
  · intro p hp l hl hpl
    rw [hDfun]
    exact hon p hp l hl hpl
  · intro X2 Y hX2 hY hcard hinc
    rw [hDfun, eX X2 hX2, eY Y hY]
    refine hsound (X ∪ X2) (insert w Y) (Finset.union_subset hXS (hX2.trans hSpS))
      (Finset.insert_subset hw (hY.trans hWpW))
      ((Finset.card_insert_le w Y).trans (by omega)) ?_
    intro p hp l hl
    rw [Finset.mem_union] at hp
    rw [Finset.mem_insert] at hl
    rcases hp with hp | hp <;> rcases hl with rfl | hl
    · exact hXw p hp
    · exact hWpX l (hY hl) p hp
    · exact hSpw p (hX2 hp)
    · exact hinc p hp l hl
