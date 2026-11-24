import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1951

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

private lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

private lemma all_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).all id = true ↔ ∀ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp

private lemma any_true (l : List ℕ) (f : ℕ → Bool) :
    (l.map f).any id = true ↔ ∃ i ∈ l, f i = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp

private def Le (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ t, u.getD t false = true → v.getD t false = true

private lemma step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : List Bool) (h : Le u v) : Le (step u g) (step v g) := by
  refine ⟨by rw [step_len, step_len, h.1], fun t ht => ?_⟩
  by_cases hlt : t < u.length
  · rw [step_lt _ _ _ hlt] at ht
    rw [step_lt _ _ _ (by rw [← h.1]; exact hlt)]
    exact h.2 t ht
  · by_cases heq : t = u.length
    · rw [step_last _ _ _ heq] at ht
      rw [step_last _ _ _ (heq.trans h.1)]
      rcases hop with hand | hor
      · rw [hand] at ht ⊢
        exact (all_true _ _).mpr (fun i hi => h.2 i ((all_true _ _).mp ht i hi))
      · rw [hor] at ht ⊢
        obtain ⟨i, hi, hti⟩ := (any_true _ _).mp ht
        exact (any_true _ _).mpr ⟨i, hi, h.2 i hti⟩
    · rw [List.getD_eq_default _ _ (by rw [step_len]; omega)] at ht
      exact Bool.noConfusion ht

private lemma wires_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ u v : List Bool, Le u v → Le (gs.foldl step u) (gs.foldl step v) := by
  induction gs with
  | nil =>
    intro u v h
    exact h
  | cons g gs ih =>
    intro u v h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (step_mono g (hg g (List.mem_cons.mpr (Or.inl rfl))) u v h)

private lemma ofFn_getD_true {n : ℕ} (x : Fin n → Bool) (t : ℕ)
    (h : (List.ofFn x).getD t false = true) : ∃ ht : t < n, x ⟨t, ht⟩ = true := by
  by_cases ht : t < n
  · refine ⟨ht, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simpa using ht)] at h
    simpa using h
  · rw [List.getD_eq_default _ _ (by simpa using ht)] at h
    exact Bool.noConfusion h

private lemma ofFn_getD_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

private lemma ofFn_le {n : ℕ} (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    Le (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, fun t ht => ?_⟩
  obtain ⟨htn, hx⟩ := ofFn_getD_true x t ht
  exact (ofFn_getD_val y ⟨t, htn⟩).trans (h _ hx)

private lemma append_mono {N : ℕ} (x y : Fin N → Bool) (h : ∀ a, x a = true → y a = true) :
    ∀ i : Fin (N + N), Fin.append x (fun _ : Fin N => false) i = true →
      Fin.append y (fun _ : Fin N => false) i = true := by
  intro i
  induction i using Fin.addCases with
  | left a =>
    intro hx
    rw [Fin.append_left] at hx ⊢
    exact h a hx
  | right b =>
    intro hx
    rw [Fin.append_right] at hx
    exact Bool.noConfusion hx

end PEqualNP.Outside.L_meta_1951

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1951 : (∀ (N231 : ℕ) (I231 : Fin N231 → Fin N231 → Prop) [DecidableRel I231] (C231 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g231 ∈ C231.gates, (g231.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g231.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g231.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N231 + N231) C231) → (∀ j231 < C231.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231 0 = 0) ∨ (∀ h231 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231).inputs, (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231 0 = 0)) → (∀ p231 p231x1 w231 w231x1 : Fin N231, p231 ≠ p231x1 → w231 ≠ w231x1 → I231 p231 w231 → I231 p231x1 w231 → I231 p231 w231x1 → I231 p231x1 w231x1 → False) → (∃ p231x2 w231x2 : Fin N231, I231 p231x2 w231x2) → (∀ p231x3 w231x3 : Fin N231, I231 p231x3 w231x3 → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append (fun a231 : Fin N231 => decide (a231 = p231x3)) (fun a231x1 : Fin N231 => decide (a231x1 = w231x3))) = true) → (∀ x231 y231 : Fin N231 → Bool, (Finset.univ.filter (fun l231 : Fin N231 => y231 l231 = true)).card ≤ 1 → (¬ ∃ p231x4 w231x4 : Fin N231, I231 p231x4 w231x4 ∧ x231 p231x4 = true ∧ y231 w231x4 = true) → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231 y231) = false) → ∀ mixed231 : ℕ → Prop, mixed231 = (fun i231x1 : ℕ => 0 < (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD i231x1 0 ∧ 0 < (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x1 0) → ∀ cone231 : ℕ → Prop, cone231 = (fun j231x1 : ℕ => j231x1 < C231.gates.length ∧ mixed231 (N231 + N231 + j231x1) ∧ Relation.ReflTransGen (fun a231x2 b231 : ℕ => a231x2 < b231 ∧ ∃ f231 : Fin C231.gates.length, b231 = N231 + N231 + f231.val ∧ a231x2 ∈ (C231.gates.get f231).inputs) (N231 + N231 + j231x1) C231.output) → ∀ gok231 : (Fin N231 → Bool) → ℕ → Prop, gok231 = (fun (x231x1 : Fin N231 → Bool) (j231x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i231x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x2).inputs, (C231.lineDegrees (N231 + N231) (Finset.Ico N231 (N231 + N231))).getD i231x2 0 = 0 ∧ (C231.wires (List.ofFn (Fin.append x231x1 (fun u231 : Fin N231 => false)))).getD i231x2 false = true) → ∀ step231 : (Fin N231 → Bool) → ℕ → ℕ → Prop, step231 = (fun (x231x2 : Fin N231 → Bool) (j231x3 j231x4 : ℕ) => cone231 j231x4 ∧ N231 + N231 + j231x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x4).inputs ∧ gok231 x231x2 j231x4) → ∀ lvx231 : (Fin N231 → Bool) → ℕ → Prop, lvx231 = (fun (x231x3 : Fin N231 → Bool) (j231x5 : ℕ) => cone231 j231x5 ∧ gok231 x231x3 j231x5 ∧ ∃ j231x6 : ℕ, N231 + N231 + j231x6 = C231.output ∧ Relation.ReflTransGen (step231 x231x3) j231x5 j231x6) → ∀ slot231 : ℕ → ℕ → Prop, slot231 = (fun h231x1 j231x7 : ℕ => cone231 j231x7 ∧ h231x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C231 j231x7).inputs ∧ (C231.lineDegrees (N231 + N231) (Finset.range N231)).getD h231x1 0 = 0) → ∀ ap231 : ℕ → Fin N231 → Prop, ap231 = (fun (h231x2 : ℕ) (p231x5 : Fin N231) => ∃ j231x8 : ℕ, slot231 h231x2 j231x8 ∧ lvx231 (fun a231x3 : Fin N231 => decide (a231x3 = p231x5)) j231x8) → ∀ lh231 : ℕ → Fin N231 → Prop, lh231 = (fun (h231x3 : ℕ) (w231x5 : Fin N231) => (C231.wires (List.ofFn (Fin.append (fun u231x1 : Fin N231 => false) (fun a231x4 : Fin N231 => decide (a231x4 = w231x5))))).getD h231x3 false = true) → ∀ lpw231 : ℕ → Fin N231 → Prop, lpw231 = (fun (h231x4 : ℕ) (w231x6 : Fin N231) => ∀ w231x7 : Fin N231, lh231 h231x4 w231x7 ↔ w231x7 = w231x6) → ∀ ppw231 : ℕ → Fin N231 → Prop, ppw231 = (fun (h231x5 : ℕ) (p231x6 : Fin N231) => (∃ w231x8 w231x9 : Fin N231, w231x8 ≠ w231x9 ∧ lh231 h231x5 w231x8 ∧ lh231 h231x5 w231x9) ∧ ∀ p231x7 : Fin N231, ap231 h231x5 p231x7 ↔ p231x7 = p231x6) → ∀ lps231 : Fin N231 → Fin N231 → Prop, lps231 = (fun p231x8 w231x10 : Fin N231 => ∃ h231x6 : ℕ, lpw231 h231x6 w231x10 ∧ ap231 h231x6 p231x8) → ∀ pps231 : Fin N231 → Fin N231 → Prop, pps231 = (fun p231x9 w231x11 : Fin N231 => ∃ h231x7 : ℕ, ppw231 h231x7 p231x9 ∧ lh231 h231x7 w231x11) → (∃ j231x9 : ℕ, N231 + N231 + j231x9 = C231.output ∧ cone231 j231x9) ∧ (∀ (x231x4 y231x1 : Fin N231 → Bool) (h231x8 j231x10 : ℕ), slot231 h231x8 j231x10 → lvx231 x231x4 j231x10 → (C231.wires (List.ofFn (Fin.append (fun u231x2 : Fin N231 => false) y231x1))).getD h231x8 false = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x4 y231x1) = true) ∧ (∀ x231x5 y231x2 : Fin N231 → Bool, PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 y231x2) = true → PEqualNP.MetaComplexity.circuitFun (N231 + N231) C231 (Fin.append x231x5 (fun u231x3 : Fin N231 => false)) = false → ∃ h231x9 j231x11 : ℕ, slot231 h231x9 j231x11 ∧ lvx231 x231x5 j231x11 ∧ (C231.wires (List.ofFn (Fin.append (fun u231x4 : Fin N231 => false) y231x2))).getD h231x9 false = true) ∧ (∀ (h231x10 j231x12 : ℕ) (w231x12 : Fin N231), slot231 h231x10 j231x12 → lh231 h231x10 w231x12 → ¬ lvx231 (fun a231x5 : Fin N231 => decide (¬ I231 a231x5 w231x12)) j231x12) ∧ (∀ (h231x11 : ℕ) (p231x10 w231x13 : Fin N231), ap231 h231x11 p231x10 → lh231 h231x11 w231x13 → I231 p231x10 w231x13) ∧ (∀ p231x11 w231x14 : Fin N231, I231 p231x11 w231x14 → lps231 p231x11 w231x14 ∨ pps231 p231x11 w231x14)) → ∀ (N240 : ℕ) (I240 : Fin N240 → Fin N240 → Prop) [DecidableRel I240] (C240 : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g240 ∈ C240.gates, (g240.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g240.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g240.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N240 + N240) C240) → (∀ j240 < C240.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i240 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).inputs, (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240 0 = 0) ∨ (∀ h240 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240).inputs, (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD h240 0 = 0)) → (∀ p240 p240x1 w240 w240x1 : Fin N240, p240 ≠ p240x1 → w240 ≠ w240x1 → I240 p240 w240 → I240 p240x1 w240 → I240 p240 w240x1 → I240 p240x1 w240x1 → False) → (∃ p240x2 w240x2 : Fin N240, I240 p240x2 w240x2) → (∀ p240x3 w240x3 : Fin N240, I240 p240x3 w240x3 → PEqualNP.MetaComplexity.circuitFun (N240 + N240) C240 (Fin.append (fun a240 : Fin N240 => decide (a240 = p240x3)) (fun a240x1 : Fin N240 => decide (a240x1 = w240x3))) = true) → (∀ x240 y240 : Fin N240 → Bool, (Finset.univ.filter (fun l240 : Fin N240 => y240 l240 = true)).card ≤ 1 → (¬ ∃ p240x4 w240x4 : Fin N240, I240 p240x4 w240x4 ∧ x240 p240x4 = true ∧ y240 w240x4 = true) → PEqualNP.MetaComplexity.circuitFun (N240 + N240) C240 (Fin.append x240 y240) = false) → ∀ mixed240 : ℕ → Prop, mixed240 = (fun i240x1 : ℕ => 0 < (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD i240x1 0 ∧ 0 < (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240x1 0) → ∀ cone240 : ℕ → Prop, cone240 = (fun j240x1 : ℕ => j240x1 < C240.gates.length ∧ mixed240 (N240 + N240 + j240x1) ∧ Relation.ReflTransGen (fun a240x2 b240 : ℕ => a240x2 < b240 ∧ ∃ f240 : Fin C240.gates.length, b240 = N240 + N240 + f240.val ∧ a240x2 ∈ (C240.gates.get f240).inputs) (N240 + N240 + j240x1) C240.output) → ∀ gok240 : (Fin N240 → Bool) → ℕ → Prop, gok240 = (fun (x240x1 : Fin N240 → Bool) (j240x2 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ ∃ i240x2 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x2).inputs, (C240.lineDegrees (N240 + N240) (Finset.Ico N240 (N240 + N240))).getD i240x2 0 = 0 ∧ (C240.wires (List.ofFn (Fin.append x240x1 (fun u240 : Fin N240 => false)))).getD i240x2 false = true) → ∀ step240 : (Fin N240 → Bool) → ℕ → ℕ → Prop, step240 = (fun (x240x2 : Fin N240 → Bool) (j240x3 j240x4 : ℕ) => cone240 j240x4 ∧ N240 + N240 + j240x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x4).inputs ∧ gok240 x240x2 j240x4) → ∀ slot240 : ℕ → ℕ → Prop, slot240 = (fun h240x1 j240x5 : ℕ => cone240 j240x5 ∧ h240x1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C240 j240x5).inputs ∧ (C240.lineDegrees (N240 + N240) (Finset.range N240)).getD h240x1 0 = 0) → ∀ lh240 : ℕ → Fin N240 → Prop, lh240 = (fun (h240x2 : ℕ) (w240x5 : Fin N240) => (C240.wires (List.ofFn (Fin.append (fun u240x1 : Fin N240 => false) (fun a240x3 : Fin N240 => decide (a240x3 = w240x5))))).getD h240x2 false = true) → ∀ (h240x3 j240x6 j240x7 : ℕ) (w240x6 p240x5 : Fin N240), slot240 h240x3 j240x6 → lh240 h240x3 w240x6 → gok240 (fun a240x4 : Fin N240 => decide (¬ I240 a240x4 w240x6)) j240x6 → Relation.ReflTransGen (step240 (fun a240x5 : Fin N240 => decide (¬ I240 a240x5 w240x6))) j240x6 j240x7 → ¬ I240 p240x5 w240x6 → ∀ j240x8 : ℕ, N240 + N240 + j240x8 = C240.output → ¬ Relation.ReflTransGen (step240 (fun a240x6 : Fin N240 => decide (a240x6 = p240x5))) j240x7 j240x8 := by
  intro H N I _ C hC hAnd h4 hE hT hF mixed hmixed cone hcone gok hgok stp hstp slot hslot
    lh hlh h j6 j7 w p hs hl hg hpath hnI j8 hout hpath2
  have key := H N I C hC hAnd h4 hE hT hF mixed hmixed cone hcone gok hgok stp hstp _ rfl
    slot hslot _ rfl lh hlh _ rfl _ rfl _ rfl _ rfl
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hC.1 g hg).1
  have hx : ∀ a : Fin N, decide (a = p) = true → decide (¬ I a w) = true := by
    intro a ha
    simp only [decide_eq_true_eq] at ha ⊢
    subst ha
    exact hnI
  have hwire : ∀ i, (C.wires (List.ofFn (Fin.append (fun a : Fin N => decide (a = p))
      (fun _ : Fin N => false)))).getD i false = true →
      (C.wires (List.ofFn (Fin.append (fun a : Fin N => decide (¬ I a w))
      (fun _ : Fin N => false)))).getD i false = true := by
    intro i hi
    exact (PEqualNP.Outside.L_meta_1951.wires_mono C.gates hops _ _
      (PEqualNP.Outside.L_meta_1951.ofFn_le _ _
        (PEqualNP.Outside.L_meta_1951.append_mono _ _ hx))).2 i hi
  have hgok' : ∀ j, gok (fun a => decide (a = p)) j → gok (fun a => decide (¬ I a w)) j := by
    intro j hj
    rw [hgok] at hj ⊢
    rcases hj with hor | ⟨i, hi, hdeg, hv⟩
    · exact Or.inl hor
    · exact Or.inr ⟨i, hi, hdeg, hwire i hv⟩
  have hmono : ∀ a b, Relation.ReflTransGen (stp (fun a => decide (a = p))) a b →
      Relation.ReflTransGen (stp (fun a => decide (¬ I a w))) a b := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hcd ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rw [hstp] at hcd ⊢
      exact ⟨hcd.1, hcd.2.1, hgok' _ hcd.2.2⟩
  have hpath3 := hmono j7 j8 hpath2
  have hs' := hs
  rw [hslot] at hs'
  exact key.2.2.2.1 h j6 w hs hl ⟨hs'.1, hg, j8, hout, hpath.trans hpath3⟩
