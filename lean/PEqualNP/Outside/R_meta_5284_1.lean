import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_5284_1
    (oneDirty : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      0 < n →
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∀ (C : Circuit), Monotone2 C → circuitFun n C = graphFun G ∅ →
        (∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ u : Fin n,
          gateVal n C j (pairInput u u) = false) →
        (∃ j, j < C.size ∧ (gateAt C j).op = GateOp.and ∧
          (∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true) ∧
          ∀ k < C.size, (gateAt C k).op = GateOp.and →
            (∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C k (pairInput u v) = true) → k = j) →
        ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
          (∀ u v : Fin n, G.Adj u v → D.eval (List.ofFn (pairInput u v)) = true) ∧
          (∀ u : Fin n, D.eval (List.ofFn (pairInput u u)) = false) ∧
          ∀ j < D.size, (gateAt D j).op = GateOp.and →
            ∀ u v : Fin n, ¬ G.Adj u v → gateVal n D j (pairInput u v) = false)
    (manyDirty : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      0 < n →
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∀ (C : Circuit), Monotone2 C → circuitFun n C = graphFun G ∅ →
        (∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ u : Fin n,
          gateVal n C j (pairInput u u) = false) →
        (∃ j1 j2, j1 ≠ j2 ∧
          j1 < C.size ∧ (gateAt C j1).op = GateOp.and ∧
            (∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j1 (pairInput u v) = true) ∧
          j2 < C.size ∧ (gateAt C j2).op = GateOp.and ∧
            (∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j2 (pairInput u v) = true)) →
        ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧
          (∀ u v : Fin n, G.Adj u v → D.eval (List.ofFn (pairInput u v)) = true) ∧
          (∀ u : Fin n, D.eval (List.ofFn (pairInput u u)) = false) ∧
          ∀ j < D.size, (gateAt D j).op = GateOp.and →
            ∀ u v : Fin n, ¬ G.Adj u v → gateVal n D j (pairInput u v) = false) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   have x4 : (Fin x1 → Bool) → Bool := fun (x4 : Fin x1 → Bool) => Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), x2.Adj x5 x6 ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true);   have x5 : Finset (Fin x1) → Fin x1 → Bool := fun (x5 : Finset (Fin x1)) (x6 : Fin x1) => Decidable.decide (x6 ∈ x5);   have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Finset (Fin x1)), x11.card ≤ (1 : ℕ) → (x6.wires (List.ofFn (x5 x11))).getD (x1 + x7) Bool.false = Bool.false;   (∀ (x7 x8 x9 : Fin x1), x2.Adj x7 x8 → x2.Adj x8 x9 → ¬x2.Adj x9 x7) → (∀ (x8 x9 x10 x11 : Fin x1), x2.Adj x8 x9 → x2.Adj x9 x10 → x2.Adj x10 x11 → x2.Adj x11 x8 → x8 = x10 ∨ x9 = x11) → ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x1 → Bool), x9.eval (List.ofFn x11) = x4 x11) → x6 x9 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ x13.size ≤ x9.size ∧ (∀ (x14 x15 : Fin x1), x2.Adj x14 x15 → x13.eval (List.ofFn (x5 {x14, x15})) = Bool.true) ∧ (∀ (x14 : Fin x1), x13.eval (List.ofFn (x5 {x14})) = Bool.false) ∧ ∀ (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x13.gates[x14]? = Option.some x15 → x15.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x18 : Finset (Fin x1)), x18.card ≤ (2 : ℕ) → (x13.wires (List.ofFn (x5 x18))).getD (x1 + x14) Bool.false = Bool.true → ∃ x21 ∈ x18, ∃ x22 ∈ x18, x2.Adj x21 x22 := by
  intro n G inst x4 x5 x6 htri hc4 C hmon hcomp hsing
  have wires_mono : ∀ (D : Circuit), Monotone2 D →
      ∀ (a b : List Bool), a.length = b.length →
      (∀ k, a.getD k false = true → b.getD k false = true) →
      ∀ k, (D.wires a).getD k false = true → (D.wires b).getD k false = true := by
    intro D hDm
    suffices ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
        ∀ (a b : List Bool), a.length = b.length →
        (∀ k, a.getD k false = true → b.getD k false = true) →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).length =
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).length ∧
        ∀ k, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) a).getD k false = true →
             (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) b).getD k false = true by
      intro a b hlen hle k hk
      exact (this D.gates (fun g hg => (hDm g hg).1) a b hlen hle).2 k hk
    intro gs
    induction gs with
    | nil => intro _ a b hlen hle; exact ⟨hlen, hle⟩
    | cons g gs ih =>
      intro hgs a b hlen hle
      simp only [List.foldl_cons]
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
      · simp [hlen]
      · intro k hk
        have hg_mono : g.op.eval (g.inputs.map fun i => a.getD i false) = true →
            g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
          have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
            simpa using hgs g (List.mem_cons_self ..)
          rcases hop with hop | hop
          · rw [hop]
            change (g.inputs.map fun i => a.getD i false).all id = true →
                (g.inputs.map fun i => b.getD i false).all id = true
            simp only [List.all_eq_true, List.mem_map, id_eq]
            rintro H _ ⟨i, hi, rfl⟩
            exact hle i (H _ ⟨i, hi, rfl⟩)
          · rw [hop]
            change (g.inputs.map fun i => a.getD i false).any id = true →
                (g.inputs.map fun i => b.getD i false).any id = true
            simp only [List.any_eq_true, List.mem_map, id_eq]
            rintro ⟨_, ⟨i, hi, rfl⟩, hia⟩
            exact ⟨_, ⟨i, hi, rfl⟩, hle i hia⟩
        by_cases hkl : k < a.length
        · rw [List.getD_append _ _ _ _ hkl] at hk
          rw [List.getD_append _ _ _ _ (by omega)]
          exact hle k hk
        · rw [List.getD_append_right _ _ _ _ (by omega)] at hk
          rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
          by_cases hke : k - a.length = 0
          · rw [hke] at hk ⊢; simpa using hg_mono (by simpa using hk)
          · have hge : 1 ≤ k - a.length := by omega
            rw [List.getD_eq_default _ _ (by simpa using hge)] at hk
            exact Bool.noConfusion hk
  by_cases hn : n = 0
  · subst hn
    refine ⟨C, hmon, le_rfl, fun u => Fin.elim0 u, fun u => Fin.elim0 u, ?_⟩
    intro j g hg hgop S _ hval
    have hSe : S = ∅ := Finset.eq_empty_of_isEmpty S
    have hf := hsing j g hg hgop S (by simp [hSe])
    rw [hf] at hval
    exact Bool.noConfusion hval
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hpair : ∀ u v : Fin n, x5 {u, v} = pairInput u v := by
    intro u v; funext w
    change decide (w ∈ ({u, v} : Finset (Fin n))) = decide (w = u ∨ w = v)
    simp
  have hsing_eq : ∀ u : Fin n, x5 {u} = pairInput u u := by
    intro u; funext w
    change decide (w ∈ ({u} : Finset (Fin n))) = decide (w = u ∨ w = u)
    simp
  have finish : ∀ D : Circuit,
      (Monotone2 D ∧ D.size ≤ C.size ∧
        (∀ u v : Fin n, G.Adj u v → D.eval (List.ofFn (pairInput u v)) = true) ∧
        (∀ u : Fin n, D.eval (List.ofFn (pairInput u u)) = false) ∧
        ∀ j < D.size, (gateAt D j).op = GateOp.and →
          ∀ u v : Fin n, ¬ G.Adj u v → gateVal n D j (pairInput u v) = false) →
      ∃ x13 : Circuit, Monotone2 x13 ∧ x13.size ≤ C.size ∧
        (∀ x14 x15 : Fin n, G.Adj x14 x15 → x13.eval (List.ofFn (x5 {x14, x15})) = true) ∧
        (∀ x14 : Fin n, x13.eval (List.ofFn (x5 {x14})) = false) ∧
        ∀ (x14 : ℕ) (x15 : Gate), x13.gates[x14]? = some x15 → x15.op = GateOp.and →
          ∀ x18 : Finset (Fin n), x18.card ≤ 2 →
          (x13.wires (List.ofFn (x5 x18))).getD (n + x14) false = true →
          ∃ x21 ∈ x18, ∃ x22 ∈ x18, G.Adj x21 x22 := by
    rintro D ⟨hDm, hDsz, hDacc, hDrej, hDclean⟩
    refine ⟨D, hDm, hDsz, ?_, ?_, ?_⟩
    · intro u v huv; rw [hpair u v]; exact hDacc u v huv
    · intro u; rw [hsing_eq u]; exact hDrej u
    · intro j g hg hgop S hSc hval
      have hg' := hg
      obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
      have hga : (gateAt D j).op = GateOp.and := by
        change (D.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.and
        rw [List.getD_eq_getElem?_getD, hg']
        exact hgop
      rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
      · let u0 : Fin n := ⟨0, hnpos⟩
        have hle : ∀ k, (List.ofFn (x5 ∅)).getD k false = true →
            (List.ofFn (pairInput u0 u0)).getD k false = true := by
          intro k hk
          by_cases hklt : k < n
          · simp [List.getD_eq_getElem?_getD, hklt, x5] at hk
          · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
            exact Bool.noConfusion hk
        have ht : gateVal n D j (pairInput u0 u0) = true :=
          wires_mono D hDm _ _ (by simp) hle (n + j) hval
        rw [hDclean j hj hga u0 u0 (G.loopless.irrefl u0)] at ht
        exact Bool.noConfusion ht
      · by_cases hS1 : S = {a}
        · subst hS1
          rw [hsing_eq a] at hval
          have hf := hDclean j hj hga a a (G.loopless.irrefl a)
          change (D.wires (List.ofFn (pairInput a a))).getD (n + j) false = false at hf
          rw [hf] at hval
          exact Bool.noConfusion hval
        · have hex : ∃ b ∈ S, b ≠ a := by
            by_contra hall
            push Not at hall
            apply hS1
            ext w
            exact ⟨fun hw => Finset.mem_singleton.mpr (hall w hw),
              fun hw => Finset.mem_singleton.mp hw ▸ ha⟩
          obtain ⟨b, hb, hba⟩ := hex
          have hSab : S = {a, b} := by
            symm
            apply Finset.eq_of_subset_of_card_le
            · intro w hw
              simp only [Finset.mem_insert, Finset.mem_singleton] at hw
              rcases hw with rfl | rfl <;> assumption
            · rw [Finset.card_pair hba.symm]
              exact hSc
          rw [hSab, hpair a b] at hval
          by_contra hno
          have hnab : ¬ G.Adj a b := fun hab => hno ⟨a, ha, b, hb, hab⟩
          have hf := hDclean j hj hga a b hnab
          change (D.wires (List.ofFn (pairInput a b))).getD (n + j) false = false at hf
          rw [hf] at hval
          exact Bool.noConfusion hval
  have hcf : circuitFun n C = graphFun G ∅ := by
    funext x
    change C.eval (List.ofFn x) =
      (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
       decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    rw [hcomp x]
    change decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) = _
    simp
  have hsing' : ∀ j < C.size, (gateAt C j).op = GateOp.and → ∀ u : Fin n,
      gateVal n C j (pairInput u u) = false := by
    intro j hj hop u
    have hj' : j < C.gates.length := hj
    have hg : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj'
    have hgop : C.gates[j].op = GateOp.and := by
      change (C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.and at hop
      rw [List.getD_eq_getElem?_getD, hg] at hop
      exact hop
    have hf := hsing j C.gates[j] hg hgop {u} (by simp)
    rw [hsing_eq u] at hf
    exact hf
  by_cases h0 : ∃ j, j < C.size ∧ (gateAt C j).op = GateOp.and ∧
      ∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C j (pairInput u v) = true
  · obtain ⟨j, hj, hja, hjd⟩ := h0
    by_cases h1 : ∀ k < C.size, (gateAt C k).op = GateOp.and →
        (∃ u v : Fin n, ¬ G.Adj u v ∧ gateVal n C k (pairInput u v) = true) → k = j
    · exact finish _ (oneDirty n G hnpos htri hc4 C hmon hcf hsing' ⟨j, hj, hja, hjd, h1⟩).choose_spec
    · push Not at h1
      obtain ⟨k, hk, hka, hkd, hkj⟩ := h1
      exact finish _ (manyDirty n G hnpos htri hc4 C hmon hcf hsing'
        ⟨j, k, hkj.symm, hj, hja, hjd, hk, hka, hkd⟩).choose_spec
  · apply finish C
    refine ⟨hmon, le_rfl, ?_, ?_, ?_⟩
    · intro u v huv
      rw [hcomp (pairInput u v)]
      change decide (∃ a b : Fin n, G.Adj a b ∧ decide (a = u ∨ a = v) = true ∧ decide (b = u ∨ b = v) = true) = true
      simp only [decide_eq_true_eq]
      exact ⟨u, v, huv, Or.inl rfl, Or.inr rfl⟩
    · intro u
      rw [hcomp (pairInput u u)]
      change decide (∃ a b : Fin n, G.Adj a b ∧ decide (a = u ∨ a = u) = true ∧ decide (b = u ∨ b = u) = true) = false
      simp only [decide_eq_false_iff_not]
      rintro ⟨a, b, hab, ha, hb⟩
      simp only [or_self, decide_eq_true_eq] at ha hb
      subst ha; subst hb
      exact G.loopless.irrefl _ hab
    · intro j hj hop u v hnab
      rw [Bool.eq_false_iff]
      intro ht
      exact h0 ⟨j, hj, hop, u, v, hnab, ht⟩
