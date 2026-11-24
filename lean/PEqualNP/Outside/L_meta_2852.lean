import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2852_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def LeW (w1 w2 : List Bool) : Prop := ∀ i, w1.getD i false = true → w2.getD i false = true

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepW, List.length_append, List.length_cons]
    simp
    omega

lemma foldl_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma gate_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w1 w2 : List Bool)
    (h : LeW w1 w2) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w2.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg]
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 a ha
    exact h _ (h1 a ha)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨a, ha, h1⟩
    exact ⟨a, ha, h _ h1⟩

lemma step_le (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w1 w2 : List Bool)
    (hl : w1.length = w2.length) (h : LeW w1 w2) : LeW (stepW w1 g) (stepW w2 g) := by
  intro i hi
  by_cases h1 : i < w1.length
  · rw [stepW, List.getD_append _ _ _ _ h1] at hi
    rw [stepW, List.getD_append _ _ _ _ (hl ▸ h1)]
    exact h i hi
  · by_cases h2 : i = w1.length
    · subst h2
      have e1 : (stepW w1 g).getD w1.length false =
          g.op.eval (g.inputs.map fun i => w1.getD i false) := by
        simp [stepW, List.getD_eq_getElem?_getD]
      have e2 : (stepW w2 g).getD w1.length false =
          g.op.eval (g.inputs.map fun i => w2.getD i false) := by
        rw [hl]; simp [stepW, List.getD_eq_getElem?_getD]
      rw [e1] at hi
      rw [e2]
      exact gate_le g hg w1 w2 h hi
    · have e : (stepW w1 g).getD i false = false := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        have : i - w1.length ≠ 0 := by omega
        simp [this]
      rw [e] at hi
      exact absurd hi (by simp)

lemma run_le (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w1 w2 : List Bool, w1.length = w2.length → LeW w1 w2 →
      LeW (gs.foldl stepW w1) (gs.foldl stepW w2) := by
  induction gs with
  | nil => intro w1 w2 _ h; exact h
  | cons g gs ih =>
    intro w1 w2 hl h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (by simp [stepW, hl]) (step_le g (hgs g List.mem_cons_self) w1 w2 hl h)


lemma stepW_le_of_val (W : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => W.getD i false) = true →
      g2.op.eval (g2.inputs.map fun i => W.getD i false) = true) :
    LeW (stepW W g1) (stepW W g2) := by
  intro i hi
  by_cases h1 : i < W.length
  · rw [stepW, List.getD_append _ _ _ _ h1] at hi
    rw [stepW, List.getD_append _ _ _ _ h1]
    exact hi
  · by_cases h2 : i = W.length
    · subst h2
      have e1 : (stepW W g1).getD W.length false =
          g1.op.eval (g1.inputs.map fun i => W.getD i false) := by
        simp [stepW, List.getD_eq_getElem?_getD]
      have e2 : (stepW W g2).getD W.length false =
          g2.op.eval (g2.inputs.map fun i => W.getD i false) := by
        simp [stepW, List.getD_eq_getElem?_getD]
      rw [e1] at hi
      rw [e2]
      exact h hi
    · have e : (stepW W g1).getD i false = false := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        have : i - W.length ≠ 0 := by omega
        simp [this]
      rw [e] at hi
      exact absurd hi (by simp)

lemma swap_le (W : List Bool) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (p q d c b : ℕ) (hb : b < 2) (hc : [p, q].getD b 0 = c)
    (hdc : W.getD d false = true → W.getD c false = true) :
    LeW (stepW W ⟨op, [p, q].set b d⟩) (stepW W ⟨op, [p, q]⟩) := by
  apply stepW_le_of_val
  interval_cases b
  · simp only [List.getD_cons_zero] at hc
    subst hc
    rcases hop with rfl | rfl <;> simp [GateOp.eval] <;> tauto
  · simp only [List.getD_cons_succ, List.getD_cons_zero] at hc
    subst hc
    rcases hop with rfl | rfl <;> simp [GateOp.eval] <;> tauto

lemma split_le (pre post : List Gate) (gg g' : Gate)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or) (x : List Bool)
    (hgate : LeW (stepW (pre.foldl stepW x) g') (stepW (pre.foldl stepW x) gg)) :
    LeW ((pre ++ g' :: post).foldl stepW x) ((pre ++ gg :: post).foldl stepW x) := by
  simp only [List.foldl_append, List.foldl_cons]
  exact run_le post hpost _ _ (by simp [stepW]) hgate


def modC (C : Circuit) (g b d : ℕ) : Circuit :=
  ⟨C.gates.set g ⟨(gateAt C g).op, (gateAt C g).inputs.set b d⟩, C.output⟩

lemma gateAt_eq (C : Circuit) (g : ℕ) (hg : g < C.gates.length) : gateAt C g = C.gates[g] := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hg]

lemma gates_split (C : Circuit) (g : ℕ) (hg : g < C.gates.length) :
    C.gates = C.gates.take g ++ gateAt C g :: C.gates.drop (g + 1) := by
  rw [gateAt_eq C g hg, ← List.drop_eq_getElem_cons hg, List.take_append_drop]

lemma gates_set_split (C : Circuit) (g : ℕ) (hg : g < C.gates.length) (g' : Gate) :
    C.gates.set g g' = C.gates.take g ++ g' :: C.gates.drop (g + 1) := by
  rw [List.set_eq_take_append_cons_drop, if_pos hg]

lemma gateAt_mem (C : Circuit) (g : ℕ) (hg : g < C.gates.length) : gateAt C g ∈ C.gates := by
  rw [gateAt_eq C g hg]; exact List.getElem_mem hg

lemma gateAt_modC_self (C : Circuit) (g b d : ℕ) (hg : g < C.gates.length) :
    gateAt (modC C g b d) g = ⟨(gateAt C g).op, (gateAt C g).inputs.set b d⟩ := by
  simp [gateAt, modC, List.getD_eq_getElem?_getD, List.getElem?_set_self, hg]

lemma gateAt_modC_ne (C : Circuit) (g b d j : ℕ) (hne : g ≠ j) :
    gateAt (modC C g b d) j = gateAt C j := by
  simp [gateAt, modC, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma modC_ao2 (n : ℕ) (C : Circuit) (g b d : ℕ) (hao : IsAO2 n C) (hg : g < C.gates.length)
    (hd : d < n + g) : IsAO2 n (modC C g b d) := by
  obtain ⟨hand, hrb, hlen⟩ := hao
  have hmem := gateAt_mem C g hg
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    rcases List.mem_or_eq_of_mem_set hgt with h | h
    · exact hand gt h
    · subst h
      have h0 := hand _ hmem
      exact h0
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [modC] using hj
    by_cases hjg : g = j
    · subst hjg
      rw [gateAt_modC_self C g b d hg] at hi
      rcases List.mem_or_eq_of_mem_set hi with h | h
      · exact hrb g hg i h
      · omega
    · rw [gateAt_modC_ne C g b d j hjg] at hi
      exact hrb j hj' i hi
  · intro gt hgt
    rcases List.mem_or_eq_of_mem_set hgt with h | h
    · exact hlen gt h
    · subst h
      have h0 := hlen _ hmem
      simpa using h0


lemma swap_le' (W : List Bool) (gg : Gate) (hop : gg.op = GateOp.and ∨ gg.op = GateOp.or)
    (hlen : gg.inputs.length = 2) (b c d : ℕ) (hb : b < 2) (hc : gg.inputs.getD b 0 = c)
    (hdc : W.getD d false = true → W.getD c false = true) :
    LeW (stepW W ⟨gg.op, gg.inputs.set b d⟩) (stepW W gg) := by
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
  obtain ⟨op, ins⟩ := gg
  simp only at hpq hop hc ⊢
  subst hpq
  exact swap_le W op hop p q d c b hb hc hdc

lemma eval_eq_foldl (C : Circuit) (l : List Bool) :
    C.eval l = (C.gates.foldl stepW l).getD C.output false := rfl

lemma modC_le (n : ℕ) (C : Circuit) (g b c d : ℕ)
    (hao : IsAO2 n C) (hg : g < C.gates.length) (hb : b < 2)
    (hc : (gateAt C g).inputs.getD b 0 = c) (hd : d < n + g)
    (hdc : ∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true →
        Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true) :
    ∀ x : Fin n → Bool, circuitFun n (modC C g b d) x = true → circuitFun n C x = true := by
  intro x
  obtain ⟨hand, hrb, hlen⟩ := hao
  have hmem := gateAt_mem C g hg
  have hop := hand _ hmem
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (hlen _ hmem)
  have hcn : c < n + g := by
    apply hrb g hg c
    rw [← hc, hpq]
    interval_cases b <;> simp
  have hsplit := gates_split C g hg
  have hpost : ∀ gt ∈ C.gates.drop (g + 1), gt.op = GateOp.and ∨ gt.op = GateOp.or :=
    fun gt hgt => hand gt (List.mem_of_mem_drop hgt)
  have hWlen : ((C.gates.take g).foldl stepW (List.ofFn x)).length = n + g := by
    rw [foldl_len]; simp; omega
  have hdcW : ((C.gates.take g).foldl stepW (List.ofFn x)).getD d false = true →
      ((C.gates.take g).foldl stepW (List.ofFn x)).getD c false = true := by
    have h := hdc x
    simp only [eval_eq_foldl] at h
    rw [hsplit] at h
    simp only [List.foldl_append, List.foldl_cons] at h
    generalize hW : (C.gates.take g).foldl stepW (List.ofFn x) = W at h hWlen ⊢
    have hk : ∀ i, i < n + g → (stepW W (gateAt C g)).getD i false = W.getD i false :=
      fun i hi => List.getD_append _ _ _ _ (by omega)
    have hl : (stepW W (gateAt C g)).length = n + g + 1 := by simp [stepW, hWlen]
    rw [foldl_keep _ _ _ (by omega), foldl_keep _ _ _ (by omega), hk _ hd, hk _ hcn] at h
    exact h
  have hgate := swap_le' ((C.gates.take g).foldl stepW (List.ofFn x)) (gateAt C g) hop
    (hlen _ hmem) b c d hb hc hdcW
  have key := split_le (C.gates.take g) (C.gates.drop (g + 1)) (gateAt C g)
    ⟨(gateAt C g).op, (gateAt C g).inputs.set b d⟩ hpost (List.ofFn x) hgate
  intro h
  have h' : ((modC C g b d).gates.foldl stepW (List.ofFn x)).getD C.output false = true := h
  have e1 : (modC C g b d).gates = C.gates.take g ++ _ :: C.gates.drop (g + 1) :=
    gates_set_split C g hg _
  rw [e1] at h'
  have h2 := key _ h'
  rw [← hsplit] at h2
  exact h2


lemma ofFn_getD_true (n : ℕ) (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = true ↔ ∃ h : i < n, x ⟨i, h⟩ = true := by
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma circuit_mono (n : ℕ) (C : Circuit) (hand : AndOrOnly C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  have h := run_le C.gates hand (List.ofFn x) (List.ofFn y) (by simp) (by
    intro i hi
    rw [ofFn_getD_true] at hi ⊢
    obtain ⟨h1, h2⟩ := hi
    exact ⟨h1, hxy _ h2⟩) C.output
  exact h

lemma exists_min_below (n : ℕ) (F : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (hx : F x = true) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ F y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → F z = false := by
  classical
  let S : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => (∀ i, y i = true → x i = true) ∧ F y = true)
  have hS : S.Nonempty := ⟨x, by simp [S, hx]⟩
  obtain ⟨y, hyS, hmin⟩ := Finset.exists_min_image S
    (fun y => (Finset.univ.filter (fun i => y i = true)).card) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hyS
  refine ⟨y, hyS.1, hyS.2, ?_⟩
  intro z hz hne
  by_contra hcon
  have hzt : F z = true := by simpa using hcon
  have hzS : z ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun i hi => hyS.1 i (hz i hi), hzt⟩
  have hlt : (Finset.univ.filter (fun i => z i = true)).card <
      (Finset.univ.filter (fun i => y i = true)).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · by_contra hno
      push_neg at hno
      apply hne
      funext i
      cases hzi : z i
      · cases hyi : y i
        · rfl
        · exfalso
          have := hno i (by simp [hyi])
          simp [hzi] at this
      · exact (hz i hzi).symm
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hz i hi
  exact absurd (hmin z hzS) (by omega)


lemma modC_iff (n : ℕ) (C : Circuit) (g b d : ℕ) (hand : AndOrOnly (modC C g b d))
    (hle : ∀ x : Fin n → Bool, circuitFun n (modC C g b d) x = true → circuitFun n C x = true) :
    circuitFun n (modC C g b d) = circuitFun n C ↔
      (∀ x : Fin n → Bool, (circuitFun n C x = true ∧ ∀ y : Fin n → Bool,
        (∀ i, y i = true → x i = true) → y ≠ x → circuitFun n C y = false) →
        circuitFun n (modC C g b d) x = true) := by
  constructor
  · intro heq x hx
    rw [heq]
    exact hx.1
  · intro h
    funext x
    cases hCx : circuitFun n C x
    · cases hC' : circuitFun n (modC C g b d) x
      · rfl
      · exact absurd (hle x hC') (by simp [hCx])
    · obtain ⟨y, hyx, hCy, hmin⟩ := exists_min_below n (circuitFun n C) x hCx
      have h1 := h y ⟨hCy, fun z hz hne => hmin z hz hne⟩
      exact circuit_mono n (modC C g b d) hand y x hyx h1

end PEqualNP.Outside.L_meta_2852_aux

theorem PEqualNP.Outside.L_meta_2852 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b c d : ℕ), (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = c ∧ d < n + g ∧ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) ∧ (PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ↔ (∀ x : Fin n → Bool, (PEqualNP.MetaComplexity.circuitFun n C x = true ∧ ∀ y : Fin n → Bool, (∀ i, y i = true → x i = true) → y ≠ x → PEqualNP.MetaComplexity.circuitFun n C y = false) → PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true)) := by
  intro n C g b c d h
  obtain ⟨hao, hrb, hg, hb, hc, hd, hdc⟩ := h
  have hle := PEqualNP.Outside.L_meta_2852_aux.modC_le n C g b c d hao hg hb hc hd hdc
  have hao' := PEqualNP.Outside.L_meta_2852_aux.modC_ao2 n C g b d hao hg hd
  refine ⟨hao', ?_, hle, ?_⟩
  · simp [PEqualNP.Outside.L_meta_2852_aux.modC, PEqualNP.CircuitLowerBounds.Circuit.size]
  · exact PEqualNP.Outside.L_meta_2852_aux.modC_iff n C g b d hao'.1 hle
