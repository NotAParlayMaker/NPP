import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2852_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

private lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

private lemma getD_append_left_lt {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

private lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact getD_append_left_lt w _ i false hi

private lemma eval_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {l₁ l₂ : List Bool} (h : List.Forall₂ (fun a b => a = true → b = true) l₁ l₂) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · induction h with
    | nil => simp [GateOp.eval]
    | cons hab _ ih =>
      simp only [GateOp.eval, List.all_cons, id_eq, Bool.and_eq_true]
      rintro ⟨ha, ht⟩
      exact ⟨hab ha, ih ht⟩
  · induction h with
    | nil => simp [GateOp.eval]
    | cons hab _ ih =>
      simp only [GateOp.eval, List.any_cons, id_eq, Bool.or_eq_true]
      rintro (ha | ht)
      · exact Or.inl (hab ha)
      · exact Or.inr (ih ht)

private lemma forall₂_map_of_pointwise {α β : Type*} (R : β → β → Prop) (f₁ f₂ : α → β)
    (h : ∀ a, R (f₁ a) (f₂ a)) : ∀ l : List α, List.Forall₂ R (l.map f₁) (l.map f₂)
  | [] => List.Forall₂.nil
  | a :: l => List.Forall₂.cons (h a) (forall₂_map_of_pointwise R f₁ f₂ h l)

private lemma step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w₁ w₂ : List Bool) (hlen : w₁.length = w₂.length)
    (hle : ∀ i, w₁.getD i false = true → w₂.getD i false = true) :
    ∀ i, (step w₁ g).getD i false = true → (step w₂ g).getD i false = true := by
  intro i hi
  rcases lt_trichotomy i w₁.length with hlt | rfl | hgt
  · rw [step, getD_append_left_lt _ _ _ _ hlt] at hi
    rw [step, getD_append_left_lt _ _ _ _ (by omega)]
    exact hle i hi
  · rw [step, getD_snoc_eq] at hi
    rw [step, hlen, getD_snoc_eq]
    exact eval_mono hop (forall₂_map_of_pointwise _ _ _ (fun j => hle j) g.inputs) hi
  · have hdef : (step w₁ g).getD i false = false :=
      List.getD_eq_default _ _ (by simp [step]; omega)
    rw [hdef] at hi
    cases hi

private lemma foldl_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w₁ w₂ : List Bool) (hlen : w₁.length = w₂.length)
    (hle : ∀ i, w₁.getD i false = true → w₂.getD i false = true) :
    ∀ i, (gs.foldl step w₁).getD i false = true → (gs.foldl step w₂).getD i false = true := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hle
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (fun h hh => hAO h (List.mem_cons_of_mem g hh))
      (step w₁ g) (step w₂ g) (by simp [step, hlen])
      (step_mono g (hAO g (List.mem_cons_self ..)) w₁ w₂ hlen hle)

private lemma circuitFun_mono {n : ℕ} (C : Circuit) (hAO : AndOrOnly C)
    {y x : Fin n → Bool} (hyx : ∀ i, y i = true → x i = true)
    (hy : circuitFun n C y = true) : circuitFun n C x = true := by
  have h0 : ∀ i, (List.ofFn y).getD i false = true → (List.ofFn x).getD i false = true := by
    intro i hi
    by_cases hlt : i < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true,
        Option.getD_some] at hi ⊢
      exact hyx ⟨i, hlt⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      cases hi
  exact foldl_mono C.gates hAO (List.ofFn y) (List.ofFn x) (by simp) h0 C.output hy

private lemma list_split_at {α : Type*} (l : List α) (g : ℕ) (hg : g < l.length) :
    l = l.take g ++ l[g] :: l.drop (g + 1) := by
  apply List.ext_getElem
  · simp only [List.length_append, List.length_cons, List.length_take, List.length_drop]; omega
  · intro i hi₁ hi₂
    have htake : (l.take g).length = g := List.length_take_of_le (le_of_lt hg)
    rcases lt_trichotomy i g with hlt | rfl | hgt
    · rw [List.getElem_append_left (by omega), List.getElem_take]
    · rw [List.getElem_append_right (by omega)]
      simp [htake]
    · rw [List.getElem_append_right (by omega)]
      have hidx : i - (l.take g).length = (i - g - 1) + 1 := by omega
      simp only [hidx, List.getElem_cons_succ, List.getElem_drop]
      congr 1; omega

private lemma list_set_split {α : Type*} (l : List α) (g : ℕ) (hg : g < l.length) (a : α) :
    l.set g a = l.take g ++ a :: l.drop (g + 1) := by
  apply List.ext_getElem
  · simp only [List.length_set, List.length_append, List.length_cons, List.length_take, List.length_drop]; omega
  · intro i hi₁ hi₂
    have htake : (l.take g).length = g := List.length_take_of_le (le_of_lt hg)
    rcases lt_trichotomy i g with hlt | rfl | hgt
    · rw [List.getElem_set_ne (by omega), List.getElem_append_left (by omega), List.getElem_take]
    · rw [List.getElem_set_self (by omega), List.getElem_append_right (by omega)]
      simp [htake]
    · rw [List.getElem_set_ne (by omega), List.getElem_append_right (by omega)]
      have hidx : i - (l.take g).length = (i - g - 1) + 1 := by omega
      simp only [hidx, List.getElem_cons_succ, List.getElem_drop]
      congr 1; omega

private lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem C.gates _ hj

theorem main (n : ℕ) (C : Circuit) (g b c d : ℕ)
    (h : IsAO2 n C ∧ ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
      (gateAt C g).inputs.getD b 0 = c ∧ d < n + g ∧
      ∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true →
        Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true) :
    let g' : Gate := ⟨(gateAt C g).op, (gateAt C g).inputs.set b d⟩
    let C' : Circuit := ⟨C.gates.set g g', C.output⟩
    IsAO2 n C' ∧ C'.size = C.size ∧
    (∀ x : Fin n → Bool, circuitFun n C' x = true → circuitFun n C x = true) ∧
    (circuitFun n C' = circuitFun n C ↔
      ∀ x : Fin n → Bool,
        (circuitFun n C x = true ∧
          ∀ y : Fin n → Bool, (∀ i, y i = true → x i = true) → y ≠ x → circuitFun n C y = false) →
        circuitFun n C' x = true) := by
  rcases h with ⟨hAO, hRB, hg, hb, hc, hd, hdc⟩
  dsimp only
  set g' : Gate := ⟨(gateAt C g).op, (gateAt C g).inputs.set b d⟩
  set C' : Circuit := ⟨C.gates.set g g', C.output⟩
  have hgg : gateAt C g = C.gates[g] := gateAt_eq_getElem C g hg
  have hgg_mem : gateAt C g ∈ C.gates := by rw [hgg]; exact List.getElem_mem hg
  have hgg_op : (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or := hAO.1 _ hgg_mem
  have hgg_len : (gateAt C g).inputs.length = 2 := hAO.2.2 _ hgg_mem
  have hAO' : IsAO2 n C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro h hh
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hh
      have hj' : j < C.gates.length := by simpa [C'] using hj
      by_cases hjg : j = g
      · subst hjg
        simp only [C', List.getElem_set_self]
        exact hgg_op
      · simp only [C', List.getElem_set_ne (Ne.symm hjg)]
        exact hAO.1 _ (List.getElem_mem hj')
    · intro j hj i hi
      have hj' : j < C.gates.length := by simpa [C'] using hj
      rw [gateAt_eq_getElem C' j hj] at hi
      by_cases hjg : j = g
      · subst hjg
        simp only [C', List.getElem_set_self, g'] at hi
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hi
        have hk' : k < (gateAt C j).inputs.length := by simpa using hk
        by_cases hkb : k = b
        · subst hkb
          simp only [List.getElem_set_self]
          exact hd
        · simp only [List.getElem_set_ne (Ne.symm hkb)]
          exact hRB j hj' _ (List.getElem_mem hk')
      · simp only [C', List.getElem_set_ne (Ne.symm hjg)] at hi
        have hi' : i ∈ (gateAt C j).inputs := by rwa [gateAt_eq_getElem C j hj']
        exact hRB j hj' i hi'
    · intro h hh
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hh
      have hj' : j < C.gates.length := by simpa [C'] using hj
      by_cases hjg : j = g
      · subst hjg
        simp only [C', List.getElem_set_self, g', List.length_set]
        exact hgg_len
      · simp only [C', List.getElem_set_ne (Ne.symm hjg)]
        exact hAO.2.2 _ (List.getElem_mem hj')
  have hSize : C'.size = C.size := by simp [C', Circuit.size]
  have hLe : ∀ x : Fin n → Bool, circuitFun n C' x = true → circuitFun n C x = true := by
    intro x hx
    set pre := C.gates.take g
    set suf := C.gates.drop (g + 1)
    have hsp : C.gates = pre ++ C.gates[g] :: suf := list_split_at C.gates g hg
    have hsp' : C'.gates = pre ++ g' :: suf := list_set_split C.gates g hg g'
    set W := pre.foldl step (List.ofFn x)
    have hWlen : W.length = n + g := by
      rw [foldl_len, List.length_ofFn, List.length_take_of_le (le_of_lt hg)]
    have hWget : ∀ w < n + g, (C.wires (List.ofFn x)).getD w false = W.getD w false := by
      intro w hw
      rw [wires_eq_foldl, hsp, List.foldl_append]
      exact foldl_getD_lt (C.gates[g] :: suf) W w (by omega)
    have hc_lt : c < n + g := by
      have hcm : c ∈ (gateAt C g).inputs := by
        rw [← hc, List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem (by omega)
      exact hRB g hg c hcm
    have hdc_W : W.getD d false = true → W.getD c false = true := by
      intro hwd
      have h1 : Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true := by
        change (C.wires (List.ofFn x)).getD d false = true
        rw [hWget d hd]; exact hwd
      have h2 := hdc x h1
      change (C.wires (List.ofFn x)).getD c false = true at h2
      rwa [hWget c hc_lt] at h2
    have hStepLe : ∀ i, (step W g').getD i false = true → (step W C.gates[g]).getD i false = true := by
      intro i hi
      rcases lt_trichotomy i W.length with hlt | rfl | hgt
      · rw [step, getD_append_left_lt _ _ _ _ hlt] at hi ⊢
        exact hi
      · rw [step, getD_snoc_eq] at hi ⊢
        have hF2 : List.Forall₂ (fun a b => a = true → b = true)
            (g'.inputs.map fun k => W.getD k false)
            (C.gates[g].inputs.map fun k => W.getD k false) := by
          rw [← hgg]
          rcases hgi : (gateAt C g).inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
          · simp [hgi] at hgg_len
          · simp [hgi] at hgg_len
          · simp only [hgi, List.getD_eq_getElem?_getD] at hc
            have hb01 : b = 0 ∨ b = 1 := by omega
            rcases hb01 with rfl | rfl
            · simp only [List.getElem?_cons_zero, Option.getD_some] at hc
              subst hc
              simp only [g', hgi, List.set_cons_zero, List.map_cons, List.map_nil]
              exact List.Forall₂.cons hdc_W (List.Forall₂.cons id List.Forall₂.nil)
            · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some] at hc
              subst hc
              simp only [g', hgi, List.set_cons_succ, List.set_cons_zero, List.map_cons, List.map_nil]
              exact List.Forall₂.cons id (List.Forall₂.cons hdc_W List.Forall₂.nil)
          · simp [hgi] at hgg_len
        have hop_eq : g'.op = C.gates[g].op := by simp [g', hgg]
        rw [hop_eq] at hi
        exact eval_mono (hgg ▸ hgg_op) hF2 hi
      · have hdef : (step W g').getD i false = false :=
          List.getD_eq_default _ _ (by simp [step]; omega)
        rw [hdef] at hi; cases hi
    have hsufAO : ∀ h ∈ suf, h.op = GateOp.and ∨ h.op = GateOp.or :=
      fun h hh => hAO.1 h (List.mem_of_mem_drop hh)
    have hFin := foldl_mono suf hsufAO (step W g') (step W C.gates[g]) (by simp [step]) hStepLe C.output
    change (C'.wires (List.ofFn x)).getD C.output false = true at hx
    change (C.wires (List.ofFn x)).getD C.output false = true
    rw [wires_eq_foldl, hsp', List.foldl_append, List.foldl_cons] at hx
    rw [wires_eq_foldl, hsp, List.foldl_append, List.foldl_cons]
    exact hFin hx
  refine ⟨hAO', hSize, hLe, ?_⟩
  constructor
  · intro heq x hmin
    rw [heq]
    exact hmin.1
  · intro hmin
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hLe x
    · intro hx
      classical
      let wt (z : Fin n → Bool) : ℕ := (Finset.univ.filter fun i => z i = true).card
      let P (k : ℕ) : Prop := ∃ y : Fin n → Bool,
        (∀ i, y i = true → x i = true) ∧ circuitFun n C y = true ∧ wt y = k
      have hex : ∃ k, P k := ⟨wt x, x, fun _ h => h, hx, rfl⟩
      obtain ⟨y, hyx, hyC, hyw⟩ := Nat.find_spec hex
      have hy_min : ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y →
          circuitFun n C z = false := by
        intro z hzy hne
        by_contra hzf
        have hzt : circuitFun n C z = true := by cases h : circuitFun n C z <;> simp_all
        have hsub : (Finset.univ.filter fun i => z i = true) ⊂
            (Finset.univ.filter fun i => y i = true) := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzy i (Finset.mem_filter.mp hi).2⟩, ?_⟩
          intro heq
          apply hne
          funext i
          apply Bool.eq_iff_iff.mpr
          have hmem : i ∈ Finset.univ.filter (fun j => z j = true) ↔
              i ∈ Finset.univ.filter (fun j => y j = true) := by rw [heq]
          simpa using hmem
        have hlt : wt z < wt y := Finset.card_lt_card hsub
        have hmink : Nat.find hex ≤ wt z := Nat.find_min' hex ⟨z, fun i hi => hyx i (hzy i hi), hzt, rfl⟩
        omega
      have hyC' : circuitFun n C' y = true := hmin y ⟨hyC, hy_min⟩
      exact circuitFun_mono C' hAO'.1 hyx hyC'

end PEqualNP.Outside.L_meta_2852_aux

theorem PEqualNP.Outside.L_meta_2852 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b c d : ℕ), (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = c ∧ d < n + g ∧ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, d⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, c⟩ (List.ofFn x) = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧ (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size ∧ (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) ∧ (PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ↔ (∀ x : Fin n → Bool, (PEqualNP.MetaComplexity.circuitFun n C x = true ∧ ∀ y : Fin n → Bool, (∀ i, y i = true → x i = true) → y ≠ x → PEqualNP.MetaComplexity.circuitFun n C y = false) → PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b d⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) x = true)) :=
  PEqualNP.Outside.L_meta_2852_aux.main
