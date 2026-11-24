import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4791

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma foldl_len (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, stepW, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma foldl_ext (gs : List Gate) : ∀ w : List Bool, ∃ t, gs.foldl stepW w = w ++ t := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht⟩ := ih (stepW w g)
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
    simp only [List.foldl_cons]
    rw [ht]
    simp [stepW]

lemma foldl_getD (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl stepW w).getD k false = w.getD k false := by
  obtain ⟨t, ht⟩ := foldl_ext gs w
  rw [ht, List.getD_append _ _ _ _ hk]

lemma orSets_len (n : ℕ) (gs : List Gate) : ∀ cs : List (List ℕ),
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs with
  | nil => intro cs; simp
  | cons g gs ih =>
    intro cs
    simp only [List.foldl_cons, ih, orStep, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma orSets_ext (n : ℕ) (gs : List Gate) : ∀ cs : List (List ℕ),
    ∃ t, gs.foldl (orStep n) cs = cs ++ t := by
  induction gs with
  | nil => intro cs; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro cs
    obtain ⟨y, hy⟩ : ∃ y, orStep n cs g = cs ++ [y] := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ := ih (orStep n cs g)
    refine ⟨[y] ++ t, ?_⟩
    simp only [List.foldl_cons]
    rw [ht, hy, List.append_assoc]

lemma orSets_pre (n : ℕ) (gs t : List Gate) (k : ℕ) (hk : k < gs.length) :
    ((gs ++ t).foldl (orStep n) []).getD k [] = (gs.foldl (orStep n) []).getD k [] := by
  rw [List.foldl_append]
  obtain ⟨u, hu⟩ := orSets_ext n t (gs.foldl (orStep n) [])
  rw [hu, List.getD_append _ _ _ _ (by rw [orSets_len]; simpa using hk)]

lemma orSets_getD (n : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    (gs.foldl (orStep n) []).getD k [] =
      (orStep n ((gs.take k).foldl (orStep n) []) gs[k]).getD k [] := by
  have hsplit : gs = (gs.take k ++ [gs[k]]) ++ gs.drop (k + 1) := by
    rw [List.append_assoc, List.singleton_append]
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.drop_eq_getElem_cons hk]
  conv_lhs => rw [hsplit]
  rw [orSets_pre n _ _ k (by simp; omega), List.foldl_append, List.foldl_cons,
    List.foldl_nil]

lemma orSets_take (n : ℕ) (gs : List Gate) (k w : ℕ) (hw : w < k) (hk : k ≤ gs.length) :
    ((gs.take k).foldl (orStep n) []).getD w [] = (gs.foldl (orStep n) []).getD w [] := by
  conv_rhs => rw [← List.take_append_drop k gs]
  rw [orSets_pre n _ _ w (by simp; omega)]

lemma orStep_mem (n : ℕ) (cs : List (List ℕ)) (g : Gate) (k : ℕ)
    (hk : k ∈ (orStep n cs g).getD cs.length []) :
    k = cs.length ∨ (g.op = GateOp.or ∧ ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧
      k ∈ cs.getD (w - n) []) := by
  simp only [orStep] at hk
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero] at hk
  rcases List.mem_cons.1 hk with h | h
  · exact Or.inl h
  · right
    by_cases hop : g.op = GateOp.or
    · rw [if_pos hop] at h
      obtain ⟨w, hw, hkw⟩ := List.mem_flatMap.1 h
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      exact ⟨hop, w, hw.1, hw.2.1, hw.2.2, hkw⟩
    · rw [if_neg hop] at h
      simp at h

lemma orIn_sub (n : ℕ) (C : Circuit) (g : ℕ) (hg : g < C.gates.length) (i : Fin n)
    (hi : i ∈ orIn n C (n + g)) :
    (gateAt C g).op = GateOp.or ∧ ((i : ℕ) ∈ (gateAt C g).inputs ∨
      ∃ w ∈ (gateAt C g).inputs, n ≤ w ∧ w < n + g ∧ i ∈ orIn n C w) := by
  unfold orIn at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with hi | ⟨k, hk, ⟨-, hkr⟩, hkop, hki⟩
  · omega
  · have hcl := orSets_getD n C.gates g hg
    have hga : gateAt C g = C.gates[g] := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hg]
    have hlen : ((C.gates.take g).foldl (orStep n) []).length = g := by
      rw [orSets_len]; simp; omega
    unfold orSets at hkr
    rw [Nat.add_sub_cancel_left, hcl] at hkr
    have hm := orStep_mem n _ C.gates[g] k (by rw [hlen]; exact hkr)
    rw [hlen] at hm
    rw [hga]
    rcases hm with rfl | ⟨hop, w, hw, hwn, hwl, hkw⟩
    · rw [hga] at hkop hki
      exact ⟨hkop, Or.inl hki⟩
    · refine ⟨hop, Or.inr ⟨w, hw, hwn, hwl, ?_⟩⟩
      rw [orSets_take n C.gates g (w - n) (by omega) (by omega)] at hkw
      unfold orIn
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inr ⟨k, hk, ⟨hwn, hkw⟩, hkop, hki⟩

lemma orIn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) (i : Fin n)
    (hi : i ∈ orIn n C w) : (i : ℕ) = w := by
  unfold orIn at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with hi | ⟨k, -, ⟨h, -⟩, -⟩
  · exact hi
  · omega

lemma wire_val (gs : List Gate) (x : List Bool) (g : ℕ) (hg : g < gs.length)
    (hrb : ∀ i ∈ gs[g].inputs, i < x.length + g) :
    (gs.foldl stepW x).getD (x.length + g) false =
      gs[g].op.eval (gs[g].inputs.map fun i => (gs.foldl stepW x).getD i false) := by
  have hsplit : gs = (gs.take g ++ [gs[g]]) ++ gs.drop (g + 1) := by
    rw [List.append_assoc, List.singleton_append]
    conv_lhs => rw [← List.take_append_drop g gs]
    rw [List.drop_eq_getElem_cons hg]
  set U := (gs.take g).foldl stepW x with hU
  have hUl : U.length = x.length + g := by rw [hU, foldl_len]; simp; omega
  have hfull : gs.foldl stepW x = (gs.drop (g + 1)).foldl stepW (stepW U gs[g]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append]
    rfl
  have hpre : ∀ i, i < x.length + g → (gs.foldl stepW x).getD i false = U.getD i false := by
    intro i hi
    rw [hfull, foldl_getD _ _ _ (by simp [stepW]; omega)]
    simp only [stepW]
    rw [List.getD_append _ _ _ _ (by omega)]
  have key : (gs.foldl stepW x).getD (x.length + g) false =
      gs[g].op.eval (gs[g].inputs.map fun i => U.getD i false) := by
    rw [hfull, foldl_getD _ _ _ (by simp [stepW]; omega)]
    simp only [stepW]
    rw [← hUl, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
  rw [key]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [hpre i (hrb i hi)]

lemma one_hot (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool) (i : Fin n)
    (hxi : x i = true) : ∀ w, ∀ hi : i ∈ orIn n C w,
      (C.wires (List.ofFn x)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hi
    by_cases hw : w < n
    · have hiw := orIn_input n C w hw i hi
      obtain rfl : w = i := hiw.symm
      rw [wires_eq, foldl_getD _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD, hxi]
    · by_cases hgl : w - n < C.gates.length
      · have hwg : w = n + (w - n) := by omega
        rw [hwg] at hi
        obtain ⟨hop, hcase⟩ := orIn_sub n C (w - n) hgl i hi
        have hga : gateAt C (w - n) = C.gates[w - n] := by
          unfold gateAt; rw [List.getD_eq_getElem _ _ hgl]
        rw [hga] at hop hcase
        have hrb : ∀ j ∈ C.gates[w - n].inputs, j < (List.ofFn x).length + (w - n) := by
          intro j hj
          have := hRB (w - n) hgl j (by rw [hga]; exact hj)
          simpa using this
        have hv := wire_val C.gates (List.ofFn x) (w - n) hgl hrb
        rw [List.length_ofFn, show n + (w - n) = w by omega] at hv
        rw [wires_eq, hv, hop]
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
        rcases hcase with hin | ⟨w', hw', hwn, hwl, hiw⟩
        · refine ⟨i, hin, ?_⟩
          rw [foldl_getD _ _ _ (by simp)]
          rw [List.getD_eq_getElem _ _ (by simp)]
          simp [hxi]
        · refine ⟨w', hw', ?_⟩
          have := ih w' (by omega) hiw
          rwa [wires_eq] at this
      · exfalso
        unfold orIn at hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rcases hi with hi | ⟨k, hk, ⟨hn, hkr⟩, -⟩
        · omega
        · unfold orSets at hkr
          rw [List.getD_eq_default _ _ (by rw [orSets_len]; simp; omega)] at hkr
          simp at hkr

def mkOr (n : ℕ) (c : Option Bool) (st : List Gate × List (Option Bool)) (u v : Option ℕ) :
    (List Gate × List (Option Bool)) × Option ℕ :=
  match u, v with
  | none, v => (st, v)
  | some a, none => (st, some a)
  | some a, some b => ((st.1 ++ [⟨GateOp.or, [a, b]⟩], st.2 ++ [c]), some (n + st.1.length))

def mkAnd (n : ℕ) (st : List Gate × List (Option Bool)) (u v : Option ℕ) :
    (List Gate × List (Option Bool)) × Option ℕ :=
  match u, v with
  | some a, some b =>
    ((st.1 ++ [⟨GateOp.and, [a, b]⟩], st.2 ++ [none]), some (n + st.1.length))
  | _, _ => (st, none)

def partOf (ps : List (Option ℕ × Option ℕ)) (w : ℕ) : Option ℕ × Option ℕ :=
  ps.getD w (none, none)

def stepG (n : ℕ) (st : (List Gate × List (Option Bool)) × List (Option ℕ × Option ℕ))
    (g : Gate) : (List Gate × List (Option Bool)) × List (Option ℕ × Option ℕ) :=
  match g.op with
  | GateOp.and =>
    let a := partOf st.2 (g.inputs.getD 0 0)
    let b := partOf st.2 (g.inputs.getD 1 0)
    let r1 := mkAnd n st.1 a.1 b.1
    let r2 := mkAnd n r1.1 a.1 b.2
    let r3 := mkAnd n r2.1 a.2 b.1
    let r4 := mkAnd n r3.1 a.2 b.2
    let r5 := mkOr n none r4.1 r1.2 r2.2
    let r6 := mkOr n none r5.1 r3.2 r4.2
    (r6.1, st.2 ++ [(r5.2, r6.2)])
  | _ =>
    let a := partOf st.2 (g.inputs.getD 0 0)
    let b := partOf st.2 (g.inputs.getD 1 0)
    let r1 := mkOr n (some false) st.1 a.1 b.1
    let r2 := mkOr n (some true) r1.1 a.2 b.2
    (r2.1, st.2 ++ [(r1.2, r2.2)])

def initParts (n p : ℕ) : List (Option ℕ × Option ℕ) :=
  (List.range n).map fun i => if i < p then (some i, none) else (none, some i)

def optV (V : List Bool) : Option ℕ → Bool
  | none => false
  | some d => V.getD d false

def okZ (n : ℕ) (tg : List (Option Bool)) (d : ℕ) : Prop :=
  n ≤ d ∧ tg.getD (d - n) (some true) = none

def okC (n p : ℕ) (tg : List (Option Bool)) (col : Bool) (d : ℕ) : Prop :=
  (d < n ∧ decide (p ≤ d) = col) ∨
    (n ≤ d ∧ (tg.getD (d - n) (some (!col)) = some col ∨ tg.getD (d - n) (some (!col)) = none))

def cls (n p : ℕ) (tg : List (Option Bool)) : Option Bool → ℕ → Prop
  | none, d => okZ n tg d
  | some col, d => okC n p tg col d

lemma okZ_ext (n : ℕ) (tg t : List (Option Bool)) (d : ℕ) (h : okZ n tg d) :
    okZ n (tg ++ t) d := by
  obtain ⟨hn, hz⟩ := h
  refine ⟨hn, ?_⟩
  have hl : d - n < tg.length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at hz
    simp at hz
  rw [List.getD_append _ _ _ _ hl]
  exact hz

lemma okC_ext (n p : ℕ) (tg t : List (Option Bool)) (col : Bool) (d : ℕ)
    (h : okC n p tg col d) : okC n p (tg ++ t) col d := by
  rcases h with h | ⟨hn, hz⟩
  · exact Or.inl h
  · right
    refine ⟨hn, ?_⟩
    have hl : d - n < tg.length := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by omega)] at hz
      cases col <;> simp at hz
    rw [List.getD_append _ _ _ _ hl]
    exact hz

lemma cls_ext (n p : ℕ) (tg t : List (Option Bool)) (c : Option Bool) (d : ℕ)
    (h : cls n p tg c d) : cls n p (tg ++ t) c d := by
  cases c with
  | none => exact okZ_ext n tg t d h
  | some col => exact okC_ext n p tg t col d h

def GInv (n p : ℕ) (st : List Gate × List (Option Bool)) : Prop :=
  st.2.length = st.1.length ∧ ∀ j (hj : j < st.1.length), ∃ a b : ℕ,
    st.1[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
    ((st.1[j].op = GateOp.and ∧ st.2.getD j (some true) = none) ∨
      (st.1[j].op = GateOp.or ∧ cls n p st.2 (st.2.getD j (some true)) a ∧
        cls n p st.2 (st.2.getD j (some true)) b))

def OkPart (n p : ℕ) (st : List Gate × List (Option Bool)) (c : Option Bool) (u : Option ℕ) :
    Prop :=
  ∀ d, u = some d → d < n + st.1.length ∧ cls n p st.2 c d

lemma okPart_ext (n p : ℕ) (st st' : List Gate × List (Option Bool)) (c : Option Bool)
    (u : Option ℕ) (t1 : List Gate) (t2 : List (Option Bool)) (h1 : st'.1 = st.1 ++ t1)
    (h2 : st'.2 = st.2 ++ t2) (h : OkPart n p st c u) : OkPart n p st' c u := by
  intro d hd
  obtain ⟨hb, hc⟩ := h d hd
  refine ⟨by rw [h1]; simp; omega, ?_⟩
  rw [h2]; exact cls_ext n p st.2 t2 c d hc

lemma ginv_snoc (n p : ℕ) (st : List Gate × List (Option Bool)) (hG : GInv n p st)
    (g : Gate) (c : Option Bool) (a b : ℕ) (hg : g.inputs = [a, b])
    (ha : a < n + st.1.length) (hb : b < n + st.1.length)
    (hop : (g.op = GateOp.and ∧ c = none) ∨
      (g.op = GateOp.or ∧ cls n p st.2 c a ∧ cls n p st.2 c b)) :
    GInv n p (st.1 ++ [g], st.2 ++ [c]) := by
  obtain ⟨hl, hall⟩ := hG
  refine ⟨by simp [hl], ?_⟩
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hjl : j < st.1.length
  · obtain ⟨a', b', h1, h2, h3, h4⟩ := hall j hjl
    refine ⟨a', b', ?_, h2, h3, ?_⟩
    · simp only [List.getElem_append_left hjl]; exact h1
    · have hgd : (st.2 ++ [c]).getD j (some true) = st.2.getD j (some true) :=
        List.getD_append _ _ _ _ (by omega)
      simp only [List.getElem_append_left hjl, hgd]
      rcases h4 with ⟨h5, h6⟩ | ⟨h5, h6, h7⟩
      · exact Or.inl ⟨h5, h6⟩
      · exact Or.inr ⟨h5, cls_ext n p _ _ _ _ h6, cls_ext n p _ _ _ _ h7⟩
  · have hje : j = st.1.length := by omega
    subst hje
    refine ⟨a, b, ?_, ha, hb, ?_⟩
    · simp [hg]
    · have hgd : (st.2 ++ [c]).getD st.1.length (some true) = c := by
        rw [← hl, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero, hgd]
      rcases hop with ⟨h5, h6⟩ | ⟨h5, h6, h7⟩
      · exact Or.inl ⟨h5, h6⟩
      · exact Or.inr ⟨h5, cls_ext n p _ _ _ _ h6, cls_ext n p _ _ _ _ h7⟩

lemma mkOr_facts (n p : ℕ) (c : Option Bool) (st : List Gate × List (Option Bool))
    (hG : GInv n p st) (u v : Option ℕ) (hu : OkPart n p st c u) (hv : OkPart n p st c v) :
    GInv n p (mkOr n c st u v).1 ∧
    (∃ t1 t2, (mkOr n c st u v).1.1 = st.1 ++ t1 ∧ (mkOr n c st u v).1.2 = st.2 ++ t2 ∧
      t1.length ≤ 1 ∧ (t1.length = 1 → u.isSome ∧ v.isSome)) ∧
    OkPart n p (mkOr n c st u v).1 c (mkOr n c st u v).2 ∧
    (∀ x : List Bool, x.length = n →
      optV ((mkOr n c st u v).1.1.foldl stepW x) (mkOr n c st u v).2 =
        (optV (st.1.foldl stepW x) u || optV (st.1.foldl stepW x) v)) := by
  rcases u with _ | a <;> rcases v with _ | b
  · refine ⟨hG, ⟨[], [], by simp [mkOr], by simp [mkOr], by simp, by simp⟩, ?_, ?_⟩
    · intro d hd; simp [mkOr] at hd
    · intro x _; simp [mkOr, optV]
  · refine ⟨hG, ⟨[], [], by simp [mkOr], by simp [mkOr], by simp, by simp⟩, hv, ?_⟩
    intro x _; simp [mkOr, optV]
  · refine ⟨hG, ⟨[], [], by simp [mkOr], by simp [mkOr], by simp, by simp⟩, hu, ?_⟩
    intro x _; simp [mkOr, optV]
  · obtain ⟨hab, hac⟩ := hu a rfl
    obtain ⟨hbb, hbc⟩ := hv b rfl
    have hG' := ginv_snoc n p st hG ⟨GateOp.or, [a, b]⟩ c a b rfl hab hbb
      (Or.inr ⟨rfl, hac, hbc⟩)
    refine ⟨hG', ⟨[⟨GateOp.or, [a, b]⟩], [c], rfl, rfl, by simp, by simp⟩, ?_, ?_⟩
    · intro d hd
      simp only [mkOr, Option.some.injEq] at hd
      subst hd
      simp only [mkOr]
      refine ⟨by simp, ?_⟩
      have hl := hG.1
      cases c with
      | none =>
        refine ⟨by omega, ?_⟩
        simp only [Nat.add_sub_cancel_left]
        rw [← hl, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl
      | some col =>
        right
        refine ⟨by omega, Or.inl ?_⟩
        simp only [Nat.add_sub_cancel_left]
        rw [← hl, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl
    · intro x hx
      have hVl : (st.1.foldl stepW x).length = n + st.1.length := by rw [foldl_len, hx]
      simp only [mkOr, optV]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [stepW]
      rw [← hVl, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      simp [GateOp.eval]

lemma mkAnd_facts (n p : ℕ) (st : List Gate × List (Option Bool))
    (hG : GInv n p st) (u v : Option ℕ) (cu cv : Option Bool) (hu : OkPart n p st cu u)
    (hv : OkPart n p st cv v) :
    GInv n p (mkAnd n st u v).1 ∧
    (∃ t1 t2, (mkAnd n st u v).1.1 = st.1 ++ t1 ∧ (mkAnd n st u v).1.2 = st.2 ++ t2 ∧
      t1.length ≤ 1 ∧ (t1.length = 1 → u.isSome ∧ v.isSome)) ∧
    OkPart n p (mkAnd n st u v).1 none (mkAnd n st u v).2 ∧
    (∀ x : List Bool, x.length = n →
      optV ((mkAnd n st u v).1.1.foldl stepW x) (mkAnd n st u v).2 =
        (optV (st.1.foldl stepW x) u && optV (st.1.foldl stepW x) v)) := by
  rcases u with _ | a <;> rcases v with _ | b
  · refine ⟨hG, ⟨[], [], by simp [mkAnd], by simp [mkAnd], by simp, by simp⟩, ?_, ?_⟩
    · intro d hd; simp [mkAnd] at hd
    · intro x _; simp [mkAnd, optV]
  · refine ⟨hG, ⟨[], [], by simp [mkAnd], by simp [mkAnd], by simp, by simp⟩, ?_, ?_⟩
    · intro d hd; simp [mkAnd] at hd
    · intro x _; simp [mkAnd, optV]
  · refine ⟨hG, ⟨[], [], by simp [mkAnd], by simp [mkAnd], by simp, by simp⟩, ?_, ?_⟩
    · intro d hd; simp [mkAnd] at hd
    · intro x _; simp [mkAnd, optV]
  · obtain ⟨hab, -⟩ := hu a rfl
    obtain ⟨hbb, -⟩ := hv b rfl
    have hG' := ginv_snoc n p st hG ⟨GateOp.and, [a, b]⟩ none a b rfl hab hbb
      (Or.inl ⟨rfl, rfl⟩)
    refine ⟨hG', ⟨[⟨GateOp.and, [a, b]⟩], [none], rfl, rfl, by simp, by simp⟩, ?_, ?_⟩
    · intro d hd
      simp only [mkAnd, Option.some.injEq] at hd
      subst hd
      simp only [mkAnd]
      have hl := hG.1
      refine ⟨by simp, by omega, ?_⟩
      simp only [Nat.add_sub_cancel_left]
      rw [← hl, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl
    · intro x hx
      have hVl : (st.1.foldl stepW x).length = n + st.1.length := by rw [foldl_len, hx]
      simp only [mkAnd, optV]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [stepW]
      rw [← hVl, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
      simp [GateOp.eval]

lemma optV_ext (n p : ℕ) (st : List Gate × List (Option Bool)) (t : List Gate)
    (c : Option Bool) (u : Option ℕ) (hu : OkPart n p st c u) (x : List Bool)
    (hx : x.length = n) :
    optV ((st.1 ++ t).foldl stepW x) u = optV (st.1.foldl stepW x) u := by
  rcases u with _ | d
  · rfl
  · obtain ⟨hd, -⟩ := hu d rfl
    simp only [optV]
    rw [List.foldl_append, foldl_getD _ _ _ (by rw [foldl_len, hx]; exact hd)]

def PInv (n p : ℕ) (st : List Gate × List (Option Bool)) (ps : List (Option ℕ × Option ℕ)) :
    Prop :=
  ∀ j, OkPart n p st (some false) (partOf ps j).1 ∧ OkPart n p st (some true) (partOf ps j).2

lemma partOf_snoc_lt (ps : List (Option ℕ × Option ℕ)) (q : Option ℕ × Option ℕ) (j : ℕ)
    (hj : j < ps.length) : partOf (ps ++ [q]) j = partOf ps j := by
  unfold partOf; rw [List.getD_append _ _ _ _ hj]

lemma partOf_snoc_eq (ps : List (Option ℕ × Option ℕ)) (q : Option ℕ × Option ℕ) :
    partOf (ps ++ [q]) ps.length = q := by
  unfold partOf; rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl

lemma partOf_snoc_gt (ps : List (Option ℕ × Option ℕ)) (q : Option ℕ × Option ℕ) (j : ℕ)
    (hj : ps.length < j) : partOf (ps ++ [q]) j = (none, none) := by
  unfold partOf; rw [List.getD_eq_default _ _ (by simp; omega)]

lemma bool_dist (aP aL bP bL : Bool) :
    ((aP || aL) && (bP || bL)) = (((aP && bP) || (aP && bL)) || ((aL && bP) || (aL && bL))) := by
  cases aP <;> cases aL <;> cases bP <;> cases bL <;> rfl

lemma bool_or4 (aP aL bP bL : Bool) :
    ((aP || aL) || (bP || bL)) = ((aP || bP) || (aL || bL)) := by
  cases aP <;> cases aL <;> cases bP <;> cases bL <;> rfl

lemma okZ_okC (n p : ℕ) (tg : List (Option Bool)) (col : Bool) (d : ℕ) (h : okZ n tg d) :
    okC n p tg col d := by
  obtain ⟨hn, hz⟩ := h
  right
  refine ⟨hn, Or.inr ?_⟩
  have hl : d - n < tg.length := by
    by_contra hc
    rw [List.getD_eq_default _ _ (by omega)] at hz
    simp at hz
  rw [List.getD_eq_getElem _ _ hl] at hz ⊢
  exact hz

lemma okPart_none_some (n p : ℕ) (st : List Gate × List (Option Bool)) (col : Bool)
    (u : Option ℕ) (h : OkPart n p st none u) : OkPart n p st (some col) u := by
  intro d hd
  obtain ⟨hb, hc⟩ := h d hd
  exact ⟨hb, okZ_okC n p st.2 col d hc⟩

lemma pinv_snoc (n p : ℕ) (st st' : List Gate × List (Option Bool))
    (ps : List (Option ℕ × Option ℕ)) (t1 : List Gate) (t2 : List (Option Bool))
    (e1 : st'.1 = st.1 ++ t1) (e2 : st'.2 = st.2 ++ t2) (hP : PInv n p st ps)
    (q : Option ℕ × Option ℕ) (hq1 : OkPart n p st' (some false) q.1)
    (hq2 : OkPart n p st' (some true) q.2) : PInv n p st' (ps ++ [q]) := by
  intro j
  by_cases hj : j < ps.length
  · rw [partOf_snoc_lt ps q j hj]
    exact ⟨okPart_ext n p st st' _ _ t1 t2 e1 e2 (hP j).1,
      okPart_ext n p st st' _ _ t1 t2 e1 e2 (hP j).2⟩
  · by_cases hje : j = ps.length
    · subst hje; rw [partOf_snoc_eq]; exact ⟨hq1, hq2⟩
    · rw [partOf_snoc_gt ps q j (by omega)]
      exact ⟨fun d hd => by simp at hd, fun d hd => by simp at hd⟩

lemma stepG_facts (n p : ℕ) (st : List Gate × List (Option Bool))
    (ps : List (Option ℕ × Option ℕ)) (hG : GInv n p st) (hP : PInv n p st ps) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    GInv n p (stepG n (st, ps) g).1 ∧ (∃ q, (stepG n (st, ps) g).2 = ps ++ [q]) ∧
    (∃ t, (stepG n (st, ps) g).1.1 = st.1 ++ t ∧ t.length ≤ 6 ∧
      (g.op = GateOp.or → t.length ≤ 2)) ∧
    PInv n p (stepG n (st, ps) g).1 (stepG n (st, ps) g).2 ∧
    (∀ x : List Bool, x.length = n →
      (optV ((stepG n (st, ps) g).1.1.foldl stepW x)
          (partOf (stepG n (st, ps) g).2 ps.length).1 ||
        optV ((stepG n (st, ps) g).1.1.foldl stepW x)
          (partOf (stepG n (st, ps) g).2 ps.length).2) =
      g.op.eval [optV (st.1.foldl stepW x) (partOf ps (g.inputs.getD 0 0)).1 ||
          optV (st.1.foldl stepW x) (partOf ps (g.inputs.getD 0 0)).2,
        optV (st.1.foldl stepW x) (partOf ps (g.inputs.getD 1 0)).1 ||
          optV (st.1.foldl stepW x) (partOf ps (g.inputs.getD 1 0)).2]) := by
  obtain ⟨haP, haL⟩ := hP (g.inputs.getD 0 0)
  obtain ⟨hbP, hbL⟩ := hP (g.inputs.getD 1 0)
  rcases hop with hop | hop
  · simp only [stepG, hop]
    generalize (partOf ps (g.inputs.getD 0 0)).1 = aP at haP ⊢
    generalize (partOf ps (g.inputs.getD 0 0)).2 = aL at haL ⊢
    generalize (partOf ps (g.inputs.getD 1 0)).1 = bP at hbP ⊢
    generalize (partOf ps (g.inputs.getD 1 0)).2 = bL at hbL ⊢
    have f1 := mkAnd_facts n p st hG aP bP _ _ haP hbP
    generalize mkAnd n st aP bP = r1 at f1 ⊢
    obtain ⟨G1, ⟨u1, v1, e1, e1', l1, -⟩, O1, S1⟩ := f1
    have haP1 := okPart_ext n p st r1.1 _ _ u1 v1 e1 e1' haP
    have haL1 := okPart_ext n p st r1.1 _ _ u1 v1 e1 e1' haL
    have hbP1 := okPart_ext n p st r1.1 _ _ u1 v1 e1 e1' hbP
    have hbL1 := okPart_ext n p st r1.1 _ _ u1 v1 e1 e1' hbL
    have f2 := mkAnd_facts n p r1.1 G1 aP bL _ _ haP1 hbL1
    generalize mkAnd n r1.1 aP bL = r2 at f2 ⊢
    obtain ⟨G2, ⟨u2, v2, e2, e2', l2, -⟩, O2, S2⟩ := f2
    have haL2 := okPart_ext n p r1.1 r2.1 _ _ u2 v2 e2 e2' haL1
    have hbP2 := okPart_ext n p r1.1 r2.1 _ _ u2 v2 e2 e2' hbP1
    have hbL2 := okPart_ext n p r1.1 r2.1 _ _ u2 v2 e2 e2' hbL1
    have f3 := mkAnd_facts n p r2.1 G2 aL bP _ _ haL2 hbP2
    generalize mkAnd n r2.1 aL bP = r3 at f3 ⊢
    obtain ⟨G3, ⟨u3, v3, e3, e3', l3, -⟩, O3, S3⟩ := f3
    have haL3 := okPart_ext n p r2.1 r3.1 _ _ u3 v3 e3 e3' haL2
    have hbL3 := okPart_ext n p r2.1 r3.1 _ _ u3 v3 e3 e3' hbL2
    have f4 := mkAnd_facts n p r3.1 G3 aL bL _ _ haL3 hbL3
    generalize mkAnd n r3.1 aL bL = r4 at f4 ⊢
    obtain ⟨G4, ⟨u4, v4, e4, e4', l4, -⟩, O4, S4⟩ := f4
    have x14a : r4.1.1 = r1.1.1 ++ (u2 ++ u3 ++ u4) := by rw [e4, e3, e2]; simp
    have x14b : r4.1.2 = r1.1.2 ++ (v2 ++ v3 ++ v4) := by rw [e4', e3', e2']; simp
    have x24a : r4.1.1 = r2.1.1 ++ (u3 ++ u4) := by rw [e4, e3]; simp
    have x24b : r4.1.2 = r2.1.2 ++ (v3 ++ v4) := by rw [e4', e3']; simp
    have f5 := mkOr_facts n p none r4.1 G4 r1.2 r2.2
      (okPart_ext n p r1.1 r4.1 _ _ _ _ x14a x14b O1)
      (okPart_ext n p r2.1 r4.1 _ _ _ _ x24a x24b O2)
    generalize mkOr n none r4.1 r1.2 r2.2 = r5 at f5 ⊢
    obtain ⟨G5, ⟨u5, v5, e5, e5', l5, -⟩, O5, S5⟩ := f5
    have x35a : r5.1.1 = r3.1.1 ++ (u4 ++ u5) := by rw [e5, e4]; simp
    have x35b : r5.1.2 = r3.1.2 ++ (v4 ++ v5) := by rw [e5', e4']; simp
    have f6 := mkOr_facts n p none r5.1 G5 r3.2 r4.2
      (okPart_ext n p r3.1 r5.1 _ _ _ _ x35a x35b O3)
      (okPart_ext n p r4.1 r5.1 _ _ _ _ e5 e5' O4)
    generalize mkOr n none r5.1 r3.2 r4.2 = r6 at f6 ⊢
    obtain ⟨G6, ⟨u6, v6, e6, e6', l6, -⟩, O6, S6⟩ := f6
    have x02a : r2.1.1 = st.1 ++ (u1 ++ u2) := by rw [e2, e1, List.append_assoc]
    have x03a : r3.1.1 = st.1 ++ (u1 ++ u2 ++ u3) := by rw [e3, e2, e1]; simp
    have x06a : r6.1.1 = st.1 ++ (u1 ++ u2 ++ u3 ++ u4 ++ u5 ++ u6) := by
      rw [e6, e5, e4, e3, e2, e1]; simp
    have x06b : r6.1.2 = st.2 ++ (v1 ++ v2 ++ v3 ++ v4 ++ v5 ++ v6) := by
      rw [e6', e5', e4', e3', e2', e1']; simp
    refine ⟨G6, ⟨_, rfl⟩, ⟨_, x06a, by simp; omega, fun h => by cases h⟩,
      ?_, ?_⟩
    · exact pinv_snoc n p st r6.1 ps _ _ x06a x06b hP (r5.2, r6.2)
        (okPart_none_some n p r6.1 false _ (okPart_ext n p r5.1 r6.1 _ _ _ _ e6 e6' O5))
        (okPart_none_some n p r6.1 true _ O6)
    · intro x hx
      rw [partOf_snoc_eq]
      have q1 : optV (r4.1.1.foldl stepW x) r1.2 =
          (optV (st.1.foldl stepW x) aP && optV (st.1.foldl stepW x) bP) := by
        rw [x14a, optV_ext n p r1.1 _ none r1.2 O1 x hx, S1 x hx]
      have q2 : optV (r4.1.1.foldl stepW x) r2.2 =
          (optV (st.1.foldl stepW x) aP && optV (st.1.foldl stepW x) bL) := by
        rw [x24a, optV_ext n p r2.1 _ none r2.2 O2 x hx, S2 x hx, e1,
          optV_ext n p st u1 _ aP haP x hx, optV_ext n p st u1 _ bL hbL x hx]
      have q3 : optV (r5.1.1.foldl stepW x) r3.2 =
          (optV (st.1.foldl stepW x) aL && optV (st.1.foldl stepW x) bP) := by
        rw [x35a, optV_ext n p r3.1 _ none r3.2 O3 x hx, S3 x hx, x02a,
          optV_ext n p st _ _ aL haL x hx, optV_ext n p st _ _ bP hbP x hx]
      have q4 : optV (r5.1.1.foldl stepW x) r4.2 =
          (optV (st.1.foldl stepW x) aL && optV (st.1.foldl stepW x) bL) := by
        rw [e5, optV_ext n p r4.1 u5 none r4.2 O4 x hx, S4 x hx, x03a,
          optV_ext n p st _ _ aL haL x hx, optV_ext n p st _ _ bL hbL x hx]
      have A1 : optV (r6.1.1.foldl stepW x) r5.2 =
          ((optV (st.1.foldl stepW x) aP && optV (st.1.foldl stepW x) bP) ||
            (optV (st.1.foldl stepW x) aP && optV (st.1.foldl stepW x) bL)) := by
        rw [e6, optV_ext n p r5.1 u6 none r5.2 O5 x hx, S5 x hx, q1, q2]
      have A2 : optV (r6.1.1.foldl stepW x) r6.2 =
          ((optV (st.1.foldl stepW x) aL && optV (st.1.foldl stepW x) bP) ||
            (optV (st.1.foldl stepW x) aL && optV (st.1.foldl stepW x) bL)) := by
        rw [S6 x hx, q3, q4]
      rw [A1, A2]
      generalize optV (st.1.foldl stepW x) aP = A
      generalize optV (st.1.foldl stepW x) aL = B
      generalize optV (st.1.foldl stepW x) bP = C
      generalize optV (st.1.foldl stepW x) bL = D
      cases A <;> cases B <;> cases C <;> cases D <;> rfl
  · have hop' : g.op ≠ GateOp.and := by rw [hop]; intro h; cases h
    simp only [stepG, hop]
    generalize (partOf ps (g.inputs.getD 0 0)).1 = aP at haP ⊢
    generalize (partOf ps (g.inputs.getD 0 0)).2 = aL at haL ⊢
    generalize (partOf ps (g.inputs.getD 1 0)).1 = bP at hbP ⊢
    generalize (partOf ps (g.inputs.getD 1 0)).2 = bL at hbL ⊢
    have f1 := mkOr_facts n p (some false) st hG aP bP haP hbP
    generalize mkOr n (some false) st aP bP = r1 at f1 ⊢
    obtain ⟨G1, ⟨u1, v1, e1, e1', l1, -⟩, O1, S1⟩ := f1
    have f2 := mkOr_facts n p (some true) r1.1 G1 aL bL
      (okPart_ext n p st r1.1 _ _ u1 v1 e1 e1' haL) (okPart_ext n p st r1.1 _ _ u1 v1 e1 e1' hbL)
    generalize mkOr n (some true) r1.1 aL bL = r2 at f2 ⊢
    obtain ⟨G2, ⟨u2, v2, e2, e2', l2, -⟩, O2, S2⟩ := f2
    have x02a : r2.1.1 = st.1 ++ (u1 ++ u2) := by rw [e2, e1, List.append_assoc]
    have x02b : r2.1.2 = st.2 ++ (v1 ++ v2) := by rw [e2', e1', List.append_assoc]
    refine ⟨G2, ⟨_, rfl⟩, ⟨_, x02a, by simp; omega, fun _ => by simp; omega⟩, ?_, ?_⟩
    · exact pinv_snoc n p st r2.1 ps _ _ x02a x02b hP (r1.2, r2.2)
        (okPart_ext n p r1.1 r2.1 _ _ _ _ e2 e2' O1) O2
    · intro x hx
      rw [partOf_snoc_eq]
      have A1 : optV (r2.1.1.foldl stepW x) r1.2 =
          (optV (st.1.foldl stepW x) aP || optV (st.1.foldl stepW x) bP) := by
        rw [e2, optV_ext n p r1.1 u2 _ r1.2 O1 x hx, S1 x hx]
      have A2 : optV (r2.1.1.foldl stepW x) r2.2 =
          (optV (st.1.foldl stepW x) aL || optV (st.1.foldl stepW x) bL) := by
        rw [S2 x hx, e1, optV_ext n p st u1 _ aL haL x hx, optV_ext n p st u1 _ bL hbL x hx]
      rw [A1, A2]
      generalize optV (st.1.foldl stepW x) aP = A
      generalize optV (st.1.foldl stepW x) aL = B
      generalize optV (st.1.foldl stepW x) bP = C
      generalize optV (st.1.foldl stepW x) bL = D
      cases A <;> cases B <;> cases C <;> cases D <;> rfl

lemma partOf_init (n p a : ℕ) (ha : a < n) :
    partOf (initParts n p) a = if a < p then (some a, none) else (none, some a) := by
  unfold partOf initParts
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

lemma first_le (n p : ℕ) (g : Gate) (a b : ℕ) (hg : g.inputs = [a, b]) (ha : a < n)
    (hb : b < n) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (stepG n (([], []), initParts n p) g).1.1.length ≤ 1 := by
  have h0 : g.inputs.getD 0 0 = a := by rw [hg]; rfl
  have h1 : g.inputs.getD 1 0 = b := by rw [hg]; rfl
  rcases hop with hop | hop <;> simp only [stepG, hop, h0, h1] <;>
    rw [partOf_init n p a ha, partOf_init n p b hb] <;> split_ifs <;> simp [mkAnd, mkOr]

lemma fold_facts (n p : ℕ) : ∀ (gs : List Gate) (st : List Gate × List (Option Bool))
    (ps : List (Option ℕ × Option ℕ)), GInv n p st → PInv n p st ps →
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) →
    GInv n p (gs.foldl (stepG n) (st, ps)).1 ∧
    PInv n p (gs.foldl (stepG n) (st, ps)).1 (gs.foldl (stepG n) (st, ps)).2 ∧
    (∃ t, (gs.foldl (stepG n) (st, ps)).1.1 = st.1 ++ t ∧ t.length ≤ 6 * gs.length) ∧
    (∀ x : List Bool, x.length = n → ∀ Wc : List Bool, ps.length = Wc.length →
      (∀ j, Wc.getD j false =
        (optV (st.1.foldl stepW x) (partOf ps j).1 || optV (st.1.foldl stepW x) (partOf ps j).2)) →
      ∀ j, (gs.foldl stepW Wc).getD j false =
        (optV ((gs.foldl (stepG n) (st, ps)).1.1.foldl stepW x)
            (partOf (gs.foldl (stepG n) (st, ps)).2 j).1 ||
          optV ((gs.foldl (stepG n) (st, ps)).1.1.foldl stepW x)
            (partOf (gs.foldl (stepG n) (st, ps)).2 j).2)) := by
  intro gs
  induction gs with
  | nil =>
    intro st ps hG hP _
    refine ⟨hG, hP, ⟨[], by simp, by simp⟩, ?_⟩
    intro x _ Wc _ hV j
    exact hV j
  | cons g gs ih =>
    intro st ps hG hP hgs
    obtain ⟨hop, hlen2⟩ := hgs g (by simp)
    obtain ⟨G1, ⟨q, hq⟩, ⟨t1, et1, lt1, -⟩, P1, S1⟩ := stepG_facts n p st ps hG hP g hop
    generalize hr : stepG n (st, ps) g = r at G1 hq et1 P1 S1
    have hr' : (st, ps) = (st, ps) := rfl
    obtain ⟨G2, P2, ⟨t2, et2, lt2⟩, S2⟩ := ih r.1 r.2 G1 P1 (fun g' hg' => hgs g' (by simp [hg']))
    simp only [List.foldl_cons, hr]
    refine ⟨G2, P2, ⟨t1 ++ t2, by rw [et2, et1, List.append_assoc], by simp; omega⟩, ?_⟩
    intro x hx Wc hWl hV j
    apply S2 x hx (stepW Wc g) (by rw [hq]; simp [stepW, hWl])
    intro j'
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen2
    by_cases hj : j' < Wc.length
    · simp only [stepW]
      rw [List.getD_append _ _ _ _ hj, hV j', hq, partOf_snoc_lt ps q j' (by omega), et1]
      obtain ⟨hP1, hP2⟩ := hP j'
      rw [optV_ext n p st t1 _ _ hP1 x hx, optV_ext n p st t1 _ _ hP2 x hx]
    · by_cases hje : j' = Wc.length
      · subst hje
        simp only [stepW]
        rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
        have hS := S1 x hx
        rw [hq] at hS ⊢
        rw [← hWl, hS]
        congr 1
        rw [hab]
        simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
        rw [hV a, hV b]
      · simp only [stepW]
        rw [List.getD_eq_default _ _ (by simp; omega), hq,
          partOf_snoc_gt ps q j' (by omega)]
        rfl

lemma purity (n p : ℕ) (st : List Gate × List (Option Bool)) (hG : GInv n p st)
    (D : Circuit) (t : List Gate) (hD : D.gates = st.1 ++ t) :
    ∀ g, g < st.1.length → ∀ i ∈ orIn n D (n + g),
      (st.2.getD g (some true) = some false → (i : ℕ) < p) ∧
      (st.2.getD g (some true) = some true → p ≤ (i : ℕ)) ∧
      (st.2.getD g (some true) = none → False) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hg i hi
    have hgD : g < D.gates.length := by rw [hD]; simp; omega
    obtain ⟨hop, hcase⟩ := orIn_sub n D g hgD i hi
    have hga : gateAt D g = st.1[g] := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hgD]
      simp only [hD, List.getElem_append_left hg]
    rw [hga] at hop hcase
    obtain ⟨a, b, hab, ha, hb, hk⟩ := hG.2 g hg
    rcases hk with ⟨hand, -⟩ | ⟨-, hca, hcb⟩
    · rw [hand] at hop; cases hop
    · generalize st.2.getD g (some true) = tag at hca hcb ⊢
      have key : ∀ w ∈ [a, b], cls n p st.2 tag w := by
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hca
        · exact hcb
      rw [hab] at hcase
      rcases hcase with hin | ⟨w, hw, hwn, hwl, hiw⟩
      · have hw := key i hin
        cases tag with
        | none => exact absurd hw.1 (by omega)
        | some col =>
          rcases hw with ⟨-, hc⟩ | ⟨hn, -⟩
          · refine ⟨fun h => ?_, fun h => ?_, fun h => by cases h⟩
            · cases h; simp at hc; omega
            · cases h; simpa using hc
          · exact absurd hn (by omega)
      · have hw' := key w hw
        have hIH := ih (w - n) (by omega) (by omega) i
          (by rw [show n + (w - n) = w by omega]; exact hiw)
        cases tag with
        | none =>
          exfalso
          obtain ⟨-, hz⟩ := hw'
          exact hIH.2.2 hz
        | some col =>
          rcases hw' with ⟨hlt, -⟩ | ⟨-, hz⟩
          · omega
          · have hl : w - n < st.2.length := by
              by_contra hc
              rw [List.getD_eq_default _ _ (by omega)] at hz
              cases col <;> simp at hz
            have heq : st.2.getD (w - n) (some true) = st.2.getD (w - n) (some (!col)) := by
              rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ hl]
            rw [← heq] at hz
            rcases hz with hz | hz
            · refine ⟨fun h => ?_, fun h => ?_, fun h => by cases h⟩
              · cases h; exact hIH.1 hz
              · cases h; exact hIH.2.1 hz
            · exact (hIH.2.2 hz).elim

def finalC (n : ℕ) (ds : List Gate) : Option ℕ → Option ℕ → Circuit
  | some a, some b => ⟨ds ++ [⟨GateOp.or, [a, b]⟩], n + ds.length⟩
  | some a, none => ⟨ds, a⟩
  | none, some b => ⟨ds, b⟩
  | none, none => ⟨ds, n + ds.length⟩

lemma finalC_eval (n : ℕ) (ds : List Gate) (u v : Option ℕ) (x : List Bool)
    (hx : x.length = n) :
    (finalC n ds u v).eval x = (optV (ds.foldl stepW x) u || optV (ds.foldl stepW x) v) := by
  have hVl : (ds.foldl stepW x).length = n + ds.length := by rw [foldl_len, hx]
  rcases u with _ | a <;> rcases v with _ | b
  · simp only [finalC, Circuit.eval, wires_eq, optV, Bool.or_false]
    rw [List.getD_eq_default _ _ (by omega)]
  · simp [finalC, Circuit.eval, wires_eq, optV]
  · simp [finalC, Circuit.eval, wires_eq, optV]
  · simp only [finalC, Circuit.eval, wires_eq, optV]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [stepW]
    rw [← hVl, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    simp [GateOp.eval]

lemma finalC_gates (n : ℕ) (ds : List Gate) (u v : Option ℕ) :
    (∃ t, (finalC n ds u v).gates = ds ++ t ∧ t.length ≤ 1) ∧
    (∀ j, ds.length ≤ j → j < (finalC n ds u v).gates.length →
      ∃ a b, u = some a ∧ v = some b ∧ j = ds.length ∧
        (finalC n ds u v).gates[j]? = some ⟨GateOp.or, [a, b]⟩ ∧
        (finalC n ds u v).output = n + ds.length) := by
  rcases u with _ | a <;> rcases v with _ | b
  · refine ⟨⟨[], by simp [finalC], by simp⟩, ?_⟩
    intro j hj hjl; simp [finalC] at hjl; omega
  · refine ⟨⟨[], by simp [finalC], by simp⟩, ?_⟩
    intro j hj hjl; simp [finalC] at hjl; omega
  · refine ⟨⟨[], by simp [finalC], by simp⟩, ?_⟩
    intro j hj hjl; simp [finalC] at hjl; omega
  · refine ⟨⟨[⟨GateOp.or, [a, b]⟩], by simp [finalC], by simp⟩, ?_⟩
    intro j hj hjl
    simp [finalC] at hjl
    refine ⟨a, b, rfl, rfl, by omega, ?_, rfl⟩
    have : j = ds.length := by omega
    subst this
    simp [finalC]

theorem main (p l : ℕ) (C : Circuit) (hC : IsAO2 (p + l) C) (hsz : 1 ≤ C.size)
    (hone : ∀ i : Fin (p + l), circuitFun (p + l) C (fun k => decide (k = i)) = false) :
    ∃ D : Circuit, IsAO2 (p + l) D ∧ D.size + 4 ≤ 6 * C.size ∧
      circuitFun (p + l) D = circuitFun (p + l) C ∧
      PEqualNP.TwoColour.tCount (p + l) D (fun i => decide (p ≤ i)) = 0 := by
  obtain ⟨hAO, hRB, h2⟩ := hC
  obtain ⟨g0, rest, hgs⟩ : ∃ g0 rest, C.gates = g0 :: rest := by
    cases hg : C.gates with
    | nil => simp [Circuit.size, hg] at hsz
    | cons g0 rest => exact ⟨g0, rest, rfl⟩
  have hg0mem : g0 ∈ C.gates := by rw [hgs]; simp
  have hop0 := hAO g0 hg0mem
  obtain ⟨a0, b0, hab0⟩ := List.length_eq_two.1 (h2 g0 hg0mem)
  have hga0 : gateAt C 0 = g0 := by unfold gateAt; rw [hgs]; rfl
  have ha0 : a0 < p + l := by
    have := hRB 0 (by rw [hgs]; simp) a0 (by rw [hga0, hab0]; simp); simpa using this
  have hb0 : b0 < p + l := by
    have := hRB 0 (by rw [hgs]; simp) b0 (by rw [hga0, hab0]; simp); simpa using this
  have G0 : GInv (p + l) p (([] : List Gate), ([] : List (Option Bool))) :=
    ⟨rfl, fun j hj => by simp at hj⟩
  have P0 : PInv (p + l) p (([] : List Gate), ([] : List (Option Bool))) (initParts (p + l) p) := by
    intro j
    by_cases hj : j < p + l
    · rw [partOf_init _ _ _ hj]
      split_ifs with hjp
      · refine ⟨fun d hd => ?_, fun d hd => by simp at hd⟩
        simp only [Option.some.injEq] at hd; subst hd
        exact ⟨by simp; omega, Or.inl ⟨by omega, by simp; omega⟩⟩
      · refine ⟨fun d hd => by simp at hd, fun d hd => ?_⟩
        simp only [Option.some.injEq] at hd; subst hd
        exact ⟨by simp; omega, Or.inl ⟨by omega, by simp; omega⟩⟩
    · have : partOf (initParts (p + l) p) j = (none, none) := by
        unfold partOf initParts; rw [List.getD_eq_default _ _ (by simp; omega)]
      rw [this]; exact ⟨fun d hd => by simp at hd, fun d hd => by simp at hd⟩
  have hall : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 :=
    fun g hg => ⟨hAO g hg, h2 g hg⟩
  obtain ⟨GF, PF, -, SF⟩ := fold_facts (p + l) p C.gates _ _ G0 P0 hall
  obtain ⟨G1, -, -, P1, -⟩ := stepG_facts (p + l) p _ _ G0 P0 g0 hop0
  have hfirst := first_le (p + l) p g0 a0 b0 hab0 ha0 hb0 hop0
  obtain ⟨-, -, ⟨tR, eR, lR⟩, -⟩ := fold_facts (p + l) p rest _ _ G1 P1
    (fun g hg => hall g (by rw [hgs]; simp [hg]))
  set R := C.gates.foldl (stepG (p + l)) (([], []), initParts (p + l) p) with hR
  have hRsize : R.1.1.length ≤ 1 + 6 * rest.length := by
    have : R = rest.foldl (stepG (p + l)) (stepG (p + l) (([], []), initParts (p + l) p) g0) := by
      rw [hR, hgs, List.foldl_cons]
    rw [this, eR]; simp; omega
  set oP := (partOf R.2 C.output).1 with hoP
  set oL := (partOf R.2 C.output).2 with hoL
  set D := finalC (p + l) R.1.1 oP oL with hDdef
  obtain ⟨⟨tf, ef, lf⟩, hlast⟩ := finalC_gates (p + l) R.1.1 oP oL
  rw [← hDdef] at ef hlast
  have hgate : ∀ j (hj : j < D.gates.length), (∃ hj' : j < R.1.1.length,
      D.gates[j] = R.1.1[j]) ∨ (∃ a b, oP = some a ∧ oL = some b ∧ j = R.1.1.length ∧
        D.gates[j]? = some ⟨GateOp.or, [a, b]⟩ ∧ D.output = p + l + R.1.1.length) := by
    intro j hj
    by_cases hjl : j < R.1.1.length
    · left; exact ⟨hjl, by simp only [ef, List.getElem_append_left hjl]⟩
    · right; exact hlast j (by omega) hj
  have hFun : circuitFun (p + l) D = circuitFun (p + l) C := by
    funext x
    show D.eval (List.ofFn x) = C.eval (List.ofFn x)
    rw [hDdef, finalC_eval _ _ _ _ _ (by simp)]
    unfold Circuit.eval
    rw [wires_eq]
    symm
    apply SF (List.ofFn x) (by simp) (List.ofFn x) (by simp [initParts])
    intro j
    simp only [List.foldl_nil]
    by_cases hj : j < p + l
    · rw [partOf_init _ _ _ hj]
      split_ifs <;> simp [optV]
    · have : partOf (initParts (p + l) p) j = (none, none) := by
        unfold partOf initParts; rw [List.getD_eq_default _ _ (by simp; omega)]
      rw [this, List.getD_eq_default _ _ (by simp; omega)]; rfl
  have hAO2 : IsAO2 (p + l) D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      rcases hgate j hj with ⟨hj', he⟩ | ⟨a, b, -, -, -, he, -⟩
      · rw [he]
        obtain ⟨a, b, -, -, -, hk⟩ := GF.2 j hj'
        rcases hk with ⟨h, -⟩ | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr h
      · rw [List.getElem?_eq_getElem hj] at he
        rw [Option.some.inj he]; exact Or.inr rfl
    · intro j hj i hi
      have hga : gateAt D j = D.gates[j] := by
        unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
      rw [hga] at hi
      rcases hgate j hj with ⟨hj', he⟩ | ⟨a, b, ha, hb, hje, he, -⟩
      · rw [he] at hi
        obtain ⟨a, b, hab, hab1, hab2, -⟩ := GF.2 j hj'
        rw [hab] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · rw [List.getElem?_eq_getElem hj] at he
        rw [Option.some.inj he] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        have hba := (PF C.output).1 a (by rw [← hoP]; exact ha)
        have hbb := (PF C.output).2 b (by rw [← hoL]; exact hb)
        rcases hi with rfl | rfl
        · rw [hje]; exact hba.1
        · rw [hje]; exact hbb.1
    · intro g hg
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      rcases hgate j hj with ⟨hj', he⟩ | ⟨a, b, -, -, -, he, -⟩
      · rw [he]
        obtain ⟨a, b, hab, -⟩ := GF.2 j hj'
        rw [hab]; rfl
      · rw [List.getElem?_eq_getElem hj] at he
        rw [Option.some.inj he]; rfl
  refine ⟨D, hAO2, ?_, hFun, ?_⟩
  · have hDs : D.size = R.1.1.length + tf.length := by
      unfold Circuit.size; rw [ef]; simp
    have hCs : C.size = rest.length + 1 := by unfold Circuit.size; rw [hgs]; simp
    rw [hDs, hCs]; omega
  · unfold PEqualNP.TwoColour.tCount PEqualNP.TwoColour.twoColour
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro g _ hTC
    obtain ⟨hgl, hop, ⟨i1, hi1, hl1⟩, ⟨i2, hi2, hl2⟩⟩ := hTC
    rcases hgate g hgl with ⟨hlt, -⟩ | ⟨a, b, -, -, hje, -, hout⟩
    · have pu := purity (p + l) p R.1 GF D tf ef g hlt
      have u1 := pu i1 hi1
      have u2 := pu i2 hi2
      cases htag : R.1.2.getD g (some true) with
      | none => exact u1.2.2 htag
      | some c =>
        cases c
        · have := u2.1 htag; simp at hl2; omega
        · have := u1.2.1 htag; simp at hl1; omega
    · have hoh := one_hot (p + l) D hAO2.2.1 (fun k => decide (k = i1)) i1 (by simp)
        (p + l + g) hi1
      have hev : circuitFun (p + l) D (fun k => decide (k = i1)) = true := by
        show D.eval _ = true
        unfold Circuit.eval
        rw [hout, ← hje]; exact hoh
      rw [hFun, hone i1] at hev
      exact absurd hev (by simp)

end PEqualNP.Outside.L_meta_4791

theorem PEqualNP.Outside.L_meta_4791 : ∀ (p l : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (p + l) C → 1 ≤ C.size → (∀ i : Fin (p + l), PEqualNP.MetaComplexity.circuitFun (p + l) C (fun k => decide (k = i)) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (p + l) D ∧ D.size + 4 ≤ 6 * C.size ∧ PEqualNP.MetaComplexity.circuitFun (p + l) D = PEqualNP.MetaComplexity.circuitFun (p + l) C ∧ PEqualNP.TwoColour.tCount (p + l) D (fun i => decide (p ≤ i)) = 0 := by
  intro p l C hC hsz hone
  exact PEqualNP.Outside.L_meta_4791.main p l C hC hsz hone
