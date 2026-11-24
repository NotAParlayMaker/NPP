import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_951_aux

open PEqualNP.CircuitLowerBounds

def Allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def Positive (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def gateValue (values : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun w => values.getD w false)

def appendGate (values : List Bool) (g : Gate) : List Bool :=
  values ++ [gateValue values g]

def run (gates : List Gate) (values : List Bool) : List Bool :=
  gates.foldl appendGate values

def Below (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ w, x.getD w false = true → y.getD w false = true

theorem gateValue_pos (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (a b : List Bool) (h : Below a b) :
    gateValue a g = true → gateValue b g = true := by
  unfold gateValue
  rcases hop with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro ha w hw
    exact h.2 w (ha w hw)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨w, hw, ha⟩
    exact ⟨w, hw, h.2 w ha⟩

theorem gateValue_neg (g : Gate) (hop : g.op = .not) (a b : List Bool) (h : Below a b) :
    gateValue b g = true → gateValue a g = true := by
  unfold gateValue
  rw [hop]
  cases hi : g.inputs with
  | nil => simp [GateOp.eval]
  | cons w ws =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true']
    intro hf
    cases ha : a.getD w false
    · rfl
    · exact (Bool.false_ne_true (hf.symm.trans (h.2 w ha))).elim

theorem appendGate_below {a b : List Bool} (h : Below a b) (g : Gate)
    (hg : gateValue a g = true → gateValue b g = true) :
    Below (appendGate a g) (appendGate b g) := by
  refine ⟨by simp [appendGate, h.1], ?_⟩
  intro w
  unfold appendGate
  by_cases hw : w < a.length
  · have hwb : w < b.length := h.1 ▸ hw
    rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hwb]
    exact h.2 w
  · have ha := Nat.le_of_not_gt hw
    have hb : b.length ≤ w := h.1 ▸ ha
    rw [List.getD_append_right _ _ _ _ ha, List.getD_append_right _ _ _ _ hb, h.1]
    cases he : w - b.length with
    | zero => simpa using hg
    | succ k => simp

theorem initial_below {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    Below (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro w
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rename_i hw
    simpa using h ⟨w, hw⟩
  · simp

theorem run_cons (g : Gate) (gs : List Gate) (a : List Bool) :
    run (g :: gs) a = run gs (appendGate a g) := rfl

theorem run_keeps (gs : List Gate) (a : List Bool) {w : ℕ} (h : w < a.length) :
    (run gs a).getD w false = a.getD w false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp [appendGate]; omega), appendGate, List.getD_append _ _ _ _ h]

theorem value_first (g : Gate) (gs : List Gate) (a : List Bool) :
    (run (g :: gs) a).getD a.length false = gateValue a g := by
  rw [run_cons, run_keeps _ _ (by simp [appendGate]), appendGate]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl a.length)]
  simp

theorem next_index (g : Gate) (gs : List Gate) (a : List Bool) (j : ℕ) :
    (run gs (appendGate a g)).getD ((appendGate a g).length + j) false =
      (run (g :: gs) a).getD (a.length + (j + 1)) false := by
  congr 1
  simp [appendGate]
  omega

def AgreesNot (gs : List Gate) (a b : List Bool) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = .not →
    (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false

theorem AgreesNot.tail {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) :
    AgreesNot gs (appendGate a g) (appendGate b g) := by
  intro j q hj hq
  rw [next_index, next_index]
  exact h (j+1) q (by simpa using hj) hq

theorem AgreesNot.first {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) (hg : g.op = .not) :
    gateValue a g = gateValue b g := by
  have h0 := h 0 g rfl hg
  simpa only [Nat.add_zero, value_first] using h0

theorem run_below (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (hnot : AgreesNot gs a b) :
    Below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    rw [run_cons, run_cons]
    apply ih _ _ (appendGate_below h g ?_)
      (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    rcases (hops _ (List.mem_cons_self ..)).1 with ha | ho | hn
    · exact gateValue_pos g (Or.inl ha) a b h
    · exact gateValue_pos g (Or.inr ho) a b h
    · rw [hnot.first hn]
      exact id

def booleanGate : Bool → Gate
  | true => ⟨.and, []⟩
  | false => ⟨.or, []⟩

theorem booleanGate_pos (b : Bool) : Positive (booleanGate b) := by
  cases b <;> simp [Positive, booleanGate]

theorem booleanGate_runs (b : Bool) (x : List Bool) :
    gateValue x (booleanGate b) = b := by
  cases b <;> rfl

noncomputable def freezeGate (a : List Bool) (g : Gate) : Gate := by
  classical
  exact if g.op = .not then booleanGate (gateValue a g) else g

noncomputable def freeze (a : List Bool) : List Gate → List Gate
  | [] => []
  | g :: gs => freezeGate a g :: freeze (appendGate a g) gs

theorem freeze_length (gs : List Gate) (a : List Bool) : (freeze a gs).length = gs.length := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => simp [freeze, ih]

theorem freeze_pos (gs : List Gate) (a : List Bool) (h : ∀ g ∈ gs, Allowed g) :
    ∀ g ∈ freeze a gs, Positive g := by
  induction gs generalizing a with
  | nil => simp [freeze]
  | cons g gs ih =>
    intro q hq
    rw [freeze, List.mem_cons] at hq
    rcases hq with rfl | hq
    · classical
      unfold freezeGate
      split
      · exact booleanGate_pos _
      · rename_i hn
        obtain ⟨ha | ho | hh, hf⟩ := h g (List.mem_cons_self ..)
        · exact ⟨Or.inl ha, hf⟩
        · exact ⟨Or.inr ho, hf⟩
        · exact (hn hh).elim
    · exact ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq)) _ hq

theorem freeze_run (gs : List Gate) (a b z : List Bool)
    (haz : Below a z) (hzb : Below z b) (hops : ∀ g ∈ gs, Allowed g)
    (hnot : AgreesNot gs a b) : run (freeze a gs) z = run gs z := by
  induction gs generalizing a b z with
  | nil => rfl
  | cons g gs ih =>
    rw [freeze, run_cons, run_cons]
    have hA : g ∈ g :: gs := List.mem_cons_self
    have hop := (hops g hA).1
    rcases hop with h | h | h
    · have hf : freezeGate a g = g := by
        classical
        simp [freezeGate, h]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (gateValue_pos g (Or.inl h) a z haz))
        (appendGate_below hzb g (gateValue_pos g (Or.inl h) z b hzb))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    · have hf : freezeGate a g = g := by
        classical
        simp [freezeGate, h]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (gateValue_pos g (Or.inr h) a z haz))
        (appendGate_below hzb g (gateValue_pos g (Or.inr h) z b hzb))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    · have he : gateValue a g = gateValue b g := hnot.first h
      have hze : gateValue z g = gateValue a g := by
        apply Bool.eq_iff_iff.mpr
        refine ⟨gateValue_neg g h a z haz, ?_⟩
        rw [he]
        exact gateValue_neg g h z b hzb
      have hf : appendGate z (freezeGate a g) = appendGate z g := by
        classical
        unfold appendGate
        simp [freezeGate, h, booleanGate_runs, hze]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (by rw [hze]; exact id))
        (appendGate_below hzb g (by rw [hze, he]; exact id))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail


theorem note_antitone (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (i : ℕ) (g : Gate) (hi : gs[i]? = some g)
    (hg : g.op = .not)
    (hprev : ∀ (j : ℕ) (q : Gate), j < i → gs[j]? = some q → q.op = .not →
      (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false) :
    (run gs b).getD (b.length + i) false = true →
      (run gs a).getD (a.length + i) false = true := by
  induction gs generalizing a b i g with
  | nil => simp at hi
  | cons q gs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst g
      simpa only [Nat.add_zero, value_first] using gateValue_neg q hg a b h
    | succ i =>
      have hb : Below (appendGate a q) (appendGate b q) := by
        apply appendGate_below h
        rcases (hops q (List.mem_cons_self ..)).1 with ha | ho | hn
        · exact gateValue_pos q (Or.inl ha) a b h
        · exact gateValue_pos q (Or.inr ho) a b h
        · have he := hprev 0 q (Nat.zero_lt_succ i) rfl hn
          simp only [Nat.add_zero, value_first] at he
          rw [he]
          exact id
      have hpre (j : ℕ) (r : Gate) (hji : j < i) (hj : gs[j]? = some r)
          (hr : r.op = .not) :
          (run gs (appendGate a q)).getD ((appendGate a q).length + j) false =
          (run gs (appendGate b q)).getD ((appendGate b q).length + j) false := by
        rw [next_index, next_index]
        exact hprev (j+1) r (by omega) (by simpa using hj) hr
      have got := ih _ _ hb (fun r hr => hops r (List.mem_cons_of_mem _ hr))
        i g (by simpa using hi) hg hpre
      rwa [next_index, next_index] at got

noncomputable def notIndices (gs : List Gate) : Finset (Fin gs.length) := by
  classical
  exact Finset.univ.filter (fun i => (gs.get i).op = .not)

theorem mem_notIndices (gs : List Gate) (j : Fin gs.length) :
    j ∈ notIndices gs ↔ (gs.get j).op = .not := by
  classical
  simp [notIndices]

noncomputable def notEmbedding (gs : List Gate) :
    Fin (notIndices gs).card ↪o Fin gs.length :=
  (notIndices gs).orderEmbOfFin rfl

theorem notEmbedding_mem (gs : List Gate) (j : Fin (notIndices gs).card) :
    notEmbedding gs j ∈ notIndices gs :=
  (notIndices gs).orderEmbOfFin_mem rfl j

theorem exists_notEmbedding (gs : List Gate) (j : Fin gs.length)
    (hj : j ∈ notIndices gs) : ∃ i, notEmbedding gs i = j := by
  have h := (notIndices gs).range_orderEmbOfFin rfl
  change Set.range (notEmbedding gs) = _ at h
  change j ∈ Set.range (notEmbedding gs)
  rw [h]
  exact hj

theorem card_notIndices (gs : List Gate) (t : ℕ)
    (h : ∃ f : Fin t → Fin gs.length,
      ∀ i : Fin gs.length, (gs.get i).op = .not → ∃ j, f j = i) :
    (notIndices gs).card ≤ t := by
  classical
  obtain ⟨f, h⟩ := h
  have hsub : notIndices gs ⊆ Finset.univ.image f := by
    intro j hj
    obtain ⟨i, hi⟩ := h j ((mem_notIndices gs j).1 hj)
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

def trace {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin gs.length) : Bool :=
  (run gs (List.ofFn x)).getD (n + i.val) false

theorem trace_after {n m : ℕ} (gs : List Gate) (x : Fin m → Fin n → Bool)
    (hx : ∀ a b : Fin m, a ≤ b → ∀ w, x a w = true → x b w = true)
    (hg : ∀ g ∈ gs, Allowed g)
    (i : Fin (notIndices gs).card) (a b : Fin m) (hab : a ≤ b)
    (hprev : ∀ j : Fin (notIndices gs).card, j < i →
      trace gs (x a) (notEmbedding gs j) = trace gs (x b) (notEmbedding gs j)) :
    trace gs (x b) (notEmbedding gs i) = true →
      trace gs (x a) (notEmbedding gs i) = true := by
  let j := notEmbedding gs i
  have hj := (mem_notIndices gs j).1 (notEmbedding_mem gs i)
  have hi : gs[j.val]? = some (gs.get j) := List.getElem?_eq_getElem j.isLt
  have got := note_antitone gs (List.ofFn (x a)) (List.ofFn (x b))
    (initial_below _ _ (hx a b hab)) hg j.val (gs.get j) hi hj
  have earlier (k : ℕ) (q : Gate) (hk : k < j.val) (hq : gs[k]? = some q)
      (hqn : q.op = .not) :
      (run gs (List.ofFn (x a))).getD ((List.ofFn (x a)).length + k) false =
      (run gs (List.ofFn (x b))).getD ((List.ofFn (x b)).length + k) false := by
    have hkl : k < gs.length := by
      apply lt_trans hk
      exact j.isLt
    let k' : Fin gs.length := ⟨k, hkl⟩
    have hget : gs.get k' = q := by simpa [k', List.getElem?_eq_getElem hkl] using hq
    obtain ⟨p, hp⟩ := exists_notEmbedding gs k'
      ((mem_notIndices gs k').2 (hget ▸ hqn))
    have hpi : p < i := by
      have hlt : notEmbedding gs p < notEmbedding gs i := by
        rw [hp]
        exact hk
      exact (notEmbedding gs).lt_iff_lt.mp hlt
    have h := hprev p hpi
    rw [hp] at h
    simpa only [trace, List.length_ofFn, k'] using h
  simpa only [trace, List.length_ofFn, j] using got earlier

theorem trace_agrees {n : ℕ} (gs : List Gate) (a b : Fin n → Bool)
    (h : ∀ i : Fin (notIndices gs).card,
      trace gs a (notEmbedding gs i) = trace gs b (notEmbedding gs i)) :
    AgreesNot gs (List.ofFn a) (List.ofFn b) := by
  intro j g hj hg
  have hlt : j < gs.length := (List.getElem?_eq_some_iff.mp hj).choose
  let i : Fin gs.length := ⟨j, hlt⟩
  have he : gs.get i = g := by simpa [i, List.getElem?_eq_getElem hlt] using hj
  obtain ⟨p, hp⟩ := exists_notEmbedding gs i
    ((mem_notIndices gs i).2 (he ▸ hg))
  have hh := h p
  rw [hp] at hh
  simpa only [trace, List.length_ofFn, i] using hh

lemma existsCuts {t m : ℕ} (p : Fin t → Fin m → Bool)
    (h : ∀ (i : Fin t) (a b : Fin m), a ≤ b →
      (∀ j : Fin t, j < i → p j a = p j b) → (p i b = true → p i a = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.range m ∧ P.card + 1 ≤ 2 ^ t ∧
      ∀ a b : Fin m, a ≤ b → (∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val)) →
        ∀ i : Fin t, p i a = p i b := by
  induction t with
  | zero =>
      refine ⟨∅, by simp, by simp, ?_⟩
      intro _ _ _ _ i
      exact Fin.elim0 i
  | succ t ih =>
      let p₀ (i : Fin t) := p i.castSucc
      have h₀ : ∀ (i : Fin t) (a b : Fin m), a ≤ b →
          (∀ j : Fin t, j < i → p₀ j a = p₀ j b) →
          (p₀ i b = true → p₀ i a = true) := by
        intro i a b hab hearlier htrue
        apply h i.castSucc a b hab ?_ htrue
        intro j hj
        have hjt : j.val < t := lt_of_lt_of_le hj i.isLt.le
        exact hearlier ⟨j.val, hjt⟩ (by exact hj)
      obtain ⟨P, hP, hp, stable⟩ := ih p₀ h₀
      have hlast {a b : Fin m} (hab : a ≤ b)
          (hgood : ∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val)) :
          p (Fin.last t) b = true → p (Fin.last t) a = true := by
        apply h (Fin.last t) a b hab
        intro j hj
        exact stable a b hab hgood ⟨j.val, hj⟩
      let value (w : ℕ) : Bool := if hw : w < m then p (Fin.last t) ⟨w, hw⟩ else false
      have value_eq (w : ℕ) (hw : w < m) : value w = p (Fin.last t) ⟨w, hw⟩ := dite_eq_left hw
      let N := (Finset.range m).filter (fun w =>
        0 < w ∧ w ∉ P ∧ value (w - 1) = true ∧ value w = false)
      have hN {w : ℕ} (hw : w ∈ N) :
          w < m ∧ 0 < w ∧ w ∉ P ∧ value (w - 1) = true ∧ value w = false := by
        have he := Finset.mem_filter.mp hw
        exact ⟨Finset.mem_range.mp he.1, he.2⟩
      let before (w : ℕ) := P.filter (fun k => k ≤ w)
      have hsep {u v : ℕ} (hu : u ∈ N) (hv : v ∈ N) (hlt : u < v) :
          (before u).card ≠ (before v).card := by
        intro he
        have hsub : before u ⊆ before v := by
          intro k hk
          obtain ⟨hkP, hku⟩ := Finset.mem_filter.mp hk
          exact Finset.mem_filter.mpr ⟨hkP, le_trans hku hlt.le⟩
        have heq : before u = before v :=
          Finset.eq_of_subset_of_card_le hsub he.ge
        have hnocut : ∀ w ∈ P, ¬ (u < w ∧ w ≤ v - 1) := by
          intro w hw hinterval
          have hwv : w ∈ before v :=
            Finset.mem_filter.mpr ⟨hw, hinterval.2.trans (Nat.sub_le ..)⟩
          rw [← heq] at hwv
          exact (not_le_of_gt hinterval.1) (Finset.mem_filter.mp hwv).2
        have huu := hN hu
        have hvv := hN hv
        have hvlt : v - 1 < m := lt_of_le_of_lt (Nat.sub_le ..) hvv.1
        have htrans := hlast
          (a := ⟨u, huu.1⟩) (b := ⟨v - 1, hvlt⟩)
          (by show u ≤ v - 1; omega) hnocut
        have htrue : value u = true := by
          rw [value_eq _ huu.1]
          apply htrans
          rw [← value_eq _ hvlt]
          exact hvv.2.2.2.1
        rw [huu.2.2.2.2] at htrue
        contradiction
      have hcount : N.card ≤ P.card + 1 := by
        simpa only [Finset.card_range] using
          (Finset.card_le_card_of_injOn
            (s := N) (t := Finset.range (P.card + 1))
            (fun w => (before w).card)
            (fun w _ => Finset.mem_range.mpr (Nat.lt_succ_of_le
              (Finset.card_filter_le _ _)))
            (by
              intro u hu v hv he
              rcases lt_trichotomy u v with hlt | heq | hgt
              · exact False.elim (hsep hu hv hlt he)
              · exact heq
              · exact False.elim (hsep hv hu hgt he.symm)))
      refine ⟨P ∪ N, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hP hw
        · exact Finset.mem_range.mpr (hN hw).1
      · have hU := Finset.card_union_le P N
        rw [Nat.pow_succ]
        omega
      · intro a b hab hgood i
        have hprev : ∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val) :=
          fun w hw => hgood w (Finset.mem_union_left _ hw)
        by_cases hi : i.val < t
        · exact stable a b hab hprev ⟨i.val, hi⟩
        · have hie : i = Fin.last t := by
            apply Fin.ext
            have hi' := i.isLt
            change i.val = t
            omega
          subst i
          have hadj (w : ℕ) (haw : a.val < w) (hwb : w ≤ b.val) :
              value (w - 1) = value w := by
            have hw : w < m := hwb.trans_lt b.isLt
            have hw' : w - 1 < m := (Nat.sub_le ..).trans_lt hw
            have hpos : 0 < w := by omega
            have hpw : w ∉ P := fun hmem => hprev w hmem ⟨haw, hwb⟩
            have hnW : w ∉ N :=
              fun hmem => hgood w (Finset.mem_union_right _ hmem) ⟨haw, hwb⟩
            have hstep := hlast
              (a := ⟨w - 1, hw'⟩) (b := ⟨w, hw⟩)
              (Nat.sub_le ..)
              (by
                rintro k hk ⟨hkw, hwk⟩
                change w - 1 < k at hkw
                change k ≤ w at hwk
                have he : k = w := by omega
                exact hpw (he ▸ hk))
            have himp : value w = true → value (w - 1) = true := by
              rw [value_eq _ hw, value_eq _ hw']
              exact hstep
            cases hr : value w <;> cases hl : value (w - 1)
            · rfl
            · exact False.elim (hnW (Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr hw, hpos, hpw, hl, hr⟩))
            · exact False.elim (Bool.false_ne_true (hl.symm.trans (himp hr)))
            · rfl
          have hdist : ∀ d : ℕ, a.val + d ≤ b.val → value (a.val + d) = value a.val := by
            intro d
            induction d with
            | zero => simp
            | succ d ih =>
                intro hd
                have hprev' := ih (by omega)
                have hs := hadj (a.val + (d + 1)) (by omega) hd
                have he : a.val + (d + 1) - 1 = a.val + d := by omega
                rw [he] at hs
                exact hs.symm.trans hprev'
          have hab' : a.val ≤ b.val := hab
          have hdist' := hdist (b.val - a.val) (by omega)
          have he : a.val + (b.val - a.val) = b.val := by omega
          rw [he, value_eq _ b.isLt, value_eq _ a.isLt] at hdist'
          exact hdist'.symm

open Classical in
lemma cutGame_le (m t budget : ℕ) (cost : ℕ × ℕ → ℕ) (P : Finset ℕ)
    (hP : P ⊆ Finset.range m) (hcount : P.card + 1 ≤ 2 ^ t)
    (hcost : ∀ a b : Fin m, a ≤ b →
      (∀ w ∈ P, ¬ (a.val < w ∧ w ≤ b.val)) → cost (a.val, b.val) ≤ budget) :
    WithTop.untopD 0 (((Finset.range m).powerset.filter
      (fun Q : Finset ℕ => Q.card + 1 ≤ 2 ^ t)).image
      (fun Q : Finset ℕ => ((Finset.range m ×ˢ Finset.range m).filter
        (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ Q, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup
        cost)).min ≤ budget := by
  let feasible := (Finset.range m).powerset.filter (fun Q : Finset ℕ => Q.card + 1 ≤ 2 ^ t)
  let score (Q : Finset ℕ) :=
    ((Finset.range m ×ˢ Finset.range m).filter
      (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ Q, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup cost
  change WithTop.untopD 0 (feasible.image score).min ≤ budget
  have hf : P ∈ feasible := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hP, hcount⟩
  have hmem : score P ∈ feasible.image score := Finset.mem_image_of_mem score hf
  have hscore : score P ≤ budget := by
    apply Finset.sup_le
    rintro ⟨u, v⟩ huv
    obtain ⟨hprod, huv', hnone⟩ := Finset.mem_filter.mp huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hprod
    exact hcost ⟨u, Finset.mem_range.mp hu⟩ ⟨v, Finset.mem_range.mp hv⟩ huv' hnone
  apply WithTop.coe_le_coe.mp
  exact (WithTop.coe_untopD_le _ _).trans
    ((Finset.min_le hmem).trans (WithTop.coe_le_coe.mpr hscore))


end PEqualNP.Outside.L_meta_951_aux
