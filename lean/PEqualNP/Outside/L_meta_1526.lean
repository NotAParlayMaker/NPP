import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1526

def m7_run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma m7_run_append (a b : List Gate) (x : List Bool) : m7_run (a ++ b) x = m7_run b (m7_run a x) := by
  simp [m7_run, List.foldl_append]

lemma m7_run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    m7_run (gs ++ [g]) x = m7_run gs x ++ [g.op.eval (g.inputs.map fun i => (m7_run gs x).getD i false)] := by
  rw [m7_run_append]; rfl

lemma m7_run_length (gs : List Gate) (x : List Bool) : (m7_run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [m7_run]
  | append_singleton gs g ih => rw [m7_run_snoc]; simp [ih]; omega

lemma m7_run_snoc_getD_lt (gs : List Gate) (g : Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs.length) :
    (m7_run (gs ++ [g]) x).getD w false = (m7_run gs x).getD w false := by
  rw [m7_run_snoc, List.getD_append _ _ _ _ (by rw [m7_run_length]; exact hw)]

lemma m7_run_snoc_getD_eq (gs : List Gate) (g : Gate) (x : List Bool) :
    (m7_run (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (m7_run gs x).getD i false) := by
  rw [m7_run_snoc, List.getD_append_right _ _ _ _ (by rw [m7_run_length]), m7_run_length]
  simp

lemma m7_run_getD_lt (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (m7_run gs x).getD w false = x.getD w false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => rw [m7_run_snoc_getD_lt _ _ _ _ (by omega), ih]

lemma m7_gate_value (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < gs.length) :
    (m7_run gs x).getD (x.length + i) false =
      gs[i].op.eval (gs[i].inputs.map fun r => (m7_run (gs.take i) x).getD r false) := by
  have e : gs = (gs.take i ++ [gs[i]]) ++ gs.drop (i + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hi,
      List.take_append_drop]
  have hl : (gs.take i).length = i := by simp; omega
  conv_lhs => rw [e]
  rw [m7_run_append, m7_run_getD_lt _ _ _ (by rw [m7_run_length]; simp; omega)]
  have := m7_run_snoc_getD_eq (gs.take i) gs[i] x
  rw [hl] at this
  exact this

lemma m7_prefix_value (gs : List Gate) (x : List Bool) (i r : ℕ) (hr : r < x.length + i)
    (hi : i ≤ gs.length) :
    (m7_run gs x).getD r false = (m7_run (gs.take i) x).getD r false := by
  conv_lhs => rw [← List.take_append_drop i gs]
  rw [m7_run_append, m7_run_getD_lt _ _ _ (by rw [m7_run_length]; simp; omega)]

lemma m7_mono_all (gs : List Gate) (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hlen : x.length = y.length)
    (le : ∀ w, x.getD w false = true → y.getD w false = true) :
    ∀ w, (m7_run gs x).getD w false = true → (m7_run gs y).getD w false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro w hw; exact le w hw
  | append_singleton gs g ih =>
    have ih' := ih (fun a ha => hop a (List.mem_append_left _ ha))
    intro w hw
    rcases lt_trichotomy w (x.length + gs.length) with h | h | h
    · rw [m7_run_snoc_getD_lt _ _ _ _ h] at hw
      rw [m7_run_snoc_getD_lt _ _ _ _ (by omega)]
      exact ih' w hw
    · subst h
      rw [m7_run_snoc_getD_eq] at hw
      rw [hlen, m7_run_snoc_getD_eq]
      rcases hop g (by simp) with ho | ho
      · simp only [ho, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply,
          id_eq] at hw ⊢
        exact fun z hz => ih' z (hw z hz)
      · simp only [ho, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply,
          id_eq] at hw ⊢
        obtain ⟨z, hz, yes⟩ := hw
        exact ⟨z, hz, ih' z yes⟩
    · rw [List.getD_eq_default _ _ (by rw [m7_run_length]; simp; omega)] at hw
      exact absurd hw (by simp)

lemma m7_and_false (f : ℕ → Bool) (l : List (ℕ ⊕ Bool)) (c : Sum.inr false ∈ l) :
    GateOp.eval GateOp.or (([] : List ℕ).map f) =
      GateOp.eval GateOp.and (l.map (Sum.elim f id)) := by
  symm
  show (l.map (Sum.elim f id)).all id = false
  apply Bool.eq_false_iff.mpr
  intro h
  rw [List.all_eq_true] at h
  have := h false (List.mem_map.mpr ⟨_, c, rfl⟩)
  exact absurd this (by simp)

lemma m7_or_true (f : ℕ → Bool) (l : List (ℕ ⊕ Bool)) (c : Sum.inr true ∈ l) :
    GateOp.eval GateOp.and (([] : List ℕ).map f) =
      GateOp.eval GateOp.or (l.map (Sum.elim f id)) := by
  symm
  show (l.map (Sum.elim f id)).any id = true
  rw [List.any_eq_true]
  exact ⟨true, List.mem_map.mpr ⟨_, c, rfl⟩, rfl⟩

lemma m7_all_simpl (f : ℕ → Bool) (l : List (ℕ ⊕ Bool)) (c : Sum.inr false ∉ l) :
    GateOp.eval GateOp.and ((l.filterMap Sum.getLeft?).map f) =
      GateOp.eval GateOp.and (l.map (Sum.elim f id)) := by
  show ((l.filterMap Sum.getLeft?).map f).all id = (l.map (Sum.elim f id)).all id
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    rcases a with r | b
    · exact h (f r) (List.mem_map.mpr ⟨r, List.mem_filterMap.mpr ⟨Sum.inl r, ha, rfl⟩, rfl⟩)
    · cases b
      · exact absurd ha c
      · rfl
  · intro h b hb
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    obtain ⟨a, ha, e⟩ := List.mem_filterMap.mp hr
    rcases a with a | a
    · simp at e
      subst e
      exact h _ (List.mem_map.mpr ⟨_, ha, rfl⟩)
    · simp at e

lemma m7_any_simpl (f : ℕ → Bool) (l : List (ℕ ⊕ Bool)) (c : Sum.inr true ∉ l) :
    GateOp.eval GateOp.or ((l.filterMap Sum.getLeft?).map f) =
      GateOp.eval GateOp.or (l.map (Sum.elim f id)) := by
  show ((l.filterMap Sum.getLeft?).map f).any id = (l.map (Sum.elim f id)).any id
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨b, hb, hbt⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    obtain ⟨a, ha, e⟩ := List.mem_filterMap.mp hr
    rcases a with a | a
    · simp at e
      subst e
      exact ⟨_, List.mem_map.mpr ⟨_, ha, rfl⟩, hbt⟩
    · simp at e
  · rintro ⟨b, hb, hbt⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    rcases a with r | b
    · exact ⟨f r, List.mem_map.mpr ⟨r, List.mem_filterMap.mpr ⟨Sum.inl r, ha, rfl⟩, rfl⟩, hbt⟩
    · cases b
      · exact absurd hbt (by simp)
      · exact absurd ha c

lemma m7_and_reader (l : List ℕ) (m : ℕ) (u : ℕ → Bool) (hm : m ∈ l) (hu : u m = false) :
    GateOp.eval GateOp.and (l.map u) = false := by
  show (l.map u).all id = false
  apply Bool.eq_false_iff.mpr
  intro h
  rw [List.all_eq_true] at h
  have := h (u m) (List.mem_map.mpr ⟨m, hm, rfl⟩)
  rw [hu] at this
  exact absurd this (by simp)

lemma m7_or_reader (l : List ℕ) (hl : l.length ≤ 2) (m : ℕ) (hm : m ∈ l) :
    ∃ b, ∀ u : ℕ → Bool, u m = false → GateOp.eval GateOp.or (l.map u) = u b := by
  match l, hl, hm with
  | [], _, hm => simp at hm
  | [a], _, hm =>
    have e : m = a := by simpa using hm
    subst e
    exact ⟨m, fun u hu => by simp [GateOp.eval]⟩
  | [a, b], _, hm =>
    have e : m = a ∨ m = b := by simpa using hm
    rcases e with e | e
    · subst e
      exact ⟨b, fun u hu => by simp [GateOp.eval, hu]⟩
    · subst e
      exact ⟨a, fun u hu => by simp [GateOp.eval, hu]⟩
  | _ :: _ :: _ :: _, hl, _ =>
    exfalso
    simp only [List.length_cons] at hl
    omega

theorem m7_elim (n : ℕ) (D : List Bool → Prop) (hD : ∀ x, D x → x.length = n)
    (rm : ℕ → Prop) [DecidablePred rm] :
    ∀ gs : List Gate,
    (∀ i (hi : i < gs.length), ¬ rm i →
      (gs[i].op = GateOp.and ∨ gs[i].op = GateOp.or) ∧ gs[i].inputs.length ≤ 2) →
    (∀ i, i < gs.length → rm i →
      (∃ b : Bool, ∀ x, D x → (m7_run gs x).getD (n + i) false = b) ∨
      (∃ r, r < n + i ∧ ∀ x, D x → (m7_run gs x).getD (n + i) false = (m7_run gs x).getD r false)) →
    ∃ (gs' : List Gate) (φ : ℕ → ℕ ⊕ Bool),
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length + ((Finset.range gs.length).filter rm).card = gs.length ∧
      (∀ w, w < n + gs.length → ∀ r, φ w = Sum.inl r → r < n + gs'.length) ∧
      (∀ w, w < n + gs.length → ∀ x, D x →
        (m7_run gs x).getD w false = Sum.elim (fun r => (m7_run gs' x).getD r false) id (φ w)) := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ _
    refine ⟨[], Sum.inl, by simp, by simp, ?_, ?_⟩
    · intro w hw r hr
      cases hr
      simpa using hw
    · intro w hw x hx
      rfl
  | append_singleton gs g ih =>
    intro H1 H2
    have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
    have H1' : ∀ i (hi : i < gs.length), ¬ rm i →
        (gs[i].op = GateOp.and ∨ gs[i].op = GateOp.or) ∧ gs[i].inputs.length ≤ 2 := by
      intro i hi hr
      have := H1 i (by rw [hlen]; omega) hr
      rwa [List.getElem_append_left hi] at this
    have H2' : ∀ i, i < gs.length → rm i →
        (∃ b : Bool, ∀ x, D x → (m7_run gs x).getD (n + i) false = b) ∨
        (∃ r, r < n + i ∧ ∀ x, D x →
          (m7_run gs x).getD (n + i) false = (m7_run gs x).getD r false) := by
      intro i hi hr
      rcases H2 i (by rw [hlen]; omega) hr with ⟨b, hb⟩ | ⟨r, hr', hb⟩
      · left
        refine ⟨b, fun x hx => ?_⟩
        rw [← hb x hx, m7_run_snoc_getD_lt _ _ _ _ (by rw [hD x hx]; omega)]
      · right
        refine ⟨r, hr', fun x hx => ?_⟩
        have := hb x hx
        rwa [m7_run_snoc_getD_lt _ _ _ _ (by rw [hD x hx]; omega),
          m7_run_snoc_getD_lt _ _ _ _ (by rw [hD x hx]; omega)] at this
    obtain ⟨gs', φ, hv, hc, hb, hval⟩ := ih H1' H2'
    by_cases hrm : rm gs.length
    · have hcount : ((Finset.range (gs ++ [g]).length).filter rm).card =
          ((Finset.range gs.length).filter rm).card + 1 := by
        rw [hlen, Finset.range_add_one, Finset.filter_insert, ite_eq_left hrm,
          Finset.card_insert_of_notMem (by simp)]
      rcases H2 gs.length (by rw [hlen]; omega) hrm with ⟨b, hbb⟩ | ⟨r, hr', hbb⟩
      · refine ⟨gs', Function.update φ (n + gs.length) (Sum.inr b), hv,
          by rw [hcount, hlen]; omega, ?_, ?_⟩
        · intro w hw r hr
          by_cases e : w = n + gs.length
          · subst e
            rw [Function.update_self] at hr
            cases hr
          · rw [Function.update_of_ne e] at hr
            exact hb w (by rw [hlen] at hw; omega) r hr
        · intro w hw x hx
          by_cases e : w = n + gs.length
          · subst e
            rw [Function.update_self]
            exact hbb x hx
          · rw [Function.update_of_ne e,
              m7_run_snoc_getD_lt _ _ _ _ (by rw [hD x hx]; rw [hlen] at hw; omega)]
            exact hval w (by rw [hlen] at hw; omega) x hx
      · refine ⟨gs', Function.update φ (n + gs.length) (φ r), hv,
          by rw [hcount, hlen]; omega, ?_, ?_⟩
        · intro w hw r' hr
          by_cases e : w = n + gs.length
          · subst e
            rw [Function.update_self] at hr
            exact hb r hr' r' hr
          · rw [Function.update_of_ne e] at hr
            exact hb w (by rw [hlen] at hw; omega) r' hr
        · intro w hw x hx
          by_cases e : w = n + gs.length
          · subst e
            rw [Function.update_self, hbb x hx,
              m7_run_snoc_getD_lt _ _ _ _ (by rw [hD x hx]; omega)]
            exact hval r hr' x hx
          · rw [Function.update_of_ne e,
              m7_run_snoc_getD_lt _ _ _ _ (by rw [hD x hx]; rw [hlen] at hw; omega)]
            exact hval w (by rw [hlen] at hw; omega) x hx
    · obtain ⟨hop, hfan⟩ : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        have := H1 gs.length (by rw [hlen]; omega) hrm
        simpa using this
      let l : List (ℕ ⊕ Bool) :=
        g.inputs.map (fun r => if r < n + gs.length then φ r else Sum.inr false)
      have hl : l.length ≤ 2 := by simpa [l] using hfan
      have hold : ∀ x, D x → g.op.eval (g.inputs.map fun i => (m7_run gs x).getD i false) =
          g.op.eval (l.map (Sum.elim (fun r => (m7_run gs' x).getD r false) id)) := by
        intro x hx
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro a _
        by_cases c : a < n + gs.length
        · simp only [Function.comp_apply, ite_eq_left c]
          exact hval a c x hx
        · simp only [Function.comp_apply, ite_eq_right c, Sum.elim_inr, id]
          exact List.getD_eq_default _ _ (by rw [m7_run_length, hD x hx]; omega)
      have hg' : ∃ g' : Gate, ((g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2) ∧
          ∀ f : ℕ → Bool, g'.op.eval (g'.inputs.map f) = g.op.eval (l.map (Sum.elim f id)) := by
        have hfl : (l.filterMap Sum.getLeft?).length ≤ 2 :=
          (List.length_filterMap_le _ _).trans hl
        rcases hop with hop | hop
        · by_cases c : Sum.inr false ∈ l
          · refine ⟨⟨GateOp.or, []⟩, ⟨Or.inr rfl, by simp⟩, fun f => ?_⟩
            rw [hop]
            exact m7_and_false f l c
          · refine ⟨⟨GateOp.and, l.filterMap Sum.getLeft?⟩, ⟨Or.inl rfl, hfl⟩, fun f => ?_⟩
            rw [hop]
            exact m7_all_simpl f l c
        · by_cases c : Sum.inr true ∈ l
          · refine ⟨⟨GateOp.and, []⟩, ⟨Or.inl rfl, by simp⟩, fun f => ?_⟩
            rw [hop]
            exact m7_or_true f l c
          · refine ⟨⟨GateOp.or, l.filterMap Sum.getLeft?⟩, ⟨Or.inr rfl, hfl⟩, fun f => ?_⟩
            rw [hop]
            exact m7_any_simpl f l c
      obtain ⟨g', hg'v, hg'e⟩ := hg'
      have hcount : ((Finset.range (gs ++ [g]).length).filter rm).card =
          ((Finset.range gs.length).filter rm).card := by
        rw [hlen, Finset.range_add_one, Finset.filter_insert, ite_eq_right hrm]
      have hlen' : (gs' ++ [g']).length = gs'.length + 1 := by simp
      refine ⟨gs' ++ [g'], Function.update φ (n + gs.length) (Sum.inl (n + gs'.length)),
        ?_, ?_, ?_, ?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hv a ha
        · have e : a = g' := by simpa using ha
          subst e
          exact hg'v
      · rw [hcount, hlen, hlen']
        omega
      · intro w hw r hr
        rw [hlen']
        by_cases e : w = n + gs.length
        · subst e
          rw [Function.update_self] at hr
          cases hr
          omega
        · rw [Function.update_of_ne e] at hr
          have := hb w (by rw [hlen] at hw; omega) r hr
          omega
      · intro w hw x hx
        have hxl := hD x hx
        by_cases e : w = n + gs.length
        · subst e
          rw [Function.update_self]
          have e1 : (m7_run (gs ++ [g]) x).getD (n + gs.length) false =
              g.op.eval (g.inputs.map fun i => (m7_run gs x).getD i false) := by
            have := m7_run_snoc_getD_eq gs g x
            rwa [hxl] at this
          have e2 : (m7_run (gs' ++ [g']) x).getD (n + gs'.length) false =
              g'.op.eval (g'.inputs.map fun i => (m7_run gs' x).getD i false) := by
            have := m7_run_snoc_getD_eq gs' g' x
            rwa [hxl] at this
          show (m7_run (gs ++ [g]) x).getD (n + gs.length) false =
            (m7_run (gs' ++ [g']) x).getD (n + gs'.length) false
          rw [e1, e2, hold x hx, hg'e]
        · have hw' : w < n + gs.length := by rw [hlen] at hw; omega
          rw [Function.update_of_ne e, m7_run_snoc_getD_lt _ _ _ _ (by rw [hxl]; exact hw'),
            hval w hw' x hx]
          rcases hφ : φ w with r | b
          · show (m7_run gs' x).getD r false = (m7_run (gs' ++ [g']) x).getD r false
            rw [m7_run_snoc_getD_lt _ _ _ _ (by rw [hxl]; exact hb w hw' r hφ)]
          · rfl

def m7_Dom (L : Fin 13 → Finset (Fin 13)) (x : Fin 13 → Bool) : Prop :=
  (∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨
    ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s

def m7_DomL (L : Fin 13 → Finset (Fin 13)) (xs : List Bool) : Prop :=
  ∃ x : Fin 13 → Bool, xs = List.ofFn x ∧ m7_Dom L x

def m7_Rm (gates : List Gate) (j h : ℕ) (i : ℕ) : Prop :=
  i = j ∨ i = h ∨ (j < i ∧ ∃ hi : i < gates.length, 13 + j ∈ gates[i].inputs)


-- The wire evaluation lemmas follow L-meta-1457.
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

lemma or_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n ≤ w) (h : w - n < C.gates.length) (hop : C.gates[w - n].op = GateOp.or) :
    value C x w = true ↔ ∃ r ∈ C.gates[w - n].inputs, r < w ∧ value C x r = true := by
  have hlt : w < n + C.size := by unfold Circuit.size; omega
  rw [gate_value C x w hw hlt]
  simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨r, hr, hv⟩
    by_cases h' : r < w
    · exact ⟨r, hr, h', by simpa [h'] using hv⟩
    · simp [h'] at hv
  · rintro ⟨r, hr, h', hv⟩
    exact ⟨r, hr, by simp [h', hv]⟩

lemma and_false {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n ≤ w) (h : w - n < C.gates.length) (hop : C.gates[w - n].op = GateOp.and) :
    value C x w = false ↔ ∃ r ∈ C.gates[w - n].inputs, w ≤ r ∨ value C x r = false := by
  have hlt : w < n + C.size := by unfold Circuit.size; omega
  rw [gate_value C x w hw hlt]
  simp only [hop, GateOp.eval, List.all_map, List.all_eq_false, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨r, hr, hf⟩
    by_cases h' : r < w
    · exact ⟨r, hr, Or.inr (by simpa [h'] using hf)⟩
    · exact ⟨r, hr, Or.inl (by omega)⟩
  · rintro ⟨r, hr, hf | hf⟩
    · exact ⟨r, hr, by simp [show ¬ r < w by omega]⟩
    · exact ⟨r, hr, by simp [hf]⟩

-- The backward expansion from L-meta-1461 is specialized to a fixed negative input.
private lemma cut {n : ℕ} (C : Circuit) (neg : Fin n → Bool) (G paid : Finset ℕ)
    (parents : ∀ w ∈ G, ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∉ paid → P.card ≤ 1) ∧
      (∀ r ∈ P, r<w) ∧ ∀ x : Fin n → Bool,
        (∀ r ∈ P, value C x r=true → value C neg r=true) → value C x w=true → value C neg w=true)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + ((G ∩ paid).filter (· < t)).card ∧
      ∀ x : Fin n → Bool,
        (∀ w ∈ B, value C x w=true → value C neg w=true) →
        ∀ w ∈ F, value C x w=true → value C neg w=true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F,Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right ..,fun _ h => h⟩
  | succ t ih =>
    have increases : ((G ∩ paid).filter (· < t)).card ≤ ((G ∩ paid).filter (· < t+1)).card :=
      Finset.card_le_card fun w hw => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hw).1,by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases expand : t ∈ F ∧ t ∈ G
    · obtain ⟨P,lim,free,lt,step⟩ := parents t expand.2
      let F' := F.erase t ∪ P
      have smaller : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw|hw
        · have ne := (Finset.mem_erase.mp hw).1
          have := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact lt w hw
      obtain ⟨B,dis,size,chains⟩ := ih F' smaller
      refine ⟨B,dis,?_,?_⟩
      · have union := Finset.card_union_le (F.erase t) P
        change F'.card ≤ _ at union
        have old := Finset.card_erase_add_one expand.1
        by_cases hp : t ∈ paid
        · have eq : (G ∩ paid).filter (· < t+1) = insert t ((G ∩ paid).filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter,Finset.mem_insert]
            constructor
            · rintro ⟨inc,bound⟩
              by_cases ne : w=t
              · exact Or.inl ne
              · exact Or.inr ⟨inc,by omega⟩
            · rintro (rfl|⟨inc,bound⟩)
              · exact ⟨Finset.mem_inter.mpr ⟨expand.2,hp⟩,by omega⟩
              · exact ⟨inc,by omega⟩
          rw [eq,Finset.card_insert_of_notMem (by simp)]
          omega
        · have := free hp
          omega
      · intro x hxy w hw
        by_cases eq : w=t
        · subst w
          exact step x fun r hr => chains x hxy r (Finset.mem_union_right _ hr)
        · exact chains x hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hw⟩))
    · have smaller : ∀ w ∈ F, w ∈ G → w<t := by
        intro w hw hg
        have ne : w≠t := fun e => expand ⟨e ▸ hw,e ▸ hg⟩
        have := hF w hw hg
        omega
      obtain ⟨B,dis,size,chains⟩ := ih F smaller
      exact ⟨B,dis,by omega,chains⟩

abbrev P := Fin 13
abbrev Good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def isOrWire (C : Circuit) (w : ℕ) : Prop :=
  ∃ i : Fin C.gates.length, w = 13 + i.val ∧ (C.gates.get i).op = GateOp.or

noncomputable def orWires (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.Ico 13 (13+C.size)).filter (isOrWire C)

def input (U : Finset P) (v : P) := decide (v ∈ U)
def neg (N : Finset P) (v : P) := decide (v ∉ N)
def hits (C : Circuit) (T : Finset P) (R : P → Finset P) (w : ℕ) :=
  T.filter (fun p => value C (input (R p)) w = true)

def wide (C : Circuit) (N T : Finset P) (R : P → Finset P) (w : ℕ) : Prop :=
  value C (neg N) w = false ∧ 2 ≤ (hits C T R w).card

noncomputable def eligible (C : Circuit) (N T : Finset P) (R : P → Finset P) : Finset ℕ := by
  classical
  exact (Finset.Ico 13 (13+C.size)).filter (wide C N T R)

noncomputable def pay (C : Circuit) (N T : Finset P) (R : P → Finset P) : Finset ℕ :=
  eligible C N T R ∩ orWires C

lemma row (C : Circuit) (valid : Good C) (N T : Finset P) (R : P → Finset P) (o : ℕ)
    (sep : ∀ p ∈ T, R p ∩ N = {p}) (hneg : value C (neg N) o = false)
    (hpos : ∀ p ∈ T, value C (input (R p)) o = true) :
    T.card - 1 ≤ (pay C N T R).card := by
  classical
  let G := eligible C N T R
  have isGate (w : ℕ) (c : wide C N T R w) : 13 ≤ w ∧ w < 13+C.size := by
    obtain ⟨zero,big⟩ := c
    constructor
    · by_contra! lt
      let a : P := ⟨w,lt⟩
      have aa : a ∈ N := by
        change value C (neg N) a = false at zero
        simpa [input_value, neg] using zero
      have sub : hits C T R w ⊆ {a} := by
        intro p hp
        obtain ⟨ht, hv⟩ := Finset.mem_filter.mp hp
        change value C (input (R p)) a = true at hv
        have both : a ∈ R p ∩ N := Finset.mem_inter.mpr ⟨by simpa [input_value,input] using hv,aa⟩
        rw [sep p ht, Finset.mem_singleton] at both
        simpa only [Finset.mem_singleton] using both.symm
      have bound := Finset.card_le_card sub
      simp only [Finset.card_singleton] at bound
      omega
    · by_contra! high
      have none : hits C T R w = ∅ := by ext p; simp [hits, missing_value C _ w high]
      simp [none] at big
  have parents (w : ℕ) (hw : w ∈ G) : ∃ S : Finset ℕ, S.card ≤ 2 ∧
      (w ∉ orWires C → S.card ≤ 1) ∧ (∀ r ∈ S, r < w) ∧
      ∀ x : P → Bool, (∀ r ∈ S, value C x r = true → value C (neg N) r = true) →
      value C x w = true → value C (neg N) w = true := by
    obtain ⟨bounds, c⟩ := Finset.mem_filter.mp (show w ∈ (Finset.Ico 13 (13+C.size)).filter (wide C N T R) from hw)
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
    have ix : w - 13 < C.gates.length := by unfold Circuit.size at hi; omega
    obtain ⟨ha | ho,_⟩ := valid C.gates[w-13] (List.getElem_mem _)
    · obtain ⟨r,hr,bad⟩ := (and_false C (neg N) w lo ix ha).mp c.1
      by_cases lt : r < w
      · have no := bad.resolve_left (Nat.not_le_of_gt lt)
        refine ⟨{r},by simp,by simp,by simpa using lt,?_⟩
        intro x step hx
        cases hx' : value C x r with
        | false => exact (Bool.false_ne_true (((and_false C x w lo ix ha).mpr ⟨r, hr, Or.inr hx'⟩).symm.trans hx)).elim
        | true => exact (Bool.false_ne_true (no.symm.trans (step r (Finset.mem_singleton_self r) hx'))).elim
      · refine ⟨∅,by simp,by simp,by simp,?_⟩
        intro x _ hx
        exact (Bool.false_ne_true (((and_false C x w lo ix ha).mpr ⟨r,hr,Or.inl (by omega)⟩).symm.trans hx)).elim
    · have isOr : w ∈ orWires C := Finset.mem_filter.mpr ⟨bounds, ⟨⟨w-13,ix⟩,by change w = 13 + (w-13); omega,ho⟩⟩
      obtain ⟨S, size, lt, step⟩ := gate_inputs C valid w lo hi
      exact ⟨S,size,fun missing => (missing isOr).elim,lt,fun x => step x (neg N)⟩
  obtain ⟨B,dis,size,chain⟩ := cut C (neg N) G (orWires C) parents (13+C.size) {o}
    (fun w _ hg => (Finset.mem_Ico.mp (Finset.mem_filter.mp hg).1).2)
  let parts (w : ℕ) := if value C (neg N) w = false then hits C T R w else ∅
  have small (w : ℕ) (hb : w ∈ B) : (parts w).card ≤ 1 := by
    by_cases zero : value C (neg N) w = false
    · simp only [parts,ite_eq_left zero]
      by_contra! big
      have c : wide C N T R w := ⟨zero,by omega⟩
      exact Finset.disjoint_left.mp dis hb (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (isGate w c),c⟩)
    · simp [parts,zero]
  have cover : T ⊆ B.biUnion parts := by
    intro p hp
    by_contra no
    have step (w : ℕ) (hb : w ∈ B) (yes : value C (input (R p)) w=true) : value C (neg N) w=true := by
      cases zero : value C (neg N) w with
      | true => rfl
      | false => exact (no (Finset.mem_biUnion.mpr ⟨w,hb,by simp [parts,zero,hits,hp,yes]⟩)).elim
    exact Bool.false_ne_true (hneg.symm.trans (chain (input (R p)) step o (Finset.mem_singleton_self o) (hpos p hp)))
  have bound := (Finset.card_le_card cover).trans (Finset.card_biUnion_le_card_mul B parts 1 small)
  have lim := Finset.card_filter_le (G ∩ orWires C) (· < 13+C.size)
  change ((G ∩ orWires C).filter (· < 13+C.size)).card ≤ (pay C N T R).card at lim
  simp only [Finset.card_singleton] at size
  simp only [mul_one] at bound
  omega

def clash (N T : P → Finset P) (R : P → P → Finset P) (i j : P) : Prop :=
  ∃ p ∈ T i, p ∉ N j ∧ (R i p ∩ N j).Nonempty

lemma collect (C : Circuit) (valid : Good C) (N T : P → Finset P) (R : P → P → Finset P)
    (o : P → ℕ) (inside : ∀ i, T i ⊆ N i) (thin : ∀ i j, i ≠ j → (N i ∩ N j).card ≤ 1)
    (sep : ∀ i p, p ∈ T i → R i p ∩ N i = {p})
    (apart : ∀ i j, i ≠ j → ¬ (clash N T R i j ∧ clash N T R j i))
    (low : ∀ i, value C (neg (N i)) (o i) = false)
    (pos : ∀ i p, p ∈ T i → value C (input (R i p)) (o i) = true) :
    (∑ i : P, ((T i).card - 1)) ≤ (orWires C).card := by
  classical
  let bills (i : P) := pay C (N i) (T i) (R i)
  have info {w : ℕ} {i : P} (hw : w ∈ bills i) : wide C (N i) (T i) (R i) w :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2
  have cross {w : ℕ} {i j : P} (ne : i ≠ j) (hi : w ∈ bills i) (hj : w ∈ bills j) : clash N T R i j := by
    let H := hits C (T i) (R i) w
    have many : 2 ≤ H.card := (info hi).2
    have outside : ∃ p ∈ H, p ∉ N j := by
      by_contra! allIn
      have sub : H ⊆ N i ∩ N j := fun p hp =>
        Finset.mem_inter.mpr ⟨inside i (Finset.mem_filter.mp hp).1,allIn p hp⟩
      have lim := Finset.card_le_card sub
      have lim' := thin i j ne
      omega
    obtain ⟨p,hp,pj⟩ := outside
    obtain ⟨pt,fires⟩ := Finset.mem_filter.mp hp
    refine ⟨p,pt,pj,?_⟩
    by_contra dry
    have le (v : P) (hv : input (R i p) v = true) : neg (N j) v = true := by
      exact decide_eq_true (fun h => dry ⟨v, Finset.mem_inter.mpr ⟨of_decide_eq_true hv,h⟩⟩)
    have both := value_mono C valid _ _ le w fires
    exact Bool.false_ne_true ((info hj).1.symm.trans both)
  have dis (i j : P) (diff : i ≠ j) : Disjoint (bills i) (bills j) := by
    apply Finset.disjoint_left.mpr
    intro w hi hj
    exact apart i j diff ⟨cross diff hi hj,cross diff.symm hj hi⟩
  have sub : Finset.univ.biUnion bills ⊆ orWires C := by
    intro w hw
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_inter.mp hi).2
  calc
    (∑ i : P, ((T i).card-1)) ≤ ∑ i : P, (bills i).card :=
      Finset.sum_le_sum fun i _ => row C valid _ _ _ _ (sep i) (low i) (pos i)
    _ = (Finset.univ.biUnion bills).card := (Finset.card_biUnion (fun i _ j _ h => dis i j h)).symm
    _ ≤ _ := Finset.card_le_card sub

lemma or_split (C : Circuit) (onlyOr : ∀ g ∈ C.gates, g.op = GateOp.or)
    (x y : P → Bool) (w : ℕ) : value C (fun v => x v || y v) w = true →
    value C x w = true ∨ value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases var : w < 13
    · let p : P := ⟨w,var⟩
      change value C _ p = true → value C x p = true ∨ value C y p = true
      simp [input_value]
    by_cases range : w < 13+C.size
    · have before : w-13 < C.gates.length := by unfold Circuit.size at range; omega
      have hop := onlyOr C.gates[w-13] (List.getElem_mem _)
      simp only [or_value C _ w (by omega) before hop]
      rintro ⟨r,hr,lt,hy⟩
      rcases ih r lt hy with yes | yes
      · exact Or.inl ⟨r,hr,lt,yes⟩
      · exact Or.inr ⟨r,hr,lt,yes⟩
    · simp [missing_value C _ w (by omega : 13+C.size ≤ w)]

def line (i : P) : Finset P := {i,i+1,i+3,i+9}
def A : Finset P := {0,1,3}
def labels (i : P) : Finset P := if i=0 then A else line i

def anchor (i : P) : P := if 0 ∈ line i then 1 else if 1 ∈ line i then 3 else 0

def test (i p : P) : Finset P := if i=0 ∨ p ∈ A then {p} else {p,anchor i}

lemma geoThin : ∀ i j : P, i ≠ j → (line i ∩ line j).card ≤ 1 := by decide
lemma label_sub : ∀ i : P, labels i ⊆ line i := by decide
lemma anchor_good : ∀ i : P, i ≠ 0 → anchor i ∈ A ∧ anchor i ∉ line i := by decide
lemma anchor_dir : ∀ i j : P, i ≠ 0 → j ≠ 0 → ¬ (anchor i ∈ line j ∧ anchor j ∈ line i) := by decide
lemma partial_sum : (∑ i : P, ((labels i).card-1)) = 38 := by decide
lemma full_sum : (∑ i : P, ((line i).card-1)) = 39 := by decide

lemma test_sep (i p : P) (hp : p ∈ labels i) : test i p ∩ line i = {p} := by
  have hpi := label_sub i hp
  by_cases small : i=0 ∨ p ∈ A
  · simp [test,small,hpi]
  · have ne : i ≠ 0 := fun eq => small (Or.inl eq)
    ext t
    simp [test,small]
    constructor
    · rintro ⟨rfl|rfl,ht⟩
      · rfl
      · exact ((anchor_good i ne).2 ht).elim
    · rintro rfl
      exact ⟨Or.inl rfl,hpi⟩

lemma test_active (i p : P) (hp : p ∈ labels i) : (test i p ∩ A).Nonempty := by
  by_cases inA : p ∈ A
  · exact ⟨p,by simp [test,inA]⟩
  · have ne : i ≠ 0 := by rintro rfl; exact inA (by simpa [labels] using hp)
    exact ⟨anchor i,by simp [test,inA,ne,(anchor_good i ne).1]⟩

lemma clash_anchor {i j : P} (h : clash line labels test i j) : i ≠ 0 ∧ anchor i ∈ line j := by
  obtain ⟨p,_,pj,v,hv⟩ := h
  obtain ⟨vr,vj⟩ := Finset.mem_inter.mp hv
  by_cases small : i=0 ∨ p ∈ A
  · have eq : v=p := by simpa [test,small] using vr
    exact (pj (eq ▸ vj)).elim
  · have choices : v=p ∨ v=anchor i := by simpa [test,small] using vr
    exact ⟨fun eq => small (Or.inl eq),(choices.resolve_left (fun eq => pj (eq ▸ vj))) ▸ vj⟩

lemma test_apart (i j : P) (_ : i ≠ j) : ¬ (clash line labels test i j ∧ clash line labels test j i) := by
  rintro ⟨a,b⟩
  obtain ⟨hi,fi⟩ := clash_anchor a
  obtain ⟨hj,fj⟩ := clash_anchor b
  exact anchor_dir i j hi hj ⟨fi,fj⟩

def domain (x : P → Bool) : Prop := (∃ v ∈ A, x v = true) ∨ ∃ s : P, ∀ v : P, x v = false → v ∈ line s

lemma main_bound (C : Circuit) (o : P → ℕ) (valid : Good C)
    (correct : ∀ (i : P) (x : P → Bool), domain x → value C x (o i) = decide (∃ v ∈ line i, x v = true)) :
    39 ≤ C.size := by
  classical
  have low (i : P) : value C (neg (line i)) (o i) = false := by
    have dom : domain (neg (line i)) := Or.inr ⟨i,fun v h => by simpa [neg] using h⟩
    rw [correct i _ dom]
    apply decide_eq_false
    rintro ⟨v,vin,h⟩
    exact (of_decide_eq_true h) vin
  have pos (i p : P) (hp : p ∈ labels i) : value C (input (test i p)) (o i) = true := by
    obtain ⟨v,hv⟩ := test_active i p hp
    obtain ⟨inside,good⟩ := Finset.mem_inter.mp hv
    have dom : domain (input (test i p)) := Or.inl ⟨v,good,decide_eq_true inside⟩
    rw [correct i _ dom]
    have both : p ∈ test i p ∩ line i := by rw [test_sep i p hp]; simp
    exact decide_eq_true ⟨p,label_sub i hp,decide_eq_true (Finset.mem_inter.mp both).1⟩
  have partialCount := collect C valid line labels test o label_sub geoThin test_sep test_apart low pos
  rw [partial_sum] at partialCount
  by_contra! short
  have total : (Finset.Ico 13 (13+C.size)).card = C.size := by simp
  have sub : orWires C ⊆ Finset.Ico 13 (13+C.size) := Finset.filter_subset _ _
  have allGates : orWires C = Finset.Ico 13 (13+C.size) := Finset.eq_of_subset_of_card_le sub (by omega)
  have onlyOr : ∀ g ∈ C.gates, g.op = GateOp.or := by
    intro g hg
    obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hg
    have w : 13+k ∈ orWires C := by rw [allGates]; exact Finset.mem_Ico.mpr ⟨by omega, by unfold Circuit.size; omega⟩
    obtain ⟨i,hi,hop⟩ := (Finset.mem_filter.mp w).2
    have idx : i = (⟨k,hk⟩ : Fin C.gates.length) := by apply Fin.ext; change i.val=k; omega
    subst i
    exact hop
  let single (_ p : P) : Finset P := {p}
  have posSingle (i p : P) (hp : p ∈ line i) : value C (input (single i p)) (o i) = true := by
    let x := neg (line i)
    let y := input (single i p)
    let z (v : P) := x v || y v
    have dom : domain z := Or.inr ⟨i,fun v h => by
      by_contra hv
      have yes : x v = true := decide_eq_true hv
      simp [z,yes] at h⟩
    have yes : value C z (o i) = true := by
      rw [correct i _ dom]
      exact decide_eq_true ⟨p,hp,by simp [z,y,single,input]⟩
    exact (or_split C onlyOr x y _ yes).resolve_left (fun h => Bool.false_ne_true ((low i).symm.trans h))
  have apart (i j : P) (_ : i ≠ j) : ¬ (clash line line single i j ∧ clash line line single j i) := by
    rintro ⟨⟨p,_,pj,v,hv⟩,_⟩
    obtain ⟨inS,vj⟩ := Finset.mem_inter.mp hv
    have eq : v=p := Finset.mem_singleton.mp inS
    exact pj (eq ▸ vj)
  have fullCount := collect C valid line line single o (fun _ => Finset.Subset.rfl) geoThin
    (fun i p hp => by simp [single,hp]) apart low posSingle
  rw [full_sum,allGates,total] at fullCount
  omega



theorem M6 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), ((∃ v ∈ ({0, 1, 3} : Finset (Fin 13)), x v = true) ∨ ∃ s : Fin 13, ∀ v : Fin 13, x v = false → v ∈ L s) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    39 ≤ gates.length := by
  intro L hL gates o good correct
  have eq : L = line := funext hL
  subst L
  exact main_bound ⟨gates,0⟩ o good correct

theorem m7_reduction (L : Fin 13 → Finset (Fin 13))
    (hL : ∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9})
    (gates : List Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length)
    (valid : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (opj : (gates.get j).op = GateOp.not)
    (unique : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hj : h < j) (hin : ∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r)
    (computes : ∀ (t : Fin 13) (x : Fin 13 → Bool),
      Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true))
    (hco : ∀ t : Fin 13, Circuit.eval ⟨gates, 13 + (h : ℕ)⟩
      (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true)
    (hpt : ∀ a ∈ ({0, 1, 3} : Finset (Fin 13)), Circuit.eval ⟨gates, 13 + (h : ℕ)⟩
      (List.ofFn (fun v : Fin 13 => decide (v = a))) = true) :
    41 + (Finset.univ.filter (fun i : Fin gates.length =>
      j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card ≤ gates.length := by
  classical
  have hjh : (h : ℕ) < (j : ℕ) := hj
  have jl : (j : ℕ) < gates.length := j.isLt
  have hD' : ∀ xs, m7_DomL L xs → xs.length = 13 := by
    rintro xs ⟨x, rfl, _⟩
    simp
  have evalrun : ∀ (w : ℕ) (xs : List Bool),
      Circuit.eval ⟨gates, w⟩ xs = (m7_run gates xs).getD w false := fun _ _ => rfl
  have ofn : ∀ (x : Fin 13 → Bool) (w : ℕ), (List.ofFn x).getD w false = true →
      ∃ v : Fin 13, (v : ℕ) = w ∧ x v = true := by
    intro x w hw
    by_cases c : w < 13
    · refine ⟨⟨w, c⟩, rfl, ?_⟩
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact c), List.getElem_ofFn] at hw
      exact hw
    · rw [List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)] at hw
      exact absurd hw (by simp)
  have ofn' : ∀ (x : Fin 13 → Bool) (v : Fin 13), (List.ofFn x).getD (v : ℕ) false = x v := by
    intro x v
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact v.isLt), List.getElem_ofFn]
  have preop : ∀ g ∈ gates.take j, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have hi' : i < (j : ℕ) := by
      have := hi
      simp at this
      omega
    rw [List.getElem_take]
    rcases (valid gates[i] (List.getElem_mem _)).1 with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · have := congrArg Fin.val (unique ⟨i, by omega⟩ a)
      simp at this
      omega
  have hA : ∀ x, m7_Dom L x → (m7_run gates (List.ofFn x)).getD (13 + (h : ℕ)) false = true := by
    intro x hx
    have key : ∀ y : Fin 13 → Bool, (∀ v, y v = true → x v = true) →
        (m7_run gates (List.ofFn y)).getD (13 + (h : ℕ)) false = true →
        (m7_run gates (List.ofFn x)).getD (13 + (h : ℕ)) false = true := by
      intro y hy hyv
      have l1 := m7_prefix_value gates (List.ofFn y) j (13 + h)
        (by rw [List.length_ofFn]; omega) (by omega)
      have l2 := m7_prefix_value gates (List.ofFn x) j (13 + h)
        (by rw [List.length_ofFn]; omega) (by omega)
      rw [l1] at hyv
      rw [l2]
      refine m7_mono_all _ preop (List.ofFn y) (List.ofFn x) (by simp) ?_ _ hyv
      intro w hw
      obtain ⟨v, rfl, hv⟩ := ofn y w hw
      rw [ofn']
      exact hy v hv
    rcases hx with ⟨a, ha, hxa⟩ | ⟨s, hs⟩
    · refine key (fun v => decide (v = a)) (fun v hv => ?_) (hpt a ha)
      have e : v = a := of_decide_eq_true hv
      rw [e]
      exact hxa
    · refine key (fun v => decide (v ∉ L s)) (fun v hv => ?_) (hco s)
      have e : v ∉ L s := of_decide_eq_true hv
      by_contra c
      exact e (hs v (by simpa using c))
  have hB : ∀ x, m7_Dom L x → (m7_run gates (List.ofFn x)).getD (13 + (j : ℕ)) false = false := by
    intro x hx
    obtain ⟨r, hr⟩ := hin
    have gv := m7_gate_value gates (List.ofFn x) j jl
    rw [List.length_ofFn] at gv
    have opj' : gates[(j : ℕ)].op = GateOp.not := opj
    have hr' : gates[(j : ℕ)].inputs = (13 + (h : ℕ)) :: r := hr
    have pv := m7_prefix_value gates (List.ofFn x) j (13 + h)
      (by rw [List.length_ofFn]; omega) (by omega)
    rw [gv, opj', hr']
    show (!((m7_run (gates.take j) (List.ofFn x)).getD (13 + (h : ℕ)) false)) = false
    rw [← pv, hA x hx]
    rfl
  have H1 : ∀ i (hi : i < gates.length), ¬ m7_Rm gates j h i →
      (gates[i].op = GateOp.and ∨ gates[i].op = GateOp.or) ∧ gates[i].inputs.length ≤ 2 := by
    intro i hi hr
    obtain ⟨a, b⟩ := valid gates[i] (List.getElem_mem _)
    refine ⟨?_, b⟩
    rcases a with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact absurd (Or.inl (congrArg Fin.val (unique ⟨i, hi⟩ a))) hr
  have H2 : ∀ i, i < gates.length → m7_Rm gates j h i →
      (∃ b : Bool, ∀ xs, m7_DomL L xs → (m7_run gates xs).getD (13 + i) false = b) ∨
      (∃ r, r < 13 + i ∧ ∀ xs, m7_DomL L xs →
        (m7_run gates xs).getD (13 + i) false = (m7_run gates xs).getD r false) := by
    intro i hi hr
    rcases hr with e | e | ⟨hji, hi', hmem⟩
    · left
      refine ⟨false, ?_⟩
      rintro xs ⟨x, rfl, hx⟩
      rw [e]
      exact hB x hx
    · left
      refine ⟨true, ?_⟩
      rintro xs ⟨x, rfl, hx⟩
      rw [e]
      exact hA x hx
    · have ne : i ≠ (j : ℕ) := by omega
      obtain ⟨a, b⟩ := valid gates[i] (List.getElem_mem _)
      have gv : ∀ x : Fin 13 → Bool, (m7_run gates (List.ofFn x)).getD (13 + i) false =
          gates[i].op.eval (gates[i].inputs.map fun r =>
            (m7_run (gates.take i) (List.ofFn x)).getD r false) := by
        intro x
        have := m7_gate_value gates (List.ofFn x) i hi
        rwa [List.length_ofFn] at this
      have uj : ∀ x, m7_Dom L x →
          (m7_run (gates.take i) (List.ofFn x)).getD (13 + (j : ℕ)) false = false := by
        intro x hx
        rw [← m7_prefix_value gates (List.ofFn x) i (13 + j)
          (by rw [List.length_ofFn]; omega) (by omega)]
        exact hB x hx
      rcases a with a | a | a
      · left
        refine ⟨false, ?_⟩
        rintro xs ⟨x, rfl, hx⟩
        rw [gv, a]
        exact m7_and_reader _ _ _ hmem (uj x hx)
      · obtain ⟨b', hb'⟩ := m7_or_reader gates[i].inputs b (13 + j) hmem
        by_cases c : b' < 13 + i
        · right
          refine ⟨b', c, ?_⟩
          rintro xs ⟨x, rfl, hx⟩
          rw [gv, a, m7_prefix_value gates (List.ofFn x) i b'
            (by rw [List.length_ofFn]; exact c) (by omega)]
          exact hb' _ (uj x hx)
        · left
          refine ⟨false, ?_⟩
          rintro xs ⟨x, rfl, hx⟩
          rw [gv, a]
          have := hb' (fun r => (m7_run (gates.take i) (List.ofFn x)).getD r false) (uj x hx)
          rw [this]
          exact List.getD_eq_default _ _ (by rw [m7_run_length, List.length_ofFn]; simp; omega)
      · exact absurd (congrArg Fin.val (unique ⟨i, hi⟩ a)) ne
  obtain ⟨gs', φ, hv, hc, hb, hval⟩ := m7_elim 13 (m7_DomL L) hD' (m7_Rm gates j h) gates H1 H2
  have hcount : (Finset.univ.filter (fun i : Fin gates.length =>
      j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤
      ((Finset.range gates.length).filter (m7_Rm gates j h)).card := by
    set K := Finset.univ.filter (fun i : Fin gates.length =>
      j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs) with hK
    have h1 : (K.image Fin.val).card = K.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have hjK : (j : ℕ) ∉ K.image Fin.val := by
      intro hm
      obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hm
      have lt : (j : ℕ) < (i : ℕ) := (Finset.mem_filter.mp hi).2.1
      omega
    have hhK : (h : ℕ) ∉ insert (j : ℕ) (K.image Fin.val) := by
      intro hm
      rcases Finset.mem_insert.mp hm with e | hm
      · omega
      · obtain ⟨i, hi, e⟩ := Finset.mem_image.mp hm
        have lt : (j : ℕ) < (i : ℕ) := (Finset.mem_filter.mp hi).2.1
        omega
    have sub : insert (h : ℕ) (insert (j : ℕ) (K.image Fin.val)) ⊆
        (Finset.range gates.length).filter (m7_Rm gates j h) := by
      intro a ha
      rw [Finset.mem_filter, Finset.mem_range]
      rcases Finset.mem_insert.mp ha with e | ha
      · exact ⟨by omega, Or.inr (Or.inl e)⟩
      · rcases Finset.mem_insert.mp ha with e | ha
        · exact ⟨by omega, Or.inl e⟩
        · obtain ⟨i, hi, e⟩ := Finset.mem_image.mp ha
          obtain ⟨_, p1, p2⟩ := Finset.mem_filter.mp hi
          subst e
          exact ⟨i.isLt, Or.inr (Or.inr ⟨p1, i.isLt, p2⟩)⟩
    have le := Finset.card_le_card sub
    rw [Finset.card_insert_of_notMem hhK, Finset.card_insert_of_notMem hjK, h1] at le
    omega
  have allones : m7_Dom L (fun _ => true) := Or.inl ⟨0, by simp, rfl⟩
  have coline : ∀ t, m7_Dom L (fun v => decide (v ∉ L t)) :=
    fun t => Or.inr ⟨t, fun v hv => by simpa using hv⟩
  have nonconst : ∀ (t : Fin 13) (b : Bool),
      ¬ (∀ x, m7_Dom L x → (m7_run gates (List.ofFn x)).getD (o t) false = b) := by
    intro t b hbc
    have e1 := hbc _ allones
    have e2 := hbc _ (coline t)
    rw [← evalrun, computes] at e1 e2
    have t1 : ∃ v ∈ L t, (fun _ : Fin 13 => true) v = true := ⟨t, by rw [hL t]; simp, rfl⟩
    have t2 : ¬ ∃ v ∈ L t, (fun v : Fin 13 => decide (v ∉ L t)) v = true := by
      rintro ⟨v, hv, hd⟩
      exact (of_decide_eq_true hd) hv
    have e1' : true = b := by
      rw [← e1]
      exact (decide_eq_true t1).symm
    have e2' : false = b := by
      rw [← e2]
      exact (decide_eq_false t2).symm
    rw [← e1'] at e2'
    exact absurd e2' (by simp)
  have outs : ∀ t : Fin 13, ∃ o' : ℕ, ∀ x, m7_Dom L x →
      (m7_run gs' (List.ofFn x)).getD o' false = decide (∃ v ∈ L t, x v = true) := by
    intro t
    by_cases c : o t < 13 + gates.length
    · rcases hφ : φ (o t) with r | b
      · refine ⟨r, fun x hx => ?_⟩
        have := hval (o t) c (List.ofFn x) ⟨x, rfl, hx⟩
        rw [hφ] at this
        rw [← computes t x, evalrun, this]
        rfl
      · exfalso
        refine nonconst t b (fun x hx => ?_)
        have := hval (o t) c (List.ofFn x) ⟨x, rfl, hx⟩
        rw [hφ] at this
        exact this
    · exfalso
      refine nonconst t false (fun x hx => ?_)
      exact List.getD_eq_default _ _ (by rw [m7_run_length, List.length_ofFn]; omega)
  choose o' ho' using outs
  have m6 := M6 L hL gs' o' hv (fun t x hx => ho' t x hx)
  omega

end PEqualNP.Outside.L_meta_1526

theorem PEqualNP.Outside.L_meta_1526 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (13 + (h : ℕ)) :: r) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin 13, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = true) →
    (∀ a ∈ ({0, 1, 3} : Finset (Fin 13)),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (h : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v = a))) = true) →
    41 + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ 13 + (j : ℕ) ∈ (gates.get i).inputs)).card ≤ gates.length := by
  intro L hL gates o j h valid opj unique hj hin computes hco hpt
  exact PEqualNP.Outside.L_meta_1526.m7_reduction L hL gates o j h valid opj unique hj hin computes hco hpt
