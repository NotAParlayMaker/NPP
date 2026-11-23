import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_273

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma run_nil (w : List Bool) : run [] w = w := rfl

lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (step w g) := rfl

lemma run_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    run (gs₁ ++ gs₂) w = run gs₂ (run gs₁ w) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run_nil]
  | cons g gs ih =>
    rw [run_cons, ih, step_length, List.length_cons]
    omega

lemma run_prefix (gs : List Gate) (w : List Bool) : w <+: run gs w := by
  induction gs generalizing w with
  | nil => exact List.prefix_rfl
  | cons g gs ih => exact (List.prefix_append w _).trans (ih (step w g))

lemma getD_of_prefix {l₁ l₂ : List Bool} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₂.getD i false = l₁.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_of_le {l : List Bool} {i : ℕ} (hi : l.length ≤ i) : l.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma getD_append_last (w : List Bool) (v : Bool) : (w ++ [v]).getD w.length false = v := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl w.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma getD_append_lt (w t : List Bool) {i : ℕ} (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma run_getD_split (gs₁ : List Gate) (g : Gate) (gs₂ : List Gate) (w : List Bool) :
    (run (gs₁ ++ g :: gs₂) w).getD (w.length + gs₁.length) false =
      g.op.eval (g.inputs.map fun a =>
        if a < w.length + gs₁.length then (run (gs₁ ++ g :: gs₂) w).getD a false else false) := by
  have hlen : (run gs₁ w).length = w.length + gs₁.length := run_length gs₁ w
  have hrun : run (gs₁ ++ g :: gs₂) w = run gs₂ (step (run gs₁ w) g) := by
    rw [run_append, run_cons]
  have hpre : step (run gs₁ w) g <+: run (gs₁ ++ g :: gs₂) w := by
    rw [hrun]; exact run_prefix _ _
  have hpre₁ : run gs₁ w <+: run (gs₁ ++ g :: gs₂) w :=
    (List.prefix_append _ _).trans hpre
  have h1 : (run (gs₁ ++ g :: gs₂) w).getD (w.length + gs₁.length) false =
      g.op.eval (g.inputs.map fun a => (run gs₁ w).getD a false) := by
    rw [getD_of_prefix hpre (by rw [step_length, hlen]; omega)]
    unfold step
    rw [← hlen, getD_append_last]
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases ha : a < w.length + gs₁.length
  · rw [ite_eq_left ha, getD_of_prefix hpre₁ (by omega)]
  · rw [ite_eq_right ha, getD_of_le (by omega)]

lemma run_getD_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (run gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun a =>
        if a < w.length + k then (run gs w).getD a false else false) := by
  have hsplit : gs.take k ++ gs[k] :: gs.drop (k + 1) = gs := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hk' : (gs.take k).length = k := List.length_take_of_le (le_of_lt hk)
  have := run_getD_split (gs.take k) gs[k] (gs.drop (k + 1)) w
  rw [hsplit, hk'] at this
  exact this

lemma run_getD_input (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false :=
  getD_of_prefix (run_prefix gs w) hi

lemma run_getD_big (gs : List Gate) (w : List Bool) {i : ℕ} (hi : w.length + gs.length ≤ i) :
    (run gs w).getD i false = false :=
  getD_of_le (by rw [run_length]; exact hi)

lemma and_eval_two (p q : Bool) : GateOp.eval GateOp.and [p, q] = (p && q) := by
  simp [GateOp.eval]

lemma or_eval_two (p q : Bool) : GateOp.eval GateOp.or [p, q] = (p || q) := by
  simp [GateOp.eval]

lemma step_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (hl : w.length = w'.length) (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    ∀ i, (step w g).getD i false = true → (step w' g).getD i false = true := by
  intro i hi
  rcases lt_trichotomy i w.length with hlt | heq | hgt
  · unfold step at hi ⊢
    rw [getD_append_lt _ _ hlt] at hi
    rw [getD_append_lt _ _ (hl ▸ hlt)]
    exact h i hi
  · subst heq
    unfold step at hi ⊢
    rw [getD_append_last] at hi
    rw [hl, getD_append_last]
    rcases hg with hand | hor
    · rw [hand] at hi ⊢
      simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] at hi ⊢
      intro a ha
      exact h a (hi a ha)
    · rw [hor] at hi ⊢
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hi ⊢
      obtain ⟨a, ha, hav⟩ := hi
      exact ⟨a, ha, h a hav⟩
  · unfold step at hi
    rw [getD_of_le (by simp; omega)] at hi
    exact absurd hi Bool.false_ne_true

lemma run_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w w' : List Bool) (hl : w.length = w'.length)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    ∀ i, (run gs w).getD i false = true → (run gs w').getD i false = true := by
  induction gs generalizing w w' with
  | nil => intro i; simpa [run_nil] using h i
  | cons g gs ih =>
    rw [run_cons, run_cons]
    refine ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _ ?_ ?_
    · rw [step_length, step_length, hl]
    · exact step_mono g (hgs g List.mem_cons_self) w w' hl h

lemma ofFn_getD (x : Fin 6 → Bool) (i : ℕ) (hi : i < 6) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

abbrev T : Fin 3 → Finset (Fin 6) := ![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}]

lemma T_inj : ∀ i j : Fin 3, T i ⊆ T j → i = j := by decide

lemma T_inter : ∀ i j : Fin 3, i ≠ j → (T i ∩ T j).card ≤ 1 := by decide

lemma T_card : ∀ i : Fin 3, (T i).card = 3 := by decide

def e (p : Fin 6) : Fin 6 → Bool := fun q => decide (q = p)

def e2 (p q : Fin 6) : Fin 6 → Bool := fun r => decide (r = p ∨ r = q)

lemma e_le_e2 (p q : Fin 6) : ∀ r, e p r = true → e2 p q r = true := by
  intro r hr
  simp only [e, decide_eq_true_eq] at hr
  simp [e2, hr]

lemma e_le_e2' (p q : Fin 6) : ∀ r, e q r = true → e2 p q r = true := by
  intro r hr
  simp only [e, decide_eq_true_eq] at hr
  simp [e2, hr]

lemma e2_card (p q : Fin 6) (hpq : p ≠ q) :
    (Finset.univ.filter (fun r : Fin 6 => e2 p q r = true)).card ≤ 2 := by
  have : Finset.univ.filter (fun r : Fin 6 => e2 p q r = true) = {p, q} := by
    ext r; simp [e2]
  rw [this, Finset.card_pair hpq]

lemma ofFn_le (x y : Fin 6 → Bool) (h : ∀ r, x r = true → y r = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases hi6 : i < 6
  · rw [ofFn_getD x i hi6] at hi
    rw [ofFn_getD y i hi6]
    exact h _ hi
  · rw [getD_of_le (by simp; omega)] at hi
    exact absurd hi Bool.false_ne_true

section main

variable (gs : List Gate)

-- the value of wire `j` on the input `x`
def wire (j : ℕ) (x : Fin 6 → Bool) : Bool := (run gs (List.ofFn x)).getD j false

-- the single points of wire `j`
def S (j : ℕ) : Finset (Fin 6) := Finset.univ.filter fun p => wire gs j (e p) = true

lemma wire_input {j : ℕ} (hj : j < 6) (x : Fin 6 → Bool) : wire gs j x = x ⟨j, hj⟩ := by
  unfold wire
  rw [run_getD_input gs _ (by simp [hj]), ofFn_getD]

lemma wire_big {j : ℕ} (hj : 6 + gs.length ≤ j) (x : Fin 6 → Bool) : wire gs j x = false := by
  unfold wire
  exact run_getD_big gs _ (by simpa using hj)

lemma wire_gate {j : ℕ} (hj₁ : 6 ≤ j) (hj₂ : j < 6 + gs.length) (x : Fin 6 → Bool) :
    wire gs j x = (gs[j - 6]'(by omega)).op.eval ((gs[j - 6]'(by omega)).inputs.map fun a =>
      if a < j then wire gs a x else false) := by
  unfold wire
  have := run_getD_gate gs (List.ofFn x) (j - 6) (by omega)
  have h6 : (List.ofFn x).length + (j - 6) = j := by simp; omega
  rw [h6] at this
  exact this

lemma wire_mono (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (j : ℕ)
    (x y : Fin 6 → Bool) (h : ∀ r, x r = true → y r = true) :
    wire gs j x = true → wire gs j y = true :=
  run_mono gs hgs _ _ (by simp) (ofFn_le x y h) j

lemma S_input {j : ℕ} (hj : j < 6) : (S gs j).card = 1 := by
  have : S gs j = {⟨j, hj⟩} := by
    ext p
    simp [S, wire_input gs hj, e, eq_comm]
  rw [this, Finset.card_singleton]

lemma S_big {j : ℕ} (hj : 6 + gs.length ≤ j) : S gs j = ∅ := by
  ext p
  simp [S, wire_big gs hj]

-- a wire whose single points lie in `T i` with at least two of them is a gate wire
lemma gate_of_S {j : ℕ} {i : Fin 3} (hsub : S gs j ⊆ T i) (hcard : 2 ≤ (S gs j).card) :
    6 ≤ j ∧ j < 6 + gs.length := by
  constructor
  · by_contra h
    have := S_input gs (show j < 6 by omega)
    omega
  · by_contra h
    rw [S_big gs (by omega), Finset.card_empty] at hcard
    omega

-- the read value of an input index `a` of the gate at wire `j`
def rd (j a : ℕ) (x : Fin 6 → Bool) : Bool := if a < j then wire gs a x else false

lemma rd_mono (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (j a : ℕ)
    (x y : Fin 6 → Bool) (h : ∀ r, x r = true → y r = true) :
    rd gs j a x = true → rd gs j a y = true := by
  unfold rd
  split_ifs
  · exact wire_mono gs hgs a x y h
  · exact id

-- from a side whose single points lie in `T i` with at least two of them, a good gate
lemma good_of_side {j a : ℕ} {i : Fin 3}
    (hsub : ∀ p, rd gs j a (e p) = true → p ∈ T i)
    (hcard : 2 ≤ (Finset.univ.filter fun p => rd gs j a (e p) = true).card) :
    a < j ∧ 6 ≤ a ∧ a < 6 + gs.length ∧ S gs a ⊆ T i ∧ 2 ≤ (S gs a).card := by
  have haj : a < j := by
    by_contra h
    have : (Finset.univ.filter fun p => rd gs j a (e p) = true) = ∅ := by
      ext p; simp [rd, h]
    rw [this, Finset.card_empty] at hcard
    omega
  have hS : S gs a = Finset.univ.filter fun p => rd gs j a (e p) = true := by
    ext p; simp [S, rd, haj]
  have hsub' : S gs a ⊆ T i := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    exact hsub p hp.2
  have hcard' : 2 ≤ (S gs a).card := by rw [hS]; exact hcard
  obtain ⟨h1, h2⟩ := gate_of_S gs hsub' hcard'
  exact ⟨haj, h1, h2, hsub', hcard'⟩

end main

theorem main : ¬ ∃ (C : Circuit) (o : Fin 3 → ℕ), C.size ≤ 5 ∧
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    ∀ i : Fin 3, (∀ p : Fin 6, (C.wires (List.ofFn (fun q : Fin 6 => decide (q = p)))).getD (o i) false = true ↔
        p ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i) ∧
      ∀ x : Fin 6 → Bool, (Finset.univ.filter (fun q : Fin 6 => x q = true)).card ≤ 2 →
        (∀ q ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i, x q = false) →
        (C.wires (List.ofFn x)).getD (o i) false = false := by
  rintro ⟨C, o, hsize, hgates, hio⟩
  set gs := C.gates with hgs_def
  have hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => (hgates g hg).1
  have hwire : ∀ j x, (C.wires (List.ofFn x)).getD j false = wire gs j x := fun _ _ => rfl
  -- the single points of output `i` are exactly `T i`
  have hS : ∀ i, S gs (o i) = T i := by
    intro i
    ext p
    have := (hio i).1 p
    rw [hwire] at this
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact this
  -- output `i` is false on weight-two inputs missing `T i`
  have hB : ∀ i (p q : Fin 6), p ≠ q → p ∉ T i → q ∉ T i → wire gs (o i) (e2 p q) = false := by
    intro i p q hpq hp hq
    rw [← hwire]
    refine (hio i).2 (e2 p q) (e2_card p q hpq) ?_
    intro r hr
    simp only [e2, decide_eq_false_iff_not, not_or]
    constructor
    · rintro rfl; exact hp hr
    · rintro rfl; exact hq hr
  -- each output wire is a gate wire
  have hout : ∀ i, 6 ≤ o i ∧ o i < 6 + gs.length := by
    intro i
    refine gate_of_S gs (i := i) (by rw [hS]) ?_
    rw [hS, T_card]; omega
  -- each output gate reads a good gate below it
  have hgood : ∀ i, ∃ c, c < o i ∧ 6 ≤ c ∧ c < 6 + gs.length ∧ S gs c ⊆ T i ∧ 2 ≤ (S gs c).card := by
    intro i
    obtain ⟨h1, h2⟩ := hout i
    have hg := hgates (gs[o i - 6]'(by omega)) (List.getElem_mem _)
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hg.2
    have hval : ∀ x, wire gs (o i) x = (gs[o i - 6]'(by omega)).op.eval [rd gs (o i) a x, rd gs (o i) b x] := by
      intro x
      rw [wire_gate gs h1 h2 x, hab]
      rfl
    rcases hg.1 with hand | hor
    · have hval' : ∀ x, wire gs (o i) x = (rd gs (o i) a x && rd gs (o i) b x) := by
        intro x; rw [hval x, hand, and_eval_two]
      have hpts : ∀ p, p ∈ T i ↔ (rd gs (o i) a (e p) = true ∧ rd gs (o i) b (e p) = true) := by
        intro p
        rw [← hS i]
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hval', Bool.and_eq_true]
      -- one side has its single points inside `T i`
      have hside : (∀ p, rd gs (o i) a (e p) = true → p ∈ T i) ∨
          (∀ p, rd gs (o i) b (e p) = true → p ∈ T i) := by
        by_contra hcon
        push_neg at hcon
        obtain ⟨⟨p, hpa, hp⟩, ⟨q, hqb, hq⟩⟩ := hcon
        have hpq : p ≠ q := by
          rintro rfl
          exact hp ((hpts p).mpr ⟨hpa, hqb⟩)
        have hfalse := hB i p q hpq hp hq
        rw [hval'] at hfalse
        have ha2 := rd_mono gs hmono (o i) a (e p) (e2 p q) (e_le_e2 p q) hpa
        have hb2 := rd_mono gs hmono (o i) b (e q) (e2 p q) (e_le_e2' p q) hqb
        rw [ha2, hb2] at hfalse
        simp at hfalse
      rcases hside with hsa | hsb
      · have hcard : 2 ≤ (Finset.univ.filter fun p => rd gs (o i) a (e p) = true).card := by
          have : T i ⊆ Finset.univ.filter fun p => rd gs (o i) a (e p) = true := by
            intro p hp
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ((hpts p).mp hp).1
          have := Finset.card_le_card this
          rw [T_card] at this
          omega
        obtain ⟨h3, h4, h5, h6, h7⟩ := good_of_side gs hsa hcard
        exact ⟨a, h3, h4, h5, h6, h7⟩
      · have hcard : 2 ≤ (Finset.univ.filter fun p => rd gs (o i) b (e p) = true).card := by
          have : T i ⊆ Finset.univ.filter fun p => rd gs (o i) b (e p) = true := by
            intro p hp
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ((hpts p).mp hp).2
          have := Finset.card_le_card this
          rw [T_card] at this
          omega
        obtain ⟨h3, h4, h5, h6, h7⟩ := good_of_side gs hsb hcard
        exact ⟨b, h3, h4, h5, h6, h7⟩
    · have hval' : ∀ x, wire gs (o i) x = (rd gs (o i) a x || rd gs (o i) b x) := by
        intro x; rw [hval x, hor, or_eval_two]
      have hpts : ∀ p, p ∈ T i ↔ (rd gs (o i) a (e p) = true ∨ rd gs (o i) b (e p) = true) := by
        intro p
        rw [← hS i]
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hval', Bool.or_eq_true]
      have hsa : ∀ p, rd gs (o i) a (e p) = true → p ∈ T i := fun p hp => (hpts p).mpr (Or.inl hp)
      have hsb : ∀ p, rd gs (o i) b (e p) = true → p ∈ T i := fun p hp => (hpts p).mpr (Or.inr hp)
      have hunion : T i ⊆ (Finset.univ.filter fun p => rd gs (o i) a (e p) = true) ∪
          (Finset.univ.filter fun p => rd gs (o i) b (e p) = true) := by
        intro p hp
        rcases (hpts p).mp hp with h | h
        · exact Finset.mem_union_left _ (by simp [h])
        · exact Finset.mem_union_right _ (by simp [h])
      have hc := Finset.card_le_card hunion
      have hc2 := Finset.card_union_le (Finset.univ.filter fun p => rd gs (o i) a (e p) = true)
        (Finset.univ.filter fun p => rd gs (o i) b (e p) = true)
      rw [T_card] at hc
      by_cases hca : 2 ≤ (Finset.univ.filter fun p => rd gs (o i) a (e p) = true).card
      · obtain ⟨h3, h4, h5, h6, h7⟩ := good_of_side gs hsa hca
        exact ⟨a, h3, h4, h5, h6, h7⟩
      · have hcb : 2 ≤ (Finset.univ.filter fun p => rd gs (o i) b (e p) = true).card := by omega
        obtain ⟨h3, h4, h5, h6, h7⟩ := good_of_side gs hsb hcb
        exact ⟨b, h3, h4, h5, h6, h7⟩
  choose c hc using hgood
  -- six distinct gate wires
  let f : Fin 3 ⊕ Fin 3 → ℕ := fun u => Sum.elim o c u
  have hinj : Function.Injective f := by
    intro u v huv
    rcases u with i | i <;> rcases v with j | j
    · simp only [f, Sum.elim_inl] at huv
      have : T i = T j := by rw [← hS i, ← hS j, huv]
      rw [T_inj i j (this ▸ Finset.Subset.refl _)]
    · simp only [f, Sum.elim_inl, Sum.elim_inr] at huv
      have hsub : T i ⊆ T j := by
        rw [← hS i, huv]; exact (hc j).2.2.2.1
      have hij := T_inj i j hsub
      subst hij
      have := (hc i).1
      omega
    · simp only [f, Sum.elim_inl, Sum.elim_inr] at huv
      have hsub : T j ⊆ T i := by
        rw [← hS j, ← huv]; exact (hc i).2.2.2.1
      have hij := T_inj j i hsub
      subst hij
      have := (hc j).1
      omega
    · simp only [f, Sum.elim_inr] at huv
      by_contra hne
      have hne' : i ≠ j := fun h => hne (h ▸ rfl)
      have h1 : S gs (c i) ⊆ T i ∩ T j := by
        intro p hp
        refine Finset.mem_inter.mpr ⟨(hc i).2.2.2.1 hp, ?_⟩
        rw [huv] at hp
        exact (hc j).2.2.2.1 hp
      have h2 := Finset.card_le_card h1
      have h3 := T_inter i j hne'
      have h4 := (hc i).2.2.2.2
      omega
  have himg : Finset.univ.image f ⊆ Finset.Ico 6 (6 + gs.length) := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨u, _, rfl⟩ := hw
    rcases u with i | i
    · simp only [f, Sum.elim_inl, Finset.mem_Ico]; exact hout i
    · simp only [f, Sum.elim_inr, Finset.mem_Ico]; exact ⟨(hc i).2.1, (hc i).2.2.1⟩
  have hcard := Finset.card_le_card himg
  rw [Finset.card_image_of_injective _ hinj, Nat.card_Ico] at hcard
  simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at hcard
  have : gs.length ≤ 5 := hsize
  omega

end PEqualNP.Outside.L_meta_273

theorem PEqualNP.Outside.L_meta_273 : ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 3 → ℕ), C.size ≤ 5 ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ ∀ i : Fin 3, (∀ p : Fin 6, (C.wires (List.ofFn (fun q : Fin 6 => decide (q = p)))).getD (o i) false = true ↔ p ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i) ∧ ∀ x : Fin 6 → Bool, (Finset.univ.filter (fun q : Fin 6 => x q = true)).card ≤ 2 → (∀ q ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false :=
  PEqualNP.Outside.L_meta_273.main
