import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1373

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem on1_wires_output (gs : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = Circuit.wires ⟨gs, o'⟩ x := rfl

theorem on1_wires_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.wires ⟨gs, o⟩ x = wiresFrom gs x := rfl

theorem on1_length_wires (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  length_wiresFrom C.gates x

theorem on1_getD_wires_of_ge (C : Circuit) (x : List Bool) (i : ℕ)
    (h : x.length + C.gates.length ≤ i) : (C.wires x).getD i false = false := by
  rw [List.getD_eq_default]; rw [on1_length_wires]; exact h

theorem on1_getD_wiresFrom_of_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (wiresFrom gs w).getD i false = false := by
  rw [List.getD_eq_default]; rw [length_wiresFrom]; exact h

theorem on1_wires_append (l1 l2 : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨l1 ++ l2, o⟩ x = wiresFrom l2 (Circuit.wires ⟨l1, o'⟩ x) :=
  wiresFrom_append l1 l2 x

theorem on1_wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w
      = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem on1_wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

theorem on1_getD_wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  show (wiresFrom C.gates (List.ofFn x)).getD i false = x ⟨i, hi⟩
  rw [getD_wiresFrom _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem on1_getD_append_left (w t : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false := List.getD_append _ _ _ _ h

def on1_renum (r : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map r }

theorem on1_renum_sim_all (r : ℕ → ℕ) (gs : List Gate) : ∀ (v w : List Bool),
    (∀ i, v.getD (r i) false = w.getD i false) →
    (∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i) →
    (∀ k < gs.length, r (w.length + k) = v.length + k) →
    (∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) →
    ∀ i, (wiresFrom (gs.map (on1_renum r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  induction gs with
  | nil => intro v w h1 _ _ _ i; exact h1 i
  | cons g gs ih =>
    intro v w h1 h2 h3 h4
    simp only [List.length_cons] at h2 h3 h4
    have hval : (on1_renum r g).op.eval
          ((on1_renum r g).inputs.map fun i => v.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [on1_renum, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h1 j
    have hr0 : r w.length = v.length := by simpa using h3 0 (by omega)
    have hne : ∀ i, i ≠ w.length → r i ≠ v.length := by
      intro i hi
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h <;> omega
      · by_cases hk : i < w.length + (gs.length + 1)
        · have := h3 (i - w.length) (by omega)
          rw [show w.length + (i - w.length) = i by omega] at this
          omega
        · have := h4 i (by omega); omega
    rw [List.map_cons, on1_wiresFrom_cons, on1_wiresFrom_cons, hval]
    apply ih
    · intro i
      by_cases hi : i = w.length
      · subst hi
        rw [hr0, getD_snoc_eq, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ (hne i hi), getD_snoc_ne _ _ _ _ hi]
        exact h1 i
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h
        · left; omega
        · right; omega
      · left; have : i = w.length := by omega
        subst this; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton]
      have := h3 (k + 1) (by omega)
      rw [show w.length + 1 + k = w.length + (k + 1) by omega, this]; omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have := h4 i (by omega); omega

theorem on1_renum_sim (r : ℕ → ℕ) (gs : List Gate) (v w : List Bool)
    (h1 : ∀ i < w.length, v.getD (r i) false = w.getD i false)
    (h2 : ∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i)
    (h3 : ∀ k < gs.length, r (w.length + k) = v.length + k)
    (h4 : ∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) (i : ℕ) :
    (wiresFrom (gs.map (on1_renum r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  apply on1_renum_sim_all r gs v w _ h2 h3 h4
  intro j
  by_cases hj : j < w.length
  · exact h1 j hj
  · have hge : v.length ≤ r j := by
      by_cases hk : j < w.length + gs.length
      · have := h3 (j - w.length) (by omega)
        rw [show w.length + (j - w.length) = j by omega] at this
        omega
      · have := h4 j (by omega); omega
    rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]

theorem on1_getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

def on1_Above (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i, v.getD i false = true → v'.getD i false = true

theorem on1_above_snoc {v v' : List Bool} {a a' : Bool} (h : on1_Above v v')
    (ha : a = true → a' = true) : on1_Above (v ++ [a]) (v' ++ [a']) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i = v.length
  · subst hiv
    rw [getD_snoc_eq] at hi
    rw [h.1, getD_snoc_eq]; exact ha hi
  · rw [getD_snoc_ne _ _ _ _ hiv] at hi
    rw [getD_snoc_ne _ _ _ _ (by rw [← h.1]; exact hiv)]
    exact h.2 i hi

theorem on1_above_wiresFrom (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ v v' : List Bool, on1_Above v v' → on1_Above (wiresFrom gs v) (wiresFrom gs v') := by
  induction gs with
  | nil => intro v v' h; exact h
  | cons g gs ih =>
    intro v v' h
    rw [on1_wiresFrom_cons, on1_wiresFrom_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    apply on1_above_snoc h
    rcases hgs g (by simp) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall b hb
      obtain ⟨j, hj, rfl⟩ := hb
      exact h.2 j (hall _ ⟨j, hj, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
      exact ⟨_, ⟨j, hj, rfl⟩, h.2 j hb⟩

theorem on1_piece_h : ∀ (n : ℕ) (pre : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
    (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = true →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn y)).getD i false).headD false) = true := by
  intro n pre ins hpre x y hxy
  have hab : on1_Above (wiresFrom pre (List.ofFn x)) (wiresFrom pre (List.ofFn y)) := by
    apply on1_above_wiresFrom pre (fun g hg => (hpre g hg).1)
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hin : i < n
    · rw [on1_getD_ofFn _ _ hin] at hi ⊢; exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp)
  cases ins with
  | nil => simp
  | cons j _ =>
    simp only [List.map_cons, List.headD_cons]
    exact hab.2 j

theorem on1_wires_slot (pre post : List Gate) (g g' : Gate) (o o' : ℕ) (x : List Bool)
    (h : g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)
      = g'.op.eval (g'.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)) :
    Circuit.wires ⟨pre ++ g :: post, o⟩ x = Circuit.wires ⟨pre ++ g' :: post, o'⟩ x := by
  rw [on1_wires_append _ _ o 0, on1_wires_append _ _ o' 0, on1_wiresFrom_cons,
    on1_wiresFrom_cons, h]

theorem on1_piece_d : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.all_nil]
  rw [h]; rfl

theorem on1_piece_u_cheap : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.any_nil]
  rw [h]; rfl

theorem on1_piece_u : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ), ∃ r : ℕ → ℕ,
    ∀ (o : ℕ) (x : Fin n → Bool),
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = true →
      PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨pre ++ post.map (fun g => ({ op := g.op, inputs := g.inputs.map r } :
            PEqualNP.CircuitLowerBounds.Gate)), r o⟩ (List.ofFn x)
        = PEqualNP.CircuitLowerBounds.Circuit.eval
          ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
            PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins
  set p := pre.length
  refine ⟨fun i => if i < n + p then i else if i = n + p then n + p + post.length + 1
    else i - 1, ?_⟩
  intro o x h
  set r : ℕ → ℕ := fun i => if i < n + p then i else if i = n + p then n + p + post.length + 1
    else i - 1 with hr
  set v := wiresFrom pre (List.ofFn x) with hv
  have hvl : v.length = n + p := by rw [hv, length_wiresFrom]; simp [p]
  set nv := GateOp.not.eval (ins.map fun i => v.getD i false) with hnv
  have hnv0 : nv = false := by
    rw [hnv]; simp only [GateOp.eval]; rw [show v = Circuit.wires ⟨pre, 0⟩ (List.ofFn x) from rfl,
      h]; rfl
  unfold Circuit.eval
  rw [List.append_cons, on1_wires_append _ _ _ 0, on1_wires_append _ _ _ 0,
    on1_wires_append _ _ _ 0]
  show (wiresFrom (post.map (on1_renum r)) v).getD (r o) false
    = (wiresFrom post (v ++ [nv])).getD o false
  apply on1_renum_sim
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi
    by_cases hlt : i < n + p
    · simp only [hr, hlt, ite_true]
      rw [on1_getD_append_left _ _ _ (by omega)]
    · have hi' : i = n + p := by omega
      subst hi'
      simp only [hr, lt_irrefl, ite_false, ite_true]
      rw [List.getD_eq_default _ _ (by omega), ← hvl, getD_snoc_eq, hnv0]
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    by_cases hlt : i < n + p
    · left; simp [hr, hlt]
    · right; have hi' : i = n + p := by omega
      subst hi'; simp [hr]
  · intro k _
    simp only [List.length_append, List.length_singleton, hvl, hr]
    split_ifs <;> omega
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    simp only [hr]
    split_ifs <;> omega

theorem on1_split : ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ g ∈ post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) := by
  intro gates hops huniq
  by_cases hex : ∃ g ∈ gates, g.op = GateOp.not
  · right
    obtain ⟨g, hg, hop⟩ := hex
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hg
    -- the NOT gate sits at index `s.length`
    have hslot : ((s ++ g :: t).get ⟨s.length, by simp⟩).op = GateOp.not := by
      simp [hop]
    have nf : ∀ g' ∈ s ++ g :: t, g'.op ≠ GateOp.not → (g'.op = GateOp.and ∨
        g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
      intro g' hg' hne
      obtain ⟨h1 | h1 | h1, h2⟩ := hops g' hg'
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 hne
    refine ⟨s, t, g.inputs, ?_, ?_, ?_⟩
    · cases g with
      | mk op ins => simp only at hop; subst hop; rfl
    · intro g' hg'
      apply nf g' (by simp [hg'])
      intro hn
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
      have := huniq ⟨i, by simp; omega⟩ ⟨s.length, by simp⟩
        (by simp [List.getElem_append_left hi, hn]) hslot
      simp only [Fin.mk.injEq] at this; omega
    · intro g' hg'
      apply nf g' (by simp [hg'])
      intro hn
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
      have := huniq ⟨s.length + 1 + i, by simp; omega⟩ ⟨s.length, by simp⟩
        (by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_right (by omega)]
          simp only [show s.length + 1 + i - s.length = i + 1 by omega,
            List.getElem_cons_succ]
          exact hn) hslot
      simp only [Fin.mk.injEq] at this; omega
  · left
    intro g hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops g hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨g, hg, h1⟩ hex



def dmod (r : ℕ → ℕ) (k : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.or => if k ∈ g.inputs then { op := GateOp.and, inputs := [] }
      else { op := GateOp.or, inputs := g.inputs.map r }
  | op => { op := op, inputs := (g.inputs.filter (fun i => decide (i ≠ k))).map r }

theorem dmod_val (r : ℕ → ℕ) (k : ℕ) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (v w : List Bool) (h1 : ∀ i, i ≠ k → v.getD (r i) false = w.getD i false)
    (hk : w.getD k false = true) :
    (dmod r k g).op.eval ((dmod r k g).inputs.map fun i => v.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases hg with hop | hop
  · simp only [dmod, hop]
    simp only [GateOp.eval, List.map_map]
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_map, List.mem_filter, id, Function.comp]
    constructor
    · rintro hall b ⟨i, hi, rfl⟩
      by_cases hik : i = k
      · subst hik; exact hk
      · have := hall _ ⟨i, ⟨hi, by simp [hik]⟩, rfl⟩
        rw [h1 i hik] at this; exact this
    · rintro hall b ⟨i, ⟨hi, hik⟩, rfl⟩
      have hik' : i ≠ k := by simpa using hik
      rw [h1 i hik']; exact hall _ ⟨i, hi, rfl⟩
  · by_cases hk' : k ∈ g.inputs
    · simp only [dmod, hop, hk', ite_true]
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      symm; rw [List.any_eq_true]; exact ⟨_, List.mem_map.2 ⟨k, hk', rfl⟩, hk⟩
    · simp only [dmod, hop, hk', ite_false]
      simp only [GateOp.eval, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      have : i ≠ k := fun h => hk' (h ▸ hi)
      simp only [Function.comp]
      exact h1 i this

theorem dmod_ok (r : ℕ → ℕ) (k : ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((dmod r k g).op = GateOp.and ∨ (dmod r k g).op = GateOp.or) ∧
      (dmod r k g).inputs.length ≤ 2 := by
  obtain ⟨hop | hop, hl⟩ := hg
  · simp only [dmod, hop]
    refine ⟨by simp, ?_⟩
    simp only [List.length_map]
    exact le_trans (List.length_filter_le _ _) hl
  · by_cases hk : k ∈ g.inputs
    · simp [dmod, hop, hk]
    · simp only [dmod, hop, hk, ite_false]
      exact ⟨by simp, by simpa using hl⟩

theorem dsim_all (r : ℕ → ℕ) (k : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) : ∀ (v w : List Bool),
    (∀ i, i ≠ k → v.getD (r i) false = w.getD i false) →
    k < w.length → w.getD k false = true →
    (∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i) →
    (∀ j < gs.length, r (w.length + j) = v.length + j) →
    (∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) →
    ∀ i, i ≠ k → (wiresFrom (gs.map (dmod r k)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  induction gs with
  | nil => intro v w h1 _ _ _ _ _ i hi; exact h1 i hi
  | cons g gs ih =>
    intro v w h1 hkl hk h2 h3 h4
    simp only [List.length_cons] at h2 h3 h4
    have hval := dmod_val r k g (hgs g (by simp)) v w h1 hk
    have hr0 : r w.length = v.length := by simpa using h3 0 (by omega)
    have hne : ∀ i, i ≠ w.length → r i ≠ v.length := by
      intro i hi
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h <;> omega
      · by_cases hk2 : i < w.length + (gs.length + 1)
        · have := h3 (i - w.length) (by omega)
          rw [show w.length + (i - w.length) = i by omega] at this
          omega
        · have := h4 i (by omega); omega
    rw [List.map_cons, on1_wiresFrom_cons, on1_wiresFrom_cons, hval]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    · intro i hik
      by_cases hi : i = w.length
      · subst hi
        rw [hr0, getD_snoc_eq, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ (hne i hi), getD_snoc_ne _ _ _ _ hi]
        exact h1 i hik
    · simp only [List.length_append, List.length_singleton]; omega
    · rw [on1_getD_append_left _ _ _ hkl]; exact hk
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h
        · left; omega
        · right; omega
      · left; have : i = w.length := by omega
        subst this; omega
    · intro j hj
      simp only [List.length_append, List.length_singleton]
      have := h3 (j + 1) (by omega)
      rw [show w.length + 1 + j = w.length + (j + 1) by omega, this]; omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have := h4 i (by omega); omega

theorem piece_dd : ∀ (n : ℕ) (pre post : List Gate) (ins : List ℕ),
    (∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∃ r : ℕ → ℕ, ∀ (o : ℕ) (x : Fin n → Bool), o ≠ n + pre.length →
      ((ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false)
        = false →
      Circuit.eval ⟨pre ++ post.map (dmod r (n + pre.length)), r o⟩ (List.ofFn x)
        = Circuit.eval ⟨pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post, o⟩
            (List.ofFn x) := by
  intro n pre post ins hpost
  set p := pre.length
  refine ⟨fun i => if i < n + p then i else if i = n + p then n + p + post.length + 1
    else i - 1, ?_⟩
  intro o x ho h
  set r : ℕ → ℕ := fun i => if i < n + p then i else if i = n + p then n + p + post.length + 1
    else i - 1 with hr
  set v := wiresFrom pre (List.ofFn x) with hv
  have hvl : v.length = n + p := by rw [hv, length_wiresFrom]; simp [p]
  set nv := GateOp.not.eval (ins.map fun i => v.getD i false) with hnv
  have hnv1 : nv = true := by
    rw [hnv]; simp only [GateOp.eval]
    rw [show v = Circuit.wires ⟨pre, 0⟩ (List.ofFn x) from rfl, h]; rfl
  unfold Circuit.eval
  rw [List.append_cons, on1_wires_append _ _ _ 0, on1_wires_append _ _ _ 0,
    on1_wires_append _ _ _ 0]
  show (wiresFrom (post.map (dmod r (n + p))) v).getD (r o) false
    = (wiresFrom post (v ++ [nv])).getD o false
  apply dsim_all r (n + p) post hpost v (v ++ [nv])
  · intro i hi
    by_cases hlt : i < n + p
    · simp only [hr, hlt, ite_true]
      rw [on1_getD_append_left _ _ _ (by omega)]
    · have hgt : n + p < i := by omega
      simp only [hr, hlt, ite_false, show i ≠ n + p by omega]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
  · simp; omega
  · rw [← hvl, getD_snoc_eq, hnv1]
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    by_cases hlt : i < n + p
    · left; simp [hr, hlt]
    · right; have hi' : i = n + p := by omega
      subst hi'; simp [hr]
  · intro j _
    simp only [List.length_append, List.length_singleton, hvl, hr]
    split_ifs <;> omega
  · intro i hi
    simp only [List.length_append, List.length_singleton, hvl] at hi ⊢
    simp only [hr]
    split_ifs <;> omega
  · exact ho

theorem eval_slot (n : ℕ) (pre post : List Gate) (g : Gate) (x : Fin n → Bool) :
    Circuit.eval ⟨pre ++ g :: post, n + pre.length⟩ (List.ofFn x)
      = g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false) := by
  unfold Circuit.eval
  rw [on1_wires_append _ _ _ 0, on1_wiresFrom_cons]
  have hl : (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).length = n + pre.length := by
    rw [on1_length_wires]; simp
  rw [getD_wiresFrom _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]

def H270 : Prop :=
  ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size

def H669 : Prop :=
  ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))

theorem wires_getD_eq_eval (G : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires ⟨G, 0⟩ x).getD o false = Circuit.eval ⟨G, o⟩ x := rfl

theorem low_bound (h270 : H270) (h669 : H669) (N q k0 : ℕ) (S : Fin N → Finset (Fin N))
    (hq : 1 ≤ q) (hcard : ∀ i, (S i).card = q + 1)
    (hint : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (G : List Gate) (out : Fin N → ℕ)
    (hG : ∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hk0 : 1 ≤ k0)
    (hf : ∀ (w : Fin N) (x : Fin N → Bool),
      (Finset.univ.filter (fun p : Fin N => x p = true)).card ≤ k0 →
      Circuit.eval ⟨G, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) :
    N * min k0 q ≤ G.length := by
  obtain ⟨G2, r2, hG2, hlen, hev⟩ := h669 N G ∅ ∅ hG
  have hsimp : ∀ x : Fin N → Bool,
      (fun i => if i ∈ (∅ : Finset (Fin N)) then true else if i ∈ (∅ : Finset (Fin N)) then false
        else x i) = x := by
    intro x; funext i; simp
  have hw0 : (Finset.univ.filter (fun p : Fin N => (fun _ : Fin N => false) p = true)).card = 0 := by
    simp
  have hw1 : ∀ p0 : Fin N,
      (Finset.univ.filter (fun p : Fin N => (fun q : Fin N => decide (q = p0)) p = true)).card = 1 := by
    intro p0; simp [Finset.filter_eq']
  have key : ∀ (w : Fin N) (x : Fin N → Bool),
      (Finset.univ.filter (fun p : Fin N => x p = true)).card ≤ k0 →
      Circuit.eval ⟨G2, r2 (out w)⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true) := by
    intro w x hx
    have hne : ∃ x y : Fin N → Bool, Circuit.eval ⟨G, out w⟩ (List.ofFn (fun i => if i ∈ (∅ : Finset (Fin N)) then true else if i ∈ (∅ : Finset (Fin N)) then false else x i)) ≠ Circuit.eval ⟨G, out w⟩ (List.ofFn (fun i => if i ∈ (∅ : Finset (Fin N)) then true else if i ∈ (∅ : Finset (Fin N)) then false else y i)) := by
      have hne0 : (S w).Nonempty := by
        rw [← Finset.card_pos, hcard]; omega
      obtain ⟨p0, hp0⟩ := hne0
      refine ⟨fun _ => false, fun q => decide (q = p0), ?_⟩
      rw [hsimp, hsimp, hf w _ (by rw [hw0]; omega), hf w _ (by rw [hw1]; omega)]
      simp only [ne_eq, decide_eq_decide]
      simp only [Bool.false_eq_true, and_false, exists_false, decide_eq_true_eq, false_iff,
        not_exists, not_and, not_forall, not_not]
      exact ⟨p0, hp0, rfl⟩
    rw [hev (out w) hne x, hsimp]
    exact hf w x hx
  have hmain := h270 N N k0 S ⟨G2, 0⟩ (fun w => r2 (out w)) (fun _ => min k0 q) hint
    (fun i => by rw [hcard]; omega) hG2
    (by
      intro i p
      rw [wires_getD_eq_eval, key i _ (by rw [hw1]; omega)]
      simp)
    (by
      intro i x hx hz
      rw [wires_getD_eq_eval, key i x hx]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro v hv hxv
      rw [hz v hv] at hxv; exact absurd hxv (by simp))
    (fun _ => min_le_left _ _)
    (fun i => by rw [hcard]; have := min_le_right k0 q; omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Circuit.size] at hmain
  omega

theorem mono_bound (h270 : H270) (h669 : H669) (N q : ℕ) (S : Fin N → Finset (Fin N))
    (hq : 1 ≤ q) (hcard : ∀ i, (S i).card = q + 1)
    (hint : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (G : List Gate) (out : Fin N → ℕ)
    (hG : ∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T : Finset (Fin N))
    (hf : ∀ (w : Fin N) (x : Fin N → Bool), (∀ p ∈ T, x p = true) →
      Circuit.eval ⟨G, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) :
    q * (Finset.univ.filter (fun w => Disjoint (S w) T)).card ≤ G.length := by
  obtain ⟨G2, r2, hG2, hlen, hev⟩ := h669 N G T ∅ hG
  set D := Finset.univ.filter (fun w => Disjoint (S w) T) with hD
  set e : Fin D.card → Fin N := fun i => (D.equivFin.symm i).1 with he
  have heD : ∀ i, Disjoint (S (e i)) T := by
    intro i
    exact (Finset.mem_filter.1 (D.equivFin.symm i).2).2
  have heinj : Function.Injective e := by
    intro i j hij
    exact D.equivFin.symm.injective (Subtype.ext hij)
  have hres : ∀ (i : Fin D.card) (x : Fin N → Bool),
      Circuit.eval ⟨G, out (e i)⟩ (List.ofFn (fun j => if j ∈ T then true else
        if j ∈ (∅ : Finset (Fin N)) then false else x j)) = decide (∃ v ∈ S (e i), x v = true) := by
    intro i x
    rw [hf (e i) _ (by intro p hp; simp [hp])]
    congr 1
    apply propext
    constructor
    · rintro ⟨v, hv, hxv⟩
      have hvT : v ∉ T := Finset.disjoint_left.1 (heD i) hv
      refine ⟨v, hv, ?_⟩
      simpa [hvT] using hxv
    · rintro ⟨v, hv, hxv⟩
      have hvT : v ∉ T := Finset.disjoint_left.1 (heD i) hv
      exact ⟨v, hv, by simp [hvT, hxv]⟩
  have key : ∀ (i : Fin D.card) (x : Fin N → Bool),
      Circuit.eval ⟨G2, r2 (out (e i))⟩ (List.ofFn x) = decide (∃ v ∈ S (e i), x v = true) := by
    intro i x
    have hne0 : (S (e i)).Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    obtain ⟨p0, hp0⟩ := hne0
    have hne : ∃ x y : Fin N → Bool, Circuit.eval ⟨G, out (e i)⟩ (List.ofFn (fun j => if j ∈ T then true else if j ∈ (∅ : Finset (Fin N)) then false else x j)) ≠ Circuit.eval ⟨G, out (e i)⟩ (List.ofFn (fun j => if j ∈ T then true else if j ∈ (∅ : Finset (Fin N)) then false else y j)) := by
      refine ⟨fun _ => false, fun q => decide (q = p0), ?_⟩
      rw [hres, hres]
      simp only [ne_eq, decide_eq_decide]
      simp only [Bool.false_eq_true, and_false, exists_false, decide_eq_true_eq, false_iff,
        not_exists, not_and, not_forall, not_not]
      exact ⟨p0, hp0, rfl⟩
    rw [hev (out (e i)) hne x, hres]
  have hmain := h270 N D.card q (fun i => S (e i)) ⟨G2, 0⟩ (fun i => r2 (out (e i)))
    (fun _ => q) (fun i j hij => hint (e i) (e j) (fun h => hij (heinj h)))
    (fun i => by rw [hcard]; omega) hG2
    (by
      intro i p
      rw [wires_getD_eq_eval, key i]
      simp)
    (by
      intro i x _ hz
      rw [wires_getD_eq_eval, key i x]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro v hv hxv
      rw [hz v hv] at hxv; exact absurd hxv (by simp))
    (fun _ => le_refl _)
    (fun i => by rw [hcard])
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Circuit.size] at hmain
  rw [mul_comm]
  omega

theorem pencil (q : ℕ) (S : Fin (q^2+q+1) → Finset (Fin (q^2+q+1)))
    (hcard : ∀ i, (S i).card = q + 1) (hint : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1)
    (p0 p : Fin (q^2+q+1)) (hp : p ≠ p0) : ∃ i, p0 ∈ S i ∧ p ∈ S i := by
  set P := Finset.univ.filter (fun i => p0 ∈ S i) with hP
  set F := P.biUnion (fun i => (S i).erase p0) with hF
  have hdisj : (P : Set (Fin (q^2+q+1))).PairwiseDisjoint (fun i => (S i).erase p0) := by
    intro i hi j hj hij
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    have hi' : p0 ∈ S i := by simpa [hP] using hi
    have hj' : p0 ∈ S j := by simpa [hP] using hj
    have ha' := Finset.mem_erase.1 ha
    have hb' := Finset.mem_erase.1 hb
    have hsub : ({a, p0} : Finset (Fin (q^2+q+1))) ⊆ S i ∩ S j := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.2 ⟨ha'.2, hb'.2⟩
      · exact Finset.mem_inter.2 ⟨hi', hj'⟩
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair ha'.1] at h2
    have := hint i j hij
    omega
  have hFcard : F.card = (q + 1) * q := by
    rw [hF, Finset.card_biUnion hdisj]
    have : ∀ i ∈ P, ((S i).erase p0).card = q := by
      intro i hi
      have hi' : p0 ∈ S i := by simpa [hP] using hi
      rw [Finset.card_erase_of_mem hi', hcard]; simp
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, hP, hdeg]
  have hFsub : F ⊆ Finset.univ.erase p0 := by
    intro a ha
    rw [hF, Finset.mem_biUnion] at ha
    obtain ⟨i, _, ha⟩ := ha
    exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 ha).1, Finset.mem_univ _⟩
  have hFeq : F = Finset.univ.erase p0 := by
    apply Finset.eq_of_subset_of_card_le hFsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      hFcard]
    have : q ^ 2 + q + 1 - 1 = (q + 1) * q := by ring_nf; omega
    omega
  have hpF : p ∈ F := by rw [hFeq]; exact Finset.mem_erase.2 ⟨hp, Finset.mem_univ _⟩
  rw [hF, Finset.mem_biUnion] at hpF
  obtain ⟨i, hi, hpi⟩ := hpF
  exact ⟨i, by simpa [hP] using hi, (Finset.mem_erase.1 hpi).2⟩

theorem meet_count (q : ℕ) (S : Fin (q^2+q+1) → Finset (Fin (q^2+q+1)))
    (hcard : ∀ i, (S i).card = q + 1) (hint : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1)
    (T : Finset (Fin (q^2+q+1))) :
    (Finset.univ.filter (fun w => ¬ Disjoint (S w) T)).card ≤ T.card * q + 1 := by
  rcases T.eq_empty_or_nonempty with hT | ⟨p0, hp0⟩
  · subst hT; simp
  set P := Finset.univ.filter (fun i => p0 ∈ S i) with hP
  set R := (T.erase p0).biUnion (fun p => Finset.univ.filter (fun i => p ∈ S i) \ P) with hR
  have hsub : Finset.univ.filter (fun w => ¬ Disjoint (S w) T) ⊆ P ∪ R := by
    intro w hw
    rw [Finset.mem_filter, Finset.not_disjoint_iff] at hw
    obtain ⟨_, a, haS, haT⟩ := hw
    by_cases h0 : p0 ∈ S w
    · exact Finset.mem_union_left _ (by simp [hP, h0])
    · apply Finset.mem_union_right
      rw [hR, Finset.mem_biUnion]
      have hne : a ≠ p0 := fun h => h0 (h ▸ haS)
      exact ⟨a, Finset.mem_erase.2 ⟨hne, haT⟩, by simp [hP, haS, h0]⟩
  have hRc : R.card ≤ (T.erase p0).card * q := by
    rw [hR]
    apply Finset.card_biUnion_le_card_mul
    intro p hp
    have hp' := Finset.mem_erase.1 hp
    obtain ⟨i0, hi0, hpi0⟩ := pencil q S hcard hint hdeg p0 p hp'.1
    have hs : Finset.univ.filter (fun i => p ∈ S i) \ P ⊆
        (Finset.univ.filter (fun i => p ∈ S i)).erase i0 := by
      intro i hi
      rw [Finset.mem_sdiff] at hi
      refine Finset.mem_erase.2 ⟨?_, hi.1⟩
      rintro rfl
      exact hi.2 (by simp [hP, hi0])
    have := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem (by simp [hpi0]), hdeg] at this
    omega
  have hPc : P.card = q + 1 := by rw [hP, hdeg]
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le P R
  rw [Finset.card_erase_of_mem hp0] at hRc
  obtain ⟨t, ht⟩ : ∃ t, T.card = t + 1 := ⟨T.card - 1, by
    have := Finset.card_pos.2 ⟨p0, hp0⟩; omega⟩
  rw [ht] at hRc ⊢
  simp only [Nat.add_sub_cancel] at hRc
  have : (t + 1) * q + 1 = (q + 1) + t * q := by ring
  omega

theorem disj_count (q : ℕ) (S : Fin (q^2+q+1) → Finset (Fin (q^2+q+1)))
    (hcard : ∀ i, (S i).card = q + 1) (hint : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdeg : ∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1)
    (T : Finset (Fin (q^2+q+1))) :
    (q^2+q+1) - (T.card * q + 1) ≤ (Finset.univ.filter (fun w => Disjoint (S w) T)).card := by
  have h1 := meet_count q S hcard hint hdeg T
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (q^2+q+1)))) (fun w => Disjoint (S w) T)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega


end PEqualNP.Outside.L_meta_1373

theorem PEqualNP.Outside.L_meta_1373 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (q : ℕ) (S : Fin (q^2+q+1) → Finset (Fin (q^2+q+1))) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q^2+q+1) → ℕ), 2 ≤ q → (∀ i, (S i).card = q + 1) → (∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ (w : Fin (q^2+q+1)) (x : Fin (q^2+q+1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → ∃ w : ℕ, 1 ≤ w ∧ 1 + max ((q^2+q+1) * min (w - 1) q) (q * ((q^2+q+1) - (w * q + 1))) ≤ gates.length := by
  intro h270 h669 q S gates out hq hcard hint hdeg hops huniq hfun
  have hq1 : 1 ≤ q := by omega
  rcases PEqualNP.Outside.L_meta_1373.on1_split gates hops huniq with hAO |
    ⟨pre, post, ins, rfl, hpre, hpost⟩
  · have hb := PEqualNP.Outside.L_meta_1373.mono_bound h270 h669 (q^2+q+1) q S hq1 hcard hint
      gates out hAO ∅ (fun w x _ => hfun w x)
    have hall : (Finset.univ.filter
        (fun w => Disjoint (S w) (∅ : Finset (Fin (q^2+q+1))))).card = q^2+q+1 := by simp
    rw [hall] at hb
    refine ⟨1, le_refl 1, ?_⟩
    have hA : (q^2+q+1) * min (1 - 1) q ≤ gates.length - 1 := by simp
    have hB : q * ((q^2+q+1) - (1 * q + 1)) ≤ gates.length - 1 := by
      have e1 : (q^2+q+1) - (1 * q + 1) = q^2 := by omega
      rw [e1]
      have e2 : q * (q^2+q+1) = q * q^2 + q * q + q := by ring
      have e3 : 1 ≤ q * q := Nat.one_le_iff_ne_zero.2 (by positivity)
      omega
    have hM := max_le hA hB
    have hL : 1 ≤ gates.length := by
      have e2 : q * (q^2+q+1) = q * q^2 + q * q + q := by ring
      omega
    omega
  · have hlen : (pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post).length = pre.length + post.length + 1 := by
      simp; omega
    have high : ∀ T : Finset (Fin (q^2+q+1)), (∀ x : Fin (q^2+q+1) → Bool,
        (∀ p ∈ T, x p = true) →
        ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = true) →
        q * (Finset.univ.filter (fun w => Disjoint (S w) T)).card
          ≤ pre.length + post.length := by
      intro T hT
      obtain ⟨r, hr⟩ := PEqualNP.Outside.L_meta_1373.on1_piece_u (q^2+q+1) pre post ins
      have hG3 : ∀ g ∈ pre ++ post.map (fun g => ({ op := g.op, inputs := g.inputs.map r } :
          PEqualNP.CircuitLowerBounds.Gate)),
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        rw [List.mem_append] at hg
        rcases hg with hg | hg
        · exact hpre g hg
        · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
          simpa using hpost g0 hg0
      have hb := PEqualNP.Outside.L_meta_1373.mono_bound h270 h669 (q^2+q+1) q S hq1 hcard hint
        _ (fun w => r (out w)) hG3 T
        (fun w x hx => by rw [hr (out w) x (hT x hx)]; exact hfun w x)
      simpa using hb
    have low : ∀ k0 : ℕ, 1 ≤ k0 → (∀ x : Fin (q^2+q+1) → Bool,
        (Finset.univ.filter (fun p => x p = true)).card ≤ k0 →
        ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = false) →
        (q^2+q+1) * min k0 q ≤ pre.length + post.length := by
      intro k0 hk0 hlow
      obtain ⟨r, hr⟩ := PEqualNP.Outside.L_meta_1373.piece_dd (q^2+q+1) pre post ins
        (fun g hg => (hpost g hg).1)
      have hG1 : ∀ g ∈ pre ++ post.map
          (PEqualNP.Outside.L_meta_1373.dmod r ((q^2+q+1) + pre.length)),
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
        intro g hg
        rw [List.mem_append] at hg
        rcases hg with hg | hg
        · exact hpre g hg
        · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
          exact PEqualNP.Outside.L_meta_1373.dmod_ok _ _ g0 (hpost g0 hg0)
      have hne : ∀ w, out w ≠ (q^2+q+1) + pre.length := by
        intro w hw
        have h0 := hfun w (fun _ => false)
        rw [hw, PEqualNP.Outside.L_meta_1373.eval_slot] at h0
        have h00 := hlow (fun _ => false) (by simp)
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval] at h0
        rw [h00] at h0
        simp at h0
      have hb := PEqualNP.Outside.L_meta_1373.low_bound h270 h669 (q^2+q+1) q k0 S hq1 hcard
        hint _ (fun w => r (out w)) hG1 hk0
        (fun w x hx => by rw [hr (out w) x (hne w) (hlow x hx)]; exact hfun w x)
      simpa using hb
    by_cases hex : ∃ x : Fin (q^2+q+1) → Bool,
        ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = true
    · classical
      have hP : ∃ w, ∃ x : Fin (q^2+q+1) → Bool,
          ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
            (List.ofFn x)).getD i false).headD false) = true ∧
          (Finset.univ.filter (fun p => x p = true)).card = w := by
        obtain ⟨x, hx⟩ := hex
        exact ⟨_, x, hx, rfl⟩
      obtain ⟨x0, hx0, hw0⟩ := Nat.find_spec hP
      set w0 := Nat.find hP with hw0def
      set T := Finset.univ.filter (fun p => x0 p = true) with hTdef
      have hT : ∀ x : Fin (q^2+q+1) → Bool, (∀ p ∈ T, x p = true) →
          ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
            (List.ofFn x)).getD i false).headD false) = true := by
        intro x hx
        exact PEqualNP.Outside.L_meta_1373.on1_piece_h _ pre ins hpre x0 x
          (fun i hi => hx i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)) hx0
      have hB := high T hT
      have hD := PEqualNP.Outside.L_meta_1373.disj_count q S hcard hint hdeg T
      rw [hw0] at hD
      have hlowx : ∀ x : Fin (q^2+q+1) → Bool,
          (Finset.univ.filter (fun p => x p = true)).card ≤ w0 - 1 → 2 ≤ w0 →
          ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
            (List.ofFn x)).getD i false).headD false) = false := by
        intro x hx h2
        by_contra hc
        have hc' : ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
            (List.ofFn x)).getD i false).headD false) = true := by simpa using hc
        have := Nat.find_min' hP ⟨x, hc', rfl⟩
        omega
      by_cases hz : w0 = 0
      · refine ⟨1, le_refl 1, ?_⟩
        rw [hz] at hD
        have hA : (q^2+q+1) * min (1 - 1) q ≤ pre.length + post.length := by simp
        have hBB : q * ((q^2+q+1) - (1 * q + 1)) ≤ pre.length + post.length := by
          calc q * ((q^2+q+1) - (1 * q + 1))
              ≤ q * (Finset.univ.filter (fun w => Disjoint (S w) T)).card := by
                apply Nat.mul_le_mul_left; omega
            _ ≤ _ := hB
        have hM := max_le hA hBB
        rw [hlen]; omega
      · refine ⟨w0, by omega, ?_⟩
        have hBB : q * ((q^2+q+1) - (w0 * q + 1)) ≤ pre.length + post.length :=
          le_trans (Nat.mul_le_mul_left _ hD) hB
        have hA : (q^2+q+1) * min (w0 - 1) q ≤ pre.length + post.length := by
          by_cases h1 : w0 = 1
          · rw [h1]; simp
          · exact low (w0 - 1) (by omega) (fun x hx => hlowx x hx (by omega))
        have hM := max_le hA hBB
        rw [hlen]; omega
    · simp only [not_exists] at hex
      have hfalse : ∀ x : Fin (q^2+q+1) → Bool,
          ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
            (List.ofFn x)).getD i false).headD false) = false := fun x => by simpa using hex x
      refine ⟨q + 1, by omega, ?_⟩
      have hA := low q hq1 (fun x _ => hfalse x)
      rw [min_self] at hA
      have e : (q + 1) * q + 1 = q^2+q+1 := by ring
      rw [e, Nat.sub_self, Nat.mul_zero, show q + 1 - 1 = q by omega, min_self]
      have hM : max ((q^2+q+1) * q) 0 ≤ pre.length + post.length := max_le hA (Nat.zero_le _)
      rw [hlen]; omega
