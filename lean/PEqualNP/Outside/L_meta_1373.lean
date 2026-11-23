import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1373

open PEqualNP.CircuitLowerBounds

-- The split and relabel arguments follow the project checked OneNot helpers.
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

def on1_relabel (r : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map r }


theorem on1_relabel_sim_all (r : ℕ → ℕ) (gs : List Gate) : ∀ (v w : List Bool),
    (∀ i, v.getD (r i) false = w.getD i false) →
    (∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i) →
    (∀ k < gs.length, r (w.length + k) = v.length + k) →
    (∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) →
    ∀ i, (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  induction gs with
  | nil => intro v w h1 _ _ _ i; exact h1 i
  | cons g gs ih =>
    intro v w h1 h2 h3 h4
    simp only [List.length_cons] at h2 h3 h4
    have hval : (on1_relabel r g).op.eval
          ((on1_relabel r g).inputs.map fun i => v.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [on1_relabel, List.map_map]
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


theorem on1_relabel_sim (r : ℕ → ℕ) (gs : List Gate) (v w : List Bool)
    (h1 : ∀ i < w.length, v.getD (r i) false = w.getD i false)
    (h2 : ∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i)
    (h3 : ∀ k < gs.length, r (w.length + k) = v.length + k)
    (h4 : ∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) (i : ℕ) :
    (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  apply on1_relabel_sim_all r gs v w _ h2 h3 h4
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


private def pRead {n : ℕ} (pre : List Gate) (ins : List ℕ) (x : Fin n → Bool) : Bool :=
  (ins.map (fun i => (wiresFrom pre (List.ofFn x)).getD i false)).headD false

private def refFace (n p : ℕ) (i : ℕ) : ℕ :=
  if i < n + p then i + 1 else if i = n + p then 0 else i

private def gatesFace (n : ℕ) (pre post : List Gate) : List Gate :=
  pre.map (on1_relabel (· + 1)) ++ post.map (on1_relabel (refFace n pre.length))

private theorem faceLen (n : ℕ) (pre post : List Gate) :
    (gatesFace n pre post).length = pre.length + post.length := by
  simp [gatesFace]

private theorem faceLegal (n : ℕ) (pre post : List Gate)
    (hpre : ∀ g ∈ pre, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ gatesFace n pre post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    simpa [on1_relabel] using hpre a ha
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    simpa [on1_relabel] using hpost a ha

private theorem faceEval {n : ℕ} (pre post : List Gate) (ins : List ℕ) (o : ℕ)
    (x : Fin n → Bool) (b : Bool) (hb : (!pRead pre ins x) = b) :
    Circuit.eval ⟨gatesFace n pre post, refFace n pre.length o⟩ (List.ofFn (Fin.cons b x)) =
      Circuit.eval ⟨pre ++ ⟨.not, ins⟩ :: post, o⟩ (List.ofFn x) := by
  let a := List.ofFn x
  let old := wiresFrom pre a
  let new := wiresFrom (pre.map (on1_relabel (· + 1))) (b :: a)
  have ha : a.length = n := by simp [a]
  have ho : old.length = n + pre.length := by simp [old, length_wiresFrom, ha]
  have hn : new.length = n + pre.length + 1 := by
    simp [new, length_wiresFrom, ha, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hpre (i : ℕ) : new.getD (i + 1) false = old.getD i false := by
    apply on1_relabel_sim (· + 1) pre (b :: a) a
    · intro j _; rfl
    · intro j hj; left; simp; omega
    · intro j _; simp; omega
    · intro j hj; simp; omega
  have hfirst : new.getD 0 false = b := by
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix (pre.map (on1_relabel (· + 1))) (b :: a)
    simp [new, ht]
  have hs : List.ofFn (Fin.cons b x) = b :: a := by simp [List.ofFn_succ, a]
  have hval : GateOp.not.eval (ins.map fun i => old.getD i false) = b := by
    simpa only [GateOp.eval, pRead, old, a] using hb
  change (wiresFrom (gatesFace n pre post) (List.ofFn (Fin.cons b x))).getD
      (refFace n pre.length o) false =
    (wiresFrom (pre ++ ⟨.not, ins⟩ :: post) a).getD o false
  rw [hs, gatesFace, wiresFrom_append, wiresFrom_append, on1_wiresFrom_cons]
  change (wiresFrom (post.map (on1_relabel (refFace n pre.length))) new).getD
      (refFace n pre.length o) false =
    (wiresFrom post (old ++ [GateOp.not.eval (ins.map fun i => old.getD i false)])).getD o false
  rw [hval]
  apply on1_relabel_sim (refFace n pre.length) post new (old ++ [b])
  · intro i hi
    by_cases hlt : i < n + pre.length
    · have hlt' : i < old.length := by omega
      simp only [refFace, hlt, ite_true]
      rw [hpre, List.getD_append _ _ _ _ hlt']
    · have he : i = n + pre.length := by simp at hi; omega
      subst i
      simp only [refFace, lt_irrefl, ite_false, ite_true]
      rw [hfirst, ← ho, getD_snoc_eq]
  · intro i hi
    left
    simp only [List.length_append, List.length_singleton, ho, hn, refFace] at hi ⊢
    split_ifs <;> omega
  · intro k hk
    simp only [List.length_append, List.length_singleton, ho, hn, refFace]
    split_ifs <;> omega
  · intro i hi
    simp only [List.length_append, List.length_singleton, ho, hn] at hi ⊢
    simp only [refFace]
    split_ifs <;> omega

private abbrev CountFact : Prop := ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size

private abbrev NormalizeFact : Prop := ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))


private def force {n : ℕ} (T Z : Finset (Fin n)) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if i ∈ T then true else if i ∈ Z then false else x i

private def trueSet {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i = true

private def onSet {n : ℕ} (y : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∈ y)

private lemma onTrueSet {n : ℕ} (x : Fin n → Bool) : onSet (trueSet x) = x := by
  funext i
  cases hx : x i <;> simp [onSet, trueSet, hx]

private lemma cardSingle {n : ℕ} (p : Fin n) :
    (trueSet (fun v => decide (v = p))).card = 1 := by
  have h : trueSet (fun v => decide (v = p)) = {p} := by ext; simp [trueSet]
  simp [h]

private lemma off_zero {n : ℕ} : (trueSet (fun _ : Fin n => false)).card = 0 := by
  simp [trueSet]

private lemma faceCount (hc : CountFact) (hn : NormalizeFact) (n m q k : ℕ)
    (S : Fin m → Finset (Fin n)) (gs : List Gate) (out : Fin m → ℕ) (T Z : Finset (Fin n))
    (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hcard : ∀ j, (S j).card = q + 1)
    (hmeet : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hops : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hEval : ∀ j x, (trueSet x).card ≤ k →
      Circuit.eval ⟨gs, out j⟩ (List.ofFn (force T Z x)) = decide (∃ p ∈ S j, x p = true)) :
    m * min k q ≤ gs.length := by
  obtain ⟨gl, r, hl, hlen, hr⟩ := hn n gs T Z hops
  have hEq (j : Fin m) (x : Fin n → Bool) (hx : (trueSet x).card ≤ k) :
      Circuit.eval ⟨gl, r (out j)⟩ (List.ofFn x) = decide (∃ p ∈ S j, x p = true) := by
    have hs : (S j).Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
    obtain ⟨p, hp⟩ := hs
    let x0 : Fin n → Bool := fun _ => false
    let xp : Fin n → Bool := fun v => decide (v = p)
    have he0 := hEval j x0 (by simpa only [x0, off_zero] using Nat.zero_le k)
    have hp0 := hEval j xp (by simpa only [xp, cardSingle] using hk)
    have hnconst :
        ∃ x y : Fin n → Bool,
          Circuit.eval ⟨gs, out j⟩ (List.ofFn (force T Z x)) ≠
            Circuit.eval ⟨gs, out j⟩ (List.ofFn (force T Z y)) := by
      refine ⟨x0, xp, ?_⟩
      rw [he0, hp0]
      simp [x0, xp, hp]
    exact (hr (out j) hnconst x).trans (hEval j x hx)
  let C : Circuit := ⟨gl, 0⟩
  have hB : ∑ _j : Fin m, min k q ≤ C.size := by
    apply hc n m k S C (r ∘ out) (fun _ => min k q) hmeet
      (fun j => by rw [hcard]; omega) hl
    · intro j p
      change Circuit.eval ⟨gl, r (out j)⟩ (List.ofFn (fun v => decide (v = p))) = true ↔ _
      rw [hEq j _ (by simpa only [cardSingle] using hk)]
      simp
    · intro j x hx hmiss
      change Circuit.eval ⟨gl, r (out j)⟩ (List.ofFn x) = false
      rw [hEq j x hx]
      simpa using hmiss
    · exact fun _ => min_le_left _ _
    · intro j
      rw [hcard]
      exact Nat.add_le_add_right (min_le_right _ _) 1
  have hC : C.size ≤ gs.length := hlen
  exact (by simpa using hB : m * min k q ≤ C.size).trans hC

private def faceSet {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.map (Fin.succEmb n)

private lemma faceSet_card {n : ℕ} (S : Finset (Fin n)) :
    (faceSet S).card = S.card := by simp [faceSet]

private lemma faceSet_meet {n : ℕ} (S T : Finset (Fin n)) :
    (faceSet S ∩ faceSet T).card = (S ∩ T).card := by
  rw [faceSet, faceSet, ← Finset.map_inter, Finset.card_map]

private def faceTrue {n : ℕ} (base : Finset (Fin n)) (b : Bool) : Finset (Fin (n + 1)) :=
  if b then insert 0 (faceSet base) else faceSet base

private def faceFalse (n : ℕ) (b : Bool) : Finset (Fin (n + 1)) :=
  if b then ∅ else {0}

private lemma faceForce {n : ℕ} (base : Finset (Fin n)) (b : Bool) (x : Fin (n + 1) → Bool) :
    force (faceTrue base b) (faceFalse n b) x =
      Fin.cons b (fun p => if p ∈ base then true else x p.succ) := by
  funext i
  refine Fin.cases ?_ (fun p => ?_) i
  · cases b <;> simp [force, faceTrue, faceFalse, faceSet, Fin.succ_ne_zero]
  · cases b <;> simp [force, faceTrue, faceFalse, faceSet, Fin.succ_ne_zero]

private lemma weight_drop {n : ℕ} (x : Fin (n + 1) → Bool) :
    (trueSet (fun p : Fin n => x p.succ)).card ≤ (trueSet x).card := by
  rw [← faceSet_card (trueSet (fun p : Fin n => x p.succ))]
  apply Finset.card_le_card
  intro i h
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩

private lemma exists_face {n : ℕ} (S : Finset (Fin n)) (x : Fin (n + 1) → Bool)
    (base : Finset (Fin n)) (hdis : Disjoint S base) :
    (∃ p ∈ S, (if p ∈ base then true else x p.succ) = true) ↔
      ∃ p ∈ faceSet S, x p = true := by
  constructor
  · rintro ⟨p, hp, hx⟩
    have hn : p ∉ base := fun he => Finset.disjoint_left.mp hdis hp he
    exact ⟨p.succ, Finset.mem_map.mpr ⟨p, hp, rfl⟩, by simpa only [ite_eq_right hn] using hx⟩
  · rintro ⟨r, hr, hx⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hr
    have hn : p ∉ base := fun he => Finset.disjoint_left.mp hdis hp he
    change x p.succ = true at hx
    exact ⟨p, hp, by rw [ite_eq_right hn]; exact hx⟩

private def through {n m : ℕ} (S : Fin m → Finset (Fin n)) (p : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun i => p ∈ S i

private lemma sharesLine (q : ℕ) (S : Fin (q^2+q+1) → Finset (Fin (q^2+q+1)))
    (hcard : ∀ i, (S i).card = q+1)
    (hmeet : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hpencil : ∀ p, (through S p).card = q+1) (p r : Fin (q^2+q+1)) (hpr : r ≠ p) :
    ∃ i, i ∈ through S p ∧ i ∈ through S r := by
  classical
  let P := through S p
  let V := P.biUnion (fun j => (S j).erase p)
  have hdis : (P : Set (Fin (q^2+q+1))).PairwiseDisjoint (fun j => (S j).erase p) := by
    intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have hp1 := (Finset.mem_filter.mp hi).2
    have hp2 := (Finset.mem_filter.mp hj).2
    obtain ⟨hun, hu1⟩ := Finset.mem_erase.mp hu
    have hu2 := (Finset.mem_erase.mp hv).2
    have hsub : ({u,p} : Finset _) ⊆ S i ∩ S j := by simp [Finset.insert_subset_iff, hu1, hu2, hp1, hp2]
    have hle := Finset.card_le_card hsub
    rw [Finset.card_pair hun] at hle
    have := hmeet i j hne
    omega
  have hv : V.card = q^2+q := by
    change (P.biUnion _).card = _
    rw [Finset.card_biUnion hdis]
    have hc (j : Fin (q^2+q+1)) (hj : j ∈ P) : ((S j).erase p).card = q := by
      have he := Finset.card_erase_add_one (Finset.mem_filter.mp hj).2
      rw [hcard] at he
      omega
    rw [Finset.sum_congr rfl hc]
    simp [P, hpencil, Nat.add_mul, pow_two]
  have hsub : V ⊆ Finset.univ.erase p := by
    intro u hu
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hu
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hi).1, Finset.mem_univ _⟩
  have heq : V = Finset.univ.erase p := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hv, Finset.card_erase_of_mem (Finset.mem_univ p)]
    simp
  have hr : r ∈ V := by rw [heq]; simp [hpr]
  obtain ⟨i, hi, hir⟩ := Finset.mem_biUnion.mp hr
  exact ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_erase.mp hir).2⟩⟩

private lemma missBound {n m q : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hpencil : ∀ p, (through S p).card = q+1)
    (hshare : ∀ p r, r ≠ p → ∃ i, i ∈ through S p ∧ i ∈ through S r) :
    m - (y.card * q + 1) ≤ (Finset.univ.filter fun i => Disjoint (S i) y).card := by
  classical
  let A : Finset (Fin m) := Finset.univ.filter (fun i => ¬ Disjoint (S i) y)
  have hA : A.card ≤ y.card * q + 1 := by
    by_cases h : y.Nonempty
    · obtain ⟨p, hp⟩ := h
      let P := through S p
      let B := (y.erase p).biUnion fun j => through S j \ P
      have hsub : A ⊆ P ∪ B := by
        intro i hi
        obtain ⟨r, hri, hry⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hi).2
        by_cases hip : i ∈ P
        · exact Finset.mem_union_left _ hip
        · have hrp : r ≠ p := fun h => hip (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ▸ hri⟩)
          exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨r, Finset.mem_erase.mpr ⟨hrp, hry⟩, Finset.mem_sdiff.mpr
              ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hri⟩, hip⟩⟩)
      have hB : B.card ≤ (y.erase p).card * q := by
        apply Finset.card_biUnion_le_card_mul
        intro r hr
        obtain ⟨i, hiP, hiR⟩ := hshare p r (Finset.mem_erase.mp hr).1
        have hpos : 1 ≤ (through S r ∩ P).card :=
          Finset.card_pos.mpr ⟨i, Finset.mem_inter.mpr ⟨hiR, hiP⟩⟩
        have he := Finset.card_sdiff_add_card_inter (through S r) P
        rw [hpencil] at he
        omega
      have hAP := (Finset.card_le_card hsub).trans (Finset.card_union_le P B)
      have hP : P.card = q+1 := hpencil p
      rw [← Finset.card_erase_add_one hp, Nat.add_mul, one_mul]
      omega
    · have he := Finset.not_nonempty_iff_eq_empty.mp h
      simp [A, he]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun i => Disjoint (S i) y)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  change _ + A.card = m at h
  omega


end PEqualNP.Outside.L_meta_1373

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1373 in
theorem PEqualNP.Outside.L_meta_1373 : (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → ∀ (q : ℕ) (S : Fin (q^2+q+1) → Finset (Fin (q^2+q+1))) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q^2+q+1) → ℕ), 2 ≤ q → (∀ i, (S i).card = q + 1) → (∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ p, (Finset.univ.filter (fun i => p ∈ S i)).card = q + 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ (w : Fin (q^2+q+1)) (x : Fin (q^2+q+1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → ∃ w : ℕ, 1 ≤ w ∧ 1 + max ((q^2+q+1) * min (w - 1) q) (q * ((q^2+q+1) - (w * q + 1))) ≤ gates.length := by
  classical
  intro hc hn q S gates out hq hcard hmeet hpoint hlegal hunique heval
  let n := q ^ 2 + q + 1
  have hq1 : 1 ≤ q := by omega
  rcases on1_split gates hlegal hunique with hnone | ⟨pre, post, ins, rfl, hpre, hpost⟩
  · have hAll : n * q ≤ gates.length := by
      have hh := faceCount hc hn n n q q S gates out ∅ ∅ hq1 hq1 hcard hmeet hnone
        (fun j x _ => by simpa [force] using heval j x)
      simpa using hh
    refine ⟨q, hq1, ?_⟩
    change 1 + max (n * min (q - 1) q) (q * (n - (q * q + 1))) ≤ gates.length
    have ha : 1 + n * min (q - 1) q ≤ n * q := by
      rw [min_eq_left (Nat.sub_le _ _)]
      have he : n * q = n * (q - 1) + n := by
        conv_lhs => rw [show q = q - 1 + 1 by omega]
        rw [Nat.mul_add, mul_one]
      have hp : 1 ≤ n := by dsimp [n]; omega
      omega
    have hDiff : n - (q * q + 1) = q := by simp [n, pow_two]
    have hb : 1 + q * (n - (q * q + 1)) ≤ n * q := by
      rw [hDiff]
      have hle : q + 1 ≤ n := by dsimp [n]; omega
      have hp := Nat.mul_le_mul_right q hle
      rw [Nat.add_mul, one_mul] at hp
      omega
    have hmax := max_le_iff.mpr ⟨ha,hb⟩
    rw [Nat.add_max_add_left] at hmax
    exact hmax.trans hAll
  · let gl := gatesFace n pre post
    let re := refFace n pre.length
    have hgl : ∀ g ∈ gl, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 :=
      faceLegal n pre post hpre hpost
    have hlen : gl.length + 1 = (pre ++ (⟨.not, ins⟩ : Gate) :: post).length := by
      simp [gl, faceLen, Nat.add_assoc, Nat.add_left_comm]
    have hforce0 (x : Fin n → Bool) : force ∅ ∅ x = x := by
      funext i
      simp [force]
    have countSlice (m k : ℕ) (e : Fin m → Fin n) (hInj : Function.Injective e)
        (base : Finset (Fin n)) (b : Bool) (hk : 1 ≤ k)
        (hdis : ∀ j, Disjoint (S (e j)) base)
        (hRead : ∀ (x : Fin n → Bool), (trueSet x).card ≤ k →
          (!pRead pre ins (force base ∅ x)) = b) :
        m * min k q ≤ gl.length := by
      refine faceCount hc hn (n + 1) m q k (fun j => faceSet (S (e j))) gl
        (fun j => re (out (e j))) (faceTrue base b) (faceFalse n b) hq1 hk
        (fun j => by rw [faceSet_card, hcard]) ?_ hgl ?_
      · intro i j hij
        rw [faceSet_meet]
        exact hmeet _ _ (fun h => hij (hInj h))
      · intro j x hx
        let z := fun p : Fin n => x p.succ
        have hweight : (trueSet z).card ≤ k := (weight_drop x).trans hx
        have hRead' := hRead z hweight
        have he := faceEval pre post ins (out (e j)) (force base ∅ z) b hRead'
        rw [faceForce, show (fun p : Fin n => if p ∈ base then true else x p.succ) =
          force base ∅ z by funext p; simp [force,z]]
        rw [he, heval]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        exact exists_face (S (e j)) x base (hdis j)
    by_cases hex : ∃ y : Finset (Fin n), pRead pre ins (onSet y) = true
    · have hyEx : ∃ w : ℕ, ∃ y : Finset (Fin n), y.card = w ∧
          pRead pre ins (onSet y) = true := by
        obtain ⟨y,hy⟩ := hex
        exact ⟨y.card,y,rfl,hy⟩
      let w := Nat.find hyEx
      obtain ⟨y, hyCard, hy⟩ := Nat.find_spec hyEx
      have hmin (x : Fin n → Bool) (hx : (trueSet x).card < w) :
          pRead pre ins x = false := by
        cases hh : pRead pre ins x
        · rfl
        · have h := Nat.find_min' hyEx (show ∃ y : Finset (Fin n),
                y.card = (trueSet x).card ∧ pRead pre ins (onSet y) = true from
              ⟨trueSet x, rfl, by rwa [onTrueSet]⟩)
          exact (Nat.not_le_of_lt hx h).elim
      let v := max 1 w
      have hv : 1 ≤ v := le_max_left _ _
      have hLow : n * min (v - 1) q ≤ gl.length := by
        by_cases hpos : 1 ≤ v - 1
        · have hvw : v = w := by dsimp [v] at *; omega
          apply countSlice n (v - 1) id Function.injective_id ∅ true hpos (by simp)
          intro x hx
          have hlt : (trueSet x).card < w := by omega
          rw [hforce0, hmin x hlt] <;> rfl
        · have hz : v - 1 = 0 := by omega
          simp [hz]
      let F := Finset.univ.filter fun j : Fin n => Disjoint (S j) y
      let e := F.orderEmbOfFin (rfl : F.card = F.card)
      have hD (j : Fin F.card) : Disjoint (S (e j)) y := by
        have hr : Set.range e = (F : Set (Fin n)) := Finset.range_orderEmbOfFin F rfl
        have he : e j ∈ (F : Set (Fin n)) := hr ▸ Set.mem_range_self j
        exact (Finset.mem_filter.mp he).2
      have hBig : F.card * q ≤ gl.length := by
        have hb := countSlice F.card q e e.injective y false hq1 hD (by
          intro x _
          have h := on1_piece_h n pre ins hpre (onSet y) (force y ∅ x)
            (fun p hp => by
              have hp' : p ∈ y := of_decide_eq_true hp
              simp [force, hp']) hy
          have hr : pRead pre ins (force y ∅ x) = true := h
          rw [hr] <;> rfl)
        simpa using hb
      have hmiss : n - (y.card * q + 1) ≤ F.card :=
        missBound S y hpoint (sharesLine q S hcard hmeet hpoint)
      have hdiff : n - (v * q + 1) ≤ F.card := by
        have hcardV : y.card ≤ v := by exact hyCard.le.trans (le_max_right _ _)
        have hmul := Nat.mul_le_mul_right q hcardV
        omega
      have hHi : q * (n - (v * q + 1)) ≤ gl.length := by
        have hmul := Nat.mul_le_mul_right q hdiff
        simpa only [Nat.mul_comm q (n - (v * q + 1))] using hmul.trans hBig
      refine ⟨v, hv, ?_⟩
      change 1 + max (n * min (v - 1) q) (q * (n - (v * q + 1))) ≤ _
      have hmax := max_le_iff.mpr ⟨hLow,hHi⟩
      omega
    · have hAll : n * q ≤ gl.length := by
        have hb := countSlice n q id Function.injective_id ∅ true hq1 (by simp) (by
          intro x _
          have hf : pRead pre ins x = false := by
            cases hh : pRead pre ins x
            · rfl
            · exact (hex ⟨trueSet x, by rwa [onTrueSet]⟩).elim
          rw [hforce0, hf] <;> rfl)
        simpa using hb
      refine ⟨q + 1, by omega, ?_⟩
      have hzero : n - ((q + 1) * q + 1) = 0 := by simp [n, pow_two, Nat.add_mul]
      change 1 + max (n * min (q + 1 - 1) q) (q * (n - ((q + 1) * q + 1))) ≤ _
      rw [hzero]
      simp only [Nat.add_sub_cancel, min_self, mul_zero, Nat.max_zero]
      omega
