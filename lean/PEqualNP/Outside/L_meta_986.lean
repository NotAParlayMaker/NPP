import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_986

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def point {n : ℕ} (S : Finset (Fin n)) (u c : Fin n) : Bool := decide (c = u ∧ u ∈ S)

def Inv {n : ℕ} (S : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs z i = false → val gs (point S u) i = true → val gs (point S v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate) (i : ℕ) : Prop :=
  val gs z i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (point S u) i = true ∧ val gs (point S v) i = true

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt S z gs i

theorem D_mono {n : ℕ} (S : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate) (g : Gate) :
    D S z gs ⊆ D S z (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, ?_, ?_⟩
  · rw [val_snoc, ite_eq_right hne]; exact hz
  · rw [val_snoc, ite_eq_right hne]; exact hu
  · rw [val_snoc, ite_eq_right hne]; exact hv

theorem main_inv {n : ℕ} (S : Finset (Fin n)) (z : Fin n → Bool) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S z gs l ∧ S.card ≤ (S.image l).card + (D S z gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, point, decide_eq_true_eq] at hu hv
      exact ⟨hu.2, hu.1.symm.trans hv.1⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, ite_eq_left hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, ite_eq_right hi]
    have key : P z = false → ∀ u, P (point S u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (point S w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) z with hall | ⟨a, b, hab⟩
      · have := hall (point S u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (point S w) a = true, fun w => val gs (point S w) b = true,
          fun w hw => hy (point S w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (point S u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P z = false ∧ ∃ u v, P (point S u) = true ∧ P (point S v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (point S w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inr (hA w v0 h h1)
            · exact absurd (hB u0 v0 h0 h1) hne
            · exact absurd (hA u0 v0 h0 h1) hne
            · exact Or.inr (hB w v0 h h1)
            · exact Or.inl (hB w u0 h h0)
            · exact Or.inl (hB w u0 h h0)
          have red : ∀ w, P (point S w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hw
            rcases two w hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [ite_eq_left h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hiu, red v hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [ite_eq_right h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S z (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, ?_, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
        have hNnot : N ∉ D S z gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S z gs).card + 1 ≤ (D S z (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S z gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono S z gs g)
        omega

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

lemma all_mono (l : List ℕ) (a b : ℕ → Bool)
    (h : ∀ i, a i = true → b i = true) :
    (l.map a).all id = true → (l.map b).all id = true := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true]
    exact fun hi => ⟨h i hi.1, ih hi.2⟩

lemma any_mono (l : List ℕ) (a b : ℕ → Bool)
    (h : ∀ i, a i = true → b i = true) :
    (l.map a).any id = true → (l.map b).any id = true := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.any_cons, id_eq, Bool.or_eq_true]
    exact fun hi => hi.elim (fun hi => Or.inl (h i hi)) (fun hi => Or.inr (ih hi))

lemma gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (h : ∀ i, a.getD i false = true → b.getD i false = true) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hg with hg | hg
  · rw [hg]
    exact all_mono _ _ _ h
  · rw [hg]
    exact any_mono _ _ _ h

lemma append_mono (a b : List Bool) (hlen : a.length = b.length)
    (h : ∀ i, a.getD i false = true → b.getD i false = true)
    (u v : Bool) (huv : u = true → v = true) :
    ∀ i, (a ++ [u]).getD i false = true → (b ++ [v]).getD i false = true := by
  intro i hi
  by_cases hil : i < a.length
  · rw [List.getD_append _ _ _ _ hil] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · by_cases hie : i = a.length
    · subst i
      have hu : u = true := by simpa using hi
      simpa [hlen] using huv hu
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      cases hi

lemma run_mono (gs : List Gate) (hgood : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (a b : List Bool), a.length = b.length →
      (∀ i, a.getD i false = true → b.getD i false = true) →
      ∀ i, (wiresFrom gs a).getD i false = true → (wiresFrom gs b).getD i false = true := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hlen h
    apply ih (fun g' hg' => hgood g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hlen]
    · exact append_mono a b hlen h _ _ (gate_mono g (hgood g List.mem_cons_self) a b h)

lemma ofFn_mono {n : ℕ} (a b : Fin n → Bool)
    (h : ∀ i, a i = true → b i = true) :
    ∀ i, (List.ofFn a).getD i false = true → (List.ofFn b).getD i false = true := by
  intro i hi
  by_cases hin : i < n
  · have ha : a ⟨i, hin⟩ = true := by simpa [hin] using hi
    simpa [hin] using h ⟨i, hin⟩ ha
  · simp [hin] at hi

def freeze (g : Gate) : Gate := match g.op with
  | .not => ⟨.and, []⟩
  | _ => g

lemma frozen_basis (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) :
    ∀ g ∈ gs.map freeze, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  rintro _ h
  obtain ⟨g, hg', rfl⟩ := List.mem_map.mp h
  obtain ⟨hop, hlen⟩ := hg g hg'
  rcases hop with h | h | h <;> simp [freeze, h, hlen]

lemma freeze_compare {n : ℕ} (gs : List Gate) (x : Fin n → Bool)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    (∀ j, val gs x j = true → val (gs.map freeze) x j = true) ∧
    ((∀ q : Fin gs.length, (gs.get q).op = GateOp.not → val gs x (n + q.val) = true) →
      ∀ j, val (gs.map freeze) x j = val gs x j) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨fun _ h => h, fun _ _ => rfl⟩
  | append_singleton gs g ih =>
    obtain ⟨hle, heq⟩ := ih (fun k hk => hg k (by simp [hk]))
    have hop := hg g (by simp)
    let w := n + gs.length
    have hn (y : Fin n → Bool) (j : ℕ) :
        val ((gs ++ [g]).map freeze) y j =
          if j = w then (freeze g).op.eval ((freeze g).inputs.map (val (gs.map freeze) y))
          else val (gs.map freeze) y j := by
      simpa only [List.map_append, List.map_cons, List.map_nil, List.length_map, w] using
        val_snoc (gs.map freeze) (freeze g) y j
    constructor
    · intro j
      rw [hn, val_snoc]
      by_cases hj : j = w
      · rw [ite_eq_left hj, ite_eq_left hj]
        rcases hop with h | h | h
        · simpa only [freeze, h, GateOp.eval] using
            all_mono g.inputs (val gs x) (val (gs.map freeze) x) hle
        · simpa only [freeze, h, GateOp.eval] using
            any_mono g.inputs (val gs x) (val (gs.map freeze) x) hle
        · simp [freeze, h, GateOp.eval]
      · rw [ite_eq_right hj, ite_eq_right hj]
        exact hle j
    · intro hnot
      have hprev := heq (by
        intro q hq
        let q' : Fin (gs ++ [g]).length := ⟨q.val, by simp⟩
        have he : (gs ++ [g]).get q' = gs.get q := by
          change (gs ++ [g])[q.val] = gs[q.val]
          rw [List.getElem_append_left q.isLt]
        have ht := hnot q' (by rw [he]; exact hq)
        change val (gs ++ [g]) x (n + q.val) = true at ht
        rwa [val_snoc, ite_eq_right (by have := q.isLt; omega)] at ht)
      intro j
      rw [hn]
      by_cases hj : j = w
      · rw [ite_eq_left hj]
        rcases hop with h | h | h
        · rw [val_snoc, ite_eq_left hj]
          simp [freeze, h, funext hprev]
        · rw [val_snoc, ite_eq_left hj]
          simp [freeze, h, funext hprev]
        · let q : Fin (gs ++ [g]).length := ⟨gs.length, by simp⟩
          have he : (gs ++ [g]).get q = g := by
            change (gs ++ [g])[gs.length] = g
            simp
          have ht := hnot q (by rw [he]; exact h)
          change val (gs ++ [g]) x w = true at ht
          rw [hj, ht]
          simp [freeze, h, GateOp.eval]
      · rw [ite_eq_right hj, val_snoc, ite_eq_right hj]
        exact hprev j

lemma wire_at_gate {n : ℕ} (gs : List Gate) (q : Fin gs.length) (x : Fin n → Bool) :
    val gs x (n + q.val) = (gs.get q).op.eval ((gs.get q).inputs.map fun j =>
      if j < n + q.val then val gs x j else false) := by
  have h := getD_wiresFrom_gate gs (List.ofFn x) q.val q.isLt
  simp only [List.length_ofFn] at h
  exact h

end PEqualNP.Outside.L_meta_986

open PEqualNP.Outside.L_meta_986 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  intro n m S gates out i0 hw T t0 _ hinter hgate hunique hi0 hhead hbefore houtputs hzero _ _
  let M := gates.map freeze
  have hM := frozen_basis gates hgate
  have hcompare := freeze_compare (n := n) gates (hg := fun g h => (hgate g h).1)
  let R (i : Fin m) := S i \ T.erase t0
  let z (i : Fin m) (p : Fin n) := decide (p ∉ S i ∧ p ∉ T)
  have hneg (i : Fin m) : val M (z i) (out i) = false := by
    have hwire : val gates (z i) hw = false :=
      hzero (z i) (fun t ht => by simp [z, ht])
    have hagree := (hcompare (z i)).2 (by
      intro q hq
      obtain rfl := hunique q hq
      rw [wire_at_gate, hq]
      cases he : (gates.get q).inputs with
      | nil => rfl
      | cons j js =>
        have hj : j = hw := by
          rw [he] at hhead
          simpa using hhead
        simp [GateOp.eval, hj, hbefore, hwire])
    rw [show val M (z i) (out i) = val gates (z i) (out i) from hagree _]
    change Circuit.eval ⟨gates, out i⟩ _ = false
    rw [houtputs]
    simp only [decide_eq_false_iff_not]
    rintro ⟨p, hp, hv⟩
    exact (of_decide_eq_true hv).1 hp
  have hpos (i : Fin m) (p : Fin n) (hp : p ∈ R i) :
      val M (point (R i) p) (out i) = true := by
    apply (hcompare _).1
    change Circuit.eval ⟨gates, out i⟩ _ = true
    rw [houtputs, decide_eq_true_eq]
    exact ⟨p, (Finset.mem_sdiff.mp hp).1, by simp [point, hp]⟩
  let charged (i : Fin m) := D (R i) (z i) M
  choose label hinv hcard using fun i => main_inv (R i) (z i) M hM
  have hbound (i : Fin m) : (R i).card - 1 ≤ (charged i).card := by
    have h1 : ((R i).image (label i)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv i (out i) u v (hneg i) (hpos i u hu) (hpos i v hv)).2
    have := hcard i
    change (R i).card - 1 ≤ (D (R i) (z i) M).card
    omega
  have apart (i j : Fin m) (hij : i ≠ j) (ht : t0 ∈ S i → t0 ∈ S j)
      (w : ℕ) (hi : w ∈ charged i) (hj : w ∈ charged j) : False := by
    obtain ⟨_, hzi, u, v, huv, hu, hv⟩ := Finset.mem_filter.mp hi
    obtain ⟨_, hzj, _⟩ := Finset.mem_filter.mp hj
    have both (p : Fin n) (hp : val M (point (R i) p) w = true) : p ∈ S i ∩ S j := by
      have hpr := (hinv i w p p hzi hp hp).1
      obtain ⟨hpi, hpd⟩ := Finset.mem_sdiff.mp hpr
      refine Finset.mem_inter.mpr ⟨hpi, ?_⟩
      by_cases he : p = t0
      · subst p
        exact ht hpi
      by_contra hpj
      have hpt : p ∉ T := fun h => hpd (Finset.mem_erase.mpr ⟨he, h⟩)
      have hxy (k : Fin n) : point (R i) p k = true → z j k = true := by
        intro hk
        obtain ⟨rfl, _⟩ := of_decide_eq_true hk
        simp [z, hpj, hpt]
      have htj := run_mono M (fun g hg => (hM g hg).1)
        (List.ofFn (point (R i) p)) (List.ofFn (z j)) (by simp)
        (ofFn_mono _ _ hxy) w hp
      change val M (z j) w = true at htj
      exact Bool.noConfusion (hzj.symm.trans htj)
    exact huv (Finset.card_le_one.mp (hinter i j hij) u (both u hu) v (both v hv))
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (charged i) (charged j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    by_cases ht : t0 ∈ S j
    · exact apart i j hij (fun _ => ht) w hi hj
    · exact apart j i hij.symm (fun h => (ht h).elim) w hj hi
  let allCharged := Finset.univ.biUnion charged
  let w0 := n + i0.val
  have hfree (x : Fin n → Bool) : val M x w0 = true := by
    let q : Fin M.length := ⟨i0.val, by simp [M]⟩
    change val M x (n + q.val) = true
    rw [wire_at_gate]
    have he : M.get q = freeze (gates.get i0) := by
      change (gates.map freeze)[i0.val] = freeze gates[i0.val]
      rw [List.getElem_map]
    rw [he]
    simp only [freeze, hi0]
    rfl
  have hnot : w0 ∉ allCharged := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨_, hz, _⟩ := Finset.mem_filter.mp hi
    exact Bool.noConfusion (hz.symm.trans (hfree (z i)))
  have hsubset : insert w0 allCharged ⊆ Finset.Ico n (n + gates.length) := by
    intro w hw'
    rcases Finset.mem_insert.mp hw' with rfl | h
    · exact Finset.mem_Ico.mpr ⟨by dsimp [w0]; omega, by dsimp [w0]; have := i0.isLt; omega⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
      have := (Finset.mem_filter.mp hi).1
      simpa [M] using this
  have hbudget : 1 + ∑ i, ((R i).card - 1) ≤ gates.length := by
    have hc : allCharged.card = ∑ i, (charged i).card := Finset.card_biUnion hdisj
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
    have hh := Finset.card_le_card hsubset
    rw [Finset.card_insert_of_notMem hnot, hc, Nat.card_Ico] at hh
    omega
  let E := T.erase t0
  have hrow (i : Fin m) : (S i).card - 1 ≤ (R i).card - 1 + (S i ∩ E).card := by
    have hc := Finset.card_sdiff_add_card_inter (S i) E
    change (S i).card - 1 ≤ (S i \ E).card - 1 + (S i ∩ E).card
    omega
  have hcount : ∑ i, (S i ∩ E).card =
      ∑ u ∈ E, (Finset.univ.filter (fun i : Fin m => u ∈ S i)).card := by
    calc
      ∑ i, (S i ∩ E).card = ∑ i, ∑ u ∈ E, if u ∈ S i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_filter]
        simp [Finset.filter_mem_eq_inter, Finset.inter_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        rw [← Finset.sum_filter]
        simp
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  rw [Finset.sum_add_distrib, hcount] at hs
  change 1 + ∑ s, ((S s).card - 1) ≤ gates.length +
    ∑ u ∈ E, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card
  omega
