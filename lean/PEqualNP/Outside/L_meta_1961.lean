import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1961_aux

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩

theorem wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wiresFrom (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false) := by
  have h1 : wiresFrom (pre ++ g :: post) X = wiresFrom post
      (wiresFrom pre X ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre X).length = n + pre.length := by
    rw [length_wiresFrom]; omega
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

def V (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (wiresFrom gs x).getD w false

theorem eval_eq (gs : List Gate) (out : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, out⟩ x = V gs x out := rfl

theorem V_prefix (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
    V (pre ++ post) x w = V pre x w := by
  unfold V
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; exact h)]

theorem gate_val_aux (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 26 + i) :
    V gs x (26 + i) = g.op.eval (g.inputs.map (V gs x)) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := split_at gs i g hg
  subst hsplit
  subst hlen
  have h1 : V (pre ++ g :: post) x (26 + pre.length)
      = g.op.eval (g.inputs.map fun w => (wiresFrom pre x).getD w false) :=
    wire_at 26 pre post g x hx
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro w hwm
  exact (V_prefix pre (g :: post) x w (by rw [hx]; exact hw w hwm)).symm

theorem gate_val (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : Fin gs.length)
    (hw : ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ)) :
    V gs x (26 + (i : ℕ)) = (gs.get i).op.eval ((gs.get i).inputs.map (V gs x)) :=
  gate_val_aux gs x hx i (gs.get i) (by simp) hw

theorem or_val (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : Fin gs.length)
    (hw : ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ)) (hop : (gs.get i).op = GateOp.or) :
    V gs x (26 + (i : ℕ)) = true ↔ ∃ w ∈ (gs.get i).inputs, V gs x w = true := by
  rw [gate_val gs x hx i hw, hop]
  simp [GateOp.eval]

def inp (S R : Finset (Fin 13)) : List Bool :=
  List.ofFn (fun u : Fin 13 => decide (u ∈ S)) ++ List.ofFn (fun v : Fin 13 => decide (v ∈ R))

theorem inp_len (S R : Finset (Fin 13)) : (inp S R).length = 26 := by
  simp [inp]

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : ℕ) (h : j < m) :
    (List.ofFn F).getD j d = F ⟨j, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem V_point (gs : List Gate) (S R : Finset (Fin 13)) (w : ℕ) (h : w < 13) :
    V gs (inp S R) w = decide ((⟨w, h⟩ : Fin 13) ∈ S) := by
  unfold V
  rw [getD_wiresFrom _ _ _ (by rw [inp_len]; omega)]
  unfold inp
  rw [List.getD_append _ _ _ _ (by simp; exact h)]
  exact getD_ofFn 13 _ false w h

theorem V_line (gs : List Gate) (S R : Finset (Fin 13)) (w : ℕ) (h1 : 13 ≤ w) (h2 : w < 26) :
    V gs (inp S R) w = decide ((⟨w - 13, by omega⟩ : Fin 13) ∈ R) := by
  unfold V
  rw [getD_wiresFrom _ _ _ (by rw [inp_len]; omega)]
  unfold inp
  rw [List.getD_append_right _ _ _ _ (by simp; exact h1)]
  simp only [List.length_ofFn]
  exact getD_ofFn 13 _ false (w - 13) (by omega)

theorem orP (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0)) :
    ∀ w : ℕ, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0) →
      ∀ S R : Finset (Fin 13),
        (V gs (inp S R) w = true ↔ ∃ p ∈ S, V gs (inp {p} ∅) w = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hP S R
    rcases hP with h | ⟨j, rfl, hj⟩
    · rw [V_point gs S R w h]
      constructor
      · intro hm
        exact ⟨⟨w, h⟩, by simpa using hm, by rw [V_point gs _ _ w h]; simp⟩
      · rintro ⟨p, hp, hv⟩
        rw [V_point gs _ _ w h] at hv
        simp at hv
        rw [hv]
        simpa using hp
    · obtain ⟨hop, hin⟩ := h0 j hj
      rw [or_val gs _ (inp_len S R) j (hwire j) hop]
      constructor
      · rintro ⟨w', hw', hv⟩
        obtain ⟨p, hp, hv'⟩ := (ih w' (hwire j w' hw') (hin w' hw') S R).1 hv
        exact ⟨p, hp, (or_val gs _ (inp_len _ _) j (hwire j) hop).2 ⟨w', hw', hv'⟩⟩
      · rintro ⟨p, hp, hv⟩
        obtain ⟨w', hw', hv'⟩ := (or_val gs _ (inp_len _ _) j (hwire j) hop).1 hv
        exact ⟨w', hw', (ih w' (hwire j w' hw') (hin w' hw') S R).2 ⟨p, hp, hv'⟩⟩

theorem orL (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1)) :
    ∀ w : ℕ, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1) →
      ∀ S R : Finset (Fin 13),
        (V gs (inp S R) w = true ↔ ∃ l ∈ R, V gs (inp ∅ {l}) w = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hP S R
    rcases hP with h | ⟨j, rfl, hj⟩
    · rw [V_line gs S R w h.1 h.2]
      constructor
      · intro hm
        exact ⟨⟨w - 13, by omega⟩, by simpa using hm, by rw [V_line gs _ _ w h.1 h.2]; simp⟩
      · rintro ⟨p, hp, hv⟩
        rw [V_line gs _ _ w h.1 h.2] at hv
        simp at hv
        rw [hv]
        simpa using hp
    · obtain ⟨hop, hin⟩ := h1 j hj
      rw [or_val gs _ (inp_len S R) j (hwire j) hop]
      constructor
      · rintro ⟨w', hw', hv⟩
        obtain ⟨p, hp, hv'⟩ := (ih w' (hwire j w' hw') (hin w' hw') S R).1 hv
        exact ⟨p, hp, (or_val gs _ (inp_len _ _) j (hwire j) hop).2 ⟨w', hw', hv'⟩⟩
      · rintro ⟨p, hp, hv⟩
        obtain ⟨w', hw', hv'⟩ := (or_val gs _ (inp_len _ _) j (hwire j) hop).1 hv
        exact ⟨w', hw', (ih w' (hwire j w' hw') (hin w' hw') S R).2 ⟨p, hp, hv'⟩⟩

def PSw (gs : List Gate) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => V gs (inp {p} ∅) w = true)

def LSw (gs : List Gate) (w : ℕ) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => V gs (inp ∅ {l}) w = true)

theorem PSw_input (gs : List Gate) (w : ℕ) (h : w < 13) : (PSw gs w).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [PSw, Finset.mem_filter, Finset.mem_univ, true_and, V_point gs _ _ w h] at ha hb
  simp at ha hb
  rw [← ha, ← hb]

theorem LSw_input (gs : List Gate) (w : ℕ) (h1 : 13 ≤ w) (h2 : w < 26) : (LSw gs w).card ≤ 1 := by
  apply Finset.card_le_one.2
  intro a ha b hb
  simp only [LSw, Finset.mem_filter, Finset.mem_univ, true_and, V_line gs _ _ w h1 h2] at ha hb
  simp at ha hb
  rw [← ha, ← hb]

def Piece {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (i : Fin N)
    (X : Finset (Fin 13)) : Prop :=
  X.card ≤ 1 ∨ ∃ j, j < i ∧ K j ∧ S j = X

def Built {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) : Prop :=
  ∀ i, K i → ∃ X Y, Piece K S i X ∧ Piece K S i Y ∧ S i = X ∪ Y

theorem split {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S) :
    ∀ (n : ℕ) (i : Fin N), (i : ℕ) = n → K i → 2 ≤ (S i).card →
      ∃ X Y : Finset (Fin 13), S i = X ∪ Y ∧ X ≠ S i ∧ Y ≠ S i ∧
        (X.card ≤ 1 ∨ ∃ j, K j ∧ S j = X) ∧ (Y.card ≤ 1 ∨ ∃ j, K j ∧ S j = Y) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hK h2
    obtain ⟨X, Y, hX, hY, hXY⟩ := hB i hK
    by_cases hXe : X = S i
    · rcases hX with hX | ⟨j, hji, hKj, hSj⟩
      · rw [hXe] at hX; omega
      · have hSji : S j = S i := by rw [hSj, hXe]
        have := ih j (by rw [← hi]; exact hji) j rfl hKj (by rw [hSji]; exact h2)
        rw [hSji] at this
        exact this
    · by_cases hYe : Y = S i
      · rcases hY with hY | ⟨j, hji, hKj, hSj⟩
        · rw [hYe] at hY; omega
        · have hSji : S j = S i := by rw [hSj, hYe]
          have := ih j (by rw [← hi]; exact hji) j rfl hKj (by rw [hSji]; exact h2)
          rw [hSji] at this
          exact this
      · refine ⟨X, Y, hXY, hXe, hYe, ?_, ?_⟩
        · rcases hX with hX | ⟨j, _, hKj, hSj⟩
          · exact Or.inl hX
          · exact Or.inr ⟨j, hKj, hSj⟩
        · rcases hY with hY | ⟨j, _, hKj, hSj⟩
          · exact Or.inl hY
          · exact Or.inr ⟨j, hKj, hSj⟩

theorem card_lt_of_ne {X Z : Finset (Fin 13)} (h : X ⊆ Z) (hne : X ≠ Z) : X.card < Z.card :=
  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨h, hne⟩)

theorem cnt3 {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S)
    (i : Fin N) (hK : K i) (h3 : (S i).card = 3) :
    ∃ j, K j ∧ (S j).card = 2 ∧ S j ⊆ S i := by
  obtain ⟨X, Y, hXY, hXe, hYe, hX, hY⟩ := split K S hB i i rfl hK (by omega)
  have hXs : X ⊆ S i := by rw [hXY]; exact Finset.subset_union_left
  have hYs : Y ⊆ S i := by rw [hXY]; exact Finset.subset_union_right
  have hXc := card_lt_of_ne hXs hXe
  have hYc := card_lt_of_ne hYs hYe
  have hu : (S i).card ≤ X.card + Y.card := by rw [hXY]; exact Finset.card_union_le X Y
  by_cases hX2 : X.card = 2
  · rcases hX with hX | ⟨j, hKj, hSj⟩
    · omega
    · exact ⟨j, hKj, by rw [hSj]; exact hX2, by rw [hSj]; exact hXs⟩
  · have hY2 : Y.card = 2 := by omega
    rcases hY with hY | ⟨j, hKj, hSj⟩
    · omega
    · exact ⟨j, hKj, by rw [hSj]; exact hY2, by rw [hSj]; exact hYs⟩

theorem cnt {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S)
    (i : Fin N) (hK : K i) (h2 : 2 ≤ (S i).card) (h4 : (S i).card ≤ 4) :
    ∃ O' : Finset (Fin N), (∀ j ∈ O', K j ∧ 2 ≤ (S j).card ∧ S j ⊆ S i) ∧
      (S i).card ≤ O'.card + 1 := by
  classical
  obtain h | h | h : (S i).card = 2 ∨ (S i).card = 3 ∨ (S i).card = 4 := by omega
  · refine ⟨{i}, ?_, by simp; omega⟩
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    exact ⟨hK, h2, Finset.Subset.refl _⟩
  · obtain ⟨j, hKj, hj2, hjs⟩ := cnt3 K S hB i hK h
    have hne : i ≠ j := by intro e; rw [e] at h; omega
    refine ⟨{i, j}, ?_, by rw [Finset.card_pair hne]; omega⟩
    intro m hm
    rw [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact ⟨hK, h2, Finset.Subset.refl _⟩
    · exact ⟨hKj, by omega, hjs⟩
  · obtain ⟨X, Y, hXY, hXe, hYe, hX, hY⟩ := split K S hB i i rfl hK (by omega)
    have hXs : X ⊆ S i := by rw [hXY]; exact Finset.subset_union_left
    have hYs : Y ⊆ S i := by rw [hXY]; exact Finset.subset_union_right
    have hXc := card_lt_of_ne hXs hXe
    have hYc := card_lt_of_ne hYs hYe
    have hu : (S i).card ≤ X.card + Y.card := by rw [hXY]; exact Finset.card_union_le X Y
    have three : ∀ Z : Finset (Fin 13), Z ⊆ S i → Z.card = 3 → (Z.card ≤ 1 ∨ ∃ j, K j ∧ S j = Z) →
        ∃ O' : Finset (Fin N), (∀ j ∈ O', K j ∧ 2 ≤ (S j).card ∧ S j ⊆ S i) ∧
          (S i).card ≤ O'.card + 1 := by
      intro Z hZs hZ3 hZ
      rcases hZ with hZ | ⟨j, hKj, hSj⟩
      · omega
      · obtain ⟨j', hKj', hj'2, hj's⟩ := cnt3 K S hB j hKj (by rw [hSj]; exact hZ3)
        have hj3 : (S j).card = 3 := by rw [hSj]; exact hZ3
        have e1 : i ≠ j := by intro e; rw [e] at h; omega
        have e2 : i ≠ j' := by intro e; rw [e] at h; omega
        have e3 : j ≠ j' := by intro e; rw [e] at hj3; omega
        refine ⟨{i, j, j'}, ?_, ?_⟩
        · intro m hm
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl | rfl
          · exact ⟨hK, h2, Finset.Subset.refl _⟩
          · exact ⟨hKj, by omega, by rw [hSj]; exact hZs⟩
          · exact ⟨hKj', by omega, fun x hx => hZs (hSj ▸ hj's hx)⟩
        · have : ({i, j, j'} : Finset (Fin N)).card = 3 :=
            Finset.card_eq_three.2 ⟨i, j, j', e1, e2, e3, rfl⟩
          omega
    by_cases hX3 : X.card = 3
    · exact three X hXs hX3 hX
    · by_cases hY3 : Y.card = 3
      · exact three Y hYs hY3 hY
      · have hX2 : X.card = 2 := by omega
        have hY2 : Y.card = 2 := by omega
        rcases hX with hX | ⟨j1, hK1, hS1⟩
        · omega
        · rcases hY with hY | ⟨j2, hK2, hS2⟩
          · omega
          · have e1 : i ≠ j1 := by intro e; rw [e, hS1] at h; omega
            have e2 : i ≠ j2 := by intro e; rw [e, hS2] at h; omega
            have e3 : j1 ≠ j2 := by
              intro e
              have hXYe : X = Y := by rw [← hS1, ← hS2, e]
              rw [hXY, hXYe, Finset.union_self] at h
              omega
            refine ⟨{i, j1, j2}, ?_, ?_⟩
            · intro m hm
              simp only [Finset.mem_insert, Finset.mem_singleton] at hm
              rcases hm with rfl | rfl | rfl
              · exact ⟨hK, h2, Finset.Subset.refl _⟩
              · exact ⟨hK1, by rw [hS1]; omega, by rw [hS1]; exact hXs⟩
              · exact ⟨hK2, by rw [hS2]; omega, by rw [hS2]; exact hYs⟩
            · have : ({i, j1, j2} : Finset (Fin N)).card = 3 :=
                Finset.card_eq_three.2 ⟨i, j1, j2, e1, e2, e3, rfl⟩
              omega

theorem arith (u k m : ℕ) (h4 : u ≤ 4) (hs : u ≤ k * (m + 1)) : 5 * u ≤ 4 * m + 8 * k := by
  obtain hk | hk | hk | hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
  · subst hk; omega
  · subst hk; omega
  · subst hk; omega
  · omega

theorem group_bound {N : ℕ} (K : Fin N → Prop) (S : Fin N → Finset (Fin 13)) (hB : Built K S)
    (Lg : Finset (Fin 13)) (hL : Lg.card ≤ 4)
    (Tg : Finset (Fin N)) (Bs : Fin N → Finset (Fin 13)) (hsub : ∀ j ∈ Tg, Bs j ⊆ Lg)
    (hgate : ∀ j ∈ Tg, 2 ≤ (Bs j).card → ∃ i, K i ∧ S i = Bs j)
    (Og : Finset (Fin N)) (hOg : ∀ i, K i → 2 ≤ (S i).card → S i ⊆ Lg → i ∈ Og) :
    5 * (Tg.biUnion Bs).card ≤ 4 * Og.card + 8 * Tg.card := by
  have hu : (Tg.biUnion Bs).card ≤ 4 :=
    le_trans (Finset.card_le_card (Finset.biUnion_subset.2 hsub)) hL
  have hj : ∀ j ∈ Tg, (Bs j).card ≤ Og.card + 1 := by
    intro j hjT
    by_cases h2 : 2 ≤ (Bs j).card
    · obtain ⟨i, hKi, hSi⟩ := hgate j hjT h2
      have h4 : (S i).card ≤ 4 := by
        rw [hSi]; exact le_trans (Finset.card_le_card (hsub j hjT)) hL
      obtain ⟨O', hO', hc⟩ := cnt K S hB i hKi (by rw [hSi]; exact h2) h4
      have hsubO : O' ⊆ Og := fun j' hj' => hOg j' (hO' j' hj').1 (hO' j' hj').2.1
        (fun x hx => hsub j hjT (hSi ▸ (hO' j' hj').2.2 hx))
      have hcc := Finset.card_le_card hsubO
      rw [hSi] at hc
      omega
    · omega
  have hs : (Tg.biUnion Bs).card ≤ Tg.card * (Og.card + 1) := by
    calc (Tg.biUnion Bs).card ≤ ∑ j ∈ Tg, (Bs j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ Tg, (Og.card + 1) := Finset.sum_le_sum hj
      _ = Tg.card * (Og.card + 1) := by simp
  exact arith _ _ _ hu hs

def E (gs : List Gate) (kind : Fin gs.length → Fin 4) (m i : Fin gs.length) : Prop :=
  kind i = 3 ∧ 26 + (m : ℕ) ∈ (gs.get i).inputs

theorem up (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h3 : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or)
    (x : List Bool) (hx : x.length = 26) (j i : Fin gs.length)
    (hr : Relation.ReflTransGen (E gs kind) j i) (hv : V gs x (26 + (j : ℕ)) = true) :
    V gs x (26 + (i : ℕ)) = true := by
  induction hr with
  | refl => exact hv
  | tail _ hE ih => exact (or_val gs x hx _ (hwire _) (h3 _ hE.1)).2 ⟨_, hE.2, ih⟩

theorem down (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h3 : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3))
    (x : List Bool) (hx : x.length = 26) :
    ∀ (n : ℕ) (i : Fin gs.length), (i : ℕ) = n → (kind i = 2 ∨ kind i = 3) →
      V gs x (26 + (i : ℕ)) = true →
      ∃ j, kind j = 2 ∧ Relation.ReflTransGen (E gs kind) j i ∧ V gs x (26 + (j : ℕ)) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hk hv
    rcases hk with hk | hk
    · exact ⟨i, hk, Relation.ReflTransGen.refl, hv⟩
    · obtain ⟨hop, hin⟩ := h3 i hk
      obtain ⟨w, hw, hvw⟩ := (or_val gs x hx i (hwire i) hop).1 hv
      obtain ⟨m, rfl, hkm⟩ := hin w hw
      have hlt := hwire i _ hw
      obtain ⟨j, hj, hr, hvj⟩ := ih m (by omega) m rfl hkm hvw
      exact ⟨j, hj, hr.tail ⟨hk, hw⟩, hvj⟩

theorem reach_two (gs : List Gate) (kind : Fin gs.length → Fin 4) (j i : Fin gs.length)
    (hi : kind i = 2) (hr : Relation.ReflTransGen (E gs kind) j i) : j = i := by
  cases hr with
  | refl => rfl
  | tail _ hE =>
    have h := hE.1
    rw [hi] at h
    exact absurd h (by decide)

theorem reach_three (gs : List Gate) (kind : Fin gs.length → Fin 4) (j i : Fin gs.length)
    (hj : kind j = 2) (hi : kind i = 3) (hr : Relation.ReflTransGen (E gs kind) j i) :
    ∃ m : Fin gs.length, 26 + (m : ℕ) ∈ (gs.get i).inputs ∧ Relation.ReflTransGen (E gs kind) j m := by
  cases hr with
  | refl =>
    rw [hj] at hi
    exact absurd hi (by decide)
  | tail hr' hE => exact ⟨_, hE.2, hr'⟩

theorem count (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h3 : ∀ i : Fin gs.length, kind i = 3 →
      ∀ w ∈ (gs.get i).inputs, ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3)) :
    ∀ (k : ℕ) (I U : Finset (Fin gs.length)), (∀ i ∈ I, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3)) →
      (∀ j ∈ U, kind j = 2 ∧ ∃ i ∈ I, Relation.ReflTransGen (E gs kind) j i) →
      U.card ≤ I.card +
        (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)).card := by
  intro k
  induction k with
  | zero =>
    intro I U hI hU
    have hUe : U = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      obtain ⟨_, i, hi, _⟩ := hU j hj
      exact absurd (hI i hi).1 (by omega)
    simp [hUe]
  | succ k ih =>
    intro I U hI hU
    have hmono : (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)).card
        ≤ (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1)).card := by
      apply Finset.card_le_card
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, hm.2.1, by omega⟩
    by_cases hex : ∃ i0 ∈ I, (i0 : ℕ) = k
    · obtain ⟨i0, hi0, hi0k⟩ := hex
      have hIpos : 1 ≤ I.card := Finset.card_pos.2 ⟨i0, hi0⟩
      have hIe : (I.erase i0).card = I.card - 1 := Finset.card_erase_of_mem hi0
      have herase : ∀ i ∈ I.erase i0, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3) := by
        intro i hi
        obtain ⟨hne, hiI⟩ := Finset.mem_erase.1 hi
        have h1 := (hI i hiI).1
        have h2 : (i : ℕ) ≠ k := by
          intro e
          exact hne (Fin.ext (by omega))
        exact ⟨by omega, (hI i hiI).2⟩
      rcases (hI i0 hi0).2 with hk2 | hk3
      · have hU' : ∀ j ∈ U.erase i0, kind j = 2 ∧
            ∃ i ∈ I.erase i0, Relation.ReflTransGen (E gs kind) j i := by
          intro j hj
          obtain ⟨hne, hjU⟩ := Finset.mem_erase.1 hj
          obtain ⟨hj2, i, hiI, hr⟩ := hU j hjU
          refine ⟨hj2, i, Finset.mem_erase.2 ⟨?_, hiI⟩, hr⟩
          intro e
          subst e
          exact hne (reach_two gs kind j i hk2 hr)
        have h := ih (I.erase i0) (U.erase i0) herase hU'
        have hUc : U.card - 1 ≤ (U.erase i0).card := Finset.pred_card_le_card_erase
        omega
      · let J : Finset (Fin gs.length) :=
          Finset.univ.filter (fun m : Fin gs.length => 26 + (m : ℕ) ∈ (gs.get i0).inputs)
        have hJmem : ∀ m, m ∈ J ↔ 26 + (m : ℕ) ∈ (gs.get i0).inputs := by
          intro m
          simp [J]
        have hJc : J.card ≤ 2 := by
          have himg : (J.image (fun m : Fin gs.length => 26 + (m : ℕ))).card = J.card := by
            apply Finset.card_image_of_injective
            intro a b hab
            exact Fin.ext (by simpa using hab)
          have hsub : J.image (fun m : Fin gs.length => 26 + (m : ℕ)) ⊆ (gs.get i0).inputs.toFinset := by
            intro w hw
            obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hw
            exact List.mem_toFinset.2 ((hJmem m).1 hm)
          have h1 := Finset.card_le_card hsub
          have h2 := List.toFinset_card_le (gs.get i0).inputs
          have h3' := hlen i0
          omega
        have hI' : ∀ i ∈ I.erase i0 ∪ J, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3) := by
          intro i hi
          rcases Finset.mem_union.1 hi with hi | hi
          · exact herase i hi
          · have hin := (hJmem i).1 hi
            have hlt := hwire i0 _ hin
            obtain ⟨j, hj, hkj⟩ := h3 i0 hk3 _ hin
            have hji : j = i := Fin.ext (by omega)
            subst hji
            exact ⟨by omega, hkj⟩
        have hU' : ∀ j ∈ U, kind j = 2 ∧
            ∃ i ∈ I.erase i0 ∪ J, Relation.ReflTransGen (E gs kind) j i := by
          intro j hjU
          obtain ⟨hj2, i, hiI, hr⟩ := hU j hjU
          by_cases e : i = i0
          · subst e
            obtain ⟨m, hm, hr'⟩ := reach_three gs kind j i hj2 hk3 hr
            exact ⟨hj2, m, Finset.mem_union_right _ ((hJmem m).2 hm), hr'⟩
          · exact ⟨hj2, i, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨e, hiI⟩), hr⟩
        have h := ih (I.erase i0 ∪ J) U hI' hU'
        have hcu := Finset.card_union_le (I.erase i0) J
        have hstep : (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)).card + 1
            ≤ (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1)).card := by
          have hmem : i0 ∈ Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1) :=
            Finset.mem_filter.2 ⟨Finset.mem_univ _, hk3, by omega⟩
          have hsub : Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k)
              ⊆ (Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < k + 1)).erase i0 := by
            intro m hm
            rw [Finset.mem_filter] at hm
            refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨hm.1, hm.2.1, by omega⟩⟩
            intro e
            subst e
            omega
          have h1 := Finset.card_le_card hsub
          have h2 := Finset.card_erase_add_one hmem
          omega
        omega
    · have hI' : ∀ i ∈ I, (i : ℕ) < k ∧ (kind i = 2 ∨ kind i = 3) := by
        intro i hi
        have h1 := (hI i hi).1
        have h2 : (i : ℕ) ≠ k := fun e => hex ⟨i, hi, e⟩
        exact ⟨by omega, (hI i hi).2⟩
      have h := ih I U hI' hU
      omega

def Lp (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun l : Fin 13 => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))

def Pl (l : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun p : Fin 13 => p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))

def TQ (Q : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun v : Fin 13 => ∀ r ∈ Q, r - v ∉ ({0, 1, 3, 9} : Finset (Fin 13)))

def Q0 (d : Fin 13) : Finset (Fin 13) :=
  if d = 4 ∨ d = 5 ∨ d = 6 then {2, 4, 5, 6} else if d = 7 ∨ d = 8 then {2, 4, 7, 8} else {2, 10, 11, 12}

def Qf (p l : Fin 13) : Finset (Fin 13) := (Q0 (p - l)).image (fun q => q + l)

theorem geo_quad : ∀ p l : Fin 13, p - l ∉ ({0, 1, 3, 9} : Finset (Fin 13)) →
    (Qf p l).card = 4 ∧
    (∀ k : Fin 13, ((Qf p l).filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    p ∈ Qf p l ∧ l ∈ TQ (Qf p l) := by
  decide +kernel

theorem geo_lines : ∀ p p' : Fin 13, p ≠ p' → (Lp p ∩ Lp p').card ≤ 1 := by
  decide +kernel

theorem geo_points : ∀ l l' : Fin 13, l ≠ l' → (Pl l ∩ Pl l').card ≤ 1 := by
  decide +kernel

theorem geo_Lp : ∀ p : Fin 13, (Lp p).card = 4 := by
  decide +kernel

theorem geo_Pl : ∀ l : Fin 13, (Pl l).card = 4 := by
  decide +kernel

theorem builtL (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1)) :
    Built (fun i : Fin gs.length => kind i = 1) (fun i : Fin gs.length => LSw gs (26 + (i : ℕ))) := by
  intro i hi
  obtain ⟨hop, hin⟩ := h1 i hi
  have hpiece : ∀ w ∈ (gs.get i).inputs, Piece (fun i : Fin gs.length => kind i = 1)
      (fun i : Fin gs.length => LSw gs (26 + (i : ℕ))) i (LSw gs w) := by
    intro w hw
    rcases hin w hw with h | ⟨j, rfl, hj⟩
    · exact Or.inl (LSw_input gs w h.1 h.2)
    · have hlt := hwire i _ hw
      exact Or.inr ⟨j, Fin.lt_def.2 (by omega), hj, rfl⟩
  have hmem : ∀ l, l ∈ LSw gs (26 + (i : ℕ)) ↔ ∃ w ∈ (gs.get i).inputs, l ∈ LSw gs w := by
    intro l
    simp only [LSw, Finset.mem_filter, Finset.mem_univ, true_and]
    exact or_val gs _ (inp_len _ _) i (hwire i) hop
  have hl := hlen i
  rcases hgi : (gs.get i).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · refine ⟨∅, ∅, Or.inl (by simp), Or.inl (by simp), ?_⟩
    show LSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨LSw gs a, ∅, hpiece a (by rw [hgi]; simp), Or.inl (by simp), ?_⟩
    show LSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨LSw gs a, LSw gs b, hpiece a (by rw [hgi]; simp), hpiece b (by rw [hgi]; simp), ?_⟩
    show LSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · rw [hgi] at hl
    simp at hl

theorem builtP (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0)) :
    Built (fun i : Fin gs.length => kind i = 0) (fun i : Fin gs.length => PSw gs (26 + (i : ℕ))) := by
  intro i hi
  obtain ⟨hop, hin⟩ := h0 i hi
  have hpiece : ∀ w ∈ (gs.get i).inputs, Piece (fun i : Fin gs.length => kind i = 0)
      (fun i : Fin gs.length => PSw gs (26 + (i : ℕ))) i (PSw gs w) := by
    intro w hw
    rcases hin w hw with h | ⟨j, rfl, hj⟩
    · exact Or.inl (PSw_input gs w h)
    · have hlt := hwire i _ hw
      exact Or.inr ⟨j, Fin.lt_def.2 (by omega), hj, rfl⟩
  have hmem : ∀ l, l ∈ PSw gs (26 + (i : ℕ)) ↔ ∃ w ∈ (gs.get i).inputs, l ∈ PSw gs w := by
    intro l
    simp only [PSw, Finset.mem_filter, Finset.mem_univ, true_and]
    exact or_val gs _ (inp_len _ _) i (hwire i) hop
  have hl := hlen i
  rcases hgi : (gs.get i).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · refine ⟨∅, ∅, Or.inl (by simp), Or.inl (by simp), ?_⟩
    show PSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨PSw gs a, ∅, hpiece a (by rw [hgi]; simp), Or.inl (by simp), ?_⟩
    show PSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · refine ⟨PSw gs a, PSw gs b, hpiece a (by rw [hgi]; simp), hpiece b (by rw [hgi]; simp), ?_⟩
    show PSw gs (26 + (i : ℕ)) = _
    ext l
    rw [hmem, hgi]
    simp
  · rw [hgi] at hl
    simp at hl

theorem term_sets (gs : List Gate) (kind : Fin gs.length → Fin 4)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1))
    (h2 : ∀ i : Fin gs.length, kind i = 2 → (gs.get i).op = GateOp.and ∧
      ∃ a b : ℕ, ((gs.get i).inputs = [a, b] ∨ (gs.get i).inputs = [b, a]) ∧
        (a < 13 ∨ ∃ j : Fin gs.length, a = 26 + (j : ℕ) ∧ kind j = 0) ∧
        ((13 ≤ b ∧ b < 26) ∨ ∃ j : Fin gs.length, b = 26 + (j : ℕ) ∧ kind j = 1))
    (i : Fin gs.length) (hi : kind i = 2) :
    ∃ A B : Finset (Fin 13),
      (∀ S R : Finset (Fin 13), V gs (inp S R) (26 + (i : ℕ)) = true ↔
        (∃ p ∈ S, p ∈ A) ∧ (∃ l ∈ R, l ∈ B)) ∧
      (2 ≤ A.card → ∃ j : Fin gs.length, kind j = 0 ∧ PSw gs (26 + (j : ℕ)) = A) ∧
      (2 ≤ B.card → ∃ j : Fin gs.length, kind j = 1 ∧ LSw gs (26 + (j : ℕ)) = B) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := h2 i hi
  refine ⟨PSw gs a, LSw gs b, ?_, ?_, ?_⟩
  · intro S R
    have hv : V gs (inp S R) (26 + (i : ℕ)) = true ↔
        V gs (inp S R) a = true ∧ V gs (inp S R) b = true := by
      rw [gate_val gs _ (inp_len S R) i (hwire i), hop]
      rcases hin with hin | hin
      · rw [hin]; simp [GateOp.eval]
      · rw [hin]; simp [GateOp.eval, and_comm]
    rw [hv, orP gs kind hwire h0 a ha S R, orL gs kind hwire h1 b hb S R]
    simp [PSw, LSw]
  · intro hc
    rcases ha with h | ⟨j, rfl, hj⟩
    · have := PSw_input gs a h
      omega
    · exact ⟨j, hj, rfl⟩
  · intro hc
    rcases hb with h | ⟨j, rfl, hj⟩
    · have := LSw_input gs b h.1 h.2
      omega
    · exact ⟨j, hj, rfl⟩

theorem dbl {α β : Type} (s : Finset α) (t : Finset β) (r : α → β → Prop)
    [∀ a b, Decidable (r a b)] :
    ∑ a ∈ s, (t.filter (r a)).card = ∑ b ∈ t, (s.filter (fun a => r a b)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem main (gs : List Gate) (kind : Fin gs.length → Fin 4) (jo : Fin gs.length)
    (hop : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hwire : ∀ (i : Fin gs.length), ∀ w ∈ (gs.get i).inputs, w < 26 + (i : ℕ))
    (h0 : ∀ i : Fin gs.length, kind i = 0 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, (w < 13 ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 0))
    (h1 : ∀ i : Fin gs.length, kind i = 1 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ((13 ≤ w ∧ w < 26) ∨ ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ kind j = 1))
    (h2 : ∀ i : Fin gs.length, kind i = 2 → (gs.get i).op = GateOp.and ∧
      ∃ a b : ℕ, ((gs.get i).inputs = [a, b] ∨ (gs.get i).inputs = [b, a]) ∧
        (a < 13 ∨ ∃ j : Fin gs.length, a = 26 + (j : ℕ) ∧ kind j = 0) ∧
        ((13 ≤ b ∧ b < 26) ∨ ∃ j : Fin gs.length, b = 26 + (j : ℕ) ∧ kind j = 1))
    (h3 : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or ∧
      ∀ w ∈ (gs.get i).inputs, ∃ j : Fin gs.length, w = 26 + (j : ℕ) ∧ (kind j = 2 ∨ kind j = 3))
    (hjo : kind jo = 2 ∨ kind jo = 3)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      V gs (inp {p} {l}) (26 + (jo : ℕ)) = true)
    (hrej : ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
      V gs (inp Q (TQ Q)) (26 + (jo : ℕ)) = false) :
    64 ≤ gs.length := by
  classical
  have hlen : ∀ i : Fin gs.length, (gs.get i).inputs.length ≤ 2 :=
    fun i => (hop _ (List.get_mem gs i)).2
  have h3op : ∀ i : Fin gs.length, kind i = 3 → (gs.get i).op = GateOp.or := fun i hi => (h3 i hi).1
  have hts : ∀ i : Fin gs.length, ∃ A B : Finset (Fin 13), kind i = 2 →
      ((∀ S R : Finset (Fin 13), V gs (inp S R) (26 + (i : ℕ)) = true ↔
        (∃ p ∈ S, p ∈ A) ∧ (∃ l ∈ R, l ∈ B)) ∧
      (2 ≤ A.card → ∃ j : Fin gs.length, kind j = 0 ∧ PSw gs (26 + (j : ℕ)) = A) ∧
      (2 ≤ B.card → ∃ j : Fin gs.length, kind j = 1 ∧ LSw gs (26 + (j : ℕ)) = B)) := by
    intro i
    by_cases hi : kind i = 2
    · obtain ⟨A, B, h⟩ := term_sets gs kind hwire h0 h1 h2 i hi
      exact ⟨A, B, fun _ => h⟩
    · exact ⟨∅, ∅, fun h => absurd h hi⟩
  choose A B hAB using hts
  obtain ⟨T, hTmem⟩ : ∃ T : Finset (Fin gs.length),
      ∀ j, j ∈ T ↔ (kind j = 2 ∧ Relation.ReflTransGen (E gs kind) j jo) :=
    ⟨Finset.univ.filter (fun j => kind j = 2 ∧ Relation.ReflTransGen (E gs kind) j jo), by simp⟩
  have hcov : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      ∃ j ∈ T, p ∈ A j ∧ l ∈ B j := by
    intro p l hpl
    obtain ⟨j, hj, hr, hv⟩ := down gs kind hwire h3 _ (inp_len _ _) jo jo rfl hjo (hacc p l hpl)
    obtain ⟨⟨p', hp', hpA⟩, ⟨l', hl', hlB⟩⟩ := ((hAB j hj).1 {p} {l}).1 hv
    rw [Finset.mem_singleton] at hp' hl'
    subst hp'
    subst hl'
    exact ⟨j, (hTmem j).2 ⟨hj, hr⟩, hpA, hlB⟩
  have hinc : ∀ j ∈ T, ∀ p ∈ A j, ∀ l ∈ B j, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
    intro j hjT p hp l hl
    obtain ⟨hj, hr⟩ := (hTmem j).1 hjT
    by_contra hn
    obtain ⟨hc, hk, hpQ, hlQ⟩ := geo_quad p l hn
    have hv : V gs (inp (Qf p l) (TQ (Qf p l))) (26 + (j : ℕ)) = true :=
      ((hAB j hj).1 _ _).2 ⟨⟨p, hpQ, hp⟩, ⟨l, hlQ, hl⟩⟩
    have hup := up gs kind hwire h3op _ (inp_len _ _) j jo hr hv
    rw [hrej _ hc hk] at hup
    exact absurd hup (by simp)
  have hBsing : ∀ j ∈ T, 2 ≤ (A j).card → ∀ l ∈ B j, B j = {l} := by
    intro j hjT hc l hl
    apply Finset.eq_singleton_iff_unique_mem.2 ⟨hl, ?_⟩
    intro l' hl'
    by_contra hne
    have hsub : A j ⊆ Pl l' ∩ Pl l := by
      intro p hp
      simp only [Finset.mem_inter, Pl, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hinc j hjT p hp l' hl', hinc j hjT p hp l hl⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := geo_points l' l hne
    omega
  have hAsing : ∀ j : Fin gs.length, ¬ 2 ≤ (A j).card → ∀ p ∈ A j, A j = {p} := by
    intro j hc p hp
    apply Finset.eq_singleton_iff_unique_mem.2 ⟨hp, ?_⟩
    intro p' hp'
    exact Finset.card_le_one.1 (by omega) p' hp' p hp
  obtain ⟨Tp, hTp⟩ : ∃ Tp : Fin 13 → Finset (Fin gs.length),
      ∀ p j, j ∈ Tp p ↔ (j ∈ T ∧ A j = {p}) :=
    ⟨fun p => T.filter (fun j => A j = {p}), by simp⟩
  obtain ⟨Tl, hTl⟩ : ∃ Tl : Fin 13 → Finset (Fin gs.length),
      ∀ l j, j ∈ Tl l ↔ (j ∈ T ∧ 2 ≤ (A j).card ∧ B j = {l}) :=
    ⟨fun l => T.filter (fun j => 2 ≤ (A j).card ∧ B j = {l}), by simp⟩
  obtain ⟨Op, hOp⟩ : ∃ Op : Fin 13 → Finset (Fin gs.length),
      ∀ p i, i ∈ Op p ↔ (kind i = 1 ∧ 2 ≤ (LSw gs (26 + (i : ℕ))).card ∧ LSw gs (26 + (i : ℕ)) ⊆ Lp p) :=
    ⟨fun p => Finset.univ.filter (fun i : Fin gs.length =>
      kind i = 1 ∧ 2 ≤ (LSw gs (26 + (i : ℕ))).card ∧ LSw gs (26 + (i : ℕ)) ⊆ Lp p), by simp⟩
  obtain ⟨Ol, hOl⟩ : ∃ Ol : Fin 13 → Finset (Fin gs.length),
      ∀ l i, i ∈ Ol l ↔ (kind i = 0 ∧ 2 ≤ (PSw gs (26 + (i : ℕ))).card ∧ PSw gs (26 + (i : ℕ)) ⊆ Pl l) :=
    ⟨fun l => Finset.univ.filter (fun i : Fin gs.length =>
      kind i = 0 ∧ 2 ≤ (PSw gs (26 + (i : ℕ))).card ∧ PSw gs (26 + (i : ℕ)) ⊆ Pl l), by simp⟩

  have gp : ∀ p : Fin 13, 5 * ((Tp p).biUnion B).card ≤ 4 * (Op p).card + 8 * (Tp p).card := by
    intro p
    apply group_bound (fun i : Fin gs.length => kind i = 1)
      (fun i : Fin gs.length => LSw gs (26 + (i : ℕ))) (builtL gs kind hlen hwire h1) (Lp p)
      (le_of_eq (geo_Lp p)) (Tp p) B
    · intro j hj l hl
      obtain ⟨hjT, hA⟩ := (hTp p j).1 hj
      simp only [Lp, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hinc j hjT p (by rw [hA]; simp) l hl
    · intro j hj hc
      obtain ⟨hjT, _⟩ := (hTp p j).1 hj
      exact (hAB j ((hTmem j).1 hjT).1).2.2 hc
    · intro i hK hc hs
      exact (hOp p i).2 ⟨hK, hc, hs⟩
  have gl : ∀ l : Fin 13, 5 * ((Tl l).biUnion A).card ≤ 4 * (Ol l).card + 8 * (Tl l).card := by
    intro l
    apply group_bound (fun i : Fin gs.length => kind i = 0)
      (fun i : Fin gs.length => PSw gs (26 + (i : ℕ))) (builtP gs kind hlen hwire h0) (Pl l)
      (le_of_eq (geo_Pl l)) (Tl l) A
    · intro j hj p hp
      obtain ⟨hjT, _, hBj⟩ := (hTl l j).1 hj
      simp only [Pl, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hinc j hjT p hp l (by rw [hBj]; simp)
    · intro j hj hc
      obtain ⟨hjT, _⟩ := (hTl l j).1 hj
      exact (hAB j ((hTmem j).1 hjT).1).2.1 hc
    · intro i hK hc hs
      exact (hOl l i).2 ⟨hK, hc, hs⟩

  have hcovp : ∀ p : Fin 13, 4 ≤ ((Tp p).biUnion B).card +
      (Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A)).card := by
    intro p
    have hsub : Lp p ⊆ (Tp p).biUnion B ∪ Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A) := by
      intro l hl
      have hpl : p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
        simpa only [Lp, Finset.mem_filter, Finset.mem_univ, true_and] using hl
      obtain ⟨j, hjT, hpA, hlB⟩ := hcov p l hpl
      by_cases hc : 2 ≤ (A j).card
      · apply Finset.mem_union_right
        rw [Finset.mem_filter, Finset.mem_biUnion]
        exact ⟨Finset.mem_univ _, j, (hTl l j).2 ⟨hjT, hc, hBsing j hjT hc l hlB⟩, hpA⟩
      · apply Finset.mem_union_left
        rw [Finset.mem_biUnion]
        exact ⟨j, (hTp p j).2 ⟨hjT, hAsing j hc p hpA⟩, hlB⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_union_le ((Tp p).biUnion B)
      (Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A))
    have hc3 := geo_Lp p
    omega
  have hswap : ∑ p : Fin 13, (Finset.univ.filter (fun l : Fin 13 => p ∈ (Tl l).biUnion A)).card
      = ∑ l : Fin 13, ((Tl l).biUnion A).card := by
    rw [dbl Finset.univ Finset.univ (fun (p l : Fin 13) => p ∈ (Tl l).biUnion A)]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    ext p
    simp
  have hC : 52 ≤ ∑ p : Fin 13, ((Tp p).biUnion B).card + ∑ l : Fin 13, ((Tl l).biUnion A).card := by
    rw [← hswap, ← Finset.sum_add_distrib]
    calc 52 = ∑ _p : Fin 13, 4 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun p _ => hcovp p)
  have hG1 : 5 * ∑ p : Fin 13, ((Tp p).biUnion B).card
      ≤ 4 * ∑ p : Fin 13, (Op p).card + 8 * ∑ p : Fin 13, (Tp p).card := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun p _ => gp p)
  have hG2 : 5 * ∑ l : Fin 13, ((Tl l).biUnion A).card
      ≤ 4 * ∑ l : Fin 13, (Ol l).card + 8 * ∑ l : Fin 13, (Tl l).card := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun l _ => gl l)

  have hO1 : ∑ p : Fin 13, (Op p).card ≤ (Finset.univ.filter (fun i : Fin gs.length => kind i = 1)).card := by
    have hd : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Op := by
      intro p _ p' _ hne
      show Disjoint (Op p) (Op p')
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨_, hc, hs⟩ := (hOp p i).1 hi
      obtain ⟨_, _, hs'⟩ := (hOp p' i).1 hi'
      have hc1 := Finset.card_le_card (Finset.subset_inter hs hs')
      have hc2 := geo_lines p p' hne
      omega
    rw [← Finset.card_biUnion hd]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hOp p i).1 hp).1⟩
  have hO2 : ∑ l : Fin 13, (Ol l).card ≤ (Finset.univ.filter (fun i : Fin gs.length => kind i = 0)).card := by
    have hd : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Ol := by
      intro l _ l' _ hne
      show Disjoint (Ol l) (Ol l')
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨_, hc, hs⟩ := (hOl l i).1 hi
      obtain ⟨_, _, hs'⟩ := (hOl l' i).1 hi'
      have hc1 := Finset.card_le_card (Finset.subset_inter hs hs')
      have hc2 := geo_points l l' hne
      omega
    rw [← Finset.card_biUnion hd]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 hi
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hOl l i).1 hl).1⟩
  have hTT : ∑ p : Fin 13, (Tp p).card + ∑ l : Fin 13, (Tl l).card ≤ T.card := by
    have hd1 : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Tp := by
      intro p _ p' _ hne
      show Disjoint (Tp p) (Tp p')
      rw [Finset.disjoint_left]
      intro j hj hj'
      have e1 := ((hTp p j).1 hj).2
      have e2 := ((hTp p' j).1 hj').2
      rw [e1] at e2
      exact hne (Finset.singleton_inj.1 e2)
    have hd2 : ((Finset.univ : Finset (Fin 13)) : Set (Fin 13)).PairwiseDisjoint Tl := by
      intro l _ l' _ hne
      show Disjoint (Tl l) (Tl l')
      rw [Finset.disjoint_left]
      intro j hj hj'
      have e1 := ((hTl l j).1 hj).2.2
      have e2 := ((hTl l' j).1 hj').2.2
      rw [e1] at e2
      exact hne (Finset.singleton_inj.1 e2)
    rw [← Finset.card_biUnion hd1, ← Finset.card_biUnion hd2]
    have hint : (Finset.univ.biUnion Tp) ∩ (Finset.univ.biUnion Tl) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_inter.1 hj
      obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hj1
      obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 hj2
      have e1 := ((hTp p j).1 hp).2
      have e2 := ((hTl l j).1 hl).2.1
      rw [e1, Finset.card_singleton] at e2
      omega
    have hun := Finset.card_union_add_card_inter (Finset.univ.biUnion Tp) (Finset.univ.biUnion Tl)
    rw [hint, Finset.card_empty] at hun
    have hsub : (Finset.univ.biUnion Tp) ∪ (Finset.univ.biUnion Tl) ⊆ T := by
      intro j hj
      rcases Finset.mem_union.1 hj with hj | hj
      · obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hj
        exact ((hTp p j).1 hp).1
      · obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.1 hj
        exact ((hTl l j).1 hl).1
    have hc := Finset.card_le_card hsub
    omega

  have hT2 : T.card ≤ (Finset.univ.filter (fun i : Fin gs.length => kind i = 2)).card := by
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ((hTmem j).1 hj).1⟩
  have hT3 : T.card ≤ 1 + (Finset.univ.filter (fun i : Fin gs.length => kind i = 3)).card := by
    have h := count gs kind hlen hwire (fun i hi => (h3 i hi).2) gs.length {jo} T
      (by
        intro i hi
        rw [Finset.mem_singleton] at hi
        subst hi
        exact ⟨i.2, hjo⟩)
      (by
        intro j hj
        obtain ⟨a, b⟩ := (hTmem j).1 hj
        exact ⟨a, jo, Finset.mem_singleton_self _, b⟩)
    have hsub : Finset.univ.filter (fun m : Fin gs.length => kind m = 3 ∧ (m : ℕ) < gs.length)
        ⊆ Finset.univ.filter (fun i : Fin gs.length => kind i = 3) := by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, hm.2.1⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_singleton] at h
    omega
  have hN : (Finset.univ.filter (fun i : Fin gs.length => kind i = 0)).card
      + (Finset.univ.filter (fun i : Fin gs.length => kind i = 1)).card
      + (Finset.univ.filter (fun i : Fin gs.length => kind i = 2)).card
      + (Finset.univ.filter (fun i : Fin gs.length => kind i = 3)).card = gs.length := by
    have h := Finset.card_eq_sum_card_fiberwise (f := kind) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [Fin.sum_univ_four, Finset.card_univ, Fintype.card_fin] at h
    omega
  omega


open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)

theorem V_in (gs gs' : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
    V gs x w = V gs' x w := by
  unfold V
  rw [getD_wiresFrom _ _ _ h, getD_wiresFrom _ _ _ h]

theorem V_gate_some (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ)
    (h : V gs x (26 + i) = true) : ∃ g, gs[i]? = some g := by
  have hi : i < gs.length := by
    by_contra hi
    rw [V_out gs x (26 + i) (by rw [hx]; omega)] at h
    exact Bool.false_ne_true h
  exact ⟨gs[i], List.getElem?_eq_getElem hi⟩

theorem orN (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 26 + i) (hop : g.op = GateOp.or) :
    V gs x (26 + i) = true ↔ ∃ w ∈ g.inputs, V gs x w = true := by
  rw [gate_val_aux gs x hx i g hg hw, hop]
  simp [GateOp.eval]

theorem andN (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hw : ∀ w ∈ g.inputs, w < 26 + i) (hop : g.op = GateOp.and) :
    V gs x (26 + i) = true ↔ ∀ w ∈ g.inputs, V gs x w = true := by
  rw [gate_val_aux gs x hx i g hg hw, hop]
  simp [GateOp.eval]

def side0 (c : ℕ → ℕ) (w : ℕ) : Prop := w < 13 ∨ (26 ≤ w ∧ c (w - 26) = 0)

def side1 (c : ℕ → ℕ) (w : ℕ) : Prop := (13 ≤ w ∧ w < 26) ∨ (26 ≤ w ∧ c (w - 26) = 1)

def sideT (c : ℕ → ℕ) (w : ℕ) : Prop := 26 ≤ w ∧ (c (w - 26) = 2 ∨ c (w - 26) = 3)

def lowW (c : ℕ → ℕ) (w : ℕ) : Prop := w < 26 ∨ (26 ≤ w ∧ (c (w - 26) = 0 ∨ c (w - 26) = 1))

def newGate (c : ℕ → ℕ) (j : ℕ) (g : Gate) : Gate :=
  if c j = 0 then
    ⟨GateOp.or, g.inputs.filter (fun w => decide (w < 13 ∨ (26 ≤ w ∧ c (w - 26) = 0)))⟩
  else if c j = 1 then
    ⟨GateOp.or, g.inputs.filter (fun w => decide ((13 ≤ w ∧ w < 26) ∨ (26 ≤ w ∧ c (w - 26) = 1)))⟩
  else if c j = 2 then g
  else if c j = 3 then
    ⟨GateOp.or, g.inputs.filter (fun w => decide (26 ≤ w ∧ (c (w - 26) = 2 ∨ c (w - 26) = 3)))⟩
  else ⟨GateOp.or, []⟩

def newGates (c : ℕ → ℕ) (gs : List Gate) : List Gate := gs.mapIdx (fun j g => newGate c j g)

theorem newGates_len (c : ℕ → ℕ) (gs : List Gate) : (newGates c gs).length = gs.length := by
  simp [newGates]

theorem newGates_get (c : ℕ → ℕ) (gs : List Gate) (i : ℕ) (g : Gate) (hg : gs[i]? = some g) :
    (newGates c gs)[i]? = some (newGate c i g) := by
  simp [newGates, List.getElem?_mapIdx, hg]

theorem newGates_inv (c : ℕ → ℕ) (gs : List Gate) (i : ℕ) (g' : Gate)
    (hg : (newGates c gs)[i]? = some g') : ∃ g, gs[i]? = some g ∧ g' = newGate c i g := by
  have hi : i < gs.length := by
    have := (List.getElem?_eq_some_iff.1 hg).1
    rw [newGates_len] at this
    exact this
  refine ⟨gs[i], List.getElem?_eq_getElem hi, ?_⟩
  have h2 := newGates_get c gs i gs[i] (List.getElem?_eq_getElem hi)
  rw [hg] at h2
  exact Option.some.inj h2

theorem mem0 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : c i = 0) :
    w ∈ (newGate c i g).inputs ↔ w ∈ g.inputs ∧ side0 c w := by
  simp [newGate, h, side0]

theorem mem1 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : c i = 1) :
    w ∈ (newGate c i g).inputs ↔ w ∈ g.inputs ∧ side1 c w := by
  simp [newGate, h, side1]

theorem eq2 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : c i = 2) : newGate c i g = g := by
  simp [newGate, h]

theorem mem3 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : c i = 3) :
    w ∈ (newGate c i g).inputs ↔ w ∈ g.inputs ∧ sideT c w := by
  simp [newGate, h, sideT]

theorem eq4 (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : 4 ≤ c i) : newGate c i g = ⟨GateOp.or, []⟩ := by
  have h0 : c i ≠ 0 := by omega
  have h1 : c i ≠ 1 := by omega
  have h2 : c i ≠ 2 := by omega
  have h3 : c i ≠ 3 := by omega
  simp [newGate, h0, h1, h2, h3]

theorem newGate_or (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : c i ≠ 2) :
    (newGate c i g).op = GateOp.or := by
  unfold newGate
  split_ifs <;> rfl

theorem newGate_sub (c : ℕ → ℕ) (i : ℕ) (g : Gate) (w : ℕ) (h : w ∈ (newGate c i g).inputs) :
    w ∈ g.inputs := by
  unfold newGate at h
  split_ifs at h
  · exact (List.mem_filter.1 h).1
  · exact (List.mem_filter.1 h).1
  · exact h
  · exact (List.mem_filter.1 h).1
  · simp at h

theorem newGate_len (c : ℕ → ℕ) (i : ℕ) (g : Gate) :
    (newGate c i g).inputs.length ≤ g.inputs.length := by
  unfold newGate
  split_ifs
  · exact List.length_filter_le _ _
  · exact List.length_filter_le _ _
  · exact le_refl _
  · exact List.length_filter_le _ _
  · simp

def Hyp (gs : List Gate) (c : ℕ → ℕ) : Prop :=
  ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 ∧ ∀ w ∈ g.inputs, w < 26 + i) ∧
    (c i = 0 ∨ c i = 1 → g.op = GateOp.or ∧ ∀ w ∈ g.inputs, lowW c w) ∧
    (c i = 2 → g.op = GateOp.and ∧
      ∃ a b, (g.inputs = [a, b] ∨ g.inputs = [b, a]) ∧ side0 c a ∧ side1 c b) ∧
    (c i = 3 → g.op = GateOp.or) ∧
    (4 ≤ c i → g.op = GateOp.and ∧ (∀ w ∈ g.inputs, lowW c w) ∧
      ¬ ∃ a b, (g.inputs = [a, b] ∨ g.inputs = [b, a]) ∧ side0 c a ∧ side1 c b) ∧
    (c i = 1 → ∀ p : Fin 13, V gs (inp {p} ∅) (26 + i) = false) ∧
    (c i = 0 → ∀ l : Fin 13, V gs (inp ∅ {l}) (26 + i) = true →
      ∃ p : Fin 13, V gs (inp {p} ∅) (26 + i) = true)

theorem monoC (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c)
    (S R S' R' : Finset (Fin 13)) (hS : S ⊆ S') (hR : R ⊆ R') :
    ∀ w, V gs (inp S R) w = true → V gs (inp S' R') w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h13 : w < 13
    · rw [V_point gs _ _ w h13] at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      exact hS h
    by_cases h26 : w < 26
    · rw [V_line gs _ _ w (by omega) h26] at h ⊢
      simp only [decide_eq_true_eq] at h ⊢
      exact hR h
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨⟨ho, _, hb⟩, _⟩ := H j g hg
    rcases ho with ho | ho
    · rw [andN gs _ (inp_len _ _) j g hg hb ho] at h ⊢
      intro u hu
      exact ih u (hb u hu) (h u hu)
    · rw [orN gs _ (inp_len _ _) j g hg hb ho] at h ⊢
      obtain ⟨u, hu, hv⟩ := h
      exact ⟨u, hu, ih u (hb u hu) hv⟩

theorem dom (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (x : List Bool) (hx : x.length = 26) :
    ∀ w, V (newGates c gs) x w = true → V gs x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    by_cases h26 : w < 26
    · rw [V_in gs (newGates c gs) x w (by omega)]
      exact h
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    obtain ⟨g', hg'⟩ := V_gate_some _ x hx j h
    obtain ⟨g, hg, rfl⟩ := newGates_inv c gs j g' hg'
    obtain ⟨⟨ho, _, hb⟩, h01, h2, h3, h4, _⟩ := H j g hg
    have hbd : ∀ u ∈ (newGate c j g).inputs, u < 26 + j := fun u hu => hb u (newGate_sub c j g u hu)
    by_cases hc2 : c j = 2
    · have hand := (h2 hc2).1
      have e := eq2 c j g hc2
      rw [e] at hg'
      rw [andN _ x hx j g hg' hb hand] at h
      rw [andN gs x hx j g hg hb hand]
      intro u hu
      exact ih u (hb u hu) (h u hu)
    · rw [orN _ x hx j _ hg' hbd (newGate_or c j g hc2)] at h
      obtain ⟨u, hu, hv⟩ := h
      have hor : g.op = GateOp.or := by
        by_cases hc4 : 4 ≤ c j
        · rw [eq4 c j g hc4] at hu
          simp at hu
        · have : c j = 0 ∨ c j = 1 ∨ c j = 3 := by omega
          rcases this with h' | h' | h'
          · exact (h01 (Or.inl h')).1
          · exact (h01 (Or.inr h')).1
          · exact h3 h'
      rw [orN gs x hx j g hg hb hor]
      exact ⟨u, newGate_sub c j g u hu, ih u (hbd u hu) hv⟩

theorem lowP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13)
    (S R : Finset (Fin 13)) (hp : p ∈ S) :
    ∀ i, c i = 0 → V gs (inp {p} ∅) (26 + i) = true →
      V (newGates c gs) (inp S R) (26 + i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hc hv
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) i hv
    obtain ⟨⟨_, _, hb⟩, h01, _, _, _, _, _⟩ := H i g hg
    obtain ⟨hor, hlow⟩ := h01 (Or.inl hc)
    rw [orN gs _ (inp_len _ _) i g hg hb hor] at hv
    obtain ⟨w, hw, hvw⟩ := hv
    rw [orN _ _ (inp_len _ _) i _ (newGates_get c gs i g hg)
      (fun u hu => hb u (newGate_sub c i g u hu)) (newGate_or c i g (by omega))]
    have hbw := hb w hw
    rcases hlow w hw with h | ⟨h26, hcw⟩
    · by_cases h13 : w < 13
      · refine ⟨w, (mem0 c i g w hc).2 ⟨hw, Or.inl h13⟩, ?_⟩
        rw [V_point gs _ _ w h13] at hvw
        rw [V_point _ _ _ w h13]
        simp only [decide_eq_true_eq, Finset.mem_singleton] at hvw ⊢
        rw [hvw]; exact hp
      · rw [V_line gs _ _ w (by omega) h] at hvw
        simp at hvw
    · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
      rw [Nat.add_sub_cancel_left] at hcw
      rcases hcw with hcw | hcw
      · refine ⟨26 + j, (mem0 c i g _ hc).2 ⟨hw, Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hcw⟩⟩, ?_⟩
        exact ih j (by omega) hcw hvw
      · obtain ⟨gj, hgj⟩ := V_gate_some gs _ (inp_len _ _) j hvw
        obtain ⟨_, _, _, _, _, hs1, _⟩ := H j gj hgj
        rw [hs1 hcw p] at hvw
        exact absurd hvw Bool.false_ne_true

theorem lowL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13)
    (S R : Finset (Fin 13)) (hl : l ∈ R) :
    ∀ i, c i = 1 → V gs (inp ∅ {l}) (26 + i) = true →
      V (newGates c gs) (inp S R) (26 + i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hc hv
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) i hv
    obtain ⟨⟨_, _, hb⟩, h01, _, _, _, hs1i, _⟩ := H i g hg
    obtain ⟨hor, hlow⟩ := h01 (Or.inr hc)
    rw [orN gs _ (inp_len _ _) i g hg hb hor] at hv
    obtain ⟨w, hw, hvw⟩ := hv
    rw [orN _ _ (inp_len _ _) i _ (newGates_get c gs i g hg)
      (fun u hu => hb u (newGate_sub c i g u hu)) (newGate_or c i g (by omega))]
    have hbw := hb w hw
    rcases hlow w hw with h | ⟨h26, hcw⟩
    · by_cases h13 : w < 13
      · rw [V_point gs _ _ w h13] at hvw
        simp at hvw
      · refine ⟨w, (mem1 c i g w hc).2 ⟨hw, Or.inl ⟨by omega, h⟩⟩, ?_⟩
        rw [V_line gs _ _ w (by omega) h] at hvw
        rw [V_line _ _ _ w (by omega) h]
        simp only [decide_eq_true_eq, Finset.mem_singleton] at hvw ⊢
        rw [hvw]; exact hl
    · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
      rw [Nat.add_sub_cancel_left] at hcw
      rcases hcw with hcw | hcw
      · obtain ⟨gj, hgj⟩ := V_gate_some gs _ (inp_len _ _) j hvw
        obtain ⟨_, _, _, _, _, _, hs0⟩ := H j gj hgj
        obtain ⟨p0, hp0⟩ := hs0 hcw l hvw
        have hi : V gs (inp {p0} ∅) (26 + i) = true :=
          (orN gs _ (inp_len _ _) i g hg hb hor).2 ⟨26 + j, hw, hp0⟩
        rw [hs1i hc p0] at hi
        exact absurd hi Bool.false_ne_true
      · refine ⟨26 + j, (mem1 c i g _ hc).2 ⟨hw, Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hcw⟩⟩, ?_⟩
        exact ih j (by omega) hcw hvw

theorem addLow (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p l : Fin 13) :
    ∀ w, lowW c w → V gs (inp {p} {l}) w = true →
      V gs (inp {p} ∅) w = true ∨ V gs (inp ∅ {l}) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hlw hv
    by_cases h13 : w < 13
    · left
      rw [V_point gs _ _ w h13] at hv ⊢
      exact hv
    by_cases h26 : w < 26
    · right
      rw [V_line gs _ _ w (by omega) h26] at hv ⊢
      exact hv
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    have hcj : c j = 0 ∨ c j = 1 := by
      rcases hlw with h | ⟨_, h⟩
      · omega
      · rw [Nat.add_sub_cancel_left] at h; exact h
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j hv
    obtain ⟨⟨_, _, hb⟩, h01, _⟩ := H j g hg
    obtain ⟨hor, hlow⟩ := h01 hcj
    rw [orN gs _ (inp_len _ _) j g hg hb hor] at hv
    obtain ⟨u, hu, hvu⟩ := hv
    rcases ih u (hb u hu) (hlow u hu) hvu with h | h
    · left
      exact (orN gs _ (inp_len _ _) j g hg hb hor).2 ⟨u, hu, h⟩
    · right
      exact (orN gs _ (inp_len _ _) j g hg hb hor).2 ⟨u, hu, h⟩

def Q1 (d : Fin 13) : Finset (Fin 13) :=
  if d = 3 then {0, 2, 3, 4} else if d = 4 then {0, 1, 4, 6} else if d = 6 then {0, 1, 2, 6}
  else if d = 7 then {0, 1, 2, 7} else if d = 8 then {0, 1, 4, 8} else if d = 9 then {0, 2, 4, 9}
  else if d = 10 then {0, 1, 5, 10} else if d = 11 then {0, 1, 2, 11}
  else if d = 12 then {0, 1, 4, 12} else {0, 1, 2, 5}

def QP (p p' : Fin 13) : Finset (Fin 13) := (Q1 (p' - p)).image (fun q => q + p)

def Q2 (d : Fin 13) : Finset (Fin 13) :=
  if d = 1 then {5, 6, 7, 11} else if d = 2 then {4, 6, 7, 8} else if d = 3 then {2, 5, 7, 8}
  else if d = 4 then {2, 6, 8, 10} else if d = 5 then {2, 4, 7, 11} else if d = 6 then {4, 5, 8, 10}
  else if d = 8 then {2, 5, 6, 10} else if d = 9 then {2, 4, 6, 8} else if d = 10 then {2, 4, 5, 8}
  else if d = 12 then {4, 5, 6, 10} else {2, 4, 5, 6}

def QL (l l' : Fin 13) : Finset (Fin 13) := (Q2 (l' - l)).image (fun q => q + l)

theorem geoPP : ∀ p p' : Fin 13,
    (QP p p').card = 4 ∧
    (∀ k : Fin 13, ((QP p p').filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    p ∈ QP p p' ∧ p' ∈ QP p p' := by
  decide +kernel

theorem geoLL : ∀ l l' : Fin 13,
    (QL l l').card = 4 ∧
    (∀ k : Fin 13, ((QL l l').filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    l ∈ TQ (QL l l') ∧ l' ∈ TQ (QL l l') := by
  decide +kernel

def Bad (gs : List Gate) (w : ℕ) : Prop :=
  ∃ Q : Finset (Fin 13), Q.card = 4 ∧
    (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) ∧
    V gs (inp Q (TQ Q)) w = true

theorem badPP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p p' : Fin 13) (w : ℕ)
    (h : V gs (inp {p, p'} ∅) w = true) : Bad gs w := by
  obtain ⟨h1, h2, h3, h4⟩ := geoPP p p'
  refine ⟨QP p p', h1, h2, monoC gs c H _ _ _ _ ?_ (Finset.empty_subset _) w h⟩
  intro q hq
  rcases Finset.mem_insert.1 hq with rfl | hq
  · exact h3
  · rw [Finset.mem_singleton.1 hq]; exact h4

theorem badLL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l l' : Fin 13) (w : ℕ)
    (h : V gs (inp ∅ {l, l'}) w = true) : Bad gs w := by
  obtain ⟨h1, h2, h3, h4⟩ := geoLL l l'
  refine ⟨QL l l', h1, h2, monoC gs c H _ _ _ _ (Finset.empty_subset _) ?_ w h⟩
  intro q hq
  rcases Finset.mem_insert.1 hq with rfl | hq
  · exact h3
  · rw [Finset.mem_singleton.1 hq]; exact h4

theorem badP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13) (w : ℕ)
    (h : V gs (inp {p} ∅) w = true) : Bad gs w :=
  badPP gs c H p p w (monoC gs c H _ _ _ _ (by simp) (Finset.empty_subset _) w h)

theorem badL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13) (w : ℕ)
    (h : V gs (inp ∅ {l}) w = true) : Bad gs w :=
  badLL gs c H l l w (monoC gs c H _ _ _ _ (Finset.empty_subset _) (by simp) w h)

theorem firesP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13) (w : ℕ)
    (hl : lowW c w) (h : V gs (inp {p} ∅) w = true) : side0 c w := by
  by_cases h13 : w < 13
  · exact Or.inl h13
  by_cases h26 : w < 26
  · rw [V_line gs _ _ w (by omega) h26] at h
    simp at h
  obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
  rcases hl with hl | ⟨_, hl⟩
  · omega
  rw [Nat.add_sub_cancel_left] at hl
  rcases hl with hl | hl
  · exact Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hl⟩
  · obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨_, _, _, _, _, hs1, _⟩ := H j g hg
    rw [hs1 hl p] at h
    exact absurd h Bool.false_ne_true

theorem firesL (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13) (w : ℕ)
    (hl : lowW c w) (h : V gs (inp ∅ {l}) w = true) :
    side1 c w ∨ ∃ p0 : Fin 13, V gs (inp {p0} ∅) w = true := by
  by_cases h13 : w < 13
  · rw [V_point gs _ _ w h13] at h
    simp at h
  by_cases h26 : w < 26
  · exact Or.inl (Or.inl ⟨by omega, h26⟩)
  obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
  rcases hl with hl | ⟨_, hl⟩
  · omega
  rw [Nat.add_sub_cancel_left] at hl
  rcases hl with hl | hl
  · obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨_, _, _, _, _, _, hs0⟩ := H j g hg
    exact Or.inr (hs0 hl l h)
  · exact Or.inl (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hl⟩)

theorem side0D (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13)
    (S R : Finset (Fin 13)) (hp : p ∈ S) (w : ℕ) (hs : side0 c w)
    (h : V gs (inp {p} ∅) w = true) : V (newGates c gs) (inp S R) w = true := by
  rcases hs with h13 | ⟨h26, hc⟩
  · rw [V_point gs _ _ w h13] at h
    rw [V_point _ _ _ w h13]
    simp only [decide_eq_true_eq, Finset.mem_singleton] at h ⊢
    rw [h]; exact hp
  · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    rw [Nat.add_sub_cancel_left] at hc
    exact lowP gs c H p S R hp j hc h

theorem side1D (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (l : Fin 13)
    (S R : Finset (Fin 13)) (hl : l ∈ R) (w : ℕ) (hs : side1 c w)
    (h : V gs (inp ∅ {l}) w = true) : V (newGates c gs) (inp S R) w = true := by
  rcases hs with ⟨h13, h26⟩ | ⟨h26, hc⟩
  · rw [V_line gs _ _ w h13 h26] at h
    rw [V_line _ _ _ w h13 h26]
    simp only [decide_eq_true_eq, Finset.mem_singleton] at h ⊢
    rw [h]; exact hl
  · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    rw [Nat.add_sub_cancel_left] at hc
    exact lowL gs c H l S R hl j hc h

theorem side0_low (c : ℕ → ℕ) (w : ℕ) (h : side0 c w) : lowW c w := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨h, Or.inl h'⟩

theorem side1_low (c : ℕ → ℕ) (w : ℕ) (h : side1 c w) : lowW c w := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl h.2
  · exact Or.inr ⟨h, Or.inr h'⟩

theorem side1_noP (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p : Fin 13) (w : ℕ)
    (hs : side1 c w) (h : V gs (inp {p} ∅) w = true) : False := by
  rcases hs with ⟨h13, h26⟩ | ⟨h26, hc⟩
  · rw [V_line gs _ _ w h13 h26] at h
    simp at h
  · obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    rw [Nat.add_sub_cancel_left] at hc
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j h
    obtain ⟨_, _, _, _, _, hs1, _⟩ := H j g hg
    rw [hs1 hc p] at h
    exact absurd h Bool.false_ne_true


theorem top (gs : List Gate) (c : ℕ → ℕ) (H : Hyp gs c) (p l : Fin 13) :
    ∀ w, V gs (inp {p} {l}) w = true →
      (sideT c w ∧ V (newGates c gs) (inp {p} {l}) w = true) ∨ Bad gs w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    have hlowcase : lowW c w → Bad gs w := by
      intro hlw
      rcases addLow gs c H p l w hlw hv with h | h
      · exact badP gs c H p w h
      · exact badL gs c H l w h
    by_cases h26 : w < 26
    · exact Or.inr (hlowcase (Or.inl h26))
    obtain ⟨j, rfl⟩ : ∃ j, w = 26 + j := ⟨w - 26, by omega⟩
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) j hv
    obtain ⟨⟨ho, hlen, hb⟩, h01, h2, h3, h4, _⟩ := H j g hg
    have hgd := newGates_get c gs j g hg
    have hbd : ∀ u ∈ (newGate c j g).inputs, u < 26 + j := fun u hu => hb u (newGate_sub c j g u hu)
    have hsT : ∀ hh : c j = 2 ∨ c j = 3, sideT c (26 + j) := fun hh =>
      ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hh⟩
    by_cases hc01 : c j = 0 ∨ c j = 1
    · exact Or.inr (hlowcase (Or.inr ⟨by omega, by rw [Nat.add_sub_cancel_left]; exact hc01⟩))
    by_cases hc2 : c j = 2
    · obtain ⟨hand, a, b, hsh, ha, hbb⟩ := h2 hc2
      have hall := (andN gs _ (inp_len _ _) j g hg hb hand).1 hv
      have hma : a ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
      have hmb : b ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
      have hbl : V gs (inp ∅ {l}) b = true := by
        rcases addLow gs c H p l b (side1_low c b hbb) (hall b hmb) with h | h
        · exact (side1_noP gs c H p b hbb h).elim
        · exact h
      rcases addLow gs c H p l a (side0_low c a ha) (hall a hma) with h | h
      · left
        refine ⟨hsT (Or.inl hc2), ?_⟩
        have e := eq2 c j g hc2
        rw [e] at hgd
        rw [andN _ _ (inp_len _ _) j g hgd hb hand]
        intro u hu
        have hu' : u = a ∨ u = b := by
          rcases hsh with e | e
          · rw [e] at hu; simpa using hu
          · rw [e] at hu; simpa [or_comm] using hu
        rcases hu' with rfl | rfl
        · exact side0D gs c H p _ _ (by simp) _ ha h
        · exact side1D gs c H l _ _ (by simp) _ hbb hbl
      · right
        apply badL gs c H l
        rw [andN gs _ (inp_len _ _) j g hg hb hand]
        intro u hu
        have hu' : u = a ∨ u = b := by
          rcases hsh with e | e
          · rw [e] at hu; simpa using hu
          · rw [e] at hu; simpa [or_comm] using hu
        rcases hu' with rfl | rfl
        · exact h
        · exact hbl
    by_cases hc3 : c j = 3
    · have hor := h3 hc3
      obtain ⟨u, hu, hvu⟩ := (orN gs _ (inp_len _ _) j g hg hb hor).1 hv
      rcases ih u (hb u hu) hvu with ⟨hT, hd⟩ | ⟨Q, hQ1, hQ2, hQ3⟩
      · left
        refine ⟨hsT (Or.inr hc3), ?_⟩
        rw [orN _ _ (inp_len _ _) j _ hgd hbd (newGate_or c j g hc2)]
        exact ⟨u, (mem3 c j g u hc3).2 ⟨hu, hT⟩, hd⟩
      · right
        exact ⟨Q, hQ1, hQ2, (orN gs _ (inp_len _ _) j g hg hb hor).2 ⟨u, hu, hQ3⟩⟩
    have hc4 : 4 ≤ c j := by omega
    obtain ⟨hand, hlow, hnsh⟩ := h4 hc4
    have hall := (andN gs _ (inp_len _ _) j g hg hb hand).1 hv
    right
    have key : ∀ S R : Finset (Fin 13), (∀ u ∈ g.inputs, V gs (inp S R) u = true) →
        V gs (inp S R) (26 + j) = true := fun S R hh =>
      (andN gs _ (inp_len _ _) j g hg hb hand).2 hh
    have hsplit : ∀ u ∈ g.inputs, V gs (inp {p} ∅) u = true ∨ V gs (inp ∅ {l}) u = true :=
      fun u hu => addLow gs c H p l u (hlow u hu) (hall u hu)
    by_cases hallP : ∀ u ∈ g.inputs, V gs (inp {p} ∅) u = true
    · exact badP gs c H p _ (key _ _ hallP)
    by_cases hallL : ∀ u ∈ g.inputs, V gs (inp ∅ {l}) u = true
    · exact badL gs c H l _ (key _ _ hallL)

    obtain ⟨a, ha, haP⟩ : ∃ a ∈ g.inputs, V gs (inp {p} ∅) a = true ∧ ¬ V gs (inp ∅ {l}) a = true := by
      by_contra hne
      apply hallL
      intro u hu
      by_contra hul
      rcases hsplit u hu with h | h
      · exact hne ⟨u, hu, h, hul⟩
      · exact hul h
    obtain ⟨b, hbm, hbL⟩ : ∃ b ∈ g.inputs, V gs (inp ∅ {l}) b = true ∧ ¬ V gs (inp {p} ∅) b = true := by
      by_contra hne
      apply hallP
      intro u hu
      by_contra hup
      rcases hsplit u hu with h | h
      · exact hup h
      · exact hne ⟨u, hu, h, hup⟩
    have hab : a ≠ b := by
      rintro rfl
      exact hbL.2 haP.1
    have hshape : g.inputs = [a, b] ∨ g.inputs = [b, a] := by
      match hgi : g.inputs, hlen, ha, hbm with
      | [], _, ha', _ => simp at ha'
      | [u], _, ha', hb' =>
        simp at ha' hb'
        exact absurd (ha'.trans hb'.symm) hab
      | [u, v], _, ha', hb' =>
        simp at ha' hb'
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact absurd rfl hab
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd rfl hab
      | _ :: _ :: _ :: _, hl', _, _ => simp at hl'
    have hs0 := firesP gs c H p a (hlow a ha) haP.1
    rcases firesL gs c H l b (hlow b hbm) hbL.1 with hs1 | ⟨p0, hp0⟩
    · exact (hnsh ⟨a, b, hshape, hs0, hs1⟩).elim
    · apply badPP gs c H p p0
      apply key
      intro u hu
      have hu' : u = a ∨ u = b := by
        rcases hshape with e | e
        · rw [e] at hu; simpa using hu
        · rw [e] at hu; simpa [or_comm] using hu
      rcases hu' with rfl | rfl
      · exact monoC gs c H _ _ _ _ (by simp) (Finset.empty_subset _) _ haP.1
      · exact monoC gs c H _ _ _ _ (by simp) (Finset.empty_subset _) _ hp0

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h



theorem newGate_op (c : ℕ → ℕ) (i : ℕ) (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (newGate c i g).op = GateOp.and ∨ (newGate c i g).op = GateOp.or := by
  by_cases h2 : c i = 2
  · rw [eq2 c i g h2]; exact h
  · exact Or.inr (newGate_or c i g h2)

theorem core (gs : List Gate) (out : ℕ)
    (hmon : Monotone2 ⟨gs, out⟩) (hback : ReadsBack 26 ⟨gs, out⟩)
    (hnn : ¬ ∃ i j : ℕ, (gateAt ⟨gs, out⟩ i).op = GateOp.and ∧
      (gateAt ⟨gs, out⟩ j).op = GateOp.and ∧ InCone 26 ⟨gs, out⟩ i j)
    (hacc : ∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      V gs (inp {p} {l}) out = true)
    (hrej : ∀ Q : Finset (Fin 13), Q.card = 4 →
      (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
      V gs (inp Q (TQ Q)) out = false) : 64 ≤ gs.length := by
  classical
  have hgat : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → gateAt (⟨gs, out⟩ : Circuit) i = g := by
    intro i g hg
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hg
    exact gateAt_eq ⟨gs, out⟩ i hi
  have hG : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 ∧ ∀ w ∈ g.inputs, w < 26 + i := by
    intro i g hg
    have e := hgat i g hg
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hg
    have hm := hmon gs[i] (List.getElem_mem hi)
    refine ⟨by simpa using hm.1, hm.2, ?_⟩
    have hb := hback i hi
    rw [e] at hb
    exact hb
  obtain ⟨Top, hTop⟩ : ∃ Top : ℕ → Prop, ∀ j, Top j ↔
      ((gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∨
        ∃ k, (gateAt (⟨gs, out⟩ : Circuit) k).op = GateOp.and ∧ InCone 26 ⟨gs, out⟩ k j) :=
    ⟨_, fun j => Iff.rfl⟩
  have hread : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → ∀ w ∈ g.inputs, 26 ≤ w → Top (w - 26) →
      ∃ k, (gateAt (⟨gs, out⟩ : Circuit) k).op = GateOp.and ∧ InCone 26 ⟨gs, out⟩ k j := by
    intro j g hg w hw h26 hT
    have hj : j < gs.length := (List.getElem?_eq_some_iff.1 hg).1
    have hbw := (hG j g hg).2.2 w hw
    have hw' : w ∈ (gateAt (⟨gs, out⟩ : Circuit) j).inputs := by rw [hgat j g hg]; exact hw
    rcases (hTop _).1 hT with h | ⟨k, hk, hkc⟩
    · exact ⟨w - 26, h, (inCone_iff 26 ⟨gs, out⟩ _ j hj).2 ⟨w, hw', h26, hbw, Or.inl rfl⟩⟩
    · exact ⟨k, hk, (inCone_iff 26 ⟨gs, out⟩ _ j hj).2 ⟨w, hw', h26, hbw, Or.inr hkc⟩⟩
  have hreadA : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ w ∈ g.inputs, 26 ≤ w →
      ¬ Top (w - 26) := by
    intro j g hg hop w hw h26 hT
    obtain ⟨k, hk, hkc⟩ := hread j g hg w hw h26 hT
    exact hnn ⟨k, j, hk, by rw [hgat j g hg]; exact hop, hkc⟩
  have hsex : ∀ j : ℕ, ∃ v : ℕ,
      (v = 1 ∧ (∀ p : Fin 13, V gs (inp {p} ∅) (26 + j) = false) ∧
        ∃ l : Fin 13, V gs (inp ∅ {l}) (26 + j) = true) ∨
      (v = 0 ∧ ¬ ((∀ p : Fin 13, V gs (inp {p} ∅) (26 + j) = false) ∧
        ∃ l : Fin 13, V gs (inp ∅ {l}) (26 + j) = true)) := by
    intro j
    by_cases h : ((∀ p : Fin 13, V gs (inp {p} ∅) (26 + j) = false) ∧
        ∃ l : Fin 13, V gs (inp ∅ {l}) (26 + j) = true)
    · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨0, Or.inr ⟨rfl, h⟩⟩
  choose s hs using hsex
  have hs01 : ∀ j, s j = 0 ∨ s j = 1 := by
    intro j
    rcases hs j with h | h
    · exact Or.inr h.1
    · exact Or.inl h.1
  obtain ⟨shape, hshape⟩ : ∃ shape : ℕ → Prop, ∀ j, shape j ↔
      ∃ a b, ((gateAt (⟨gs, out⟩ : Circuit) j).inputs = [a, b] ∨
        (gateAt (⟨gs, out⟩ : Circuit) j).inputs = [b, a]) ∧ side0 s a ∧ side1 s b :=
    ⟨_, fun j => Iff.rfl⟩
  have hcex : ∀ j : ℕ, ∃ v : ℕ,
      (¬ Top j ∧ v = s j) ∨
      (Top j ∧ (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∧ shape j ∧ v = 2) ∨
      (Top j ∧ (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∧ ¬ shape j ∧ v = 4) ∨
      (Top j ∧ ¬ (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and ∧ v = 3) := by
    intro j
    by_cases hT : Top j
    · by_cases ha : (gateAt (⟨gs, out⟩ : Circuit) j).op = GateOp.and
      · by_cases hsj : shape j
        · exact ⟨2, Or.inr (Or.inl ⟨hT, ha, hsj, rfl⟩)⟩
        · exact ⟨4, Or.inr (Or.inr (Or.inl ⟨hT, ha, hsj, rfl⟩))⟩
      · exact ⟨3, Or.inr (Or.inr (Or.inr ⟨hT, ha, rfl⟩))⟩
    · exact ⟨s j, Or.inl ⟨hT, rfl⟩⟩
  choose c hc using hcex
  have hcs : ∀ j, ¬ Top j → c j = s j := by
    intro j hT
    rcases hc j with h | h | h | h
    · exact h.2
    · exact absurd h.1 hT
    · exact absurd h.1 hT
    · exact absurd h.1 hT

  have tr0 : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ a ∈ g.inputs,
      (side0 s a ↔ side0 c a) := by
    intro j g hg hop a ha
    unfold side0
    constructor
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [← hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
  have tr1 : ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = GateOp.and → ∀ a ∈ g.inputs,
      (side1 s a ↔ side1 c a) := by
    intro j g hg hop a ha
    unfold side1
    constructor
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
    · rintro (h | ⟨h26, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h26, by rw [← hcs _ (hreadA j g hg hop a ha h26)]; exact e⟩
  have H : Hyp gs c := by
    intro i g hg
    have hga := hgat i g hg
    have hs01i := hs01 i
    refine ⟨hG i g hg, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h01
      have hnT : ¬ Top i := by
        intro hT
        rcases hc i with h | h | h | h
        · exact h.1 hT
        · obtain ⟨_, _, _, e⟩ := h; omega
        · obtain ⟨_, _, _, e⟩ := h; omega
        · obtain ⟨_, _, e⟩ := h; omega
      have hor : g.op = GateOp.or := by
        rcases (hG i g hg).1 with h | h
        · exact absurd ((hTop i).2 (Or.inl (by rw [hga]; exact h))) hnT
        · exact h
      refine ⟨hor, fun w hw => ?_⟩
      by_cases h26 : w < 26
      · exact Or.inl h26
      · have hnTw : ¬ Top (w - 26) := fun hT =>
          hnT ((hTop i).2 (Or.inr (hread i g hg w hw (by omega) hT)))
        refine Or.inr ⟨by omega, ?_⟩
        rw [hcs _ hnTw]
        exact hs01 _
    · intro h2
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h; omega
      · obtain ⟨_, hand, hsh, _⟩ := h
        rw [hga] at hand
        obtain ⟨a, b, hab, ha, hb⟩ := (hshape i).1 hsh
        rw [hga] at hab
        have hma : a ∈ g.inputs := by rcases hab with e | e <;> simp [e]
        have hmb : b ∈ g.inputs := by rcases hab with e | e <;> simp [e]
        exact ⟨hand, a, b, hab, (tr0 i g hg hand a hma).1 ha, (tr1 i g hg hand b hmb).1 hb⟩
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, e⟩ := h; omega
    · intro h3
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, hna, _⟩ := h
        rw [hga] at hna
        rcases (hG i g hg).1 with h' | h'
        · exact absurd h' hna
        · exact h'
    · intro h4
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, hand, hnsh, _⟩ := h
        rw [hga] at hand
        refine ⟨hand, fun w hw => ?_, ?_⟩
        · by_cases h26 : w < 26
          · exact Or.inl h26
          · refine Or.inr ⟨by omega, ?_⟩
            rw [hcs _ (hreadA i g hg hand w hw (by omega))]
            exact hs01 _
        · rintro ⟨a, b, hab, ha, hb⟩
          apply hnsh
          have hma : a ∈ g.inputs := by rcases hab with e | e <;> simp [e]
          have hmb : b ∈ g.inputs := by rcases hab with e | e <;> simp [e]
          exact (hshape i).2 ⟨a, b, by rw [hga]; exact hab,
            (tr0 i g hg hand a hma).2 ha, (tr1 i g hg hand b hmb).2 hb⟩
      · obtain ⟨_, _, e⟩ := h; omega
    · intro h1 p
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h
        rcases hs i with h' | h'
        · exact h'.2.1 p
        · obtain ⟨e', _⟩ := h'; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, e⟩ := h; omega
    · intro h0 l hl
      rcases hc i with h | h | h | h
      · obtain ⟨_, e⟩ := h
        rcases hs i with h' | h'
        · obtain ⟨e', _⟩ := h'; omega
        · by_contra hne
          apply h'.2
          refine ⟨fun p => ?_, l, hl⟩
          by_contra hp
          exact hne ⟨p, by simpa using hp⟩
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, _, e⟩ := h; omega
      · obtain ⟨_, _, e⟩ := h; omega
  have h00 : V gs (inp {0} {0}) out = true := hacc 0 0 (by decide)
  have hBadOut : ¬ Bad gs out := by
    rintro ⟨Q, h1, h2, h3⟩
    rw [hrej Q h1 h2] at h3
    exact Bool.false_ne_true h3
  have hT0 : sideT c out := by
    rcases top gs c H 0 0 out h00 with ⟨h, _⟩ | h
    · exact h
    · exact absurd h hBadOut
  obtain ⟨h26, hco⟩ := hT0
  obtain ⟨jo, rfl⟩ : ∃ j, out = 26 + j := ⟨out - 26, by omega⟩
  rw [Nat.add_sub_cancel_left] at hco
  have hjo : jo < gs.length := by
    obtain ⟨g, hg⟩ := V_gate_some gs _ (inp_len _ _) jo h00
    exact (List.getElem?_eq_some_iff.1 hg).1
  have hkex : ∀ i : ℕ, ∃ v : Fin 4, (c i = 1 ∧ v = 1) ∨ (c i = 2 ∧ v = 2) ∨ (c i = 3 ∧ v = 3) ∨
      (c i ≠ 1 ∧ c i ≠ 2 ∧ c i ≠ 3 ∧ v = 0) := by
    intro i
    by_cases h1 : c i = 1
    · exact ⟨1, Or.inl ⟨h1, rfl⟩⟩
    by_cases h2 : c i = 2
    · exact ⟨2, Or.inr (Or.inl ⟨h2, rfl⟩)⟩
    by_cases h3 : c i = 3
    · exact ⟨3, Or.inr (Or.inr (Or.inl ⟨h3, rfl⟩))⟩
    exact ⟨0, Or.inr (Or.inr (Or.inr ⟨h1, h2, h3, rfl⟩))⟩
  choose kd hkd using hkex
  have k0 : ∀ i, kd i = 0 ↔ (c i = 0 ∨ 4 ≤ c i) := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have k1 : ∀ i, kd i = 1 ↔ c i = 1 := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have k2 : ∀ i, kd i = 2 ↔ c i = 2 := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have k3 : ∀ i, kd i = 3 ↔ c i = 3 := by
    intro i
    rcases hkd i with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, e⟩ | ⟨h1, h2, h3, e⟩ <;> rw [e] <;> constructor <;>
      intro hh <;> first | exact absurd hh (by decide) | rfl | omega
  have hlenD := newGates_len c gs
  have hD : ∀ i : Fin (newGates c gs).length,
      ∃ g, gs[(i : ℕ)]? = some g ∧ (newGates c gs).get i = newGate c i g := by
    intro i
    exact newGates_inv c gs i _ (by simp)
  have toFin : ∀ (i : Fin (newGates c gs).length) (w : ℕ), w < 26 + (i : ℕ) → 26 ≤ w →
      ∀ P : Fin 4 → Prop, P (kd (w - 26)) →
      ∃ j : Fin (newGates c gs).length, w = 26 + (j : ℕ) ∧ P (kd j) := by
    intro i w hw h26 P hP
    have hi := i.2
    refine ⟨⟨w - 26, by omega⟩, ?_, hP⟩
    show w = 26 + (w - 26)
    omega
  have hfin : 64 ≤ (newGates c gs).length → 64 ≤ gs.length := fun h => by rw [hlenD] at h; exact h
  apply hfin
  refine main (newGates c gs) (fun i => kd i) ⟨jo, by rw [hlenD]; exact hjo⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨g0, hg0, e⟩ := newGates_inv c gs i _ (List.getElem?_eq_getElem hi)
    rw [e]
    obtain ⟨⟨ho, hl, _⟩, _⟩ := H i g0 hg0
    exact ⟨newGate_op c i g0 ho, le_trans (newGate_len c i g0) hl⟩
  · intro i w hw
    obtain ⟨g, hg, e⟩ := hD i
    rw [e] at hw
    exact (H i g hg).1.2.2 w (newGate_sub c i g w hw)
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    rcases (k0 i).1 hk with h | h
    · refine ⟨newGate_or c i g (by omega), fun w hw => ?_⟩
      obtain ⟨hw1, hw2⟩ := (mem0 c i g w h).1 hw
      rcases hw2 with h13 | ⟨h26, hcw⟩
      · exact Or.inl h13
      · exact Or.inr (toFin i w ((H i g hg).1.2.2 w hw1) h26 (fun v => v = 0)
          ((k0 _).2 (Or.inl hcw)))
    · rw [eq4 c i g h]
      exact ⟨rfl, fun w hw => by simp at hw⟩
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    have h := (k1 i).1 hk
    refine ⟨newGate_or c i g (by omega), fun w hw => ?_⟩
    obtain ⟨hw1, hw2⟩ := (mem1 c i g w h).1 hw
    rcases hw2 with h13 | ⟨h26, hcw⟩
    · exact Or.inl h13
    · exact Or.inr (toFin i w ((H i g hg).1.2.2 w hw1) h26 (fun v => v = 1) ((k1 _).2 hcw))
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    have h := (k2 i).1 hk
    rw [eq2 c i g h]
    obtain ⟨hand, a, b, hsh, ha, hb⟩ := (H i g hg).2.2.1 h
    have hma : a ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
    have hmb : b ∈ g.inputs := by rcases hsh with e | e <;> simp [e]
    refine ⟨hand, a, b, hsh, ?_, ?_⟩
    · rcases ha with h13 | ⟨h26, hcw⟩
      · exact Or.inl h13
      · exact Or.inr (toFin i a ((H i g hg).1.2.2 a hma) h26 (fun v => v = 0)
          ((k0 _).2 (Or.inl hcw)))
    · rcases hb with h13 | ⟨h26, hcw⟩
      · exact Or.inl h13
      · exact Or.inr (toFin i b ((H i g hg).1.2.2 b hmb) h26 (fun v => v = 1) ((k1 _).2 hcw))
  · intro i hk
    obtain ⟨g, hg, e⟩ := hD i
    rw [e]
    have h := (k3 i).1 hk
    refine ⟨newGate_or c i g (by omega), fun w hw => ?_⟩
    obtain ⟨hw1, h26, hcw⟩ := (mem3 c i g w h).1 hw
    refine toFin i w ((H i g hg).1.2.2 w hw1) h26 (fun v => v = 2 ∨ v = 3) ?_
    rcases hcw with hcw | hcw
    · exact Or.inl ((k2 _).2 hcw)
    · exact Or.inr ((k3 _).2 hcw)
  · rcases hco with hco | hco
    · exact Or.inl ((k2 _).2 hco)
    · exact Or.inr ((k3 _).2 hco)
  · intro p l hpl
    rcases top gs c H p l _ (hacc p l hpl) with ⟨_, h⟩ | h
    · exact h
    · exact absurd h hBadOut
  · intro Q h1 h2
    by_contra hne
    have ht : V (newGates c gs) (inp Q (TQ Q)) (26 + jo) = true := by simpa using hne
    have h3 := dom gs c H _ (inp_len _ _) _ ht
    rw [hrej Q h1 h2] at h3
    exact Bool.false_ne_true h3

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wf_append (pre post : List Gate) (w : List Bool) :
    wf (pre ++ post) w = wf post (wf pre w) := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma clean_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma clean_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

def sk (N i : ℕ) : ℕ := if i < N then i else i - 1

def rn (N a i : ℕ) : ℕ := if i < N then i else if i = N then a else i - 1

theorem sk_lt (N M i : ℕ) (hN0 : 0 < N) (hM : N ≤ M) (hi : i < M + 1) : sk N i < M := by
  unfold sk
  split_ifs <;> omega

theorem getD_mid (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) :
    (A ++ b :: E).getD N false = b := by
  subst hN
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl A.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem getD_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (i : ℕ) (hi : i ≠ N) :
    (A ++ E).getD (sk N i) false = (A ++ b :: E).getD i false := by
  subst hN
  unfold sk
  by_cases h : i < A.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    have h1 : A.length ≤ i - 1 := by omega
    have h2 : A.length ≤ i := by omega
    have h3 : i - A.length = (i - 1 - A.length) + 1 := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
      List.getElem?_append_right h2]
    rw [h3, List.getElem?_cons_succ]

theorem getD_rn (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (i : ℕ) :
    (A ++ E).getD (rn N a i) false = (A ++ b :: E).getD i false := by
  by_cases h : i = N
  · have e : rn N a N = a := by
      unfold rn
      rw [if_neg (lt_irrefl _), if_pos rfl]
    have ha' : a < A.length := by omega
    rw [h, getD_mid A E b N hN, e, ← hb]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha']
  · have e : rn N a i = sk N i := by
      unfold rn sk
      by_cases h' : i < N
      · rw [if_pos h', if_pos h']
      · rw [if_neg h', if_neg h, if_neg h']
    rw [e]
    exact getD_sk A E b N hN i h

theorem surg (T : Gate → Gate) (A : List Bool) (b : Bool) :
    ∀ (post : List Gate) (E : List Bool),
      (∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (A ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (A ++ E').getD i false)) →
      ∃ E2 : List Bool, wf post (A ++ b :: E) = A ++ b :: E2 ∧
        wf (post.map T) (A ++ E) = A ++ E2 := by
  intro post
  induction post with
  | nil => intro E _; exact ⟨E, rfl, rfl⟩
  | cons h post ih =>
    intro E hT
    have e := hT h (List.mem_cons.mpr (Or.inl rfl)) E
    obtain ⟨E2, h1, h2⟩ :=
      ih (E ++ [h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)])
        (fun h' hh' E' => hT h' (List.mem_cons.mpr (Or.inr hh')) E')
    refine ⟨E2, ?_, ?_⟩
    · rw [wf_cons, List.append_assoc, List.cons_append]
      exact h1
    · rw [List.map_cons, wf_cons, ← e, List.append_assoc]
      exact h2

theorem ev (pre post : List Gate) (g : Gate) (T : Gate → Gate) (x : List Bool) (b : Bool)
    (hb : g.op.eval (g.inputs.map fun i => (wf pre x).getD i false) = b)
    (hT : ∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (wf pre x ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (wf pre x ++ E').getD i false)) :
    ∃ E2 : List Bool, wf (pre ++ g :: post) x = wf pre x ++ b :: E2 ∧
      wf (pre ++ post.map T) x = wf pre x ++ E2 := by
  obtain ⟨E2, h1, h2⟩ := surg T (wf pre x) b post [] hT
  rw [List.append_nil] at h2
  refine ⟨E2, ?_, ?_⟩
  · rw [wf_append, wf_cons, hb]
    exact h1
  · rw [wf_append]
    exact h2

def Tc (N a : ℕ) (h : Gate) : Gate := ⟨h.op, h.inputs.map (rn N a)⟩

def Tt (N : ℕ) (h : Gate) : Gate :=
  match h.op with
  | GateOp.and => ⟨GateOp.and, (h.inputs.filter (fun i => decide (i ≠ N))).map (sk N)⟩
  | _ => if N ∈ h.inputs then ⟨GateOp.and, []⟩ else ⟨h.op, h.inputs.map (sk N)⟩

def Tf (N : ℕ) (h : Gate) : Gate :=
  match h.op with
  | GateOp.or => ⟨GateOp.or, (h.inputs.filter (fun i => decide (i ≠ N))).map (sk N)⟩
  | _ => if N ∈ h.inputs then ⟨GateOp.or, []⟩ else ⟨h.op, h.inputs.map (sk N)⟩

theorem Tt_and (N : ℕ) (ins : List ℕ) : Tt N ⟨GateOp.and, ins⟩
    = ⟨GateOp.and, (ins.filter (fun i => decide (i ≠ N))).map (sk N)⟩ := rfl

theorem Tt_or (N : ℕ) (ins : List ℕ) : Tt N ⟨GateOp.or, ins⟩
    = if N ∈ ins then ⟨GateOp.and, []⟩ else ⟨GateOp.or, ins.map (sk N)⟩ := rfl

theorem Tf_or (N : ℕ) (ins : List ℕ) : Tf N ⟨GateOp.or, ins⟩
    = ⟨GateOp.or, (ins.filter (fun i => decide (i ≠ N))).map (sk N)⟩ := rfl

theorem Tf_and (N : ℕ) (ins : List ℕ) : Tf N ⟨GateOp.and, ins⟩
    = if N ∈ ins then ⟨GateOp.or, []⟩ else ⟨GateOp.and, ins.map (sk N)⟩ := rfl

theorem map_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (ins : List ℕ)
    (hni : N ∉ ins) :
    (ins.map (sk N)).map (fun i => (A ++ E).getD i false)
      = ins.map (fun i => (A ++ b :: E).getD i false) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  exact getD_sk A E b N hN i (fun e => hni (by rw [← e]; exact hi))

theorem all_drop (f : ℕ → Bool) (N : ℕ) (hf : f N = true) : ∀ ins : List ℕ,
    (ins.map f).all id = ((ins.filter (fun i => decide (i ≠ N))).map f).all id := by
  intro ins
  induction ins with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : i = N
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_neg (by simp [h])
      rw [e, ← ih, List.map_cons, List.all_cons, h]
      simp [hf]
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = i :: rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.all_cons, ih]

theorem any_drop (f : ℕ → Bool) (N : ℕ) (hf : f N = false) : ∀ ins : List ℕ,
    (ins.map f).any id = ((ins.filter (fun i => decide (i ≠ N))).map f).any id := by
  intro ins
  induction ins with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : i = N
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_neg (by simp [h])
      rw [e, ← ih, List.map_cons, List.any_cons, h]
      simp [hf]
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = i :: rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.any_cons, ih]

theorem sound_c (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (h : Gate) :
    h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
      = (Tc N a h).op.eval ((Tc N a h).inputs.map fun i => (A ++ E).getD i false) := by
  have e : (h.inputs.map (rn N a)).map (fun i => (A ++ E).getD i false)
      = h.inputs.map fun i => (A ++ b :: E).getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact getD_rn A E b N hN a ha hb i
  show h.op.eval _ = h.op.eval ((h.inputs.map (rn N a)).map fun i => (A ++ E).getD i false)
  rw [e]

theorem sound_t (A E : List Bool) (N : ℕ) (hN : A.length = N) (h : Gate)
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or) :
    h.op.eval (h.inputs.map fun i => (A ++ true :: E).getD i false)
      = (Tt N h).op.eval ((Tt N h).inputs.map fun i => (A ++ E).getD i false) := by
  obtain ⟨op, ins⟩ := h
  have hf : (A ++ true :: E).getD N false = true := getD_mid A E true N hN
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    show (ins.map fun i => (A ++ true :: E).getD i false).all id
      = (((ins.filter (fun i => decide (i ≠ N))).map (sk N)).map
          fun i => (A ++ E).getD i false).all id
    rw [map_sk A E true N hN (ins.filter (fun i => decide (i ≠ N))) (by simp)]
    exact all_drop _ N hf ins
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      show (ins.map fun i => (A ++ true :: E).getD i false).any id = true
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨N, hm, rfl⟩, hf⟩
    · rw [if_neg hm]
      show (ins.map fun i => (A ++ true :: E).getD i false).any id
        = ((ins.map (sk N)).map fun i => (A ++ E).getD i false).any id
      rw [map_sk A E true N hN ins hm]

theorem sound_f (A E : List Bool) (N : ℕ) (hN : A.length = N) (h : Gate)
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or) :
    h.op.eval (h.inputs.map fun i => (A ++ false :: E).getD i false)
      = (Tf N h).op.eval ((Tf N h).inputs.map fun i => (A ++ E).getD i false) := by
  obtain ⟨op, ins⟩ := h
  have hf : (A ++ false :: E).getD N false = false := getD_mid A E false N hN
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      show (ins.map fun i => (A ++ false :: E).getD i false).all id = false
      cases hall : (ins.map fun i => (A ++ false :: E).getD i false).all id with
      | false => rfl
      | true =>
        have t := List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨N, hm, rfl⟩)
        have t2 : (A ++ false :: E).getD N false = true := t
        rw [hf] at t2
        exact Bool.noConfusion t2
    · rw [if_neg hm]
      show (ins.map fun i => (A ++ false :: E).getD i false).all id
        = ((ins.map (sk N)).map fun i => (A ++ E).getD i false).all id
      rw [map_sk A E false N hN ins hm]
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    show (ins.map fun i => (A ++ false :: E).getD i false).any id
      = (((ins.filter (fun i => decide (i ≠ N))).map (sk N)).map
          fun i => (A ++ E).getD i false).any id
    rw [map_sk A E false N hN (ins.filter (fun i => decide (i ≠ N))) (by simp)]
    exact any_drop _ N hf ins

theorem Tc_legal (N a : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tc N a h).op = GateOp.and ∨ (Tc N a h).op = GateOp.or) ∧ (Tc N a h).inputs.length ≤ 2 := by
  refine ⟨hl.1, ?_⟩
  show (h.inputs.map (rn N a)).length ≤ 2
  rw [List.length_map]
  exact hl.2

theorem Tc_rb (N a : ℕ) (ha : a < N) (h : Gate) (M : ℕ) (hM : N ≤ M)
    (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tc N a h).inputs, i < M := by
  intro i hi'
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
  have := hi j hj
  unfold rn
  split_ifs <;> omega

theorem Tt_legal (N : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tt N h).op = GateOp.and ∨ (Tt N h).op = GateOp.or) ∧ (Tt N h).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := h
  obtain ⟨hop, hlen⟩ := hl
  have hlen' : ins.length ≤ 2 := hlen
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    refine ⟨Or.inl rfl, ?_⟩
    show ((ins.filter (fun i => decide (i ≠ N))).map (sk N)).length ≤ 2
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) hlen'
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      exact ⟨Or.inl rfl, Nat.zero_le 2⟩
    · rw [if_neg hm]
      refine ⟨Or.inr rfl, ?_⟩
      show (ins.map (sk N)).length ≤ 2
      rw [List.length_map]
      exact hlen'

theorem Tf_legal (N : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tf N h).op = GateOp.and ∨ (Tf N h).op = GateOp.or) ∧ (Tf N h).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := h
  obtain ⟨hop, hlen⟩ := hl
  have hlen' : ins.length ≤ 2 := hlen
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      exact ⟨Or.inr rfl, Nat.zero_le 2⟩
    · rw [if_neg hm]
      refine ⟨Or.inl rfl, ?_⟩
      show (ins.map (sk N)).length ≤ 2
      rw [List.length_map]
      exact hlen'
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    refine ⟨Or.inr rfl, ?_⟩
    show ((ins.filter (fun i => decide (i ≠ N))).map (sk N)).length ≤ 2
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) hlen'

theorem Tt_rb (N : ℕ) (hN0 : 0 < N) (h : Gate) (hop : h.op = GateOp.and ∨ h.op = GateOp.or)
    (M : ℕ) (hM : N ≤ M) (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tt N h).inputs, i < M := by
  obtain ⟨op, ins⟩ := h
  have hi2 : ∀ i ∈ ins, i < M + 1 := hi
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    intro i hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    exact sk_lt N M j hN0 hM (hi2 j (List.mem_filter.mp hj).1)
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      intro i hi'
      exact absurd hi' List.not_mem_nil
    · rw [if_neg hm]
      intro i hi'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
      exact sk_lt N M j hN0 hM (hi2 j hj)

theorem Tf_rb (N : ℕ) (hN0 : 0 < N) (h : Gate) (hop : h.op = GateOp.and ∨ h.op = GateOp.or)
    (M : ℕ) (hM : N ≤ M) (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tf N h).inputs, i < M := by
  obtain ⟨op, ins⟩ := h
  have hi2 : ∀ i ∈ ins, i < M + 1 := hi
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      intro i hi'
      exact absurd hi' List.not_mem_nil
    · rw [if_neg hm]
      intro i hi'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
      exact sk_lt N M j hN0 hM (hi2 j hj)
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    intro i hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    exact sk_lt N M j hN0 hM (hi2 j (List.mem_filter.mp hj).1)

theorem assemble (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : C.gates = pre ++ g :: post) (T : Gate → Gate) (o' : ℕ)
    (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, 26 + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M)
    (hev : ∀ x : List Bool, x.length = 26 →
      Circuit.eval ⟨pre ++ post.map T, o'⟩ x = C.eval x) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  have legal := legal_of C hmono
  refine ⟨⟨pre ++ post.map T, o'⟩, ?_, ?_, hev, ?_⟩
  · intro g' hg'
    have hg2 : g' ∈ pre ∨ g' ∈ post.map T := List.mem_append.mp hg'
    rcases hg2 with hp | hp
    · exact hmono g' (by rw [hC]; exact List.mem_append.mpr (Or.inl hp))
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      have hl := hTm h (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh)))))
      refine ⟨?_, hl.2⟩
      rcases hl.1 with e | e
      · exact Or.inl e
      · exact Or.inr e
  · intro j hj i hi
    have hj' : j < pre.length + post.length := by simpa using hj
    by_cases hjp : j < pre.length
    · have e : gateAt ⟨pre ++ post.map T, o'⟩ j = gateAt C j := by
        simp only [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
      rw [e] at hi
      exact hrb j (by rw [hC]; simp only [List.length_append, List.length_cons]; omega) i hi
    · have hjk : j - pre.length < post.length := by omega
      have e1 : gateAt ⟨pre ++ post.map T, o'⟩ j = T (post[j - pre.length]) := by
        simp [gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_of_not_lt hjp), hjk]
      have e2 : gateAt C (j + 1) = post[j - pre.length] := by
        have h3 : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ j + 1 by omega), h3, hjk]
      rw [e1] at hi
      have hmem : post[j - pre.length] ∈ C.gates := by
        rw [hC]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.getElem_mem hjk))))
      have hold : ∀ i ∈ (post[j - pre.length]).inputs, i < (26 + j) + 1 := by
        intro i hi2
        have := hrb (j + 1) (by rw [hC]; simp only [List.length_append, List.length_cons]; omega)
          i (by rw [e2]; exact hi2)
        omega
      exact hTr _ (legal _ hmem) (26 + j) (by omega) hold i hi
  · show (pre ++ post.map T).length < C.gates.length
    rw [hC]
    simp

theorem copy_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post) (a : ℕ)
    (ha : a < 26 + pre.length)
    (hb : ∀ A : List Bool, g.op.eval (g.inputs.map fun i => A.getD i false) = A.getD a false) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  apply assemble C pre post g hC (Tc (26 + pre.length) a) (rn (26 + pre.length) a C.output)
    hmono hrb
  · intro h hl
    exact Tc_legal _ _ h hl
  · intro h _ M hM hi
    exact Tc_rb _ _ ha h M hM hi
  · intro x hx
    have hlen : (wf pre x).length = 26 + pre.length := by rw [wf_len, hx]
    obtain ⟨E2, h1, h2⟩ := ev pre post g (Tc (26 + pre.length) a) x _ (hb (wf pre x))
      (fun h _ E' => sound_c (wf pre x) E' _ (26 + pre.length) hlen a ha rfl h)
    show (wf (pre ++ post.map (Tc (26 + pre.length) a)) x).getD
        (rn (26 + pre.length) a C.output) false = (wf C.gates x).getD C.output false
    rw [h2, hC, h1]
    exact getD_rn (wf pre x) E2 _ (26 + pre.length) hlen a ha rfl C.output

theorem const_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post) (T : Gate → Gate)
    (b : Bool)
    (hb : ∀ A : List Bool, g.op.eval (g.inputs.map fun i => A.getD i false) = b)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, 26 + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M)
    (hs : ∀ h : Gate, (h.op = GateOp.and ∨ h.op = GateOp.or) → ∀ (A E : List Bool),
      A.length = 26 + pre.length →
      h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
        = (T h).op.eval ((T h).inputs.map fun i => (A ++ E).getD i false))
    (hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
      C.eval y = false) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  have legal := legal_of C hmono
  have key : ∀ x : List Bool, x.length = 26 → ∃ E2 : List Bool,
      wf C.gates x = wf pre x ++ b :: E2 ∧ wf (pre ++ post.map T) x = wf pre x ++ E2 := by
    intro x hx
    have hlen : (wf pre x).length = 26 + pre.length := by rw [wf_len, hx]
    have hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := by
      intro h hh
      exact (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh))))).1
    rw [hC]
    exact ev pre post g T x b (hb (wf pre x))
      (fun h hh E' => hs h (hpost h hh) (wf pre x) E' hlen)
  have hout : C.output ≠ 26 + pre.length := by
    intro ho
    obtain ⟨x, y, hx, hy, ex, ey⟩ := hne
    obtain ⟨E2, h1, _⟩ := key x hx
    obtain ⟨E3, h3, _⟩ := key y hy
    have vx : C.eval x = b := by
      show (wf C.gates x).getD C.output false = b
      rw [h1, ho]
      exact getD_mid _ _ _ _ (by rw [wf_len, hx])
    have vy : C.eval y = b := by
      show (wf C.gates y).getD C.output false = b
      rw [h3, ho]
      exact getD_mid _ _ _ _ (by rw [wf_len, hy])
    rw [vx] at ex
    rw [vy, ex] at ey
    exact Bool.noConfusion ey
  apply assemble C pre post g hC T (sk (26 + pre.length) C.output) hmono hrb hTm hTr
  intro x hx
  obtain ⟨E2, h1, h2⟩ := key x hx
  show (wf (pre ++ post.map T) x).getD (sk (26 + pre.length) C.output) false
    = (wf C.gates x).getD C.output false
  rw [h2, h1]
  exact getD_sk _ _ _ _ (by rw [wf_len, hx]) _ hout

theorem copy_val (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (v : Bool) :
    op.eval [v] = v ∧ op.eval [v, v] = v := by
  rcases hop with rfl | rfl <;> cases v <;> exact ⟨rfl, rfl⟩

theorem len26 (f g : Fin 13 → Bool) : (List.ofFn f ++ List.ofFn g).length = 26 := by
  simp

theorem short_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
      C.eval y = false)
    (hdeg : ∃ g ∈ C.gates, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
    obtain ⟨g, hg, hd⟩ := hdeg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    obtain ⟨pre, post, gj, hC, hpl, hgj⟩ := clean_split_gates C.gates k hk
    have hgg : gj = g := by rw [← hgj, hgk]
    rw [hgg] at hC
    have hl := legal_of C hmono g hg
    have hin : ∀ i ∈ g.inputs, i < 26 + pre.length := by
      intro i hi
      have := hrb k hk i (by rw [clean_gateAt_eq C k hk, hgk]; exact hi)
      omega
    obtain ⟨op, ins⟩ := g
    have hop : op = GateOp.and ∨ op = GateOp.or := hl.1
    have hlen : ins.length ≤ 2 := hl.2
    have hd' : ins.length < 2 ∨ ins.getD 0 0 = ins.getD 1 0 := hd
    have hin' : ∀ i ∈ ins, i < 26 + pre.length := hin
    rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, r⟩⟩⟩
    · rcases hop with hop | hop
      · subst hop
        exact const_case C hmono hrb pre post _ hC (Tt (26 + pre.length)) true (fun _ => rfl)
          (fun h hl => Tt_legal _ h hl)
          (fun h hl M hM hi => Tt_rb _ (by omega) h hl.1 M hM hi)
          (fun h hop A E hA => sound_t A E _ hA h hop) hne
      · subst hop
        exact const_case C hmono hrb pre post _ hC (Tf (26 + pre.length)) false (fun _ => rfl)
          (fun h hl => Tf_legal _ h hl)
          (fun h hl M hM hi => Tf_rb _ (by omega) h hl.1 M hM hi)
          (fun h hop A E hA => sound_f A E _ hA h hop) hne
    · exact copy_case C hmono hrb pre post _ hC a (hin' a (by simp))
        (fun A => (copy_val op hop _).1)
    · have hac : a = c := by simpa using hd'
      subst hac
      exact copy_case C hmono hrb pre post _ hC a (hin' a (by simp))
        (fun A => (copy_val op hop _).2)
    · have h3 : (a :: c :: d :: r).length ≤ 2 := hlen
      simp only [List.length_cons] at h3
      omega

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def clean_AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : clean_AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma clean_inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [clean_inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [clean_inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [clean_inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : clean_AOB n C) (hC' : clean_AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : clean_AOB n C) (hC' : clean_AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : clean_AOB n C) (hC' : clean_AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : clean_AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [clean_inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [clean_inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [clean_inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [clean_inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, clean_inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [clean_inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [clean_inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, clean_inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma pairs_lt2 (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    (T T' : Finset (ℕ × ℕ))
    (hT : ∀ p : ℕ × ℕ, p ∈ T ↔ (p.1 < C.gates.length ∧ p.2 < C.gates.length) ∧
      (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)
    (hT' : ∀ p : ℕ × ℕ, p ∈ T' ↔ (p.1 < C'.gates.length ∧ p.2 < C'.gates.length) ∧
      (gateAt C' p.1).op = GateOp.and ∧ (gateAt C' p.2).op = GateOp.and ∧
        InCone n C' p.1 p.2) :
    T'.card < T.card := by
  classical
  have e : T = (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2) := by
    ext p
    rw [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  have e' : T' = (Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2) := by
    ext p
    rw [hT', Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  rw [e, e']
  exact pairs_lt n C C' r i j hr hir hlen hops htop hcone hno hi hj hij

lemma reader_or (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hC r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hC) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x hb => V1_fun n C r (n + i) x hC hr hir hout hb (key x)
  have hle := hmin _ (V1_AO2 n C r (n + i) hC hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hC : AO2 n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hC hout i r1 hr1 hmin hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hC hout i r2 hr2 hmin hin2
  have hir1 : i < r1 := by have := (hC r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hC) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hC) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hC hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x hb => V2_out n C r2 c2 i x hC hr2 hc2lt hir2 hout hb (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x hb =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x hb)
  have hle := hmin _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

lemma step3_core (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hC hout i r hr hmin hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hC hout i k r h hr hmin hkin hrin).elim
    · exact h
    · exact (reader_unique n C hC hout i r k h hk hmin hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hC) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma lift_abs (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hcone : InCone n C i j) :
    ∃ D : Circuit, AO2 n D ∧ D.gates.length = C.gates.length ∧
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) ∧
      PEqualNP.TopForm.andPairs n D < PEqualNP.TopForm.andPairs n C := by
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hC hout i j hmin hcone
  refine ⟨V2 n C r c i, V2_AO2 n C r c i hC hr hclt hir hout, V2_len n C r c i,
    fun x hb => V2_out n C r c i x hC hr hclt hir hout hb (h0 x), ?_⟩
  unfold PEqualNP.TopForm.andPairs
  refine pairs_lt2 n C (V2 n C r c i) r i j hr hir (V2_len n C r c i) ?_ ?_ ?_ ?_ hi hj hcone
    _ _ ?_ ?_
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro a' b' hb' h
    exact V2_cone n C r c i hC hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq
  · intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  · intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]

lemma ofFn_of_len (L : List Bool) : ∀ (m : ℕ), L.length = m →
    ∃ x : Fin m → Bool, List.ofFn x = L := by
  intro m hm
  subst hm
  exact ⟨L.get, List.ofFn_get L⟩

lemma AO2_mono {n : ℕ} {C : Circuit} (h : AO2 n C) : Monotone2 C := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have e := clean_gateAt_eq C k hk
  obtain ⟨h1, ⟨a, b, h2⟩, _⟩ := h k hk
  rw [e] at h1 h2
  refine ⟨?_, by rw [h2]; simp⟩
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

lemma to_AO2 (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (h2 : ∀ g ∈ C.gates, ¬ g.inputs.length < 2) : AO2 26 C := by
  intro k hk
  have e := clean_gateAt_eq C k hk
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk
  have hl := legal_of C hmono _ hmem
  have h3 := h2 _ hmem
  refine ⟨by rw [e]; exact hl.1, ?_, hrb k hk⟩
  rw [e]
  have h4 : (C.gates[k]).inputs.length = 2 := by
    have := hl.2
    omega
  exact List.length_eq_two.mp h4

theorem main26 (A R : List Bool → Prop) (hA : ∀ L, A L → L.length = 26)
    (hR : ∀ L, R L → L.length = 26) (hAne : ∃ L, A L) (hRne : ∃ L, R L)
    (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hacc : ∀ L, A L → C.eval L = true) (hrej : ∀ L, R L → C.eval L = false)
    (i j : ℕ) (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone 26 C i j)
    (hB : ∀ L, R L → (C.wires L).getD (26 + i) false = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ ((∀ L, A L → D.eval L = true) ∧
      ∀ L, R L → D.eval L = false) ∧
      (D.size < C.size ∨ D.size = C.size ∧
        PEqualNP.TopForm.andPairs 26 D < PEqualNP.TopForm.andPairs 26 C) := by
  by_cases hsm : ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧
      ((∀ L, A L → D.eval L = true) ∧ ∀ L, R L → D.eval L = false) ∧ D.size < C.size
  · obtain ⟨D, h1, h2, h3, h4⟩ := hsm
    exact ⟨D, h1, h2, h3, Or.inl h4⟩
  · have hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
        C.eval y = false := by
      obtain ⟨La, ha⟩ := hAne
      obtain ⟨Lr, hr⟩ := hRne
      exact ⟨La, Lr, hA _ ha, hR _ hr, hacc _ ha, hrej _ hr⟩
    have hC : AO2 26 C := by
      apply to_AO2 C hmono hrb
      intro g hg hlt
      obtain ⟨C', m1, m2, heq, hsz⟩ := short_case C hmono hrb hne ⟨g, hg, Or.inl hlt⟩
      apply hsm
      refine ⟨C', m1, m2, ⟨?_, ?_⟩, hsz⟩
      · intro L hL
        rw [heq L (hA L hL)]
        exact hacc L hL
      · intro L hL
        rw [heq L (hR L hL)]
        exact hrej L hL
    have hbelA : ∀ x : Fin 26 → Bool, A (List.ofFn x) →
        (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) := by
      intro x hL _
      exact hacc _ hL
    have hbelR : ∀ x : Fin 26 → Bool, R (List.ofFn x) →
        (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) := by
      intro x hL hv
      have h1 : wv 26 C x (26 + i) = false := hB _ hL
      rw [h1] at hv
      exact absurd hv (by simp)
    have tg : ∀ D : Circuit, AO2 26 D →
        (∀ x, (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) →
          wv 26 D x D.output = wv 26 C x C.output) →
        ((∀ L, A L → D.eval L = true) ∧ ∀ L, R L → D.eval L = false) := by
      intro D _ hf
      constructor
      · intro L hL
        obtain ⟨x, hx⟩ := ofFn_of_len L 26 (hA L hL)
        subst hx
        have h1 := hf x (hbelA x hL)
        have h2 : wv 26 C x C.output = true := hacc _ hL
        show wv 26 D x D.output = true
        rw [h1]
        exact h2
      · intro L hL
        obtain ⟨x, hx⟩ := ofFn_of_len L 26 (hR L hL)
        subst hx
        have h1 := hf x (hbelR x hL)
        have h2 : wv 26 C x C.output = false := hrej _ hL
        show wv 26 D x D.output = false
        rw [h1]
        exact h2
    have hmin : ∀ D : Circuit, AO2 26 D →
        (∀ x, (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) →
          wv 26 D x D.output = wv 26 C x C.output) → C.gates.length ≤ D.gates.length := by
      intro D hD hf
      by_contra hlt
      apply hsm
      refine ⟨D, AO2_mono hD, (fun k hk => (hD k hk).2.2), tg D hD hf, ?_⟩
      show D.gates.length < C.gates.length
      omega
    have hout : C.output < 26 + C.gates.length := by
      obtain ⟨La, ha⟩ := hAne
      obtain ⟨x, hx⟩ := ofFn_of_len La 26 (hA La ha)
      subst hx
      exact out_lt 26 C x (hacc _ ha)
    obtain ⟨D, hD, hlen, hf, hp⟩ := lift_abs 26 C hC hout i j hmin hi hj hij
    exact ⟨D, AO2_mono hD, (fun k hk => (hD k hk).2.2), tg D hD hf, Or.inr ⟨hlen, hp⟩⟩

def hits {X Y : Type*} (P : Fin 3 → X → Prop) (L : Fin 3 → Y → Prop) (x : X) (y : Y) : Prop :=
  ∀ i, P i x ∨ L i y

def noSame {X : Type*} (P : Fin 3 → X → Prop) : Prop :=
  ∀ x y, ∃ i, ¬ P i x ∧ ¬ P i y

def noSquare {X Y : Type*} (I : X → Y → Prop) : Prop :=
  ∀ x x' y y', I x y → I x y' → I x' y → I x' y' → x = x' ∨ y = y'

lemma three_slots (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (t : Fin 3) : t = i ∨ t = j ∨ t = k := by omega

lemma doubleStar {X Y : Type*} {P : Fin 3 → X → Prop} {L : Fin 3 → Y → Prop}
    {I : X → Y → Prop} (hP : noSame P) (hL : noSame L)
    (safe : ∀ x y, hits P L x y → I x y) (sq : noSquare I)
    {p q : X} {l m : Y} (ep : hits P L p l) (eq' : hits P L q m)
    (hpq : p ≠ q) (hlm : l ≠ m) (cross : ¬ I q l) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (∀ y, ¬ L i y) ∧ (∀ x, ¬ P j x) ∧ P i p ∧ L j m ∧ P k p ∧ L k m ∧
      (∀ x, P i x → P k x → x = p) ∧ (∀ y, L j y → L k y → y = m) ∧
      (∀ x y, hits P L x y ↔ (x = p ∧ L j y) ∨ (P i x ∧ y = m)) := by
  classical
  obtain ⟨i, hil, him⟩ := hL l m
  obtain ⟨j, hjp, hjq⟩ := hP p q
  have hFail : ¬ hits P L q l := fun h => cross (safe q l h)
  unfold hits at hFail
  push Not at hFail
  obtain ⟨k, hkq, hkl⟩ := hFail
  have hip := (ep i).resolve_right hil
  have hiq := (eq' i).resolve_right him
  have hjl := (ep j).resolve_left hjp
  have hjm := (eq' j).resolve_left hjq
  have hkp := (ep k).resolve_right hkl
  have hkm := (eq' k).resolve_left hkq
  have hij : i ≠ j := fun e => hjp (e ▸ hip)
  have hik : i ≠ k := fun e => hkq (e ▸ hiq)
  have hjk : j ≠ k := fun e => hkl (e ▸ hjl)
  have ipure (y) : ¬ L i y := by
    intro hy
    obtain ⟨t, htm, hty⟩ := hL m y
    rcases three_slots i j k hij hik hjk t with rfl | rfl | rfl
    · exact hty hy
    · exact htm hjm
    · exact htm hkm
  have jpure (x) : ¬ P j x := by
    intro hx
    obtain ⟨t, htp, htx⟩ := hP p x
    rcases three_slots i j k hij hik hjk t with rfl | rfl | rfl
    · exact htp hip
    · exact htx hx
    · exact htp hkp
  have makeHit {x y} (hx : P i x) (hy : L j y) (hk : P k x ∨ L k y) : hits P L x y := by
    intro t
    rcases three_slots i j k hij hik hjk t with rfl | rfl | rfl
    · exact Or.inl hx
    · exact Or.inr hy
    · exact hk
  have centerP (x) (hx : P i x) (hk : P k x) : x = p :=
    (sq x p l m (safe _ _ (makeHit hx hjl (.inl hk)))
      (safe _ _ (makeHit hx hjm (.inl hk))) (safe _ _ ep)
      (safe _ _ (makeHit hip hjm (.inl hkp)))).resolve_right hlm
  have centerL (y) (hy : L j y) (hk : L k y) : y = m :=
    (sq p q y m (safe _ _ (makeHit hip hy (.inr hk)))
      (safe _ _ (makeHit hip hjm (.inl hkp))) (safe _ _ (makeHit hiq hy (.inr hk)))
      (safe _ _ eq')).resolve_left hpq
  refine ⟨i, j, k, hij, hik, hjk, ipure, jpure, hip, hjm, hkp, hkm, centerP, centerL, ?_⟩
  intro x y
  constructor
  · intro h
    have hx := (h i).resolve_right (ipure y)
    have hy := (h j).resolve_left (jpure x)
    rcases h k with hk | hk
    · exact Or.inl ⟨centerP x hx hk, hy⟩
    · exact Or.inr ⟨hx, centerL y hy hk⟩
  · rintro (⟨rfl, hy⟩ | ⟨hx, rfl⟩)
    · exact makeHit hip hy (.inl hkp)
    · exact makeHit hx hjm (.inr hkm)

def forbidMixed {X Y : Type*} (P : Fin 3 → X → Prop) (L : Fin 3 → Y → Prop)
    (I : X → Y → Prop) : Prop :=
  ∀ p l m, ¬ I p l → ¬ I p m → ∃ t, ¬ P t p ∧ ¬ L t l ∧ ¬ L t m

lemma projectedClause {X Y : Type*} {P : Fin 3 → X → Prop} {L : Fin 3 → Y → Prop}
    {I : X → Y → Prop} (hP : noSame P) (hL : noSame L)
    (reject : forbidMixed P L I) {p : X} {l : Y} (edge : hits P L p l) :
    ∃ t, ¬ P t p ∧ (∀ y, hits P L p y → L t y) ∧ (∀ y, L t y → I p y) := by
  classical
  suffices good : ∃ t, ¬ P t p ∧ ∀ y, L t y → I p y by
    obtain ⟨t, ht, hg⟩ := good
    exact ⟨t, ht, fun y h => (h t).resolve_left ht, hg⟩
  by_contra bad
  push Not at bad
  obtain ⟨i, hip, _⟩ := hP p p
  obtain ⟨y, hiy, hy⟩ := bad i hip
  obtain ⟨j, hjp, hjy, _⟩ := reject p y y hy hy
  obtain ⟨z, hjz, hz⟩ := bad j hjp
  obtain ⟨k, hkp, hky, hkz⟩ := reject p y z hy hz
  obtain ⟨t, htl, _⟩ := hL l l
  have htp := (edge t).resolve_right htl
  rcases three_slots i j k (fun e => hjy (e ▸ hiy)) (fun e => hky (e ▸ hiy))
      (fun e => hkz (e ▸ hjz)) t with rfl | rfl | rfl
  · exact hip htp
  · exact hjp htp
  · exact hkp htp

def flatCases {X Y : Type*} (P : Fin 3 → X → Prop) (L : Fin 3 → Y → Prop)
    (I : X → Y → Prop) : Prop :=
  (∀ x y, ¬ hits P L x y) ∨
  (∃ p i, (∀ x y, hits P L x y → x = p ∧ L i y) ∧ (∀ y, L i y → I p y)) ∨
  (∃ l j, (∀ x y, hits P L x y → P j x ∧ y = l) ∧ (∀ x, P j x → I x l)) ∨
  ∃ p m i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    (∀ y, ¬ L i y) ∧ (∀ x, ¬ P j x) ∧ P i p ∧ L j m ∧ P k p ∧ L k m ∧
    (∀ x, P i x → P k x → x = p) ∧ (∀ y, L j y → L k y → y = m) ∧
    (∀ x y, hits P L x y ↔ (x = p ∧ L j y) ∨ (P i x ∧ y = m))

lemma classify {X Y : Type*} {P : Fin 3 → X → Prop} {L : Fin 3 → Y → Prop}
    {I : X → Y → Prop} (hP : noSame P) (hL : noSame L)
    (safe : ∀ x y, hits P L x y → I x y) (sq : noSquare I)
    (hpMix : forbidMixed P L I) (hlMix : forbidMixed L P (fun y x => I x y)) :
    flatCases P L I := by
  classical
  by_cases h0 : ∃ x y, hits P L x y
  · obtain ⟨p, l, he⟩ := h0
    by_cases h1 : ∀ x y, hits P L x y → x = p
    · obtain ⟨i, _, hl, hi⟩ := projectedClause hP hL hpMix he
      refine Or.inr (Or.inl ⟨p, i, ?_, hi⟩)
      intro x y h
      obtain rfl := h1 x y h
      exact ⟨rfl, hl y h⟩
    by_cases h2 : ∀ x y, hits P L x y → y = l
    · obtain ⟨j, _, hp, hi⟩ := projectedClause hL hP hlMix (p := l) (l := p)
          (fun i => (he i).symm)
      refine Or.inr (Or.inr (Or.inl ⟨l, j, ?_, hi⟩))
      intro x y h
      obtain rfl := h2 x y h
      exact ⟨hp x (fun i => (h i).symm), rfl⟩
    have matching : ∃ a b c d, hits P L a b ∧ hits P L c d ∧ a ≠ c ∧ b ≠ d := by
      push Not at h1 h2
      obtain ⟨x, y, hxy, hx⟩ := h1
      obtain ⟨z, w, hzw, hw⟩ := h2
      by_cases hy : y = l
      · by_cases hz : z = p
        · exact ⟨x, y, z, w, hxy, hzw, hz ▸ hx, hy ▸ Ne.symm hw⟩
        · exact ⟨z, w, p, l, hzw, he, hz, hw⟩
      · exact ⟨x, y, p, l, hxy, he, hx, hy⟩
    obtain ⟨a, b, c, d, hab, hcd, hac, hbd⟩ := matching
    apply Or.inr
    apply Or.inr
    apply Or.inr
    by_cases hc : I c b
    · have ha : ¬ I a d := fun had =>
        (sq a c b d (safe _ _ hab) had hc (safe _ _ hcd)).elim hac hbd
      exact ⟨c, b, doubleStar hP hL safe sq hcd hab hac.symm hbd.symm ha⟩
    · exact ⟨a, d, doubleStar hP hL safe sq hab hcd hac hbd hc⟩
  · exact Or.inl (fun x y h => h0 ⟨x, y, h⟩)

abbrev D : Finset (Fin 13) := {0, 1, 3, 9}

abbrev inc (p l : Fin 13) : Prop := p - l ∈ D

abbrev quad (Q : Finset (Fin 13)) : Prop :=
  Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter (fun p => inc p l)).card ≤ 2

abbrev miss (Q : Finset (Fin 13)) (l : Fin 13) : Prop := ∀ p ∈ Q, ¬ inc p l

def qShift (a : Fin 13) (Q : Finset (Fin 13)) := Q.image (fun p => p + a)

lemma shifted_inc (p l a : Fin 13) : inc (p + a) (l + a) ↔ inc p l := by
  simp only [inc, add_sub_add_right_eq_sub]

lemma shifted_mem (p a : Fin 13) (Q : Finset (Fin 13)) :
    p + a ∈ qShift a Q ↔ p ∈ Q := by simp [qShift]

lemma shifted_miss {l a : Fin 13} {Q : Finset (Fin 13)} (hm : miss Q l) :
    miss (qShift a Q) (l + a) := by
  rintro u hu
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
  exact fun h => hm p hp ((shifted_inc p l a).mp h)

lemma shifted_quad {a : Fin 13} {Q : Finset (Fin 13)} (hq : quad Q) : quad (qShift a Q) := by
  have inj : Function.Injective (fun p : Fin 13 => p + a) := fun _ _ h => add_right_cancel h
  refine ⟨(Finset.card_image_of_injective _ inj).trans hq.1, ?_⟩
  intro l
  have hf : (qShift a Q).filter (fun p => inc p l) = qShift a (Q.filter (fun p => inc p (l-a))) := by
    ext z
    obtain ⟨w, rfl⟩ : ∃ w, w + a = z := ⟨z - a, sub_add_cancel _ _⟩
    have h : inc (w+a) l ↔ inc w (l-a) := by
      simpa only [sub_add_cancel] using shifted_inc w (l-a) a
    simp only [Finset.mem_filter, shifted_mem, h]
  rw [hf, qShift, Finset.card_image_of_injective _ inj]
  exact hq.2 (l-a)

def pointQuads : List (Finset (Fin 13)) :=
  [{0,1,2,5}, {0,1,4,8}, {0,2,3,4}, {0,3,5,6}, {0,3,10,12}, {0,4,6,9}, {0,5,8,10},
   {0,5,11,12}, {0,7,8,9}, {0,1,2,6}, {0,2,7,11}, {0,3,7,11}, {0,4,9,12}, {0,1,6,7}]

def lineQuads : List (Finset (Fin 13)) :=
  [{2,4,5,6}, {8,10,11,12}, {2,4,7,8}, {5,6,7,10}, {2,4,11,12}, {5,6,11,12},
   {2,5,8,10}, {4,6,8,10}, {2,4,7,11}, {2,4,7,12}]

lemma pointQuads_ok : ∀ Q ∈ pointQuads, quad Q ∧ 0 ∈ Q := by
  have yes : pointQuads.all (fun Q => decide (quad Q ∧ 0 ∈ Q)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using yes

lemma lineQuads_ok : ∀ Q ∈ lineQuads, quad Q ∧ miss Q 0 := by
  have yes : lineQuads.all (fun Q => decide (quad Q ∧ miss Q 0)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using yes

set_option maxHeartbeats 4000000 in
lemma pointQuads_cover : ∀ l m : Fin 13, ¬ inc 0 l → ¬ inc 0 m →
    ∃ Q ∈ pointQuads, miss Q l ∧ miss Q m := by
  have yes : ∀ l m : Fin 13, ¬ inc 0 l → ¬ inc 0 m →
      pointQuads.any (fun Q => decide (miss Q l ∧ miss Q m)) = true := by decide +kernel
  simpa only [List.any_eq_true, decide_eq_true_eq] using yes

set_option maxHeartbeats 4000000 in
lemma lineQuads_cover : ∀ p r : Fin 13, ¬ inc p 0 → ¬ inc r 0 →
    ∃ Q ∈ lineQuads, p ∈ Q ∧ r ∈ Q := by
  have yes : ∀ p r : Fin 13, ¬ inc p 0 → ¬ inc r 0 →
      lineQuads.any (fun Q => decide (p ∈ Q ∧ r ∈ Q)) = true := by decide +kernel
  simpa only [List.any_eq_true, decide_eq_true_eq] using yes

lemma mixedPLLines (p l m : Fin 13) (hl : ¬ inc p l) (hm : ¬ inc p m) :
    ∃ Q, quad Q ∧ p ∈ Q ∧ miss Q l ∧ miss Q m := by
  have rot (t : Fin 13) : inc 0 (t-p) ↔ inc p t := by
    simpa only [zero_add, sub_add_cancel] using (shifted_inc 0 (t-p) p).symm
  obtain ⟨Q, hQ, hlQ, hmQ⟩ := pointQuads_cover (l-p) (m-p)
      (fun h => hl ((rot l).mp h)) (fun h => hm ((rot m).mp h))
  obtain ⟨hq, hz⟩ := pointQuads_ok Q hQ
  refine ⟨qShift p Q, shifted_quad hq, ?_, ?_, ?_⟩
  · simpa only [zero_add] using (shifted_mem 0 p Q).mpr hz
  · simpa only [sub_add_cancel] using shifted_miss (a := p) hlQ
  · simpa only [sub_add_cancel] using shifted_miss (a := p) hmQ

lemma mixedLPPoints (l p r : Fin 13) (hp : ¬ inc p l) (hr : ¬ inc r l) :
    ∃ Q, quad Q ∧ miss Q l ∧ p ∈ Q ∧ r ∈ Q := by
  have rot (t : Fin 13) : inc (t-l) 0 ↔ inc t l := by
    simpa only [zero_add, sub_add_cancel] using (shifted_inc (t-l) 0 l).symm
  obtain ⟨Q, hQ, hpQ, hrQ⟩ := lineQuads_cover (p-l) (r-l)
      (fun h => hp ((rot p).mp h)) (fun h => hr ((rot r).mp h))
  obtain ⟨hq, hz⟩ := lineQuads_ok Q hQ
  refine ⟨qShift l Q, shifted_quad hq, ?_, ?_, ?_⟩
  · simpa only [zero_add] using shifted_miss (a := l) hz
  · simpa only [sub_add_cancel] using (shifted_mem (p-l) l Q).mpr hpQ
  · simpa only [sub_add_cancel] using (shifted_mem (r-l) l Q).mpr hrQ

def rejectsQuads (P L : Fin 3 → Fin 13 → Prop) : Prop :=
  ∀ Q, quad Q → ∃ i, (∀ p ∈ Q, ¬ P i p) ∧ (∀ l, miss Q l → ¬ L i l)

set_option synthInstance.maxSize 1024 in
lemma plane_noSquare : noSquare inc := by
  unfold noSquare
  decide +kernel

lemma classOfQuadRejection {P L : Fin 3 → Fin 13 → Prop} (rej : rejectsQuads P L) :
    flatCases P L inc := by
  have hpMix : forbidMixed P L inc := by
    intro p l m hl hm
    obtain ⟨Q, hQ, hpQ, hlQ, hmQ⟩ := mixedPLLines p l m hl hm
    obtain ⟨i, hi, hj⟩ := rej Q hQ
    exact ⟨i, hi p hpQ, hj l hlQ, hj m hmQ⟩
  have hlMix : forbidMixed L P (fun l p => inc p l) := by
    intro l p r hp hr
    obtain ⟨Q, hQ, hlQ, hpQ, hrQ⟩ := mixedLPPoints l p r hp hr
    obtain ⟨i, hi, hj⟩ := rej Q hQ
    exact ⟨i, hj l hlQ, hi p hpQ, hi r hrQ⟩
  have safe (p l) (e : hits P L p l) : inc p l := by
    by_contra h
    obtain ⟨i, hp, hl, _⟩ := hpMix p l l h h
    exact (e i).elim hp hl
  have lineMissesPair : ∀ p r : Fin 13, ∃ l : Fin 13, ¬ inc p l ∧ ¬ inc r l := by decide +kernel
  have ptMissesPair : ∀ l m : Fin 13, ∃ p : Fin 13, ¬ inc p l ∧ ¬ inc p m := by decide +kernel
  have hp : noSame P := by
    intro p r
    obtain ⟨l, h1, h2⟩ := lineMissesPair p r
    obtain ⟨i, _, hip, hir⟩ := hlMix l p r h1 h2
    exact ⟨i, hip, hir⟩
  have hl : noSame L := by
    intro l m
    obtain ⟨p, h1, h2⟩ := ptMissesPair l m
    obtain ⟨i, _, hil, him⟩ := hpMix p l m h1 h2
    exact ⟨i, hil, him⟩
  exact classify hp hl safe plane_noSquare hpMix hlMix

def addCommon {X : Type*} (B : Fin 3 → X → Prop) (U : X → Prop) (i : Fin 3) (x : X) : Prop :=
  B i x ∨ (i ≠ 2 ∧ U x)

lemma stripCommon {X Y : Type*} {P : Fin 3 → X → Prop} {L : Fin 3 → Y → Prop}
    {U : X → Prop} {V : Y → Prop} {p : X} {m : Y} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (pi : ∀ y, ¬ addCommon L V i y) (pj : ∀ x, ¬ addCommon P U j x)
    (hip : addCommon P U i p) (hjm : addCommon L V j m)
    (xp : ∀ x, addCommon P U i x → addCommon P U k x → x = p)
    (ym : ∀ y, addCommon L V j y → addCommon L V k y → y = m) (x : X) (y : Y) :
    ((x = p ∧ addCommon L V j y) ∨ (addCommon P U i x ∧ y = m)) ↔
      ((x = p ∧ L j y) ∨ (P i x ∧ y = m)) := by
  classical
  constructor
  · rintro (⟨rfl, h | ⟨_, hv⟩⟩ | ⟨h | ⟨_, hu⟩, rfl⟩)
    · exact Or.inl ⟨rfl, h⟩
    · have ei : i = 2 := by
        by_contra h
        exact pi y (Or.inr ⟨h, hv⟩)
      have ej : j ≠ 2 := fun e => hij (ei.trans e.symm)
      have ek : k ≠ 2 := fun e => hik (ei.trans e.symm)
      exact Or.inr ⟨hip.resolve_right (fun h => h.1 ei),
        ym y (.inr ⟨ej, hv⟩) (.inr ⟨ek, hv⟩)⟩
    · exact Or.inr ⟨h, rfl⟩
    · have ej : j = 2 := by
        by_contra h
        exact pj x (Or.inr ⟨h, hu⟩)
      have ei : i ≠ 2 := fun e => hij (e.trans ej.symm)
      have ek : k ≠ 2 := fun e => hjk (ej.trans e.symm)
      exact Or.inl ⟨xp x (.inr ⟨ei, hu⟩) (.inr ⟨ek, hu⟩),
        hjm.resolve_right (fun h => h.1 ej)⟩
  · rintro (⟨hp, hl⟩ | ⟨hx, hy⟩)
    · exact Or.inl ⟨hp, Or.inl hl⟩
    · exact Or.inr ⟨Or.inl hx, hy⟩

def meets (P L : Fin 13 → Prop) (S T : Fin 13 → Prop) : Prop :=
  (∃ p, S p ∧ P p) ∨ ∃ l, T l ∧ L l

def nested (b : Fin 3 → Prop) (u : Prop) : Prop := ((b 0 ∧ b 1) ∨ u) ∧ b 2

lemma threeClause (b : Fin 3 → Prop) (u : Prop) :
    nested b u ↔ ∀ i : Fin 3, b i ∨ (i ≠ 2 ∧ u) := by
  constructor
  · rintro ⟨h, h2⟩ i
    rcases three_slots 0 1 2 (by decide) (by decide) (by decide) i with rfl | rfl | rfl
    · exact h.elim (fun h => Or.inl h.1) (fun hu => Or.inr ⟨by decide, hu⟩)
    · exact h.elim (fun h => Or.inl h.2) (fun hu => Or.inr ⟨by decide, hu⟩)
    · exact Or.inl h2
  · intro h
    refine ⟨?_, (h 2).resolve_right (fun h => h.1 rfl)⟩
    by_cases hu : u
    · exact Or.inr hu
    · exact Or.inl ⟨(h 0).resolve_right (fun h => hu h.2), (h 1).resolve_right (fun h => hu h.2)⟩

lemma meets_addCommon (P L : Fin 3 → Fin 13 → Prop) (U V S T : Fin 13 → Prop) (i : Fin 3) :
    meets (addCommon P U i) (addCommon L V i) S T ↔
      meets (P i) (L i) S T ∨ (i ≠ 2 ∧ meets U V S T) := by
  unfold meets addCommon
  constructor
  · rintro (⟨p, hp, ha | ⟨hi, hu⟩⟩ | ⟨l, hl, ha | ⟨hi, hv⟩⟩)
    · exact Or.inl (Or.inl ⟨p, hp, ha⟩)
    · exact Or.inr ⟨hi, Or.inl ⟨p, hp, hu⟩⟩
    · exact Or.inl (Or.inr ⟨l, hl, ha⟩)
    · exact Or.inr ⟨hi, Or.inr ⟨l, hl, hv⟩⟩
  · rintro ((⟨p, hp, ha⟩ | ⟨l, hl, ha⟩) | ⟨hi, ⟨p, hp, hu⟩ | ⟨l, hl, hv⟩⟩)
    · exact Or.inl ⟨p, hp, Or.inl ha⟩
    · exact Or.inr ⟨l, hl, Or.inl ha⟩
    · exact Or.inl ⟨p, hp, Or.inr ⟨hi, hu⟩⟩
    · exact Or.inr ⟨l, hl, Or.inr ⟨hi, hv⟩⟩

lemma classifyNested (P L : Fin 3 → Fin 13 → Prop) (U V : Fin 13 → Prop)
    (negative : ∀ Q, quad Q → ¬ nested (fun i => meets (P i) (L i) (· ∈ Q) (miss Q))
      (meets U V (· ∈ Q) (miss Q))) :
    let F := fun p l => nested (fun i => P i p ∨ L i l) (U p ∨ V l)
    (∀ x y, ¬ F x y) ∨
    (∃ p i, (∀ x y, F x y → x = p ∧ addCommon L V i y) ∧ (∀ y, addCommon L V i y → inc p y)) ∨
    (∃ l j, (∀ x y, F x y → addCommon P U j x ∧ y = l) ∧ (∀ x, addCommon P U j x → inc x l)) ∨
    ∃ p m i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      (∀ y, ¬ L i y) ∧ (∀ x, ¬ P j x) ∧
      ((∃ x, U x) ∨ (∃ y, V y) ∨ (P k p ∧ L k m)) ∧
      (∀ x y, F x y ↔ (x = p ∧ L j y) ∨ (P i x ∧ y = m)) := by
  classical
  intro F
  have rejected : rejectsQuads (addCommon P U) (addCommon L V) := by
    intro Q hQ
    have h (i) := meets_addCommon P L U V (· ∈ Q) (miss Q) i
    have fail : ¬ ∀ i, meets (addCommon P U i) (addCommon L V i) (· ∈ Q) (miss Q) :=
      fun hAll => negative Q hQ ((threeClause _ _).mpr (fun i => (h i).mp (hAll i)))
    push Not at fail
    obtain ⟨i, hi⟩ := fail
    exact ⟨i, fun p hp hit => hi (Or.inl ⟨p, hp, hit⟩),
      fun l hl hit => hi (Or.inr ⟨l, hl, hit⟩)⟩
  have heq (x y) : F x y ↔ hits (addCommon P U) (addCommon L V) x y := by
    rw [show F x y = nested (fun i => P i x ∨ L i y) (U x ∨ V y) from rfl, threeClause]
    unfold hits addCommon
    apply forall_congr'
    intro i
    tauto
  rcases classOfQuadRejection rejected with h | ⟨p, i, h, hs⟩ | ⟨l, j, h, hs⟩ |
    ⟨p, m, i, j, k, hij, hik, hjk, pi, pj, hip, hjm, hkp, hkm, xp, ym, rule⟩
  · exact Or.inl (fun x y e => h x y ((heq x y).mp e))
  · exact Or.inr (Or.inl ⟨p, i, fun x y e => h x y ((heq x y).mp e), hs⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨l, j, fun x y e => h x y ((heq x y).mp e), hs⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨p, m, i, j, k, hij, hik, hjk,
        fun y h => pi y (Or.inl h), fun x h => pj x (Or.inl h), ?_, ?_⟩))
    · rcases hkp with a | ⟨_, a⟩
      · rcases hkm with b | ⟨_, b⟩
        · exact Or.inr (Or.inr ⟨a, b⟩)
        · exact Or.inr (Or.inl ⟨m, b⟩)
      · exact Or.inl ⟨p, a⟩
    · intro x y
      exact (heq x y).trans ((rule x y).trans (stripCommon hij hik hjk pi pj hip hjm xp ym x y))

def orPath (E : ℕ → ℕ → Prop) (O : ℕ → Prop) :=
  Relation.ReflTransGen (fun u v => E u v ∧ O v)

lemma propagate {E : ℕ → ℕ → Prop} {O V : ℕ → Prop}
    (sem : ∀ w, O w → (V w ↔ ∃ u, E u w ∧ V u)) {s w : ℕ}
    (path : orPath E O s w) (hs : V s) : V w := by
  induction path with
  | refl => exact hs
  | tail _ e ih => exact (sem _ e.2).mpr ⟨_, e.1, ih⟩

lemma boundaryWire {E : ℕ → ℕ → Prop} {O V : ℕ → Prop}
    (back : ∀ u v, E u v → u < v)
    (sem : ∀ w, O w → (V w ↔ ∃ u, E u w ∧ V u)) (w : ℕ) :
    V w ↔ ∃ s, ¬ O s ∧ orPath E O s w ∧ V s := by
  constructor
  · induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases tag : O w
      · obtain ⟨u, hu, huv⟩ := (sem w tag).mp hw
        obtain ⟨s, hs, path, hval⟩ := ih u (back u w hu) huv
        exact ⟨s, hs, path.tail ⟨hu, tag⟩, hval⟩
      · exact ⟨w, tag, .refl, hw⟩
  · rintro ⟨s, _, path, hv⟩
    exact propagate sem path hv

lemma pathThenRead {E : ℕ → ℕ → Prop} {O : ℕ → Prop} {s w a : ℕ}
    (path : orPath E O s w) (read : E w a) : Relation.TransGen E s a := by
  induction path generalizing a with
  | refl => exact .single read
  | tail _ e ih => exact (ih e.1).tail read

def rawHit (E : ℕ → ℕ → Prop) (O V : ℕ → Prop) (w : ℕ) : Prop :=
  ∃ s < 26, orPath E O s w ∧ V s

lemma onePairOperand {E : ℕ → ℕ → Prop} {O A V : ℕ → Prop} {h t : ℕ}
    (back : ∀ u v, E u v → u < v)
    (sem : ∀ w, O w → (V w ↔ ∃ u, E u w ∧ V u))
    (tags : ∀ s, ¬ O s → 26 ≤ s → A s)
    (unique : ∀ a b, A a → A b → Relation.TransGen E a b → a = h ∧ b = t)
    {w z : ℕ} (az : A z) (read : E w z) :
    V w ↔ rawHit E O V w ∨ (z = t ∧ orPath E O h w ∧ V h) := by
  constructor
  · intro hv
    obtain ⟨s, hs, path, hsv⟩ := (boundaryWire back sem w).mp hv
    by_cases hin : s < 26
    · exact Or.inl ⟨s, hin, path, hsv⟩
    · obtain ⟨rfl, hz⟩ := unique s z (tags s hs (by omega)) az (pathThenRead path read)
      exact Or.inr ⟨hz, path, hsv⟩
  · rintro (⟨s, _, path, hs⟩ | ⟨_, path, hs⟩) <;> exact propagate sem path hs

lemma onePairNested {E : ℕ → ℕ → Prop} {O A V : ℕ → Prop} {h t a b w v : ℕ}
    (back : ∀ u z, E u z → u < z)
    (sem : ∀ z, O z → (V z ↔ ∃ u, E u z ∧ V u))
    (tags : ∀ s, ¬ O s → 26 ≤ s → A s)
    (unique : ∀ x y, A x → A y → Relation.TransGen E x y → x = h ∧ y = t)
    (diff : h ≠ t) (ah : A h) (atop : A t)
    (ea : E a h) (eb : E b h) (ew : E w t) (ev : E v t)
    (hand : V h ↔ V a ∧ V b) (tand : V t ↔ V w ∧ V v)
    (leftPath : orPath E O h w) (rightFree : ¬ orPath E O h v) :
    V t ↔ nested (fun i => rawHit E O V (if i = 0 then a else if i = 1 then b else v))
      (rawHit E O V w) := by
  have H := fun {u z} (az : A z) (e : E u z) => onePairOperand back sem tags unique az e
  have aeq : V a ↔ rawHit E O V a := by simpa only [diff, false_and, or_false] using H ah ea
  have beq : V b ↔ rawHit E O V b := by simpa only [diff, false_and, or_false] using H ah eb
  have veq : V v ↔ rawHit E O V v := by simpa [rightFree] using H atop ev
  have weq : V w ↔ rawHit E O V w ∨ V h := by simpa [leftPath] using H atop ew
  change V t ↔ ((rawHit E O V a ∧ rawHit E O V b) ∨ rawHit E O V w) ∧ rawHit E O V v
  rw [tand, weq, veq, hand, aeq, beq, or_comm]

lemma rawHit_eq_meets {E : ℕ → ℕ → Prop} {O V : ℕ → Prop} {S T : Fin 13 → Prop}
    (pv : ∀ p : Fin 13, V p.val ↔ S p) (lv : ∀ l : Fin 13, V (13 + l.val) ↔ T l) (w : ℕ) :
    rawHit E O V w ↔ meets (fun p : Fin 13 => orPath E O p.val w)
      (fun l : Fin 13 => orPath E O (13 + l.val) w) S T := by
  constructor
  · rintro ⟨s, hs, path, hv⟩
    by_cases hp : s < 13
    · exact Or.inl ⟨⟨s, hp⟩, (pv ⟨s, hp⟩).mp hv, path⟩
    · let l : Fin 13 := ⟨s - 13, by omega⟩
      have e : 13 + l.val = s := by dsimp [l]; omega
      refine Or.inr ⟨l, (lv l).mp (e.symm ▸ hv), ?_⟩
      change orPath E O (13 + l.val) w
      rwa [e]
  · rintro (⟨p, hp, path⟩ | ⟨l, hl, path⟩)
    · exact ⟨p.val, by have := p.isLt; omega, path, (pv p).mpr hp⟩
    · exact ⟨13 + l.val, by have := l.isLt; omega, path, (lv l).mpr hl⟩

lemma twoPathsForceOr {E : ℕ → ℕ → Prop} {O : ℕ → Prop} {x y w : ℕ}
    (hx : orPath E O x w) (hy : orPath E O y w) (diff : x ≠ y) : O w := by
  rcases hx.cases_tail with h | ⟨_, _, _, ho⟩
  · rcases hy.cases_tail with h' | ⟨_, _, _, ho⟩
    · exact (diff (h.symm.trans h')).elim
    · exact ho
  · exact ho

lemma betweenOrCannotFeedOther {E : ℕ → ℕ → Prop} {O A : ℕ → Prop} {h t w z u : ℕ}
    (unique : ∀ a b, A a → A b → Relation.TransGen E a b → a = h ∧ b = t)
    (ah : A h) (az : A z) (diff : z ≠ t) (hw : orPath E O h w) (ez : E u z) :
    ¬ orPath E O w u := by
  intro hu
  exact diff (unique h z ah az (pathThenRead (hw.trans hu) ez)).2

lemma falseOnSide {E : ℕ → ℕ → Prop} {O V : ℕ → Prop} {h w v t : ℕ}
    (sem : ∀ z, O z → (V z ↔ ∃ u, E u z ∧ V u)) (reject : ¬ V t)
    (inner : V h) (tand : V t ↔ V w ∧ V v) :
    ¬ (orPath E O h w ∧ orPath E O h v) :=
  fun ⟨hw, hv⟩ => reject (tand.mpr ⟨propagate sem hw inner, propagate sem hv inner⟩)

lemma dirtyNoBypass {E : ℕ → ℕ → Prop} {O V : ℕ → Prop} {h out : ℕ}
    (sem : ∀ z, O z → (V z ↔ ∃ u, E u z ∧ V u)) (reject : ¬ V out)
    (inner : V h) : ¬ orPath E O h out := fun path => reject (propagate sem path inner)

lemma innerPathToOperand {E : ℕ → ℕ → Prop} {O A : ℕ → Prop} {h t : ℕ}
    (back : ∀ a b, E a b → a < b) (targetGate : ∀ a b, E a b → O b ∨ A b)
    (unique : ∀ a b, A a → A b → Relation.TransGen E a b → a = h ∧ b = t) (ah : A h)
    {u : ℕ} (hu : Relation.TransGen E h u) (hlt : u < t) : orPath E O h u := by
  induction hu with
  | single e =>
    rcases targetGate _ _ e with hh | aa
    · exact .single ⟨e, hh⟩
    · have := (unique _ _ ah aa (.single e)).2
      omega
  | tail path e ih =>
    rcases targetGate _ _ e with hh | aa
    · exact (ih (lt_trans (back _ _ e) hlt)).tail ⟨e, hh⟩
    · have := (unique _ _ ah aa (path.tail e)).2
      omega

lemma cleanOrdinarySides {P₀ L₀ P₁ L₁ : Fin 13 → Prop}
    (aLive : (∃ p, P₀ p) ∨ ∃ l, L₀ l) (bLive : (∃ p, P₁ p) ∨ ∃ l, L₁ l)
    (clean : ∀ Q, quad Q → ¬ (meets P₀ L₀ (· ∈ Q) (miss Q) ∧ meets P₁ L₁ (· ∈ Q) (miss Q))) :
    ((∀ y, ¬ L₀ y) ∧ (∀ x, ¬ P₁ x)) ∨ ((∀ x, ¬ P₀ x) ∧ (∀ y, ¬ L₁ y)) := by
  classical
  have pp (p r) (hp : P₀ p) (hr : P₁ r) : False := by
    have miss2 : ∀ p r : Fin 13, ∃ l : Fin 13, ¬ inc p l ∧ ¬ inc r l := by decide +kernel
    obtain ⟨l, h1, h2⟩ := miss2 p r
    obtain ⟨Q, hq, _, hpq, hrq⟩ := mixedLPPoints l p r h1 h2
    exact clean Q hq ⟨Or.inl ⟨p, hpq, hp⟩, Or.inl ⟨r, hrq, hr⟩⟩
  have ll (l m) (hl : L₀ l) (hm : L₁ m) : False := by
    have miss2 : ∀ l m : Fin 13, ∃ p : Fin 13, ¬ inc p l ∧ ¬ inc p m := by decide +kernel
    obtain ⟨p, h1, h2⟩ := miss2 l m
    obtain ⟨Q, hq, hpq, hlq, hmq⟩ := mixedPLLines p l m h1 h2
    exact clean Q hq ⟨Or.inr ⟨l, hlq, hl⟩, Or.inr ⟨m, hmq, hm⟩⟩
  rcases aLive with ⟨p, hp⟩ | ⟨l, hl⟩
  · rcases bLive with ⟨r, hr⟩ | ⟨m, hm⟩
    · exact (pp p r hp hr).elim
    · exact Or.inl ⟨fun y hy => ll y m hy hm, fun x hx => pp p x hp hx⟩
  · rcases bLive with ⟨r, hr⟩ | ⟨m, hm⟩
    · exact Or.inr ⟨fun x hx => pp x r hx hr, fun y hy => ll l y hl hy⟩
    · exact (ll l m hl hm).elim

lemma mixedCannotFeedPure {E : ℕ → ℕ → Prop} {O : ℕ → Prop} {g w : ℕ}
    {p l : Fin 13} (hp : orPath E O p.val g) (hl : orPath E O (13 + l.val) g)
    (pure : (∀ x : Fin 13, ¬ orPath E O x.val w) ∨ (∀ y : Fin 13, ¬ orPath E O (13 + y.val) w)) :
    ¬ orPath E O g w := by
  intro reaches
  exact pure.elim (fun h => h p (hp.trans reaches)) (fun h => h l (hl.trans reaches))

def wireRead (n len : ℕ) (ins : ℕ → List ℕ) (u v : ℕ) : Prop :=
  n ≤ v ∧ v - n < len ∧ u ∈ ins (v - n)

lemma conePathBridge {n len : ℕ} {ins : ℕ → List ℕ} {cone : ℕ → ℕ → Prop}
    (rb : ∀ j < len, ∀ w ∈ ins j, w < n + j)
    (rec : ∀ i j, cone i j ↔ j < len ∧ ∃ w ∈ ins j, n ≤ w ∧ w < n + j ∧
      (i = w - n ∨ cone i (w - n))) (i j : ℕ) :
    cone i j ↔ Relation.TransGen (wireRead n len ins) (n+i) (n+j) := by
  constructor
  · induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro h
      obtain ⟨hj, w, hw, hn, hlt, h⟩ := (rec i j).mp h
      have ew : wireRead n len ins w (n+j) := ⟨by omega, by simpa, by simpa using hw⟩
      rcases h with e | prev
      · have eq : n + i = w := by omega
        exact .single (eq ▸ ew)
      · have path := ih (w-n) (by omega) prev
        have eq : n + (w-n) = w := by omega
        exact (eq ▸ path).tail ew
  · intro path
    have pathAux {v : ℕ} (h : Relation.TransGen (wireRead n len ins) (n+i) v) :
        n ≤ v ∧ cone i (v-n) := by
      induction h with
      | single e =>
        obtain ⟨hv, hj, hw⟩ := e
        exact ⟨hv, (rec _ _).mpr ⟨hj, n+i, hw, by omega, rb _ hj _ hw, Or.inl (by omega)⟩⟩
      | tail _ e ih =>
        obtain ⟨hv, hj, hw⟩ := e
        exact ⟨hv, (rec _ _).mpr ⟨hj, _, hw, ih.1, rb _ hj _ hw, Or.inr ih.2⟩⟩
    simpa using (pathAux path).2

lemma rectCentre {P L : Fin 13 → Prop}
    (safe : ∀ p l, P p → L l → inc p l) {p l : Fin 13} (hp : P p) (hl : L l) :
    (∀ x, P x → x = p) ∨ (∀ y, L y → y = l) := by
  classical
  by_cases h : ∀ x, P x → x = p
  · exact Or.inl h
  · push Not at h
    obtain ⟨x, hx, diff⟩ := h
    exact Or.inr (fun y hy => (plane_noSquare x p y l (safe _ _ hx hy)
      (safe _ _ hx hl) (safe _ _ hp hy) (safe _ _ hp hl)).resolve_left diff)

def ordinaryFlags (P L : Fin 2 → Fin 13 → Prop) (p l : Fin 13) : Prop :=
  (P 0 p ∨ L 0 l) ∧ (P 1 p ∨ L 1 l)

lemma ordinaryStar (P L : Fin 2 → Fin 13 → Prop)
    (clean : ∀ Q, quad Q → ¬ (meets (P 0) (L 0) (· ∈ Q) (miss Q) ∧
      meets (P 1) (L 1) (· ∈ Q) (miss Q))) :
    (∀ p l, ¬ ordinaryFlags P L p l) ∨
    (∃ p i, (∀ x, ¬ P i x) ∧ (∀ y, L i y → inc p y) ∧
      ∀ x y, ordinaryFlags P L x y → x = p ∧ L i y) ∨
    (∃ l i, (∀ y, ¬ L i y) ∧ (∀ x, P i x → inc x l) ∧
      ∀ x y, ordinaryFlags P L x y → P i x ∧ y = l) := by
  classical
  by_cases live : ∃ p l, ordinaryFlags P L p l
  · obtain ⟨p, l, edge⟩ := live
    have aLive := edge.1.elim (fun h => Or.inl (Exists.intro p h))
      (fun h => Or.inr (Exists.intro l h))
    have bLive := edge.2.elim (fun h => Or.inl (Exists.intro p h))
      (fun h => Or.inr (Exists.intro l h))
    have safe (x y) (h : ordinaryFlags P L x y) : inc x y := by
      by_contra n
      obtain ⟨Q, hq, hx, hy, _⟩ := mixedPLLines x y y n n
      have lift (i) (hit : P i x ∨ L i y) : meets (P i) (L i) (· ∈ Q) (miss Q) :=
        hit.elim (fun e => Or.inl ⟨x, hx, e⟩) (fun e => Or.inr ⟨y, hy, e⟩)
      exact clean Q hq ⟨lift 0 h.1, lift 1 h.2⟩
    rcases cleanOrdinarySides aLive bLive clean with ⟨i0, i1⟩ | ⟨i0, i1⟩
    · have point := edge.1.resolve_right (i0 l)
      have line := edge.2.resolve_left (i1 p)
      have rect (x y) (hx : P 0 x) (hy : L 1 y) := safe x y ⟨Or.inl hx, Or.inr hy⟩
      rcases rectCentre rect point line with ctr | ctr
      · exact Or.inr (Or.inl ⟨p, 1, i1, fun y => rect p y point,
          fun x y e => ⟨ctr x (e.1.resolve_right (i0 y)), e.2.resolve_left (i1 x)⟩⟩)
      · exact Or.inr (Or.inr ⟨l, 0, i0, fun x hx => rect x l hx line,
          fun x y e => ⟨e.1.resolve_right (i0 y), ctr y (e.2.resolve_left (i1 x))⟩⟩)
    · have point := edge.2.resolve_right (i1 l)
      have line := edge.1.resolve_left (i0 p)
      have rect (x y) (hx : P 1 x) (hy : L 0 y) := safe x y ⟨Or.inr hy, Or.inl hx⟩
      rcases rectCentre rect point line with ctr | ctr
      · exact Or.inr (Or.inl ⟨p, 0, i0, fun y => rect p y point,
          fun x y e => ⟨ctr x (e.2.resolve_right (i1 y)), e.1.resolve_left (i0 x)⟩⟩)
      · exact Or.inr (Or.inr ⟨l, 1, i1, fun x hx => rect x l hx line,
          fun x y e => ⟨e.2.resolve_right (i1 y), ctr y (e.1.resolve_left (i0 x))⟩⟩)
  · exact Or.inl (fun p l h => live ⟨p, l, h⟩)

def available {α : Type*} (bank : List (Finset α)) (s : Finset α) : Prop :=
  s.card ≤ 1 ∨ s ∈ bank

def orBank {α : Type*} [DecidableEq α] : List (Finset α) → Prop
  | [] => True
  | s :: bank => (s.card ≤ 1 ∨ ∃ a b, available bank a ∧ available bank b ∧ s = a ∪ b) ∧ orBank bank

def charge {α : Type*} [DecidableEq α] (N : Finset α) (bank : List (Finset α)) : ℕ :=
  (bank.filter (fun s => decide (1 < s.card ∧ s ⊆ N))).length

lemma countDistinctLeaves {α : Type*} [DecidableEq α] (N : Finset α) (bank : List (Finset α))
    (built : orBank bank) (R : Finset (Finset α))
    (roots : ∀ s ∈ R, available bank s ∧ s ⊆ N) :
    (R.biUnion id).card ≤ R.card + charge N bank := by
  classical
  induction bank generalizing R with
  | nil =>
    have small (s) (hs : s ∈ R) : s.card ≤ 1 := by simpa [available] using (roots s hs).1
    calc
      (R.biUnion id).card ≤ ∑ s ∈ R, s.card := Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ R, 1 := Finset.sum_le_sum small
      _ = _ := by simp [charge]
  | cons s bank ih =>
    have previous (r) (hr : r ∈ R) (hne : r ≠ s) : available bank r ∧ r ⊆ N := by
      obtain ⟨h | h, hn⟩ := roots r hr
      · exact ⟨Or.inl h, hn⟩
      · exact ⟨Or.inr ((List.mem_cons.mp h).resolve_left hne), hn⟩
    have mono : charge N bank ≤ charge N (s :: bank) := by
      by_cases h : 1 < s.card ∧ s ⊆ N <;> simp [charge, h]
    by_cases hUse : s ∈ R ∧ 1 < s.card
    · obtain ⟨hs, hbig⟩ := hUse
      obtain ⟨a, b, ha, hb, hab⟩ := built.1.resolve_left (by omega)
      have hN := (roots s hs).2
      let R' := insert a (insert b (R.erase s))
      have hr' (r) (hr : r ∈ R') : available bank r ∧ r ⊆ N := by
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact ⟨ha, (Finset.subset_union_left.trans (hab ▸ hN))⟩
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact ⟨hb, (Finset.subset_union_right.trans (hab ▸ hN))⟩
        exact previous r (Finset.mem_erase.mp hr).2 (Finset.mem_erase.mp hr).1
      have sub : R.biUnion id ⊆ R'.biUnion id := by
        intro x hx
        obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp hx
        by_cases e : r = s
        · subst r
          change x ∈ s at hxr
          rw [hab] at hxr
          rcases Finset.mem_union.mp hxr with hx | hx
          · exact Finset.mem_biUnion.mpr ⟨a, by simp [R'], hx⟩
          · exact Finset.mem_biUnion.mpr ⟨b, by simp [R'], hx⟩
        · exact Finset.mem_biUnion.mpr ⟨r, by simp [R', e, hr], hxr⟩
      have rc : R'.card ≤ R.card + 1 := by
        have he := Finset.card_erase_add_one hs
        have h1 := Finset.card_insert_le a (insert b (R.erase s))
        have h2 := Finset.card_insert_le b (R.erase s)
        dsimp [R']
        omega
      have step : charge N (s :: bank) = charge N bank + 1 := by simp [charge, hbig, hN]
      have := ih built.2 R' hr'
      have := Finset.card_le_card sub
      omega
    · have hr (r) (hr : r ∈ R) : available bank r ∧ r ⊆ N := by
        by_cases e : r = s
        · subst r
          exact ⟨Or.inl (by by_contra! h; exact hUse ⟨hr, h⟩), (roots s hr).2⟩
        · exact previous r hr e
      exact (ih built.2 R hr).trans (Nat.add_le_add_left mono _)

lemma chargesDisjoint {α ι : Type*} [DecidableEq α] (centres : Finset ι)
    (N : ι → Finset α) (bank : List (Finset α))
    (unique : ∀ s : Finset α, 1 < s.card → ∀ i ∈ centres, ∀ j ∈ centres,
      s ⊆ N i → s ⊆ N j → i = j) :
    ∑ i ∈ centres, charge (N i) bank ≤ bank.length := by
  classical
  induction bank with
  | nil => simp [charge]
  | cons s bank ih =>
    have e (i) : charge (N i) (s :: bank) = charge (N i) bank +
        if 1 < s.card ∧ s ⊆ N i then 1 else 0 := by
      by_cases h : 1 < s.card ∧ s ⊆ N i <;> simp [charge, h]
    have small : (centres.filter (fun i => 1 < s.card ∧ s ⊆ N i)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      obtain ⟨hic, hb, hin⟩ := Finset.mem_filter.mp hi
      obtain ⟨hjc, _, hjn⟩ := Finset.mem_filter.mp hj
      exact unique s hb i hic j hjc hin hjn
    simp only [e, Finset.sum_add_distrib, List.length_cons]
    rw [Finset.card_filter] at small
    omega

lemma pooledLeaves {α ι : Type*} [DecidableEq α] (centres : Finset ι)
    (N : ι → Finset α) (bank : List (Finset α)) (built : orBank bank)
    (roots : ι → Finset (Finset α))
    (valid : ∀ i ∈ centres, ∀ s ∈ roots i, available bank s ∧ s ⊆ N i)
    (unique : ∀ s : Finset α, 1 < s.card → ∀ i ∈ centres, ∀ j ∈ centres,
      s ⊆ N i → s ⊆ N j → i = j) :
    ∑ i ∈ centres, ((roots i).biUnion id).card ≤ (∑ i ∈ centres, (roots i).card) + bank.length := by
  calc
    _ ≤ ∑ i ∈ centres, ((roots i).card + charge (N i) bank) :=
      Finset.sum_le_sum (fun i hi => countDistinctLeaves (N i) bank built (roots i) (valid i hi))
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := Nat.add_le_add_left (chargesDisjoint centres N bank unique) _

lemma countStarBudget {α ι : Type*} [DecidableEq α] (centres : Finset ι)
    (N : ι → Finset α) (bank : List (Finset α)) (built : orBank bank)
    (roots : ι → Finset (Finset α)) (numStars size : ℕ)
    (valid : ∀ i ∈ centres, ∀ s ∈ roots i, available bank s ∧ s ⊆ N i)
    (unique : ∀ s : Finset α, 1 < s.card → ∀ i ∈ centres, ∀ j ∈ centres,
      s ⊆ N i → s ⊆ N j → i = j)
    (degree : ∀ i ∈ centres, (N i).card ≤ 4)
    (cover : 52 ≤ ∑ i ∈ centres, ((roots i).biUnion id).card)
    (terms : (∑ i ∈ centres, (roots i).card) ≤ numStars)
    (budget : bank.length + 2 * numStars ≤ size + 1 ∨
      14 ≤ numStars ∧ bank.length + 2 * numStars ≤ size + 2) : 64 ≤ size := by
  have lo := pooledLeaves centres N bank built roots valid unique
  have line (i) (hi : i ∈ centres) : ((roots i).biUnion id).card ≤ (roots i).card * 4 := by
    calc
      _ ≤ ∑ s ∈ roots i, s.card := Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ roots i, 4 :=
        Finset.sum_le_sum (fun s hs => (Finset.card_le_card (valid i hi s hs).2).trans (degree i hi))
      _ = _ := by simp
  have hi := Finset.sum_le_sum line
  rw [← Finset.sum_mul] at hi
  rcases budget with h | ⟨h, h'⟩ <;> omega

abbrev Vertex := Fin 13 ⊕ Fin 13

def incident (p l : Fin 13) : Prop := p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))

def neighbours : Vertex → Finset Vertex
  | .inl p => (Finset.univ.filter (fun l => decide (p - l ∈ ({0,1,3,9} : Finset (Fin 13))))).image Sum.inr
  | .inr l => (Finset.univ.filter (fun p => decide (p - l ∈ ({0,1,3,9} : Finset (Fin 13))))).image Sum.inl

def flagOf : Vertex → Vertex → Fin 13 × Fin 13
  | .inl p, .inr l => (p, l)
  | .inr l, .inl p => (p, l)
  | _, _ => (0, 0)

lemma fourNeighbours : ∀ v : Vertex, (neighbours v).card ≤ 4 := by decide +kernel

set_option maxHeartbeats 1000000 in
lemma intersectionSmall : ∀ a b : Vertex, a ≠ b → (neighbours a ∩ neighbours b).card ≤ 1 := by
  decide +kernel

lemma planeStarBound (bank : List (Finset Vertex)) (built : orBank bank)
    (roots : Vertex → Finset (Finset Vertex)) (numStars size : ℕ)
    (valid : ∀ i, ∀ s ∈ roots i, available bank s ∧ s ⊆ neighbours i)
    (cover : ∀ p l, incident p l →
      Sum.inr l ∈ (roots (.inl p)).biUnion id ∨ Sum.inl p ∈ (roots (.inr l)).biUnion id)
    (terms : (∑ i, (roots i).card) ≤ numStars)
    (budget : bank.length + 2 * numStars ≤ size + 1 ∨
      14 ≤ numStars ∧ bank.length + 2 * numStars ≤ size + 2) : 64 ≤ size := by
  classical
  apply countStarBudget Finset.univ neighbours bank built roots numStars size
    (fun i _ => valid i) _ (fun i _ => fourNeighbours i) _ terms budget
  · intro s hb i _ j _ hi hj
    by_contra diff
    have hcard := Finset.card_le_card (Finset.subset_inter hi hj)
    have bound := intersectionSmall i j diff
    omega
  · let flags := (Finset.univ : Finset (Fin 13 × Fin 13)).filter fun e =>
        decide (e.1 - e.2 ∈ ({0,1,3,9} : Finset (Fin 13)))
    have card : flags.card = 52 := by decide +revert +kernel
    let assigned := fun i => ((roots i).biUnion id).image (flagOf i)
    have allFlags : flags ⊆ Finset.univ.biUnion assigned := by
      rintro ⟨p, l⟩ h
      have hi : incident p l := by
        simpa only [flags, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, incident] using h
      rcases cover p l hi with hp | hl
      · exact Finset.mem_biUnion.mpr ⟨.inl p, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨.inr l, hp, rfl⟩⟩
      · exact Finset.mem_biUnion.mpr ⟨.inr l, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨.inl p, hl, rfl⟩⟩
    calc 52 = flags.card := card.symm
      _ ≤ _ := Finset.card_le_card allFlags
      _ ≤ ∑ i, (assigned i).card := Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.card_image_le)

lemma oneRootLeaves {α : Type*} [DecidableEq α] (bank : List (Finset α))
    (built : orBank bank) (s : Finset α) (root : available bank s) : s.card ≤ bank.length + 1 := by
  classical
  have hs : ∀ r ∈ ({s} : Finset (Finset α)), available bank r ∧ r ⊆ s := by
    intro r hr
    obtain rfl := Finset.mem_singleton.mp hr
    exact ⟨root, Finset.Subset.rfl⟩
  have hc := countDistinctLeaves s bank built {s} hs
  simp only [Finset.singleton_biUnion, id_eq, Finset.card_singleton] at hc
  have hle : charge s bank ≤ bank.length := List.length_filter_le ..
  omega

def vertexIndex : Vertex → Fin 13 := Sum.elim id id

lemma mixedCentres (C : Finset Vertex)
    (cover : ∀ p l, incident p l → Sum.inl p ∈ C ∨ Sum.inr l ∈ C)
    {p m : Fin 13} (hp : Sum.inl p ∈ C) (hm : Sum.inr m ∈ C) : 14 ≤ C.card := by
  classical
  have full : C.image vertexIndex = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    have hii : incident i i := by simp [incident]
    rcases cover i i hii with hi | hi
    · exact Finset.mem_image.mpr ⟨Sum.inl i, hi, rfl⟩
    · exact Finset.mem_image.mpr ⟨Sum.inr i, hi, rfl⟩
  by_contra! small
  have hcard : (C.image vertexIndex).card = C.card := by
    have hle := Finset.card_image_le (s := C) (f := vertexIndex)
    rw [full] at hle ⊢
    simp at hle ⊢
    omega
  have inj := Finset.card_image_iff.mp hcard
  have excl (i : Fin 13) (h : Sum.inl i ∈ C) : Sum.inr i ∉ C := by
    intro h'
    have bad := inj (x₁ := Sum.inl i) h (x₂ := Sum.inr i) h' rfl
    cases bad
  have step (i : Fin 13) (h : Sum.inl i ∈ C) : Sum.inl (i + 1) ∈ C := by
    have hi : incident (i + 1) i := by simp [incident]
    exact (cover (i+1) i hi).resolve_right (excl i h)
  have orbit (d : ℕ) : Sum.inl (p + d • (1 : Fin 13)) ∈ C := by
    induction d with
    | zero => simpa using hp
    | succ d ih => simpa [succ_nsmul, add_assoc] using step _ ih
  have reach : ∀ a b : Fin 13, a + (b-a).val • (1 : Fin 13) = b := by decide +kernel
  have h := orbit (m-p).val
  rw [reach] at h
  exact excl m h hm

def prefixBank {α : Type*} (support : ℕ → Finset α) (mark : ℕ → Bool) : ℕ → List (Finset α)
  | 0 => []
  | n+1 => if mark n then support n :: prefixBank support mark n else prefixBank support mark n

def prior {α : Type*} (support : ℕ → Finset α) (w : ℕ) (s : Finset α) : Prop :=
  s.card ≤ 1 ∨ ∃ u < w, support u = s

lemma buildFromWires {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (mark : ℕ → Bool) (n : ℕ)
    (step : ∀ w < n, prior support w (support w) ∨
      (mark w = true ∧ ∃ a b, prior support w a ∧ prior support w b ∧ support w = a ∪ b)) :
    orBank (prefixBank support mark n) ∧ ∀ w < n, available (prefixBank support mark n) (support w) := by
  induction n with
  | zero => exact ⟨trivial, by omega⟩
  | succ n ih =>
    obtain ⟨hb, hw⟩ := ih (fun w h => step w (by omega))
    have prev (s) (hs : prior support n s) : available (prefixBank support mark n) s := by
      rcases hs with h | ⟨u, hu, rfl⟩
      · exact Or.inl h
      · exact hw u hu
    have st := step n (by omega)
    by_cases m : mark n = true
    · simp only [prefixBank, m, ↓reduceIte]
      refine ⟨⟨?_, hb⟩, ?_⟩
      · rcases st with h | ⟨_, a, b, ha, hba, eq⟩
        · exact Or.inr ⟨support n, ∅, prev _ h, Or.inl (by simp), by simp⟩
        · exact Or.inr ⟨a, b, prev _ ha, prev _ hba, eq⟩
      · intro w h
        by_cases he : w = n
        · subst w
          exact Or.inr List.mem_cons_self
        · rcases hw w (by omega) with hs | hs
          · exact Or.inl hs
          · exact Or.inr (List.mem_cons_of_mem _ hs)
    · simp only [prefixBank, m]
      refine ⟨hb, ?_⟩
      intro w h
      by_cases he : w = n
      · subst w
        exact prev _ (st.resolve_right (fun hm => m hm.1))
      · exact hw w (by omega)

lemma prefixBank_length {α : Type*} (support : ℕ → Finset α) (mark : ℕ → Bool) (n : ℕ) :
    (prefixBank support mark n).length = ((Finset.range n).filter (fun w => mark w = true)).card := by
  induction n with
  | zero => simp [prefixBank]
  | succ n ih => cases h : mark n <;> simp [prefixBank, h, ih, Finset.range_add_one, Finset.filter_insert]

def preferred {α : Type*} [DecidableEq α] (side s : Finset α) : Finset α :=
  if Disjoint s side then s else s ∩ side

lemma preferred_pure {α : Type*} [DecidableEq α] {side s : Finset α}
    (pure : Disjoint s side ∨ s ⊆ side) : preferred side s = s := by
  unfold preferred
  split_ifs with h
  · rfl
  · exact Finset.inter_eq_left.mpr (pure.resolve_left h)

lemma preferred_projection {α : Type*} [DecidableEq α] (side s : Finset α) :
    s ∩ side = ∅ ∨ s ∩ side = preferred side s := by
  by_cases h : Disjoint s side
  · exact Or.inl (Finset.disjoint_iff_inter_eq_empty.mp h)
  · exact Or.inr (by simp [preferred, h])

lemma preferred_union {α : Type*} [DecidableEq α] (side a b : Finset α) :
    ∃ u v, (u = ∅ ∨ u = preferred side a) ∧ (v = ∅ ∨ v = preferred side b) ∧
      preferred side (a ∪ b) = u ∪ v := by
  by_cases h : Disjoint (a ∪ b) side
  · have d := Finset.disjoint_union_left.mp h
    exact ⟨a, b, Or.inr (by simp [preferred, d.1]), Or.inr (by simp [preferred, d.2]),
      by simp [preferred, h]⟩
  · exact ⟨a ∩ side, b ∩ side, preferred_projection _ _, preferred_projection _ _,
      by simp [preferred, h, Finset.union_inter_distrib_right]⟩

lemma preferred_small {α : Type*} [DecidableEq α] (side s : Finset α) (h : s.card ≤ 1) :
    (preferred side s).card ≤ 1 := by
  apply (Finset.card_le_card ?_).trans h
  unfold preferred
  split <;> first | exact Finset.Subset.rfl | exact Finset.inter_subset_left

lemma projectedWireBank {α : Type*} [DecidableEq α] (S : ℕ → Finset α)
    (side : Finset α) (paid : ℕ → Bool) (n : ℕ)
    (step : ∀ w < n, (S w).card ≤ 1 ∨ (∃ u < w, S w = S u) ∨
      (paid w = true ∧ ∃ a < w, ∃ b < w, S w = S a ∪ S b)) :
    let bank := prefixBank (fun w => preferred side (S w)) paid n
    orBank bank ∧
      (∀ w < n, (Disjoint (S w) side ∨ S w ⊆ side) → available bank (S w)) ∧
      (∀ w < n, available bank (S w ∩ side)) ∧
      bank.length = ((Finset.range n).filter (fun w => paid w = true)).card := by
  intro bank
  let F := fun w => preferred side (S w)
  have legal (w) (hw : w < n) : prior F w (F w) ∨
      (paid w = true ∧ ∃ a b, prior F w a ∧ prior F w b ∧ F w = a ∪ b) := by
    rcases step w hw with h | ⟨u, hu, eq⟩ | ⟨cost, a, ha, b, hb, eq⟩
    · exact Or.inl (Or.inl (preferred_small _ _ h))
    · exact Or.inl (Or.inr ⟨u, hu, congrArg (preferred side) eq.symm⟩)
    · obtain ⟨u, v, hu, hv, huv⟩ := preferred_union side (S a) (S b)
      have prior' (i) (hi : i < w) (s) (hs : s = ∅ ∨ s = F i) : prior F w s := by
        rcases hs with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr ⟨i, hi, rfl⟩
      exact Or.inr ⟨cost, u, v, prior' a ha u hu, prior' b hb v hv, (congrArg _ eq).trans huv⟩
  obtain ⟨built, seen⟩ := buildFromWires F paid n legal
  refine ⟨built, ?_, ?_, prefixBank_length ..⟩
  · intro w hw pure
    rw [← preferred_pure pure]
    exact seen w hw
  · intro w hw
    rcases preferred_projection side (S w) with e | e
    · exact Or.inl (by simp [e])
    · rw [e]
      exact seen w hw

lemma terminalCount {E : ℕ → ℕ → Prop} {O : ℕ → Prop} (out n : ℕ) (bound : out < n)
    (T : Finset ℕ) (free : ∀ s ∈ T, ¬ O s)
    (binary : ∀ w < n, O w → ∃ a < w, ∃ b < w, ∀ u, E u w ↔ u = a ∨ u = b)
    (reaches : ∀ s ∈ T, Relation.ReflTransGen (fun a b => E a b ∧ O b) s out) :
    let R := Relation.ReflTransGen (fun a b => E a b ∧ O b)
    T.card ≤ ((Finset.range n).filter (fun w => @decide (O w ∧ R w out) (Classical.propDecidable _))).card + 1 := by
  classical
  intro R
  let S := fun w => if R w out then T.filter (fun s => R s w) else ∅
  let paid := fun w => decide (O w ∧ R w out)
  have step (w) (hw : w < n) : prior S w (S w) ∨
      (paid w = true ∧ ∃ a b, prior S w a ∧ prior S w b ∧ S w = a ∪ b) := by
    by_cases rout : R w out
    · by_cases ow : O w
      · obtain ⟨a, ha, b, hb, inputs⟩ := binary w hw ow
        have ar : R a w := .single ⟨(inputs a).mpr (Or.inl rfl), ow⟩
        have br : R b w := .single ⟨(inputs b).mpr (Or.inr rfl), ow⟩
        refine Or.inr ⟨by simp [paid, ow, rout], S a, S b,
          Or.inr ⟨a, ha, rfl⟩, Or.inr ⟨b, hb, rfl⟩, ?_⟩
        ext s
        have ao : R a out := ar.trans rout
        have bo : R b out := br.trans rout
        simp only [S, rout, ao, bo, ite_true, Finset.mem_filter, Finset.mem_union]
        constructor
        · rintro ⟨hs, path⟩
          rcases path.cases_tail with eq | ⟨u, path, e, _⟩
          · exact (free s hs (eq ▸ ow)).elim
          · rcases (inputs u).mp e with rfl | rfl
            · exact Or.inl ⟨hs, path⟩
            · exact Or.inr ⟨hs, path⟩
        · rintro (⟨hs, path⟩ | ⟨hs, path⟩)
          · exact ⟨hs, path.trans ar⟩
          · exact ⟨hs, path.trans br⟩
      · left
        left
        have sub : S w ⊆ {w} := by
          intro s hs
          have mem : s ∈ T ∧ R s w := by simpa [S, rout] using hs
          have path := mem.2
          rcases path.cases_tail with eq | ⟨_, _, _, ho⟩
          · exact Finset.mem_singleton.mpr eq.symm
          · exact (ow ho).elim
        simpa using Finset.card_le_card sub
    · exact Or.inl (Or.inl (by simp [S, rout]))
  obtain ⟨built, seen⟩ := buildFromWires S paid n step
  have root : S out = T := by
    simp only [S, show R out out from .refl, ite_true]
    exact Finset.filter_true_of_mem reaches
  have h := oneRootLeaves _ built _ (seen out bound)
  rw [root, prefixBank_length] at h
  simpa only [paid, decide_eq_true_eq] using h

lemma namedStars {ι : Type*} [DecidableEq ι] (tokens : Finset ι) (centre : ι → Vertex)
    (leaves : ι → Finset Vertex) (bank : List (Finset Vertex)) (built : orBank bank) (size : ℕ)
    (valid : ∀ t ∈ tokens, available bank (leaves t) ∧ leaves t ⊆ neighbours (centre t))
    (covers : ∀ p l, incident p l → ∃ t ∈ tokens,
      (centre t = .inl p ∧ .inr l ∈ leaves t) ∨ (centre t = .inr l ∧ .inl p ∈ leaves t))
    (budget : bank.length + 2 * tokens.card ≤ size + 1 ∨
      (∃ t ∈ tokens, ∃ p, centre t = .inl p) ∧ (∃ t ∈ tokens, ∃ l, centre t = .inr l) ∧
      bank.length + 2 * tokens.card ≤ size + 2) : 64 ≤ size := by
  classical
  let group := fun v => tokens.filter (fun t => centre t = v)
  let roots := fun v => (group v).image leaves
  apply planeStarBound bank built roots tokens.card size
  · intro v s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    have facts : t ∈ tokens ∧ centre t = v := Finset.mem_filter.mp ht
    exact facts.2 ▸ valid t facts.1
  · intro p l hi
    obtain ⟨t, ht, h | h⟩ := covers p l hi
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨leaves t,
        Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, h.1⟩, rfl⟩, h.2⟩)
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨leaves t,
        Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, h.1⟩, rfl⟩, h.2⟩)
  · calc
      _ ≤ ∑ v : Vertex, (group v).card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      _ = _ := by
        simp only [group, Finset.card_filter]
        rw [Finset.sum_comm]
        simp
  · rcases budget with h | ⟨⟨t, ht, p, hp⟩, ⟨u, hu, l, hl⟩, bound⟩
    · exact Or.inl h
    · have cmem (z) (hz : z ∈ tokens) : centre z ∈ tokens.image centre :=
        Finset.mem_image_of_mem _ hz
      have cov (x y) (hxy : incident x y) :
          Sum.inl x ∈ tokens.image centre ∨ Sum.inr y ∈ tokens.image centre := by
        obtain ⟨z, hz, h | h⟩ := covers x y hxy
        · exact Or.inl (h.1 ▸ cmem z hz)
        · exact Or.inr (h.1 ▸ cmem z hz)
      have mixed := mixedCentres _ cov (hp ▸ cmem t ht) (hm := hl ▸ cmem u hu)
      exact Or.inr ⟨mixed.trans Finset.card_image_le, bound⟩

abbrev pass (E : ℕ → ℕ → Prop) (O : ℕ → Prop) :=
  Relation.ReflTransGen (fun a b => E a b ∧ O b)

noncomputable def sourceSet {α : Type*} [Fintype α] (src : α → ℕ → Prop)
    (R : ℕ → ℕ → Prop) (w : ℕ) : Finset α := by
  classical
  exact Finset.univ.filter (fun x => ∃ u, src x u ∧ R u w)

lemma source_mem {α : Type*} [Fintype α] (src : α → ℕ → Prop) (R : ℕ → ℕ → Prop)
    (w : ℕ) (x : α) :
    x ∈ sourceSet src R w ↔ ∃ u, src x u ∧ R u w := by classical simp [sourceSet]

lemma source_or {α : Type*} [Fintype α] [DecidableEq α] {E : ℕ → ℕ → Prop} {O : ℕ → Prop}
    (src : α → ℕ → Prop) (noOr : ∀ x u, src x u → ¬ O u) {a b w : ℕ}
    (ow : O w) (read : ∀ u, E u w ↔ u = a ∨ u = b) :
    sourceSet src (pass E O) w = sourceSet src (pass E O) a ∪ sourceSet src (pass E O) b := by
  classical
  ext x
  simp only [Finset.mem_union, source_mem]
  constructor
  · rintro ⟨s, hs, path⟩
    rcases path.cases_tail with eq | ⟨u, hu, e, _⟩
    · exact (noOr x s hs (eq ▸ ow)).elim
    · rcases (read u).mp e with rfl | rfl
      · exact Or.inl ⟨s, hs, hu⟩
      · exact Or.inr ⟨s, hs, hu⟩
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
    · exact ⟨s, hs, h.tail ⟨(read a).mpr (Or.inl rfl), ow⟩⟩
    · exact ⟨s, hs, h.tail ⟨(read b).mpr (Or.inr rfl), ow⟩⟩

lemma source_nonOr {α : Type*} [Fintype α] {E : ℕ → ℕ → Prop} {O : ℕ → Prop}
    (src : α → ℕ → Prop) {w : ℕ} (hw : ¬ O w) (x : α) :
    x ∈ sourceSet src (pass E O) w ↔ src x w := by
  rw [source_mem]
  constructor
  · rintro ⟨u, hs, path⟩
    rcases path.cases_tail with e | ⟨_, _, _, h⟩
    · exact e ▸ hs
    · exact (hw h).elim
  · exact fun h => ⟨w, h, .refl⟩

def vertexWire : Vertex → ℕ
  | .inl p => p.val
  | .inr l => 13 + l.val

lemma vertexWire_inj : Function.Injective vertexWire := by
  rintro (p | l) (q | m) eq
  all_goals simp only [vertexWire] at eq
  · exact congrArg Sum.inl (Fin.ext eq)
  · have := p.isLt
    omega
  · have := q.isLt
    omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

noncomputable def baseSet (E : ℕ → ℕ → Prop) (O : ℕ → Prop) :=
  sourceSet (fun x w => vertexWire x = w) (pass E O)

lemma mem_base (E : ℕ → ℕ → Prop) (O : ℕ → Prop) (w) (x) :
    x ∈ baseSet E O w ↔ pass E O (vertexWire x) w := by simp [baseSet, source_mem]

def selectedSources (E : ℕ → ℕ → Prop) (O : ℕ → Prop) (enabled : Prop)
    (inner child : ℕ) (x : Vertex) (u : ℕ) : Prop :=
  vertexWire x = u ∨ enabled ∧ u = inner ∧ pass E O (vertexWire x) child

lemma selected_mem (E : ℕ → ℕ → Prop) (O : ℕ → Prop) (enabled : Prop)
    (inner child w : ℕ) (x : Vertex) :
    x ∈ sourceSet (selectedSources E O enabled inner child) (pass E O) w ↔
    pass E O (vertexWire x) w ∨ enabled ∧ pass E O inner w ∧ pass E O (vertexWire x) child := by
  rw [source_mem]
  constructor
  · rintro ⟨u, e | ⟨he, rfl, hc⟩, path⟩
    · exact Or.inl (e ▸ path)
    · exact Or.inr ⟨he, path, hc⟩
  · rintro (h | ⟨he, hw, hc⟩)
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr ⟨he, rfl, hc⟩, hw⟩

lemma pass_le {E : ℕ → ℕ → Prop} {O : ℕ → Prop}
    (back : ∀ a b, E a b → a < b) {a b} (h : pass E O a b) : a ≤ b := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ e ih => exact ih.trans (Nat.le_of_lt (back _ _ e.1))

lemma bankAndTerminals (E : ℕ → ℕ → Prop) (O : ℕ → Prop) (n out inner child : ℕ)
    (enabled : Prop) (side : Finset Vertex) (T : Finset ℕ) (bound : out < n)
    (back : ∀ a b, E a b → a < b)
    (binary : ∀ w < n, O w → ∃ a < w, ∃ b < w, ∀ u, E u w ↔ u = a ∨ u = b)
    (internal : ∀ w, O w → 26 ≤ w)
    (ihigh : 26 ≤ inner) (ifree : ¬ O inner) (childBefore : child < inner)
    (noInput : ∀ x, ¬ pass E O (vertexWire x) out)
    (noBypass : enabled → ¬ pass E O inner out)
    (terms : ∀ s ∈ T, 26 ≤ s ∧ s < n ∧ ¬ O s ∧ pass E O s out) :
    let S := sourceSet (selectedSources E O enabled inner child) (pass E O)
    ∃ bank, orBank bank ∧
      (∀ w < n, (Disjoint (S w) side ∨ S w ⊆ side) → available bank (S w)) ∧
      (∀ w < n, available bank (S w ∩ side)) ∧
      bank.length + 2*T.card ≤ (n-26)+1 ∧
      (inner < n → inner ∉ T → bank.length + 2*T.card ≤ n-26) := by
  classical
  intro S
  let R := pass E O
  let paid := fun w => decide (O w ∧ ¬ R w out)
  have inputBound (x : Vertex) : vertexWire x < 26 := by
    cases x with
    | inl p => exact lt_trans p.isLt (by decide)
    | inr l => simp only [vertexWire]; have := l.isLt; omega
  have noOr (x u) (hu : selectedSources E O enabled inner child x u) : ¬ O u := by
    rcases hu with rfl | ⟨_, rfl, _⟩
    · intro h
      have := internal _ h
      have := inputBound x
      omega
    · exact ifree
  have step (w) (hw : w < n) : (S w).card ≤ 1 ∨ (∃ u < w, S w = S u) ∨
      (paid w = true ∧ ∃ a < w, ∃ b < w, S w = S a ∪ S b) := by
    by_cases ow : O w
    · by_cases rout : R w out
      · have empty : S w = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          rcases (selected_mem ..).mp hx with path | ⟨he, path, _⟩
          · exact noInput x (path.trans rout)
          · exact noBypass he (path.trans rout)
        exact Or.inl (by simp [empty])
      · obtain ⟨a, ha, b, hb, read⟩ := binary w hw ow
        exact Or.inr (Or.inr ⟨by simp [paid, ow, rout], a, ha, b, hb, source_or _ noOr ow read⟩)
    · by_cases on : enabled ∧ w = inner
      · obtain ⟨he, rfl⟩ := on
        right; left
        refine ⟨child, childBefore, ?_⟩
        ext x
        have neq : vertexWire x ≠ w := by have := inputBound x; omega
        have nop : ¬ pass E O w child := by intro h; have := pass_le back h; omega
        rw [source_nonOr _ ow, selected_mem]
        simp [selectedSources, neq, he, nop]
      · left
        apply Finset.card_le_one.mpr
        intro x hx y hy
        have f (z) (hz : z ∈ S w) : vertexWire z = w := by
          rcases (source_nonOr _ ow z).mp hz with eq | ⟨he, eq, _⟩
          · exact eq
          · exact (on ⟨he, eq⟩).elim
        exact vertexWire_inj ((f x hx).trans (f y hy).symm)
  obtain ⟨built, pure, proj, count⟩ := projectedWireBank S side paid n step
  refine ⟨_, built, pure, proj, ?_⟩
  rw [count]
  let lower := (Finset.range n).filter (fun w => paid w = true)
  let upper := (Finset.range n).filter (fun w => decide (O w ∧ R w out) = true)
  have uBound : T.card ≤ upper.card + 1 := by
    simpa only [upper, decide_eq_true_eq] using
      terminalCount out n bound T (fun s hs => (terms s hs).2.2.1) binary
        (fun s hs => (terms s hs).2.2.2)
  have dl : Disjoint lower upper := by
    apply Finset.disjoint_left.mpr
    intro w hl hu
    simp [lower, paid] at hl
    simp [upper] at hu
    exact hl.2.2 hu.2.2
  have allOr (w) (hw : w ∈ lower ∪ upper) : 26 ≤ w ∧ w < n ∧ O w := by
    rcases Finset.mem_union.mp hw with h | h
    · simp [lower, paid] at h
      exact ⟨internal _ h.2.1, h.1, h.2.1⟩
    · simp [upper] at h
      exact ⟨internal _ h.2.1, h.1, h.2.1⟩
  have dT : Disjoint (lower ∪ upper) T := by
    apply Finset.disjoint_left.mpr
    intro w hw ht
    exact (terms w ht).2.2.1 (allOr w hw).2.2
  let used := (lower ∪ upper) ∪ T
  have sub : used ⊆ Finset.Ico 26 n := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_Ico.mpr ⟨(allOr _ hw).1, (allOr _ hw).2.1⟩
    · exact Finset.mem_Ico.mpr ⟨(terms _ hw).1, (terms _ hw).2.1⟩
  have uc : used.card = lower.card + upper.card + T.card := by
    rw [show used = (lower ∪ upper) ∪ T from rfl,
      Finset.card_union_of_disjoint dT, Finset.card_union_of_disjoint dl]
  change lower.card + 2*T.card ≤ n-26+1 ∧ _
  constructor
  · have h := Finset.card_le_card sub
    rw [uc, Nat.card_Ico] at h
    omega
  · intro ib hnt
    have hnu : inner ∉ used := by
      intro hin
      rcases Finset.mem_union.mp hin with h | h
      · exact ifree (allOr _ h).2.2
      · exact hnt h
    have hsub : insert inner used ⊆ Finset.Ico 26 n :=
      Finset.insert_subset (Finset.mem_Ico.mpr ⟨ihigh, ib⟩) sub
    have h := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnu, uc, Nat.card_Ico] at h
    change lower.card + 2*T.card ≤ n-26
    omega

def readsWire (C : Circuit) := wireRead 26 C.gates.length (fun j => (gateAt C j).inputs)

def wireAnd (C : Circuit) (w : ℕ) : Prop :=
  26 ≤ w ∧ (gateAt C (w-26)).op = GateOp.and

def wireOr (C : Circuit) (w : ℕ) : Prop :=
  26 ≤ w ∧ (gateAt C (w-26)).op = GateOp.or

lemma existingGate (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma invalidGate (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨.or, []⟩ := by simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

lemma actualAnd (C : Circuit) {j : ℕ} (hop : (gateAt C j).op = GateOp.and) :
    j < C.gates.length := by
  by_contra! h
  rw [invalidGate C h] at hop
  cases hop

lemma readBackWire (C : Circuit) (rb : ReadsBack 26 C) {u w} (e : readsWire C u w) : u < w := by
  obtain ⟨hw, hj, hi⟩ := e
  have ht := rb _ hj _ hi
  omega

lemma gateTags (C : Circuit) (mono : Monotone2 C) {w} (hw : 26 ≤ w) :
    wireOr C w ∨ wireAnd C w := by
  by_cases h : w-26 < C.gates.length
  · have op := (mono _ (existingGate C h)).1
    change (gateAt C (w-26)).op = GateOp.and ∨ (gateAt C (w-26)).op = GateOp.or at op
    exact op.elim (fun ha => Or.inr ⟨hw, ha⟩) (fun ho => Or.inl ⟨hw, ho⟩)
  · exact Or.inl ⟨hw, by rw [invalidGate C (by omega)]⟩

lemma realOperands (C : Circuit) (rb : ReadsBack 26 C)
    (two : ∀ g ∈ C.gates, g.inputs.length = 2) {w} (hi : 26 ≤ w) (hw : w < 26+C.size) :
    ∃ a < w, ∃ b < w, (gateAt C (w-26)).inputs = [a,b] ∧
      ∀ u, readsWire C u w ↔ u = a ∨ u = b := by
  have hlen : w-26 < C.gates.length := by change w < 26+C.gates.length at hw; omega
  have hl := two _ (existingGate C hlen)
  obtain ⟨a, b, eq⟩ := List.length_eq_two.mp hl
  have h (u) : readsWire C u w ↔ u = a ∨ u = b := by
    simp [readsWire, wireRead, hi, hlen, eq]
  exact ⟨a, readBackWire C rb ((h a).mpr (Or.inl rfl)), b,
    readBackWire C rb ((h b).mpr (Or.inr rfl)), eq, h⟩

lemma circuitCone (C : Circuit) (rb : ReadsBack 26 C) (i j) :
    InCone 26 C i j ↔ Relation.TransGen (readsWire C) (26+i) (26+j) :=
  conePathBridge rb (cones_char 26 C.gates) i j

lemma uniqueAndPath (C : Circuit) (rb : ReadsBack 26 C) (lo : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    {i j} (ai : (gateAt C i).op = GateOp.and) (aj : (gateAt C j).op = GateOp.and)
    (ij : InCone 26 C i j) {a b} (aa : wireAnd C a) (ab : wireAnd C b)
    (path : Relation.TransGen (readsWire C) a b) : a = 26+i ∧ b = 26+j := by
  have first : (26+(a-26)) = a := by have := aa.1; omega
  have second : (26+(b-26)) = b := by have := ab.1; omega
  have hab : InCone 26 C (a-26) (b-26) :=
    (circuitCone C rb _ _).mpr (by rwa [first, second])
  letI := gateOpDecEq
  let pairs := (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
    fun p => (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 26 C p.1 p.2
  change pairs.card ≤ 1 at lo
  have mem {u v} (hu : (gateAt C u).op = GateOp.and) (hv : (gateAt C v).op = GateOp.and)
      (h : InCone 26 C u v) : (u,v) ∈ pairs := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (actualAnd C hu),
        Finset.mem_range.mpr (actualAnd C hv)⟩, show (gateAt C (u,v).1).op = GateOp.and ∧
        (gateAt C (u,v).2).op = GateOp.and ∧ InCone 26 C (u,v).1 (u,v).2 from ⟨hu, hv, h⟩⟩
  have eq : (a-26,b-26) = (i,j) := Finset.card_le_one.mp lo _ (mem aa.2 ab.2 hab) _ (mem ai aj ij)
  have aeq := congrArg Prod.fst eq
  have beq := congrArg Prod.snd eq
  simp only [Prod.fst, Prod.snd] at aeq beq
  omega

lemma realValue (C : Circuit) (rb : ReadsBack 26 C) (L : List Bool) (len : L.length = 26)
    {w} (hi : 26 ≤ w) (hw : w < 26+C.size) :
    V C.gates L w = (gateAt C (w-26)).op.eval ((gateAt C (w-26)).inputs.map (V C.gates L)) := by
  have j : w-26 < C.gates.length := by change w < 26+C.gates.length at hw; omega
  have eq : C.gates[w-26]? = some (gateAt C (w-26)) := by
    simp [gateAt, List.getD_eq_getElem?_getD, j]
  have v := gate_val_aux C.gates L len (w-26) _ eq (rb _ j)
  rwa [show 26+(w-26) = w by omega] at v

lemma invalidValue (C : Circuit) (L : List Bool) (len : L.length = 26)
    {w} (hw : 26+C.size ≤ w) : V C.gates L w = false := by
  have h : (wiresFrom C.gates L).length ≤ w := by rwa [length_wiresFrom, len]
  simp [V, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma wireOrValue (C : Circuit) (rb : ReadsBack 26 C) (L : List Bool) (len : L.length = 26)
    (w) (ow : wireOr C w) : V C.gates L w = true ↔ ∃ u, readsWire C u w ∧ V C.gates L u = true := by
  by_cases hw : w < 26+C.size
  · have hj : w-26 < C.gates.length := by
      change w < 26+C.gates.length at hw
      have := ow.1
      omega
    rw [realValue C rb L len ow.1 hw, ow.2]
    simp [GateOp.eval, readsWire, wireRead, ow.1, hj]
  · rw [invalidValue C L len (by omega)]
    have hj : ¬ w-26 < C.gates.length := by change ¬ w < 26+C.gates.length at hw; omega
    simp [readsWire, wireRead, hj]

lemma wireAndValue (C : Circuit) (rb : ReadsBack 26 C) (L : List Bool) (len : L.length = 26)
    {w a b} (aw : wireAnd C w) (eq : (gateAt C (w-26)).inputs = [a,b]) :
    V C.gates L w = true ↔ V C.gates L a = true ∧ V C.gates L b = true := by
  have hw : w < 26+C.size := by
    change w < 26+C.gates.length
    have := actualAnd C aw.2
    have := aw.1
    omega
  rw [realValue C rb L len aw.1 hw, aw.2, eq]
  simp [GateOp.eval]

def absent (Q : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun l => ∀ p ∈ Q, p-l ∉ D)

lemma absent_iff (Q : Finset (Fin 13)) (l : Fin 13) : l ∈ absent Q ↔ miss Q l := by
  simp [absent, miss, inc]

def pairVal (C : Circuit) (p l : Fin 13) (w : ℕ) : Prop :=
  V C.gates (inp {p} {l}) w = true

def quadVal (C : Circuit) (Q : Finset (Fin 13)) (w : ℕ) : Prop :=
  V C.gates (inp Q (absent Q)) w = true

def Fits (C : Circuit) : Prop :=
  (∀ p l, inc p l → pairVal C p l C.output) ∧ ∀ Q, quad Q → ¬ quadVal C Q C.output

noncomputable def terminalSet (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range (26+C.size)).filter (fun w => wireAnd C w ∧
    pass (readsWire C) (wireOr C) w C.output)

lemma terminal_mem (C : Circuit) (w) :
    w ∈ terminalSet C ↔ w < 26+C.size ∧ wireAnd C w ∧ pass (readsWire C) (wireOr C) w C.output := by
  classical simp [terminalSet]

lemma noInputPath (C : Circuit) (rb : ReadsBack 26 C) (good : Fits C) (x : Vertex) :
    ¬ pass (readsWire C) (wireOr C) (vertexWire x) C.output := by
  intro path
  have emit (Q) (hq : quad Q) (hit : quadVal C Q (vertexWire x)) : False :=
    good.2 Q hq (propagate (wireOrValue C rb _ (inp_len _ _)) path hit)
  cases x with
  | inl p =>
    have off : ∀ p : Fin 13, ∃ l, ¬ inc p l := by decide +kernel
    obtain ⟨l, hl⟩ := off p
    obtain ⟨Q, hq, hp, _, _⟩ := mixedPLLines p l l hl hl
    apply emit Q hq
    simpa [quadVal, vertexWire, V_point _ _ _ _ p.isLt] using hp
  | inr l =>
    have off : ∀ l : Fin 13, ∃ p, ¬ inc p l := by decide +kernel
    obtain ⟨p, hp⟩ := off l
    obtain ⟨Q, hq, hl, _, _⟩ := mixedLPPoints l p p hp hp
    apply emit Q hq
    have len : 13+l.val < 26 := by have := l.isLt; omega
    simpa [quadVal, vertexWire, V_line _ _ _ _ (by omega : 13 ≤ 13+l.val) len,
      absent_iff] using hl

lemma validOutput (C : Circuit) (good : Fits C) : C.output < 26+C.size := by
  by_contra! bad
  have h := good.1 0 0 (by decide)
  change V _ _ _ = true at h
  rw [invalidValue C _ (inp_len _ _) bad] at h
  cases h

lemma terminalCover (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C) (good : Fits C)
    (p l) (edge : inc p l) : ∃ w ∈ terminalSet C, pairVal C p l w := by
  have v := good.1 p l edge
  obtain ⟨w, no, path, hv⟩ := (boundaryWire (fun _ _ => readBackWire C rb)
    (wireOrValue C rb _ (inp_len _ _)) C.output).mp v
  have vb := validOutput C good
  have le := pass_le (fun _ _ => readBackWire C rb) path
  have internal : 26 ≤ w := by
    by_contra! hin
    by_cases pt : w < 13
    · exact noInputPath C rb good (.inl ⟨w, pt⟩) path
    · let l' : Fin 13 := ⟨w-13, by omega⟩
      have eq : vertexWire (.inr l') = w := by dsimp [vertexWire, l']; omega
      exact noInputPath C rb good (.inr l') (eq ▸ path)
  exact ⟨w, (terminal_mem C w).mpr ⟨by omega, (gateTags C mono internal).resolve_left no, path⟩, hv⟩

lemma terminalReject (C : Circuit) (rb : ReadsBack 26 C) (good : Fits C)
    {w} (hw : w ∈ terminalSet C) {Q} (hq : quad Q) : ¬ quadVal C Q w := by
  intro hv
  exact good.2 Q hq (propagate (wireOrValue C rb _ (inp_len _ _)) ((terminal_mem C w).mp hw).2.2 hv)

lemma physicalBank (C : Circuit) (rb : ReadsBack 26 C) (good : Fits C)
    (two : ∀ g ∈ C.gates, g.inputs.length = 2) {h a} (ah : wireAnd C h) (early : a < h)
    (on : Prop) (side : Finset Vertex)
    (noBypass : on → ¬ pass (readsWire C) (wireOr C) h C.output) :
    let S := sourceSet (selectedSources (readsWire C) (wireOr C) on h a) (pass (readsWire C) (wireOr C))
    let T := terminalSet C
    ∃ bank, orBank bank ∧
      (∀ w < 26+C.size, (Disjoint (S w) side ∨ S w ⊆ side) → available bank (S w)) ∧
      (∀ w < 26+C.size, available bank (S w ∩ side)) ∧
      bank.length + 2*T.card ≤ C.size+1 ∧
      (h ∉ T → bank.length + 2*T.card ≤ C.size) := by
  intro S T
  have disj (w) (aw : wireAnd C w) : ¬ wireOr C w := by
    rintro ⟨_, o⟩
    have bad := aw.2.symm.trans o
    cases bad
  have binary (w) (hw : w < 26+C.size) (ow : wireOr C w) :
      ∃ i < w, ∃ j < w, ∀ u, readsWire C u w ↔ u = i ∨ u = j := by
    obtain ⟨i, hi, j, hj, _, read⟩ := realOperands C rb two ow.1 hw
    exact Exists.intro i (And.intro hi (Exists.intro j (And.intro hj read)))
  have terms (w) (hw : w ∈ T) := (terminal_mem C w).mp hw
  obtain ⟨bank, built, pure, proj, b₁, b₂⟩ := bankAndTerminals (readsWire C) (wireOr C)
    (26+C.size) C.output h a on side T (validOutput C good) (fun _ _ => readBackWire C rb)
    binary (fun _ ho => ho.1) ah.1 (disj h ah) early (noInputPath C rb good) noBypass
    (fun w hw => ⟨(terms w hw).2.1.1, (terms w hw).1, disj w (terms w hw).2.1, (terms w hw).2.2⟩)
  have hl : h < 26+C.size := by
    change h < 26+C.gates.length
    have := actualAnd C ah.2
    have := ah.1
    omega
  exact ⟨bank, built, pure, proj, by simpa using b₁, fun hn => by simpa using b₂ hl hn⟩

abbrev rr (C : Circuit) := pass (readsWire C) (wireOr C)

abbrev pointsAt (C : Circuit) (w : ℕ) (p : Fin 13) : Prop := rr C p.val w

abbrev linesAt (C : Circuit) (w : ℕ) (l : Fin 13) : Prop := rr C (13+l.val) w

lemma raw_pair (C : Circuit) (p l : Fin 13) (w) :
    rawHit (readsWire C) (wireOr C) (pairVal C p l) w ↔ pointsAt C w p ∨ linesAt C w l := by
  have pv (q : Fin 13) : pairVal C p l q.val ↔ q = p := by
    simp [pairVal, V_point _ _ _ _ q.isLt]
  have lv (m : Fin 13) : pairVal C p l (13+m.val) ↔ m = l := by
    have h := m.isLt
    simp [pairVal, V_line _ _ _ _ (by omega : 13 ≤ 13+m.val) (by omega : 13+m.val < 26)]
  simpa [meets, pointsAt, linesAt, rr, pass, orPath] using
    rawHit_eq_meets (E := readsWire C) (O := wireOr C) pv lv w

lemma raw_quad (C : Circuit) (Q : Finset (Fin 13)) (w) :
    rawHit (readsWire C) (wireOr C) (quadVal C Q) w ↔
      meets (pointsAt C w) (linesAt C w) (· ∈ Q) (miss Q) := by
  have pv (q : Fin 13) : quadVal C Q q.val ↔ q ∈ Q := by
    simp [quadVal, V_point _ _ _ _ q.isLt]
  have lv (m : Fin 13) : quadVal C Q (13+m.val) ↔ miss Q m := by
    have h := m.isLt
    simp [quadVal, V_line _ _ _ _ (by omega : 13 ≤ 13+m.val) (by omega : 13+m.val < 26), absent_iff]
  exact rawHit_eq_meets pv lv w

def owned (c : Vertex) (s : Finset Vertex) (p l : Fin 13) : Prop :=
  (c = .inl p ∧ .inr l ∈ s) ∨ (c = .inr l ∧ .inl p ∈ s)

def colour : Bool → Finset Vertex
  | false => Finset.univ.image (Sum.inl : Fin 13 → Vertex)
  | true => Finset.univ.image (Sum.inr : Fin 13 → Vertex)

lemma leafLine {p : Fin 13} {s : Finset Vertex} (only : ∀ x : Fin 13, Sum.inl x ∉ s)
    (ok : ∀ y, Sum.inr y ∈ s → inc p y) : s ⊆ neighbours (.inl p) := by
  rintro (x | y) h
  · exact (only x h).elim
  · simpa [neighbours, inc, D] using ok y h

lemma leafPoint {l : Fin 13} {s : Finset Vertex} (only : ∀ y : Fin 13, Sum.inr y ∉ s)
    (ok : ∀ x, Sum.inl x ∈ s → inc x l) : s ⊆ neighbours (.inr l) := by
  rintro (x | y) h
  · simpa [neighbours, inc, D] using ok x h
  · exact (only y h).elim

lemma pureLeaf {c : Vertex} {s : Finset Vertex} (sub : s ⊆ neighbours c) (b : Bool) :
    Disjoint s (colour b) ∨ s ⊆ colour b := by
  cases c with
  | inl p =>
    have only (z) (hz : z ∈ s) : ∃ l : Fin 13, z = Sum.inr l := by
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp (sub hz)
      exact ⟨l, rfl⟩
    cases b
    · left
      apply Finset.disjoint_left.mpr
      intro z hz h
      obtain ⟨l, rfl⟩ := only z hz
      simpa [colour] using h
    · right
      intro z hz
      obtain ⟨l, rfl⟩ := only z hz
      simp [colour]
  | inr l =>
    have only (z) (hz : z ∈ s) : ∃ p : Fin 13, z = Sum.inl p := by
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp (sub hz)
      exact ⟨p, rfl⟩
    cases b
    · right
      intro z hz
      obtain ⟨p, rfl⟩ := only z hz
      simp [colour]
    · left
      apply Finset.disjoint_left.mpr
      intro z hz h
      obtain ⟨p, rfl⟩ := only z hz
      simpa [colour] using h

def uniquePath (C : Circuit) (h t : ℕ) : Prop :=
  ∀ x y, wireAnd C x → wireAnd C y → Relation.TransGen (readsWire C) x y → x = h ∧ y = t

noncomputable abbrev rawSet (C : Circuit) := baseSet (readsWire C) (wireOr C)

lemma ordinaryTerminal (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C) (good : Fits C)
    (two : ∀ g ∈ C.gates, g.inputs.length = 2) {h t z} (unique : uniquePath C h t)
    (ah : wireAnd C h) (hz : z ∈ terminalSet C) (diff : z ≠ t) :
    ∃ c s, s ⊆ neighbours c ∧ (∀ p l, pairVal C p l z → owned c s p l) ∧
      (s = ∅ ∨ ∃ u < 26+C.size, ¬ rr C h u ∧ s = rawSet C u) := by
  obtain ⟨size, az, _⟩ := (terminal_mem C z).mp hz
  obtain ⟨a, ha, b, hb, ins, edges⟩ := realOperands C rb two az.1 size
  let f := fun i : Fin 2 => if i = 0 then a else b
  have ef (i) : readsWire C (f i) z := (edges _).mpr (by by_cases e : i = 0 <;> simp [f,e])
  have no (i) : ¬ rr C h (f i) :=
    betweenOrCannotFeedOther unique ah az diff (.refl : rr C h h) (ef i)
  have bin (L) (hl : L.length = 26) (i) :
      V C.gates L (f i) = true ↔ rawHit (readsWire C) (wireOr C) (fun w => V C.gates L w = true) (f i) := by
    simpa [diff] using onePairOperand (fun _ _ => readBackWire C rb) (wireOrValue C rb L hl)
      (fun _ no high => (gateTags C mono high).resolve_left no) unique az (ef i)
  let P := fun i => pointsAt C (f i)
  let B := fun i => linesAt C (f i)
  have peq (p l) : pairVal C p l z ↔ ordinaryFlags P B p l := by
    change V C.gates (inp {p} {l}) z = true ↔ _
    rw [wireAndValue C rb _ (inp_len _ _) az ins]
    have tmp (i) := (bin (inp {p} {l}) (inp_len _ _) i).trans (raw_pair C p l (f i))
    exact and_congr (tmp 0) (tmp 1)
  have clean (Q) (hq : quad Q) : ¬ (meets (P 0) (B 0) (· ∈ Q) (miss Q) ∧
      meets (P 1) (B 1) (· ∈ Q) (miss Q)) := by
    intro hit
    apply terminalReject C rb good hz hq
    apply (wireAndValue C rb _ (inp_len _ _) az ins).mpr
    have tmp (i) := (bin (inp Q (absent Q)) (inp_len _ _) i).trans (raw_quad C Q (f i))
    exact ⟨(tmp 0).mpr hit.1, (tmp 1).mpr hit.2⟩
  have bounds (i) : f i < 26+C.size := (readBackWire C rb (ef i)).trans size
  rcases ordinaryStar P B clean with dead | ⟨p, i, pure, safe, cover⟩ | ⟨l, i, pure, safe, cover⟩
  · exact ⟨.inl 0, ∅, Finset.empty_subset _, fun p l v => (dead _ _ ((peq p l).mp v)).elim, Or.inl rfl⟩
  · refine ⟨.inl p, rawSet C (f i), leafLine (fun x h => pure x ((mem_base ..).mp h))
        (fun y h => safe y ((mem_base ..).mp h)), ?_, Or.inr ⟨_, bounds i, no i, rfl⟩⟩
    intro x y v
    obtain ⟨rfl, hl⟩ := cover x y ((peq x y).mp v)
    exact Or.inl ⟨rfl, (mem_base ..).mpr hl⟩
  · refine ⟨.inr l, rawSet C (f i), leafPoint (fun y h => pure y ((mem_base ..).mp h))
        (fun x h => safe x ((mem_base ..).mp h)), ?_, Or.inr ⟨_, bounds i, no i, rfl⟩⟩
    intro x y v
    obtain ⟨hp, rfl⟩ := cover x y ((peq x y).mp v)
    exact Or.inr ⟨rfl, (mem_base ..).mpr hp⟩

abbrev Star := Vertex × Finset Vertex

def usable (bank : List (Finset Vertex)) (s : Star) : Prop :=
  available bank s.2 ∧ s.2 ⊆ neighbours s.1

lemma collectTerms (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C) (good : Fits C)
    (bank : List (Finset Vertex)) (built : orBank bank) (t : ℕ) (extra : Finset Star)
    (extraValid : ∀ s ∈ extra, usable bank s)
    (normal : ∀ w ∈ (terminalSet C).erase t, ∃ s, usable bank s ∧
      ∀ p l, pairVal C p l w → owned s.1 s.2 p l)
    (special : t ∈ terminalSet C → ∀ p l, pairVal C p l t → ∃ s ∈ extra, owned s.1 s.2 p l)
    (budget : let k := ((terminalSet C).erase t).card + extra.card
      bank.length + 2*k ≤ C.size+1 ∨ (∃ s ∈ extra, ∃ p, s.1 = .inl p) ∧
      (∃ s ∈ extra, ∃ l, s.1 = .inr l) ∧ bank.length + 2*k ≤ C.size+2) : 64 ≤ C.size := by
  classical
  let G := (terminalSet C).erase t
  let chosen := fun w => if h : w ∈ G then (normal w h).choose else ((.inl 0, ∅) : Star)
  have spec (w) (hw : w ∈ G) : usable bank (chosen w) ∧
      ∀ p l, pairVal C p l w → owned (chosen w).1 (chosen w).2 p l := by
    simpa [chosen, hw] using (normal w hw).choose_spec
  let family := G.image chosen ∪ extra
  have count : family.card ≤ G.card + extra.card :=
    (Finset.card_union_le ..).trans (Nat.add_le_add_right Finset.card_image_le _)
  have inside (s) (h : s ∈ extra) : s ∈ family := Finset.mem_union_right _ h
  apply namedStars family Prod.fst Prod.snd bank built C.size
  · intro s hs
    rcases Finset.mem_union.mp hs with h | h
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
      exact (spec w hw).1
    · exact extraValid s h
  · intro p l edge
    obtain ⟨w, hw, v⟩ := terminalCover C mono rb good p l edge
    by_cases eq : w = t
    · subst w
      obtain ⟨s, hs, hit⟩ := special hw p l v
      exact ⟨s, inside s hs, hit⟩
    · have mem : w ∈ G := Finset.mem_erase.mpr ⟨eq, hw⟩
      exact ⟨chosen w, Finset.mem_union_left _ (Finset.mem_image_of_mem _ mem), (spec w mem).2 p l v⟩
  · change bank.length + 2*(G.card + extra.card) ≤ C.size+1 ∨ _ at budget
    rcases budget with h | ⟨⟨s, hs, p, hp⟩, ⟨z, hz, l, hl⟩, bound⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨⟨s, inside s hs, p, hp⟩, ⟨z, inside z hz, l, hl⟩, by
        change bank.length + 2*(G.card + extra.card) ≤ C.size+2 at bound
        omega⟩

noncomputable abbrev effectiveSet (C : Circuit) (on : Prop) (h a) :=
  sourceSet (selectedSources (readsWire C) (wireOr C) on h a) (rr C)

lemma effective_free (C : Circuit) {on : Prop} {h a w} (free : ¬ rr C h w) :
    effectiveSet C on h a w = rawSet C w := by
  ext x
  simp only [effectiveSet, rawSet, selected_mem, mem_base, show ¬ pass (readsWire C) (wireOr C) h w from free,
    false_and, and_false, or_false, rr]

lemma ordinaryUsable (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C) (good : Fits C)
    (two : ∀ g ∈ C.gates, g.inputs.length = 2) {h t a} (unique : uniquePath C h t)
    (ah : wireAnd C h) (on : Prop) (b : Bool) (bank : List (Finset Vertex))
    (pure : ∀ w < 26+C.size, (Disjoint (effectiveSet C on h a w) (colour b) ∨
      effectiveSet C on h a w ⊆ colour b) → available bank (effectiveSet C on h a w))
    (z) (hz : z ∈ (terminalSet C).erase t) : ∃ s, usable bank s ∧
      ∀ p l, pairVal C p l z → owned s.1 s.2 p l := by
  obtain ⟨diff, hz⟩ := Finset.mem_erase.mp hz
  obtain ⟨c, s, sub, cover, repr⟩ := ordinaryTerminal C mono rb good two unique ah hz diff
  refine ⟨⟨c,s⟩, ⟨?_, sub⟩, cover⟩
  rcases repr with rfl | ⟨u, hu, free, rfl⟩
  · exact Or.inl (by simp)
  · have e := effective_free C (on := on) (a := a) free
    rw [← e] at sub ⊢
    exact pure _ hu (pureLeaf sub b)

lemma outsideTerminal (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C) (good : Fits C)
    (two : ∀ g ∈ C.gates, g.inputs.length = 2) {h t} (unique : uniquePath C h t)
    (ah : wireAnd C h) (missing : t ∉ terminalSet C) : 64 ≤ C.size := by
  have early : 0 < h := by have := ah.1; omega
  obtain ⟨bank, built, pure, _, budget, _⟩ := physicalBank C rb good two ah early False (colour false)
    (fun bad => bad.elim)
  apply collectTerms C mono rb good bank built t ∅ (by simp)
    (ordinaryUsable C mono rb good two unique ah False false bank pure) (fun ht => (missing ht).elim)
  left
  simpa [Finset.erase_eq_of_notMem missing] using budget

lemma oneSpecial (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C) (good : Fits C)
    (two : ∀ g ∈ C.gates, g.inputs.length = 2) {h t a} (unique : uniquePath C h t)
    (ah : wireAnd C h) (ht : t ∈ terminalSet C) (early : a < h)
    (on : Prop) (b : Bool) (noBypass : on → ¬ rr C h C.output) (s : Star)
    (sub : s.2 ⊆ neighbours s.1) (cover : ∀ p l, pairVal C p l t → owned s.1 s.2 p l)
    (leaf : s.2 = ∅ ∨ ∃ u < 26+C.size, s.2 = effectiveSet C on h a u ∩ colour b) : 64 ≤ C.size := by
  obtain ⟨bank, built, pure, proj, budget, _⟩ := physicalBank C rb good two ah early on (colour b) noBypass
  have usable' : usable bank s := by
    refine ⟨?_, sub⟩
    rcases leaf with e | ⟨u, hu, e⟩
    · exact Or.inl (by simp [e])
    · rw [e]
      exact proj _ hu
  apply collectTerms C mono rb good bank built t {s}
    (fun z hz => (Finset.mem_singleton.mp hz) ▸ usable')
    (ordinaryUsable C mono rb good two unique ah on b bank pure)
    (fun _ p l hit => ⟨s, Finset.mem_singleton_self _, cover p l hit⟩)
  left
  simpa only [Finset.card_singleton, Finset.card_erase_add_one ht] using budget

lemma twoSpecial (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C) (good : Fits C)
    (two : ∀ g ∈ C.gates, g.inputs.length = 2) {h t} (unique : uniquePath C h t)
    (ah : wireAnd C h) (ht : t ∈ terminalSet C) (hn : h ∉ terminalSet C)
    (p l : Fin 13) {w v} (hw : w < 26+C.size) (hv : v < 26+C.size)
    (sub₁ : rawSet C w ⊆ neighbours (.inl p)) (sub₂ : rawSet C v ⊆ neighbours (.inr l))
    (cover : ∀ x y, pairVal C x y t → owned (.inl p) (rawSet C w) x y ∨
      owned (.inr l) (rawSet C v) x y) : 64 ≤ C.size := by
  classical
  have early : 0 < h := by have := ah.1; omega
  obtain ⟨bank, built, pure, _, _, budget⟩ := physicalBank C rb good two ah early False
    (colour false) (fun bad => bad.elim)
  have eff (u) : effectiveSet C False h 0 u = rawSet C u := by
    ext x
    simp [effectiveSet, rawSet, rr, selected_mem, mem_base]
  have seen {u} (hu : u < 26+C.size) {c} (sub : rawSet C u ⊆ neighbours c) : available bank (rawSet C u) := by
    have e := eff u
    rw [← e] at sub ⊢
    exact pure _ hu (pureLeaf sub false)
  let s : Star := (.inl p, rawSet C w)
  let r : Star := (.inr l, rawSet C v)
  have diff : s ≠ r := by simp [s,r]
  have u₁ : usable bank s := ⟨seen hw sub₁, sub₁⟩
  have u₂ : usable bank r := ⟨seen hv sub₂, sub₂⟩
  apply collectTerms C mono rb good bank built t {s,r}
    (fun z hz => by simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                    rcases hz with rfl | rfl
                    · exact u₁
                    · exact u₂)
    (ordinaryUsable C mono rb good two unique ah False false bank pure)
    (fun _ x y v => (cover x y v).elim (fun H => ⟨s, by simp, H⟩) (fun H => ⟨r, by simp, H⟩))
  right
  refine ⟨⟨s, by simp, p, rfl⟩, ⟨r, by simp, l, rfl⟩, ?_⟩
  have H := budget hn
  have H' := Finset.card_erase_add_one ht
  simp [diff]
  omega

lemma firstInnerRead (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C)
    {h t} (ah : wireAnd C h) (unique : uniquePath C h t)
    (path : Relation.TransGen (readsWire C) h t) : ∃ w, readsWire C w t ∧ rr C h w := by
  cases path with
  | single e => exact ⟨h, e, .refl⟩
  | tail prior e => exact ⟨_, e, innerPathToOperand (fun _ _ => readBackWire C rb)
        (fun _ _ e => gateTags C mono e.1) unique ah prior (readBackWire C rb e)⟩

lemma nestedSafe {P L : Fin 3 → Fin 13 → Prop} {U V : Fin 13 → Prop}
    (negative : ∀ Q, quad Q → ¬ nested (fun i => meets (P i) (L i) (· ∈ Q) (miss Q))
      (meets U V (· ∈ Q) (miss Q))) {p l}
    (hit : nested (fun i => P i p ∨ L i l) (U p ∨ V l)) : inc p l := by
  by_contra n
  obtain ⟨Q,hq,hp,hl,_⟩ := mixedPLLines p l l n n
  have lift {X Y : Fin 13 → Prop} (v : X p ∨ Y l) : meets X Y (· ∈ Q) (miss Q) :=
    v.elim (fun e => Or.inl ⟨p, hp, e⟩) (fun e => Or.inr ⟨l, hl, e⟩)
  exact negative Q hq ⟨hit.1.elim (fun a => Or.inl ⟨lift a.1, lift a.2⟩) (fun u => Or.inr (lift u)),
    lift hit.2⟩

lemma orientedNested (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C) (good : Fits C)
    (two : ∀ g ∈ C.gates, g.inputs.length = 2) {h t a b w v} (unique : uniquePath C h t)
    (ah : wireAnd C h) (atop : wireAnd C t) (diff : h ≠ t) (ht : t ∈ terminalSet C)
    (ea : readsWire C a h) (eb : readsWire C b h) (ew : readsWire C w t) (ev : readsWire C v t)
    (hand : ∀ L, L.length = 26 → (V C.gates L h = true ↔ V C.gates L a = true ∧ V C.gates L b = true))
    (tand : ∀ L, L.length = 26 → (V C.gates L t = true ↔ V C.gates L w = true ∧ V C.gates L v = true))
    (leftPath : rr C h w) (rightFree : ¬ rr C h v) (noOut : ¬ rr C h C.output) : 64 ≤ C.size := by
  classical
  let f := fun i : Fin 3 => if i = 0 then a else if i = 1 then b else v
  let P := fun i => pointsAt C (f i)
  let B := fun i => linesAt C (f i)
  let U := pointsAt C w
  let W := linesAt C w
  let F := fun p l => nested (fun i => P i p ∨ B i l) (U p ∨ W l)
  have sem (L) (len : L.length = 26) : V C.gates L t = true ↔
      nested (fun i => rawHit (readsWire C) (wireOr C) (fun z => V C.gates L z = true) (f i))
        (rawHit (readsWire C) (wireOr C) (fun z => V C.gates L z = true) w) :=
    onePairNested (fun _ _ => readBackWire C rb) (wireOrValue C rb L len)
      (fun _ no high => (gateTags C mono high).resolve_left no) unique diff ah atop ea eb ew ev
      (hand L len) (tand L len) leftPath rightFree
  have peq (p l) : pairVal C p l t ↔ F p l := by
    have H := sem (inp {p} {l}) (inp_len _ _)
    change pairVal C p l t ↔ nested (fun i => rawHit _ _ (pairVal C p l) (f i))
      (rawHit _ _ (pairVal C p l) w) at H
    simpa only [F, P, B, U, W, raw_pair] using H
  have negative (Q) (hq : quad Q) :
      ¬ nested (fun i => meets (P i) (B i) (· ∈ Q) (miss Q)) (meets U W (· ∈ Q) (miss Q)) := by
    intro hit
    apply terminalReject C rb good ht hq
    apply (sem _ (inp_len Q (absent Q))).mpr
    change nested (fun i => rawHit _ _ (quadVal C Q) (f i)) (rawHit _ _ (quadVal C Q) w)
    simpa only [P, B, U, W, raw_quad] using hit
  have bound := ((terminal_mem C t).mp ht).1
  have ht' : h < t := (pass_le (fun _ _ => readBackWire C rb) leftPath).trans_lt (readBackWire C rb ew)
  have ab := readBackWire C rb ea
  have bb := readBackWire C rb eb
  have wb := readBackWire C rb ew
  have vb := readBackWire C rb ev
  let child := fun i : Fin 3 => if i = 1 then b else a
  let root := fun i : Fin 3 => if i = 2 then v else w
  have early (i) : child i < h := by dsimp [child]; split <;> assumption
  have rootBound (i) : root i < 26+C.size := by dsimp [root]; split <;> omega
  have fb (i) : f i < 26+C.size := by dsimp [f]; split <;> first | omega | split <;> omega
  have support (i) (z : Vertex) : z ∈ effectiveSet C True h (child i) (root i) ↔
      rr C (vertexWire z) (f i) ∨ (i ≠ 2 ∧ rr C (vertexWire z) w) := by
    change z ∈ sourceSet _ (pass (readsWire C) (wireOr C)) _ ↔ _
    rw [selected_mem]
    fin_cases i <;> simp [root, child, f, show pass _ _ h w from leftPath,
      show ¬ pass _ _ h v from rightFree, rr, or_comm]
  have hn : h ∉ terminalSet C := fun hh => noOut ((terminal_mem C h).mp hh).2.2
  rcases classifyNested P B U W negative with dead | ⟨p,i,cover,safe⟩ | ⟨l,i,cover,safe⟩ |
    ⟨p,l,i,j,_,_,_,_,pi,pj,_,cover⟩
  · exact oneSpecial C mono rb good two unique ah ht ab False false (fun h => h.elim)
      (.inl 0, ∅) (Finset.empty_subset _) (fun x y hit => (dead _ _ ((peq x y).mp hit)).elim) (Or.inl rfl)
  · let leaf := effectiveSet C True h (child i) (root i) ∩ colour true
    have eq (y : Fin 13) : Sum.inr y ∈ leaf ↔ addCommon B W i y := by
      simp [leaf, support, colour, B, W, linesAt, addCommon, vertexWire]
    refine oneSpecial C mono rb good two unique ah ht (early i) True true (fun _ => noOut)
      (.inl p, leaf) (leafLine (by simp [leaf, colour]) (fun y h => safe y ((eq y).mp h))) ?_
      (Or.inr ⟨root i, rootBound i, rfl⟩)
    intro x y hit
    obtain ⟨rfl, h⟩ := cover x y ((peq x y).mp hit)
    exact Or.inl ⟨rfl, (eq y).mpr h⟩
  · let leaf := effectiveSet C True h (child i) (root i) ∩ colour false
    have eq (x : Fin 13) : Sum.inl x ∈ leaf ↔ addCommon P U i x := by
      simp [leaf, support, colour, P, U, pointsAt, addCommon, vertexWire]
    refine oneSpecial C mono rb good two unique ah ht (early i) True false (fun _ => noOut)
      (.inr l, leaf) (leafPoint (by simp [leaf, colour]) (fun x h => safe x ((eq x).mp h))) ?_
      (Or.inr ⟨root i, rootBound i, rfl⟩)
    intro x y hit
    obtain ⟨h, rfl⟩ := cover x y ((peq x y).mp hit)
    exact Or.inr ⟨rfl, (eq x).mpr h⟩
  · have safe (x y) (hit : F x y) := nestedSafe negative hit
    apply twoSpecial C mono rb good two unique ah ht hn p l (fb j) (fb i)
    · exact leafLine (fun x h => pj x ((mem_base ..).mp h))
        (fun y h => safe p y ((cover p y).mpr (Or.inl ⟨rfl, (mem_base ..).mp h⟩)))
    · exact leafPoint (fun y h => pi y ((mem_base ..).mp h))
        (fun x h => safe x l ((cover x l).mpr (Or.inr ⟨(mem_base ..).mp h, rfl⟩)))
    · intro x y hit
      rcases (cover x y).mp ((peq x y).mp hit) with ⟨rfl, hy⟩ | ⟨hx, rfl⟩
      · exact Or.inl (Or.inl ⟨rfl, (mem_base ..).mpr hy⟩)
      · exact Or.inr (Or.inr ⟨rfl, (mem_base ..).mpr hx⟩)

lemma dirtyLower (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C) (good : Fits C)
    (two : ∀ g ∈ C.gates, g.inputs.length = 2) {h t} (unique : uniquePath C h t)
    (ah : wireAnd C h) (atop : wireAnd C t) (path : Relation.TransGen (readsWire C) h t)
    {Q} (hq : quad Q) (vQ : quadVal C Q h) : 64 ≤ C.size := by
  by_cases ht : t ∈ terminalSet C
  · have noOut : ¬ rr C h C.output :=
      dirtyNoBypass (wireOrValue C rb _ (inp_len _ _)) (good.2 Q hq) vQ
    have hb : h < 26+C.size := by
      change h < 26+C.gates.length
      have := actualAnd C ah.2
      have := ah.1
      omega
    obtain ⟨a, _, b, _, insH, hread⟩ := realOperands C rb two ah.1 hb
    obtain ⟨w, _, v, _, insT, tread⟩ := realOperands C rb two atop.1 ((terminal_mem C t).mp ht).1
    have ea := (hread a).mpr (Or.inl rfl)
    have eb := (hread b).mpr (Or.inr rfl)
    have ew := (tread w).mpr (Or.inl rfl)
    have ev := (tread v).mpr (Or.inr rfl)
    have andH L len := wireAndValue C rb L len ah insH
    have andT L len := wireAndValue C rb L len atop insT
    have rej := terminalReject C rb good ht hq
    have only := falseOnSide (wireOrValue C rb _ (inp_len _ _)) rej vQ (andT _ (inp_len _ _))
    have diff : h ≠ t := by
      intro eq
      exact noOut (eq ▸ ((terminal_mem C t).mp ht).2.2)
    obtain ⟨u, eu, hu⟩ := firstInnerRead C mono rb ah unique path
    rcases (tread u).mp eu with rfl | rfl
    · exact orientedNested C mono rb good two unique ah atop diff ht ea eb ew ev andH andT
        hu (fun hv => only ⟨hu, hv⟩) noOut
    · exact orientedNested C mono rb good two unique ah atop diff ht ea eb ev ew andH
        (fun L len => (andT L len).trans and_comm) hu (fun hw => only ⟨hw, hu⟩) noOut
  · exact outsideTerminal C mono rb good two unique ah ht

def acceptedTest (L : List Bool) : Prop :=
  ∃ p l, inc p l ∧ L = inp {p} {l}

def rejectedTest (L : List Bool) : Prop :=
  ∃ Q, quad Q ∧ L = inp Q (absent Q)

lemma zeroPairs (C : Circuit) (zero : PEqualNP.TopForm.andPairs 26 C = 0) :
    ¬ ∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j := by
  rintro ⟨i,j,hi,hj,path⟩
  let _ := gateOpDecEq
  let pairs := (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
    fun p => (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 26 C p.1 p.2
  change pairs.card = 0 at zero
  have mem : (i,j) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (actualAnd C hi), Finset.mem_range.mpr (actualAnd C hj)⟩, hi,hj,path⟩
  have pos := Finset.card_pos.mpr ⟨_,mem⟩
  omega

lemma cleanFinish (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C) (good : Fits C)
    (small : C.size < 64) (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    {i j} (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (ij : InCone 26 C i j) (clean : ∀ Q, quad Q → ¬ quadVal C Q (26+i)) :
    ∃ D, Monotone2 D ∧ ReadsBack 26 D ∧ Fits D ∧ D.size < C.size := by
  have lenA : ∀ L, acceptedTest L → L.length = 26 := by
    rintro _ ⟨_,_,_,rfl⟩
    exact inp_len _ _
  have lenR : ∀ L, rejectedTest L → L.length = 26 := by
    rintro _ ⟨_,_,rfl⟩
    exact inp_len _ _
  have someA : ∃ L, acceptedTest L := ⟨_, 0, 0, by decide, rfl⟩
  have witness : quad ({0,1,2,5} : Finset (Fin 13)) := by decide +kernel
  have someR : ∃ L, rejectedTest L := ⟨_, _, witness, rfl⟩
  have acc : ∀ L, acceptedTest L → C.eval L = true := by
    rintro _ ⟨p,l,hl,rfl⟩
    exact good.1 p l hl
  have rej : ∀ L, rejectedTest L → C.eval L = false := by
    rintro _ ⟨Q,hq,rfl⟩
    exact Bool.eq_false_iff.mpr (good.2 Q hq)
  have hB : ∀ L, rejectedTest L → (C.wires L).getD (26+i) false = false := by
    rintro _ ⟨Q,hq,rfl⟩
    exact Bool.eq_false_iff.mpr (clean Q hq)
  obtain ⟨D, md, rd, ⟨ad, nd⟩, smaller | ⟨eq, pairs⟩⟩ :=
    main26 acceptedTest rejectedTest lenA lenR someA someR C mono rb acc rej i j hi hj ij hB
  · exact ⟨D,md,rd,⟨fun p l h => ad _ ⟨p,l,h,rfl⟩, fun Q h =>
      Bool.eq_false_iff.mp (nd _ ⟨Q,h,rfl⟩)⟩,smaller⟩
  · have no := zeroPairs D (by omega)
    have lower := core D.gates D.output md rd no
      (fun p l h => ad _ ⟨p,l,h,rfl⟩) (fun Q h₁ h₂ => nd _ ⟨Q,⟨h₁,h₂⟩,rfl⟩)
    change 64 ≤ D.size at lower
    omega

lemma finish (C : Circuit) (mono : Monotone2 C) (rb : ReadsBack 26 C) (good : Fits C)
    (small : C.size < 64) (two : ∀ g ∈ C.gates, g.inputs.length = 2)
    (one : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    {i j} (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (ij : InCone 26 C i j) :
    ∃ D, Monotone2 D ∧ ReadsBack 26 D ∧ Fits D ∧ D.size < C.size := by
  classical
  by_cases dirty : ∃ Q, quad Q ∧ quadVal C Q (26+i)
  · obtain ⟨Q,hq,hv⟩ := dirty
    have unique : uniquePath C (26+i) (26+j) :=
      fun _ _ aa ab path => uniqueAndPath C rb one hi hj ij aa ab path
    have a : wireAnd C (26+i) := ⟨by omega, by simpa using hi⟩
    have b : wireAnd C (26+j) := ⟨by omega, by simpa using hj⟩
    have lower := dirtyLower C mono rb good two unique a b ((circuitCone C rb i j).mp ij) hq hv
    omega
  · exact cleanFinish C mono rb good small one hi hj ij (fun Q hq hv => dirty ⟨Q,hq,hv⟩)

lemma fitsTests (C : Circuit) : Fits C ↔
    (∀ p l : Fin 13, p-l ∈ D → C.eval ((List.ofFn fun u : Fin 13 => decide (u=p)) ++
      List.ofFn fun u : Fin 13 => decide (u=l)) = true) ∧
    ∀ Q : Finset (Fin 13), Q.card = 4 → (∀ l : Fin 13, (Q.filter (fun p => p-l ∈ D)).card ≤ 2) →
      C.eval ((List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ D)) = false := by
  have pos (p l) : pairVal C p l C.output ↔
      C.eval ((List.ofFn fun u : Fin 13 => decide (u=p)) ++ List.ofFn fun u : Fin 13 => decide (u=l)) = true := by
    simp [pairVal, V, inp, wiresFrom, Circuit.eval, Circuit.wires]
  have neg (Q) : ¬ quadVal C Q C.output ↔
      C.eval ((List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p-l ∉ D)) = false := by
    simp [quadVal,V,inp,wiresFrom,Circuit.eval,Circuit.wires,absent]
  constructor
  · intro h
    exact ⟨fun p l hp => (pos p l).mp (h.1 p l hp), fun Q hc hk => (neg Q).mp (h.2 Q ⟨hc,hk⟩)⟩
  · intro h
    exact ⟨fun p l hp => (pos p l).mpr (h.1 p l hp), fun Q hq => (neg Q).mpr (h.2 Q hq.1 hq.2)⟩

end PEqualNP.Outside.L_meta_1961_aux

theorem PEqualNP.Outside.L_meta_1961 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → PEqualNP.TopForm.andPairs (26 : ℕ) x4 ≤ (1 : ℕ) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size := by
  intro diff tests nested C mono rb good small inside operands pairs
  obtain ⟨i,j,hi,hj,ij⟩ := inside
  obtain ⟨D,md,rd,gd,sd⟩ := PEqualNP.Outside.L_meta_1961_aux.finish C mono rb
    ((PEqualNP.Outside.L_meta_1961_aux.fitsTests C).mpr good) small (fun g hg => (operands g hg).1)
    pairs hi hj ij
  exact ⟨D, md, rd, (PEqualNP.Outside.L_meta_1961_aux.fitsTests D).mp gd, sd⟩
