import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_282_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (h : i < m) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_app (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false
      = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp [List.getD_eq_getElem?_getD]
  · exact getD_ge _ _ (by simp; omega)


def jn {n : ℕ} (z z' : Fin n → Bool) : Fin n → Bool := fun i => z i || z' i


def realAnd (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => decide (g.inputs.length = 2)
  | _ => false

theorem realAnd_spec (g : Gate) (h : realAnd g = true) : ∃ a b, g = ⟨GateOp.and, [a, b]⟩ := by
  obtain ⟨op, l⟩ := g
  cases op <;> simp [realAnd] at h
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp h
  exact ⟨a, b, rfl⟩

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hg with e | e
  · rw [e]
    simp only [GateOp.eval]
    intro H
    rw [List.all_eq_true] at H ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h i (H _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [e]
    simp only [GateOp.eval]
    intro H
    rw [List.any_eq_true] at H ⊢
    obtain ⟨b, hb, hbt⟩ := H
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f' i, List.mem_map.mpr ⟨i, hi, rfl⟩, h i hbt⟩


theorem mono_fold : ∀ (gs : List Gate) (W W' : List Bool), W.length = W'.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W.getD i false = true → W'.getD i false = true) →
    ∀ i, (gs.foldl stp W).getD i false = true → (gs.foldl stp W').getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W W' _ _ h i; exact h i
  | cons g gs ih =>
    intro W W' hl hops h
    simp only [List.foldl_cons]
    apply ih (stp W g) (stp W' g) (by simp [stp, hl]) (fun g' hg' => hops g' (by simp [hg']))
    intro i
    simp only [stp]
    rw [getD_app, getD_app, ← hl]
    split_ifs
    · exact h i
    · exact eval_mono g (hops g (by simp)) _ _ h
    · exact id

theorem any_or (l : List ℕ) (f1 f2 : ℕ → Bool) :
    (l.map (fun i => f1 i || f2 i)).any id = ((l.map f1).any id || (l.map f2).any id) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, ih, id]
    generalize (l.map f1).any id = X
    generalize (l.map f2).any id = Y
    cases f1 a <;> cases f2 a <;> cases X <;> cases Y <;> rfl


theorem eval_join (g : Gate) (hm : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hr : realAnd g = false) (f f1 f2 : ℕ → Bool) (h : ∀ i, f i = (f1 i || f2 i)) :
    g.op.eval (g.inputs.map f)
      = (g.op.eval (g.inputs.map f1) || g.op.eval (g.inputs.map f2)) := by
  have e : g.inputs.map f = g.inputs.map (fun i => f1 i || f2 i) :=
    List.map_congr_left (fun i _ => h i)
  rw [e]
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hlen⟩ := hm
  simp only at hop hlen
  rcases hop with rfl | rfl
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · simp [GateOp.eval]
    · simp [GateOp.eval]
    · simp [realAnd] at hr
    · simp at hlen
  · simp only [GateOp.eval]
    exact any_or l f1 f2

theorem join_fold : ∀ (gs : List Gate) (W W1 W2 : List Bool), W.length = W1.length →
    W.length = W2.length →
    (∀ g ∈ gs, ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      realAnd g = false) →
    (∀ i, W.getD i false = (W1.getD i false || W2.getD i false)) →
    ∀ i, (gs.foldl stp W).getD i false
      = ((gs.foldl stp W1).getD i false || (gs.foldl stp W2).getD i false) := by
  intro gs
  induction gs with
  | nil => intro W W1 W2 _ _ _ h i; exact h i
  | cons g gs ih =>
    intro W W1 W2 hl1 hl2 hg h
    simp only [List.foldl_cons]
    apply ih (stp W g) (stp W1 g) (stp W2 g) (by simp [stp, hl1]) (by simp [stp, hl2])
      (fun g' hg' => hg g' (by simp [hg']))
    intro i
    simp only [stp]
    rw [getD_app, getD_app, getD_app, ← hl1, ← hl2]
    split_ifs
    · exact h i
    · exact eval_join g (hg g (by simp)).1 (hg g (by simp)).2 _ _ _ h
    · rfl

theorem ofFn_jn {n : ℕ} (z z' : Fin n → Bool) (i : ℕ) :
    (List.ofFn (jn z z')).getD i false
      = ((List.ofFn z).getD i false || (List.ofFn z').getD i false) := by
  by_cases h : i < n
  · rw [getD_ofFn _ i h, getD_ofFn _ i h, getD_ofFn _ i h]
    rfl
  · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; omega),
      getD_ge _ _ (by simp; omega)]
    rfl



theorem bound0 {n : ℕ} {ι : Type} [DecidableEq ι] (Z : ι → Fin n → Bool) (o : ℕ)
    (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (h0 : gs.countP realAnd = 0) (S : Finset ι)
    (hz : ∀ s ∈ S, (gs.foldl stp (List.ofFn (Z s))).getD o false = false)
    (hj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      (gs.foldl stp (List.ofFn (jn (Z s) (Z t)))).getD o false = true) :
    S.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s hs t ht
  by_contra hne
  have h1 := hj s hs t ht hne
  have hreal : ∀ g ∈ gs, realAnd g = false := by
    intro g hg
    have := List.countP_eq_zero.mp h0 g hg
    simpa using this
  rw [join_fold gs _ (List.ofFn (Z s)) (List.ofFn (Z t)) (by simp) (by simp)
    (fun g hg => ⟨hm g hg, hreal g hg⟩) (ofFn_jn (Z s) (Z t)) o, hz s hs, hz t ht] at h1
  simp at h1


theorem and_zero (W : List Bool) (a b o : ℕ) (post : List Gate)
    (h : (post.foldl stp (stp W ⟨GateOp.and, [a, b]⟩)).getD o false = false) :
    (post.foldl stp (stp W ⟨GateOp.and, [a]⟩)).getD o false = false ∨
      (post.foldl stp (stp W ⟨GateOp.and, [b]⟩)).getD o false = false := by
  have e1 : stp W ⟨GateOp.and, [a, b]⟩ = W ++ [W.getD a false && W.getD b false] := by
    simp [stp, GateOp.eval]
  have e2 : stp W ⟨GateOp.and, [a]⟩ = W ++ [W.getD a false] := by simp [stp, GateOp.eval]
  have e3 : stp W ⟨GateOp.and, [b]⟩ = W ++ [W.getD b false] := by simp [stp, GateOp.eval]
  rw [e1] at h
  rw [e2, e3]
  cases ha : W.getD a false
  · rw [ha] at h
    exact Or.inl h
  · rw [ha] at h
    exact Or.inr h

theorem and_up (W : List Bool) (a b o : ℕ) (post : List Gate)
    (hops : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : (post.foldl stp (stp W ⟨GateOp.and, [a, b]⟩)).getD o false = true) :
    (post.foldl stp (stp W ⟨GateOp.and, [a]⟩)).getD o false = true ∧
      (post.foldl stp (stp W ⟨GateOp.and, [b]⟩)).getD o false = true := by
  have e1 : stp W ⟨GateOp.and, [a, b]⟩ = W ++ [W.getD a false && W.getD b false] := by
    simp [stp, GateOp.eval]
  have e2 : stp W ⟨GateOp.and, [a]⟩ = W ++ [W.getD a false] := by simp [stp, GateOp.eval]
  have e3 : stp W ⟨GateOp.and, [b]⟩ = W ++ [W.getD b false] := by simp [stp, GateOp.eval]
  rw [e1] at h
  rw [e2, e3]
  constructor
  · apply mono_fold post _ _ (by simp) hops _ o h
    intro i
    rw [getD_app, getD_app]
    split_ifs
    · exact id
    · intro hv
      rw [Bool.and_eq_true] at hv
      exact hv.1
    · exact id
  · apply mono_fold post _ _ (by simp) hops _ o h
    intro i
    rw [getD_app, getD_app]
    split_ifs
    · exact id
    · intro hv
      rw [Bool.and_eq_true] at hv
      exact hv.2
    · exact id



theorem bound {n : ℕ} {ι : Type} [DecidableEq ι] (Z : ι → Fin n → Bool) (o : ℕ) :
    ∀ (r : ℕ) (gs : List Gate),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      gs.countP realAnd ≤ r → ∀ S : Finset ι,
      (∀ s ∈ S, (gs.foldl stp (List.ofFn (Z s))).getD o false = false) →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t →
        (gs.foldl stp (List.ofFn (jn (Z s) (Z t)))).getD o false = true) →
      S.card ≤ 2 ^ r := by
  intro r
  induction r with
  | zero =>
    intro gs hm hc S hz hj
    have := bound0 Z o gs hm (by omega) S hz hj
    simpa using this
  | succ r ih =>
    intro gs hm hc S hz hj
    by_cases h0 : gs.countP realAnd = 0
    · have h1 := bound0 Z o gs hm h0 S hz hj
      have h2 : 1 ≤ 2 ^ (r + 1) := Nat.one_le_two_pow
      omega
    · have hex : ∃ g ∈ gs, realAnd g = true := by
        by_contra hno
        apply h0
        apply List.countP_eq_zero.mpr
        intro g hg hp
        exact hno ⟨g, hg, hp⟩
      obtain ⟨g, hg, hreal⟩ := hex
      obtain ⟨a, b, rfl⟩ := realAnd_spec g hreal
      obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
      have hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
        fun g hg' => (hm g (by simp [hg'])).1
      have hcount : ∀ c : ℕ, (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).countP realAnd ≤ r := by
        intro c
        have e1 : (pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post).countP realAnd
            = pre.countP realAnd + (post.countP realAnd + 1) := by
          rw [List.countP_append, List.countP_cons_of_pos (by simp [realAnd])]
        have e2 : (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).countP realAnd
            = pre.countP realAnd + post.countP realAnd := by
          rw [List.countP_append, List.countP_cons_of_neg (by simp [realAnd])]
        omega
      have hmono : ∀ c : ℕ, ∀ g ∈ pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post,
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
        intro c g hg'
        rcases List.mem_append.mp hg' with h | h
        · exact hm g (by simp [h])
        · rcases List.mem_cons.mp h with rfl | h
          · exact ⟨Or.inl rfl, by simp⟩
          · exact hm g (by simp [h])
      simp only [List.foldl_append, List.foldl_cons] at hz hj
      have ha := ih (pre ++ (⟨GateOp.and, [a]⟩ : Gate) :: post) (hmono a) (hcount a)
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [a]⟩)).getD o false = false))
        (by
          intro s hs
          simp only [List.foldl_append, List.foldl_cons]
          exact (Finset.mem_filter.mp hs).2)
        (by
          intro s hs t ht hne
          simp only [List.foldl_append, List.foldl_cons]
          exact (and_up _ a b o post hpost
            (hj s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 hne)).1)
      have hb := ih (pre ++ (⟨GateOp.and, [b]⟩ : Gate) :: post) (hmono b) (hcount b)
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [b]⟩)).getD o false = false))
        (by
          intro s hs
          simp only [List.foldl_append, List.foldl_cons]
          exact (Finset.mem_filter.mp hs).2)
        (by
          intro s hs t ht hne
          simp only [List.foldl_append, List.foldl_cons]
          exact (and_up _ a b o post hpost
            (hj s (Finset.mem_filter.mp hs).1 t (Finset.mem_filter.mp ht).1 hne)).2)
      have hsub : S ⊆ S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
            ⟨GateOp.and, [a]⟩)).getD o false = false) ∪
          S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
            ⟨GateOp.and, [b]⟩)).getD o false = false) := by
        intro s hs
        rcases and_zero _ a b o post (hz s hs) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, h⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, h⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [a]⟩)).getD o false = false))
        (S.filter (fun s => (post.foldl stp (stp (pre.foldl stp (List.ofFn (Z s)))
          ⟨GateOp.and, [b]⟩)).getD o false = false))
      have h3 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
      omega


theorem countP_le : ∀ (l : List Gate) (A : Finset ℕ) (s : ℕ),
    (∀ j g, l[j]? = some g → realAnd g = true → j + s ∈ A) →
    l.countP realAnd ≤ (A.filter (fun j => s ≤ j)).card := by
  intro l
  induction l with
  | nil => intro A s _; simp
  | cons x xs ih =>
    intro A s h
    have ih' := ih A (s + 1) (fun j g hj hp => by
      have := h (j + 1) g (by simpa using hj) hp
      rwa [show j + 1 + s = j + (s + 1) by omega] at this)
    by_cases hx : realAnd x = true
    · rw [List.countP_cons_of_pos hx]
      have hs : s ∈ A := by
        have := h 0 x (by simp) hx
        simpa using this
      have hsub : insert s (A.filter (fun j => s + 1 ≤ j)) ⊆ A.filter (fun j => s ≤ j) := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_filter] at hj ⊢
        rcases hj with rfl | ⟨h1, h2⟩
        · exact ⟨hs, le_refl _⟩
        · exact ⟨h1, by omega⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp)] at hc
      omega
    · rw [List.countP_cons_of_neg hx]
      have hsub : A.filter (fun j => s + 1 ≤ j) ⊆ A.filter (fun j => s ≤ j) := by
        intro j hj
        simp only [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, by omega⟩
      have hc := Finset.card_le_card hsub
      omega

def sample (r : Fin 8) (v : Fin 6) : Bool :=
  (([9, 10, 17, 18, 20, 33, 34, 36] : List ℕ).getD r.val 0).testBit v.val

abbrev hasEdge (x : Fin 6 → Bool) :=
  ∃ u v : Fin 6, (u.val, v.val) ∈
    ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧
    x u = true ∧ x v = true

theorem independent : ∀ r, ¬ hasEdge (sample r) := by decide

theorem pair_union : ∀ r s, r ≠ s → hasEdge (jn (sample r) (sample s)) := by decide

def lin (s : Fin 6 → Bool) (r : Fin 8) : Bool :=
  decide (∃ v, s v = true ∧ sample r v = true)

def Linear (f : Fin 8 → Bool) : Prop := ∃ s, f = lin s

theorem linear_false : Linear (fun _ => false) := by
  refine ⟨fun _ => false, ?_⟩
  funext r
  simp [lin]

theorem linear_true : Linear (fun _ => true) := by
  refine ⟨fun _ => true, ?_⟩
  exact (show (fun _ : Fin 8 => true) = lin (fun _ => true) by decide)

theorem linear_var (v : Fin 6) : Linear (fun r => sample r v) := by
  refine ⟨fun w => decide (w = v), ?_⟩
  funext r
  simp [lin]

theorem linear_or (f g : Fin 8 → Bool) (hf : Linear f) (hg : Linear g) :
    Linear (fun r => f r || g r) := by
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨t, rfl⟩ := hg
  refine ⟨fun v => s v || t v, ?_⟩
  funext r
  apply Bool.eq_iff_iff.mpr
  simp only [lin, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (⟨v, hv, hx⟩ | ⟨v, hv, hx⟩)
    · exact ⟨v, Or.inl hv, hx⟩
    · exact ⟨v, Or.inr hv, hx⟩
  · rintro ⟨v, hv | hv, hx⟩
    · exact Or.inl ⟨v, hv, hx⟩
    · exact Or.inr ⟨v, hv, hx⟩

theorem linear_gate (g : Gate)
    (hm : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hr : realAnd g = false) (f : ℕ → Fin 8 → Bool) (hf : ∀ i, Linear (f i)) :
    Linear (fun r => g.op.eval (g.inputs.map (fun i => f i r))) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hm
  change op = GateOp.and ∨ op = GateOp.or at hop
  change ins.length ≤ 2 at hlen
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · simpa [GateOp.eval] using linear_true
    · simpa [GateOp.eval] using linear_false
  · rcases hop with rfl | rfl <;> simpa [GateOp.eval] using hf a
  · rcases hop with rfl | rfl
    · simp [realAnd] at hr
    · simpa [GateOp.eval] using linear_or (f a) (f b) (hf a) (hf b)
  · simp at hlen

theorem linear_fold (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hr : gs.countP realAnd = 0) (W : Fin 8 → List Bool)
    (hlen : ∀ r, (W r).length = (W 0).length)
    (hw : ∀ i, Linear (fun r => (W r).getD i false)) :
    ∀ i, Linear (fun r => (gs.foldl stp (W r)).getD i false) := by
  induction gs generalizing W with
  | nil => exact hw
  | cons g gs ih =>
    have hg : realAnd g = false := by
      have h := List.countP_eq_zero.mp hr g (by simp)
      simpa using h
    have hgs : gs.countP realAnd = 0 := by
      simpa [List.countP_cons, hg] using hr
    apply ih (fun g' hg' => hm g' (by simp [hg'])) hgs (fun r => stp (W r) g)
    · intro r
      simp [stp, hlen r]
    · intro i
      simp only [stp]
      have he : (fun r => (W r ++ [g.op.eval (g.inputs.map fun j => (W r).getD j false)]).getD i false)
          = (fun r => if i < (W 0).length then (W r).getD i false else
            if i = (W 0).length then g.op.eval (g.inputs.map fun j => (W r).getD j false) else false) := by
        funext r
        rw [getD_app, hlen r]
      rw [he]
      by_cases h₁ : i < (W 0).length
      · simpa [h₁] using hw i
      · by_cases h₂ : i = (W 0).length
        · simpa [h₁, h₂] using linear_gate g (hm g (by simp)) hg
            (fun i r => (W r).getD i false) hw
        · simpa [h₁, h₂] using linear_false

theorem linear_prefix (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hr : gs.countP realAnd = 0) (i : ℕ) :
    Linear (fun r => (gs.foldl stp (List.ofFn (sample r))).getD i false) := by
  apply linear_fold gs hm hr (fun r => List.ofFn (sample r)) (by simp)
  intro j
  by_cases hj : j < 6
  · have he : (fun r => (List.ofFn (sample r)).getD j false) = fun r => sample r ⟨j, hj⟩ := by
      funext r
      exact getD_ofFn _ _ hj
    rw [he]
    exact linear_var _
  · have he : (fun r => (List.ofFn (sample r)).getD j false) = fun _ => false := by
      funext r
      exact getD_ge _ _ (by simp; omega)
    rw [he]
    exact linear_false

def agree (f g : Fin 8 → Bool) : Finset (Fin 8) :=
  Finset.univ.filter (fun r => (f r && g r) = f r)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem finite_obstruction : ∀ s t : Fin 6 → Bool,
    5 ≤ (agree (lin s) (lin t)).card ∨ 5 ≤ (agree (lin t) (lin s)).card := by
  decide

theorem linear_obstruction (f g : Fin 8 → Bool) (hf : Linear f) (hg : Linear g) :
    5 ≤ (agree f g).card ∨ 5 ≤ (agree g f).card := by
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨t, rfl⟩ := hg
  exact finite_obstruction s t

theorem first_and (gs : List Gate) (h : gs.countP realAnd ≠ 0) :
    ∃ pre post a b, gs = pre ++ (⟨GateOp.and, [a, b]⟩ : Gate) :: post ∧
      pre.countP realAnd = 0 := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    by_cases hg : realAnd g = true
    · obtain ⟨a, b, rfl⟩ := realAnd_spec g hg
      exact ⟨[], gs, a, b, rfl, rfl⟩
    · have hr : realAnd g = false := by simpa using hg
      have hz : gs.countP realAnd ≠ 0 := by simpa [List.countP_cons, hr] using h
      obtain ⟨pre, post, a, b, he, hc⟩ := ih hz
      refine ⟨g :: pre, post, a, b, ?_, ?_⟩
      · simp [he]
      · simp [List.countP_cons, hr, hc]

theorem no_three (gs : List Gate) (o : ℕ)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hc : gs.countP realAnd ≤ 3)
    (hz : ∀ r, (gs.foldl stp (List.ofFn (sample r))).getD o false = false)
    (hj : ∀ r s, r ≠ s →
      (gs.foldl stp (List.ofFn (jn (sample r) (sample s)))).getD o false = true) : False := by
  by_cases h0 : gs.countP realAnd = 0
  · have hb := bound0 sample o gs hm h0 Finset.univ (fun r _ => hz r)
      (fun r _ s _ hne => hj r s hne)
    simp at hb
  · obtain ⟨pre, post, a, b, rfl, hpre⟩ := first_and gs h0
    have hmPre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      fun g hg => hm g (by simp [hg])
    have hmPost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
      fun g hg => (hm g (by simp [hg])).1
    let W (r : Fin 8) := pre.foldl stp (List.ofFn (sample r))
    let f (r : Fin 8) := (W r).getD a false
    let g (r : Fin 8) := (W r).getD b false
    have hf : Linear f := linear_prefix pre hmPre hpre a
    have hg : Linear g := linear_prefix pre hmPre hpre b
    have hcPost : post.countP realAnd ≤ 2 := by
      have hh : post.countP realAnd < 3 := by
        simpa [List.countP_append, List.countP_cons, realAnd, hpre] using hc
      omega
    have save_bound (c : ℕ) (hcab : c = a ∨ c = b) (S : Finset (Fin 8))
        (he : ∀ r ∈ S, (f r && g r) = (W r).getD c false) : S.card ≤ 4 := by
      have hm' : ∀ h ∈ pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post,
          (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 := by
        intro h hh
        rcases List.mem_append.mp hh with hh | hh
        · exact hmPre h hh
        · rcases List.mem_cons.mp hh with rfl | hh
          · exact ⟨Or.inl rfl, by simp⟩
          · exact hm h (by simp [hh])
      have hc' : (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).countP realAnd ≤ 2 := by
        simpa [List.countP_append, List.countP_cons, realAnd, hpre] using hcPost
      apply bound sample o 2 (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post) hm' hc' S
      · intro r hr
        have h := hz r
        simp only [List.foldl_append, List.foldl_cons] at h ⊢
        have eq : stp (W r) ⟨GateOp.and, [a, b]⟩ = stp (W r) ⟨GateOp.and, [c]⟩ := by
          simp only [stp, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true]
          exact congrArg (fun z => W r ++ [z]) (he r hr)
        change (post.foldl stp (stp (W r) ⟨GateOp.and, [c]⟩)).getD o false = false
        rw [← eq]
        exact h
      · intro r _ s _ hrs
        have h := hj r s hrs
        simp only [List.foldl_append, List.foldl_cons] at h ⊢
        have hu := and_up _ a b o post hmPost h
        rcases hcab with rfl | rfl
        · exact hu.1
        · exact hu.2
    rcases linear_obstruction f g hf hg with h | h
    · have hb := save_bound a (Or.inl rfl) (agree f g) (by
        intro r hr
        exact (Finset.mem_filter.mp hr).2)
      omega
    · have hb := save_bound b (Or.inr rfl) (agree g f) (by
        intro r hr
        simpa only [Bool.and_comm] using (Finset.mem_filter.mp hr).2)
      omega

end PEqualNP.Outside.L_meta_282_aux

namespace PEqualNP.Outside

open PEqualNP.Outside.L_meta_282_aux PEqualNP.CircuitLowerBounds

theorem L_meta_282 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro ⟨C, ⟨hM, A, hA, hAnd⟩, hcomp⟩
  have hm : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hM g hg
    exact ⟨by simpa using h.1, h.2⟩
  have hc : C.gates.countP realAnd ≤ 3 := by
    have h1 := countP_le C.gates A 0 (fun j g hj hp => by
      obtain ⟨a, b, rfl⟩ := realAnd_spec g hp
      exact hAnd j _ hj rfl)
    have h2 := Finset.card_filter_le A (fun j => 0 ≤ j)
    omega
  apply no_three C.gates C.output hm hc
  · intro r
    by_contra hne
    have ht : C.eval (List.ofFn (sample r)) = true := by
      simpa [Circuit.eval, wires_eq] using hne
    exact independent r ((hcomp _).mp ht)
  · intro r s hrs
    have h := (hcomp _).mpr (pair_union r s hrs)
    simpa [Circuit.eval, wires_eq] using h

end PEqualNP.Outside
