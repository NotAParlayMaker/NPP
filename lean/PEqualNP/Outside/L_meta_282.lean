import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_282

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- One evaluation step: the gate adds one wire.
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

-- The join of two inputs.
def jn {n : ℕ} (z z' : Fin n → Bool) : Fin n → Bool := fun i => z i || z' i

-- An AND gate that really reads two wires.
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

-- Raising wire values never lowers a later wire of a circuit of AND and OR gates.
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

-- A gate that is not a real AND gate commutes with the join.
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

-- Without a real AND gate the circuit commutes with joins, so at most one member of a
-- family of zeros with pairwise true joins exists.
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

-- Replacing a real AND gate by one of its two operands.
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

-- A family of zeros whose pairwise joins are true has at most 2 ^ r members when the circuit
-- has at most r real AND gates.
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

-- The real AND gates are among the listed AND gates.
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

def left (p : Fin 8) : Fin 6 := ![0, 0, 0, 1, 1, 1, 2, 2] p
def right (p : Fin 8) : Fin 6 := ![3, 4, 5, 3, 4, 5, 4, 5] p
def single (i : Fin 6) : Fin 6 → Bool := fun v => decide (v = i)
def Zt (p : Fin 8) : Fin 6 → Bool := jn (single (left p)) (single (right p))
def hit (a : Fin 6 → Bool) (p : Fin 8) : Bool := a (left p) || a (right p)

theorem noedge : ∀ p : Fin 8, ¬ ∃ u v : Fin 6,
    (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧
      Zt p u = true ∧ Zt p v = true := by decide

theorem joinedge : ∀ p q : Fin 8, p ≠ q → ∃ u v : Fin 6,
    (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧
      jn (Zt p) (Zt q) u = true ∧ jn (Zt p) (Zt q) v = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem obstruction : ∀ a b : Fin 6 → Bool,
    (∀ p : Fin 8, hit a p ≠ hit b p) →
    (Finset.univ.filter (fun p : Fin 8 => hit a p = false)).card ≤ 4 →
    (Finset.univ.filter (fun p : Fin 8 => hit b p = false)).card ≤ 4 → False := by
  decide

theorem first_real (gs : List Gate) (h : gs.countP realAnd ≠ 0) :
    ∃ pre post a b, gs = pre ++ (⟨GateOp.and, [a,b]⟩ : Gate) :: post ∧
      ∀ g ∈ pre, realAnd g = false := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    by_cases hg : realAnd g = true
    · obtain ⟨a,b,rfl⟩ := realAnd_spec g hg
      exact ⟨[], gs, a, b, rfl, by simp⟩
    · have hg' : realAnd g = false := by simpa using hg
      have ht : gs.countP realAnd ≠ 0 := by simpa [List.countP_cons, hg'] using h
      obtain ⟨pre,post,a,b,he,hpre⟩ := ih ht
      refine ⟨g :: pre,post,a,b,by simp [he],?_⟩
      intro g' hg'
      rcases List.mem_cons.mp hg' with rfl | hmem
      · exact by simpa using hg
      · exact hpre g' hmem

theorem stp_same (W : List Bool) (a b : ℕ) (h : W.getD a false = W.getD b false) :
    stp W ⟨GateOp.and, [a,b]⟩ = stp W ⟨GateOp.and, [a]⟩ ∧
    stp W ⟨GateOp.and, [a,b]⟩ = stp W ⟨GateOp.and, [b]⟩ := by
  simp only [stp, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, h, Bool.and_self, and_self]

theorem stp_left_false (W : List Bool) (a b : ℕ) (h : W.getD a false = false) :
    stp W ⟨GateOp.and, [a,b]⟩ = stp W ⟨GateOp.and, [a]⟩ := by
  simp only [stp, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, h, Bool.false_and]

theorem stp_right_false (W : List Bool) (a b : ℕ) (h : W.getD b false = false) :
    stp W ⟨GateOp.and, [a,b]⟩ = stp W ⟨GateOp.and, [b]⟩ := by
  simp only [stp, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    id_eq, Bool.and_true, h, Bool.and_false]

set_option maxHeartbeats 800000 in
theorem no_three (gs : List Gate) (o : ℕ)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hc : gs.countP realAnd ≤ 3)
    (hz : ∀ p, (gs.foldl stp (List.ofFn (Zt p))).getD o false = false)
    (hj : ∀ p q, p ≠ q → (gs.foldl stp (List.ofFn (jn (Zt p) (Zt q)))).getD o false = true) :
    False := by
  by_cases h0 : gs.countP realAnd = 0
  · have h := bound0 Zt o gs hm h0 (Finset.univ : Finset (Fin 8))
      (fun p _ => hz p) (fun p _ q _ hne => hj p q hne)
    norm_num at h
  obtain ⟨pre,post,a,b,rfl,hpre⟩ := first_real gs h0
  have hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hg => (hm g (by simp [hg])).1
  have hcount : ∀ c : ℕ, (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).countP realAnd ≤ 2 := by
    intro c
    have e1 : (pre ++ (⟨GateOp.and, [a,b]⟩ : Gate) :: post).countP realAnd =
        pre.countP realAnd + (post.countP realAnd + 1) := by
      rw [List.countP_append, List.countP_cons_of_pos (by simp [realAnd])]
    have e2 : (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).countP realAnd =
        pre.countP realAnd + post.countP realAnd := by
      rw [List.countP_append, List.countP_cons_of_neg (by simp [realAnd])]
    omega
  have hmono : ∀ c : ℕ, ∀ g ∈ pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro c g hg
    rcases List.mem_append.mp hg with h | h
    · exact hm g (by simp [h])
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨Or.inl rfl, by simp⟩
      · exact hm g (by simp [h])
  let W (p : Fin 8) := pre.foldl stp (List.ofFn (Zt p))
  let ev (c : ℕ) (p : Fin 8) := (post.foldl stp (stp (W p) ⟨GateOp.and, [c]⟩)).getD o false
  let U (c : ℕ) := Finset.univ.filter (fun p : Fin 8 => ev c p = false)
  have hz' : ∀ p, (post.foldl stp (stp (W p) ⟨GateOp.and, [a,b]⟩)).getD o false = false := by
    simpa only [List.foldl_append, List.foldl_cons] using hz
  have hj' : ∀ p q, p ≠ q →
      (post.foldl stp (stp (pre.foldl stp (List.ofFn (jn (Zt p) (Zt q))))
        ⟨GateOp.and, [a,b]⟩)).getD o false = true := by
    simpa only [List.foldl_append, List.foldl_cons] using hj
  have hU : ∀ c ∈ [a,b], (U c).card ≤ 4 := by
    intro c hc'
    have hup : ∀ p q, p ≠ q →
        ((pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post).foldl stp
          (List.ofFn (jn (Zt p) (Zt q)))).getD o false = true := by
      intro p q hne
      simp only [List.foldl_append, List.foldl_cons]
      have h := and_up _ a b o post hpost (hj' p q hne)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl
      · exact h.1
      · exact h.2
    have h := bound Zt o 2 (pre ++ (⟨GateOp.and, [c]⟩ : Gate) :: post)
      (hmono c) (hcount c) (U c)
      (by
        intro p hp
        simp only [List.foldl_append, List.foldl_cons]
        exact (Finset.mem_filter.mp hp).2)
      (fun p _ q _ hne => hup p q hne)
    exact h
  have hua := hU a (by simp)
  have hub := hU b (by simp)
  have hcov : U a ∪ U b = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro p
    rcases and_zero (W p) a b o post (hz' p) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hi : U a ∩ U b = ∅ := by
    apply Finset.card_eq_zero.mp
    have h := Finset.card_union_add_card_inter (U a) (U b)
    rw [hcov] at h
    norm_num at h
    omega
  have hdis : ∀ p, p ∈ U a → p ∈ U b → False := by
    intro p ha hb
    have h := Finset.mem_inter.mpr ⟨ha,hb⟩
    rw [hi] at h
    exact Finset.notMem_empty p h
  let V (c : ℕ) (i : Fin 6) := (pre.foldl stp (List.ofFn (single i))).getD c false
  have hv : ∀ c p, (W p).getD c false = hit (V c) p := by
    intro c p
    exact join_fold pre _ _ _ (by simp) (by simp)
      (fun g hg => ⟨hm g (by simp [hg]),hpre g hg⟩)
      (ofFn_jn (single (left p)) (single (right p))) c
  have hdiff : ∀ p, hit (V a) p ≠ hit (V b) p := by
    intro p he
    have hs : (W p).getD a false = (W p).getD b false := by rw [hv,hv,he]
    have h := stp_same (W p) a b hs
    apply hdis p
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change (post.foldl stp (stp (W p) ⟨GateOp.and,[a]⟩)).getD o false = false
      rw [← h.1]
      exact hz' p
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change (post.foldl stp (stp (W p) ⟨GateOp.and,[b]⟩)).getD o false = false
      rw [← h.2]
      exact hz' p
  have hfa : (Finset.univ.filter (fun p : Fin 8 => hit (V a) p = false)).card ≤ 4 := by
    apply le_trans (Finset.card_le_card ?_) hua
    intro p hp
    have hs : (W p).getD a false = false := (hv a p).trans (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (post.foldl stp (stp (W p) ⟨GateOp.and,[a]⟩)).getD o false = false
    rw [← stp_left_false (W p) a b hs]
    exact hz' p
  have hfb : (Finset.univ.filter (fun p : Fin 8 => hit (V b) p = false)).card ≤ 4 := by
    apply le_trans (Finset.card_le_card ?_) hub
    intro p hp
    have hs : (W p).getD b false = false := (hv b p).trans (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (post.foldl stp (stp (W p) ⟨GateOp.and,[b]⟩)).getD o false = false
    rw [← stp_right_false (W p) a b hs]
    exact hz' p
  exact obstruction (V a) (V b) hdiff hfa hfb

end PEqualNP.Outside.L_meta_282

open PEqualNP.Outside.L_meta_282 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_282 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 3 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A)) ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 5), (4, 5), (2, 3)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro ⟨C, ⟨hM, A, hA, hAnd⟩, hcomp⟩
  have hm : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have := hM g hg
    exact ⟨by simpa using this.1, this.2⟩
  have hc : C.gates.countP realAnd ≤ 3 := by
    have h1 := countP_le C.gates A 0 (fun j g hj hp => by
      obtain ⟨a, b, rfl⟩ := realAnd_spec g hp
      exact hAnd j _ hj rfl)
    have h2 := Finset.card_filter_le A (fun j => 0 ≤ j)
    omega
  apply no_three C.gates C.output hm hc
  · intro p
    by_contra hne
    have ht : C.eval (List.ofFn (Zt p)) = true := by
      simpa [Circuit.eval, wires_eq] using hne
    exact noedge p ((hcomp (Zt p)).mp ht)
  · intro p q hne
    have h := (hcomp (jn (Zt p) (Zt q))).mpr (joinedge p q hne)
    simpa [Circuit.eval, wires_eq] using h
