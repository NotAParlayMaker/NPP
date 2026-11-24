import Mathlib
import PEqualNP.Defs

-- Removing an AND pair below a quadrangle-false AND gate.

namespace PEqualNP.Outside.L_meta_2061_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

-- Wire values.

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

theorem eval_V (C : Circuit) (x : List Bool) : C.eval x = V C.gates x C.output := rfl

theorem V_prefix (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
    V (pre ++ post) x w = V pre x w := by
  unfold V
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; exact h)]

theorem V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)

theorem getElem?_gateAt (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    C.gates[k]? = some (gateAt C k) := by
  rw [List.getElem?_eq_getElem hk]
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem gateAt_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k ∈ C.gates := by
  have h := getElem?_gateAt C k hk
  rw [List.getElem?_eq_getElem hk] at h
  rw [← Option.some_inj.mp h]
  exact List.getElem_mem hk

theorem gval (n : ℕ) (C : Circuit) (hb : ReadsBack n C) (x : List Bool) (hx : x.length = n)
    (k : ℕ) (hk : k < C.gates.length) :
    V C.gates x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map (V C.gates x)) := by
  obtain ⟨pre, post, hsplit, hlen⟩ := split_at C.gates k (gateAt C k) (getElem?_gateAt C k hk)
  have hw : ∀ w ∈ (gateAt C k).inputs, w < n + k := hb k hk
  generalize gateAt C k = g at hsplit hw ⊢
  rw [hsplit]
  rw [← hlen] at hw ⊢
  show (wiresFrom (pre ++ g :: post) x).getD (n + pre.length) false = _
  rw [wire_at n pre post g x hx]
  congr 1
  apply List.map_congr_left
  intro w hwm
  exact (V_prefix pre (g :: post) x w (by rw [hx]; exact hw w hwm)).symm

-- Deleting gate r and redirecting its readers to wire t.

def sd (m u : ℕ) : ℕ := if m < u then u - 1 else u

def al (m t u : ℕ) : ℕ := if u = m then t else sd m u

def alG (m t : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (al m t)⟩

def del (n r t : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take r ++ (C.gates.drop (r + 1)).map (alG (n + r) t), al (n + r) t C.output⟩

theorem del_len (n r t : ℕ) (C : Circuit) (hr : r < C.gates.length) :
    (del n r t C).gates.length = C.gates.length - 1 := by
  simp [del]; omega

theorem gateAt_del_lt (n r t : ℕ) (C : Circuit) (hr : r < C.gates.length) (k : ℕ) (hk : k < r) :
    gateAt (del n r t C) k = gateAt C k := by
  unfold gateAt del
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hk]

theorem gateAt_del_ge (n r t : ℕ) (C : Circuit) (hr : r < C.gates.length) (k : ℕ) (hk : r ≤ k) :
    gateAt (del n r t C) k = alG (n + r) t (gateAt C (k + 1)) := by
  unfold gateAt del
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  have h1 : (List.take r C.gates).length = r := by simp; omega
  rw [h1, List.getElem?_map, List.getElem?_drop]
  have h2 : r + 1 + (k - r) = k + 1 := by omega
  rw [h2]
  cases C.gates[k + 1]? <;> simp [alG]

theorem del_mono (n r t : ℕ) (C : Circuit) (hm : Monotone2 C) : Monotone2 (del n r t C) := by
  intro g hg
  simp only [del, List.mem_append, List.mem_map] at hg
  rcases hg with hg | ⟨g0, hg0, rfl⟩
  · exact hm g (List.mem_of_mem_take hg)
  · have := hm g0 (List.mem_of_mem_drop hg0)
    simpa [alG] using this

theorem al_lt (n r t u k : ℕ) (ht : t < n + r) (hrk : r ≤ k) (hu : u < n + (k + 1)) :
    al (n + r) t u < n + k := by
  unfold al sd; split_ifs <;> omega

theorem del_rb (n r t : ℕ) (C : Circuit) (hb : ReadsBack n C) (hr : r < C.gates.length)
    (ht : t < n + r) : ReadsBack n (del n r t C) := by
  intro k hk w hw
  rw [del_len n r t C hr] at hk
  by_cases hkr : k < r
  · rw [gateAt_del_lt n r t C hr k hkr] at hw
    exact hb k (by omega) w hw
  · rw [gateAt_del_ge n r t C hr k (by omega)] at hw
    simp only [alG, List.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    exact al_lt n r t u k ht (by omega) (hb (k + 1) (by omega) u hu)

theorem V_del_lt (n r t : ℕ) (C : Circuit) (hr : r < C.gates.length) (x : List Bool)
    (hx : x.length = n) (u : ℕ) (hu : u < n + r) :
    V (del n r t C).gates x u = V C.gates x u := by
  have h1 : (del n r t C).gates = C.gates.take r ++ (C.gates.drop (r + 1)).map (alG (n + r) t) :=
    rfl
  have h2 : C.gates = C.gates.take r ++ C.gates.drop r := (List.take_append_drop r C.gates).symm
  rw [h1, V_prefix _ _ _ _ (by simp [hx]; omega)]
  conv_rhs => rw [h2]
  rw [V_prefix _ _ _ _ (by simp [hx]; omega)]

theorem V_del (n r t : ℕ) (C : Circuit) (hb : ReadsBack n C) (hr : r < C.gates.length)
    (ht : t < n + r) (x : List Bool) (hx : x.length = n)
    (hval : V C.gates x (n + r) = V C.gates x t) :
    ∀ u, V (del n r t C).gates x (al (n + r) t u) = V C.gates x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  by_cases hlt : u < n + r
  · have : al (n + r) t u = u := by unfold al sd; split_ifs <;> omega
    rw [this, V_del_lt n r t C hr x hx u hlt]
  by_cases heq : u = n + r
  · have : al (n + r) t u = t := by simp [al, heq]
    rw [this, V_del_lt n r t C hr x hx t ht, heq, hval]
  have hal : al (n + r) t u = u - 1 := by unfold al sd; split_ifs <;> omega
  rw [hal]
  by_cases hin : u < n + C.gates.length
  · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
    have hk : k + 1 < C.gates.length := by omega
    have hrk : r ≤ k := by omega
    have hkD : k < (del n r t C).gates.length := by rw [del_len n r t C hr]; omega
    rw [show n + (k + 1) - 1 = n + k by omega, gval n _ (del_rb n r t C hb hr ht) x hx k hkD,
      gval n C hb x hx (k + 1) hk, gateAt_del_ge n r t C hr k hrk]
    simp only [alG, List.map_map]
    congr 1
    apply List.map_congr_left
    intro w hw
    exact ih w (hb (k + 1) hk w hw)
  · rw [V_out _ _ _ (by rw [hx, del_len n r t C hr]; omega), V_out _ _ _ (by rw [hx]; omega)]

theorem del_eval (n r t : ℕ) (C : Circuit) (hb : ReadsBack n C) (hr : r < C.gates.length)
    (ht : t < n + r) (x : List Bool) (hx : x.length = n)
    (hval : V C.gates x (n + r) = V C.gates x t) :
    (del n r t C).eval x = C.eval x :=
  V_del n r t C hb hr ht x hx hval C.output

theorem del_out (n r t : ℕ) (C : Circuit) (hr : r < C.gates.length) (ht : t < n + r)
    (ho : C.output < n + C.gates.length) :
    (del n r t C).output < n + (del n r t C).gates.length := by
  rw [del_len n r t C hr]
  show al (n + r) t C.output < _
  unfold al sd; split_ifs <;> omega


-- Appending an OR gate as the new output.

def app (n o i : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [o, n + i]⟩], n + C.gates.length⟩

theorem app_len (n o i : ℕ) (C : Circuit) :
    (app n o i C).gates.length = C.gates.length + 1 := by
  simp [app]

theorem app_eval (n o i : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) :
    (app n o i C).eval x = (V C.gates x o || V C.gates x (n + i)) := by
  show (wiresFrom (C.gates ++ [⟨GateOp.or, [o, n + i]⟩]) x).getD (n + C.gates.length) false = _
  rw [wire_at n C.gates [] _ x hx]
  simp [GateOp.eval, V]

theorem gateAt_app_lt (n o i : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt (app n o i C) k = gateAt C k := by
  unfold gateAt app
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hk]

theorem gateAt_app_len (n o i : ℕ) (C : Circuit) :
    gateAt (app n o i C) C.gates.length = ⟨GateOp.or, [o, n + i]⟩ := by
  unfold gateAt app
  simp

theorem app_mono (n o i : ℕ) (C : Circuit) (hm : Monotone2 C) : Monotone2 (app n o i C) := by
  intro g hg
  simp only [app, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact hm g hg
  · simp

theorem app_rb (n o i : ℕ) (C : Circuit) (hb : ReadsBack n C) (ho : o < n + C.gates.length)
    (hi : i < C.gates.length) : ReadsBack n (app n o i C) := by
  intro k hk w hw
  rw [app_len] at hk
  by_cases hkl : k < C.gates.length
  · rw [gateAt_app_lt n o i C k hkl] at hw
    exact hb k hkl w hw
  · have hk' : k = C.gates.length := by omega
    subst hk'
    rw [gateAt_app_len] at hw
    simp at hw
    rcases hw with rfl | rfl <;> omega

-- Cones.

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


theorem cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  simp [cones, coneFold_length]

theorem cone_lt_len (n : ℕ) (C : Circuit) (a b : ℕ) (h : InCone n C a b) :
    b < C.gates.length := by
  by_contra hb
  unfold InCone at h
  rw [List.getD_eq_default _ _ (by rw [cones_length]; omega)] at h
  simp at h

theorem cone_lt (n : ℕ) (C : Circuit) : ∀ b a, InCone n C a b → a < b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro a h
  have hb := cone_lt_len n C a b h
  rw [inCone_iff n C a b hb] at h
  obtain ⟨w, _, hn, hlt, h⟩ := h
  rcases h with h | h
  · omega
  · have := ih (w - n) (by omega) a h; omega

theorem cone_direct (n : ℕ) (C : Circuit) (b w : ℕ) (hb : b < C.gates.length)
    (hw : w ∈ (gateAt C b).inputs) (hn : n ≤ w) (hlt : w < n + b) : InCone n C (w - n) b :=
  (inCone_iff n C (w - n) b hb).2 ⟨w, hw, hn, hlt, Or.inl rfl⟩

theorem cone_trans (n : ℕ) (C : Circuit) :
    ∀ c a b, InCone n C a b → InCone n C b c → InCone n C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro a b hab hbc
  have hc := cone_lt_len n C b c hbc
  rw [inCone_iff n C b c hc] at hbc
  rw [inCone_iff n C a c hc]
  obtain ⟨w, hw, hn, hlt, h⟩ := hbc
  refine ⟨w, hw, hn, hlt, Or.inr ?_⟩
  rcases h with h | h
  · rw [← h]; exact hab
  · exact ih (w - n) (by omega) a b hab h

theorem cone_reader (n : ℕ) (C : Circuit) : ∀ b a, InCone n C a b →
    ∃ c, c < C.gates.length ∧ n + a ∈ (gateAt C c).inputs := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro a h
  have hb := cone_lt_len n C a b h
  rw [inCone_iff n C a b hb] at h
  obtain ⟨w, hw, hn, hlt, h⟩ := h
  rcases h with h | h
  · refine ⟨b, hb, ?_⟩
    rw [show n + a = w by omega]; exact hw
  · exact ih (w - n) (by omega) a h

theorem cones_app (n o i : ℕ) (C : Circuit) (b : ℕ) (hb : b < C.gates.length) (a : ℕ) :
    InCone n (app n o i C) a b ↔ InCone n C a b := by
  unfold InCone cones app
  simp only
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, coneStep_getD_lt]
  rw [coneFold_length]; simpa using hb

def psi (r k : ℕ) : ℕ := if k < r then k else k + 1

theorem psi_lt (r k : ℕ) (h : k < r) : psi r k = k := by simp [psi, h]

theorem psi_ge (r k : ℕ) (h : r ≤ k) : psi r k = k + 1 := by
  unfold psi; split_ifs <;> omega

theorem psi_inj (r : ℕ) : Function.Injective (psi r) := by
  intro a b h
  unfold psi at h
  split_ifs at h <;> omega

theorem op_del (n r t : ℕ) (C : Circuit) (hr : r < C.gates.length) (k : ℕ) :
    (gateAt (del n r t C) k).op = (gateAt C (psi r k)).op := by
  by_cases hk : k < r
  · rw [gateAt_del_lt n r t C hr k hk, psi_lt r k hk]
  · rw [gateAt_del_ge n r t C hr k (by omega), psi_ge r k (by omega)]; rfl

theorem cone_del (n r t : ℕ) (C : Circuit) (hr : r < C.gates.length) (ht : t < n + r)
    (htin : t ∈ (gateAt C r).inputs) :
    ∀ b a, InCone n (del n r t C) a b → InCone n C (psi r a) (psi r b) := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro a h
  have hbD := cone_lt_len n _ a b h
  have hbD' : b < C.gates.length - 1 := by rw [del_len n r t C hr] at hbD; exact hbD
  rw [inCone_iff n _ a b hbD] at h
  obtain ⟨w, hw, hnw, hwb, hcase⟩ := h
  by_cases hbr : b < r
  · rw [gateAt_del_lt n r t C hr b hbr] at hw
    rw [psi_lt r b hbr, inCone_iff n C _ b (by omega)]
    refine ⟨w, hw, hnw, hwb, ?_⟩
    rcases hcase with h | h
    · left; rw [h, psi_lt r _ (by omega)]
    · right
      have := ih (w - n) (by omega) a h
      rwa [psi_lt r (w - n) (by omega)] at this
  · rw [gateAt_del_ge n r t C hr b (by omega)] at hw
    rw [psi_ge r b (by omega)]
    simp only [alG, List.mem_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have hb1 : b + 1 < C.gates.length := by omega
    by_cases hur : u = n + r
    · simp only [al, ite_eq_left hur] at hnw hwb hcase
      subst hur
      have hcr : InCone n C (t - n) r := cone_direct n C r t hr htin hnw ht
      have hrb : InCone n C r (b + 1) := by
        have := cone_direct n C (b + 1) (n + r) hb1 hu (by omega) (by omega)
        simpa using this
      have hcb := cone_trans n C (b + 1) (t - n) r hcr hrb
      rcases hcase with h | h
      · rw [h, psi_lt r _ (by omega)]; exact hcb
      · have := ih (t - n) (by omega) a h
        rw [psi_lt r (t - n) (by omega)] at this
        exact cone_trans n C (b + 1) _ (t - n) this hcb
    · simp only [al, ite_eq_right hur] at hnw hwb hcase
      have hnu : n ≤ u := by unfold sd at hnw; split_ifs at hnw <;> omega
      have hpsi : psi r (sd (n + r) u - n) = u - n := by
        unfold sd psi; split_ifs <;> omega
      have hub : u < n + (b + 1) := by unfold sd at hwb; split_ifs at hwb <;> omega
      have hdir := cone_direct n C (b + 1) u hb1 hu hnu hub
      rcases hcase with h | h
      · rw [h, hpsi]; exact hdir
      · have := ih (sd (n + r) u - n) (by omega) a h
        rw [hpsi] at this
        exact cone_trans n C (b + 1) _ (u - n) this hdir

theorem app_pair (n o i : ℕ) (D : Circuit) (a b : ℕ) (hb : b < D.gates.length + 1)
    (hopb : (gateAt (app n o i D) b).op = GateOp.and) (hc : InCone n (app n o i D) a b) :
    b < D.gates.length ∧ a < D.gates.length ∧ InCone n D a b ∧
      gateAt (app n o i D) a = gateAt D a ∧ gateAt (app n o i D) b = gateAt D b := by
  have hbl : b < D.gates.length := by
    by_contra h
    have : b = D.gates.length := by omega
    rw [this, gateAt_app_len] at hopb
    simp at hopb
  have hcD := (cones_app n o i D b hbl a).1 hc
  have hab := cone_lt n D b a hcD
  exact ⟨hbl, by omega, hcD, gateAt_app_lt n o i D a (by omega), gateAt_app_lt n o i D b hbl⟩

theorem pairs_lt (n r t o i : ℕ) (C : Circuit) (hr : r < C.gates.length) (ht : t < n + r)
    (htin : t ∈ (gateAt C r).inputs) (a0 b0 : ℕ) (ha0 : a0 < C.gates.length)
    (hb0 : b0 < C.gates.length) (hop0 : (gateAt C a0).op = GateOp.and)
    (hop1 : (gateAt C b0).op = GateOp.and) (hc0 : InCone n C a0 b0)
    (hno : ∀ a b, InCone n (del n r t C) a b → ¬(psi r a = a0 ∧ psi r b = b0)) :
    andPairs n (app n o i (del n r t C)) < andPairs n C := by
  have hlenD := del_len n r t C hr
  unfold andPairs
  have hinj : Function.Injective (Prod.map (psi r) (psi r)) := (psi_inj r).prodMap (psi_inj r)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨(a0, b0), ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a, b⟩, hp, rfl⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨_, hb⟩, hopa, hopb, hc⟩ := hp
    rw [app_len] at hb
    obtain ⟨hbl, hal, hcD, hga, hgb⟩ := app_pair n o i _ a b hb hopb hc
    rw [hga, op_del n r t C hr] at hopa
    rw [hgb, op_del n r t C hr] at hopb
    rw [hlenD] at hbl hal
    simp only [Prod.map_apply, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨?_, ?_⟩, hopa, hopb, cone_del n r t C hr ht htin b a hcD⟩ <;>
      unfold psi <;> split_ifs <;> omega
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨ha0, hb0⟩, hop0, hop1, hc0⟩
  · rw [Finset.mem_image]
    rintro ⟨⟨a, b⟩, hp, heq⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨_, hb⟩, _, hopb, hc⟩ := hp
    rw [app_len] at hb
    obtain ⟨_, _, hcD, _, _⟩ := app_pair n o i _ a b hb hopb hc
    simp only [Prod.map_apply, Prod.mk.injEq] at heq
    exact hno a b hcD heq


-- Gate values.

theorem valA (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ) (v : ℕ)
    (hall : ∀ u ∈ l, u = v) (hv : v ∈ l) (f : ℕ → Bool) : op.eval (l.map f) = f v := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map]
    rw [Bool.eq_iff_iff, List.all_eq_true]
    constructor
    · intro h; simpa using h v hv
    · intro h u hu; rw [hall u hu]; simpa using h
  · simp only [GateOp.eval, List.any_map]
    rw [Bool.eq_iff_iff, List.any_eq_true]
    constructor
    · rintro ⟨u, hu, h⟩; rw [hall u hu] at h; simpa using h
    · intro h; exact ⟨v, hv, by simpa using h⟩

theorem valB (op : GateOp) (hop : op = GateOp.and) (l : List ℕ) (v : ℕ) (hv : v ∈ l)
    (f : ℕ → Bool) (hf : f v = false) : op.eval (l.map f) = false := by
  subst hop
  simp only [GateOp.eval, List.all_map]
  rw [Bool.eq_false_iff]
  intro h
  rw [List.all_eq_true] at h
  have := h v hv
  simp [hf] at this

theorem valC (op : GateOp) (hop : op = GateOp.or) (l : List ℕ) (v y : ℕ)
    (hall : ∀ u ∈ l, u = v ∨ u = y) (hy : y ∈ l) (f : ℕ → Bool) (hf : f v = false) :
    op.eval (l.map f) = f y := by
  subst hop
  simp only [GateOp.eval, List.any_map]
  rw [Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨u, hu, h⟩
    rcases hall u hu with rfl | rfl
    · simp [hf] at h
    · simpa using h
  · intro h; exact ⟨y, hy, by simpa using h⟩

theorem two_elems (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : ∀ u ∈ l, u = a ∨ u = b := by
  match l, hl with
  | [], _ => simp at ha
  | [p], _ => simp at ha hb; omega
  | [p, q], _ => intro u hu; simp at ha hb hu; omega
  | _ :: _ :: _ :: _, hl => simp at hl

theorem mono_gate (C : Circuit) (hm : Monotone2 C) (k : ℕ) (hk : k < C.gates.length) :
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length ≤ 2 := by
  have h := hm _ (gateAt_mem C k hk)
  refine ⟨?_, h.2⟩
  have := h.1
  simpa using this

-- Correctness on the test inputs.

abbrev Good (Pos Neg : List Bool → Prop) (C : Circuit) : Prop :=
  (∀ x, Pos x → C.eval x = true) ∧ (∀ x, Neg x → C.eval x = false)

theorem good_app (n i : ℕ) (Pos Neg : List Bool → Prop) (hP : ∀ x, Pos x → x.length = n)
    (hN : ∀ x, Neg x → x.length = n) (C D : Circuit) (hg : Good Pos Neg C)
    (hneg : ∀ x, Neg x → V C.gates x (n + i) = false)
    (hDi : ∀ x : List Bool, x.length = n → V D.gates x (n + i) = V C.gates x (n + i))
    (hDe : ∀ x : List Bool, x.length = n → V C.gates x (n + i) = false → D.eval x = C.eval x) :
    Good Pos Neg (app n D.output i D) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have hl := hP x hx
    rw [app_eval n _ i D x hl, hDi x hl]
    cases hc : V C.gates x (n + i)
    · rw [← eval_V D x, hDe x hl hc, hg.1 x hx]; rfl
    · simp
  · intro x hx
    have hl := hN x hx
    rw [app_eval n _ i D x hl, hDi x hl, hneg x hx, ← eval_V D x, hDe x hl (hneg x hx),
      hg.2 x hx]
    rfl

theorem caseA (n i r : ℕ) (Pos Neg : List Bool → Prop) (hP : ∀ x, Pos x → x.length = n)
    (hN : ∀ x, Neg x → x.length = n) (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack n C)
    (hg : Good Pos Neg C) (hr : r < C.gates.length) (hin : n + i ∈ (gateAt C r).inputs)
    (hall : ∀ u ∈ (gateAt C r).inputs, u = n + i) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ Good Pos Neg D ∧ D.size < C.size := by
  have ht : n + i < n + r := hb r hr _ hin
  have hval : ∀ x : List Bool, x.length = n → V C.gates x (n + r) = V C.gates x (n + i) := by
    intro x hx
    rw [gval n C hb x hx r hr]
    exact valA _ (mono_gate C hm r hr).1 _ _ hall hin _
  refine ⟨del n r (n + i) C, del_mono n r _ C hm, del_rb n r _ C hb hr ht, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rw [del_eval n r _ C hb hr ht x (hP x hx) (hval x (hP x hx))]; exact hg.1 x hx
  · intro x hx
    rw [del_eval n r _ C hb hr ht x (hN x hx) (hval x (hN x hx))]; exact hg.2 x hx
  · show (del n r (n + i) C).gates.length < C.gates.length
    rw [del_len n r _ C hr]; omega

theorem delApp (n i r t : ℕ) (Pos Neg : List Bool → Prop) (hP : ∀ x, Pos x → x.length = n)
    (hN : ∀ x, Neg x → x.length = n) (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack n C)
    (hg : Good Pos Neg C) (hout : C.output < n + C.gates.length) (hir : i < r)
    (hr : r < C.gates.length) (ht : t < n + r)
    (hneg : ∀ x, Neg x → V C.gates x (n + i) = false)
    (hval : ∀ x : List Bool, x.length = n → V C.gates x (n + i) = false →
      V C.gates x (n + r) = V C.gates x t) :
    Monotone2 (app n (del n r t C).output i (del n r t C)) ∧
      ReadsBack n (app n (del n r t C).output i (del n r t C)) ∧
      Good Pos Neg (app n (del n r t C).output i (del n r t C)) ∧
      (app n (del n r t C).output i (del n r t C)).size = C.size := by
  refine ⟨app_mono _ _ _ _ (del_mono n r t C hm),
    app_rb _ _ _ _ (del_rb n r t C hb hr ht) (del_out n r t C hr ht hout)
      (by rw [del_len n r t C hr]; omega),
    good_app n i Pos Neg hP hN C _ hg hneg ?_ ?_, ?_⟩
  · intro x hx; exact V_del_lt n r t C hr x hx _ (by omega)
  · intro x hx hc; exact del_eval n r t C hb hr ht x hx (hval x hx hc)
  · show (app n (del n r t C).output i (del n r t C)).gates.length = C.gates.length
    rw [app_len, del_len n r t C hr]; omega

theorem caseB (n i r : ℕ) (Pos Neg : List Bool → Prop) (hP : ∀ x, Pos x → x.length = n)
    (hN : ∀ x, Neg x → x.length = n) (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack n C)
    (hg : Good Pos Neg C) (hout : C.output < n + C.gates.length) (hr : r < C.gates.length)
    (hin : n + i ∈ (gateAt C r).inputs) (hand : (gateAt C r).op = GateOp.and)
    (hiop : (gateAt C i).op = GateOp.and)
    (hneg : ∀ x, Neg x → V C.gates x (n + i) = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ Good Pos Neg D ∧ D.size = C.size ∧
      andPairs n D < andPairs n C := by
  have ht : n + i < n + r := hb r hr _ hin
  have hval : ∀ x : List Bool, x.length = n → V C.gates x (n + i) = false →
      V C.gates x (n + r) = V C.gates x (n + i) := by
    intro x hx hc
    rw [gval n C hb x hx r hr, hc]
    exact valB _ hand _ _ hin _ hc
  obtain ⟨h1, h2, h3, h4⟩ := delApp n i r (n + i) Pos Neg hP hN C hm hb hg hout (by omega) hr ht
    hneg hval
  refine ⟨_, h1, h2, h3, h4, ?_⟩
  have hic : InCone n C i r := by
    have := cone_direct n C r (n + i) hr hin (by omega) ht
    simpa using this
  apply pairs_lt n r (n + i) _ i C hr ht hin i r (by omega) hr hiop hand hic
  rintro a b _ ⟨_, hb'⟩
  unfold psi at hb'; split_ifs at hb' <;> omega

theorem caseC2 (n i r y j : ℕ) (Pos Neg : List Bool → Prop) (hP : ∀ x, Pos x → x.length = n)
    (hN : ∀ x, Neg x → x.length = n) (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack n C)
    (hg : Good Pos Neg C) (hout : C.output < n + C.gates.length) (hr : r < C.gates.length)
    (hin : n + i ∈ (gateAt C r).inputs) (hor : (gateAt C r).op = GateOp.or)
    (hy : y ∈ (gateAt C r).inputs) (hyi : y ≠ n + i)
    (hall : ∀ u ∈ (gateAt C r).inputs, u = n + i ∨ u = y)
    (huniq : ∀ c, c < C.gates.length → n + i ∈ (gateAt C c).inputs → c = r)
    (hiop : (gateAt C i).op = GateOp.and) (hjop : (gateAt C j).op = GateOp.and)
    (hc : InCone n C i j)
    (hneg : ∀ x, Neg x → V C.gates x (n + i) = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ Good Pos Neg D ∧ D.size = C.size ∧
      andPairs n D < andPairs n C := by
  have hir : n + i < n + r := hb r hr _ hin
  have ht : y < n + r := hb r hr y hy
  have hval : ∀ x : List Bool, x.length = n → V C.gates x (n + i) = false →
      V C.gates x (n + r) = V C.gates x y := by
    intro x hx hc
    rw [gval n C hb x hx r hr]
    exact valC _ hor _ _ _ hall hy _ hc
  obtain ⟨h1, h2, h3, h4⟩ := delApp n i r y Pos Neg hP hN C hm hb hg hout (by omega) hr ht
    hneg hval
  refine ⟨_, h1, h2, h3, h4, ?_⟩
  have hj := cone_lt_len n C i j hc
  have hij := cone_lt n C j i hc
  apply pairs_lt n r y _ i C hr ht hy i j (by omega) hj hiop hjop hc
  rintro a b hab ⟨ha, _⟩
  have ha' : a = i := by unfold psi at ha; split_ifs at ha <;> omega
  rw [ha'] at hab
  obtain ⟨c, hcl, hcin⟩ := cone_reader n _ b i hab
  rw [del_len n r y C hr] at hcl
  by_cases hcr : c < r
  · rw [gateAt_del_lt n r y C hr c hcr] at hcin
    have := huniq c (by omega) hcin
    omega
  · rw [gateAt_del_ge n r y C hr c (by omega)] at hcin
    simp only [alG, List.mem_map] at hcin
    obtain ⟨u, hu, hue⟩ := hcin
    unfold al sd at hue
    split_ifs at hue with h1 h2
    · exact hyi hue
    · omega
    · have := huniq (c + 1) (by omega) (by rw [← hue]; exact hu)
      omega

theorem caseC1 (n i r1 r2 y1 y2 : ℕ) (Pos Neg : List Bool → Prop)
    (hP : ∀ x, Pos x → x.length = n) (hN : ∀ x, Neg x → x.length = n) (C : Circuit)
    (hm : Monotone2 C) (hb : ReadsBack n C) (hg : Good Pos Neg C)
    (hout : C.output < n + C.gates.length) (h12 : r1 < r2) (hr2 : r2 < C.gates.length)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hor1 : (gateAt C r1).op = GateOp.or)
    (hy1 : y1 ∈ (gateAt C r1).inputs) (hall1 : ∀ u ∈ (gateAt C r1).inputs, u = n + i ∨ u = y1)
    (hor2 : (gateAt C r2).op = GateOp.or)
    (hy2 : y2 ∈ (gateAt C r2).inputs) (hall2 : ∀ u ∈ (gateAt C r2).inputs, u = n + i ∨ u = y2)
    (hneg : ∀ x, Neg x → V C.gates x (n + i) = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ Good Pos Neg D ∧ D.size < C.size := by
  have hr1 : r1 < C.gates.length := by omega
  have hi1 : n + i < n + r1 := hb r1 hr1 _ hin1
  have ht1 : y1 < n + r1 := hb r1 hr1 _ hy1
  have ht2 : y2 < n + r2 := hb r2 hr2 _ hy2
  have hl1 : (del n r2 y2 C).gates.length = C.gates.length - 1 := del_len n r2 y2 C hr2
  have hm1 := del_mono n r2 y2 C hm
  have hb1 := del_rb n r2 y2 C hb hr2 ht2
  have hr1' : r1 < (del n r2 y2 C).gates.length := by omega
  have hl2 : (del n r1 y1 (del n r2 y2 C)).gates.length = (del n r2 y2 C).gates.length - 1 :=
    del_len n r1 y1 _ hr1'
  have hout1 := del_out n r2 y2 C hr2 ht2 hout
  have hout2 := del_out n r1 y1 _ hr1' ht1 hout1
  refine ⟨app n (del n r1 y1 (del n r2 y2 C)).output i (del n r1 y1 (del n r2 y2 C)),
    app_mono _ _ _ _ (del_mono n r1 y1 _ hm1),
    app_rb _ _ _ _ (del_rb n r1 y1 _ hb1 hr1' ht1) hout2 (by omega),
    good_app n i Pos Neg hP hN C _ hg hneg ?_ ?_, ?_⟩
  · intro x hx
    rw [V_del_lt n r1 y1 _ hr1' x hx _ hi1, V_del_lt n r2 y2 C hr2 x hx _ (by omega)]
  · intro x hx hc
    have hv1 : V (del n r2 y2 C).gates x (n + r1) = V (del n r2 y2 C).gates x y1 := by
      rw [V_del_lt n r2 y2 C hr2 x hx _ (by omega), V_del_lt n r2 y2 C hr2 x hx _ (by omega),
        gval n C hb x hx r1 hr1]
      exact valC _ hor1 _ _ _ hall1 hy1 _ hc
    have hv2 : V C.gates x (n + r2) = V C.gates x y2 := by
      rw [gval n C hb x hx r2 hr2]
      exact valC _ hor2 _ _ _ hall2 hy2 _ hc
    rw [del_eval n r1 y1 _ hb1 hr1' ht1 x hx hv1, del_eval n r2 y2 C hb hr2 ht2 x hx hv2]
  · show (app n (del n r1 y1 (del n r2 y2 C)).output i
      (del n r1 y1 (del n r2 y2 C))).gates.length < C.gates.length
    rw [app_len]; omega

theorem core (n : ℕ) (Pos Neg : List Bool → Prop) (hP : ∀ x, Pos x → x.length = n)
    (hN : ∀ x, Neg x → x.length = n) (hPne : ∃ x, Pos x)
    (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack n C) (hg : Good Pos Neg C) (i j : ℕ)
    (hiop : (gateAt C i).op = GateOp.and) (hjop : (gateAt C j).op = GateOp.and)
    (hc : InCone n C i j) (hneg : ∀ x, Neg x → V C.gates x (n + i) = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ Good Pos Neg D ∧
      (D.size < C.size ∨ D.size = C.size ∧ andPairs n D < andPairs n C) := by
  have hout : C.output < n + C.gates.length := by
    obtain ⟨x0, hx0⟩ := hPne
    by_contra h
    have h1 := hg.1 x0 hx0
    rw [eval_V, V_out _ _ _ (by rw [hP x0 hx0]; omega)] at h1
    exact Bool.false_ne_true h1
  obtain ⟨c, hcl, hcin⟩ := cone_reader n C j i hc
  by_cases hA : ∃ r, r < C.gates.length ∧ n + i ∈ (gateAt C r).inputs ∧
      ∀ u ∈ (gateAt C r).inputs, u = n + i
  · obtain ⟨r, hr, hin, hall⟩ := hA
    obtain ⟨D, h1, h2, h3, h4⟩ := caseA n i r Pos Neg hP hN C hm hb hg hr hin hall
    exact ⟨D, h1, h2, h3, Or.inl h4⟩
  by_cases hB : ∃ r, r < C.gates.length ∧ n + i ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.and
  · obtain ⟨r, hr, hin, hand⟩ := hB
    obtain ⟨D, h1, h2, h3, h4, h5⟩ :=
      caseB n i r Pos Neg hP hN C hm hb hg hout hr hin hand hiop hneg
    exact ⟨D, h1, h2, h3, Or.inr ⟨h4, h5⟩⟩
  have hrd : ∀ r, r < C.gates.length → n + i ∈ (gateAt C r).inputs →
      (gateAt C r).op = GateOp.or ∧ ∃ y, y ∈ (gateAt C r).inputs ∧ y ≠ n + i ∧
        ∀ u ∈ (gateAt C r).inputs, u = n + i ∨ u = y := by
    intro r hr hin
    have hmg := mono_gate C hm r hr
    have hor : (gateAt C r).op = GateOp.or := by
      rcases hmg.1 with h | h
      · exact (hB ⟨r, hr, hin, h⟩).elim
      · exact h
    have hex : ∃ y ∈ (gateAt C r).inputs, y ≠ n + i := by
      by_contra hno
      push Not at hno
      exact hA ⟨r, hr, hin, hno⟩
    obtain ⟨y, hy, hyi⟩ := hex
    exact ⟨hor, y, hy, hyi, two_elems _ hmg.2 _ _ hin hy (Ne.symm hyi)⟩
  by_cases hC1 : ∃ r1 r2, r1 < r2 ∧ r2 < C.gates.length ∧ n + i ∈ (gateAt C r1).inputs ∧
      n + i ∈ (gateAt C r2).inputs
  · obtain ⟨r1, r2, h12, hr2, hin1, hin2⟩ := hC1
    obtain ⟨hor1, y1, hy1, _, hall1⟩ := hrd r1 (by omega) hin1
    obtain ⟨hor2, y2, hy2, _, hall2⟩ := hrd r2 hr2 hin2
    obtain ⟨D, h1, h2, h3, h4⟩ := caseC1 n i r1 r2 y1 y2 Pos Neg hP hN C hm hb hg hout h12 hr2
      hin1 hor1 hy1 hall1 hor2 hy2 hall2 hneg
    exact ⟨D, h1, h2, h3, Or.inl h4⟩
  · have huniq : ∀ c', c' < C.gates.length → n + i ∈ (gateAt C c').inputs → c' = c := by
      intro c' hc' hin'
      rcases lt_trichotomy c' c with h | h | h
      · exact (hC1 ⟨c', c, h, hcl, hin', hcin⟩).elim
      · exact h
      · exact (hC1 ⟨c, c', h, hc', hcin, hin'⟩).elim
    obtain ⟨hor, y, hy, hyi, hall⟩ := hrd c hcl hcin
    obtain ⟨D, h1, h2, h3, h4, h5⟩ := caseC2 n i c y j Pos Neg hP hN C hm hb hg hout hcl hcin
      hor hy hyi hall huniq hiop hjop hc hneg
    exact ⟨D, h1, h2, h3, Or.inr ⟨h4, h5⟩⟩

end PEqualNP.Outside.L_meta_2061_aux

theorem PEqualNP.Outside.L_meta_2061 : have x1 : Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ)) => Decidable.decide (x1 = (0 : Fin (13 : ℕ)) ∨ x1 = (1 : Fin (13 : ℕ)) ∨ x1 = (3 : Fin (13 : ℕ)) ∨ x1 = (9 : Fin (13 : ℕ))); have x2 : Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ))) => x2.card = (4 : ℕ) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2 | x1 (x4 - x3) = Bool.true}.card ≤ (2 : ℕ); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x1 (x5 - x4) = Bool.false); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x5 - x6) = Bool.true → x4.eval ((List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x6)) = Bool.true) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x2 x5 → x4.eval (x3 x5) = Bool.false; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → x4 x5 → (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x5 x9 x10 ∧ ∀ (x11 : Finset (Fin (13 : ℕ))), x2 x11 → (x5.wires (x3 x11)).getD ((26 : ℕ) + x9) Bool.false = Bool.false) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x10 ∧ x4 x10 ∧ (x10.size < x5.size ∨ x10.size = x5.size ∧ PEqualNP.TopForm.andPairs (26 : ℕ) x10 < PEqualNP.TopForm.andPairs (26 : ℕ) x5) := by
  intro x1 x2 x3 x4 C hm hb hgood hex
  obtain ⟨i, j, hiop, hjop, hc, hq⟩ := hex
  have hlen3 : ∀ Q, (x3 Q).length = 26 := by intro Q; simp [x3]
  let Pos : List Bool → Prop := fun x => ∃ a b : Fin 13, x1 (a - b) = true ∧
      x = (List.ofFn fun x8 : Fin 13 => decide (x8 = a)) ++
        List.ofFn fun x8 : Fin 13 => decide (x8 = b)
  let Neg : List Bool → Prop := fun x => ∃ Q, x2 Q ∧ x = x3 Q
  have hP : ∀ x, Pos x → x.length = 26 := by
    rintro x ⟨a, b, _, rfl⟩
    simp
  have hN : ∀ x, Neg x → x.length = 26 := by
    rintro x ⟨Q, _, rfl⟩
    exact hlen3 Q
  have hPne : ∃ x, Pos x := ⟨_, 0, 0, by simp [x1], rfl⟩
  have hG : PEqualNP.Outside.L_meta_2061_aux.Good Pos Neg C := by
    refine ⟨?_, ?_⟩
    · rintro x ⟨a, b, h, rfl⟩
      exact hgood.1 a b h
    · rintro x ⟨Q, hQ, rfl⟩
      exact hgood.2 Q hQ
  have hneg : ∀ x, Neg x → PEqualNP.Outside.L_meta_2061_aux.V C.gates x (26 + i) = false := by
    rintro x ⟨Q, hQ, rfl⟩
    exact hq Q hQ
  obtain ⟨D, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_meta_2061_aux.core 26 Pos Neg hP hN hPne
    C hm hb hG i j hiop hjop hc hneg
  exact ⟨D, h1, h2, ⟨fun a b h => h3.1 _ ⟨a, b, h, rfl⟩, fun Q hQ => h3.2 _ ⟨Q, hQ, rfl⟩⟩, h4⟩
