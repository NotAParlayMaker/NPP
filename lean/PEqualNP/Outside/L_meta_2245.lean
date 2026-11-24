import Mathlib
import PEqualNP.Defs

-- Deleting a degenerate gate: a copy of a wire or a constant.

namespace PEqualNP.Outside.L_meta_2245_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
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

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
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

lemma wire_at (n : ℕ) (pre post : List Gate) (g : Gate) (X : List Bool) (hX : X.length = n) :
    (wiresFrom (pre ++ g :: post) X).getD (n + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false) := by
  have h1 : wiresFrom (pre ++ g :: post) X = wiresFrom post
      (wiresFrom pre X ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pre X).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have hl : (wiresFrom pre X).length = n + pre.length := by
    rw [length_wiresFrom]; omega
  rw [h1, getD_wiresFrom _ _ _ (by simp [hl]), getD_snoc_len _ _ _ _ hl]

-- The value of wire w.
def V (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (wiresFrom gs x).getD w false

lemma eval_eq (gs : List Gate) (out : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, out⟩ x = V gs x out := rfl

lemma V_prefix (pre post : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length + pre.length) :
    V (pre ++ post) x w = V pre x w := by
  unfold V
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rw [length_wiresFrom]; exact h)]

lemma gate_val_aux (gs : List Gate) (x : List Bool) (hx : x.length = 26) (i : ℕ) (g : Gate)
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

lemma V_out (gs : List Gate) (x : List Bool) (w : ℕ) (h : x.length + gs.length ≤ w) :
    V gs x w = false := by
  unfold V
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; exact h)

lemma V_in (gs gs' : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
    V gs x w = V gs' x w := by
  unfold V
  rw [getD_wiresFrom _ _ _ h, getD_wiresFrom _ _ _ h]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

-- Wire renaming after the deletion of gate j.
def sg (j : ℕ) (u : ℕ) : ℕ := if 26 + j < u then u - 1 else u

lemma sg_le (j u : ℕ) (h : u ≤ 26 + j) : sg j u = u := by
  have h' : ¬ 26 + j < u := by omega
  simp [sg, h']

lemma sg_gt (j u : ℕ) (h : 26 + j < u) : sg j u = u - 1 := by
  simp [sg, h]

def sh (j : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sg j)⟩

def del (f : Gate → Gate) (j : ℕ) (gs : List Gate) : List Gate :=
  ((gs.map f).eraseIdx j).map (sh j)

lemma del_get (f : Gate → Gate) (j : ℕ) (gs : List Gate) (i : ℕ) (g : Gate)
    (hg : gs[i]? = some g) (hij : i ≠ j) :
    ∃ i', sg j (26 + i) = 26 + i' ∧ (del f j gs)[i']? = some (sh j (f g)) ∧
      ((i' = i ∧ i < j) ∨ (i' + 1 = i ∧ j ≤ i')) := by
  by_cases h : i < j
  · refine ⟨i, sg_le j _ (by omega), ?_, Or.inl ⟨rfl, h⟩⟩
    simp [del, List.getElem?_eraseIdx, h, hg]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : ¬ k < j := by omega
    refine ⟨k, ?_, ?_, Or.inr ⟨rfl, by omega⟩⟩
    · rw [sg_gt j _ (by omega)]; omega
    · simp [del, List.getElem?_eraseIdx, hk, hg]

lemma del_inv (f : Gate → Gate) (j : ℕ) (gs : List Gate) (i' : ℕ) (g' : Gate)
    (h : (del f j gs)[i']? = some g') :
    ∃ i g, gs[i]? = some g ∧ g' = sh j (f g) ∧ ((i' = i ∧ i < j) ∨ (i' + 1 = i ∧ j ≤ i')) := by
  by_cases h3 : i' < j
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i', g, hg, rfl, Or.inl ⟨rfl, h3⟩⟩
  · simp [del, List.getElem?_eraseIdx, h3] at h
    obtain ⟨g, hg, rfl⟩ := h
    exact ⟨i' + 1, g, hg, rfl, Or.inr ⟨rfl, by omega⟩⟩

lemma del_back (f : Gate → Gate) (j : ℕ) (gs : List Gate)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < 26 + i ∧ u ≠ 26 + j)
    (i' : ℕ) (g' : Gate) (h : (del f j gs)[i']? = some g') :
    ∀ u ∈ g'.inputs, u < 26 + i' := by
  obtain ⟨i, g, hg, rfl, hi⟩ := del_inv f j gs i' g' h
  intro u hu
  simp only [sh, List.mem_map] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  have h1 := hfb i g hg v hv
  unfold sg
  split_ifs <;> omega

lemma del_val (f : Gate → Gate) (j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (x : List Bool) (hx : x.length = 26)
    (hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < 26 + i)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < 26 + i ∧ u ≠ 26 + j)
    (hfv : ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
      (f g).op.eval ((f g).inputs.map (V gs x)) = g.op.eval (g.inputs.map (V gs x))) :
    ∀ u, u ≠ 26 + j → V (del f j gs) x (sg j u) = V gs x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    have hlen : (del f j gs).length = gs.length - 1 := by
      simp [del, List.length_eraseIdx, hj]
    by_cases h1 : u < 26
    · rw [sg_le j u (by omega)]
      exact V_in _ _ x u (by omega)
    · obtain ⟨i, rfl⟩ : ∃ i, u = 26 + i := ⟨u - 26, by omega⟩
      have hij : i ≠ j := by omega
      by_cases h2 : i < gs.length
      · have hg : gs[i]? = some gs[i] := List.getElem?_eq_getElem h2
        obtain ⟨i', hs, hd, _⟩ := del_get f j gs i gs[i] hg hij
        rw [hs, gate_val_aux _ x hx i' _ hd (del_back f j gs hfb i' _ hd),
          gate_val_aux gs x hx i _ hg (hback i _ hg), ← hfv i _ hg]
        simp only [sh, List.map_map]
        congr 1
        apply List.map_congr_left
        intro w hw
        exact ih w (hfb i _ hg w hw).1 (hfb i _ hg w hw).2
      · rw [V_out gs x _ (by omega)]
        apply V_out
        rw [hlen]
        unfold sg
        split_ifs <;> omega

lemma core (gs : List Gate) (out : ℕ) (j : ℕ) (hj : j < gs.length) (f : Gate → Gate) (out' : ℕ)
    (hout : out' ≠ 26 + j)
    (hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < 26 + i)
    (hfm : ∀ g ∈ gs, (f g).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (f g).inputs.length ≤ 2)
    (hfb : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ (f g).inputs, u < 26 + i ∧ u ≠ 26 + j)
    (hfv : ∀ (x : List Bool), x.length = 26 → ∀ (i : ℕ) (g : Gate), gs[i]? = some g →
      (f g).op.eval ((f g).inputs.map (V gs x)) = g.op.eval (g.inputs.map (V gs x)))
    (hov : ∀ (x : List Bool), x.length = 26 → V gs x out' = V gs x out) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ D.size < gs.length ∧
      ∀ (x : List Bool), x.length = 26 → D.eval x = Circuit.eval ⟨gs, out⟩ x := by
  refine ⟨⟨del f j gs, sg j out'⟩, ?_, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨i', hi'⟩ := List.getElem?_of_mem hg'
    obtain ⟨i, g, hg, rfl, _⟩ := del_inv f j gs i' g' hi'
    have h := hfm g (List.mem_of_getElem? hg)
    exact ⟨h.1, by simpa [sh] using h.2⟩
  · intro i' hi' u hu
    rw [gateAt_eq _ i' hi'] at hu
    exact del_back f j gs hfb i' _ (List.getElem?_eq_getElem hi') u hu
  · show (del f j gs).length < gs.length
    simp [del, List.length_eraseIdx, hj]
    omega
  · intro x hx
    rw [eval_eq, eval_eq, del_val f j gs hj x hx hback hfb (hfv x hx) out' hout, hov x hx]

-- Case one: the gate copies wire w.
def f1 (j w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun u => if u = 26 + j then w else u)⟩

-- Case two: the gate gj is a constant.
def f2 (j : ℕ) (gj g : Gate) : Gate :=
  if g.op.eval [] = gj.op.eval [] then ⟨g.op, g.inputs.filter (fun u => decide (u ≠ 26 + j))⟩
  else if 26 + j ∈ g.inputs then gj else g

lemma all_filter (W : ℕ → Bool) (a : ℕ) (h : W a = true) (l : List ℕ) :
    ((l.filter (fun u => decide (u ≠ a))).map W).all id = (l.map W).all id := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro H b ⟨u, hu, rfl⟩
    by_cases hb : u = a
    · subst hb; simpa using h
    · exact H _ ⟨u, ⟨hu, hb⟩, rfl⟩
  · rintro H b ⟨u, ⟨hu, _⟩, rfl⟩
    exact H _ ⟨u, hu, rfl⟩

lemma any_filter (W : ℕ → Bool) (a : ℕ) (h : W a = false) (l : List ℕ) :
    ((l.filter (fun u => decide (u ≠ a))).map W).any id = (l.map W).any id := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨b, ⟨u, ⟨hu, _⟩, rfl⟩, hb⟩
    exact ⟨_, ⟨u, hu, rfl⟩, hb⟩
  · rintro ⟨b, ⟨u, hu, rfl⟩, hb⟩
    have hne : u ≠ a := by
      rintro rfl
      rw [h] at hb
      simp at hb
    exact ⟨_, ⟨u, ⟨hu, hne⟩, rfl⟩, hb⟩

lemma f2_val (j : ℕ) (gj g : Gate) (W : ℕ → Bool)
    (hgj : gj.op = GateOp.and ∨ gj.op = GateOp.or) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : gj.inputs = []) (hW : W (26 + j) = gj.op.eval []) :
    (f2 j gj g).op.eval ((f2 j gj g).inputs.map W) = g.op.eval (g.inputs.map W) := by
  rcases hgj with h1 | h1 <;> rcases hg with h2 | h2
  · have hc : W (26 + j) = true := by rw [hW, h1]; rfl
    have e : f2 j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ 26 + j))⟩ := by
      simp [f2, h1, h2, GateOp.eval]
    rw [e]
    simp only [h2, GateOp.eval]
    exact all_filter W _ hc _
  · have hc : W (26 + j) = true := by rw [hW, h1]; rfl
    by_cases hm : 26 + j ∈ g.inputs
    · have e : f2 j gj g = gj := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e, hin, h1, h2]
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      exact ⟨_, List.mem_map.mpr ⟨_, hm, rfl⟩, hc⟩
    · have e : f2 j gj g = g := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e]
  · have hc : W (26 + j) = false := by rw [hW, h1]; rfl
    by_cases hm : 26 + j ∈ g.inputs
    · have e : f2 j gj g = gj := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e, hin, h1, h2]
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [List.all_eq_false]
      exact ⟨_, List.mem_map.mpr ⟨_, hm, rfl⟩, by simp [hc]⟩
    · have e : f2 j gj g = g := by simp [f2, h1, h2, GateOp.eval, hm]
      rw [e]
  · have hc : W (26 + j) = false := by rw [hW, h1]; rfl
    have e : f2 j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ 26 + j))⟩ := by
      simp [f2, h1, h2, GateOp.eval]
    rw [e]
    simp only [h2, GateOp.eval]
    exact any_filter W _ hc _

lemma f2_cases (j : ℕ) (gj g : Gate) :
    f2 j gj g = ⟨g.op, g.inputs.filter (fun u => decide (u ≠ 26 + j))⟩ ∨
    f2 j gj g = gj ∨ (f2 j gj g = g ∧ 26 + j ∉ g.inputs) := by
  unfold f2
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨rfl, h2⟩)

lemma shape (gs : List Gate) (j : ℕ) (g : Gate) (hg : gs[j]? = some g)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (hb : ∀ u ∈ g.inputs, u < 26 + j)
    (hdeg : g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    g.inputs = [] ∨ ∃ w, w < 26 + j ∧
      ∀ (x : List Bool), x.length = 26 → V gs x (26 + j) = V gs x w := by
  rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exact Or.inl rfl
  · right
    refine ⟨a, hb a (by simp [hin]), fun x hx => ?_⟩
    rw [gate_val_aux gs x hx j g hg hb, hin]
    rcases hop with h | h <;> simp [h, GateOp.eval]
  · right
    rw [hin] at hdeg
    have hab : a = b := by simpa using hdeg
    subst hab
    refine ⟨a, hb a (by simp [hin]), fun x hx => ?_⟩
    rw [gate_val_aux gs x hx j g hg hb, hin]
    rcases hop with h | h <;> simp [h, GateOp.eval]
  · rw [hin] at hlen
    simp at hlen

lemma main (gs : List Gate) (out : ℕ) (hmon : Monotone2 ⟨gs, out⟩) (hrb : ReadsBack 26 ⟨gs, out⟩)
    (x1 x0 : List Bool) (h1 : x1.length = 26) (h0 : x0.length = 26)
    (ht : Circuit.eval ⟨gs, out⟩ x1 = true) (hf : Circuit.eval ⟨gs, out⟩ x0 = false)
    (hd : ∃ g ∈ gs, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ D.size < gs.length ∧
      ∀ (x : List Bool), x.length = 26 → D.eval x = Circuit.eval ⟨gs, out⟩ x := by
  have hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hmon g hg).1
  have hback : ∀ (i : ℕ) (g : Gate), gs[i]? = some g → ∀ u ∈ g.inputs, u < 26 + i := by
    intro i g hg u hu
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hg
    have := hrb i hi u
    rw [gateAt_eq _ i hi] at this
    exact this hu
  obtain ⟨gj, hmem, hdeg⟩ := hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
  have hgj : gs[j]? = some gs[j] := List.getElem?_eq_getElem hj
  rcases shape gs j gs[j] hgj (hops _ hmem) (hmon _ hmem).2 (hback j _ hgj) hdeg with hin | ⟨w, hw, hv⟩
  · -- a constant gate
    have hc : ∀ (x : List Bool), x.length = 26 → V gs x (26 + j) = gs[j].op.eval [] := by
      intro x hx
      rw [gate_val_aux gs x hx j _ hgj (hback j _ hgj), hin]
      rfl
    have hout : out ≠ 26 + j := by
      rintro rfl
      rw [eval_eq, hc x1 h1] at ht
      rw [eval_eq, hc x0 h0, ht] at hf
      exact Bool.noConfusion hf
    refine core gs out j hj (f2 j gs[j]) out hout hback ?_ ?_ ?_ (fun _ _ => rfl)
    · intro g hg
      rcases f2_cases j gs[j] g with e | e | ⟨e, _⟩
      · rw [e]
        exact ⟨(hmon g hg).1, le_trans (List.length_filter_le _ _) (hmon g hg).2⟩
      · rw [e]; exact hmon _ hmem
      · rw [e]; exact hmon g hg
    · intro i g hg u hu
      rcases f2_cases j gs[j] g with e | e | ⟨e, hn⟩
      · rw [e] at hu
        simp only [List.mem_filter, decide_eq_true_eq] at hu
        exact ⟨hback i g hg u hu.1, hu.2⟩
      · rw [e, hin] at hu
        simp at hu
      · rw [e] at hu
        refine ⟨hback i g hg u hu, ?_⟩
        rintro rfl
        exact hn hu
    · intro x hx i g hg
      exact f2_val j gs[j] g (V gs x) (hops _ hmem) (hops g (List.mem_of_getElem? hg)) hin (hc x hx)
  · -- a copy of wire w
    refine core gs out j hj (f1 j w) (if out = 26 + j then w else out) ?_ hback ?_ ?_ ?_ ?_
    · split_ifs with h
      · omega
      · exact h
    · intro g hg
      exact ⟨(hmon g hg).1, by simpa [f1] using (hmon g hg).2⟩
    · intro i g hg u hu
      simp only [f1, List.mem_map] at hu
      obtain ⟨v, hv', rfl⟩ := hu
      have := hback i g hg v hv'
      split_ifs with h
      · omega
      · exact ⟨this, h⟩
    · intro x hx i g hg
      simp only [f1, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u _
      simp only [Function.comp]
      split_ifs with h
      · rw [h, hv x hx]
      · rfl
    · intro x hx
      split_ifs with h
      · rw [h, hv x hx]
      · rfl

-- Wire-value comparison lemmas for replacing one gate by a copy of an input wire.

lemma gate_eval_mono :
    ∀ {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or) {ins : List ℕ} {V V' : ℕ → Bool},
      (∀ u ∈ ins, V u = true → V' u = true) →
      op.eval (ins.map V) = true → op.eval (ins.map V') = true := by
  intro op hop ins
  induction ins with
  | nil =>
      intro V V' h he
      rcases hop with rfl | rfl <;> simp [GateOp.eval] at he ⊢
  | cons a ins ih =>
      intro V V' h he
      rcases hop with rfl | rfl
      · simp only [GateOp.eval, List.map_cons, List.all_cons, Bool.and_eq_true] at he ⊢
        exact ⟨h a (by simp) he.1, ih (fun u hu => h u (by simp [hu])) he.2⟩
      · simp only [GateOp.eval, List.map_cons, List.any_cons, Bool.or_eq_true] at he ⊢
        rcases he with ha | hr
        · exact Or.inl (h a (by simp) ha)
        · exact Or.inr (ih (fun u hu => h u (by simp [hu])) hr)

lemma wires_imp_and (pre post : List Gate) (g : Gate) (x : List Bool) (hx : x.length = 26)
    (j i : ℕ) (hpre : pre.length = j) (hi : i ∈ g.inputs) (hopand : g.op = GateOp.and)
    (hmon : ∀ gg ∈ (pre ++ g :: post), gg.op = GateOp.and ∨ gg.op = GateOp.or)
    (hback : ∀ k < (pre ++ g :: post).length, ∀ u ∈ ((pre ++ g :: post).getD k dflt).inputs, u < 26 + k) :
    ∀ m, V (pre ++ g :: post) x m = true → V (pre ++ ⟨GateOp.or, [i]⟩ :: post) x m = true := by
  let old : List Gate := pre ++ g :: post
  let new : List Gate := pre ++ ⟨GateOp.or, [i]⟩ :: post
  have hlen : old.length = new.length := by simp [old, new]
  have hi_lt : i < 26 + j := by
    have hgj : old.getD j dflt = g := by simp [old, hpre]
    have := hback j (by simp [old]) i (by simpa [hgj] using hi)
    simpa [old, hpre] using this
  have hmonnew : ∀ gg ∈ new, gg.op = GateOp.and ∨ gg.op = GateOp.or := by
    intro gg hgg
    by_cases hg : gg = ⟨GateOp.or, [i]⟩
    · subst gg; exact Or.inr rfl
    · exact hmon gg (by simpa [old, new, hg] using hgg)
  have hbacknew : ∀ k < new.length, ∀ u ∈ (new.getD k dflt).inputs, u < 26 + k := by
    intro k hk u hu
    have hkold : k < old.length := by simpa [hlen] using hk
    by_cases hkj : k < j
    · have hg : new.getD k dflt = old.getD k dflt := by simp [old, new, List.getD_append, hkj, hpre]
      rw [hg] at hu
      exact hback k hkold u hu
    · by_cases hkeq : k = j
      · subst k
        have hg : new.getD j dflt = ⟨GateOp.or, [i]⟩ := by simp [new, hpre]
        rw [hg] at hu
        simp only at hu
        subst u
        exact hi_lt
      · have hg : new.getD k dflt = old.getD k dflt := by
          by_cases hklt : k < j <;> simp [old, new, List.getD_append, hpre, hkj, hkeq, hklt]
        rw [hg] at hu
        exact hback k hkold u hu
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hml : m < 26
    · have h1 : V old x m = V new x m := V_in old new x m hml
      simpa [h1] using hm
    · obtain ⟨k, rfl⟩ : ∃ k, m = 26 + k := ⟨m - 26, by omega⟩
      by_cases hkold : k < old.length
      · rw [gate_val_aux old x hx k _ (old.getD k dflt) (List.getElem?_eq_getElem hkold)
              (by intro u hu; exact hback k hkold u hu),
            gate_val_aux new x hx k _ (new.getD k dflt) (List.getElem?_eq_getElem (by simpa [hlen] using hkold))
              (by intro u hu; exact hbacknew k (by simpa [hlen] using hkold) u hu)]
        by_cases hkj : k < j
        · have hg : old.getD k dflt = new.getD k dflt := by simp [old, new, List.getD_append, hkj, hpre]
          rw [← hg]
          apply gate_eval_mono (hmon (old.getD k dflt) (by
            rw [List.getD_eq_getElem _ _ hkold]; exact List.getElem_mem _))
          intro u hu
          exact ih u (by have := hback k hkold u hu; omega)
        · by_cases hkeq : k = j
          · subst k
            have hold : old.getD j dflt = g := by simp [old, hpre]
            have hnew : new.getD j dflt = ⟨GateOp.or, [i]⟩ := by simp [new, hpre]
            rw [hold, hnew, hopand]
            simp only [GateOp.eval, List.all_eq_true] at hm
            have hvi : V old x i = true :=
              (List.all_eq_true.mp (by simpa [GateOp.eval] using hm)) (V old x i)
                (List.mem_map.mpr ⟨i, hi, rfl⟩)
            have hvi' : V new x i = true := ih i (by have := hback j (by simp [old]) i (by simpa [old] using hi); omega)
            simpa [GateOp.eval] using hvi'
          · have hg : old.getD k dflt = new.getD k dflt := by
              by_cases hklt : k < j <;> simp [old, new, List.getD_append, hpre, hkj, hkeq, hklt]
            rw [← hg]
            apply gate_eval_mono (hmon (old.getD k dflt) (by
              rw [List.getD_eq_getElem _ _ hkold]; exact List.getElem_mem _))
            intro u hu
            exact ih u (by have := hback k hkold u hu; omega)
      · have hz : V old x (26 + k) = false := by
          apply V_out
          simp [old]
          omega
        simp [hz] at hm

lemma wires_imp_or (pre post : List Gate) (g : Gate) (x : List Bool) (hx : x.length = 26)
    (j i : ℕ) (hpre : pre.length = j) (hi : i ∈ g.inputs) (hopor : g.op = GateOp.or)
    (hmon : ∀ gg ∈ (pre ++ g :: post), gg.op = GateOp.and ∨ gg.op = GateOp.or)
    (hback : ∀ k < (pre ++ g :: post).length, ∀ u ∈ ((pre ++ g :: post).getD k dflt).inputs, u < 26 + k) :
    ∀ m, V (pre ++ ⟨GateOp.or, [i]⟩ :: post) x m = true → V (pre ++ g :: post) x m = true := by
  let old : List Gate := pre ++ ⟨GateOp.or, [i]⟩ :: post
  let new : List Gate := pre ++ g :: post
  have hlen : old.length = new.length := by simp [old, new]
  have hi_lt : i < 26 + j := by
    have hgj : new.getD j dflt = g := by simp [new, hpre]
    have := hback j (by simp [new]) i (by simpa [hgj] using hi)
    simpa [new, hpre] using this
  have hmonold : ∀ gg ∈ old, gg.op = GateOp.and ∨ gg.op = GateOp.or := by
    intro gg hgg
    by_cases hg : gg = ⟨GateOp.or, [i]⟩
    · subst gg; exact Or.inr rfl
    · exact hmon gg (by simpa [old, new, hg] using hgg)
  have hbackold : ∀ k < old.length, ∀ u ∈ (old.getD k dflt).inputs, u < 26 + k := by
    intro k hk u hu
    have hknew : k < new.length := by simpa [hlen] using hk
    by_cases hkj : k < j
    · have hg : old.getD k dflt = new.getD k dflt := by simp [old, new, List.getD_append, hkj, hpre]
      rw [hg] at hu
      exact hback k hknew u hu
    · by_cases hkeq : k = j
      · subst k
        have hg : old.getD j dflt = ⟨GateOp.or, [i]⟩ := by simp [old, hpre]
        rw [hg] at hu
        simp only at hu
        subst u
        exact hi_lt
      · have hg : old.getD k dflt = new.getD k dflt := by
          by_cases hklt : k < j <;> simp [old, new, List.getD_append, hpre, hkj, hkeq, hklt]
        rw [hg] at hu
        exact hback k hknew u hu
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hml : m < 26
    · have h1 : V old x m = V new x m := V_in old new x m hml
      simpa [← h1] using hm
    · obtain ⟨k, rfl⟩ : ∃ k, m = 26 + k := ⟨m - 26, by omega⟩
      by_cases hkold : k < old.length
      · rw [gate_val_aux old x hx k _ (old.getD k dflt) (List.getElem?_eq_getElem hkold)
              (by intro u hu; exact hbackold k hkold u hu),
            gate_val_aux new x hx k _ (new.getD k dflt) (List.getElem?_eq_getElem (by simpa [hlen] using hkold))
              (by intro u hu; exact hback k (by simpa [hlen] using hkold) u hu)]
        by_cases hkj : k < j
        · have hg : old.getD k dflt = new.getD k dflt := by simp [old, new, List.getD_append, hkj, hpre]
          rw [hg]
          apply gate_eval_mono (hmon (new.getD k dflt) (by
            rw [List.getD_eq_getElem _ _ (by simpa [hlen] using hkold)]; exact List.getElem_mem _))
          intro u hu
          exact ih u (by have := hbackold k hkold u hu; omega)
        · by_cases hkeq : k = j
          · subst k
            have hold : old.getD j dflt = ⟨GateOp.or, [i]⟩ := by simp [old, hpre]
            have hnew : new.getD j dflt = g := by simp [new, hpre]
            rw [hold, hnew]
            simp [GateOp.eval] at hm
            have hvi' : V new x i = true := ih i (by have := hbackold j (by simp [old]) i (by simp [old]); omega)
            rw [hopor]
            have himem : V new x i ∈ g.inputs.map (V new x) := List.mem_map.mpr ⟨i, hi, rfl⟩
            simpa [GateOp.eval, List.any_eq_true] using
              (show ∃ b, b ∈ g.inputs.map (V new x) ∧ b = true from ⟨V new x i, himem, hvi'⟩)
          · have hg : old.getD k dflt = new.getD k dflt := by
              by_cases hklt : k < j <;> simp [old, new, List.getD_append, hpre, hkj, hkeq, hklt]
            rw [hg]
            apply gate_eval_mono (hmon (new.getD k dflt) (by
              rw [List.getD_eq_getElem _ _ (by simpa [hlen] using hkold)]; exact List.getElem_mem _))
            intro u hu
            exact ih u (by have := hbackold k hkold u hu; omega)
      · have hz : V old x (26 + k) = false := by
          apply V_out
          simp [old]
          omega
        simp [hz] at hm

lemma wires_eq (pre post : List Gate) (g : Gate) (x : List Bool) (hx : x.length = 26)
    (j i : ℕ) (hpre : pre.length = j) (hi : i ∈ g.inputs)
    (hback : ∀ k < (pre ++ g :: post).length, ∀ u ∈ ((pre ++ g :: post).getD k dflt).inputs, u < 26 + k)
    (hback' : ∀ k < (pre ++ ⟨GateOp.or, [i]⟩ :: post).length,
       ∀ u ∈ ((pre ++ ⟨GateOp.or, [i]⟩ :: post).getD k dflt).inputs, u < 26 + k)
    (heqj : V (pre ++ g :: post) x (26 + j) = V (pre ++ ⟨GateOp.or, [i]⟩ :: post) x (26 + j)) :
    ∀ m, V (pre ++ g :: post) x m = V (pre ++ ⟨GateOp.or, [i]⟩ :: post) x m := by
  let old : List Gate := pre ++ g :: post
  let new : List Gate := pre ++ ⟨GateOp.or, [i]⟩ :: post
  have hlen : old.length = new.length := by simp [old, new]
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hml : m < 26
    · exact V_in old new x m hml
    · obtain ⟨k, rfl⟩ : ∃ k, m = 26 + k := ⟨m - 26, by omega⟩
      by_cases hkold : k < old.length
      · rw [gate_val_aux old x hx k _ (old.getD k dflt) (List.getElem?_eq_getElem hkold)
              (by intro u hu; exact hback k hkold u hu),
            gate_val_aux new x hx k _ (new.getD k dflt) (List.getElem?_eq_getElem (by simpa [hlen] using hkold))
              (by intro u hu; exact hback' k (by simpa [hlen] using hkold) u hu)]
        by_cases hkj : k = j
        · subst k
          have hknew : j < new.length := by simpa [hlen] using hkold
          have he := heqj
          rw [gate_val_aux old x hx j _ (old.getD j dflt) (List.getElem?_eq_getElem hkold)
                (by intro u hu; exact hback j hkold u hu),
              gate_val_aux new x hx j _ (new.getD j dflt) (List.getElem?_eq_getElem hknew)
                (by intro u hu; exact hback' j hknew u hu)] at he
          exact he
        · have hg : old.getD k dflt = new.getD k dflt := by
            by_cases hklt : k < j <;> simp [old, new, List.getD_append, hpre, hkj, hklt]
          rw [hg]
          congr 1
          apply List.map_congr_left
          intro u hu
          exact ih u (by have := hback k hkold u hu; omega)
      · rw [V_out old x (26 + k) (by simp [old]; omega),
            V_out new x (26 + k) (by simp [new]; omega)]

end PEqualNP.Outside.L_meta_2245_aux

open PEqualNP.Outside.L_meta_2245_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.L_meta_2245 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 ∧ x5.size < x4.size; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ x6 < x5.gates.length,     have x8 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6;     have x9 : Bool := !x8.op.eval [];     ∀ x10 ∈ x8.inputs, ∃ (x12 : List Bool), x2 x9 x12 ∧ (x5.wires x12).getD x10 Bool.false = !x9 ∧ (x5.wires x12).getD ((26 : ℕ) + x6) Bool.false = x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x4 x6 ∨ x5 x6 := by
  intro x1 x2 x3 x4 x5 C hC
  rcases hC with ⟨hmon, hrb, hcorr⟩
  classical
  by_cases h5 : x5 C
  · exact Or.inr h5
  · left
    dsimp [x5] at h5
    have hex : ∃ j < C.gates.length, ∃ i ∈ (gateAt C j).inputs,
        ∀ l, x2 (! (gateAt C j).op.eval []) l →
          ¬ ((C.wires l).getD i false = !(! (gateAt C j).op.eval [])) ∧
            (C.wires l).getD (26 + j) false = (! (gateAt C j).op.eval [])) := by
      by_contra hn
      apply h5
      intro j hj
      dsimp only
      intro i hi
      by_contra hni
      apply hn
      refine ⟨j, hj, i, hi, ?_⟩
      intro l hl hw
      apply hni
      refine ⟨l, by simpa using hl, hw.1, hw.2⟩
    obtain ⟨j, hj, i, hi, hno⟩ := hex
    let g : Gate := gateAt C j
    let b : Bool := !g.op.eval []
    have hgC : C.gates[j]? = some g := by
      simp [g, gateAt_eq C j hj]
    have hi_g : i ∈ g.inputs := by simpa [g] using hi
    have hback : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < 26 + k := by
      intro k hk u hu
      simpa [gateAt_eq C k hk] using hrb k hk u hu
    have hi_lt : i < 26 + j := hback j hj i (by simpa [g, gateAt_eq C j hj] using hi)
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      have hm := hmon g (by
        rw [← hgC]
        exact List.getElem_mem _)
      simpa using hm.1
    have len_of_x2 : ∀ (bb : Bool) (l : List Bool), x2 bb l → l.length = 26 := by
      intro bb l hx
      dsimp [x2] at hx
      split_ifs at hx
      · obtain ⟨a, c, hac, rfl⟩ := hx
        simp
      · obtain ⟨S, hcard, hbound, rfl⟩ := hx
        simp
    rcases hop with hopand | hopor
    · have hb_false : b = false := by simp [b, hopand, GateOp.eval]
      have hno' : ∀ l, x2 false l →
          (C.wires l).getD i false = false ∨ (C.wires l).getD (26 + j) false = true := by
        intro l hl
        have hh := hno l (by simpa [b, hb_false] using hl)
        by_cases hi0 : (C.wires l).getD i false = false
        · exact Or.inl hi0
        · right
          by_contra hw0
          have hi1 : (C.wires l).getD i false = true := by
            cases (C.wires l).getD i false <;> simp_all
          have hwf : (C.wires l).getD (26 + j) false = false := by
            cases (C.wires l).getD (26 + j) false <;> simp_all
          exact hh (by simpa [b, hb_false] using And.intro hi1 hwf)
      have heq : ∀ l, l.length = 26 → x2 false l → V C.gates l (26 + j) = V C.gates l i := by
        intro l hl hlneg
        have hcase := hno' l hlneg
        have hle : V C.gates l (26 + j) = true → V C.gates l i = true := by
          intro hw
          rw [gate_val_aux C.gates l hl j g hgC
            (by intro u hu; exact hback j hj u (by simpa [g] using hu))] at hw
          have hall : ∀ a ∈ g.inputs.map (V C.gates l), a = true := by
            simpa [GateOp.eval, hopand, List.all_eq_true] using hw
          exact hall (V C.gates l i) (List.mem_map.mpr ⟨i, hi_g, rfl⟩)
        have hle' : (C.wires l).getD (26 + j) false = true →
            (C.wires l).getD i false = true := by
          simpa [V, Circuit.wires, wiresFrom] using hle
        rcases hcase with hi0 | hw1
        · have hw0 : (C.wires l).getD (26 + j) false = false := by
            by_contra hwc
            have hwtrue : (C.wires l).getD (26 + j) false = true := by
              cases h : (C.wires l).getD (26 + j) false <;> simp_all
            have : (C.wires l).getD i false = true := hle' hwtrue
            simp_all
          simp [V, Circuit.wires, wiresFrom, hi0, hw0]
        · have hi1 : (C.wires l).getD i false = true := hle' hw1
          simp [V, Circuit.wires, wiresFrom, hi1, hw1]
      obtain ⟨pre, post, hsplit, hprelen⟩ := split_at C.gates j g hgC
      let gs' : List Gate := pre ++ ⟨GateOp.or, [i]⟩ :: post
      let Cstar : Circuit := ⟨gs', C.output⟩
      have hmono_all : ∀ gg ∈ C.gates, gg.op = GateOp.and ∨ gg.op = GateOp.or := by
        intro gg hgg
        simpa using (hmon gg hgg).1
      have hmon_star : Monotone2 Cstar := by
        intro gg hgg
        by_cases hgnew : gg = ⟨GateOp.or, [i]⟩
        · subst gg
          exact ⟨Or.inr rfl, by simp⟩
        · have hggold : gg ∈ C.gates := by
            simpa [Cstar, gs', hsplit, hgnew] using hgg
          exact hmon gg hggold
      have hrb_star : ReadsBack 26 Cstar := by
        intro k hk u hu
        have hkold : k < C.gates.length := by simpa [Cstar, gs', hsplit] using hk
        by_cases hkeq : k = j
        · subst k
          have hgk : gs'.getD j dflt = ⟨GateOp.or, [i]⟩ := by simp [gs', List.getD_append, hprelen]
          change u ∈ (gs'.getD j dflt).inputs at hu
          rw [hgk] at hu
          simp only at hu
          subst u
          exact hi_lt
        · have hgk : gs'.getD k dflt = C.gates.getD k dflt := by
            rw [hsplit]
            by_cases hklt : k < j <;> simp [gs', List.getD_append, hprelen, hkeq, hklt]
          change u ∈ (gs'.getD k dflt).inputs at hu
          rw [hgk] at hu
          exact hrb k hkold u (by simpa [gateAt_eq C k hkold] using hu)
      have hback_star : ∀ k < gs'.length, ∀ u ∈ (gs'.getD k dflt).inputs, u < 26 + k := by
        intro k hk u hu
        exact hrb_star k hk u hu
      have hcorr_star : ∀ bb l, x2 bb l → Cstar.eval l = bb := by
        intro bb l hx2l
        have hlen := len_of_x2 bb l hx2l
        by_cases hbtrue : bb = true
        · subst bb
          have hCl : C.eval l = true := hcorr true l hx2l
          have hcmp := wires_imp_and pre post g l hlen j i hprelen hi_g hopand
            (by simpa [hsplit] using hmono_all) (by simpa [hsplit] using hback)
          have hv : V gs' l C.output = true := by
            apply hcmp C.output
            simpa [hsplit, V, Circuit.wires, wiresFrom] using hCl
          simpa [Cstar, Circuit.eval, V, Circuit.wires, wiresFrom] using hv
        · have hbfalse : bb = false := by cases bb <;> simp_all
          subst bb
          have hCl : C.eval l = false := hcorr false l hx2l
          have heqj : V (pre ++ g :: post) l (26 + j) = V gs' l (26 + j) := by
            have h1 : V (pre ++ g :: post) l (26 + j) = V C.gates l i := by
              simpa [hsplit] using heq l hlen hx2l
            have h2 : V gs' l (26 + j) = V C.gates l i := by
              have hgj : gs'.getD j dflt = ⟨GateOp.or, [i]⟩ := by simp [gs', List.getD_append, hprelen]
              rw [gate_val_aux gs' l hlen j _ ⟨GateOp.or, [i]⟩ hgj
                (by intro u hu; simp at hu; subst u; omega)]
              simp [GateOp.eval]
            rw [h1, h2]
          have heqw := wires_eq pre post g l hlen j i hprelen hi_g
            (by simpa [hsplit] using hback) (by simpa [gs'] using hback_star) heqj
          have hv : V gs' l C.output = false := by
            rw [← heqw C.output]
            simpa [V, Circuit.wires, wiresFrom, hsplit] using hCl
          simpa [Cstar, Circuit.eval, V, Circuit.wires, wiresFrom] using hv
      let out' : ℕ := if C.output = 26 + j then i else C.output
      have hout_ne : out' ≠ 26 + j := by
        dsimp [out']
        split_ifs with h
        · omega
        · exact h
      have hwi : ∀ x : List Bool, x.length = 26 → V gs' x (26 + j) = V gs' x i := by
        intro x hx
        have hgj : gs'.getD j dflt = ⟨GateOp.or, [i]⟩ := by simp [gs', List.getD_append, hprelen]
        rw [gate_val_aux gs' x hx j _ ⟨GateOp.or, [i]⟩ hgj
          (by intro u hu; simp at hu; subst u; omega)]
        simp [GateOp.eval]
      have hfv : ∀ (x : List Bool), x.length = 26 → ∀ (k : ℕ) (gg : Gate), gs'[k]? = some gg →
          (f1 j i gg).op.eval ((f1 j i gg).inputs.map (V gs' x)) = gg.op.eval (gg.inputs.map (V gs' x)) := by
        intro x hx k gg hk
        simp only [f1, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        by_cases huj : u = 26 + j
        · subst u
          exact (hwi x hx).symm
        · simp [huj]
      have hfm : ∀ gg ∈ gs', (f1 j i gg).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
          (f1 j i gg).inputs.length ≤ 2 := by
        intro gg hgg
        have hh := hmon_star gg (by simpa [Cstar] using hgg)
        exact ⟨by simpa [f1] using hh.1, by simpa [f1] using hh.2⟩
      have hfb : ∀ (k : ℕ) (gg : Gate), gs'[k]? = some gg →
          ∀ u ∈ (f1 j i gg).inputs, u < 26 + k ∧ u ≠ 26 + j := by
        intro k gg hk u hu
        simp only [f1, List.mem_map] at hu
        obtain ⟨v, hv, rfl⟩ := hu
        have hklt : k < gs'.length := (List.getElem?_eq_some_iff.mp hk).1
        have hvlt := hback_star k hklt v hv
        by_cases hvj : v = 26 + j
        · subst v
          constructor <;> omega
        · exact ⟨hvlt, hvj⟩
      have hov : ∀ (x : List Bool), x.length = 26 → V gs' x out' = V gs' x C.output := by
        intro x hx
        dsimp [out']
        split_ifs with h
        · exact hwi x hx
        · rfl
      obtain ⟨D, hDmon, hDrb, hDlt, hDeval⟩ :=
        core gs' C.output j (by simp [gs', List.getD_append, hprelen]) (f1 j i) out' hout_ne
          hback_star hfm hfb hfv hov
      refine ⟨D, ?_, ?_⟩
      · refine ⟨hDmon, hDrb, ?_⟩
        intro bb l hx2l
        have hlen := len_of_x2 bb l hx2l
        change Circuit.eval ⟨gs', C.output⟩ l = bb
        rw [hDeval l hlen]
        exact hcorr_star bb l hx2l
      · simpa [gs', hsplit] using hDlt
    · have hb_true : b = true := by simp [b, hopor, GateOp.eval]
      have hno' : ∀ l, x2 true l →
          (C.wires l).getD i false = true ∨ (C.wires l).getD (26 + j) false = false := by
        intro l hl
        have hh := hno l (by simpa [b, hb_true] using hl)
        by_cases hi1 : (C.wires l).getD i false = true
        · exact Or.inl hi1
        · right
          by_contra hw1
          have hi0 : (C.wires l).getD i false = false := by
            cases (C.wires l).getD i false <;> simp_all
          have hwt : (C.wires l).getD (26 + j) false = true := by
            cases (C.wires l).getD (26 + j) false <;> simp_all
          exact hh (by simpa [b, hb_true] using And.intro hi0 hwt)
      have heq : ∀ l, l.length = 26 → x2 true l → V C.gates l (26 + j) = V C.gates l i := by
        intro l hl hlpos
        have hcase := hno' l hlpos
        have hle : V C.gates l i = true → V C.gates l (26 + j) = true := by
          intro hiv
          rw [gate_val_aux C.gates l hl j g hgC
            (by intro u hu; exact hback j hj u (by simpa [g] using hu))]
          rw [hopor]
          have himem : V C.gates l i ∈ g.inputs.map (V C.gates l) := List.mem_map.mpr ⟨i, hi_g, rfl⟩
          simpa [GateOp.eval, List.any_eq_true] using
            (show ∃ z, z ∈ g.inputs.map (V C.gates l) ∧ z = true from ⟨V C.gates l i, himem, hiv⟩)
        have hle' : (C.wires l).getD i false = true →
            (C.wires l).getD (26 + j) false = true := by
          simpa [V, Circuit.wires, wiresFrom] using hle
        rcases hcase with hi1 | hw0
        · have hw1 : (C.wires l).getD (26 + j) false = true := hle' hi1
          simp [V, Circuit.wires, wiresFrom, hi1, hw1]
        · have hi0 : (C.wires l).getD i false = false := by
            by_contra hic
            have hitrue : (C.wires l).getD i false = true := by
              cases (C.wires l).getD i false <;> simp_all
            have := hle' hitrue
            simp_all
          simp [V, Circuit.wires, wiresFrom, hi0, hw0]
      obtain ⟨pre, post, hsplit, hprelen⟩ := split_at C.gates j g hgC
      let gs' : List Gate := pre ++ ⟨GateOp.or, [i]⟩ :: post
      let Cstar : Circuit := ⟨gs', C.output⟩
      have hmono_all : ∀ gg ∈ C.gates, gg.op = GateOp.and ∨ gg.op = GateOp.or := by
        intro gg hgg
        simpa using (hmon gg hgg).1
      have hmon_star : Monotone2 Cstar := by
        intro gg hgg
        by_cases hgnew : gg = ⟨GateOp.or, [i]⟩
        · subst gg
          exact ⟨Or.inr rfl, by simp⟩
        · have hggold : gg ∈ C.gates := by
            simpa [Cstar, gs', hsplit, hgnew] using hgg
          exact hmon gg hggold
      have hrb_star : ReadsBack 26 Cstar := by
        intro k hk u hu
        have hkold : k < C.gates.length := by simpa [Cstar, gs', hsplit] using hk
        by_cases hkeq : k = j
        · subst k
          have hgk : gs'.getD j dflt = ⟨GateOp.or, [i]⟩ := by simp [gs', List.getD_append, hprelen]
          change u ∈ (gs'.getD j dflt).inputs at hu
          rw [hgk] at hu
          simp only at hu
          subst u
          exact hi_lt
        · have hgk : gs'.getD k dflt = C.gates.getD k dflt := by
            rw [hsplit]
            by_cases hklt : k < j <;> simp [gs', List.getD_append, hprelen, hkeq, hklt]
          change u ∈ (gs'.getD k dflt).inputs at hu
          rw [hgk] at hu
          exact hrb k hkold u (by simpa [gateAt_eq C k hkold] using hu)
      have hback_star : ∀ k < gs'.length, ∀ u ∈ (gs'.getD k dflt).inputs, u < 26 + k := by
        intro k hk u hu
        exact hrb_star k hk u hu
      have hcorr_star : ∀ bb l, x2 bb l → Cstar.eval l = bb := by
        intro bb l hx2l
        have hlen := len_of_x2 bb l hx2l
        by_cases hbtrue : bb = true
        · subst bb
          have hCl : C.eval l = true := hcorr true l hx2l
          have heqj : V (pre ++ g :: post) l (26 + j) = V gs' l (26 + j) := by
            have h1 : V (pre ++ g :: post) l (26 + j) = V C.gates l i := by
              simpa [hsplit] using heq l hlen hx2l
            have h2 : V gs' l (26 + j) = V C.gates l i := by
              have hgj : gs'.getD j dflt = ⟨GateOp.or, [i]⟩ := by simp [gs', List.getD_append, hprelen]
              rw [gate_val_aux gs' l hlen j _ ⟨GateOp.or, [i]⟩ hgj
                (by intro u hu; simp at hu; subst u; omega)]
              simp [GateOp.eval]
            rw [h1, h2]
          have heqw := wires_eq pre post g l hlen j i hprelen hi_g
            (by simpa [hsplit] using hback) (by simpa [gs'] using hback_star) heqj
          have hv : V gs' l C.output = true := by
            rw [← heqw C.output]
            simpa [V, Circuit.wires, wiresFrom, hsplit] using hCl
          simpa [Cstar, Circuit.eval, V, Circuit.wires, wiresFrom] using hv
        · have hbfalse : bb = false := by cases bb <;> simp_all
          subst bb
          have hCl : C.eval l = false := hcorr false l hx2l
          have hcmp := wires_imp_or pre post g l hlen j i hprelen hi_g hopor
            (by simpa [hsplit] using hmono_all) (by simpa [hsplit] using hback)
          have hv : V gs' l C.output = false := by
            by_contra hvc
            have hvtrue : V gs' l C.output = true := by
              cases V gs' l C.output <;> simp_all
            have hctrue : V (pre ++ g :: post) l C.output = true := by
              simpa [hsplit] using hcmp C.output hvtrue
            have hcfalse : V C.gates l C.output = false := by
              simpa [V, Circuit.wires, wiresFrom] using hCl
            simp_all
          simpa [Cstar, Circuit.eval, V, Circuit.wires, wiresFrom] using hv
      let out' : ℕ := if C.output = 26 + j then i else C.output
      have hout_ne : out' ≠ 26 + j := by
        dsimp [out']
        split_ifs with h
        · omega
        · exact h
      have hwi : ∀ x : List Bool, x.length = 26 → V gs' x (26 + j) = V gs' x i := by
        intro x hx
        have hgj : gs'.getD j dflt = ⟨GateOp.or, [i]⟩ := by simp [gs', List.getD_append, hprelen]
        rw [gate_val_aux gs' x hx j _ ⟨GateOp.or, [i]⟩ hgj
          (by intro u hu; simp at hu; subst u; omega)]
        simp [GateOp.eval]
      have hfv : ∀ (x : List Bool), x.length = 26 → ∀ (k : ℕ) (gg : Gate), gs'[k]? = some gg →
          (f1 j i gg).op.eval ((f1 j i gg).inputs.map (V gs' x)) = gg.op.eval (gg.inputs.map (V gs' x)) := by
        intro x hx k gg hk
        simp only [f1, List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        by_cases huj : u = 26 + j
        · subst u
          exact (hwi x hx).symm
        · simp [huj]
      have hfm : ∀ gg ∈ gs', (f1 j i gg).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
          (f1 j i gg).inputs.length ≤ 2 := by
        intro gg hgg
        have hh := hmon_star gg (by simpa [Cstar] using hgg)
        exact ⟨by simpa [f1] using hh.1, by simpa [f1] using hh.2⟩
      have hfb : ∀ (k : ℕ) (gg : Gate), gs'[k]? = some gg →
          ∀ u ∈ (f1 j i gg).inputs, u < 26 + k ∧ u ≠ 26 + j := by
        intro k gg hk u hu
        simp only [f1, List.mem_map] at hu
        obtain ⟨v, hv, rfl⟩ := hu
        have hklt : k < gs'.length := (List.getElem?_eq_some_iff.mp hk).1
        have hvlt := hback_star k hklt v hv
        by_cases hvj : v = 26 + j
        · subst v
          constructor <;> omega
        · exact ⟨hvlt, hvj⟩
      have hov : ∀ (x : List Bool), x.length = 26 → V gs' x out' = V gs' x C.output := by
        intro x hx
        dsimp [out']
        split_ifs with h
        · exact hwi x hx
        · rfl
      obtain ⟨D, hDmon, hDrb, hDlt, hDeval⟩ :=
        core gs' C.output j (by simp [gs', List.getD_append, hprelen]) (f1 j i) out' hout_ne
          hback_star hfm hfb hfv hov
      refine ⟨D, ?_, ?_⟩
      · refine ⟨hDmon, hDrb, ?_⟩
        intro bb l hx2l
        have hlen := len_of_x2 bb l hx2l
        change Circuit.eval ⟨gs', C.output⟩ l = bb
        rw [hDeval l hlen]
        exact hcorr_star bb l hx2l
      · simpa [gs', hsplit] using hDlt
