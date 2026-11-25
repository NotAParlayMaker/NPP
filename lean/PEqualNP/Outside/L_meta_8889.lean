import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8889_aux

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem gL {V l : List Bool} {i : ℕ} (h : i < V.length) :
    (V ++ l).getD i false = V.getD i false := List.getD_append _ _ _ _ h

theorem fold_pre (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl stp w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (stp w g)
    exact ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, by
      simp only [List.foldl_cons]; rw [ht]; simp [stp]⟩

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stp w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons]; rw [ih]; simp [stp]; omega

theorem fold_get (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl stp w).getD i false = w.getD i false := by
  obtain ⟨t, ht⟩ := fold_pre gs w
  rw [ht]; exact gL h

def RB (n : ℕ) (gs : List Gate) : Prop := ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j

theorem rb_app {n : ℕ} {a b : List Gate} (ha : RB n a) (hb : RB (n + a.length) b) : RB n (a ++ b) := by
  intro j hj i hi
  by_cases h : j < a.length
  · rw [List.getElem_append_left h] at hi; exact ha j h i hi
  · rw [List.getElem_append_right (by omega)] at hi
    have := hb (j - a.length) (by simp at hj; omega) i hi
    omega

theorem rb_one {n : ℕ} {g : Gate} (h : ∀ i ∈ g.inputs, i < n) : RB n [g] := by
  intro j hj i hi
  simp at hj
  subst hj
  have := h i (by simpa using hi)
  omega

theorem rb_iff (n : ℕ) (C : Circuit) : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ↔ RB n C.gates := by
  constructor
  · intro h j hj i hi
    have := h j hj i
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at this
    rw [List.getD_eq_getElem _ _ hj] at this
    exact this hi
  · intro h j hj i hi
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    exact h j hj i hi

def OK (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def ent : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | c, cur, y :: ys => ⟨GateOp.or, [cur, y]⟩ :: ent (c + 1) c ys

def lw : ℕ → ℕ → List ℕ → ℕ
  | _, cur, [] => cur
  | c, _, _ :: ys => lw (c + 1) c ys

theorem ent_len (c cur : ℕ) (ys : List ℕ) : (ent c cur ys).length = ys.length := by
  induction ys generalizing c cur with
  | nil => simp [ent]
  | cons y ys ih => simp [ent, ih]

theorem lw_lt (c cur : ℕ) (ys : List ℕ) (h : cur < c) : lw c cur ys < c + ys.length := by
  induction ys generalizing c cur with
  | nil => simpa [lw] using h
  | cons y ys ih => have := ih (c + 1) c (by omega); simp [lw]; omega

theorem ent_ok (c cur : ℕ) (ys : List ℕ) : ∀ g ∈ ent c cur ys, OK g := by
  induction ys generalizing c cur with
  | nil => simp [ent]
  | cons y ys ih =>
    intro g hg
    simp only [ent, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp [OK]
    · exact ih _ _ g hg

theorem ent_rb (c cur : ℕ) (ys : List ℕ) (h : cur < c) (hy : ∀ y ∈ ys, y < c) :
    RB c (ent c cur ys) := by
  induction ys generalizing c cur with
  | nil => intro j hj; simp [ent] at hj
  | cons y ys ih =>
    show RB c ([⟨GateOp.or, [cur, y]⟩] ++ ent (c + 1) c ys)
    apply rb_app
    · apply rb_one
      have := hy y (by simp)
      intro i hi; simp at hi; omega
    · simp only [List.length_singleton]
      exact ih (c + 1) c (by omega) (fun z hz => by have := hy z (by simp [hz]); omega)

theorem stp_last (V : List Bool) (g : Gate) :
    (stp V g).getD V.length false = g.op.eval (g.inputs.map fun i => V.getD i false) := by
  simp [stp, List.getD_eq_getElem?_getD]

theorem ent_val (R : ℕ) (f : ℕ → Bool) (ys : List ℕ) (hy : ∀ y ∈ ys, y < R) :
    ∀ (c cur : ℕ) (V : List Bool), V.length = c → cur < c → R ≤ c →
      (∀ i < R, V.getD i false = f i) →
      ((ent c cur ys).foldl stp V).getD (lw c cur ys) false = (V.getD cur false || ys.any f) := by
  induction ys with
  | nil => intro c cur V _ _ _ _; simp [ent, lw]
  | cons y ys ih =>
    intro c cur V hV hc hR hf
    have hyR := hy y (by simp)
    simp only [ent, lw, List.foldl_cons]
    rw [ih (fun z hz => hy z (by simp [hz])) (c + 1) c (stp V _) (by simp [stp, hV]) (by omega)
      (by omega) (fun i hi => by rw [stp, gL (by omega)]; exact hf i hi)]
    rw [← hV, stp_last]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id_eq]
    rw [hf y hyR, Bool.or_assoc]

def ea (c p y : ℕ) (t : List ℕ) : List Gate := ent c y t ++ [⟨GateOp.and, [p, lw c y t]⟩]

theorem ea_len (c p y : ℕ) (t : List ℕ) : (ea c p y t).length = t.length + 1 := by
  simp [ea, ent_len]

theorem ea_ok (c p y : ℕ) (t : List ℕ) : ∀ g ∈ ea c p y t, OK g := by
  intro g hg
  simp only [ea, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact ent_ok _ _ _ g hg
  · simp [OK]

theorem ea_rb (c p y : ℕ) (t : List ℕ) (hp : p < c) (hy : y < c) (ht : ∀ z ∈ t, z < c) :
    RB c (ea c p y t) := by
  apply rb_app (ent_rb c y t hy ht)
  apply rb_one
  have := lw_lt c y t hy
  intro i hi; simp at hi; rw [ent_len]; omega

theorem ea_val (R : ℕ) (f : ℕ → Bool) (p y : ℕ) (t : List ℕ) (hp : p < R) (hy : y < R)
    (ht : ∀ z ∈ t, z < R) (c : ℕ) (V : List Bool) (hV : V.length = c) (hR : R ≤ c)
    (hf : ∀ i < R, V.getD i false = f i) :
    ((ea c p y t).foldl stp V).getD (c + t.length) false = (f p && (y :: t).any f) := by
  simp only [ea, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hl : ((ent c y t).foldl stp V).length = c + t.length := by rw [fold_len, ent_len, hV]
  have hv := ent_val R f t ht c y V hV (by omega) hR hf
  have hpre : ((ent c y t).foldl stp V).getD p false = f p := by
    rw [fold_get _ _ _ (by omega)]; exact hf p hp
  generalize (ent c y t).foldl stp V = W at hl hv hpre
  rw [← hl, stp_last]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id_eq]
  rw [hpre, hv, hf y hy]

def blk (c acc p : ℕ) : List ℕ → List Gate
  | [] => []
  | y :: t => ea c p y t ++ [⟨GateOp.or, [acc, c + t.length]⟩]

def chainG : ℕ → ℕ → List (ℕ × List ℕ) → List Gate
  | _, _, [] => []
  | c, acc, e :: es => blk c acc e.1 e.2 ++ chainG (c + e.2.length + 1) (c + e.2.length) es

def finalAcc : ℕ → ℕ → List (ℕ × List ℕ) → ℕ
  | _, acc, [] => acc
  | c, _, e :: es => finalAcc (c + e.2.length + 1) (c + e.2.length) es

theorem blk_len (c acc p : ℕ) (ys : List ℕ) (h : ys ≠ []) : (blk c acc p ys).length = ys.length + 1 := by
  cases ys with
  | nil => exact absurd rfl h
  | cons y t => simp [blk, ea_len]

theorem blk_ok (c acc p : ℕ) (ys : List ℕ) : ∀ g ∈ blk c acc p ys, OK g := by
  cases ys with
  | nil => simp [blk]
  | cons y t =>
    intro g hg
    simp only [blk, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ea_ok _ _ _ _ g hg
    · simp [OK]

theorem blk_rb (c acc p : ℕ) (ys : List ℕ) (ha : acc < c) (hp : p < c) (hy : ∀ z ∈ ys, z < c) :
    RB c (blk c acc p ys) := by
  cases ys with
  | nil => intro j hj; simp [blk] at hj
  | cons y t =>
    apply rb_app (ea_rb c p y t hp (hy y (by simp)) (fun z hz => hy z (by simp [hz])))
    apply rb_one
    intro i hi; simp at hi; rw [ea_len]; omega

theorem blk_val (R : ℕ) (f : ℕ → Bool) (acc p : ℕ) (ys : List ℕ) (hne : ys ≠ []) (hp : p < R)
    (hy : ∀ z ∈ ys, z < R) (c : ℕ) (V : List Bool) (hV : V.length = c) (hR : R ≤ c) (ha : acc < c)
    (hf : ∀ i < R, V.getD i false = f i) :
    ((blk c acc p ys).foldl stp V).getD (c + ys.length) false =
      (V.getD acc false || (f p && ys.any f)) := by
  cases ys with
  | nil => exact absurd rfl hne
  | cons y t =>
    simp only [blk, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hl : ((ea c p y t).foldl stp V).length = c + t.length + 1 := by rw [fold_len, ea_len, hV]; omega
    have hv := ea_val R f p y t hp (hy y (by simp)) (fun z hz => hy z (by simp [hz])) c V hV hR hf
    have hacc : ((ea c p y t).foldl stp V).getD acc false = V.getD acc false := fold_get _ _ _ (by omega)
    generalize (ea c p y t).foldl stp V = W at hl hv hacc
    rw [show c + (y :: t).length = W.length by simp [hl]; omega, stp_last]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id_eq]
    rw [hacc, hv, List.any_cons]

theorem chain_len (es : List (ℕ × List ℕ)) (hne : ∀ e ∈ es, e.2 ≠ []) :
    ∀ c acc, (chainG c acc es).length = (es.map fun e => e.2.length + 1).sum := by
  induction es with
  | nil => simp [chainG]
  | cons e es ih =>
    intro c acc
    simp only [chainG, List.length_append, List.map_cons, List.sum_cons]
    rw [blk_len _ _ _ _ (hne e (by simp)), ih (fun e he => hne e (by simp [he]))]

theorem chain_ok (es : List (ℕ × List ℕ)) : ∀ c acc, ∀ g ∈ chainG c acc es, OK g := by
  induction es with
  | nil => simp [chainG]
  | cons e es ih =>
    intro c acc g hg
    simp only [chainG, List.mem_append] at hg
    rcases hg with hg | hg
    · exact blk_ok _ _ _ _ g hg
    · exact ih _ _ g hg

theorem chain_rb (R : ℕ) (es : List (ℕ × List ℕ)) (hes : ∀ e ∈ es, e.1 < R ∧ e.2 ≠ [] ∧ ∀ y ∈ e.2, y < R) :
    ∀ c acc, R ≤ c → acc < c → RB c (chainG c acc es) := by
  induction es with
  | nil => intro c acc _ _ j hj; simp [chainG] at hj
  | cons e es ih =>
    intro c acc hR ha
    obtain ⟨h1, h2, h3⟩ := hes e (by simp)
    apply rb_app (blk_rb c acc e.1 e.2 ha (by omega) (fun z hz => by have := h3 z hz; omega))
    rw [blk_len _ _ _ _ h2]
    exact ih (fun e he => hes e (by simp [he])) _ _ (by omega) (by omega)

theorem chain_val (R : ℕ) (f : ℕ → Bool) (es : List (ℕ × List ℕ))
    (hes : ∀ e ∈ es, e.1 < R ∧ e.2 ≠ [] ∧ ∀ y ∈ e.2, y < R) :
    ∀ c acc (V : List Bool), V.length = c → R ≤ c → acc < c → (∀ i < R, V.getD i false = f i) →
      ((chainG c acc es).foldl stp V).getD (finalAcc c acc es) false =
        (V.getD acc false || es.any fun e => f e.1 && e.2.any f) := by
  induction es with
  | nil => intro c acc V _ _ _ _; simp [chainG, finalAcc]
  | cons e es ih =>
    intro c acc V hV hR ha hf
    obtain ⟨h1, h2, h3⟩ := hes e (by simp)
    simp only [chainG, finalAcc, List.foldl_append]
    have hl : ((blk c acc e.1 e.2).foldl stp V).length = c + e.2.length + 1 := by
      rw [fold_len, blk_len _ _ _ _ h2, hV]; omega
    have hv := blk_val R f acc e.1 e.2 h2 h1 h3 c V hV hR ha hf
    have hf2 : ∀ i < R, ((blk c acc e.1 e.2).foldl stp V).getD i false = f i := by
      intro i hi; rw [fold_get _ _ _ (by omega)]; exact hf i hi
    rw [ih (fun e he => hes e (by simp [he])) _ _ _ hl (by omega) (by omega) hf2, hv]
    simp [Bool.or_assoc]

def rho (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (k : ℕ) : ℕ :=
  if h : k < x1 then (x3 ⟨k, h⟩).val else k - x1 + x2

def re (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rho x1 x2 x3)⟩

theorem frel (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2) (gs : List Gate) : ∀ (W w : List Bool),
    x1 ≤ w.length → W.length + x1 = w.length + x2 → (∀ k, W[rho x1 x2 x3 k]? = w[k]?) →
    (∀ k, ((gs.map (re x1 x2 x3)).foldl stp W)[rho x1 x2 x3 k]? = (gs.foldl stp w)[k]?) := by
  induction gs with
  | nil => intro W w _ _ h; simpa using h
  | cons g gs ih =>
    intro W w hn hl h
    simp only [List.map_cons, List.foldl_cons]
    have e : (re x1 x2 x3 g).inputs.map (fun i => W.getD i false) =
        g.inputs.map (fun i => w.getD i false) := by
      simp only [re, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, List.getD_eq_getElem?_getD, h]
    apply ih
    · simp only [stp, List.length_append, List.length_singleton]; omega
    · simp only [stp, List.length_append, List.length_singleton]; omega
    · intro k
      simp only [stp, e]
      have hop : (re x1 x2 x3 g).op = g.op := rfl
      rw [hop]
      rcases lt_trichotomy k w.length with hk | hk | hk
      · have : rho x1 x2 x3 k < W.length := by
          unfold rho; split_ifs with h0
          · have := (x3 ⟨k, h0⟩).isLt; omega
          · omega
        rw [List.getElem?_append_left this, List.getElem?_append_left hk, h]
      · subst hk
        have : rho x1 x2 x3 w.length = W.length := by unfold rho; split_ifs <;> omega
        rw [this]; simp
      · have : W.length < rho x1 x2 x3 k := by unfold rho; split_ifs <;> omega
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem cf (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n C x = (C.gates.foldl stp (List.ofFn x)).getD C.output false := rfl

theorem core : ∀ {x1 x2 : ℕ} (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x4 → x4.output < x1 + x4.size → ∀ (x6 : List (Fin x2 × List (Fin x2))), (∀ x7 ∈ x6, x7.2 ≠ []) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x2 x8 ∧ x8.size ≤ x4.size + (List.map (fun (x9 : Fin x2 × List (Fin x2)) => x9.2.length + (1 : ℕ)) x6).sum ∧ ∀ (x9 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x8 x9 = (PEqualNP.MetaComplexity.circuitFun x1 x4 (x9 ∘ x3) || x6.any fun (x10 : Fin x2 × List (Fin x2)) => x9 x10.1 && x10.2.any x9) := by
  intro x1 x2 x3 x4 hAO hout x6 hne
  obtain ⟨hand, hrb, h2⟩ := hAO
  rw [rb_iff] at hrb
  have hs : x4.size = x4.gates.length := rfl
  let es : List (ℕ × List ℕ) := x6.map fun e => (e.1.val, e.2.map Fin.val)
  have hes : ∀ e ∈ es, e.1 < x2 ∧ e.2 ≠ [] ∧ ∀ y ∈ e.2, y < x2 := by
    intro e he
    simp only [es, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    refine ⟨e0.1.isLt, by simpa using hne e0 he0, ?_⟩
    intro y hy
    simp at hy
    obtain ⟨a, _, rfl⟩ := hy
    exact a.isLt
  let B := x2 + x4.size
  let a := rho x1 x2 x3 x4.output
  have ha : a < B := by
    simp only [a, B, rho]; split_ifs with h0
    · have := (x3 ⟨x4.output, h0⟩).isLt; omega
    · omega
  let O := x4.gates.map (re x1 x2 x3)
  have hOl : O.length = x4.size := by simp [O, hs]
  refine ⟨⟨O ++ chainG B a es, finalAcc B a es⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg | hg
    · simp only [O, List.mem_map] at hg; obtain ⟨g0, hg0, rfl⟩ := hg; exact hand g0 hg0
    · exact (chain_ok es B a g hg).1
  · rw [rb_iff]
    apply rb_app
    · intro j hj i hi
      have hj' : j < x4.gates.length := by simpa [O] using hj
      simp only [O, List.getElem_map, re, List.mem_map] at hi
      obtain ⟨b, hb, rfl⟩ := hi
      have := hrb j hj' b hb
      unfold rho; split_ifs with h0
      · have := (x3 ⟨b, h0⟩).isLt; omega
      · omega
    · rw [hOl]
      exact chain_rb x2 es hes B a (by omega) ha
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg | hg
    · simp only [O, List.mem_map] at hg; obtain ⟨g0, hg0, rfl⟩ := hg; simpa [re] using h2 g0 hg0
    · exact (chain_ok es B a g hg).2
  · have := chain_len es (fun e he => (hes e he).2.1) B a
    simp only [Circuit.size, List.length_append] at this ⊢
    rw [this]
    simp [es, List.map_map, Function.comp_def, hOl, ← hs]
  · intro x9
    rw [cf, cf]
    dsimp only
    rw [List.foldl_append]
    let f : ℕ → Bool := fun i => if h : i < x2 then x9 ⟨i, h⟩ else false
    have hV0l : (O.foldl stp (List.ofFn x9)).length = B := by rw [fold_len]; simp [hOl, B]
    rw [chain_val x2 f es hes B a _ hV0l (by omega) ha (by
      intro i hi
      rw [fold_get _ _ _ (by simpa using hi)]
      simp [f, hi, List.getD_eq_getElem?_getD])]
    congr 1
    · have := frel x1 x2 x3 x4.gates (List.ofFn x9) (List.ofFn (x9 ∘ x3)) (by simp) (by simp; omega)
        (by
          intro k
          unfold rho
          split_ifs with h0
          · simp [List.getElem?_ofFn, h0]
          · rw [List.getElem?_eq_none (by simp only [List.length_ofFn]; omega), List.getElem?_eq_none (by simp only [List.length_ofFn]; omega)]) x4.output
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      exact congrArg (fun o => Option.getD o false) this
    · simp [es, List.any_map, Function.comp_def, f]

end PEqualNP.Outside.L_meta_8889_aux

open PEqualNP.Outside.L_meta_8889_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8889 : ∀ {x1 x2 : ℕ} (x3 : Fin x1 → Fin x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x4 → ∀ (x6 : List (Fin x2 × List (Fin x2))), (∀ x7 ∈ x6, x7.2 ≠ []) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x2 x8 ∧ x8.size ≤ x4.size + (List.map (fun (x9 : Fin x2 × List (Fin x2)) => x9.2.length + (1 : ℕ)) x6).sum ∧ ∀ (x9 : Fin x2 → Bool), PEqualNP.MetaComplexity.circuitFun x2 x8 x9 = (PEqualNP.MetaComplexity.circuitFun x1 x4 (x9 ∘ x3) || x6.any fun (x10 : Fin x2 × List (Fin x2)) => x9 x10.1 && x10.2.any x9) := by
  intro x1 x2 x3 x4 hAO x6 hne
  by_cases hout : x4.output < x1 + x4.size
  · exact core x3 x4 hAO hout x6 hne
  have hz : ∀ x : Fin x1 → Bool, PEqualNP.MetaComplexity.circuitFun x1 x4 x = false := by
    intro x
    rw [cf]
    apply List.getD_eq_default
    rw [fold_len]; simp [Circuit.size] at hout ⊢; omega
  cases x6 with
  | nil =>
    refine ⟨⟨[], x2⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · intro g hg; simp at hg
    · intro j hj; simp at hj
    · intro g hg; simp at hg
    · simp [Circuit.size]
    · intro x9; rw [cf, hz]; simp
  | cons e rest =>
    obtain ⟨p, ys⟩ := e
    have hys : ys ≠ [] := hne (p, ys) (by simp)
    obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hys
    let C0 : Circuit := ⟨ea x2 p.val y.val (t.map Fin.val), x2 + t.length⟩
    have hC0 : PEqualNP.TopForm.IsAO2 x2 C0 :=
      ⟨fun g hg => (ea_ok _ _ _ _ g hg).1,
        (rb_iff _ _).2 (ea_rb _ _ _ _ p.isLt y.isLt (by simp)),
        fun g hg => (ea_ok _ _ _ _ g hg).2⟩
    have hC0o : C0.output < x2 + C0.size := by simp [C0, Circuit.size, ea_len]
    obtain ⟨x8, h1, h2, h3⟩ := core id C0 hC0 hC0o rest (fun e he => hne e (by simp [he]))
    refine ⟨x8, h1, ?_, ?_⟩
    · simp [C0, Circuit.size, ea_len] at h2 ⊢; omega
    · intro x9
      rw [h3 x9, hz]
      let f : ℕ → Bool := fun i => if h : i < x2 then x9 ⟨i, h⟩ else false
      have hv := ea_val x2 f p.val y.val (t.map Fin.val) p.isLt y.isLt (by simp) x2 (List.ofFn x9)
        (by simp) le_rfl (by intro i hi; simp [f, hi, List.getD_eq_getElem?_getD])
      have e0 : PEqualNP.MetaComplexity.circuitFun x2 C0 (x9 ∘ id) = (x9 p && (y :: t).any x9) := by
        rw [cf]
        simp only [C0, Function.comp_id]
        rw [List.length_map] at hv
        rw [hv]
        simp [f, List.any_map, Function.comp_def]
      rw [e0]
      simp
