import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L568H
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def dG : Gate := ⟨GateOp.or, []⟩
def G (C : Circuit) (j : ℕ) : Gate := C.gates.getD j dG
def val (N : ℕ) (C : Circuit) (x : Fin N → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false
def rd (v : ℕ → Bool) (p a : ℕ) : Bool := if a < p then v a else false
def ev (g : Gate) (f : ℕ → Bool) : Bool := g.op.eval (g.inputs.map f)
def Sat (N : ℕ) (C : Circuit) (x : Fin N → Bool) (v : ℕ → Bool) : Prop :=
  ∀ i, v i = if h : i < N then x ⟨i, h⟩ else
    if i < N + C.gates.length then ev (G C (i - N)) (rd v i) else false

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem fold_spec : ∀ (gs : List Gate) (w : List Bool),
    (gs.foldl stp w).length = w.length + gs.length ∧
    (∀ i < w.length, (gs.foldl stp w).getD i false = w.getD i false) ∧
    ∀ j < gs.length, (gs.foldl stp w).getD (w.length + j) false =
      ev (gs.getD j dG) (rd (fun a => (gs.foldl stp w).getD a false) (w.length + j)) := by
  intro gs
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    obtain ⟨h1, h2, h3⟩ := ih (stp w g)
    have hl : (stp w g).length = w.length + 1 := by simp [stp]
    simp only [List.foldl_cons]
    refine ⟨by rw [h1, hl]; simp; omega, ?_, ?_⟩
    · intro i hi
      rw [h2 i (by omega)]
      simp [stp, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    · intro j hj
      rcases j with _ | j
      · have e0 : (stp w g).getD w.length false =
            g.op.eval (g.inputs.map fun i => w.getD i false) := by simp [stp]
        have e1 : ∀ a < w.length, (stp w g).getD a false = w.getD a false := by
          intro a ha; simp [stp, List.getD_eq_getElem?_getD, List.getElem?_append_left ha]
        rw [Nat.add_zero, h2 _ (by omega), e0]
        unfold ev
        simp only [List.getD_cons_zero]
        congr 1
        apply List.map_congr_left
        intro a _
        unfold rd
        split_ifs with ha
        · show _ = (List.foldl stp (stp w g) gs).getD a false
          rw [h2 a (by omega), e1 a ha]
        · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt ha)]
      · have := h3 j (by simp at hj; omega)
        rw [hl] at this
        simp only [List.getD_cons_succ]
        rw [show w.length + (j + 1) = w.length + 1 + j by omega]
        exact this

theorem fold_beyond (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (gs.foldl stp w).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [(fold_spec gs w).1]; exact h

theorem wires_eq (C : Circuit) (l : List Bool) : C.wires l = C.gates.foldl stp l := rfl

theorem val_sat (N : ℕ) (C : Circuit) (x : Fin N → Bool) : Sat N C x (val N C x) := by
  intro i
  have hlen : (List.ofFn x).length = N := List.length_ofFn
  obtain ⟨_, h2, h3⟩ := fold_spec C.gates (List.ofFn x)
  unfold val
  rw [wires_eq]
  split_ifs with h hh
  · rw [h2 i (by omega)]; simp [List.getD_eq_getElem?_getD, h]
  · have := h3 (i - N) (by omega)
    rw [hlen, show N + (i - N) = i by omega] at this
    exact this
  · exact fold_beyond _ _ _ (by omega)

theorem sat_unique (N : ℕ) (C : Circuit) (x : Fin N → Bool) (v : ℕ → Bool)
    (hv : Sat N C x v) : v = val N C x := by
  funext i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [hv i, val_sat N C x i]
    split_ifs with h hh
    · rfl
    · unfold ev
      congr 1
      apply List.map_congr_left
      intro a _
      unfold rd
      split_ifs with ha
      · exact ih a ha
      · rfl
    · rfl

theorem fun_val (N : ℕ) (C : Circuit) (x : Fin N → Bool) :
    circuitFun N C x = val N C x C.output := rfl

def SR (g : Gate) (a : ℕ) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.head? = some a) ∨ (g.op ≠ GateOp.not ∧ a ∈ g.inputs)

theorem ev_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ a, SR g a → f a = f' a) :
    ev g f = ev g f' := by
  unfold ev
  rcases g with ⟨op, l⟩
  cases op with
  | not =>
    cases l with
    | nil => rfl
    | cons a l =>
      simp only [GateOp.eval, List.map_cons, List.headD_cons]
      rw [h a (Or.inl ⟨rfl, rfl⟩)]
  | _ =>
    congr 1
    apply List.map_congr_left
    intro a ha
    exact h a (Or.inr ⟨by simp, ha⟩)


def mk (L : ℕ) (φ : ℕ → Gate) : List Gate := (List.range L).map φ

theorem mk_len (L : ℕ) (φ : ℕ → Gate) : (mk L φ).length = L := by simp [mk]

theorem mk_getD (L : ℕ) (φ : ℕ → Gate) (j : ℕ) :
    (mk L φ).getD j dG = if j < L then φ j else dG := by
  unfold mk
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem G_mem (C : Circuit) (j : ℕ) (h : j < C.gates.length) : G C j ∈ C.gates := by
  unfold G; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; simp

theorem fit_iff (C : Circuit) : FanInTwo C ↔ ∀ j < C.gates.length, Ok (G C j) := by
  constructor
  · intro h j hj
    obtain ⟨h1, h2⟩ := h _ (G_mem C j hj)
    refine ⟨?_, h2⟩
    simpa using h1
  · intro h g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have := h j hj
    have e : G C j = C.gates[j] := by
      unfold G; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    rw [← e]
    refine ⟨?_, this.2⟩
    rcases this.1 with h1 | h1 | h1 <;> simp [h1]

theorem fit_mk (L o : ℕ) (φ : ℕ → Gate) (h : ∀ j < L, Ok (φ j)) :
    FanInTwo ⟨mk L φ, o⟩ := by
  rw [fit_iff]
  intro j hj
  simp only [mk_len] at hj
  simp only [G, mk_getD, hj, if_true]
  exact h j hj

def rp (N d ρ big : ℕ) : ℕ := if ρ < N + d then ρ else big

def mp (N d ρ big j a : ℕ) : ℕ :=
  if a = N + d then (if d < j then rp N d ρ big else big) else if a < N + d then a else a - 1

def rg (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩

def delG (N : ℕ) (C : Circuit) (d ρ : ℕ) (j : ℕ) : Gate :=
  if j < d then rg (mp N d ρ (N + C.gates.length) j) (G C j)
  else rg (mp N d ρ (N + C.gates.length) (j + 1)) (G C (j + 1))

def del (N : ℕ) (C : Circuit) (d ρ : ℕ) : Circuit :=
  ⟨mk (C.gates.length - 1) (delG N C d ρ),
   if C.output = N + d then rp N d ρ (N + C.gates.length)
   else if C.output < N + d then C.output else C.output - 1⟩

theorem ev_rg (f : ℕ → ℕ) (g : Gate) (v : ℕ → Bool) : ev (rg f g) v = ev g (v ∘ f) := by
  simp [ev, rg, List.map_map]

theorem ev_ext (g : Gate) (f f' : ℕ → Bool) (h : ∀ a, f a = f' a) : ev g f = ev g f' := by
  rw [funext h]

theorem del_size (N : ℕ) (C : Circuit) (d ρ : ℕ) : (del N C d ρ).size = C.gates.length - 1 := by
  simp [del, Circuit.size, mk_len]

theorem del_fit (N : ℕ) (C : Circuit) (d ρ : ℕ) (hC : FanInTwo C) : FanInTwo (del N C d ρ) := by
  rw [fit_iff] at hC
  apply fit_mk
  intro j hj
  unfold delG
  split_ifs
  · have := hC j (by omega); exact ⟨this.1, by simpa [rg] using this.2⟩
  · have := hC (j + 1) (by omega); exact ⟨this.1, by simpa [rg] using this.2⟩

theorem del_val (N : ℕ) (C : Circuit) (d ρ : ℕ) (hd : d < C.gates.length) (x : Fin N → Bool)
    (hH : ∀ j, d < j → j < C.gates.length →
      ev (G C j) (rd (Function.update (val N C x) (N + d) (rd (val N C x) (N + d) ρ)) (N + j))
        = val N C x (N + j))
    (hO : C.output = N + d → rd (val N C x) (N + d) ρ = val N C x (N + d)) :
    circuitFun N (del N C d ρ) x = circuitFun N C x := by
  have hW := val_sat N C x
  have hU : Sat N (del N C d ρ) x
      (fun i => if i < N + d then val N C x i else val N C x (i + 1)) := by
    intro i
    have hlen : (del N C d ρ).gates.length = C.gates.length - 1 := by simp [del, mk_len]
    rw [hlen]
    show (if i < N + d then val N C x i else val N C x (i + 1)) = _
    by_cases h1 : i < N
    · rw [dif_pos h1, if_pos (by omega), hW i, dif_pos h1]
    rw [dif_neg h1]
    by_cases h2 : i < N + (C.gates.length - 1)
    · rw [if_pos h2]
      have hg : G (del N C d ρ) (i - N) = delG N C d ρ (i - N) := by
        simp only [G, del, mk_getD]; rw [if_pos (by omega)]
      rw [hg]
      unfold delG
      by_cases h3 : i < N + d
      · rw [if_pos h3, hW i, dif_neg h1, if_pos (by omega), if_pos (by omega), ev_rg]
        apply ev_ext
        intro a
        simp only [Function.comp, rd, mp]
        split_ifs <;> first | rfl | omega
      · have hh := hH (i - N + 1) (by omega) (by omega)
        rw [show N + (i - N + 1) = i + 1 by omega] at hh
        rw [if_neg h3, ← hh, if_neg (by omega), ev_rg]
        apply ev_ext
        intro a
        simp only [Function.comp, rd, mp, rp, Function.update]
        split_ifs <;> first | rfl | omega | (subst_vars; rfl) | (congr 1; omega)
    · rw [if_neg h2, if_neg (by omega), hW (i + 1), dif_neg (by omega), if_neg (by omega)]
  have e := sat_unique N _ x _ hU
  rw [fun_val, fun_val, ← e]
  have hb : ∀ i, N + C.gates.length ≤ i → val N C x i = false := by
    intro i hi; rw [hW i, dif_neg (by omega), if_neg (by omega)]
  by_cases ho : C.output = N + d
  · have hout : (del N C d ρ).output = rp N d ρ (N + C.gates.length) := by simp [del, ho]
    have := hO ho
    rw [hout, ho, ← this]
    beta_reduce
    unfold rp rd
    by_cases hr : ρ < N + d
    · rw [if_pos hr, if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr, if_neg (by omega), hb _ (by omega)]
  · by_cases ho2 : C.output < N + d
    · have hout : (del N C d ρ).output = C.output := by simp [del, ho, ho2]
      rw [hout]; beta_reduce; rw [if_pos ho2]
    · have hout : (del N C d ρ).output = C.output - 1 := by simp [del, ho, ho2]
      rw [hout]; beta_reduce
      rw [if_neg (by omega), show C.output - 1 + 1 = C.output by omega]


def forceG (g : Gate) (p : ℕ) (b : Bool) : Gate :=
  match g.op, b with
  | GateOp.and, true => ⟨GateOp.and, g.inputs.filter (· ≠ p)⟩
  | GateOp.and, false => ⟨GateOp.or, []⟩
  | GateOp.or, true => ⟨GateOp.and, []⟩
  | GateOp.or, false => ⟨GateOp.or, g.inputs.filter (· ≠ p)⟩
  | _, true => ⟨GateOp.or, []⟩
  | _, false => ⟨GateOp.and, []⟩

def Triv (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 1) ∨
    (g.op = GateOp.not ∧ g.inputs = [])

theorem all_filter (l : List ℕ) (f : ℕ → Bool) (p : ℕ) (hp : f p = true) :
    ((l.filter (· ≠ p)).map f).all id = (l.map f).all id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = p
    · subst h
      rw [List.filter_cons_of_neg (by simp)]
      simp only [List.map_cons, List.all_cons, hp, id, Bool.true_and]
      exact ih
    · rw [List.filter_cons_of_pos (by simpa using h)]
      simp only [List.map_cons, List.all_cons]
      rw [ih]

theorem any_filter (l : List ℕ) (f : ℕ → Bool) (p : ℕ) (hp : f p = false) :
    ((l.filter (· ≠ p)).map f).any id = (l.map f).any id := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : a = p
    · subst h
      rw [List.filter_cons_of_neg (by simp)]
      simp only [List.map_cons, List.any_cons, hp, id, Bool.false_or]
      exact ih
    · rw [List.filter_cons_of_pos (by simpa using h)]
      simp only [List.map_cons, List.any_cons]
      rw [ih]

theorem filter_len (l : List ℕ) (p : ℕ) (h : p ∈ l) (h2 : l.length ≤ 2) :
    (l.filter (· ≠ p)).length ≤ 1 := by
  have : (l.filter (· ≠ p)).length < l.length := by
    rw [List.length_filter_lt_length_iff_exists]
    exact ⟨p, h, by simp⟩
  omega

theorem forceG_ev (g : Gate) (p : ℕ) (b : Bool) (f : ℕ → Bool) (hg : Ok g) (hs : SR g p)
    (hf : f p = b) : ev (forceG g p b) f = ev g f := by
  rcases g with ⟨op, l⟩
  obtain ⟨hop, _⟩ := hg
  simp only at hop
  rcases hop with rfl | rfl | rfl
  · have hm : p ∈ l := by
      rcases hs with ⟨h, _⟩ | ⟨_, h⟩
      · simp at h
      · exact h
    cases b
    · simp only [forceG, ev, GateOp.eval, List.map_nil, List.any_nil]
      symm; rw [List.all_eq_false]; exact ⟨f p, by simp; exact ⟨p, hm, rfl⟩, by simp [hf]⟩
    · simp only [forceG, ev, GateOp.eval]; exact all_filter l f p hf
  · have hm : p ∈ l := by
      rcases hs with ⟨h, _⟩ | ⟨_, h⟩
      · simp at h
      · exact h
    cases b
    · simp only [forceG, ev, GateOp.eval]; exact any_filter l f p hf
    · simp only [forceG, ev, GateOp.eval, List.map_nil, List.all_nil]
      symm; rw [List.any_eq_true]; exact ⟨f p, by simp; exact ⟨p, hm, rfl⟩, by simp [hf]⟩
  · have hh : l.head? = some p := by
      rcases hs with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd rfl h
    cases l with
    | nil => simp at hh
    | cons a t =>
      simp at hh; subst hh
      cases b <;> simp [forceG, ev, GateOp.eval, hf]

theorem forceG_ok (g : Gate) (p : ℕ) (b : Bool) (hg : Ok g) : Ok (forceG g p b) := by
  rcases g with ⟨op, l⟩
  obtain ⟨hop, hl⟩ := hg
  simp only at hop hl
  have := List.length_filter_le (· ≠ p) l
  rcases hop with rfl | rfl | rfl <;> cases b <;> simp only [forceG, Ok] <;>
    first | exact ⟨by simp, le_trans this hl⟩ | exact ⟨by simp, by simp⟩

theorem forceG_triv (g : Gate) (p : ℕ) (b : Bool) (hg : Ok g) (hs : SR g p) :
    Triv (forceG g p b) := by
  rcases g with ⟨op, l⟩
  obtain ⟨hop, hl⟩ := hg
  simp only at hop hl
  rcases hop with rfl | rfl | rfl
  · have hm : p ∈ l := by
      rcases hs with ⟨h, _⟩ | ⟨_, h⟩
      · simp at h
      · exact h
    cases b <;> simp only [forceG, Triv] <;> first | (left; exact ⟨by simp, filter_len l p hm hl⟩) | simp
  · have hm : p ∈ l := by
      rcases hs with ⟨h, _⟩ | ⟨_, h⟩
      · simp at h
      · exact h
    cases b <;> simp only [forceG, Triv] <;> first | (left; exact ⟨by simp, filter_len l p hm hl⟩) | simp
  · cases b <;> simp [forceG, Triv]

theorem forceG_noread (g : Gate) (p : ℕ) (b : Bool) (hg : Ok g) : ¬ SR (forceG g p b) p := by
  rcases g with ⟨op, l⟩
  obtain ⟨hop, _⟩ := hg
  simp only at hop
  rcases hop with rfl | rfl | rfl <;> cases b <;> simp [forceG, SR]

open Classical in
noncomputable def fG (N : ℕ) (C : Circuit) (p : ℕ) (b : Bool) (j : ℕ) : Gate :=
  if p < N + j ∧ SR (G C j) p then forceG (G C j) p b else G C j

noncomputable def force (N : ℕ) (C : Circuit) (p : ℕ) (b : Bool) : Circuit :=
  ⟨mk C.gates.length (fG N C p b), C.output⟩

theorem force_len (N : ℕ) (C : Circuit) (p : ℕ) (b : Bool) :
    (force N C p b).gates.length = C.gates.length := by simp [force, mk_len]

theorem force_G (N : ℕ) (C : Circuit) (p : ℕ) (b : Bool) (j : ℕ) (hj : j < C.gates.length) :
    G (force N C p b) j = fG N C p b j := by
  simp only [G, force]; rw [mk_getD, if_pos hj]

theorem force_fit (N : ℕ) (C : Circuit) (p : ℕ) (b : Bool) (hC : FanInTwo C) :
    FanInTwo (force N C p b) := by
  rw [fit_iff] at hC
  apply fit_mk
  intro j hj
  unfold fG
  split_ifs
  · exact forceG_ok _ _ _ (hC j hj)
  · exact hC j hj

theorem force_val (N : ℕ) (C : Circuit) (p : ℕ) (b : Bool) (hC : FanInTwo C)
    (x : Fin N → Bool) (hp : val N C x p = b) : val N (force N C p b) x = val N C x := by
  rw [fit_iff] at hC
  symm
  apply sat_unique
  intro i
  rw [val_sat N C x i, force_len]
  split_ifs with h1 h2
  · rfl
  · rw [force_G _ _ _ _ _ (by omega)]
    unfold fG
    split_ifs with h3
    · symm
      apply forceG_ev _ _ _ _ (hC _ (by omega)) h3.2
      unfold rd; rw [if_pos (by omega), hp]
    · rfl
  · rfl

theorem force_triv (N : ℕ) (C : Circuit) (p : ℕ) (b : Bool) (hC : FanInTwo C) (j : ℕ)
    (hj : j < C.gates.length) (h : Triv (G C j)) : Triv (G (force N C p b) j) := by
  rw [fit_iff] at hC
  rw [force_G _ _ _ _ _ hj]
  unfold fG
  split_ifs with h3
  · exact forceG_triv _ _ _ (hC j hj) h3.2
  · exact h

def appC (N : ℕ) (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], N + C.gates.length⟩

theorem appC_G (N : ℕ) (C : Circuit) (g : Gate) (j : ℕ) :
    G (appC N C g) j = if j < C.gates.length then G C j else if j = C.gates.length then g else dG := by
  unfold G appC
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp [List.getElem?_eq_none (show C.gates.length ≤ j by omega)]

theorem appC_val (N : ℕ) (C : Circuit) (g : Gate) (x : Fin N → Bool) (i : ℕ) :
    val N (appC N C g) x i = if i < N + C.gates.length then val N C x i
      else if i = N + C.gates.length then ev g (rd (val N C x) (N + C.gates.length)) else false := by
  have hU : Sat N (appC N C g) x (fun i => if i < N + C.gates.length then val N C x i
      else if i = N + C.gates.length then ev g (rd (val N C x) (N + C.gates.length)) else false) := by
    intro i
    have hl : (appC N C g).gates.length = C.gates.length + 1 := by simp [appC]
    rw [hl, appC_G]
    beta_reduce
    have hW := val_sat N C x i
    have hr : rd (fun i => if i < N + C.gates.length then val N C x i
      else if i = N + C.gates.length then ev g (rd (val N C x) (N + C.gates.length)) else false) i =
        rd (val N C x) i ∨ N + C.gates.length < i := by
      by_cases hi : i ≤ N + C.gates.length
      · left; funext a; unfold rd
        by_cases ha : a < i
        · rw [if_pos ha, if_pos ha]; beta_reduce; rw [if_pos (by omega)]
        · rw [if_neg ha, if_neg ha]
      · right; omega
    by_cases h1 : i < N
    · rw [if_pos (by omega), hW, dif_pos h1, dif_pos h1]
    rw [dif_neg h1]
    by_cases h2 : i < N + C.gates.length
    · rw [if_pos h2, if_pos (by omega), if_pos (by omega), hW, dif_neg h1, if_pos h2]
      rcases hr with hr | hr
      · rw [hr]
      · omega
    · by_cases h3 : i = N + C.gates.length
      · rw [if_neg h2, if_pos h3, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        rcases hr with hr | hr
        · rw [hr, h3]
        · omega
      · rw [if_neg h2, if_neg h3, if_neg (by omega)]
  exact (congrFun (sat_unique N _ x _ hU) i).symm

theorem appC_fit (N : ℕ) (C : Circuit) (g : Gate) (hC : FanInTwo C) (hg : Ok g) :
    FanInTwo (appC N C g) := by
  intro g' hg'
  simp only [appC, List.mem_append, List.mem_singleton] at hg'
  rcases hg' with h | rfl
  · exact hC g' h
  · refine ⟨?_, hg.2⟩
    rcases hg.1 with h | h | h <;> simp [h]


theorem triv_rg (f : ℕ → ℕ) (g : Gate) (h : Triv g) : Triv (rg f g) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1, by simpa [rg] using h2⟩
  · right; exact ⟨h1, by simp [rg, h2]⟩

theorem del_G (N : ℕ) (C : Circuit) (d ρ : ℕ) (j : ℕ) (hj : j < C.gates.length - 1) :
    G (del N C d ρ) j = delG N C d ρ j := by
  simp only [G, del]; rw [mk_getD, if_pos hj]

theorem triv_del (N : ℕ) (C : Circuit) (d ρ : ℕ) (j : ℕ) (hj : j < C.gates.length) (hjd : j ≠ d)
    (hd : d < C.gates.length) (h : Triv (G C j)) :
    Triv (G (del N C d ρ) (if j < d then j else j - 1)) := by
  split_ifs with h1
  · rw [del_G _ _ _ _ _ (by omega)]; unfold delG; rw [if_pos h1]; exact triv_rg _ _ h
  · rw [del_G _ _ _ _ _ (by omega)]; unfold delG; rw [if_neg (by omega),
      show j - 1 + 1 = j by omega]; exact triv_rg _ _ h

theorem triv_cases (g : Gate) (hg : Ok g) (ht : Triv g) :
    (∃ a, ∀ f, ev g f = f a) ∨ (∀ f, ev g f = false) ∨ (∀ f, ev g f = true) := by
  rcases g with ⟨op, l⟩
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only at h1 h2
    match l, h2 with
    | [], _ => rcases h1 with rfl | rfl
               · right; right; intro f; simp [ev, GateOp.eval]
               · right; left; intro f; simp [ev, GateOp.eval]
    | [a], _ => left; refine ⟨a, fun f => ?_⟩; rcases h1 with rfl | rfl <;> simp [ev, GateOp.eval]
  · simp only at h1 h2; subst h1; subst h2
    right; right; intro f; simp [ev, GateOp.eval]

theorem force_noread (N : ℕ) (C : Circuit) (p : ℕ) (b : Bool) (hC : FanInTwo C) (j : ℕ)
    (hj : j < C.gates.length) (hp : p < N + j) : ¬ SR (G (force N C p b) j) p := by
  rw [fit_iff] at hC
  rw [force_G _ _ _ _ _ hj]
  unfold fG
  split_ifs with h3
  · exact forceG_noread _ _ _ (hC j hj)
  · exact fun h => h3 ⟨hp, h⟩

theorem elim (N : ℕ) : ∀ (t : ℕ) (E : Circuit) (T : Finset ℕ), FanInTwo E →
    (∃ x x' : Fin N → Bool, circuitFun N E x ≠ circuitFun N E x') → T.card = t →
    (∀ d ∈ T, d < E.gates.length ∧ Triv (G E d)) →
    ∃ D : Circuit, FanInTwo D ∧ D.size + t ≤ E.size ∧ circuitFun N D = circuitFun N E := by
  intro t
  induction t with
  | zero => intro E T hE _ _ _; exact ⟨E, hE, by simp, rfl⟩
  | succ t ih =>
    intro E T hE hnc hT hTd
    obtain ⟨d, hdT⟩ : T.Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨hd, htd⟩ := hTd d hdT
    have hok : Ok (G E d) := (fit_iff E).1 hE d hd
    have hWd := fun x => val_sat N E x (N + d)
    have hWd' : ∀ x, val N E x (N + d) = ev (G E d) (rd (val N E x) (N + d)) := by
      intro x; rw [hWd x, dif_neg (by omega), if_pos (by omega), show N + d - N = d by omega]
    obtain ⟨E', hE', hlen', hfun', htriv', hρ⟩ : ∃ E' : Circuit, FanInTwo E' ∧
        E'.gates.length = E.gates.length ∧ circuitFun N E' = circuitFun N E ∧
        (∀ j < E.gates.length, Triv (G E j) → Triv (G E' j)) ∧
        ∃ ρ, ∀ x, (∀ j, d < j → j < E'.gates.length →
          ev (G E' j) (rd (Function.update (val N E' x) (N + d) (rd (val N E' x) (N + d) ρ)) (N + j))
            = val N E' x (N + j)) ∧
          (E'.output = N + d → rd (val N E' x) (N + d) ρ = val N E' x (N + d)) := by
      have hsimple : ∀ ρ, (∀ x, rd (val N E x) (N + d) ρ = val N E x (N + d)) →
          ∃ E' : Circuit, FanInTwo E' ∧
          E'.gates.length = E.gates.length ∧ circuitFun N E' = circuitFun N E ∧
          (∀ j < E.gates.length, Triv (G E j) → Triv (G E' j)) ∧
          ∃ ρ, ∀ x, (∀ j, d < j → j < E'.gates.length →
            ev (G E' j) (rd (Function.update (val N E' x) (N + d) (rd (val N E' x) (N + d) ρ)) (N + j))
              = val N E' x (N + j)) ∧
            (E'.output = N + d → rd (val N E' x) (N + d) ρ = val N E' x (N + d)) := by
        intro ρ hρ
        refine ⟨E, hE, rfl, rfl, fun j _ h => h, ρ, fun x => ⟨fun j h1 h2 => ?_, fun _ => hρ x⟩⟩
        rw [hρ x, Function.update_eq_self, val_sat N E x (N + j), dif_neg (by omega),
          if_pos (by omega), show N + j - N = j by omega]
      rcases triv_cases _ hok htd with ⟨a, ha⟩ | hf | ht
      · apply hsimple a
        intro x; rw [hWd' x, ha]
      · apply hsimple (N + d)
        intro x; rw [hWd' x, hf]; simp [rd]
      · have hv : ∀ x, val N E x (N + d) = true := fun x => by rw [hWd' x, ht]
        refine ⟨force N E (N + d) true, force_fit _ _ _ _ hE, force_len _ _ _ _,
          ?_, fun j hj h => force_triv _ _ _ _ hE j hj h, N + d, fun x => ⟨?_, ?_⟩⟩
        · funext x; rw [fun_val, fun_val, force_val _ _ _ _ hE x (hv x)]; rfl
        · intro j h1 h2
          rw [force_len] at h2
          rw [val_sat N (force N E (N + d) true) x (N + j), dif_neg (by omega),
            if_pos (by rw [force_len]; omega), show N + j - N = j by omega]
          apply ev_congr
          intro a ha
          have hne : a ≠ N + d := by
            rintro rfl
            exact force_noread N E (N + d) true hE j h2 (by omega) ha
          simp only [rd, Function.update_of_ne hne]
        · intro ho
          exfalso
          obtain ⟨x, x', hxx⟩ := hnc
          apply hxx
          have ho' : E.output = N + d := ho
          rw [fun_val, fun_val, ho', hv, hv]
    obtain ⟨ρ, hρ⟩ := hρ
    have hd' : d < E'.gates.length := by omega
    set D0 := del N E' d ρ with hD0
    have hf0 : circuitFun N D0 = circuitFun N E := by
      rw [← hfun']; funext x; exact del_val N E' d ρ hd' x (hρ x).1 (hρ x).2
    have hfit0 : FanInTwo D0 := del_fit N E' d ρ hE'
    have hs0 : D0.size = E.gates.length - 1 := by rw [hD0, del_size, hlen']
    let φ : ℕ → ℕ := fun j => if j < d then j else j - 1
    have hinj : Set.InjOn φ (T.erase d : Set ℕ) := by
      intro a ha b hb hab
      simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at ha hb
      simp only [φ] at hab
      split_ifs at hab <;> omega
    obtain ⟨D, hD, hDs, hDf⟩ := ih D0 ((T.erase d).image φ) hfit0
      (by rw [hf0]; exact hnc)
      (by rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hdT, hT]; rfl)
      (by
        intro j' hj'
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hj'
        obtain ⟨hjd, hjT⟩ := Finset.mem_erase.1 hj
        obtain ⟨hjl, hjt⟩ := hTd j hjT
        refine ⟨?_, ?_⟩
        · rw [hD0]
          simp only [del, mk_len, φ]; split_ifs <;> omega
        · exact triv_del N E' d ρ j (by omega) hjd hd' (htriv' j hjl hjt))
    refine ⟨D, hD, ?_, hDf.trans hf0⟩
    simp only [Circuit.size] at hDs hs0 ⊢
    omega


def Clean (p : ℕ) (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < p ∧ b < p) ∨
    (g.op = GateOp.not ∧ ∃ a, g.inputs.head? = some a ∧ a < p)

theorem canon (p : ℕ) (g : Gate) (hg : Ok g) :
    Clean p g ∨ ∃ g', Ok g' ∧ Triv g' ∧ ∀ f, ev g' (rd f p) = ev g (rd f p) := by
  rcases g with ⟨op, l⟩
  obtain ⟨hop, hl⟩ := hg
  simp only at hop hl
  rcases hop with rfl | rfl | rfl
  · match l, hl with
    | [], _ => right; exact ⟨_, ⟨by simp, by simp⟩, Or.inl ⟨by simp, by simp⟩, fun f => rfl⟩
    | [a], _ => right; exact ⟨_, ⟨by simp, by simp⟩, Or.inl ⟨by simp, by simp⟩, fun f => rfl⟩
    | [a, b], _ =>
      by_cases h : a ≠ b ∧ a < p ∧ b < p
      · left; left; exact ⟨by simp, a, b, rfl, h⟩
      · right
        by_cases hab : a = b
        · subst hab
          exact ⟨⟨GateOp.and, [a]⟩, ⟨by simp, by simp⟩, Or.inl ⟨by simp, by simp⟩,
            fun f => by simp [ev, GateOp.eval]⟩
        · refine ⟨⟨GateOp.or, []⟩, ⟨by simp, by simp⟩, Or.inl ⟨by simp, by simp⟩, fun f => ?_⟩
          have : ¬ a < p ∨ ¬ b < p := by tauto
          rcases this with h1 | h1 <;> simp [ev, GateOp.eval, rd, h1]
  · match l, hl with
    | [], _ => right; exact ⟨_, ⟨by simp, by simp⟩, Or.inl ⟨by simp, by simp⟩, fun f => rfl⟩
    | [a], _ => right; exact ⟨_, ⟨by simp, by simp⟩, Or.inl ⟨by simp, by simp⟩, fun f => rfl⟩
    | [a, b], _ =>
      by_cases h : a ≠ b ∧ a < p ∧ b < p
      · left; left; exact ⟨by simp, a, b, rfl, h⟩
      · right
        by_cases hab : a = b
        · subst hab
          exact ⟨⟨GateOp.or, [a]⟩, ⟨by simp, by simp⟩, Or.inl ⟨by simp, by simp⟩,
            fun f => by simp [ev, GateOp.eval]⟩
        · by_cases ha : a < p
          · have hb : ¬ b < p := by tauto
            exact ⟨⟨GateOp.or, [a]⟩, ⟨by simp, by simp⟩, Or.inl ⟨by simp, by simp⟩,
              fun f => by simp [ev, GateOp.eval, rd, hb]⟩
          · exact ⟨⟨GateOp.or, [b]⟩, ⟨by simp, by simp⟩, Or.inl ⟨by simp, by simp⟩,
              fun f => by simp [ev, GateOp.eval, rd, ha]⟩
  · match l with
    | [] => right; exact ⟨_, ⟨by simp, by simp⟩, Or.inr ⟨rfl, rfl⟩, fun f => rfl⟩
    | a :: t =>
      by_cases ha : a < p
      · left; right; exact ⟨rfl, a, rfl, ha⟩
      · right
        exact ⟨⟨GateOp.and, []⟩, ⟨by simp, by simp⟩, Or.inl ⟨by simp, by simp⟩,
          fun f => by simp [ev, GateOp.eval, rd, ha]⟩

theorem no_elim (N : ℕ) (C : Circuit) (hmin : IsMinimalCircuit N C)
    (hnc : ∃ x x' : Fin N → Bool, circuitFun N C x ≠ circuitFun N C x')
    (E : Circuit) (hE : FanInTwo E) (hf : circuitFun N E = circuitFun N C) (T : Finset ℕ)
    (hT : ∀ d ∈ T, d < E.gates.length ∧ Triv (G E d)) : C.size + T.card ≤ E.size := by
  obtain ⟨D, hD, hDs, hDf⟩ := elim N T.card E T hE (by rw [hf]; exact hnc) rfl hT
  have := hmin.2 D hD (hDf.trans hf)
  omega

theorem all_clean (N : ℕ) (C : Circuit) (hmin : IsMinimalCircuit N C)
    (hnc : ∃ x x' : Fin N → Bool, circuitFun N C x ≠ circuitFun N C x') :
    ∀ j < C.gates.length, Clean (N + j) (G C j) := by
  intro j hj
  have hfit := (fit_iff C).1 hmin.1
  rcases canon (N + j) (G C j) (hfit j hj) with h | ⟨g', hok, htr, hev⟩
  · exact h
  · exfalso
    let C' : Circuit := ⟨mk C.gates.length (fun i => if i = j then g' else G C i), C.output⟩
    have hG : ∀ i < C.gates.length, G C' i = if i = j then g' else G C i := by
      intro i hi; simp only [C', G]; rw [mk_getD, if_pos hi]
    have hfit' : FanInTwo C' := by
      apply fit_mk; intro i hi; split_ifs with h
      · exact hok
      · exact hfit i hi
    have hval : ∀ x, val N C' x = val N C x := by
      intro x; symm; apply sat_unique; intro i
      rw [val_sat N C x i]
      have hl : C'.gates.length = C.gates.length := mk_len _ _
      rw [hl]
      split_ifs with h1 h2
      · rfl
      · rw [hG _ (by omega)]
        split_ifs with h3
        · subst h3; rw [show N + (i - N) = i by omega] at hev; rw [hev]
        · rfl
      · rfl
    have := no_elim N C hmin hnc C' hfit' (by funext x; rw [fun_val, fun_val, hval]) {j}
      (by
        intro d hd; rw [Finset.mem_singleton] at hd; subst hd
        refine ⟨by rw [mk_len]; exact hj, ?_⟩
        rw [hG _ hj, if_pos rfl]; exact htr)
    simp [Circuit.size, C', mk_len] at this

theorem clean_lt (p : ℕ) (g : Gate) (h : Clean p g) (a : ℕ) (ha : SR g a) : a < p := by
  rcases h with ⟨h1, x, y, h2, _, hx, hy⟩ | ⟨h1, x, h2, hx⟩
  · rcases ha with ⟨h3, _⟩ | ⟨_, h3⟩
    · rcases h1 with h1 | h1 <;> rw [h1] at h3 <;> simp at h3
    · rw [h2] at h3; simp at h3; rcases h3 with rfl | rfl <;> assumption
  · rcases ha with ⟨_, h3⟩ | ⟨h3, _⟩
    · rw [h2] at h3; simp at h3; subst h3; exact hx
    · exact absurd h1 h3

theorem val_beyond (N : ℕ) (C : Circuit) (x : Fin N → Bool) (i : ℕ)
    (h : N + C.gates.length ≤ i) : val N C x i = false := by
  rw [val_sat N C x i, dif_neg (by omega), if_neg (by omega)]

theorem rd_full (N : ℕ) (C : Circuit) (x : Fin N → Bool) (a : ℕ) :
    rd (val N C x) (N + C.gates.length) a = val N C x a := by
  unfold rd; split_ifs with h
  · rfl
  · rw [val_beyond N C x a (by omega)]

theorem rd_full' (N : ℕ) (C : Circuit) (x : Fin N → Bool) (a L : ℕ) (h : C.gates.length = L) :
    rd (val N C x) (N + L) a = val N C x a := by
  subst h; exact rd_full N C x a

theorem live (N : ℕ) (C : Circuit) (hmin : IsMinimalCircuit N C) :
    ∀ d < C.gates.length, C.output = N + d ∨
      ∃ j, d < j ∧ j < C.gates.length ∧ SR (G C j) (N + d) := by
  intro d hd
  by_contra hc
  push_neg at hc
  have hf : circuitFun N (del N C d (N + d)) = circuitFun N C := by
    funext x
    apply del_val N C d (N + d) hd x
    · intro j h1 h2
      rw [val_sat N C x (N + j), dif_neg (by omega), if_pos (by omega),
        show N + j - N = j by omega]
      apply ev_congr
      intro a ha
      have hne : a ≠ N + d := by rintro rfl; exact hc.2 j h1 h2 ha
      simp only [rd, Function.update_of_ne hne]
    · intro h; exact absurd h hc.1
  have := hmin.2 _ (del_fit N C d (N + d) hmin.1) hf
  rw [del_size] at this
  simp only [Circuit.size] at this
  omega

theorem out_last (N : ℕ) (C : Circuit) (hmin : IsMinimalCircuit N C)
    (hnc : ∃ x x' : Fin N → Bool, circuitFun N C x ≠ circuitFun N C x')
    (hproj : ∀ i (h : i < N), ∃ x, circuitFun N C x ≠ x ⟨i, h⟩) :
    0 < C.gates.length ∧ C.output = N + C.gates.length - 1 := by
  by_cases h1 : C.output < N
  · exfalso
    obtain ⟨x, hx⟩ := hproj _ h1
    apply hx
    rw [fun_val, val_sat N C x, dif_pos h1]
  by_cases h2 : N + C.gates.length ≤ C.output
  · exfalso
    obtain ⟨x, x', hx⟩ := hnc
    apply hx
    rw [fun_val, fun_val, val_beyond N C x _ h2, val_beyond N C x' _ h2]
  refine ⟨by omega, ?_⟩
  rcases live N C hmin (C.gates.length - 1) (by omega) with h | ⟨j, hj1, hj2, _⟩
  · omega
  · omega


theorem force_prefix (N : ℕ) (C : Circuit) (p : ℕ) (b : Bool) (x : Fin N → Bool) :
    ∀ i, i ≤ p → val N (force N C p b) x i = val N C x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rw [val_sat N (force N C p b) x i, val_sat N C x i, force_len]
    split_ifs with h1 h2
    · rfl
    · rw [force_G _ _ _ _ _ (by omega)]
      unfold fG
      rw [if_neg (fun h => absurd h.1 (by omega))]
      apply ev_ext; intro a; unfold rd; split_ifs with ha
      · exact ih a ha (by omega)
      · rfl
    · rfl

theorem step (N : ℕ) (C : Circuit) (hmin : IsMinimalCircuit N C)
    (hnc : ∃ x x' : Fin N → Bool, circuitFun N C x ≠ circuitFun N C x')
    (p : ℕ) (hp1 : ∀ x, val N C x p = true → circuitFun N C x = true)
    (hr : ∃ j < C.gates.length, SR (G C j) p) :
    ∃ r < C.gates.length, (G C r).op = GateOp.or ∧ (G C r).inputs.length = 2 ∧
      p ∈ (G C r).inputs ∧ ∀ j < C.gates.length, SR (G C j) p → j = r := by
  have hcl := all_clean N C hmin hnc
  have hfit := (fit_iff C).1 hmin.1
  have hlv := live N C hmin
  obtain ⟨r, hrl, hrs⟩ := hr
  have hpr : p < N + r := clean_lt _ _ (hcl r hrl) p hrs
  let E : Circuit := appC N (force N C p false) ⟨GateOp.or, [p, C.output]⟩
  have hEl : E.gates.length = C.gates.length + 1 := by simp [E, appC, force_len]
  have hEfit : FanInTwo E := appC_fit _ _ _ (force_fit _ _ _ _ hmin.1) ⟨by simp, by simp⟩
  have hEf : circuitFun N E = circuitFun N C := by
    funext x
    have hEo : E.output = N + C.gates.length := by simp [E, appC, force_len]
    rw [fun_val, hEo, appC_val, force_len, if_neg (by omega), if_pos rfl]
    simp only [ev, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    rw [rd_full' _ _ _ _ _ (force_len N C p false), rd_full' _ _ _ _ _ (force_len N C p false)]
    by_cases hv : val N C x p = true
    · rw [hp1 x hv, force_prefix N C p false x p le_rfl, hv]; rfl
    · have hv' : val N C x p = false := by simpa using hv
      rw [force_val N C p false hmin.1 x hv', hv']; rfl
  have hGE : ∀ j < C.gates.length, G E j = fG N C p false j := by
    intro j hj
    have : G E j = G (force N C p false) j := by
      simp only [E]; rw [appC_G, force_len, if_pos hj]
    rw [this, force_G _ _ _ _ _ hj]
  have hTr : ∀ j < C.gates.length, SR (G C j) p → Triv (G E j) := by
    intro j hj hs
    rw [hGE j hj]; unfold fG
    rw [if_pos ⟨clean_lt _ _ (hcl j hj) p hs, hs⟩]
    exact forceG_triv _ _ _ (hfit j hj) hs
  by_cases hu : ∃ r2 < C.gates.length, r2 ≠ r ∧ SR (G C r2) p
  · exfalso
    obtain ⟨r2, hr2l, hr2r, hr2s⟩ := hu
    have := no_elim N C hmin hnc E hEfit hEf {r, r2}
      (by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · exact ⟨by omega, hTr _ hrl hrs⟩
        · exact ⟨by omega, hTr _ hr2l hr2s⟩)
    rw [Finset.card_pair (Ne.symm hr2r)] at this
    simp only [Circuit.size] at this
    omega
  push_neg at hu
  have huniq : ∀ j < C.gates.length, SR (G C j) p → j = r := by
    intro j hj hs; by_contra hne; exact hu j hj hne hs
  obtain ⟨hop, hlen⟩ := hfit r hrl
  rcases hop with hop | hop | hop
  rotate_left
  · refine ⟨r, hrl, hop, ?_, ?_, huniq⟩
    · rcases hcl r hrl with ⟨_, a, b, hab, _⟩ | ⟨h1, _⟩
      · rw [hab]; rfl
      · rw [hop] at h1; simp at h1
    · rcases hrs with ⟨h1, _⟩ | ⟨_, h1⟩
      · rw [hop] at h1; simp at h1
      · exact h1
  all_goals exfalso
  all_goals
    obtain ⟨b, hb⟩ : ∃ b : Bool, ∀ f, ev (G E r) f = b := by
      rw [hGE r hrl]; unfold fG; rw [if_pos ⟨hpr, hrs⟩]
      unfold forceG
      rw [hop]
      first | exact ⟨false, fun f => rfl⟩ | exact ⟨true, fun f => rfl⟩
    have hvr : ∀ x, val N E x (N + r) = b := by
      intro x
      rw [val_sat N E x (N + r), dif_neg (by omega), if_pos (by omega),
        show N + r - N = r by omega, hb]
    let E2 := force N E (N + r) b
    have hE2fit : FanInTwo E2 := force_fit _ _ _ _ hEfit
    have hE2f : circuitFun N E2 = circuitFun N C := by
      rw [← hEf]; funext x; rw [fun_val, fun_val, force_val N E (N + r) b hEfit x (hvr x)]; rfl
    obtain ⟨r2, hr2a, hr2b, hr2s⟩ : ∃ r2, r < r2 ∧ r2 < C.gates.length + 1 ∧ SR (G E r2) (N + r) := by
      rcases hlv r hrl with ho | ⟨j, hj1, hj2, hjs⟩
      · refine ⟨C.gates.length, by omega, by omega, ?_⟩
        simp only [E]; rw [appC_G, force_len, if_neg (by omega), if_pos rfl]
        right; refine ⟨by simp, ?_⟩; rw [← ho]; simp
      · refine ⟨j, hj1, by omega, ?_⟩
        rw [hGE j hj2]; unfold fG
        rw [if_neg (fun h => absurd (huniq j hj2 h.2) (by omega))]
        exact hjs
    have hEfit' := (fit_iff E).1 hEfit
    have := no_elim N C hmin hnc E2 hE2fit hE2f {r, r2}
      (by
        intro d hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl
        · refine ⟨by simp only [E2, force_len]; omega, ?_⟩
          apply force_triv _ _ _ _ hEfit _ (by omega)
          exact hTr _ hrl hrs
        · refine ⟨by simp only [E2, force_len]; omega, ?_⟩
          simp only [E2]
          rw [force_G _ _ _ _ _ (by omega)]
          unfold fG
          rw [if_pos ⟨by omega, hr2s⟩]
          exact forceG_triv _ _ _ (hEfit' _ (by omega)) hr2s)
    rw [Finset.card_pair (by omega)] at this
    simp only [Circuit.size, E2, force_len] at this
    omega


theorem agree (N : ℕ) (C : Circuit) (hcl : ∀ j < C.gates.length, Clean (N + j) (G C j))
    (S : ℕ → Prop) (x x' : Fin N → Bool) (hx : ∀ i (h : i < N), ¬ S i → x ⟨i, h⟩ = x' ⟨i, h⟩)
    (hg : ∀ j < C.gates.length, ¬ S (N + j) →
      val N C x (N + j) = val N C x' (N + j) ∨ ∀ a, SR (G C j) a → ¬ S a) :
    ∀ w, ¬ S w → val N C x w = val N C x' w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases h1 : w < N
    · rw [val_sat N C x w, val_sat N C x' w, dif_pos h1, dif_pos h1]; exact hx w h1 hw
    by_cases h2 : w < N + C.gates.length
    · have hj := hg (w - N) (by omega) (by rw [show N + (w - N) = w by omega]; exact hw)
      rw [show N + (w - N) = w by omega] at hj
      rcases hj with hj | hj
      · exact hj
      · rw [val_sat N C x w, val_sat N C x' w, dif_neg h1, dif_neg h1, if_pos h2, if_pos h2]
        apply ev_congr
        intro a ha
        have hlt := clean_lt _ _ (hcl (w - N) (by omega)) a ha
        rw [show N + (w - N) = w by omega] at hlt
        unfold rd; rw [if_pos hlt, if_pos hlt]
        exact ih a hlt (hj a ha)
    · rw [val_beyond N C x w (by omega), val_beyond N C x' w (by omega)]

theorem or_true (g : Gate) (hg : g.op = GateOp.or) (q p : ℕ) (hq : q ∈ g.inputs) (hqp : q < p)
    (f : ℕ → Bool) (hf : f q = true) : ev g (rd f p) = true := by
  rcases g with ⟨op, l⟩
  simp only at hg hq; subst hg
  simp only [ev, GateOp.eval, List.any_map, List.any_eq_true]
  exact ⟨q, hq, by simp [rd, hqp, hf]⟩

def Ch (n : ℕ) (C : Circuit) (m : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ i < m, c i < c (i + 1)) ∧ c m < C.gates.length ∧
  (∀ i ≤ m, (G C (c i)).op = GateOp.or ∧ (G C (c i)).inputs.length = 2) ∧
  n ∈ (G C (c 0)).inputs ∧
  (∀ i < m, n + 1 + c i ∈ (G C (c (i + 1))).inputs) ∧
  (∀ j < C.gates.length, SR (G C j) n → j = c 0) ∧
  (∀ i < m, ∀ j < C.gates.length, SR (G C j) (n + 1 + c i) → j = c (i + 1))

theorem ch_mono (m : ℕ) (c : ℕ → ℕ) (h : ∀ i < m, c i < c (i + 1)) :
    ∀ i j, i < j → j ≤ m → c i < c j := by
  intro i j
  induction j with
  | zero => intro h1; omega
  | succ j ih =>
    intro h1 h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h3 | h3
    · exact lt_trans (ih h3 (by omega)) (h j (by omega))
    · subst h3; exact h i (by omega)

theorem ch_true (n : ℕ) (C : Circuit) (m : ℕ) (c : ℕ → ℕ) (hc : Ch n C m c)
    (hcl : ∀ j < C.gates.length, Clean (n + 1 + j) (G C j))
    (x : Fin (n + 1) → Bool) (hx : val (n + 1) C x n = true) :
    ∀ i ≤ m, val (n + 1) C x (n + 1 + c i) = true := by
  obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := hc
  have hlt : ∀ i ≤ m, c i < C.gates.length := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact lt_trans (ch_mono m c h1 i m h le_rfl) h2
    · rw [h]; exact h2
  intro i
  induction i with
  | zero =>
    intro _
    rw [val_sat _ C x, dif_neg (by omega), if_pos (by have := hlt 0 (by omega); omega),
      show n + 1 + c 0 - (n + 1) = c 0 by omega]
    exact or_true _ (h3 0 (by omega)).1 n _ h4 (by omega) _ hx
  | succ i ih =>
    intro hi
    rw [val_sat _ C x, dif_neg (by omega), if_pos (by have := hlt (i + 1) hi; omega),
      show n + 1 + c (i + 1) - (n + 1) = c (i + 1) by omega]
    exact or_true _ (h3 (i + 1) hi).1 (n + 1 + c i) _ (h5 i (by omega))
      (by have := h1 i (by omega); omega) _ (ih (by omega))


def mkx (n : ℕ) (y : Fin n → Bool) (b : Bool) : Fin (n + 1) → Bool :=
  fun i => if h : i.val < n then y ⟨i.val, h⟩ else b

theorem mkx_last (n : ℕ) (y : Fin n → Bool) (b : Bool) : mkx n y b (Fin.last n) = b := by
  simp [mkx]

theorem mkx_cs (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    (fun i : Fin n => mkx n y b i.castSucc) = y := by
  funext i; simp [mkx]

def Hyp (n : ℕ) (C : Circuit) (H : (Fin n → Bool) → Bool) : Prop :=
  IsMinimalCircuit (n + 1) C ∧ (∃ y y' : Fin n → Bool, H y ≠ H y') ∧
    ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))

theorem Hyp.hmin {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool} (h : Hyp n C H) :
    IsMinimalCircuit (n + 1) C := h.1

theorem Hyp.hH {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool} (h : Hyp n C H) :
    ∃ y y' : Fin n → Bool, H y ≠ H y' := h.2.1

theorem Hyp.hF {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool} (h : Hyp n C H) :
    ∀ x : Fin (n + 1) → Bool,
      circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc)) := h.2.2

theorem Hyp.y01 {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool} (h : Hyp n C H) :
    ∃ y0 y1, H y0 = false ∧ H y1 = true := by
  obtain ⟨y, y', hy⟩ := h.hH
  cases h1 : H y
  · cases h2 : H y'
    · exact absurd (h1.trans h2.symm) hy
    · exact ⟨y, y', h1, h2⟩
  · cases h2 : H y'
    · exact ⟨y', y, h2, h1⟩
    · exact absurd (h1.trans h2.symm) hy

theorem Hyp.nc {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool} (h : Hyp n C H) :
    ∃ x x' : Fin (n + 1) → Bool, circuitFun (n + 1) C x ≠ circuitFun (n + 1) C x' := by
  obtain ⟨y0, _, h0, _⟩ := h.y01
  refine ⟨mkx n y0 false, mkx n y0 true, ?_⟩
  rw [h.hF, h.hF, mkx_last, mkx_last, mkx_cs, mkx_cs, h0]; simp

theorem Hyp.proj {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool} (h : Hyp n C H) :
    ∀ i (hi : i < n + 1), ∃ x, circuitFun (n + 1) C x ≠ x ⟨i, hi⟩ := by
  intro i hi
  obtain ⟨_, y1, _, h1⟩ := h.y01
  by_cases hin : i = n
  · subst hin
    refine ⟨mkx i y1 false, ?_⟩
    rw [h.hF, mkx_last, mkx_cs, h1]
    simp [mkx]
  · refine ⟨fun j => decide (j.val ≠ i), ?_⟩
    rw [h.hF]
    simp only [Fin.val_last]
    simp [Ne.symm hin]

theorem Hyp.out {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool} (h : Hyp n C H) :
    0 < C.gates.length ∧ C.output = n + 1 + C.gates.length - 1 :=
  out_last (n + 1) C h.hmin h.nc h.proj

theorem Hyp.base {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool} (h : Hyp n C H) :
    ∃ c, Ch n C 0 c := by
  obtain ⟨hL0, ho⟩ := h.out
  have hcl := all_clean (n + 1) C h.hmin h.nc
  have hst := step (n + 1) C h.hmin h.nc n
    (by
      intro x hx
      rw [val_sat _ C x n, dif_pos (by omega)] at hx
      rw [h.hF]
      have : x (Fin.last n) = true := hx
      rw [this]; rfl)
    (by
      by_contra hno
      push_neg at hno
      obtain ⟨y0, _, h0, _⟩ := h.y01
      have := agree (n + 1) C hcl (fun w => w = n) (mkx n y0 false) (mkx n y0 true)
        (by intro i hi hin; simp only [mkx]; rw [dif_pos (by omega), dif_pos (by omega)])
        (by intro j hj _; right; intro a ha hna; subst hna; exact hno j hj ha)
        C.output (by omega)
      have e1 := h.hF (mkx n y0 false)
      have e2 := h.hF (mkx n y0 true)
      rw [mkx_last, mkx_cs, h0, fun_val, this] at e1
      rw [mkx_last, mkx_cs, fun_val] at e2
      rw [e1] at e2
      simp at e2)
  obtain ⟨r, hr, h1, h2, h3, h4⟩ := hst
  refine ⟨fun _ => r, fun i hi => absurd hi (by omega), hr, fun i _ => ⟨h1, h2⟩, h3,
    fun i hi => absurd hi (by omega), h4, fun i hi => absurd hi (by omega)⟩

theorem Hyp.extend {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool} (h : Hyp n C H)
    (m : ℕ) (c : ℕ → ℕ) (hc : Ch n C m c) (hne : c m ≠ C.gates.length - 1) :
    ∃ c', Ch n C (m + 1) c' ∧ c m < c' (m + 1) := by
  obtain ⟨hL0, ho⟩ := h.out
  have hcl := all_clean (n + 1) C h.hmin h.nc
  have hlv := live (n + 1) C h.hmin
  have hc' := hc
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc'
  have hmono := ch_mono m c c1
  have hst := step (n + 1) C h.hmin h.nc (n + 1 + c m)
    (by
      intro x hx
      cases hxl : x (Fin.last n)
      · let x1 := Function.update x (Fin.last n) true
        have hF1 := h.hF x1
        simp only [x1, Function.update_self, Bool.true_or] at hF1
        have hv1 : val (n + 1) C x1 n = true := by
          rw [val_sat _ C x1 n, dif_pos (by omega)]
          show x1 (Fin.last n) = true
          simp [x1]
        have ht := ch_true n C m c hc hcl x1 hv1 m le_rfl
        have hag := agree (n + 1) C hcl (fun w => w = n ∨ ∃ i < m, w = n + 1 + c i) x x1
          (by
            intro i hi hS
            simp only [x1]
            rw [Function.update_of_ne]
            intro he; apply hS; left
            have := congrArg Fin.val he; simpa using this)
          (by
            intro j hj hS
            by_cases hjm : j = c m
            · left; subst hjm; rw [hx, ht]
            · right
              intro a ha hSa
              rcases hSa with rfl | ⟨i, hi, rfl⟩
              · have := c6 j hj ha
                subst this
                rcases Nat.eq_zero_or_pos m with hm | hm
                · subst hm; exact hjm rfl
                · exact hS (Or.inr ⟨0, hm, rfl⟩)
              · have := c7 i hi j hj ha
                subst this
                by_cases him : i + 1 = m
                · subst him; exact hjm rfl
                · exact hS (Or.inr ⟨i + 1, by omega, rfl⟩))
          C.output
          (by
            rintro (h1 | ⟨i, hi, h1⟩)
            · omega
            · have := hmono i m hi le_rfl; omega)
        rw [fun_val, hag, ← fun_val, hF1]
      · rw [h.hF, hxl]; rfl)
    (by
      rcases hlv (c m) c2 with h1 | ⟨j, hj1, hj2, hj3⟩
      · omega
      · exact ⟨j, hj2, hj3⟩)
  obtain ⟨r, hr, h1, h2, h3, h4⟩ := hst
  have hrs : SR (G C r) (n + 1 + c m) := Or.inr ⟨by rw [h1]; simp, h3⟩
  have hcr : c m < r := by have := clean_lt _ _ (hcl r hr) _ hrs; omega
  refine ⟨fun i => if i ≤ m then c i else r, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    by_cases him : i < m
    · simp only [if_pos (show i ≤ m by omega), if_pos (show i + 1 ≤ m by omega)]; exact c1 i him
    · simp only [if_pos (show i ≤ m by omega), if_neg (show ¬ i + 1 ≤ m by omega)]
      rw [show i = m by omega]; exact hcr
  · simp only [if_neg (show ¬ m + 1 ≤ m by omega)]; exact hr
  · intro i hi
    by_cases him : i ≤ m
    · simp only [if_pos him]; exact c3 i him
    · simp only [if_neg him]; exact ⟨h1, h2⟩
  · simp only [if_pos (Nat.zero_le m)]; exact c4
  · intro i hi
    by_cases him : i < m
    · simp only [if_pos (show i ≤ m by omega), if_pos (show i + 1 ≤ m by omega)]; exact c5 i him
    · simp only [if_pos (show i ≤ m by omega), if_neg (show ¬ i + 1 ≤ m by omega)]
      rw [show i = m by omega]; exact h3
  · simp only [if_pos (Nat.zero_le m)]; exact c6
  · intro i hi j hj hs
    by_cases him : i < m
    · simp only [if_pos (show i ≤ m by omega), if_pos (show i + 1 ≤ m by omega)] at hs ⊢
      exact c7 i him j hj hs
    · simp only [if_pos (show i ≤ m by omega), if_neg (show ¬ i + 1 ≤ m by omega)] at hs ⊢
      rw [show i = m by omega] at hs; exact h4 j hj hs
  · simp only [if_neg (show ¬ m + 1 ≤ m by omega)]; exact hcr

theorem Hyp.loop {n : ℕ} {C : Circuit} {H : (Fin n → Bool) → Bool} (h : Hyp n C H) :
    ∀ k m c, Ch n C m c → C.gates.length - c m ≤ k →
      ∃ m' c', Ch n C m' c' ∧ c' m' = C.gates.length - 1 := by
  intro k
  induction k with
  | zero => intro m c hc hk; have := hc.2.1; omega
  | succ k ih =>
    intro m c hc hk
    by_cases he : c m = C.gates.length - 1
    · exact ⟨m, c, hc, he⟩
    · obtain ⟨c', hc', hlt⟩ := h.extend m c hc he
      exact ih (m + 1) c' hc' (by have := hc'.2.1; omega)

theorem get_eq (C : Circuit) (j : Fin C.gates.length) : C.gates.get j = G C j.val := by
  unfold G; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt]; rfl

theorem other (p : ℕ) (g : Gate) (hop : g.op = GateOp.or) (hc : Clean p g) (q : ℕ)
    (hq : q ∈ g.inputs) : ∃ w ∈ g.inputs, w ≠ q ∧ w < p := by
  rcases hc with ⟨_, a, b, hab, hne, ha, hb⟩ | ⟨h1, _⟩
  · rw [hab] at hq ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨b, by simp, Ne.symm hne, hb⟩
    · exact ⟨a, by simp, hne, ha⟩
  · rw [hop] at h1; simp at h1

end PEqualNP.Outside.L568H

theorem PEqualNP.Outside.L_meta_568 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (H : (Fin n → Bool) → Bool), PEqualNP.MetaComplexity.IsMinimalCircuit (n + 1) C → (∃ y y' : Fin n → Bool, H y ≠ H y') → (∀ x : Fin (n + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (n + 1) C x = (x (Fin.last n) || H (fun i : Fin n => x i.castSucc))) → ∃ (k : ℕ) (c : Fin (k + 1) → Fin C.gates.length), StrictMono c ∧ (c (Fin.last k)).val + 1 = C.gates.length ∧ C.output = n + 1 + (c (Fin.last k)).val ∧ (∀ i : Fin (k + 1), (C.gates.get (c i)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get (c i)).inputs.length = 2) ∧ n ∈ (C.gates.get (c 0)).inputs ∧ (∀ i : Fin k, n + 1 + (c i.castSucc).val ∈ (C.gates.get (c i.succ)).inputs) ∧ (∀ j : Fin C.gates.length, ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some n ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ n ∈ (C.gates.get j).inputs) → j = c 0) ∧ (∀ (i : Fin k) (j : Fin C.gates.length), ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some (n + 1 + (c i.castSucc).val) ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (n + 1 + (c i.castSucc).val) ∈ (C.gates.get j).inputs) → j = c i.succ) ∧ (∀ j : Fin C.gates.length, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + j.val) ↔ ∃ i : Fin (k + 1), c i = j) ∧ (∃ w ∈ (C.gates.get (c 0)).inputs, w ≠ n ∧ w < n + 1 + (c 0).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) ∧ (∀ i : Fin k, ∃ w ∈ (C.gates.get (c i.succ)).inputs, w ≠ n + 1 + (c i.castSucc).val ∧ w ≠ n ∧ w < n + 1 + (c i.succ).val ∧ ¬ Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n w) := by
  intro n C H hmin hH hF
  have h : PEqualNP.Outside.L568H.Hyp n C H := ⟨hmin, hH, hF⟩
  obtain ⟨c0, hc0⟩ := h.base
  obtain ⟨k, c, hc, hck⟩ := h.loop _ 0 c0 hc0 le_rfl
  obtain ⟨hL0, ho⟩ := h.out
  have hcl := PEqualNP.Outside.L568H.all_clean (n + 1) C hmin h.nc
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := hc
  have hmono := PEqualNP.Outside.L568H.ch_mono k c c1
  have hle : ∀ a b, a ≤ b → b ≤ k → c a ≤ c b := by
    intro a b hab hb
    rcases Nat.lt_or_eq_of_le hab with h1 | h1
    · exact le_of_lt (hmono a b h1 hb)
    · rw [h1]
  have hlt : ∀ i ≤ k, c i < C.gates.length := by
    intro i hi; have := hle i k hi le_rfl; omega
  have hge := PEqualNP.Outside.L568H.get_eq C
  have key : ∀ b, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n b → ∃ i ≤ k, b = n + 1 + c i := by
    intro b hb
    induction hb with
    | single hab =>
      obtain ⟨j, rfl, hs⟩ := hab
      rw [hge] at hs
      exact ⟨0, Nat.zero_le _, by rw [c6 j j.isLt hs]⟩
    | tail _ hbc ih =>
      obtain ⟨i, hi, rfl⟩ := ih
      obtain ⟨j, rfl, hs⟩ := hbc
      rw [hge] at hs
      by_cases hik : i < k
      · exact ⟨i + 1, hik, by rw [c7 i hik j j.isLt hs]⟩
      · exfalso
        have h1 := PEqualNP.Outside.L568H.clean_lt _ _ (hcl j j.isLt) _ hs
        have h2 : i = k := by omega
        subst h2
        have := j.isLt
        omega
  have hreach : ∀ i ≤ k, Relation.TransGen (fun a b : ℕ => ∃ j : Fin C.gates.length, b = n + 1 + j.val ∧ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (C.gates.get j).inputs.head? = some a ∨ (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ a ∈ (C.gates.get j).inputs)) n (n + 1 + c i) := by
    intro i
    induction i with
    | zero =>
      intro _
      apply Relation.TransGen.single
      refine ⟨⟨c 0, hlt 0 (Nat.zero_le _)⟩, rfl, ?_⟩
      rw [hge]
      right; exact ⟨by rw [(c3 0 (Nat.zero_le _)).1]; simp, c4⟩
    | succ i ih =>
      intro hi
      apply Relation.TransGen.tail (ih (by omega))
      refine ⟨⟨c (i + 1), hlt (i + 1) hi⟩, rfl, ?_⟩
      rw [hge]
      right; exact ⟨by rw [(c3 (i + 1) hi).1]; simp, c5 i (by omega)⟩
  have h0 : ((0 : Fin (k + 1)) : ℕ) = 0 := Fin.val_zero (k + 1)
  refine ⟨k, fun i => ⟨c i, hlt i (by omega)⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    show c a < c b
    exact hmono a b hab (by omega)
  · show c k + 1 = C.gates.length
    omega
  · show C.output = n + 1 + c k
    omega
  · intro i
    rw [hge]
    exact c3 i (by omega)
  · rw [hge]
    show n ∈ (PEqualNP.Outside.L568H.G C (c ((0 : Fin (k + 1)) : ℕ))).inputs
    rw [h0]; exact c4
  · intro i
    rw [hge]
    exact c5 i i.isLt
  · intro j hs
    rw [hge] at hs
    apply Fin.ext
    show j.val = c ((0 : Fin (k + 1)) : ℕ)
    rw [h0]
    exact c6 j j.isLt hs
  · intro i j hs
    rw [hge] at hs
    apply Fin.ext
    exact c7 i i.isLt j j.isLt hs
  · intro j
    constructor
    · intro hT
      obtain ⟨i, hi, he⟩ := key _ hT
      exact ⟨⟨i, by omega⟩, Fin.ext (by show c i = j.val; omega)⟩
    · rintro ⟨i, rfl⟩
      exact hreach i (by omega)
  · rw [hge]
    show ∃ w ∈ (PEqualNP.Outside.L568H.G C (c ((0 : Fin (k + 1)) : ℕ))).inputs, _
    rw [h0]
    obtain ⟨w, hw, hwn, hwl⟩ := PEqualNP.Outside.L568H.other _ _ (c3 0 (Nat.zero_le _)).1
      (hcl (c 0) (hlt 0 (Nat.zero_le _))) n c4
    refine ⟨w, hw, hwn, ?_, ?_⟩
    · show w < n + 1 + c ((0 : Fin (k + 1)) : ℕ)
      rw [h0]; exact hwl
    · intro hT
      obtain ⟨i, hi, rfl⟩ := key _ hT
      have := hle 0 i (Nat.zero_le _) hi
      rw [h0] at *
      omega
  · intro i
    rw [hge]
    obtain ⟨w, hw, hwn, hwl⟩ := PEqualNP.Outside.L568H.other _ _ (c3 (i + 1) i.isLt).1
      (hcl (c (i + 1)) (hlt (i + 1) i.isLt)) _ (c5 i i.isLt)
    have hsr : PEqualNP.Outside.L568H.SR (PEqualNP.Outside.L568H.G C (c (i + 1))) w :=
      Or.inr ⟨by rw [(c3 (i + 1) i.isLt).1]; simp, hw⟩
    refine ⟨w, hw, hwn, ?_, hwl, ?_⟩
    · rintro rfl
      have := c6 _ (hlt (i + 1) i.isLt) hsr
      have := hmono 0 (i + 1) (by omega) i.isLt
      omega
    · intro hT
      obtain ⟨i', hi', rfl⟩ := key _ hT
      have hii : i' < i.val + 1 := by
        by_contra hc'
        have := hle (i + 1) i' (by omega) hi'
        omega
      by_cases he : i' = i.val
      · subst he; exact hwn rfl
      · have := c7 i' (by omega) _ (hlt (i + 1) i.isLt) hsr
        have := hmono (i' + 1) (i.val + 1) (by omega) i.isLt
        omega
