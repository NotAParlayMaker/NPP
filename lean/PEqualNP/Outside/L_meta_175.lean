import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_175_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- One evaluation step: the gate adds one wire. -/
def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

/-- The wires a gate really reads: a NOT gate reads only its first. -/
def trunc (op : GateOp) (l : List ℕ) : List ℕ :=
  match op with
  | GateOp.not => l.take 1
  | _ => l

theorem eval_trunc (op : GateOp) (l : List ℕ) (f : ℕ → Bool) :
    op.eval ((trunc op l).map f) = op.eval (l.map f) := by
  cases op with
  | not => cases l <;> simp [trunc, GateOp.eval]
  | _ => rfl

theorem trunc_length (op : GateOp) (l : List ℕ) : (trunc op l).length ≤ l.length := by
  cases op <;> simp [trunc]

theorem trunc_not_length (l : List ℕ) : (trunc GateOp.not l).length ≤ 1 := by
  simp [trunc]

/-! ### From a circuit for `g` to a circuit for the contraction -/

/-- The new name of a wire: two wires are inserted at position `n`. -/
def rel (n i : ℕ) : ℕ := if i < n then i else i + 2

def relG (n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rel n)⟩

theorem getD_rel (xs rest : List Bool) (z1 z2 z : Bool) (i : ℕ) :
    (xs ++ z1 :: z2 :: z :: rest).getD (rel xs.length i) false
      = (xs ++ z :: rest).getD i false := by
  unfold rel
  by_cases h : i < xs.length
  · rw [if_pos h, List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
  · rw [if_neg h]
    have h1 : xs.length ≤ i := Nat.le_of_not_lt h
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ h1]
    have : i + 2 - xs.length = (i - xs.length) + 2 := by omega
    rw [this]
    simp [List.getD_eq_getElem?_getD]

theorem up_spec (xs : List Bool) (z1 z2 z : Bool) (gs : List Gate) :
    ∀ rest : List Bool, ∃ rest' : List Bool,
      (gs.map (relG xs.length)).foldl stp (xs ++ z1 :: z2 :: z :: rest)
          = xs ++ z1 :: z2 :: z :: rest' ∧
        gs.foldl stp (xs ++ z :: rest) = xs ++ z :: rest' := by
  induction gs with
  | nil => intro rest; exact ⟨rest, rfl, rfl⟩
  | cons g gs ih =>
    intro rest
    obtain ⟨rest', h1, h2⟩ :=
      ih (rest ++ [g.op.eval (g.inputs.map fun i => (xs ++ z :: rest).getD i false)])
    refine ⟨rest', ?_, ?_⟩
    · rw [← h1]
      simp only [List.map_cons, List.foldl_cons]
      congr 1
      simp only [stp, relG, List.map_map]
      have : ((fun i => (xs ++ z1 :: z2 :: z :: rest).getD i false) ∘ rel xs.length)
          = fun i => (xs ++ z :: rest).getD i false := by
        funext i
        exact getD_rel xs rest z1 z2 z i
      rw [this]
      simp
    · rw [← h2]
      simp only [List.foldl_cons]
      congr 1
      simp [stp]

/-! ### From a circuit for the contraction to a circuit for `g` -/

/-- What an old wire is in the new circuit: a constant, or a wire. -/
inductive Rep where
  | c (b : Bool)
  | w (i : ℕ)

def Rep.val (W : List Bool) : Rep → Bool
  | Rep.c b => b
  | Rep.w i => W.getD i false

def Rep.ok (k : ℕ) : Rep → Prop
  | Rep.c _ => True
  | Rep.w i => i < k

def Rep.isW : Rep → Bool
  | Rep.c _ => false
  | Rep.w _ => true

def Rep.idx : Rep → ℕ
  | Rep.c _ => 0
  | Rep.w i => i

theorem Rep.ok_mono {k k' : ℕ} (h : k ≤ k') (r : Rep) (hr : r.ok k) : r.ok k' := by
  cases r with
  | c b => trivial
  | w i => exact Nat.lt_of_lt_of_le hr h

theorem Rep.val_append (W t : List Bool) (r : Rep) (hr : r.ok W.length) :
    r.val (W ++ t) = r.val W := by
  cases r with
  | c b => rfl
  | w i => exact List.getD_append _ _ _ _ hr

/-- The value of a gate whose inputs are known as `rs`, without a new gate when a constant
is among them. -/
def stepC (op : GateOp) (rs : List Rep) : Rep :=
  match op, rs with
  | GateOp.not, [Rep.c b] => Rep.c (!b)
  | GateOp.and, [Rep.c b] => Rep.c b
  | GateOp.and, [Rep.c b, r] => if b then r else Rep.c false
  | GateOp.and, [r, Rep.c b] => if b then r else Rep.c false
  | GateOp.or, [Rep.c b] => Rep.c b
  | GateOp.or, [Rep.c b, r] => if b then Rep.c true else r
  | GateOp.or, [r, Rep.c b] => if b then Rep.c true else r
  | _, _ => Rep.c false

def stepR (op : GateOp) (rs : List Rep) (k : ℕ) : Rep × Option Gate :=
  if rs.all Rep.isW then (Rep.w k, some ⟨op, rs.map Rep.idx⟩) else (stepC op rs, none)

def Wnext (W : List Bool) : Option Gate → List Bool
  | none => W
  | some g => stp W g

def knext (k : ℕ) : Option Gate → ℕ
  | none => k
  | some _ => k + 1

theorem Wnext_length (W : List Bool) (o : Option Gate) :
    (Wnext W o).length = knext W.length o := by
  cases o <;> simp [Wnext, knext, stp]

theorem Wnext_append (W : List Bool) (o : Option Gate) : ∃ t, Wnext W o = W ++ t := by
  cases o with
  | none => exact ⟨[], by simp [Wnext]⟩
  | some g => exact ⟨_, rfl⟩

theorem stepC_spec (op : GateOp) (rs : List Rep) (W : List Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : rs.length ≤ 2) (hnot : op = GateOp.not → rs.length ≤ 1)
    (hok : ∀ r ∈ rs, r.ok W.length) (hc : rs.all Rep.isW = false) :
    (stepC op rs).ok W.length ∧ (stepC op rs).val W = op.eval (rs.map (Rep.val W)) := by
  rcases rs with _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, rs⟩⟩⟩
  · simp at hc
  · rcases hop with rfl | rfl | rfl <;> cases r1 <;>
      simp_all [stepC, Rep.isW, Rep.ok, Rep.val, GateOp.eval]
  · rcases hop with rfl | rfl | rfl
    · cases r1 with
      | c b1 =>
        cases r2 with
        | c b2 => cases b1 <;> cases b2 <;> simp [stepC, Rep.ok, Rep.val, GateOp.eval]
        | w i2 =>
          have h2 : (Rep.w i2).ok W.length := hok _ (by simp)
          cases b1 <;> simp_all [stepC, Rep.ok, Rep.val, GateOp.eval]
      | w i1 =>
        have h1 : (Rep.w i1).ok W.length := hok _ (by simp)
        cases r2 with
        | c b2 => cases b2 <;> simp_all [stepC, Rep.ok, Rep.val, GateOp.eval]
        | w i2 => simp [Rep.isW] at hc
    · cases r1 with
      | c b1 =>
        cases r2 with
        | c b2 => cases b1 <;> cases b2 <;> simp [stepC, Rep.ok, Rep.val, GateOp.eval]
        | w i2 =>
          have h2 : (Rep.w i2).ok W.length := hok _ (by simp)
          cases b1 <;> simp_all [stepC, Rep.ok, Rep.val, GateOp.eval]
      | w i1 =>
        have h1 : (Rep.w i1).ok W.length := hok _ (by simp)
        cases r2 with
        | c b2 => cases b2 <;> simp_all [stepC, Rep.ok, Rep.val, GateOp.eval]
        | w i2 => simp [Rep.isW] at hc
    · have := hnot rfl
      simp at this
  · simp at hlen

theorem stepR_spec (op : GateOp) (rs : List Rep) (W : List Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hlen : rs.length ≤ 2) (hnot : op = GateOp.not → rs.length ≤ 1)
    (hok : ∀ r ∈ rs, r.ok W.length) :
    (stepR op rs W.length).1.ok (Wnext W (stepR op rs W.length).2).length ∧
      (stepR op rs W.length).1.val (Wnext W (stepR op rs W.length).2)
        = op.eval (rs.map (Rep.val W)) := by
  by_cases hc : rs.all Rep.isW = true
  · have hmap : (rs.map Rep.idx).map (fun i => W.getD i false) = rs.map (Rep.val W) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro r hr
      have := List.all_eq_true.mp hc r hr
      cases r with
      | c b => simp [Rep.isW] at this
      | w i => rfl
    simp only [stepR, hc, if_true, Wnext, stp, hmap]
    constructor
    · simp [Rep.ok]
    · simp [Rep.val, List.getD_eq_getElem?_getD]
  · have hc' : rs.all Rep.isW = false := by simpa using hc
    simp only [stepR, hc', Wnext]
    exact stepC_spec op rs W hop hlen hnot hok hc'

theorem stepR_snd_some (op : GateOp) (rs : List Rep) (k : ℕ) (g : Gate)
    (h : (stepR op rs k).2 = some g) : g = ⟨op, rs.map Rep.idx⟩ := by
  unfold stepR at h
  split at h
  · simpa using h.symm
  · simp at h

theorem stepR_snd_none (op : GateOp) (rs : List Rep) (k : ℕ)
    (h : rs.all Rep.isW = false) : (stepR op rs k).2 = none := by
  simp [stepR, h]

/-- The representations of the wires a gate reads. -/
def reads (reps : List Rep) (g : Gate) : List Rep :=
  (trunc g.op g.inputs).map fun i => reps.getD i (Rep.c false)

def simG : List Gate → List Rep → ℕ → List Gate
  | [], _, _ => []
  | g :: gs, reps, k =>
    (stepR g.op (reads reps g) k).2.toList ++
      simG gs (reps ++ [(stepR g.op (reads reps g) k).1]) (knext k (stepR g.op (reads reps g) k).2)

def simR : List Gate → List Rep → ℕ → List Rep
  | [], reps, _ => reps
  | g :: gs, reps, k =>
    simR gs (reps ++ [(stepR g.op (reads reps g) k).1]) (knext k (stepR g.op (reads reps g) k).2)

theorem foldl_toList (W : List Bool) (o : Option Gate) (l : List Gate) :
    (o.toList ++ l).foldl stp W = l.foldl stp (Wnext W o) := by
  cases o <;> simp [Wnext]

def Good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem sim_spec (gs : List Gate) :
    ∀ (reps : List Rep) (Wo Wn : List Bool), (∀ g ∈ gs, Good g) →
      reps.length = Wo.length →
      (∀ i, (reps.getD i (Rep.c false)).ok Wn.length ∧
        (reps.getD i (Rep.c false)).val Wn = Wo.getD i false) →
      ∀ i, ((simR gs reps Wn.length).getD i (Rep.c false)).ok
            ((simG gs reps Wn.length).foldl stp Wn).length ∧
          ((simR gs reps Wn.length).getD i (Rep.c false)).val
            ((simG gs reps Wn.length).foldl stp Wn) = (gs.foldl stp Wo).getD i false := by
  induction gs with
  | nil =>
    intro reps Wo Wn _ _ h i
    simpa [simR, simG] using h i
  | cons g gs ih =>
    intro reps Wo Wn hgood hlen h
    have hg : Good g := hgood g (by simp)
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
      have := hg.1
      simpa using this
    have hrl : (reads reps g).length ≤ 2 := by
      simp only [reads, List.length_map]
      exact le_trans (trunc_length _ _) hg.2
    have hrn : g.op = GateOp.not → (reads reps g).length ≤ 1 := by
      intro e
      simp only [reads, List.length_map, e]
      exact trunc_not_length _
    have hrok : ∀ r ∈ reads reps g, r.ok Wn.length := by
      intro r hr
      simp only [reads, List.mem_map] at hr
      obtain ⟨i, _, rfl⟩ := hr
      exact (h i).1
    have hsp := stepR_spec g.op (reads reps g) Wn hop hrl hrn hrok
    have hval : g.op.eval ((reads reps g).map (Rep.val Wn))
        = g.op.eval (g.inputs.map fun i => Wo.getD i false) := by
      rw [← eval_trunc g.op g.inputs (fun i => Wo.getD i false)]
      simp only [reads, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (h i).2
    obtain ⟨t, ht⟩ := Wnext_append Wn (stepR g.op (reads reps g) Wn.length).2
    have hlen' : (reps ++ [(stepR g.op (reads reps g) Wn.length).1]).length
        = (stp Wo g).length := by
      simp [stp, hlen]
    have hinv : ∀ i,
        ((reps ++ [(stepR g.op (reads reps g) Wn.length).1]).getD i (Rep.c false)).ok
            (Wnext Wn (stepR g.op (reads reps g) Wn.length).2).length ∧
          ((reps ++ [(stepR g.op (reads reps g) Wn.length).1]).getD i (Rep.c false)).val
            (Wnext Wn (stepR g.op (reads reps g) Wn.length).2) = (stp Wo g).getD i false := by
      intro i
      rcases lt_trichotomy i reps.length with hi | hi | hi
      · rw [List.getD_append _ _ _ _ hi]
        have hi' : i < Wo.length := hlen ▸ hi
        simp only [stp]
        rw [List.getD_append _ _ _ _ hi']
        constructor
        · apply Rep.ok_mono _ _ (h i).1
          rw [ht]; simp
        · rw [ht, Rep.val_append _ _ _ (h i).1]
          exact (h i).2
      · subst hi
        have e1 : (reps ++ [(stepR g.op (reads reps g) Wn.length).1]).getD reps.length
            (Rep.c false) = (stepR g.op (reads reps g) Wn.length).1 := by
          simp [List.getD_eq_getElem?_getD]
        have e2 : (stp Wo g).getD reps.length false
            = g.op.eval (g.inputs.map fun i => Wo.getD i false) := by
          simp [stp, hlen, List.getD_eq_getElem?_getD]
        rw [e1, e2, ← hval]
        exact hsp
      · have e1 : (reps ++ [(stepR g.op (reads reps g) Wn.length).1]).getD i
            (Rep.c false) = Rep.c false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
          rfl
        have e2 : (stp Wo g).getD i false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [stp]; omega)]
          rfl
        rw [e1, e2]
        exact ⟨trivial, rfl⟩
    have key := ih (reps ++ [(stepR g.op (reads reps g) Wn.length).1]) (stp Wo g)
      (Wnext Wn (stepR g.op (reads reps g) Wn.length).2)
      (fun g' hg' => hgood g' (by simp [hg'])) hlen' hinv
    intro i
    simp only [simR, simG, List.foldl_cons, foldl_toList]
    rw [Wnext_length] at key
    exact key i

theorem simG_good (gs : List Gate) :
    ∀ (reps : List Rep) (k : ℕ), (∀ g ∈ gs, Good g) → ∀ g' ∈ simG gs reps k, Good g' := by
  induction gs with
  | nil => intro reps k _ g' hg'; simp [simG] at hg'
  | cons g gs ih =>
    intro reps k hgood g' hg'
    simp only [simG, List.mem_append] at hg'
    rcases hg' with hg' | hg'
    · have hs : (stepR g.op (reads reps g) k).2 = some g' := by
        cases hx : (stepR g.op (reads reps g) k).2 with
        | none => simp [hx] at hg'
        | some a =>
          simp [hx] at hg'
          rw [hg']
      have := stepR_snd_some _ _ _ _ hs
      have hg : Good g := hgood g (by simp)
      subst this
      refine ⟨hg.1, ?_⟩
      simp only [reads, List.length_map]
      exact le_trans (trunc_length _ _) hg.2
    · exact ih _ _ (fun g'' h'' => hgood g'' (by simp [h''])) g' hg'

theorem simG_len_le (gs : List Gate) :
    ∀ (reps : List Rep) (k : ℕ), (simG gs reps k).length ≤ gs.length := by
  induction gs with
  | nil => intro reps k; simp [simG]
  | cons g gs ih =>
    intro reps k
    simp only [simG, List.length_append, List.length_cons]
    have := ih (reps ++ [(stepR g.op (reads reps g) k).1])
      (knext k (stepR g.op (reads reps g) k).2)
    have h1 : (stepR g.op (reads reps g) k).2.toList.length ≤ 1 := by
      cases (stepR g.op (reads reps g) k).2 <;> simp
    omega

theorem getElem?_append_of_some {α : Type} (l t : List α) (i : ℕ) (x : α)
    (h : l[i]? = some x) : (l ++ t)[i]? = some x := by
  obtain ⟨hi, hx⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem?_append_left hi]
  exact h

theorem simG_len_lt (L : ℕ) (b : Bool) (gs : List Gate) :
    ∀ (reps : List Rep) (k : ℕ), reps[L]? = some (Rep.c b) →
      (∃ g ∈ gs, L ∈ trunc g.op g.inputs) → (simG gs reps k).length < gs.length := by
  induction gs with
  | nil => intro reps k _ h; simp at h
  | cons g gs ih =>
    intro reps k hL hex
    simp only [simG, List.length_append, List.length_cons]
    have hle := simG_len_le gs (reps ++ [(stepR g.op (reads reps g) k).1])
      (knext k (stepR g.op (reads reps g) k).2)
    have h1 : (stepR g.op (reads reps g) k).2.toList.length ≤ 1 := by
      cases (stepR g.op (reads reps g) k).2 <;> simp
    by_cases hg : L ∈ trunc g.op g.inputs
    · have hall : (reads reps g).all Rep.isW = false := by
        rw [List.all_eq_false]
        refine ⟨Rep.c b, ?_, by simp [Rep.isW]⟩
        simp only [reads, List.mem_map]
        refine ⟨L, hg, ?_⟩
        simp [List.getD_eq_getElem?_getD, hL]
      have := stepR_snd_none g.op (reads reps g) k hall
      rw [this] at hle ⊢
      simp
      omega
    · have hex' : ∃ g' ∈ gs, L ∈ trunc g'.op g'.inputs := by
        obtain ⟨g', hg', hL'⟩ := hex
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · exact absurd hL' hg
        · exact ⟨g', hg', hL'⟩
      have := ih (reps ++ [(stepR g.op (reads reps g) k).1])
        (knext k (stepR g.op (reads reps g) k).2)
        (getElem?_append_of_some _ _ _ _ hL) hex'
      omega

theorem simR_keep (L : ℕ) (x : Rep) (gs : List Gate) :
    ∀ (reps : List Rep) (k : ℕ), reps[L]? = some x → (simR gs reps k)[L]? = some x := by
  induction gs with
  | nil => intro reps k h; simpa [simR] using h
  | cons g gs ih =>
    intro reps k h
    simp only [simR]
    exact ih _ _ (getElem?_append_of_some _ _ _ _ h)

/-- A wire that no gate reads does not matter, away from itself. -/
theorem indep (L : ℕ) (gs : List Gate) :
    ∀ (Wa Wb : List Bool), Wa.length = Wb.length →
      (∀ i, i ≠ L → Wa.getD i false = Wb.getD i false) →
      (∀ g ∈ gs, L ∉ trunc g.op g.inputs) →
      ∀ i, i ≠ L → (gs.foldl stp Wa).getD i false = (gs.foldl stp Wb).getD i false := by
  induction gs with
  | nil => intro Wa Wb _ h _ i hi; simpa using h i hi
  | cons g gs ih =>
    intro Wa Wb hlen h hno
    simp only [List.foldl_cons]
    have hv : g.op.eval (g.inputs.map fun i => Wa.getD i false)
        = g.op.eval (g.inputs.map fun i => Wb.getD i false) := by
      rw [← eval_trunc g.op g.inputs (fun i => Wa.getD i false),
        ← eval_trunc g.op g.inputs (fun i => Wb.getD i false)]
      congr 1
      apply List.map_congr_left
      intro i hi
      apply h
      rintro rfl
      exact hno g (by simp) hi
    apply ih
    · simp [stp, hlen]
    · intro i hi
      simp only [stp, hv]
      by_cases hlt : i < Wa.length
      · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hlen ▸ hlt)]
        exact h i hi
      · have hge : Wa.length ≤ i := Nat.le_of_not_lt hlt
        rw [List.getD_append_right _ _ _ _ hge, List.getD_append_right _ _ _ _ (hlen ▸ hge),
          hlen]
    · intro g' hg'
      exact hno g' (by simp [hg'])

/-- The first representations: every input is itself, the last one is the constant `true`. -/
def reps0 (m : ℕ) : List Rep := (List.range m).map Rep.w ++ [Rep.c true]

theorem reps0_last (m : ℕ) : (reps0 m)[m]? = some (Rep.c true) := by
  simp [reps0]

theorem reps0_inv (m : ℕ) (inp : List Bool) (hm : inp.length = m) :
    ∀ i, ((reps0 m).getD i (Rep.c false)).ok inp.length ∧
      ((reps0 m).getD i (Rep.c false)).val inp = (inp ++ [true]).getD i false := by
  intro i
  rcases lt_trichotomy i m with hi | hi | hi
  · have e : (reps0 m).getD i (Rep.c false) = Rep.w i := by
      simp [reps0, List.getD_eq_getElem?_getD, List.getElem?_append, hi]
    rw [e, List.getD_append _ _ _ _ (hm ▸ hi)]
    exact ⟨hm ▸ hi, rfl⟩
  · subst hi
    have e : (reps0 i).getD i (Rep.c false) = Rep.c true := by
      simp [List.getD_eq_getElem?_getD, reps0_last]
    rw [e]
    refine ⟨trivial, ?_⟩
    simp [Rep.val, List.getD_eq_getElem?_getD, hm]
  · have e : (reps0 m).getD i (Rep.c false) = Rep.c false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [reps0]; omega)]
      rfl
    rw [e]
    refine ⟨trivial, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

theorem ofFn_snoc {m : ℕ} (y : Fin m → Bool) (z : Bool) :
    List.ofFn (Fin.snoc y z : Fin (m + 1) → Bool) = List.ofFn y ++ [z] := by
  rw [List.ofFn_succ']
  simp [List.concat_eq_append]

end PEqualNP.Outside.L_meta_175_aux

open PEqualNP.Outside.L_meta_175_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_175 : ∀ (n s : ℕ) (g : (Fin (n + 1) → Bool) → Bool), (∃ y : Fin n → Bool, g (Fin.snoc y false) ≠ g (Fin.snoc y true)) → (PEqualNP.MetaComplexity.HasCircuitSize (n + 2) (fun x : Fin (n + 2) → Bool => g (Fin.snoc (fun i : Fin n => x i.castSucc.castSucc) (x (Fin.last n).castSucc && x (Fin.last (n + 1))))) (s + 1) ↔ PEqualNP.MetaComplexity.HasCircuitSize (n + 1) g s) := by
  intro n s g hdep
  obtain ⟨y, hy⟩ := hdep
  constructor
  · rintro ⟨C, hF, hsz, hC⟩
    -- the value of `C` when the last input is `b`
    have hCb : ∀ (x : Fin (n + 1) → Bool) (b : Bool),
        (C.gates.foldl stp (List.ofFn x ++ [b])).getD C.output false
          = g (Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n) && b)) := by
      intro x b
      have := hC (Fin.snoc x b)
      rw [ofFn_snoc] at this
      simpa [Circuit.eval, wires_eq] using this
    have hgood : ∀ g' ∈ C.gates, Good g' := hF
    have hsim : ∀ (x : Fin (n + 1) → Bool) (i : ℕ),
        ((simR C.gates (reps0 (n + 1)) (n + 1)).getD i (Rep.c false)).val
            ((simG C.gates (reps0 (n + 1)) (n + 1)).foldl stp (List.ofFn x))
          = (C.gates.foldl stp (List.ofFn x ++ [true])).getD i false := by
      intro x i
      have h := sim_spec C.gates (reps0 (n + 1)) (List.ofFn x ++ [true]) (List.ofFn x) hgood
        (by simp [reps0]) (reps0_inv (n + 1) (List.ofFn x) (by simp)) i
      simp only [List.length_ofFn] at h
      exact h.2
    have hgx : ∀ x : Fin (n + 1) → Bool,
        g (Fin.snoc (fun i : Fin n => x i.castSucc) (x (Fin.last n) && true)) = g x := by
      intro x
      congr 1
      simp only [Bool.and_true]
      exact Fin.snoc_init_self x
    cases hro : (simR C.gates (reps0 (n + 1)) (n + 1)).getD C.output (Rep.c false) with
    | c b =>
      exfalso
      have hconst : ∀ x : Fin (n + 1) → Bool, g x = b := by
        intro x
        have h := hsim x C.output
        rw [hro, hCb, hgx] at h
        exact h.symm
      exact hy ((hconst _).trans (hconst _).symm)
    | w j =>
      refine ⟨⟨simG C.gates (reps0 (n + 1)) (n + 1), j⟩, simG_good _ _ _ hgood, ?_, ?_⟩
      · have hne : C.output ≠ n + 1 := by
          intro e
          have hk := simR_keep (n + 1) (Rep.c true) C.gates (reps0 (n + 1)) (n + 1)
            (reps0_last (n + 1))
          rw [e, List.getD_eq_getElem?_getD, hk] at hro
          simp at hro
        have hex : ∃ g' ∈ C.gates, (n + 1) ∈ trunc g'.op g'.inputs := by
          by_contra hno
          push Not at hno
          have hi := indep (n + 1) C.gates
            (List.ofFn (Fin.snoc y true : Fin (n + 1) → Bool) ++ [false])
            (List.ofFn (Fin.snoc y true : Fin (n + 1) → Bool) ++ [true])
            (by simp)
            (by
              intro i hi
              by_cases hlt : i < n + 1
              · rw [List.getD_append _ _ _ _ (by simpa using hlt),
                  List.getD_append _ _ _ _ (by simpa using hlt)]
              · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                  List.getElem?_eq_none (by simp; omega),
                  List.getElem?_eq_none (by simp; omega)])
            hno C.output hne
          rw [hCb, hCb] at hi
          simp only [Fin.snoc_last, Fin.snoc_castSucc, Bool.and_false, Bool.and_true] at hi
          exact hy hi
        have hlt := simG_len_lt (n + 1) true C.gates (reps0 (n + 1)) (n + 1)
          (reps0_last (n + 1)) hex
        have : C.gates.length ≤ s + 1 := hsz
        show (simG C.gates (reps0 (n + 1)) (n + 1)).length ≤ s
        omega
      · intro x
        have h := hsim x C.output
        rw [hro, hCb, hgx] at h
        simpa [Circuit.eval, wires_eq, Rep.val] using h
  · rintro ⟨D, hF, hsz, hD⟩
    refine ⟨⟨⟨GateOp.and, [n, n + 1]⟩ :: D.gates.map (relG n), rel n D.output⟩, ?_, ?_, ?_⟩
    · intro g' hg'
      simp only [List.mem_cons, List.mem_map] at hg'
      rcases hg' with rfl | ⟨g0, hg0, rfl⟩
      · simp
      · have := hF g0 hg0
        exact ⟨this.1, by simpa [relG] using this.2⟩
    · have : D.gates.length ≤ s := hsz
      show ((⟨GateOp.and, [n, n + 1]⟩ : Gate) :: D.gates.map (relG n)).length ≤ s + 1
      simp
      omega
    · intro X
      have hX : List.ofFn X = List.ofFn (fun i : Fin n => X i.castSucc.castSucc)
          ++ [X (Fin.last n).castSucc, X (Fin.last (n + 1))] := by
        rw [List.ofFn_succ', List.ofFn_succ']
        simp [List.concat_eq_append]
      have hlen : (List.ofFn (fun i : Fin n => X i.castSucc.castSucc)).length = n := by simp
      have hD' := hD (Fin.snoc (fun i : Fin n => X i.castSucc.castSucc)
        (X (Fin.last n).castSucc && X (Fin.last (n + 1))))
      rw [ofFn_snoc] at hD'
      beta_reduce
      rw [← hD']
      generalize List.ofFn (fun i : Fin n => X i.castSucc.castSucc) = xs at hX hlen
      generalize X (Fin.last n).castSucc = z1 at hX
      generalize X (Fin.last (n + 1)) = z2 at hX
      subst hlen
      obtain ⟨rest', h1, h2⟩ := up_spec xs z1 z2 (z1 && z2) D.gates []
      have hfirst : stp (xs ++ [z1, z2]) ⟨GateOp.and, [xs.length, xs.length + 1]⟩
          = xs ++ z1 :: z2 :: (z1 && z2) :: [] := by
        simp [stp, GateOp.eval, List.getD_eq_getElem?_getD, List.getElem?_append]
      simp only [Circuit.eval, wires_eq, hX, List.foldl_cons, hfirst]
      rw [h1, h2]
      exact getD_rel xs rest' z1 z2 (z1 && z2) D.output
