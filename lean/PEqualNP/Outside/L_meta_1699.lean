import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1699
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem hasCircuitSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (hst : s ≤ t)
    (h : HasCircuitSize n f s) : HasCircuitSize n f t := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  exact ⟨C, ok, le_trans hsz hst, hev⟩

theorem encodePartial_cons (o : Option Bool) (T : List (Option Bool)) :
    encodePartial (o :: T) =
      (match o with
        | none => [false, false]
        | some b => [true, b]) ++ encodePartial T := by
  cases o <;> simp [encodePartial, List.flatMap_cons]

theorem length_encodePartial (T : List (Option Bool)) :
    (encodePartial T).length = 2 * T.length := by
  induction T with
  | nil => rfl
  | cons o T ih =>
    rw [encodePartial_cons, List.length_append, ih, List.length_cons]
    cases o <;> simp <;> omega

theorem getElem?_replicate_append_add (s k : ℕ) (l : List Bool) :
    (List.replicate s true ++ l)[s + k]? = l[k]? := by
  have h : (List.replicate s true).length ≤ s + k := by simp
  rw [List.getElem?_append_right h]
  simp

theorem split_unique : ∀ (s s' : ℕ) (A B : List Bool),
    List.replicate s true ++ false :: A = List.replicate s' true ++ false :: B →
      s = s' ∧ A = B
  | 0, 0, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.nil_append] at h
    exact ⟨rfl, (List.cons.inj h).2⟩
  | 0, s' + 1, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | s + 1, 0, A, B, h => by
    rw [List.replicate_zero, List.nil_append, List.replicate_succ, List.cons_append] at h
    exact absurd (List.cons.inj h).1 (by decide)
  | s + 1, s' + 1, A, B, h => by
    rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append] at h
    obtain ⟨h1, h2⟩ := split_unique s s' A B (List.cons.inj h).2
    exact ⟨by rw [h1], h2⟩

theorem encodePartial_injective : ∀ (T T' : List (Option Bool)),
    encodePartial T = encodePartial T' → T = T'
  | [], [], _ => rfl
  | [], o :: T', h => by
    have hl := congrArg List.length h
    rw [length_encodePartial, length_encodePartial] at hl
    simp at hl
  | o :: T, [], h => by
    have hl := congrArg List.length h
    rw [length_encodePartial, length_encodePartial] at hl
    simp at hl
  | o :: T, o' :: T', h => by
    have ih := encodePartial_injective T T'
    rw [encodePartial_cons, encodePartial_cons] at h
    rcases o with _ | b <;> rcases o' with _ | b' <;> simp at h
    · rw [ih h]
    · rw [h.1, ih h.2]

theorem enc_pair : ∀ (T : List (Option Bool)) (k : ℕ), k < T.length →
    (encodePartial T)[2 * k]? = some (T.getD k none).isSome ∧
      (encodePartial T)[2 * k + 1]? = some ((T.getD k none).getD false)
  | [], k, h => by simp at h
  | o :: T, 0, _ => by
    rw [encodePartial_cons]
    cases o <;> simp
  | o :: T, k + 1, h => by
    have ih := enc_pair T k (by simpa using h)
    rw [encodePartial_cons]
    have e1 : 2 * (k + 1) = 2 * k + 2 := by ring
    have e2 : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    rw [e2, e1]
    cases o <;> simpa using ih

theorem word_pair (s : ℕ) (T : List (Option Bool)) (u : List Bool)
    (h : u = List.replicate s true ++ false :: encodePartial T) (k : ℕ) (hk : k < T.length) :
    u[s + 1 + 2 * k]? = some (T.getD k none).isSome ∧
      u[s + 1 + 2 * k + 1]? = some ((T.getD k none).getD false) := by
  obtain ⟨p1, p2⟩ := enc_pair T k hk
  have a1 := getElem?_replicate_append_add s (2 * k + 1) (false :: encodePartial T)
  have a2 := getElem?_replicate_append_add s (2 * k + 1 + 1)
    (false :: encodePartial T)
  rw [List.getElem?_cons_succ] at a1 a2
  have e1 : s + 1 + 2 * k = s + (2 * k + 1) := by ring
  have e2 : s + 1 + 2 * k + 1 = s + (2 * k + 1 + 1) := by ring
  rw [h, e2, e1, a1, a2]
  exact ⟨p1, p2⟩

def rel (m d : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun a => if a < m then a else a + d⟩

theorem reloc_wires (x p : List Bool) (gs : List Gate) : ∀ t : List Bool,
    wiresFrom (gs.map (rel x.length p.length)) (x ++ p ++ t) =
      x ++ p ++ (wiresFrom gs (x ++ t)).drop x.length := by
  induction gs with
  | nil => intro t; simp [wiresFrom]
  | cons g gs ih =>
    intro t
    have key : ∀ a : ℕ, (x ++ p ++ t).getD (if a < x.length then a else a + p.length) false =
        (x ++ t).getD a false := by
      intro a
      by_cases h : a < x.length
      · rw [if_pos h, List.append_assoc, List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ h]
      · rw [if_neg h, List.getD_append_right _ _ _ _ (by simp; omega),
          List.getD_append_right _ _ _ _ (by omega)]
        congr 1
        simp
        omega
    have hval : (rel x.length p.length g).op.eval
        ((rel x.length p.length g).inputs.map fun i => (x ++ p ++ t).getD i false) =
        g.op.eval (g.inputs.map fun i => (x ++ t).getD i false) := by
      simp only [rel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact key a
    have e1 : wiresFrom ((g :: gs).map (rel x.length p.length)) (x ++ p ++ t) =
        wiresFrom (gs.map (rel x.length p.length)) (x ++ p ++ t ++
          [(rel x.length p.length g).op.eval
            ((rel x.length p.length g).inputs.map fun i => (x ++ p ++ t).getD i false)]) := rfl
    have e2 : wiresFrom (g :: gs) (x ++ t) =
        wiresFrom gs (x ++ t ++ [g.op.eval (g.inputs.map fun i => (x ++ t).getD i false)]) := rfl
    rw [e1, e2, hval, List.append_assoc (x ++ p), ih, List.append_assoc x t]

def out (m d l B o : ℕ) : ℕ :=
  if o < m then o else if o < m + l then o + d else B

theorem out_range (m d l L B o : ℕ) (hL : m + d + l ≤ L) (hB : L + 4 ≤ B) :
    out m d l B o < L ∨ L + 4 ≤ out m d l B o := by
  unfold out
  split_ifs <;> omega

theorem getD_mid (v x p u q : List Bool) (d l B o : ℕ) (hv : v = x ++ p ++ u ++ q)
    (hB : v.length ≤ B) (hd : d = p.length) (hl : l = u.length) :
    v.getD (out x.length d l B o) false = (x ++ u).getD o false := by
  subst hv hd hl
  unfold out
  by_cases h1 : o < x.length
  · rw [if_pos h1, List.append_assoc, List.append_assoc, List.getD_append _ _ _ _ h1,
      List.getD_append _ _ _ _ h1]
  · rw [if_neg h1]
    by_cases h2 : o < x.length + u.length
    · rw [if_pos h2, List.getD_append _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by omega)]
      congr 1
      simp
      omega
    · rw [if_neg h2, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none hB, List.getElem?_eq_none (by simp; omega)]

theorem ok_rel (m d : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (rel m d g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (rel m d g).inputs.length ≤ 2 := by
  simpa [rel] using h

theorem flip_odd {n : ℕ} (x : Fin n → Bool) (i : Fin n)
    (hx : ¬ (Finset.univ.filter fun k : Fin n => x k = true).card % 2 = 1) :
    (Finset.univ.filter fun k : Fin n => Function.update x i (!x i) k = true).card % 2 = 1 := by
  cases hxi : x i with
  | false =>
    have hset : (Finset.univ.filter fun k : Fin n => Function.update x i (!false) k = true) =
        insert i (Finset.univ.filter fun k : Fin n => x k = true) := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [hset, Finset.card_insert_of_notMem (by simp [hxi])]
    omega
  | true =>
    have hset : (Finset.univ.filter fun k : Fin n => Function.update x i (!true) k = true) =
        (Finset.univ.filter fun k : Fin n => x k = true).erase i := by
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    have hmem : i ∈ Finset.univ.filter fun k : Fin n => x k = true := by simp [hxi]
    have hpos := Finset.card_pos.2 ⟨i, hmem⟩
    rw [hset, Finset.card_erase_of_mem hmem]
    omega

def stage (L A : ℕ) (row : ℕ → ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => stage L A row k ++
      [⟨GateOp.and, if k = 0 then [A] else [row (k - 1), A]⟩, ⟨GateOp.or, [row k, L + 2 * k]⟩]

theorem stage_length (L A : ℕ) (row : ℕ → ℕ) : ∀ K : ℕ, (stage L A row K).length = 2 * K
  | 0 => rfl
  | K + 1 => by
    simp only [stage, List.length_append, stage_length L A row K, List.length_cons,
      List.length_nil]
    omega

theorem stage_ok (L A : ℕ) (row : ℕ → ℕ) : ∀ K : ℕ, ∀ g ∈ stage L A row K, Ok g
  | 0 => by simp [stage]
  | K + 1 => by
    intro g hg
    simp only [stage, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact stage_ok L A row K g hg
    · by_cases h : K = 0 <;> simp [Ok, h]
    · simp [Ok]

theorem wires_two (W : List Bool) (g1 g2 : Gate) :
    wiresFrom [g1, g2] W =
      W ++ [g1.op.eval (g1.inputs.map fun i => W.getD i false)] ++
        [g2.op.eval (g2.inputs.map fun i =>
          (W ++ [g1.op.eval (g1.inputs.map fun i => W.getD i false)]).getD i false)] := rfl

theorem stage_spec (V : List Bool) (L A : ℕ) (row : ℕ → ℕ) (hL : V.length = L) (hA : A < L) :
    ∀ K : ℕ, (∀ k < K, row k < L) → ∀ k < K,
      (wiresFrom (stage L A row K) V).getD (L + 2 * k + 1) false =
        (V.getD (row k) false ||
          ((decide (k = 0) || V.getD (row (k - 1)) false) && V.getD A false)) := by
  subst hL
  intro K
  induction K with
  | zero => intro _ k hk; omega
  | succ K ih =>
    intro hrow k hk
    have ih' := ih (fun k hk => hrow k (by omega))
    have hlen := length_wiresFrom (stage V.length A row K) V
    rw [stage_length] at hlen
    have hst : ∀ i, i < V.length →
        (wiresFrom (stage V.length A row K) V).getD i false = V.getD i false :=
      fun i hi => getD_wiresFrom _ _ i hi
    have e : wiresFrom (stage V.length A row (K + 1)) V =
        wiresFrom [⟨GateOp.and, if K = 0 then [A] else [row (K - 1), A]⟩,
          ⟨GateOp.or, [row K, V.length + 2 * K]⟩] (wiresFrom (stage V.length A row K) V) :=
      wiresFrom_append _ _ _
    rw [e]
    generalize wiresFrom (stage V.length A row K) V = W at ih' hlen hst ⊢
    rw [wires_two]
    by_cases hkK : k < K
    · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
      exact ih' k hkK
    · have hkK' : k = K := by omega
      subst hkK'
      have hrk := hrow k (by omega)
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      have i1 : V.length + 2 * k + 1 - (W ++ [GateOp.and.eval
          ((if k = 0 then [A] else [row (k - 1), A]).map fun i => W.getD i false)]).length = 0 := by
        simp; omega
      rw [i1]
      have a1 : ∀ c : Bool, (W ++ [c]).getD (row k) false = V.getD (row k) false := by
        intro c
        rw [List.getD_append _ _ _ _ (by omega)]
        exact hst _ hrk
      have a2 : ∀ c : Bool, (W ++ [c]).getD (V.length + 2 * k) false = c := by
        intro c
        rw [List.getD_append_right _ _ _ _ (by omega)]
        have : V.length + 2 * k - W.length = 0 := by omega
        rw [this]
        rfl
      simp only [List.getD_cons_zero, List.map_cons, List.map_nil, a1, a2]
      by_cases hk0 : k = 0
      · have hA' := hst A hA
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at hA'
        simp [hk0, GateOp.eval, hA']
      · have hA' := hst A hA
        have hrk' := hst _ (hrow (k - 1) (by omega))
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at hA' hrk'
        simp [hk0, GateOp.eval, hA', hrk']

def step (m : ℕ) (gs cg : List Gate) (o : ℕ) (row : ℕ → ℕ) (K : ℕ) : List Gate :=
  gs ++ cg.map (rel m gs.length) ++
    [⟨GateOp.or, [out m gs.length cg.length (m + gs.length + cg.length) o]⟩] ++
    stage (m + gs.length + cg.length + 1) (m + gs.length + cg.length) row K

theorem step_spec (x : List Bool) (gs cg : List Gate) (o : ℕ) (row : ℕ → ℕ) (K : ℕ)
    (hrow : ∀ k < K, row k < x.length + gs.length) : ∀ k < K,
    (wiresFrom (step x.length gs cg o row K) x).getD
        (x.length + gs.length + cg.length + 1 + 2 * k + 1) false =
      ((wiresFrom gs x).getD (row k) false ||
        ((decide (k = 0) || (wiresFrom gs x).getD (row (k - 1)) false) &&
          (wiresFrom cg x).getD o false)) := by
  intro k hk
  obtain ⟨p, hp, hlp⟩ := wiresFrom_prefix gs x
  obtain ⟨t, ht, hlt⟩ := wiresFrom_prefix cg x
  have r2 : wiresFrom (cg.map (rel x.length gs.length)) (x ++ p) = x ++ p ++ t := by
    have h := reloc_wires x p cg []
    rw [List.append_nil, List.append_nil, ht, List.drop_left, hlp] at h
    exact h
  have hcopy : (x ++ p ++ t).getD (out x.length gs.length cg.length
      (x.length + gs.length + cg.length) o) false = (x ++ t).getD o false :=
    getD_mid _ x p t [] gs.length cg.length _ o (by simp) (by simp [hlp, hlt]; omega)
      hlp.symm hlt.symm
  have hV : (x ++ p ++ t ++ [(x ++ t).getD o false]).length =
      x.length + gs.length + cg.length + 1 := by
    simp [hlp, hlt]
    omega
  have e : wiresFrom (step x.length gs cg o row K) x =
      wiresFrom (stage (x.length + gs.length + cg.length + 1) (x.length + gs.length + cg.length)
        row K) (x ++ p ++ t ++ [(x ++ t).getD o false]) := by
    unfold step
    rw [wiresFrom_append, wiresFrom_append, wiresFrom_append, hp, r2]
    congr 1
    simp only [wiresFrom, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, hcopy]
    simp [GateOp.eval]
  have old : ∀ i, i < x.length + gs.length →
      (x ++ p ++ t ++ [(x ++ t).getD o false]).getD i false = (x ++ p).getD i false := by
    intro i hi
    rw [List.getD_append _ _ _ _ (by simp [hlp, hlt]; omega),
      List.getD_append _ _ _ _ (by simp [hlp]; omega)]
  have hAval : (x ++ p ++ t ++ [(x ++ t).getD o false]).getD
      (x.length + gs.length + cg.length) false = (x ++ t).getD o false := by
    rw [List.getD_append_right _ _ _ _ (by simp [hlp, hlt]; omega)]
    have : x.length + gs.length + cg.length - (x ++ p ++ t).length = 0 := by
      simp [hlp, hlt]
      omega
    rw [this]
    rfl
  rw [e, stage_spec _ _ _ row hV (by omega) K (fun k hk => by have := hrow k hk; omega) k hk,
    old _ (hrow k hk), old _ (hrow (k - 1) (by omega)), hAval, hp, ht]

theorem thr_gates (n s K : ℕ) : ∀ fs : List ((Fin n → Bool) → Bool),
    (∀ f ∈ fs, HasCircuitSize n f s) →
    ∃ (gs : List Gate) (row : ℕ → ℕ), (∀ g ∈ gs, Ok g) ∧
      gs.length ≤ 1 + fs.length * (s + 1 + 2 * K) ∧ (∀ k < K, row k < n + gs.length) ∧
      ∀ (z : Fin n → Bool), ∀ k < K, (wiresFrom gs (List.ofFn z)).getD (row k) false =
        decide (k + 1 ≤ (fs.map fun f => f z).count true) := by
  intro fs
  induction fs with
  | nil =>
    intro _
    refine ⟨[⟨GateOp.or, []⟩], fun _ => n, ?_, by simp, fun k _ => by simp, ?_⟩
    · intro g hg
      rw [List.mem_singleton] at hg
      subst hg
      simp [Ok]
    · intro z k _
      have e : wiresFrom [⟨GateOp.or, []⟩] (List.ofFn z) = List.ofFn z ++ [false] := rfl
      rw [e, List.getD_append_right _ _ _ _ (by simp)]
      simp
  | cons f fs ih =>
    intro h
    obtain ⟨gs, row, hok, hlen, hrow, hval⟩ := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    obtain ⟨C, F, S, E⟩ := h f List.mem_cons_self
    refine ⟨step n gs C.gates C.output row K,
      fun k => n + gs.length + C.gates.length + 1 + 2 * k + 1, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [step, List.mem_append, List.mem_map, List.mem_singleton] at hg
      rcases hg with ((hg | ⟨g', hg', rfl⟩) | rfl) | hg
      · exact hok g hg
      · exact ok_rel _ _ _ (F g' hg')
      · simp [Ok]
      · exact stage_ok _ _ _ _ g hg
    · simp only [Circuit.size] at S
      simp only [step, List.length_append, List.length_map, List.length_cons, List.length_nil,
        stage_length]
      have e : (fs.length + 1) * (s + 1 + 2 * K) =
          fs.length * (s + 1 + 2 * K) + (s + 1 + 2 * K) := by ring
      rw [e]
      generalize fs.length * (s + 1 + 2 * K) = X at hlen ⊢
      omega
    · intro k hk
      simp only [step, List.length_append, List.length_map, List.length_cons, List.length_nil,
        stage_length]
      omega
    · intro z k hk
      have hs := step_spec (List.ofFn z) gs C.gates C.output row K
        (by simpa using hrow) k hk
      simp only [List.length_ofFn] at hs
      have e := E z
      simp only [Circuit.eval, wires_eq] at e
      rw [hs, hval z k hk, hval z (k - 1) (by omega), e, List.map_cons, List.count_cons]
      rw [Bool.eq_iff_iff]
      cases f z
      · simp
      · simp
        omega

theorem thr_size (n s t : ℕ) (fs : List ((Fin n → Bool) → Bool))
    (h : ∀ f ∈ fs, HasCircuitSize n f s) (ht : 1 ≤ t) :
    HasCircuitSize n (fun z => decide (t ≤ (fs.map fun f => f z).count true))
      (1 + fs.length * (s + 1 + 2 * t)) := by
  obtain ⟨gs, row, hok, hlen, _, hval⟩ := thr_gates n s t fs h
  refine ⟨⟨gs, row (t - 1)⟩, hok, hlen, fun z => ?_⟩
  have e := hval z (t - 1) (by omega)
  have e' : t - 1 + 1 = t := by omega
  rw [e'] at e
  simpa only [Circuit.eval, wires_eq] using e

theorem odd_witness (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool))
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP)
    (x : Fin n → Bool) (hx : (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1) :
    ∃ f : (Fin n' → Bool) → Bool, Consistent n' (T x) f ∧ HasCircuitSize n' f s := by
  obtain ⟨m, s', T', hw, hlen, f, hc, hs⟩ := (hred x).1 hx
  rw [(hfmt x).1] at hw
  obtain ⟨e1, e2⟩ := split_unique s s' _ _ hw
  have e3 := encodePartial_injective _ _ e2
  subst e1
  subst e3
  have e4 : m = n' := Nat.pow_right_injective (Nat.le_refl 2) (hlen.symm.trans (hfmt x).2)
  subst e4
  exact ⟨f, hc, hs⟩

theorem entry_same (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool))
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (x y : Fin n → Bool) (k : ℕ) (hk : k < 2 ^ n') (b : Bool)
    (he : (T x).getD k none = some b)
    (h1 : (w y)[s + 1 + 2 * k]? = (w x)[s + 1 + 2 * k]?)
    (h2 : (w y)[s + 1 + 2 * k + 1]? = (w x)[s + 1 + 2 * k + 1]?) :
    (T y).getD k none = some b := by
  rw [(word_pair s (T y) (w y) (hfmt y).1 k (by rw [(hfmt y).2]; exact hk)).1,
    (word_pair s (T x) (w x) (hfmt x).1 k (by rw [(hfmt x).2]; exact hk)).1, he] at h1
  rw [(word_pair s (T y) (w y) (hfmt y).1 k (by rw [(hfmt y).2]; exact hk)).2,
    (word_pair s (T x) (w x) (hfmt x).1 k (by rw [(hfmt x).2]; exact hk)).2, he] at h2
  cases hy : (T y).getD k none with
  | none => rw [hy] at h1; simp at h1
  | some c => rw [hy] at h2; simp at h2; rw [h2]

theorem entry_true (n n' s : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool))
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (x y : Fin n → Bool) (k : ℕ) (hk : k < 2 ^ n')
    (he : (T x).getD k none = some true)
    (h2 : (w y)[s + 1 + 2 * k + 1]? = (w x)[s + 1 + 2 * k + 1]?) :
    (T y).getD k none = some true := by
  rw [(word_pair s (T y) (w y) (hfmt y).1 k (by rw [(hfmt y).2]; exact hk)).2,
    (word_pair s (T x) (w x) (hfmt x).1 k (by rw [(hfmt x).2]; exact hk)).2, he] at h2
  cases hy : (T y).getD k none with
  | none => rw [hy] at h2; simp at h2
  | some c => rw [hy] at h2; simp at h2; rw [h2]

theorem majq_witness (n n' s q : ℕ) (w : (Fin n → Bool) → List Bool)
    (T : (Fin n → Bool) → List (Option Bool)) (hq0 : 0 < q) (hn : 3 * q + 1 ≤ n)
    (hq : QueryLocal n q w)
    (hfmt : ∀ x : Fin n → Bool,
      w x = List.replicate s true ++ false :: encodePartial (T x) ∧ (T x).length = 2 ^ n')
    (hred : ∀ x : Fin n → Bool,
      (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PartialMCSP)
    (x : Fin n → Bool) :
    ∃ f : (Fin n' → Bool) → Bool, Consistent n' (T x) f ∧
      HasCircuitSize n' f ((3 * q + 1) * s + 3 * (3 * q + 1) ^ 2) := by
  by_cases hx : (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1
  · obtain ⟨f, hc, hs⟩ := odd_witness n n' s w T hfmt hred x hx
    exact ⟨f, hc, hasCircuitSize_mono (by nlinarith [Nat.zero_le (q * s)]) hs⟩
  · have wit : ∀ l : Fin n, ∃ f : (Fin n' → Bool) → Bool,
        Consistent n' (T (Function.update x l (!x l))) f ∧ HasCircuitSize n' f s :=
      fun l => odd_witness n n' s w T hfmt hred _ (flip_odd x l hx)
    choose F hFc hFs using wit
    obtain ⟨G, hG⟩ : ∃ G : Fin (3 * q + 1) → (Fin n' → Bool) → Bool,
        G = fun l => F (Fin.castLE hn l) := ⟨_, rfl⟩
    refine ⟨fun z => decide (2 * q + 1 ≤ ((List.ofFn G).map fun f => f z).count true), ?_, ?_⟩
    · intro e b he
      by_cases hk : tableIndex e < 2 ^ n'
      · obtain ⟨Sd, cd, hSd⟩ := hq (s + 1 + 2 * tableIndex e) x
        obtain ⟨Sv, cv, hSv⟩ := hq (s + 1 + 2 * tableIndex e + 1) x
        have hsum := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin (3 * q + 1)))) (fun l => G l e = b)
        rw [Finset.card_univ, Fintype.card_fin] at hsum
        show decide (2 * q + 1 ≤ ((List.ofFn G).map fun f => f e).count true) = b
        rw [List.map_ofFn, List.count_ofFn]
        simp only [Function.comp]
        cases b with
        | true =>
          have good : ∀ l : Fin (3 * q + 1), Fin.castLE hn l ∉ Sv → G l e = true := by
            intro l hl
            rw [hG]
            apply hFc
            exact entry_true n n' s w T hfmt x _ _ hk he
              (hSv _ fun i hi => Function.update_of_ne (by rintro rfl; exact hl hi) _ _)
          have hbad : (Finset.univ.filter fun l : Fin (3 * q + 1) => ¬ G l e = true).card ≤ q := by
            calc (Finset.univ.filter fun l : Fin (3 * q + 1) => ¬ G l e = true).card
                ≤ Sv.card :=
                  Finset.card_le_card_of_injOn (fun l => Fin.castLE hn l)
                    (fun l hl => by
                      by_contra hc
                      exact (Finset.mem_filter.1 hl).2 (good l hc))
                    (fun a _ b _ hab => Fin.castLE_injective hn hab)
              _ ≤ q := cv
          rw [decide_eq_true_eq]
          omega
        | false =>
          have good : ∀ l : Fin (3 * q + 1), Fin.castLE hn l ∉ Sd ∪ Sv → G l e = false := by
            intro l hl
            rw [Finset.mem_union, not_or] at hl
            rw [hG]
            apply hFc
            exact entry_same n n' s w T hfmt x _ _ hk false he
              (hSd _ fun i hi => Function.update_of_ne (by rintro rfl; exact hl.1 hi) _ _)
              (hSv _ fun i hi => Function.update_of_ne (by rintro rfl; exact hl.2 hi) _ _)
          have hbad : (Finset.univ.filter fun l : Fin (3 * q + 1) => ¬ G l e = false).card
              ≤ 2 * q := by
            calc (Finset.univ.filter fun l : Fin (3 * q + 1) => ¬ G l e = false).card
                ≤ (Sd ∪ Sv).card :=
                  Finset.card_le_card_of_injOn (fun l => Fin.castLE hn l)
                    (fun l hl => by
                      by_contra hc
                      exact (Finset.mem_filter.1 hl).2 (good l hc))
                    (fun a _ b _ hab => Fin.castLE_injective hn hab)
              _ ≤ Sd.card + Sv.card := Finset.card_union_le _ _
              _ ≤ 2 * q := by omega
          have hle : (Finset.univ.filter fun l : Fin (3 * q + 1) => G l e = true).card ≤
              (Finset.univ.filter fun l : Fin (3 * q + 1) => ¬ G l e = false).card :=
            Finset.card_le_card fun l hl => by
              rw [Finset.mem_filter] at hl ⊢
              exact ⟨hl.1, by rw [hl.2]; simp⟩
          rw [decide_eq_false_iff_not]
          omega
      · exfalso
        have hl : (T x).length ≤ tableIndex e := by
          rw [(hfmt _).2]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at he
        simp at he
    · have hsz := thr_size n' s (2 * q + 1) (List.ofFn G)
        (fun f hf => by
          rw [List.mem_ofFn] at hf
          obtain ⟨l, rfl⟩ := hf
          rw [hG]
          exact hFs _) (by omega)
      rw [List.length_ofFn] at hsz
      refine hasCircuitSize_mono ?_ hsz
      have h1 : q ≤ q * q := Nat.le_mul_of_pos_left q hq0
      have e1 : 1 + (3 * q + 1) * (s + 1 + 2 * (2 * q + 1)) =
          (3 * q + 1) * s + (12 * (q * q) + 13 * q + 4) := by ring
      have e2 : (3 * q + 1) * s + 3 * (3 * q + 1) ^ 2 =
          (3 * q + 1) * s + (27 * (q * q) + 18 * q + 3) := by ring
      rw [e1, e2]
      omega

end PEqualNP.Outside.L_meta_1699

theorem PEqualNP.Outside.L_meta_1699 : ∀ (n n' s q : ℕ) (w : (Fin n → Bool) → List Bool) (T : (Fin n → Bool) → List (Option Bool)), 0 < q → 3 * q + 1 ≤ n → PEqualNP.MetaComplexity.QueryLocal n q w → (∀ x : Fin n → Bool, w x = List.replicate s true ++ false :: PEqualNP.MetaComplexity.encodePartial (T x) ∧ (T x).length = 2 ^ n') → (∀ x : Fin n → Bool, (Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1 ↔ w x ∈ PEqualNP.MetaComplexity.PartialMCSP) → ∀ x : Fin n → Bool, ∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' (T x) f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f ((3 * q + 1) * s + 3 * (3 * q + 1) ^ 2) :=
  PEqualNP.Outside.L_meta_1699.majq_witness
