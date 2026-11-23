import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Triples273

-- A wire is recorded by its values on the 36 test inputs (p, q): the input that is true
-- exactly at positions p and q (the unit input when p = q).
private abbrev T := Fin 6 → Fin 6 → Bool
private abbrev S : Fin 3 → Finset (Fin 6) := ![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}]

private def tz : T := fun _ _ => false
private def ev (p q : Fin 6) (t : T) : Bool := t p q
private def inT (k : Fin 6) : T := fun p q => decide (k = p) || decide (k = q)
private def ins : List T := [inT 0, inT 1, inT 2, inT 3, inT 4, inT 5]
private def inp (p q : Fin 6) : Fin 6 → Bool := fun r => decide (r = p) || decide (r = q)
private def tand (x y : T) : T := fun p q => x p q && y p q
private def tor (x y : T) : T := fun p q => x p q || y p q

-- Every wire of an AND/OR circuit is monotone: true on a unit input, true on the pair inputs above it.
private def mono (t : T) : Prop :=
  ∀ p q, (t p p = true → t p q = true) ∧ (t q q = true → t p q = true)

-- Heavy for triple i: true on unit inputs only inside the triple, and on at least two of them.
private def heavy (i : Fin 3) (t : T) : Prop :=
  (∀ p, t p p = true → p ∈ S i) ∧ ∃ p q, p ≠ q ∧ t p p = true ∧ t q q = true

-- What output i must look like on the test inputs.
private def outp (i : Fin 3) (t : T) : Prop :=
  (∀ p, t p p = true ↔ p ∈ S i) ∧ ∀ p q, p ∉ S i → q ∉ S i → t p q = false

private theorem sets_meet : ∀ i j : Fin 3, i ≠ j → ∀ p q : Fin 6,
    p ∈ S i → p ∈ S j → q ∈ S i → q ∈ S j → p = q := by decide

private theorem two_in : ∀ i : Fin 3, ∃ p q : Fin 6, p ≠ q ∧ p ∈ S i ∧ q ∈ S i := by decide

private theorem three_in : ∀ i : Fin 3, ∃ a b c : Fin 6,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ∈ S i ∧ b ∈ S i ∧ c ∈ S i := by decide

private theorem inp_card : ∀ p q : Fin 6,
    (Finset.univ.filter (fun r : Fin 6 => inp p q r = true)).card ≤ 2 := by decide

private theorem ofFn_inp : ∀ p q : Fin 6, List.ofFn (inp p q) = ins.map (ev p q) := by decide

private theorem ofFn_unit : ∀ p : Fin 6,
    List.ofFn (fun q : Fin 6 => decide (q = p)) = ins.map (ev p p) := by decide

private theorem read_ev (w : List T) (i : ℕ) (p q : Fin 6) :
    (w.map (ev p q)).getD i false = ev p q (w.getD i tz) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), ev, tz]

private theorem read_wire (w : List T) (i : ℕ) : w.getD i tz = tz ∨ w.getD i tz ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

private theorem gate_table (w : List T) (g : Gate) (hg : legal g) :
    ∃ x y z : T, (x = tz ∨ x ∈ w) ∧ (y = tz ∨ y ∈ w) ∧ (z = tand x y ∨ z = tor x y) ∧
      ∀ p q, step (w.map (ev p q)) g = (w ++ [z]).map (ev p q) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length = 2 at hlen
  cases args with
  | nil => simp at hlen
  | cons a tail =>
    cases tail with
    | nil => simp at hlen
    | cons b tail =>
      cases tail with
      | cons c tail => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · refine ⟨w.getD a tz, w.getD b tz, tand (w.getD a tz) (w.getD b tz),
            read_wire w a, read_wire w b, Or.inl rfl, ?_⟩
          intro p q
          simp only [step, List.map_cons, List.map_nil, read_ev]
          simp [GateOp.eval, ev, tand]
        · refine ⟨w.getD a tz, w.getD b tz, tor (w.getD a tz) (w.getD b tz),
            read_wire w a, read_wire w b, Or.inr rfl, ?_⟩
          intro p q
          simp only [step, List.map_cons, List.map_nil, read_ev]
          simp [GateOp.eval, ev, tor]

private theorem mono_tz : mono tz := by
  intro p q
  simp [tz]

private theorem mono_in (k : Fin 6) : mono (inT k) := by
  intro p q
  simp only [inT, Bool.or_eq_true, decide_eq_true_eq]
  tauto

private theorem mono_tand {x y : T} (hx : mono x) (hy : mono y) : mono (tand x y) := by
  intro p q
  have h1 := hx p q
  have h2 := hy p q
  simp only [tand, Bool.and_eq_true]
  tauto

private theorem mono_tor {x y : T} (hx : mono x) (hy : mono y) : mono (tor x y) := by
  intro p q
  have h1 := hx p q
  have h2 := hy p q
  simp only [tor, Bool.or_eq_true]
  tauto

private theorem heavy_unique {i j : Fin 3} {t : T} (hi : heavy i t) (hj : heavy j t) : i = j := by
  by_contra hne
  obtain ⟨hsub, p, q, hpq, hp, hq⟩ := hi
  exact hpq (sets_meet i j hne p q (hsub p hp) (hj.1 p hp) (hsub q hq) (hj.1 q hq))

private theorem heavy_of_outp {i : Fin 3} {t : T} (h : outp i t) : heavy i t := by
  obtain ⟨p, q, hpq, hp, hq⟩ := two_in i
  exact ⟨fun r hr => (h.1 r).1 hr, p, q, hpq, (h.1 p).2 hp, (h.1 q).2 hq⟩

private theorem not_heavy_tz (i : Fin 3) : ¬ heavy i tz := by
  rintro ⟨-, p, q, -, hp, -⟩
  simp [tz] at hp

private theorem not_heavy_in (i : Fin 3) (k : Fin 6) : ¬ heavy i (inT k) := by
  rintro ⟨-, p, q, hpq, hp, hq⟩
  simp only [inT, Bool.or_self, decide_eq_true_eq] at hp hq
  exact hpq (hp.symm.trans hq)

-- An OR of two wires that are not heavy is true on at most two unit inputs of the triple.
private theorem not_outp_tor {i : Fin 3} {x y : T} (hx : ¬ heavy i x) (hy : ¬ heavy i y) :
    ¬ outp i (tor x y) := by
  intro h
  have hsx : ∀ p, x p p = true → p ∈ S i := fun p hp => (h.1 p).1 (by simp [tor, hp])
  have hsy : ∀ p, y p p = true → p ∈ S i := fun p hp => (h.1 p).1 (by simp [tor, hp])
  have hx1 : ∀ p q, x p p = true → x q q = true → p = q := by
    intro p q hp hq
    by_contra hne
    exact hx ⟨hsx, p, q, hne, hp, hq⟩
  have hy1 : ∀ p q, y p p = true → y q q = true → p = q := by
    intro p q hp hq
    by_contra hne
    exact hy ⟨hsy, p, q, hne, hp, hq⟩
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ := three_in i
  have ha' := (h.1 a).2 ha
  have hb' := (h.1 b).2 hb
  have hc' := (h.1 c).2 hc
  simp only [tor, Bool.or_eq_true] at ha' hb' hc'
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;> rcases hc' with hc' | hc'
  all_goals first
    | exact hab (hx1 a b ha' hb')
    | exact hac (hx1 a c ha' hc')
    | exact hbc (hx1 b c hb' hc')
    | exact hab (hy1 a b ha' hb')
    | exact hac (hy1 a c ha' hc')
    | exact hbc (hy1 b c hb' hc')

-- An AND of two wires that are not heavy is true on a pair input outside the triple.
private theorem not_outp_tand {i : Fin 3} {x y : T} (mx : mono x) (my : mono y)
    (hx : ¬ heavy i x) (hy : ¬ heavy i y) : ¬ outp i (tand x y) := by
  intro h
  obtain ⟨a, b, hab, ha, hb⟩ := two_in i
  have ha' := (h.1 a).2 ha
  have hb' := (h.1 b).2 hb
  simp only [tand, Bool.and_eq_true] at ha' hb'
  have ex : ∃ p, x p p = true ∧ p ∉ S i := by
    by_contra hno
    exact hx ⟨fun p hp => Classical.byContradiction (fun hps => hno ⟨p, hp, hps⟩),
      a, b, hab, ha'.1, hb'.1⟩
  have ey : ∃ q, y q q = true ∧ q ∉ S i := by
    by_contra hno
    exact hy ⟨fun p hp => Classical.byContradiction (fun hps => hno ⟨p, hp, hps⟩),
      a, b, hab, ha'.2, hb'.2⟩
  obtain ⟨p, hp, hps⟩ := ex
  obtain ⟨q, hq, hqs⟩ := ey
  have hbad := h.2 p q hps hqs
  have h1 := (mx p q).1 hp
  have h2 := (my p q).2 hq
  simp [tand, h1, h2] at hbad

-- The number of wires that are heavy for triple i.
open Classical in
private noncomputable def cnt (i : Fin 3) (w : List T) : ℕ :=
  w.countP (fun t => decide (heavy i t))

open Classical in
private theorem cnt_pos (i : Fin 3) (w : List T) (z : T) (h : heavy i z) :
    cnt i (w ++ [z]) = cnt i w + 1 := by
  simp [cnt, List.countP_append, h]

open Classical in
private theorem cnt_neg (i : Fin 3) (w : List T) (z : T) (h : ¬ heavy i z) :
    cnt i (w ++ [z]) = cnt i w := by
  simp [cnt, List.countP_append, h]

open Classical in
private theorem cnt_le (i : Fin 3) (w : List T) (z : T) : cnt i (w ++ [z]) ≤ cnt i w + 1 := by
  by_cases h : heavy i z
  · rw [cnt_pos i w z h]
  · rw [cnt_neg i w z h]
    omega

open Classical in
private theorem cnt_ge (i : Fin 3) (w : List T) (z : T) : cnt i w ≤ cnt i (w ++ [z]) := by
  by_cases h : heavy i z
  · rw [cnt_pos i w z h]
    omega
  · rw [cnt_neg i w z h]

open Classical in
private theorem cnt_zero {i : Fin 3} {w : List T} (h : cnt i w = 0) : ∀ s ∈ w, ¬ heavy i s := by
  intro s hs hh
  have h' : w.countP (fun t => decide (heavy i t)) = 0 := h
  have := List.countP_eq_zero.mp h' s hs
  simp [hh] at this

open Classical in
private theorem cnt_sum (w : List T) (z : T) :
    cnt 0 (w ++ [z]) + cnt 1 (w ++ [z]) + cnt 2 (w ++ [z]) ≤ cnt 0 w + cnt 1 w + cnt 2 w + 1 := by
  by_cases h0 : heavy 0 z
  · have n1 : ¬ heavy 1 z := fun h1 => absurd (heavy_unique h0 h1) (by decide)
    have n2 : ¬ heavy 2 z := fun h2 => absurd (heavy_unique h0 h2) (by decide)
    have e0 := cnt_le 0 w z
    have e1 := cnt_neg 1 w z n1
    have e2 := cnt_neg 2 w z n2
    omega
  · by_cases h1 : heavy 1 z
    · have n2 : ¬ heavy 2 z := fun h2 => absurd (heavy_unique h1 h2) (by decide)
      have e0 := cnt_neg 0 w z h0
      have e1 := cnt_le 1 w z
      have e2 := cnt_neg 2 w z n2
      omega
    · have e0 := cnt_neg 0 w z h0
      have e1 := cnt_neg 1 w z h1
      have e2 := cnt_le 2 w z
      omega

-- Each gate adds one wire, heavy for at most one triple, and an output wire for triple i
-- is never the first heavy wire for i. So three outputs need six gates.
open Classical in
private theorem core (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List T)
    (hm : ∀ t ∈ w, mono t)
    (hJ : ∀ i, (∃ t ∈ w, outp i t) → 2 ≤ cnt i w)
    (hout : ∀ i : Fin 3, ∃ o : ℕ,
      (∀ p, (gs.foldl step (w.map (ev p p))).getD o false = true ↔ p ∈ S i) ∧
      (∀ p q, p ∉ S i → q ∉ S i → (gs.foldl step (w.map (ev p q))).getD o false = false)) :
    6 ≤ gs.length + (cnt 0 w + cnt 1 w + cnt 2 w) := by
  induction gs generalizing w with
  | nil =>
    have key : ∀ i : Fin 3, 2 ≤ cnt i w := by
      intro i
      obtain ⟨o, h1, h2⟩ := hout i
      apply hJ i
      have hf : outp i (w.getD o tz) := by
        constructor
        · intro p
          have := h1 p
          simpa only [List.foldl_nil, read_ev, ev] using this
        · intro p q hp hq
          have := h2 p q hp hq
          simpa only [List.foldl_nil, read_ev, ev] using this
      rcases read_wire w o with hz | hmem
      · rw [hz] at hf
        exact absurd (heavy_of_outp hf) (not_heavy_tz i)
      · exact ⟨_, hmem, hf⟩
    have k0 := key 0
    have k1 := key 1
    have k2 := key 2
    omega
  | cons g gs ih =>
    obtain ⟨x, y, z, hx, hy, hz, hstep⟩ := gate_table w g (hg g (by simp))
    have mx : mono x := by
      rcases hx with hx | hx
      · rw [hx]
        exact mono_tz
      · exact hm x hx
    have my : mono y := by
      rcases hy with hy | hy
      · rw [hy]
        exact mono_tz
      · exact hm y hy
    have mz : mono z := by
      rcases hz with hz | hz
      · rw [hz]
        exact mono_tand mx my
      · rw [hz]
        exact mono_tor mx my
    have hm' : ∀ t ∈ w ++ [z], mono t := by
      intro t ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | ht
      · exact hm t ht
      · rw [ht]
        exact mz
    have hJ' : ∀ i, (∃ t ∈ w ++ [z], outp i t) → 2 ≤ cnt i (w ++ [z]) := by
      intro i ⟨t, ht, hf⟩
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | ht
      · have a1 := hJ i ⟨t, ht, hf⟩
        have a2 := cnt_ge i w z
        omega
      · rw [ht] at hf
        rw [cnt_pos i w z (heavy_of_outp hf)]
        by_contra hlt
        have h0 : cnt i w = 0 := by omega
        have hnone := cnt_zero h0
        have nx : ¬ heavy i x := by
          rcases hx with hx | hx
          · rw [hx]
            exact not_heavy_tz i
          · exact hnone x hx
        have ny : ¬ heavy i y := by
          rcases hy with hy | hy
          · rw [hy]
            exact not_heavy_tz i
          · exact hnone y hy
        rcases hz with hz | hz
        · rw [hz] at hf
          exact not_outp_tand mx my nx ny hf
        · rw [hz] at hf
          exact not_outp_tor nx ny hf
    have hout' : ∀ i : Fin 3, ∃ o : ℕ,
        (∀ p, (gs.foldl step ((w ++ [z]).map (ev p p))).getD o false = true ↔ p ∈ S i) ∧
        (∀ p q, p ∉ S i → q ∉ S i →
          (gs.foldl step ((w ++ [z]).map (ev p q))).getD o false = false) := by
      intro i
      obtain ⟨o, h1, h2⟩ := hout i
      refine ⟨o, ?_, ?_⟩
      · intro p
        simpa only [List.foldl_cons, hstep] using h1 p
      · intro p q hp hq
        simpa only [List.foldl_cons, hstep] using h2 p q hp hq
    have hrec := ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [z]) hm' hJ' hout'
    have hsum := cnt_sum w z
    simp only [List.length_cons]
    omega

private theorem mem_ins {t : T} (ht : t ∈ ins) : ∃ k, t = inT k := by
  simp only [ins, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

open Classical in
private theorem cnt_ins (i : Fin 3) : cnt i ins = 0 := by
  have h : ins.countP (fun t => decide (heavy i t)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro t ht
    obtain ⟨k, rfl⟩ := mem_ins ht
    simpa using not_heavy_in i k
  exact h

open Classical in
private theorem lower (C : Circuit) (o : Fin 3 → ℕ)
    (hgates : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hout : ∀ i : Fin 3,
      (∀ p : Fin 6, (C.wires (List.ofFn (fun q : Fin 6 => decide (q = p)))).getD (o i) false = true
        ↔ p ∈ S i) ∧
      ∀ x : Fin 6 → Bool, (Finset.univ.filter (fun q : Fin 6 => x q = true)).card ≤ 2 →
        (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) :
    6 ≤ C.size := by
  have hm : ∀ t ∈ ins, mono t := by
    intro t ht
    obtain ⟨k, rfl⟩ := mem_ins ht
    exact mono_in k
  have hJ : ∀ i, (∃ t ∈ ins, outp i t) → 2 ≤ cnt i ins := by
    intro i ⟨t, ht, hf⟩
    obtain ⟨k, rfl⟩ := mem_ins ht
    exact absurd (heavy_of_outp hf) (not_heavy_in i k)
  have houts : ∀ i : Fin 3, ∃ o' : ℕ,
      (∀ p, (C.gates.foldl step (ins.map (ev p p))).getD o' false = true ↔ p ∈ S i) ∧
      (∀ p q, p ∉ S i → q ∉ S i →
        (C.gates.foldl step (ins.map (ev p q))).getD o' false = false) := by
    intro i
    obtain ⟨ha, hb⟩ := hout i
    refine ⟨o i, ?_, ?_⟩
    · intro p
      have h := ha p
      rw [ofFn_unit p] at h
      exact h
    · intro p q hp hq
      have h := hb (inp p q) (inp_card p q) (by
        intro r hr
        simp only [inp, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        exact ⟨fun e => hp (e ▸ hr), fun e => hq (e ▸ hr)⟩)
      rw [ofFn_inp p q] at h
      exact h
  have h := core C.gates hgates ins hm hJ houts
  rw [cnt_ins 0, cnt_ins 1, cnt_ins 2] at h
  have hs : C.size = C.gates.length := rfl
  omega

end Triples273

theorem PEqualNP.Outside.L_meta_273 :
    ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 3 → ℕ), C.size ≤ 5 ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ ∀ i : Fin 3, (∀ p : Fin 6, (C.wires (List.ofFn (fun q : Fin 6 => decide (q = p)))).getD (o i) false = true ↔ p ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i) ∧ ∀ x : Fin 6 → Bool, (Finset.univ.filter (fun q : Fin 6 => x q = true)).card ≤ 2 → (∀ q ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false := by
  rintro ⟨C, o, hsize, hgates, hout⟩
  have h6 := Triples273.lower C o hgates hout
  omega
