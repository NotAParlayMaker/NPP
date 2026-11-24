import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3893

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_lt _ _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)


def full : ℕ := 2 ^ 512 - 1
def ff : ℕ := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def w0 : List ℕ := [0, 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa]

def nxt (w : List ℕ) : List ℕ :=
  full :: w.flatMap fun a => (full ^^^ a) :: w.flatMap fun b => [a &&& b, a ||| b]

def ok (t : ℕ) : Bool := !(Nat.beq (ff &&& t) ff) || Nat.beq t full

theorem chk0 : w0.all ok = true := by decide +kernel
theorem chk1 : (nxt w0).all ok = true := by decide +kernel
theorem chk2 : ((nxt w0).all fun g => (nxt (g :: w0)).all ok) = true := by decide +kernel

def pt (m : ℕ) : Fin 9 → Bool := fun i => m.testBit i

def pet (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 ||
    x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

theorem ff_bit : ((List.range 512).all fun m => ff.testBit m == pet (pt m)) = true := by
  decide +kernel

theorem ff_lt : ff < 2 ^ 512 := by decide +kernel

theorem w0_bit : ((List.range 9).all fun i => (List.range 512).all fun m =>
    (w0.getD (i + 1) 0).testBit m == m.testBit i) = true := by decide +kernel

theorem w9_bit : ((List.range 512).all fun m =>
    (w0.getD 10 0).testBit m == (m.testBit 0 || m.testBit 3)) = true := by decide +kernel

def Rep (w : List ℕ) (f : ℕ → Bool) : Prop := ∃ t ∈ w, ∀ m < 512, t.testBit m = f m

theorem full_bit {m : ℕ} (h : m < 512) : full.testBit m = true := by
  unfold full
  rw [Nat.testBit_two_pow_sub_one]
  simpa using h

theorem rep_not {w : List ℕ} {f : ℕ → Bool} (h : Rep w f) : Rep (nxt w) fun m => !f m := by
  obtain ⟨t, ht, hb⟩ := h
  refine ⟨full ^^^ t, List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨t, ht, by simp⟩), fun m hm => ?_⟩
  rw [Nat.testBit_xor, full_bit hm, hb m hm]; simp

theorem rep_and {w : List ℕ} {f g : ℕ → Bool} (h : Rep w f) (h' : Rep w g) :
    Rep (nxt w) fun m => f m && g m := by
  obtain ⟨t, ht, hb⟩ := h
  obtain ⟨u, hu, hc⟩ := h'
  refine ⟨t &&& u, List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨t, ht,
    List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨u, hu, by simp⟩)⟩), fun m hm => ?_⟩
  rw [Nat.testBit_land, hb m hm, hc m hm]

theorem rep_or {w : List ℕ} {f g : ℕ → Bool} (h : Rep w f) (h' : Rep w g) :
    Rep (nxt w) fun m => f m || g m := by
  obtain ⟨t, ht, hb⟩ := h
  obtain ⟨u, hu, hc⟩ := h'
  refine ⟨t ||| u, List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨t, ht,
    List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨u, hu, by simp⟩)⟩), fun m hm => ?_⟩
  rw [Nat.testBit_lor, hb m hm, hc m hm]

theorem rep_true (w : List ℕ) : Rep (nxt w) fun _ => true :=
  ⟨full, by simp [nxt], fun m hm => full_bit hm⟩

theorem rep_congr {w : List ℕ} {f g : ℕ → Bool} (h : Rep w f) (e : ∀ m, f m = g m) : Rep w g := by
  obtain ⟨t, ht, hb⟩ := h
  exact ⟨t, ht, fun m hm => (hb m hm).trans (e m)⟩

theorem rep_gate {w : List ℕ} (o : GateOp) (I : List ℕ) (v : ℕ → ℕ → Bool)
    (ho : o = GateOp.and ∨ o = GateOp.or ∨ o = GateOp.not) (hI : I.length ≤ 2)
    (hv : ∀ i, Rep w (v i)) (h0 : Rep w fun _ => false) :
    Rep (nxt w) fun m => o.eval (I.map fun i => v i m) := by
  match I, hI with
  | [], _ =>
    rcases ho with rfl | rfl | rfl
    · exact rep_congr (rep_true w) fun m => rfl
    · exact rep_congr (rep_and h0 h0) fun m => rfl
    · exact rep_congr (rep_true w) fun m => rfl
  | [a], _ =>
    rcases ho with rfl | rfl | rfl
    · exact rep_congr (rep_and (hv a) (hv a)) fun m => by simp [GateOp.eval]
    · exact rep_congr (rep_or (hv a) (hv a)) fun m => by simp [GateOp.eval]
    · exact rep_congr (rep_not (hv a)) fun m => by simp [GateOp.eval]
  | [a, b], _ =>
    rcases ho with rfl | rfl | rfl
    · exact rep_congr (rep_and (hv a) (hv b)) fun m => by simp [GateOp.eval]
    · exact rep_congr (rep_or (hv a) (hv b)) fun m => by simp [GateOp.eval]
    · exact rep_congr (rep_not (hv a)) fun m => by simp [GateOp.eval]

theorem rep_ok {w : List ℕ} (hw : w.all ok = true) {f : ℕ → Bool} (h : Rep w f)
    (hf : ∀ m < 512, pet (pt m) = true → f m = true) : ∀ m < 512, f m = true := by
  obtain ⟨t, ht, hb⟩ := h
  rw [List.all_eq_true] at hw
  have h1 := hw t ht
  have hsub : ff &&& t = ff := by
    apply Nat.eq_of_testBit_eq
    intro m
    rw [Nat.testBit_land]
    rcases Nat.lt_or_ge m 512 with hm | hm
    · have hfb := ff_bit
      rw [List.all_eq_true] at hfb
      have e := eq_of_beq (hfb m (List.mem_range.2 hm))
      rw [e, hb m hm]
      cases hp : pet (pt m)
      · rfl
      · rw [hf m hm hp]; rfl
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ff_lt (Nat.pow_le_pow_right (by omega) hm))]; rfl
  unfold ok at h1
  rw [hsub] at h1
  have e1 : Nat.beq ff ff = true := Nat.beq_refl ff
  rw [e1] at h1
  have e2 : t = full := Nat.eq_of_beq_eq_true (by simpa using h1)
  intro m hm
  rw [← hb m hm, e2, full_bit hm]

end PEqualNP.Outside.L_meta_3893

theorem PEqualNP.Outside.L_meta_3893 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       ∀ (x4 : ℕ),         have x5 : (Fin (9 : ℕ) → Bool) → ℕ → Bool := fun (x5 : Fin (9 : ℕ) → Bool) (x6 : ℕ) => ({ gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ))])).getD x6 Bool.false;         have x6 : (Fin (9 : ℕ) → Bool) → Bool := fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ));         (∀ (x7 : Fin (9 : ℕ) → Bool), x6 x7 = Bool.true → x5 x7 x4 = Bool.true) → (∃ (x8 : Fin (9 : ℕ) → Bool), x5 x8 x4 = Bool.false) → (12 : ℕ) ≤ x4 := by
  intro gs hlen hF w x5 x6 himp hfalse
  by_contra hcon
  have hops : ∀ (j : ℕ) (hj : j < gs.length), (gs[j].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      gs[j].op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      gs[j].op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gs[j].inputs.length ≤ 2 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hF _ (List.getElem_mem hj)
    exact ⟨by simpa using h1, h2⟩
  let inl : ℕ → List Bool := fun m => List.ofFn (PEqualNP.Outside.L_meta_3893.pt m) ++ [PEqualNP.Outside.L_meta_3893.pt m 0 || PEqualNP.Outside.L_meta_3893.pt m 3]
  have inlen : ∀ m, (inl m).length = 10 := fun m => by simp [inl]
  let val : ℕ → ℕ → Bool := fun i m => (PEqualNP.Outside.L_meta_3893.run gs (inl m)).getD i false
  have zero : PEqualNP.Outside.L_meta_3893.Rep PEqualNP.Outside.L_meta_3893.w0 fun _ => false := ⟨0, by simp [PEqualNP.Outside.L_meta_3893.w0], fun m _ => by simp⟩
  have inrep : ∀ i < 10, PEqualNP.Outside.L_meta_3893.Rep PEqualNP.Outside.L_meta_3893.w0 (val i) := by
    intro i hi
    have hv : ∀ m, val i m = (inl m).getD i false := fun m =>
      PEqualNP.Outside.L_meta_3893.run_input gs (inl m) i (by rw [inlen]; exact hi)
    rcases Nat.lt_or_ge i 9 with h | h
    · refine ⟨PEqualNP.Outside.L_meta_3893.w0.getD (i + 1) 0, ?_, fun m hm => ?_⟩
      · have : i + 1 < PEqualNP.Outside.L_meta_3893.w0.length := by simp [PEqualNP.Outside.L_meta_3893.w0]; omega
        rw [List.getD_eq_getElem _ _ this]; exact List.getElem_mem this
      · have hb := PEqualNP.Outside.L_meta_3893.w0_bit
        rw [List.all_eq_true] at hb
        have h1 := hb i (List.mem_range.2 h)
        rw [List.all_eq_true] at h1
        rw [eq_of_beq (h1 m (List.mem_range.2 hm)), hv]
        simp only [inl]
        rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
          List.getElem_ofFn]
        rfl
    · have hi9 : i = 9 := by omega
      subst hi9
      refine ⟨PEqualNP.Outside.L_meta_3893.w0.getD 10 0, ?_, fun m hm => ?_⟩
      · have : 10 < PEqualNP.Outside.L_meta_3893.w0.length := by simp [PEqualNP.Outside.L_meta_3893.w0]
        rw [List.getD_eq_getElem _ _ this]; exact List.getElem_mem this
      · have hb := PEqualNP.Outside.L_meta_3893.w9_bit
        rw [List.all_eq_true] at hb
        rw [eq_of_beq (hb m (List.mem_range.2 hm)), hv]
        simp only [inl]
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp [PEqualNP.Outside.L_meta_3893.pt]
  have gate : ∀ (j : ℕ) (hj : j < gs.length) (m : ℕ), val (10 + j) m =
      gs[j].op.eval (gs[j].inputs.map fun i => if i < 10 + j then val i m else false) := by
    intro j hj m
    have h := PEqualNP.Outside.L_meta_3893.run_gate gs (inl m) j hj
    rw [inlen] at h
    exact h
  have g0 : PEqualNP.Outside.L_meta_3893.Rep (PEqualNP.Outside.L_meta_3893.nxt PEqualNP.Outside.L_meta_3893.w0) (val 10) := by
    have hj : 0 < gs.length := by omega
    refine PEqualNP.Outside.L_meta_3893.rep_congr (PEqualNP.Outside.L_meta_3893.rep_gate gs[0].op gs[0].inputs
      (fun i m => if i < 10 + 0 then val i m else false) (hops 0 hj).1 (hops 0 hj).2 (fun i => ?_)
      zero) fun m => (gate 0 hj m).symm
    by_cases h : i < 10 + 0
    · simp only [h, if_true]; exact inrep i (by omega)
    · simp only [h, if_false]; exact zero
  obtain ⟨t, ht, htb⟩ := g0
  have rep1 : ∀ f : ℕ → Bool, PEqualNP.Outside.L_meta_3893.Rep PEqualNP.Outside.L_meta_3893.w0 f → PEqualNP.Outside.L_meta_3893.Rep (t :: PEqualNP.Outside.L_meta_3893.w0) f := by
    rintro f ⟨u, hu, hb⟩
    exact ⟨u, List.mem_cons_of_mem _ hu, hb⟩
  have g1 : PEqualNP.Outside.L_meta_3893.Rep (PEqualNP.Outside.L_meta_3893.nxt (t :: PEqualNP.Outside.L_meta_3893.w0)) (val 11) := by
    have hj : 1 < gs.length := by omega
    refine PEqualNP.Outside.L_meta_3893.rep_congr (PEqualNP.Outside.L_meta_3893.rep_gate gs[1].op gs[1].inputs
      (fun i m => if i < 10 + 1 then val i m else false) (hops 1 hj).1 (hops 1 hj).2 (fun i => ?_)
      (rep1 _ zero)) fun m => (gate 1 hj m).symm
    by_cases h : i < 10 + 1
    · simp only [h, if_true]
      rcases Nat.lt_or_ge i 10 with h' | h'
      · exact rep1 _ (inrep i h')
      · rw [show i = 10 by omega]; exact ⟨t, by simp, htb⟩
    · simp only [h, if_false]; exact rep1 _ zero
  have himp' : ∀ m < 512, PEqualNP.Outside.L_meta_3893.pet (PEqualNP.Outside.L_meta_3893.pt m) = true → val w m = true :=
    fun m _ h => himp (PEqualNP.Outside.L_meta_3893.pt m) h
  have hall : ∀ m < 512, val w m = true := by
    rcases Nat.lt_or_ge w 10 with h | h
    · exact PEqualNP.Outside.L_meta_3893.rep_ok PEqualNP.Outside.L_meta_3893.chk0 (inrep w h) himp'
    · rcases Nat.lt_or_ge w 11 with h' | h'
      · have : w = 10 := by omega
        subst this
        exact PEqualNP.Outside.L_meta_3893.rep_ok PEqualNP.Outside.L_meta_3893.chk1 ⟨t, ht, htb⟩ himp'
      · have : w = 11 := by omega
        subst this
        have hc := PEqualNP.Outside.L_meta_3893.chk2
        rw [List.all_eq_true] at hc
        exact PEqualNP.Outside.L_meta_3893.rep_ok (hc t ht) g1 himp'
  obtain ⟨x, hx⟩ := hfalse
  have hpt : PEqualNP.Outside.L_meta_3893.pt (Nat.ofBits x) = x := funext fun i => Nat.testBit_ofBits_lt x i i.2
  have h := hall (Nat.ofBits x) (Nat.ofBits_lt_two_pow x)
  have e : val w (Nat.ofBits x) = x5 x w := by
    simp only [val, inl]
    rw [hpt]
    rfl
  rw [e, hx] at h
  cases h
