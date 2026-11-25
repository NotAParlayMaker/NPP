import Mathlib
import PEqualNP.Defs

-- The sharp five-input bound is adapted from L-meta-8667 (Apache-2.0).
-- Circuit relabeling and gate elimination are adapted from L-meta-9479 (Apache-2.0).

namespace PEqualNP.Outside.L_meta_12531

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

namespace Core
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev ALL : ℕ := 4294967295

theorem all_bit : ∀ p : Fin 32, ALL.testBit p = true := by decide +kernel

def nc (pool : List ℕ) : List ℕ := pool.filter (fun a => decide (a ≠ 0) && decide (a ≠ ALL))

theorem mem_nc (pool : List ℕ) (a : ℕ) : a ∈ nc pool ↔ a ∈ pool ∧ a ≠ 0 ∧ a ≠ ALL := by
  simp [nc, List.mem_filter]

def cand (pool : List ℕ) : List ℕ :=
  pool ++ ((nc pool).map (fun a => ALL ^^^ a) ++
    (nc pool).flatMap (fun a => (nc pool).flatMap (fun b => [a &&& b, a ||| b])))

def Inv (pool : List ℕ) (ws : Fin 32 → List Bool) : Prop :=
  0 ∈ pool ∧ ALL ∈ pool ∧ ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 32, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem cand_not (pool : List ℕ) (h0 : 0 ∈ pool) (hA : ALL ∈ pool) (m : ℕ) (hm : m ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 32, c.testBit p = !m.testBit p := by
  by_cases e0 : m = 0
  · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [e0, all_bit p]; simp⟩
  · by_cases eA : m = ALL
    · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [eA, all_bit p]; simp⟩
    · refine ⟨ALL ^^^ m, List.mem_append_right _ (List.mem_append_left _
        (List.mem_map.mpr ⟨m, (mem_nc pool m).mpr ⟨hm, e0, eA⟩, rfl⟩)), fun p => ?_⟩
      rw [Nat.testBit_xor, all_bit p]
      simp

theorem cand_and (pool : List ℕ) (h0 : 0 ∈ pool) (ma mb : ℕ) (ha : ma ∈ pool) (hb : mb ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 32, c.testBit p = (ma.testBit p && mb.testBit p) := by
  by_cases a0 : ma = 0
  · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [a0]; simp⟩
  · by_cases aA : ma = ALL
    · exact ⟨mb, List.mem_append_left _ hb, fun p => by rw [aA, all_bit p]; simp⟩
    · by_cases b0 : mb = 0
      · exact ⟨0, List.mem_append_left _ h0, fun p => by rw [b0]; simp⟩
      · by_cases bA : mb = ALL
        · exact ⟨ma, List.mem_append_left _ ha, fun p => by rw [bA, all_bit p]; simp⟩
        · refine ⟨ma &&& mb, ?_, fun p => Nat.testBit_and ma mb p⟩
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact List.mem_flatMap.mpr ⟨ma, (mem_nc pool ma).mpr ⟨ha, a0, aA⟩,
            List.mem_flatMap.mpr ⟨mb, (mem_nc pool mb).mpr ⟨hb, b0, bA⟩, by simp⟩⟩

theorem cand_or (pool : List ℕ) (hA : ALL ∈ pool) (ma mb : ℕ) (ha : ma ∈ pool) (hb : mb ∈ pool) :
    ∃ c ∈ cand pool, ∀ p : Fin 32, c.testBit p = (ma.testBit p || mb.testBit p) := by
  by_cases a0 : ma = 0
  · exact ⟨mb, List.mem_append_left _ hb, fun p => by rw [a0]; simp⟩
  · by_cases aA : ma = ALL
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [aA, all_bit p]; simp⟩
    · by_cases b0 : mb = 0
      · exact ⟨ma, List.mem_append_left _ ha, fun p => by rw [b0]; simp⟩
      · by_cases bA : mb = ALL
        · exact ⟨ALL, List.mem_append_left _ hA, fun p => by rw [bA, all_bit p]; simp⟩
        · refine ⟨ma ||| mb, ?_, fun p => Nat.testBit_or ma mb p⟩
          refine List.mem_append_right _ (List.mem_append_right _ ?_)
          exact List.mem_flatMap.mpr ⟨ma, (mem_nc pool ma).mpr ⟨ha, a0, aA⟩,
            List.mem_flatMap.mpr ⟨mb, (mem_nc pool mb).mpr ⟨hb, b0, bA⟩, by simp⟩⟩

theorem gate_vec (pool : List ℕ) (ws : Fin 32 → List Bool) (h : Inv pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    ∃ c ∈ cand pool, ∀ p : Fin 32,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨h0, hA, hw⟩ := h
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by simp [GateOp.eval, all_bit p]⟩
    · exact ⟨0, List.mem_append_left _ h0, fun p => by simp [GateOp.eval]⟩
    · exact ⟨ALL, List.mem_append_left _ hA, fun p => by simp [GateOp.eval, all_bit p]⟩
  | [a], _ =>
    obtain ⟨ma, hma, ha⟩ := hw a
    rcases hop with rfl | rfl | rfl
    · exact ⟨ma, List.mem_append_left _ hma, fun p => by simp [GateOp.eval, ha p]⟩
    · exact ⟨ma, List.mem_append_left _ hma, fun p => by simp [GateOp.eval, ha p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_not pool h0 hA ma hma
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p]⟩
  | [a, b], _ =>
    obtain ⟨ma, hma, ha⟩ := hw a
    obtain ⟨mb, hmb, hb⟩ := hw b
    rcases hop with rfl | rfl | rfl
    · obtain ⟨c, hc, hcv⟩ := cand_and pool h0 ma mb hma hmb
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p, hb p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_or pool hA ma mb hma hmb
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p, hb p]⟩
    · obtain ⟨c, hc, hcv⟩ := cand_not pool h0 hA ma hma
      exact ⟨c, hc, fun p => by simp [GateOp.eval, hcv p, ha p]⟩
  | _ :: _ :: _ :: _, hl => simp at hl

theorem inv_step (pool pool' : List ℕ) (ws : Fin 32 → List Bool) (L : ℕ)
    (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws) (b : Fin 32 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 32, c.testBit p = b p) (hsub : ∀ m ∈ pool, m ∈ pool') (hcp : c ∈ pool') :
    Inv pool' (fun p => ws p ++ [b p]) := by
  obtain ⟨h0, hA, hw⟩ := hI
  refine ⟨hsub 0 h0, hsub ALL hA, fun i => ?_⟩
  obtain ⟨m, hm, hmb⟩ := hw i
  by_cases hi : i = L
  · subst hi
    exact ⟨c, hcp, fun p => by rw [getD_snoc, if_pos (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, if_neg (by rw [hL p]; exact hi), hmb p]⟩

def pool0 : List ℕ := [2863311530, 3435973836, 4042322160, 4278255360, 4294901760, 0, ALL]

def X (p : Fin 32) : List Bool := List.ofFn (fun i : Fin 5 => p.val.testBit i.val)

theorem X_len (p : Fin 32) : (X p).length = 5 := by simp [X]

theorem inv0 : Inv pool0 X := by
  refine ⟨by decide, by decide, fun i => ?_⟩
  by_cases hi : i < 5
  · have key : ∀ j : Fin 5, ∀ p : Fin 32,
        (pool0.getD j 0).testBit p = (X p).getD j false := by
      decide +kernel
    exact ⟨pool0.getD i 0, by interval_cases i <;> simp [pool0], fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by decide, fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X_len]; omega)]

abbrev Good (T : ℕ) (G : Finset ℕ) : Prop :=
  ∀ p q : Fin 32, T.testBit p = true → T.testBit q = false →
    ∃ w ∈ G, w.testBit p ≠ w.testBit q

theorem good_mono (T : ℕ) (G H : Finset ℕ) (h : G ⊆ H) (hG : Good T G) : Good T H := by
  intro p q hp hq
  obtain ⟨w, hw, h1⟩ := hG p q hp hq
  exact ⟨w, h hw, h1⟩

theorem good_split (T : ℕ) (G : Finset ℕ) (a b c : ℕ) (hG : Good T G)
    (hc : ∀ p q : Fin 32, c.testBit p ≠ c.testBit q →
      a.testBit p ≠ a.testBit q ∨ b.testBit p ≠ b.testBit q) :
    Good T (insert a (insert b (G.erase c))) := by
  intro p q hp hq
  obtain ⟨w, hw, h1⟩ := hG p q hp hq
  by_cases hwc : w = c
  · rw [hwc] at h1
    rcases hc p q h1 with h2 | h2
    · exact ⟨a, Finset.mem_insert_self _ _, h2⟩
    · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h2⟩
  · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hwc, hw⟩)), h1⟩

theorem all_bit' (i : ℕ) : ALL.testBit i = decide (i < 32) := by
  have h : ALL = 2 ^ 32 - 1 := by decide +kernel
  rw [h, Nat.testBit_two_pow_sub_one]

theorem all_lt : ALL < 2 ^ 32 := by decide +kernel

def rep (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | _ :: zs => Nat.add (Nat.mul (2 ^ 32) (rep x zs)) x

theorem rep_bit (x : ℕ) (hx : x < 2 ^ 32) : ∀ (zs : List ℕ) (i : ℕ),
    (rep x zs).testBit i = (decide (i / 32 < zs.length) && x.testBit (i % 32))
  | [], i => by simp [rep]
  | q :: zs, i => by
    rw [rep]
    change (2 ^ 32 * rep x zs + x).testBit i = _
    rw [Nat.testBit_two_pow_mul_add _ hx]
    by_cases hi : i < 32
    · have e1 : i / 32 = 0 := Nat.div_eq_of_lt hi
      have e2 : i % 32 = i := Nat.mod_eq_of_lt hi
      rw [if_pos hi, e1, e2]
      simp
    · have e1 : i / 32 = (i - 32) / 32 + 1 := by omega
      have e2 : i % 32 = (i - 32) % 32 := by omega
      rw [if_neg hi, rep_bit x hx zs (i - 32), e1, e2, List.length_cons]
      simp

theorem mul_rep (x : ℕ) : ∀ zs : List ℕ, x * rep 1 zs = rep x zs
  | [] => by simp [rep]
  | q :: zs => by
    rw [rep, rep]
    change x * (2 ^ 32 * rep 1 zs + 1) = 2 ^ 32 * rep x zs + x
    rw [← mul_rep x zs]
    ring

def msk (w : ℕ) : List ℕ → ℕ
  | [] => 0
  | q :: zs => Nat.add (Nat.mul (2 ^ 32) (msk w zs)) (Nat.mul ALL (Nat.mod (Nat.shiftRight w q) 2))

theorem msk_bit (w : ℕ) : ∀ (zs : List ℕ) (i : ℕ),
    (msk w zs).testBit i = (decide (i / 32 < zs.length) && w.testBit (zs.getD (i / 32) 0))
  | [], i => by simp [msk]
  | q :: zs, i => by
    rw [msk]
    change (2 ^ 32 * msk w zs + ALL * ((w >>> q) % 2)).testBit i = _
    have hb : (w >>> q) % 2 = (w.testBit q).toNat := by
      rw [Nat.toNat_testBit, Nat.shiftRight_eq_div_pow]
    rw [hb]
    have hlt : ALL * (w.testBit q).toNat < 2 ^ 32 := by
      cases w.testBit q
      · show ALL * 0 < 2 ^ 32
        rw [Nat.mul_zero]
        exact Nat.two_pow_pos 32
      · show ALL * 1 < 2 ^ 32
        rw [Nat.mul_one]
        exact all_lt
    rw [Nat.testBit_two_pow_mul_add _ hlt]
    by_cases hi : i < 32
    · have e1 : i / 32 = 0 := Nat.div_eq_of_lt hi
      rw [if_pos hi, e1, List.getD_cons_zero]
      cases w.testBit q
      · show (ALL * 0).testBit i = _
        simp
      · show (ALL * 1).testBit i = _
        rw [Nat.mul_one, all_bit']
        simp [hi]
    · have e1 : i / 32 = (i - 32) / 32 + 1 := by omega
      rw [if_neg hi, msk_bit w zs (i - 32), e1, List.getD_cons_succ, List.length_cons]
      simp

def ppos (T : ℕ) (zs : List ℕ) (w : ℕ) : ℕ := Nat.mul (Nat.land T w) (rep 1 zs)

def pneg (T : ℕ) (zs : List ℕ) (w : ℕ) : ℕ := Nat.mul (Nat.land T (Nat.xor ALL w)) (rep 1 zs)

def full (zs : List ℕ) : ℕ := Nat.mul ALL (rep 1 zs)

theorem ppos_bit (T : ℕ) (zs : List ℕ) (w : ℕ) (hT : T < 2 ^ 32) (i : ℕ) :
    (ppos T zs w).testBit i =
      (decide (i / 32 < zs.length) && (T.testBit (i % 32) && w.testBit (i % 32))) := by
  unfold ppos
  change ((T &&& w) * rep 1 zs).testBit i = _
  rw [mul_rep, rep_bit _ (lt_of_le_of_lt Nat.and_le_left hT), Nat.testBit_and]

theorem pneg_bit (T : ℕ) (zs : List ℕ) (w : ℕ) (hT : T < 2 ^ 32) (i : ℕ) :
    (pneg T zs w).testBit i =
      (decide (i / 32 < zs.length) && (T.testBit (i % 32) && !w.testBit (i % 32))) := by
  unfold pneg
  change ((T &&& (ALL ^^^ w)) * rep 1 zs).testBit i = _
  have hp : i % 32 < 32 := Nat.mod_lt _ (by norm_num)
  rw [mul_rep, rep_bit _ (lt_of_le_of_lt Nat.and_le_left hT), Nat.testBit_and, Nat.testBit_xor,
    all_bit']
  simp [hp]

theorem full_bit (zs : List ℕ) (i : ℕ) : (full zs).testBit i = decide (i / 32 < zs.length) := by
  unfold full
  change (ALL * rep 1 zs).testBit i = _
  have hp : i % 32 < 32 := Nat.mod_lt _ (by norm_num)
  rw [mul_rep, rep_bit _ all_lt, all_bit']
  simp [hp]

def pkF (T : ℕ) (zs : List ℕ) (w : ℕ) : ℕ :=
  Nat.lor (Nat.land (ppos T zs w) (msk w zs))
    (Nat.land (pneg T zs w) (Nat.xor (msk w zs) (full zs)))

abbrev Cov (T : ℕ) (zs : List ℕ) (w P : ℕ) : Prop :=
  ∀ i : ℕ, P.testBit i = true → i / 32 < zs.length ∧ T.testBit (i % 32) = true ∧
    w.testBit (i % 32) = w.testBit (zs.getD (i / 32) 0)

theorem cov_pkF (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 32) (w : ℕ) : Cov T zs w (pkF T zs w) := by
  intro i h
  unfold pkF at h
  change ((ppos T zs w &&& msk w zs) ||| (pneg T zs w &&& (msk w zs ^^^ full zs))).testBit i =
    true at h
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, ppos_bit T zs _ hT,
    pneg_bit T zs _ hT, msk_bit, full_bit] at h
  by_cases hd : i / 32 < zs.length
  · refine ⟨hd, ?_⟩
    revert h
    cases T.testBit (i % 32) <;> cases w.testBit (i % 32) <;>
      cases w.testBit (zs.getD (i / 32) 0) <;> simp [hd]
  · simp [hd] at h

def vand (T : ℕ) (zs : List ℕ) (a b : ℕ) : ℕ :=
  Nat.lor (Nat.land (Nat.land (ppos T zs a) (ppos T zs b)) (Nat.land (msk a zs) (msk b zs)))
    (Nat.land (Nat.lor (pneg T zs a) (pneg T zs b))
      (Nat.xor (Nat.land (msk a zs) (msk b zs)) (full zs)))

theorem cov_and (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 32) (a b : ℕ) :
    Cov T zs (a &&& b) (vand T zs a b) := by
  intro i h
  unfold vand at h
  change (((ppos T zs a &&& ppos T zs b) &&& (msk a zs &&& msk b zs)) |||
    ((pneg T zs a ||| pneg T zs b) &&& ((msk a zs &&& msk b zs) ^^^ full zs))).testBit i =
    true at h
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, ppos_bit T zs _ hT,
    pneg_bit T zs _ hT, msk_bit, full_bit] at h ⊢
  by_cases hd : i / 32 < zs.length
  · refine ⟨hd, ?_⟩
    revert h
    cases T.testBit (i % 32) <;> cases a.testBit (i % 32) <;> cases b.testBit (i % 32) <;>
      cases a.testBit (zs.getD (i / 32) 0) <;> cases b.testBit (zs.getD (i / 32) 0) <;>
      simp [hd]
  · simp [hd] at h

def vor (T : ℕ) (zs : List ℕ) (a b : ℕ) : ℕ :=
  Nat.lor (Nat.land (Nat.lor (ppos T zs a) (ppos T zs b)) (Nat.lor (msk a zs) (msk b zs)))
    (Nat.land (Nat.land (pneg T zs a) (pneg T zs b))
      (Nat.xor (Nat.lor (msk a zs) (msk b zs)) (full zs)))

theorem cov_or (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 32) (a b : ℕ) :
    Cov T zs (a ||| b) (vor T zs a b) := by
  intro i h
  unfold vor at h
  change (((ppos T zs a ||| ppos T zs b) &&& (msk a zs ||| msk b zs)) |||
    ((pneg T zs a &&& pneg T zs b) &&& ((msk a zs ||| msk b zs) ^^^ full zs))).testBit i =
    true at h
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, ppos_bit T zs _ hT,
    pneg_bit T zs _ hT, msk_bit, full_bit] at h ⊢
  by_cases hd : i / 32 < zs.length
  · refine ⟨hd, ?_⟩
    revert h
    cases T.testBit (i % 32) <;> cases a.testBit (i % 32) <;> cases b.testBit (i % 32) <;>
      cases a.testBit (zs.getD (i / 32) 0) <;> cases b.testBit (zs.getD (i / 32) 0) <;>
      simp [hd]
  · simp [hd] at h

theorem cov_not (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 32)
    (hzs : ∀ q ∈ zs, q < 32 ∧ T.testBit q = false) (a : ℕ) :
    Cov T zs (ALL ^^^ a) (pkF T zs a) := by
  intro i h
  obtain ⟨h1, h2, h3⟩ := cov_pkF T zs hT a i h
  refine ⟨h1, h2, ?_⟩
  have hq := (hzs (zs.getD (i / 32) 0) (by
    rw [List.getD_eq_getElem _ _ h1]
    exact List.getElem_mem h1)).1
  have hp : i % 32 < 32 := Nat.mod_lt _ (by norm_num)
  rw [Nat.testBit_xor, Nat.testBit_xor, all_bit', all_bit', h3, decide_eq_true hp,
    decide_eq_true hq]

def andL (T : ℕ) (zs : List ℕ) (L : List ℕ) : ℕ :=
  L.foldr (fun w acc => Nat.land (pkF T zs w) acc) (ppos T zs ALL)

theorem fold_bits (T : ℕ) (zs : List ℕ) (i : ℕ) : ∀ (L : List ℕ),
    (andL T zs L).testBit i = true →
    (ppos T zs ALL).testBit i = true ∧ ∀ w ∈ L, (pkF T zs w).testBit i = true
  | [], h => ⟨h, by simp⟩
  | w :: L, h => by
    change (pkF T zs w &&& andL T zs L).testBit i = true at h
    rw [Nat.testBit_and, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := fold_bits T zs i L h.2
    refine ⟨h1, fun w' hw' => ?_⟩
    rcases List.mem_cons.mp hw' with e | e
    · rw [e]
      exact h.1
    · exact h2 w' e

abbrev GoodL (T : ℕ) (zs : List ℕ) (L : List ℕ) : Prop := andL T zs L = 0

theorem goodL_of_good (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 32)
    (hzs : ∀ q ∈ zs, q < 32 ∧ T.testBit q = false) (L : List ℕ) (hg : Good T L.toFinset) :
    GoodL T zs L := by
  by_contra hne
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  obtain ⟨h0, hall⟩ := fold_bits T zs i L hi
  rw [ppos_bit T zs ALL hT] at h0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
  obtain ⟨hk, hTp, _⟩ := h0
  have hq := hzs (zs.getD (i / 32) 0) (by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk)
  have hp : i % 32 < 32 := Nat.mod_lt _ (by norm_num)
  obtain ⟨w, hw, hsep⟩ := hg ⟨i % 32, hp⟩ ⟨zs.getD (i / 32) 0, hq.1⟩ hTp hq.2
  apply hsep
  show w.testBit (i % 32) = w.testBit (zs.getD (i / 32) 0)
  exact (cov_pkF T zs hT w i (hall w (List.mem_toFinset.mp hw))).2.2

theorem good_zero (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 32)
    (hzs : ∀ q ∈ zs, q < 32 ∧ T.testBit q = false) (L : List ℕ) (c P : ℕ)
    (hP : Cov T zs c P) (hg : Good T (insert c L.toFinset)) :
    Nat.land P (andL T zs L) = 0 := by
  by_contra hne
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  change (P &&& andL T zs L).testBit i = true at hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hi
  obtain ⟨_, hall⟩ := fold_bits T zs i L hi.2
  obtain ⟨hk, hTp, hcp⟩ := hP i hi.1
  have hq := hzs (zs.getD (i / 32) 0) (by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk)
  have hp : i % 32 < 32 := Nat.mod_lt _ (by norm_num)
  obtain ⟨w, hw, hsep⟩ := hg ⟨i % 32, hp⟩ ⟨zs.getD (i / 32) 0, hq.1⟩ hTp hq.2
  apply hsep
  show w.testBit (i % 32) = w.testBit (zs.getD (i / 32) 0)
  rcases Finset.mem_insert.mp hw with e | e
  · rw [e]
    exact hcp
  · exact (cov_pkF T zs hT w i (hall w (List.mem_toFinset.mp e))).2.2

def goodC (T : ℕ) (zs : List ℕ) (P : ℕ) (E : List ℕ) : Bool :=
  Nat.beq (Nat.land P (andL T zs E)) 0

theorem goodC_true (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 32)
    (hzs : ∀ q ∈ zs, q < 32 ∧ T.testBit q = false) (E : List ℕ) (c P : ℕ)
    (hP : Cov T zs c P) (hg : Good T (insert c E.toFinset)) : goodC T zs P E = true := by
  unfold goodC
  rw [good_zero T zs hT hzs E c P hP hg]
  rfl

def Sym (T : ℕ) (f : ℕ → ℕ) : Prop :=
  Function.Injective f ∧ f 0 = 0 ∧ f ALL = ALL ∧ (∀ a b : ℕ, f (a &&& b) = f a &&& f b) ∧
    (∀ a b : ℕ, f (a ||| b) = f a ||| f b) ∧ (∀ a : ℕ, f (ALL ^^^ a) = ALL ^^^ f a) ∧
    ∀ G : Finset ℕ, Good T (G.image f) → Good T G

theorem sym_id (T : ℕ) : Sym T (fun x => x) :=
  ⟨fun _ _ h => h, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun G h => by rwa [Finset.image_id'] at h⟩

theorem sym_comp (T : ℕ) (f g : ℕ → ℕ) (hf : Sym T f) (hg : Sym T g) :
    Sym T (fun x => f (g x)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hg
  refine ⟨fun a b h => g1 (f1 h), ?_, ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, fun G h => ?_⟩
  · show f (g 0) = 0
    rw [g2, f2]
  · show f (g ALL) = ALL
    rw [g3, f3]
  · show f (g (a &&& b)) = f (g a) &&& f (g b)
    rw [g4, f4]
  · show f (g (a ||| b)) = f (g a) ||| f (g b)
    rw [g5, f5]
  · show f (g (ALL ^^^ a)) = ALL ^^^ f (g a)
    rw [g6, f6]
  · apply g7
    apply f7
    rw [Finset.image_image]
    exact h

def appG (w : ℕ) : List ℕ → ℕ → ℕ
  | [], init => init
  | j :: π, init => Nat.add (Nat.mul 2 (appG w π init)) (Nat.mod (Nat.shiftRight w j) 2)

theorem appG_cons (w j : ℕ) (π : List ℕ) (init : ℕ) :
    appG w (j :: π) init = Nat.bit (w.testBit j) (appG w π init) := by
  rw [appG]
  show 2 * appG w π init + (w >>> j) % 2 = _
  rw [Nat.bit_val, Nat.toNat_testBit, Nat.shiftRight_eq_div_pow]

def app (π : List ℕ) (w : ℕ) : ℕ := appG w π (w >>> π.length)

theorem appG_bit (w : ℕ) : ∀ (π : List ℕ) (init i : ℕ),
    (appG w π init).testBit i =
      if i < π.length then w.testBit (π.getD i 0) else init.testBit (i - π.length)
  | [], init, i => by simp [appG]
  | j :: π, init, 0 => by simp [appG_cons, Nat.testBit_bit_zero]
  | j :: π, init, i + 1 => by
    rw [appG_cons, Nat.testBit_bit_succ, appG_bit w π init i]
    simp

theorem app_bit (π : List ℕ) (w i : ℕ) :
    (app π w).testBit i = if i < π.length then w.testBit (π.getD i 0) else w.testBit i := by
  unfold app
  rw [appG_bit]
  split
  · rfl
  · rw [Nat.testBit_shiftRight]
    congr 1
    omega

abbrev PermOk (T : ℕ) (π : List ℕ) : Prop :=
  π.length = 32 ∧ (∀ j ∈ π, j < 32) ∧ (∀ j ∈ List.range 32, j ∈ π) ∧
    ∀ i ∈ List.range 32, T.testBit (π.getD i 0) = T.testBit i

theorem sym_app (T : ℕ) (π : List ℕ) (hπ : PermOk T π) : Sym T (app π) := by
  obtain ⟨hlen, hlt, hsurj, hT⟩ := hπ
  have hb : ∀ w i : ℕ, (app π w).testBit i =
      if i < 32 then w.testBit (π.getD i 0) else w.testBit i := by
    intro w i
    rw [app_bit, hlen]
  have hget : ∀ i : ℕ, i < 32 → π.getD i 0 < 32 := by
    intro i hi
    have hi' : i < π.length := by omega
    rw [List.getD_eq_getElem _ _ hi']
    exact hlt _ (List.getElem_mem hi')
  have hidx : ∀ j : ℕ, j < 32 → ∃ i : ℕ, i < 32 ∧ π.getD i 0 = j := by
    intro j hj
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem (hsurj j (List.mem_range.mpr hj))
    exact ⟨i, by omega, by rw [List.getD_eq_getElem _ _ hi]; exact e⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 32
    · obtain ⟨i, hi, e⟩ := hidx j hj
      have h1 := hb a i
      have h2 := hb b i
      rw [if_pos hi, e] at h1 h2
      rw [← h1, ← h2, h]
    · have h1 := hb a j
      have h2 := hb b j
      rw [if_neg hj] at h1 h2
      rw [← h1, ← h2, h]
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [hb]
    simp
  · apply Nat.eq_of_testBit_eq
    intro i
    rw [hb, all_bit', all_bit']
    by_cases hi : i < 32
    · rw [if_pos hi, decide_eq_true (hget i hi), decide_eq_true hi]
    · rw [if_neg hi]
  · intro a b
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [hb, Nat.testBit_and]
    split <;> rfl
  · intro a b
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [hb, Nat.testBit_or]
    split <;> rfl
  · intro a
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [hb, Nat.testBit_xor, all_bit']
    by_cases hi : i < 32
    · rw [if_pos hi, if_pos hi, decide_eq_true (hget i hi), decide_eq_true hi]
    · rw [if_neg hi, if_neg hi]
  · intro G hG p q hp hq
    obtain ⟨p', hp', ep⟩ := hidx p.val p.isLt
    obtain ⟨q', hq', eq⟩ := hidx q.val q.isLt
    have hTp : T.testBit p' = true := by
      rw [← hT p' (List.mem_range.mpr hp'), ep]
      exact hp
    have hTq : T.testBit q' = false := by
      rw [← hT q' (List.mem_range.mpr hq'), eq]
      exact hq
    obtain ⟨w, hw, hne⟩ := hG ⟨p', hp'⟩ ⟨q', hq'⟩ hTp hTq
    obtain ⟨w0, hw0, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨w0, hw0, ?_⟩
    have h1 := hb w0 p'
    have h2 := hb w0 q'
    rw [if_pos hp', ep] at h1
    rw [if_pos hq', eq] at h2
    rw [← h1, ← h2]
    exact hne

def Leaf (T : ℕ) (S : Finset ℕ) : Prop :=
  S.card ≠ 1 ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ c : ℕ, (c = a &&& b ∨ c = a ||| b) →
    ¬ Good T (insert c ((S.erase a).erase b))

theorem leaf_sym (T : ℕ) (f : ℕ → ℕ) (hf : Sym T f) (S : Finset ℕ) (h : Leaf T S) :
    Leaf T (S.image f) := by
  obtain ⟨f1, _, _, f4, f5, _, f7⟩ := hf
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [Finset.card_image_of_injective _ f1]; exact h1, ?_⟩
  intro a ha b hb hab c hc hg
  obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hb
  have hab0 : a0 ≠ b0 := fun e => hab (by rw [e])
  have him : ∀ c0 : ℕ, insert (f c0) (((S.image f).erase (f a0)).erase (f b0)) =
      (insert c0 ((S.erase a0).erase b0)).image f := by
    intro c0
    rw [Finset.image_insert, Finset.image_erase f1, Finset.image_erase f1]
  rcases hc with e | e
  · refine h2 a0 ha0 b0 hb0 hab0 (a0 &&& b0) (Or.inl rfl) (f7 _ ?_)
    rw [← him, f4, ← e]
    exact hg
  · refine h2 a0 ha0 b0 hb0 hab0 (a0 ||| b0) (Or.inr rfl) (f7 _ ?_)
    rw [← him, f5, ← e]
    exact hg

def InF (T D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (δ : ℕ) (S : Finset ℕ) : Prop :=
  (∃ e ∈ fam, e.1 ≤ δ ∧ ∃ f : ℕ → ℕ, Sym T f ∧ e.2.1.toFinset.image f = S) ∨
    (D ≤ δ + 1 ∧ Leaf T S)

theorem inF_mono (T D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (δ δ' : ℕ) (h : δ ≤ δ') (S : Finset ℕ)
    (hS : InF T D fam δ S) : InF T D fam δ' S := by
  rcases hS with ⟨e, he, h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨e, he, le_trans h1 h, h2⟩
  · exact Or.inr ⟨by omega, h2⟩

def Clos (T D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) : Prop :=
  ∀ δ : ℕ, ∀ S : Finset ℕ, InF T D fam δ S → ∀ a ∈ S, ∀ b ∈ S, ∀ c : ℕ,
    ((a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∨ (a = b ∧ c = ALL ^^^ a)) →
    c ∉ S → c ≠ 0 → c ≠ ALL →
    ∀ E : Finset ℕ, E ⊆ S → S ⊆ insert a (insert b E) → Good T (insert c E) →
    ∀ δ' : ℕ, δ' < D → δ' + S.card = δ + E.card + 2 → InF T D fam δ' (insert c E)

def Jn (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (pool : List ℕ) (j : ℕ) : Prop :=
  ∀ G : Finset ℕ, G ⊆ pool.toFinset → 0 ∉ G → ALL ∉ G → Good T G →
    N ≤ G.card + j ∧ ∀ δ : ℕ, δ < D → G.card + j = N + δ → InF T D fam δ G

theorem jn_weak (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (pool : List ℕ) (j : ℕ)
    (h : Jn T N D fam pool j) : Jn T N D fam pool (j + 1) := by
  intro G hG hG0 hGA hg
  obtain ⟨h1, h2⟩ := h G hG hG0 hGA hg
  exact ⟨by omega, fun δ hδ hcd =>
    inF_mono T D fam (δ - 1) δ (by omega) G (h2 (δ - 1) (by omega) (by omega))⟩

theorem jn_step (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (hcl : Clos T D fam)
    (pool : List ℕ) (j c : ℕ) (h : Jn T N D fam pool j) (hc : c ∈ cand pool) (hcn : c ∉ pool) :
    Jn T N D fam (pool ++ [c]) (j + 1) := by
  intro G hG hG0 hGA hg
  have hmem : ∀ x ∈ G, x ≠ c → x ∈ pool.toFinset := by
    intro x hx hxc
    have h1 := hG hx
    simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset,
      List.mem_singleton] at h1
    rcases h1 with h1 | h1
    · exact List.mem_toFinset.mpr h1
    · exact absurd h1 hxc
  by_cases hcG : c ∈ G
  · have hsubE : G.erase c ⊆ pool.toFinset := by
      intro x hx
      obtain ⟨hxc, hxG⟩ := Finset.mem_erase.mp hx
      exact hmem x hxG hxc
    have hcard : (G.erase c).card + 1 = G.card := Finset.card_erase_add_one hcG
    have hIns : insert c (G.erase c) = G := Finset.insert_erase hcG
    have hc0 : c ≠ 0 := fun e => hG0 (e ▸ hcG)
    have hcA : c ≠ ALL := fun e => hGA (e ▸ hcG)
    have key : ∃ a b : ℕ, a ∈ pool ∧ b ∈ pool ∧ a ≠ 0 ∧ a ≠ ALL ∧ b ≠ 0 ∧ b ≠ ALL ∧
        ((a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∨ (a = b ∧ c = ALL ^^^ a)) ∧
        ∀ p q : Fin 32, c.testBit p ≠ c.testBit q →
          a.testBit p ≠ a.testBit q ∨ b.testBit p ≠ b.testBit q := by
      simp only [cand, List.mem_append, List.mem_map, List.mem_flatMap] at hc
      rcases hc with hc | ⟨a, ha, hc⟩ | ⟨a, ha, b, hb, hc⟩
      · exact absurd hc hcn
      · obtain ⟨ha1, ha2, ha3⟩ := (mem_nc pool a).mp ha
        refine ⟨a, a, ha1, ha1, ha2, ha3, ha2, ha3, Or.inr ⟨rfl, hc.symm⟩,
          fun p q hpq => Or.inl ?_⟩
        intro e
        apply hpq
        rw [← hc, Nat.testBit_xor, Nat.testBit_xor, all_bit p, all_bit q, e]
      · obtain ⟨ha1, ha2, ha3⟩ := (mem_nc pool a).mp ha
        obtain ⟨hb1, hb2, hb3⟩ := (mem_nc pool b).mp hb
        have hc' : c = a &&& b ∨ c = a ||| b := by simpa using hc
        have hab : a ≠ b := by
          intro e
          apply hcn
          rcases hc' with e2 | e2
          · rw [e2, e, Nat.and_self]
            exact hb1
          · rw [e2, e, Nat.or_self]
            exact hb1
        refine ⟨a, b, ha1, hb1, ha2, ha3, hb2, hb3, Or.inl ⟨hab, hc'⟩, fun p q hpq => ?_⟩
        by_contra hno
        rw [not_or, not_not, not_not] at hno
        apply hpq
        rcases hc' with e2 | e2
        · rw [e2, Nat.testBit_and, Nat.testBit_and, hno.1, hno.2]
        · rw [e2, Nat.testBit_or, Nat.testBit_or, hno.1, hno.2]
    obtain ⟨a, b, ha, hb, ha0, haA, hb0, hbA, hcand, hsep⟩ := key
    have hgA : Good T (insert a (insert b (G.erase c))) := good_split T G a b c hg hsep
    have hsubA : insert a (insert b (G.erase c)) ⊆ pool.toFinset := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · rw [hx]
        exact List.mem_toFinset.mpr ha
      · rcases Finset.mem_insert.mp hx with hx | hx
        · rw [hx]
          exact List.mem_toFinset.mpr hb
        · exact hsubE hx
    have h0A : 0 ∉ insert a (insert b (G.erase c)) := by
      intro e
      rcases Finset.mem_insert.mp e with e | e
      · exact ha0 e.symm
      · rcases Finset.mem_insert.mp e with e | e
        · exact hb0 e.symm
        · exact hG0 (Finset.mem_of_mem_erase e)
    have hAA : ALL ∉ insert a (insert b (G.erase c)) := by
      intro e
      rcases Finset.mem_insert.mp e with e | e
      · exact haA e.symm
      · rcases Finset.mem_insert.mp e with e | e
        · exact hbA e.symm
        · exact hGA (Finset.mem_of_mem_erase e)
    obtain ⟨h1, h2⟩ := h _ hsubA h0A hAA hgA
    have hcA' : c ∉ insert a (insert b (G.erase c)) :=
      fun e => hcn (List.mem_toFinset.mp (hsubA e))
    have hEA : G.erase c ⊆ insert a (insert b (G.erase c)) :=
      fun x hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
    have h3 := Finset.card_insert_le a (insert b (G.erase c))
    have h4 := Finset.card_insert_le b (G.erase c)
    refine ⟨by omega, fun δ hδ hcd => ?_⟩
    have hfin := hcl ((insert a (insert b (G.erase c))).card + j - N) _
      (h2 _ (by omega) (by omega)) a (Finset.mem_insert_self _ _) b
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) c hcand hcA' hc0 hcA
      (G.erase c) hEA (Finset.Subset.refl _) (by rw [hIns]; exact hg) δ hδ (by omega)
    rw [hIns] at hfin
    exact hfin
  · have hsubG : G ⊆ pool.toFinset := fun x hx => hmem x hx (fun e => hcG (e ▸ hx))
    exact jn_weak T N D fam pool j h G hsubG hG0 hGA hg

theorem filter_ne (L : List ℕ) (a : ℕ) :
    (L.filter (fun x => decide (x ≠ a))).toFinset = L.toFinset.erase a := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_erase, decide_eq_true_eq]
  tauto

theorem filter_ne2 (L : List ℕ) (a b : ℕ) :
    (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))).toFinset =
      (L.toFinset.erase a).erase b := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter, Finset.mem_erase, decide_eq_true_eq,
    Bool.and_eq_true]
  tauto

theorem sub_cases (S E : Finset ℕ) (a b : ℕ) (h1 : E ⊆ S) (h2 : S ⊆ insert a (insert b E)) :
    E = S ∨ E = S.erase a ∨ E = S.erase b ∨ E = (S.erase a).erase b := by
  have hx : ∀ x ∈ S, x = a ∨ x = b ∨ x ∈ E := by
    intro x hx
    rcases Finset.mem_insert.mp (h2 hx) with e | e
    · exact Or.inl e
    · exact Or.inr (Finset.mem_insert.mp e)
  by_cases ha : a ∈ E
  · by_cases hb : b ∈ E
    · left
      refine Finset.Subset.antisymm h1 (fun x hxS => ?_)
      rcases hx x hxS with e | e | e
      · rw [e]
        exact ha
      · rw [e]
        exact hb
      · exact e
    · right; right; left
      ext x
      rw [Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => hb (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2 with e | e | e
      · rw [e]
        exact ha
      · exact absurd e hxS.1
      · exact e
  · by_cases hb : b ∈ E
    · right; left
      ext x
      rw [Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => ha (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2 with e | e | e
      · exact absurd e hxS.1
      · rw [e]
        exact hb
      · exact e
    · right; right; right
      ext x
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨fun hxE => ⟨fun e => hb (by rw [← e]; exact hxE),
        fun e => ha (by rw [← e]; exact hxE), h1 hxE⟩, fun hxS => ?_⟩
      rcases hx x hxS.2.2 with e | e | e
      · exact absurd e hxS.2.1
      · exact absurd e hxS.1
      · exact e

abbrev LeafL (T : ℕ) (zs : List ℕ) (L : List ℕ) : Prop :=
  L.length ≠ 1 ∧ ∀ a ∈ L, ∀ b ∈ L, a < b →
    goodC T zs (vand T zs a b) (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))) = false ∧
    goodC T zs (vor T zs a b) (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))) = false

theorem leaf_of_leafL (T : ℕ) (zs : List ℕ) (hT : T < 2 ^ 32)
    (hzs : ∀ q ∈ zs, q < 32 ∧ T.testBit q = false) (L : List ℕ) (hnd : L.Nodup)
    (h : LeafL T zs L) : Leaf T L.toFinset := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [List.toFinset_card_of_nodup hnd]; exact h1, ?_⟩
  intro a ha b hb hab c hc hg
  have key : ∀ a' b' : ℕ, a' ∈ L → b' ∈ L → a' < b' → (c = a' &&& b' ∨ c = a' ||| b') →
      Good T (insert c ((L.toFinset.erase a').erase b')) → False := by
    intro a' b' ha' hb' hlt hc' hg'
    obtain ⟨hA, hO⟩ := h2 a' ha' b' hb' hlt
    rw [← filter_ne2] at hg'
    rcases hc' with e | e
    · rw [e] at hg'
      rw [goodC_true T zs hT hzs _ _ _ (cov_and T zs hT a' b') hg'] at hA
      exact absurd hA (by decide)
    · rw [e] at hg'
      rw [goodC_true T zs hT hzs _ _ _ (cov_or T zs hT a' b') hg'] at hO
      exact absurd hO (by decide)
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact key a b (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hlt hc hg
  · refine key b a (List.mem_toFinset.mp hb) (List.mem_toFinset.mp ha) hgt ?_ ?_
    · rcases hc with e | e
      · exact Or.inl (e.trans (Nat.and_comm a b))
      · exact Or.inr (e.trans (Nat.or_comm a b))
    · rw [Finset.erase_right_comm]
      exact hg

def leafB (T : ℕ) (zs : List ℕ) (L : List ℕ) : Bool :=
  decide (LeafL T zs L)

theorem leafB_ok (T : ℕ) (zs : List ℕ) (L : List ℕ)
    (h : leafB T zs L = true) : LeafL T zs L := by
  unfold leafB at h
  exact of_decide_eq_true h

theorem map_fin (f : ℕ → ℕ) (L : List ℕ) : (L.map f).toFinset = L.toFinset.image f := by
  ext y
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

def ent (parts : List (List (ℕ × List ℕ × List ℕ))) (t : ℕ) : ℕ × List ℕ × List ℕ :=
  (parts.getD (t / 16) []).getD (t % 16) (0, [], [])

abbrev Hit2 (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Prop :=
  (w % 1000) / 16 < parts.length ∧
    (w % 1000) % 16 < (parts.getD ((w % 1000) / 16) []).length ∧
    (w / 1000) % 10 < perms.length ∧ (ent parts (w % 1000)).1 ≤ lv ∧
    (if (w / 1000) % 10 = 0 then (ent parts (w % 1000)).2.1
      else ((ent parts (w % 1000)).2.1.map (app (perms.getD ((w / 1000) % 10) []))).insertionSort
        (fun x y => x ≤ y)) = E.orderedInsert (fun x y => x ≤ y) c

def hit2B (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Bool :=
  decide (Hit2 parts perms lv E c w)

theorem hit2B_ok (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ)
    (h : hit2B parts perms lv E c w = true) : Hit2 parts perms lv E c w := by
  unfold hit2B at h
  exact of_decide_eq_true h

abbrev Hit (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Prop :=
  w / 10000 = (c + 3 * E.sum) % 100 ∧ hit2B parts perms lv E c w = true

def hitB (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ) : Bool :=
  decide (Hit parts perms lv E c w)

theorem hitB_ok (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ)) (lv : ℕ) (E : List ℕ)
    (c w : ℕ)
    (h : hitB parts perms lv E c w = true) : Hit parts perms lv E c w := by
  unfold hitB at h
  exact of_decide_eq_true h

abbrev Opt (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (wit : List ℕ) (c P lv : ℕ) (E : List ℕ) : Prop :=
  D ≤ lv ∨ goodC T zs P E = false ∨ (∃ w ∈ wit, hitB parts perms lv E c w = true) ∨
    (D ≤ lv + 1 ∧ leafB T zs (c :: E) = true)

def optB (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (wit : List ℕ) (c P lv : ℕ) (E : List ℕ) : Bool :=
  decide (Opt T zs D parts perms wit c P lv E)

theorem optB_ok (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (wit : List ℕ) (c P lv : ℕ) (E : List ℕ)
    (h : optB T zs D parts perms wit c P lv E = true) : Opt T zs D parts perms wit c P lv E := by
  unfold optB at h
  exact of_decide_eq_true h

abbrev OkOne (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a b c P : ℕ) : Prop :=
  c ∈ L ∨ c = 0 ∨ c = ALL ∨ (optB T zs D parts perms wit c P (i + 2) L = true ∧
      optB T zs D parts perms wit c P (i + 1) (L.filter (fun x => decide (x ≠ a))) = true ∧
      optB T zs D parts perms wit c P (i + 1) (L.filter (fun x => decide (x ≠ b))) = true ∧
      optB T zs D parts perms wit c P i
        (L.filter (fun x => decide (x ≠ a) && decide (x ≠ b))) = true)

def okOneB (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a b c P : ℕ) : Bool :=
  decide (OkOne T zs D parts perms i L wit a b c P)

theorem okOneB_ok (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a b c P : ℕ)
    (h : okOneB T zs D parts perms i L wit a b c P = true) : OkOne T zs D parts perms i L wit a b c P := by
  unfold okOneB at h
  exact of_decide_eq_true h

abbrev OkNot (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a c P : ℕ) : Prop :=
  c ∈ L ∨ c = 0 ∨ c = ALL ∨ (optB T zs D parts perms wit c P (i + 2) L = true ∧
      optB T zs D parts perms wit c P (i + 1) (L.filter (fun x => decide (x ≠ a))) = true)

def okNotB (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a c P : ℕ) : Bool :=
  decide (OkNot T zs D parts perms i L wit a c P)

theorem okNotB_ok (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (i : ℕ) (L wit : List ℕ) (a c P : ℕ)
    (h : okNotB T zs D parts perms i L wit a c P = true) : OkNot T zs D parts perms i L wit a c P := by
  unfold okNotB at h
  exact of_decide_eq_true h

abbrev OkEntry (T : ℕ) (zs : List ℕ) (D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (e : ℕ × List ℕ × List ℕ) : Prop :=
  e.2.1.Nodup ∧ e.2.1.length ≠ 1 ∧ ∀ a ∈ e.2.1, ∀ b ∈ e.2.1,
    (a < b → okOneB T zs D parts perms e.1 e.2.1 e.2.2 a b (a &&& b) (vand T zs a b) = true ∧
      okOneB T zs D parts perms e.1 e.2.1 e.2.2 a b (a ||| b) (vor T zs a b) = true) ∧
    (a = b → okNotB T zs D parts perms e.1 e.2.1 e.2.2 a (ALL ^^^ a) (pkF T zs a) = true)

theorem opt_inF (T D : ℕ) (zs : List ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (hT : T < 2 ^ 32) (hzs : ∀ q ∈ zs, q < 32 ∧ T.testBit q = false)
    (hperm : ∀ π ∈ perms, PermOk T π) (wit : List ℕ) (c P : ℕ) (hP : Cov T zs c P) (lv : ℕ)
    (El : List ℕ) (hopt : optB T zs D parts perms wit c P lv El = true) (hnd : El.Nodup)
    (hc : c ∉ El) (hg : Good T (insert c El.toFinset)) (δ' : ℕ) (hδ' : δ' < D) (hle : lv ≤ δ') :
    InF T D parts.flatten δ' (insert c El.toFinset) := by
  have hcons : (c :: El).toFinset = insert c El.toFinset := List.toFinset_cons
  rcases optB_ok T zs D parts perms wit c P lv El hopt with h3 | h3 | ⟨w, hw, hh⟩ | ⟨h3, h4⟩
  · omega
  · rw [goodC_true T zs hT hzs El c P hP hg] at h3
    exact absurd h3 (by decide)
  · obtain ⟨hkey, hh2⟩ := hitB_ok parts perms lv El c w hh
    obtain ⟨hp1, hp2, hp3, hlv', heq⟩ := hit2B_ok parts perms lv El c w hh2
    left
    have hmem : ent parts (w % 1000) ∈ parts.flatten := by
      refine List.mem_flatten.mpr ⟨parts.getD ((w % 1000) / 16) [], ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hp1]
        exact List.getElem_mem hp1
      · unfold ent
        rw [List.getD_eq_getElem _ _ hp2]
        exact List.getElem_mem hp2
    by_cases h0 : (w / 1000) % 10 = 0
    · rw [if_pos h0] at heq
      refine ⟨ent parts (w % 1000), hmem, le_trans hlv' hle, fun x => x, sym_id T, ?_⟩
      rw [Finset.image_id', heq, List.toFinset_eq_of_perm _ _ (List.perm_orderedInsert _ _ _),
        hcons]
    · rw [if_neg h0] at heq
      refine ⟨ent parts (w % 1000), hmem, le_trans hlv' hle,
        app (perms.getD ((w / 1000) % 10) []), sym_app T _ (hperm _ ?_), ?_⟩
      · rw [List.getD_eq_getElem _ _ hp3]
        exact List.getElem_mem hp3
      · rw [← map_fin, ← List.toFinset_eq_of_perm _ _
          (List.perm_insertionSort (fun x y : ℕ => x ≤ y) _),
          heq, List.toFinset_eq_of_perm _ _ (List.perm_orderedInsert _ _ _), hcons]
  · right
    refine ⟨by omega, ?_⟩
    rw [← hcons]
    exact leaf_of_leafL T zs hT hzs (c :: El) (List.nodup_cons.mpr ⟨hc, hnd⟩)
      (leafB_ok T zs _ h4)

theorem clos_rep (T D : ℕ) (zs : List ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (hT : T < 2 ^ 32) (hzs : ∀ q ∈ zs, q < 32 ∧ T.testBit q = false)
    (hperm : ∀ π ∈ perms, PermOk T π)
    (hok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry T zs D parts perms e)
    (e : ℕ × List ℕ × List ℕ) (he : e ∈ parts.flatten) (δ : ℕ) (hlv : e.1 ≤ δ)
    (a : ℕ) (ha : a ∈ e.2.1.toFinset) (b : ℕ) (hb : b ∈ e.2.1.toFinset) (c : ℕ)
    (hcand : (a ≠ b ∧ (c = a &&& b ∨ c = a ||| b)) ∨ (a = b ∧ c = ALL ^^^ a))
    (hcS : c ∉ e.2.1.toFinset) (hc0 : c ≠ 0) (hcA : c ≠ ALL) (E : Finset ℕ)
    (hES : E ⊆ e.2.1.toFinset) (hSE : e.2.1.toFinset ⊆ insert a (insert b E))
    (hg : Good T (insert c E)) (δ' : ℕ) (hδ' : δ' < D)
    (hlev : δ' + e.2.1.toFinset.card = δ + E.card + 2) :
    InF T D parts.flatten δ' (insert c E) := by
  obtain ⟨part, hpart, hep⟩ := List.mem_flatten.mp he
  obtain ⟨hnd, _, hall⟩ := hok part hpart e hep
  have hcL : c ∉ e.2.1 := fun h => hcS (List.mem_toFinset.mpr h)
  have fin : ∀ (P : ℕ), Cov T zs c P → ∀ (lv : ℕ) (El : List ℕ),
      optB T zs D parts perms e.2.2 c P lv El = true → El.Nodup →
      (∀ x ∈ El, x ∈ e.2.1) → El.toFinset = E → lv ≤ δ' →
      InF T D parts.flatten δ' (insert c E) := by
    intro P hP lv El hopt hEl hsub hEq hle
    have h := opt_inF T D zs parts perms hT hzs hperm e.2.2 c P hP lv El hopt hEl
      (fun h2 => hcL (hsub c h2)) (by rw [hEq]; exact hg) δ' hδ' hle
    rw [hEq] at h
    exact h
  have same : E = e.2.1.toFinset → δ' = δ + 2 := by
    intro h1
    rw [h1] at hlev
    omega
  have one : ∀ x : ℕ, x ∈ e.2.1.toFinset → E = e.2.1.toFinset.erase x → δ' = δ + 1 := by
    intro x hx h1
    have hpos : 0 < e.2.1.toFinset.card := Finset.card_pos.mpr ⟨x, hx⟩
    rw [h1, Finset.card_erase_of_mem hx] at hlev
    omega
  have two : ∀ x y : ℕ, x ∈ e.2.1.toFinset → y ∈ e.2.1.toFinset → x ≠ y →
      E = (e.2.1.toFinset.erase x).erase y → δ' = δ := by
    intro x y hx hy hxy h1
    have h2 : 1 < e.2.1.toFinset.card := Finset.one_lt_card.mpr ⟨x, hx, y, hy, hxy⟩
    rw [h1, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩),
      Finset.card_erase_of_mem hx] at hlev
    omega
  have bin : ∀ a' b' : ℕ, a' ∈ e.2.1.toFinset → b' ∈ e.2.1.toFinset → a' < b' →
      (c = a' &&& b' ∨ c = a' ||| b') → e.2.1.toFinset ⊆ insert a' (insert b' E) →
      InF T D parts.flatten δ' (insert c E) := by
    intro a' b' ha' hb' hlt hc hSE'
    obtain ⟨hA, hO⟩ := (hall a' (List.mem_toFinset.mp ha') b' (List.mem_toFinset.mp hb')).1 hlt
    have hP : ∃ P : ℕ, Cov T zs c P ∧
        okOneB T zs D parts perms e.1 e.2.1 e.2.2 a' b' c P = true := by
      rcases hc with e2 | e2
      · rw [e2]
        exact ⟨_, cov_and T zs hT a' b', hA⟩
      · rw [e2]
        exact ⟨_, cov_or T zs hT a' b', hO⟩
    obtain ⟨P, hcov, hok1⟩ := hP
    rcases okOneB_ok T zs D parts perms e.1 e.2.1 e.2.2 a' b' c P hok1 with
      h | h | h | ⟨o2, o1a, o1b, o0⟩
    · exact absurd h hcL
    · exact absurd h hc0
    · exact absurd h hcA
    · rcases sub_cases e.2.1.toFinset E a' b' hES hSE' with h1 | h1 | h1 | h1
      · have h2 := same h1
        exact fin _ hcov _ e.2.1 o2 hnd (fun x hx => hx) h1.symm (by rw [h2]; exact Nat.add_le_add_right hlv 2)
      · have h2 := one a' ha' h1
        exact fin _ hcov _ _ o1a (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne, h1]) (by rw [h2]; exact Nat.add_le_add_right hlv 1)
      · have h2 := one b' hb' h1
        exact fin _ hcov _ _ o1b (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne, h1]) (by rw [h2]; exact Nat.add_le_add_right hlv 1)
      · have h2 := two a' b' ha' hb' (Nat.ne_of_lt hlt) h1
        exact fin _ hcov _ _ o0 (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne2, h1]) (by rw [h2]; exact hlv)
  rcases hcand with ⟨hab, hc⟩ | ⟨hab, hc⟩
  · rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact bin a b ha hb hlt hc hSE
    · refine bin b a hb ha hgt ?_ (by rw [Finset.insert_comm]; exact hSE)
      rcases hc with e2 | e2
      · exact Or.inl (e2.trans (Nat.and_comm a b))
      · exact Or.inr (e2.trans (Nat.or_comm a b))
  · subst hab
    subst hc
    have hcov := cov_not T zs hT hzs a
    rcases okNotB_ok T zs D parts perms e.1 e.2.1 e.2.2 a (ALL ^^^ a) (pkF T zs a)
      ((hall a (List.mem_toFinset.mp ha) a (List.mem_toFinset.mp ha)).2 rfl) with
      h | h | h | ⟨o2, o1⟩
    · exact absurd h hcL
    · exact absurd h hc0
    · exact absurd h hcA
    · have fin1 : E = e.2.1.toFinset.erase a → InF T D parts.flatten δ' (insert (ALL ^^^ a) E) := by
        intro h1
        have h2 := one a ha h1
        exact fin _ hcov _ _ o1 (hnd.filter _) (fun x hx => List.mem_of_mem_filter hx)
          (by rw [filter_ne, h1]) (by rw [h2]; exact Nat.add_le_add_right hlv 1)
      rcases sub_cases e.2.1.toFinset E a a hES hSE with h1 | h1 | h1 | h1
      · have h2 := same h1
        exact fin _ hcov _ e.2.1 o2 hnd (fun x hx => hx) h1.symm (by rw [h2]; exact Nat.add_le_add_right hlv 2)
      · exact fin1 h1
      · exact fin1 h1
      · rw [Finset.erase_idem] at h1
        exact fin1 h1

theorem clos_of_ok (T D : ℕ) (zs : List ℕ) (parts : List (List (ℕ × List ℕ × List ℕ)))
    (perms : List (List ℕ)) (hT : T < 2 ^ 32) (hzs : ∀ q ∈ zs, q < 32 ∧ T.testBit q = false)
    (hperm : ∀ π ∈ perms, PermOk T π)
    (hok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry T zs D parts perms e) :
    Clos T D parts.flatten := by
  intro δ S hS a ha b hb c hcand hcS hc0 hcA E hES hSE hg δ' hδ' hlev
  rcases hS with ⟨e, he, hlv, f, hf, himg⟩ | ⟨hD, hl1, hl2⟩
  · have hf' := hf
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hf
    subst himg
    obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.mp hb
    have hc0ex : ∃ c0 : ℕ, f c0 = c ∧ ((a0 ≠ b0 ∧ (c0 = a0 &&& b0 ∨ c0 = a0 ||| b0)) ∨
        (a0 = b0 ∧ c0 = ALL ^^^ a0)) := by
      rcases hcand with ⟨hab, hc | hc⟩ | ⟨hab, hc⟩
      · exact ⟨a0 &&& b0, by rw [f4, hc], Or.inl ⟨fun e2 => hab (by rw [e2]), Or.inl rfl⟩⟩
      · exact ⟨a0 ||| b0, by rw [f5, hc], Or.inl ⟨fun e2 => hab (by rw [e2]), Or.inr rfl⟩⟩
      · exact ⟨ALL ^^^ a0, by rw [f6, hc], Or.inr ⟨f1 hab, rfl⟩⟩
    obtain ⟨c0, rfl, hcand0⟩ := hc0ex
    have hE0 : (e.2.1.toFinset.filter (fun x => f x ∈ E)).image f = E := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hx⟩, rfl⟩
        exact hx
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hES hy)
        exact ⟨x, ⟨hx, hy⟩, rfl⟩
    have hS0E : e.2.1.toFinset ⊆
        insert a0 (insert b0 (e.2.1.toFinset.filter (fun x => f x ∈ E))) := by
      intro x hx
      rcases Finset.mem_insert.mp (hSE (Finset.mem_image_of_mem f hx)) with h1 | h1
      · rw [f1 h1]
        exact Finset.mem_insert_self _ _
      · rcases Finset.mem_insert.mp h1 with h1 | h1
        · rw [f1 h1]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_filter.mpr ⟨hx, h1⟩))
    have himg2 : (insert c0 (e.2.1.toFinset.filter (fun x => f x ∈ E))).image f =
        insert (f c0) E := by rw [Finset.image_insert, hE0]
    have hcard1 : (e.2.1.toFinset.image f).card = e.2.1.toFinset.card :=
      Finset.card_image_of_injective _ f1
    have hcard2 : E.card = (e.2.1.toFinset.filter (fun x => f x ∈ E)).card := by
      conv_lhs => rw [← hE0]
      exact Finset.card_image_of_injective _ f1
    have hrep := clos_rep T D zs parts perms hT hzs hperm hok e he δ hlv a0 ha0 b0 hb0 c0
      hcand0 (fun h => hcS (Finset.mem_image_of_mem f h)) (fun h => hc0 (by rw [h, f2]))
      (fun h => hcA (by rw [h, f3])) _ (Finset.filter_subset _ _) hS0E
      (f7 _ (by rw [himg2]; exact hg)) δ' hδ' (by omega)
    rw [← himg2]
    rcases hrep with ⟨e', he', hlv', g, hgs, hgi⟩ | ⟨hD', hleaf'⟩
    · refine Or.inl ⟨e', he', hlv', fun x => f (g x), sym_comp T f g hf' hgs, ?_⟩
      rw [← hgi, Finset.image_image]
      rfl
    · exact Or.inr ⟨hD', leaf_sym T f hf' _ hleaf'⟩
  · exfalso
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
    rcases hcand with ⟨hab, hc⟩ | ⟨hab, hc⟩
    · rcases sub_cases S E a b hES hSE with h1 | h1 | h1 | h1
      · rw [h1] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem ha] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem hb] at hlev
        omega
      · rw [h1] at hg
        exact hl2 a ha b hb hab c hc hg
    · subst hab
      rcases sub_cases S E a a hES hSE with h1 | h1 | h1 | h1
      · rw [h1] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem ha] at hlev
        omega
      · rw [h1, Finset.card_erase_of_mem ha] at hlev
        omega
      · rw [h1, Finset.erase_idem, Finset.card_erase_of_mem ha] at hlev
        omega

theorem jn_base (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (zs : List ℕ) (hT : T < 2 ^ 32)
    (hzs : ∀ q ∈ zs, q < 32 ∧ T.testBit q = false) (base : List ℕ)
    (hpool : pool0 = base ++ [0, ALL])
    (hnec : ∀ a ∈ base, ¬ GoodL T zs (base.filter (fun x => decide (x ≠ a))))
    (hbase : ∃ e ∈ fam, e.1 = 0 ∧ e.2.1 = base) (hcard : base.length = N) (hnd : base.Nodup) :
    Jn T N D fam pool0 0 := by
  intro G hG hG0 hGA hg
  have hGb : G ⊆ base.toFinset := by
    intro x hx
    have h1 := List.mem_toFinset.mp (hG hx)
    rw [hpool] at h1
    rcases List.mem_append.mp h1 with h1 | h1
    · exact List.mem_toFinset.mpr h1
    · exfalso
      rcases List.mem_cons.mp h1 with h1 | h1
      · exact hG0 (by rw [← h1]; exact hx)
      · exact hGA (by rw [← List.mem_singleton.mp h1]; exact hx)
  have hbG : base.toFinset ⊆ G := by
    intro a ha
    by_contra hna
    apply hnec a (List.mem_toFinset.mp ha)
    apply goodL_of_good T zs hT hzs
    rw [filter_ne]
    exact good_mono T G _ (fun x hx => Finset.mem_erase.mpr
      ⟨fun e => hna (by rw [← e]; exact hx), hGb hx⟩) hg
  have hEq : G = base.toFinset := Finset.Subset.antisymm hGb hbG
  have hc : G.card = N := by rw [hEq, List.toFinset_card_of_nodup hnd, hcard]
  obtain ⟨e0, he0, h01, h02⟩ := hbase
  exact ⟨by omega, fun δ _ _ => Or.inl ⟨e0, he0, by omega, fun x => x, sym_id T, by
    rw [Finset.image_id', h02]
    exact hEq.symm⟩⟩

theorem main (T N D : ℕ) (fam : List (ℕ × List ℕ × List ℕ)) (hcl : Clos T D fam)
    (hT1 : ∃ p : Fin 32, T.testBit p = true) (hT0 : ∃ q : Fin 32, T.testBit q = false) :
    ∀ (gs : List Gate) (pool : List ℕ) (ws : Fin 32 → List Bool) (L j o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) →
    (∀ p, (ws p).length = L) → Inv pool ws → Jn T N D fam pool j →
    (∀ p : Fin 32, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws p)).getD o false = T.testBit p) →
    N ≤ 1 + (j + gs.length) ∧
      ∀ δ : ℕ, δ < D → 1 + (j + gs.length) = N + δ → ∃ m : ℕ, InF T D fam δ {m}
  | [], pool, ws, L, j, o, _, _, hI, hJ, hout => by
    obtain ⟨m, hm, hmb⟩ := hI.2.2 o
    have hmT : ∀ p : Fin 32, m.testBit p = T.testBit p := fun p => (hmb p).trans (hout p)
    have hg : Good T {m} := by
      intro p q hp hq
      refine ⟨m, Finset.mem_singleton_self m, ?_⟩
      rw [hmT p, hmT q, hp, hq]
      simp
    have hm0 : (0 : ℕ) ∉ ({m} : Finset ℕ) := by
      intro e
      obtain ⟨p, hp⟩ := hT1
      have h1 := hmT p
      rw [← Finset.mem_singleton.mp e, Nat.zero_testBit, hp] at h1
      exact absurd h1 (by simp)
    have hmA : ALL ∉ ({m} : Finset ℕ) := by
      intro e
      obtain ⟨q, hq⟩ := hT0
      have h1 := hmT q
      rw [← Finset.mem_singleton.mp e, all_bit q, hq] at h1
      exact absurd h1 (by simp)
    obtain ⟨h1, h2⟩ := hJ {m} (by
      intro x hx
      rw [Finset.mem_singleton.mp hx]
      exact List.mem_toFinset.mpr hm) hm0 hmA hg
    rw [Finset.card_singleton] at h1 h2
    simp only [List.length_nil, Nat.add_zero]
    exact ⟨by omega, fun δ hδ e => ⟨m, h2 δ hδ (by omega)⟩⟩
  | g :: gs, pool, ws, L, j, o, hg, hL, hI, hJ, hout => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g hop hlen
    have hout' : ∀ p : Fin 32, (gs.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)])).getD o false =
          T.testBit p :=
      fun p => by
        have h3 := hout p
        rw [List.foldl_cons] at h3
        exact h3
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (by simp [hg'])
    have hL' : ∀ p, (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]).length =
        L + 1 :=
      fun p => by simp [hL p]
    have hlen2 : 1 + (j + (g :: gs).length) = 1 + ((j + 1) + gs.length) := by
      simp only [List.length_cons]
      omega
    rw [hlen2]
    by_cases hcin : c ∈ pool
    · exact main T N D fam hcl hT1 hT0 gs pool _ (L + 1) (j + 1) o hg' hL'
        (inv_step pool pool ws L hL hI _ c hcv (fun m hm => hm) hcin)
        (jn_weak T N D fam pool j hJ) hout'
    · exact main T N D fam hcl hT1 hT0 gs (pool ++ [c]) _ (L + 1) (j + 1) o hg' hL'
        (inv_step pool (pool ++ [c]) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp))
        (jn_step T N D fam hcl pool j c hJ hc hcin) hout'

theorem lower (T N D : ℕ) (parts : List (List (ℕ × List ℕ × List ℕ))) (perms : List (List ℕ))
    (zs base : List ℕ) (hT : T < 2 ^ 32)
    (hT1 : ∃ p : Fin 32, T.testBit p = true) (hT0 : ∃ q : Fin 32, T.testBit q = false)
    (hzs : ∀ q ∈ zs, q < 32 ∧ T.testBit q = false) (hperm : ∀ π ∈ perms, PermOk T π)
    (hok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry T zs D parts perms e)
    (hpool : pool0 = base ++ [0, ALL])
    (hnec : ∀ a ∈ base, ¬ GoodL T zs (base.filter (fun x => decide (x ≠ a))))
    (hbase : ∃ e ∈ parts.flatten, e.1 = 0 ∧ e.2.1 = base) (hcard : base.length = N)
    (hnd : base.Nodup)
    (C : Circuit) (hC : FanInTwo C) (hev : ∀ p : Fin 32, C.eval (X p) = T.testBit p) :
    N + D ≤ C.gates.length + 1 := by
  obtain ⟨h1, h2⟩ := main T N D parts.flatten (clos_of_ok T D zs parts perms hT hzs hperm hok)
    hT1 hT0 C.gates pool0 X 5 0 C.output hC X_len inv0
    (jn_base T N D parts.flatten zs hT hzs base hpool hnec hbase hcard hnd) hev
  by_contra hlt
  obtain ⟨m, hm⟩ := h2 (1 + (0 + C.gates.length) - N) (by omega) (by omega)
  rcases hm with ⟨e, he, _, f, hf, hem⟩ | ⟨_, hl1, _⟩
  · obtain ⟨part, hpart, hep⟩ := List.mem_flatten.mp he
    obtain ⟨hnd', hlen, _⟩ := hok part hpart e hep
    apply hlen
    rw [← List.toFinset_card_of_nodup hnd', ← Finset.card_image_of_injective _ hf.1, hem,
      Finset.card_singleton]
  · exact hl1 (Finset.card_singleton m)

def tab : ℕ := 4008241856

def zs : List ℕ := [0, 1, 2, 3, 4, 5, 8, 10, 12, 16, 17, 18, 20, 24, 28]

def t0 : ℕ := 255
def t1 : ℕ := 13107
def t2 : ℕ := 43690
def t3 : ℕ := 61680
def t4 : ℕ := 65535
def t5 : ℕ := 5570645
def t6 : ℕ := 11141290
def t7 : ℕ := 13369548
def t8 : ℕ := 15728880
def t9 : ℕ := 16711680
def t10 : ℕ := 16711935
def t11 : ℕ := 16777215
def t12 : ℕ := 252645135
def t13 : ℕ := 268374015
def t14 : ℕ := 286331153
def t15 : ℕ := 572662306
def t16 : ℕ := 808464432
def t17 : ℕ := 855651072
def t18 : ℕ := 858980352
def t19 : ℕ := 858993459
def t20 : ℕ := 1061109567
def t21 : ℕ := 1431655765
def t22 : ℕ := 2155905152
def t23 : ℕ := 2290614272
def t24 : ℕ := 2290649224
def t25 : ℕ := 2684395520
def t26 : ℕ := 2694840320
def t27 : ℕ := 2694881440
def t28 : ℕ := 2829625512
def t29 : ℕ := 2852126720
def t30 : ℕ := 2852170240
def t31 : ℕ := 2861083272
def t32 : ℕ := 2862656160
def t33 : ℕ := 2863267840
def t34 : ℕ := 2863302792
def t35 : ℕ := 2863308960
def t36 : ℕ := 2863311360
def t37 : ℕ := 2863311530
def t38 : ℕ := 2863333375
def t39 : ℕ := 2868882175
def t40 : ℕ := 2947526575
def t41 : ℕ := 3149642683
def t42 : ℕ := 3233857728
def t43 : ℕ := 3422604288
def t44 : ℕ := 3435921408
def t45 : ℕ := 3435970752
def t46 : ℕ := 3435973836
def t47 : ℕ := 3439316223
def t48 : ℕ := 3772825792
def t49 : ℕ := 3772834016
def t50 : ℕ := 3941264106
def t51 : ℕ := 3974889472
def t52 : ℕ := 3974950124
def t53 : ℕ := 4004179626
def t54 : ℕ := 4006407884
def t55 : ℕ := 4008574976
def t56 : ℕ := 4008618666
def t57 : ℕ := 4008636142
def t58 : ℕ := 4026531840
def t59 : ℕ := 4026593280
def t60 : ℕ := 4037079200
def t61 : ℕ := 4039176384
def t62 : ℕ := 4042260480
def t63 : ℕ := 4042301600
def t64 : ℕ := 4042309824
def t65 : ℕ := 4042321920
def t66 : ℕ := 4042322160
def t67 : ℕ := 4042326015
def t68 : ℕ := 4043305215
def t69 : ℕ := 4092851187
def t70 : ℕ := 4126537205
def t71 : ℕ := 4177066232
def t72 : ℕ := 4205509290
def t73 : ℕ := 4210096880
def t74 : ℕ := 4210688000
def t75 : ℕ := 4210731690
def t76 : ℕ := 4210749680
def t77 : ℕ := 4210752250
def t78 : ℕ := 4243651824
def t79 : ℕ := 4244373504
def t80 : ℕ := 4244425932
def t81 : ℕ := 4244435184
def t82 : ℕ := 4244438268
def t83 : ℕ := 4278124286
def t84 : ℕ := 4278190080
def t85 : ℕ := 4278233600
def t86 : ℕ := 4278255360
def t87 : ℕ := 4281597747
def t88 : ℕ := 4289396650
def t89 : ℕ := 4290838464
def t90 : ℕ := 4291624908
def t91 : ℕ := 4293918720
def t92 : ℕ := 4293980400
def t93 : ℕ := 4293982960
def t94 : ℕ := 4293984000
def t95 : ℕ := 4293984192
def t96 : ℕ := 4293984240
def t97 : ℕ := 4294639610
def t98 : ℕ := 4294901760
def t99 : ℕ := 4294902015
def t100 : ℕ := 4294914867
def t101 : ℕ := 4294936712
def t102 : ℕ := 4294942880
def t103 : ℕ := 4294945280
def t104 : ℕ := 4294945450
def t105 : ℕ := 4294951104
def t106 : ℕ := 4294954188
def t107 : ℕ := 4294962926
def t108 : ℕ := 4294963200
def t109 : ℕ := 4294963440
def t110 : ℕ := 4294966010
def t111 : ℕ := 4294966524
def t112 : ℕ := 4294967040
def t113 : ℕ := 4294967280

def base : List ℕ := [t37, t46, t66, t86, t98]

def perms : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31],
  [0, 2, 1, 3, 8, 10, 9, 11, 4, 6, 5, 7, 12, 14, 13, 15, 16, 18, 17, 19, 24, 26, 25, 27, 20, 22, 21, 23, 28, 30, 29, 31]]

def fam0 : List (ℕ × List ℕ × List ℕ) := [
  (0, [t37, t46, t66, t86, t98], [131048, 31096, 890048, 970096, 931032, 731080, 930032, 730080, 930016, 730064, 620112, 800176, 780128, 880224, 780144, 881001, 780160, 880033, 661144, 60001, 261128, 461224, 461160, 261033, 180192, 780017, 180208, 780049, 181208, 781049]),
  (2, [t37, t46, t66, t82, t86, t98], [171167, 930119, 971085, 651163, 970053, 970099, 500152, 240140, 621057, 901232, 821234, 221188, 620225, 420092, 660076, 620093]),
  (2, [t37, t46, t66, t86, t103], [680078, 181174]),
  (3, [t4, t37, t38, t46, t66, t86], []),
  (3, [t8, t10, t37, t46, t66, t98], []),
  (3, [t10, t37, t46, t62, t66, t98], []),
  (3, [t14, t37, t46, t66, t86, t98], []),
  (3, [t19, t37, t43, t66, t86, t98], []),
  (3, [t19, t37, t66, t86, t98, t106], []),
  (3, [t30, t37, t46, t66, t96, t98], []),
  (3, [t37, t38, t46, t66, t86, t98], []),
  (3, [t37, t46, t61, t66, t86, t98], [220034]),
  (3, [t37, t46, t66, t74, t86, t98], []),
  (3, [t37, t46, t66, t86, t98, t102], []),
  (3, [t33, t37, t46, t86, t92], []),
  (3, [t37, t46, t92, t98, t112], [])]

def fam1 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t4, t37, t46, t66, t86], [180000, 230064, 381081, 140081, 181065, 180065, 530114, 380003, 911114, 61003, 430146, 780067, 431146, 781067, 870178, 50019, 30194, 130083, 30210, 131099, 911210, 310099, 511194, 711083, 430035, 30115]),
  (2, [t37, t46, t66, t86, t96, t98], [331199, 90199, 131117, 130117, 130115, 281157, 180009, 980089, 480188, 61009, 860157, 301089, 221188, 581218, 580218, 181173, 180173, 580156, 180109]),
  (2, [t37, t46, t66, t86, t108], []),
  (3, [t4, t37, t46, t57, t66, t86], []),
  (3, [t8, t37, t46, t66, t86, t98], []),
  (3, [t10, t37, t46, t66, t68, t98], []),
  (3, [t15, t19, t37, t66, t86, t98], []),
  (3, [t19, t37, t44, t66, t86, t98], []),
  (3, [t19, t37, t66, t86, t98, t109], []),
  (3, [t30, t37, t46, t73, t86, t98], []),
  (3, [t37, t39, t46, t66, t86, t98], []),
  (3, [t37, t46, t62, t66, t86, t109], [421046, 980222]),
  (3, [t37, t46, t66, t75, t86, t98], []),
  (3, [t37, t46, t66, t86, t98, t103], [80161, 581209]),
  (3, [t33, t46, t56, t66, t86], []),
  (3, [t37, t46, t96, t109, t112], [80079, 821079])]

def fam2 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t10, t37, t46, t66, t98], [180000, 230080, 380129, 140113, 180097, 180065, 530179, 380132, 110211, 860196, 430004, 780021, 430036, 780133, 870068, 50212, 30084, 130037, 30116, 130149, 910148, 310053, 710180, 510165, 430005, 30181]),
  (2, [t37, t46, t66, t86, t98, t104], [631008, 390231, 431165, 430149, 430131, 831098, 380169, 480137, 981185, 640045, 380075, 480077, 480125, 581209, 81107, 381091, 481093]),
  (2, [t37, t46, t66, t89, t98], []),
  (3, [t4, t37, t46, t59, t66, t86], []),
  (3, [t9, t10, t37, t46, t66, t98], []),
  (3, [t10, t37, t46, t66, t77, t98], []),
  (3, [t15, t37, t46, t66, t86, t98], []),
  (3, [t19, t37, t57, t66, t86, t98], []),
  (3, [t19, t37, t66, t86, t98, t112], []),
  (3, [t30, t37, t54, t66, t86, t98], []),
  (3, [t37, t40, t46, t66, t86, t98], []),
  (3, [t37, t46, t62, t66, t94, t98], []),
  (3, [t37, t46, t66, t76, t86, t98], []),
  (3, [t37, t46, t66, t86, t98, t107], []),
  (3, [t36, t46, t66, t84, t86], []),
  (3, [t36, t45, t66, t86], [])]

def fam3 : List (ℕ × List ℕ × List ℕ) := [
  (1, [t19, t37, t66, t86, t98], [660000, 430096, 820145, 621129, 620113, 620081, 130022, 900214, 390054, 940087, 790086, 540151, 590118, 740215, 470166, 570103, 470182, 570167, 470198, 570231, 870055, 470199, 870071, 470024, 870135, 470040]),
  (2, [t37, t46, t66, t86, t98, t109], [331040, 90024, 131197, 130181, 130147, 931082, 180153, 980201, 480077, 661125, 821161, 21233, 901217, 620093, 181173, 580059, 580027, 180141, 581123, 180109]),
  (2, [t37, t46, t66, t94, t98], [61221, 861014, 181015, 180222]),
  (3, [t4, t37, t46, t62, t66, t86], []),
  (3, [t9, t37, t46, t66, t86, t98], []),
  (3, [t10, t37, t46, t66, t82, t98], []),
  (3, [t16, t19, t37, t66, t86, t98], []),
  (3, [t19, t37, t59, t66, t86, t98], []),
  (3, [t20, t37, t46, t66, t86, t98], []),
  (3, [t30, t46, t66, t86, t88, t98], []),
  (3, [t37, t41, t46, t66, t86, t98], []),
  (3, [t37, t46, t62, t86, t98, t109], [421062, 981015]),
  (3, [t37, t46, t66, t78, t86, t98], []),
  (3, [t37, t46, t66, t86, t98, t108], []),
  (3, [t36, t46, t66, t84, t98], []),
  (3, [t36, t46, t66, t85], [])]

def fam4 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t4, t37, t46, t66, t86, t98], [280130, 130010, 661130, 811010, 180162, 530139, 181162, 531139, 30226, 130131, 711226, 511131, 430051, 30147, 431051, 31147]),
  (2, [t4, t10, t37, t46, t66], [430032, 430016]),
  (2, [t37, t54, t66, t86, t98], []),
  (3, [t4, t37, t46, t66, t67, t86], []),
  (3, [t10, t24, t37, t46, t66, t98], []),
  (3, [t10, t37, t46, t66, t84, t98], []),
  (3, [t16, t37, t46, t66, t86, t98], []),
  (3, [t19, t37, t62, t66, t86, t98], []),
  (3, [t22, t37, t46, t66, t86, t98], []),
  (3, [t31, t37, t46, t66, t86, t98], [140066]),
  (3, [t37, t46, t49, t57, t86, t98], []),
  (3, [t37, t46, t63, t66, t86, t98], []),
  (3, [t37, t46, t66, t79, t82, t86], []),
  (3, [t37, t46, t66, t86, t98, t110], []),
  (3, [t36, t46, t66, t86, t103], [680063]),
  (3, [t36, t46, t96, t109], [])]

def fam5 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t10, t37, t46, t66, t86, t98], [280195, 130026, 860227, 611042, 180020, 530155, 180052, 530204, 30100, 130085, 510164, 710101, 430228, 30117, 430069, 30197]),
  (2, [t4, t19, t37, t66, t86], [870048, 910016]),
  (3, [t0, t37, t46, t66, t86, t98], []),
  (3, [t4, t37, t46, t66, t77, t86], []),
  (3, [t10, t27, t37, t46, t66, t98], []),
  (3, [t10, t37, t46, t66, t88, t98], []),
  (3, [t17, t19, t37, t66, t86, t98], []),
  (3, [t19, t37, t66, t69, t86, t98], []),
  (3, [t23, t37, t46, t66, t86, t98], []),
  (3, [t32, t37, t46, t66, t86, t98], [381034]),
  (3, [t37, t46, t49, t66, t86, t98], [541066]),
  (3, [t37, t46, t64, t66, t86, t98], [500238, 621002, 900190]),
  (3, [t37, t46, t66, t79, t86, t98], []),
  (3, [t37, t46, t66, t86, t98, t111], []),
  (3, [t36, t46, t66, t86, t104], [680063]),
  (3, [t37, t46, t93, t103], [])]

def fam6 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t19, t37, t46, t66, t86, t98], [440038, 210058, 700070, 250171, 100102, 851187, 900134, 50220, 310150, 490039, 350230, 750119, 950007, 150183, 150023, 950008]),
  (2, [t10, t12, t37, t46, t98], [431032, 430032]),
  (3, [t1, t37, t46, t66, t86, t98], []),
  (3, [t4, t37, t46, t66, t82, t86], []),
  (3, [t10, t30, t37, t46, t66, t98], []),
  (3, [t10, t37, t46, t66, t90, t98], []),
  (3, [t17, t37, t46, t66, t86, t98], []),
  (3, [t19, t37, t66, t77, t86, t98], []),
  (3, [t25, t37, t46, t66, t86, t98], []),
  (3, [t33, t37, t44, t46, t66, t86], [340193, 781030, 540030]),
  (3, [t37, t46, t50, t66, t86, t98], [740177]),
  (3, [t37, t46, t64, t86, t98, t106], []),
  (3, [t37, t46, t66, t80, t86, t98], [820209, 620225]),
  (3, [t37, t46, t66, t86, t98, t113], []),
  (3, [t36, t46, t66, t86, t109], [920047, 480079]),
  (3, [t37, t46, t93, t112], [])]

def fam7 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t24, t37, t46, t66, t86, t98], [851150, 610150, 651068, 650068, 650178, 900072, 700203, 301072, 301203, 100088, 500236]),
  (2, [t10, t19, t37, t66, t98], [870048, 910032]),
  (3, [t2, t4, t37, t46, t66, t86], []),
  (3, [t4, t37, t46, t66, t86, t96], []),
  (3, [t10, t33, t37, t46, t66, t98], []),
  (3, [t10, t37, t46, t66, t96, t98], []),
  (3, [t18, t19, t37, t66, t86, t98], []),
  (3, [t19, t37, t66, t82, t86, t98], []),
  (3, [t26, t37, t46, t66, t86, t98], []),
  (3, [t33, t37, t46, t66, t84, t86], [581225, 880205, 980014]),
  (3, [t37, t46, t52, t66, t86, t98], [501237, 740177, 300158]),
  (3, [t37, t46, t65, t66, t86, t98], [580050, 580018]),
  (3, [t37, t46, t66, t81, t86, t98], [821161, 620225]),
  (3, [t37, t46, t66, t86, t104, t112], [780094, 981190, 380002]),
  (3, [t36, t46, t66, t96, t98], [480079])]

def fam8 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t27, t37, t46, t66, t86, t98], [331007, 90166, 131164, 130084, 130194, 900072, 620122, 580104, 181060, 580120, 180013, 60136]),
  (2, [t10, t21, t46, t66, t98], [231048, 30032]),
  (3, [t2, t37, t46, t66, t86, t98], []),
  (3, [t4, t37, t46, t66, t86, t104], []),
  (3, [t10, t37, t39, t46, t66, t98], []),
  (3, [t10, t37, t46, t66, t98, t99], []),
  (3, [t18, t37, t46, t66, t86, t98], []),
  (3, [t19, t37, t66, t84, t86, t98], []),
  (3, [t27, t37, t42, t46, t86, t98], [740177, 581237]),
  (3, [t33, t37, t46, t66, t86, t104], []),
  (3, [t37, t46, t55, t57, t66, t86], []),
  (3, [t37, t46, t66, t67, t86, t98], []),
  (3, [t37, t46, t66, t83, t86, t98], []),
  (3, [t37, t46, t66, t86, t109, t112], [480110, 221110, 780031, 580018]),
  (3, [t37, t46, t48, t86, t98], [])]

def fam9 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t30, t37, t46, t66, t86, t98], [931056, 331230, 90182, 131148, 130100, 130210, 301072, 140066, 221106, 340041, 580104, 381034, 180235, 580025, 580168, 380002, 180029, 580216, 180057, 280232, 80184, 661136, 180009, 580200]),
  (2, [t19, t21, t66, t86, t98], [711048, 470048]),
  (3, [t3, t4, t37, t46, t66, t86], []),
  (3, [t4, t37, t46, t66, t86, t109], []),
  (3, [t10, t37, t42, t46, t66, t98], []),
  (3, [t10, t37, t46, t66, t98, t104], []),
  (3, [t19, t24, t37, t66, t86, t98], []),
  (3, [t19, t37, t66, t86, t87, t98], []),
  (3, [t28, t37, t46, t66, t86, t98], []),
  (3, [t33, t37, t46, t66, t86, t109], []),
  (3, [t37, t46, t55, t66, t86, t98], []),
  (3, [t37, t46, t66, t68, t86, t98], []),
  (3, [t37, t46, t66, t86, t91, t98], [581050, 580050]),
  (3, [t37, t46, t66, t90, t96, t98], [220034]),
  (3, [t37, t46, t51, t66, t86], [])]

def fam10 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t33, t37, t46, t66, t86, t98], [331023, 90198, 131180, 130116, 130226, 100088, 421170, 580120, 180044, 580168, 181124, 80184, 180169, 280137, 860105, 180153, 580121]),
  (2, [t36, t46, t66, t86, t98], [280078, 880126, 880110, 280062, 280046]),
  (3, [t3, t37, t46, t66, t86, t98], []),
  (3, [t5, t37, t46, t66, t86, t98], []),
  (3, [t10, t37, t43, t46, t66, t98], []),
  (3, [t10, t37, t46, t66, t98, t106], []),
  (3, [t19, t27, t37, t66, t86, t98], []),
  (3, [t19, t37, t66, t86, t88, t98], []),
  (3, [t29, t37, t46, t66, t86, t98], []),
  (3, [t33, t46, t66, t86, t98, t104], []),
  (3, [t37, t46, t56, t66, t86, t98], [60030, 861142, 340193]),
  (3, [t37, t46, t66, t69, t86, t98], []),
  (3, [t37, t46, t66, t86, t92, t98], []),
  (3, [t37, t46, t66, t96, t98, t112], [480126, 780031, 580050]),
  (3, [t37, t46, t64, t86, t105], [941063, 21095])]

def fam11 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t37, t46, t57, t66, t86, t98], [391039, 150039, 910006, 191212, 190212, 190019, 241189, 640189, 740177, 540090, 74, 240140, 941177, 741090, 201074, 41140, 340193, 140154, 600138, 640045]),
  (2, [t37, t46, t49, t86, t98], []),
  (3, [t4, t24, t37, t46, t66, t86], []),
  (3, [t6, t10, t37, t46, t66, t98], []),
  (3, [t10, t37, t44, t46, t66, t98], []),
  (3, [t10, t37, t46, t66, t98, t109], []),
  (3, [t19, t30, t37, t66, t86, t98], []),
  (3, [t19, t37, t66, t86, t90, t98], []),
  (3, [t30, t33, t46, t66, t86, t98], [80161, 80205]),
  (3, [t34, t37, t46, t66, t86, t98], []),
  (3, [t37, t46, t58, t66, t86, t98], []),
  (3, [t37, t46, t66, t70, t86, t98], []),
  (3, [t37, t46, t66, t86, t97, t98], []),
  (3, [t37, t57, t66, t86, t90, t98], [140066]),
  (3, [t37, t46, t64, t86, t109], [941063, 101111])]

def fam12 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t37, t46, t59, t66, t86, t98], [531055, 290055, 530229, 331228, 330228, 330035, 580104, 280219, 621104, 301219, 780186, 580018, 380061, 980202, 381218, 380218]),
  (2, [t37, t46, t55, t66, t86], []),
  (3, [t4, t27, t37, t46, t66, t86], []),
  (3, [t6, t37, t46, t66, t86, t98], []),
  (3, [t10, t37, t46, t47, t66, t98], []),
  (3, [t10, t37, t46, t66, t98, t112], []),
  (3, [t19, t33, t37, t66, t86, t98], []),
  (3, [t19, t37, t66, t86, t96, t98], []),
  (3, [t30, t37, t46, t66, t84, t98], [581209, 880205, 980221]),
  (3, [t35, t37, t46, t66, t86, t98], []),
  (3, [t37, t46, t59, t66, t86, t108], []),
  (3, [t37, t46, t66, t71, t86, t98], []),
  (3, [t37, t46, t66, t86, t98, t99], []),
  (3, [t30, t33, t46, t66, t84], []),
  (3, [t37, t46, t64, t95, t98], [781095])]

def fam13 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t37, t46, t62, t66, t86, t98], [531135, 290071, 531213, 331069, 330005, 330051, 580120, 280028, 221168, 700108, 261200, 61121, 780186, 580050, 381172, 980043, 380059, 380027]),
  (2, [t37, t46, t64, t86, t98], [420206, 540174]),
  (3, [t4, t30, t37, t46, t66, t86], []),
  (3, [t7, t10, t37, t46, t66, t98], []),
  (3, [t10, t37, t46, t57, t66, t98], []),
  (3, [t11, t37, t46, t66, t86, t98], []),
  (3, [t19, t37, t41, t66, t86, t98], []),
  (3, [t19, t37, t66, t86, t98, t100], []),
  (3, [t30, t37, t46, t66, t86, t103], []),
  (3, [t36, t37, t46, t66, t86, t98], [380002, 980094]),
  (3, [t37, t46, t59, t66, t96, t98], []),
  (3, [t37, t46, t66, t72, t86, t98], []),
  (3, [t37, t46, t66, t86, t98, t100], []),
  (3, [t30, t37, t46, t92, t98], []),
  (3, [t37, t46, t66, t94, t109], [])]

def fam14 : List (ℕ × List ℕ × List ℕ) := [
  (2, [t37, t46, t66, t77, t86, t98], [631183, 390103, 431101, 430037, 430083, 401189, 381073, 240140, 481157, 381011, 480188, 380012, 480077]),
  (2, [t37, t46, t66, t79, t86], []),
  (3, [t4, t33, t37, t46, t66, t86], []),
  (3, [t7, t37, t46, t66, t86, t98], []),
  (3, [t10, t37, t46, t59, t66, t98], []),
  (3, [t13, t37, t46, t66, t86, t98], []),
  (3, [t19, t37, t42, t66, t86, t98], []),
  (3, [t19, t37, t66, t86, t98, t104], []),
  (3, [t30, t37, t46, t66, t88, t98], []),
  (3, [t36, t46, t66, t86, t98, t112], []),
  (3, [t37, t46, t60, t66, t86, t98], []),
  (3, [t37, t46, t66, t73, t86, t98], []),
  (3, [t37, t46, t66, t86, t98, t101], []),
  (3, [t30, t46, t53, t66, t98], []),
  (3, [t37, t46, t66, t95, t98], [141111])]

def chunk0 : List (List (ℕ × List ℕ × List ℕ)) := [fam0, fam1, fam2, fam3, fam4, fam5, fam6, fam7, fam8, fam9, fam10, fam11, fam12, fam13, fam14]

def parts : List (List (ℕ × List ℕ × List ℕ)) := [fam0, fam1, fam2, fam3, fam4, fam5, fam6, fam7, fam8, fam9, fam10, fam11, fam12, fam13, fam14]

set_option synthInstance.maxSize 4000 in
def okB (e : ℕ × List ℕ × List ℕ) : Bool := decide (OkEntry tab zs 4 parts perms e)

set_option synthInstance.maxSize 4000 in
theorem okB_ok (e : ℕ × List ℕ × List ℕ) (h : okB e = true) : OkEntry tab zs 4 parts perms e := by
  unfold okB at h
  exact of_decide_eq_true h

theorem ok0 : fam0.all okB = true := by decide +kernel

theorem ok1 : fam1.all okB = true := by decide +kernel

theorem ok2 : fam2.all okB = true := by decide +kernel

theorem ok3 : fam3.all okB = true := by decide +kernel

theorem ok4 : fam4.all okB = true := by decide +kernel

theorem ok5 : fam5.all okB = true := by decide +kernel

theorem ok6 : fam6.all okB = true := by decide +kernel

theorem ok7 : fam7.all okB = true := by decide +kernel

theorem ok8 : fam8.all okB = true := by decide +kernel

theorem ok9 : fam9.all okB = true := by decide +kernel

theorem ok10 : fam10.all okB = true := by decide +kernel

theorem ok11 : fam11.all okB = true := by decide +kernel

theorem ok12 : fam12.all okB = true := by decide +kernel

theorem ok13 : fam13.all okB = true := by decide +kernel

theorem ok14 : fam14.all okB = true := by decide +kernel

theorem okc0 : ∀ part ∈ chunk0, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  simp only [chunk0, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok0 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok1 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok2 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok3 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok4 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok5 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok6 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok7 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok8 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok9 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok10 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok11 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok12 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok13 e he)
  · exact fun e he => okB_ok e (List.all_eq_true.mp ok14 e he)

set_option maxRecDepth 8000 in
theorem ok : ∀ part ∈ parts, ∀ e ∈ part, OkEntry tab zs 4 parts perms e := by
  intro part hp
  exact okc0 part (by simpa only [parts, chunk0] using hp)

theorem perms_ok : ∀ π ∈ perms, PermOk tab π := by decide +kernel

theorem tab_lt : tab < 2 ^ 32 := by decide +kernel

theorem tab_one : ∃ p : Fin 32, tab.testBit p = true := by decide +kernel

theorem tab_zero : ∃ q : Fin 32, tab.testBit q = false := by decide +kernel

theorem zs_ok : ∀ q ∈ zs, q < 32 ∧ tab.testBit q = false := by decide +kernel

theorem pool_eq : pool0 = base ++ [0, ALL] := by decide +kernel

theorem nec : ∀ a ∈ base, ¬ GoodL tab zs (base.filter (fun x => decide (x ≠ a))) := by
  decide +kernel

theorem base_mem : ∃ e ∈ parts.flatten, e.1 = 0 ∧ e.2.1 = base :=
  ⟨(0, base, [131048, 31096, 890048, 970096, 931032, 731080, 930032, 730080, 930016, 730064, 620112, 800176, 780128, 880224, 780144, 881001, 780160, 880033, 661144, 60001, 261128, 461224, 461160, 261033, 180192, 780017, 180208, 780049, 181208, 781049]), by decide +kernel, rfl, rfl⟩

theorem base_len : base.length = 5 := by decide +kernel

theorem base_nd : base.Nodup := by decide +kernel

theorem tab_eq : ∀ p : Fin 32, (fun x : Fin 5 → Bool => Nat.testBit 0xeee8eac0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) (fun i : Fin 5 => p.val.testBit i.val) =
    tab.testBit p.val := by
  decide +kernel

-- The AND/OR circuit of the upper bound: wires 0 to 4 are the inputs, gate j is wire 5 + j.
def upper : Circuit :=
  ⟨[⟨GateOp.and, [3, 4]⟩,
   ⟨GateOp.or, [1, 2]⟩,
   ⟨GateOp.and, [4, 6]⟩,
   ⟨GateOp.or, [2, 5]⟩,
   ⟨GateOp.and, [1, 8]⟩,
   ⟨GateOp.or, [3, 7]⟩,
   ⟨GateOp.and, [0, 10]⟩,
   ⟨GateOp.or, [9, 11]⟩], 12⟩

theorem upper_mono : Monotone2 upper := by
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_size : upper.size = 8 := rfl

theorem upper_eval : ∀ x : Fin 5 → Bool, upper.eval (List.ofFn x) =
    Nat.testBit 0xeee8eac0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

theorem coreLower (t : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 5
    (fun x : Fin 5 → Bool => Nat.testBit 0xeee8eac0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) t) : 8 ≤ t := by
  obtain ⟨C, hC, hs, hev⟩ := h
  have h := lower tab 5 4 parts perms zs base tab_lt
    tab_one tab_zero zs_ok perms_ok ok pool_eq
    nec base_mem base_len base_nd
    C hC (fun p => (hev _).trans (tab_eq p))
  have hs' : C.gates.length ≤ t := hs
  omega

end Core

namespace Restrict

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

/-! Section 1: Self-contained circuit simplification, relabeling, and gate elimination -/

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y))
        ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this


end Restrict


def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008241384 * 2 ^ 32 + 3938500800)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def rename : Fin 6 → Fin 6 := ![0, 1, 2, 5, 3, 4]

def relabeled (x : Fin 6 → Bool) : Bool := target (x ∘ rename)

theorem essential :
    ∃ x : Fin 6 → Bool,
      relabeled (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ relabeled x :=
  ⟨fun i => decide (i.val = 0 ∨ i.val = 3), by decide +kernel⟩

theorem pin_nonconstant :
    ∃ x y : Fin 5 → Bool, relabeled (Fin.snoc x true) ≠ relabeled (Fin.snoc y true) :=
  ⟨fun _ => false, fun _ => true, by decide +kernel⟩

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 10000 in
theorem pin_eq (x : Fin 5 → Bool) :
    relabeled (Fin.snoc x true) =
      Nat.testBit 0xeee8eac0 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  revert x
  decide +kernel

theorem fullLower (t : ℕ) (h : HasCircuitSize 6 target t) : 9 ≤ t := by
  have hr : HasCircuitSize 6 relabeled t := Restrict.relabel_size rename target t h
  obtain ⟨k, hk, hrest⟩ := Restrict.gate_elim_one 5 relabeled true t essential pin_nonconstant hr
  simp only [pin_eq] at hrest
  have hcore := Core.coreLower k hrest
  omega

def fullUpper : Circuit :=
  ⟨[
    ⟨.and, [3, 4]⟩,
    ⟨.and, [6, 5]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [5, 8]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [11, 13]⟩
  ], 14⟩

theorem fullUpper_mono : Monotone2 fullUpper := by
  intro g hg
  simp only [fullUpper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 10000 in
theorem fullUpper_eval : ∀ x : Fin 6 → Bool, fullUpper.eval (List.ofFn x) = target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_12531

open PEqualNP.Outside.L_meta_12531 in
theorem PEqualNP.Outside.L_meta_12531 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241384 * 2 ^ 32 + 3938500800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241384 * 2 ^ 32 + 3938500800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  exact ⟨fullUpper, fullUpper_mono, fullLower s h, fullUpper_eval⟩
