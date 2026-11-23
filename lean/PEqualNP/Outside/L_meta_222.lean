import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_222

open PEqualNP.MetaComplexity

/-! # Skeleton for L_meta_222. Sections: formula restriction machinery (proven, from
Research/FormulaElim.lean), graph structure (proven, from Research/short_try.lean and
Research/graph_try.lean), upper half (proven, from Research/upper_try.lean), lower half
(gr_/lo_ lemmas), glue (gl_). -/

section FormulaPart

variable {n : ℕ}

abbrev Vec (n : ℕ) := Fin n → ℕ

def occ : DMFormula n → Fin n → ℕ
  | .lit i _ => fun k => if k = i then 1 else 0
  | .and a b => fun k => occ a k + occ b k
  | .or a b => fun k => occ a k + occ b k

def zv (o : Vec n) (i : Fin n) : Vec n := fun k => if k = i then 0 else o k

def dv (o : Vec n) (j : Fin n) : Vec n := fun k => if k = j then o j - 1 else o k

def upd (x : Fin n → Bool) (i : Fin n) (c : Bool) : Fin n → Bool :=
  fun k => if k = i then c else x k

def litv (s v : Bool) : Bool := if s then v else !v

def bop (g a b : Bool) : Bool := if g then (a || b) else (a && b)

def mk (g : Bool) (a b : DMFormula n) : DMFormula n := if g then .or a b else .and a b

theorem eval_mk (g : Bool) (a b : DMFormula n) (x : Fin n → Bool) :
    (mk g a b).eval x = bop g (a.eval x) (b.eval x) := by
  cases g <;> rfl

theorem occ_mk (g : Bool) (a b : DMFormula n) (k : Fin n) :
    occ (mk g a b) k = occ a k + occ b k := by
  cases g <;> rfl

theorem eval_lit (i : Fin n) (s : Bool) (x : Fin n → Bool) :
    (DMFormula.lit i s).eval x = litv s (x i) := by
  cases s <;> rfl

theorem leaves_eq (φ : DMFormula n) : φ.leaves = ∑ k, occ φ k := by
  induction φ with
  | lit i b => simp [DMFormula.leaves, occ]
  | and a b iha ihb => simp [DMFormula.leaves, occ, iha, ihb, Finset.sum_add_distrib]
  | or a b iha ihb => simp [DMFormula.leaves, occ, iha, ihb, Finset.sum_add_distrib]

theorem eval_congr (φ : DMFormula n) (x y : Fin n → Bool)
    (h : ∀ k, 1 ≤ occ φ k → x k = y k) : φ.eval x = φ.eval y := by
  induction φ with
  | lit i b =>
    simp only [eval_lit]
    rw [h i (by simp [occ])]
  | and a b iha ihb =>
    simp only [DMFormula.eval]
    rw [iha (fun k hk => h k (by simp [occ]; omega)), ihb (fun k hk => h k (by simp [occ]; omega))]
  | or a b iha ihb =>
    simp only [DMFormula.eval]
    rw [iha (fun k hk => h k (by simp [occ]; omega)), ihb (fun k hk => h k (by simp [occ]; omega))]

theorem eval_upd_of_zero (φ : DMFormula n) (i : Fin n) (h : occ φ i = 0) (x : Fin n → Bool)
    (c : Bool) : φ.eval (upd x i c) = φ.eval x := by
  apply eval_congr
  intro k hk
  have : k ≠ i := by rintro rfl; omega
  simp [upd, this]

theorem exists_occ (φ : DMFormula n) : ∃ j, 1 ≤ occ φ j := by
  induction φ with
  | lit i b => exact ⟨i, by simp [occ]⟩
  | and a b iha ihb => obtain ⟨j, hj⟩ := iha; exact ⟨j, by simp [occ]; omega⟩
  | or a b iha ihb => obtain ⟨j, hj⟩ := iha; exact ⟨j, by simp [occ]; omega⟩

def Ach (o : Vec n) (h : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x, h x = c) ∨ ∃ φ : DMFormula n, (∀ x, φ.eval x = h x) ∧ ∀ k, occ φ k ≤ o k

theorem Ach.mono {o o' : Vec n} {h : (Fin n → Bool) → Bool} (hle : ∀ k, o k ≤ o' k)
    (a : Ach o h) : Ach o' h := by
  rcases a with hc | ⟨φ, he, ho⟩
  · exact .inl hc
  · exact .inr ⟨φ, he, fun k => (ho k).trans (hle k)⟩

theorem Ach.congr {o : Vec n} {h h' : (Fin n → Bool) → Bool} (e : ∀ x, h x = h' x)
    (a : Ach o h) : Ach o h' := by
  rcases a with ⟨c, hc⟩ | ⟨φ, he, ho⟩
  · exact .inl ⟨c, fun x => by rw [← e, hc]⟩
  · exact .inr ⟨φ, fun x => by rw [he, e], ho⟩

theorem Ach.form (φ : DMFormula n) : Ach (occ φ) φ.eval := .inr ⟨φ, fun _ => rfl, fun _ => le_rfl⟩

theorem Ach.const (o : Vec n) (c : Bool) : Ach o (fun _ => c) := .inl ⟨c, fun _ => rfl⟩

theorem Ach.bop {o1 o2 : Vec n} {h1 h2 : (Fin n → Bool) → Bool} (g : Bool) (a1 : Ach o1 h1)
    (a2 : Ach o2 h2) : Ach (fun k => o1 k + o2 k) (fun x => bop g (h1 x) (h2 x)) := by
  rcases a1 with ⟨c1, hc1⟩ | ⟨φ1, e1, b1⟩
  · by_cases hg : c1 = g
    · exact .inl ⟨g, fun x => by beta_reduce; rw [hc1, hg]; cases g <;> simp [PEqualNP.Outside.L_meta_222.bop]⟩
    · refine (a2.mono (fun k => Nat.le_add_left _ _)).congr (fun x => ?_)
      rw [hc1]; cases g <;> cases c1 <;> simp_all [PEqualNP.Outside.L_meta_222.bop]
  · rcases a2 with ⟨c2, hc2⟩ | ⟨φ2, e2, b2⟩
    · by_cases hg : c2 = g
      · exact .inl ⟨g, fun x => by beta_reduce; rw [hc2, hg]; cases g <;> simp [PEqualNP.Outside.L_meta_222.bop]⟩
      · refine (Ach.mono (o := o1) (fun k => Nat.le_add_right _ _) (.inr ⟨φ1, e1, b1⟩)).congr
          (fun x => ?_)
        rw [hc2]; cases g <;> cases c2 <;> simp_all [PEqualNP.Outside.L_meta_222.bop]
    · exact .inr ⟨mk g φ1 φ2, fun x => by rw [eval_mk, e1, e2],
        fun k => by rw [occ_mk]; exact Nat.add_le_add (b1 k) (b2 k)⟩

theorem restrict (φ : DMFormula n) (i : Fin n) (c : Bool) :
    Ach (zv (occ φ) i) (fun x => φ.eval (upd x i c)) := by
  induction φ with
  | lit j b =>
    by_cases hj : j = i
    · subst hj
      exact .inl ⟨litv b c, fun x => by simp [eval_lit, upd]⟩
    · refine .inr ⟨.lit j b, fun x => by simp [eval_lit, upd, hj], fun k => ?_⟩
      simp only [occ, zv]
      split_ifs <;> simp_all
  | and a b iha ihb =>
    refine ((iha.bop false ihb).mono (fun k => ?_)).congr (fun x => ?_)
    · simp only [zv, occ]; split_ifs <;> simp
    · rfl
  | or a b iha ihb =>
    refine ((iha.bop true ihb).mono (fun k => ?_)).congr (fun x => ?_)
    · simp only [zv, occ]; split_ifs <;> simp
    · rfl

theorem Ach.restrict {o : Vec n} {h : (Fin n → Bool) → Bool} (a : Ach o h) (i : Fin n) (c : Bool) :
    Ach (zv o i) (fun x => h (upd x i c)) := by
  rcases a with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · exact .inl ⟨c0, fun x => hc _⟩
  · refine ((L_meta_222.restrict φ i c).mono (fun k => ?_)).congr (fun x => by rw [he])
    simp only [zv]; split_ifs <;> simp [ho k]

theorem Ach.upd_inv {o : Vec n} {h : (Fin n → Bool) → Bool} (a : Ach o h) (i : Fin n)
    (hi : o i = 0) (x : Fin n → Bool) (c : Bool) : h (upd x i c) = h x := by
  rcases a with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · rw [hc, hc]
  · rw [← he, ← he, eval_upd_of_zero φ i (by have := ho i; omega)]


def KM (i : Fin n) (o : Vec n) (h : (Fin n → Bool) → Bool) : Prop :=
  Ach (dv o i) h ∨ ∃ c j, j ≠ i ∧ 1 ≤ o j ∧ Ach (dv (zv o i) j) (fun x => h (upd x i c))

theorem KM.congr {i : Fin n} {o o' : Vec n} {h h' : (Fin n → Bool) → Bool} (eo : ∀ k, o k = o' k)
    (eh : ∀ x, h x = h' x) (a : KM i o h) : KM i o' h' := by
  obtain rfl : o = o' := funext eo
  obtain rfl : h = h' := funext eh
  exact a

theorem km_step (i : Fin n) (g : Bool) (A B : DMFormula n) (hA : 1 ≤ occ A i)
    (ihA : (∃ s, A = .lit i s) ∨ KM i (occ A) A.eval) :
    KM i (fun k => occ A k + occ B k) (fun x => bop g (A.eval x) (B.eval x)) := by
  rcases ihA with ⟨s, rfl⟩ | hk
  · by_cases hB : ∃ j, j ≠ i ∧ 1 ≤ occ B j
    · obtain ⟨j, hji, hj⟩ := hB
      refine .inr ⟨litv s g, j, hji, by simp only; omega, .inl ⟨g, fun x => ?_⟩⟩
      simp only [eval_lit, upd, ite_true]
      cases s <;> cases g <;> simp [litv, bop]
    · push Not at hB
      left
      have hBi : 1 ≤ occ B i := by
        obtain ⟨j, hj⟩ := exists_occ B
        by_cases hji : j = i
        · exact hji ▸ hj
        · have := hB j hji; omega
      have key : ∀ x, B.eval x = B.eval (fun _ => x i) := fun x =>
        eval_congr B _ _ (fun k hk => by
          by_cases hk' : k = i
          · subst hk'; rfl
          · have := hB k hk'; omega)
      have hH : ∀ x, bop g ((DMFormula.lit i s).eval x) (B.eval x)
          = bop g (litv s (x i)) (B.eval (fun _ => x i)) := by
        intro x; rw [eval_lit, key x]
      refine Ach.congr (fun x => (hH x).symm) ?_
      have hocc : ∀ (b : Bool) k, occ (DMFormula.lit i b) k ≤
          dv (fun k => occ (DMFormula.lit i s) k + occ B k) i k := by
        intro b k
        simp only [occ, dv]
        split_ifs <;> subst_vars <;> omega
      cases hf : bop g (litv s false) (B.eval (fun _ => false)) <;>
        cases ht : bop g (litv s true) (B.eval (fun _ => true))
      · refine .inl ⟨false, fun x => ?_⟩
        show bop g (litv s (x i)) (B.eval (fun _ => x i)) = false
        cases x i
        · exact hf
        · exact ht
      · refine .inr ⟨.lit i true, fun x => ?_, hocc true⟩
        show (DMFormula.lit i true).eval x = bop g (litv s (x i)) (B.eval (fun _ => x i))
        rw [eval_lit]
        cases x i
        · rw [hf]; rfl
        · rw [ht]; rfl
      · refine .inr ⟨.lit i false, fun x => ?_, hocc false⟩
        show (DMFormula.lit i false).eval x = bop g (litv s (x i)) (B.eval (fun _ => x i))
        rw [eval_lit]
        cases x i
        · rw [hf]; rfl
        · rw [ht]; rfl
      · refine .inl ⟨true, fun x => ?_⟩
        show bop g (litv s (x i)) (B.eval (fun _ => x i)) = true
        cases x i
        · exact hf
        · exact ht
  · rcases hk with hl | ⟨c, j, hji, hj, ha⟩
    · left
      refine (hl.bop g (Ach.form B)).mono (fun k => ?_)
      simp only [dv]
      split_ifs with hk
      · subst hk; omega
      · omega
    · right
      refine ⟨c, j, hji, by simp only; omega, ?_⟩
      refine (ha.bop g ((Ach.form B).restrict i c)).mono (fun k => ?_)
      simp only [dv, zv]
      split_ifs <;> subst_vars <;> omega

theorem kill_multi (i : Fin n) (φ : DMFormula n) :
    1 ≤ occ φ i → (∀ s, φ ≠ .lit i s) → KM i (occ φ) φ.eval := by
  induction φ with
  | lit j b =>
    intro h1 hne
    by_cases hj : j = i
    · subst hj; exact absurd rfl (hne b)
    · simp [occ, Ne.symm hj] at h1
  | and a b iha ihb =>
    intro h1 _
    have hsum : 1 ≤ occ a i + occ b i := h1
    by_cases ha : 1 ≤ occ a i
    · have ih : (∃ s, a = .lit i s) ∨ KM i (occ a) a.eval := by
        by_cases hl : ∃ s, a = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (iha ha hl)
      exact km_step i false a b ha ih
    · have hb : 1 ≤ occ b i := by omega
      have ih : (∃ s, b = .lit i s) ∨ KM i (occ b) b.eval := by
        by_cases hl : ∃ s, b = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (ihb hb hl)
      exact (km_step i false b a hb ih).congr (fun k => Nat.add_comm _ _)
        (fun x => by simp [bop, DMFormula.eval, Bool.and_comm])
  | or a b iha ihb =>
    intro h1 _
    have hsum : 1 ≤ occ a i + occ b i := h1
    by_cases ha : 1 ≤ occ a i
    · have ih : (∃ s, a = .lit i s) ∨ KM i (occ a) a.eval := by
        by_cases hl : ∃ s, a = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (iha ha hl)
      exact km_step i true a b ha ih
    · have hb : 1 ≤ occ b i := by omega
      have ih : (∃ s, b = .lit i s) ∨ KM i (occ b) b.eval := by
        by_cases hl : ∃ s, b = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (ihb hb hl)
      exact (km_step i true b a hb ih).congr (fun k => Nat.add_comm _ _)
        (fun x => by simp [bop, DMFormula.eval, Bool.or_comm])

def KS (i : Fin n) (o : Vec n) (h : (Fin n → Bool) → Bool) : Prop :=
  (∃ j, j ≠ i ∧ 1 ≤ o j ∧ ∃ g si sj : Bool, ∃ ψ : DMFormula n, (∀ k, occ ψ k ≤ dv o j k) ∧
      ∀ x, h x = ψ.eval (upd x i (bop g (litv si (x i)) (litv sj (x j))))) ∨
  (∃ c j k, j ≠ i ∧ k ≠ i ∧ j ≤ k ∧ 1 ≤ o j ∧ 1 ≤ o k ∧ (j ≠ k ∨ 2 ≤ o j) ∧
      Ach (dv (dv (zv o i) j) k) (fun x => h (upd x i c)))

theorem KS.congr {i : Fin n} {o o' : Vec n} {h h' : (Fin n → Bool) → Bool} (eo : ∀ k, o k = o' k)
    (eh : ∀ x, h x = h' x) (a : KS i o h) : KS i o' h' := by
  obtain rfl : o = o' := funext eo
  obtain rfl : h = h' := funext eh
  exact a

theorem two_leaves (i : Fin n) (C D : DMFormula n) (hC : occ C i = 0) (hD : occ D i = 0) :
    ∃ j k, j ≠ i ∧ k ≠ i ∧ j ≤ k ∧ 1 ≤ occ C j + occ D j ∧ 1 ≤ occ C k + occ D k ∧
      (j ≠ k ∨ 2 ≤ occ C j + occ D j) := by
  obtain ⟨j, hj⟩ := exists_occ C
  obtain ⟨k, hk⟩ := exists_occ D
  have hji : j ≠ i := by rintro rfl; omega
  have hki : k ≠ i := by rintro rfl; omega
  rcases le_total j k with hjk | hjk
  · refine ⟨j, k, hji, hki, hjk, by omega, by omega, ?_⟩
    by_cases e : j = k
    · subst e; right; omega
    · left; exact e
  · refine ⟨k, j, hki, hji, hjk, by omega, by omega, ?_⟩
    by_cases e : k = j
    · subst e; right; omega
    · left; exact e

theorem ks_step (i : Fin n) (g : Bool) (A B : DMFormula n) (hA : occ A i = 1) (hB0 : occ B i = 0)
    (ihA : (∃ s, A = .lit i s) ∨ KS i (occ A) A.eval) :
    KS i (fun k => occ A k + occ B k) (fun x => bop g (A.eval x) (B.eval x)) := by
  rcases ihA with ⟨si, rfl⟩ | hk
  · have kill2 : ∀ C D : DMFormula n, occ C i = 0 → occ D i = 0 →
        (∀ k, occ B k = occ C k + occ D k) →
        KS i (fun k => occ (DMFormula.lit i si) k + occ B k)
          (fun x => bop g ((DMFormula.lit i si).eval x) (B.eval x)) := by
      intro C D hC hD hBCD
      obtain ⟨j, k, hji, hki, hjk, hj, hk, hjk2⟩ := two_leaves i C D hC hD
      refine .inr ⟨litv si g, j, k, hji, hki, hjk, ?_, ?_, ?_, .inl ⟨g, fun x => ?_⟩⟩
      · simp only [hBCD]; omega
      · simp only [hBCD]; omega
      · rcases hjk2 with e | e
        · exact .inl e
        · right; simp only [hBCD]; omega
      · simp only [eval_lit, upd, ite_true]
        cases si <;> cases g <;> simp [litv, bop]
    cases B with
    | lit j sj =>
      have hji : j ≠ i := by
        rintro rfl; simp [occ] at hB0
      refine .inl ⟨j, hji, by simp [occ], g, si, sj, .lit i true, fun k => ?_, fun x => ?_⟩
      · simp only [occ, dv]
        split_ifs <;> simp_all
      · simp [eval_lit, upd, litv]
    | and C D =>
      have hB0' : occ C i + occ D i = 0 := hB0
      exact kill2 C D (by omega) (by omega) (fun k => rfl)
    | or C D =>
      have hB0' : occ C i + occ D i = 0 := hB0
      exact kill2 C D (by omega) (by omega) (fun k => rfl)
  · rcases hk with ⟨j, hji, hj, g', si, sj, ψ, hψo, hψe⟩ |
      ⟨c, j, k, hji, hki, hjk, hj, hk1, hjk2, ha⟩
    · refine .inl ⟨j, hji, by simp only; omega, g', si, sj, mk g ψ B, fun k => ?_, fun x => ?_⟩
      · rw [occ_mk]
        have := hψo k
        simp only [dv] at this ⊢
        split_ifs at this ⊢ with e
        · subst e; omega
        · omega
      · rw [eval_mk, ← hψe x, eval_upd_of_zero B i hB0]
    · refine .inr ⟨c, j, k, hji, hki, hjk, by simp only; omega, by simp only; omega, ?_, ?_⟩
      · rcases hjk2 with e | e
        · exact .inl e
        · right; simp only; omega
      · refine (ha.bop g ((Ach.form B).restrict i c)).mono (fun m => ?_)
        simp only [dv, zv]
        split_ifs <;> subst_vars <;> omega

theorem kill_single (i : Fin n) (φ : DMFormula n) :
    occ φ i = 1 → (∀ s, φ ≠ .lit i s) → KS i (occ φ) φ.eval := by
  induction φ with
  | lit j b =>
    intro h1 hne
    by_cases hj : j = i
    · subst hj; exact absurd rfl (hne b)
    · simp [occ, Ne.symm hj] at h1
  | and a b iha ihb =>
    intro h1 _
    have hsum : occ a i + occ b i = 1 := h1
    by_cases ha : occ a i = 1
    · have ih : (∃ s, a = .lit i s) ∨ KS i (occ a) a.eval := by
        by_cases hl : ∃ s, a = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (iha ha hl)
      exact ks_step i false a b ha (by omega) ih
    · have hb : occ b i = 1 := by omega
      have ih : (∃ s, b = .lit i s) ∨ KS i (occ b) b.eval := by
        by_cases hl : ∃ s, b = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (ihb hb hl)
      exact (ks_step i false b a hb (by omega) ih).congr (fun k => Nat.add_comm _ _)
        (fun x => by simp [bop, DMFormula.eval, Bool.and_comm])
  | or a b iha ihb =>
    intro h1 _
    have hsum : occ a i + occ b i = 1 := h1
    by_cases ha : occ a i = 1
    · have ih : (∃ s, a = .lit i s) ∨ KS i (occ a) a.eval := by
        by_cases hl : ∃ s, a = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (iha ha hl)
      exact ks_step i true a b ha (by omega) ih
    · have hb : occ b i = 1 := by omega
      have ih : (∃ s, b = .lit i s) ∨ KS i (occ b) b.eval := by
        by_cases hl : ∃ s, b = .lit i s
        · exact .inl hl
        · push Not at hl; exact .inr (ihb hb hl)
      exact (ks_step i true b a hb (by omega) ih).congr (fun k => Nat.add_comm _ _)
        (fun x => by simp [bop, DMFormula.eval, Bool.or_comm])


/-! Bridge to the total-leaf form `ALeaf` (same definition as in `lower_try.lean`) -/

def ALeaf (s : ℕ) (h : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x, h x = c) ∨ ∃ φ : DMFormula n, φ.leaves ≤ s ∧ ∀ x, φ.eval x = h x

theorem ALeaf.of_ach {o : Vec n} {h : (Fin n → Bool) → Bool} (a : Ach o h) :
    ALeaf (∑ k, o k) h := by
  rcases a with hc | ⟨φ, he, ho⟩
  · exact .inl hc
  · exact .inr ⟨φ, by rw [leaves_eq]; exact Finset.sum_le_sum fun k _ => ho k, he⟩

theorem ALeaf.to_ach {s : ℕ} {h : (Fin n → Bool) → Bool} (a : ALeaf s h) :
    ∃ o : Vec n, Ach o h ∧ ∑ k, o k ≤ s := by
  rcases a with hc | ⟨φ, h1, h2⟩
  · exact ⟨fun _ => 0, .inl hc, by simp⟩
  · exact ⟨occ φ, .inr ⟨φ, h2, fun _ => le_rfl⟩, by rw [← leaves_eq]; exact h1⟩

theorem ALeaf.mono {s s' : ℕ} {h : (Fin n → Bool) → Bool} (hs : s ≤ s') (a : ALeaf s h) :
    ALeaf s' h := by
  rcases a with hc | ⟨φ, h1, h2⟩
  · exact .inl hc
  · exact .inr ⟨φ, h1.trans hs, h2⟩

theorem ALeaf.congr {s : ℕ} {h h' : (Fin n → Bool) → Bool} (e : ∀ x, h x = h' x)
    (a : ALeaf s h) : ALeaf s h' := by
  rcases a with ⟨c, hc⟩ | ⟨φ, h1, h2⟩
  · exact .inl ⟨c, fun x => by rw [← e, hc]⟩
  · exact .inr ⟨φ, h1, fun x => (h2 x).trans (e x)⟩

theorem ALeaf.restrict {s : ℕ} {h : (Fin n → Bool) → Bool} (a : ALeaf s h) (i : Fin n)
    (c : Bool) : ALeaf s (fun x => h (upd x i c)) := by
  obtain ⟨o, ha, hs⟩ := a.to_ach
  refine ALeaf.mono ?_ (ALeaf.of_ach (ha.restrict i c))
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) hs
  unfold zv; split_ifs <;> omega

theorem ALeaf.bop {a b : ℕ} {h1 h2 : (Fin n → Bool) → Bool} (g : Bool) (ha : ALeaf a h1)
    (hb : ALeaf b h2) : ALeaf (a + b) (fun x => bop g (h1 x) (h2 x)) := by
  obtain ⟨o1, a1, s1⟩ := ha.to_ach
  obtain ⟨o2, a2, s2⟩ := hb.to_ach
  refine ALeaf.mono ?_ (ALeaf.of_ach (Ach.bop g a1 a2))
  rw [Finset.sum_add_distrib]; omega

theorem sum_zv (o : Vec n) (i : Fin n) : ∑ k, zv o i k + o i = ∑ k, o k := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ o (Finset.mem_univ i)]
  have : ∑ k ∈ Finset.univ.erase i, zv o i k = ∑ k ∈ Finset.univ.erase i, o k :=
    Finset.sum_congr rfl fun k hk => by simp [zv, Finset.ne_of_mem_erase hk]
  rw [this]; simp [zv]; omega

/-- Restriction removes every occurrence of the restricted variable. -/
theorem restrict_occ (φ : DMFormula n) (i : Fin n) (c : Bool) :
    ALeaf (φ.leaves - occ φ i) (fun x => φ.eval (upd x i c)) := by
  refine ALeaf.mono ?_ (ALeaf.of_ach (restrict φ i c))
  have := sum_zv (occ φ) i
  rw [leaves_eq]; omega

theorem leaves_pos (φ : DMFormula n) : 1 ≤ φ.leaves := by
  induction φ with
  | lit _ _ => simp [DMFormula.leaves]
  | and A B iA iB => simp only [DMFormula.leaves]; omega
  | or A B iA iB => simp only [DMFormula.leaves]; omega

theorem bop_comm (g a b : Bool) : bop g a b = bop g b a := by
  cases g <;> cases a <;> cases b <;> rfl

theorem kill_gate (i : Fin n) (g : Bool) (A B : DMFormula n) (hi : 1 ≤ occ A i)
    (ihA : 2 ≤ A.leaves → ∃ c : Bool, ALeaf (A.leaves - 2) (fun x => A.eval (upd x i c))) :
    ∃ c : Bool, ALeaf (A.leaves + B.leaves - 2)
      (fun x => bop g (A.eval (upd x i c)) (B.eval (upd x i c))) := by
  cases A with
  | lit j s =>
    have hj : i = j := by
      by_contra h; simp [occ, h] at hi
    subst hj
    refine ⟨if s then g else !g, .inl ⟨g, fun x => ?_⟩⟩
    show bop g ((DMFormula.lit i s).eval _) _ = g
    rw [eval_lit]
    simp only [upd, ite_true]
    cases s <;> cases g <;> simp [litv, bop]
  | and C D =>
    have h1 := leaves_pos C
    have h2 := leaves_pos D
    obtain ⟨c, hc⟩ := ihA (by simp only [DMFormula.leaves]; omega)
    refine ⟨c, ALeaf.mono ?_ (ALeaf.bop g hc (ALeaf.restrict (.inr ⟨B, le_rfl, fun _ => rfl⟩) i c))⟩
    simp only [DMFormula.leaves]; omega
  | or C D =>
    have h1 := leaves_pos C
    have h2 := leaves_pos D
    obtain ⟨c, hc⟩ := ihA (by simp only [DMFormula.leaves]; omega)
    refine ⟨c, ALeaf.mono ?_ (ALeaf.bop g hc (ALeaf.restrict (.inr ⟨B, le_rfl, fun _ => rfl⟩) i c))⟩
    simp only [DMFormula.leaves]; omega

theorem kill_gate2 (i : Fin n) (g : Bool) (A B : DMFormula n) (hi : 1 ≤ occ A i + occ B i)
    (ihA : 1 ≤ occ A i → 2 ≤ A.leaves →
      ∃ c : Bool, ALeaf (A.leaves - 2) (fun x => A.eval (upd x i c)))
    (ihB : 1 ≤ occ B i → 2 ≤ B.leaves →
      ∃ c : Bool, ALeaf (B.leaves - 2) (fun x => B.eval (upd x i c))) :
    ∃ c : Bool, ALeaf (A.leaves + B.leaves - 2)
      (fun x => bop g (A.eval (upd x i c)) (B.eval (upd x i c))) := by
  by_cases hA : 1 ≤ occ A i
  · exact kill_gate i g A B hA (ihA hA)
  · obtain ⟨c, hc⟩ := kill_gate i g B A (by omega) (ihB (by omega))
    exact ⟨c, ALeaf.congr (fun x => bop_comm _ _ _) (by rwa [Nat.add_comm])⟩

/-- Subbotovskaya: restricting `i` to the constant absorbing the parent gate of one of its
leaves kills at least two leaves (when `φ` is not a single literal). -/
theorem restrict_kill (φ : DMFormula n) (i : Fin n) (hi : 1 ≤ occ φ i) (hL : 2 ≤ φ.leaves) :
    ∃ c : Bool, ALeaf (φ.leaves - 2) (fun x => φ.eval (upd x i c)) := by
  induction φ with
  | lit j b => simp [DMFormula.leaves] at hL
  | and A B iA iB =>
    obtain ⟨c, hc⟩ := kill_gate2 i false A B (by simpa [occ] using hi)
      (fun h1 h2 => iA h1 h2) (fun h1 h2 => iB h1 h2)
    exact ⟨c, ALeaf.congr (fun x => by simp [bop, DMFormula.eval]) hc⟩
  | or A B iA iB =>
    obtain ⟨c, hc⟩ := kill_gate2 i true A B (by simpa [occ] using hi)
      (fun h1 h2 => iA h1 h2) (fun h1 h2 => iB h1 h2)
    exact ⟨c, ALeaf.congr (fun x => by simp [bop, DMFormula.eval]) hc⟩


end FormulaPart

/-! ## Graph structure (proven) -/

def CycHyp {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → p.length = 3

/-- A path from l to w whose ends are adjacent has length 1 or 2 (no cycles of length ≥ 4). -/
theorem path_back_short {n : ℕ} {G : SimpleGraph (Fin n)} (hC : CycHyp G) {l w : Fin n}
    (Q : G.Walk l w) (hQ : Q.IsPath) (h : G.Adj w l) : Q.length ≤ 2 := by
  cases Q with
  | nil => simp
  | cons h1 Q' =>
    rename_i l1
    rw [SimpleGraph.Walk.cons_isPath_iff] at hQ
    by_cases he : s(w, l) ∈ (SimpleGraph.Walk.cons h1 Q').edges
    · rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · rw [Sym2.eq_swap, Sym2.eq_iff] at he
        rcases he with ⟨-, rfl⟩ | ⟨rfl, -⟩
        · cases Q' with
          | nil => simp
          | cons h2 Q'' =>
            exfalso
            have := hQ.1.support_nodup
            simp at this
        · exact (G.irrefl h1).elim
      · exact absurd (Q'.snd_mem_support_of_mem_edges he) hQ.2
    · have hcyc : (SimpleGraph.Walk.cons h (SimpleGraph.Walk.cons h1 Q')).IsCycle := by
        rw [SimpleGraph.Walk.cons_isCycle_iff]
        exact ⟨(SimpleGraph.Walk.cons_isPath_iff _ _).2 hQ, he⟩
      have := hC _ _ hcyc
      simp at this ⊢
      omega

/-- Endpoint of a longest path: every neighbour is the 1st or 2nd vertex of the path. -/
theorem longest_endpoint_nbrs {n : ℕ} (G : SimpleGraph (Fin n)) (hC : CycHyp G)
    {l z : Fin n} (P : G.Walk l z) (hP : P.IsPath)
    (hmax : ∀ (c d : Fin n) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length) :
    ∀ w, G.Adj l w → w = P.getVert 1 ∨ w = P.getVert 2 := by
  intro w hw
  by_cases hm : w ∈ P.support
  · have hQ := hP.takeUntil hm
    have h2 := path_back_short hC (P.takeUntil w hm) hQ hw.symm
    have hg := P.getVert_length_takeUntil hm
    have h0 : (P.takeUntil w hm).length ≠ 0 := by
      intro h0
      rw [h0, SimpleGraph.Walk.getVert_zero] at hg
      exact G.ne_of_adj hw hg
    rcases (by omega : (P.takeUntil w hm).length = 1 ∨ (P.takeUntil w hm).length = 2) with h | h
    · left; rw [← hg, h]
    · right; rw [← hg, h]
  · exfalso
    have hp : (SimpleGraph.Walk.cons hw.symm P).IsPath :=
      (SimpleGraph.Walk.cons_isPath_iff _ _).2 ⟨hP, hm⟩
    have := hmax _ _ _ hp
    simp at this

/-- A neighbour of the start of a path that lies on the path is its 1st or 2nd vertex. -/
theorem nbr_on_path {n : ℕ} {G : SimpleGraph (Fin n)} (hC : CycHyp G)
    {l z : Fin n} (P : G.Walk l z) (hP : P.IsPath) {w : Fin n} (hw : G.Adj l w)
    (hm : w ∈ P.support) : w = P.getVert 1 ∨ w = P.getVert 2 := by
  have hQ := hP.takeUntil hm
  have h2 := path_back_short hC (P.takeUntil w hm) hQ hw.symm
  have hg := P.getVert_length_takeUntil hm
  have h0 : (P.takeUntil w hm).length ≠ 0 := by
    intro h0
    rw [h0, SimpleGraph.Walk.getVert_zero] at hg
    exact G.ne_of_adj hw hg
  rcases (by omega : (P.takeUntil w hm).length = 1 ∨ (P.takeUntil w hm).length = 2) with h | h
  · left; rw [← hg, h]
  · right; rw [← hg, h]

/-- Generic: a longest path exists (copied from L_meta_659.lean:615, proven there). -/
theorem exists_longest_path {V : Type*} [Fintype V] (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧
      ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length := by
  by_contra hno
  push Not at hno
  have hk : ∀ k : ℕ, ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧ k ≤ P.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨v, v, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, le_refl _⟩
    | succ k ih =>
      obtain ⟨a, b, P, hP, hk⟩ := ih
      obtain ⟨c, d, Q, hQ, hlt⟩ := hno a b P hP
      exact ⟨c, d, Q, hQ, by omega⟩
  obtain ⟨a, b, P, hP, hle⟩ := hk (Fintype.card V)
  have := hP.length_lt
  omega

/-- Case A of `leaf_config`: if the endpoint l of a longest path l p q ... is adjacent to q,
then p's only neighbours are l and q. -/
theorem caseA {n : ℕ} (G : SimpleGraph (Fin n)) (hC : CycHyp G)
    {l p q z : Fin n} (h1 : G.Adj l p) (h2 : G.Adj p q) (P2 : G.Walk q z)
    (hP : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).IsPath)
    (hmax : ∀ (c d : Fin n) (Q : G.Walk c d), Q.IsPath →
      Q.length ≤ (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).length)
    (hlq : G.Adj l q) : ∀ w, G.Adj p w → w = l ∨ w = q := by
  have hs := hP.support_nodup
  simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons, not_or] at hs
  have hQ : (SimpleGraph.Walk.cons h1.symm (SimpleGraph.Walk.cons hlq P2)).IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons, not_or]
    exact ⟨⟨fun e => hs.1.1 e.symm, hs.2.1⟩, hs.1.2, hs.2.2⟩
  intro w hw
  have := longest_endpoint_nbrs G hC _ hQ (by
    intro c d Q hQ'
    have := hmax c d Q hQ'
    simpa using this) w hw
  simpa using this

/-- Case B helper: on a longest path l p q ..., a neighbour w of p off the path is a pendant at p. -/
theorem caseB_off {n : ℕ} (G : SimpleGraph (Fin n)) (hC : CycHyp G)
    {l p q z : Fin n} (h1 : G.Adj l p) (h2 : G.Adj p q) (P2 : G.Walk q z)
    (hP : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).IsPath)
    (hmax : ∀ (c d : Fin n) (Q : G.Walk c d), Q.IsPath →
      Q.length ≤ (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).length)
    {w : Fin n} (hpw : G.Adj p w)
    (hwn : w ∉ (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).support) :
    ∀ x, G.Adj w x → x = p := by
  have hs := hP.support_nodup
  simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons, not_or] at hs hwn
  have hT : (SimpleGraph.Walk.cons h2 P2).IsPath := hP.tail
  have hQ : (SimpleGraph.Walk.cons hpw.symm (SimpleGraph.Walk.cons h2 P2)).IsPath := by
    rw [SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨hT, ?_⟩
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
    exact ⟨hwn.2.1, hwn.2.2⟩
  have hmax' : ∀ (c d : Fin n) (Q : G.Walk c d), Q.IsPath →
      Q.length ≤ (SimpleGraph.Walk.cons hpw.symm (SimpleGraph.Walk.cons h2 P2)).length := by
    intro c d Q hQ'
    have := hmax c d Q hQ'
    simpa using this
  intro x hx
  have hx' := longest_endpoint_nbrs G hC _ hQ hmax' x hx
  simp at hx'
  rcases hx' with rfl | rfl
  · rfl
  · exfalso
    have hA := caseA G hC hpw.symm h2 P2 hQ hmax' hx l h1.symm
    rcases hA with rfl | rfl
    · exact hwn.1 rfl
    · exact hs.1.2 (SimpleGraph.Walk.start_mem_support _)

theorem leaf_config {n : ℕ} (G : SimpleGraph (Fin n)) (hC : CycHyp G)
    (he : ∃ u v : Fin n, G.Adj u v) :
    (∃ a b c : Fin n, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (∀ w, G.Adj b w → w = a ∨ w = c) ∧ (∀ w, G.Adj c w → w = a ∨ w = b)) ∨
    (∃ l p q : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ (∀ w, G.Adj p w → w = l ∨ w = q)) ∨
    (∃ l p l' : Fin n, l' ≠ l ∧ G.Adj l p ∧ G.Adj l' p ∧ (∀ w, G.Adj l w → w = p) ∧
        (∀ w, G.Adj l' w → w = p)) ∨
    (∃ l p q r : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ G.Adj p q ∧ G.Adj q r ∧ G.Adj r p ∧
        (∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r)) := by
  obtain ⟨u, v, huv⟩ := he
  have : Nonempty (Fin n) := ⟨u⟩
  obtain ⟨a, b, P, hP, hmax⟩ := exists_longest_path G
  have h1len := hmax u v (SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil) (by simp [huv.ne])
  have hE := longest_endpoint_nbrs G hC P hP hmax
  cases P with
  | nil => simp at h1len
  | cons h1 P' =>
    rename_i p
    cases P' with
    | nil =>
      have hR : (SimpleGraph.Walk.cons h1.symm SimpleGraph.Walk.nil).IsPath := by simp [h1.ne.symm]
      have hE2 := longest_endpoint_nbrs G hC _ hR (by intro c d Q hQ; simpa using hmax c d Q hQ)
      right; left
      refine ⟨a, b, a, h1, fun w hw => ?_, fun w hw => ?_⟩
      · simpa using hE w hw
      · have := hE2 w hw; simp at this; exact Or.inl this
    | cons h2 P2 =>
      rename_i q
      by_cases hlq : G.Adj a q
      · left
        refine ⟨q, a, p, hlq.symm, h1, h2, fun w hw => ?_, fun w hw => ?_⟩
        · have := hE w hw; simp at this; tauto
        · exact (caseA G hC h1 h2 P2 hP hmax hlq w hw).symm
      · have hNl : ∀ w, G.Adj a w → w = p := by
          intro w hw
          have := hE w hw; simp at this
          rcases this with h | h
          · exact h
          · exact absurd (h ▸ hw) hlq
        by_cases hoff : ∃ w, G.Adj p w ∧ w ∉ (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).support
        · obtain ⟨w, hpw, hwn⟩ := hoff
          right; right; left
          refine ⟨a, p, w, ?_, h1, hpw.symm, hNl, caseB_off G hC h1 h2 P2 hP hmax hpw hwn⟩
          rintro rfl; exact hwn (SimpleGraph.Walk.start_mem_support _)
        · push Not at hoff
          have hon : ∀ w, G.Adj p w → w = a ∨ w = q ∨ w = P2.getVert 1 := by
            intro w hw
            have hm := hoff w hw
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
            rcases hm with h | h | h
            · exact Or.inl h
            · exact absurd (h ▸ hw) (G.irrefl)
            · have := nbr_on_path hC (SimpleGraph.Walk.cons h2 P2) hP.tail hw
                (by simp [h])
              simp at this
              tauto
          by_cases hpr : G.Adj p (P2.getVert 1) ∧ G.Adj q (P2.getVert 1)
          · right; right; right
            exact ⟨a, p, q, P2.getVert 1, h1, hNl, h2, hpr.2, hpr.1.symm, hon⟩
          · right; left
            refine ⟨a, p, q, h1, hNl, fun w hw => ?_⟩
            rcases hon w hw with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · subst h
              cases P2 with
              | nil => exact Or.inr (by simp)
              | cons h3 P3 =>
                exact absurd ⟨hw, by simpa using h3⟩ hpr


def TriHyp {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d e : Fin n, G.Adj a b → G.Adj b c → G.Adj c a → G.Adj a d → G.Adj d e → G.Adj e a →
    ((b = d ∧ c = e) ∨ (b = e ∧ c = d))

/-- PROVEN: the cycle hypothesis passes to any subgraph on the same vertex type. -/
theorem CycHyp.mono {n : ℕ} {G H : SimpleGraph (Fin n)} (h : H ≤ G) (hG : CycHyp G) :
    CycHyp H := by
  intro u p hp
  have := hG u (p.mapLe h) (hp.mapLe h)
  simpa using this

/-- PROVEN: the triangle hypothesis passes to any subgraph. -/
theorem TriHyp.mono {n : ℕ} {G H : SimpleGraph (Fin n)} (h : H ≤ G) (hG : TriHyp G) :
    TriHyp H := fun a b c d e h1 h2 h3 h4 h5 h6 => hG a b c d e (h h1) (h h2) (h h3) (h h4) (h h5) (h h6)

/-! ## Upper half (proven) -/

theorem hasLeafSize_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s s' : ℕ}
    (h : HasLeafSize n f s) (hs : s ≤ s') : HasLeafSize n f s' := by
  obtain ⟨φ, h1, h2⟩ := h
  exact ⟨φ, h1.trans hs, h2⟩

def PL (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  (∀ x, f x = false) ∨ HasLeafSize n f s

theorem PL.congr {n : ℕ} {f g : (Fin n → Bool) → Bool} {s s' : ℕ} (h : PL n f s)
    (e : ∀ x, f x = g x) (hs : s ≤ s') : PL n g s' := by
  rcases h with h | ⟨φ, h1, h2⟩
  · exact Or.inl fun x => (e x) ▸ h x
  · exact Or.inr ⟨φ, h1.trans hs, fun x => (h2 x).trans (e x)⟩

theorem PL.or {n : ℕ} {f g : (Fin n → Bool) → Bool} {a b : ℕ} (hf : PL n f a) (hg : PL n g b) :
    PL n (fun x => f x || g x) (a + b) := by
  rcases hf with hf | ⟨φ, h1, h2⟩
  · exact PL.congr hg (fun x => by simp [hf x]) (Nat.le_add_left _ _)
  · rcases hg with hg | ⟨ψ, h3, h4⟩
    · exact PL.congr (Or.inr ⟨φ, h1, h2⟩) (fun x => by simp [hg x]) (Nat.le_add_right _ _)
    · exact Or.inr ⟨DMFormula.or φ ψ, by simp only [DMFormula.leaves]; omega,
        fun x => by simp only [DMFormula.eval, h2, h4]⟩

theorem PL.and_lit {n : ℕ} {g : (Fin n → Bool) → Bool} {b : ℕ} (i : Fin n) (hg : PL n g b) :
    PL n (fun x => x i && g x) (b + 1) := by
  rcases hg with hg | ⟨ψ, h3, h4⟩
  · exact Or.inl fun x => by simp [hg x]
  · exact Or.inr ⟨DMFormula.and (DMFormula.lit i true) ψ,
      by simp only [DMFormula.leaves]; omega,
      fun x => by simp [DMFormula.eval, h4]⟩

theorem PL_orLits {n : ℕ} (N : Finset (Fin n)) :
    PL n (fun x => decide (∃ u ∈ N, x u = true)) N.card := by
  induction N using Finset.induction_on with
  | empty => exact Or.inl fun x => by simp
  | insert a N ha ih =>
    rw [Finset.card_insert_of_notMem ha]
    have hl : PL n (fun x => x a) 1 :=
      Or.inr ⟨DMFormula.lit a true, le_rfl, fun x => by simp [DMFormula.eval]⟩
    refine PL.congr (PL.or ih hl) (fun x => ?_) (by omega)
    by_cases hx : x a = true <;> simp [hx]

def edgeF {n : ℕ} (E : Finset (Sym2 (Fin n))) (x : Fin n → Bool) : Bool :=
  decide (∃ u v, s(u, v) ∈ E ∧ x u = true ∧ x v = true)

theorem card_star {n : ℕ} (E : Finset (Sym2 (Fin n))) (v : Fin n) :
    (Finset.univ.filter (fun u => s(v, u) ∈ E)).card = (E.filter (fun e => v ∈ e)).card := by
  refine Finset.card_nbij (fun u => s(v, u)) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
    simp [hu]
  · intro a _ b _ hab
    exact Sym2.congr_right.mp hab
  · intro e he
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at he
    obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp he.2
    exact ⟨b, by simpa using he.1, rfl⟩

theorem PL_edges {n : ℕ} (S : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)),
    (∀ u v, s(u, v) ∈ E → u ∈ S ∨ v ∈ S) → PL n (edgeF E) (E.card + S.card) := by
  induction S using Finset.induction_on with
  | empty =>
    intro E hE
    refine Or.inl fun x => ?_
    simp only [edgeF, decide_eq_false_iff_not, not_exists, not_and]
    intro u v h
    simpa using hE u v h
  | insert v S hv ih =>
    intro E hE
    have hE' : ∀ u w, s(u, w) ∈ E.filter (fun e => v ∉ e) → u ∈ S ∨ w ∈ S := by
      intro u w h
      rw [Finset.mem_filter, Sym2.mem_iff, not_or] at h
      rcases hE u w h.1 with h1 | h1
      · rw [Finset.mem_insert] at h1
        exact Or.inl (h1.resolve_left (Ne.symm h.2.1))
      · rw [Finset.mem_insert] at h1
        exact Or.inr (h1.resolve_left (Ne.symm h.2.2))
    have h1 := ih _ hE'
    have h2 := PL.and_lit v (PL_orLits (Finset.univ.filter (fun u => s(v, u) ∈ E)))
    have hc := Finset.card_filter_add_card_filter_not (s := E) (fun e => v ∈ e)
    rw [card_star] at h2
    refine PL.congr (PL.or h1 h2) (fun x => ?_) (by rw [Finset.card_insert_of_notMem hv]; omega)
    apply Bool.eq_iff_iff.mpr
    simp only [edgeF, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨u, w, ⟨he, -⟩, hu, hw⟩ | ⟨hx, u, he, hu⟩)
      · exact ⟨u, w, he, hu, hw⟩
      · exact ⟨v, u, he, hx, hu⟩
    · rintro ⟨u, w, he, hu, hw⟩
      by_cases hvu : v ∈ s(u, w)
      · right
        rcases Sym2.mem_iff.mp hvu with rfl | rfl
        · exact ⟨hu, w, he, hw⟩
        · exact ⟨hw, u, by rwa [Sym2.eq_swap], hu⟩
      · left
        exact ⟨u, w, ⟨he, hvu⟩, hu, hw⟩

theorem upper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n))
    (hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S) (hE : ∃ u v, G.Adj u v) :
    HasLeafSize n (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
      (G.edgeFinset.card + S.card) := by
  have h := PL_edges S G.edgeFinset (fun u v h => hS u v (by simpa using h))
  have e : ∀ x, edgeF G.edgeFinset x =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := fun x => by
    simp [edgeF]
  rcases PL.congr h e le_rfl with h | h
  · obtain ⟨u, v, huv⟩ := hE
    have := h (fun _ => true)
    simp only [decide_eq_false_iff_not, not_exists, not_and] at this
    exact (this u v huv trivial trivial).elim
  · exact h

theorem upper_dir {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t s : ℕ)
    (hE : ∃ u v, G.Adj u v)
    (hT : ∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t)
    (hs : G.edgeFinset.card + t ≤ s) :
    HasLeafSize n (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
      s := by
  obtain ⟨S, hS, rfl⟩ := hT
  exact hasLeafSize_mono (upper G S hS hE) hs


/-! ## Wrappers with the skeleton prefixes for the copied, proven entry points -/

theorem up_dir {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t s : ℕ)
    (hE : ∃ u v, G.Adj u v)
    (hT : ∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t)
    (hs : G.edgeFinset.card + t ≤ s) :
    HasLeafSize n (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
      s :=
  upper_dir G t s hE hT hs

/-! ## Lower half (direction `→`): definitions -/

section LowerHalf

variable {n : ℕ}

/-- The generalised function: some input of `A` is true, or both ends of some edge are true. -/
noncomputable def EF (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (Classical.propDecidable _)

/-- The graph class of the target: every cycle is a triangle, a vertex lies on one triangle. -/
def Good (G : SimpleGraph (Fin n)) : Prop := CycHyp G ∧ TriHyp G

/-- Every vertex of `A` is isolated in `G`. -/
def Iso (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop := ∀ a ∈ A, ∀ v, ¬ G.Adj a v

/-- `k` is at most the size of every vertex cover of `G`. -/
def CovLB (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card

/-- `G` with every edge at `v` deleted (same vertex type `Fin n`). -/
def dropV (G : SimpleGraph (Fin n)) (v : Fin n) : SimpleGraph (Fin n) where
  Adj x y := G.Adj x y ∧ x ≠ v ∧ y ≠ v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩

/-- The degree of `v`, as an `ncard` (no decidability needed). -/
noncomputable def dg (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ := {w | G.Adj v w}.ncard

/-- The lower-bound claim for one pair `(G, A)`: `|A| + |E| + τ ≤ s` for every `s` with
`ALeaf s (EF G A)`, where `τ` is replaced by any lower bound `k` on vertex covers. -/
def LoClaim (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  ∀ k s : ℕ, CovLB G k → ALeaf s (EF G A) → A.card + G.edgeSet.ncard + k ≤ s

/-- The induction hypothesis: the claim for every pair of the class with a smaller measure
`2 |E| + |A|`. -/
def LoIH (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  ∀ (G' : SimpleGraph (Fin n)) (A' : Finset (Fin n)), Good G' → Iso G' A' →
    2 * G'.edgeSet.ncard + A'.card < 2 * G.edgeSet.ncard + A.card → LoClaim G' A'

/-! ## Graph structure (gr_) -/

theorem gr_dropV_adj (G : SimpleGraph (Fin n)) (v x y : Fin n) :
    (dropV G v).Adj x y ↔ G.Adj x y ∧ x ≠ v ∧ y ≠ v := Iff.rfl

theorem gr_dropV_le (G : SimpleGraph (Fin n)) (v : Fin n) : dropV G v ≤ G := fun _ _ h => h.1

theorem gr_good_mono {G H : SimpleGraph (Fin n)} (h : H ≤ G) (hG : Good G) : Good H :=
  And.intro (CycHyp.mono h hG.1) (TriHyp.mono h hG.2)

theorem gr_iso_mono {G H : SimpleGraph (Fin n)} (h : H ≤ G) {A : Finset (Fin n)} (hA : Iso G A) :
    Iso H A := fun a ha v hv => hA a ha v (h hv)

theorem gr_iso_insert (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n) (hA : Iso G A) :
    Iso (dropV G v) (insert v A) := by
  intro a ha w hw
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact hw.2.1 rfl
  · exact hA a ha w hw.1

theorem gr_iso_erase (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n) (hA : Iso G A) :
    Iso G (A.erase a) := fun b hb v hv => hA b (Finset.mem_of_mem_erase hb) v hv

theorem gr_not_mem_of_adj {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (hA : Iso G A)
    {u v : Fin n} (h : G.Adj u v) : u ∉ A := fun hu => hA u hu v h

/-- The map `w ↦ s(v, w)` is injective. -/
theorem gr_ncard_dropV_aux_inj (v : Fin n) : Function.Injective (fun w : Fin n => s(v, w)) :=
  fun _ _ h => Sym2.congr_right.mp h

/-- The edges of `G` are the edges of `dropV G v` together with the edges `s(v, w)` at `v`. -/
theorem gr_ncard_dropV_aux_union (G : SimpleGraph (Fin n)) (v : Fin n) :
    G.edgeSet = (dropV G v).edgeSet ∪ (fun w : Fin n => s(v, w)) '' {w | G.Adj v w} := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
    rw [Set.mem_union, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet, Set.mem_image]
    constructor
    · intro h
      by_cases hx : x = v
      · subst hx
        exact Or.inr ⟨y, h, rfl⟩
      · by_cases hy : y = v
        · subst hy
          exact Or.inr ⟨x, h.symm, Sym2.eq_swap⟩
        · exact Or.inl ⟨h, hx, hy⟩
    · rintro (h | ⟨w, hw, he⟩)
      · exact h.1
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hw
        · exact hw.symm

/-- No edge of `dropV G v` contains `v`. -/
theorem gr_ncard_dropV_aux_disj (G : SimpleGraph (Fin n)) (v : Fin n) :
    Disjoint (dropV G v).edgeSet ((fun w : Fin n => s(v, w)) '' {w | G.Adj v w}) := by
  rw [Set.disjoint_left]
  rintro e he ⟨w, _, rfl⟩
  exact (show (dropV G v).Adj v w from he).2.1 rfl

/-- Deleting the edges at `v` removes exactly `dg G v` edges. -/
theorem gr_ncard_dropV (G : SimpleGraph (Fin n)) (v : Fin n) :
    (dropV G v).edgeSet.ncard + dg G v = G.edgeSet.ncard := by
  unfold dg
  conv_rhs => rw [gr_ncard_dropV_aux_union G v]
  rw [Set.ncard_union_eq (gr_ncard_dropV_aux_disj G v) (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ (gr_ncard_dropV_aux_inj v)]

theorem gr_dg_one {G : SimpleGraph (Fin n)} {l p : Fin n} (hlp : G.Adj l p)
    (hl : ∀ w, G.Adj l w → w = p) : dg G l = 1 := by
  unfold dg
  rw [Set.ncard_eq_one]
  refine ⟨p, Set.ext fun w => ?_⟩
  show G.Adj l w ↔ w = p
  exact ⟨fun h => hl w h, fun h => h ▸ hlp⟩

theorem gr_dg_pos {G : SimpleGraph (Fin n)} {v w : Fin n} (h : G.Adj v w) : 1 ≤ dg G v := by
  unfold dg
  exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨w, h⟩

theorem gr_dg_le_two {G : SimpleGraph (Fin n)} {p l q : Fin n}
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) : dg G p ≤ 2 := by
  unfold dg
  calc {w | G.Adj p w}.ncard ≤ ({l, q} : Set (Fin n)).ncard :=
        Set.ncard_le_ncard (fun w hw => by rcases hp w hw with rfl | rfl <;> simp)
    _ ≤ ({q} : Set (Fin n)).ncard + 1 := Set.ncard_insert_le l {q}
    _ = 2 := by rw [Set.ncard_singleton]

theorem gr_dg_two {G : SimpleGraph (Fin n)} {b a c : Fin n} (hba : G.Adj b a) (hbc : G.Adj b c)
    (hac : a ≠ c) (hb : ∀ w, G.Adj b w → w = a ∨ w = c) : dg G b = 2 := by
  unfold dg
  have e : {w | G.Adj b w} = ({a, c} : Set (Fin n)) := by
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      exact hb w h
    · rintro (rfl | rfl)
      · exact hba
      · exact hbc
  rw [e, Set.ncard_pair hac]

theorem gr_dg_le_three {G : SimpleGraph (Fin n)} {p l q r : Fin n}
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) : dg G p ≤ 3 := by
  unfold dg
  calc {w | G.Adj p w}.ncard ≤ ({l, q, r} : Set (Fin n)).ncard :=
        Set.ncard_le_ncard (fun w hw => by rcases hp w hw with rfl | rfl | rfl <;> simp)
    _ ≤ ({q, r} : Set (Fin n)).ncard + 1 := Set.ncard_insert_le l {q, r}
    _ ≤ ({r} : Set (Fin n)).ncard + 1 + 1 := by
        have := Set.ncard_insert_le q {r}
        omega
    _ = 3 := by rw [Set.ncard_singleton]

/-- Covers: adding `v` to a cover of `dropV G v` covers `G`, so `τ` drops by at most 1. -/
theorem gr_cov_dropV {G : SimpleGraph (Fin n)} {k : ℕ} (h : CovLB G k) (v : Fin n) :
    CovLB (dropV G v) (k - 1) := by
  intro T hT
  have h2 := h (insert v T) (fun x y hxy => by
    by_cases hx : x = v
    · left
      rw [hx]
      exact Finset.mem_insert_self v T
    · by_cases hy : y = v
      · right
        rw [hy]
        exact Finset.mem_insert_self v T
      · rcases hT x y ⟨hxy, hx, hy⟩ with h | h
        · left
          exact Finset.mem_insert_of_mem h
        · right
          exact Finset.mem_insert_of_mem h)
  have h3 := Finset.card_insert_le v T
  omega

/-- Covers: a pendant vertex `l` whose neighbour `p` has a second pendant neighbour `l'` can be
deleted without changing `τ` (swap `l'` for `p`). -/
theorem gr_cov_twin {G : SimpleGraph (Fin n)} {k : ℕ} (h : CovLB G k) {l p l' : Fin n}
    (hll' : l' ≠ l) (hlp : G.Adj l p) (hl'p : G.Adj l' p) (hl : ∀ w, G.Adj l w → w = p)
    (hl' : ∀ w, G.Adj l' w → w = p) : CovLB (dropV G l) k := by
  intro T hT
  have hpl : p ≠ l := (G.ne_of_adj hlp).symm
  by_cases hp : p ∈ T
  · apply h T
    intro x y hxy
    by_cases hx : x = l
    · subst hx
      right
      rw [hl y hxy]
      exact hp
    · by_cases hy : y = l
      · subst hy
        left
        rw [hl x hxy.symm]
        exact hp
      · exact hT x y ⟨hxy, hx, hy⟩
  · have hl'T : l' ∈ T := by
      rcases hT l' p ⟨hl'p, hll', hpl⟩ with h' | h'
      · exact h'
      · exact absurd h' hp
    have hc := h (insert p (T.erase l')) (by
      intro x y hxy
      by_cases hx : x = l ∨ x = l'
      · right
        rcases hx with rfl | rfl
        · rw [hl y hxy]
          exact Finset.mem_insert_self p _
        · rw [hl' y hxy]
          exact Finset.mem_insert_self p _
      · by_cases hy : y = l ∨ y = l'
        · left
          rcases hy with rfl | rfl
          · rw [hl x hxy.symm]
            exact Finset.mem_insert_self p _
          · rw [hl' x hxy.symm]
            exact Finset.mem_insert_self p _
        · push Not at hx hy
          rcases hT x y ⟨hxy, hx.1, hy.1⟩ with h' | h'
          · left
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hx.2, h'⟩)
          · right
            exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hy.2, h'⟩))
    have h1 := Finset.card_insert_le p (T.erase l')
    have h2 := Finset.card_erase_of_mem hl'T
    have h3 := Finset.card_pos.mpr ⟨l', hl'T⟩
    omega

/-- No edges: the empty set is a cover and there are no edges. -/
theorem gr_noedge {G : SimpleGraph (Fin n)} (hE : ∀ u v, ¬ G.Adj u v) {k : ℕ} (h : CovLB G k) :
    k = 0 ∧ G.edgeSet.ncard = 0 := by
  refine ⟨?_, ?_⟩
  · have := h ∅ (fun u v huv => absurd huv (hE u v))
    simpa using this
  · have e : G.edgeSet = ∅ := by
      ext e
      induction e using Sym2.ind with
      | _ x y => simp [hE]
    rw [e, Set.ncard_empty]

/-! ## Lower half: restriction identities for `EF` and generic formula facts (lo_) -/

theorem lo_EF_const_false (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    EF G A (fun _ => false) = false := by
  simp [EF]

/-- `v := false` deletes the edges at `v`. -/
theorem lo_EF_upd_false (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n) (hv : v ∉ A)
    (x : Fin n → Bool) : EF G A (upd x v false) = EF (dropV G v) A x := by
  unfold EF
  rw [decide_eq_decide]
  constructor
  · rintro (⟨a, ha, hx⟩ | ⟨u, w, huw, hu, hw⟩)
    · have hav : a ≠ v := fun h => hv (h ▸ ha)
      left
      exact ⟨a, ha, by simpa [upd, hav] using hx⟩
    · have huv : u ≠ v := by
        intro h
        subst h
        simp [upd] at hu
      have hwv : w ≠ v := by
        intro h
        subst h
        simp [upd] at hw
      right
      exact ⟨u, w, ⟨huw, huv, hwv⟩, by simpa [upd, huv] using hu, by simpa [upd, hwv] using hw⟩
  · rintro (⟨a, ha, hx⟩ | ⟨u, w, ⟨huw, huv, hwv⟩, hu, hw⟩)
    · have hav : a ≠ v := fun h => hv (h ▸ ha)
      left
      exact ⟨a, ha, by simpa [upd, hav] using hx⟩
    · right
      exact ⟨u, w, huw, by simpa [upd, huv] using hu, by simpa [upd, hwv] using hw⟩

/-- `a := false` for an isolated OR-input `a ∈ A` removes it from `A`. -/
theorem lo_EF_upd_A (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n) (ha : a ∈ A)
    (hA : Iso G A) (x : Fin n → Bool) : EF G A (upd x a false) = EF G (A.erase a) x := by
  unfold EF
  rw [decide_eq_decide]
  constructor
  · rintro (⟨b, hb, hx⟩ | ⟨u, w, huw, hu, hw⟩)
    · by_cases hba : b = a
      · subst hba
        simp [upd] at hx
      · left
        exact ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, by simpa [upd, hba] using hx⟩
    · have hua : u ≠ a := fun h => hA a ha w (h ▸ huw)
      have hwa : w ≠ a := fun h => hA a ha u (h ▸ huw.symm)
      right
      exact ⟨u, w, huw, by simpa [upd, hua] using hu, by simpa [upd, hwa] using hw⟩
  · rintro (⟨b, hb, hx⟩ | ⟨u, w, huw, hu, hw⟩)
    · obtain ⟨hba, hb'⟩ := Finset.mem_erase.mp hb
      left
      exact ⟨b, hb', by simpa [upd, hba] using hx⟩
    · have hua : u ≠ a := fun h => hA a ha w (h ▸ huw)
      have hwa : w ≠ a := fun h => hA a ha u (h ▸ huw.symm)
      right
      exact ⟨u, w, huw, by simpa [upd, hua] using hu, by simpa [upd, hwa] using hw⟩

/-- `l := true` for a pendant `l` with neighbour `p`: `p` becomes an OR-input and the edges at
`p` disappear. -/
theorem lo_EF_upd_true_pendant (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlp : G.Adj l p) (hl : ∀ w, G.Adj l w → w = p) (hlA : l ∉ A) (x : Fin n → Bool) :
    EF G A (upd x l true) = EF (dropV G p) (insert p A) x := by
  unfold EF
  rw [decide_eq_decide]
  have hpl : p ≠ l := (G.ne_of_adj hlp).symm
  constructor
  · rintro (⟨a, ha, hx⟩ | ⟨u, w, huw, hu, hw⟩)
    · have hal : a ≠ l := fun h => hlA (h ▸ ha)
      left
      exact ⟨a, Finset.mem_insert_of_mem ha, by simpa [upd, hal] using hx⟩
    · by_cases hul : u = l
      · subst hul
        have hwp := hl w huw
        subst hwp
        left
        exact ⟨w, Finset.mem_insert_self w A, by simpa [upd, hpl] using hw⟩
      · by_cases hwl : w = l
        · subst hwl
          have hup := hl u huw.symm
          subst hup
          left
          exact ⟨u, Finset.mem_insert_self u A, by simpa [upd, hpl] using hu⟩
        · have hu' : x u = true := by simpa [upd, hul] using hu
          have hw' : x w = true := by simpa [upd, hwl] using hw
          by_cases hup : u = p
          · subst hup
            left
            exact ⟨u, Finset.mem_insert_self u A, hu'⟩
          · by_cases hwp : w = p
            · subst hwp
              left
              exact ⟨w, Finset.mem_insert_self w A, hw'⟩
            · right
              exact ⟨u, w, ⟨huw, hup, hwp⟩, hu', hw'⟩
  · rintro (⟨a, ha, hx⟩ | ⟨u, w, ⟨huw, hup, hwp⟩, hu, hw⟩)
    · rcases Finset.mem_insert.mp ha with rfl | ha
      · right
        exact ⟨l, a, hlp, by simp [upd], by simpa [upd, hpl] using hx⟩
      · have hal : a ≠ l := fun h => hlA (h ▸ ha)
        left
        exact ⟨a, ha, by simpa [upd, hal] using hx⟩
    · have hul : u ≠ l := fun h => hwp (hl w (h ▸ huw))
      have hwl : w ≠ l := fun h => hup (hl u (h ▸ huw.symm))
      right
      exact ⟨u, w, huw, by simpa [upd, hul] using hu, by simpa [upd, hwl] using hw⟩

/-- `b := true` for `b` with neighbours exactly `a, c`: `a, c` become OR-inputs and the edges at
`a` and `c` disappear. -/
theorem lo_EF_upd_true_tri (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a b c : Fin n)
    (hba : G.Adj b a) (hbc : G.Adj b c) (hb : ∀ w, G.Adj b w → w = a ∨ w = c) (hbA : b ∉ A)
    (x : Fin n → Bool) :
    EF G A (upd x b true) = EF (dropV (dropV G a) c) (insert a (insert c A)) x := by
  unfold EF
  rw [decide_eq_decide]
  have hab : a ≠ b := (G.ne_of_adj hba).symm
  have hcb : c ≠ b := (G.ne_of_adj hbc).symm
  constructor
  · rintro (⟨a', ha', hx⟩ | ⟨u, w, huw, hu, hw⟩)
    · have hab' : a' ≠ b := fun h => hbA (h ▸ ha')
      left
      exact ⟨a', Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha'),
        by simpa [upd, hab'] using hx⟩
    · by_cases hub : u = b
      · subst hub
        have hwu : w ≠ u := (G.ne_of_adj huw).symm
        have hw' : x w = true := by simpa [upd, hwu] using hw
        left
        rcases hb w huw with rfl | rfl
        · exact ⟨w, Finset.mem_insert_self w _, hw'⟩
        · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_self w A), hw'⟩
      · by_cases hwb : w = b
        · subst hwb
          have hu' : x u = true := by simpa [upd, hub] using hu
          left
          rcases hb u huw.symm with rfl | rfl
          · exact ⟨u, Finset.mem_insert_self u _, hu'⟩
          · exact ⟨u, Finset.mem_insert_of_mem (Finset.mem_insert_self u A), hu'⟩
        · have hu' : x u = true := by simpa [upd, hub] using hu
          have hw' : x w = true := by simpa [upd, hwb] using hw
          by_cases hua : u = a
          · subst hua
            left
            exact ⟨u, Finset.mem_insert_self u _, hu'⟩
          · by_cases hwa : w = a
            · subst hwa
              left
              exact ⟨w, Finset.mem_insert_self w _, hw'⟩
            · by_cases huc : u = c
              · subst huc
                left
                exact ⟨u, Finset.mem_insert_of_mem (Finset.mem_insert_self u A), hu'⟩
              · by_cases hwc : w = c
                · subst hwc
                  left
                  exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_self w A), hw'⟩
                · right
                  exact ⟨u, w, ⟨⟨huw, hua, hwa⟩, huc, hwc⟩, hu', hw'⟩
  · rintro (⟨a', ha', hx⟩ | ⟨u, w, ⟨⟨huw, hua, hwa⟩, huc, hwc⟩, hu, hw⟩)
    · rcases Finset.mem_insert.mp ha' with rfl | ha'
      · right
        exact ⟨b, a', hba, by simp [upd], by simpa [upd, hab] using hx⟩
      · rcases Finset.mem_insert.mp ha' with rfl | ha'
        · right
          exact ⟨b, a', hbc, by simp [upd], by simpa [upd, hcb] using hx⟩
        · have hab' : a' ≠ b := fun h => hbA (h ▸ ha')
          left
          exact ⟨a', ha', by simpa [upd, hab'] using hx⟩
    · have hub : u ≠ b := by
        intro h
        rcases hb w (h ▸ huw) with h' | h'
        · exact hwa h'
        · exact hwc h'
      have hwb : w ≠ b := by
        intro h
        rcases hb u (h ▸ huw.symm) with h' | h'
        · exact hua h'
        · exact huc h'
      right
      exact ⟨u, w, huw, by simpa [upd, hub] using hu, by simpa [upd, hwb] using hw⟩

/-- `EF` depends on an endpoint `u` of an edge `uv` (witness: only `v` true). -/
theorem lo_EF_dep_edge (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hA : Iso G A)
    {u v : Fin n} (h : G.Adj u v) :
    EF G A (upd (upd (fun _ => false) v true) u true) ≠
      EF G A (upd (upd (fun _ => false) v true) u false) := by
  have huv : u ≠ v := G.ne_of_adj h
  have h1 : EF G A (upd (upd (fun _ => false) v true) u true) = true := by
    unfold EF
    simp only [decide_eq_true_eq]
    exact Or.inr ⟨u, v, h, by simp [upd], by simp [upd, huv.symm]⟩
  have e : upd (upd (fun _ => false) v true) u false = fun k => decide (k = v) := by
    funext k
    simp only [upd]
    by_cases hk : k = u <;> by_cases hk' : k = v <;> simp_all
  have h2 : EF G A (upd (upd (fun _ => false) v true) u false) = false := by
    rw [e]
    unfold EF
    rw [decide_eq_false_iff_not]
    rintro (⟨a, ha, hx⟩ | ⟨x, y, hxy, hx, hy⟩)
    · simp only [decide_eq_true_eq] at hx
      subst hx
      exact hA a ha u h.symm
    · simp only [decide_eq_true_eq] at hx hy
      subst hx
      subst hy
      exact G.loopless.irrefl _ hxy
  rw [h1, h2]
  simp

/-- `EF` depends on every `a ∈ A` (witness: everything false). -/
theorem lo_EF_dep_A (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) {a : Fin n} (ha : a ∈ A) :
    EF G A (upd (fun _ => false) a true) ≠ EF G A (upd (fun _ => false) a false) := by
  have h1 : EF G A (upd (fun _ => false) a true) = true := by
    unfold EF
    simp only [decide_eq_true_eq]
    exact Or.inl ⟨a, ha, by simp [upd]⟩
  have e : upd (fun _ => false) a false = fun _ => false := by
    funext k
    simp [upd]
  rw [h1, e, lo_EF_const_false]
  simp

/-- A variable the computed function depends on occurs in the formula. -/
theorem lo_occ_pos (φ : DMFormula n) (i : Fin n) (x : Fin n → Bool)
    (h : φ.eval (upd x i true) ≠ φ.eval (upd x i false)) : 1 ≤ occ φ i := by
  by_contra h0
  have h0' : occ φ i = 0 := by omega
  exact h (by rw [eval_upd_of_zero φ i h0' x true, eval_upd_of_zero φ i h0' x false])

/-- Each variable occurs at most `leaves` times. -/
theorem lo_occ_le_leaves (φ : DMFormula n) (i : Fin n) : occ φ i ≤ φ.leaves := by
  rw [leaves_eq]
  exact Finset.single_le_sum (fun k _ => Nat.zero_le (occ φ k)) (Finset.mem_univ i)

/-- Two distinct variables together occur at most `leaves` times. -/
theorem lo_two_occ_le_leaves (φ : DMFormula n) {i j : Fin n} (hij : i ≠ j) :
    occ φ i + occ φ j ≤ φ.leaves := by
  rw [leaves_eq]
  have := Finset.sum_le_sum_of_subset_of_nonneg (s := {i, j}) (t := Finset.univ) (f := occ φ)
    (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair hij] at this
  exact this

/-- A nonconstant function with `ALeaf s` has an actual formula with at most `s` leaves. -/
theorem lo_formula_of_nonconst {s : ℕ} {h : (Fin n → Bool) → Bool} (a : ALeaf s h)
    (x y : Fin n → Bool) (hxy : h x ≠ h y) :
    ∃ φ : DMFormula n, φ.leaves ≤ s ∧ ∀ z, φ.eval z = h z := by
  rcases a with ⟨c, hc⟩ | hφ
  · exact absurd (by rw [hc x, hc y]) hxy
  · exact hφ

/-- Restricting a variable removes all of its occurrences. -/
theorem lo_restrict {s : ℕ} {h : (Fin n → Bool) → Bool} (φ : DMFormula n) (hφ : φ.leaves ≤ s)
    (he : ∀ z, φ.eval z = h z) (i : Fin n) (c : Bool) :
    ALeaf (s - occ φ i) (fun x => h (upd x i c)) := by
  have := restrict_occ φ i c
  exact ALeaf.congr (fun x => he _) (ALeaf.mono (by omega) this)

/-- Subbotovskaya, weak form, for functions: some constant kills two leaves. -/
theorem lo_restrict_kill {s : ℕ} {h : (Fin n → Bool) → Bool} (φ : DMFormula n) (hφ : φ.leaves ≤ s)
    (he : ∀ z, φ.eval z = h z) (i : Fin n) (hi : 1 ≤ occ φ i) (hL : 2 ≤ φ.leaves) :
    ∃ c : Bool, ALeaf (s - 2) (fun x => h (upd x i c)) := by
  obtain ⟨c, hc⟩ := restrict_kill φ i hi hL
  exact ⟨c, ALeaf.congr (fun x => he _) (ALeaf.mono (by omega) hc)⟩

/-- Shape predicate for `lo_single_occ`: `f = β ∨ (α ∧ (ℓ_i ∘_g ψ))` within leaf budget `L`. -/
def lo_single_occ_aux_P (i : Fin n) (L : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (sg g : Bool) (ψ : DMFormula n) (m : ℕ) (α β : (Fin n → Bool) → Bool),
      occ ψ i = 0 ∧ m + ψ.leaves + 1 ≤ L ∧ ALeaf m α ∧ ALeaf m β ∧
      (∀ x c, α (upd x i c) = α x) ∧ (∀ x c, β (upd x i c) = β x) ∧
      (∀ x, β x = true → α x = true) ∧
      ∀ x, f x = (β x || (α x && bop g (litv sg (x i)) (ψ.eval x)))

theorem lo_single_occ_aux_bool1 (g0 p q r : Bool) (h : p = true → q = true)
    (hp : bop g0 p r = true) : bop g0 q r = true := by
  cases g0 <;> cases p <;> cases q <;> cases r <;> simp_all [bop]

theorem lo_single_occ_aux_bool2 (g0 p q r d : Bool) (h : p = true → q = true) :
    bop g0 (p || (q && d)) r = (bop g0 p r || (bop g0 q r && d)) := by
  cases g0 <;> cases p <;> cases q <;> cases r <;> cases d <;> simp_all [bop]

/-- Base: the `i`-leaf is a child of the gate `g0` whose other child is `B`. -/
theorem lo_single_occ_aux_lit (i : Fin n) (g0 s : Bool) (B : DMFormula n) (hB : occ B i = 0)
    {L : ℕ} {f : (Fin n → Bool) → Bool} (hL : 1 + B.leaves ≤ L)
    (hf : ∀ x, f x = bop g0 (litv s (x i)) (B.eval x)) : lo_single_occ_aux_P i L f :=
  ⟨s, g0, B, 0, fun _ => true, fun _ => false, hB, by omega, .inl ⟨true, fun _ => rfl⟩,
    .inl ⟨false, fun _ => rfl⟩, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun x => by rw [hf x]; simp⟩

/-- Step: combine a formula already of the required shape with a sibling `B` free of `i`. -/
theorem lo_single_occ_aux_gate (i : Fin n) (g0 : Bool) (B : DMFormula n) (hB : occ B i = 0)
    {LA : ℕ} {fA : (Fin n → Bool) → Bool} (hA : lo_single_occ_aux_P i LA fA)
    {L : ℕ} {f : (Fin n → Bool) → Bool} (hL : LA + B.leaves ≤ L)
    (hf : ∀ x, f x = bop g0 (fA x) (B.eval x)) : lo_single_occ_aux_P i L f := by
  obtain ⟨sg, g, ψ, m, α, β, hψ, hm, hα, hβ, hαi, hβi, hβα, he⟩ := hA
  have hBL : ALeaf B.leaves B.eval := .inr ⟨B, le_rfl, fun _ => rfl⟩
  refine ⟨sg, g, ψ, m + B.leaves, fun x => bop g0 (α x) (B.eval x),
    fun x => bop g0 (β x) (B.eval x), hψ, by omega, ALeaf.bop g0 hα hBL, ALeaf.bop g0 hβ hBL,
    fun x c => by simp only [hαi, eval_upd_of_zero B i hB],
    fun x c => by simp only [hβi, eval_upd_of_zero B i hB],
    fun x hx => lo_single_occ_aux_bool1 g0 _ _ _ (hβα x) hx, fun x => ?_⟩
  rw [hf x, he x]
  exact lo_single_occ_aux_bool2 g0 _ _ _ _ (hβα x)

/-- One side: the `i`-leaf lies in `A`, and `B` has no `i`. -/
theorem lo_single_occ_aux_side (i : Fin n) (g0 : Bool) (A B : DMFormula n) (hA : occ A i = 1)
    (hB : occ B i = 0)
    (iA : (∀ b, A ≠ DMFormula.lit i b) → lo_single_occ_aux_P i A.leaves A.eval)
    {L : ℕ} {f : (Fin n → Bool) → Bool} (hL : A.leaves + B.leaves ≤ L)
    (hf : ∀ x, f x = bop g0 (A.eval x) (B.eval x)) : lo_single_occ_aux_P i L f := by
  by_cases hl : ∃ s, A = DMFormula.lit i s
  · obtain ⟨s, rfl⟩ := hl
    have h1 : (DMFormula.lit i s).leaves = 1 := rfl
    exact lo_single_occ_aux_lit i g0 s B hB (by omega) (fun x => by rw [hf x, eval_lit])
  · push Not at hl
    exact lo_single_occ_aux_gate i g0 B hB (iA hl) hL hf

/-- A gate node: exactly one of the two children contains the `i`-leaf. -/
theorem lo_single_occ_aux_node (i : Fin n) (g0 : Bool) (A B : DMFormula n)
    (h1 : occ A i + occ B i = 1)
    (iA : occ A i = 1 → (∀ b, A ≠ DMFormula.lit i b) → lo_single_occ_aux_P i A.leaves A.eval)
    (iB : occ B i = 1 → (∀ b, B ≠ DMFormula.lit i b) → lo_single_occ_aux_P i B.leaves B.eval)
    {L : ℕ} {f : (Fin n → Bool) → Bool} (hL : A.leaves + B.leaves ≤ L)
    (hf : ∀ x, f x = bop g0 (A.eval x) (B.eval x)) : lo_single_occ_aux_P i L f := by
  by_cases hA : occ A i = 1
  · exact lo_single_occ_aux_side i g0 A B hA (by omega) (iA hA) hL hf
  · exact lo_single_occ_aux_side i g0 B A (by omega) (by omega) (iB (by omega)) (by omega)
      (fun x => by rw [hf x, bop_comm])

/-- Induction on `φ` along the path to the unique `i`-leaf. -/
theorem lo_single_occ_aux_main (i : Fin n) (φ : DMFormula n) :
    occ φ i = 1 → (∀ b, φ ≠ DMFormula.lit i b) → lo_single_occ_aux_P i φ.leaves φ.eval := by
  induction φ with
  | lit j b =>
    intro h1 hlit
    by_cases hj : j = i
    · subst hj; exact absurd rfl (hlit b)
    · simp [occ, Ne.symm hj] at h1
  | and A B iA iB =>
    intro h1 _
    exact lo_single_occ_aux_node i false A B h1 iA iB le_rfl (fun x => rfl)
  | or A B iA iB =>
    intro h1 _
    exact lo_single_occ_aux_node i true A B h1 iA iB le_rfl (fun x => rfl)

/-- Single-occurrence decomposition (tool for the open cases (T)/(TP)): if `i` occurs once and
`φ` is not that literal, then `φ = β ∨ (α ∧ (ℓ_i ∘_g ψ))` with `α = C[1]`, `β = C[0]` for the
one-hole context `C` above the parent gate `g` of the `i`-leaf. -/
theorem lo_single_occ (φ : DMFormula n) (i : Fin n) (h1 : occ φ i = 1)
    (hlit : ∀ b, φ ≠ DMFormula.lit i b) :
    ∃ (sg g : Bool) (ψ : DMFormula n) (m : ℕ) (α β : (Fin n → Bool) → Bool),
      occ ψ i = 0 ∧ m + ψ.leaves + 1 ≤ φ.leaves ∧ ALeaf m α ∧ ALeaf m β ∧
      (∀ x c, α (upd x i c) = α x) ∧ (∀ x c, β (upd x i c) = β x) ∧
      (∀ x, β x = true → α x = true) ∧
      ∀ x, φ.eval x = (β x || (α x && bop g (litv sg (x i)) (ψ.eval x))) := by
  exact lo_single_occ_aux_main i φ h1 hlit

/-! ## Lower half: the induction steps (lo_) -/

/-- Base: no edges and no OR-inputs. -/
theorem lo_base (G : SimpleGraph (Fin n)) (hE : ∀ u v, ¬ G.Adj u v) : LoClaim G ∅ := by
  intro k s hk _
  obtain ⟨h1, h2⟩ := gr_noedge hE hk
  simp [h1, h2]

/-- Step (A): `A ≠ ∅`; restrict some `a ∈ A` to false (drop ≥ 1, measure drop 1). -/
theorem lo_stepA (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G) (hA : Iso G A)
    (IH : LoIH G A) (hne : A.Nonempty) : LoClaim G A := by
  intro k s hk hs
  obtain ⟨a, ha⟩ := hne
  obtain ⟨φ, hφ, he⟩ := lo_formula_of_nonconst hs _ _ (lo_EF_dep_A G A ha)
  have hocc : 1 ≤ occ φ a :=
    lo_occ_pos φ a (fun _ => false) (by rw [he, he]; exact lo_EF_dep_A G A ha)
  have hr := lo_restrict φ hφ he a false
  have hr' : ALeaf (s - occ φ a) (EF G (A.erase a)) :=
    ALeaf.congr (fun x => lo_EF_upd_A G A a ha hA x) hr
  have hc1 := Finset.card_erase_of_mem ha
  have hc2 := Finset.card_pos.mpr ⟨a, ha⟩
  have hc3 := lo_occ_le_leaves φ a
  have := IH G (A.erase a) hG (gr_iso_erase G A a hA) (by omega) k (s - occ φ a) hk hr'
  omega

/-- Step (P2): pendant `l` at `p` and a second pendant `l'` at `p`; restrict `l := false`
(drop ≥ 1; `|E|` drops 1, `τ` unchanged by `gr_cov_twin`). -/
theorem lo_stepP2 (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G) (hA : Iso G A)
    (IH : LoIH G A) (l p l' : Fin n) (hll' : l' ≠ l) (hlp : G.Adj l p) (hl'p : G.Adj l' p)
    (hl : ∀ w, G.Adj l w → w = p) (hl' : ∀ w, G.Adj l' w → w = p) : LoClaim G A := by
  intro k s hk hs
  have hlA : l ∉ A := gr_not_mem_of_adj hA hlp
  have hdep := lo_EF_dep_edge G A hA hlp
  obtain ⟨φ, hφ, he⟩ := lo_formula_of_nonconst hs _ _ hdep
  have hocc : 1 ≤ occ φ l :=
    lo_occ_pos φ l (upd (fun _ => false) p true) (by rw [he, he]; exact hdep)
  have hr := lo_restrict φ hφ he l false
  have hr' : ALeaf (s - occ φ l) (EF (dropV G l) A) :=
    ALeaf.congr (fun x => lo_EF_upd_false G A l hlA x) hr
  have hE := gr_ncard_dropV G l
  have hd := gr_dg_one hlp hl
  have hc3 := lo_occ_le_leaves φ l
  have := IH (dropV G l) A (gr_good_mono (gr_dropV_le G l) hG) (gr_iso_mono (gr_dropV_le G l) hA)
    (by omega) k (s - occ φ l) (gr_cov_twin hk hll' hlp hl'p hl hl') hr'
  omega

/-- Step (P1): pendant `l` at `p` with `N(p) ⊆ {l, q}`; restrict `l` to the killing constant of
`lo_restrict_kill` (drop ≥ 2). `l := false`: `|E|` drops 1, `τ` at most 1.
`l := true`: `A` gains `p`, `|E|` drops `dg p ≤ 2`, `τ` at most 1. -/
theorem lo_stepP1 (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G) (hA : Iso G A)
    (IH : LoIH G A) (l p q : Fin n) (hlp : G.Adj l p) (hl : ∀ w, G.Adj l w → w = p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) : LoClaim G A := by
  intro k s hk hs
  have hlA : l ∉ A := gr_not_mem_of_adj hA hlp
  have hpA : p ∉ A := gr_not_mem_of_adj hA hlp.symm
  have hdep := lo_EF_dep_edge G A hA hlp
  obtain ⟨φ, hφ, he⟩ := lo_formula_of_nonconst hs _ _ hdep
  have hoccl : 1 ≤ occ φ l :=
    lo_occ_pos φ l (upd (fun _ => false) p true) (by rw [he, he]; exact hdep)
  have hdep' := lo_EF_dep_edge G A hA hlp.symm
  have hoccp : 1 ≤ occ φ p :=
    lo_occ_pos φ p (upd (fun _ => false) l true) (by rw [he, he]; exact hdep')
  have h2 := lo_two_occ_le_leaves φ (G.ne_of_adj hlp)
  obtain ⟨c, hc⟩ := lo_restrict_kill φ hφ he l hoccl (by omega)
  have hE := gr_ncard_dropV G l
  have hd := gr_dg_one hlp hl
  cases c with
  | false =>
    have hr' : ALeaf (s - 2) (EF (dropV G l) A) :=
      ALeaf.congr (fun x => lo_EF_upd_false G A l hlA x) hc
    have := IH (dropV G l) A (gr_good_mono (gr_dropV_le G l) hG)
      (gr_iso_mono (gr_dropV_le G l) hA) (by omega) (k - 1) (s - 2) (gr_cov_dropV hk l) hr'
    omega
  | true =>
    have hr' : ALeaf (s - 2) (EF (dropV G p) (insert p A)) :=
      ALeaf.congr (fun x => lo_EF_upd_true_pendant G A l p hlp hl hlA x) hc
    have hEp := gr_ncard_dropV G p
    have hdp := gr_dg_le_two hp
    have hdp1 := gr_dg_pos hlp.symm
    have hcard := Finset.card_insert_of_notMem hpA
    have := IH (dropV G p) (insert p A) (gr_good_mono (gr_dropV_le G p) hG)
      (gr_iso_insert G A p hA) (by omega) (k - 1) (s - 2) (gr_cov_dropV hk p) hr'
    omega

/-- (T) bookkeeping, `b := false`: a restriction that drops 3 leaves suffices
(`|E|` drops 2, `τ` drops at most 1). -/
theorem lo_T_zero (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G) (hA : Iso G A)
    (IH : LoIH G A) (a b c : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hb : ∀ w, G.Adj b w → w = a ∨ w = c) (_hc : ∀ w, G.Adj c w → w = a ∨ w = b) (k s : ℕ)
    (hk : CovLB G k) (hdrop : ALeaf (s - 3) (fun x => EF G A (upd x b false))) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  have hbA : b ∉ A := gr_not_mem_of_adj hA hab.symm
  have hr' : ALeaf (s - 3) (EF (dropV G b) A) :=
    ALeaf.congr (fun x => lo_EF_upd_false G A b hbA x) hdrop
  have hE := gr_ncard_dropV G b
  have hac : a ≠ c := (G.ne_of_adj hca).symm
  have hd := gr_dg_two hab.symm hbc hac hb
  have hpos : 1 ≤ (dropV G b).edgeSet.ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr
      ⟨s(c, a), (show (dropV G b).Adj c a from ⟨hca, (G.ne_of_adj hbc).symm, G.ne_of_adj hab⟩)⟩
  have := IH (dropV G b) A (gr_good_mono (gr_dropV_le G b) hG) (gr_iso_mono (gr_dropV_le G b) hA)
    (by omega) (k - 1) (s - 3) (gr_cov_dropV hk b) hr'
  omega

/-- (T) bookkeeping, `b := true`: a restriction that drops `dg a + 1` leaves suffices
(`A` gains `a, c`; `|E|` drops `dg a + 1`; `τ` drops at most 2). -/
theorem lo_T_one (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G) (hA : Iso G A)
    (IH : LoIH G A) (a b c : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hb : ∀ w, G.Adj b w → w = a ∨ w = c) (hc : ∀ w, G.Adj c w → w = a ∨ w = b) (k s : ℕ)
    (hk : CovLB G k) (hdrop : ALeaf (s - (dg G a + 1)) (fun x => EF G A (upd x b true))) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  have hbA : b ∉ A := gr_not_mem_of_adj hA hab.symm
  have haA : a ∉ A := gr_not_mem_of_adj hA hab
  have hcA : c ∉ A := gr_not_mem_of_adj hA hca
  have hac : a ≠ c := (G.ne_of_adj hca).symm
  have hr' : ALeaf (s - (dg G a + 1)) (EF (dropV (dropV G a) c) (insert a (insert c A))) :=
    ALeaf.congr (fun x => lo_EF_upd_true_tri G A a b c hab.symm hbc hb hbA x) hdrop
  have hE1 := gr_ncard_dropV G a
  have hE2 := gr_ncard_dropV (dropV G a) c
  have hd2 : dg (dropV G a) c = 1 :=
    gr_dg_one (show (dropV G a).Adj c b from ⟨hbc.symm, hac.symm, (G.ne_of_adj hab).symm⟩)
      (fun w hw => by
        rcases hc w hw.1 with h | h
        · exact absurd h hw.2.2
        · exact h)
  have hda := gr_dg_pos hab
  have hc1 := Finset.card_insert_of_notMem hcA
  have haA' : a ∉ insert c A := by
    rw [Finset.mem_insert]
    rintro (h | h)
    · exact hac h
    · exact haA h
  have hc2 := Finset.card_insert_of_notMem haA'
  have hle : dropV (dropV G a) c ≤ G := le_trans (gr_dropV_le _ c) (gr_dropV_le G a)
  have hiso : Iso (dropV (dropV G a) c) (insert a (insert c A)) := by
    intro x hx w hw
    rcases Finset.mem_insert.mp hx with hxa | hx
    · exact hw.1.2.1 hxa
    · exact gr_iso_insert (dropV G a) A c (gr_iso_mono (gr_dropV_le G a) hA) x hx w hw
  have := IH (dropV (dropV G a) c) (insert a (insert c A)) (gr_good_mono hle hG) hiso
    (by omega) (k - 1 - 1) (s - (dg G a + 1)) (gr_cov_dropV (gr_cov_dropV hk a) c) hr'
  omega

/-! ## lo_stepT helpers (Triangle/lo_stepT.lean; argument: Triangle/lo_stepT.chosen.md) -/

/-- (MIN) A nonconstant `h` with `ALeaf s h` has a minimum-size formula. -/
theorem lo_stepT_aux_min {s : ℕ} {h : (Fin n → Bool) → Bool} (a : ALeaf s h)
    (x y : Fin n → Bool) (hxy : h x ≠ h y) :
    ∃ φ : DMFormula n, φ.leaves ≤ s ∧ (∀ z, φ.eval z = h z) ∧
      ∀ ψ : DMFormula n, (∀ z, ψ.eval z = h z) → φ.leaves ≤ ψ.leaves := by
  classical
  obtain ⟨φ0, h0, e0⟩ := lo_formula_of_nonconst a x y hxy
  have hex : ∃ m, ∃ φ : DMFormula n, φ.leaves = m ∧ ∀ z, φ.eval z = h z := ⟨_, φ0, rfl, e0⟩
  obtain ⟨φ, hφm, hφe⟩ := Nat.find_spec hex
  refine ⟨φ, ?_, hφe, fun ψ hψ => ?_⟩
  · rw [hφm]; exact (Nat.find_min' hex ⟨φ0, rfl, e0⟩).trans h0
  · rw [hφm]; exact Nat.find_min' hex ⟨ψ, rfl, hψ⟩

/-- `φ` is a literal of the variable `v`. -/
def lo_stepT_aux_isv (v : Fin n) : DMFormula n → Prop
  | .lit i _ => i = v
  | .and _ _ => False
  | .or _ _ => False

/-- Reduced w.r.t. `v`: no `v`-literal has a sibling that reads `v`. -/
def lo_stepT_aux_Red (v : Fin n) : DMFormula n → Prop
  | .lit _ _ => True
  | .and A B => lo_stepT_aux_Red v A ∧ lo_stepT_aux_Red v B ∧
      (lo_stepT_aux_isv v A → occ B v = 0) ∧ (lo_stepT_aux_isv v B → occ A v = 0)
  | .or A B => lo_stepT_aux_Red v A ∧ lo_stepT_aux_Red v B ∧
      (lo_stepT_aux_isv v A → occ B v = 0) ∧ (lo_stepT_aux_isv v B → occ A v = 0)

/-- Absorption: next to the literal `litv sg (x v)` under gate `g`, the sibling may read `v` as the
non-absorbing value `xor g sg`. -/
theorem lo_stepT_aux_absorb (g sg : Bool) (v : Fin n) (B : DMFormula n) (x : Fin n → Bool) :
    bop g (litv sg (x v)) (B.eval x) = bop g (litv sg (x v)) (B.eval (upd x v (xor g sg))) := by
  by_cases hx : x v = xor g sg
  · have e : upd x v (xor g sg) = x := by
      funext k
      unfold upd
      split_ifs with hk
      · rw [hk, hx]
      · rfl
    rw [e]
  · have hx' : x v = !(xor g sg) := by
      cases h1 : x v <;> cases h2 : xor g sg <;> simp_all
    rw [hx']
    cases g <;> cases sg <;> simp [bop, litv]

theorem lo_stepT_aux_shrink_gate (v : Fin n) (g : Bool) (A B : DMFormula n)
    (ihA : ¬ lo_stepT_aux_Red v A → ALeaf (A.leaves - 1) A.eval)
    (ihB : ¬ lo_stepT_aux_Red v B → ALeaf (B.leaves - 1) B.eval)
    (h : ¬ (lo_stepT_aux_Red v A ∧ lo_stepT_aux_Red v B ∧
      (lo_stepT_aux_isv v A → occ B v = 0) ∧ (lo_stepT_aux_isv v B → occ A v = 0))) :
    ALeaf (A.leaves + B.leaves - 1) (fun x => bop g (A.eval x) (B.eval x)) := by
  have hA1 := leaves_pos A
  have hB1 := leaves_pos B
  by_cases hRA : lo_stepT_aux_Red v A
  · by_cases hRB : lo_stepT_aux_Red v B
    · by_cases hCA : lo_stepT_aux_isv v A → occ B v = 0
      · have hCB : ¬ (lo_stepT_aux_isv v B → occ A v = 0) := fun hCB => h ⟨hRA, hRB, hCA, hCB⟩
        have hvB : lo_stepT_aux_isv v B := by
          by_contra hh
          exact hCB (fun h' => absurd h' hh)
        have hoA : occ A v ≠ 0 := fun h0 => hCB (fun _ => h0)
        cases B with
        | lit i sg =>
          have hi : i = v := hvB
          have hr := restrict_occ A v (xor g sg)
          have hl : ALeaf 1 (fun x => (DMFormula.lit i sg).eval x) :=
            .inr ⟨_, by simp [DMFormula.leaves], fun _ => rfl⟩
          refine ALeaf.mono ?_ (ALeaf.congr (fun x => ?_) (ALeaf.bop g hr hl))
          · simp only [DMFormula.leaves]; omega
          · show bop g (A.eval (upd x v (xor g sg))) ((DMFormula.lit i sg).eval x) =
              bop g (A.eval x) ((DMFormula.lit i sg).eval x)
            rw [eval_lit, hi, bop_comm, ← lo_stepT_aux_absorb g sg v A x, bop_comm]
        | and _ _ => exact absurd hvB id
        | or _ _ => exact absurd hvB id
      · have hvA : lo_stepT_aux_isv v A := by
          by_contra hh
          exact hCA (fun h' => absurd h' hh)
        have hoB : occ B v ≠ 0 := fun h0 => hCA (fun _ => h0)
        cases A with
        | lit i sg =>
          have hi : i = v := hvA
          have hr := restrict_occ B v (xor g sg)
          have hl : ALeaf 1 (fun x => (DMFormula.lit i sg).eval x) :=
            .inr ⟨_, by simp [DMFormula.leaves], fun _ => rfl⟩
          refine ALeaf.mono ?_ (ALeaf.congr (fun x => ?_) (ALeaf.bop g hl hr))
          · simp only [DMFormula.leaves]; omega
          · show bop g ((DMFormula.lit i sg).eval x) (B.eval (upd x v (xor g sg))) =
              bop g ((DMFormula.lit i sg).eval x) (B.eval x)
            rw [eval_lit, hi, ← lo_stepT_aux_absorb g sg v B x]
        | and _ _ => exact absurd hvA id
        | or _ _ => exact absurd hvA id
    · have := ihB hRB
      refine ALeaf.mono ?_ (ALeaf.bop g (.inr ⟨A, le_rfl, fun _ => rfl⟩) this)
      omega
  · have := ihA hRA
    refine ALeaf.mono ?_ (ALeaf.bop g this (.inr ⟨B, le_rfl, fun _ => rfl⟩))
    omega

/-- (RED-shrink) A formula that is not reduced can be shortened by one leaf. -/
theorem lo_stepT_aux_red_shrink (v : Fin n) (φ : DMFormula n) (h : ¬ lo_stepT_aux_Red v φ) :
    ALeaf (φ.leaves - 1) φ.eval := by
  induction φ with
  | lit i s => exact absurd trivial h
  | and A B ihA ihB =>
    exact ALeaf.congr (fun x => rfl) (lo_stepT_aux_shrink_gate v false A B ihA ihB h)
  | or A B ihA ihB =>
    exact ALeaf.congr (fun x => rfl) (lo_stepT_aux_shrink_gate v true A B ihA ihB h)

/-- (RED-min) A minimum formula of a nonconstant function is reduced. -/
theorem lo_stepT_aux_red_of_min (v : Fin n) (φ : DMFormula n) {h : (Fin n → Bool) → Bool}
    (he : ∀ z, φ.eval z = h z)
    (hmin : ∀ ψ : DMFormula n, (∀ z, ψ.eval z = h z) → φ.leaves ≤ ψ.leaves)
    (x y : Fin n → Bool) (hxy : h x ≠ h y) : lo_stepT_aux_Red v φ := by
  by_contra hR
  have h1 := lo_stepT_aux_red_shrink v φ hR
  obtain ⟨ψ, hψ, hψe⟩ := lo_formula_of_nonconst h1 x y (by rwa [he, he])
  have := hmin ψ (fun z => (hψe z).trans (he z))
  have := leaves_pos φ
  omega

/-- Killing constant of a literal with sign `sg` under the gate `g` (`g = true` is OR). -/
def lo_stepT_aux_kc (sg g : Bool) : Bool := if g then sg else !sg

/-- Number of `v`-leaves whose parent gate has killing constant `κ`; `p` is the gate above the
root (`none` at the root). -/
def lo_stepT_aux_kp (v : Fin n) (κ : Bool) : Option Bool → DMFormula n → ℕ
  | none, .lit _ _ => 0
  | some g, .lit i sg => if i = v ∧ lo_stepT_aux_kc sg g = κ then 1 else 0
  | _, .and A B => lo_stepT_aux_kp v κ (some false) A + lo_stepT_aux_kp v κ (some false) B
  | _, .or A B => lo_stepT_aux_kp v κ (some true) A + lo_stepT_aux_kp v κ (some true) B

theorem lo_stepT_aux_kp_some (v : Fin n) (g : Bool) (φ : DMFormula n) :
    lo_stepT_aux_kp v false (some g) φ + lo_stepT_aux_kp v true (some g) φ = occ φ v := by
  induction φ generalizing g with
  | lit i sg =>
    simp only [lo_stepT_aux_kp, occ]
    by_cases hi : i = v
    · subst hi
      cases h : lo_stepT_aux_kc sg g <;> simp
    · simp [hi, Ne.symm hi]
  | and A B ihA ihB =>
    simp only [lo_stepT_aux_kp, occ]
    have := ihA false
    have := ihB false
    omega
  | or A B ihA ihB =>
    simp only [lo_stepT_aux_kp, occ]
    have := ihA true
    have := ihB true
    omega

/-- (KOCC-part) -/
theorem lo_stepT_aux_kp_part (v : Fin n) (φ : DMFormula n) (hφ : ∀ j sg, φ ≠ .lit j sg) :
    lo_stepT_aux_kp v false none φ + lo_stepT_aux_kp v true none φ = occ φ v := by
  cases φ with
  | lit j sg => exact absurd rfl (hφ j sg)
  | and A B =>
    simp only [lo_stepT_aux_kp, occ]
    have := lo_stepT_aux_kp_some v false A
    have := lo_stepT_aux_kp_some v false B
    omega
  | or A B =>
    simp only [lo_stepT_aux_kp, occ]
    have := lo_stepT_aux_kp_some v true A
    have := lo_stepT_aux_kp_some v true B
    omega

/-- (KOCC-zero) -/
theorem lo_stepT_aux_kp_zero (v : Fin n) (κ : Bool) (p : Option Bool) (φ : DMFormula n)
    (h : occ φ v = 0) : lo_stepT_aux_kp v κ p φ = 0 := by
  induction φ generalizing p with
  | lit i sg =>
    cases p with
    | none => rfl
    | some g =>
      have hi : i ≠ v := by
        rintro rfl
        simp [occ] at h
      simp [lo_stepT_aux_kp, hi]
  | and A B ihA ihB =>
    have hA0 : occ A v = 0 := by simp only [occ] at h; omega
    have hB0 : occ B v = 0 := by simp only [occ] at h; omega
    simp only [lo_stepT_aux_kp, ihA (some false) hA0, ihB (some false) hB0]
  | or A B ihA ihB =>
    have hA0 : occ A v = 0 := by simp only [occ] at h; omega
    have hB0 : occ B v = 0 := by simp only [occ] at h; omega
    simp only [lo_stepT_aux_kp, ihA (some true) hA0, ihB (some true) hB0]

theorem lo_stepT_aux_kp_some_eq (v : Fin n) (κ g : Bool) (A : DMFormula n)
    (h : ¬ lo_stepT_aux_isv v A) :
    lo_stepT_aux_kp v κ (some g) A = lo_stepT_aux_kp v κ none A := by
  cases A with
  | lit i sg =>
    have hi : ¬ i = v := h
    simp [lo_stepT_aux_kp, hi]
  | and _ _ => simp only [lo_stepT_aux_kp]
  | or _ _ => simp only [lo_stepT_aux_kp]

theorem lo_stepT_aux_lit_kill (sg g y : Bool) : bop g (litv sg (lo_stepT_aux_kc sg g)) y = g := by
  cases sg <;> cases g <;> cases y <;> rfl

theorem lo_stepT_aux_lit_pass (sg g κ : Bool) (hk : ¬ lo_stepT_aux_kc sg g = κ) (y : Bool) :
    bop g (litv sg κ) y = y := by
  cases sg <;> cases g <;> cases κ <;> cases y <;> simp_all [lo_stepT_aux_kc, litv, bop]
/-- `u x i j` sets `b := i`, then `c := j`. -/
def lo_stepT_aux_u (b c : Fin n) (x : Fin n → Bool) (i j : Bool) : Fin n → Bool := upd (upd x b i) c j

def lo_stepT_aux_ORt (b c : Fin n) (φ : DMFormula n) : Prop :=
  ∀ x, φ.eval (lo_stepT_aux_u b c x true true) = true →
    φ.eval (lo_stepT_aux_u b c x true false) = true ∨ φ.eval (lo_stepT_aux_u b c x false true) = true

def lo_stepT_aux_ANDt (b c : Fin n) (φ : DMFormula n) : Prop :=
  ∀ x, φ.eval (lo_stepT_aux_u b c x true false) = true → φ.eval (lo_stepT_aux_u b c x false true) = true →
    φ.eval (lo_stepT_aux_u b c x false false) = true

theorem lo_stepT_aux_eval_u_c0 {b c : Fin n} (ψ : DMFormula n) (h : occ ψ c = 0) (x : Fin n → Bool)
    (i j : Bool) : ψ.eval (lo_stepT_aux_u b c x i j) = ψ.eval (upd x b i) := by
  unfold lo_stepT_aux_u; exact eval_upd_of_zero ψ c h _ j

theorem lo_stepT_aux_eval_u_b0 {b c : Fin n} (hbc : b ≠ c) (ψ : DMFormula n) (h : occ ψ b = 0)
    (x : Fin n → Bool) (i j : Bool) : ψ.eval (lo_stepT_aux_u b c x i j) = ψ.eval (upd x c j) := by
  have e : lo_stepT_aux_u b c x i j = upd (upd x c j) b i := by
    funext k; unfold lo_stepT_aux_u upd
    by_cases hk : k = c
    · subst hk; simp [Ne.symm hbc]
    · by_cases hk' : k = b
      · subst hk'; simp [hbc]
      · simp [hk, hk']
  rw [e]; exact eval_upd_of_zero ψ b h _ i

theorem lo_stepT_aux_ort_of_c0 {b c : Fin n} (φ : DMFormula n) (h : occ φ c = 0) : lo_stepT_aux_ORt b c φ := by
  intro x hx; left; rw [lo_stepT_aux_eval_u_c0 φ h] at hx ⊢; exact hx

theorem lo_stepT_aux_ort_of_b0 {b c : Fin n} (hbc : b ≠ c) (φ : DMFormula n) (h : occ φ b = 0) :
    lo_stepT_aux_ORt b c φ := by
  intro x hx; right; rw [lo_stepT_aux_eval_u_b0 hbc φ h] at hx ⊢; exact hx

/-- Lemma TWO_RO: two variables read at most once each give an OR-type or AND-type formula. -/
theorem lo_stepT_aux_two_read_once {b c : Fin n} (hbc : b ≠ c) (φ : DMFormula n) (hb : occ φ b ≤ 1)
    (hc : occ φ c ≤ 1) : lo_stepT_aux_ORt b c φ ∨ lo_stepT_aux_ANDt b c φ := by
  induction φ with
  | lit i s =>
    left
    by_cases hi : i = c
    · subst hi; exact lo_stepT_aux_ort_of_b0 hbc _ (by simp [occ, hbc])
    · exact lo_stepT_aux_ort_of_c0 _ (by simp [occ, Ne.symm hi])
  | and A B ihA ihB =>
    have hb' : occ A b + occ B b ≤ 1 := hb
    have hc' : occ A c + occ B c ≤ 1 := hc
    by_cases hb0 : occ A b + occ B b = 0
    · left; exact lo_stepT_aux_ort_of_b0 hbc _ (show occ A b + occ B b = 0 from hb0)
    by_cases hc0 : occ A c + occ B c = 0
    · left; exact lo_stepT_aux_ort_of_c0 _ (show occ A c + occ B c = 0 from hc0)
    rcases Nat.lt_or_ge (occ A b) 1 with hAb | hAb <;>
      rcases Nat.lt_or_ge (occ A c) 1 with hAc | hAc
    · -- both in B
      have hBb : occ B b ≤ 1 := by omega
      have hBc : occ B c ≤ 1 := by omega
      have hAb0 : occ A b = 0 := by omega
      have hAc0 : occ A c = 0 := by omega
      have eA : ∀ x i j, A.eval (lo_stepT_aux_u b c x i j) = A.eval x := fun x i j => by
        rw [lo_stepT_aux_eval_u_c0 A hAc0, eval_upd_of_zero A b hAb0]
      rcases ihB hBb hBc with h | h
      · left; intro x hx; simp only [DMFormula.eval, eA, Bool.and_eq_true] at hx ⊢
        rcases h x hx.2 with h' | h' <;> simp [hx.1, h']
      · right; intro x h1 h2; simp only [DMFormula.eval, eA, Bool.and_eq_true] at h1 h2 ⊢
        exact ⟨h1.1, h x h1.2 h2.2⟩
    · -- b in B, c in A: split
      have hBc0 : occ B c = 0 := by omega
      have hAb0 : occ A b = 0 := by omega
      right; intro x h1 h2
      simp only [DMFormula.eval, Bool.and_eq_true, lo_stepT_aux_eval_u_b0 hbc A hAb0, lo_stepT_aux_eval_u_c0 B hBc0] at h1 h2 ⊢
      exact ⟨h1.1, h2.2⟩
    · -- b in A, c in B: split
      have hAc0 : occ A c = 0 := by omega
      have hBb0 : occ B b = 0 := by omega
      right; intro x h1 h2
      simp only [DMFormula.eval, Bool.and_eq_true, lo_stepT_aux_eval_u_c0 A hAc0, lo_stepT_aux_eval_u_b0 hbc B hBb0] at h1 h2 ⊢
      exact ⟨h2.1, h1.2⟩
    · -- both in A
      have hBb0 : occ B b = 0 := by omega
      have hBc0 : occ B c = 0 := by omega
      have eB : ∀ x i j, B.eval (lo_stepT_aux_u b c x i j) = B.eval x := fun x i j => by
        rw [lo_stepT_aux_eval_u_c0 B hBc0, eval_upd_of_zero B b hBb0]
      rcases ihA (by omega) (by omega) with h | h
      · left; intro x hx; simp only [DMFormula.eval, eB, Bool.and_eq_true] at hx ⊢
        rcases h x hx.1 with h' | h' <;> simp [hx.2, h']
      · right; intro x h1 h2; simp only [DMFormula.eval, eB, Bool.and_eq_true] at h1 h2 ⊢
        exact ⟨h x h1.1 h2.1, h1.2⟩
  | or A B ihA ihB =>
    have hb' : occ A b + occ B b ≤ 1 := hb
    have hc' : occ A c + occ B c ≤ 1 := hc
    by_cases hb0 : occ A b + occ B b = 0
    · left; exact lo_stepT_aux_ort_of_b0 hbc _ (show occ A b + occ B b = 0 from hb0)
    by_cases hc0 : occ A c + occ B c = 0
    · left; exact lo_stepT_aux_ort_of_c0 _ (show occ A c + occ B c = 0 from hc0)
    rcases Nat.lt_or_ge (occ A b) 1 with hAb | hAb <;>
      rcases Nat.lt_or_ge (occ A c) 1 with hAc | hAc
    · have hAb0 : occ A b = 0 := by omega
      have hAc0 : occ A c = 0 := by omega
      have eA : ∀ x i j, A.eval (lo_stepT_aux_u b c x i j) = A.eval x := fun x i j => by
        rw [lo_stepT_aux_eval_u_c0 A hAc0, eval_upd_of_zero A b hAb0]
      rcases ihB (by omega) (by omega) with h | h
      · left; intro x hx; simp only [DMFormula.eval, eA, Bool.or_eq_true] at hx ⊢
        rcases hx with hx | hx
        · simp [hx]
        · rcases h x hx with h' | h' <;> simp [h']
      · right; intro x h1 h2; simp only [DMFormula.eval, eA, Bool.or_eq_true] at h1 h2 ⊢
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · rcases h2 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (h x h1 h2)
    · have hBc0 : occ B c = 0 := by omega
      have hAb0 : occ A b = 0 := by omega
      left; intro x hx
      simp only [DMFormula.eval, Bool.or_eq_true, lo_stepT_aux_eval_u_b0 hbc A hAb0, lo_stepT_aux_eval_u_c0 B hBc0] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inl (Or.inr hx)
    · have hAc0 : occ A c = 0 := by omega
      have hBb0 : occ B b = 0 := by omega
      left; intro x hx
      simp only [DMFormula.eval, Bool.or_eq_true, lo_stepT_aux_eval_u_c0 A hAc0, lo_stepT_aux_eval_u_b0 hbc B hBb0] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    · have hBb0 : occ B b = 0 := by omega
      have hBc0 : occ B c = 0 := by omega
      have eB : ∀ x i j, B.eval (lo_stepT_aux_u b c x i j) = B.eval x := fun x i j => by
        rw [lo_stepT_aux_eval_u_c0 B hBc0, eval_upd_of_zero B b hBb0]
      rcases ihA (by omega) (by omega) with h | h
      · left; intro x hx; simp only [DMFormula.eval, eB, Bool.or_eq_true] at hx ⊢
        rcases hx with hx | hx
        · rcases h x hx with h' | h' <;> simp [h']
        · simp [hx]
      · right; intro x h1 h2; simp only [DMFormula.eval, eB, Bool.or_eq_true] at h1 h2 ⊢
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · exact Or.inl (h x h1 h2)
          · exact Or.inr h2
        · exact Or.inr h1


/-- (DROP), gate step. -/
theorem lo_stepT_aux_drop_gate (v : Fin n) (κ g : Bool) (A B : DMFormula n)
    (ihA : lo_stepT_aux_Red v A → ∃ m, ALeaf m (fun x => A.eval (upd x v κ)) ∧
      m + occ A v + lo_stepT_aux_kp v κ none A ≤ A.leaves)
    (ihB : lo_stepT_aux_Red v B → ∃ m, ALeaf m (fun x => B.eval (upd x v κ)) ∧
      m + occ B v + lo_stepT_aux_kp v κ none B ≤ B.leaves)
    (hR : lo_stepT_aux_Red v A ∧ lo_stepT_aux_Red v B ∧
      (lo_stepT_aux_isv v A → occ B v = 0) ∧ (lo_stepT_aux_isv v B → occ A v = 0)) :
    ∃ m, ALeaf m (fun x => bop g (A.eval (upd x v κ)) (B.eval (upd x v κ))) ∧
      m + (occ A v + occ B v) +
        (lo_stepT_aux_kp v κ (some g) A + lo_stepT_aux_kp v κ (some g) B) ≤
        A.leaves + B.leaves := by
  obtain ⟨hRA, hRB, hCA, hCB⟩ := hR
  have hA1 := leaves_pos A
  have hB1 := leaves_pos B
  by_cases hvA : lo_stepT_aux_isv v A
  · have hB0 := hCA hvA
    have hkB := lo_stepT_aux_kp_zero v κ (some g) B hB0
    have eB : ∀ x, B.eval (upd x v κ) = B.eval x := fun x => eval_upd_of_zero B v hB0 x κ
    cases A with
    | lit i sg =>
      have hi : i = v := hvA
      have ho : occ (DMFormula.lit i sg) v = 1 := by simp [occ, hi]
      have hL : (DMFormula.lit i sg).leaves = 1 := rfl
      by_cases hk : lo_stepT_aux_kc sg g = κ
      · have hkl : lo_stepT_aux_kp v κ (some g) (DMFormula.lit i sg) = 1 := by
          simp [lo_stepT_aux_kp, hi, hk]
        refine ⟨0, .inl ⟨g, fun x => ?_⟩, by omega⟩
        show bop g ((DMFormula.lit i sg).eval (upd x v κ)) (B.eval (upd x v κ)) = g
        rw [eval_lit, hi, show upd x v κ v = κ by simp [upd], ← hk]
        exact lo_stepT_aux_lit_kill sg g _
      · have hkl : lo_stepT_aux_kp v κ (some g) (DMFormula.lit i sg) = 0 := by
          simp [lo_stepT_aux_kp, hk]
        refine ⟨B.leaves, .inr ⟨B, le_rfl, fun x => ?_⟩, by omega⟩
        show B.eval x = bop g ((DMFormula.lit i sg).eval (upd x v κ)) (B.eval (upd x v κ))
        rw [eval_lit, hi, show upd x v κ v = κ by simp [upd], eB x,
          lo_stepT_aux_lit_pass sg g κ hk]
    | and _ _ => exact absurd hvA id
    | or _ _ => exact absurd hvA id
  · by_cases hvB : lo_stepT_aux_isv v B
    · have hA0 := hCB hvB
      have hkA := lo_stepT_aux_kp_zero v κ (some g) A hA0
      have eA : ∀ x, A.eval (upd x v κ) = A.eval x := fun x => eval_upd_of_zero A v hA0 x κ
      cases B with
      | lit i sg =>
        have hi : i = v := hvB
        have ho : occ (DMFormula.lit i sg) v = 1 := by simp [occ, hi]
        have hL : (DMFormula.lit i sg).leaves = 1 := rfl
        by_cases hk : lo_stepT_aux_kc sg g = κ
        · have hkl : lo_stepT_aux_kp v κ (some g) (DMFormula.lit i sg) = 1 := by
            simp [lo_stepT_aux_kp, hi, hk]
          refine ⟨0, .inl ⟨g, fun x => ?_⟩, by omega⟩
          show bop g (A.eval (upd x v κ)) ((DMFormula.lit i sg).eval (upd x v κ)) = g
          rw [eval_lit, hi, show upd x v κ v = κ by simp [upd], ← hk, bop_comm]
          exact lo_stepT_aux_lit_kill sg g _
        · have hkl : lo_stepT_aux_kp v κ (some g) (DMFormula.lit i sg) = 0 := by
            simp [lo_stepT_aux_kp, hk]
          refine ⟨A.leaves, .inr ⟨A, le_rfl, fun x => ?_⟩, by omega⟩
          show A.eval x = bop g (A.eval (upd x v κ)) ((DMFormula.lit i sg).eval (upd x v κ))
          rw [eval_lit, hi, show upd x v κ v = κ by simp [upd], eA x, bop_comm,
            lo_stepT_aux_lit_pass sg g κ hk]
      | and _ _ => exact absurd hvB id
      | or _ _ => exact absurd hvB id
    · obtain ⟨mA, hmA, hA⟩ := ihA hRA
      obtain ⟨mB, hmB, hB⟩ := ihB hRB
      refine ⟨mA + mB, ALeaf.bop g hmA hmB, ?_⟩
      rw [lo_stepT_aux_kp_some_eq v κ g A hvA, lo_stepT_aux_kp_some_eq v κ g B hvB]
      omega

/-- (DROP) Restriction drop for reduced formulas. -/
theorem lo_stepT_aux_drop (v : Fin n) (κ : Bool) (φ : DMFormula n) (hR : lo_stepT_aux_Red v φ) :
    ∃ m, ALeaf m (fun x => φ.eval (upd x v κ)) ∧
      m + occ φ v + lo_stepT_aux_kp v κ none φ ≤ φ.leaves := by
  induction φ with
  | lit i sg =>
    by_cases hi : i = v
    · refine ⟨0, .inl ⟨litv sg κ, fun x => ?_⟩, ?_⟩
      · simp [eval_lit, upd, hi]
      · simp [occ, hi, lo_stepT_aux_kp, DMFormula.leaves]
    · refine ⟨1, .inr ⟨.lit i sg, by simp [DMFormula.leaves], fun x => ?_⟩, ?_⟩
      · simp [eval_lit, upd, hi]
      · simp [occ, Ne.symm hi, lo_stepT_aux_kp, DMFormula.leaves]
  | and A B ihA ihB =>
    obtain ⟨m, hm, hle⟩ := lo_stepT_aux_drop_gate v κ false A B ihA ihB hR
    exact ⟨m, ALeaf.congr (fun x => rfl) hm, by simp only [occ, lo_stepT_aux_kp, DMFormula.leaves]; omega⟩
  | or A B ihA ihB =>
    obtain ⟨m, hm, hle⟩ := lo_stepT_aux_drop_gate v κ true A B ihA ihB hR
    exact ⟨m, ALeaf.congr (fun x => rfl) hm, by simp only [occ, lo_stepT_aux_kp, DMFormula.leaves]; omega⟩


theorem lo_stepT_aux_EF_true (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) {u v : Fin n}
    (h : G.Adj u v) (x : Fin n → Bool) (hu : x u = true) (hv : x v = true) : EF G A x = true := by
  unfold EF
  simp only [decide_eq_true_eq]
  exact Or.inr ⟨u, v, h, hu, hv⟩

theorem lo_stepT_aux_EF_false (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (p q : Fin n)
    (hpq : ¬ G.Adj p q) (hpA : p ∉ A) (hqA : q ∉ A) (x : Fin n → Bool)
    (hx : ∀ k, x k = true → k = p ∨ k = q) : EF G A x = false := by
  unfold EF
  simp only [decide_eq_false_iff_not]
  rintro (⟨a, ha, hxa⟩ | ⟨u, v, huv, hu, hv⟩)
  · rcases hx a hxa with rfl | rfl
    · exact hpA ha
    · exact hqA ha
  · rcases hx u hu with rfl | rfl <;> rcases hx v hv with rfl | rfl
    · exact G.ne_of_adj huv rfl
    · exact hpq huv
    · exact hpq huv.symm
    · exact G.ne_of_adj huv rfl

/-- Corollary of (TWO_RO) for the T configuration. -/
theorem lo_stepT_aux_no_two_ro (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hA : Iso G A)
    (a b c : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (φ : DMFormula n) (he : ∀ z, φ.eval z = EF G A z) : ¬ (occ φ b ≤ 1 ∧ occ φ c ≤ 1) := by
  rintro ⟨h1, h2⟩
  have hbc' : b ≠ c := G.ne_of_adj hbc
  have hab' : a ≠ b := G.ne_of_adj hab
  have hca' : c ≠ a := G.ne_of_adj hca
  have haA : a ∉ A := gr_not_mem_of_adj hA hab
  have hbA : b ∉ A := gr_not_mem_of_adj hA hbc
  have hcA : c ∉ A := gr_not_mem_of_adj hA hca
  rcases lo_stepT_aux_two_read_once hbc' φ h1 h2 with hor | hand
  · have h11 : φ.eval (lo_stepT_aux_u b c (fun _ => false) true true) = true := by
      rw [he]
      exact lo_stepT_aux_EF_true G A hbc _ (by simp [lo_stepT_aux_u, upd, hbc'])
        (by simp [lo_stepT_aux_u, upd])
    have h10 : φ.eval (lo_stepT_aux_u b c (fun _ => false) true false) = false := by
      rw [he]
      refine lo_stepT_aux_EF_false G A b b (fun hh => G.ne_of_adj hh rfl) hbA hbA _ (fun k hk => ?_)
      simp only [lo_stepT_aux_u, upd] at hk
      by_cases h1 : k = c <;> by_cases h2 : k = b <;> simp_all
    have h01 : φ.eval (lo_stepT_aux_u b c (fun _ => false) false true) = false := by
      rw [he]
      refine lo_stepT_aux_EF_false G A c c (fun hh => G.ne_of_adj hh rfl) hcA hcA _ (fun k hk => ?_)
      simp only [lo_stepT_aux_u, upd] at hk
      by_cases h1 : k = c <;> by_cases h2 : k = b <;> simp_all
    rcases hor _ h11 with h | h
    · rw [h10] at h; exact Bool.false_ne_true h
    · rw [h01] at h; exact Bool.false_ne_true h
  · have h10 : φ.eval (lo_stepT_aux_u b c (upd (fun _ => false) a true) true false) = true := by
      rw [he]
      exact lo_stepT_aux_EF_true G A hab _ (by simp [lo_stepT_aux_u, upd, hab', hca'.symm])
        (by simp [lo_stepT_aux_u, upd, hbc'])
    have h01 : φ.eval (lo_stepT_aux_u b c (upd (fun _ => false) a true) false true) = true := by
      rw [he]
      exact lo_stepT_aux_EF_true G A hca _ (by simp [lo_stepT_aux_u, upd])
        (by simp [lo_stepT_aux_u, upd, hab', hca'.symm])
    have h00 : φ.eval (lo_stepT_aux_u b c (upd (fun _ => false) a true) false false) = false := by
      rw [he]
      refine lo_stepT_aux_EF_false G A a a (fun hh => G.ne_of_adj hh rfl) haA haA _ (fun k hk => ?_)
      simp only [lo_stepT_aux_u, upd] at hk
      by_cases h1 : k = c <;> by_cases h2 : k = b <;> by_cases h3 : k = a <;> simp_all
    have := hand _ h10 h01
    rw [h00] at this
    exact Bool.false_ne_true this

/-- `gr_cov_twin_tri`: deleting a pendant `w` at the apex of a pendant triangle keeps `τ`. -/
theorem lo_stepT_aux_cov_tri {G : SimpleGraph (Fin n)} {k : ℕ} (h : CovLB G k) {a b c w : Fin n}
    (haw : G.Adj a w) (hw : ∀ u, G.Adj w u → u = a) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) (hc : ∀ u, G.Adj c u → u = a ∨ u = b) :
    CovLB (dropV G w) k := by
  intro T hT
  have hwa : w ≠ a := (G.ne_of_adj haw).symm
  have hwb : w ≠ b := by
    rintro rfl
    exact G.ne_of_adj hca (hw c hbc)
  have hwc : w ≠ c := by
    rintro rfl
    exact G.ne_of_adj hab (hw b hbc.symm).symm
  have hcb : c ≠ b := (G.ne_of_adj hbc).symm
  by_cases ha : a ∈ T
  · apply h T
    intro x y hxy
    by_cases hx : x = w
    · subst hx
      right
      rw [hw y hxy]
      exact ha
    · by_cases hy : y = w
      · subst hy
        left
        rw [hw x hxy.symm]
        exact ha
      · exact hT x y ⟨hxy, hx, hy⟩
  · have hbT : b ∈ T := by
      rcases hT a b ⟨hab, hwa.symm, hwb.symm⟩ with h' | h'
      · exact absurd h' ha
      · exact h'
    have hcT : c ∈ T := by
      rcases hT c a ⟨hca, hwc.symm, hwa.symm⟩ with h' | h'
      · exact h'
      · exact absurd h' ha
    have hbT' : b ∈ insert a (T.erase c) :=
      Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hcb.symm, hbT⟩)
    have haT' : a ∈ insert a (T.erase c) := Finset.mem_insert_self a _
    have hc2 := h (insert a (T.erase c)) (by
      intro x y hxy
      by_cases hx : x = w
      · right
        rw [hw y (hx ▸ hxy)]
        exact haT'
      by_cases hxc : x = c
      · right
        rcases hc y (hxc ▸ hxy) with h' | h'
        · rw [h']; exact haT'
        · rw [h']; exact hbT'
      by_cases hy : y = w
      · left
        rw [hw x (hy ▸ hxy.symm)]
        exact haT'
      by_cases hyc : y = c
      · left
        rcases hc x (hyc ▸ hxy.symm) with h' | h'
        · rw [h']; exact haT'
        · rw [h']; exact hbT'
      rcases hT x y ⟨hxy, hx, hy⟩ with h' | h'
      · left
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxc, h'⟩)
      · right
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hyc, h'⟩))
    have h1 := Finset.card_insert_le a (T.erase c)
    have h2 := Finset.card_erase_of_mem hcT
    have h3 := Finset.card_pos.mpr ⟨c, hcT⟩
    omega

/-- Step 1: a pendant `w` at the apex `a`; restrict `w := false`. -/
theorem lo_stepT_aux_pend (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (a b c : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) (hc : ∀ w, G.Adj c w → w = a ∨ w = b) (w : Fin n)
    (haw : G.Adj a w) (hw : ∀ u, G.Adj w u → u = a) : LoClaim G A := by
  intro k s hk hs
  have hwa : G.Adj w a := haw.symm
  have hwA : w ∉ A := gr_not_mem_of_adj hA hwa
  have hdep := lo_EF_dep_edge G A hA hwa
  obtain ⟨φ, hφ, he⟩ := lo_formula_of_nonconst hs _ _ hdep
  have hocc : 1 ≤ occ φ w :=
    lo_occ_pos φ w (upd (fun _ => false) a true) (by rw [he, he]; exact hdep)
  have hr := lo_restrict φ hφ he w false
  have hr' : ALeaf (s - occ φ w) (EF (dropV G w) A) :=
    ALeaf.congr (fun x => lo_EF_upd_false G A w hwA x) hr
  have hE := gr_ncard_dropV G w
  have hd := gr_dg_one hwa hw
  have hc3 := lo_occ_le_leaves φ w
  have := IH (dropV G w) A (gr_good_mono (gr_dropV_le G w) hG) (gr_iso_mono (gr_dropV_le G w) hA)
    (by omega) k (s - occ φ w) (lo_stepT_aux_cov_tri hk haw hw hab hbc hca hc) hr'
  omega

/-- Step 2: `dg a ≤ 3`. Minimum formula; restrict `b` or `c`. -/
theorem lo_stepT_aux_deg3 (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (a b c : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) (hb : ∀ w, G.Adj b w → w = a ∨ w = c)
    (hc : ∀ w, G.Adj c w → w = a ∨ w = b) (hdeg : dg G a ≤ 3) : LoClaim G A := by
  intro k s hk hs
  have hdep := lo_EF_dep_edge G A hA hab.symm
  obtain ⟨φ, hφ, he, hmin⟩ := lo_stepT_aux_min hs _ _ hdep
  have key : ∀ b c : Fin n, G.Adj a b → G.Adj b c → G.Adj c a →
      (∀ w, G.Adj b w → w = a ∨ w = c) → (∀ w, G.Adj c w → w = a ∨ w = b) →
      2 ≤ occ φ b → A.card + G.edgeSet.ncard + k ≤ s := by
    intro b c hab hbc hca hb hc h2
    have hRb := lo_stepT_aux_red_of_min b φ he hmin _ _ hdep
    rcases Nat.lt_or_ge (occ φ b) 3 with h3 | h3
    · have hocc : occ φ b = 2 := by omega
      have hnl : ∀ j sg, φ ≠ .lit j sg := by
        rintro j sg rfl
        simp only [occ] at hocc
        split_ifs at hocc
        omega
      have hpart := lo_stepT_aux_kp_part b φ hnl
      by_cases hk0 : 1 ≤ lo_stepT_aux_kp b false none φ
      · obtain ⟨m, hm, hmle⟩ := lo_stepT_aux_drop b false φ hRb
        exact lo_T_zero G A hG hA IH a b c hab hbc hca hb hc k s hk
          (ALeaf.congr (fun x => he _) (ALeaf.mono (by omega) hm))
      · obtain ⟨m, hm, hmle⟩ := lo_stepT_aux_drop b true φ hRb
        exact lo_T_one G A hG hA IH a b c hab hbc hca hb hc k s hk
          (ALeaf.congr (fun x => he _) (ALeaf.mono (by omega) hm))
    · exact lo_T_zero G A hG hA IH a b c hab hbc hca hb hc k s hk
        (ALeaf.mono (by omega) (lo_restrict φ hφ he b false))
  by_cases hb2 : 2 ≤ occ φ b
  · exact key b c hab hbc hca hb hc hb2
  by_cases hc2 : 2 ≤ occ φ c
  · exact key c b hca.symm hbc.symm hab.symm hc hb hc2
  exact absurd ⟨by omega, by omega⟩ (lo_stepT_aux_no_two_ro G A hA a b c hab hbc hca φ he)

/-- `lo_stepT'`: lo_stepT under the apex hypothesis (Triangle/lo_stepT.chosen.md §3). -/
theorem lo_stepT_aux_main (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (a b c : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) (hb : ∀ w, G.Adj b w → w = a ∨ w = c)
    (hc : ∀ w, G.Adj c w → w = a ∨ w = b)
    (hapex : (∃ q, ∀ w, G.Adj a w → w = b ∨ w = c ∨ w = q) ∨
      (∃ w, G.Adj a w ∧ ∀ u, G.Adj w u → u = a)) : LoClaim G A := by
  rcases hapex with ⟨q, hq⟩ | ⟨w, haw, hw⟩
  · exact lo_stepT_aux_deg3 G A hG hA IH a b c hab hbc hca hb hc (gr_dg_le_three hq)
  · exact lo_stepT_aux_pend G A hG hA IH a b c hab hbc hca hc w haw hw

/-- Tbranch, on-path part: a neighbour of the apex `q` on `P2` is `P2.getVert 1` (a neighbour at
`P2.getVert 2` would close a second triangle at `q`). -/
theorem lo_stepT_aux_Tb_on (G : SimpleGraph (Fin n)) (hC : CycHyp G) (hT : TriHyp G)
    {a p q z : Fin n} (h1 : G.Adj a p) (h2 : G.Adj p q) (P2 : G.Walk q z)
    (hP : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).IsPath)
    (hlq : G.Adj a q) (w : Fin n) (hw : G.Adj q w) (hm : w ∈ P2.support) :
    w = P2.getVert 1 := by
  have hs := hP.support_nodup
  simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons, not_or] at hs
  have hP2 : P2.IsPath :=
    ((SimpleGraph.Walk.cons_isPath_iff _ _).1 ((SimpleGraph.Walk.cons_isPath_iff _ _).1 hP).1).1
  rcases nbr_on_path hC P2 hP2 hw hm with h | h
  · exact h
  · by_cases hlen : 2 ≤ P2.length
    · exfalso
      have hq1 : G.Adj q (P2.getVert 1) := by
        have := P2.adj_getVert_succ (i := 0) (by omega)
        simpa using this
      have h12 : G.Adj (P2.getVert 1) (P2.getVert 2) := P2.adj_getVert_succ (i := 1) (by omega)
      have h2q : G.Adj (P2.getVert 2) q := by rw [← h]; exact hw.symm
      rcases hT q a p (P2.getVert 1) (P2.getVert 2) hlq.symm h1 h2 hq1 h12 h2q with
        ⟨e1, -⟩ | ⟨-, e2⟩
      · exact hs.1.2 (by rw [e1]; exact P2.getVert_mem_support 1)
      · exact hs.2.1 (by rw [e2]; exact P2.getVert_mem_support 1)
    · push Not at hlen
      rw [h, P2.getVert_of_length_le (by omega : P2.length ≤ 2),
        P2.getVert_of_length_le (by omega : P2.length ≤ 1)]

/-- Tbranch, off-path part: an off-path neighbour `w` of the apex `q` is pendant at `q`, or gives
P1 `(z, w, q)` or P2 `(z, w, z')` (chosen.md §4; template `caseB_off`). -/
theorem lo_stepT_aux_Tb_off (G : SimpleGraph (Fin n)) (hC : CycHyp G) (hT : TriHyp G)
    {a p q z : Fin n} (h1 : G.Adj a p) (h2 : G.Adj p q) (P2 : G.Walk q z)
    (hP : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).IsPath)
    (hmax : ∀ (c d : Fin n) (Q : G.Walk c d), Q.IsPath →
      Q.length ≤ (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).length)
    (hlq : G.Adj a q) (w : Fin n) (hqw : G.Adj q w)
    (hwn : w ∉ (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).support) :
    (∀ u, G.Adj w u → u = q) ∨
    (∃ l p q : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ (∀ w, G.Adj p w → w = l ∨ w = q)) ∨
    (∃ l p l' : Fin n, l' ≠ l ∧ G.Adj l p ∧ G.Adj l' p ∧ (∀ w, G.Adj l w → w = p) ∧
        (∀ w, G.Adj l' w → w = p)) := by
  simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hwn
  have hNa : ∀ y, G.Adj a y → y = p ∨ y = q := by
    intro y hy
    have := longest_endpoint_nbrs G hC _ hP hmax y hy
    simpa using this
  have hNp := caseA G hC h1 h2 P2 hP hmax hlq
  have hP2 : P2.IsPath :=
    ((SimpleGraph.Walk.cons_isPath_iff _ _).1 ((SimpleGraph.Walk.cons_isPath_iff _ _).1 hP).1).1
  have hQ : (SimpleGraph.Walk.cons hqw.symm P2).IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff _ _).2 ⟨hP2, hwn.2.2⟩
  have htri : ∀ y, G.Adj w y → G.Adj y q → False := by
    intro y hwy hyq
    rcases hT q a p w y hlq.symm h1 h2 hqw hwy hyq with ⟨e, -⟩ | ⟨-, e⟩
    · exact hwn.1 e.symm
    · exact hwn.2.1 e.symm
  have pend : ∀ y, G.Adj w y → y ≠ q → ∀ x, G.Adj y x → x = w := by
    intro y hwy hyq
    have hyP2 : y ∉ P2.support := by
      intro hm
      have hm' : y ∈ (SimpleGraph.Walk.cons hqw.symm P2).support := by simp [hm]
      rcases nbr_on_path hC _ hQ hwy hm' with h | h
      · simp at h
        exact hyq h
      · simp at h
        by_cases hlen : 1 ≤ P2.length
        · have hq1 : G.Adj q (P2.getVert 1) := by
            have := P2.adj_getVert_succ (i := 0) (by omega)
            simpa using this
          exact htri y hwy (by rw [h]; exact hq1.symm)
        · push Not at hlen
          have h0 : P2.length = 0 := by omega
          have hzq := SimpleGraph.Walk.eq_of_length_eq_zero h0
          rw [P2.getVert_of_length_le (by omega : P2.length ≤ 1), ← hzq] at h
          exact hyq h
    have hR : (SimpleGraph.Walk.cons hwy.symm (SimpleGraph.Walk.cons hqw.symm P2)).IsPath := by
      rw [SimpleGraph.Walk.cons_isPath_iff]
      refine ⟨hQ, ?_⟩
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
      exact ⟨(G.ne_of_adj hwy).symm, hyP2⟩
    have hmaxR : ∀ (c d : Fin n) (Q : G.Walk c d), Q.IsPath →
        Q.length ≤ (SimpleGraph.Walk.cons hwy.symm (SimpleGraph.Walk.cons hqw.symm P2)).length := by
      intro c d Q hQ'
      have := hmax c d Q hQ'
      simpa using this
    intro x hx
    have := longest_endpoint_nbrs G hC _ hR hmaxR x hx
    simp at this
    rcases this with h | h
    · exact h
    · exact (htri y hwy (by rw [h] at hx; exact hx)).elim
  by_cases hall : ∀ u, G.Adj w u → u = q
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨z1, hwz1, hz1q⟩ := hall
    by_cases two : ∃ z2, G.Adj w z2 ∧ z2 ≠ q ∧ z2 ≠ z1
    · obtain ⟨z2, hwz2, hz2q, hz21⟩ := two
      exact Or.inr (Or.inr ⟨z1, w, z2, hz21, hwz1.symm, hwz2.symm, pend z1 hwz1 hz1q,
        pend z2 hwz2 hz2q⟩)
    · push Not at two
      refine Or.inr (Or.inl ⟨z1, w, q, hwz1.symm, pend z1 hwz1 hz1q, fun u hu => ?_⟩)
      by_cases huq : u = q
      · exact Or.inr huq
      · exact Or.inl (two u hu huq)

/-- The only new graph content (Triangle/lo_stepT.chosen.md §4): in `leaf_config`'s T-branch
(longest path `a p q …`, `a ~ q`; apex `q`), either the apex hypothesis holds or P1/P2 occurs.
Proved from `lo_stepT_aux_Tb_on` and `lo_stepT_aux_Tb_off`. -/
theorem lo_stepT_aux_Tbranch (G : SimpleGraph (Fin n)) (hC : CycHyp G) (hT : TriHyp G)
    {a p q z : Fin n} (h1 : G.Adj a p) (h2 : G.Adj p q) (P2 : G.Walk q z)
    (hP : (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).IsPath)
    (hmax : ∀ (c d : Fin n) (Q : G.Walk c d), Q.IsPath →
      Q.length ≤ (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).length)
    (hlq : G.Adj a q) :
    ((∃ x, ∀ w, G.Adj q w → w = a ∨ w = p ∨ w = x) ∨
      (∃ w, G.Adj q w ∧ ∀ u, G.Adj w u → u = q)) ∨
    (∃ l p q : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ (∀ w, G.Adj p w → w = l ∨ w = q)) ∨
    (∃ l p l' : Fin n, l' ≠ l ∧ G.Adj l p ∧ G.Adj l' p ∧ (∀ w, G.Adj l w → w = p) ∧
        (∀ w, G.Adj l' w → w = p)) := by
  have hs := hP.support_nodup
  simp only [SimpleGraph.Walk.support_cons, List.nodup_cons, List.mem_cons, not_or] at hs
  by_cases hoff : ∃ w, G.Adj q w ∧ w ∉ (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).support
  · obtain ⟨w, hqw, hwn⟩ := hoff
    rcases lo_stepT_aux_Tb_off G hC hT h1 h2 P2 hP hmax hlq w hqw hwn with h | h | h
    · exact Or.inl (Or.inr ⟨w, hqw, h⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · push Not at hoff
    refine Or.inl (Or.inl ⟨P2.getVert 1, fun w hw => ?_⟩)
    have hm := hoff w hw
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (lo_stepT_aux_Tb_on G hC hT h1 h2 P2 hP hlq w hw h))

/-- Strengthened `leaf_config` (Triangle/lo_stepT.chosen.md §4, checked on paper there): with
`TriHyp`, the T-disjunct also carries the apex hypothesis. Copy of `leaf_config`'s proof; the
T-branch calls `lo_stepT_aux_Tbranch`. -/
theorem lo_stepT_aux_leaf_config (G : SimpleGraph (Fin n)) (hC : CycHyp G) (hT : TriHyp G)
    (he : ∃ u v : Fin n, G.Adj u v) :
    (∃ a b c : Fin n, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧
        (∀ w, G.Adj b w → w = a ∨ w = c) ∧ (∀ w, G.Adj c w → w = a ∨ w = b) ∧
        ((∃ q, ∀ w, G.Adj a w → w = b ∨ w = c ∨ w = q) ∨
          (∃ w, G.Adj a w ∧ ∀ u, G.Adj w u → u = a))) ∨
    (∃ l p q : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ (∀ w, G.Adj p w → w = l ∨ w = q)) ∨
    (∃ l p l' : Fin n, l' ≠ l ∧ G.Adj l p ∧ G.Adj l' p ∧ (∀ w, G.Adj l w → w = p) ∧
        (∀ w, G.Adj l' w → w = p)) ∨
    (∃ l p q r : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ G.Adj p q ∧ G.Adj q r ∧
        G.Adj r p ∧ (∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r)) := by
  obtain ⟨u, v, huv⟩ := he
  have : Nonempty (Fin n) := ⟨u⟩
  obtain ⟨a, b, P, hP, hmax⟩ := exists_longest_path G
  have h1len := hmax u v (SimpleGraph.Walk.cons huv SimpleGraph.Walk.nil) (by simp [huv.ne])
  have hE := longest_endpoint_nbrs G hC P hP hmax
  cases P with
  | nil => simp at h1len
  | cons h1 P' =>
    rename_i p
    cases P' with
    | nil =>
      have hR : (SimpleGraph.Walk.cons h1.symm SimpleGraph.Walk.nil).IsPath := by simp [h1.ne.symm]
      have hE2 := longest_endpoint_nbrs G hC _ hR (by intro c d Q hQ; simpa using hmax c d Q hQ)
      right; left
      refine ⟨a, b, a, h1, fun w hw => ?_, fun w hw => ?_⟩
      · simpa using hE w hw
      · have := hE2 w hw; simp at this; exact Or.inl this
    | cons h2 P2 =>
      rename_i q
      by_cases hlq : G.Adj a q
      · rcases lo_stepT_aux_Tbranch G hC hT h1 h2 P2 hP hmax hlq with hap | hP1 | hP2
        · left
          refine ⟨q, a, p, hlq.symm, h1, h2, fun w hw => ?_, fun w hw => ?_, hap⟩
          · have := hE w hw; simp at this; tauto
          · exact (caseA G hC h1 h2 P2 hP hmax hlq w hw).symm
        · right; left; exact hP1
        · right; right; left; exact hP2
      · have hNl : ∀ w, G.Adj a w → w = p := by
          intro w hw
          have := hE w hw; simp at this
          rcases this with h | h
          · exact h
          · exact absurd (h ▸ hw) hlq
        by_cases hoff : ∃ w, G.Adj p w ∧ w ∉ (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 P2)).support
        · obtain ⟨w, hpw, hwn⟩ := hoff
          right; right; left
          refine ⟨a, p, w, ?_, h1, hpw.symm, hNl, caseB_off G hC h1 h2 P2 hP hmax hpw hwn⟩
          rintro rfl; exact hwn (SimpleGraph.Walk.start_mem_support _)
        · push Not at hoff
          have hon : ∀ w, G.Adj p w → w = a ∨ w = q ∨ w = P2.getVert 1 := by
            intro w hw
            have hm := hoff w hw
            simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hm
            rcases hm with h | h | h
            · exact Or.inl h
            · exact absurd (h ▸ hw) (G.irrefl)
            · have := nbr_on_path hC (SimpleGraph.Walk.cons h2 P2) hP.tail hw
                (by simp [h])
              simp at this
              tauto
          by_cases hpr : G.Adj p (P2.getVert 1) ∧ G.Adj q (P2.getVert 1)
          · right; right; right
            exact ⟨a, p, q, P2.getVert 1, h1, hNl, h2, hpr.2, hpr.1.symm, hon⟩
          · right; left
            refine ⟨a, p, q, h1, hNl, fun w hw => ?_⟩
            rcases hon w hw with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · subst h
              cases P2 with
              | nil => exact Or.inr (by simp)
              | cons h3 P3 =>
                exact absurd ⟨hw, by simpa using h3⟩ hpr

/-- (TP) bookkeeping, `l := true`: a restriction that drops 3 leaves suffices
(`A` gains `p`; `|E|` drops `dg p ≤ 3`; `τ` drops at most 1). -/
theorem lo_TP_one (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G) (hA : Iso G A)
    (IH : LoIH G A) (l p q r : Fin n) (hlp : G.Adj l p) (hl : ∀ w, G.Adj l w → w = p)
    (hpq : G.Adj p q) (hqr : G.Adj q r) (hrp : G.Adj r p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k s : ℕ) (hk : CovLB G k)
    (hdrop : ALeaf (s - 3) (fun x => EF G A (upd x l true))) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  -- the triangle edges are not needed for the count (`dg G p ≤ 3` comes from `hp`)
  have _ : G.Adj p q ∧ G.Adj q r ∧ G.Adj r p := ⟨hpq, hqr, hrp⟩
  have hlA : l ∉ A := gr_not_mem_of_adj hA hlp
  have hpA : p ∉ A := gr_not_mem_of_adj hA hlp.symm
  have hr' : ALeaf (s - 3) (EF (dropV G p) (insert p A)) :=
    ALeaf.congr (fun x => lo_EF_upd_true_pendant G A l p hlp hl hlA x) hdrop
  have hEp := gr_ncard_dropV G p
  have hdp := gr_dg_le_three hp
  have hdp1 := gr_dg_pos hlp.symm
  have hcard := Finset.card_insert_of_notMem hpA
  have := IH (dropV G p) (insert p A) (gr_good_mono (gr_dropV_le G p) hG)
    (gr_iso_insert G A p hA) (by omega) (k - 1) (s - 3) (gr_cov_dropV hk p) hr'
  omega

/-- (TP) bookkeeping, `l := false`: a restriction that drops 2 leaves suffices
(`|E|` drops 1, `τ` drops at most 1). -/
theorem lo_TP_zero (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G) (hA : Iso G A)
    (IH : LoIH G A) (l p q r : Fin n) (hlp : G.Adj l p) (hl : ∀ w, G.Adj l w → w = p)
    (hpq : G.Adj p q) (hqr : G.Adj q r) (hrp : G.Adj r p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k s : ℕ) (hk : CovLB G k)
    (hdrop : ALeaf (s - 2) (fun x => EF G A (upd x l false))) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  have hlA : l ∉ A := gr_not_mem_of_adj hA hlp
  have hr' : ALeaf (s - 2) (EF (dropV G l) A) :=
    ALeaf.congr (fun x => lo_EF_upd_false G A l hlA x) hdrop
  have hE := gr_ncard_dropV G l
  have hd := gr_dg_one hlp hl
  have hql : q ≠ l := by
    rintro rfl
    have hrp' := hl r hqr
    subst hrp'
    exact G.ne_of_adj hrp rfl
  have hpos : 1 ≤ (dropV G l).edgeSet.ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr
      ⟨s(p, q), (show (dropV G l).Adj p q from ⟨hpq, (G.ne_of_adj hlp).symm, hql⟩)⟩
  have := IH (dropV G l) A (gr_good_mono (gr_dropV_le G l) hG) (gr_iso_mono (gr_dropV_le G l) hA)
    (by omega) (k - 1) (s - 2) (gr_cov_dropV hk l) hr'
  omega

/-- (Round 3) Occurrence-vector form of the `lo_single_occ` shape: the context `C` (above the
parent gate of the single `i`-leaf) has occurrence vector `o`, `α = C[1]`, `β = C[0]`. -/
def lo_stepTP_aux_PA (i : Fin n) (O : Vec n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (sg g : Bool) (ψ : DMFormula n) (o : Vec n) (α β : (Fin n → Bool) → Bool),
      occ ψ i = 0 ∧ (∀ w, o w + occ ψ w + (if w = i then 1 else 0) ≤ O w) ∧ Ach o α ∧
      Ach o β ∧ (∀ x c, α (upd x i c) = α x) ∧ (∀ x c, β (upd x i c) = β x) ∧
      (∀ x, β x = true → α x = true) ∧
      ∀ x, f x = (β x || (α x && bop g (litv sg (x i)) (ψ.eval x)))

theorem lo_stepTP_aux_sab1 (g0 p q r : Bool) (h : p = true → q = true)
    (hp : bop g0 p r = true) : bop g0 q r = true := by
  cases g0 <;> cases p <;> cases q <;> cases r <;> simp_all [bop]

theorem lo_stepTP_aux_sab2 (g0 p q r d : Bool) (h : p = true → q = true) :
    bop g0 (p || (q && d)) r = (bop g0 p r || (bop g0 q r && d)) := by
  cases g0 <;> cases p <;> cases q <;> cases r <;> cases d <;> simp_all [bop]

theorem lo_stepTP_aux_salit (i : Fin n) (g0 s : Bool) (B : DMFormula n) (hB : occ B i = 0)
    {O : Vec n} {f : (Fin n → Bool) → Bool}
    (hL : ∀ w, (if w = i then 1 else 0) + occ B w ≤ O w)
    (hf : ∀ x, f x = bop g0 (litv s (x i)) (B.eval x)) : lo_stepTP_aux_PA i O f :=
  ⟨s, g0, B, fun _ => 0, fun _ => true, fun _ => false, hB,
    fun w => by have h := hL w; show 0 + occ B w + _ ≤ O w; omega,
    Ach.const _ true, Ach.const _ false, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun x => by rw [hf x]; simp⟩

theorem lo_stepTP_aux_sagate (i : Fin n) (g0 : Bool) (B : DMFormula n) (hB : occ B i = 0)
    {OA : Vec n} {fA : (Fin n → Bool) → Bool} (hA : lo_stepTP_aux_PA i OA fA)
    {O : Vec n} {f : (Fin n → Bool) → Bool} (hL : ∀ w, OA w + occ B w ≤ O w)
    (hf : ∀ x, f x = bop g0 (fA x) (B.eval x)) : lo_stepTP_aux_PA i O f := by
  obtain ⟨sg, g, ψ, o, α, β, hψ, hm, hα, hβ, hαi, hβi, hβα, he⟩ := hA
  refine ⟨sg, g, ψ, fun w => o w + occ B w, fun x => bop g0 (α x) (B.eval x),
    fun x => bop g0 (β x) (B.eval x), hψ, fun w => ?_, Ach.bop g0 hα (Ach.form B),
    Ach.bop g0 hβ (Ach.form B),
    fun x c => by simp only [hαi, eval_upd_of_zero B i hB],
    fun x c => by simp only [hβi, eval_upd_of_zero B i hB],
    fun x hx => lo_stepTP_aux_sab1 g0 _ _ _ (hβα x) hx, fun x => ?_⟩
  · have h1 := hm w
    have h2 := hL w
    show o w + occ B w + occ ψ w + _ ≤ O w
    omega
  · rw [hf x, he x]
    exact lo_stepTP_aux_sab2 g0 _ _ _ _ (hβα x)

theorem lo_stepTP_aux_saside (i : Fin n) (g0 : Bool) (A B : DMFormula n) (hA : occ A i = 1)
    (hB : occ B i = 0)
    (iA : (∀ b, A ≠ DMFormula.lit i b) → lo_stepTP_aux_PA i (occ A) A.eval)
    {O : Vec n} {f : (Fin n → Bool) → Bool} (hL : ∀ w, occ A w + occ B w ≤ O w)
    (hf : ∀ x, f x = bop g0 (A.eval x) (B.eval x)) : lo_stepTP_aux_PA i O f := by
  by_cases hl : ∃ s, A = DMFormula.lit i s
  · obtain ⟨s, rfl⟩ := hl
    exact lo_stepTP_aux_salit i g0 s B hB (fun w => hL w) (fun x => by rw [hf x, eval_lit])
  · push Not at hl
    exact lo_stepTP_aux_sagate i g0 B hB (iA hl) hL hf

theorem lo_stepTP_aux_sanode (i : Fin n) (g0 : Bool) (A B : DMFormula n)
    (h1 : occ A i + occ B i = 1)
    (iA : occ A i = 1 → (∀ b, A ≠ DMFormula.lit i b) → lo_stepTP_aux_PA i (occ A) A.eval)
    (iB : occ B i = 1 → (∀ b, B ≠ DMFormula.lit i b) → lo_stepTP_aux_PA i (occ B) B.eval)
    {O : Vec n} {f : (Fin n → Bool) → Bool} (hL : ∀ w, occ A w + occ B w ≤ O w)
    (hf : ∀ x, f x = bop g0 (A.eval x) (B.eval x)) : lo_stepTP_aux_PA i O f := by
  by_cases hA : occ A i = 1
  · exact lo_stepTP_aux_saside i g0 A B hA (by omega) (iA hA) hL hf
  · exact lo_stepTP_aux_saside i g0 B A (by omega) (by omega) (iB (by omega))
      (fun w => by have := hL w; omega) (fun x => by rw [hf x, bop_comm])

theorem lo_stepTP_aux_samain (i : Fin n) (φ : DMFormula n) :
    occ φ i = 1 → (∀ b, φ ≠ DMFormula.lit i b) → lo_stepTP_aux_PA i (occ φ) φ.eval := by
  induction φ with
  | lit j b =>
    intro h1 hlit
    by_cases hj : j = i
    · subst hj; exact absurd rfl (hlit b)
    · simp [occ, Ne.symm hj] at h1
  | and A B iA iB =>
    intro h1 _
    exact lo_stepTP_aux_sanode i false A B h1 iA iB (fun w => le_rfl) (fun x => rfl)
  | or A B iA iB =>
    intro h1 _
    exact lo_stepTP_aux_sanode i true A B h1 iA iB (fun w => le_rfl) (fun x => rfl)

/-- (Round 3, PROVEN) `lo_single_occ` plus the occurrence vector `o` of the context `C`:
`Ach o α`, `Ach o β` and `o + occ ψ + e_i ≤ occ φ`. -/
theorem lo_stepTP_aux_single_ach (φ : DMFormula n) (i : Fin n) (h1 : occ φ i = 1)
    (hlit : ∀ b, φ ≠ DMFormula.lit i b) :
    ∃ (sg g : Bool) (ψ : DMFormula n) (m : ℕ) (α β : (Fin n → Bool) → Bool) (o : Vec n),
      occ ψ i = 0 ∧ m + ψ.leaves + 1 ≤ φ.leaves ∧ ALeaf m α ∧ ALeaf m β ∧
      (∀ x c, α (upd x i c) = α x) ∧ (∀ x c, β (upd x i c) = β x) ∧
      (∀ x, β x = true → α x = true) ∧
      (∀ x, φ.eval x = (β x || (α x && bop g (litv sg (x i)) (ψ.eval x)))) ∧
      Ach o α ∧ Ach o β ∧ (∀ w, o w + occ ψ w + (if w = i then 1 else 0) ≤ occ φ w) := by
  obtain ⟨sg, g, ψ, o, α, β, hψ, hle, hα, hβ, hαi, hβi, hβα, he⟩ :=
    lo_stepTP_aux_samain i φ h1 hlit
  refine ⟨sg, g, ψ, ∑ k, o k, α, β, o, hψ, ?_, ALeaf.of_ach hα, ALeaf.of_ach hβ, hαi, hβi, hβα,
    he, hα, hβ, hle⟩
  have hS := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hle w)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hS
  rw [← leaves_eq, ← leaves_eq] at hS
  omega

/-- If the gate of the single `l`-leaf absorbs (literal value `= g`), the decomposition
`β ∨ (α ∧ (lit ∘_g ψ))` collapses to `α` (OR gate) or `β` (AND gate), so it has `ALeaf m`. -/
theorem lo_stepTP_aux_abs (α β : (Fin n → Bool) → Bool) (m : ℕ) (hα : ALeaf m α)
    (hβ : ALeaf m β) (hβα : ∀ x, β x = true → α x = true) (g : Bool)
    (ψv : (Fin n → Bool) → Bool) :
    ALeaf m (fun x => (β x || (α x && bop g g (ψv x)))) := by
  cases g
  · exact ALeaf.congr (fun x => by simp [bop]) hβ
  · refine ALeaf.congr (fun x => ?_) hα
    have := hβα x
    cases hb : β x <;> cases ha : α x <;> simp_all [bop]

/-- A one-leaf formula is a literal (tool for `lo_stepTP_aux_badT`). -/
theorem lo_stepTP_aux_lit (ψ : DMFormula n) (h : ψ.leaves = 1) :
    ∃ j t, ψ = DMFormula.lit j t := by
  cases ψ with
  | lit j t => exact ⟨j, t, rfl⟩
  | and a b =>
    have := leaves_pos a
    have := leaves_pos b
    simp only [DMFormula.leaves] at h
    omega
  | or a b =>
    have := leaves_pos a
    have := leaves_pos b
    simp only [DMFormula.leaves] at h
    omega

/-- Where `x_l` matters (`EF` false at `l := false`, true at `l := true`), the sibling `ψ` of the
`l`-leaf is false (tool for `lo_stepTP_aux_badT`; `g = sg = true`). -/
theorem lo_stepTP_aux_psi (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l : Fin n)
    (ψ : DMFormula n) (α β : (Fin n → Bool) → Bool)
    (hres : ∀ x c, EF G A (upd x l c) = (β x || (α x && bop true (litv true c) (ψ.eval x))))
    (x : Fin n → Bool) (h0 : EF G A (upd x l false) = false)
    (h1 : EF G A (upd x l true) = true) : ψ.eval x = false := by
  have e0 := hres x false
  have e1 := hres x true
  rw [h0] at e0
  rw [h1] at e1
  revert e0 e1
  cases ψ.eval x <;> cases α x <;> cases β x <;> simp [litv, bop]

/-- `EF G ∅` at `{p, j}` (+ `l`), when `j ∉ N[p] ∪ {l}`: false without `l`, true with `l`. -/
theorem lo_stepTP_aux_far (G : SimpleGraph (Fin n)) (l p j : Fin n) (hlp : G.Adj l p)
    (hjl : j ≠ l) (hjp : j ≠ p) (hpj : ¬ G.Adj p j) :
    EF G ∅ (upd (upd (upd (fun _ => false) p true) j true) l false) = false ∧
    EF G ∅ (upd (upd (upd (fun _ => false) p true) j true) l true) = true := by
  have hpl : p ≠ l := (G.ne_of_adj hlp).symm
  have key : ∀ w, upd (upd (upd (fun _ => false) p true) j true) l false w = true →
      w = p ∨ w = j := by
    intro w hw
    simp only [upd] at hw
    split_ifs at hw <;> simp_all
  constructor
  · unfold EF
    rw [decide_eq_false_iff_not]
    rintro (⟨a, ha, _⟩ | ⟨u, v, huv, hu, hv⟩)
    · simp at ha
    · rcases key u hu with h1 | h1 <;> rcases key v hv with h2 | h2 <;> subst h1 <;> subst h2 <;>
        first
          | exact G.loopless.irrefl _ huv
          | exact hpj huv
          | exact hpj huv.symm
  · unfold EF
    simp only [decide_eq_true_eq]
    exact Or.inr ⟨l, p, hlp, by simp [upd], by simp [upd, hpl]⟩

/-- Classification of the sibling literal (fact 2 of the notes): `ψ = ¬x_p`, or `ψ = x_q`, or
`ψ = x_r`. Tool for `lo_stepTP_aux_badT`. -/
theorem lo_stepTP_aux_cls (G : SimpleGraph (Fin n)) (l p q r : Fin n) (hlp : G.Adj l p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (ψ : DMFormula n)
    (α β : (Fin n → Bool) → Bool)
    (hres : ∀ x c, EF G ∅ (upd x l c) = (β x || (α x && bop true (litv true c) (ψ.eval x))))
    (hψ0 : occ ψ l = 0) (j : Fin n) (t : Bool) (hψlit : ψ = DMFormula.lit j t)
    (hx0 : ψ.eval (upd (fun _ => false) p true) = false) :
    (j = p ∧ t = false) ∨ (t = true ∧ (j = q ∨ j = r)) := by
  subst hψlit
  have hjl : j ≠ l := by
    intro h
    subst h
    simp [occ] at hψ0
  by_cases hjp : j = p
  · subst hjp
    left
    refine ⟨rfl, ?_⟩
    rw [eval_lit] at hx0
    cases t <;> simp_all [litv, upd]
  · right
    have ht : t = true := by
      rw [eval_lit] at hx0
      cases t <;> simp_all [litv, upd]
    refine ⟨ht, ?_⟩
    by_contra hqr
    push Not at hqr
    have hpj : ¬ G.Adj p j := by
      intro h
      rcases hp j h with h' | h' | h'
      · exact hjl h'
      · exact hqr.1 h'
      · exact hqr.2 h'
    obtain ⟨e0, e1⟩ := lo_stepTP_aux_far G l p j hlp hjl hjp hpj
    have := lo_stepTP_aux_psi G ∅ l _ α β hres _ e0 e1
    rw [eval_lit, ht] at this
    simp [litv, upd] at this

/-- An isolated vertex outside `A` is irrelevant to `EF`. -/
theorem lo_stepTP_aux_isoupd (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n)
    (hv : v ∉ A) (hiso : ∀ w, ¬ G.Adj v w) (x : Fin n → Bool) (c : Bool) :
    EF G A (upd x v c) = EF G A x := by
  unfold EF
  rw [decide_eq_decide]
  have hne : ∀ w, G.Adj w v → False := fun w h => hiso w h.symm
  constructor
  · rintro (⟨a, ha, hx⟩ | ⟨u, w, huw, hu, hw⟩)
    · have hav : a ≠ v := fun h => hv (by rw [← h]; exact ha)
      exact Or.inl ⟨a, ha, by simpa [upd, hav] using hx⟩
    · have huv : u ≠ v := fun h => hiso w (by rw [← h]; exact huw)
      have hwv : w ≠ v := fun h => hne u (by rw [← h]; exact huw)
      exact Or.inr ⟨u, w, huw, by simpa [upd, huv] using hu, by simpa [upd, hwv] using hw⟩
  · rintro (⟨a, ha, hx⟩ | ⟨u, w, huw, hu, hw⟩)
    · have hav : a ≠ v := fun h => hv (by rw [← h]; exact ha)
      exact Or.inl ⟨a, ha, by simpa [upd, hav] using hx⟩
    · have huv : u ≠ v := fun h => hiso w (by rw [← h]; exact huw)
      have hwv : w ≠ v := fun h => hne u (by rw [← h]; exact huw)
      exact Or.inr ⟨u, w, huw, by simpa [upd, huv] using hu, by simpa [upd, hwv] using hw⟩

/-- (TP) `p := false` together with `l := false` turns `EF G A` into `EF (dropV G p) A`
(`|E|` drops by `dg p ≤ 3`, `τ` by at most 1), so `occ φ l + occ φ p ≥ 4` suffices.
Valid for every TP configuration (no bad-case assumption). -/
theorem lo_stepTP_aux_p0 (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (l p q r : Fin n) (hlp : G.Adj l p)
    (hl : ∀ w, G.Adj l w → w = p) (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k s : ℕ)
    (hk : CovLB G k) (φ : DMFormula n) (hφ : φ.leaves ≤ s) (he : ∀ z, φ.eval z = EF G A z)
    (h4 : 4 ≤ occ φ l + occ φ p) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  have hlA : l ∉ A := gr_not_mem_of_adj hA hlp
  have hpA : p ∉ A := gr_not_mem_of_adj hA hlp.symm
  have hlp' : l ≠ p := G.ne_of_adj hlp
  have hiso : ∀ w, ¬ (dropV G p).Adj l w := by
    rintro w ⟨h1, _, h3⟩
    exact h3 (hl w h1)
  have a2 := ((Ach.form φ).restrict l false).restrict p false
  have hsum := ALeaf.of_ach a2
  have e1 := sum_zv (zv (occ φ) l) p
  have e2 := sum_zv (occ φ) l
  have e3 : zv (occ φ) l p = occ φ p := by simp [zv, hlp'.symm]
  rw [← leaves_eq] at e2
  have hr : ALeaf (s - (occ φ l + occ φ p)) (EF (dropV G p) A) := by
    refine ALeaf.congr (fun x => ?_) (ALeaf.mono (by omega) hsum)
    show φ.eval (upd (upd x p false) l false) = EF (dropV G p) A x
    have hcomm : upd (upd x p false) l false = upd (upd x l false) p false := by
      funext w
      unfold upd
      by_cases hw1 : w = l <;> by_cases hw2 : w = p <;> simp [hw1, hw2]
    rw [hcomm, he, lo_EF_upd_false G A p hpA, lo_stepTP_aux_isoupd (dropV G p) A l hlA hiso]
  have hE := gr_ncard_dropV G p
  have hd3 := gr_dg_le_three hp
  have hd1 := gr_dg_pos hlp.symm
  have hLL := lo_two_occ_le_leaves φ hlp'
  have := IH (dropV G p) A (gr_good_mono (gr_dropV_le G p) hG)
    (gr_iso_mono (gr_dropV_le G p) hA) (by omega) (k - 1) (s - (occ φ l + occ φ p))
    (gr_cov_dropV hk p) hr
  omega

/-- (TP, bad case, paper fact 1) `α = C[1]` computes `EF` at `l := true`, i.e.
`x_p ∨ EF (G - p) A` = `EF (dropV G p) (insert p A)`. -/
theorem lo_stepTP_aux_alpha (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hA : Iso G A)
    (l p : Fin n) (hlp : G.Adj l p) (hl : ∀ w, G.Adj l w → w = p)
    (φ : DMFormula n) (he : ∀ z, φ.eval z = EF G A z) (ψ : DMFormula n)
    (α β : (Fin n → Bool) → Bool)
    (hαl : ∀ x c, α (upd x l c) = α x) (hβl : ∀ x c, β (upd x l c) = β x)
    (hβα : ∀ x, β x = true → α x = true)
    (hdec : ∀ x, φ.eval x = (β x || (α x && bop true (litv true (x l)) (ψ.eval x))))
    (x : Fin n → Bool) : α x = EF (dropV G p) (insert p A) x := by
  have hlA : l ∉ A := gr_not_mem_of_adj hA hlp
  rw [← lo_EF_upd_true_pendant G A l p hlp hl hlA x, ← he, hdec, hαl, hβl]
  have hu : upd x l true l = true := by simp [upd]
  rw [hu]
  cases hb : β x
  · simp [bop, litv]
  · simp [bop, litv, hβα x hb]

/-- (TP, bad case, `ψ = x_q`, paper fact 1) `C[0] ∨ (C[1] ∧ x_q)` computes `EF` at `l := false`,
i.e. `EF (dropV G l) A`. -/
theorem lo_stepTP_aux_betaq (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hA : Iso G A)
    (l p q : Fin n) (hlp : G.Adj l p) (hql : q ≠ l)
    (φ : DMFormula n) (he : ∀ z, φ.eval z = EF G A z)
    (α β : (Fin n → Bool) → Bool)
    (hαl : ∀ x c, α (upd x l c) = α x) (hβl : ∀ x c, β (upd x l c) = β x)
    (hdec : ∀ x, φ.eval x =
      (β x || (α x && bop true (litv true (x l)) ((DMFormula.lit q true : DMFormula n).eval x))))
    (x : Fin n → Bool) : (β x || (α x && x q)) = EF (dropV G l) A x := by
  have hlA : l ∉ A := gr_not_mem_of_adj hA hlp
  rw [← lo_EF_upd_false G A l hlA x, ← he, hdec, hαl, hβl, eval_lit]
  simp [upd, hql, bop, litv]

/-- (TP, bad case, `ψ = ¬x_p`, paper fact 1) `C[0] ∨ (C[1] ∧ ¬x_p)` computes `EF` at
`l := false`, i.e. `EF (dropV G l) A`. -/
theorem lo_stepTP_aux_betanp (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hA : Iso G A)
    (l p : Fin n) (hlp : G.Adj l p)
    (φ : DMFormula n) (he : ∀ z, φ.eval z = EF G A z)
    (α β : (Fin n → Bool) → Bool)
    (hαl : ∀ x c, α (upd x l c) = α x) (hβl : ∀ x c, β (upd x l c) = β x)
    (hdec : ∀ x, φ.eval x =
      (β x || (α x && bop true (litv true (x l)) ((DMFormula.lit p false : DMFormula n).eval x))))
    (x : Fin n → Bool) : (β x || (α x && !x p)) = EF (dropV G l) A x := by
  have hlA : l ∉ A := gr_not_mem_of_adj hA hlp
  have hpl : p ≠ l := (G.ne_of_adj hlp).symm
  rw [← lo_EF_upd_false G A l hlA x, ← he, hdec, hαl, hβl, eval_lit]
  simp [upd, hpl, bop, litv]

/-- (TP, `ψ = x_q`, PROVEN tool for `lo_stepTP_aux_posq`) Given an occurrence vector `o` of the
context (`Ach o α`, `o + e_q + e_l ≤ occ φ`, as an occurrence-vector `lo_single_occ` would give),
`l := 1` (giving `α`) then `p := 0` shows that `2 ≤ occ φ p` suffices. -/
theorem lo_stepTP_aux_posq_two (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (l p q r : Fin n) (hlp : G.Adj l p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (hpq : p ≠ q) (k s : ℕ) (hk : CovLB G k)
    (φ : DMFormula n) (hφ : φ.leaves ≤ s) (α : (Fin n → Bool) → Bool)
    (hαe : ∀ x, α x = EF (dropV G p) (insert p A) x) (o : Vec n) (ho : Ach o α)
    (hle : ∀ w, o w + (if w = q then 1 else 0) + (if w = l then 1 else 0) ≤ occ φ w)
    (h2 : 2 ≤ occ φ p) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  have hpA : p ∉ A := gr_not_mem_of_adj hA hlp.symm
  have hlp' : l ≠ p := G.ne_of_adj hlp
  have a := ho.restrict p false
  have hsum := ALeaf.of_ach a
  have hpt : ∀ w, zv o p w + (if w = p then occ φ w else 0) + (if w = q then 1 else 0)
      + (if w = l then 1 else 0) ≤ occ φ w := by
    intro w
    by_cases hw : w = p
    · subst hw
      simp [zv, hpq, hlp'.symm]
    · have := hle w
      simp only [zv, hw, ↓reduceIte]
      omega
  have hS := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hpt w)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hS
  rw [← leaves_eq] at hS
  have hr : ALeaf (s - occ φ p - 2) (EF (dropV G p) A) := by
    refine ALeaf.congr (fun x => ?_) (ALeaf.mono (by omega) hsum)
    show α (upd x p false) = EF (dropV G p) A x
    rw [hαe, lo_EF_upd_A (dropV G p) (insert p A) p (Finset.mem_insert_self p A)
      (gr_iso_insert G A p hA), Finset.erase_insert hpA]
  have hE := gr_ncard_dropV G p
  have hd3 := gr_dg_le_three hp
  have hd1 := gr_dg_pos hlp.symm
  have := IH (dropV G p) A (gr_good_mono (gr_dropV_le G p) hG)
    (gr_iso_mono (gr_dropV_le G p) hA) (by omega) (k - 1) (s - occ φ p - 2)
    (gr_cov_dropV hk p) hr
  omega

/-- (TP, Round 3, PROVEN tool for `lo_stepTP_aux_posq_one` / `lo_stepTP_aux_negp`) Let `χ` be a
formula for `α = C[1] = x_p ∨ EF (G - p) A` with `χ.leaves + 2 ≤ s`, decomposed at its single
`p`-leaf (`lo_stepTP_aux_single_ach χ p`). If that leaf's gate ABSORBS at `p := false`, then
`EF (G - p) A` has `≤ s - 4` leaves and the IH (`μ` drops by 4) finishes. -/
theorem lo_stepTP_aux_posq_abs (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (l p q r : Fin n) (hlp : G.Adj l p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k s : ℕ) (hk : CovLB G k)
    (α : (Fin n → Bool) → Bool) (hαe : ∀ x, α x = EF (dropV G p) (insert p A) x)
    (χ : DMFormula n) (hχ : ∀ x, χ.eval x = α x) (hχs : χ.leaves + 2 ≤ s)
    (sg3 g3 : Bool) (ψ3 : DMFormula n) (m3 : ℕ) (α3 β3 : (Fin n → Bool) → Bool)
    (hm3 : m3 + ψ3.leaves + 1 ≤ χ.leaves) (hα3 : ALeaf m3 α3) (hβ3 : ALeaf m3 β3)
    (hα3p : ∀ x c, α3 (upd x p c) = α3 x) (hβ3p : ∀ x c, β3 (upd x p c) = β3 x)
    (hβα3 : ∀ x, β3 x = true → α3 x = true)
    (hdec3 : ∀ x, χ.eval x = (β3 x || (α3 x && bop g3 (litv sg3 (x p)) (ψ3.eval x))))
    (habs : litv sg3 false = g3) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  have hpA : p ∉ A := gr_not_mem_of_adj hA hlp.symm
  have hψ3 := leaves_pos ψ3
  have hab := lo_stepTP_aux_abs α3 β3 m3 hα3 hβ3 hβα3 g3 (fun x => ψ3.eval (upd x p false))
  have hr : ALeaf (s - 4) (EF (dropV G p) A) := by
    refine ALeaf.congr (fun x => ?_) (ALeaf.mono (by omega) hab)
    show (β3 x || (α3 x && bop g3 g3 (ψ3.eval (upd x p false)))) = EF (dropV G p) A x
    have h1 : EF (dropV G p) A x = α (upd x p false) := by
      rw [hαe, lo_EF_upd_A (dropV G p) (insert p A) p (Finset.mem_insert_self p A)
        (gr_iso_insert G A p hA), Finset.erase_insert hpA]
    have hu : upd x p false p = false := by simp [upd]
    rw [h1, ← hχ, hdec3, hα3p, hβ3p, hu, habs]
  have hE := gr_ncard_dropV G p
  have hd3 := gr_dg_le_three hp
  have hd1 := gr_dg_pos hlp.symm
  have := IH (dropV G p) A (gr_good_mono (gr_dropV_le G p) hG)
    (gr_iso_mono (gr_dropV_le G p) hA) (by omega) (k - 1) (s - 4)
    (gr_cov_dropV hk p) hr
  omega

/-- (TP, Round 3, PROVEN tool for the `_or` cases) In a formula `χ` for `α = x_p ∨ EF (G - p) A`
decomposed at its single `p`-leaf, a NON-absorbing gate is an OR with positive `x_p`, and then
`α3 ≡ true` (so `χ` computes `β3 ∨ x_p ∨ ψ3`). -/
theorem lo_stepTP_aux_or_pos (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (p : Fin n)
    (α : (Fin n → Bool) → Bool) (hαe : ∀ x, α x = EF (dropV G p) (insert p A) x)
    (χ : DMFormula n) (hχ : ∀ x, χ.eval x = α x)
    (sg3 g3 : Bool) (ψ3 : DMFormula n) (α3 β3 : (Fin n → Bool) → Bool)
    (hα3p : ∀ x c, α3 (upd x p c) = α3 x) (hβ3p : ∀ x c, β3 (upd x p c) = β3 x)
    (hβα3 : ∀ x, β3 x = true → α3 x = true)
    (hdec3 : ∀ x, χ.eval x = (β3 x || (α3 x && bop g3 (litv sg3 (x p)) (ψ3.eval x))))
    (habs : litv sg3 false ≠ g3) :
    g3 = true ∧ sg3 = true ∧ ∀ x, α3 x = true := by
  have htop : ∀ x, α (upd x p true) = true := by
    intro x
    rw [hαe]
    unfold EF
    simp only [decide_eq_true_eq]
    exact Or.inl ⟨p, Finset.mem_insert_self p A, by simp [upd]⟩
  have hu : ∀ x, upd x p true p = true := fun x => by simp [upd]
  cases sg3 <;> cases g3
  · exfalso
    have hβ : ∀ x, β3 x = true := by
      intro x
      have h := htop x
      rw [← hχ, hdec3, hα3p, hβ3p, hu] at h
      simpa [litv, bop] using h
    have h0 := lo_EF_const_false (dropV G p) (insert p A)
    rw [← hαe, ← hχ, hdec3, hβ] at h0
    simp at h0
  · exact absurd rfl habs
  · exact absurd rfl habs
  · refine ⟨rfl, rfl, fun x => ?_⟩
    have h := htop x
    rw [← hχ, hdec3, hα3p, hβ3p, hu] at h
    cases hb : β3 x
    · simpa [hb, litv, bop] using h
    · exact hβα3 x hb

/-- (TP, Round 3, PROVEN tool) In shape (c) (`g3 = sg3 = true`, `α3 ≡ true`):
`EF (G - p) A = β3 ∨ ψ3`, where `β3` and `ψ3` come from the decomposition of `χ` at `p`. -/
theorem lo_stepTP_aux_or_E (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hA : Iso G A)
    (l p : Fin n) (hlp : G.Adj l p)
    (α : (Fin n → Bool) → Bool) (hαe : ∀ x, α x = EF (dropV G p) (insert p A) x)
    (χ : DMFormula n) (hχ : ∀ x, χ.eval x = α x) (ψ3 : DMFormula n) (hψ30 : occ ψ3 p = 0)
    (α3 β3 : (Fin n → Bool) → Bool)
    (hα3p : ∀ x c, α3 (upd x p c) = α3 x) (hβ3p : ∀ x c, β3 (upd x p c) = β3 x)
    (hdec3 : ∀ x, χ.eval x = (β3 x || (α3 x && bop true (litv true (x p)) (ψ3.eval x))))
    (hα3t : ∀ x, α3 x = true) (x : Fin n → Bool) :
    EF (dropV G p) A x = (β3 x || ψ3.eval x) := by
  have hpA : p ∉ A := gr_not_mem_of_adj hA hlp.symm
  have h1 : EF (dropV G p) A x = α (upd x p false) := by
    rw [hαe, lo_EF_upd_A (dropV G p) (insert p A) p (Finset.mem_insert_self p A)
      (gr_iso_insert G A p hA), Finset.erase_insert hpA]
  have hu : upd x p false p = false := by simp [upd]
  rw [h1, ← hχ, hdec3, hα3p, hβ3p, hu, eval_upd_of_zero ψ3 p hψ30, hα3t]
  simp [litv, bop]

/-! ### Fable block: syntactic context formula `Φ = C[x_i]`, LCA split, and the Q3 bound.
See `Fable/notes.md`. Proves `lo_stepTP_aux_negp_or` and `lo_stepTP_aux_posq_or`. -/

/-- `lo_stepTP_aux_PA` plus the SYNTACTIC formula `Φ = C[x_i]` (the gate `lit_i ∘_g ψ` replaced
by the single positive leaf `x_i`). -/
def fable_PA (i : Fin n) (O : Vec n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (sg g : Bool) (ψ : DMFormula n) (o : Vec n) (α β : (Fin n → Bool) → Bool),
      occ ψ i = 0 ∧ (∀ w, o w + occ ψ w + (if w = i then 1 else 0) ≤ O w) ∧ Ach o α ∧
      Ach o β ∧ (∀ x c, α (upd x i c) = α x) ∧ (∀ x c, β (upd x i c) = β x) ∧
      (∀ x, β x = true → α x = true) ∧
      (∀ x, f x = (β x || (α x && bop g (litv sg (x i)) (ψ.eval x)))) ∧
      ∃ Φ : DMFormula n, occ Φ i = 1 ∧ (∀ w, occ Φ w + occ ψ w ≤ O w) ∧
        ∀ x, f x = Φ.eval (upd x i (bop g (litv sg (x i)) (ψ.eval x)))

theorem fable_salit (i : Fin n) (g0 s : Bool) (B : DMFormula n) (hB : occ B i = 0)
    {O : Vec n} {f : (Fin n → Bool) → Bool}
    (hL : ∀ w, (if w = i then 1 else 0) + occ B w ≤ O w)
    (hf : ∀ x, f x = bop g0 (litv s (x i)) (B.eval x)) : fable_PA i O f :=
  ⟨s, g0, B, fun _ => 0, fun _ => true, fun _ => false, hB,
    fun w => by have h := hL w; show 0 + occ B w + _ ≤ O w; omega,
    Ach.const _ true, Ach.const _ false, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun x => by rw [hf x]; simp,
    DMFormula.lit i true, by simp [occ], fun w => by have h := hL w; simp only [occ]; exact h,
    fun x => by rw [hf x, eval_lit]; simp [litv, upd]⟩

theorem fable_sagate (i : Fin n) (g0 : Bool) (B : DMFormula n) (hB : occ B i = 0)
    {OA : Vec n} {fA : (Fin n → Bool) → Bool} (hA : fable_PA i OA fA)
    {O : Vec n} {f : (Fin n → Bool) → Bool} (hL : ∀ w, OA w + occ B w ≤ O w)
    (hf : ∀ x, f x = bop g0 (fA x) (B.eval x)) : fable_PA i O f := by
  obtain ⟨sg, g, ψ, o, α, β, hψ, hm, hα, hβ, hαi, hβi, hβα, he, Φ, hΦi, hΦo, hΦe⟩ := hA
  refine ⟨sg, g, ψ, fun w => o w + occ B w, fun x => bop g0 (α x) (B.eval x),
    fun x => bop g0 (β x) (B.eval x), hψ, fun w => ?_, Ach.bop g0 hα (Ach.form B),
    Ach.bop g0 hβ (Ach.form B),
    fun x c => by simp only [hαi, eval_upd_of_zero B i hB],
    fun x c => by simp only [hβi, eval_upd_of_zero B i hB],
    fun x hx => lo_stepTP_aux_sab1 g0 _ _ _ (hβα x) hx, fun x => ?_,
    mk g0 Φ B, ?_, fun w => ?_, fun x => ?_⟩
  · have h1 := hm w
    have h2 := hL w
    show o w + occ B w + occ ψ w + _ ≤ O w
    omega
  · rw [hf x, he x]
    exact lo_stepTP_aux_sab2 g0 _ _ _ _ (hβα x)
  · rw [occ_mk, hΦi, hB]
  · have h1 := hΦo w
    have h2 := hL w
    rw [occ_mk]
    omega
  · rw [hf x, hΦe x, eval_mk, eval_upd_of_zero B i hB]

theorem fable_saside (i : Fin n) (g0 : Bool) (A B : DMFormula n) (hA : occ A i = 1)
    (hB : occ B i = 0)
    (iA : (∀ b, A ≠ DMFormula.lit i b) → fable_PA i (occ A) A.eval)
    {O : Vec n} {f : (Fin n → Bool) → Bool} (hL : ∀ w, occ A w + occ B w ≤ O w)
    (hf : ∀ x, f x = bop g0 (A.eval x) (B.eval x)) : fable_PA i O f := by
  by_cases hl : ∃ s, A = DMFormula.lit i s
  · obtain ⟨s, rfl⟩ := hl
    exact fable_salit i g0 s B hB (fun w => hL w) (fun x => by rw [hf x, eval_lit])
  · push Not at hl
    exact fable_sagate i g0 B hB (iA hl) hL hf

theorem fable_sanode (i : Fin n) (g0 : Bool) (A B : DMFormula n)
    (h1 : occ A i + occ B i = 1)
    (iA : occ A i = 1 → (∀ b, A ≠ DMFormula.lit i b) → fable_PA i (occ A) A.eval)
    (iB : occ B i = 1 → (∀ b, B ≠ DMFormula.lit i b) → fable_PA i (occ B) B.eval)
    {O : Vec n} {f : (Fin n → Bool) → Bool} (hL : ∀ w, occ A w + occ B w ≤ O w)
    (hf : ∀ x, f x = bop g0 (A.eval x) (B.eval x)) : fable_PA i O f := by
  by_cases hA : occ A i = 1
  · exact fable_saside i g0 A B hA (by omega) (iA hA) hL hf
  · exact fable_saside i g0 B A (by omega) (by omega) (iB (by omega))
      (fun w => by have := hL w; omega) (fun x => by rw [hf x, bop_comm])

theorem fable_samain (i : Fin n) (φ : DMFormula n) :
    occ φ i = 1 → (∀ b, φ ≠ DMFormula.lit i b) → fable_PA i (occ φ) φ.eval := by
  induction φ with
  | lit j b =>
    intro h1 hlit
    by_cases hj : j = i
    · subst hj; exact absurd rfl (hlit b)
    · simp [occ, Ne.symm hj] at h1
  | and A B iA iB =>
    intro h1 _
    exact fable_sanode i false A B h1 iA iB (fun w => le_rfl) (fun x => rfl)
  | or A B iA iB =>
    intro h1 _
    exact fable_sanode i true A B h1 iA iB (fun w => le_rfl) (fun x => rfl)

/-- `lo_stepTP_aux_single_ach` plus the syntactic `Φ = C[x_i]`:
`φ.eval x = Φ.eval (upd x i (lit_i ∘_g ψ))`, `occ Φ i = 1`, `occ Φ + occ ψ ≤ occ φ`. -/
theorem fable_single_ach (φ : DMFormula n) (i : Fin n) (h1 : occ φ i = 1)
    (hlit : ∀ b, φ ≠ DMFormula.lit i b) :
    ∃ (sg g : Bool) (ψ : DMFormula n) (m : ℕ) (α β : (Fin n → Bool) → Bool) (o : Vec n),
      occ ψ i = 0 ∧ m + ψ.leaves + 1 ≤ φ.leaves ∧ ALeaf m α ∧ ALeaf m β ∧
      (∀ x c, α (upd x i c) = α x) ∧ (∀ x c, β (upd x i c) = β x) ∧
      (∀ x, β x = true → α x = true) ∧
      (∀ x, φ.eval x = (β x || (α x && bop g (litv sg (x i)) (ψ.eval x)))) ∧
      Ach o α ∧ Ach o β ∧ (∀ w, o w + occ ψ w + (if w = i then 1 else 0) ≤ occ φ w) ∧
      ∃ Φ : DMFormula n, occ Φ i = 1 ∧ (∀ w, occ Φ w + occ ψ w ≤ occ φ w) ∧
        ∀ x, φ.eval x = Φ.eval (upd x i (bop g (litv sg (x i)) (ψ.eval x))) := by
  obtain ⟨sg, g, ψ, o, α, β, hψ, hle, hα, hβ, hαi, hβi, hβα, he, hΦ⟩ :=
    fable_samain i φ h1 hlit
  refine ⟨sg, g, ψ, ∑ k, o k, α, β, o, hψ, ?_, ALeaf.of_ach hα, ALeaf.of_ach hβ, hαi, hβi, hβα,
    he, hα, hβ, hle, hΦ⟩
  have hS := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hle w)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hS
  rw [← leaves_eq, ← leaves_eq] at hS
  omega

theorem fable_leaves_mk (g : Bool) (a b : DMFormula n) :
    (mk g a b).leaves = a.leaves + b.leaves := by
  cases g <;> rfl

theorem fable_bop_ctx (g0 d0 d1 nv cv : Bool) :
    bop g0 (d0 || (d1 && nv)) cv = (bop g0 d0 cv || (bop g0 d1 cv && nv)) := by
  cases g0 <;> cases d0 <;> cases d1 <;> cases nv <;> cases cv <;> rfl

theorem fable_bop_ctx' (g0 d0 d1 nv cv : Bool) :
    bop g0 cv (d0 || (d1 && nv)) = (bop g0 cv d0 || (bop g0 cv d1 && nv)) := by
  cases g0 <;> cases d0 <;> cases d1 <;> cases nv <;> cases cv <;> rfl

/-- LCA split of the single `l`-leaf and the single `p`-leaf (as in `TP/LcaSplit.lean`):
`φ = D[A op B]`, `D[y] = δ0 ∨ (δ1 ∧ y)` free of `l, p`, `Ψ = D[B]`, `L(Ψ) + L(A) ≤ L(φ)`. -/
def fable_LCA (l p : Fin n) (φ : DMFormula n) : Prop :=
  ∃ (g : Bool) (A B Ψ : DMFormula n) (δ0 δ1 : (Fin n → Bool) → Bool),
    occ A p = 0 ∧ occ B l = 0 ∧ occ A l = 1 ∧ occ B p = 1 ∧
    (∀ x c, δ0 (upd x l c) = δ0 x) ∧ (∀ x c, δ0 (upd x p c) = δ0 x) ∧
    (∀ x c, δ1 (upd x l c) = δ1 x) ∧ (∀ x c, δ1 (upd x p c) = δ1 x) ∧
    (∀ x, φ.eval x = (δ0 x || (δ1 x && bop g (A.eval x) (B.eval x)))) ∧
    (∀ x, Ψ.eval x = (δ0 x || (δ1 x && B.eval x))) ∧
    Ψ.leaves + A.leaves ≤ φ.leaves

theorem fable_lca_node (l p : Fin n) (g0 : Bool) (φ1 φ2 : DMFormula n)
    (IH1 : occ φ1 l = 1 → occ φ1 p = 1 → fable_LCA l p φ1)
    (IH2 : occ φ2 l = 1 → occ φ2 p = 1 → fable_LCA l p φ2)
    (h1 : occ (mk g0 φ1 φ2) l = 1) (h2 : occ (mk g0 φ1 φ2) p = 1) :
    fable_LCA l p (mk g0 φ1 φ2) := by
  rw [occ_mk] at h1 h2
  rcases Nat.lt_or_ge (occ φ1 l) 1 with hl1 | hl1 <;>
    rcases Nat.lt_or_ge (occ φ1 p) 1 with hp1 | hp1
  · have hl1' : occ φ1 l = 0 := by omega
    have hp1' : occ φ1 p = 0 := by omega
    obtain ⟨g, A, B, Ψ, δ0, δ1, hAp, hBl, hAl, hBp, h0l, h0p, h1l, h1p, hev, hΨ, hle⟩ :=
      IH2 (by omega) (by omega)
    refine ⟨g, A, B, mk g0 φ1 Ψ, fun x => bop g0 (φ1.eval x) (δ0 x),
      fun x => bop g0 (φ1.eval x) (δ1 x), hAp, hBl, hAl, hBp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x c; simp only [eval_upd_of_zero φ1 l hl1', h0l]
    · intro x c; simp only [eval_upd_of_zero φ1 p hp1', h0p]
    · intro x c; simp only [eval_upd_of_zero φ1 l hl1', h1l]
    · intro x c; simp only [eval_upd_of_zero φ1 p hp1', h1p]
    · intro x; rw [eval_mk, hev, fable_bop_ctx']
    · intro x; rw [eval_mk, hΨ, fable_bop_ctx']
    · rw [fable_leaves_mk, fable_leaves_mk]; omega
  · refine ⟨g0, φ2, φ1, φ1, fun _ => false, fun _ => true, by omega, by omega, by omega,
      by omega, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro x; rw [eval_mk, bop_comm]; simp
    · intro x; simp
    · exact (fable_leaves_mk g0 φ1 φ2).ge
  · refine ⟨g0, φ1, φ2, φ2, fun _ => false, fun _ => true, by omega, by omega, by omega,
      by omega, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro x; rw [eval_mk]; simp
    · intro x; simp
    · rw [fable_leaves_mk]; omega
  · have hl2 : occ φ2 l = 0 := by omega
    have hp2 : occ φ2 p = 0 := by omega
    obtain ⟨g, A, B, Ψ, δ0, δ1, hAp, hBl, hAl, hBp, h0l, h0p, h1l, h1p, hev, hΨ, hle⟩ :=
      IH1 (by omega) (by omega)
    refine ⟨g, A, B, mk g0 Ψ φ2, fun x => bop g0 (δ0 x) (φ2.eval x),
      fun x => bop g0 (δ1 x) (φ2.eval x), hAp, hBl, hAl, hBp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x c; simp only [eval_upd_of_zero φ2 l hl2, h0l]
    · intro x c; simp only [eval_upd_of_zero φ2 p hp2, h0p]
    · intro x c; simp only [eval_upd_of_zero φ2 l hl2, h1l]
    · intro x c; simp only [eval_upd_of_zero φ2 p hp2, h1p]
    · intro x; rw [eval_mk, hev, fable_bop_ctx]
    · intro x; rw [eval_mk, hΨ, fable_bop_ctx]
    · rw [fable_leaves_mk, fable_leaves_mk]; omega

theorem fable_lca (l p : Fin n) (hlp : l ≠ p) :
    ∀ φ : DMFormula n, occ φ l = 1 → occ φ p = 1 → fable_LCA l p φ := by
  intro φ
  induction φ with
  | lit i b =>
    intro h1 h2
    simp only [occ] at h1 h2
    split_ifs at h1 h2 with ha hb
    · exact absurd (ha.trans hb.symm) hlp
  | and a b iha ihb =>
    intro h1 h2
    exact fable_lca_node l p false a b iha ihb h1 h2
  | or a b iha ihb =>
    intro h1 h2
    exact fable_lca_node l p true a b iha ihb h1 h2

theorem fable_b2 : ∀ (d0 d1 a0 a1 b0 b1 : Bool), (d0 || d1 && bop true a1 b0) = false →
    (d0 || d1 && bop true a0 b1) = false → (d0 || d1 && bop true a1 b1) = true → False := by
  decide

theorem fable_b3 : ∀ (d0 d1 a1 b0 b1 e : Bool), (d0 || d1 && bop false a1 b0) = e →
    (d0 || d1 && bop false a1 b1) = true → (d0 || d1 && b0) = e := by
  decide

theorem fable_b3t : ∀ (d0 d1 a1 b1 : Bool), (d0 || d1 && bop false a1 b1) = true →
    (d0 || d1 && b1) = true := by
  decide

theorem fable_b5 : ∀ (d0 d1 a0 a1 b0 b1 v : Bool), (d0 || d1 && bop false a1 b0) = false →
    (d0 || d1 && bop false a1 b1) = true → (d0 || d1 && bop false a0 b1) = v → a0 = v := by
  decide

def fable_z : Fin n → Bool := fun _ => false

theorem fable_z_apply (k : Fin n) : (fable_z : Fin n → Bool) k = false := rfl

theorem fable_EF_one (G : SimpleGraph (Fin n)) (x : Fin n → Bool)
    (h : ∀ u v, x u = true → x v = true → u = v) : EF G ∅ x = false := by
  unfold EF
  rw [decide_eq_false_iff_not]
  rintro (⟨a, ha, _⟩ | ⟨u, v, huv, hu, hv⟩)
  · simp at ha
  · exact G.ne_of_adj huv (h u v hu hv)

theorem fable_EF_edge (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool)
    (u v : Fin n) (huv : G.Adj u v) (hu : x u = true) (hv : x v = true) : EF G A x = true := by
  unfold EF
  simp only [decide_eq_true_eq]
  exact Or.inr ⟨u, v, huv, hu, hv⟩

theorem fable_EF_ins (G : SimpleGraph (Fin n)) (p : Fin n) (x : Fin n → Bool) :
    EF G (insert p ∅) x = (x p || EF G ∅ x) := by
  unfold EF
  cases hx : x p
  · rw [Bool.false_or, decide_eq_decide]
    simp [hx]
  · rw [Bool.true_or]
    simp only [decide_eq_true_eq]
    exact Or.inl ⟨p, by simp, hx⟩

theorem fable_upd_comm (x : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    upd (upd x i a) j b = upd (upd x j b) i a := by
  funext k
  simp only [upd]
  by_cases h1 : k = i
  · subst h1
    simp [hij]
  · simp [h1]

theorem fable_upd_self (x : Fin n → Bool) (i : Fin n) (c : Bool) (h : x i = c) :
    upd x i c = x := by
  funext k
  simp only [upd]
  by_cases hk : k = i
  · subst hk
    simp [h]
  · simp [hk]

/-- (Q3 bound) TP configuration, `A = ∅`. Any formula `Φ` with one `l`-leaf and at most one
`p`-leaf that agrees with `EF G ∅` whenever `x_l = 1` or `x_p = 1` has `|E| + k ≤ L(Φ)`.
Proof: LCA split `Φ = D[A ∧ B]`; `D[B]` computes `x_p ∨ EF (G - p)` (IH: `≥ μ - 3` leaves) and
the deleted subtree `A` depends on `l, q, r` (`≥ 3` leaves). -/
theorem fable_q3 (G : SimpleGraph (Fin n)) (hG : Good G) (IH : LoIH G ∅)
    (l p q r : Fin n) (hlp : G.Adj l p) (hl : ∀ w, G.Adj l w → w = p)
    (hpq : G.Adj p q) (hqr : G.Adj q r) (hrp : G.Adj r p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k : ℕ) (hk : CovLB G k)
    (Φ : DMFormula n) (hΦl : occ Φ l = 1) (hΦp : occ Φ p ≤ 1)
    (hQ : ∀ x, x l = true ∨ x p = true → Φ.eval x = EF G ∅ x) :
    G.edgeSet.ncard + k ≤ Φ.leaves := by
  have hlp' : l ≠ p := G.ne_of_adj hlp
  have hA : Iso G (∅ : Finset (Fin n)) := fun a ha => absurd ha (Finset.notMem_empty a)
  have hpA : p ∉ (∅ : Finset (Fin n)) := Finset.notMem_empty p
  have hlq : l ≠ q := by
    rintro rfl
    have := hl r hqr
    exact G.ne_of_adj hrp this
  have hlr : l ≠ r := by
    rintro rfl
    have := hl q hqr.symm
    exact G.ne_of_adj hpq this.symm
  have h11 : ∀ x, Φ.eval (upd (upd x l true) p true) = true := by
    intro x
    rw [hQ _ (Or.inr (by simp [upd]))]
    exact fable_EF_edge G ∅ _ l p hlp (by simp [upd, hlp']) (by simp [upd])
  have hliso : ∀ w, ¬ (dropV G p).Adj l w := fun w hw => hw.2.2 (hl w hw.1)
  have h10 : ∀ x, Φ.eval (upd (upd x l true) p false) = EF (dropV G p) ∅ x := by
    intro x
    rw [hQ _ (Or.inl (by simp [upd, hlp'])), lo_EF_upd_false G ∅ p hpA,
      lo_stepTP_aux_isoupd (dropV G p) ∅ l (Finset.notMem_empty l) hliso]
  have hE1 : ∀ v, EF (dropV G p) ∅ (upd fable_z v true) = false := by
    intro v
    apply fable_EF_one
    intro a b ha hb
    have ha' : a = v := by
      by_contra h
      simp [upd, h, fable_z_apply] at ha
    have hb' : b = v := by
      by_contra h
      simp [upd, h, fable_z_apply] at hb
    rw [ha', hb']
  have hE0 : EF (dropV G p) ∅ fable_z = false := by
    apply fable_EF_one
    intro a b ha
    simp [fable_z_apply] at ha
  have h01z : Φ.eval (upd (upd fable_z l false) p true) = false := by
    rw [hQ _ (Or.inr (by simp [upd]))]
    apply fable_EF_one
    intro a b ha hb
    have ha' : a = p := by
      by_contra h
      simp [upd, h, fable_z_apply] at ha
    have hb' : b = p := by
      by_contra h
      simp [upd, h, fable_z_apply] at hb
    rw [ha', hb']
  have h01v : ∀ v, G.Adj p v → v ≠ l →
      Φ.eval (upd (upd (upd fable_z v true) l false) p true) = true := by
    intro v hpv hvl
    have hvp : v ≠ p := (G.ne_of_adj hpv).symm
    rw [hQ _ (Or.inr (by simp [upd]))]
    exact fable_EF_edge G ∅ _ p v hpv (by simp [upd]) (by simp [upd, hvp, hvl])
  have hΦp1 : occ Φ p = 1 := by
    by_contra hne
    have h0 : occ Φ p = 0 := by omega
    have e1 := h11 fable_z
    have e2 := h10 fable_z
    rw [eval_upd_of_zero Φ p h0] at e1 e2
    rw [e1, hE0] at e2
    exact Bool.noConfusion e2
  obtain ⟨g, A, B, Ψ, δ0, δ1, hAp, hBl, hAl, hBp, h0l, h0p, h1l, h1p, hev, hΨ, hle⟩ :=
    fable_lca l p hlp' Φ hΦl hΦp1
  have hquad : ∀ x i j, Φ.eval (upd (upd x l i) p j) =
      (δ0 x || (δ1 x && bop g (A.eval (upd x l i)) (B.eval (upd x p j)))) := by
    intro x i j
    rw [hev, h0p, h0l, h1p, h1l, eval_upd_of_zero A p hAp, fable_upd_comm x l p hlp' i j,
      eval_upd_of_zero B l hBl]
  have hg : g = false := by
    cases g
    · rfl
    · exfalso
      have e10 := h10 fable_z
      have e01 := h01z
      have e11 := h11 fable_z
      rw [hquad] at e10 e01 e11
      rw [hE0] at e10
      exact fable_b2 _ _ _ _ _ _ e10 e01 e11
  subst hg
  have hΨe : ∀ x, Ψ.eval x = EF (dropV G p) (insert p ∅) x := by
    intro x
    rw [hΨ, fable_EF_ins]
    by_cases hx : x p = true
    · have e11 := h11 x
      rw [hquad, fable_upd_self x p true hx] at e11
      rw [hx, Bool.true_or]
      exact fable_b3t _ _ _ _ e11
    · have hx' : x p = false := by simpa using hx
      have e11 := h11 x
      have e10 := h10 x
      rw [hquad] at e11 e10
      rw [fable_upd_self x p false hx'] at e10
      rw [hx', Bool.false_or]
      exact fable_b3 _ _ _ _ _ _ e10 e11
  have hE := gr_ncard_dropV G p
  have hd3 := gr_dg_le_three hp
  have hd1 := gr_dg_pos hlp.symm
  have hcard : (insert p (∅ : Finset (Fin n))).card = 1 := by simp
  have hIH := IH (dropV G p) (insert p ∅) (gr_good_mono (gr_dropV_le G p) hG)
    (gr_iso_insert G ∅ p hA) (by rw [hcard, Finset.card_empty]; omega) (k - 1) Ψ.leaves
    (gr_cov_dropV hk p) (.inr ⟨Ψ, le_rfl, hΨe⟩)
  rw [hcard] at hIH
  have hkey : ∀ v, G.Adj p v → v ≠ l → 1 ≤ occ A v := by
    intro v hpv hvl
    have a0z : A.eval (upd fable_z l false) = false := by
      have e10 := h10 fable_z
      have e11 := h11 fable_z
      have e01 := h01z
      rw [hquad] at e10 e11 e01
      rw [hE0] at e10
      exact fable_b5 _ _ _ _ _ _ _ e10 e11 e01
    have a0v : A.eval (upd (upd fable_z v true) l false) = true := by
      have e10 := h10 (upd fable_z v true)
      have e11 := h11 (upd fable_z v true)
      have e01 := h01v v hpv hvl
      rw [hquad] at e10 e11 e01
      rw [hE1] at e10
      exact fable_b5 _ _ _ _ _ _ _ e10 e11 e01
    by_contra hne
    have h0 : occ A v = 0 := by omega
    rw [fable_upd_comm fable_z v l hvl true false, eval_upd_of_zero A v h0] at a0v
    rw [a0z] at a0v
    exact Bool.noConfusion a0v
  have hAq := hkey q hpq hlq.symm
  have hAr := hkey r hrp.symm hlr.symm
  have hqr' : q ≠ r := G.ne_of_adj hqr
  have h3 : 3 ≤ A.leaves := by
    rw [leaves_eq]
    have hsub : ∑ w ∈ ({l, q, r} : Finset (Fin n)), occ A w ≤ ∑ w, occ A w :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [Finset.sum_insert (by simp [hlq, hlr]), Finset.sum_insert (by simp [hqr']),
      Finset.sum_singleton] at hsub
    omega
  omega

/-- (TP, Round 3) THE OPEN CORE for `ψ = ¬x_p`: as `lo_stepTP_aux_posq_or` (same shape (c)),
with `occ φ p ≤ 2`: the `p`-leaf of the context is the single `p`-leaf of `χ` (a formula for `α`,
`occ χ ≤ o`), and its gate does NOT absorb at `p := false`. -/
theorem lo_stepTP_aux_negp_or (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (hA0 : A = ∅) (l p q r : Fin n) (hlp : G.Adj l p)
    (hl : ∀ w, G.Adj l w → w = p) (hpq : G.Adj p q) (hqr : G.Adj q r) (hrp : G.Adj r p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k s : ℕ) (hk : CovLB G k)
    (φ : DMFormula n) (hφ : φ.leaves ≤ s) (he : ∀ z, φ.eval z = EF G A z)
    (hocc1 : occ φ l = 1) (hocc2 : occ φ p ≤ 2) (ψ : DMFormula n) (m : ℕ)
    (α β : (Fin n → Bool) → Bool) (hψ0 : occ ψ l = 0)
    (hm : m + 2 ≤ φ.leaves) (hα : ALeaf m α) (hβ : ALeaf m β)
    (hαl : ∀ x c, α (upd x l c) = α x) (hβl : ∀ x c, β (upd x l c) = β x)
    (hβα : ∀ x, β x = true → α x = true)
    (hdec : ∀ x, φ.eval x = (β x || (α x && bop true (litv true (x l)) (ψ.eval x))))
    (hT : ∃ T : Finset (Fin n), (∀ u v, (dropV G l).Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card < k)
    (hψlit : ψ = DMFormula.lit p false)
    (heq : A.card + G.edgeSet.ncard + k = s + 1)
    (o : Vec n) (hoβ : Ach o β)
    (hole : ∀ w, o w + occ ψ w + (if w = l then 1 else 0) ≤ occ φ w)
    (χ : DMFormula n) (hχ : ∀ x, χ.eval x = α x) (hχo : ∀ w, occ χ w ≤ o w)
    (sg3 g3 : Bool) (ψ3 : DMFormula n) (m3 : ℕ) (α3 β3 : (Fin n → Bool) → Bool) (o3 : Vec n)
    (hψ30 : occ ψ3 p = 0) (hm3 : m3 + ψ3.leaves + 1 ≤ χ.leaves) (hα3 : ALeaf m3 α3)
    (hβ3 : ALeaf m3 β3) (hα3p : ∀ x c, α3 (upd x p c) = α3 x)
    (hβ3p : ∀ x c, β3 (upd x p c) = β3 x) (hβα3 : ∀ x, β3 x = true → α3 x = true)
    (hdec3 : ∀ x, χ.eval x = (β3 x || (α3 x && bop g3 (litv sg3 (x p)) (ψ3.eval x))))
    (hoα3 : Ach o3 α3) (hoβ3 : Ach o3 β3)
    (hole3 : ∀ w, o3 w + occ ψ3 w + (if w = p then 1 else 0) ≤ occ χ w)
    (habs : litv sg3 false ≠ g3)
    (hΦ : ∃ Φ : DMFormula n, occ Φ l = 1 ∧ (∀ w, occ Φ w + occ ψ w ≤ occ φ w) ∧
      ∀ x, φ.eval x = Φ.eval (upd x l (bop true (litv true (x l)) (ψ.eval x)))) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  subst hA0
  subst hψlit
  obtain ⟨Φ, hΦl, hΦo, hΦe⟩ := hΦ
  have hΦp : occ Φ p ≤ 1 := by
    have h1 := hΦo p
    have h2 : occ (DMFormula.lit p false : DMFormula n) p = 1 := by simp [occ]
    omega
  have hQ : ∀ x, x l = true ∨ x p = true → Φ.eval x = EF G ∅ x := by
    intro x hx
    rw [← he, hΦe x]
    congr 1
    symm
    apply fable_upd_self
    rw [eval_lit]
    rcases hx with h | h <;> simp [bop, litv, h]
  have hb := fable_q3 G hG IH l p q r hlp hl hpq hqr hrp hp k hk Φ hΦl hΦp hQ
  have hL : Φ.leaves + 1 ≤ φ.leaves := by
    have hS := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hΦo w)
    simp only [Finset.sum_add_distrib] at hS
    rw [← leaves_eq, ← leaves_eq, ← leaves_eq] at hS
    have h1 : (DMFormula.lit p false : DMFormula n).leaves = 1 := rfl
    omega
  rw [Finset.card_empty]
  omega

/-- (TP) OPEN CORE, case `ψ = ¬x_p` (the sibling of the single `l`-leaf is `¬x_p`), after the
bad-case split (`hT`) and after `lo_stepTP_aux_p0` (so `occ φ p ≤ 2`; on paper
`occ φ p = 2`: the leaf `¬x_p` plus one positive `x_p` in the context, under an OR gate).
See `Triangle/lo_stepTP.inv.md` §3 (case (a)): open sub-case (ii-b). -/
theorem lo_stepTP_aux_negp (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (hA0 : A = ∅) (l p q r : Fin n) (hlp : G.Adj l p)
    (hl : ∀ w, G.Adj l w → w = p) (hpq : G.Adj p q) (hqr : G.Adj q r) (hrp : G.Adj r p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k s : ℕ) (hk : CovLB G k)
    (φ : DMFormula n) (hφ : φ.leaves ≤ s) (he : ∀ z, φ.eval z = EF G A z)
    (hocc1 : occ φ l = 1) (hocc2 : occ φ p ≤ 2) (ψ : DMFormula n) (m : ℕ)
    (α β : (Fin n → Bool) → Bool) (hψ0 : occ ψ l = 0)
    (hm : m + 2 ≤ φ.leaves) (hα : ALeaf m α) (hβ : ALeaf m β)
    (hαl : ∀ x c, α (upd x l c) = α x) (hβl : ∀ x c, β (upd x l c) = β x)
    (hβα : ∀ x, β x = true → α x = true)
    (hdec : ∀ x, φ.eval x = (β x || (α x && bop true (litv true (x l)) (ψ.eval x))))
    (hT : ∃ T : Finset (Fin n), (∀ u v, (dropV G l).Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card < k)
    (hψlit : ψ = DMFormula.lit p false)
    (heq : A.card + G.edgeSet.ncard + k = s + 1)
    (o : Vec n) (hoα : Ach o α) (hoβ : Ach o β)
    (hole : ∀ w, o w + occ ψ w + (if w = l then 1 else 0) ≤ occ φ w)
    (hΦ : ∃ Φ : DMFormula n, occ Φ l = 1 ∧ (∀ w, occ Φ w + occ ψ w ≤ occ φ w) ∧
      ∀ x, φ.eval x = Φ.eval (upd x l (bop true (litv true (x l)) (ψ.eval x)))) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  subst hψlit
  have hpq' : p ≠ q := G.ne_of_adj hpq
  have hpl : p ≠ l := (G.ne_of_adj hlp).symm
  have hαe : ∀ x, α x = EF (dropV G p) (insert p A) x := fun x =>
    lo_stepTP_aux_alpha G A hA l p hlp hl φ he _ α β hαl hβl hβα hdec x
  have hdepp := lo_EF_dep_A (dropV G p) (insert p A) (Finset.mem_insert_self p A)
  have hsum : ∑ w, o w + 2 ≤ φ.leaves := by
    have hS := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hole w)
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hS
    rw [← leaves_eq, ← leaves_eq] at hS
    have h1 : (DMFormula.lit p false : DMFormula n).leaves = 1 := rfl
    omega
  rcases hoα with ⟨c, hc⟩ | ⟨χ, hχ, hχo⟩
  · exfalso
    apply hdepp
    rw [← hαe, ← hαe, hc, hc]
  have hχs : χ.leaves + 2 ≤ s := by
    have : χ.leaves ≤ ∑ w, o w := by
      rw [leaves_eq]; exact Finset.sum_le_sum fun w _ => hχo w
    omega
  have hχp : occ χ p = 1 := by
    have h1 : 1 ≤ occ χ p :=
      lo_occ_pos χ p (fun _ => false) (by rw [hχ, hχ, hαe, hαe]; exact hdepp)
    have h2 := hχo p
    have h3 := hole p
    simp [occ, hpl] at h3
    omega
  have hχlit : ∀ b, χ ≠ DMFormula.lit p b := by
    rintro b rfl
    have hqr' : (dropV G p).Adj q r := ⟨hqr, hpq'.symm, G.ne_of_adj hrp⟩
    have hdq := lo_EF_dep_edge (dropV G p) (insert p A) (gr_iso_insert G A p hA) hqr'
    rw [← hαe, ← hαe, ← hχ, ← hχ] at hdq
    apply hdq
    simp [eval_lit, upd, hpq']
  obtain ⟨sg3, g3, ψ3, m3, α3, β3, o3, hψ30, hm3, hα3, hβ3, hα3p, hβ3p, hβα3, hdec3, hoα3, hoβ3,
    hole3⟩ := lo_stepTP_aux_single_ach χ p hχp hχlit
  by_cases habs : litv sg3 false = g3
  · exact lo_stepTP_aux_posq_abs G A hG hA IH l p q r hlp hp k s hk α hαe χ hχ hχs sg3 g3 ψ3 m3
      α3 β3 hm3 hα3 hβ3 hα3p hβ3p hβα3 hdec3 habs
  · exact lo_stepTP_aux_negp_or G A hG hA IH hA0 l p q r hlp hl hpq hqr hrp hp k s hk φ hφ he
      hocc1 hocc2 _ m α β hψ0 hm hα hβ hαl hβl hβα hdec hT rfl heq o hoβ hole χ hχ hχo sg3 g3 ψ3
      m3 α3 β3 o3 hψ30 hm3 hα3 hβ3 hα3p hβ3p hβα3 hdec3 hoα3 hoβ3 hole3 habs hΦ

/-- (TP, Round 3) THE OPEN CORE for `ψ = x_q`: `occ φ p = 1`, `χ` a formula for `α` with
`occ χ ≤ o`, decomposed at its single `p`-leaf, and that leaf's gate does NOT absorb at
`p := false` (on paper: positive `x_p` under an OR gate, so `α3 ≡ 1` and
`EF (G - p) A = β3 ∨ ψ3`; every single restriction is one leaf short). Shape (c) of
`Work/lo_stepTP.notes.md` Round 3 = Key Lemma K of `Triangle/lo_stepTP.dec.md`. -/
theorem lo_stepTP_aux_posq_or (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (hA0 : A = ∅) (l p q r : Fin n) (hlp : G.Adj l p)
    (hl : ∀ w, G.Adj l w → w = p) (hpq : G.Adj p q) (hqr : G.Adj q r) (hrp : G.Adj r p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k s : ℕ) (hk : CovLB G k)
    (φ : DMFormula n) (hφ : φ.leaves ≤ s) (he : ∀ z, φ.eval z = EF G A z)
    (hocc1 : occ φ l = 1) (hp1 : occ φ p = 1) (ψ : DMFormula n) (m : ℕ)
    (α β : (Fin n → Bool) → Bool) (hψ0 : occ ψ l = 0)
    (hm : m + 2 ≤ φ.leaves) (hα : ALeaf m α) (hβ : ALeaf m β)
    (hαl : ∀ x c, α (upd x l c) = α x) (hβl : ∀ x c, β (upd x l c) = β x)
    (hβα : ∀ x, β x = true → α x = true)
    (hdec : ∀ x, φ.eval x = (β x || (α x && bop true (litv true (x l)) (ψ.eval x))))
    (hT : ∃ T : Finset (Fin n), (∀ u v, (dropV G l).Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card < k)
    (hψlit : ψ = DMFormula.lit q true)
    (heq : A.card + G.edgeSet.ncard + k = s + 1)
    (o : Vec n) (hoβ : Ach o β)
    (hole : ∀ w, o w + occ ψ w + (if w = l then 1 else 0) ≤ occ φ w)
    (χ : DMFormula n) (hχ : ∀ x, χ.eval x = α x) (hχo : ∀ w, occ χ w ≤ o w)
    (sg3 g3 : Bool) (ψ3 : DMFormula n) (m3 : ℕ) (α3 β3 : (Fin n → Bool) → Bool) (o3 : Vec n)
    (hψ30 : occ ψ3 p = 0) (hm3 : m3 + ψ3.leaves + 1 ≤ χ.leaves) (hα3 : ALeaf m3 α3)
    (hβ3 : ALeaf m3 β3) (hα3p : ∀ x c, α3 (upd x p c) = α3 x)
    (hβ3p : ∀ x c, β3 (upd x p c) = β3 x) (hβα3 : ∀ x, β3 x = true → α3 x = true)
    (hdec3 : ∀ x, χ.eval x = (β3 x || (α3 x && bop g3 (litv sg3 (x p)) (ψ3.eval x))))
    (hoα3 : Ach o3 α3) (hoβ3 : Ach o3 β3)
    (hole3 : ∀ w, o3 w + occ ψ3 w + (if w = p then 1 else 0) ≤ occ χ w)
    (habs : litv sg3 false ≠ g3) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  subst hA0
  have hb := fable_q3 G hG IH l p q r hlp hl hpq hqr hrp hp k hk φ hocc1 (le_of_eq hp1)
    (fun x _ => he x)
  rw [Finset.card_empty]
  omega

/-- (TP, Round 3) Case `ψ = x_q` with `occ φ p = 1` (the case `occ φ p = 2` is
`lo_stepTP_aux_posq_two`). The single `p`-leaf lies in the context `C` (`o p = 1`); on paper it is
a positive `x_p` under an OR gate: Key Lemma K of `Triangle/lo_stepTP.dec.md`. -/
theorem lo_stepTP_aux_posq_one (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (hA0 : A = ∅) (l p q r : Fin n) (hlp : G.Adj l p)
    (hl : ∀ w, G.Adj l w → w = p) (hpq : G.Adj p q) (hqr : G.Adj q r) (hrp : G.Adj r p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k s : ℕ) (hk : CovLB G k)
    (φ : DMFormula n) (hφ : φ.leaves ≤ s) (he : ∀ z, φ.eval z = EF G A z)
    (hocc1 : occ φ l = 1) (hp1 : occ φ p = 1) (ψ : DMFormula n) (m : ℕ)
    (α β : (Fin n → Bool) → Bool) (hψ0 : occ ψ l = 0)
    (hm : m + 2 ≤ φ.leaves) (hα : ALeaf m α) (hβ : ALeaf m β)
    (hαl : ∀ x c, α (upd x l c) = α x) (hβl : ∀ x c, β (upd x l c) = β x)
    (hβα : ∀ x, β x = true → α x = true)
    (hdec : ∀ x, φ.eval x = (β x || (α x && bop true (litv true (x l)) (ψ.eval x))))
    (hT : ∃ T : Finset (Fin n), (∀ u v, (dropV G l).Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card < k)
    (hψlit : ψ = DMFormula.lit q true)
    (heq : A.card + G.edgeSet.ncard + k = s + 1)
    (o : Vec n) (hoα : Ach o α) (hoβ : Ach o β)
    (hole : ∀ w, o w + occ ψ w + (if w = l then 1 else 0) ≤ occ φ w) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  subst hψlit
  have hpq' : p ≠ q := G.ne_of_adj hpq
  have hpl : p ≠ l := (G.ne_of_adj hlp).symm
  have hαe : ∀ x, α x = EF (dropV G p) (insert p A) x := fun x =>
    lo_stepTP_aux_alpha G A hA l p hlp hl φ he _ α β hαl hβl hβα hdec x
  have hdepp := lo_EF_dep_A (dropV G p) (insert p A) (Finset.mem_insert_self p A)
  have hsum : ∑ w, o w + 2 ≤ φ.leaves := by
    have hS := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hole w)
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hS
    rw [← leaves_eq, ← leaves_eq] at hS
    have h1 : (DMFormula.lit q true : DMFormula n).leaves = 1 := rfl
    omega
  rcases hoα with ⟨c, hc⟩ | ⟨χ, hχ, hχo⟩
  · exfalso
    apply hdepp
    rw [← hαe, ← hαe, hc, hc]
  have hχs : χ.leaves + 2 ≤ s := by
    have : χ.leaves ≤ ∑ w, o w := by
      rw [leaves_eq]; exact Finset.sum_le_sum fun w _ => hχo w
    omega
  have hχp : occ χ p = 1 := by
    have h1 : 1 ≤ occ χ p :=
      lo_occ_pos χ p (fun _ => false) (by rw [hχ, hχ, hαe, hαe]; exact hdepp)
    have h2 := hχo p
    have h3 := hole p
    simp only [occ, hpq', hpl, ↓reduceIte] at h3
    omega
  have hχlit : ∀ b, χ ≠ DMFormula.lit p b := by
    rintro b rfl
    have hqr' : (dropV G p).Adj q r := ⟨hqr, hpq'.symm, G.ne_of_adj hrp⟩
    have hdq := lo_EF_dep_edge (dropV G p) (insert p A) (gr_iso_insert G A p hA) hqr'
    rw [← hαe, ← hαe, ← hχ, ← hχ] at hdq
    apply hdq
    simp [eval_lit, upd, hpq']
  obtain ⟨sg3, g3, ψ3, m3, α3, β3, o3, hψ30, hm3, hα3, hβ3, hα3p, hβ3p, hβα3, hdec3, hoα3, hoβ3,
    hole3⟩ := lo_stepTP_aux_single_ach χ p hχp hχlit
  by_cases habs : litv sg3 false = g3
  · exact lo_stepTP_aux_posq_abs G A hG hA IH l p q r hlp hp k s hk α hαe χ hχ hχs sg3 g3 ψ3 m3
      α3 β3 hm3 hα3 hβ3 hα3p hβ3p hβα3 hdec3 habs
  · exact lo_stepTP_aux_posq_or G A hG hA IH hA0 l p q r hlp hl hpq hqr hrp hp k s hk φ hφ he
      hocc1 hp1 _ m α β hψ0 hm hα hβ hαl hβl hβα hdec hT rfl heq o hoβ hole χ hχ hχo sg3 g3 ψ3
      m3 α3 β3 o3 hψ30 hm3 hα3 hβ3 hα3p hβ3p hβα3 hdec3 hoα3 hoβ3 hole3 habs

/-- (TP) Case `ψ = x_q` (the case `ψ = x_r` is this lemma with `q, r` swapped), after
the bad-case split (`hT`) and after `lo_stepTP_aux_p0` (so `occ φ p ≤ 2`). Round 3: PROVEN from
`lo_stepTP_aux_posq_two` (`occ φ p = 2`) and `lo_stepTP_aux_posq_one` (`occ φ p = 1`, OPEN). -/
theorem lo_stepTP_aux_posq (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (hA0 : A = ∅) (l p q r : Fin n) (hlp : G.Adj l p)
    (hl : ∀ w, G.Adj l w → w = p) (hpq : G.Adj p q) (hqr : G.Adj q r) (hrp : G.Adj r p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k s : ℕ) (hk : CovLB G k)
    (φ : DMFormula n) (hφ : φ.leaves ≤ s) (he : ∀ z, φ.eval z = EF G A z)
    (hocc1 : occ φ l = 1) (hocc2 : occ φ p ≤ 2) (ψ : DMFormula n) (m : ℕ)
    (α β : (Fin n → Bool) → Bool) (hψ0 : occ ψ l = 0)
    (hm : m + 2 ≤ φ.leaves) (hα : ALeaf m α) (hβ : ALeaf m β)
    (hαl : ∀ x c, α (upd x l c) = α x) (hβl : ∀ x c, β (upd x l c) = β x)
    (hβα : ∀ x, β x = true → α x = true)
    (hdec : ∀ x, φ.eval x = (β x || (α x && bop true (litv true (x l)) (ψ.eval x))))
    (hT : ∃ T : Finset (Fin n), (∀ u v, (dropV G l).Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card < k)
    (hψlit : ψ = DMFormula.lit q true)
    (heq : A.card + G.edgeSet.ncard + k = s + 1)
    (o : Vec n) (hoα : Ach o α) (hoβ : Ach o β)
    (hole : ∀ w, o w + occ ψ w + (if w = l then 1 else 0) ≤ occ φ w) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  have hoccp : 1 ≤ occ φ p :=
    lo_occ_pos φ p (upd (fun _ => false) l true) (by rw [he, he]; exact lo_EF_dep_edge G A hA hlp.symm)
  by_cases h2 : 2 ≤ occ φ p
  · have hαe : ∀ x, α x = EF (dropV G p) (insert p A) x := fun x =>
      lo_stepTP_aux_alpha G A hA l p hlp hl φ he ψ α β hαl hβl hβα hdec x
    refine lo_stepTP_aux_posq_two G A hG hA IH l p q r hlp hp (G.ne_of_adj hpq) k s hk φ hφ α
      hαe o hoα (fun w => ?_) h2
    have h := hole w
    rw [hψlit] at h
    exact h
  · exact lo_stepTP_aux_posq_one G A hG hA IH hA0 l p q r hlp hl hpq hqr hrp hp k s hk φ hφ he
      hocc1 (by omega) ψ m α β hψ0 hm hα hβ hαl hβl hβα hdec hT hψlit heq o hoα hoβ hole

/-- (TP) THE REMAINING OPEN CASE, after the `τ(G - l) ≥ k` split: there is a cover `T` of
`G - l` with `|T| < k` (so `p, l ∉ T` and `q, r ∈ T`, since `T ∪ {p}` covers `G`). The rest is
as in `lo_stepTP_aux_bad`. On paper (notes, Round 1): necessarily `g = true`, `sg = true`
(OR gate, positive `x_l`; else `EF` would not depend on `x_l`), and the sibling literal is
`¬x_p`, `x_q` or `x_r` (any other literal contradicts `EF` at `{p}` / `{p, j}`).
Round 2: split into `occ φ p ≥ 3` (`lo_stepTP_aux_p0`, PROVEN), `ψ = ¬x_p`
(`lo_stepTP_aux_negp`, OPEN) and `ψ = x_q` / `ψ = x_r` (`lo_stepTP_aux_posq`, OPEN). -/
theorem lo_stepTP_aux_badT (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (hA0 : A = ∅) (l p q r : Fin n) (hlp : G.Adj l p)
    (hl : ∀ w, G.Adj l w → w = p) (hpq : G.Adj p q) (hqr : G.Adj q r) (hrp : G.Adj r p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k s : ℕ) (hk : CovLB G k)
    (φ : DMFormula n) (hφ : φ.leaves ≤ s) (he : ∀ z, φ.eval z = EF G A z)
    (hocc1 : occ φ l = 1) (sg g : Bool) (ψ : DMFormula n) (m : ℕ)
    (α β : (Fin n → Bool) → Bool) (hψ0 : occ ψ l = 0) (_hψ1 : ψ.leaves = 1)
    (hm : m + 2 ≤ φ.leaves) (hα : ALeaf m α) (hβ : ALeaf m β)
    (hαl : ∀ x c, α (upd x l c) = α x) (hβl : ∀ x c, β (upd x l c) = β x)
    (hβα : ∀ x, β x = true → α x = true) (_habs : litv sg true = g)
    (hdec : ∀ x, φ.eval x = (β x || (α x && bop g (litv sg (x l)) (ψ.eval x))))
    (hT : ∃ T : Finset (Fin n), (∀ u v, (dropV G l).Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card < k)
    (hg : g = true) (hsg : sg = true) (j : Fin n) (t : Bool) (hψlit : ψ = DMFormula.lit j t)
    (_hx0 : ψ.eval (upd (fun _ => false) p true) = false)
    (hcls : (j = p ∧ t = false) ∨ (t = true ∧ (j = q ∨ j = r)))
    (o : Vec n) (hoα : Ach o α) (hoβ : Ach o β)
    (hole : ∀ w, o w + occ ψ w + (if w = l then 1 else 0) ≤ occ φ w)
    (hΦ : ∃ Φ : DMFormula n, occ Φ l = 1 ∧ (∀ w, occ Φ w + occ ψ w ≤ occ φ w) ∧
      ∀ x, φ.eval x = Φ.eval (upd x l (bop g (litv sg (x l)) (ψ.eval x)))) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  by_cases h3 : 3 ≤ occ φ p
  · exact lo_stepTP_aux_p0 G A hG hA IH l p q r hlp hl hp k s hk φ hφ he (by omega)
  have hocc2 : occ φ p ≤ 2 := by omega
  rw [hg, hsg] at hdec
  rw [hg, hsg] at hΦ
  -- `l := true` drops 2 leaves, so `lo_TP_one` at `s + 1` gives `μ ≤ s + 1`: one short.
  have hαF : ∀ x, α x = EF G A (upd x l true) := by
    intro x
    rw [← he, hdec, hαl, hβl]
    have hu : upd x l true l = true := by simp [upd]
    rw [hu]
    cases hb : β x
    · simp [bop, litv]
    · simp [bop, litv, hβα x hb]
  have hone := lo_TP_one G A hG hA IH l p q r hlp hl hpq hqr hrp hp k (s + 1) hk
    (ALeaf.congr hαF (ALeaf.mono (by omega) hα))
  rcases le_or_gt (A.card + G.edgeSet.ncard + k) s with hle | hlt
  · exact hle
  have heq : A.card + G.edgeSet.ncard + k = s + 1 := by omega
  rcases hcls with ⟨hj, ht⟩ | ⟨ht, hj | hj⟩
  · exact lo_stepTP_aux_negp G A hG hA IH hA0 l p q r hlp hl hpq hqr hrp hp k s hk φ hφ he
      hocc1 hocc2 ψ m α β hψ0 hm hα hβ hαl hβl hβα hdec hT (by rw [hψlit, hj, ht]) heq
      o hoα hoβ hole hΦ
  · exact lo_stepTP_aux_posq G A hG hA IH hA0 l p q r hlp hl hpq hqr hrp hp k s hk φ hφ he
      hocc1 hocc2 ψ m α β hψ0 hm hα hβ hαl hβl hβα hdec hT (by rw [hψlit, hj, ht]) heq
      o hoα hoβ hole
  · exact lo_stepTP_aux_posq G A hG hA IH hA0 l p r q hlp hl hrp.symm hqr.symm hpq.symm
      (fun w h => (hp w h).imp_right Or.symm) k s hk φ hφ he
      hocc1 hocc2 ψ m α β hψ0 hm hα hβ hαl hβl hβα hdec hT (by rw [hψlit, hj, ht]) heq
      o hoα hoβ hole

/-- `EF` is monotone in each input. -/
theorem lo_stepTP_aux_mono (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool)
    (i : Fin n) (h : EF G A (upd x i false) = true) : EF G A (upd x i true) = true := by
  unfold EF at *
  simp only [decide_eq_true_eq] at h ⊢
  have key : ∀ w, upd x i false w = true → upd x i true w = true := by
    intro w hw
    unfold upd at *
    by_cases hwi : w = i
    · simp [hwi]
    · simpa [hwi] using hw
  rcases h with ⟨a, ha, hx⟩ | ⟨u, v, huv, hu, hv⟩
  · exact Or.inl ⟨a, ha, key a hx⟩
  · exact Or.inr ⟨u, v, huv, key u hu, key v hv⟩

/-- In the absorbing-at-`true` case the gate is OR and the literal is positive `x_l`:
otherwise `l := true` gives `β`, which (by monotonicity) makes `EF` independent of `x_l`. -/
theorem lo_stepTP_aux_gate (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hA : Iso G A)
    (l p : Fin n) (hlp : G.Adj l p) (sg g : Bool) (ψ : DMFormula n)
    (α β : (Fin n → Bool) → Bool) (habs : litv sg true = g)
    (hres : ∀ x c, EF G A (upd x l c) = (β x || (α x && bop g (litv sg c) (ψ.eval x)))) :
    g = true ∧ sg = true := by
  have hdep := lo_EF_dep_edge G A hA hlp
  cases g with
  | true =>
    cases sg with
    | true => exact ⟨rfl, rfl⟩
    | false => simp [litv] at habs
  | false =>
    exfalso
    cases sg with
    | true => simp [litv] at habs
    | false =>
      have hm := lo_stepTP_aux_mono G A (upd (fun _ => false) p true) l
      rw [hres, hres] at hdep hm
      revert hdep hm
      cases β (upd (fun _ => false) p true) <;> cases α (upd (fun _ => false) p true) <;>
        cases ψ.eval (upd (fun _ => false) p true) <;> simp [litv, bop]

/-- (TP) THE REMAINING OPEN CASE. `A = ∅`, `l` occurs exactly once in `φ`, the parent gate of
the `l`-leaf absorbs at `l := true` (`litv sg true = g`), and the sibling `ψ` of the `l`-leaf is
a single literal (`ψ.leaves = 1`). Then `l := true` drops only 2 leaves (needs 3) and
`l := false` drops only 1 (needs 2 when `τ(G - l) = τ - 1`). See
`Work/lo_stepTP.notes.md` (Round 1) for the further reductions found on paper. -/
theorem lo_stepTP_aux_bad (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G)
    (hA : Iso G A) (IH : LoIH G A) (hA0 : A = ∅) (l p q r : Fin n) (hlp : G.Adj l p)
    (hl : ∀ w, G.Adj l w → w = p) (hpq : G.Adj p q) (hqr : G.Adj q r) (hrp : G.Adj r p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) (k s : ℕ) (hk : CovLB G k)
    (φ : DMFormula n) (hφ : φ.leaves ≤ s) (he : ∀ z, φ.eval z = EF G A z)
    (hocc1 : occ φ l = 1) (sg g : Bool) (ψ : DMFormula n) (m : ℕ)
    (α β : (Fin n → Bool) → Bool) (hψ0 : occ ψ l = 0) (hψ1 : ψ.leaves = 1)
    (hm : m + 2 ≤ φ.leaves) (hα : ALeaf m α) (hβ : ALeaf m β)
    (hαl : ∀ x c, α (upd x l c) = α x) (hβl : ∀ x c, β (upd x l c) = β x)
    (hβα : ∀ x, β x = true → α x = true) (habs : litv sg true = g)
    (hdec : ∀ x, φ.eval x = (β x || (α x && bop g (litv sg (x l)) (ψ.eval x))))
    (o : Vec n) (hoα : Ach o α) (hoβ : Ach o β)
    (hole : ∀ w, o w + occ ψ w + (if w = l then 1 else 0) ≤ occ φ w)
    (hΦ : ∃ Φ : DMFormula n, occ Φ l = 1 ∧ (∀ w, occ Φ w + occ ψ w ≤ occ φ w) ∧
      ∀ x, φ.eval x = Φ.eval (upd x l (bop g (litv sg (x l)) (ψ.eval x)))) :
    A.card + G.edgeSet.ncard + k ≤ s := by
  by_cases hcov : CovLB (dropV G l) k
  · -- `τ(G - l) ≥ k`: `l := false` drops 1 leaf and `μ` drops by 1.
    have hlA : l ∉ A := gr_not_mem_of_adj hA hlp
    have hr := lo_restrict φ hφ he l false
    rw [hocc1] at hr
    have hr' : ALeaf (s - 1) (EF (dropV G l) A) :=
      ALeaf.congr (fun x => lo_EF_upd_false G A l hlA x) hr
    have hE := gr_ncard_dropV G l
    have hd := gr_dg_one hlp hl
    have := IH (dropV G l) A (gr_good_mono (gr_dropV_le G l) hG)
      (gr_iso_mono (gr_dropV_le G l) hA) (by omega) k (s - 1) hcov hr'
    omega
  · unfold CovLB at hcov
    push Not at hcov
    have hres : ∀ x c, EF G A (upd x l c) =
        (β x || (α x && bop g (litv sg c) (ψ.eval x))) := by
      intro x c
      have hu : upd x l c l = c := by simp [upd]
      rw [← he, hdec, hαl, hβl, eval_upd_of_zero ψ l hψ0, hu]
    obtain ⟨hg, hsg⟩ := lo_stepTP_aux_gate G A hA l p hlp sg g ψ α β habs hres
    subst hg
    subst hsg
    have hdep := lo_EF_dep_edge G A hA hlp
    have hmono := lo_stepTP_aux_mono G A (upd (fun _ => false) p true) l
    have h0 : EF G A (upd (upd (fun _ => false) p true) l false) = false := by
      cases h : EF G A (upd (upd (fun _ => false) p true) l false)
      · rfl
      · exact absurd (by rw [hmono h, h]) hdep
    have h1 : EF G A (upd (upd (fun _ => false) p true) l true) = true := by
      cases h : EF G A (upd (upd (fun _ => false) p true) l true)
      · exact absurd (by rw [h, h0]) hdep
      · rfl
    obtain ⟨j, t, hψlit⟩ := lo_stepTP_aux_lit ψ hψ1
    have hx0 := lo_stepTP_aux_psi G A l ψ α β hres _ h0 h1
    have hres' := hres
    rw [hA0] at hres'
    have hcls := lo_stepTP_aux_cls G l p q r hlp hp ψ α β hres' hψ0 j t hψlit hx0
    exact lo_stepTP_aux_badT G A hG hA IH hA0 l p q r hlp hl hpq hqr hrp hp k s hk φ hφ he
      hocc1 true true ψ m α β hψ0 hψ1 hm hα hβ hαl hβl hβα habs hdec hcov rfl rfl j t hψlit hx0
      hcls o hoα hoβ hole hΦ

/-- Step (TP): pendant `l` at `p`, and `p` on the triangle `p q r` with `N(p) = {l, q, r}`.
Reduced to `lo_stepTP_aux_bad` (the single-literal-sibling case), which is OPEN. -/
theorem lo_stepTP (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G) (hA : Iso G A)
    (IH : LoIH G A) (l p q r : Fin n) (hlp : G.Adj l p) (hl : ∀ w, G.Adj l w → w = p)
    (hpq : G.Adj p q) (hqr : G.Adj q r) (hrp : G.Adj r p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q ∨ w = r) : LoClaim G A := by
  rcases A.eq_empty_or_nonempty with hA0 | hne
  swap
  · exact lo_stepA G A hG hA IH hne
  intro k s hk hs
  have hdep := lo_EF_dep_edge G A hA hlp
  obtain ⟨φ, hφ, he⟩ := lo_formula_of_nonconst hs _ _ hdep
  have hoccl : 1 ≤ occ φ l :=
    lo_occ_pos φ l (upd (fun _ => false) p true) (by rw [he, he]; exact hdep)
  have hdep' := lo_EF_dep_edge G A hA hlp.symm
  have hoccp : 1 ≤ occ φ p :=
    lo_occ_pos φ p (upd (fun _ => false) l true) (by rw [he, he]; exact hdep')
  rcases Nat.lt_or_ge (occ φ l) 2 with h1 | h2
  · have hocc1 : occ φ l = 1 := by omega
    have hlit : ∀ b, φ ≠ DMFormula.lit l b := by
      rintro b rfl
      have hpl : p ≠ l := (G.ne_of_adj hlp).symm
      simp [occ, hpl] at hoccp
    obtain ⟨sg, g, ψ, m, α, β, o, hψ0, hm, hα, hβ, hαl, hβl, hβα, hdec, hoα, hoβ, hole, hΦ⟩ :=
      fable_single_ach φ l hocc1 hlit
    have hψpos := leaves_pos ψ
    have hres : ∀ x c, EF G A (upd x l c) =
        (β x || (α x && bop g (litv sg c) (ψ.eval x))) := by
      intro x c
      have hu : upd x l c l = c := by simp [upd]
      rw [← he, hdec, hαl, hβl, eval_upd_of_zero ψ l hψ0, hu]
    by_cases habs : litv sg true = g
    · rcases Nat.lt_or_ge ψ.leaves 2 with hψ1 | hψ2
      · exact lo_stepTP_aux_bad G A hG hA IH hA0 l p q r hlp hl hpq hqr hrp hp k s hk φ hφ he
          hocc1 sg g ψ m α β hψ0 (by omega) (by omega) hα hβ hαl hβl hβα habs hdec o hoα hoβ hole hΦ
      · apply lo_TP_one G A hG hA IH l p q r hlp hl hpq hqr hrp hp k s hk
        have hA' := lo_stepTP_aux_abs α β m hα hβ hβα g (fun x => ψ.eval x)
        refine ALeaf.mono (by omega) (ALeaf.congr (fun x => ?_) hA')
        rw [hres, habs]
    · have habs' : litv sg false = g := by
        cases sg <;> cases g <;> simp_all [litv]
      apply lo_TP_zero G A hG hA IH l p q r hlp hl hpq hqr hrp hp k s hk
      have hA' := lo_stepTP_aux_abs α β m hα hβ hβα g (fun x => ψ.eval x)
      refine ALeaf.mono (by omega) (ALeaf.congr (fun x => ?_) hA')
      rw [hres, habs']
  · apply lo_TP_zero G A hG hA IH l p q r hlp hl hpq hqr hrp hp k s hk
    exact ALeaf.mono (by omega) (lo_restrict φ hφ he l false)

/-- Step (T): pendant triangle `a b c` with `N(b) = {a, c}`, `N(c) = {a, b}` (apex `a`).
SKELETON CHANGE (Triangle/lo_stepT.lean): moved below `lo_stepTP` (statement unchanged). A
single restriction does not suffice for an arbitrary T (dg a ≥ 4, no pendant at a); the proof
re-runs the configuration search `lo_stepT_aux_leaf_config` and dispatches: nice T →
`lo_stepT_aux_main`, P1 → `lo_stepP1`, P2 → `lo_stepP2`, TP → `lo_stepTP`. So `lo_stepTP` must
not use `lo_stepT`. -/
theorem lo_stepT (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (hG : Good G) (hA : Iso G A)
    (IH : LoIH G A) (a b c : Fin n) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a)
    (hb : ∀ w, G.Adj b w → w = a ∨ w = c) (hc : ∀ w, G.Adj c w → w = a ∨ w = b) :
    LoClaim G A := by
  have _ : G.Adj b c ∧ G.Adj c a ∧ (∀ w, G.Adj b w → w = a ∨ w = c) ∧
      (∀ w, G.Adj c w → w = a ∨ w = b) := ⟨hbc, hca, hb, hc⟩
  rcases lo_stepT_aux_leaf_config G hG.1 hG.2 ⟨a, b, hab⟩ with
    ⟨a', b', c', h1, h2, h3, h4, h5, h6⟩ | ⟨l, p, q, h1, h2, h3⟩ |
    ⟨l, p, l', h1, h2, h3, h4, h5⟩ | ⟨l, p, q, r, h1, h2, h3, h4, h5, h6⟩
  · exact lo_stepT_aux_main G A hG hA IH a' b' c' h1 h2 h3 h4 h5 h6
  · exact lo_stepP1 G A hG hA IH l p q h1 h2 h3
  · exact lo_stepP2 G A hG hA IH l p l' h1 h2 h3 h4 h5
  · exact lo_stepTP G A hG hA IH l p q r h1 h2 h3 h4 h5 h6

/-! ## Glue (gl_) -/

/-- Strong induction on `2 |E| + |A|`, splitting by `leaf_config`. -/
theorem gl_lower_main (m : ℕ) : ∀ (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
    2 * G.edgeSet.ncard + A.card = m → Good G → Iso G A → LoClaim G A := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro G A hm hG hA
    have IH : LoIH G A := fun G' A' hG' hA' hlt => ih _ (by omega) G' A' rfl hG' hA'
    by_cases hAne : A.Nonempty
    · exact lo_stepA G A hG hA IH hAne
    · rw [Finset.not_nonempty_iff_eq_empty] at hAne
      subst hAne
      by_cases hE : ∃ u v : Fin n, G.Adj u v
      · rcases leaf_config G hG.1 hE with ⟨a, b, c, h1, h2, h3, h4, h5⟩ | ⟨l, p, q, h1, h2, h3⟩ |
          ⟨l, p, l', h1, h2, h3, h4, h5⟩ | ⟨l, p, q, r, h1, h2, h3, h4, h5, h6⟩
        · exact lo_stepT G ∅ hG hA IH a b c h1 h2 h3 h4 h5
        · exact lo_stepP1 G ∅ hG hA IH l p q h1 h2 h3
        · exact lo_stepP2 G ∅ hG hA IH l p l' h1 h2 h3 h4 h5
        · exact lo_stepTP G ∅ hG hA IH l p q r h1 h2 h3 h4 h5 h6
      · push Not at hE
        exact lo_base G hE

theorem gl_ncard_eq (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

/-- The lower direction of the target. -/
theorem gl_lower (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t s : ℕ) (hG : Good G)
    (ht : ∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S →
      t ≤ S.card)
    (h : HasLeafSize n
      (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) s) :
    G.edgeFinset.card + t ≤ s := by
  obtain ⟨φ, hφ, he⟩ := h
  have hiso : Iso G ∅ := fun a ha => by simp at ha
  have := gl_lower_main _ G ∅ rfl hG hiso t s (fun T hT => ht T hT)
    (.inr ⟨φ, hφ, fun x => by
      rw [he x]
      unfold EF
      simp⟩)
  rw [gl_ncard_eq] at this
  simpa using this

end LowerHalf

end PEqualNP.Outside.L_meta_222

theorem PEqualNP.Outside.L_meta_222 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t s : ℕ), (∃ u v : Fin n, G.Adj u v) → (∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → p.length = 3) → (∀ a b c d e : Fin n, G.Adj a b → G.Adj b c → G.Adj c a → G.Adj a d → G.Adj d e → G.Adj e a → ((b = d ∧ c = e) ∨ (b = e ∧ c = d))) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → (PEqualNP.MetaComplexity.HasLeafSize n (fun x : Fin n → Bool => decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) s ↔ G.edgeFinset.card + t ≤ s) := by
  intro n G _ t s hE hcyc htri hT hmin
  exact ⟨fun h => PEqualNP.Outside.L_meta_222.gl_lower G t s (And.intro hcyc htri) hmin h,
    PEqualNP.Outside.L_meta_222.up_dir G t s hE hT⟩
