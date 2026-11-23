import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_183

open PEqualNP.MetaComplexity

abbrev Vec := Fin 6 → ℕ

def occ : DMFormula 6 → Fin 6 → ℕ
  | .lit i _ => fun k => if k = i then 1 else 0
  | .and a b => fun k => occ a k + occ b k
  | .or a b => fun k => occ a k + occ b k

def zv (o : Vec) (i : Fin 6) : Vec := fun k => if k = i then 0 else o k

def dv (o : Vec) (j : Fin 6) : Vec := fun k => if k = j then o j - 1 else o k

def upd (x : Fin 6 → Bool) (i : Fin 6) (c : Bool) : Fin 6 → Bool :=
  fun k => if k = i then c else x k

def litv (s v : Bool) : Bool := if s then v else !v

def bop (g a b : Bool) : Bool := if g then (a || b) else (a && b)

def mk (g : Bool) (a b : DMFormula 6) : DMFormula 6 := if g then .or a b else .and a b

theorem eval_mk (g : Bool) (a b : DMFormula 6) (x : Fin 6 → Bool) :
    (mk g a b).eval x = bop g (a.eval x) (b.eval x) := by
  cases g <;> rfl

theorem occ_mk (g : Bool) (a b : DMFormula 6) (k : Fin 6) :
    occ (mk g a b) k = occ a k + occ b k := by
  cases g <;> rfl

theorem eval_lit (i : Fin 6) (s : Bool) (x : Fin 6 → Bool) :
    (DMFormula.lit i s).eval x = litv s (x i) := by
  cases s <;> rfl

theorem leaves_eq (φ : DMFormula 6) : φ.leaves = ∑ k, occ φ k := by
  induction φ with
  | lit i b => simp [DMFormula.leaves, occ]
  | and a b iha ihb => simp [DMFormula.leaves, occ, iha, ihb, Finset.sum_add_distrib]
  | or a b iha ihb => simp [DMFormula.leaves, occ, iha, ihb, Finset.sum_add_distrib]

theorem eval_congr (φ : DMFormula 6) (x y : Fin 6 → Bool)
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

theorem eval_upd_of_zero (φ : DMFormula 6) (i : Fin 6) (h : occ φ i = 0) (x : Fin 6 → Bool)
    (c : Bool) : φ.eval (upd x i c) = φ.eval x := by
  apply eval_congr
  intro k hk
  have : k ≠ i := by rintro rfl; omega
  simp [upd, this]

theorem exists_occ (φ : DMFormula 6) : ∃ j, 1 ≤ occ φ j := by
  induction φ with
  | lit i b => exact ⟨i, by simp [occ]⟩
  | and a b iha ihb => obtain ⟨j, hj⟩ := iha; exact ⟨j, by simp [occ]; omega⟩
  | or a b iha ihb => obtain ⟨j, hj⟩ := iha; exact ⟨j, by simp [occ]; omega⟩

def Ach (o : Vec) (h : (Fin 6 → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x, h x = c) ∨ ∃ φ : DMFormula 6, (∀ x, φ.eval x = h x) ∧ ∀ k, occ φ k ≤ o k

theorem Ach.mono {o o' : Vec} {h : (Fin 6 → Bool) → Bool} (hle : ∀ k, o k ≤ o' k)
    (a : Ach o h) : Ach o' h := by
  rcases a with hc | ⟨φ, he, ho⟩
  · exact .inl hc
  · exact .inr ⟨φ, he, fun k => (ho k).trans (hle k)⟩

theorem Ach.congr {o : Vec} {h h' : (Fin 6 → Bool) → Bool} (e : ∀ x, h x = h' x)
    (a : Ach o h) : Ach o h' := by
  rcases a with ⟨c, hc⟩ | ⟨φ, he, ho⟩
  · exact .inl ⟨c, fun x => by rw [← e, hc]⟩
  · exact .inr ⟨φ, fun x => by rw [he, e], ho⟩

theorem Ach.form (φ : DMFormula 6) : Ach (occ φ) φ.eval := .inr ⟨φ, fun _ => rfl, fun _ => le_rfl⟩

theorem Ach.const (o : Vec) (c : Bool) : Ach o (fun _ => c) := .inl ⟨c, fun _ => rfl⟩

theorem Ach.bop {o1 o2 : Vec} {h1 h2 : (Fin 6 → Bool) → Bool} (g : Bool) (a1 : Ach o1 h1)
    (a2 : Ach o2 h2) : Ach (fun k => o1 k + o2 k) (fun x => bop g (h1 x) (h2 x)) := by
  rcases a1 with ⟨c1, hc1⟩ | ⟨φ1, e1, b1⟩
  · by_cases hg : c1 = g
    · exact .inl ⟨g, fun x => by beta_reduce; rw [hc1, hg]; cases g <;> simp [PEqualNP.Outside.L_meta_183.bop]⟩
    · refine (a2.mono (fun k => Nat.le_add_left _ _)).congr (fun x => ?_)
      rw [hc1]; cases g <;> cases c1 <;> simp_all [PEqualNP.Outside.L_meta_183.bop]
  · rcases a2 with ⟨c2, hc2⟩ | ⟨φ2, e2, b2⟩
    · by_cases hg : c2 = g
      · exact .inl ⟨g, fun x => by beta_reduce; rw [hc2, hg]; cases g <;> simp [PEqualNP.Outside.L_meta_183.bop]⟩
      · refine (Ach.mono (o := o1) (fun k => Nat.le_add_right _ _) (.inr ⟨φ1, e1, b1⟩)).congr
          (fun x => ?_)
        rw [hc2]; cases g <;> cases c2 <;> simp_all [PEqualNP.Outside.L_meta_183.bop]
    · exact .inr ⟨mk g φ1 φ2, fun x => by rw [eval_mk, e1, e2],
        fun k => by rw [occ_mk]; exact Nat.add_le_add (b1 k) (b2 k)⟩

theorem restrict (φ : DMFormula 6) (i : Fin 6) (c : Bool) :
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

theorem Ach.restrict {o : Vec} {h : (Fin 6 → Bool) → Bool} (a : Ach o h) (i : Fin 6) (c : Bool) :
    Ach (zv o i) (fun x => h (upd x i c)) := by
  rcases a with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · exact .inl ⟨c0, fun x => hc _⟩
  · refine ((L_meta_183.restrict φ i c).mono (fun k => ?_)).congr (fun x => by rw [he])
    simp only [zv]; split_ifs <;> simp [ho k]

theorem Ach.upd_inv {o : Vec} {h : (Fin 6 → Bool) → Bool} (a : Ach o h) (i : Fin 6)
    (hi : o i = 0) (x : Fin 6 → Bool) (c : Bool) : h (upd x i c) = h x := by
  rcases a with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · rw [hc, hc]
  · rw [← he, ← he, eval_upd_of_zero φ i (by have := ho i; omega)]


def KM (i : Fin 6) (o : Vec) (h : (Fin 6 → Bool) → Bool) : Prop :=
  Ach (dv o i) h ∨ ∃ c j, j ≠ i ∧ 1 ≤ o j ∧ Ach (dv (zv o i) j) (fun x => h (upd x i c))

theorem KM.congr {i : Fin 6} {o o' : Vec} {h h' : (Fin 6 → Bool) → Bool} (eo : ∀ k, o k = o' k)
    (eh : ∀ x, h x = h' x) (a : KM i o h) : KM i o' h' := by
  obtain rfl : o = o' := funext eo
  obtain rfl : h = h' := funext eh
  exact a

theorem km_step (i : Fin 6) (g : Bool) (A B : DMFormula 6) (hA : 1 ≤ occ A i)
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

theorem kill_multi (i : Fin 6) (φ : DMFormula 6) :
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

def ind2 (j k : Fin 6) : Vec := fun v => (if v = j then 1 else 0) + (if v = k then 1 else 0)

def ind3 (j k m : Fin 6) : Vec :=
  fun v => (if v = j then 1 else 0) + (if v = k then 1 else 0) + (if v = m then 1 else 0)

def sb (o p : Vec) : Vec := fun v => o v - p v

def KS (i : Fin 6) (o : Vec) (h : (Fin 6 → Bool) → Bool) : Prop :=
  (∃ j, j ≠ i ∧ 1 ≤ o j ∧ ∃ g si sj : Bool, ∃ ψ : DMFormula 6, (∀ k, occ ψ k ≤ dv o j k) ∧
      ∀ x, h x = ψ.eval (upd x i (bop g (litv si (x i)) (litv sj (x j))))) ∨
  (∃ j k, j ≠ i ∧ k ≠ i ∧ j ≤ k ∧ (∀ v, ind2 j k v ≤ o v) ∧ ∃ g g2 si sj sk : Bool,
      ∃ ψ : DMFormula 6, (∀ v, occ ψ v ≤ sb o (ind2 j k) v) ∧
      ∀ x, h x = ψ.eval (upd x i (bop g (litv si (x i))
        (bop g2 (litv sj (x j)) (litv sk (x k)))))) ∨
  (∃ c j k m, j ≠ i ∧ k ≠ i ∧ m ≠ i ∧ j ≤ k ∧ k ≤ m ∧ (∀ v, ind3 j k m v ≤ o v) ∧
      Ach (sb (zv o i) (ind3 j k m)) (fun x => h (upd x i c)))

theorem KS.congr {i : Fin 6} {o o' : Vec} {h h' : (Fin 6 → Bool) → Bool} (eo : ∀ k, o k = o' k)
    (eh : ∀ x, h x = h' x) (a : KS i o h) : KS i o' h' := by
  obtain rfl : o = o' := funext eo
  obtain rfl : h = h' := funext eh
  exact a

theorem bop_comm (g a b : Bool) : bop g a b = bop g b a := by
  cases g <;> cases a <;> cases b <;> rfl

theorem sort3 (j k m : Fin 6) : ∃ j' k' m' : Fin 6, j' ≤ k' ∧ k' ≤ m' ∧
    ∀ v, ind3 j k m v = ind3 j' k' m' v := by
  rcases le_total j k with h1 | h1 <;> rcases le_total k m with h2 | h2 <;>
    rcases le_total j m with h3 | h3
  · exact ⟨j, k, m, h1, h2, fun v => rfl⟩
  · exact ⟨j, k, m, h1, h2, fun v => rfl⟩
  · exact ⟨j, m, k, h3, h2, fun v => by simp only [ind3]; ring⟩
  · exact ⟨m, j, k, h3, h1, fun v => by simp only [ind3]; ring⟩
  · exact ⟨k, j, m, h1, h3, fun v => by simp only [ind3]; ring⟩
  · exact ⟨k, m, j, h2, h3, fun v => by simp only [ind3]; ring⟩
  · exact ⟨m, k, j, h2, h1, fun v => by simp only [ind3]; ring⟩
  · exact ⟨m, k, j, h2, h1, fun v => by simp only [ind3]; ring⟩

theorem ind3_pos (j k m : Fin 6) :
    1 ≤ ind3 j k m j ∧ 1 ≤ ind3 j k m k ∧ 1 ≤ ind3 j k m m := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold ind3 <;> rw [if_pos rfl] <;> omega

theorem three_aux (P Q R : DMFormula 6) :
    ∃ j k m, ∀ v, ind3 j k m v ≤ occ P v + occ Q v + occ R v := by
  obtain ⟨j, hj⟩ := exists_occ P
  obtain ⟨k, hk⟩ := exists_occ Q
  obtain ⟨m, hm⟩ := exists_occ R
  refine ⟨j, k, m, fun v => ?_⟩
  simp only [ind3]
  split_ifs <;> subst_vars <;> omega

theorem three_leaves (C D : DMFormula 6)
    (h : ¬ ((∃ j s, C = .lit j s) ∧ (∃ k s, D = .lit k s))) :
    ∃ j k m, ∀ v, ind3 j k m v ≤ occ C v + occ D v := by
  cases C with
  | lit j s =>
    cases D with
    | lit k s' => exact absurd ⟨⟨j, s, rfl⟩, ⟨k, s', rfl⟩⟩ h
    | and D1 D2 =>
      obtain ⟨a, b, c, hh⟩ := three_aux (.lit j s) D1 D2
      exact ⟨a, b, c, fun v => by have := hh v; simp only [occ] at this ⊢; omega⟩
    | or D1 D2 =>
      obtain ⟨a, b, c, hh⟩ := three_aux (.lit j s) D1 D2
      exact ⟨a, b, c, fun v => by have := hh v; simp only [occ] at this ⊢; omega⟩
  | and C1 C2 =>
    obtain ⟨a, b, c, hh⟩ := three_aux C1 C2 D
    exact ⟨a, b, c, fun v => by have := hh v; simp only [occ] at this ⊢; omega⟩
  | or C1 C2 =>
    obtain ⟨a, b, c, hh⟩ := three_aux C1 C2 D
    exact ⟨a, b, c, fun v => by have := hh v; simp only [occ] at this ⊢; omega⟩

theorem ks_leaf (i : Fin 6) (g g2 si : Bool) (B C D : DMFormula 6) (hC : occ C i = 0)
    (hD : occ D i = 0) (hocc : ∀ v, occ B v = occ C v + occ D v)
    (hev : ∀ x, B.eval x = bop g2 (C.eval x) (D.eval x)) :
    KS i (fun k => occ (DMFormula.lit i si) k + occ B k)
      (fun x => bop g ((DMFormula.lit i si).eval x) (B.eval x)) := by
  by_cases hlit : (∃ j s, C = .lit j s) ∧ (∃ k s, D = .lit k s)
  · obtain ⟨⟨j, sj, rfl⟩, ⟨k, sk, rfl⟩⟩ := hlit
    have hji : j ≠ i := by
      rintro rfl; simp [occ] at hC
    have hki : k ≠ i := by
      rintro rfl; simp [occ] at hD
    rcases le_total j k with hjk | hjk
    · refine .inr (.inl ⟨j, k, hji, hki, hjk, fun v => ?_, g, g2, si, sj, sk, .lit i true,
        fun v => ?_, fun x => ?_⟩)
      · simp only [ind2, hocc, occ]; omega
      · simp only [sb, ind2, hocc, occ]; omega
      · simp [eval_lit, upd, litv, hev]
    · refine .inr (.inl ⟨k, j, hki, hji, hjk, fun v => ?_, g, g2, si, sk, sj, .lit i true,
        fun v => ?_, fun x => ?_⟩)
      · simp only [ind2, hocc, occ]; omega
      · simp only [sb, ind2, hocc, occ]; omega
      · simp only [hev, eval_lit]
        rw [bop_comm g2]
        simp [upd, litv]
  · obtain ⟨j0, k0, m0, h3⟩ := three_leaves C D hlit
    obtain ⟨j, k, m, hjk, hkm, hs⟩ := sort3 j0 k0 m0
    have h3' : ∀ v, ind3 j k m v ≤ occ C v + occ D v := fun v => by rw [← hs]; exact h3 v
    have nz : ∀ w, 1 ≤ ind3 j k m w → w ≠ i := by
      intro w hw
      rintro rfl
      have := h3' w
      omega
    refine .inr (.inr ⟨litv si g, j, k, m, nz j (ind3_pos j k m).1, nz k (ind3_pos j k m).2.1,
      nz m (ind3_pos j k m).2.2, hjk, hkm, fun v => ?_, .inl ⟨g, fun x => ?_⟩⟩)
    · have := h3' v
      simp only [hocc]; omega
    · simp only [eval_lit, upd, ite_true]
      cases si <;> cases g <;> simp [litv, bop]

theorem ks_step (i : Fin 6) (g : Bool) (A B : DMFormula 6) (hA : occ A i = 1) (hB0 : occ B i = 0)
    (ihA : (∃ s, A = .lit i s) ∨ KS i (occ A) A.eval) :
    KS i (fun k => occ A k + occ B k) (fun x => bop g (A.eval x) (B.eval x)) := by
  rcases ihA with ⟨si, rfl⟩ | hk
  · cases B with
    | lit j sj =>
      have hji : j ≠ i := by
        rintro rfl; simp [occ] at hB0
      refine .inl ⟨j, hji, by simp [occ], g, si, sj, .lit i true, fun k => ?_, fun x => ?_⟩
      · simp only [occ, dv]
        split_ifs <;> simp_all
      · simp [eval_lit, upd, litv]
    | and C D =>
      have hB0' : occ C i + occ D i = 0 := hB0
      exact ks_leaf i g false si _ C D (by omega) (by omega) (fun _ => rfl) (fun _ => rfl)
    | or C D =>
      have hB0' : occ C i + occ D i = 0 := hB0
      exact ks_leaf i g true si _ C D (by omega) (by omega) (fun _ => rfl) (fun _ => rfl)
  · rcases hk with ⟨j, hji, hj, g', si, sj, ψ, hψo, hψe⟩ |
      ⟨j, k, hji, hki, hjk, hv, g', g2, si, sj, sk, ψ, hψo, hψe⟩ |
      ⟨c, j, k, m, hji, hki, hmi, hjk, hkm, hv, ha⟩
    · refine .inl ⟨j, hji, by simp only; omega, g', si, sj, mk g ψ B, fun k => ?_, fun x => ?_⟩
      · rw [occ_mk]
        have := hψo k
        simp only [dv] at this ⊢
        split_ifs at this ⊢ with e
        · subst e; omega
        · omega
      · rw [eval_mk, ← hψe x, eval_upd_of_zero B i hB0]
    · refine .inr (.inl ⟨j, k, hji, hki, hjk, fun v => ?_, g', g2, si, sj, sk, mk g ψ B,
        fun v => ?_, fun x => ?_⟩)
      · have := hv v
        simp only; omega
      · rw [occ_mk]
        have h1 := hψo v
        have h2 := hv v
        simp only [sb] at h1 ⊢
        omega
      · rw [eval_mk, ← hψe x, eval_upd_of_zero B i hB0]
    · refine .inr (.inr ⟨c, j, k, m, hji, hki, hmi, hjk, hkm, fun v => ?_, ?_⟩)
      · have := hv v
        simp only; omega
      · refine (ha.bop g ((Ach.form B).restrict i c)).mono (fun w => ?_)
        have := hv w
        simp only [sb, zv]
        split_ifs <;> omega

theorem kill_single (i : Fin 6) (φ : DMFormula 6) :
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

def code (x : Fin 6 → Bool) : ℕ :=
  Nat.bit (x 0) (Nat.bit (x 1) (Nat.bit (x 2) (Nat.bit (x 3) (Nat.bit (x 4) (Nat.bit (x 5) 0)))))

def ev (T : ℕ) (x : Fin 6 → Bool) : Bool := T.testBit (code x)

def M : ℕ := 0xffffffffffffffff

def vt : Fin 6 → ℕ := ![0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem allx {P : (Fin 6 → Bool) → Prop}
    (h : ∀ b0 b1 b2 b3 b4 b5 : Bool, P ![b0, b1, b2, b3, b4, b5]) (x : Fin 6 → Bool) : P x := by
  have e : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext k; fin_cases k <;> rfl
  rw [e]; exact h _ _ _ _ _ _

theorem code_lt : ∀ x, code x < 64 := allx (by decide +kernel)

def setIdx (a : ℕ) (i : Fin 6) (c : Bool) : ℕ :=
  if c then (if a.testBit i then a else 2 ^ (i : ℕ) + a)
  else (if a.testBit i then a - 2 ^ (i : ℕ) else a)

theorem code_upd (i : Fin 6) (c : Bool) : ∀ x, code (upd x i c) = setIdx (code x) i c := by
  fin_cases i <;> cases c <;> exact allx (by decide +kernel)

def rst (g : ℕ) (i : Fin 6) (c : Bool) : ℕ :=
  if c then (g &&& vt i) ||| ((g &&& vt i) >>> 2 ^ (i : ℕ))
  else (g &&& (M ^^^ vt i)) ||| ((g &&& (M ^^^ vt i)) <<< 2 ^ (i : ℕ))

theorem facts_t : ∀ i : Fin 6, ∀ a < 64,
    ((vt i).testBit a = true → setIdx a i true = a ∧ (vt i).testBit (2 ^ (i : ℕ) + a) = false) ∧
    ((vt i).testBit a = false →
      setIdx a i true = 2 ^ (i : ℕ) + a ∧ (vt i).testBit (2 ^ (i : ℕ) + a) = true) := by
  decide +kernel

theorem facts_f : ∀ i : Fin 6, ∀ a < 64,
    ((vt i).testBit a = true → setIdx a i false = a - 2 ^ (i : ℕ) ∧ 2 ^ (i : ℕ) ≤ a ∧
      (M ^^^ vt i).testBit a = false ∧ (M ^^^ vt i).testBit (a - 2 ^ (i : ℕ)) = true) ∧
    ((vt i).testBit a = false → setIdx a i false = a ∧ (M ^^^ vt i).testBit a = true ∧
      (decide (a ≥ 2 ^ (i : ℕ)) && (M ^^^ vt i).testBit (a - 2 ^ (i : ℕ))) = false) := by
  decide +kernel

theorem rst_bit (g : ℕ) (i : Fin 6) (c : Bool) (a : ℕ) (ha : a < 64) :
    (rst g i c).testBit a = g.testBit (setIdx a i c) := by
  cases c
  · have F := facts_f i a ha
    simp only [rst, Bool.false_eq_true, if_false, Nat.testBit_or, Nat.testBit_and,
      Nat.testBit_shiftLeft]
    cases hL : (vt i).testBit a
    · obtain ⟨h1, h2, h3⟩ := F.2 hL
      rw [h1, h2]
      cases hd : decide (a ≥ 2 ^ (i : ℕ)) <;> cases hm : (M ^^^ vt i).testBit (a - 2 ^ (i : ℕ)) <;>
        simp_all
    · obtain ⟨h1, h2, h3, h4⟩ := F.1 hL
      rw [h1, h3, h4]
      simp [h2]
  · have F := facts_t i a ha
    simp only [rst, if_true, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight]
    cases hL : (vt i).testBit a
    · obtain ⟨h1, h2⟩ := F.2 hL
      rw [h1, h2]; simp
    · obtain ⟨h1, h2⟩ := F.1 hL
      rw [h1, h2]; simp

theorem ev_rst (g : ℕ) (i : Fin 6) (c : Bool) (x : Fin 6 → Bool) :
    ev (rst g i c) x = ev g (upd x i c) := by
  unfold ev
  rw [rst_bit _ _ _ _ (code_lt x), code_upd]

theorem ev_and (A B : ℕ) (x : Fin 6 → Bool) : ev (A &&& B) x = (ev A x && ev B x) :=
  Nat.testBit_and _ _ _

theorem ev_or (A B : ℕ) (x : Fin 6 → Bool) : ev (A ||| B) x = (ev A x || ev B x) :=
  Nat.testBit_or _ _ _

theorem ev_xor (A B : ℕ) (x : Fin 6 → Bool) : ev (A ^^^ B) x = (ev A x ^^ ev B x) :=
  Nat.testBit_xor _ _ _

theorem ev_zero (x : Fin 6 → Bool) : ev 0 x = false := Nat.zero_testBit _

theorem ev_M : ∀ x, ev M x = true := allx (by decide +kernel)

theorem ev_vt (i : Fin 6) : ∀ x, ev (vt i) x = x i := by
  fin_cases i <;> exact allx (by decide +kernel)

def cT (b : Bool) : ℕ := if b then M else 0

def litT (j : Fin 6) (s : Bool) : ℕ := if s then vt j else M ^^^ vt j

def opT (g : Bool) (a b : ℕ) : ℕ := if g then a ||| b else a &&& b

theorem ev_cT (b : Bool) (x : Fin 6 → Bool) : ev (cT b) x = b := by
  cases b
  · exact ev_zero x
  · exact ev_M x

theorem ev_litT (j : Fin 6) (s : Bool) (x : Fin 6 → Bool) : ev (litT j s) x = litv s (x j) := by
  cases s <;> simp [litT, litv, ev_xor, ev_M, ev_vt]

theorem ev_opT (g : Bool) (A B : ℕ) (x : Fin 6 → Bool) :
    ev (opT g A B) x = bop g (ev A x) (ev B x) := by
  cases g <;> simp [opT, bop, ev_and, ev_or]

def cnd (i j : Fin 6) (g si sj b : Bool) : ℕ := M ^^^ (opT g (cT (litv si b)) (litT j sj) ^^^ vt i)

theorem ev_cnd (i j : Fin 6) (g si sj b : Bool) (z : Fin 6 → Bool) :
    ev (cnd i j g si sj b) z = !(bop g (litv si b) (litv sj (z j)) ^^ z i) := by
  simp only [cnd, ev_xor, ev_M, ev_opT, ev_cT, ev_litT, ev_vt, Bool.true_xor]

def absLo (lo : ℕ) (i j : Fin 6) (g si sj : Bool) : ℕ :=
  (cnd i j g si sj false &&& rst lo i false) ||| (cnd i j g si sj true &&& rst lo i true)

def absHi (hi : ℕ) (i j : Fin 6) (g si sj : Bool) : ℕ :=
  M ^^^ ((cnd i j g si sj false &&& (M ^^^ rst hi i false)) |||
    (cnd i j g si sj true &&& (M ^^^ rst hi i true)))

def InIv (lo hi : ℕ) (h : (Fin 6 → Bool) → Bool) : Prop :=
  ∀ x, (ev lo x = true → h x = true) ∧ (h x = true → ev hi x = true)

def Bad (lo hi : ℕ) (o : Vec) : Prop := ∀ h, InIv lo hi h → ¬ Ach o h

theorem code_dec : ∀ a < 64, code (fun k : Fin 6 => a.testBit k) = a := by decide +kernel

theorem exists_x (T : ℕ) (hT : T &&& M ≠ 0) : ∃ x, ev T x = true := by
  obtain ⟨a, ha⟩ := Nat.exists_testBit_of_ne_zero hT
  rw [Nat.testBit_and, Bool.and_eq_true] at ha
  have ha64 : a < 64 := by
    by_contra hc
    push Not at hc
    have hM : M < 2 ^ a :=
      lt_of_lt_of_le (by decide : M < 2 ^ 64) (Nat.pow_le_pow_right (by norm_num) hc)
    rw [Nat.testBit_lt_two_pow hM] at ha
    exact absurd ha.2 (by simp)
  exact ⟨fun k => a.testBit k, by unfold ev; rw [code_dec a ha64]; exact ha.1⟩

theorem InIv.rst' {lo hi : ℕ} {h : (Fin 6 → Bool) → Bool} (hI : InIv lo hi h) (i : Fin 6)
    (c : Bool) : InIv (rst lo i c) (rst hi i c) (fun x => h (upd x i c)) := fun x => by
  rw [ev_rst, ev_rst]; exact hI _

theorem InIv.abs {lo hi : ℕ} {h : (Fin 6 → Bool) → Bool} (hI : InIv lo hi h) {i j : Fin 6}
    (hji : j ≠ i) {g si sj : Bool} {ψ : DMFormula 6}
    (hψ : ∀ x, h x = ψ.eval (upd x i (bop g (litv si (x i)) (litv sj (x j))))) :
    InIv (absLo lo i j g si sj) (absHi hi i j g si sj) ψ.eval := by
  have key : ∀ z b, bop g (litv si b) (litv sj (z j)) = z i → h (upd z i b) = ψ.eval z := by
    intro z b hb
    rw [hψ]
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp [upd, hji, hb]
    · simp [upd, hk]
  intro z
  have hf : ∀ b, bop g (litv si b) (litv sj (z j)) = z i → ψ.eval z = true →
      ev hi (upd z i b) = true := fun b hb hz => (hI _).2 (by rw [key z b hb]; exact hz)
  have hl : ∀ b, bop g (litv si b) (litv sj (z j)) = z i → ev lo (upd z i b) = true →
      ψ.eval z = true := fun b hb hz => by rw [← key z b hb]; exact (hI _).1 hz
  clear key hψ
  have f0 := hf false
  have f1 := hf true
  have g0 := hl false
  have g1 := hl true
  clear hf hl
  simp only [absLo, absHi, ev_or, ev_and, ev_xor, ev_M, ev_cnd, ev_rst]
  generalize ψ.eval z = v at f0 f1 g0 g1 ⊢
  generalize ev lo (upd z i false) = l0 at f0 f1 g0 g1 ⊢
  generalize ev lo (upd z i true) = l1 at f0 f1 g0 g1 ⊢
  generalize ev hi (upd z i false) = u0 at f0 f1 g0 g1 ⊢
  generalize ev hi (upd z i true) = u1 at f0 f1 g0 g1 ⊢
  generalize bop g (litv si false) (litv sj (z j)) = p0 at f0 f1 g0 g1 ⊢
  generalize bop g (litv si true) (litv sj (z j)) = p1 at f0 f1 g0 g1 ⊢
  generalize z i = w at f0 f1 g0 g1 ⊢
  revert f0 f1 g0 g1
  cases v <;> cases l0 <;> cases l1 <;> cases u0 <;> cases u1 <;> cases p0 <;> cases p1 <;>
    cases w <;> simp

def cnd2 (i j k : Fin 6) (g g2 si sj sk b : Bool) : ℕ :=
  M ^^^ (opT g (cT (litv si b)) (opT g2 (litT j sj) (litT k sk)) ^^^ vt i)

theorem ev_cnd2 (i j k : Fin 6) (g g2 si sj sk b : Bool) (z : Fin 6 → Bool) :
    ev (cnd2 i j k g g2 si sj sk b) z =
      !(bop g (litv si b) (bop g2 (litv sj (z j)) (litv sk (z k))) ^^ z i) := by
  simp only [cnd2, ev_xor, ev_M, ev_opT, ev_cT, ev_litT, ev_vt, Bool.true_xor]

def abs2Lo (lo : ℕ) (i j k : Fin 6) (g g2 si sj sk : Bool) : ℕ :=
  (cnd2 i j k g g2 si sj sk false &&& rst lo i false) |||
    (cnd2 i j k g g2 si sj sk true &&& rst lo i true)

def abs2Hi (hi : ℕ) (i j k : Fin 6) (g g2 si sj sk : Bool) : ℕ :=
  M ^^^ ((cnd2 i j k g g2 si sj sk false &&& (M ^^^ rst hi i false)) |||
    (cnd2 i j k g g2 si sj sk true &&& (M ^^^ rst hi i true)))

theorem InIv.abs2 {lo hi : ℕ} {h : (Fin 6 → Bool) → Bool} (hI : InIv lo hi h) {i j k : Fin 6}
    (hji : j ≠ i) (hki : k ≠ i) {g g2 si sj sk : Bool} {ψ : DMFormula 6}
    (hψ : ∀ x, h x = ψ.eval (upd x i (bop g (litv si (x i))
      (bop g2 (litv sj (x j)) (litv sk (x k)))))) :
    InIv (abs2Lo lo i j k g g2 si sj sk) (abs2Hi hi i j k g g2 si sj sk) ψ.eval := by
  have key : ∀ z b, bop g (litv si b) (bop g2 (litv sj (z j)) (litv sk (z k))) = z i →
      h (upd z i b) = ψ.eval z := by
    intro z b hb
    rw [hψ]
    congr 1
    funext m
    by_cases hm : m = i
    · subst hm; simp [upd, hji, hki, hb]
    · simp [upd, hm]
  intro z
  have hf : ∀ b, bop g (litv si b) (bop g2 (litv sj (z j)) (litv sk (z k))) = z i →
      ψ.eval z = true → ev hi (upd z i b) = true :=
    fun b hb hz => (hI _).2 (by rw [key z b hb]; exact hz)
  have hl : ∀ b, bop g (litv si b) (bop g2 (litv sj (z j)) (litv sk (z k))) = z i →
      ev lo (upd z i b) = true → ψ.eval z = true :=
    fun b hb hz => by rw [← key z b hb]; exact (hI _).1 hz
  clear key hψ
  have f0 := hf false
  have f1 := hf true
  have g0 := hl false
  have g1 := hl true
  clear hf hl
  simp only [abs2Lo, abs2Hi, ev_or, ev_and, ev_xor, ev_M, ev_cnd2, ev_rst]
  generalize ψ.eval z = v at f0 f1 g0 g1 ⊢
  generalize ev lo (upd z i false) = l0 at f0 f1 g0 g1 ⊢
  generalize ev lo (upd z i true) = l1 at f0 f1 g0 g1 ⊢
  generalize ev hi (upd z i false) = u0 at f0 f1 g0 g1 ⊢
  generalize ev hi (upd z i true) = u1 at f0 f1 g0 g1 ⊢
  generalize bop g (litv si false) (bop g2 (litv sj (z j)) (litv sk (z k))) = p0 at f0 f1 g0 g1 ⊢
  generalize bop g (litv si true) (bop g2 (litv sj (z j)) (litv sk (z k))) = p1 at f0 f1 g0 g1 ⊢
  generalize z i = w at f0 f1 g0 g1 ⊢
  revert f0 f1 g0 g1
  cases v <;> cases l0 <;> cases l1 <;> cases u0 <;> cases u1 <;> cases p0 <;> cases p1 <;>
    cases w <;> simp

def F6 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

def BB : List Bool := [false, true]

theorem mem_F6 (j : Fin 6) : j ∈ F6 := by fin_cases j <;> simp [F6]

theorem mem_BB (b : Bool) : b ∈ BB := by cases b <;> simp [BB]

def nstep (o : Vec) (p : ℕ × ℕ) (i : Fin 6) : ℕ × ℕ :=
  if o i = 0 then (rst p.1 i false ||| rst p.1 i true, rst p.2 i false &&& rst p.2 i true) else p

def nrm (lo hi : ℕ) (o : Vec) : ℕ × ℕ := F6.foldl (nstep o) (lo, hi)

theorem nstep_ok {o : Vec} {h : (Fin 6 → Bool) → Bool} (hA : Ach o h) (p : ℕ × ℕ) (i : Fin 6)
    (hI : InIv p.1 p.2 h) : InIv (nstep o p i).1 (nstep o p i).2 h := by
  unfold nstep
  split_ifs with h0
  · intro x
    have e0 := hA.upd_inv i h0 x false
    have e1 := hA.upd_inv i h0 x true
    simp only [ev_or, ev_and, ev_rst, Bool.or_eq_true, Bool.and_eq_true]
    refine ⟨fun hl => ?_, fun hx => ⟨?_, ?_⟩⟩
    · rcases hl with hl | hl
      · rw [← e0]; exact (hI _).1 hl
      · rw [← e1]; exact (hI _).1 hl
    · exact (hI _).2 (by rw [e0]; exact hx)
    · exact (hI _).2 (by rw [e1]; exact hx)
  · exact hI

theorem nrm_ok {o : Vec} {h : (Fin 6 → Bool) → Bool} {lo hi : ℕ} (hA : Ach o h)
    (hI : InIv lo hi h) : InIv (nrm lo hi o).1 (nrm lo hi o).2 h := by
  unfold nrm
  suffices ∀ (l : List (Fin 6)) (p : ℕ × ℕ), InIv p.1 p.2 h →
      InIv (l.foldl (nstep o) p).1 (l.foldl (nstep o) p).2 h from this _ _ hI
  intro l
  induction l with
  | nil => intro p hp; exact hp
  | cons i l ih => intro p hp; exact ih _ (nstep_ok hA p i hp)

theorem bad_nrm {lo hi : ℕ} {o : Vec} (hb : Bad (nrm lo hi o).1 (nrm lo hi o).2 o) :
    Bad lo hi o := fun h hI hA => hb h (nrm_ok hA hI) hA

theorem bad0 {lo hi : ℕ} {o : Vec} (hz : lo &&& (M ^^^ hi) &&& M ≠ 0) : Bad lo hi o := by
  intro h hI _
  obtain ⟨x, hx⟩ := exists_x _ hz
  simp only [ev_and, ev_xor, ev_M, Bool.and_eq_true] at hx
  have h2 := (hI x).2 ((hI x).1 hx.1)
  rw [h2] at hx
  simp at hx

theorem bad1 {lo hi : ℕ} {o : Vec} (i : Fin 6) (c : Bool)
    (hb : Bad (rst lo i c) (rst hi i c) (zv o i)) : Bad lo hi o :=
  fun h hI hA => hb _ (hI.rst' i c) (hA.restrict i c)

def kids2 (lo hi : ℕ) (o : Vec) (i : Fin 6) : List (ℕ × ℕ × Vec) :=
  (lo, hi, dv o i) :: BB.flatMap (fun c => (F6.filter (fun j => decide (j ≠ i ∧ 1 ≤ o j))).map
    (fun j => (rst lo i c, rst hi i c, dv (zv o i) j)))

theorem mem_kids2 {lo hi : ℕ} {o : Vec} {i j : Fin 6} (c : Bool) (hji : j ≠ i) (hj : 1 ≤ o j) :
    (rst lo i c, rst hi i c, dv (zv o i) j) ∈ kids2 lo hi o i := by
  simp only [kids2, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact .inr ⟨c, mem_BB c, j, ⟨mem_F6 j, decide_eq_true ⟨hji, hj⟩⟩, rfl⟩

theorem bad2 {lo hi : ℕ} {o : Vec} {i : Fin 6} (h2 : 2 ≤ o i)
    (hk : ∀ k ∈ kids2 lo hi o i, Bad k.1 k.2.1 k.2.2) : Bad lo hi o := by
  intro h hI hA
  have c1 : Bad lo hi (dv o i) := hk (lo, hi, dv o i) (by simp [kids2])
  rcases hA with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · exact c1 h hI (.inl ⟨c0, hc⟩)
  · by_cases hφ : occ φ i = 0 ∨ ∃ s, φ = .lit i s
    · refine c1 h hI (.inr ⟨φ, he, fun k => ?_⟩)
      have := ho k
      have := ho i
      rcases hφ with h0 | ⟨s, rfl⟩
      · simp only [dv]; split_ifs <;> subst_vars <;> omega
      · simp only [dv, occ] at *; split_ifs at * <;> subst_vars <;> omega
    · push Not at hφ
      obtain ⟨h0, hl⟩ := hφ
      rcases kill_multi i φ (by omega) hl with ha | ⟨c, j, hji, hj, ha⟩
      · refine c1 h hI ((ha.mono (fun k => ?_)).congr he)
        have := ho k; have := ho i
        simp only [dv]; split_ifs <;> subst_vars <;> omega
      · have hk' := hk _ (mem_kids2 (lo := lo) (hi := hi) c hji (le_trans hj (ho j)))
        refine hk' _ (hI.rst' i c) ((ha.mono (fun k => ?_)).congr (fun x => he _))
        have := ho k; have := ho i; have := ho j
        simp only [dv, zv]; split_ifs <;> subst_vars <;> omega

def litin (lo hi t : ℕ) : Bool := (lo &&& (M ^^^ t) &&& M == 0) && (t &&& (M ^^^ hi) &&& M == 0)

def litok (lo hi : ℕ) (i : Fin 6) : Bool := !litin lo hi (litT i true) && !litin lo hi (litT i false)

theorem litin_of {lo hi t : ℕ} {h : (Fin 6 → Bool) → Bool} (hI : InIv lo hi h)
    (he : ∀ x, h x = ev t x) : litin lo hi t = true := by
  unfold litin
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · by_contra hne
    obtain ⟨x, hx⟩ := exists_x _ hne
    simp only [ev_and, ev_xor, ev_M, Bool.and_eq_true] at hx
    have := (hI x).1 hx.1
    rw [he] at this
    rw [this] at hx
    simp at hx
  · by_contra hne
    obtain ⟨x, hx⟩ := exists_x _ hne
    simp only [ev_and, ev_xor, ev_M, Bool.and_eq_true] at hx
    have := (hI x).2 (by rw [he]; exact hx.1)
    rw [this] at hx
    simp at hx

theorem all_F6 {P : Fin 6 → Prop} [DecidablePred P] (h : ∀ v, P v) :
    F6.all (fun v => decide (P v)) = true :=
  List.all_eq_true.2 (fun v _ => decide_eq_true (h v))

def kidsA (lo hi : ℕ) (o : Vec) (i : Fin 6) : List (ℕ × ℕ × Vec) :=
  (F6.filter (fun j => decide (j ≠ i ∧ 1 ≤ o j))).flatMap (fun j => BB.flatMap (fun g =>
    BB.flatMap (fun si => BB.map (fun sj =>
      (absLo lo i j g si sj, absHi hi i j g si sj, dv o j)))))

def kidsB (lo hi : ℕ) (o : Vec) (i : Fin 6) : List (ℕ × ℕ × Vec) :=
  F6.flatMap (fun j => (F6.filter (fun k => decide (j ≠ i ∧ k ≠ i ∧ j ≤ k) &&
      F6.all (fun v => decide (ind2 j k v ≤ o v)))).flatMap (fun k => BB.flatMap (fun g =>
    BB.flatMap (fun g2 => BB.flatMap (fun si => BB.flatMap (fun sj => BB.map (fun sk =>
      (abs2Lo lo i j k g g2 si sj sk, abs2Hi hi i j k g g2 si sj sk, sb o (ind2 j k)))))))))

def kidsC (lo hi : ℕ) (o : Vec) (i : Fin 6) : List (ℕ × ℕ × Vec) :=
  BB.flatMap (fun c => F6.flatMap (fun j => F6.flatMap (fun k => (F6.filter (fun m =>
    decide (j ≠ i ∧ k ≠ i ∧ m ≠ i ∧ j ≤ k ∧ k ≤ m) &&
      F6.all (fun v => decide (ind3 j k m v ≤ o v)))).map
      (fun m => (rst lo i c, rst hi i c, sb (zv o i) (ind3 j k m))))))

def kids3 (lo hi : ℕ) (o : Vec) (i : Fin 6) : List (ℕ × ℕ × Vec) :=
  (lo, hi, zv o i) :: (kidsA lo hi o i ++ (kidsB lo hi o i ++ kidsC lo hi o i))

theorem mem_kids3_abs {lo hi : ℕ} {o : Vec} {i j : Fin 6} (g si sj : Bool) (hji : j ≠ i)
    (hj : 1 ≤ o j) : (absLo lo i j g si sj, absHi hi i j g si sj, dv o j) ∈ kids3 lo hi o i := by
  simp only [kids3, kidsA, kidsB, kidsC, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  exact .inr (.inl ⟨j, ⟨mem_F6 j, decide_eq_true ⟨hji, hj⟩⟩, g, mem_BB g, si, mem_BB si, sj,
    mem_BB sj, rfl⟩)

theorem mem_kids3_abs2 {lo hi : ℕ} {o : Vec} {i j k : Fin 6} (g g2 si sj sk : Bool)
    (hji : j ≠ i) (hki : k ≠ i) (hjk : j ≤ k) (hv : ∀ v, ind2 j k v ≤ o v) :
    (abs2Lo lo i j k g g2 si sj sk, abs2Hi hi i j k g g2 si sj sk, sb o (ind2 j k)) ∈
      kids3 lo hi o i := by
  simp only [kids3, kidsA, kidsB, kidsC, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  exact .inr (.inr (.inl ⟨j, mem_F6 j, k, ⟨mem_F6 k, by
    rw [Bool.and_eq_true]; exact ⟨decide_eq_true ⟨hji, hki, hjk⟩, all_F6 hv⟩⟩, g, mem_BB g,
    g2, mem_BB g2, si, mem_BB si, sj, mem_BB sj, sk, mem_BB sk, rfl⟩))

theorem mem_kids3_kill {lo hi : ℕ} {o : Vec} {i j k m : Fin 6} (c : Bool) (hji : j ≠ i)
    (hki : k ≠ i) (hmi : m ≠ i) (hjk : j ≤ k) (hkm : k ≤ m) (hv : ∀ v, ind3 j k m v ≤ o v) :
    (rst lo i c, rst hi i c, sb (zv o i) (ind3 j k m)) ∈ kids3 lo hi o i := by
  simp only [kids3, kidsA, kidsB, kidsC, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  exact .inr (.inr (.inr ⟨c, mem_BB c, j, mem_F6 j, k, mem_F6 k, m, ⟨mem_F6 m, by
    rw [Bool.and_eq_true]; exact ⟨decide_eq_true ⟨hji, hki, hmi, hjk, hkm⟩, all_F6 hv⟩⟩, rfl⟩))

theorem bad3 {lo hi : ℕ} {o : Vec} {i : Fin 6} (h1 : o i = 1) (hlit : litok lo hi i = true)
    (hk : ∀ k ∈ kids3 lo hi o i, Bad k.1 k.2.1 k.2.2) : Bad lo hi o := by
  intro h hI hA
  have c1 : Bad lo hi (zv o i) := hk (lo, hi, zv o i) (by simp [kids3])
  rcases hA with ⟨c0, hc⟩ | ⟨φ, he, ho⟩
  · exact c1 h hI (.inl ⟨c0, hc⟩)
  · by_cases h0 : occ φ i = 0
    · refine c1 h hI (.inr ⟨φ, he, fun k => ?_⟩)
      have := ho k
      simp only [zv]; split_ifs <;> subst_vars <;> omega
    · have hi1 : occ φ i = 1 := by have := ho i; omega
      by_cases hl : ∃ s, φ = .lit i s
      · obtain ⟨s, rfl⟩ := hl
        have := litin_of hI (t := litT i s) (fun x => by rw [← he, eval_lit, ev_litT])
        unfold litok at hlit
        cases s <;> simp_all
      · push Not at hl
        rcases kill_single i φ hi1 hl with ⟨j, hji, hj, g, si, sj, ψ, hψo, hψe⟩ |
          ⟨j, k, hji, hki, hjk, hv, g, g2, si, sj, sk, ψ, hψo, hψe⟩ |
          ⟨c, j, k, m, hji, hki, hmi, hjk, hkm, hv, ha⟩
        · have hk' := hk _ (mem_kids3_abs (lo := lo) (hi := hi) g si sj hji (le_trans hj (ho j)))
          refine hk' _ (hI.abs hji (fun x => by rw [← he]; exact hψe x))
            (.inr ⟨ψ, fun _ => rfl, fun m => ?_⟩)
          have h3 := hψo m
          have := ho m; have := ho j
          simp only [dv] at h3 ⊢
          split_ifs at h3 ⊢ <;> subst_vars <;> omega
        · have hk' := hk _ (mem_kids3_abs2 (lo := lo) (hi := hi) g g2 si sj sk hji hki hjk
            (fun v => le_trans (hv v) (ho v)))
          refine hk' _ (hI.abs2 hji hki (fun x => by rw [← he]; exact hψe x))
            (.inr ⟨ψ, fun _ => rfl, fun m => ?_⟩)
          have h3 := hψo m
          have := ho m
          simp only [sb] at h3 ⊢
          omega
        · have hk' := hk _ (mem_kids3_kill (lo := lo) (hi := hi) c hji hki hmi hjk hkm
            (fun v => le_trans (hv v) (ho v)))
          refine hk' _ (hI.rst' i c) ((ha.mono (fun w => ?_)).congr (fun x => he _))
          have := ho w
          simp only [sb, zv]
          split_ifs <;> omega

def chkAll (f : ℕ → ℕ → Vec → ℕ → Option ℕ) : List (ℕ × ℕ × Vec) → ℕ → Option ℕ
  | [], r => some r
  | k :: ks, r => (f k.1 k.2.1 k.2.2 r).bind (chkAll f ks)

theorem chkAll_ok (f : ℕ → ℕ → Vec → ℕ → Option ℕ) : ∀ (ks : List (ℕ × ℕ × Vec)) (r r' : ℕ),
    chkAll f ks r = some r' → ∀ k ∈ ks, ∃ r1 r2, f k.1 k.2.1 k.2.2 r1 = some r2
  | [], _, _, _ => by simp
  | k :: ks, r, r', h => by
    simp only [chkAll, Option.bind_eq_some_iff] at h
    obtain ⟨r1, h1, h2⟩ := h
    intro k' hk'
    rcases List.mem_cons.1 hk' with rfl | hk'
    · exact ⟨r, r1, h1⟩
    · exact chkAll_ok f ks r1 r' h2 k' hk'

def chk : ℕ → ℕ → ℕ → Vec → ℕ → Option ℕ
  | 0, _, _, _, _ => none
  | n + 1, lo0, hi0, o, cert =>
    if cert % 8 = 0 then
      (if (nrm lo0 hi0 o).1 &&& (M ^^^ (nrm lo0 hi0 o).2) &&& M ≠ 0 then some (cert / 8) else none)
    else if hi6 : cert / 8 % 8 < 6 then
      (if cert % 8 = 1 then
        chk n (rst (nrm lo0 hi0 o).1 ⟨cert / 8 % 8, hi6⟩ (cert / 8 / 8 % 8 == 1))
          (rst (nrm lo0 hi0 o).2 ⟨cert / 8 % 8, hi6⟩ (cert / 8 / 8 % 8 == 1))
          (zv o ⟨cert / 8 % 8, hi6⟩) (cert / 8 / 8 / 8)
      else if cert % 8 = 2 then
        (if 2 ≤ o ⟨cert / 8 % 8, hi6⟩ then
          chkAll (chk n) (kids2 (nrm lo0 hi0 o).1 (nrm lo0 hi0 o).2 o ⟨cert / 8 % 8, hi6⟩)
            (cert / 8 / 8)
        else none)
      else if cert % 8 = 3 then
        (if o ⟨cert / 8 % 8, hi6⟩ = 1 ∧
            litok (nrm lo0 hi0 o).1 (nrm lo0 hi0 o).2 ⟨cert / 8 % 8, hi6⟩ = true then
          chkAll (chk n) (kids3 (nrm lo0 hi0 o).1 (nrm lo0 hi0 o).2 o ⟨cert / 8 % 8, hi6⟩)
            (cert / 8 / 8)
        else none)
      else none)
    else none

theorem chk_ok : ∀ (n lo hi : ℕ) (o : Vec) (cert r : ℕ), chk n lo hi o cert = some r → Bad lo hi o
  | 0, _, _, _, _, _, h => by simp [chk] at h
  | n + 1, lo, hi, o, cert, r, h => by
    apply bad_nrm
    have IH : ∀ ks : List (ℕ × ℕ × Vec), ∀ r1 r2, chkAll (chk n) ks r1 = some r2 →
        ∀ k ∈ ks, Bad k.1 k.2.1 k.2.2 := fun ks r1 r2 e k hk => by
      obtain ⟨_, _, e'⟩ := chkAll_ok _ ks r1 r2 e k hk
      exact chk_ok n _ _ _ _ _ e'
    simp only [chk] at h
    split_ifs at h with t0 z hi6 t1 t2 h2 t3 h3
    · exact bad0 z
    · exact bad1 _ _ (chk_ok n _ _ _ _ _ h)
    · exact bad2 h2 (IH _ _ _ h)
    · exact bad3 h3.1 h3.2 (IH _ _ _ h)

def fT : ℕ := 18446738485953493192

def certN : ℕ :=
  275287989483734239832266670825656184758046371594916435637790126372704525956425680903859866901448615053027571033738970954044638527710143405776445393641651082451421355454451167750321584265601204357641593314453995558989201159727074793903511949597021757746630646708652270008058703501591600853901499638011831765736968556741218496735513802651772690128980555396340487994225222875277342507353610267466873480435263233119555833935077438051351993721688086059053137464827706908647362273751230499670124709455072358182480134886768139617157097670849316939799029386568453150514091071264559454876444102756402012393544167983078704641629983704008920060497826290360007510070080381586870287775685583170082730791942485980952170764675118840938431815552315292333264685852242233312208178653503101879202869082170205755320145629602804882196361343817154131563764282025892350518792321504578600038069189012841872596304093670967906046538189383084191398394316066596335821848007932027300832224410005960779016549689090510347710246957133253666590888152013189239501240856856419740877860257280594814446126604735571488381477605837094255242115518479005284152163324431863969001472380272197422666057446446485166440331822892165778983341929842135749055802959855419883546573541367951152499026661744909587758599427038079335174534108328390462764310841025301522854467592947749539319309983538609499256253124289877805304202013996792720252518848416374376293983626471252226225505070249656117878524953177947136940337877351359519501079542871618879660265736961568453868131369478794367031976087096866570163342212313293601994572779451323108941956072962286360506339409570051185594214577585036343729451002493284472868546064349535988524873360724754763215642651238199729994418207268699587560721313606498270582797695466067094417994030561663001562220202426009433841264177135514496692099670599938392594411011711665152949195594261879072966402750209660942397111319904672182262214542351173871788704626073049216101532867399204810059777057870811212710101500735266627252860984500674011689398186169576188269061709603469911782448952066995174013788014191603626749927401511916059366465297067990155933256325001097334739822124314700973743220383979793014989065219395748628423168110315565935307149918844394980514342436242110813036406927282341171340336969952339332019656264870409258262272550831580998557064378680221336307739386078614737930833537703196210953570401345659552426064920888713880965723922825826882193718323163250468274981712618750095888717390450453495205254268930567350162553577329562746715497176798445053281583394579145185008532209687295324070183374528727883671334126569940608259493674201374376149168496197675155669490192410836636607754729112933686410866932178072438146366388239097882394483062673317265884641132866129701621397761475115633564689239779749605367708044620646641246268810687196247128792492259982906881839277198869915696279713790434210719620966819563158626359448495867851702425288235122456810741875792736649506928286760813638158029657365715224680855780905479365113511889911912968881929811881580882710418948705353547275444602868541897962414128432493063793131333839926457911454511415678063437268786665194694210347559322984372497265173998239508483477333773743034697275346539742133655572993889522264625514923934117812429330247198479491651955259757663023652265841899391609188419950477651863383443206046638114088566592275852040053341083522636140248991000630121313525837624662470626979177013813249216412993478406524381443912651922514315624548813006038132423880631262463409698200854068630044116494463049969385702492205656496167195794988911849285160662375935097334065807821539533721880042525049553559891159804469572041045090146627223765899135028806661109838595738934161596173018184883186272775783026970549197212396977724090729486381199301235956407032307701169420728773020878257721173131469376035704068594945106789024319438687670690636152629809515002927655103948997198855922174949934743298934053067228046611804926615093196512028211607054435718144588361686576483560290816382332964449679407403951263482886580885171112310605524941725268918461939091381708517930075159588932023340968064822599574933943166338411690930615799465134792487096290483953003433191517284271838018726838509650005421033976475819795992651741064886987740900386978684160982796932262291258739859660334662327826804856751561419797068039308963180119687825485672666505914323468718735555284024589719796559081894623343553235679614088413754684448536468829910607123244670794398818588748836020278649834331541286232028475267033228043071664308806048067886759238782945517490484403305123335619999940067048654737398747415988789320538606971054754662841035645779587931273286859523132784658900755636092924815191442788171773144279831668331401729

def topsL : List (List ℕ) :=
  [[1, 1, 1, 1, 1, 3], [1, 1, 1, 1, 2, 2], [1, 1, 1, 1, 3, 1], [1, 1, 1, 2, 1, 2], [1, 1, 1, 2, 2, 1], [1, 1, 1, 3, 1, 1], [1, 1, 2, 1, 1, 2], [1, 1, 2, 1, 2, 1], [1, 1, 2, 2, 1, 1], [1, 1, 3, 1, 1, 1], [1, 2, 1, 1, 1, 2], [1, 2, 1, 1, 2, 1], [1, 2, 1, 2, 1, 1], [1, 2, 2, 1, 1, 1], [1, 3, 1, 1, 1, 1], [2, 1, 1, 1, 1, 2], [2, 1, 1, 1, 2, 1], [2, 1, 1, 2, 1, 1], [2, 1, 2, 1, 1, 1], [2, 2, 1, 1, 1, 1], [3, 1, 1, 1, 1, 1]]

def vecOf (l : List ℕ) : Vec := fun k => l.getD (k : ℕ) 0

theorem tops_run :
    chkAll (chk 20) (topsL.map (fun l => (fT, fT, vecOf l))) certN = some 0 := by
  decide +kernel

theorem tops_bad : ∀ l ∈ topsL, Bad fT fT (vecOf l) := by
  intro l hl
  obtain ⟨_, _, e⟩ := chkAll_ok _ _ _ _ tops_run (fT, fT, vecOf l) (List.mem_map.2 ⟨l, hl, rfl⟩)
  exact chk_ok _ _ _ _ _ _ e

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tops_cover : ∀ a < 4, ∀ b < 4, ∀ c < 4, ∀ d < 4, ∀ e < 4, ∀ f < 4,
    ¬ (1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ 1 ≤ d ∧ 1 ≤ e ∧ 1 ≤ f ∧ a + b + c + d + e + f = 8) ∨
    [a, b, c, d, e, f] ∈ topsL := by
  decide +kernel

def fn (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 0 && x 5)

theorem ev_fT : ∀ x, ev fT x = fn x := allx (by decide +kernel)

def up : DMFormula 6 :=
  .or (.and (.lit 0 true) (.or (.lit 1 true) (.lit 5 true)))
    (.or (.and (.lit 2 true) (.or (.lit 1 true) (.lit 3 true)))
      (.and (.lit 4 true) (.or (.lit 3 true) (.lit 5 true))))

theorem up_leaves : up.leaves = 9 := by decide

theorem up_eval : ∀ x, up.eval x = fn x := allx (by decide +kernel)

theorem dep (k : Fin 6) : ∃ x c, fn (upd x k c) ≠ fn x := by
  fin_cases k
  · exact ⟨![false, true, false, false, false, false], true, by decide⟩
  · exact ⟨![true, false, false, false, false, false], true, by decide⟩
  · exact ⟨![false, true, false, false, false, false], true, by decide⟩
  · exact ⟨![false, false, true, false, false, false], true, by decide⟩
  · exact ⟨![false, false, false, true, false, false], true, by decide⟩
  · exact ⟨![true, false, false, false, false, false], true, by decide⟩

theorem lower (φ : DMFormula 6) (hl : φ.leaves ≤ 8) (he : ∀ x, φ.eval x = fn x) : False := by
  have hpos : ∀ k, 1 ≤ occ φ k := by
    intro k
    by_contra hk
    obtain ⟨x, c, hx⟩ := dep k
    apply hx
    rw [← he, ← he, eval_upd_of_zero φ k (by omega)]
  rw [leaves_eq, Fin.sum_univ_six] at hl
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  have h3 := hpos 3
  have h4 := hpos 4
  have h5 := hpos 5
  have mem := tops_cover (8 - (occ φ 1 + occ φ 2 + occ φ 3 + occ φ 4 + occ φ 5)) (by omega)
    (occ φ 1) (by omega) (occ φ 2) (by omega) (occ φ 3) (by omega) (occ φ 4) (by omega)
    (occ φ 5) (by omega) |>.resolve_left (not_not.2 ⟨by omega, h1, h2, h3, h4, h5, by omega⟩)
  refine tops_bad _ mem fn (fun x => by rw [ev_fT]; exact ⟨id, id⟩) (.inr ⟨φ, he, fun k => ?_⟩)
  fin_cases k
  · show occ φ 0 ≤ 8 - (occ φ 1 + occ φ 2 + occ φ 3 + occ φ 4 + occ φ 5); omega
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

end PEqualNP.Outside.L_meta_183

theorem PEqualNP.Outside.L_meta_183 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 0 && x 5)) s ↔ 9 ≤ s := by
  intro s
  unfold PEqualNP.MetaComplexity.HasLeafSize
  constructor
  · rintro ⟨φ, hl, he⟩
    by_contra hs
    exact PEqualNP.Outside.L_meta_183.lower φ (by omega) he
  · intro hs
    exact ⟨PEqualNP.Outside.L_meta_183.up,
      by rw [PEqualNP.Outside.L_meta_183.up_leaves]; exact hs,
      PEqualNP.Outside.L_meta_183.up_eval⟩
