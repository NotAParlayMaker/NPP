import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Image
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push

namespace PEqualNP.Outside.L_meta_3763

/-!
## Projective plane combinatorics
-/

private lemma line_card_filter {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1) (l : Fin N) :
    (Finset.univ.filter (fun p : Fin N => I p l)).card = q + 1 := by
  have h := hline l
  rw [Fintype.card_subtype] at h
  exact h

private lemma point_card_filter {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (p : Fin N) :
    (Finset.univ.filter (fun l : Fin N => I p l)).card = q + 1 := by
  let S : Finset (Fin N × Fin N) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun x => x.1 ≠ p ∧ I p x.2 ∧ I x.1 x.2)
  have hS1 : S.card = N - 1 := by
    have hbij : S.card = (Finset.univ.erase p).card := by
      refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
      · intro x hx
        simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hx
        exact Finset.mem_erase.mpr ⟨hx.1, Finset.mem_univ _⟩
      · intro x hx y hy hxy
        simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hx hy
        have hpr : p ≠ x.1 := Ne.symm hx.1
        obtain ⟨l, _, hl⟩ := huniq p x.1 hpr
        have hx2 : x.2 = l := hl x.2 hx.2
        have hy2 : y.2 = l := hl y.2 (by rw [hxy]; exact hy.2)
        exact Prod.ext hxy (hx2.trans hy2.symm)
      · intro r hr
        have hrp : r ≠ p := (Finset.mem_erase.mp hr).1
        obtain ⟨l, ⟨hpl, hrl⟩, _⟩ := huniq p r (Ne.symm hrp)
        exact ⟨(r, l), by simp [S, hrp, hpl, hrl], rfl⟩
    rw [hbij, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
  have hS2 : S.card = (Finset.univ.filter (fun l : Fin N => I p l)).card * q := by
    have hfib : S.card =
        ∑ l ∈ Finset.univ.filter (fun l : Fin N => I p l),
          (S.filter (fun x => x.2 = l)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext ⟨r, l⟩
        simp only [S, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
          true_and]
        constructor
        · intro h
          exact ⟨l, h.2.1, h, rfl⟩
        · rintro ⟨l', _, h, rfl⟩
          exact h
      · intro l1 _ l2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_filter] at hx1 hx2
        exact hne (hx1.2.symm.trans hx2.2)
    rw [hfib]
    have hterm : ∀ l ∈ Finset.univ.filter (fun l : Fin N => I p l),
        (S.filter (fun x => x.2 = l)).card = q := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      have hbij : (S.filter (fun x => x.2 = l)).card =
          ((Finset.univ.filter (fun r : Fin N => I r l)).erase p).card := by
        refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
        · intro x hx
          simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hx
          exact Finset.mem_erase.mpr ⟨hx.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2 ▸ hx.1.2.2⟩⟩
        · intro x hx y hy hxy
          simp only [Finset.mem_filter] at hx hy
          exact Prod.ext hxy (hx.2.trans hy.2.symm)
        · intro r hr
          rcases Finset.mem_erase.mp hr with ⟨hrp, hrl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrl
          exact ⟨(r, l), by simp [S, hrp, hl, hrl], rfl⟩
      rw [hbij,
        Finset.card_erase_of_mem (s := Finset.univ.filter (fun r : Fin N => I r l)) (a := p)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩),
        line_card_filter hline l]
      omega
    rw [Finset.sum_const_nat hterm]
  have heq : (Finset.univ.filter (fun l : Fin N => I p l)).card * q = (q + 1) * q := by
    have : N - 1 = (q + 1) * q := by
      rw [hN]
      simp only [Nat.add_sub_cancel]
      ring
    omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) heq

private lemma exists_line_not_through {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    {p r : Fin N} (hpr : p ≠ r) :
    ∃ l : Fin N, I p l ∧ ¬ I r l := by
  obtain ⟨l0, _, hl0⟩ := huniq p r hpr
  have hcard : (Finset.univ.filter (fun l : Fin N => I p l)).card = q + 1 :=
    point_card_filter hq hN hline huniq p
  have hne : ((Finset.univ.filter (fun l : Fin N => I p l)).erase l0).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hle := Finset.card_erase_le (s := Finset.univ.filter (fun l : Fin N => I p l)) (a := l0)
    have hsub : (Finset.univ.filter (fun l : Fin N => I p l)).card - 1 ≤
        ((Finset.univ.filter (fun l : Fin N => I p l)).erase l0).card :=
      Finset.pred_card_le_card_erase
    rw [hemp, Finset.card_empty, hcard] at hsub
    omega
  obtain ⟨l, hl⟩ := hne
  rcases Finset.mem_erase.mp hl with ⟨hlne, hlp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlp
  refine ⟨l, hlp, fun hrl => hlne (hl0 l ⟨hlp, hrl⟩)⟩

private lemma exists_point_ne {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (l r : Fin N) : ∃ p : Fin N, I p l ∧ p ≠ r := by
  have hcard := line_card_filter hline l
  have hsub : (Finset.univ.filter (fun p : Fin N => I p l)).card - 1 ≤
      ((Finset.univ.filter (fun p : Fin N => I p l)).erase r).card :=
    Finset.pred_card_le_card_erase
  have hpos : 0 < ((Finset.univ.filter (fun p : Fin N => I p l)).erase r).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_erase.mp hp with ⟨hpr, hpl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpl
  exact ⟨p, hpl, hpr⟩

private lemma exists_point_not_on {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    {l l' : Fin N} (hll' : l ≠ l') :
    ∃ p : Fin N, I p l ∧ ¬ I p l' := by
  by_contra hall
  push Not at hall
  have hcard := line_card_filter hline l
  have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p l)).card := by omega
  obtain ⟨p1, hp1⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1
  obtain ⟨p2, hp2, hp21⟩ := exists_point_ne hq hline l p1
  obtain ⟨l0, _, hl0⟩ := huniq p1 p2 (Ne.symm hp21)
  have h1 : l = l0 := hl0 l ⟨hp1, hp2⟩
  have h2 : l' = l0 := hl0 l' ⟨hall p1 hp1, hall p2 hp2⟩
  exact hll' (h1.trans h2.symm)

private lemma exists_line_through {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (p : Fin N) : ∃ l : Fin N, I p l := by
  have hcard := point_card_filter hq hN hline huniq p
  have hpos : 0 < (Finset.univ.filter (fun l : Fin N => I p l)).card := by omega
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  exact ⟨l, hl⟩

private lemma exists_point_on {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (l : Fin N) : ∃ p : Fin N, I p l := by
  have hcard := line_card_filter hline l
  have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p l)).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  exact ⟨p, hp⟩

private lemma indep_card_le {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (PB LB : Finset (Fin N)) (hind : ∀ p ∈ PB, ∀ l ∈ LB, ¬ I p l) :
    PB.card + LB.card ≤ N := by
  let E : Finset (Fin N × Fin N) :=
    (PB ×ˢ (Finset.univ \ LB)).filter (fun x => I x.1 x.2)
  have hE1 : E.card = PB.card * (q + 1) := by
    have hfib : E.card = ∑ p ∈ PB, (E.filter (fun x => x.1 = p)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext ⟨p, l⟩
        simp only [E, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]
        constructor
        · intro h
          exact ⟨p, h.1.1, h, rfl⟩
        · rintro ⟨p', _, h, rfl⟩
          exact h
      · intro p1 _ p2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_filter] at hx1 hx2
        exact hne (hx1.2.symm.trans hx2.2)
    rw [hfib]
    have hterm : ∀ p ∈ PB, (E.filter (fun x => x.1 = p)).card = q + 1 := by
      intro p hp
      have hbij : (E.filter (fun x => x.1 = p)).card =
          (Finset.univ.filter (fun l : Fin N => I p l)).card := by
        refine Finset.card_bij (fun x _ => x.2) ?_ ?_ ?_
        · intro x hx
          simp only [E, Finset.mem_filter, Finset.mem_product] at hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2 ▸ hx.1.2⟩
        · intro x hx y hy hxy
          simp only [Finset.mem_filter] at hx hy
          exact Prod.ext (hx.2.trans hy.2.symm) hxy
        · intro l hl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
          have hlLB : l ∉ LB := fun hmem => hind p hp l hmem hl
          exact ⟨(p, l), by simp [E, hp, hlLB, hl], rfl⟩
      rw [hbij]
      exact point_card_filter hq hN hline huniq p
    rw [Finset.sum_const_nat hterm]
  have hE2 : E.card ≤ (Finset.univ \ LB).card * (q + 1) := by
    have hfib : E.card = ∑ l ∈ Finset.univ \ LB, (E.filter (fun x => x.2 = l)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext ⟨p, l⟩
        simp only [E, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]
        constructor
        · intro h
          exact ⟨l, h.1.2, h, rfl⟩
        · rintro ⟨l', _, h, rfl⟩
          exact h
      · intro l1 _ l2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_filter] at hx1 hx2
        exact hne (hx1.2.symm.trans hx2.2)
    rw [hfib]
    have hterm : ∀ l ∈ Finset.univ \ LB, (E.filter (fun x => x.2 = l)).card ≤ q + 1 := by
      intro l _
      have hinj : (E.filter (fun x => x.2 = l)).card ≤
          (Finset.univ.filter (fun p : Fin N => I p l)).card := by
        refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
        · intro x hx
          simp only [Finset.mem_coe, E, Finset.mem_filter, Finset.mem_product] at hx
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2 ▸ hx.1.2⟩
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
          exact Prod.ext hxy (hx.2.trans hy.2.symm)
      rw [line_card_filter hline l] at hinj
      exact hinj
    calc
      ∑ l ∈ Finset.univ \ LB, (E.filter (fun x => x.2 = l)).card
          ≤ ∑ _l ∈ Finset.univ \ LB, (q + 1) := Finset.sum_le_sum hterm
      _ = (Finset.univ \ LB).card * (q + 1) := Finset.sum_const_nat (fun _ _ => rfl)
  have hle : PB.card ≤ (Finset.univ \ LB).card :=
    Nat.le_of_mul_le_mul_right (hE1 ▸ hE2) (by omega)
  have hcomp : (Finset.univ \ LB).card = N - LB.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hLB : LB.card ≤ N := by
    simpa [Fintype.card_fin] using Finset.card_le_univ LB
  omega

/-!
## Monotone Boolean circuit evaluator and semantics
-/

private def ceval (N : ℕ) (kind a b : ℕ → ℕ) (x : ℕ → Bool) : ℕ → Bool
  | w =>
    if h : w < 2 * N ∨ w = 0 then x w
    else
      let j := w - 2 * N
      let k := kind j
      if k = 0 then
        ceval N kind a b x (min (a j) (w - 1)) && ceval N kind a b x (min (b j) (w - 1))
      else if k = 1 then
        ceval N kind a b x (min (a j) (w - 1)) || ceval N kind a b x (min (b j) (w - 1))
      else if k = 2 then
        ceval N kind a b x (min (a j) (w - 1))
      else if k = 3 then
        false
      else
        true

private lemma ceval_input (N : ℕ) (kind a b : ℕ → ℕ) (x : ℕ → Bool) {w : ℕ}
    (hw : w < 2 * N) : ceval N kind a b x w = x w := by
  rw [ceval]
  simp [hw]

private lemma ceval_gate_and (N : ℕ) (kind a b : ℕ → ℕ) (x : ℕ → Bool) {j : ℕ}
    (hN : 0 < N) (ha : a j < 2 * N + j) (hb : b j < 2 * N + j) (hk : kind j = 0) :
    ceval N kind a b x (2 * N + j) =
      (ceval N kind a b x (a j) && ceval N kind a b x (b j)) := by
  rw [ceval]
  have hN0 : N ≠ 0 := by omega
  have h2 : 2 * N + j - 2 * N = j := by omega
  have h3 : min (a j) (2 * N + j - 1) = a j := by omega
  have h4 : min (b j) (2 * N + j - 1) = b j := by omega
  simp [hN0, h2, hk, h3, h4]

private lemma ceval_gate_or (N : ℕ) (kind a b : ℕ → ℕ) (x : ℕ → Bool) {j : ℕ}
    (hN : 0 < N) (ha : a j < 2 * N + j) (hb : b j < 2 * N + j) (hk : kind j = 1) :
    ceval N kind a b x (2 * N + j) =
      (ceval N kind a b x (a j) || ceval N kind a b x (b j)) := by
  rw [ceval]
  have hN0 : N ≠ 0 := by omega
  have h2 : 2 * N + j - 2 * N = j := by omega
  have h3 : min (a j) (2 * N + j - 1) = a j := by omega
  have h4 : min (b j) (2 * N + j - 1) = b j := by omega
  simp [hN0, h2, hk, h3, h4]

private lemma ceval_gate_copy (N : ℕ) (kind a b : ℕ → ℕ) (x : ℕ → Bool) {j : ℕ}
    (hN : 0 < N) (ha : a j < 2 * N + j) (hk : kind j = 2) :
    ceval N kind a b x (2 * N + j) = ceval N kind a b x (a j) := by
  rw [ceval]
  have hN0 : N ≠ 0 := by omega
  have h2 : 2 * N + j - 2 * N = j := by omega
  have h3 : min (a j) (2 * N + j - 1) = a j := by omega
  simp [hN0, h2, hk, h3]

private lemma ceval_gate_false (N : ℕ) (kind a b : ℕ → ℕ) (x : ℕ → Bool) {j : ℕ}
    (hN : 0 < N) (hk : kind j = 3) :
    ceval N kind a b x (2 * N + j) = false := by
  rw [ceval]
  have hN0 : N ≠ 0 := by omega
  have h2 : 2 * N + j - 2 * N = j := by omega
  simp [hN0, h2, hk]

private lemma ceval_gate_true (N : ℕ) (kind a b : ℕ → ℕ) (x : ℕ → Bool) {j : ℕ}
    (hN : 0 < N) (hk : kind j = 4) :
    ceval N kind a b x (2 * N + j) = true := by
  rw [ceval]
  have hN0 : N ≠ 0 := by omega
  have h2 : 2 * N + j - 2 * N = j := by omega
  simp [hN0, h2, hk]

private lemma ceval_mono (N : ℕ) (kind a b : ℕ → ℕ) {x y : ℕ → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, ceval N kind a b x w = true → ceval N kind a b y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hx
    rw [ceval] at hx ⊢
    by_cases h0 : w < 2 * N ∨ w = 0
    · simp only [h0, ↓reduceDIte] at hx ⊢
      exact hxy w hx
    · simp only [h0, ↓reduceDIte] at hx ⊢
      split_ifs at hx ⊢
      · simp only [Bool.and_eq_true] at hx ⊢
        exact ⟨ih _ (by omega) hx.1, ih _ (by omega) hx.2⟩
      · simp only [Bool.or_eq_true] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (ih _ (by omega) hx)
        · exact Or.inr (ih _ (by omega) hx)
      · exact ih _ (by omega) hx
      · exact hx

private def xT (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (T : Finset (Fin N)) (v : ℕ) : Bool :=
  if h1 : v < N then
    decide (∀ l ∈ T, ¬ I ⟨v, h1⟩ l)
  else if h2 : v < 2 * N then
    decide ((⟨v - N, by omega⟩ : Fin N) ∈ T)
  else
    false

private def ValidCirc (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s o : ℕ) (kind a b : ℕ → ℕ) : Prop :=
  o < 2 * N + s ∧
  (∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j ∧ kind j ≤ 4) ∧
  (∀ (x : ℕ → Bool) (p l : Fin N), I p l → x p.val = true → x (N + l.val) = true →
    ceval N kind a b x o = true) ∧
  (∀ (T : Finset (Fin N)), T.card ≤ q →
    ceval N kind a b (xT N I T) o = false)

private lemma ceval_false_of_le_xT {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    {s o : ℕ} {kind a b : ℕ → ℕ}
    (hv : ValidCirc q N I s o kind a b)
    (T : Finset (Fin N)) (hT : T.card ≤ q)
    {x : ℕ → Bool} (hx : ∀ i, x i = true → xT N I T i = true) :
    ceval N kind a b x o = false := by
  cases h : ceval N kind a b x o
  · rfl
  · have h1 := ceval_mono N kind a b hx o h
    have h2 := hv.2.2.2 T hT
    rw [h1] at h2
    exact Bool.noConfusion h2

private lemma ceval_all_false {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    {s o : ℕ} {kind a b : ℕ → ℕ}
    (hv : ValidCirc q N I s o kind a b) :
    ceval N kind a b (fun _ => false) o = false :=
  ceval_false_of_le_xT hv ∅ (by simp) (by intro _ h; exact Bool.noConfusion h)

private lemma ceval_all_true {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    {s o : ℕ} {kind a b : ℕ → ℕ}
    (hv : ValidCirc q N I s o kind a b) :
    ceval N kind a b (fun _ => true) o = true := by
  have hNpos : 0 < N := by rw [hN]; nlinarith
  let l0 : Fin N := ⟨0, hNpos⟩
  obtain ⟨p0, hp0⟩ := exists_point_on hq hline l0
  exact hv.2.2.1 (fun _ => true) p0 l0 hp0 rfl rfl

private lemma ceval_single_false {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) {s o : ℕ} {kind a b : ℕ → ℕ}
    (hv : ValidCirc q N I s o kind a b)
    {v : ℕ} (hv2 : v < 2 * N) :
    ceval N kind a b (fun u => decide (u = v)) o = false := by
  by_cases h1 : v < N
  · refine ceval_false_of_le_xT hv ∅ (by simp) ?_
    intro i hi
    simp only [decide_eq_true_eq] at hi
    subst hi
    simp [xT, h1]
  · let l : Fin N := ⟨v - N, by omega⟩
    refine ceval_false_of_le_xT hv {l} (by simp; omega) ?_
    intro i hi
    simp only [decide_eq_true_eq] at hi
    subst hi
    simp [xT, h1, hv2, l]

/-!
## Pair sensitivity (P4)
-/

private lemma pair_sens {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    {s o : ℕ} {kind a b : ℕ → ℕ}
    (hv : ValidCirc q N I s o kind a b)
    {i j : ℕ} (hi : i < 2 * N) (hj : j < 2 * N) (hij : i ≠ j) :
    ∃ x y : ℕ → Bool,
      (∀ u, u ≠ i → x u = y u) ∧
      x j = true ∧ y j = true ∧
      ceval N kind a b x o = false ∧ ceval N kind a b y o = true := by
  by_cases hiN : i < N
  · by_cases hjN : j < N
    · let p : Fin N := ⟨i, hiN⟩
      let r : Fin N := ⟨j, hjN⟩
      have hpr : p ≠ r := fun h => hij (congrArg Fin.val h)
      obtain ⟨l, hpl, hrl⟩ := exists_line_not_through hq hN hline huniq hpr
      let x : ℕ → Bool := fun u => decide (u = j ∨ u = N + l.val)
      let y : ℕ → Bool := fun u => decide (u = i ∨ u = j ∨ u = N + l.val)
      refine ⟨x, y, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hui
        simp [x, y, hui]
      · simp [x]
      · simp [y]
      · refine ceval_false_of_le_xT hv {l} (by simp; omega) ?_
        intro u hu
        simp only [x, decide_eq_true_eq] at hu
        rcases hu with rfl | rfl
        · simp [xT, hjN, r, hrl]
        · have hlt1 : ¬ (N + l.val < N) := by omega
          have hlt2 : N + l.val < 2 * N := by omega
          simp [xT, hlt1, hlt2]
      · exact hv.2.2.1 y p l hpl (by simp [y, p]) (by simp [y])
    · let p : Fin N := ⟨i, hiN⟩
      let l' : Fin N := ⟨j - N, by omega⟩
      obtain ⟨l, hpl⟩ := exists_line_through hq hN hline huniq p
      let T : Finset (Fin N) := {l', l}
      have hT : T.card ≤ q := by
        have hle : T.card ≤ 2 := Finset.card_le_two
        omega
      let x : ℕ → Bool := fun u => decide (u = N + l'.val ∨ u = N + l.val)
      let y : ℕ → Bool := fun u => decide (u = i ∨ u = N + l'.val ∨ u = N + l.val)
      have hj_eq : j = N + l'.val := by simp [l']; omega
      refine ⟨x, y, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hui
        simp [x, y, hui]
      · simp [x, hj_eq]
      · simp [y, hj_eq]
      · refine ceval_false_of_le_xT hv T hT ?_
        intro u hu
        simp only [x, decide_eq_true_eq] at hu
        rcases hu with rfl | rfl
        · have hlt1 : ¬ (N + l'.val < N) := by omega
          have hlt2 : N + l'.val < 2 * N := by omega
          simp [xT, hlt1, hlt2, T]
        · have hlt1 : ¬ (N + l.val < N) := by omega
          have hlt2 : N + l.val < 2 * N := by omega
          simp [xT, hlt1, hlt2, T]
      · exact hv.2.2.1 y p l hpl (by simp [y, p]) (by simp [y])
  · by_cases hjN : j < N
    · let l : Fin N := ⟨i - N, by omega⟩
      obtain ⟨p, hpl⟩ := exists_point_on hq hline l
      let x : ℕ → Bool := fun u => decide (u = p.val ∨ u = j)
      let y : ℕ → Bool := fun u => decide (u = i ∨ u = p.val ∨ u = j)
      have hi_eq : i = N + l.val := by simp [l]; omega
      refine ⟨x, y, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hui
        simp [x, y, hui]
      · simp [x]
      · simp [y]
      · refine ceval_false_of_le_xT hv ∅ (by simp) ?_
        intro u hu
        simp only [x, decide_eq_true_eq] at hu
        rcases hu with rfl | rfl
        · simp [xT, p.isLt]
        · simp [xT, hjN]
      · exact hv.2.2.1 y p l hpl (by simp [y]) (by simp [y, hi_eq])
    · let l : Fin N := ⟨i - N, by omega⟩
      let l' : Fin N := ⟨j - N, by omega⟩
      have hll' : l ≠ l' := by
        intro h
        have hv' : l.val = l'.val := congrArg Fin.val h
        simp only [l, l'] at hv'
        omega
      obtain ⟨p, hpl, hpl'⟩ := exists_point_not_on hq hline huniq hll'
      let x : ℕ → Bool := fun u => decide (u = p.val ∨ u = j)
      let y : ℕ → Bool := fun u => decide (u = i ∨ u = p.val ∨ u = j)
      have hi_eq : i = N + l.val := by simp [l]; omega
      have hj_eq : j = N + l'.val := by simp [l']; omega
      refine ⟨x, y, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hui
        simp [x, y, hui]
      · simp [x]
      · simp [y]
      · refine ceval_false_of_le_xT hv {l'} (by simp; omega) ?_
        intro u hu
        simp only [x, decide_eq_true_eq] at hu
        rcases hu with hu1 | hu2
        · rw [hu1]; simp [xT, p.isLt, hpl']
        · rw [hu2]; simp [xT, hjN, hj, l']
      · exact hv.2.2.1 y p l hpl (by simp [y]) (by simp [y, hi_eq])

/-!
## Fanout and circuit cleanup (C1, C2, C3)
-/

private def fanout (s o : ℕ) (a b : ℕ → ℕ) (w : ℕ) : ℕ :=
  (if w = o then 1 else 0) +
  ∑ j ∈ Finset.range s, ((if a j = w then 1 else 0) + (if b j = w then 1 else 0))

private lemma fanout_eq_zero_iff (s o : ℕ) (a b : ℕ → ℕ) (w : ℕ) :
    fanout s o a b w = 0 ↔ w ≠ o ∧ ∀ k < s, a k ≠ w ∧ b k ≠ w := by
  unfold fanout
  rw [Nat.add_eq_zero_iff, Finset.sum_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro heq; simp [heq] at h1
    · intro k hk
      have h3 := h2 k (Finset.mem_range.mpr hk)
      rw [Nat.add_eq_zero_iff] at h3
      exact ⟨fun ha => by simp [ha] at h3, fun hb => by simp [hb] at h3⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by simp [h1], ?_⟩
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rcases h2 k hk' with ⟨ha, hb⟩
    simp [ha, hb]

private lemma sum_fanout (N s o : ℕ) (a b : ℕ → ℕ)
    (ho : o < 2 * N + s) (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j) :
    ∑ w ∈ Finset.range (2 * N + s), fanout s o a b w = 2 * s + 1 := by
  unfold fanout
  rw [Finset.sum_add_distrib]
  have h1 : ∑ w ∈ Finset.range (2 * N + s), (if w = o then 1 else 0) = 1 := by
    rw [Finset.sum_ite_eq' (Finset.range (2 * N + s)) o (fun _ => 1)]
    simp [Finset.mem_range.mpr ho]
  rw [h1, Finset.sum_comm]
  have h2 : ∑ j ∈ Finset.range s,
      ∑ w ∈ Finset.range (2 * N + s), ((if a j = w then 1 else 0) + (if b j = w then 1 else 0)) =
      2 * s := by
    have hterm : ∀ j ∈ Finset.range s,
        ∑ w ∈ Finset.range (2 * N + s),
          ((if a j = w then 1 else 0) + (if b j = w then 1 else 0)) = 2 := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rcases hab j hj' with ⟨ha, hb⟩
      rw [Finset.sum_add_distrib]
      have ha' : a j ∈ Finset.range (2 * N + s) := Finset.mem_range.mpr (by omega)
      have hb' : b j ∈ Finset.range (2 * N + s) := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_ite_eq (Finset.range (2 * N + s)) (a j) (fun _ => 1),
          Finset.sum_ite_eq (Finset.range (2 * N + s)) (b j) (fun _ => 1)]
      simp [ha', hb']
    rw [Finset.sum_const_nat hterm, Finset.card_range]
    omega
  omega

private def shiftW (W w : ℕ) : ℕ := if w < W then w else w - 1

private lemma delete_dead_gate {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hN : 0 < N) {s o : ℕ} {kind a b : ℕ → ℕ}
    (hv : ValidCirc q N I s o kind a b)
    {j : ℕ} (hj : j < s)
    (hdead : fanout s o a b (2 * N + j) = 0) :
    ∃ o' kind' a' b', ValidCirc q N I (s - 1) o' kind' a' b' := by
  rw [fanout_eq_zero_iff] at hdead
  rcases hdead with ⟨ho_ne, hno_read⟩
  let W := 2 * N + j
  let o' := shiftW W o
  let kind' : ℕ → ℕ := fun k => if k < j then kind k else kind (k + 1)
  let a' : ℕ → ℕ := fun k => shiftW W (if k < j then a k else a (k + 1))
  let b' : ℕ → ℕ := fun k => shiftW W (if k < j then b k else b (k + 1))
  have ho' : o' < 2 * N + (s - 1) := by
    dsimp only [o', shiftW, W]
    have := hv.1
    split_ifs <;> omega
  have hwf' : ∀ k < s - 1, a' k < 2 * N + k ∧ b' k < 2 * N + k ∧ kind' k ≤ 4 := by
    intro k hk
    by_cases hkj : k < j
    · rcases hv.2.1 k (by omega) with ⟨ha, hb, hkd⟩
      refine ⟨?_, ?_, ?_⟩
      · dsimp only [a', shiftW, W]; simp [hkj]; split_ifs <;> omega
      · dsimp only [b', shiftW, W]; simp [hkj]; split_ifs <;> omega
      · dsimp only [kind']; simp [hkj, hkd]
    · rcases hv.2.1 (k + 1) (by omega) with ⟨ha, hb, hkd⟩
      rcases hno_read (k + 1) (by omega) with ⟨haW, hbW⟩
      refine ⟨?_, ?_, ?_⟩
      · dsimp only [a', shiftW, W]; simp [hkj]; split_ifs <;> omega
      · dsimp only [b', shiftW, W]; simp [hkj]; split_ifs <;> omega
      · dsimp only [kind']; simp [hkj, hkd]
  have heval : ∀ (x : ℕ → Bool) (w : ℕ), w < 2 * N + s → w ≠ W →
      ceval N kind' a' b' x (shiftW W w) = ceval N kind a b x w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hwW
      by_cases hwN : w < 2 * N
      · have hsh : shiftW W w = w := by dsimp [shiftW, W]; split_ifs <;> omega
        rw [hsh, ceval_input N kind' a' b' x hwN, ceval_input N kind a b x hwN]
      · by_cases hwlt : w < W
        · let k := w - 2 * N
          have hk : k < j := by omega
          have hks : k < s := by omega
          have hw_eq : w = 2 * N + k := by omega
          have hsh : shiftW W w = 2 * N + k := by dsimp [shiftW]; rw [if_pos hwlt]; exact hw_eq
          rcases hv.2.1 k hks with ⟨ha, hb, hkd⟩
          rcases hwf' k (by omega) with ⟨ha', hb', _⟩
          have ha_eq : a' k = shiftW W (a k) := by dsimp [a']; simp [hk]
          have hb_eq : b' k = shiftW W (b k) := by dsimp [b']; simp [hk]
          have hkd_eq : kind' k = kind k := by dsimp [kind']; simp [hk]
          have iha : ceval N kind' a' b' x (a' k) = ceval N kind a b x (a k) := by
            rw [ha_eq]; exact ih (a k) (by omega) (by omega) (by omega)
          have ihb : ceval N kind' a' b' x (b' k) = ceval N kind a b x (b k) := by
            rw [hb_eq]; exact ih (b k) (by omega) (by omega) (by omega)
          rw [hsh, hw_eq]
          have hk04 : kind k = 0 ∨ kind k = 1 ∨ kind k = 2 ∨ kind k = 3 ∨ kind k = 4 := by omega
          rcases hk04 with h0 | h1 | h2 | h3 | h4
          · rw [ceval_gate_and N kind' a' b' x hN ha' hb' (hkd_eq.trans h0),
                ceval_gate_and N kind a b x hN ha hb h0, iha, ihb]
          · rw [ceval_gate_or N kind' a' b' x hN ha' hb' (hkd_eq.trans h1),
                ceval_gate_or N kind a b x hN ha hb h1, iha, ihb]
          · rw [ceval_gate_copy N kind' a' b' x hN ha' (hkd_eq.trans h2),
                ceval_gate_copy N kind a b x hN ha h2, iha]
          · rw [ceval_gate_false N kind' a' b' x hN (hkd_eq.trans h3),
                ceval_gate_false N kind a b x hN h3]
          · rw [ceval_gate_true N kind' a' b' x hN (hkd_eq.trans h4),
                ceval_gate_true N kind a b x hN h4]
        · let k := w - 2 * N - 1
          have hkj : ¬ (k < j) := by omega
          have hks : k + 1 < s := by omega
          have hw_eq : w = 2 * N + (k + 1) := by omega
          have hsh : shiftW W w = 2 * N + k := by dsimp [shiftW]; rw [if_neg hwlt]; omega
          rcases hv.2.1 (k + 1) hks with ⟨ha, hb, hkd⟩
          rcases hwf' k (by omega) with ⟨ha', hb', _⟩
          rcases hno_read (k + 1) hks with ⟨haW, hbW⟩
          have ha_eq : a' k = shiftW W (a (k + 1)) := by dsimp [a']; simp [hkj]
          have hb_eq : b' k = shiftW W (b (k + 1)) := by dsimp [b']; simp [hkj]
          have hkd_eq : kind' k = kind (k + 1) := by dsimp [kind']; simp [hkj]
          have iha : ceval N kind' a' b' x (a' k) = ceval N kind a b x (a (k + 1)) := by
            rw [ha_eq]; exact ih (a (k + 1)) (by omega) (by omega) haW
          have ihb : ceval N kind' a' b' x (b' k) = ceval N kind a b x (b (k + 1)) := by
            rw [hb_eq]; exact ih (b (k + 1)) (by omega) (by omega) hbW
          rw [hsh, hw_eq]
          have hk04 : kind (k + 1) = 0 ∨ kind (k + 1) = 1 ∨ kind (k + 1) = 2 ∨
              kind (k + 1) = 3 ∨ kind (k + 1) = 4 := by omega
          rcases hk04 with h0 | h1 | h2 | h3 | h4
          · rw [ceval_gate_and N kind' a' b' x hN ha' hb' (hkd_eq.trans h0),
                ceval_gate_and N kind a b x hN ha hb h0, iha, ihb]
          · rw [ceval_gate_or N kind' a' b' x hN ha' hb' (hkd_eq.trans h1),
                ceval_gate_or N kind a b x hN ha hb h1, iha, ihb]
          · rw [ceval_gate_copy N kind' a' b' x hN ha' (hkd_eq.trans h2),
                ceval_gate_copy N kind a b x hN ha h2, iha]
          · rw [ceval_gate_false N kind' a' b' x hN (hkd_eq.trans h3),
                ceval_gate_false N kind a b x hN h3]
          · rw [ceval_gate_true N kind' a' b' x hN (hkd_eq.trans h4),
                ceval_gate_true N kind a b x hN h4]
  refine ⟨o', kind', a', b', ho', hwf', ?_, ?_⟩
  · intro x p l hpl hp hl
    rw [heval x o hv.1 (Ne.symm ho_ne)]
    exact hv.2.2.1 x p l hpl hp hl
  · intro T hT
    rw [heval (xT N I T) o hv.1 (Ne.symm ho_ne)]
    exact hv.2.2.2 T hT

private lemma elim_const_gate {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    {s o : ℕ} {kind a b : ℕ → ℕ}
    (hv : ValidCirc q N I s o kind a b)
    {j : ℕ} (hj : j < s) (c : Bool)
    (hconst : ∀ x, ceval N kind a b x (2 * N + j) = c) :
    ∃ o' kind' a' b', ValidCirc q N I (s - 1) o' kind' a' b' := by
  have hNpos : 0 < N := by rw [hN]; nlinarith
  let W := 2 * N + j
  have ho_ne : o ≠ W := by
    intro heq
    cases c
    · have h1 := ceval_all_true hq hN hline hv
      rw [heq, hconst] at h1
      exact Bool.noConfusion h1
    · have h1 := ceval_all_false hv
      rw [heq, hconst] at h1
      exact Bool.noConfusion h1
  let ckind : ℕ := if c then 4 else 3
  let kind' : ℕ → ℕ := fun k =>
    if kind k = 0 then
      if c then
        if a k = W ∧ b k = W then 4
        else if a k = W ∨ b k = W then 2
        else 0
      else
        if a k = W ∨ b k = W then 3 else 0
    else if kind k = 1 then
      if c then
        if a k = W ∨ b k = W then 4 else 1
      else
        if a k = W ∧ b k = W then 3
        else if a k = W ∨ b k = W then 2
        else 1
    else if kind k = 2 then
      if a k = W then ckind else 2
    else
      kind k
  let a' : ℕ → ℕ := fun k =>
    if kind k = 0 then
      if c then
        if a k = W ∧ b k = W then 0
        else if a k = W then b k
        else a k
      else
        if a k = W ∨ b k = W then 0 else a k
    else if kind k = 1 then
      if c then
        if a k = W ∨ b k = W then 0 else a k
      else
        if a k = W ∧ b k = W then 0
        else if a k = W then b k
        else a k
    else if kind k = 2 then
      if a k = W then 0 else a k
    else
      0
  let b' : ℕ → ℕ := fun k =>
    if kind k = 0 then
      if a k = W ∨ b k = W then 0 else b k
    else if kind k = 1 then
      if a k = W ∨ b k = W then 0 else b k
    else
      0
  have hWpos : 0 < W := by omega
  have hwf' : ∀ k < s, a' k < 2 * N + k ∧ b' k < 2 * N + k ∧ kind' k ≤ 4 := by
    intro k hk
    rcases hv.2.1 k hk with ⟨ha, hb, hkd⟩
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [a']; split_ifs <;> omega
    · dsimp only [b']; split_ifs <;> omega
    · dsimp only [kind', ckind]; split_ifs <;> omega
  have hdead : fanout s o a' b' W = 0 := by
    rw [fanout_eq_zero_iff]
    refine ⟨Ne.symm ho_ne, fun k _ => ⟨?_, ?_⟩⟩
    · dsimp only [a']; split_ifs <;> omega
    · dsimp only [b']; split_ifs <;> omega
  have heval : ∀ (x : ℕ → Bool) (w : ℕ), w < 2 * N + s → w ≠ W →
      ceval N kind' a' b' x w = ceval N kind a b x w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hwW
      by_cases hwN : w < 2 * N
      · rw [ceval_input N kind' a' b' x hwN, ceval_input N kind a b x hwN]
      · let k := w - 2 * N
        have hks : k < s := by omega
        have hw_eq : w = 2 * N + k := by omega
        rcases hv.2.1 k hks with ⟨ha, hb, hkd⟩
        rcases hwf' k hks with ⟨ha', hb', _⟩
        rw [hw_eq]
        have hk04 : kind k = 0 ∨ kind k = 1 ∨ kind k = 2 ∨ kind k = 3 ∨ kind k = 4 := by omega
        rcases hk04 with h0 | h1 | h2 | h3 | h4
        · rw [ceval_gate_and N kind a b x hNpos ha hb h0]
          by_cases haW : a k = W <;> by_cases hbW : b k = W
          · cases c
            · have hk' : kind' k = 3 := by simp [kind', h0, haW]
              rw [ceval_gate_false N kind' a' b' x hNpos hk', haW, hconst x]
              rfl
            · have hk' : kind' k = 4 := by simp [kind', h0, haW, hbW]
              rw [ceval_gate_true N kind' a' b' x hNpos hk', haW, hbW, hconst x]
              rfl
          · have ihb := ih (b k) (by omega) (by omega) hbW
            cases c
            · have hk' : kind' k = 3 := by simp [kind', h0, haW]
              rw [ceval_gate_false N kind' a' b' x hNpos hk', haW, hconst x]
              rfl
            · have hk' : kind' k = 2 := by simp [kind', h0, haW, hbW]
              have ha'eq : a' k = b k := by simp [a', h0, haW, hbW]
              rw [ceval_gate_copy N kind' a' b' x hNpos ha' hk', ha'eq, ihb, haW, hconst x]
              simp
          · have iha := ih (a k) (by omega) (by omega) haW
            cases c
            · have hk' : kind' k = 3 := by simp [kind', h0, hbW]
              rw [ceval_gate_false N kind' a' b' x hNpos hk', hbW, hconst x]
              simp
            · have hk' : kind' k = 2 := by simp [kind', h0, haW, hbW]
              have ha'eq : a' k = a k := by simp [a', h0, haW]
              rw [ceval_gate_copy N kind' a' b' x hNpos ha' hk', ha'eq, iha, hbW, hconst x]
              simp
          · have iha := ih (a k) (by omega) (by omega) haW
            have ihb := ih (b k) (by omega) (by omega) hbW
            have hk' : kind' k = 0 := by cases c <;> simp [kind', h0, haW, hbW]
            have ha'eq : a' k = a k := by cases c <;> simp [a', h0, haW, hbW]
            have hb'eq : b' k = b k := by simp [b', h0, haW, hbW]
            rw [ceval_gate_and N kind' a' b' x hNpos ha' hb' hk', ha'eq, hb'eq, iha, ihb]
        · rw [ceval_gate_or N kind a b x hNpos ha hb h1]
          by_cases haW : a k = W <;> by_cases hbW : b k = W
          · cases c
            · have hk' : kind' k = 3 := by simp [kind', h1, haW, hbW]
              rw [ceval_gate_false N kind' a' b' x hNpos hk', haW, hbW, hconst x]
              rfl
            · have hk' : kind' k = 4 := by simp [kind', h1, haW]
              rw [ceval_gate_true N kind' a' b' x hNpos hk', haW, hconst x]
              rfl
          · have ihb := ih (b k) (by omega) (by omega) hbW
            cases c
            · have hk' : kind' k = 2 := by simp [kind', h1, haW, hbW]
              have ha'eq : a' k = b k := by simp [a', h1, haW, hbW]
              rw [ceval_gate_copy N kind' a' b' x hNpos ha' hk', ha'eq, ihb, haW, hconst x]
              simp
            · have hk' : kind' k = 4 := by simp [kind', h1, haW]
              rw [ceval_gate_true N kind' a' b' x hNpos hk', haW, hconst x]
              rfl
          · have iha := ih (a k) (by omega) (by omega) haW
            cases c
            · have hk' : kind' k = 2 := by simp [kind', h1, haW, hbW]
              have ha'eq : a' k = a k := by simp [a', h1, haW]
              rw [ceval_gate_copy N kind' a' b' x hNpos ha' hk', ha'eq, iha, hbW, hconst x]
              simp
            · have hk' : kind' k = 4 := by simp [kind', h1, hbW]
              rw [ceval_gate_true N kind' a' b' x hNpos hk', hbW, hconst x]
              simp
          · have iha := ih (a k) (by omega) (by omega) haW
            have ihb := ih (b k) (by omega) (by omega) hbW
            have hk' : kind' k = 1 := by cases c <;> simp [kind', h1, haW, hbW]
            have ha'eq : a' k = a k := by cases c <;> simp [a', h1, haW, hbW]
            have hb'eq : b' k = b k := by simp [b', h1, haW, hbW]
            rw [ceval_gate_or N kind' a' b' x hNpos ha' hb' hk', ha'eq, hb'eq, iha, ihb]
        · rw [ceval_gate_copy N kind a b x hNpos ha h2]
          by_cases haW : a k = W
          · cases c
            · have hk' : kind' k = 3 := by simp [kind', ckind, h2, haW]
              rw [ceval_gate_false N kind' a' b' x hNpos hk', haW, hconst x]
            · have hk' : kind' k = 4 := by simp [kind', ckind, h2, haW]
              rw [ceval_gate_true N kind' a' b' x hNpos hk', haW, hconst x]
          · have iha := ih (a k) (by omega) (by omega) haW
            have hk' : kind' k = 2 := by simp [kind', h2, haW]
            have ha'eq : a' k = a k := by simp [a', h2, haW]
            rw [ceval_gate_copy N kind' a' b' x hNpos ha' hk', ha'eq, iha]
        · have hk' : kind' k = 3 := by simp [kind', h3]
          rw [ceval_gate_false N kind' a' b' x hNpos hk',
              ceval_gate_false N kind a b x hNpos h3]
        · have hk' : kind' k = 4 := by simp [kind', h4]
          rw [ceval_gate_true N kind' a' b' x hNpos hk',
              ceval_gate_true N kind a b x hNpos h4]
  have hv' : ValidCirc q N I s o kind' a' b' := by
    refine ⟨hv.1, hwf', ?_, ?_⟩
    · intro x p l hpl hp hl
      rw [heval x o hv.1 ho_ne]
      exact hv.2.2.1 x p l hpl hp hl
    · intro T hT
      rw [heval (xT N I T) o hv.1 ho_ne]
      exact hv.2.2.2 T hT
  exact delete_dead_gate hNpos hv' hj hdead

private lemma elim_equiv_gate {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hN : 0 < N) {s o : ℕ} {kind a b : ℕ → ℕ}
    (hv : ValidCirc q N I s o kind a b)
    {j : ℕ} (hj : j < s)
    (heq : ∀ x, ceval N kind a b x (2 * N + j) = ceval N kind a b x (a j)) :
    ∃ o' kind' a' b', ValidCirc q N I (s - 1) o' kind' a' b' := by
  let W := 2 * N + j
  let r := a j
  have hrW : r < W := (hv.2.1 j hj).1
  let redir : ℕ → ℕ := fun w => if w = W then r else w
  let o' := redir o
  let a' : ℕ → ℕ := fun k => redir (a k)
  let b' : ℕ → ℕ := fun k => redir (b k)
  have ho' : o' < 2 * N + s := by
    dsimp only [o', redir]; have := hv.1; split_ifs <;> omega
  have hwf' : ∀ k < s, a' k < 2 * N + k ∧ b' k < 2 * N + k ∧ kind k ≤ 4 := by
    intro k hk
    rcases hv.2.1 k hk with ⟨ha, hb, hkd⟩
    refine ⟨?_, ?_, hkd⟩
    · dsimp only [a', redir]; split_ifs <;> omega
    · dsimp only [b', redir]; split_ifs <;> omega
  have hdead : fanout s o' a' b' W = 0 := by
    rw [fanout_eq_zero_iff]
    refine ⟨?_, fun k _ => ⟨?_, ?_⟩⟩
    · dsimp only [o', redir]; split_ifs <;> omega
    · dsimp only [a', redir]; split_ifs <;> omega
    · dsimp only [b', redir]; split_ifs <;> omega
  have heval : ∀ (x : ℕ → Bool) (w : ℕ), w < 2 * N + s →
      ceval N kind a' b' x w = ceval N kind a b x w := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hwN : w < 2 * N
      · rw [ceval_input N kind a' b' x hwN, ceval_input N kind a b x hwN]
      · let k := w - 2 * N
        have hks : k < s := by omega
        have hw_eq : w = 2 * N + k := by omega
        rcases hv.2.1 k hks with ⟨ha, hb, hkd⟩
        rcases hwf' k hks with ⟨ha', hb', _⟩
        have iha : ceval N kind a' b' x (a' k) = ceval N kind a b x (a k) := by
          dsimp only [a', redir]
          split_ifs with hW
          · rw [ih r (by omega) (by omega), hW, heq x]
          · exact ih (a k) (by omega) (by omega)
        have ihb : ceval N kind a' b' x (b' k) = ceval N kind a b x (b k) := by
          dsimp only [b', redir]
          split_ifs with hW
          · rw [ih r (by omega) (by omega), hW, heq x]
          · exact ih (b k) (by omega) (by omega)
        rw [hw_eq]
        have hk04 : kind k = 0 ∨ kind k = 1 ∨ kind k = 2 ∨ kind k = 3 ∨ kind k = 4 := by omega
        rcases hk04 with h0 | h1 | h2 | h3 | h4
        · rw [ceval_gate_and N kind a' b' x hN ha' hb' h0,
              ceval_gate_and N kind a b x hN ha hb h0, iha, ihb]
        · rw [ceval_gate_or N kind a' b' x hN ha' hb' h1,
              ceval_gate_or N kind a b x hN ha hb h1, iha, ihb]
        · rw [ceval_gate_copy N kind a' b' x hN ha' h2,
              ceval_gate_copy N kind a b x hN ha h2, iha]
        · rw [ceval_gate_false N kind a' b' x hN h3,
              ceval_gate_false N kind a b x hN h3]
        · rw [ceval_gate_true N kind a' b' x hN h4,
              ceval_gate_true N kind a b x hN h4]
  have heval_o : ∀ x, ceval N kind a' b' x o' = ceval N kind a b x o := by
    intro x
    dsimp only [o', redir]
    split_ifs with hW
    · rw [heval x r (by omega), hW, heq x]
    · exact heval x o hv.1
  have hv' : ValidCirc q N I s o' kind a' b' :=
    ⟨ho', hwf',
      fun x p l hpl hp hl => by rw [heval_o x]; exact hv.2.2.1 x p l hpl hp hl,
      fun T hT => by rw [heval_o _]; exact hv.2.2.2 T hT⟩
  exact delete_dead_gate hN hv' hj hdead

/-!
## Unique reader and forward OR-chains
-/

private def findReader (s : ℕ) (a b : ℕ → ℕ) (w : ℕ) : Option ℕ :=
  (List.range s).find? (fun k => decide (a k = w ∨ b k = w))

private lemma unique_reader_of_fanout_one {s o : ℕ} {a b : ℕ → ℕ} {w : ℕ}
    (hfan : fanout s o a b w = 1) (hwo : w ≠ o) :
    ∃ k < s, findReader s a b w = some k ∧
      (a k = w ∨ b k = w) ∧
      (∀ j < s, (a j = w ∨ b j = w) → j = k) := by
  have hsum : ∑ j ∈ Finset.range s, ((if a j = w then 1 else 0) + (if b j = w then 1 else 0)) = 1 := by
    unfold fanout at hfan
    simp [hwo] at hfan
    exact hfan
  have hex : ∃ k ∈ Finset.range s,
      (if a k = w then 1 else 0) + (if b k = w then 1 else 0) ≠ 0 := by
    by_contra hall
    push Not at hall
    rw [Finset.sum_eq_zero hall] at hsum
    omega
  obtain ⟨k, hk_mem, hk_ne⟩ := hex
  have hk_lt : k < s := Finset.mem_range.mp hk_mem
  have hk_read : a k = w ∨ b k = w := by
    by_contra h
    push Not at h
    simp [h.1, h.2] at hk_ne
  have hk_pos : 1 ≤ (if a k = w then 1 else 0) + (if b k = w then 1 else 0) := by omega
  have huniq : ∀ j < s, (a j = w ∨ b j = w) → j = k := by
    intro j hj hread
    by_contra hjk
    have hj_mem : j ∈ Finset.range s := Finset.mem_range.mpr hj
    have hj_pos : 1 ≤ (if a j = w then 1 else 0) + (if b j = w then 1 else 0) := by
      rcases hread with h1 | h2
      · simp [h1]
      · simp [h2]
    have hpair : ({k, j} : Finset ℕ) ⊆ Finset.range s := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hle := Finset.sum_le_sum_of_subset (f := fun i => (if a i = w then 1 else 0) + (if b i = w then 1 else 0)) hpair
    rw [Finset.sum_pair (Ne.symm hjk), hsum] at hle
    omega
  have hfind : findReader s a b w = some k := by
    unfold findReader
    cases h : (List.range s).find? (fun i => decide (a i = w ∨ b i = w)) with
    | none =>
      have := List.find?_eq_none.mp h k (List.mem_range.mpr hk_lt)
      simp [hk_read] at this
    | some k' =>
      have hmem := List.mem_of_find?_eq_some h
      have hsat := List.find?_some h
      simp only [List.mem_range] at hmem
      simp only [decide_eq_true_eq] at hsat
      rw [huniq k' hmem hsat]
  exact ⟨k, hk_lt, hfind, hk_read, huniq⟩

private def nextOr (N s o : ℕ) (kind a b : ℕ → ℕ) (w : ℕ) : Option ℕ :=
  if fanout s o a b w = 1 ∧ w ≠ o then
    match findReader s a b w with
    | some k => if kind k = 1 then some (2 * N + k) else none
    | none => none
  else
    none

private lemma nextOr_some_spec {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j)
    {w w' : ℕ} (h : nextOr N s o kind a b w = some w') :
    fanout s o a b w = 1 ∧ w ≠ o ∧
      ∃ k < s, w' = 2 * N + k ∧ kind k = 1 ∧ (a k = w ∨ b k = w) ∧
        (∀ j < s, (a j = w ∨ b j = w) → j = k) ∧ w < w' ∧ w' < 2 * N + s := by
  unfold nextOr at h
  split_ifs at h with hcond
  rcases hcond with ⟨hfan, hwo⟩
  obtain ⟨k, hk_lt, hfind, hk_read, huniq⟩ := unique_reader_of_fanout_one hfan hwo
  rw [hfind] at h
  dsimp only at h
  split_ifs at h with hk1
  injection h with hw'
  have hlt : w < 2 * N + k := by
    rcases hab k hk_lt with ⟨ha, hb⟩
    rcases hk_read with h1 | h2 <;> omega
  exact ⟨hfan, hwo, k, hk_lt, hw'.symm, hk1, hk_read, huniq, by omega, by omega⟩

private def orPathAux (N s o : ℕ) (kind a b : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, w => [w]
  | f + 1, w =>
    match nextOr N s o kind a b w with
    | some w' => w :: orPathAux N s o kind a b f w'
    | none => [w]

private lemma orPathAux_ne_nil (N s o : ℕ) (kind a b : ℕ → ℕ) (f w : ℕ) :
    orPathAux N s o kind a b f w ≠ [] := by
  cases f with
  | zero => simp [orPathAux]
  | succ f =>
    unfold orPathAux
    cases nextOr N s o kind a b w <;> simp

private lemma mem_orPathAux_self (N s o : ℕ) (kind a b : ℕ → ℕ) (f w : ℕ) :
    w ∈ orPathAux N s o kind a b f w := by
  cases f with
  | zero => simp [orPathAux]
  | succ f =>
    unfold orPathAux
    cases nextOr N s o kind a b w <;> simp

private lemma orPathAux_eq_of_le {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j) :
    ∀ f1 f2 w, w < 2 * N + s → 2 * N + s - w ≤ f1 → 2 * N + s - w ≤ f2 →
      orPathAux N s o kind a b f1 w = orPathAux N s o kind a b f2 w := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 w hw hf1 _
    omega
  | succ f1 ih =>
    intro f2 w hw hf1 hf2
    cases f2 with
    | zero => omega
    | succ f2 =>
      unfold orPathAux
      cases hnext : nextOr N s o kind a b w with
      | none => rfl
      | some w' =>
        obtain ⟨_, _, _, _, _, _, _, _, hlt, hw's⟩ := nextOr_some_spec hab hnext
        dsimp only
        congr 1
        exact ih f2 w' hw's (by omega) (by omega)

private def orPath (N s o : ℕ) (kind a b : ℕ → ℕ) (w : ℕ) : List ℕ :=
  orPathAux N s o kind a b (2 * N + s) w

private def endW (N s o : ℕ) (kind a b : ℕ → ℕ) (w : ℕ) : ℕ :=
  (orPath N s o kind a b w).getLast (orPathAux_ne_nil N s o kind a b (2 * N + s) w)

private lemma orPath_unfold {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j)
    {w : ℕ} (hw : w < 2 * N + s) :
    orPath N s o kind a b w =
      match nextOr N s o kind a b w with
      | some w' => w :: orPath N s o kind a b w'
      | none => [w] := by
  have hpos : 0 < 2 * N + s := by omega
  have heq : orPath N s o kind a b w = orPathAux N s o kind a b (2 * N + s + 1) w :=
    orPathAux_eq_of_le hab (2 * N + s) (2 * N + s + 1) w hw (by omega) (by omega)
  rw [heq]
  unfold orPathAux
  cases hnext : nextOr N s o kind a b w with
  | none => rfl
  | some w' => rfl

private lemma mem_orPath_self (N s o : ℕ) (kind a b : ℕ → ℕ) (w : ℕ) :
    w ∈ orPath N s o kind a b w :=
  mem_orPathAux_self N s o kind a b (2 * N + s) w

private lemma endW_mem_orPath (N s o : ℕ) (kind a b : ℕ → ℕ) (w : ℕ) :
    endW N s o kind a b w ∈ orPath N s o kind a b w :=
  List.getLast_mem _

private lemma orPath_props {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j) :
    ∀ f w, w < 2 * N + s → 2 * N + s - w ≤ f →
      let L := orPathAux N s o kind a b f w
      let e := L.getLast (orPathAux_ne_nil N s o kind a b f w)
      e < 2 * N + s ∧ nextOr N s o kind a b e = none ∧
      (∀ u ∈ L, u < 2 * N + s ∧ (u ≠ e → ∃ u' ∈ L, nextOr N s o kind a b u = some u') ∧
        endW N s o kind a b u = e) := by
  intro f
  induction f with
  | zero =>
    intro w hw hf; omega
  | succ f ih =>
    intro w hw hf
    have hL : orPathAux N s o kind a b (f + 1) w = orPath N s o kind a b w :=
      orPathAux_eq_of_le hab (f + 1) (2 * N + s) w hw hf (by omega)
    dsimp only
    cases hnext : nextOr N s o kind a b w with
    | none =>
      have hLw : orPathAux N s o kind a b (f + 1) w = [w] := by
        simp [orPathAux, hnext]
      simp only [hLw, List.getLast_singleton, List.mem_singleton]
      refine ⟨hw, hnext, ?_⟩
      intro u hu
      subst hu
      refine ⟨hw, fun h => absurd rfl h, ?_⟩
      unfold endW
      simp [← hL, hLw]
    | some w' =>
      obtain ⟨_, _, _, _, _, _, _, _, hlt, hw's⟩ := nextOr_some_spec hab hnext
      obtain ⟨he_lt, he_none, hmem⟩ := ih w' hw's (by omega)
      have hne' := orPathAux_ne_nil N s o kind a b f w'
      have hLw : orPathAux N s o kind a b (f + 1) w = w :: orPathAux N s o kind a b f w' := by
        simp [orPathAux, hnext]
      have hlast : (orPathAux N s o kind a b (f + 1) w).getLast (orPathAux_ne_nil N s o kind a b (f + 1) w) =
          (orPathAux N s o kind a b f w').getLast hne' := by
        simp [hLw, List.getLast_cons hne']
      rw [hlast]
      refine ⟨he_lt, he_none, ?_⟩
      intro u hu
      rw [hLw] at hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu'
      · refine ⟨hw, ?_, ?_⟩
        · intro _
          refine ⟨w', ?_, hnext⟩
          rw [hLw]
          exact List.mem_cons_of_mem _ (mem_orPathAux_self _ _ _ _ _ _ _ _)
        · unfold endW
          simp [← hL, hlast]
      · obtain ⟨hu_lt, hu_step, hu_end⟩ := hmem u hu'
        refine ⟨hu_lt, ?_, hu_end⟩
        intro hne
        obtain ⟨u', hu'mem, hu'next⟩ := hu_step hne
        refine ⟨u', ?_, hu'next⟩
        rw [hLw]
        exact List.mem_cons_of_mem _ hu'mem

private lemma endW_lt {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j)
    {w : ℕ} (hw : w < 2 * N + s) :
    endW N s o kind a b w < 2 * N + s :=
  (orPath_props hab (2 * N + s) w hw (by omega)).1

private lemma nextOr_endW_none {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j)
    {w : ℕ} (hw : w < 2 * N + s) :
    nextOr N s o kind a b (endW N s o kind a b w) = none :=
  (orPath_props hab (2 * N + s) w hw (by omega)).2.1

private lemma orPath_step_of_ne_endW {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j)
    {w u : ℕ} (hw : w < 2 * N + s)
    (hu : u ∈ orPath N s o kind a b w) (hne : u ≠ endW N s o kind a b w) :
    ∃ u' ∈ orPath N s o kind a b w, nextOr N s o kind a b u = some u' :=
  ((orPath_props hab (2 * N + s) w hw (by omega)).2.2 u hu).2.1 hne

private lemma endW_eq_of_mem_orPath {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j)
    {w u : ℕ} (hw : w < 2 * N + s) (hu : u ∈ orPath N s o kind a b w) :
    endW N s o kind a b u = endW N s o kind a b w :=
  ((orPath_props hab (2 * N + s) w hw (by omega)).2.2 u hu).2.2

private lemma orPath_mono {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hN : 0 < N) (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j)
    (x : ℕ → Bool) :
    ∀ f w, ceval N kind a b x w = true →
      ∀ u ∈ orPathAux N s o kind a b f w, ceval N kind a b x u = true := by
  intro f
  induction f with
  | zero =>
    intro w hw u hu
    simp only [orPathAux, List.mem_singleton] at hu
    subst hu; exact hw
  | succ f ih =>
    intro w hw u hu
    unfold orPathAux at hu
    cases hnext : nextOr N s o kind a b w with
    | none =>
      rw [hnext] at hu
      simp only [List.mem_singleton] at hu
      subst hu; exact hw
    | some w' =>
      rw [hnext] at hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu'
      · exact hw
      · obtain ⟨_, _, k, hk, hw'eq, hk1, hread, _, _, _⟩ := nextOr_some_spec hab hnext
        rcases hab k hk with ⟨ha, hb⟩
        have hw' : ceval N kind a b x w' = true := by
          rw [hw'eq, ceval_gate_or N kind a b x hN ha hb hk1]
          rcases hread with h1 | h2
          · rw [h1, hw]; rfl
          · rw [h2, hw]; simp
        exact ih w' hw' u hu'

/-!
## Isolation lemmas (L2, L3, L3', L4, L5)
-/

private lemma iso_outside_orPath {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hN : 0 < N) (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j)
    (hbin : ∀ j < s, kind j = 0 ∨ kind j = 1)
    {i : ℕ} (hi : i < 2 * N)
    {x y : ℕ → Bool} (hxy : ∀ v, v ≠ i → x v = y v)
    (hend : ceval N kind a b x (endW N s o kind a b i) =
            ceval N kind a b y (endW N s o kind a b i)) :
    ∀ u < 2 * N + s, u ∉ orPath N s o kind a b i →
      ceval N kind a b x u = ceval N kind a b y u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hu hunot
    by_cases huN : u < 2 * N
    · have hui : u ≠ i := fun h => hunot (h ▸ mem_orPath_self N s o kind a b i)
      rw [ceval_input N kind a b x huN, ceval_input N kind a b y huN, hxy u hui]
    · let k := u - 2 * N
      have hks : k < s := by omega
      have hu_eq : u = 2 * N + k := by omega
      rcases hab k hks with ⟨ha, hb⟩
      have hsub : ∀ v, (a k = v ∨ b k = v) → v < u →
          ceval N kind a b x v = ceval N kind a b y v := by
        intro v hvread hvlt
        by_cases hvmem : v ∈ orPath N s o kind a b i
        · by_cases hvend : v = endW N s o kind a b i
          · rw [hvend, hend]
          · obtain ⟨v', hv'mem, hv'next⟩ :=
              orPath_step_of_ne_endW hab (by omega) hvmem hvend
            obtain ⟨_, _, k', _, hv'eq, _, _, huniq, _, _⟩ := nextOr_some_spec hab hv'next
            have hk_eq : k = k' := huniq k hks hvread
            exact absurd (by rw [hu_eq, hk_eq, ← hv'eq]; exact hv'mem) hunot
        · exact ih v hvlt (by omega) hvmem
      have ha_eq := hsub (a k) (Or.inl rfl) (by omega)
      have hb_eq := hsub (b k) (Or.inr rfl) (by omega)
      rw [hu_eq]
      rcases hbin k hks with hk0 | hk1
      · rw [ceval_gate_and N kind a b x hN ha hb hk0,
            ceval_gate_and N kind a b y hN ha hb hk0, ha_eq, hb_eq]
      · rw [ceval_gate_or N kind a b x hN ha hb hk1,
            ceval_gate_or N kind a b y hN ha hb hk1, ha_eq, hb_eq]

private lemma iso_below_reader {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hN : 0 < N) (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j)
    (hbin : ∀ j < s, kind j = 0 ∨ kind j = 1)
    {i k_i : ℕ} (hi : i < 2 * N)
    (huniq_e : ∀ j < s, (a j = endW N s o kind a b i ∨ b j = endW N s o kind a b i) → j = k_i)
    {x y : ℕ → Bool} (hxy : ∀ v, v ≠ i → x v = y v) :
    ∀ u < 2 * N + k_i, u < 2 * N + s → u ∉ orPath N s o kind a b i →
      ceval N kind a b x u = ceval N kind a b y u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hult hus hunot
    by_cases huN : u < 2 * N
    · have hui : u ≠ i := fun h => hunot (h ▸ mem_orPath_self N s o kind a b i)
      rw [ceval_input N kind a b x huN, ceval_input N kind a b y huN, hxy u hui]
    · let k := u - 2 * N
      have hks : k < s := by omega
      have hu_eq : u = 2 * N + k := by omega
      rcases hab k hks with ⟨ha, hb⟩
      have hsub : ∀ v, (a k = v ∨ b k = v) → v < u →
          ceval N kind a b x v = ceval N kind a b y v := by
        intro v hvread hvlt
        by_cases hvmem : v ∈ orPath N s o kind a b i
        · by_cases hvend : v = endW N s o kind a b i
          · rw [hvend] at hvread
            have hk_eq := huniq_e k hks hvread
            omega
          · obtain ⟨v', hv'mem, hv'next⟩ :=
              orPath_step_of_ne_endW hab (by omega) hvmem hvend
            obtain ⟨_, _, k', _, hv'eq, _, _, huniq, _, _⟩ := nextOr_some_spec hab hv'next
            have hk_eq : k = k' := huniq k hks hvread
            exact absurd (by rw [hu_eq, hk_eq, ← hv'eq]; exact hv'mem) hunot
        · exact ih v hvlt (by omega) (by omega) hvmem
      have ha_eq := hsub (a k) (Or.inl rfl) (by omega)
      have hb_eq := hsub (b k) (Or.inr rfl) (by omega)
      rw [hu_eq]
      rcases hbin k hks with hk0 | hk1
      · rw [ceval_gate_and N kind a b x hN ha hb hk0,
            ceval_gate_and N kind a b y hN ha hb hk0, ha_eq, hb_eq]
      · rw [ceval_gate_or N kind a b x hN ha hb hk1,
            ceval_gate_or N kind a b y hN ha hb hk1, ha_eq, hb_eq]

private lemma iso_past_reader {N s o : ℕ} {kind a b : ℕ → ℕ}
    (hN : 0 < N) (hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j)
    (hbin : ∀ j < s, kind j = 0 ∨ kind j = 1)
    {i k_i : ℕ} (hi : i < 2 * N)
    (huniq_e : ∀ j < s, (a j = endW N s o kind a b i ∨ b j = endW N s o kind a b i) → j = k_i)
    {x y : ℕ → Bool} (hxy : ∀ v, v ≠ i → x v = y v)
    (hh : ceval N kind a b x (2 * N + k_i) = ceval N kind a b y (2 * N + k_i)) :
    ∀ u < 2 * N + s, u ∉ orPath N s o kind a b i → u ≠ 2 * N + k_i →
      ceval N kind a b x u = ceval N kind a b y u := by
  intro u
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    intro hus hunot hune
    by_cases huN : u < 2 * N
    · have hui : u ≠ i := fun h => hunot (h ▸ mem_orPath_self N s o kind a b i)
      rw [ceval_input N kind a b x huN, ceval_input N kind a b y huN, hxy u hui]
    · let k := u - 2 * N
      have hks : k < s := by omega
      have hu_eq : u = 2 * N + k := by omega
      rcases hab k hks with ⟨ha, hb⟩
      have hsub : ∀ v, (a k = v ∨ b k = v) → v < u →
          ceval N kind a b x v = ceval N kind a b y v := by
        intro v hvread hvlt
        by_cases hvh : v = 2 * N + k_i
        · rw [hvh, hh]
        · by_cases hvmem : v ∈ orPath N s o kind a b i
          · by_cases hvend : v = endW N s o kind a b i
            · rw [hvend] at hvread
              have hk_eq := huniq_e k hks hvread
              exact absurd (by omega) hune
            · obtain ⟨v', hv'mem, hv'next⟩ :=
                orPath_step_of_ne_endW hab (by omega) hvmem hvend
              obtain ⟨_, _, k', _, hv'eq, _, _, huniq, _, _⟩ := nextOr_some_spec hab hv'next
              have hk_eq : k = k' := huniq k hks hvread
              exact absurd (by rw [hu_eq, hk_eq, ← hv'eq]; exact hv'mem) hunot
          · exact ih v hvlt (by omega) hvmem hvh
      have ha_eq := hsub (a k) (Or.inl rfl) (by omega)
      have hb_eq := hsub (b k) (Or.inr rfl) (by omega)
      rw [hu_eq]
      rcases hbin k hks with hk0 | hk1
      · rw [ceval_gate_and N kind a b x hN ha hb hk0,
            ceval_gate_and N kind a b y hN ha hb hk0, ha_eq, hb_eq]
      · rw [ceval_gate_or N kind a b x hN ha hb hk1,
            ceval_gate_or N kind a b y hN ha hb hk1, ha_eq, hb_eq]

private lemma out_not_mem_orPath {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : 0 < N) {s o : ℕ} {kind a b : ℕ → ℕ}
    (hv : ValidCirc q N I s o kind a b)
    {i : ℕ} (hi : i < 2 * N) :
    o ∉ orPath N s o kind a b i := by
  intro ho_mem
  let x : ℕ → Bool := fun u => decide (u = i)
  have hxi : ceval N kind a b x i = true := by
    rw [ceval_input N kind a b x hi]; simp [x]
  have hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j :=
    fun j hj => ⟨(hv.2.1 j hj).1, (hv.2.1 j hj).2.1⟩
  have h1 := orPath_mono hN hab x (2 * N + s) i hxi o ho_mem
  have h2 := ceval_single_false hq hv hi
  rw [h1] at h2
  exact Bool.noConfusion h2

private lemma orPath_disjoint {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    {s o : ℕ} {kind a b : ℕ → ℕ}
    (hv : ValidCirc q N I s o kind a b)
    (hbin : ∀ j < s, kind j = 0 ∨ kind j = 1)
    {i j : ℕ} (hi : i < 2 * N) (hj : j < 2 * N) (hij : i ≠ j) :
    ∀ w, w ∈ orPath N s o kind a b i → w ∉ orPath N s o kind a b j := by
  intro w hwi hwj
  have hNpos : 0 < N := by rw [hN]; nlinarith
  have hab : ∀ k < s, a k < 2 * N + k ∧ b k < 2 * N + k :=
    fun k hk => ⟨(hv.2.1 k hk).1, (hv.2.1 k hk).2.1⟩
  obtain ⟨x, y, hxy, hxj, hyj, hox, hoy⟩ := pair_sens hq hN hline huniq hv hi hj hij
  have hwx : ceval N kind a b x w = true :=
    orPath_mono hNpos hab x (2 * N + s) j (by rw [ceval_input N kind a b x hj]; exact hxj) w hwj
  have hwy : ceval N kind a b y w = true :=
    orPath_mono hNpos hab y (2 * N + s) j (by rw [ceval_input N kind a b y hj]; exact hyj) w hwj
  have hend_eq : endW N s o kind a b w = endW N s o kind a b i :=
    endW_eq_of_mem_orPath hab (by omega) hwi
  have hex : ceval N kind a b x (endW N s o kind a b i) = true := by
    rw [← hend_eq]
    exact orPath_mono hNpos hab x (2 * N + s) w hwx _ (endW_mem_orPath _ _ _ _ _ _ w)
  have hey : ceval N kind a b y (endW N s o kind a b i) = true := by
    rw [← hend_eq]
    exact orPath_mono hNpos hab y (2 * N + s) w hwy _ (endW_mem_orPath _ _ _ _ _ _ w)
  have houteq := iso_outside_orPath hNpos hab hbin hi hxy (hex.trans hey.symm)
    o hv.1 (out_not_mem_orPath hq hNpos hv hi)
  rw [hox, hoy] at houteq
  exact Bool.noConfusion houteq

/-!
## Main lower bound by strong induction on s
-/

private lemma and_reader_case2 {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hq : 2 ≤ q) (hN : 0 < N) {s o : ℕ} {kind a b : ℕ → ℕ}
    (hv : ValidCirc q N I s o kind a b)
    (hnonconst : ∀ w < 2 * N + s, ceval N kind a b (fun _ => false) w = false)
    (hbin : ∀ j < s, (kind j = 0 ∨ kind j = 1) ∧ a j ≠ b j)
    {u v k_u k_v : ℕ} (hu : u < 2 * N) (hv2 : v < 2 * N)
    (hku : k_u < s) (hkv : k_v < s) (hlt : k_u < k_v)
    (hk_u0 : kind k_u = 0)
    (huniq_u : ∀ j < s, (a j = endW N s o kind a b u ∨ b j = endW N s o kind a b u) → j = k_u)
    (huniq_v : ∀ j < s, (a j = endW N s o kind a b v ∨ b j = endW N s o kind a b v) → j = k_v)
    (hpair_true : ceval N kind a b (fun t => decide (t = u ∨ t = v)) o = true) :
    False := by
  have hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j :=
    fun j hj => ⟨(hv.2.1 j hj).1, (hv.2.1 j hj).2.1⟩
  have hbin0 : ∀ j < s, kind j = 0 ∨ kind j = 1 := fun j hj => (hbin j hj).1
  let z : ℕ := if a k_u = endW N s o kind a b u then b k_u else a k_u
  have hz_ne_eu : z ≠ endW N s o kind a b u := by
    dsimp only [z]
    have habne := (hbin k_u hku).2
    split_ifs with h
    · intro h2; exact habne (h.trans h2.symm)
    · exact h
  have hz_read : a k_u = z ∨ b k_u = z := by
    dsimp only [z]
    split_ifs with h
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hz_lt : z < 2 * N + k_u := by
    rcases hab k_u hku with ⟨ha, hb⟩
    dsimp only [z]
    split_ifs <;> omega
  have hz_not_u : z ∉ orPath N s o kind a b u := by
    intro hzmem
    obtain ⟨z', _, hznext⟩ := orPath_step_of_ne_endW hab (by omega) hzmem hz_ne_eu
    obtain ⟨_, _, k', _, _, hk'1, _, huniq', _, _⟩ := nextOr_some_spec hab hznext
    have hk_eq := huniq' k_u hku hz_read
    rw [hk_eq] at hk_u0
    omega
  have hz_not_v : z ∉ orPath N s o kind a b v := by
    intro hzmem
    by_cases hzev : z = endW N s o kind a b v
    · rw [hzev] at hz_read
      have hk_eq := huniq_v k_u hku hz_read
      omega
    · obtain ⟨z', _, hznext⟩ := orPath_step_of_ne_endW hab (by omega) hzmem hzev
      obtain ⟨_, _, k', _, _, hk'1, _, huniq', _, _⟩ := nextOr_some_spec hab hznext
      have hk_eq := huniq' k_u hku hz_read
      rw [hk_eq] at hk_u0
      omega
  let x : ℕ → Bool := fun t => decide (t = v)
  let y : ℕ → Bool := fun t => decide (t = u ∨ t = v)
  have hxy : ∀ t, t ≠ u → x t = y t := by intro t ht; simp [x, y, ht]
  have hx0 : ∀ t, t ≠ v → x t = false := by intro t ht; simp [x, ht]
  have hz_xy : ceval N kind a b x z = ceval N kind a b y z :=
    iso_below_reader hN hab hbin0 hu huniq_u hxy z hz_lt (by omega) hz_not_u
  have hz_x0 : ceval N kind a b x z = ceval N kind a b (fun _ => false) z :=
    iso_below_reader hN hab hbin0 hv2 huniq_v hx0 z (by omega) (by omega) hz_not_v
  have hz0 : ceval N kind a b (fun _ => false) z = false := hnonconst z (by omega)
  have hzx : ceval N kind a b x z = false := hz_x0.trans hz0
  have hzy : ceval N kind a b y z = false := hz_xy.symm.trans hzx
  rcases hab k_u hku with ⟨ha, hb⟩
  have hhu_x : ceval N kind a b x (2 * N + k_u) = false := by
    rw [ceval_gate_and N kind a b x hN ha hb hk_u0]
    rcases hz_read with h1 | h2
    · rw [h1, hzx]; rfl
    · rw [h2, hzx]; simp
  have hhu_y : ceval N kind a b y (2 * N + k_u) = false := by
    rw [ceval_gate_and N kind a b y hN ha hb hk_u0]
    rcases hz_read with h1 | h2
    · rw [h1, hzy]; rfl
    · rw [h2, hzy]; simp
  by_cases ho_eq : o = 2 * N + k_u
  · rw [ho_eq, hhu_y] at hpair_true
    exact Bool.noConfusion hpair_true
  · have hox : ceval N kind a b x o = false := ceval_single_false hq hv hv2
    have houteq := iso_past_reader hN hab hbin0 hu huniq_u hxy (hhu_x.trans hhu_y.symm)
      o hv.1 (out_not_mem_orPath hq hN hv hu) ho_eq
    rw [hox, hpair_true] at houteq
    exact Bool.noConfusion houteq

private theorem circ_lower_bound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hline : ∀ l : Fin N, Fintype.card { p : Fin N // I p l } = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) :
    ∀ s o kind a b, ValidCirc q N I s o kind a b → 3 * N ≤ s + 1 := by
  have hNpos : 0 < N := by rw [hN]; nlinarith
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro o kind a b hv
    -- (C1) Eliminate any dead gate
    by_cases hdead : ∃ j < s, fanout s o a b (2 * N + j) = 0
    · obtain ⟨j, hj, hfj⟩ := hdead
      obtain ⟨o', kind', a', b', hv'⟩ := delete_dead_gate hNpos hv hj hfj
      have hle := ih (s - 1) (by omega) o' kind' a' b' hv'
      omega
    push Not at hdead
    -- (C2) Eliminate any constant gate
    by_cases hconst : ∃ j < s,
        ceval N kind a b (fun _ => false) (2 * N + j) = true ∨
        ceval N kind a b (fun _ => true) (2 * N + j) = false
    · obtain ⟨j, hj, hc⟩ := hconst
      rcases hc with hct | hcf
      · have hall : ∀ x, ceval N kind a b x (2 * N + j) = true := fun x =>
          ceval_mono N kind a b (fun _ h => Bool.noConfusion h) (2 * N + j) hct
        obtain ⟨o', kind', a', b', hv'⟩ := elim_const_gate hq hN hline hv hj true hall
        have hle := ih (s - 1) (by omega) o' kind' a' b' hv'
        omega
      · have hall : ∀ x, ceval N kind a b x (2 * N + j) = false := by
          intro x
          cases h : ceval N kind a b x (2 * N + j)
          · rfl
          · have h1 := ceval_mono N kind a b (fun _ _ => rfl) (2 * N + j) h
            rw [h1] at hcf; exact Bool.noConfusion hcf
        obtain ⟨o', kind', a', b', hv'⟩ := elim_const_gate hq hN hline hv hj false hall
        have hle := ih (s - 1) (by omega) o' kind' a' b' hv'
        omega
    push Not at hconst
    have hnonconst : ∀ w < 2 * N + s, ceval N kind a b (fun _ => false) w = false := by
      intro w hw
      by_cases hwN : w < 2 * N
      · rw [ceval_input N kind a b (fun _ => false) hwN]
      · have h1 := (hconst (w - 2 * N) (by omega)).1
        have h2 : 2 * N + (w - 2 * N) = w := by omega
        rw [h2] at h1
        cases h : ceval N kind a b (fun _ => false) w
        · rfl
        · exact absurd h h1
    have hkind_le2 : ∀ j < s, kind j ≤ 2 := by
      intro j hj
      rcases hv.2.1 j hj with ⟨_, _, hkd⟩
      have hne3' : kind j ≠ 3 := by
        intro h3
        have h1 := ceval_gate_false N kind a b (fun _ => true) hNpos h3
        exact (hconst j hj).2 h1
      have hne4' : kind j ≠ 4 := by
        intro h4
        have h1 := ceval_gate_true N kind a b (fun _ => false) hNpos h4
        exact (hconst j hj).1 h1
      omega
    -- (C3) Eliminate any copy gate or gate with a j = b j
    by_cases hred : ∃ j < s, kind j = 2 ∨ a j = b j
    · obtain ⟨j, hj, hr⟩ := hred
      rcases hv.2.1 j hj with ⟨ha, hb, _⟩
      have heq : ∀ x, ceval N kind a b x (2 * N + j) = ceval N kind a b x (a j) := by
        intro x
        have hle2 := hkind_le2 j hj
        rcases hr with hk2 | hab_eq
        · exact ceval_gate_copy N kind a b x hNpos ha hk2
        · have hk012 : kind j = 0 ∨ kind j = 1 ∨ kind j = 2 := by omega
          rcases hk012 with h0 | h1 | h2
          · rw [ceval_gate_and N kind a b x hNpos ha hb h0, ← hab_eq, Bool.and_self]
          · rw [ceval_gate_or N kind a b x hNpos ha hb h1, ← hab_eq, Bool.or_self]
          · exact ceval_gate_copy N kind a b x hNpos ha h2
      obtain ⟨o', kind', a', b', hv'⟩ := elim_equiv_gate hNpos hv hj heq
      have hle := ih (s - 1) (by omega) o' kind' a' b' hv'
      omega
    push Not at hred
    have hbin : ∀ j < s, (kind j = 0 ∨ kind j = 1) ∧ a j ≠ b j := by
      intro j hj
      have h1 := hkind_le2 j hj
      have h2 := hred j hj
      exact ⟨by omega, h2.2⟩
    have hbin0 : ∀ j < s, kind j = 0 ∨ kind j = 1 := fun j hj => (hbin j hj).1
    have hab : ∀ j < s, a j < 2 * N + j ∧ b j < 2 * N + j :=
      fun j hj => ⟨(hv.2.1 j hj).1, (hv.2.1 j hj).2.1⟩
    -- (C4) Every raw input has fanout ≥ 1
    have hinput_fan : ∀ i < 2 * N, 1 ≤ fanout s o a b i := by
      intro i hi
      by_contra hlt
      have hzero : fanout s o a b i = 0 := by omega
      rw [fanout_eq_zero_iff] at hzero
      rcases hzero with ⟨hio, hnoread⟩
      let j := if i = 0 then 1 else 0
      have hj : j < 2 * N := by dsimp [j]; split_ifs <;> omega
      have hij : i ≠ j := by dsimp [j]; split_ifs <;> omega
      obtain ⟨x, y, hxy, _, _, hox, hoy⟩ := pair_sens hq hN hline huniq hv hi hj hij
      have hsame : ∀ w < 2 * N + s, w ≠ i → ceval N kind a b x w = ceval N kind a b y w := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ihw =>
          intro hw hwi
          by_cases hwN : w < 2 * N
          · rw [ceval_input N kind a b x hwN, ceval_input N kind a b y hwN, hxy w hwi]
          · let k := w - 2 * N
            have hks : k < s := by omega
            have hw_eq : w = 2 * N + k := by omega
            rcases hab k hks with ⟨ha, hb⟩
            rcases hnoread k hks with ⟨hai, hbi⟩
            have iha := ihw (a k) (by omega) (by omega) hai
            have ihb := ihw (b k) (by omega) (by omega) hbi
            rw [hw_eq]
            rcases hbin0 k hks with h0 | h1
            · rw [ceval_gate_and N kind a b x hNpos ha hb h0,
                  ceval_gate_and N kind a b y hNpos ha hb h0, iha, ihb]
            · rw [ceval_gate_or N kind a b x hNpos ha hb h1,
                  ceval_gate_or N kind a b y hNpos ha hb h1, iha, ihb]
      have heq := hsame o hv.1 (Ne.symm hio)
      rw [hox, hoy] at heq
      exact Bool.noConfusion heq
    have hall_fan : ∀ w < 2 * N + s, 1 ≤ fanout s o a b w := by
      intro w hw
      by_cases hwN : w < 2 * N
      · exact hinput_fan w hwN
      · have hne := hdead (w - 2 * N) (by omega)
        have h2 : 2 * N + (w - 2 * N) = w := by omega
        rw [h2] at hne
        omega
    -- Partition [0, 2N) into A (fanout(endW i) ≥ 2) and B (fanout(endW i) = 1)
    let A : Finset ℕ := (Finset.range (2 * N)).filter (fun i => 2 ≤ fanout s o a b (endW N s o kind a b i))
    let B : Finset ℕ := (Finset.range (2 * N)).filter (fun i => fanout s o a b (endW N s o kind a b i) = 1)
    have hAB_card : A.card + B.card = 2 * N := by
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro i hiA hiB
        simp only [A, B, Finset.mem_filter] at hiA hiB
        omega
      have hunion : A ∪ B = Finset.range (2 * N) := by
        ext i
        simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro hi
          have hfan := hall_fan (endW N s o kind a b i) (endW_lt hab (by omega))
          by_cases h2 : 2 ≤ fanout s o a b (endW N s o kind a b i)
          · exact Or.inl ⟨hi, h2⟩
          · exact Or.inr ⟨hi, by omega⟩
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
    -- Show PB and LB are non-incident in the plane
    let PB : Finset (Fin N) := Finset.univ.filter (fun p : Fin N => p.val ∈ B)
    let LB : Finset (Fin N) := Finset.univ.filter (fun l : Fin N => N + l.val ∈ B)
    have hPB_LB_card : PB.card + LB.card = B.card := by
      let B1 : Finset ℕ := B.filter (fun i => i < N)
      let B2 : Finset ℕ := B.filter (fun i => ¬ (i < N))
      have hB12 : B1.card + B2.card = B.card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext i; simp only [B1, B2, Finset.mem_union, Finset.mem_filter]; tauto
        · rw [Finset.disjoint_left]; intro i h1 h2; simp only [B1, B2, Finset.mem_filter] at h1 h2; exact h2.2 h1.2
      have hPB : PB.card = B1.card := by
        refine Finset.card_bij (fun p _ => p.val) ?_ ?_ ?_
        · intro p hp
          simp only [PB, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          exact Finset.mem_filter.mpr ⟨hp, p.isLt⟩
        · intro p1 _ p2 _ h; exact Fin.ext h
        · intro i hi
          simp only [B1, Finset.mem_filter] at hi
          exact ⟨⟨i, hi.2⟩, by simp [PB, hi.1], rfl⟩
      have hLB : LB.card = B2.card := by
        refine Finset.card_bij (fun l _ => N + l.val) ?_ ?_ ?_
        · intro l hl
          simp only [LB, Finset.mem_filter, Finset.mem_univ, true_and] at hl
          exact Finset.mem_filter.mpr ⟨hl, by omega⟩
        · intro l1 _ l2 _ h; exact Fin.ext (by omega)
        · intro i hi
          simp only [B2, B, Finset.mem_filter, Finset.mem_range] at hi
          have hiB : i ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi.1.1, hi.1.2⟩
          exact ⟨⟨i - N, by omega⟩, by simp [LB, show N + (i - N) = i by omega, hiB], by dsimp; omega⟩
      omega
    have hind : ∀ p ∈ PB, ∀ l ∈ LB, ¬ I p l := by
      intro p hp l hl hpl
      simp only [PB, LB, B, Finset.mem_filter, Finset.mem_univ, Finset.mem_range, true_and] at hp hl
      let i := p.val
      let j := N + l.val
      have hi : i < 2 * N := by dsimp [i]; omega
      have hj : j < 2 * N := by dsimp [j]; omega
      have hij : i ≠ j := by dsimp [i, j]; omega
      have hfi : fanout s o a b (endW N s o kind a b i) = 1 := hp.2
      have hfj : fanout s o a b (endW N s o kind a b j) = 1 := hl.2
      have hei_neo : endW N s o kind a b i ≠ o := by
        intro h
        have hmem := endW_mem_orPath N s o kind a b i
        rw [h] at hmem
        exact out_not_mem_orPath hq hNpos hv hi hmem
      have hej_neo : endW N s o kind a b j ≠ o := by
        intro h
        have hmem := endW_mem_orPath N s o kind a b j
        rw [h] at hmem
        exact out_not_mem_orPath hq hNpos hv hj hmem
      obtain ⟨ki, hki_lt, hfind_i, hread_i, huniq_i⟩ := unique_reader_of_fanout_one hfi hei_neo
      obtain ⟨kj, hkj_lt, hfind_j, hread_j, huniq_j⟩ := unique_reader_of_fanout_one hfj hej_neo
      have hki0 : kind ki = 0 := by
        have hnone := nextOr_endW_none (o := o) (kind := kind) hab (w := i) (by omega)
        unfold nextOr at hnone
        rw [if_pos ⟨hfi, hei_neo⟩, hfind_i] at hnone
        dsimp only at hnone
        have hk1 : kind ki ≠ 1 := by intro h1; simp [h1] at hnone
        rcases hbin0 ki hki_lt with h0 | h1
        · exact h0
        · exact absurd h1 hk1
      have hkj0 : kind kj = 0 := by
        have hnone := nextOr_endW_none (o := o) (kind := kind) hab (w := j) (by omega)
        unfold nextOr at hnone
        rw [if_pos ⟨hfj, hej_neo⟩, hfind_j] at hnone
        dsimp only at hnone
        have hk1 : kind kj ≠ 1 := by intro h1; simp [h1] at hnone
        rcases hbin0 kj hkj_lt with h0 | h1
        · exact h0
        · exact absurd h1 hk1
      have hpair_ij : ceval N kind a b (fun t => decide (t = i ∨ t = j)) o = true :=
        hv.2.2.1 _ p l hpl (by simp [i]) (by simp [j])
      have hpair_ji : ceval N kind a b (fun t => decide (t = j ∨ t = i)) o = true :=
        hv.2.2.1 _ p l hpl (by simp [i]) (by simp [j])
      rcases lt_trichotomy ki kj with hlt | heqk | hgt
      · exact and_reader_case2 hq hNpos hv hnonconst hbin hi hj hki_lt hkj_lt hlt hki0
          huniq_i huniq_j hpair_ij
      · -- Case 1: ki = kj
        subst heqk
        let h := 2 * N + ki
        have heij_ne : endW N s o kind a b i ≠ endW N s o kind a b j := fun hEq =>
          orPath_disjoint hq hN hline huniq hv hbin0 hi hj hij (endW N s o kind a b i)
            (endW_mem_orPath _ _ _ _ _ _ i) (hEq ▸ endW_mem_orPath _ _ _ _ _ _ j)
        obtain ⟨r, hrl, hrp⟩ := exists_point_ne hq hline l p
        let x1 : ℕ → Bool := fun t => decide (t = r.val)
        let y1 : ℕ → Bool := fun t => decide (t = r.val ∨ t = j)
        have hxy1 : ∀ t, t ≠ j → x1 t = y1 t := by intro t ht; simp [x1, y1, ht]
        have hx1_le_y1 : ∀ t, x1 t = true → y1 t = true := by
          intro t ht; simp only [x1, y1, decide_eq_true_eq] at ht ⊢; exact Or.inl ht
        have hox1 : ceval N kind a b x1 o = false := ceval_single_false hq hv (by omega)
        have hoy1 : ceval N kind a b y1 o = true :=
          hv.2.2.1 y1 r l hrl (by simp [y1]) (by simp [y1, j])
        have hhy1 : ceval N kind a b y1 h = true := by
          cases hh : ceval N kind a b y1 h
          · have hhx1 : ceval N kind a b x1 h = false := by
              cases hhx : ceval N kind a b x1 h
              · rfl
              · have := ceval_mono N kind a b hx1_le_y1 h hhx
                rw [this] at hh; exact Bool.noConfusion hh
            by_cases hoh : o = h
            · rw [hoh, hh] at hoy1; exact Bool.noConfusion hoy1
            · have houteq := iso_past_reader hNpos hab hbin0 hj huniq_j hxy1
                (hhx1.trans hh.symm) o hv.1 (out_not_mem_orPath hq hNpos hv hj) hoh
              rw [hox1, hoy1] at houteq; exact Bool.noConfusion houteq
          · rfl
        rcases hab ki hki_lt with ⟨ha, hb⟩
        have heiy1 : ceval N kind a b y1 (endW N s o kind a b i) = true := by
          dsimp only [h] at hhy1
          rw [ceval_gate_and N kind a b y1 hNpos ha hb hki0, Bool.and_eq_true] at hhy1
          rcases hread_i with h1 | h2
          · rw [← h1]; exact hhy1.1
          · rw [← h2]; exact hhy1.2
        have hei_lt_h : endW N s o kind a b i < 2 * N + ki := by
          rcases hread_i with h1 | h2 <;> omega
        have hei_not_j : endW N s o kind a b i ∉ orPath N s o kind a b j :=
          orPath_disjoint hq hN hline huniq hv hbin0 hi hj hij _ (endW_mem_orPath _ _ _ _ _ _ i)
        have heix1 : ceval N kind a b x1 (endW N s o kind a b i) = true := by
          have := iso_below_reader hNpos hab hbin0 hj huniq_j hxy1
            (endW N s o kind a b i) hei_lt_h (by omega) hei_not_j
          rw [this, heiy1]
        obtain ⟨l', hpl', hrl'⟩ := exists_line_not_through hq hN hline huniq (Ne.symm hrp)
        let x2 : ℕ → Bool := fun t => decide (t = r.val ∨ t = N + l'.val)
        let y2 : ℕ → Bool := fun t => decide (t = i ∨ t = r.val ∨ t = N + l'.val)
        have hxy2 : ∀ t, t ≠ i → x2 t = y2 t := by intro t ht; simp [x2, y2, ht]
        have hx1_le_x2 : ∀ t, x1 t = true → x2 t = true := by
          intro t ht; simp only [x1, x2, decide_eq_true_eq] at ht ⊢; exact Or.inl ht
        have hx1_le_y2 : ∀ t, x1 t = true → y2 t = true := by
          intro t ht; simp only [x1, y2, decide_eq_true_eq] at ht ⊢; exact Or.inr (Or.inl ht)
        have heix2 : ceval N kind a b x2 (endW N s o kind a b i) = true :=
          ceval_mono N kind a b hx1_le_x2 _ heix1
        have heiy2 : ceval N kind a b y2 (endW N s o kind a b i) = true :=
          ceval_mono N kind a b hx1_le_y2 _ heix1
        have hox2 : ceval N kind a b x2 o = false := by
          refine ceval_false_of_le_xT hv {l'} (by simp; omega) ?_
          intro t ht
          simp only [x2, decide_eq_true_eq] at ht
          rcases ht with rfl | rfl
          · simp [xT, r.isLt, hrl']
          · have hlt1 : ¬ (N + l'.val < N) := by omega
            have hlt2 : N + l'.val < 2 * N := by omega
            simp [xT, hlt1, hlt2]
        have hoy2 : ceval N kind a b y2 o = true :=
          hv.2.2.1 y2 p l' hpl' (by simp [y2, i]) (by simp [y2])
        have houteq := iso_outside_orPath hNpos hab hbin0 hi hxy2 (heix2.trans heiy2.symm)
          o hv.1 (out_not_mem_orPath hq hNpos hv hi)
        rw [hox2, hoy2] at houteq
        exact Bool.noConfusion houteq
      · exact and_reader_case2 hq hNpos hv hnonconst hbin hj hi hkj_lt hki_lt hgt hkj0
          huniq_j huniq_i hpair_ji
    have hB_le : B.card ≤ N := by
      rw [← hPB_LB_card]
      exact indep_card_le hq hN hline huniq PB LB hind
    have hA_ge : N ≤ A.card := by omega
    -- Count excess fanout over image of A under endW
    let SA : Finset ℕ := A.image (endW N s o kind a b)
    have hSA_card : SA.card = A.card := by
      refine Finset.card_image_of_injOn ?_
      intro i hiA j hjA hEq
      by_contra hij
      simp only [Finset.mem_coe, A, Finset.mem_filter, Finset.mem_range] at hiA hjA
      exact orPath_disjoint hq hN hline huniq hv hbin0 hiA.1 hjA.1 hij _
        (endW_mem_orPath _ _ _ _ _ _ i) (hEq ▸ endW_mem_orPath _ _ _ _ _ _ j)
    have hSA_sub : SA ⊆ Finset.range (2 * N + s) := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨i, hiA, rfl⟩
      simp only [A, Finset.mem_filter, Finset.mem_range] at hiA
      exact Finset.mem_range.mpr (endW_lt hab (by omega))
    have hexcess : SA.card ≤ ∑ w ∈ Finset.range (2 * N + s), (fanout s o a b w - 1) := by
      calc
        SA.card = ∑ _w ∈ SA, 1 := by simp
        _ ≤ ∑ w ∈ SA, (fanout s o a b w - 1) := by
          refine Finset.sum_le_sum ?_
          intro w hw
          rcases Finset.mem_image.mp hw with ⟨i, hiA, rfl⟩
          simp only [A, Finset.mem_filter] at hiA
          omega
        _ ≤ ∑ w ∈ Finset.range (2 * N + s), (fanout s o a b w - 1) :=
          Finset.sum_le_sum_of_subset hSA_sub
    have hsum_id : ∑ w ∈ Finset.range (2 * N + s), fanout s o a b w =
        (2 * N + s) + ∑ w ∈ Finset.range (2 * N + s), (fanout s o a b w - 1) := by
      have h1 : ∀ w ∈ Finset.range (2 * N + s),
          fanout s o a b w = 1 + (fanout s o a b w - 1) := by
        intro w hw
        have := hall_fan w (Finset.mem_range.mp hw)
        omega
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib,
          Finset.sum_const_nat (fun _ _ => rfl), Finset.card_range, mul_one]
    have hsum_val := sum_fanout N s o a b hv.1 hab
    omega

/-!
## Translation from Finset-family semantics F to monotone Boolean circuits
-/

private def evalF (F : ℕ → Set (Finset ℕ)) (w : ℕ) (x : ℕ → Bool) : Prop :=
  ∀ A ∈ F w, ∃ i ∈ A, x i = true

private lemma evalF_input {N : ℕ} {F : ℕ → Set (Finset ℕ)}
    (hF_in : ∀ v < N + N, F v = {{v}})
    {v : ℕ} (hv : v < 2 * N) (x : ℕ → Bool) :
    evalF F v x ↔ x v = true := by
  unfold evalF
  rw [hF_in v (by omega)]
  simp

private lemma evalF_or {F : ℕ → Set (Finset ℕ)} {w a b : ℕ}
    (hw : F w = Set.image2 (fun A B : Finset ℕ => A ∪ B) (F a) (F b))
    (x : ℕ → Bool) :
    evalF F w x ↔ evalF F a x ∨ evalF F b x := by
  unfold evalF
  rw [hw]
  constructor
  · intro h
    by_cases ha : ∀ A ∈ F a, ∃ i ∈ A, x i = true
    · exact Or.inl ha
    · right
      push Not at ha
      obtain ⟨A, hA, hAx⟩ := ha
      intro B hB
      obtain ⟨i, hi, hix⟩ := h (A ∪ B) ⟨A, hA, B, hB, rfl⟩
      rcases Finset.mem_union.mp hi with hiA | hiB
      · exact absurd hix (hAx i hiA)
      · exact ⟨i, hiB, hix⟩
  · rintro (ha | hb) C hC
    · rcases hC with ⟨A, hA, B, _, rfl⟩
      obtain ⟨i, hi, hix⟩ := ha A hA
      exact ⟨i, Finset.mem_union_left B hi, hix⟩
    · rcases hC with ⟨A, _, B, hB, rfl⟩
      obtain ⟨i, hi, hix⟩ := hb B hB
      exact ⟨i, Finset.mem_union_right A hi, hix⟩

private lemma evalF_and {F : ℕ → Set (Finset ℕ)} {w a b : ℕ}
    (hw : F w = F a ∪ F b) (x : ℕ → Bool) :
    evalF F w x ↔ evalF F a x ∧ evalF F b x := by
  unfold evalF
  rw [hw]
  constructor
  · intro h
    exact ⟨fun A hA => h A (Or.inl hA), fun B hB => h B (Or.inr hB)⟩
  · rintro ⟨ha, hb⟩ C (hC | hC)
    · exact ha C hC
    · exact hb C hC

private lemma evalF_false {F : ℕ → Set (Finset ℕ)} {w : ℕ}
    (hw : F w = {∅}) (x : ℕ → Bool) :
    evalF F w x ↔ False := by
  unfold evalF
  rw [hw]
  simp

private lemma main_proof :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
    (2 : ℕ) ≤ x1 →
    x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
    (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
    (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
    ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)),
      x10 < x2 + x2 + x9 →
      (∀ x13 < x2 + x2, x11 x13 = {{x13}}) →
      (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14,
        x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨
        x11 (x2 + x2 + x14) = x11 x16 ∨
        x11 (x2 + x2 + x14) = {∅} ∨
        x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) →
      (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) →
      (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 →
        ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2),
          (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) →
      (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) := by
  intro q N I _ hq hN hline huniq s o F ho hF_in hF_gate hSound hSat
  classical
  have hNpos : 0 < N := by rw [hN]; nlinarith
  let a : ℕ → ℕ := fun j =>
    if h : j < s then Classical.choose (hF_gate j h) else 0
  let b : ℕ → ℕ := fun j =>
    if h : j < s then Classical.choose (Classical.choose_spec (hF_gate j h)).2 else 0
  have hab_spec : ∀ j (h : j < s),
      a j < 2 * N + j ∧ b j < 2 * N + j ∧
      (F (2 * N + j) = Set.image2 (fun A B : Finset ℕ => A ∪ B) (F (a j)) (F (b j)) ∨
       F (2 * N + j) = F (a j) ∨
       F (2 * N + j) = {∅} ∨
       F (2 * N + j) = F (a j) ∪ F (b j)) := by
    intro j h
    have h1 := Classical.choose_spec (hF_gate j h)
    have h2 := Classical.choose_spec h1.2
    have ha_eq : a j = Classical.choose (hF_gate j h) := dite_eq_left h
    have hb_eq : b j = Classical.choose h1.2 := dite_eq_left h
    have hNN : N + N + j = 2 * N + j := by omega
    rw [ha_eq, hb_eq, ← hNN]
    exact ⟨h1.1, h2.1, h2.2⟩
  let kind : ℕ → ℕ := fun j =>
    if F (2 * N + j) = Set.image2 (fun A B : Finset ℕ => A ∪ B) (F (a j)) (F (b j)) then 1
    else if F (2 * N + j) = F (a j) then 2
    else if F (2 * N + j) = {∅} then 3
    else 0
  have heval : ∀ (x : ℕ → Bool) (w : ℕ), w < 2 * N + s →
      (ceval N kind a b x w = true ↔ evalF F w x) := by
    intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hwN : w < 2 * N
      · rw [ceval_input N kind a b x hwN, evalF_input hF_in hwN x]
      · let j := w - 2 * N
        have hj : j < s := by omega
        have hw_eq : w = 2 * N + j := by omega
        rcases hab_spec j hj with ⟨ha, hb, hgate⟩
        have iha := ih (a j) (by omega) (by omega)
        have ihb := ih (b j) (by omega) (by omega)
        rw [hw_eq]
        by_cases h1 : F (2 * N + j) = Set.image2 (fun A B : Finset ℕ => A ∪ B) (F (a j)) (F (b j))
        · have hk : kind j = 1 := by dsimp only [kind]; rw [if_pos h1]
          rw [ceval_gate_or N kind a b x hNpos ha hb hk, Bool.or_eq_true, iha, ihb,
              evalF_or h1 x]
        · by_cases h2 : F (2 * N + j) = F (a j)
          · have hk : kind j = 2 := by dsimp only [kind]; rw [if_neg h1, if_pos h2]
            rw [ceval_gate_copy N kind a b x hNpos ha hk, iha]
            unfold evalF; rw [h2]
          · by_cases h3 : F (2 * N + j) = {∅}
            · have hk : kind j = 3 := by dsimp only [kind]; rw [if_neg h1, if_neg h2, if_pos h3]
              rw [ceval_gate_false N kind a b x hNpos hk, evalF_false h3 x]
              simp
            · have h4 : F (2 * N + j) = F (a j) ∪ F (b j) := by
                rcases hgate with g1 | g2 | g3 | g4
                · exact absurd g1 h1
                · exact absurd g2 h2
                · exact absurd g3 h3
                · exact g4
              have hk : kind j = 0 := by dsimp only [kind]; rw [if_neg h1, if_neg h2, if_neg h3]
              rw [ceval_gate_and N kind a b x hNpos ha hb hk, Bool.and_eq_true, iha, ihb,
                  evalF_and h4 x]
  have hv : ValidCirc q N I s o kind a b := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro j hj
      rcases hab_spec j hj with ⟨ha, hb, _⟩
      refine ⟨ha, hb, ?_⟩
      dsimp only [kind]; split_ifs <;> omega
    · intro x p l hpl hp hl
      rw [heval x o (by omega)]
      intro A hA
      rcases hSound A hA p l hpl with hpA | hlA
      · exact ⟨p.val, hpA, hp⟩
      · exact ⟨N + l.val, hlA, hl⟩
    · intro T hT
      cases h : ceval N kind a b (xT N I T) o
      · rfl
      · rw [heval (xT N I T) o (by omega)] at h
        obtain ⟨A, hA, hA_iff⟩ := hSat T hT
        obtain ⟨i, hiA, hix⟩ := h A hA
        by_cases h1 : i < N
        · have hi' : (⟨i, h1⟩ : Fin N).val ∈ A := hiA
          obtain ⟨l, hlT, hil⟩ := (hA_iff ⟨i, h1⟩).1.mp hi'
          simp only [xT, h1, dite_true, decide_eq_true_eq] at hix
          exact False.elim (hix l hlT hil)
        · by_cases h2 : i < 2 * N
          · let p : Fin N := ⟨i - N, by omega⟩
            have hpA : N + p.val ∈ A := by
              have : N + p.val = i := by simp [p]; omega
              rw [this]; exact hiA
            have hpnotT : p ∉ T := (hA_iff p).2.mp hpA
            simp only [xT, h1, h2, dite_false, dite_true, decide_eq_true_eq] at hix
            exact False.elim (hpnotT hix)
          · simp [xT, h1, h2] at hix
  exact circ_lower_bound q N I hq hN hline huniq s o kind a b hv

end PEqualNP.Outside.L_meta_3763

theorem PEqualNP.Outside.L_meta_3763 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → (3 : ℕ) * x2 ≤ x9 + (1 : ℕ) :=
  PEqualNP.Outside.L_meta_3763.main_proof
