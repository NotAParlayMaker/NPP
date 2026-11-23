import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_101

open PEqualNP.ProofComplexity

def neg {n : ℕ} (T : Finset (Fin n)) : Clause (Fin n) := T.image (fun v : Fin n => (v, false))

def VC {n : ℕ} (E : List (Fin n × Fin n)) (k : ℕ) : Set (Clause (Fin n)) :=
  {Ca | ∃ e ∈ E, Ca = {(e.1, true), (e.2, true)}} ∪
    {Cb | ∃ S : Finset (Fin n), S.card = k ∧ Cb = S.image (fun v : Fin n => (v, false))}

theorem neg_card {n : ℕ} (T : Finset (Fin n)) : (neg T).card = T.card := by
  unfold neg
  apply Finset.card_image_of_injective
  intro a b h
  exact (Prod.mk.inj h).1

theorem mem_neg {n : ℕ} (T : Finset (Fin n)) (l : Literal (Fin n)) :
    l ∈ neg T ↔ l.1 ∈ T ∧ l.2 = false := by
  unfold neg
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨l.1, h1, Prod.ext rfl h2.symm⟩

theorem neg_insert_erase {n : ℕ} (T : Finset (Fin n)) (u : Fin n) (hu : u ∉ T) :
    (neg (insert u T)).erase (u, false) = neg T := by
  ext l
  rw [Finset.mem_erase, mem_neg, mem_neg, Finset.mem_insert]
  constructor
  · rintro ⟨h1, h2 | h2, h3⟩
    · exact absurd (Prod.ext h2 h3) h1
    · exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, Or.inr h1, h2⟩
    intro e
    rw [e] at h1
    exact hu h1

theorem append_der {V : Type} [DecidableEq V] (F : Set (Clause V)) (p q : List (Clause V))
    (hp : IsDerivation F p) (hq : IsDerivation F q) : IsDerivation F (p ++ q) := by
  induction hp with
  | nil => exact hq
  | ax _ hC ih => exact IsDerivation.ax ih hC
  | res _ hC hD hR ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR

theorem upper {n : ℕ} (E : List (Fin n × Fin n)) (k : ℕ) (hk : 2 ≤ k)
    (hne : ∀ e ∈ E, e.1 ≠ e.2)
    (hcov : ∀ T : Finset (Fin n), T.card < k → ∃ e ∈ E, e.1 ∉ T ∧ e.2 ∉ T) :
    ∀ m : ℕ, ∀ T : Finset (Fin n), T.card + m = k →
      ∃ p : List (Clause (Fin n)), IsDerivation (VC E k) p ∧ (∀ D ∈ p, D.card ≤ k) ∧ neg T ∈ p := by
  intro m
  induction m with
  | zero =>
    intro T hT
    refine ⟨[neg T], IsDerivation.ax IsDerivation.nil (Or.inr ⟨T, by omega, rfl⟩), ?_, by simp⟩
    intro D hD
    rw [List.mem_singleton] at hD
    rw [hD, neg_card]
    omega
  | succ m ih =>
    intro T hT
    obtain ⟨e, heE, hu, hv⟩ := hcov T (by omega)
    obtain ⟨p1, d1, w1, m1⟩ := ih (insert e.1 T) (by rw [Finset.card_insert_of_notMem hu]; omega)
    obtain ⟨p2, d2, w2, m2⟩ := ih (insert e.2 T) (by rw [Finset.card_insert_of_notMem hv]; omega)
    have huv := hne e heE
    have hedge : ({(e.1, true), (e.2, true)} : Clause (Fin n)) ∈ VC E k := Or.inl ⟨e, heE, rfl⟩
    have hR1 : ({(e.1, true), (e.2, true)} : Clause (Fin n)).erase (e.1, true) ∪
        (neg (insert e.1 T)).erase (e.1, false) = insert (e.2, true) (neg T) := by
      rw [neg_insert_erase T e.1 hu]
      ext l
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (⟨h1, h2 | h2⟩ | h)
        · exact absurd h2 h1
        · exact Or.inl h2
        · exact Or.inr h
      · rintro (h | h)
        · refine Or.inl ⟨?_, Or.inr h⟩
          rw [h]
          intro e'
          exact huv (Prod.mk.inj e').1.symm
        · exact Or.inr h
    have hR2 : (insert (e.2, true) (neg T)).erase (e.2, true) ∪
        (neg (insert e.2 T)).erase (e.2, false) = neg T := by
      rw [neg_insert_erase T e.2 hv]
      ext l
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
      constructor
      · rintro (⟨h1, h2 | h2⟩ | h)
        · exact absurd h2 h1
        · exact h2
        · exact h
      · intro h
        exact Or.inr h
    have dq : IsDerivation (VC E k) (({(e.1, true), (e.2, true)} : Clause (Fin n)) :: (p1 ++ p2)) :=
      IsDerivation.ax (append_der _ _ _ d1 d2) hedge
    have dr1 : IsDerivation (VC E k) (insert (e.2, true) (neg T) ::
        ({(e.1, true), (e.2, true)} : Clause (Fin n)) :: (p1 ++ p2)) := by
      refine IsDerivation.res dq (C := {(e.1, true), (e.2, true)}) (D := neg (insert e.1 T))
        List.mem_cons_self
        (List.mem_cons_of_mem _ (List.mem_append_left _ m1)) ⟨e.1, by simp, ?_, hR1.symm⟩
      rw [mem_neg]
      exact ⟨Finset.mem_insert_self _ _, rfl⟩
    have dr2 : IsDerivation (VC E k) (neg T :: insert (e.2, true) (neg T) ::
        ({(e.1, true), (e.2, true)} : Clause (Fin n)) :: (p1 ++ p2)) := by
      refine IsDerivation.res dr1 (C := insert (e.2, true) (neg T)) (D := neg (insert e.2 T))
        List.mem_cons_self
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ m2)))
        ⟨e.2, Finset.mem_insert_self _ _, ?_, hR2.symm⟩
      rw [mem_neg]
      exact ⟨Finset.mem_insert_self _ _, rfl⟩
    refine ⟨_, dr2, ?_, List.mem_cons_self⟩
    intro D hD
    rcases List.mem_cons.mp hD with h | hD
    · rw [h, neg_card]
      omega
    rcases List.mem_cons.mp hD with h | hD
    · rw [h]
      refine (Finset.card_insert_le _ _).trans ?_
      rw [neg_card]
      omega
    rcases List.mem_cons.mp hD with h | hD
    · rw [h]
      exact (Finset.card_le_two).trans hk
    rcases List.mem_append.mp hD with h | h
    · exact w1 D h
    · exact w2 D h

theorem lower {n : ℕ} (E : List (Fin n × Fin n)) (k : ℕ) (p : List (Clause (Fin n)))
    (hp : IsDerivation (VC E k) p) (hw : ∀ D ∈ p, D.card < k) :
    ∀ D ∈ p, ∃ e ∈ E, D = {(e.1, true), (e.2, true)} := by
  induction hp with
  | nil => intro D hD; simp at hD
  | ax _ hC ih =>
    intro D hD
    rcases List.mem_cons.mp hD with h | h
    · rcases hC with hC | ⟨S, hS, hC⟩
      · rw [h]
        exact hC
      · exfalso
        have h1 := hw D hD
        rw [h, hC] at h1
        have h2 := neg_card S
        unfold neg at h2
        omega
    · exact ih (fun D' hD' => hw D' (List.mem_cons_of_mem _ hD')) D h
  | res _ hC hD' hR ih =>
    intro D hD
    have ih' := ih (fun D' h => hw D' (List.mem_cons_of_mem _ h))
    rcases List.mem_cons.mp hD with h | h
    · exfalso
      obtain ⟨v, -, hv, -⟩ := hR
      obtain ⟨e, -, he⟩ := ih' _ hD'
      rw [he] at hv
      simp at hv
    · exact ih' D h

theorem both {n : ℕ} (E : List (Fin n × Fin n)) (k : ℕ) (hk : 2 ≤ k)
    (hne : ∀ e ∈ E, e.1 ≠ e.2)
    (hcov : ∀ T : Finset (Fin n), T.card < k → ∃ e ∈ E, e.1 ∉ T ∧ e.2 ∉ T) :
    (∃ p, IsRefutation (VC E k) p ∧ ∀ D ∈ p, D.card ≤ k) ∧
      ¬ ∃ p, IsRefutation (VC E k) p ∧ ∀ D ∈ p, D.card ≤ k - 1 := by
  constructor
  · obtain ⟨p, d, w, m⟩ := upper E k hk hne hcov k ∅ (by simp)
    exact ⟨p, ⟨d, m⟩, w⟩
  · rintro ⟨p, ⟨d, m⟩, w⟩
    obtain ⟨e, -, he⟩ := lower E k p d (fun D hD => by have := w D hD; omega) ∅ m
    have h1 : ((e.1, true) : Literal (Fin n)) ∈ (∅ : Clause (Fin n)) := by
      rw [he]
      simp
    simp at h1

end PEqualNP.Outside.L_pcx_101

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_pcx_101 : (∀ F1 : Set (PEqualNP.ProofComplexity.Clause (Fin 10)), F1 = {Ca1 | ∃ ea1 ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)), Ca1 = {(ea1.1, true), (ea1.2, true)}} ∪ {Cb1 | ∃ Sb1 : Finset (Fin 10), Sb1.card = 6 ∧ Cb1 = Sb1.image (fun vb1 : Fin 10 => (vb1, false))} → (∃ πa1, PEqualNP.ProofComplexity.IsRefutation F1 πa1 ∧ ∀ Da1 ∈ πa1, Da1.card ≤ 6) ∧ ¬ ∃ πb1, PEqualNP.ProofComplexity.IsRefutation F1 πb1 ∧ ∀ Db1 ∈ πb1, Db1.card ≤ 5) ∧ (∀ F2 : Set (PEqualNP.ProofComplexity.Clause (Fin 11)), F2 = {Ca2 | ∃ ea2 ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (Fin 11 × Fin 11)), Ca2 = {(ea2.1, true), (ea2.2, true)}} ∪ {Cb2 | ∃ Sb2 : Finset (Fin 11), Sb2.card = 7 ∧ Cb2 = Sb2.image (fun vb2 : Fin 11 => (vb2, false))} → (∃ πa2, PEqualNP.ProofComplexity.IsRefutation F2 πa2 ∧ ∀ Da2 ∈ πa2, Da2.card ≤ 7) ∧ ¬ ∃ πb2, PEqualNP.ProofComplexity.IsRefutation F2 πb2 ∧ ∀ Db2 ∈ πb2, Db2.card ≤ 6) := by
  constructor
  · intro F1 hF
    rw [hF]
    exact PEqualNP.Outside.L_pcx_101.both _ 6 (by norm_num) (by decide) (by decide +kernel)
  · intro F2 hF
    rw [hF]
    exact PEqualNP.Outside.L_pcx_101.both _ 7 (by norm_num) (by decide) (by decide +kernel)
