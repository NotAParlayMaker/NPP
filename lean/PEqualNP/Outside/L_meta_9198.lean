import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9198_aux

open PEqualNP.ProofComplexity PEqualNP.Search

abbrev Var := Fin (3 + 1) × Fin 3
abbrev Lit := Var × Bool

def neg (l : Lit) : Lit := (l.1, !l.2)

theorem neg_eq (l : Lit) : negLit l = neg l := rfl

theorem neg_neg (l : Lit) : neg (neg l) = l := by simp [neg]

-- Unit propagation from S neither adds a literal through D nor falsifies D.
def OK (S : Finset Lit) (D : Finset Lit) : Prop :=
  (∀ l ∈ D, (∀ m ∈ D, m ≠ l → neg m ∈ S) → l ∈ S) ∧ ∃ l ∈ D, neg l ∉ S

-- The same test as a computation.
def okB (S D : Finset Lit) : Bool :=
  decide ((D.filter fun l => l ∉ S ∧ (D.filter fun m => m ≠ l ∧ neg m ∉ S) = ∅) = ∅) &&
    decide (∃ l ∈ D, neg l ∉ S)

theorem okB_ok {S D : Finset Lit} (h : okB S D = true) : OK S D := by
  obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
  refine ⟨fun l hl all => ?_, of_decide_eq_true h2⟩
  by_contra out
  have e := of_decide_eq_true h1
  have mem : l ∈ D.filter fun l => l ∉ S ∧ (D.filter fun m => m ≠ l ∧ neg m ∉ S) = ∅ := by
    refine Finset.mem_filter.mpr ⟨hl, out, Finset.filter_eq_empty_iff.mpr ?_⟩
    intro m hm bad
    exact bad.2 (all m hm bad.1)
  rw [e] at mem
  simp at mem

theorem not_rup {Γ : Set (Clause Var)} {C : Clause Var} (S : Finset Lit)
    (ok : ∀ D ∈ Γ, OK S D) (start : ∀ l ∈ C, neg l ∈ S) : ¬ IsRUP Γ C := by
  rintro ⟨D, hD, conflict⟩
  have forced : ∀ l, UPForces Γ (negLit '' (↑C : Set (Literal Var))) l → l ∈ S := by
    intro l h
    induction h with
    | hyp h =>
      obtain ⟨m, hm, rfl⟩ := h
      exact start m hm
    | unit hE hl _ ih => exact (ok _ hE).1 _ hl ih
  obtain ⟨l, hl, out⟩ := (ok D hD).2
  exact out (forced _ (conflict l hl))

def Sm (v : Var) : Finset Lit := {(v, false)}

def Sp (v : Var) : Finset Lit :=
  Finset.univ.filter fun l => l = (v, true) ∨ (l.2 = false ∧ l.1.2 = v.2 ∧ l.1.1 ≠ v.1)

def pigeon (i : Fin (3 + 1)) : Finset Lit := Finset.univ.image fun j : Fin 3 => ((i, j), true)

def hole (i k : Fin (3 + 1)) (j : Fin 3) : Finset Lit := {((i, j), false), ((k, j), false)}

theorem php_ok (S : Finset Lit) (p : ∀ i, okB S (pigeon i) = true)
    (h : ∀ i k j, i ≠ k → okB S (hole i k j) = true) : ∀ D ∈ PHP (3 + 1) 3, OK S D := by
  rintro D (⟨i, rfl⟩ | ⟨i, k, j, ne, rfl⟩)
  · exact okB_ok (p i)
  · exact okB_ok (h i k j ne)

theorem php_empty : ∀ D ∈ PHP (3 + 1) 3, OK ∅ D :=
  php_ok _ (by decide +kernel) (by decide +kernel)

theorem php_m (v : Var) : ∀ D ∈ PHP (3 + 1) 3, OK (Sm v) D := by
  have p : ∀ v i, okB (Sm v) (pigeon i) = true := by decide +kernel
  have h : ∀ v i k j, i ≠ k → okB (Sm v) (hole i k j) = true := by decide +kernel
  exact php_ok _ (p v) (h v)

theorem php_p (v : Var) : ∀ D ∈ PHP (3 + 1) 3, OK (Sp v) D := by
  have p : ∀ v i, okB (Sp v) (pigeon i) = true := by decide +kernel
  have h : ∀ v i k j, i ≠ k → okB (Sp v) (hole i k j) = true := by decide +kernel
  exact php_ok _ (p v) (h v)

theorem mem_p (v : Var) : (v, true) ∈ Sp v := by simp [Sp]

theorem not_mem_p (v : Var) : (v, false) ∉ Sp v := by simp [Sp]

theorem ok_true {S D : Finset Lit} (l : Lit) (hD : l ∈ D) (hS : l ∈ S) (out : neg l ∉ S) :
    OK S D := by
  refine ⟨fun m _ all => ?_, l, hD, out⟩
  by_cases e : l = m
  · exact e ▸ hS
  · exact absurd (all l hD e) out

theorem ok_free {S D : Finset Lit} (two : 1 < D.card) (free : ∀ l ∈ D, neg l ∉ S) : OK S D := by
  constructor
  · intro l hl all
    obtain ⟨m, hm, ne⟩ := Finset.exists_mem_ne two l
    exact absurd (all m hm ne) (free m hm)
  · obtain ⟨l, hl⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
    exact ⟨l, hl, free l hl⟩

theorem ok_or (D : Finset Lit) (two : 1 < D.card) (v : Var) : OK (Sm v) D ∨ OK (Sp v) D := by
  by_cases h : (v, true) ∈ D
  · exact Or.inr (ok_true (v, true) h (mem_p v) (by simpa [neg] using not_mem_p v))
  · refine Or.inl (ok_free two fun l hl hs => h ?_)
    have e : neg l = (v, false) := by simpa [Sm] using hs
    have e2 : l = (v, true) := by rw [← neg_neg l, e]; rfl
    exact e2 ▸ hl

theorem ok_union {S : Finset Lit} {F : Set (Clause Var)} {ρ : List (Clause Var)}
    (hF : ∀ D ∈ F, OK S D) (hρ : ∀ D ∈ ρ, OK S D) : ∀ D ∈ F ∪ {D | D ∈ ρ}, OK S D := by
  rintro D (h | h)
  · exact hF D h
  · exact hρ D h

theorem small {C : Finset Lit} (h : ¬ 1 < C.card) : C = ∅ ∨ ∃ l, C = {l} := by
  rcases Nat.lt_or_ge C.card 1 with h0 | h1
  · exact Or.inl (Finset.card_eq_zero.mp (by omega))
  · exact Or.inr (Finset.card_eq_one.mp (by omega))

theorem first_two {A : Clause Var} (r : IsRUP (PHP (3 + 1) 3 ∪ {D | D ∈ ([] : List (Clause Var))}) A) :
    1 < A.card := by
  by_contra h
  rcases small h with rfl | ⟨⟨v, b⟩, rfl⟩
  · exact not_rup ∅ (ok_union php_empty (by simp)) (by simp) r
  · cases b
    · exact not_rup (Sp v) (ok_union (php_p v) (by simp)) (by simpa [neg] using mem_p v) r
    · exact not_rup (Sm v) (ok_union (php_m v) (by simp)) (by simp [neg, Sm]) r

theorem second_ne {A B : Clause Var} (two : 1 < A.card)
    (r : IsRUP (PHP (3 + 1) 3 ∪ {D | D ∈ [A]}) B) : B ≠ ∅ := by
  rintro rfl
  refine not_rup ∅ (ok_union php_empty ?_) (by simp) r
  intro D hD
  obtain rfl := List.mem_singleton.mp hD
  exact ok_free two (by simp)

theorem third_ne {A B C : Clause Var} (two : 1 < A.card)
    (r : IsRUP (PHP (3 + 1) 3 ∪ {D | D ∈ [A]}) B)
    (s : IsRUP (PHP (3 + 1) 3 ∪ {D | D ∈ [B, A]}) C) : C ≠ ∅ := by
  rintro rfl
  have pair {S : Finset Lit} (hB : OK S B) (hA : OK S A) : ∀ D ∈ [B, A], OK S D := by
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hB
    · obtain rfl := List.mem_singleton.mp hD
      exact hA
  have one {S : Finset Lit} (hA : OK S A) : ∀ D ∈ [A], OK S D := by
    intro D hD
    obtain rfl := List.mem_singleton.mp hD
    exact hA
  by_cases big : 1 < B.card
  · exact not_rup ∅ (ok_union php_empty (pair (ok_free big (by simp)) (ok_free two (by simp))))
      (by simp) s
  rcases small big with e | ⟨⟨v, b⟩, rfl⟩
  · exact second_ne two r e
  cases b
  · rcases ok_or A two v with hA | hA
    · exact not_rup (Sm v) (ok_union (php_m v)
        (pair (ok_true (v, false) (by simp) (by simp [Sm]) (by simp [neg, Sm])) hA)) (by simp) s
    · exact not_rup (Sp v) (ok_union (php_p v) (one hA)) (by simpa [neg] using mem_p v) r
  · rcases ok_or A two v with hA | hA
    · exact not_rup (Sm v) (ok_union (php_m v) (one hA)) (by simp [neg, Sm]) r
    · exact not_rup (Sp v) (ok_union (php_p v)
        (pair (ok_true (v, true) (by simp) (mem_p v) (by simpa [neg] using not_mem_p v)) hA))
        (by simp) s

theorem main : ¬ (∃ ρ : List (Clause Var), IsRUPRun (PHP (3 + 1) 3) ρ ∧
    (∅ : Clause Var) ∈ ρ ∧ ρ.length ≤ 3) := by
  rintro ⟨ρ, run, mem, len⟩
  cases run with
  | nil => simp at mem
  | @learn ρ1 C1 run1 r1 =>
  cases run1 with
  | nil =>
    have e : C1 = ∅ := by simpa [eq_comm] using mem
    have t := first_two r1
    simp [e] at t
  | @learn ρ2 C2 run2 r2 =>
  cases run2 with
  | nil =>
    have t := first_two r2
    rcases List.mem_cons.mp mem with e | mem
    · exact second_ne t r1 e.symm
    · have e := List.mem_singleton.mp mem
      simp [← e] at t
  | @learn ρ3 C3 run3 r3 =>
  cases run3 with
  | nil =>
    have t := first_two r3
    rcases List.mem_cons.mp mem with e | mem
    · exact third_ne t r2 r1 e.symm
    rcases List.mem_cons.mp mem with e | mem
    · exact second_ne t r2 e.symm
    · have e := List.mem_singleton.mp mem
      simp [← e] at t
  | @learn ρ4 C4 run4 r4 =>
    simp only [List.length_cons] at len
    omega

end PEqualNP.Outside.L_meta_9198_aux

theorem PEqualNP.Outside.L_meta_9198 : ¬ (∃ ρ : List (PEqualNP.ProofComplexity.Clause (Fin (3 + 1) × Fin 3)), PEqualNP.Search.IsRUPRun (PEqualNP.ProofComplexity.PHP (3 + 1) 3) ρ ∧ (∅ : PEqualNP.ProofComplexity.Clause (Fin (3 + 1) × Fin 3)) ∈ ρ ∧ ρ.length ≤ 3) := by
  exact PEqualNP.Outside.L_meta_9198_aux.main
