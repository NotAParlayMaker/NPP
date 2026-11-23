import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_183

open PEqualNP.MetaComplexity

def occurrences : DMFormula 6 → Fin 6 → ℕ
  | .lit i _, k => if k = i then 1 else 0
  | .and a b, k => occurrences a k + occurrences b k
  | .or a b, k => occurrences a k + occurrences b k

theorem leaves_eq (f : DMFormula 6) : f.leaves = ∑ k, occurrences f k := by
  induction f with
  | lit i b => simp [DMFormula.leaves, occurrences]
  | and a b ha hb => simp [DMFormula.leaves, occurrences, ha, hb, Finset.sum_add_distrib]
  | or a b ha hb => simp [DMFormula.leaves, occurrences, ha, hb, Finset.sum_add_distrib]

theorem eval_congr (f : DMFormula 6) (x y : Fin 6 → Bool)
    (h : ∀ k, occurrences f k ≠ 0 → x k = y k) : f.eval x = f.eval y := by
  induction f with
  | lit i b => simp only [DMFormula.eval, h i (by simp [occurrences])]
  | and a b ha hb =>
    simp only [DMFormula.eval]
    rw [ha (fun k hk => h k (by simp only [occurrences]; omega)),
      hb (fun k hk => h k (by simp only [occurrences]; omega))]
  | or a b ha hb =>
    simp only [DMFormula.eval]
    rw [ha (fun k hk => h k (by simp only [occurrences]; omega)),
      hb (fun k hk => h k (by simp only [occurrences]; omega))]

def assign (x : Fin 6 → Bool) (i j : Fin 6) (a b : Bool) : Fin 6 → Bool :=
  fun k => if k = i then a else if k = j then b else x k

def restricted (f : DMFormula 6) (i j : Fin 6) (x : Fin 6 → Bool) (a b : Bool) : Bool :=
  f.eval (assign x i j a b)

theorem ignores_first (f : DMFormula 6) (i j : Fin 6) (h : occurrences f i = 0)
    (x : Fin 6 → Bool) (a b : Bool) :
    restricted f i j x a b = restricted f i j x false b := by
  apply eval_congr
  intro k hk
  have hki : k ≠ i := by rintro rfl; exact hk h
  simp [assign, hki]

theorem ignores_second (f : DMFormula 6) (i j : Fin 6) (h : occurrences f j = 0)
    (x : Fin 6 → Bool) (a b : Bool) :
    restricted f i j x a b = restricted f i j x a false := by
  apply eval_congr
  intro k hk
  have hkj : k ≠ j := by rintro rfl; exact hk h
  simp [assign, hkj]

def op (isOr a b : Bool) : Bool := if isOr then a || b else a && b

def combine (isOr : Bool) (a b : DMFormula 6) : DMFormula 6 :=
  if isOr then .or a b else .and a b

theorem occurrences_combine (isOr : Bool) (a b : DMFormula 6) (k : Fin 6) :
    occurrences (combine isOr a b) k = occurrences a k + occurrences b k := by
  cases isOr <;> rfl

theorem restrict_combine (isOr : Bool) (l r : DMFormula 6) (i j : Fin 6)
    (x : Fin 6 → Bool) (a b : Bool) :
    restricted (combine isOr l r) i j x a b =
      op isOr (restricted l i j x a b) (restricted r i j x a b) := by
  cases isOr <;> rfl

theorem op_comm (isOr a b : Bool) : op isOr a b = op isOr b a := by
  cases isOr <;> cases a <;> cases b <;> rfl

def Shape (isOr : Bool) (f : Bool → Bool → Bool) : Prop :=
  (∀ a b, f a b = f false b) ∨
  (∀ a b, f a b = f a false) ∨
  ∃ p q : Bool → Bool, ∀ a b, f a b = op isOr (p a) (q b)

theorem shape_const (outer inner c : Bool) (f : Bool → Bool → Bool) (h : Shape inner f) :
    Shape inner (fun a b => op outer (f a b) c) := by
  cases outer <;> cases c
  · exact Or.inl (fun a b => by simp [op])
  · simpa [op] using h
  · simpa [op] using h
  · exact Or.inl (fun a b => by simp [op])

theorem shape_left (isOr : Bool) (l r : DMFormula 6) (i j : Fin 6)
    (hi : occurrences r i = 0) (hj : occurrences r j = 0)
    (g : Bool) (hg : ∀ x, Shape g (restricted l i j x)) :
    ∀ x, Shape g (restricted (combine isOr l r) i j x) := by
  intro x
  have hf : restricted (combine isOr l r) i j x =
      fun a b => op isOr (restricted l i j x a b) (restricted r i j x false false) := by
    funext a b
    rw [restrict_combine, ignores_first r i j hi, ignores_second r i j hj]
  rw [hf]
  exact shape_const _ _ _ _ (hg x)

theorem shape_right (isOr : Bool) (l r : DMFormula 6) (i j : Fin 6)
    (hi : occurrences l i = 0) (hj : occurrences l j = 0)
    (g : Bool) (hg : ∀ x, Shape g (restricted r i j x)) :
    ∀ x, Shape g (restricted (combine isOr l r) i j x) := by
  intro x
  have hf : restricted (combine isOr l r) i j x =
      fun a b => op isOr (restricted r i j x a b) (restricted l i j x false false) := by
    funext a b
    rw [restrict_combine, ignores_first l i j hi, ignores_second l i j hj, op_comm]
  rw [hf]
  exact shape_const _ _ _ _ (hg x)

theorem shape_step (isOr : Bool) (l r : DMFormula 6) (i j : Fin 6)
    (hl : occurrences l i ≤ 1 → occurrences l j ≤ 1 → ∃ g, ∀ x, Shape g (restricted l i j x))
    (hr : occurrences r i ≤ 1 → occurrences r j ≤ 1 → ∃ g, ∀ x, Shape g (restricted r i j x))
    (hi : occurrences (combine isOr l r) i ≤ 1) (hj : occurrences (combine isOr l r) j ≤ 1) :
    ∃ g, ∀ x, Shape g (restricted (combine isOr l r) i j x) := by
  rw [occurrences_combine] at hi hj
  by_cases hli : occurrences l i = 0 <;> by_cases hlj : occurrences l j = 0
  · obtain ⟨g, hg⟩ := hr (by omega) (by omega)
    exact ⟨g, shape_right isOr l r i j hli hlj g hg⟩
  · have hri : occurrences r j = 0 := by omega
    refine ⟨isOr, fun x => Or.inr (Or.inr ⟨
      fun a => restricted r i j x a false, fun b => restricted l i j x false b, ?_⟩)⟩
    intro a b
    rw [restrict_combine, ignores_first l i j hli, ignores_second r i j hri, op_comm]
  · have hrj : occurrences r i = 0 := by omega
    refine ⟨isOr, fun x => Or.inr (Or.inr ⟨
      fun a => restricted l i j x a false, fun b => restricted r i j x false b, ?_⟩)⟩
    intro a b
    rw [restrict_combine, ignores_second l i j hlj, ignores_first r i j hrj]
  · obtain ⟨g, hg⟩ := hl (by omega) (by omega)
    exact ⟨g, shape_left isOr l r i j (by omega) (by omega) g hg⟩

theorem fixed_shape (f : DMFormula 6) (i j : Fin 6) (hij : i ≠ j)
    (hi : occurrences f i ≤ 1) (hj : occurrences f j ≤ 1) :
    ∃ g, ∀ x, Shape g (restricted f i j x) := by
  induction f with
  | lit k s =>
    refine ⟨false, fun x => ?_⟩
    by_cases hk : i = k
    · have hjk : j ≠ k := by intro e; exact hij (hk.trans e.symm)
      exact Or.inr (Or.inl (ignores_second _ _ _ (by simp [occurrences, hjk]) x))
    · exact Or.inl (ignores_first _ _ _ (by simp [occurrences, hk]) x)
  | and l r hl hr => exact shape_step false l r i j hl hr hi hj
  | or l r hl hr => exact shape_step true l r i j hl hr hi hj

theorem shape_unique (g t : Bool) (h : Shape g (op t)) : g = t := by
  rcases h with h | h | ⟨p, q, h⟩
  · cases t
    · have e := h true true
      simp [op] at e
    · have e := h true false
      simp [op] at e
  · cases t
    · have e := h true true
      simp [op] at e
    · have e := h false true
      simp [op] at e
  · cases g <;> cases t
    · rfl
    · have h00 := h false false
      have h01 := h false true
      have h10 := h true false
      cases hp0 : p false <;> cases hp1 : p true <;>
        cases hq0 : q false <;> cases hq1 : q true <;> simp_all [op]
    · have h01 := h false true
      have h10 := h true false
      have h11 := h true true
      cases hp0 : p false <;> cases hp1 : p true <;>
        cases hq0 : q false <;> cases hq1 : q true <;> simp_all [op]
    · rfl

def target (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 0 && x 5)

theorem pair_lower (f : DMFormula 6) (i j : Fin 6) (hij : i ≠ j)
    (he : ∀ x, f.eval x = target x) (base : Fin 6 → Bool)
    (hand : ∀ a b, target (assign (fun _ => false) i j a b) = op false a b)
    (hor : ∀ a b, target (assign base i j a b) = op true a b) :
    3 ≤ occurrences f i + occurrences f j := by
  have and_eq : restricted f i j (fun _ => false) = op false := by
    funext a b
    exact (he _).trans (hand a b)
  have or_eq : restricted f i j base = op true := by
    funext a b
    exact (he _).trans (hor a b)
  have hi : occurrences f i ≠ 0 := by
    intro hz
    have e := ignores_first f i j hz (fun _ => false) true true
    rw [and_eq] at e
    contradiction
  have hj : occurrences f j ≠ 0 := by
    intro hz
    have e := ignores_second f i j hz (fun _ => false) true true
    rw [and_eq] at e
    contradiction
  by_contra h
  obtain ⟨g, hg⟩ := fixed_shape f i j hij (by omega) (by omega)
  have ha := hg (fun _ => false)
  have hb := hg base
  rw [and_eq] at ha
  rw [or_eq] at hb
  have ha' := shape_unique g false ha
  have hb' := shape_unique g true hb
  rw [ha'] at hb'
  contradiction

theorem lower (f : DMFormula 6) (he : ∀ x, f.eval x = target x) : 9 ≤ f.leaves := by
  have h01 := pair_lower f 0 1 (by decide) he (fun k => decide (k = 2 ∨ k = 5))
    (by decide) (by decide)
  have h23 := pair_lower f 2 3 (by decide) he (fun k => decide (k = 1 ∨ k = 4))
    (by decide) (by decide)
  have h45 := pair_lower f 4 5 (by decide) he (fun k => decide (k = 0 ∨ k = 3))
    (by decide) (by decide)
  rw [leaves_eq, Fin.sum_univ_six]
  omega

def upper : DMFormula 6 :=
  .or (.or (.and (.lit 0 true) (.or (.lit 1 true) (.lit 5 true)))
    (.and (.lit 2 true) (.or (.lit 1 true) (.lit 3 true))))
    (.and (.lit 4 true) (.or (.lit 3 true) (.lit 5 true)))

theorem upper_eval (x : Fin 6 → Bool) : upper.eval x = target x := by
  simp only [upper, target, DMFormula.eval, if_pos rfl]
  generalize x 0 = a
  generalize x 1 = b
  generalize x 2 = c
  generalize x 3 = d
  generalize x 4 = e
  generalize x 5 = f
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

end PEqualNP.Outside.L_meta_183

theorem PEqualNP.Outside.L_meta_183 :
  ∀ s : ℕ, PEqualNP.MetaComplexity.HasLeafSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 0 && x 5)) s ↔ 9 ≤ s := by
  intro s
  constructor
  · rintro ⟨f, hsize, he⟩
    exact (PEqualNP.Outside.L_meta_183.lower f he).trans hsize
  · intro hs
    exact ⟨PEqualNP.Outside.L_meta_183.upper, hs, PEqualNP.Outside.L_meta_183.upper_eval⟩
