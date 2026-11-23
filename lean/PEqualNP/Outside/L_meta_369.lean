import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_369_aux

/-- The edges of the 7-cycle, in the order of the statement. -/
def edge : Fin 7 → Fin 7 × Fin 7 := ![(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 6)]

/-- The seven independent sets of size three. -/
def Js : Fin 7 → Finset (Fin 7) :=
  ![{0, 2, 4}, {0, 2, 5}, {0, 3, 5}, {1, 3, 5}, {1, 3, 6}, {1, 4, 6}, {2, 4, 6}]

/-- The one edge that Js k does not touch. -/
def free : Fin 7 → Fin 7 := ![5, 3, 1, 6, 4, 2, 0]

/-- The orientation forced by Js k on each edge (1: from the first end to the second); the
entry at the free edge is a placeholder. -/
def forced : Fin 7 → Fin 7 → ZMod 2 :=
  ![![1, 0, 1, 0, 1, 0, 1], ![1, 0, 1, 0, 0, 1, 1], ![1, 0, 0, 1, 0, 1, 1],
    ![0, 1, 0, 1, 0, 1, 0], ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 1, 0, 0],
    ![0, 0, 1, 0, 1, 0, 0]]

def val (f : Fin 7 → ZMod 2) (k c : Fin 7) : ZMod 2 := if c = free k then f k else forced k c

def L4 : List (Fin 4 → Fin 7) :=
  [![1, 2, 3, 4], ![1, 2, 3, 5], ![1, 2, 3, 6], ![1, 2, 4, 5], ![1, 2, 4, 6], ![1, 2, 5, 6],
    ![1, 3, 4, 5], ![1, 3, 4, 6], ![1, 3, 5, 6], ![1, 4, 5, 6], ![2, 3, 4, 5], ![2, 3, 4, 6],
    ![2, 3, 5, 6], ![2, 4, 5, 6], ![3, 4, 5, 6]]

theorem edge_mem : ∀ c : Fin 7,
    edge c ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 6)] : List (Fin 7 × Fin 7)) := by
  decide

theorem indep : ∀ k : Fin 7, ∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 6)] :
    List (Fin 7 × Fin 7)), ¬ (f.1 ∈ Js k ∧ f.2 ∈ Js k) := by
  decide

theorem tab1 : ∀ k c : Fin 7, c ≠ free k → (edge c).1 ∈ Js k ∨ (edge c).2 ∈ Js k := by decide
theorem tab2 : ∀ k c : Fin 7, (edge c).1 ∈ Js k → forced k c = 1 := by decide
theorem tab3 : ∀ k c : Fin 7, (edge c).2 ∈ Js k → forced k c = 0 := by decide

/-- For every filling of the seven free edges, four of the six differences are independent. -/
theorem core : ∀ f0 f1 f2 f3 f4 f5 f6 : ZMod 2, ∃ s ∈ L4, ∀ g0 g1 g2 g3 : ZMod 2,
    (∀ c : Fin 7,
      g0 * (val ![f0, f1, f2, f3, f4, f5, f6] (s 0) c - val ![f0, f1, f2, f3, f4, f5, f6] 0 c) +
      g1 * (val ![f0, f1, f2, f3, f4, f5, f6] (s 1) c - val ![f0, f1, f2, f3, f4, f5, f6] 0 c) +
      g2 * (val ![f0, f1, f2, f3, f4, f5, f6] (s 2) c - val ![f0, f1, f2, f3, f4, f5, f6] 0 c) +
      g3 * (val ![f0, f1, f2, f3, f4, f5, f6] (s 3) c - val ![f0, f1, f2, f3, f4, f5, f6] 0 c) = 0) →
    g0 = 0 ∧ g1 = 0 ∧ g2 = 0 ∧ g3 = 0 := by
  decide +kernel

end PEqualNP.Outside.L_meta_369_aux

open PEqualNP.Outside.L_meta_369_aux in
theorem PEqualNP.Outside.L_meta_369 : ∀ E : List (Fin 7 × Fin 7), E = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 6)] → ∀ O : Finset (Fin 7) → Finset (Fin 7 × Fin 7), (∀ J : Finset (Fin 7), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) → (∀ d ∈ O J, d ∈ E ∨ (d.2, d.1) ∈ E) ∧ (∀ e ∈ E, (e ∈ O J ∨ (e.2, e.1) ∈ O J) ∧ ¬ (e ∈ O J ∧ (e.2, e.1) ∈ O J)) ∧ (∀ d ∈ O J, d.2 ∉ J)) → PEqualNP.MetaComplexity.SingleLevel.vc E ≤ Module.finrank (ZMod 2) (vectorSpan (ZMod 2) {w : Fin 7 × Fin 7 → ZMod 2 | ∃ J : Finset (Fin 7), (∀ f ∈ E, ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0}) := by
  intro E hE O hO
  subst hE
  -- The cover number is at most 4: the cover {0, 2, 4, 6}.
  have hvc : PEqualNP.MetaComplexity.SingleLevel.vc
      ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 6)] : List (Fin 7 × Fin 7)) ≤ 4 :=
    Nat.sInf_le ⟨{0, 2, 4, 6}, by decide, rfl⟩
  -- The orientation vectors of the seven independent sets of size three.
  let p : Fin 7 → (Fin 7 × Fin 7 → ZMod 2) := fun k d => if d ∈ O (Js k) then 1 else 0
  have hval1 : ∀ k c, (edge c).1 ∈ Js k → p k (edge c) = 1 := by
    intro k c h
    obtain ⟨-, h2, h3⟩ := hO (Js k) (indep k)
    have hs : ((edge c).2, (edge c).1) ∉ O (Js k) := fun hm => h3 _ hm h
    have : edge c ∈ O (Js k) := ((h2 (edge c) (edge_mem c)).1).resolve_right hs
    simp [p, this]
  have hval0 : ∀ k c, (edge c).2 ∈ Js k → p k (edge c) = 0 := by
    intro k c h
    obtain ⟨-, -, h3⟩ := hO (Js k) (indep k)
    have : edge c ∉ O (Js k) := fun hm => h3 _ hm h
    simp [p, this]
  let f : Fin 7 → ZMod 2 := fun k => p k (edge (free k))
  have hval : ∀ k c, p k (edge c) = val f k c := by
    intro k c
    unfold val
    by_cases hc : c = free k
    · rw [if_pos hc, hc]
    · rw [if_neg hc]
      rcases tab1 k c hc with h | h
      · rw [hval1 k c h, tab2 k c h]
      · rw [hval0 k c h, tab3 k c h]
  have hf : f = ![f 0, f 1, f 2, f 3, f 4, f 5, f 6] := by
    funext k
    fin_cases k <;> rfl
  obtain ⟨s, -, hs⟩ := core (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)
  rw [← hf] at hs
  let v : Fin 4 → (Fin 7 × Fin 7 → ZMod 2) := fun i => p (s i) - p 0
  have hli : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have heq : ∀ c : Fin 7,
        g 0 * (val f (s 0) c - val f 0 c) + g 1 * (val f (s 1) c - val f 0 c) +
        g 2 * (val f (s 2) c - val f 0 c) + g 3 * (val f (s 3) c - val f 0 c) = 0 := by
      intro c
      have := congrFun hg (edge c)
      simp only [Finset.sum_apply, Fin.sum_univ_four, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Pi.zero_apply, v, hval] at this
      exact this
    obtain ⟨h0, h1, h2, h3⟩ := hs (g 0) (g 1) (g 2) (g 3) heq
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hmem : ∀ k, p k ∈ {w : Fin 7 × Fin 7 → ZMod 2 | ∃ J : Finset (Fin 7),
      (∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 6)] : List (Fin 7 × Fin 7)),
        ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0} :=
    fun k => ⟨Js k, indep k, rfl⟩
  have hspan : Submodule.span (ZMod 2) (Set.range v) ≤ vectorSpan (ZMod 2) {w : Fin 7 × Fin 7 → ZMod 2 |
      ∃ J : Finset (Fin 7), (∀ f ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (0, 6)] :
        List (Fin 7 × Fin 7)), ¬ (f.1 ∈ J ∧ f.2 ∈ J)) ∧ w = fun d => if d ∈ O J then 1 else 0} := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have := vsub_mem_vectorSpan (ZMod 2) (hmem (s i)) (hmem 0)
    simpa [vsub_eq_sub, v] using this
  have h4 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range v)) = 4 := by
    rw [finrank_span_eq_card hli]
    simp
  have := Submodule.finrank_mono hspan
  omega
