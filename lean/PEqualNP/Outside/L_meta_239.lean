import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_239

open PEqualNP.MetaComplexity

def ev (gs : List BinaryGate) (out : ℕ) (x : List Bool) : Bool :=
  (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) x).getD out false

theorem ev_cons (g : BinaryGate) (gs : List BinaryGate) (out : ℕ) (x : List Bool) :
    ev (g :: gs) out x = ev gs out (x ++ [g.op (x.getD g.left false) (x.getD g.right false)]) := rfl

theorem getD_set_ne' (x : List Bool) (i j : ℕ) (v : Bool) (h : j ≠ i) :
    (x.set i v).getD j false = x.getD j false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem set_append_left' (x : List Bool) (i : ℕ) (v c : Bool) (h : i < x.length) :
    x.set i v ++ [c] = (x ++ [c]).set i v := by
  rw [List.set_append_left _ _ h]

theorem set_last (x : List Bool) (a b : Bool) :
    (x ++ [a]).set x.length b = x ++ [b] := by
  simp

theorem getD_last (x : List Bool) (a : Bool) :
    (x ++ [a]).getD x.length false = a := by
  simp

theorem getD_append_left' (x : List Bool) (a : Bool) (i : ℕ) (h : i < x.length) :
    (x ++ [a]).getD i false = x.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem main (gs : List BinaryGate) : ∀ (m out : ℕ) (E : Finset ℕ),
    (∀ i ∈ E, i < m ∧ ∃ x : List Bool, x.length = m ∧
      ev gs out (x.set i (!x.getD i false)) ≠ ev gs out x) → E.card ≤ gs.length + 1 := by
  induction gs with
  | nil =>
    intro m out E hE
    have hsub : E ⊆ {out} := by
      intro i hi
      obtain ⟨_, x, _, hx⟩ := hE i hi
      by_contra hne
      rw [Finset.mem_singleton] at hne
      exact hx (getD_set_ne' x i out _ (Ne.symm hne))
    simpa using Finset.card_le_card hsub
  | cons g gs ih =>
    intro m out E hE
    by_cases hm : ∃ z : List Bool, z.length = m + 1 ∧
        ev gs out (z.set m (!z.getD m false)) ≠ ev gs out z
    · let E' := (E.filter (fun i => i ≠ g.left ∧ i ≠ g.right))
      have h1 : (insert m E').card ≤ gs.length + 1 := by
        apply ih (m + 1) out
        intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact ⟨Nat.lt_succ_self _, hm⟩
        · rw [Finset.mem_filter] at hi
          obtain ⟨hiE, hl, hr⟩ := hi
          obtain ⟨him, x, hxl, hx⟩ := hE i hiE
          refine ⟨by omega, x ++ [g.op (x.getD g.left false) (x.getD g.right false)], by simp [hxl], ?_⟩
          rw [ev_cons, ev_cons, getD_set_ne' x i _ _ (Ne.symm hl), getD_set_ne' x i _ _ (Ne.symm hr),
            set_append_left' x i _ _ (by omega)] at hx
          rwa [getD_append_left' x _ i (by omega)]
      have hmE : m ∉ E' := by
        intro h
        rw [Finset.mem_filter] at h
        exact absurd (hE m h.1).1 (lt_irrefl _)
      rw [Finset.card_insert_of_notMem hmE] at h1
      have h2 : E ⊆ E' ∪ {g.left, g.right} := by
        intro i hi
        by_cases h : i ≠ g.left ∧ i ≠ g.right
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h⟩)
        · apply Finset.mem_union_right
          rw [not_and_or, not_not, not_not] at h
          rcases h with h | h <;> simp [h]
      have h3 := Finset.card_le_card h2
      have h4 := Finset.card_union_le E' {g.left, g.right}
      have h5 : ({g.left, g.right} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      simp only [List.length_cons]
      omega
    · push_neg at hm
      have key : ∀ x : List Bool, x.length = m → ∀ b : Bool,
          ev gs out (x ++ [b]) = ev gs out (x ++ [false]) := by
        intro x hx b
        cases b
        · rfl
        · have := hm (x ++ [false]) (by simp [hx])
          rw [← hx, getD_last, set_last] at this
          exact this
      have h1 : E.card ≤ gs.length + 1 := by
        apply ih (m + 1) out
        intro i hi
        obtain ⟨him, x, hxl, hx⟩ := hE i hi
        refine ⟨by omega, x ++ [false], by simp [hxl], ?_⟩
        rw [ev_cons, ev_cons, key _ (by simp [hxl]), key x hxl,
          set_append_left' x i _ _ (by omega)] at hx
        rwa [getD_append_left' x _ i (by omega)]
      simp only [List.length_cons]
      omega

end PEqualNP.Outside.L_meta_239

theorem PEqualNP.Outside.L_meta_239 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), (∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x) → ∀ s : ℕ, PEqualNP.MetaComplexity.HasBinarySize n f s → n ≤ s + 1 := by
  intro n f hf s ⟨C, hsize, hC⟩
  have h := PEqualNP.Outside.L_meta_239.main C.gates n C.output (Finset.range n) (by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨x, hx⟩ := hf ⟨i, hi⟩
    refine ⟨hi, List.ofFn x, by simp, ?_⟩
    have e1 : (List.ofFn x).set i (!(List.ofFn x).getD i false)
        = List.ofFn (Function.update x ⟨i, hi⟩ (!x ⟨i, hi⟩)) := by
      apply List.ext_getElem
      · simp
      · intro j h1 h2
        simp only [List.getElem_set, List.getElem_ofFn, List.length_ofFn] at *
        by_cases hij : i = j
        · subst hij
          simp [List.getD_eq_getElem?_getD, hi]
        · rw [if_neg hij, Function.update_of_ne]
          intro h
          exact hij (congrArg Fin.val h).symm
    have hev : ∀ y : Fin n → Bool, PEqualNP.Outside.L_meta_239.ev C.gates C.output (List.ofFn y) = f y :=
      fun y => hC y
    rw [e1, hev, hev]
    exact hx)
  simp only [Finset.card_range] at h
  unfold PEqualNP.MetaComplexity.BinaryCircuit.size at hsize
  omega
