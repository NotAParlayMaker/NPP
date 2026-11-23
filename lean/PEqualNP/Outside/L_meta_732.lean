import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_732_aux

def allB (f : Bool → Bool) : Bool := f false && f true

theorem allB_spec (f : Bool → Bool) (h : allB f = true) (b : Bool) : f b = true := by
  cases b <;> simp_all [allB]

def mk (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Fin 8 → Bool := fun i =>
  match i.val with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5
  | 6 => b6
  | _ => b7

def el : List (Fin 8 × Fin 8) :=
  [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
   (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)]

def al : List (Fin 8 × Fin 8) :=
  [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
   (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]

def vl : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

def ind (w : Fin 8 → Bool) : Bool := el.all fun p => !(w p.1 && w p.2)

def dis (w k : Fin 8 → Bool) : Bool := vl.all fun u => !(k u && w u)

def ex (w k : Fin 8 → Bool) : Bool :=
  vl.any fun v => (!(w v) && !(k v)) && al.all fun p => !(p.1 == v && k p.2)

theorem comp :
    allB (fun a0 => allB fun a1 => allB fun a2 => allB fun a3 =>
      allB fun a4 => allB fun a5 => allB fun a6 => allB fun a7 =>
      !(ind (mk a0 a1 a2 a3 a4 a5 a6 a7)) ||
      allB fun c0 => allB fun c1 => allB fun c2 => allB fun c3 =>
      allB fun c4 => allB fun c5 => allB fun c6 => allB fun c7 =>
      !(ind (mk c0 c1 c2 c3 c4 c5 c6 c7)) ||
      !(dis (mk a0 a1 a2 a3 a4 a5 a6 a7) (mk c0 c1 c2 c3 c4 c5 c6 c7)) ||
      ex (mk a0 a1 a2 a3 a4 a5 a6 a7) (mk c0 c1 c2 c3 c4 c5 c6 c7)) = true := by
  decide +kernel

theorem mk_eta (w : Fin 8 → Bool) :
    mk (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) = w := by
  funext i
  fin_cases i <;> rfl

theorem key (w k : Fin 8 → Bool) (hw : ind w = true) (hk : ind k = true)
    (hd : dis w k = true) : ex w k = true := by
  have h := comp
  have h := allB_spec _ h (w 0)
  have h := allB_spec _ h (w 1)
  have h := allB_spec _ h (w 2)
  have h := allB_spec _ h (w 3)
  have h := allB_spec _ h (w 4)
  have h := allB_spec _ h (w 5)
  have h := allB_spec _ h (w 6)
  have h := allB_spec _ h (w 7)
  beta_reduce at h
  rw [mk_eta w] at h
  simp only [hw, Bool.not_true, Bool.false_or] at h
  have h := allB_spec _ h (k 0)
  have h := allB_spec _ h (k 1)
  have h := allB_spec _ h (k 2)
  have h := allB_spec _ h (k 3)
  have h := allB_spec _ h (k 4)
  have h := allB_spec _ h (k 5)
  have h := allB_spec _ h (k 6)
  have h := allB_spec _ h (k 7)
  beta_reduce at h
  rw [mk_eta k] at h
  simp only [hk, hd, Bool.not_true, Bool.false_or] at h
  exact h

theorem vl_mem : ∀ v : Fin 8, v ∈ vl := by decide

end PEqualNP.Outside.L_meta_732_aux

open PEqualNP.Outside.L_meta_732_aux in
theorem PEqualNP.Outside.L_meta_732 : ∀ (E D : Fin 8 → Fin 8 → Prop),
  (∀ u v, E u v ↔ ((u.val, v.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
      (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)] ∨
    (v.val, u.val) ∈ [(0, 1), (0, 3), (0, 4), (0, 5), (0, 6), (1, 3), (1, 4), (1, 6), (2, 4),
      (2, 6), (2, 7), (3, 4), (3, 5), (3, 7), (4, 5), (4, 6), (4, 7), (5, 7)])) →
  (∀ u v, D u v ↔ (u.val, v.val) ∈ [(0, 3), (0, 4), (1, 0), (1, 6), (2, 4), (2, 6), (3, 1), (3, 5), (3, 7),
      (4, 1), (4, 3), (5, 0), (5, 4), (5, 7), (6, 0), (6, 4), (7, 2), (7, 4)]) →
  (∀ u v, E u v ↔ (D u v ∨ D v u)) ∧ (∀ u v, D u v → ¬ D v u) ∧
  ∀ W K : Set (Fin 8),
    (∀ u ∈ W, ∀ v ∈ W, ¬ E u v) → Disjoint K W → (∀ u ∈ K, ∀ v ∈ K, ¬ E u v) →
    ∃ v, v ∉ W ∧ v ∉ K ∧ ∀ k ∈ K, ¬ D v k := by
  intro E D hE hD
  refine ⟨?_, ?_, ?_⟩
  · simp only [hE, hD]
    decide
  · simp only [hD]
    decide
  · intro W K hW hKW hK
    classical
    have hEl : ∀ p ∈ el, E p.1 p.2 := by
      simp only [hE]
      decide
    have hAl : ∀ u v : Fin 8, D u v → (u, v) ∈ al := by
      simp only [hD]
      decide
    have hw : ind (fun i => decide (i ∈ W)) = true := by
      simp only [ind, List.all_eq_true]
      intro p hp
      have hne : ¬(p.1 ∈ W ∧ p.2 ∈ W) := fun h => hW _ h.1 _ h.2 (hEl p hp)
      simp
      exact not_and_or.mp hne
    have hk : ind (fun i => decide (i ∈ K)) = true := by
      simp only [ind, List.all_eq_true]
      intro p hp
      have hne : ¬(p.1 ∈ K ∧ p.2 ∈ K) := fun h => hK _ h.1 _ h.2 (hEl p hp)
      simp
      exact not_and_or.mp hne
    have hd : dis (fun i => decide (i ∈ W)) (fun i => decide (i ∈ K)) = true := by
      simp only [dis, List.all_eq_true]
      intro u _
      have hne : ¬(u ∈ K ∧ u ∈ W) := fun h => Set.disjoint_left.mp hKW h.1 h.2
      simp
      exact not_and_or.mp hne
    have h := key _ _ hw hk hd
    simp only [ex, List.any_eq_true, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨v, _, ⟨hv1, hv2⟩, hv3⟩ := h
    refine ⟨v, by simpa using hv1, by simpa using hv2, ?_⟩
    intro x hx hDvx
    have h3 := hv3 (v, x) (hAl v x hDvx)
    simp [hx] at h3
