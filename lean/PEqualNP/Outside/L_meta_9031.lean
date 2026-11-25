import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def L (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [x 0 || x 1]

def fP : (Fin 10 → Bool) → Bool := (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)))

def ind (u v : Fin 10) : Fin 10 → Bool := fun k => decide (k = u ∨ k = v)

def edges : List (Fin 10 × Fin 10) := [(2,3),(3,4),(5,7),(7,9),(9,6),(6,8),(8,5),(2,7),(3,8),(4,9)]

theorem edges_f : ∀ e ∈ edges, fP (ind e.1 e.2) = true := by decide

theorem edges_big : ∀ e ∈ edges, 2 ≤ e.1.val ∧ 2 ≤ e.2.val := by decide

theorem edges_pick : ∀ a b : Fin 11, ∃ e ∈ edges, a.val ≠ e.1.val ∧ a.val ≠ e.2.val ∧ b.val ≠ e.1.val ∧ b.val ≠ e.2.val := by decide

theorem L_len (x : Fin 10 → Bool) : (L x).length = 11 := by simp [L]

theorem L_ind (u v : Fin 10) (hu : 2 ≤ u.val) (hv : 2 ≤ v.val) (a : ℕ) (hau : a ≠ u.val) (hav : a ≠ v.val) :
    (L (ind u v)).getD a false = false := by
  rcases lt_trichotomy a 10 with h | h | h
  · rw [L, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
    rw [List.getElem?_ofFn]
    simp [ind, h, Fin.ext_iff]
    omega
  · subst h
    simp [L, ind, List.getD_eq_getElem?_getD]
    constructor
    · constructor
      · intro e; rw [← e] at hu; simp at hu
      · intro e; rw [← e] at hv; simp at hv
    · constructor
      · intro e; rw [← e] at hu; simp at hu
      · intro e; rw [← e] at hv; simp at hv
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [L_len]; omega)]
    rfl

theorem L_zero (a : ℕ) : (L (fun _ => false)).getD a false = false := by
  rcases lt_trichotomy a 10 with h | h | h
  · rw [L, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
    interval_cases a <;> rfl
  · subst h
    simp [L, List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [L_len]; omega)]
    rfl

theorem pick (a b : ℕ) : ∃ u v : Fin 10, fP (ind u v) = true ∧
    (L (ind u v)).getD a false = false ∧ (L (ind u v)).getD b false = false := by
  obtain ⟨e, he, h1, h2, h3, h4⟩ := edges_pick ⟨min a 10, by omega⟩ ⟨min b 10, by omega⟩
  have hb := edges_big e he
  have hu := e.1.isLt
  have hv := e.2.isLt
  simp only at h1 h2 h3 h4
  refine ⟨e.1, e.2, edges_f e he, L_ind _ _ hb.1 hb.2 a ?_ ?_, L_ind _ _ hb.1 hb.2 b ?_ ?_⟩ <;> omega

theorem dep (C : Circuit) (hF : FanInTwo C) (h1 : C.gates[(1 : ℕ)]? = Option.none) :
    ∃ a b : ℕ, ∀ x y : List Bool, x.length = 11 → y.length = 11 →
      x.getD a false = y.getD a false → x.getD b false = y.getD b false → C.eval x = C.eval y := by
  obtain ⟨gs, o⟩ := C
  match gs with
  | [] =>
    exact ⟨o, o, fun x y _ _ h _ => by simpa [Circuit.eval, Circuit.wires] using h⟩
  | [⟨op, ins⟩] =>
    have hl : ins.length ≤ 2 := (hF ⟨op, ins⟩ (by simp)).2
    have key : ∀ x y : List Bool, x.length = 11 → y.length = 11 →
        (o ≠ 11 → x.getD o false = y.getD o false) →
        (o = 11 → ∀ k ∈ ins, x.getD k false = y.getD k false) →
        Circuit.eval ⟨[⟨op, ins⟩], o⟩ x = Circuit.eval ⟨[⟨op, ins⟩], o⟩ y := by
      intro x y hx hy ho hi
      simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil]
      rcases lt_trichotomy o 11 with h | h | h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
        have := ho (by omega)
        simpa [List.getD_eq_getElem?_getD] using this
      · subst h
        have hm : ins.map (fun i => x.getD i false) = ins.map (fun i => y.getD i false) :=
          List.map_congr_left (hi rfl)
        rw [hm]
        simp [List.getD_eq_getElem?_getD, hx, hy]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    by_cases ho : o = 11
    · match ins, hl with
      | [], _ => exact ⟨o, o, fun x y hx hy _ _ => key x y hx hy (fun h => absurd ho h) (fun _ k hk => by simp at hk)⟩
      | [i], _ => exact ⟨i, i, fun x y hx hy ha _ => key x y hx hy (fun h => absurd ho h) (fun _ k hk => by simp at hk; subst hk; exact ha)⟩
      | [i, j], _ => exact ⟨i, j, fun x y hx hy ha hb => key x y hx hy (fun h => absurd ho h) (fun _ k hk => by
          simp at hk
          rcases hk with hk | hk <;> subst hk <;> assumption)⟩
    · exact ⟨o, o, fun x y hx hy ha _ => key x y hx hy (fun _ => ha) (fun h => absurd h ho)⟩
  | _ :: _ :: _ =>
    simp at h1

end PEqualNP.Outside.L_meta_9031_aux

open PEqualNP.Outside.L_meta_9031_aux in
theorem PEqualNP.Outside.L_meta_9031 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.gates[(1 : ℕ)]? = Option.none → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  intro C hF _ h1
  obtain ⟨a, b, hd⟩ := dep C hF h1
  obtain ⟨u, v, hf, ha, hb⟩ := pick a b
  by_contra hall
  push Not at hall
  have e := hd (L (ind u v)) (L (fun _ => false)) (L_len _) (L_len _)
    (ha.trans (L_zero a).symm) (hb.trans (L_zero b).symm)
  have e1 := hall (ind u v)
  have e2 := hall (fun _ => false)
  have hz : fP (fun _ => false) = false := by decide
  change C.eval (L (ind u v)) = fP (ind u v) at e1
  change C.eval (L (fun _ => false)) = fP (fun _ => false) at e2
  rw [e1, e2, hf, hz] at e
  exact absurd e (by simp)
