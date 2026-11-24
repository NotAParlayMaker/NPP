import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1563

-- Split an input into its values at 0 and 1 and the other eleven values.
def psi (q : Bool × Bool × (Fin 11 → Bool)) : Fin 13 → Bool := fun v =>
  if v.1 = 0 then q.1 else if v.1 = 1 then q.2.1 else q.2.2 ⟨v.1 - 2, by omega⟩

def phi (x : Fin 13 → Bool) : Bool × Bool × (Fin 11 → Bool) :=
  (x 0, x 1, fun i => x ⟨i.1 + 2, by omega⟩)

def e : Bool × Bool × (Fin 11 → Bool) ≃ (Fin 13 → Bool) where
  toFun := psi
  invFun := phi
  left_inv := by
    rintro ⟨a, b, f⟩
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext i
    simp only [phi, psi]
    rw [if_neg (by omega), if_neg (by omega)]
    congr 1
  right_inv := by
    intro x
    funext v
    simp only [phi, psi]
    split_ifs with h0 h1
    · congr 1
      ext
      simp [h0]
    · congr 1
      ext
      simp [h1]
    · congr 1
      ext
      simp only
      omega

lemma e_zero (q : Bool × Bool × (Fin 11 → Bool)) : e q 0 = q.1 := rfl

lemma e_one (q : Bool × Bool × (Fin 11 → Bool)) : e q 1 = q.2.1 := rfl

lemma count01 : (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 := by
  rw [Finset.card_filter]
  rw [← Fintype.sum_equiv e (fun q => if e q 0 = true ∨ e q 1 = true then 1 else 0) _ (fun q => rfl)]
  simp only [e_zero, e_one, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun]

end PEqualNP.Outside.L_meta_1563

theorem PEqualNP.Outside.L_meta_1563 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    (∀ x y : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) → (∀ v : Fin 13, x v = true → y v = true) → (y 0 = true ∨ y 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → y v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true))).card = 6148 ∧
    (∀ t : Fin 13, ((fun v : Fin 13 => decide (v ∉ L t)) 0 = true ∨ (fun v : Fin 13 => decide (v ∉ L t)) 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → (fun v : Fin 13 => decide (v ∉ L t)) v = true)) ∧
    (Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true)).card = 6144 ∧
    (∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔ (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)))) := by
  intro L hL
  have hL0 : L 0 = {0, 1, 3, 9} := by rw [hL]; decide
  have hmem : ∀ v : Fin 13, v ∈ L 0 ↔ (v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 9) := by
    intro v; rw [hL0]; simp
  have hsplit : ∀ v : Fin 13, v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 9 ∨ v ∉ L 0 := by
    intro v
    by_cases h : v ∈ L 0
    · rw [hmem] at h; tauto
    · tauto
  have hchar : ∀ x : Fin 13 → Bool, (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true) ↔
      (x 0 = true ∨ x 1 = true ∨ x = (fun v : Fin 13 => decide (v ∉ L 0)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3)) ∨ x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9)) ∨
      x = (fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9))) := by
    intro x
    constructor
    · rintro (h | h | hv)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · by_cases h0 : x 0 = true
        · exact Or.inl h0
        by_cases h1 : x 1 = true
        · exact Or.inr (Or.inl h1)
        simp only [Bool.not_eq_true] at h0 h1
        right; right
        cases h3 : x 3 <;> cases h9 : x 9
        · left
          funext v
          rcases hsplit v with rfl | rfl | rfl | rfl | hv'
          · simp [h0, hmem]
          · simp [h1, hmem]
          · simp [h3, hmem]
          · simp [h9, hmem]
          · simp [hv v hv', hv']
        · right; right; left
          funext v
          rcases hsplit v with rfl | rfl | rfl | rfl | hv'
          · simp [h0, hmem]
          · simp [h1, hmem]
          · simp [h3, hmem]
          · simp [h9, hmem]
          · simp [hv v hv', hv']
        · right; left
          funext v
          rcases hsplit v with rfl | rfl | rfl | rfl | hv'
          · simp [h0, hmem]
          · simp [h1, hmem]
          · simp [h3, hmem]
          · simp [h9, hmem]
          · simp [hv v hv', hv']
        · right; right; right
          funext v
          rcases hsplit v with rfl | rfl | rfl | rfl | hv'
          · simp [h0, hmem]
          · simp [h1, hmem]
          · simp [h3, hmem]
          · simp [h9, hmem]
          · simp [hv v hv', hv']
    · rintro (h | h | h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      all_goals (subst h; right; right; intro v hv; simp [hv])
  refine ⟨?_, ?_, ?_, PEqualNP.Outside.L_meta_1563.count01, hchar⟩
  · intro x y hx hxy
    rcases hx with h | h | h
    · exact Or.inl (hxy _ h)
    · exact Or.inr (Or.inl (hxy _ h))
    · exact Or.inr (Or.inr (fun v hv => hxy v (h v hv)))
  · have hset : Finset.univ.filter (fun x : Fin 13 → Bool =>
        (x 0 = true ∨ x 1 = true ∨ ∀ v : Fin 13, v ∉ L 0 → x v = true)) =
        Finset.univ.filter (fun x : Fin 13 → Bool => x 0 = true ∨ x 1 = true) ∪
        ({fun v : Fin 13 => decide (v ∉ L 0), fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3),
          fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 9), fun v : Fin 13 => decide (v ∉ L 0 ∨ v = 3 ∨ v = 9)} :
          Finset (Fin 13 → Bool)) := by
      ext x
      rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, hchar x]
      simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      tauto
    have h3 : (3 : Fin 13) ∈ L 0 := (hmem 3).2 (by decide)
    have h9 : (9 : Fin 13) ∈ L 0 := (hmem 9).2 (by decide)
    have h0 : (0 : Fin 13) ∈ L 0 := (hmem 0).2 (by decide)
    have h1 : (1 : Fin 13) ∈ L 0 := (hmem 1).2 (by decide)
    rw [hset, Finset.card_union_of_disjoint, PEqualNP.Outside.L_meta_1563.count01]
    · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
      · intro h
        have := congrFun h 3
        simp [h3] at this
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · have := congrFun h 3
          simp [h3] at this
        · have := congrFun h 9
          simp [h9] at this
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
        · have := congrFun h 3
          simp [h3] at this
        · have := congrFun h 9
          simp [h9] at this
        · have := congrFun h 3
          simp [h3] at this
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl | rfl | rfl <;> simp [h0, h1] at hx
  · have key : ∀ t : Fin 13, (0 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) ∨
        (1 : Fin 13) ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) ∨
        ∀ v : Fin 13, ¬ (v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 9) → v ∉ ({t, t + 1, t + 3, t + 9} : Finset (Fin 13)) := by
      decide
    intro t
    rw [hL t]
    simp only [decide_eq_true_eq]
    rcases key t with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (fun v hv => h v (fun hv' => hv ((hmem v).2 hv'))))
