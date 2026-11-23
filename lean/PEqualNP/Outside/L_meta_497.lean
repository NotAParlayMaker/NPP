import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_497_aux

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

/-- The clause-by-clause member list: literals of each clause as `some`, then `none`. -/
private def Ml (φ : CNF) : List (Option Literal) :=
  φ.flatMap (fun c => c.map some ++ [none])

/-- The offset function recorded in the statement. -/
private def OFF (φ : CNF) (i : ℕ) : ℕ :=
  ((φ.take i).map (fun c => c.length + 1)).sum

private theorem OFF_zero (φ : CNF) : OFF φ 0 = 0 := rfl

private theorem OFF_apply (φ : CNF) (i : ℕ) :
    OFF φ i = ((φ.take i).map (fun c => c.length + 1)).sum := rfl

private theorem length_Ml (φ : CNF) : (Ml φ).length = OFF φ φ.length := by
  simp only [Ml, OFF, List.length_flatMap, List.map_map, List.length_append,
    List.length_map, List.length_cons, List.length_nil, Function.comp]
  rw [List.take_length]

private theorem length_Ml_take (φ : CNF) (i : ℕ) :
    (Ml (φ.take i)).length = OFF φ i := by
  by_cases hi : i ≤ φ.length
  · rw [length_Ml]
    show ((φ.take i).take (φ.take i).length |>.map fun c => c.length + 1).sum = OFF φ i
    rw [OFF_apply, List.length_take, Nat.min_eq_left hi,
      List.take_of_length_le (by rw [List.length_take]; exact Nat.min_le_left i _)]
  · push Not at hi
    have h1 : φ.take i = φ := List.take_of_length_le (Nat.le_of_lt hi)
    rw [h1]
    have h2 : OFF φ i = OFF φ φ.length := by
      show ((φ.take i).map fun c => c.length + 1).sum =
        ((φ.take φ.length).map fun c => c.length + 1).sum
      rw [h1, List.take_of_length_le (Nat.le_refl φ.length)]
    rw [length_Ml, h2]

private theorem take_succ_eq (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    φ.take (i + 1) = φ.take i ++ [φ.getD i []] := by
  rw [List.getD_eq_getElem _ _ hi, List.take_add_one, List.getElem?_eq_getElem hi,
    Option.toList_some]

private theorem OFF_succ (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    OFF φ (i + 1) = OFF φ i + (φ.getD i []).length + 1 := by
  rw [OFF_apply, OFF_apply, take_succ_eq φ hi, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  omega

private theorem OFF_mono (φ : CNF) {a b : ℕ} (hab : a ≤ b) : OFF φ a ≤ OFF φ b := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hab
  have h : φ.take (a + d) = φ.take a ++ (φ.drop a).take d := List.take_add
  rw [OFF_apply, OFF_apply, h, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

private theorem OFF_strict (φ : CNF) {a b : ℕ} (h : a < b) (hb : b ≤ φ.length) :
    OFF φ a < OFF φ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  have hlt : a + d < φ.length := by omega
  have h1 := OFF_succ φ hlt
  have h3 := OFF_mono φ (Nat.le_add_right a d)
  change OFF φ a < OFF φ (a + d + 1)
  omega


/-- Every clause contributes at least `|c| + 1` bits to the encoding. -/
private theorem Ml_le_encode (φ : CNF) :
    (Ml φ).length ≤ (encodeCNF φ).length := by
  simp only [Ml, encodeCNF, List.length_flatMap, List.map_map, Function.comp]
  apply List.sum_le_sum
  rintro c -
  simp only [encodeClause, List.length_flatMap, List.map_map, Function.comp,
    List.length_append, List.length_map, List.length_cons, List.length_nil]
  have hlit : ∀ l : Literal, 1 ≤ (encodeLiteral l).length := fun l => by
    simp [encodeLiteral]
  calc c.length + 1
      ≤ (c.map fun l => (encodeLiteral l).length).sum + 1 := by
        have := List.sum_le_sum (l := c) (fun l _ => hlit l)
        simpa [List.map_const] using this
    _ ≤ (c.map fun l => (encodeLiteral l).length).sum + 2 := by omega

/-- `φ` splits around clause `i`. -/
private theorem Ml_decomp (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    Ml φ = Ml (φ.take i) ++ ((φ.getD i []).map some ++ [none]) ++ Ml (φ.drop (i + 1)) := by
  have hφ : φ = φ.take (i + 1) ++ φ.drop (i + 1) := (List.take_append_drop _ _).symm
  conv_lhs => rw [hφ, Ml, List.flatMap_append]
  rw [take_succ_eq φ hi, Ml, List.flatMap_append]
  simp [Ml]

private theorem Ml_lt_off_succ (φ : CNF) {i j : ℕ} (hi : i < φ.length)
    (hj : j ≤ (φ.getD i []).length) : OFF φ i + j < OFF φ (i + 1) := by
  rw [OFF_succ φ hi]; omega

/-- Position `off i + j` of `Ml φ` is entry `j` of clause `i`'s block. -/
private theorem Ml_getElem (φ : CNF) {i j : ℕ} (hi : i < φ.length)
    (hj : j ≤ (φ.getD i []).length) :
    (Ml φ)[OFF φ i + j]? =
      some (((φ.getD i []).map some ++ [none]).getD j none) := by
  have hj' : j ≤ (φ[i]?.getD []).length := hj
  conv_lhs => rw [Ml_decomp φ hi]
  rw [List.getElem?_append_left (show OFF φ i + j <
      (Ml (φ.take i) ++ ((φ.getD i []).map some ++ [none])).length by
    rw [List.length_append, length_Ml_take, List.length_append, List.length_map,
      List.length_cons, List.length_nil]
    omega)]
  rw [List.getElem?_append_right (show (Ml (φ.take i)).length ≤ OFF φ i + j by
    rw [length_Ml_take]; omega)]
  rw [length_Ml_take, Nat.add_sub_cancel_left]
  have hj2 : j < ((φ.getD i []).map some ++ [none]).length := by
    rw [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  rw [List.getElem?_eq_getElem hj2, List.getD_eq_getElem _ _ hj2]

/-- Every position of `Ml φ` sits in some clause block. -/
private theorem Ml_pos (φ : CNF) {m : ℕ} (hm : m < (Ml φ).length) :
    ∃ i j, i < φ.length ∧ j ≤ (φ.getD i []).length ∧ m = OFF φ i + j := by
  induction φ generalizing m with
  | nil => simp [Ml] at hm
  | cons c φ ih =>
    rw [Ml, List.flatMap_cons, List.length_append, List.length_append,
      List.length_map, List.length_cons, List.length_nil] at hm
    by_cases h : m < c.length + 1
    · refine ⟨0, m, by simp, by simp; omega, by simp [OFF]⟩
    · have h3 : (List.flatMap (fun c => List.map some c ++ [none]) (c :: φ)).length =
          c.length + 1 +
            (List.flatMap (fun c => List.map some c ++ [none]) φ).length := by
        simp [List.flatMap_cons]; omega
      have hm2 : m - (c.length + 1) < (Ml φ).length := by
        simp only [Ml]
        omega
      obtain ⟨i, j, hi, hj, hm'⟩ := ih hm2
      refine ⟨i + 1, j, by simp; omega, by simpa using hj, ?_⟩
      have h2 : OFF (c :: φ) (i + 1) = c.length + 1 + OFF φ i := by
        rw [OFF_apply, OFF_apply, List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

/-- Clause-block positions are unique. -/
private theorem OFF_inj (φ : CNF) {i i' j j' : ℕ}
    (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length)
    (hi' : i' < φ.length) (hj' : j' ≤ (φ.getD i' []).length)
    (h : OFF φ i + j = OFF φ i' + j') : i = i' ∧ j = j' := by
  rcases lt_trichotomy i i' with hlt | rfl | hgt
  · have h1 := OFF_succ φ (lt_trans hlt hi')
    have h2 := OFF_mono φ (show i + 1 ≤ i' by omega)
    omega
  · exact ⟨rfl, by omega⟩
  · have h1 := OFF_succ φ (lt_trans hgt hi)
    have h2 := OFF_mono φ (show i' + 1 ≤ i by omega)
    omega

/-- A variable occurs when some clause has a literal on it. -/
private theorem mem_vars {φ : CNF} {z : ℕ} :
    z ∈ vars φ ↔ ∃ c ∈ φ, ∃ l ∈ c, l.1 = z := by
  unfold vars
  rw [List.mem_toFinset]
  simp only [List.mem_flatMap, List.mem_map, Prod.exists, exists_and_right]

private theorem fresh_gt {φ : CNF} {z : ℕ} (hz : z ∈ vars φ) : z < fresh φ := by
  have h : id z ≤ (vars φ).sup id := Finset.le_sup hz
  simp only [fresh, id] at h ⊢
  omega

private theorem fresh_not_mem (φ : CNF) : fresh φ ∉ vars φ := by
  intro h
  have := fresh_gt h
  omega

private theorem vars_cvc (φ : CNF) :
    vars (cvcFormula φ) = insert (fresh φ) (vars φ) := by
  ext z
  have hunfold : z ∈ vars (cvcFormula φ) ↔
      (∃ c ∈ φ, ∃ a ∈ c, a.1 = z) ∨ z = fresh φ := by
    rw [mem_vars]
    constructor
    · rintro ⟨c', hc', l, hl, rfl⟩
      rw [cvcFormula, List.mem_append] at hc'
      rcases hc' with hc' | hc'
      · obtain ⟨c, hc, hcEq⟩ := List.mem_map.1 hc'
        subst hcEq
        rw [List.mem_append, List.mem_singleton] at hl
        rcases hl with hl | rfl
        · exact Or.inl ⟨c, hc, l, hl, rfl⟩
        · exact Or.inr rfl
      · rw [List.mem_singleton] at hc'
        subst hc'
        rw [List.mem_singleton] at hl
        cases hl
        exact Or.inr rfl
    · rintro (⟨c, hc, a, ha, rfl⟩ | rfl)
      · exact ⟨c ++ [(fresh φ, true)], List.mem_append_left _
            (List.mem_map.2 ⟨c, hc, rfl⟩), a, List.mem_append_left _ ha, rfl⟩
      · exact ⟨[(fresh φ, false)], List.mem_append_right _ (List.mem_singleton_self _),
            (fresh φ, false), List.mem_singleton_self _, rfl⟩
  rw [hunfold]
  simp only [Finset.mem_insert, mem_vars, or_comm]

/-- `c'ᵢ` for `i` inside `φ` is the clause extended by the fresh literal. -/
private theorem cvc_getD_lt (φ : CNF) {i : ℕ} (hi : i < φ.length) :
    (cvcFormula φ).getD i [] = (φ.getD i []) ++ [(fresh φ, true)] := by
  rw [cvcFormula,
    List.getD_append (φ.map (fun C => C ++ [(fresh φ, true)])) [[(fresh φ, false)]] [] i
      (by simp [List.length_map]; omega)]
  rw [List.getD_eq_getElem _ _ (by simp [List.length_map]; omega),
    List.getElem_map, List.getD_eq_getElem _ _ hi]

/-- `c'_{len}` is the unit clause on the fresh variable. -/
private theorem cvc_getD_len (φ : CNF) :
    (cvcFormula φ).getD φ.length [] = [(fresh φ, false)] := by
  rw [cvcFormula,
    List.getD_append_right (φ.map (fun C => C ++ [(fresh φ, true)])) [[(fresh φ, false)]] []
      φ.length (by simp [List.length_map])]
  simp [List.length_map]

/-- `c'ᵢ` is empty past the unit clause. -/
private theorem cvc_getD_gt (φ : CNF) {i : ℕ} (hi : φ.length < i) :
    (cvcFormula φ).getD i [] = [] := by
  apply List.getD_eq_default
  simp only [cvcFormula, List.length_append, List.length_map, List.length_cons,
    List.length_nil]
  omega


/-- `inner` blocks are disjoint from vertex numbers: all their elements are `≥ N`. -/
private theorem inner_ge {inner : ℕ → ℕ → Bool → List ℕ} {k N u v : ℕ} {b : Bool} {x : ℕ}
    (hinner : ∀ u v b, inner u v b =
      ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map
        (fun t => N + 2 * k * (u * N + v) + t))
    (hx : x ∈ inner u v b) : N ≤ x := by
  rw [hinner] at hx
  simp only [List.mem_map, List.mem_filter, List.mem_range] at hx
  obtain ⟨t, ⟨_, _⟩, rfl⟩ := hx
  omega

/-- An `inner` block is nodup: it maps an injective function over a filtered range. -/
private theorem inner_nodup {inner : ℕ → ℕ → Bool → List ℕ} {k N u v : ℕ} {b : Bool}
    (hinner : ∀ u v b, inner u v b =
      ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map
        (fun t => N + 2 * k * (u * N + v) + t)) :
    (inner u v b).Nodup := by
  rw [hinner]
  apply List.Nodup.map (l := ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)))
    (f := fun t => N + 2 * k * (u * N + v) + t)
  · intro a b h; dsimp only at h; omega
  · exact List.Nodup.filter _ List.nodup_range

/-- Membership in an `inner` block: the elements with `t` of parity `b`. -/
private theorem inner_mem {inner : ℕ → ℕ → Bool → List ℕ} {k N u v : ℕ} {b : Bool} {x : ℕ}
    (hinner : ∀ u v b, inner u v b =
      ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map
        (fun t => N + 2 * k * (u * N + v) + t)) :
    x ∈ inner u v b ↔ ∃ t < 2 * k, x = N + 2 * k * (u * N + v) + t ∧ (t % 2 = 1 ↔ b) := by
  rw [hinner]
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨t, ⟨ht, hp⟩, rfl⟩
    exact ⟨t, ht, rfl, by
      cases b <;> rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp_all⟩
  · rintro ⟨t, ht, rfl, hp⟩
    exact ⟨t, ⟨ht, by
      cases b <;> rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp_all⟩, rfl⟩

/-- Blocks decode uniquely: equal block elements have equal `(u, v, t)`. -/
private theorem block_inj {N k : ℕ} (hk : 0 < k) {u₁ v₁ t₁ u₂ v₂ t₂ : ℕ}
    (hu₁ : u₁ < N) (hv₁ : v₁ < N) (hu₂ : u₂ < N) (hv₂ : v₂ < N)
    (ht₁ : t₁ < 2 * k) (ht₂ : t₂ < 2 * k)
    (h : N + 2 * k * (u₁ * N + v₁) + t₁ = N + 2 * k * (u₂ * N + v₂) + t₂) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ t₁ = t₂ := by
  have hk2 : 0 < 2 * k := by omega
  have hle12 : u₁ * N + v₁ ≤ u₂ * N + v₂ := by
    by_contra hc
    push_neg at hc
    have e2 : 2 * k * (u₂ * N + v₂ + 1) = 2 * k * (u₂ * N + v₂) + 2 * k := by ring
    have le1 : 2 * k * (u₂ * N + v₂ + 1) ≤ 2 * k * (u₁ * N + v₁) :=
      Nat.mul_le_mul_left _ hc
    omega
  have hle21 : u₂ * N + v₂ ≤ u₁ * N + v₁ := by
    by_contra hc
    push_neg at hc
    have e2 : 2 * k * (u₁ * N + v₁ + 1) = 2 * k * (u₁ * N + v₁) + 2 * k := by ring
    have le1 : 2 * k * (u₁ * N + v₁ + 1) ≤ 2 * k * (u₂ * N + v₂) :=
      Nat.mul_le_mul_left _ hc
    omega
  have hS : u₁ * N + v₁ = u₂ * N + v₂ := Nat.le_antisymm hle12 hle21
  have ht : t₁ = t₂ := by
    have h' := h
    rw [hS] at h'
    omega
  have hv : v₁ = v₂ := by
    have h1 : v₁ = (u₁ * N + v₁) % N := by
      rw [Nat.mul_comm u₁ N, Nat.mul_add_mod, Nat.mod_eq_of_lt hv₁]
    have h2 : v₂ = (u₂ * N + v₂) % N := by
      rw [Nat.mul_comm u₂ N, Nat.mul_add_mod, Nat.mod_eq_of_lt hv₂]
    rw [h1, hS, ← h2]
  have hN : 0 < N := by omega
  have hu : u₁ = u₂ := by
    have : u₁ * N = u₂ * N := by omega
    exact Nat.eq_of_mul_eq_mul_right hN this
  exact ⟨hu, hv, ht⟩

end PEqualNP.Outside.L_meta_497_aux

open PEqualNP.Outside.L_meta_497_aux PEqualNP.MetaComplexity.CoverPromise in
theorem PEqualNP.Outside.L_meta_497 :
    ∀ k : ℕ, ∀ (φ : PEqualNP.Search.CNF) (E N : ℕ) (off : ℕ → ℕ) (e : ℕ → ℕ),
    E = (PEqualNP.Search.encodeCNF φ).length → N = 3 * (E + 1) →
    (∀ i, off i = ((φ.take i).map (fun c => c.length + 1)).sum) →
    (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z < E) →
    (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
      ∀ z' ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, e z = e z' → z = z') →
    (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ,
      ∃ l : PEqualNP.Search.Literal,
        (φ.flatMap (fun c => c.map some ++ [none]))[e z]? = some (some l) ∧ l.1 = z) →
    ∀ num : PEqualNP.MetaComplexity.CoverPromise.Vertex → ℕ,
    (∀ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, ∀ b : Bool,
      num (Sum.inl (z, b)) = 2 * e z + (if b then 1 else 0)) →
    (∀ b : Bool, num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, b)) =
      2 * E + (if b then 1 else 0)) →
    (∀ i j, i < φ.length → j ≤ (φ.getD i []).length →
      num (Sum.inr (i, j)) = 2 * (E + 1) + off i + j) →
    num (Sum.inr (φ.length, 0)) = 3 * E + 2 →
    ∀ H : SimpleGraph (Fin N),
    (∀ a b : Fin N, H.Adj a b ↔ ∃ u v,
      (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v ∧
        num u = a.val ∧ num v = b.val) →
    ∀ (f : ℕ → ℕ),
    (∀ i, f i = ((φ.getD i []) ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).findIdx
      (fun l => l.2)) →
    ∀ TH : ℕ → Prop,
    (∀ a, TH a ↔ ((∃ z ∈ PEqualNP.MetaComplexity.CoverPromise.vars φ, a = 2 * e z + 1) ∨
      a = 2 * E + 1 ∨ (∃ i < φ.length, ∃ j ≤ (φ.getD i []).length, j ≠ f i ∧
        a = 2 * (E + 1) + off i + j) ∨ a = 3 * E + 2)) →
    ∀ lit : ℕ → ℕ → PEqualNP.Search.Literal,
    (∀ i j, lit i j = ((φ.getD i []) ++
      [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)]).getD j (0, false)) →
    ∀ inner : ℕ → ℕ → Bool → List ℕ,
    (∀ u v b, inner u v b = ((List.range (2 * k)).filter (fun t => (t % 2 == 1) == b)).map
      (fun t => N + 2 * k * (u * N + v) + t)) →
    ∀ TL : List ℕ,
    TL = (List.range φ.length).flatMap (fun i =>
      (List.range ((φ.getD i []).length + 1)).flatMap (fun j =>
        inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l)))
            (decide (j ≠ f i))) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
          else []) ++
        (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else []))) ++
      (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)))
        (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++
      inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)))
        (num (Sum.inr (φ.length, 0))) false ++
      [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)),
        num (Sum.inr (φ.length, 0))]) →
    TL.Nodup ∧ ∀ x : ℕ, x ∈ TL ↔ (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧
      ∃ t < 2 * k, x = N + 2 * k * (u.val * N + v.val) + t ∧ (t % 2 = 1 ↔ TH u.val)) := by
  classical
  intro k φ E N off e hE hN hoff hElt hEinj hElit
  intro num hninl hnfr hninr hntail
  intro H hadj f hf TH hTH lit hlit inner hinner TL hTL
  -- scalar facts
  have hOFF : ∀ i, off i = OFF φ i := fun i => hoff i
  have hElen : (Ml φ).length ≤ E := hE ▸ Ml_le_encode φ
  have helt {z : ℕ} (hz : z ∈ vars φ) : e z < E := hElt z hz
  have heltMl {z : ℕ} (hz : z ∈ vars φ) : e z < (Ml φ).length := by
    obtain ⟨l, h1, _⟩ := hElit z hz
    exact (List.getElem?_eq_some_iff.1 h1).1
  -- off bounds
  have hofflt {i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      off i + j < E := by
    have h1 : off i + j + 1 ≤ OFF φ (i + 1) := by
      simp only [hOFF]; rw [OFF_succ φ hi]; omega
    have h2 : OFF φ (i + 1) ≤ OFF φ φ.length := OFF_mono φ (by omega)
    have h3 : OFF φ φ.length ≤ E := by rw [← length_Ml]; exact hElen
    omega
  have hofflen : off φ.length = (Ml φ).length := by rw [hOFF, length_Ml]
  -- lit facts
  have hlitD {i j : ℕ} (hi : i < φ.length) :
      lit i j = (φ.getD i [] ++ [(fresh φ, true)]).getD j (0, false) := hlit i j
  have hlit_lt {i j : ℕ} (hi : i < φ.length) (hj : j < (φ.getD i []).length) :
      lit i j = (φ.getD i []).getD j (0, false) := by
    rw [hlitD hi, List.getD_append _ _ _ _ hj]
  have hlit_len {i : ℕ} (hi : i < φ.length) :
      lit i (φ.getD i []).length = (fresh φ, true) := by
    rw [hlitD hi, List.getD_append_right _ _ _ _ (Nat.le_refl _)]
    simp
  have hlit_var {i j : ℕ} (hi : i < φ.length) (hj : j < (φ.getD i []).length) :
      (lit i j).1 ∈ vars φ := by
    rw [hlit_lt hi hj, List.getD_eq_getElem _ _ hj]
    have h1 : φ.getD i [] = φ[i] := List.getD_eq_getElem _ _ hi
    exact mem_vars.2 ⟨φ.getD i [], by rw [h1]; exact List.getElem_mem _,
      (φ.getD i [])[j], List.getElem_mem _, rfl⟩
  -- variable site: e z sits at some (i, j)
  have hSite {z : ℕ} (hz : z ∈ vars φ) :
      ∃ i j, i < φ.length ∧ j < (φ.getD i []).length ∧ off i + j = e z ∧
        (lit i j).1 = z := by
    obtain ⟨l, hml, hl1⟩ := hElit z hz
    obtain ⟨i, j, hi, hj, hoff_eq⟩ := Ml_pos φ (heltMl hz)
    have hml' : (Ml φ)[OFF φ i + j]? = some (some l) := hoff_eq ▸ hml
    rw [Ml_getElem φ hi hj] at hml'
    have hb : ((φ.getD i []).map some ++ [none]).getD j none = some l := by
      simpa using hml'
    rcases Nat.lt_or_ge j (φ.getD i []).length with hjt | hjt
    · rw [List.getD_append (List.map some (φ.getD i [])) [none] none j
        (by simpa using hjt)] at hb
      rw [List.getD_eq_getElem _ _ (by simpa using hjt), List.getElem_map] at hb
      have hl : lit i j = l := by
        rw [hlit_lt hi hjt, List.getD_eq_getElem _ _ hjt]; exact Option.some.inj hb
      refine ⟨i, j, hi, hjt, by simp only [hOFF]; omega, ?_⟩
      rw [hl]; exact hl1
    · have hj' : j = (φ.getD i []).length := by omega
      rw [List.getD_append_right _ _ _ _ (by simpa using hjt), hj'] at hb
      simp at hb
  -- num bounds
  have hninl_le {z : ℕ} (hz : z ∈ vars φ) (b : Bool) :
      num (Sum.inl (z, b)) ≤ 2 * E + 1 := by
    rw [hninl z hz b]; have := hElt z hz; cases b <;> simp <;> omega
  have hninl_ltN {z : ℕ} (hz : z ∈ vars φ) (b : Bool) :
      num (Sum.inl (z, b)) < N := by
    rw [hN]; have := hninl_le hz b; omega
  have hninl_fr_le (b : Bool) : num (Sum.inl (fresh φ, b)) ≤ 2 * E + 1 := by
    rw [hnfr b]; cases b <;> simp <;> omega
  have hninl_fr_ltN (b : Bool) : num (Sum.inl (fresh φ, b)) < N := by
    rw [hN]; have := hninl_fr_le b; omega
  have hninr_ge {i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      2 * (E + 1) ≤ num (Sum.inr (i, j)) := by
    rw [hninr i j hi hj]; omega
  have hninr_le {i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      num (Sum.inr (i, j)) ≤ 3 * E + 1 := by
    rw [hninr i j hi hj]; have := hofflt hi hj; omega
  have hninr_ltN {i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      num (Sum.inr (i, j)) < N := by
    rw [hN]; have := hninr_le hi hj; omega
  have hntail_ltN : num (Sum.inr (φ.length, 0)) < N := by rw [hntail, hN]; omega
  -- num injectivity
  have hninl_inj {z z' : ℕ} {b b' : Bool} (hz : z ∈ vars φ) (hz' : z' ∈ vars φ)
      (h : num (Sum.inl (z, b)) = num (Sum.inl (z', b'))) : z = z' ∧ b = b' := by
    rw [hninl z hz b, hninl z' hz' b'] at h
    have h1 : ∀ b : Bool, (if b then 1 else 0 : ℕ) = b.toNat :=
      fun b => by cases b <;> rfl
    rw [h1, h1] at h
    have h4 : b.toNat = b'.toNat := by
      have := Bool.toNat_le b; have := Bool.toNat_le b'; omega
    have hbb : b = b' := by cases b <;> cases b' <;> simp at h4 ⊢
    subst hbb
    have hzeq : e z = e z' := by omega
    exact ⟨hEinj z hz z' hz' hzeq, rfl⟩
  have hninr_inj {i i' j j' : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length)
      (hi' : i' < φ.length) (hj' : j' ≤ (φ.getD i' []).length)
      (h : num (Sum.inr (i, j)) = num (Sum.inr (i', j'))) : i = i' ∧ j = j' := by
    rw [hninr i j hi hj, hninr i' j' hi' hj'] at h
    have hoff' : OFF φ i + j = OFF φ i' + j' := by simp only [hOFF] at h; omega
    exact OFF_inj φ hi hj hi' hj' hoff'
  -- band separations
  have hband_inl_inr {z : ℕ} (hz : z ∈ vars φ) (b : Bool) {i j : ℕ}
      (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      num (Sum.inl (z, b)) < num (Sum.inr (i, j)) := by
    rw [hninr i j hi hj]; have := hninl_le hz b; omega
  have hband_fr_inr (b : Bool) {i j : ℕ}
      (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      num (Sum.inl (fresh φ, b)) < num (Sum.inr (i, j)) := by
    rw [hninr i j hi hj]; have := hninl_fr_le b; omega
  have hband_inl_tail {z : ℕ} (hz : z ∈ vars φ) (b : Bool) :
      num (Sum.inl (z, b)) < num (Sum.inr (φ.length, 0)) := by
    rw [hntail]; have := hninl_le hz b; omega
  have hband_fr_tail (b : Bool) :
      num (Sum.inl (fresh φ, b)) < num (Sum.inr (φ.length, 0)) := by
    rw [hntail]; have := hninl_fr_le b; omega
  have hband_inr_tail {i j : ℕ}
      (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      num (Sum.inr (i, j)) < num (Sum.inr (φ.length, 0)) := by
    rw [hntail]; have := hninr_le hi hj; omega
  -- TH facts
  have hTHv {z : ℕ} (hz : z ∈ vars φ) : TH (2 * e z + 1) :=
    (hTH _).2 (Or.inl ⟨z, hz, rfl⟩)
  have hTH2E1 : TH (2 * E + 1) := (hTH _).2 (Or.inr (Or.inl rfl))
  have hTH3E2 : TH (3 * E + 2) := (hTH _).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hTHn2ez {z : ℕ} (hz : z ∈ vars φ) : ¬ TH (2 * e z) := by
    intro h
    rcases (hTH _).1 h with ⟨z', hz', h'⟩ | h' | ⟨i, hi, j, hj, -, h'⟩ | h'
    · have := hElt z' hz'; omega
    · omega
    · have := hofflt hi hj; have := hElt z hz; omega
    · have := hElt z hz; omega
  have hTHn2E : ¬ TH (2 * E) := by
    intro h
    rcases (hTH _).1 h with ⟨z', hz', h'⟩ | h' | ⟨i, hi, j, hj, -, h'⟩ | h'
    · have := hElt z' hz'; omega
    · omega
    · have := hofflt hi hj; omega
    · omega
  have hTHinl_iff {z : ℕ} (hz : z ∈ vars φ) (b : Bool) :
      TH (num (Sum.inl (z, b))) ↔ b := by
    rw [hninl z hz b]; cases b <;> simp [hTHn2ez hz, hTHv hz]
  have hTHinl_fr_iff (b : Bool) : TH (num (Sum.inl (fresh φ, b))) ↔ b := by
    rw [hnfr b]; cases b <;> simp [hTHn2E, hTH2E1]
  have hTHinr_iff {i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      TH (num (Sum.inr (i, j))) ↔ j ≠ f i := by
    constructor
    · intro h
      rcases (hTH _).1 h with ⟨z', hz', h'⟩ | h' | ⟨i', hi', j', hj', hne', h'⟩ | h'
      · have := hElt z' hz'; rw [hninr i j hi hj] at h'; omega
      · rw [hninr i j hi hj] at h'; omega
      · rw [hninr i j hi hj] at h'
        have h'' : off i + j = off i' + j' := by omega
        have hoff'' : OFF φ i + j = OFF φ i' + j' := by simp only [hOFF] at h''; exact h''
        obtain ⟨rfl, rfl⟩ := OFF_inj φ hi hj hi' hj' hoff''
        exact hne'
      · rw [hninr i j hi hj] at h'; have := hofflt hi hj; omega
    · intro hne
      exact (hTH _).2 (Or.inr (Or.inr (Or.inl
        ⟨i, hi, j, hj, hne, by rw [hninr i j hi hj]⟩)))
  -- bridge: a satAdj edge lifts to H.Adj on the num images
  have hmk_adj {W₁ W₂ : Vertex} (hs : satAdj (cvcFormula φ) W₁ W₂)
      (h1 : num W₁ < N) (h2 : num W₂ < N) :
      H.Adj ⟨num W₁, h1⟩ ⟨num W₂, h2⟩ :=
    (hadj _ _).2 ⟨W₁, W₂, hs, rfl, rfl⟩
  -- the five emission blocks: u < v, the satAdj edge, and parity
  have hblkA {i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      num (Sum.inl (lit i j)) < num (Sum.inr (i, j)) ∧
      satAdj (cvcFormula φ) (Sum.inl (lit i j)) (Sum.inr (i, j)) ∧
      (TH (num (Sum.inl (lit i j))) ↔ (lit i j).2) := by
    rcases Nat.lt_or_ge j (φ.getD i []).length with hjt | hjt
    · have hz := hlit_var hi hjt
      refine ⟨hband_inl_inr hz _ hi hj, ?_, hTHinl_iff hz _⟩
      show ((cvcFormula φ).getD i [])[j]? = some (lit i j)
      have hj2 : j < ((φ.getD i []) ++ [(fresh φ, true)]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [cvc_getD_lt φ hi, List.getElem?_eq_getElem hj2]
      rw [List.getElem_append_left hjt, List.getElem_eq_getD, ← hlit_lt hi hjt]
    · have hj' : j = (φ.getD i []).length := by omega
      subst hj'
      rw [hlit_len hi]
      refine ⟨hband_fr_inr _ hi hj, ?_, hTHinl_fr_iff _⟩
      show ((cvcFormula φ).getD i [])[(φ.getD i []).length]? = some (fresh φ, true)
      rw [cvc_getD_lt φ hi, List.getElem?_eq_getElem (by simp)]
      simp
  have hblkB {i j l : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length)
      (hl : l ≤ (φ.getD i []).length) (hjl : j < l) :
      num (Sum.inr (i, j)) < num (Sum.inr (i, l)) ∧
      satAdj (cvcFormula φ) (Sum.inr (i, j)) (Sum.inr (i, l)) ∧
      (TH (num (Sum.inr (i, j))) ↔ j ≠ f i) := by
    refine ⟨?_, ?_, hTHinr_iff hi hj⟩
    · rw [hninr i j hi hj, hninr i l hi hl]; omega
    · refine ⟨rfl, by omega, ?_, ?_⟩
      · show j < ((cvcFormula φ).getD i []).length
        rw [cvc_getD_lt φ hi, List.length_append, List.length_cons, List.length_nil]
        omega
      · show l < ((cvcFormula φ).getD i []).length
        rw [cvc_getD_lt φ hi, List.length_append, List.length_cons, List.length_nil]
        omega
  have hblkC {i j : ℕ} (hi : i < φ.length) (hj : j < (φ.getD i []).length) :
      num (Sum.inl ((lit i j).1, false)) < num (Sum.inl ((lit i j).1, true)) ∧
      satAdj (cvcFormula φ) (Sum.inl ((lit i j).1, false)) (Sum.inl ((lit i j).1, true)) ∧
      ¬ TH (num (Sum.inl ((lit i j).1, false))) := by
    have hz := hlit_var hi hj
    refine ⟨?_, ?_, ?_⟩
    · rw [hninl _ hz, hninl _ hz]
      have h1 : ∀ b : Bool, (if b then 1 else 0 : ℕ) = b.toNat := fun b => by cases b <;> rfl
      rw [h1, h1]; simp
    · refine ⟨rfl, fun h => Bool.noConfusion h, ?_⟩
      rw [vars_cvc]; exact Finset.mem_insert_of_mem hz
    · rw [hninl _ hz]; exact hTHn2ez hz
  have hblkT1 :
      num (Sum.inl (fresh φ, false)) < num (Sum.inl (fresh φ, true)) ∧
      satAdj (cvcFormula φ) (Sum.inl (fresh φ, false)) (Sum.inl (fresh φ, true)) ∧
      ¬ TH (num (Sum.inl (fresh φ, false))) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hnfr, hnfr]
      have h1 : ∀ b : Bool, (if b then 1 else 0 : ℕ) = b.toNat := fun b => by cases b <;> rfl
      rw [h1, h1]; simp
    · refine ⟨rfl, fun h => Bool.noConfusion h, ?_⟩
      rw [vars_cvc]; exact Finset.mem_insert_self _ _
    · rw [hnfr]; exact hTHn2E
  have hblkT2 :
      num (Sum.inl (fresh φ, false)) < num (Sum.inr (φ.length, 0)) ∧
      satAdj (cvcFormula φ) (Sum.inl (fresh φ, false)) (Sum.inr (φ.length, 0)) ∧
      ¬ TH (num (Sum.inl (fresh φ, false))) := by
    refine ⟨hband_fr_tail _, ?_, ?_⟩
    · show ((cvcFormula φ).getD φ.length [])[(0 : ℕ)]? = some (fresh φ, false)
      rw [cvc_getD_len φ]; rfl
    · rw [hnfr]; exact hTHn2E
  -- decode: block elements carry their (u, v) pair uniquely
  have hdec {x u v u' v' : ℕ} {b b' : Bool} (hu : u < N) (hv : v < N) (hu' : u' < N)
      (hv' : v' < N)
      (hx : x ∈ inner u v b) (hx' : x ∈ inner u' v' b') : u = u' ∧ v = v' := by
    rw [inner_mem hinner] at hx hx'
    obtain ⟨t, ht, rfl, -⟩ := hx
    obtain ⟨t', ht', h', -⟩ := hx'
    obtain ⟨huu, hvv, -⟩ := block_inj (by omega) hu hv hu' hv' ht ht' h'
    exact ⟨huu, hvv⟩
  -- the per-site emission parts
  -- membership characterization of one site's emission list
  have hpart_mem {x i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      x ∈ inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l)))
            (decide (j ≠ f i))) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
            false else []) ++
        (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else [])
        ↔
      (x ∈ inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ∨
        (∃ l, j < l ∧ l ≤ (φ.getD i []).length ∧
          x ∈ inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ∨
        (j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 ∧
          x ∈ inner (num (Sum.inl ((lit i j).1, false)))
            (num (Sum.inl ((lit i j).1, true))) false) ∨
        (j ≠ f i ∧ x = num (Sum.inr (i, j))) ∨
        (j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 ∧
          x = num (Sum.inl ((lit i j).1, true)))) := by
    simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
      List.mem_ite_nil_right, List.mem_singleton, decide_eq_true_eq]
    constructor
    · intro hmem
      rcases hmem with (((h | h) | h) | h) | h
      · exact Or.inl h
      · obtain ⟨l, hmem2, hxl⟩ := h
        obtain ⟨hle, hlt⟩ := hmem2
        exact Or.inr (Or.inl ⟨l, hlt, by omega, hxl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨h.1.1, h.1.2, h.2⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1, h.2⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1.1, h.1.2, h.2⟩)))
    · intro hmem
      rcases hmem with h | h | h | h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
      · obtain ⟨l, hlt, hle, hxl⟩ := h
        exact Or.inl (Or.inl (Or.inl (Or.inr ⟨l, ⟨by omega, hlt⟩, hxl⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨⟨h.1, h.2.1⟩, h.2.2⟩))
      · exact Or.inl (Or.inr ⟨h.1, h.2⟩)
      · exact Or.inr ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  -- membership in an emitted part is always a block (≥ N) or a marker (< N)
  have hblock_ge {x u v : ℕ} {b : Bool} (hx : x ∈ inner u v b) : N ≤ x :=
    inner_ge hinner hx
  -- bounds for every emitted vertex
  have huA_ltN {i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      num (Sum.inl (lit i j)) < N := by
    rcases Nat.lt_or_ge j (φ.getD i []).length with hjt | hjt
    · exact hninl_ltN (hlit_var hi hjt) _
    · have hj' : j = (φ.getD i []).length := by omega
      subst hj'; rw [hlit_len hi]; exact hninl_fr_ltN _
  have hvA_ltN {i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      num (Sum.inr (i, j)) < N := hninr_ltN hi hj
  have huvC_ltN {i j : ℕ} (hi : i < φ.length) (hj : j < (φ.getD i []).length)
      (b : Bool) : num (Sum.inl ((lit i j).1, b)) < N := hninl_ltN (hlit_var hi hj) b
  have huT1_ltN : num (Sum.inl (fresh φ, false)) < N := hninl_fr_ltN _
  have hvT1_ltN : num (Sum.inl (fresh φ, true)) < N := hninl_fr_ltN _
  -- lit i j is always a literal vertex on the formula's variables or the fresh literal
  have hlit_or {i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      (lit i j).1 ∈ vars φ ∨ lit i j = (fresh φ, true) := by
    rcases Nat.lt_or_ge j (φ.getD i []).length with hjt | hjt
    · exact Or.inl (hlit_var hi hjt)
    · have hj' : j = (φ.getD i []).length := by omega
      subst hj'; exact Or.inr (hlit_len hi)
  have hninl_any_le {l : ℕ × Bool} (hl : l.1 ∈ vars φ ∨ l = (fresh φ, true)) :
      num (Sum.inl l) ≤ 2 * E + 1 := by
    rcases hl with hz | rfl
    · rcases l with ⟨z, b⟩; exact hninl_le hz b
    · exact hninl_fr_le true
  -- two sites never share an element (membership given in decomposed form)
  have hsite_disj {x i j i' j' : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length)
      (hi' : i' < φ.length) (hj' : j' ≤ (φ.getD i' []).length)
      (hne : i ≠ i' ∨ j ≠ j')
      (hx : x ∈ inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ∨
        (∃ l, j < l ∧ l ≤ (φ.getD i []).length ∧
          x ∈ inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ∨
        (j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 ∧
          x ∈ inner (num (Sum.inl ((lit i j).1, false)))
            (num (Sum.inl ((lit i j).1, true))) false) ∨
        (j ≠ f i ∧ x = num (Sum.inr (i, j))) ∨
        (j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 ∧
          x = num (Sum.inl ((lit i j).1, true))))
      (hx' : x ∈ inner (num (Sum.inl (lit i' j'))) (num (Sum.inr (i', j'))) (lit i' j').2 ∨
        (∃ l, j' < l ∧ l ≤ (φ.getD i' []).length ∧
          x ∈ inner (num (Sum.inr (i', j'))) (num (Sum.inr (i', l))) (decide (j' ≠ f i'))) ∨
        (j' < (φ.getD i' []).length ∧ off i' + j' = e (lit i' j').1 ∧
          x ∈ inner (num (Sum.inl ((lit i' j').1, false)))
            (num (Sum.inl ((lit i' j').1, true))) false) ∨
        (j' ≠ f i' ∧ x = num (Sum.inr (i', j'))) ∨
        (j' < (φ.getD i' []).length ∧ off i' + j' = e (lit i' j').1 ∧
          x = num (Sum.inl ((lit i' j').1, true)))) : False := by
    rcases hx with hA | hB | hC | hD | hE5 <;>
      rcases hx' with hA' | hB' | hC' | hD' | hE5'
    -- per-cell disjointness
    · obtain ⟨hu, hv⟩ := hdec (huA_ltN hi hj) (hvA_ltN hi hj) (huA_ltN hi' hj') (hvA_ltN hi' hj') hA hA'
      obtain ⟨rfl, rfl⟩ := hninr_inj hi hj hi' hj' hv
      exact hne.elim (fun h => h rfl) (fun h => h rfl)
    · obtain ⟨l, hjl, hle, hB⟩ := hB'
      obtain ⟨hu, hv⟩ := hdec (huA_ltN hi hj) (hvA_ltN hi hj) (hvA_ltN hi' hj') (hvA_ltN hi' hle) hA hB
      have h1 := hninl_any_le (hlit_or hi hj)
      have h2 := hninr_ge hi' hj'
      omega
    · obtain ⟨hjl', hoff', hCm⟩ := hC'
      obtain ⟨hu, hv⟩ := hdec (huA_ltN hi hj) (hvA_ltN hi hj) (huvC_ltN hi' hjl' _) (huvC_ltN hi' hjl' _) hA hCm
      have h1 := hninr_ge hi hj
      have h2 := hninl_le (hlit_var hi' hjl') true
      omega
    · have hge : N ≤ x := hblock_ge hA
      rw [hD'.2] at hge
      have := hninr_ltN hi' hj'
      omega
    · have hge : N ≤ x := hblock_ge hA
      rw [hE5'.2.2] at hge
      have := hninl_ltN (hlit_var hi' hE5'.1) true
      omega
    · obtain ⟨l, hjl, hle, hB⟩ := hB
      obtain ⟨hu, hv⟩ := hdec (hvA_ltN hi hj) (hvA_ltN hi hle) (huA_ltN hi' hj') (hvA_ltN hi' hj') hB hA'
      have h1 := hninr_ge hi hj
      have h2 := hninl_any_le (hlit_or hi' hj')
      omega
    · obtain ⟨l, hjl, hle, hB⟩ := hB
      obtain ⟨l', hjl', hle', hB'⟩ := hB'
      obtain ⟨hu, hv⟩ := hdec (hvA_ltN hi hj) (hvA_ltN hi hle) (hvA_ltN hi' hj') (hvA_ltN hi' hle') hB hB'
      obtain ⟨rfl, rfl⟩ := hninr_inj hi hj hi' hj' hu
      exact hne.elim (fun h => h rfl) (fun h => h rfl)
    · obtain ⟨l, hjl, hle, hB⟩ := hB
      obtain ⟨hjl', hoff', hCm⟩ := hC'
      obtain ⟨hu, hv⟩ := hdec (hvA_ltN hi hj) (hvA_ltN hi hle) (huvC_ltN hi' hjl' _) (huvC_ltN hi' hjl' _) hB hCm
      have h1 := hninr_ge hi hj
      have h2 := hninl_le (hlit_var hi' hjl') false
      omega
    · obtain ⟨l, hjl, hle, hB⟩ := hB
      have hge : N ≤ x := hblock_ge hB
      rw [hD'.2] at hge
      have := hninr_ltN hi' hj'
      omega
    · obtain ⟨l, hjl, hle, hB⟩ := hB
      have hge : N ≤ x := hblock_ge hB
      rw [hE5'.2.2] at hge
      have := hninl_ltN (hlit_var hi' hE5'.1) true
      omega
    · obtain ⟨hjl, hoff, hCm⟩ := hC
      obtain ⟨hu, hv⟩ := hdec (huvC_ltN hi hjl _) (huvC_ltN hi hjl _) (huA_ltN hi' hj') (hvA_ltN hi' hj') hCm hA'
      have h1 := hninl_le (hlit_var hi hjl) true
      have h2 := hninr_ge hi' hj'
      omega
    · obtain ⟨hjl, hoff, hCm⟩ := hC
      obtain ⟨l', hjl', hle', hB'⟩ := hB'
      obtain ⟨hu, hv⟩ := hdec (huvC_ltN hi hjl _) (huvC_ltN hi hjl _) (hvA_ltN hi' hj') (hvA_ltN hi' hle') hCm hB'
      have h1 := hninl_le (hlit_var hi hjl) false
      have h2 := hninr_ge hi' hj'
      omega
    · obtain ⟨hjl, hoff, hCm⟩ := hC
      obtain ⟨hjl', hoff', hCm'⟩ := hC'
      obtain ⟨hu, hv⟩ := hdec (huvC_ltN hi hjl _) (huvC_ltN hi hjl _) (huvC_ltN hi' hjl' _) (huvC_ltN hi' hjl' _) hCm hCm'
      obtain ⟨hz, -⟩ := hninl_inj (hlit_var hi hjl) (hlit_var hi' hjl') hv
      have hof : OFF φ i + j = OFF φ i' + j' := by
        simp only [hOFF] at hoff hoff'
        have heq : e (lit i j).1 = e (lit i' j').1 := congrArg e hz
        omega
      obtain ⟨rfl, rfl⟩ := OFF_inj φ hi (Nat.le_of_lt hjl) hi' (Nat.le_of_lt hjl') hof
      exact hne.elim (fun h => h rfl) (fun h => h rfl)
    · obtain ⟨hjl, hoff, hCm⟩ := hC
      have hge : N ≤ x := hblock_ge hCm
      rw [hD'.2] at hge
      have := hninr_ltN hi' hj'
      omega
    · obtain ⟨hjl, hoff, hCm⟩ := hC
      have hge : N ≤ x := hblock_ge hCm
      rw [hE5'.2.2] at hge
      have := hninl_ltN (hlit_var hi' hE5'.1) true
      omega
    · have hge : N ≤ x := hblock_ge hA'
      rw [hD.2] at hge
      have := hninr_ltN hi hj
      omega
    · obtain ⟨l', hjl', hle', hB'⟩ := hB'
      have hge : N ≤ x := hblock_ge hB'
      rw [hD.2] at hge
      have := hninr_ltN hi hj
      omega
    · obtain ⟨hjl', hoff', hCm'⟩ := hC'
      have hge : N ≤ x := hblock_ge hCm'
      rw [hD.2] at hge
      have := hninr_ltN hi hj
      omega
    · obtain ⟨rfl, rfl⟩ := hninr_inj hi hj hi' hj' (hD.2.symm.trans hD'.2)
      exact hne.elim (fun h => h rfl) (fun h => h rfl)
    · rw [hE5'.2.2] at hD
      have h1 := hninr_ge hi hj
      have h2 := hninl_le (hlit_var hi' hE5'.1) true
      omega
    · have hge : N ≤ x := hblock_ge hA'
      rw [hE5.2.2] at hge
      have := hninl_ltN (hlit_var hi hE5.1) true
      omega
    · obtain ⟨l', hjl', hle', hB'⟩ := hB'
      have hge : N ≤ x := hblock_ge hB'
      rw [hE5.2.2] at hge
      have := hninl_ltN (hlit_var hi hE5.1) true
      omega
    · obtain ⟨hjl', hoff', hCm'⟩ := hC'
      have hge : N ≤ x := hblock_ge hCm'
      rw [hE5.2.2] at hge
      have := hninl_ltN (hlit_var hi hE5.1) true
      omega
    · rw [hD'.2] at hE5
      have h1 := hninl_le (hlit_var hi hE5.1) true
      have h2 := hninr_ge hi' hj'
      omega
    · obtain ⟨hz, -⟩ := hninl_inj (hlit_var hi hE5.1) (hlit_var hi' hE5'.1)
        (hE5.2.2.symm.trans hE5'.2.2)
      have hof : OFF φ i + j = OFF φ i' + j' := by
        simp only [hOFF] at hE5 hE5'
        have heq : e (lit i j).1 = e (lit i' j').1 := congrArg e hz
        omega
      obtain ⟨rfl, rfl⟩ := OFF_inj φ hi (Nat.le_of_lt hE5.1) hi' (Nat.le_of_lt hE5'.1) hof
      exact hne.elim (fun h => h rfl) (fun h => h rfl)
  have hvT2_ltN : num (Sum.inr (φ.length, 0)) < N := hntail_ltN
  -- nodup of one site's list
  have hsite_nodup {i j : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length) :
      (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l)))
            (decide (j ≠ f i))) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
            false else []) ++
        (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else [])).Nodup := by
    have hndA := inner_nodup hinner (u := num (Sum.inl (lit i j)))
      (v := num (Sum.inr (i, j))) (b := (lit i j).2)
    have hndB : (((List.range ((φ.getD i []).length + 1)).filter
        (fun l => decide (j < l))).flatMap
        (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l)))
          (decide (j ≠ f i)))).Nodup := by
      apply List.nodup_flatMap.2
      refine ⟨fun l _ => inner_nodup hinner, ?_⟩
      apply List.Nodup.pairwise_of_forall_ne (List.Nodup.filter _ List.nodup_range)
      intro l₁ hl₁ l₂ hl₂ hne
      simp only [Function.onFun]
      rw [List.disjoint_left]
      intro x hx hx'
      obtain ⟨-, hv⟩ := hdec (hvA_ltN hi hj) (hvA_ltN hi (by
        have := (List.mem_filter.1 hl₁).1; rw [List.mem_range] at this; omega))
        (hvA_ltN hi hj) (hvA_ltN hi (by
        have := (List.mem_filter.1 hl₂).1; rw [List.mem_range] at this; omega)) hx hx'
      obtain ⟨-, rfl⟩ := hninr_inj hi (by
        have := (List.mem_filter.1 hl₁).1; rw [List.mem_range] at this; omega) hi (by
        have := (List.mem_filter.1 hl₂).1; rw [List.mem_range] at this; omega) hv
      exact hne rfl
    have hndC : (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
        inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
          false else []).Nodup := by
      by_cases hC : j < (φ.getD i []).length ∧ off i + j = e (lit i j).1
      · rw [if_pos hC]; exact inner_nodup hinner
      · rw [if_neg hC]; exact List.nodup_nil
    have hndD : (if j ≠ f i then [num (Sum.inr (i, j))] else []).Nodup := by
      by_cases hD : j ≠ f i
      · rw [if_pos hD]; exact List.nodup_singleton _
      · rw [if_neg hD]; exact List.nodup_nil
    have hndE5 : (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
        [num (Sum.inl ((lit i j).1, true))] else []).Nodup := by
      by_cases hC : j < (φ.getD i []).length ∧ off i + j = e (lit i j).1
      · rw [if_pos hC]; exact List.nodup_singleton _
      · rw [if_neg hC]; exact List.nodup_nil
    -- cross-part disjointness
    have hdjAB : (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2).Disjoint
        (((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l)))
            (decide (j ≠ f i)))) := by
      rw [List.disjoint_left]
      intro a ha hb
      obtain ⟨l, hlm, hx⟩ := List.mem_flatMap.1 hb
      rw [List.mem_filter, List.mem_range] at hlm
      obtain ⟨hu, hv⟩ := hdec (huA_ltN hi hj) (hvA_ltN hi hj) (hvA_ltN hi hj)
        (hvA_ltN hi (by omega)) ha hx
      have h1 := hninl_any_le (hlit_or hi hj)
      have h2 := hninr_ge hi hj
      omega
    have hdjAC : (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2).Disjoint
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
            false else []) := by
      rw [List.disjoint_left]
      intro a ha hc
      by_cases hC : j < (φ.getD i []).length ∧ off i + j = e (lit i j).1
      · rw [if_pos hC] at hc
        obtain ⟨hu, hv⟩ := hdec (huA_ltN hi hj) (hvA_ltN hi hj) (huvC_ltN hi hC.1 _)
          (huvC_ltN hi hC.1 _) ha hc
        have h1 := hninr_ge hi hj
        have h2 := hninl_le (hlit_var hi hC.1) true
        omega
      · rw [if_neg hC] at hc; exact List.not_mem_nil hc
    have hdjAD : (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2).Disjoint
        (if j ≠ f i then [num (Sum.inr (i, j))] else []) := by
      rw [List.disjoint_left]
      intro a ha hd
      by_cases hD : j ≠ f i
      · rw [if_pos hD] at hd
        have hge : N ≤ a := hblock_ge ha
        rw [List.mem_singleton.1 hd] at hge
        have := hninr_ltN hi hj
        omega
      · rw [if_neg hD] at hd; exact List.not_mem_nil hd
    have hdjAE5 : (inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2).Disjoint
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else []) := by
      rw [List.disjoint_left]
      intro a ha he
      by_cases hC : j < (φ.getD i []).length ∧ off i + j = e (lit i j).1
      · rw [if_pos hC] at he
        have hge : N ≤ a := hblock_ge ha
        rw [List.mem_singleton.1 he] at hge
        have := hninl_ltN (hlit_var hi hC.1) true
        omega
      · rw [if_neg hC] at he; exact List.not_mem_nil he
    have hdjBC : (((List.range ((φ.getD i []).length + 1)).filter
        (fun l => decide (j < l))).flatMap
        (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l)))
          (decide (j ≠ f i)))).Disjoint
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
            false else []) := by
      rw [List.disjoint_left]
      intro a hb hc
      obtain ⟨l, hlm, hx⟩ := List.mem_flatMap.1 hb
      rw [List.mem_filter, List.mem_range] at hlm
      by_cases hC : j < (φ.getD i []).length ∧ off i + j = e (lit i j).1
      · rw [if_pos hC] at hc
        obtain ⟨hu, hv⟩ := hdec (hvA_ltN hi hj) (hvA_ltN hi (by omega))
          (huvC_ltN hi hC.1 _) (huvC_ltN hi hC.1 _) hx hc
        have h1 := hninr_ge hi hj
        have h2 := hninl_le (hlit_var hi hC.1) false
        omega
      · rw [if_neg hC] at hc; exact List.not_mem_nil hc
    have hdjBD : (((List.range ((φ.getD i []).length + 1)).filter
        (fun l => decide (j < l))).flatMap
        (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l)))
          (decide (j ≠ f i)))).Disjoint
        (if j ≠ f i then [num (Sum.inr (i, j))] else []) := by
      rw [List.disjoint_left]
      intro a hb hd
      obtain ⟨l, hlm, hx⟩ := List.mem_flatMap.1 hb
      by_cases hD : j ≠ f i
      · rw [if_pos hD] at hd
        have hge : N ≤ a := hblock_ge hx
        rw [List.mem_singleton.1 hd] at hge
        have := hninr_ltN hi hj
        omega
      · rw [if_neg hD] at hd; exact List.not_mem_nil hd
    have hdjBE5 : (((List.range ((φ.getD i []).length + 1)).filter
        (fun l => decide (j < l))).flatMap
        (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l)))
          (decide (j ≠ f i)))).Disjoint
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else []) := by
      rw [List.disjoint_left]
      intro a hb he
      obtain ⟨l, hlm, hx⟩ := List.mem_flatMap.1 hb
      by_cases hC : j < (φ.getD i []).length ∧ off i + j = e (lit i j).1
      · rw [if_pos hC] at he
        have hge : N ≤ a := hblock_ge hx
        rw [List.mem_singleton.1 he] at hge
        have := hninl_ltN (hlit_var hi hC.1) true
        omega
      · rw [if_neg hC] at he; exact List.not_mem_nil he
    have hdjCD : (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
        inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
          false else []).Disjoint
        (if j ≠ f i then [num (Sum.inr (i, j))] else []) := by
      rw [List.disjoint_left]
      intro a hc hd
      by_cases hC : j < (φ.getD i []).length ∧ off i + j = e (lit i j).1
      · rw [if_pos hC] at hc
        by_cases hD : j ≠ f i
        · rw [if_pos hD] at hd
          have hge : N ≤ a := hblock_ge hc
          rw [List.mem_singleton.1 hd] at hge
          have := hninr_ltN hi hj
          omega
        · rw [if_neg hD] at hd; exact List.not_mem_nil hd
      · rw [if_neg hC] at hc; exact List.not_mem_nil hc
    have hdjCE5 : (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
        inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
          false else []).Disjoint
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else []) := by
      rw [List.disjoint_left]
      intro a hc he
      by_cases hC : j < (φ.getD i []).length ∧ off i + j = e (lit i j).1
      · rw [if_pos hC] at hc he
        have hge : N ≤ a := hblock_ge hc
        rw [List.mem_singleton.1 he] at hge
        have := hninl_ltN (hlit_var hi hC.1) true
        omega
      · rw [if_neg hC] at hc; exact List.not_mem_nil hc
    have hdjDE5 : (if j ≠ f i then [num (Sum.inr (i, j))] else []).Disjoint
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else []) := by
      rw [List.disjoint_left]
      intro a hd he
      by_cases hD : j ≠ f i
      · rw [if_pos hD] at hd
        by_cases hC : j < (φ.getD i []).length ∧ off i + j = e (lit i j).1
        · rw [if_pos hC] at he
          have h1 := hninr_ge hi hj
          have h2 := hninl_le (hlit_var hi hC.1) true
          have hd1 := List.mem_singleton.1 hd
          have he1 := List.mem_singleton.1 he
          omega
        · rw [if_neg hC] at he; exact List.not_mem_nil he
      · rw [if_neg hD] at hd; exact List.not_mem_nil hd
    have hdjCD' : ((if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
        inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
          false else []) ++
        (if j ≠ f i then [num (Sum.inr (i, j))] else [])).Disjoint
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else []) := by
      rw [List.disjoint_left]
      intro a hcd he
      rcases List.mem_append.1 hcd with hc | hd
      · exact hdjCE5 hc he
      · exact hdjDE5 hd he
    have hdjBC'' : (((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
            false else [])).Disjoint (if j ≠ f i then [num (Sum.inr (i, j))] else []) := by
      rw [List.disjoint_left]
      intro a hbc hd
      rcases List.mem_append.1 hbc with hb | hc
      · exact hdjBD hb hd
      · exact hdjCD hc hd
    have hdjBCD'' : (((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
            false else []) ++ (if j ≠ f i then [num (Sum.inr (i, j))] else [])).Disjoint (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else []) := by
      rw [List.disjoint_left]
      intro a hbcd he
      rcases List.mem_append.1 hbcd with hbc | hd
      · rcases List.mem_append.1 hbc with hb | hc
        · exact hdjBE5 hb he
        · exact hdjCE5 hc he
      · exact hdjDE5 hd he
    have hdjAB'' : ((inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2) ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i)))).Disjoint (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
            false else []) := by
      rw [List.disjoint_left]
      intro a hab hc
      rcases List.mem_append.1 hab with ha | hb
      · exact hdjAC ha hc
      · exact hdjBC hb hc
    have hdjABC'' : ((inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2) ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
            false else [])).Disjoint (if j ≠ f i then [num (Sum.inr (i, j))] else []) := by
      rw [List.disjoint_left]
      intro a habc hd
      rcases List.mem_append.1 habc with hab | hc
      · rcases List.mem_append.1 hab with ha | hb
        · exact hdjAD ha hd
        · exact hdjBD hb hd
      · exact hdjCD hc hd
    have hdjABCD'' : ((inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2) ++ ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l))) (decide (j ≠ f i))) ++ (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true)))
            false else []) ++ (if j ≠ f i then [num (Sum.inr (i, j))] else [])).Disjoint (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else []) := by
      rw [List.disjoint_left]
      intro a habcd he
      rcases List.mem_append.1 habcd with habc | hd
      · rcases List.mem_append.1 habc with hab | hc
        · rcases List.mem_append.1 hab with ha | hb
          · exact hdjAE5 ha he
          · exact hdjBE5 hb he
        · exact hdjCE5 hc he
      · exact hdjDE5 hd he
    exact List.Nodup.append
      (List.Nodup.append
        (List.Nodup.append
          (List.Nodup.append hndA hndB hdjAB) hndC hdjAB'') hndD hdjABC'') hndE5 hdjABCD''

  -- the marker values: decode which side of the marker
  have hmarker_ne {x i j i' j' : ℕ} (hi : i < φ.length) (hj : j ≤ (φ.getD i []).length)
      (hi' : i' < φ.length) (hj' : j' ≤ (φ.getD i' []).length)
      (h : num (Sum.inr (i, j)) = num (Sum.inr (i', j'))) : i = i' ∧ j = j' :=
    hninr_inj hi hj hi' hj' h
  -- variable-side inl marker pins the site through e
  have hmarker_inl {x i j : ℕ} (hi : i < φ.length)
      (hj : j < (φ.getD i []).length) (he : off i + j = e (lit i j).1)
      {i' j' : ℕ} (hi' : i' < φ.length) (hj' : j' < (φ.getD i' []).length)
      (he' : off i' + j' = e (lit i' j').1)
      (h : num (Sum.inl ((lit i j).1, true)) = num (Sum.inl ((lit i' j').1, true))) :
      i = i' ∧ j = j' := by
    have hzeq := hninl_inj (hlit_var hi hj) (hlit_var hi' hj') h
    have : e (lit i j).1 = e (lit i' j').1 := congrArg e hzeq.1
    have hof : OFF φ i + j = OFF φ i' + j' := by
      simp only [hOFF] at he he'; omega
    exact OFF_inj φ hi (Nat.le_of_lt hj) hi' (Nat.le_of_lt hj') hof
  -- inl values for variables stay below 2*E
  have hninl_var_lt {z : ℕ} (hz : z ∈ vars φ) (b : Bool) :
      num (Sum.inl (z, b)) < 2 * E := by
    rw [hninl z hz b]; have := hElt z hz
    have h1 : ∀ b : Bool, (if b = true then 1 else 0 : ℕ) ≤ 1 := by
      intro b; cases b <;> simp
    have := h1 b; omega
  have hnf0 : num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)) = 2 * E := by
    rw [hnfr]; simp
  have hnf1 : num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)) = 2 * E + 1 := by
    rw [hnfr]; simp
  -- T1 and T2 are disjoint
  have hdjT12 : (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false).Disjoint (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false) := by
    rw [List.disjoint_left]
    intro a ht1 ht2
    obtain ⟨hu, hv⟩ := hdec huT1_ltN hvT1_ltN huT1_ltN hvT2_ltN ht1 ht2
    rw [hnf1, hntail] at hv; omega
  -- body elements never appear in the tail
  have hdjBT : ((List.range φ.length).flatMap (fun i =>
      (List.range ((φ.getD i []).length + 1)).flatMap (fun j =>
        inner (num (Sum.inl (lit i j))) (num (Sum.inr (i, j))) (lit i j).2 ++
        ((List.range ((φ.getD i []).length + 1)).filter (fun l => decide (j < l))).flatMap
          (fun l => inner (num (Sum.inr (i, j))) (num (Sum.inr (i, l)))
            (decide (j ≠ f i))) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          inner (num (Sum.inl ((lit i j).1, false))) (num (Sum.inl ((lit i j).1, true))) false
          else []) ++
        (if j ≠ f i then [num (Sum.inr (i, j))] else []) ++
        (if j < (φ.getD i []).length ∧ off i + j = e (lit i j).1 then
          [num (Sum.inl ((lit i j).1, true))] else [])))).Disjoint (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++ inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))]) := by
    rw [List.disjoint_left]
    intro a ha ht
    obtain ⟨i, hi, ha⟩ := List.mem_flatMap.1 ha
    have hi' : i < φ.length := List.mem_range.1 hi
    obtain ⟨j, hj, ha⟩ := List.mem_flatMap.1 ha
    have hj' : j ≤ (φ.getD i []).length := by
      have := List.mem_range.1 hj; omega
    rcases List.mem_append.1 ht with hT | hm
    · rcases List.mem_append.1 hT with hT1 | hT2
      · -- a ∈ site vs a ∈ T1
        rcases (hpart_mem hi' hj').1 ha with hA | hB | hC | hD | hE5
        · obtain ⟨hu, hv⟩ := hdec (huA_ltN hi' hj') (hvA_ltN hi' hj')
            huT1_ltN hvT1_ltN hA hT1
          rcases hlit_or hi' hj' with hz | hlit
          · have hlt := hninl_var_lt hz (lit i j).2
            have hconv : num (Sum.inl (lit i j)) = num (Sum.inl ((lit i j).1, (lit i j).2)) := rfl
            rw [hconv] at hu; omega
          · rw [hlit, hnf1, hnf0] at hu; omega
        · obtain ⟨l, hlt, hle, hx⟩ := hB
          obtain ⟨hu, hv⟩ := hdec (hvA_ltN hi' hj') (hvA_ltN hi' (by omega))
            huT1_ltN hvT1_ltN hx hT1
          have hge := hninr_ge hi' hj'; rw [hnf0] at hu; omega
        · obtain ⟨hjl, hof, hx⟩ := hC
          obtain ⟨hu, hv⟩ := hdec (huvC_ltN hi' hjl _) (huvC_ltN hi' hjl _)
            huT1_ltN hvT1_ltN hx hT1
          have hlt := hninl_var_lt (hlit_var hi' hjl) false; rw [hnf0] at hu; omega
        · obtain ⟨hne2, rfl⟩ := hD
          have hge := hblock_ge hT1; have hlt := hninr_ltN hi' hj'; omega
        · obtain ⟨hjl, hof, rfl⟩ := hE5
          have hge := hblock_ge hT1
          have hlt := huvC_ltN hi' hjl true; omega
      · -- a ∈ site vs a ∈ T2
        rcases (hpart_mem hi' hj').1 ha with hA | hB | hC | hD | hE5
        · obtain ⟨hu, hv⟩ := hdec (huA_ltN hi' hj') (hvA_ltN hi' hj')
            huT1_ltN hvT2_ltN hA hT2
          rcases hlit_or hi' hj' with hz | hlit
          · have hlt := hninl_var_lt hz (lit i j).2
            have hconv : num (Sum.inl (lit i j)) = num (Sum.inl ((lit i j).1, (lit i j).2)) := rfl
            rw [hconv] at hu; omega
          · rw [hlit, hnf1, hnf0] at hu; omega
        · obtain ⟨l, hlt, hle, hx⟩ := hB
          obtain ⟨hu, hv⟩ := hdec (hvA_ltN hi' hj') (hvA_ltN hi' (by omega))
            huT1_ltN hvT2_ltN hx hT2
          have hge := hninr_ge hi' hj'; rw [hnf0] at hu; omega
        · obtain ⟨hjl, hof, hx⟩ := hC
          obtain ⟨hu, hv⟩ := hdec (huvC_ltN hi' hjl _) (huvC_ltN hi' hjl _)
            huT1_ltN hvT2_ltN hx hT2
          have hlt := hninl_var_lt (hlit_var hi' hjl) false; rw [hnf0] at hu; omega
        · obtain ⟨hne2, rfl⟩ := hD
          have hge := hblock_ge hT2; have hlt := hninr_ltN hi' hj'; omega
        · obtain ⟨hjl, hof, rfl⟩ := hE5
          have hge := hblock_ge hT2
          have hlt := huvC_ltN hi' hjl true; omega
    · -- a ∈ site vs a ∈ markers
      rcases List.mem_pair.1 hm with hm | hm
      · -- marker 2E+1
        rw [hnf1] at hm
        rcases (hpart_mem hi' hj').1 ha with hA | hB | hC | hD | hE5
        · have hge := hblock_ge hA; omega
        · obtain ⟨l, hlt, hle, hx⟩ := hB; have hge := hblock_ge hx; omega
        · obtain ⟨hjl, hof, hx⟩ := hC; have hge := hblock_ge hx; omega
        · obtain ⟨hne2, rfl⟩ := hD
          have hge := hninr_ge hi' hj'; omega
        · obtain ⟨hjl, hof, rfl⟩ := hE5
          have hlt := hninl_var_lt (hlit_var hi' hjl) true; omega
      · -- marker 3E+2
        rw [hntail] at hm
        rcases (hpart_mem hi' hj').1 ha with hA | hB | hC | hD | hE5
        · have hge := hblock_ge hA; omega
        · obtain ⟨l, hlt, hle, hx⟩ := hB; have hge := hblock_ge hx; omega
        · obtain ⟨hjl, hof, hx⟩ := hC; have hge := hblock_ge hx; omega
        · obtain ⟨hne2, rfl⟩ := hD
          have hle := hninr_le hi' hj'; omega
        · obtain ⟨hjl, hof, rfl⟩ := hE5
          have hlt := hninl_var_lt (hlit_var hi' hjl) true; omega
  -- tail is nodup and disjoint pieces assemble
  have hndm : [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)),
      num (Sum.inr (φ.length, 0))].Nodup := by
    rw [hnf1, hntail]
    apply List.Nodup.cons
    · simp; omega
    · exact List.nodup_singleton _
  have hdjTm : (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++ inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false).Disjoint [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))] := by
    rw [List.disjoint_left]
    intro a hT hm
    rcases List.mem_append.1 hT with hT | hT
    · have hge := hblock_ge hT
      rcases List.mem_pair.1 hm with rfl | rfl
      · rw [hnf1] at hge; rw [hN] at hge; omega
      · rw [hntail] at hge; rw [hN] at hge; omega
    · have hge := hblock_ge hT
      rcases List.mem_pair.1 hm with rfl | rfl
      · rw [hnf1] at hge; rw [hN] at hge; omega
      · rw [hntail] at hge; rw [hN] at hge; omega
  have hndtail : (inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true))) false ++ inner (num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false))) (num (Sum.inr (φ.length, 0))) false ++ [num (Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)), num (Sum.inr (φ.length, 0))]).Nodup :=
    List.Nodup.append
      (List.Nodup.append (inner_nodup hinner) (inner_nodup hinner) hdjT12)
      hndm hdjTm
  -- TL nodup
  have hTLn : TL.Nodup := by
    rw [hTL]
    apply List.Nodup.append _ hndtail hdjBT
    apply List.nodup_flatMap.2
    constructor
    · intro i hi
      have hi' : i < φ.length := List.mem_range.1 hi
      apply List.nodup_flatMap.2
      refine ⟨fun j hj => hsite_nodup hi' (by
        have := List.mem_range.1 hj; omega), ?_⟩
      apply List.Nodup.pairwise_of_forall_ne List.nodup_range
      intro j hj j' hj' hne
      simp only [Function.onFun]
      rw [List.disjoint_left]
      intro a ha ha'
      have hj2 : j ≤ (φ.getD i []).length := by
        have := List.mem_range.1 hj; omega
      have hj2' : j' ≤ (φ.getD i []).length := by
        have := List.mem_range.1 hj'; omega
      exact hsite_disj hi' hj2 hi' hj2' (Or.inr hne)
        ((hpart_mem hi' hj2).1 ha) ((hpart_mem hi' hj2').1 ha')
    · apply List.Nodup.pairwise_of_forall_ne List.nodup_range
      intro i hi i' hi' hne
      simp only [Function.onFun]
      rw [List.disjoint_left]
      intro a ha ha'
      obtain ⟨j, hj, ha2⟩ := List.mem_flatMap.1 ha
      obtain ⟨j', hj', ha3⟩ := List.mem_flatMap.1 ha'
      have hi2 : i < φ.length := List.mem_range.1 hi
      have hi2' : i' < φ.length := List.mem_range.1 hi'
      have hj2 : j ≤ (φ.getD i []).length := by
        have := List.mem_range.1 hj; omega
      have hj2' : j' ≤ (φ.getD i' []).length := by
        have := List.mem_range.1 hj'; omega
      exact hsite_disj hi2 hj2 hi2' hj2' (Or.inl hne)
        ((hpart_mem hi2 hj2).1 ha2) ((hpart_mem hi2' hj2').1 ha3)

  -- membership implies TH x or block form
  have hiff_fwd : ∀ x : ℕ, x ∈ TL →
      (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧
        ∃ t < 2 * k, x = N + 2 * k * (u.val * N + v.val) + t ∧
          (t % 2 = 1 ↔ TH u.val)) := by
    intro x hx
    rw [hTL] at hx
    rcases List.mem_append.1 hx with hb | ht
    · obtain ⟨i, hi, hb⟩ := List.mem_flatMap.1 hb
      obtain ⟨j, hj, hb⟩ := List.mem_flatMap.1 hb
      have hi' : i < φ.length := List.mem_range.1 hi
      have hj' : j ≤ (φ.getD i []).length := by
        have := List.mem_range.1 hj; omega
      rcases (hpart_mem hi' hj').1 hb with hA | hB | hC | hD | hE5
      · right
        rw [inner_mem hinner] at hA
        obtain ⟨t, ht, hx, hb⟩ := hA
        obtain ⟨huv, hsat, hth⟩ := hblkA hi' hj'
        exact ⟨⟨_, huA_ltN hi' hj'⟩, ⟨_, hvA_ltN hi' hj'⟩, huv,
          hmk_adj hsat _ _, t, ht, hx, hb.trans hth.symm⟩
      · obtain ⟨l, hlt, hle, hxl⟩ := hB
        rw [inner_mem hinner] at hxl
        obtain ⟨t, ht, hx, hb⟩ := hxl
        obtain ⟨huv, hsat, hth⟩ := hblkB hi' hj' hle hlt
        right
        refine ⟨⟨_, hvA_ltN hi' hj'⟩, ⟨_, hvA_ltN hi' hle⟩, huv,
          hmk_adj hsat _ _, t, ht, hx, ?_⟩
        have hth' : TH (num (Sum.inr (i, j))) ↔ decide (j ≠ f i) :=
          hth.trans decide_eq_true_iff.symm
        exact hb.trans hth'.symm
      · obtain ⟨hjl, hof, hx⟩ := hC
        rw [inner_mem hinner] at hx
        obtain ⟨t, ht, hx', hb⟩ := hx
        obtain ⟨huv, hsat, hnth⟩ := hblkC hi' hjl
        right
        exact ⟨⟨_, huvC_ltN hi' hjl false⟩, ⟨_, huvC_ltN hi' hjl true⟩, huv,
          hmk_adj hsat _ _, t, ht, hx',
          ⟨fun h => Bool.noConfusion (hb.1 h), fun h => (hnth h).elim⟩⟩
      · obtain ⟨hne, rfl⟩ := hD
        left; exact (hTHinr_iff hi' hj').2 hne
      · obtain ⟨hjl, hof, rfl⟩ := hE5
        left; exact (hTHinl_iff (hlit_var hi' hjl) true).2 rfl
    · rcases List.mem_append.1 ht with hT | hm
      · rcases List.mem_append.1 hT with hT1 | hT2
        · rw [inner_mem hinner] at hT1
          obtain ⟨t, ht, hx, hb⟩ := hT1
          obtain ⟨huv, hsat, hnth⟩ := hblkT1
          right
          exact ⟨⟨_, huT1_ltN⟩, ⟨_, hvT1_ltN⟩, huv, hmk_adj hsat _ _, t, ht, hx,
            ⟨fun h => Bool.noConfusion (hb.1 h), fun h => (hnth h).elim⟩⟩
        · rw [inner_mem hinner] at hT2
          obtain ⟨t, ht, hx, hb⟩ := hT2
          obtain ⟨huv, hsat, hnth⟩ := hblkT2
          right
          exact ⟨⟨_, huT1_ltN⟩, ⟨_, hvT2_ltN⟩, huv, hmk_adj hsat _ _, t, ht, hx,
            ⟨fun h => Bool.noConfusion (hb.1 h), fun h => (hnth h).elim⟩⟩
      · rcases List.mem_pair.1 hm with rfl | rfl
        · left; exact (hTHinl_fr_iff true).2 rfl
        · left; rw [hntail]; exact hTH3E2

  -- backward: TH x or block form implies membership
  have hiff_bwd : ∀ x : ℕ,
      (TH x ∨ ∃ u v : Fin N, u < v ∧ H.Adj u v ∧
        ∃ t < 2 * k, x = N + 2 * k * (u.val * N + v.val) + t ∧
          (t % 2 = 1 ↔ TH u.val)) → x ∈ TL := by
    intro x h
    rw [hTL]
    rcases h with hTh | hblk
    · rcases (hTH _).1 hTh with ⟨z, hz, h'⟩ | h' | ⟨i, hi, j, hj, hne, h'⟩ | h'
      · -- x = 2*e z + 1: E5 part at the site covering z
        obtain ⟨i, j, hi, hj, hoff, hlfst⟩ := hSite hz
        apply List.mem_append_left
        apply List.mem_flatMap.2; refine ⟨i, List.mem_range.2 hi, ?_⟩
        apply List.mem_flatMap.2; refine ⟨j, List.mem_range.2 (by omega), ?_⟩
        apply (hpart_mem hi (Nat.le_of_lt hj)).2
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        refine ⟨hj, hoff.trans (congrArg e hlfst).symm, ?_⟩
        have hnl1 := hninl _ (hlfst ▸ hz) true
        have h2 : 2 * e z + 1 = 2 * e (lit i j).1 + 1 := by rw [hlfst]
        have hnl2 : 2 * e (lit i j).1 + 1 = num (Sum.inl ((lit i j).1, true)) := by
          rw [hnl1]; simp
        exact h'.trans (h2.trans hnl2)
      · -- x = 2*E+1: first tail marker
        rw [h', ← hnf1]
        apply List.mem_append_right
        exact List.mem_append_right _ (List.mem_pair.2 (Or.inl rfl))
      · -- x = num inr(i,j): D marker
        rw [h', ← hninr i j hi hj]
        apply List.mem_append_left
        apply List.mem_flatMap.2; refine ⟨i, List.mem_range.2 hi, ?_⟩
        apply List.mem_flatMap.2; refine ⟨j, List.mem_range.2 (by omega), ?_⟩
        apply (hpart_mem hi hj).2
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
        exact ⟨hne, rfl⟩
      · -- x = 3*E+2: second tail marker
        rw [h', ← hntail]
        apply List.mem_append_right
        exact List.mem_append_right _ (List.mem_pair.2 (Or.inr rfl))
    · obtain ⟨u, v, huv, hA, t, ht, hx, hpar⟩ := hblk
      obtain ⟨U, V, hsat, hu, hv⟩ := (hadj u v).1 hA
      have hsat2 : satAdj (cvcFormula φ) U V := hsat
      have hlen : (cvcFormula φ).length = φ.length + 1 := by simp [cvcFormula]
      rcases U with ⟨z, b⟩ | ⟨i, j⟩
      · rcases V with ⟨z', b'⟩ | ⟨i', j'⟩
        · -- inl-inl: same variable edge
          obtain ⟨rfl, hne, hz⟩ := hsat2
          rw [vars_cvc] at hz
          have hle : num (Sum.inl (z, b)) < num (Sum.inl (z, b')) := by
            rw [hu, hv]; exact huv
          have hbb : b = false ∧ b' = true := by
            rcases Finset.mem_insert.1 hz with hfl | hzv
            · subst hfl
              rw [hnfr, hnfr] at hle
              cases b <;> cases b' <;>
                first | exact absurd rfl hne | exact ⟨rfl, rfl⟩ |
                  (exfalso; simp at hle)
            · rw [hninl _ hzv, hninl _ hzv] at hle
              cases b <;> cases b' <;>
                first | exact absurd rfl hne | exact ⟨rfl, rfl⟩ |
                  (exfalso; simp at hle)
          obtain ⟨rfl, rfl⟩ := hbb
          rcases Finset.mem_insert.1 hz with rfl | hzv
          · -- fresh variable: T1 block
            apply List.mem_append_right
            apply List.mem_append_left
            apply List.mem_append_left
            apply (inner_mem hinner).2
            refine ⟨t, ht, ?_, ?_⟩
            · rw [hx]; congr 2; rw [← hu, ← hv]
            · have hpar' := hpar
              rw [← hu, hnf0] at hpar'
              exact ⟨fun h => (hTHn2E (hpar'.1 h)).elim,
                fun h => Bool.noConfusion h⟩
          · -- ordinary variable z: C block at its site
            obtain ⟨i, j, hi, hj, hoff, hlfst⟩ := hSite hzv
            apply List.mem_append_left
            apply List.mem_flatMap.2; refine ⟨i, List.mem_range.2 hi, ?_⟩
            apply List.mem_flatMap.2; refine ⟨j, List.mem_range.2 (by omega), ?_⟩
            apply (hpart_mem hi (Nat.le_of_lt hj)).2
            apply Or.inr; apply Or.inr; apply Or.inl
            refine ⟨hj, hoff.trans (congrArg e hlfst).symm, ?_⟩
            apply (inner_mem hinner).2
            refine ⟨t, ht, ?_, ?_⟩
            · rw [hx]; congr 2; rw [← hu, ← hv, hlfst]
            · have hpar' := hpar
              rw [← hu] at hpar'
              exact ⟨fun h => Bool.noConfusion
                  ((hTHinl_iff hzv false).1 (hpar'.1 h)),
                fun h => Bool.noConfusion h⟩
        · -- inl-inr: A block
          have hs : ((cvcFormula φ).getD i' [])[j']? = some (z, b) := hsat2
          rcases lt_trichotomy i' φ.length with hilt | rfl | higt
          · rw [cvc_getD_lt φ hilt] at hs
            rcases Nat.lt_or_ge j' (φ.getD i' []).length with hjl | hjl
            · rw [List.getElem?_append_left hjl] at hs
              have hgs := (List.getElem?_eq_some_iff.1 hs)
              have hali : lit i' j' = (z, b) := by
                rw [hlit_lt hilt hjl, List.getD_eq_getElem _ _ hjl]
                exact hgs.2
              have hjb : j' ≤ (φ.getD i' []).length := Nat.le_of_lt hjl
              apply List.mem_append_left
              apply List.mem_flatMap.2; refine ⟨i', List.mem_range.2 hilt, ?_⟩
              apply List.mem_flatMap.2; refine ⟨j', List.mem_range.2 (by omega), ?_⟩
              apply (hpart_mem hilt hjb).2; apply Or.inl
              apply (inner_mem hinner).2
              refine ⟨t, ht, ?_, ?_⟩
              · rw [hx]; congr 2; rw [← hu, ← hali, ← hv]
              · have hpar' := hpar
                rw [← hu, ← hali] at hpar'
                exact hpar'.trans (hblkA hilt hjb).2.2
            · have hj' : j' = (φ.getD i' []).length := by
                have hcl := (List.getElem?_eq_some_iff.1 hs).1
                rw [List.length_append, List.length_cons, List.length_nil] at hcl
                omega
              rw [List.getElem?_append_right (by omega : (φ.getD i' []).length ≤ j'), hj'] at hs
              have hz : List.length (List.getD φ i' []) - List.length (List.getD φ i' []) = 0 :=
                Nat.sub_self _
              rw [hz] at hs
              have hs2 : [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)][0]? =
                  some (z, b) := hs
              simp at hs2
              obtain ⟨rfl, rfl⟩ := hs2.symm
              have hali : lit i' j' =
                  (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true) :=
                hj'.symm ▸ hlit_len hilt
              have hjb : j' ≤ (φ.getD i' []).length := by omega
              apply List.mem_append_left
              apply List.mem_flatMap.2; refine ⟨i', List.mem_range.2 hilt, ?_⟩
              apply List.mem_flatMap.2; refine ⟨j', List.mem_range.2 (by omega), ?_⟩
              apply (hpart_mem hilt hjb).2; apply Or.inl
              apply (inner_mem hinner).2
              refine ⟨t, ht, ?_, ?_⟩
              · rw [hx]; congr 2; rw [← hu, ← hali, ← hv]
              · have hpar' := hpar
                rw [← hu, ← hali] at hpar'
                exact hpar'.trans (hblkA hilt hjb).2.2
          · -- i = len: unit clause, j = 0, literal (fresh, false): T2 block
            rw [cvc_getD_len φ] at hs
            have hgs := (List.getElem?_eq_some_iff.1 hs)
            obtain ⟨hj1, heq⟩ := hgs
            have hj0 : j' = 0 := by
              have : [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)].length = 1 := rfl
              rw [this] at hj1; omega
            subst hj0
            have hfa : (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false) = (z, b) := heq
            cases hfa
            apply List.mem_append_right
            apply List.mem_append_left
            apply List.mem_append_right
            apply (inner_mem hinner).2
            refine ⟨t, ht, ?_, ?_⟩
            · rw [hx]; congr 2; rw [← hu, ← hv]
            · have hpar' := hpar
              rw [← hu, hnf0] at hpar'
              exact ⟨fun h => (hTHn2E (hpar'.1 h)).elim,
                fun h => Bool.noConfusion h⟩
          · -- i > len: empty clause
            rw [List.getD_eq_default _ _ (by omega)] at hs
            simp at hs
      · rcases V with ⟨z', b'⟩ | ⟨i', j'⟩
        · -- inr-inl: impossible, inr values exceed inl values
          have hs : ((cvcFormula φ).getD i [])[j]? = some (z', b') := hsat2
          have hle : num (Sum.inr (i, j)) < num (Sum.inl (z', b')) := by
            rw [hu, hv]; exact huv
          rcases lt_trichotomy i φ.length with hilt | rfl | higt
          · rw [cvc_getD_lt φ hilt] at hs
            have hjl : j ≤ (φ.getD i []).length := by
              have hcl := (List.getElem?_eq_some_iff.1 hs).1
              rw [List.length_append, List.length_cons, List.length_nil] at hcl
              omega
            rcases Nat.lt_or_ge j (φ.getD i []).length with hjt | hjt
            · rw [List.getElem?_append_left hjt] at hs
              have hgs := (List.getElem?_eq_some_iff.1 hs)
              have hz2 : (z', b') ∈ (φ.getD i []) := hgs.2 ▸ List.getElem_mem hgs.1
              have hzv : z' ∈ vars φ := mem_vars.2
                ⟨φ.getD i [],
                  (List.getD_eq_getElem _ _ hilt).symm ▸ List.getElem_mem hilt,
                  (z', b'), hz2, rfl⟩
              have h1 := hninr_ge hilt hjl
              have h2 := hninl_le hzv b'
              omega
            · have hj' : j = (φ.getD i []).length := by omega
              rw [List.getElem?_append_right (by omega : (φ.getD i []).length ≤ j), hj'] at hs
              have hz : List.length (List.getD φ i []) - List.length (List.getD φ i []) = 0 :=
                Nat.sub_self _
              rw [hz] at hs
              have hs2 : [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)][0]? =
                  some (z', b') := hs
              simp at hs2
              obtain ⟨rfl, rfl⟩ := hs2.symm
              have h1 := hninr_ge hilt (by omega)
              have h2 := hnf1
              omega
          · -- i = len
            rw [cvc_getD_len φ] at hs
            have hgs := (List.getElem?_eq_some_iff.1 hs)
            obtain ⟨hj1, heq⟩ := hgs
            have hj0 : j = 0 := by
              have : [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)].length = 1 := rfl
              rw [this] at hj1; omega
            subst hj0
            have hfa : (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false) = (z', b') := heq
            cases hfa
            rw [hntail, hnf0] at hle
            omega
          · rw [List.getD_eq_default _ _ (by omega)] at hs
            simp at hs
        · -- inr-inr: B block
          obtain ⟨rfl, hne2, hj, hj'⟩ := hsat2
          have hjc : j < ((cvcFormula φ).getD i []).length := hj
          have hjc' : j' < ((cvcFormula φ).getD i []).length := hj'
          rcases lt_trichotomy i φ.length with hilt | rfl | higt
          · rw [cvc_getD_lt φ hilt] at hjc hjc'
            rw [List.length_append, List.length_cons, List.length_nil] at hjc hjc'
            have hjl : j ≤ (φ.getD i []).length := by omega
            have hjl' : j' ≤ (φ.getD i []).length := by omega
            have hlt : j < j' := by
              have hle : num (Sum.inr (i, j)) < num (Sum.inr (i, j')) := by
                rw [hu, hv]; exact huv
              rw [hninr i j hilt hjl, hninr i j' hilt hjl'] at hle
              omega
            apply List.mem_append_left
            apply List.mem_flatMap.2; refine ⟨i, List.mem_range.2 hilt, ?_⟩
            apply List.mem_flatMap.2; refine ⟨j, List.mem_range.2 (by omega), ?_⟩
            apply (hpart_mem hilt hjl).2
            apply Or.inr; apply Or.inl
            refine ⟨j', hlt, hjl', ?_⟩
            apply (inner_mem hinner).2
            refine ⟨t, ht, ?_, ?_⟩
            · rw [hx]; congr 2; rw [← hu, ← hv]
            · have hpar' := hpar
              rw [← hu] at hpar'
              exact hpar'.trans ((hTHinr_iff hilt hjl).trans decide_eq_true_iff.symm)
          · -- i = len: clause has one literal, j ≠ j' impossible
            rw [cvc_getD_len φ] at hjc hjc'
            simp at hjc hjc'
            omega
          · rw [List.getD_eq_default _ _ (by omega)] at hjc
            simp at hjc
  exact ⟨hTLn, fun x => ⟨hiff_fwd x, hiff_bwd x⟩⟩
