import Mathlib
import PEqualNP.Defs

/-!
# The 2k-subdivision has (2k + 1) times as many edges

Each edge `u < v` of `H` becomes a path with `2 * k + 1` edges, through `2 * k` new vertices
whose numbers encode `u`, `v` and the place on the path. The edges of `S` are the image of
(oriented edges of `H`) times (places `0 .. 2k`) under the map sending `(u, v, j)` to the
`j`-th edge of the path, and that map is injective: a new vertex determines `u`, `v` and its
place, and every edge of a path has a new vertex since `1 ≤ k`.
-/

namespace PEqualNP.Outside.L_meta_449_aux

/-- The number of the vertex at place `p` of the path that replaces the edge `u v`. -/
def pos (m k u v p : ℕ) : ℕ :=
  if p = 0 then u else if p = 2 * k + 1 then v else m + 2 * k * (u * m + v) + p - 1

lemma pos_lt (m k u v p : ℕ) (hu : u < m) (hv : v < m) (hp : p ≤ 2 * k + 1) :
    pos m k u v p < m + 2 * k * (m * m) := by
  have h1 : (u + 1) * m ≤ m * m := Nat.mul_le_mul_right m hu
  have h2 : (u + 1) * m = u * m + m := by ring
  have h3 : 2 * k * (u * m + v + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ (by omega)
  have h4 : 2 * k * (u * m + v + 1) = 2 * k * (u * m + v) + 2 * k := by ring
  have h5 : 0 ≤ 2 * k * (m * m) := Nat.zero_le _
  unfold pos
  generalize 2 * k * (u * m + v) = X at *
  generalize 2 * k * (m * m) = Y at *
  split_ifs <;> omega

lemma pos_facts (m k u v p : ℕ) :
    (p = 0 → pos m k u v p = u) ∧ (p = 2 * k + 1 → pos m k u v p = v) ∧
      (1 ≤ p → p ≤ 2 * k → m ≤ pos m k u v p) := by
  unfold pos
  refine ⟨fun h => by simp [h], fun h => by simp [h], fun h1 h2 => ?_⟩
  rw [if_neg (by omega), if_neg (by omega)]
  generalize 2 * k * (u * m + v) = X
  omega

lemma decode (a c c' r r' : ℕ) (hr : r < a) (hr' : r' < a) (h : a * c + r = a * c' + r') :
    c = c' ∧ r = r' := by
  have ha : 0 < a := by omega
  have h1 : (a * c + r) / a = c := by rw [Nat.mul_add_div ha, Nat.div_eq_of_lt hr, add_zero]
  have h2 : (a * c' + r') / a = c' := by rw [Nat.mul_add_div ha, Nat.div_eq_of_lt hr', add_zero]
  have hc : c = c' := by rw [← h1, ← h2, h]
  subst hc
  exact ⟨rfl, by omega⟩

lemma pos_inj (m k u v u' v' p p' : ℕ) (hv : v < m) (hv' : v' < m)
    (hp : 1 ≤ p ∧ p ≤ 2 * k) (hp' : 1 ≤ p' ∧ p' ≤ 2 * k)
    (h : pos m k u v p = pos m k u' v' p') : u = u' ∧ v = v' ∧ p = p' := by
  unfold pos at h
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
  have h' : 2 * k * (u * m + v) + (p - 1) = 2 * k * (u' * m + v') + (p' - 1) := by
    generalize 2 * k * (u * m + v) = X at *
    generalize 2 * k * (u' * m + v') = Y at *
    omega
  obtain ⟨hc, hpp⟩ := decode (2 * k) _ _ _ _ (by omega) (by omega) h'
  have hc' : m * u + v = m * u' + v' := by rw [Nat.mul_comm m u, Nat.mul_comm m u']; exact hc
  obtain ⟨huu, hvv⟩ := decode m _ _ _ _ hv hv' hc'
  exact ⟨huu, hvv, by omega⟩

/-- Two edges of two paths that coincide are the same edge of the same path. -/
lemma core (m k u v u' v' j j' : ℕ) (hk : 1 ≤ k) (hu : u < m) (hv : v < m) (hu' : u' < m)
    (hv' : v' < m) (hj : j ≤ 2 * k) (hj' : j' ≤ 2 * k)
    (h : (pos m k u v j = pos m k u' v' j' ∧ pos m k u v (j + 1) = pos m k u' v' (j' + 1)) ∨
      (pos m k u v j = pos m k u' v' (j' + 1) ∧ pos m k u v (j + 1) = pos m k u' v' j')) :
    u = u' ∧ v = v' ∧ j = j' := by
  have f1 := pos_facts m k u v j
  have f2 := pos_facts m k u v (j + 1)
  have f3 := pos_facts m k u' v' j'
  have f4 := pos_facts m k u' v' (j' + 1)
  have k1 := pos_inj m k u v u' v' j j' hv hv'
  have k2 := pos_inj m k u v u' v' (j + 1) (j' + 1) hv hv'
  have k3 := pos_inj m k u v u' v' j (j' + 1) hv hv'
  have k4 := pos_inj m k u v u' v' (j + 1) j' hv hv'
  generalize pos m k u v j = a at *
  generalize pos m k u v (j + 1) = b at *
  generalize pos m k u' v' j' = a' at *
  generalize pos m k u' v' (j' + 1) = b' at *
  omega

/-- The vertex at place `p` of the path that replaces the edge `u v`. -/
def node (m k : ℕ) (u v : Fin m) (p : ℕ) : Fin (m + 2 * k * (m * m)) :=
  ⟨pos m k u.val v.val (min p (2 * k + 1)),
    pos_lt m k u.val v.val _ u.isLt v.isLt (Nat.min_le_right _ _)⟩

lemma node_val (m k : ℕ) (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) :
    (node m k u v p).val = pos m k u.val v.val p := by
  simp [node, Nat.min_eq_left hp]

end PEqualNP.Outside.L_meta_449_aux

open PEqualNP.Outside.L_meta_449_aux in
theorem PEqualNP.Outside.L_meta_449 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → S.edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard := by
  intro m k H Q S hk hQ hS
  have hQ' : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), p ≤ 2 * k + 1 →
      (Q u v p x ↔ x.val = pos m k u.val v.val p) := by
    intro u v p x hp
    rw [hQ]
    unfold pos
    generalize 2 * k * (u.val * m + v.val) = X
    split_ifs <;> omega
  let D : Set (Fin m × Fin m) := {q | q.1 < q.2 ∧ H.Adj q.1 q.2}
  let g : (Fin m × Fin m) × Fin (2 * k + 1) → Sym2 (Fin (m + 2 * k * (m * m))) :=
    fun q => s(node m k q.1.1 q.1.2 q.2.val, node m k q.1.1 q.1.2 (q.2.val + 1))
  have hH : H.edgeSet = (fun q : Fin m × Fin m => s(q.1, q.2)) '' D := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      constructor
      · intro h
        rcases lt_or_gt_of_ne (H.ne_of_adj h) with hlt | hlt
        · exact ⟨(x, y), ⟨hlt, h⟩, rfl⟩
        · exact ⟨(y, x), ⟨hlt, h.symm⟩, Sym2.eq_swap⟩
      · rintro ⟨⟨u, v⟩, ⟨-, hadj⟩, h⟩
        have h' : s(u, v) = s(x, y) := h
        rw [← SimpleGraph.mem_edgeSet, ← h']
        exact hadj
  have hHinj : Set.InjOn (fun q : Fin m × Fin m => s(q.1, q.2)) D := by
    rintro ⟨u, v⟩ ⟨huv, -⟩ ⟨u', v'⟩ ⟨huv', -⟩ h
    change u < v at huv
    change u' < v' at huv'
    have h' : s(u, v) = s(u', v') := h
    rw [Sym2.eq_iff] at h'
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd huv (lt_asymm huv')
  have hSe : S.edgeSet = g '' (D ×ˢ Set.univ) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      rw [SimpleGraph.mem_edgeSet, hS]
      constructor
      · rintro ⟨u, v, huv, hadj, p, hp, h⟩
        refine ⟨((u, v), ⟨p, by omega⟩), ⟨⟨huv, hadj⟩, Set.mem_univ _⟩, ?_⟩
        show s(node m k u v p, node m k u v (p + 1)) = s(x, y)
        rw [hQ' u v p x (by omega), hQ' u v (p + 1) y (by omega), hQ' u v p y (by omega),
          hQ' u v (p + 1) x (by omega)] at h
        rw [Sym2.eq_iff]
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Fin.ext ((node_val m k u v p (by omega)).trans h1.symm),
            Fin.ext ((node_val m k u v (p + 1) (by omega)).trans h2.symm)⟩
        · exact Or.inr ⟨Fin.ext ((node_val m k u v p (by omega)).trans h1.symm),
            Fin.ext ((node_val m k u v (p + 1) (by omega)).trans h2.symm)⟩
      · rintro ⟨⟨⟨u, v⟩, j⟩, ⟨⟨huv, hadj⟩, -⟩, h⟩
        have hj := j.isLt
        have h' : s(node m k u v j.val, node m k u v (j.val + 1)) = s(x, y) := h
        refine ⟨u, v, huv, hadj, j.val, by omega, ?_⟩
        rw [hQ' u v j.val x (by omega), hQ' u v (j.val + 1) y (by omega),
          hQ' u v j.val y (by omega), hQ' u v (j.val + 1) x (by omega)]
        rw [Sym2.eq_iff] at h'
        rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by rw [← h1]; exact node_val m k u v j.val (by omega),
            by rw [← h2]; exact node_val m k u v (j.val + 1) (by omega)⟩
        · exact Or.inr ⟨by rw [← h1]; exact node_val m k u v j.val (by omega),
            by rw [← h2]; exact node_val m k u v (j.val + 1) (by omega)⟩
  have hginj : Set.InjOn g (D ×ˢ Set.univ) := by
    rintro ⟨⟨u, v⟩, j⟩ - ⟨⟨u', v'⟩, j'⟩ - h
    have hj := j.isLt
    have hj' := j'.isLt
    have h' : s(node m k u v j.val, node m k u v (j.val + 1)) =
        s(node m k u' v' j'.val, node m k u' v' (j'.val + 1)) := h
    rw [Sym2.eq_iff] at h'
    have hc : (pos m k u.val v.val j.val = pos m k u'.val v'.val j'.val ∧
          pos m k u.val v.val (j.val + 1) = pos m k u'.val v'.val (j'.val + 1)) ∨
        (pos m k u.val v.val j.val = pos m k u'.val v'.val (j'.val + 1) ∧
          pos m k u.val v.val (j.val + 1) = pos m k u'.val v'.val j'.val) := by
      rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have a := congrArg Fin.val h1
        have b := congrArg Fin.val h2
        rw [node_val _ _ _ _ _ (by omega), node_val _ _ _ _ _ (by omega)] at a b
        exact Or.inl ⟨a, b⟩
      · have a := congrArg Fin.val h1
        have b := congrArg Fin.val h2
        rw [node_val _ _ _ _ _ (by omega), node_val _ _ _ _ _ (by omega)] at a b
        exact Or.inr ⟨a, b⟩
    obtain ⟨e1, e2, e3⟩ := core m k u.val v.val u'.val v'.val j.val j'.val hk u.isLt v.isLt
      u'.isLt v'.isLt (by omega) (by omega) hc
    exact Prod.ext (Prod.ext (Fin.ext e1) (Fin.ext e2)) (Fin.ext e3)
  rw [hSe, hginj.ncard_image, Set.ncard_prod, hH, hHinj.ncard_image, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin, Nat.mul_comm]
