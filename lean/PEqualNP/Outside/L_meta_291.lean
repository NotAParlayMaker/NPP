import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace PEqualNP.Outside

theorem L_meta_291 : ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)), 1 ≤ k → (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ t ∈ T, ∃ w : Fin m, H.Adj t w ∧ w ∉ T) → ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)), S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) => ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k), x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ ((i.val = 0 ∧ y.val = u.val) ∨ (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨ (i.val + 1 = 2 * k ∧ y.val = v.val))) → ∀ F : Finset (Fin (m + 2 * k * m * m)), (∀ j : Fin (m + 2 * k * m * m), j ∈ F ↔ (∃ u ∈ T, j.val = u.val) ∨ ∃ u v : Fin m, ∃ i : Fin (2 * k), u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧ (i.val % 2 = 1 ↔ u ∈ T)) → ∀ x ∈ F, ∃ y : Fin (m + 2 * k * m * m), S.Adj x y ∧ y ∉ F := by
  intro k m H T hk _hcover hmin S hS F hF x hx
  have separate (a b c p q : ℕ) (ha : 0 < a) (hp : p < a) (hq : q < a)
      (he : a * b + p = a * c + q) : b = c ∧ p = q := by
    have hm := congrArg (fun n : ℕ => n % a) he
    change (a * b + p) % a = (a * c + q) % a at hm
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at hm
    exact ⟨Nat.eq_of_mul_eq_mul_left ha (by omega), hm⟩
  have slot_bound (u v : Fin m) (i : Fin (2 * k)) :
      m + 2 * k * (u.val * m + v.val) + i.val < m + 2 * k * m * m := by
    have hu := u.isLt
    have hv := v.isLt
    have hi := i.isLt
    have hbase : u.val * m + v.val + 1 ≤ m * m := by
      calc
        u.val * m + v.val + 1 ≤ u.val * m + m := by omega
        _ = (u.val + 1) * m := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ m * m := Nat.mul_le_mul_right m (by omega)
    have hmul := Nat.mul_le_mul_left (2 * k) hbase
    rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc] at hmul
    omega
  let slot (u v : Fin m) (i : Fin (2*k)) : Fin (m + 2*k*m*m) :=
    ⟨m + 2*k*(u.val*m+v.val) + i.val, slot_bound u v i⟩
  let orig (u : Fin m) : Fin (m + 2*k*m*m) :=
    ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right m (2*k*m*m))⟩
  have slot_ne_orig (u v : Fin m) (i : Fin (2*k)) (w : Fin m) :
      slot u v i ≠ orig w := by
    intro he
    have he' := congrArg Fin.val he
    change m + 2*k*(u.val*m+v.val) + i.val = w.val at he'
    have hw := w.isLt
    omega
  have slot_inj (u v u' v' : Fin m) (i i' : Fin (2*k))
      (he : slot u v i = slot u' v' i') : u = u' ∧ v = v' ∧ i = i' := by
    have hh := congrArg Fin.val he
    change m + 2*k*(u.val*m+v.val) + i.val = m + 2*k*(u'.val*m+v'.val) + i'.val at hh
    obtain ⟨hcode, hi⟩ := separate (2*k) (u.val*m+v.val) (u'.val*m+v'.val)
      i.val i'.val (by omega) i.isLt i'.isLt (by omega)
    have hm : 0 < m := Nat.zero_lt_of_lt u.isLt
    obtain ⟨hu,hv⟩ := separate m u.val u'.val v.val v'.val hm v.isLt v'.isLt (by
      simpa only [Nat.mul_comm m] using hcode)
    exact ⟨Fin.ext hu, Fin.ext hv, Fin.ext hi⟩
  have orig_out (w : Fin m) (hw : w ∉ T) : orig w ∉ F := by
    intro hwF
    rcases (hF _).mp hwF with ⟨w', hw', he⟩ | ⟨u, v, i, _, _, he, _⟩
    · have hww' : w = w' := Fin.ext he
      exact hw (hww' ▸ hw')
    · exact slot_ne_orig u v i w ((Fin.ext he).symm)
  have slot_out (u v : Fin m) (i : Fin (2*k)) (hi : ¬ (i.val % 2 = 1 ↔ u ∈ T)) :
      slot u v i ∉ F := by
    intro hiF
    rcases (hF _).mp hiF with ⟨w, _, he⟩ | ⟨u', v', i', _, _, he, hp⟩
    · exact slot_ne_orig u v i w (Fin.ext he)
    · obtain ⟨rfl, rfl, rfl⟩ := slot_inj u v u' v' i i' (Fin.ext he)
      exact hi hp
  rw [hS]
  rcases (hF x).mp hx with ⟨t, ht, hxt⟩ | ⟨u, v, i, huv, hadj, hxi, hpar⟩
  · obtain ⟨w, htw, hw⟩ := hmin t ht
    have hxt' : x = orig t := Fin.ext hxt
    subst x
    have hne : t ≠ w := H.ne_of_adj htw
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · let i : Fin (2*k) := ⟨0, by omega⟩
      refine ⟨slot t w i, ?_, slot_out t w i ?_⟩
      · apply (SimpleGraph.fromRel_adj _ _ _).2
        exact ⟨(slot_ne_orig t w i t).symm, Or.inr ⟨t, w, hlt, htw, i, rfl,
          Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact fun hi => (by simpa [i] using hi.mpr ht : False)
    · let i : Fin (2*k) := ⟨2*k-1, by omega⟩
      refine ⟨slot w t i, ?_, slot_out w t i ?_⟩
      · apply (SimpleGraph.fromRel_adj _ _ _).2
        refine ⟨(slot_ne_orig w t i t).symm, Or.inr ⟨w, t, hlt, htw.symm, i, rfl,
          Or.inr (Or.inr ⟨?_, rfl⟩)⟩⟩
        dsimp [i]
        omega
      · intro hi
        apply hw (hi.mp ?_)
        dsimp [i]
        omega
  · have hxi' : x = slot u v i := Fin.ext hxi
    subst x
    have hi := i.isLt
    by_cases hut : u ∈ T
    · have hiOdd := hpar.mpr hut
      let j : Fin (2*k) := ⟨i.val-1, by omega⟩
      have hj : j.val + 1 = i.val := by dsimp [j]; omega
      refine ⟨slot u v j, ?_, slot_out u v j ?_⟩
      · apply (SimpleGraph.fromRel_adj _ _ _).2
        refine ⟨?_, Or.inr ⟨u, v, huv, hadj, j, rfl, Or.inr (Or.inl ⟨?_, ?_⟩)⟩⟩
        · intro he
          have hijeq := congrArg Fin.val (slot_inj u v u v i j he).2.2
          omega
        · omega
        · change m + 2*k*(u.val*m+v.val) + i.val = m + 2*k*(u.val*m+v.val) + j.val + 1
          omega
      · intro h
        have hjOdd := h.mpr hut
        omega
    · have hiEven : i.val % 2 ≠ 1 := fun h => hut (hpar.mp h)
      let j : Fin (2*k) := ⟨i.val+1, by omega⟩
      have hj : j.val = i.val + 1 := rfl
      refine ⟨slot u v j, ?_, slot_out u v j ?_⟩
      · apply (SimpleGraph.fromRel_adj _ _ _).2
        refine ⟨?_, Or.inl ⟨u, v, huv, hadj, i, rfl, Or.inr (Or.inl ⟨?_, rfl⟩)⟩⟩
        · intro he
          have hijeq := congrArg Fin.val (slot_inj u v u v i j he).2.2
          omega
        · omega
      · intro h
        apply hut (h.mp ?_)
        omega

end PEqualNP.Outside
