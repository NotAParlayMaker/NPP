import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_469

open Classical

lemma pair_idx_lt (m : ℕ) (u v : Fin m) : u.val * m + v.val < m * m := by
  have hu : u.val < m := u.isLt
  have hv : v.val < m := v.isLt
  calc
    u.val * m + v.val < u.val * m + m := by omega
    _ = (u.val + 1) * m := by ring
    _ ≤ m * m := by gcongr <;> omega

lemma encode_lt (m k : ℕ) (u v : Fin m) (i : ℕ) (hi : i < 2 * k) :
    m + 2 * k * (u.val * m + v.val) + i < m + 2 * k * (m * m) := by
  have hp : u.val * m + v.val < m * m := pair_idx_lt m u v
  calc
    m + 2 * k * (u.val * m + v.val) + i
      < m + 2 * k * (u.val * m + v.val) + 2 * k := by omega
    _ = m + 2 * k * (u.val * m + v.val + 1) := by ring
    _ ≤ m + 2 * k * (m * m) := by gcongr <;> omega

lemma mul_add_lt_mul_add {B q1 r1 q2 r2 : ℕ} (hr1 : r1 < B) (hq : q1 < q2) :
    B * q1 + r1 < B * q2 + r2 := by
  calc
    B * q1 + r1 < B * q1 + B := by omega
    _ = B * (q1 + 1) := by ring
    _ ≤ B * q2 := by gcongr <;> omega
    _ ≤ B * q2 + r2 := by omega

lemma nat_base_inj {B q1 r1 q2 r2 : ℕ} (hr1 : r1 < B) (hr2 : r2 < B)
    (h : B * q1 + r1 = B * q2 + r2) : q1 = q2 ∧ r1 = r2 := by
  rcases lt_trichotomy q1 q2 with hlt | rfl | hgt
  · have hlt' : B * q1 + r1 < B * q2 + r2 := mul_add_lt_mul_add hr1 hlt
    omega
  · exact ⟨rfl, by omega⟩
  · have hgt' : B * q2 + r2 < B * q1 + r1 := mul_add_lt_mul_add hr2 hgt
    omega

lemma encode_inj (m k : ℕ) (u1 v1 u2 v2 : Fin m) (i1 i2 : ℕ)
    (hi1 : i1 < 2 * k) (hi2 : i2 < 2 * k)
    (h : m + 2 * k * (u1.val * m + v1.val) + i1 = m + 2 * k * (u2.val * m + v2.val) + i2) :
    u1 = u2 ∧ v1 = v2 ∧ i1 = i2 := by
  have h1 : 2 * k * (u1.val * m + v1.val) + i1 = 2 * k * (u2.val * m + v2.val) + i2 := by
    omega
  obtain ⟨huv, hi⟩ := nat_base_inj hi1 hi2 h1
  rw [mul_comm u1.val m, mul_comm u2.val m] at huv
  obtain ⟨hu, hv⟩ := nat_base_inj v1.isLt v2.isLt huv
  exact ⟨Fin.ext hu, Fin.ext hv, hi⟩

lemma edgePairs_card (m : ℕ) (H : SimpleGraph (Fin m)) :
    (Finset.univ.filter (fun p : Fin m × Fin m => p.1 < p.2 ∧ H.Adj p.1 p.2)).card =
      H.edgeSet.ncard := by
  let S : Finset (Fin m × Fin m) :=
    Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)
  let E : Finset (Sym2 (Fin m)) := S.image (fun p => s(p.1, p.2))
  have hinj : Set.InjOn (fun p : Fin m × Fin m => s(p.1, p.2)) (S : Set (Fin m × Fin m)) := by
    intro p1 hp1 p2 hp2 heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, S] at hp1 hp2
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have ha : p1.1 < p1.2 := hp1.1
      have hb : p2.1 < p2.2 := hp2.1
      rw [h1, h2] at ha
      exact lt_irrefl p2.1 (lt_trans hb ha)
  have hcard : S.card = E.card := (Finset.card_image_of_injOn hinj).symm
  have hE : (E : Set (Sym2 (Fin m))) = H.edgeSet := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [Finset.mem_coe, H.mem_edgeSet]
      simp only [E, S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨a, b⟩, ⟨-, hadj⟩, heq⟩
        dsimp only at hadj heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj
        · rw [H.adj_comm]
          exact hadj
      · intro hadj
        rcases lt_or_gt_of_ne (H.ne_of_adj hadj) with huv | hvu
        · exact ⟨⟨u, v⟩, ⟨huv, hadj⟩, rfl⟩
        · exact ⟨⟨v, u⟩, ⟨hvu, by rw [H.adj_comm]; exact hadj⟩, by rw [Sym2.eq_swap]⟩
  change S.card = H.edgeSet.ncard
  rw [hcard, ← hE, Set.ncard_coe_finset]

lemma main_aux (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m))
    (T' : Finset (Fin (m + 2 * k * (m * m))))
    (hT' : ∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔
      (∃ u ∈ T, x.val = u.val) ∨
      ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧
        x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) :
    T'.card = T.card + k * H.edgeSet.ncard := by
  let g : Fin m → Fin (m + 2 * k * (m * m)) := fun u =>
    ⟨u.val, by have := u.isLt; omega⟩
  let V_part : Finset (Fin (m + 2 * k * (m * m))) := T.image g
  let S : Finset (Fin m × Fin m) :=
    Finset.univ.filter (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)
  let P : Finset ((Fin m × Fin m) × Fin k) := S ×ˢ Finset.univ
  let f : (Fin m × Fin m) × Fin k → Fin (m + 2 * k * (m * m)) := fun q =>
    ⟨m + 2 * k * (q.1.1.val * m + q.1.2.val) + (2 * q.2.val + if q.1.1 ∈ T then 1 else 0),
      encode_lt m k q.1.1 q.1.2 (2 * q.2.val + if q.1.1 ∈ T then 1 else 0)
        (by have := q.2.isLt; split_ifs <;> omega)⟩
  let E_part : Finset (Fin (m + 2 * k * (m * m))) := P.image f
  have hg_inj : Function.Injective g := by
    intro u1 u2 h
    have hval := congrArg Fin.val h
    dsimp [g] at hval
    exact Fin.ext hval
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨u1, v1⟩, j1⟩ ⟨⟨u2, v2⟩, j2⟩ h
    have hval := congrArg Fin.val h
    dsimp [f] at hval
    have hi1 : 2 * j1.val + (if u1 ∈ T then 1 else 0) < 2 * k := by
      have := j1.isLt
      split_ifs <;> omega
    have hi2 : 2 * j2.val + (if u2 ∈ T then 1 else 0) < 2 * k := by
      have := j2.isLt
      split_ifs <;> omega
    have hinj := encode_inj m k u1 v1 u2 v2 _ _ hi1 hi2 hval
    rcases hinj with ⟨rfl, rfl, hi⟩
    have hj : j1 = j2 := by
      apply Fin.ext
      omega
    rw [hj]
  have hdisj : Disjoint V_part E_part := by
    rw [Finset.disjoint_left]
    intro x hxV hxE
    rw [Finset.mem_image] at hxV hxE
    rcases hxV with ⟨u, -, rfl⟩
    rcases hxE with ⟨q, -, hq⟩
    have hval := congrArg Fin.val hq
    dsimp [g, f] at hval
    have hu := u.isLt
    omega
  have hT'_eq : T' = V_part ∪ E_part := by
    ext x
    rw [hT', Finset.mem_union]
    have hV : (∃ u ∈ T, x.val = u.val) ↔ x ∈ V_part := by
      rw [Finset.mem_image]
      constructor
      · rintro ⟨u, hu, hx⟩
        exact ⟨u, hu, Fin.ext hx.symm⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, rfl⟩
    have hE : (∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧
        x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) ↔ x ∈ E_part := by
      rw [Finset.mem_image]
      constructor
      · rintro ⟨u, v, i, hi, huv, hadj, hx, hmod⟩
        refine ⟨((u, v), ⟨i / 2, by omega⟩), ?_, ?_⟩
        · simp only [P, S, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
            true_and, and_true]
          exact ⟨huv, hadj⟩
        · apply Fin.ext
          dsimp [f]
          rw [hx]
          have hdiv := Nat.div_add_mod i 2
          have hmlt := Nat.mod_lt i (by omega : 0 < 2)
          by_cases hu : u ∈ T
          · rw [if_pos hu]
            have : i % 2 = 1 := hmod.mpr hu
            omega
          · rw [if_neg hu]
            have : i % 2 ≠ 1 := fun h => hu (hmod.mp h)
            omega
      · rintro ⟨⟨⟨u, v⟩, j⟩, hq, rfl⟩
        simp only [P, S, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
          true_and, and_true] at hq
        refine ⟨u, v, 2 * j.val + (if u ∈ T then 1 else 0), ?_, hq.1, hq.2, rfl, ?_⟩
        · have := j.isLt
          split_ifs <;> omega
        · by_cases hu : u ∈ T
          · rw [if_pos hu]
            exact ⟨fun _ => hu, fun _ => by omega⟩
          · rw [if_neg hu]
            exact ⟨fun h => by omega, fun h => absurd h hu⟩
    rw [hV, hE]
  have hV_card : V_part.card = T.card := Finset.card_image_of_injective T hg_inj
  have hE_card : E_part.card = k * H.edgeSet.ncard := by
    change (P.image f).card = k * H.edgeSet.ncard
    rw [Finset.card_image_of_injective P hf_inj]
    simp only [P, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have hS : S.card = H.edgeSet.ncard := edgePairs_card m H
    rw [hS, Nat.mul_comm]
  rw [hT'_eq, Finset.card_union_of_disjoint hdisj, hV_card, hE_card]

end PEqualNP.Outside.L_meta_469

theorem PEqualNP.Outside.L_meta_469 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → T'.card = T.card + k * H.edgeSet.ncard := by
  exact PEqualNP.Outside.L_meta_469.main_aux
