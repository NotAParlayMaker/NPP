import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic

namespace PEqualNP.Outside.L_meta_291_aux

private lemma eq_of_mul_add_eq {d q1 q2 r1 r2 : ℕ}
    (hr1 : r1 < d) (hr2 : r2 < d) (h : d * q1 + r1 = d * q2 + r2) :
    q1 = q2 ∧ r1 = r2 := by
  have hq : q1 = q2 := by
    rcases Nat.lt_trichotomy q1 q2 with hlt | heq | hgt
    · have : d * q1 + d ≤ d * q2 := by
        calc d * q1 + d = d * (q1 + 1) := by rw [Nat.mul_succ]
          _ ≤ d * q2 := Nat.mul_le_mul_left d hlt
      omega
    · exact heq
    · have : d * q2 + d ≤ d * q1 := by
        calc d * q2 + d = d * (q2 + 1) := by rw [Nat.mul_succ]
          _ ≤ d * q1 := Nat.mul_le_mul_left d hgt
      omega
  subst hq
  exact ⟨rfl, by omega⟩

private lemma slot_unique {m k : ℕ} {u v u' v' : Fin m} {i i' : Fin (2 * k)}
    (h : m + 2 * k * (u.val * m + v.val) + i.val = m + 2 * k * (u'.val * m + v'.val) + i'.val) :
    u = u' ∧ v = v' ∧ i = i' := by
  have h1 : 2 * k * (u.val * m + v.val) + i.val = 2 * k * (u'.val * m + v'.val) + i'.val := by
    omega
  rcases eq_of_mul_add_eq i.isLt i'.isLt h1 with ⟨hslot, hi⟩
  have hslot' : m * u.val + v.val = m * u'.val + v'.val := by
    rw [Nat.mul_comm m u.val, Nat.mul_comm m u'.val]
    exact hslot
  rcases eq_of_mul_add_eq v.isLt v'.isLt hslot' with ⟨hu, hv⟩
  exact ⟨Fin.ext hu, Fin.ext hv, Fin.ext hi⟩

private lemma slot_lt {m k : ℕ} (u v : Fin m) (i : Fin (2 * k)) :
    m + 2 * k * (u.val * m + v.val) + i.val < m + 2 * k * m * m := by
  have h1 : u.val * m + v.val + 1 ≤ m * m := by
    have hu : u.val + 1 ≤ m := u.isLt
    have hv : v.val + 1 ≤ m := v.isLt
    calc u.val * m + v.val + 1
        ≤ u.val * m + m := by omega
      _ = (u.val + 1) * m := by rw [Nat.succ_mul]
      _ ≤ m * m := Nat.mul_le_mul_right m hu
  have h2 : 2 * k * (u.val * m + v.val) + i.val < 2 * k * (m * m) := by
    calc 2 * k * (u.val * m + v.val) + i.val
        < 2 * k * (u.val * m + v.val) + 2 * k := Nat.add_lt_add_left i.isLt _
      _ = 2 * k * (u.val * m + v.val + 1) := by rw [Nat.mul_succ]
      _ ≤ 2 * k * (m * m) := Nat.mul_le_mul_left (2 * k) h1
  have h3 : 2 * k * (m * m) = 2 * k * m * m := (Nat.mul_assoc (2 * k) m m).symm
  omega

end PEqualNP.Outside.L_meta_291_aux

theorem PEqualNP.Outside.L_meta_291 :
    ∀ (k m : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)), 1 ≤ k →
      (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) →
      (∀ t ∈ T, ∃ w : Fin m, H.Adj t w ∧ w ∉ T) →
      ∀ S : SimpleGraph (Fin (m + 2 * k * m * m)),
        S = SimpleGraph.fromRel (fun x y : Fin (m + 2 * k * m * m) =>
          ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ i : Fin (2 * k),
            x.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
            ((i.val = 0 ∧ y.val = u.val) ∨
             (i.val + 1 < 2 * k ∧ y.val = m + 2 * k * (u.val * m + v.val) + i.val + 1) ∨
             (i.val + 1 = 2 * k ∧ y.val = v.val))) →
        ∀ F : Finset (Fin (m + 2 * k * m * m)),
          (∀ j : Fin (m + 2 * k * m * m), j ∈ F ↔
            (∃ u ∈ T, j.val = u.val) ∨
            ∃ u v : Fin m, ∃ i : Fin (2 * k),
              u < v ∧ H.Adj u v ∧ j.val = m + 2 * k * (u.val * m + v.val) + i.val ∧
              (i.val % 2 = 1 ↔ u ∈ T)) →
          ∀ x ∈ F, ∃ y : Fin (m + 2 * k * m * m), S.Adj x y ∧ y ∉ F := by
  intro k m H T hk _ hmin S hS F hF x hx
  subst hS
  have hnotF_slot : ∀ (u v : Fin m) (i : Fin (2 * k))
      (y : Fin (m + 2 * k * m * m)),
      y.val = m + 2 * k * (u.val * m + v.val) + i.val →
      ¬ (i.val % 2 = 1 ↔ u ∈ T) → y ∉ F := by
    intro u v i y hy hbad hyF
    rcases (hF y).mp hyF with ⟨u0, _, hy0⟩ | ⟨u', v', i', _, _, hy', hiff⟩
    · have := u0.isLt; omega
    · rcases PEqualNP.Outside.L_meta_291_aux.slot_unique (hy.symm.trans hy') with ⟨rfl, rfl, rfl⟩
      exact hbad hiff
  rcases (hF x).mp hx with ⟨u, huT, hxu⟩ | ⟨u, v, i, huv, hadj, hxi, hiff⟩
  · rcases hmin u huT with ⟨w, huw, hwT⟩
    have hne : u ≠ w := H.ne_of_adj huw
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · let i0 : Fin (2 * k) := ⟨0, by omega⟩
      let y : Fin (m + 2 * k * m * m) :=
        ⟨m + 2 * k * (u.val * m + w.val) + i0.val,
          PEqualNP.Outside.L_meta_291_aux.slot_lt u w i0⟩
      refine ⟨y, ?_, hnotF_slot u w i0 y rfl (by simp [i0, huT])⟩
      refine ⟨?_, Or.inr ⟨u, w, hlt, huw, i0, rfl, Or.inl ⟨rfl, hxu⟩⟩⟩
      intro heq
      have h1 : x.val = y.val := congrArg Fin.val heq
      have h2 := u.isLt
      simp only [y, hxu] at h1
      omega
    · let ilast : Fin (2 * k) := ⟨2 * k - 1, by omega⟩
      let y : Fin (m + 2 * k * m * m) :=
        ⟨m + 2 * k * (w.val * m + u.val) + ilast.val,
          PEqualNP.Outside.L_meta_291_aux.slot_lt w u ilast⟩
      have hmod : ilast.val % 2 = 1 := by simp only [ilast]; omega
      refine ⟨y, ?_, hnotF_slot w u ilast y rfl (by simp [hmod, hwT])⟩
      refine ⟨?_, Or.inr ⟨w, u, hgt, H.symm.symm _ _ huw, ilast, rfl,
        Or.inr (Or.inr ⟨by simp only [ilast]; omega, hxu⟩)⟩⟩
      intro heq
      have h1 : x.val = y.val := congrArg Fin.val heq
      have h2 := u.isLt
      simp only [y, hxu] at h1
      omega
  · by_cases hlt : i.val + 1 < 2 * k
    · let inext : Fin (2 * k) := ⟨i.val + 1, hlt⟩
      let y : Fin (m + 2 * k * m * m) :=
        ⟨m + 2 * k * (u.val * m + v.val) + inext.val,
          PEqualNP.Outside.L_meta_291_aux.slot_lt u v inext⟩
      have hbad : ¬ (inext.val % 2 = 1 ↔ u ∈ T) := by
        intro h2
        have h3 : i.val % 2 = 1 ↔ inext.val % 2 = 1 := hiff.trans h2.symm
        simp only [inext] at h3
        omega
      refine ⟨y, ?_, hnotF_slot u v inext y rfl hbad⟩
      refine ⟨?_, Or.inl ⟨u, v, huv, hadj, i, hxi, Or.inr (Or.inl ⟨hlt, by simp [y, inext]; omega⟩)⟩⟩
      intro heq
      have h1 : x.val = y.val := congrArg Fin.val heq
      simp only [y, inext, hxi] at h1
      omega
    · have hilast : i.val + 1 = 2 * k := by have := i.isLt; omega
      let iprev : Fin (2 * k) := ⟨2 * k - 2, by omega⟩
      let y : Fin (m + 2 * k * m * m) :=
        ⟨m + 2 * k * (u.val * m + v.val) + iprev.val,
          PEqualNP.Outside.L_meta_291_aux.slot_lt u v iprev⟩
      have huT : u ∈ T := hiff.mp (by omega)
      have hmod : iprev.val % 2 = 0 := by simp only [iprev]; omega
      have hbad : ¬ (iprev.val % 2 = 1 ↔ u ∈ T) := by simp [hmod, huT]
      refine ⟨y, ?_, hnotF_slot u v iprev y rfl hbad⟩
      refine ⟨?_, Or.inr ⟨u, v, huv, hadj, iprev, rfl,
        Or.inr (Or.inl ⟨by simp only [iprev]; omega, by simp only [iprev, hxi]; omega⟩)⟩⟩
      intro heq
      have h1 : x.val = y.val := congrArg Fin.val heq
      simp only [y, iprev, hxi] at h1
      omega
