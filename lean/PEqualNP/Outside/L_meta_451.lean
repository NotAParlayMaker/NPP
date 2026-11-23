import Mathlib
import PEqualNP.Defs

namespace Meta451

private def label (m d u v p : ℕ) : ℕ :=
  if p = 0 then u else if p = d + 1 then v else m + (d * (u * m + v) + (p - 1))

private def decode (m d a : ℕ) : ℕ × ℕ × ℕ :=
  let slot := (a - m) / d
  (slot / m, slot % m, (a - m) % d + 1)

private theorem decode_label {m d u v p : ℕ} (hv : v < m) (hp1 : 1 ≤ p) (hp2 : p ≤ d) :
    decode m d (label m d u v p) = (u,v,p) := by
  have hd : 0 < d := by omega
  have hm : 0 < m := by omega
  have hpd : p - 1 < d := by omega
  have step : (d * (u * m + v) + (p-1)) / d = u * m + v := by
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hpd, Nat.add_zero]
  have step2 : (u * m + v) / m = u := by
    rw [Nat.mul_comm u m, Nat.mul_add_div hm, Nat.div_eq_of_lt hv, Nat.add_zero]
  have step3 : (u * m + v) % m = v := by
    rw [Nat.mul_comm u m, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
  have step4 : (d * (u * m + v) + (p-1)) % d + 1 = p := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hpd]
    omega
  rw [show label m d u v p = m + (d*(u*m+v)+(p-1)) by
    simp [label,show p ≠ 0 by omega,show p ≠ d+1 by omega]]
  simp only [decode,Nat.add_sub_cancel_left,step,step2,step3,step4]

private def EdgeLabels {m d N : ℕ} (S : SimpleGraph (Fin N)) : Prop :=
  ∀ {x y : Fin N}, S.Adj x y → ∃ u v : Fin m, u ≠ v ∧ ∃ p ≤ d,
    (x.val = label m d u.val v.val p ∧ y.val = label m d u.val v.val (p+1)) ∨
    (y.val = label m d u.val v.val p ∧ x.val = label m d u.val v.val (p+1))

private theorem neighbor_labels {m d N : ℕ} {S : SimpleGraph (Fin N)}
    (edges : EdgeLabels (m:=m) (d:=d) S) {x y : Fin N} (hx : m ≤ x.val) (edge : S.Adj x y) :
    let z := decode m d x.val
    y.val = label m d z.1 z.2.1 (z.2.2 - 1) ∨ y.val = label m d z.1 z.2.1 (z.2.2 + 1) := by
  obtain ⟨u,v,_,p,hp,h | h⟩ := edges edge
  · obtain ⟨ex,ey⟩ := h
    have h0 : p ≠ 0 := by
      rintro rfl
      simp [label] at ex
      have := u.isLt
      omega
    dsimp only
    rw [ex,decode_label v.isLt (by omega) hp]
    exact Or.inr ey
  · obtain ⟨ey,ex⟩ := h
    have h1 : p + 1 ≠ d + 1 := by
      intro e
      have ex' : x.val = v.val := by simpa [label,e] using ex
      have := v.isLt
      omega
    dsimp only
    rw [ex,decode_label v.isLt (by omega) (by omega)]
    exact Or.inl (by simpa using ey)

private theorem label_lt {m d : ℕ} (u v : Fin m) (i : ℕ) (hi : i ≤ d+1) :
    label m d u.val v.val i < m + d*(m*m) := by
  have hu := u.isLt
  have hv := v.isLt
  have hrow := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hu)
  rw [Nat.succ_mul] at hrow
  have hslot : u.val * m + v.val < m * m := by omega
  have hnext := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hslot)
  rw [Nat.mul_succ] at hnext
  unfold label
  split_ifs <;> omega

private theorem distinct_labels {m d i j : ℕ} (u v : Fin m) (huv : u ≠ v)
    (hi : i ≤ d+1) (hj : j ≤ d+1) (hne : i ≠ j) :
    label m d u.val v.val i ≠ label m d u.val v.val j := by
  have hu := u.isLt
  have hv := v.isLt
  have hval : u.val ≠ v.val := fun he => huv (Fin.ext he)
  unfold label
  split_ifs <;> omega

end Meta451

theorem PEqualNP.Outside.L_meta_451 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), u < v → H.Adj u v → 1 ≤ p → p ≤ 2 * k → Q u v p x → (S.neighborSet x).ncard = 2 := by
  intro m k H Q S hk hQ hS u v p x huv he hp1 hp2 hqx
  have pos : ∀ (u v : Fin m) (i : ℕ) (z : Fin (m + 2*k*(m*m))), Q u v i z →
      z.val = Meta451.label m (2*k) u.val v.val i := by
    intro u v i z hz
    rcases (hQ u v i z).mp hz with ⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨h1,h2,h⟩
    · simpa [Meta451.label] using h
    · simpa [Meta451.label] using h
    · simp only [Meta451.label, ite_eq_right (show i ≠ 0 by omega),
        ite_eq_right (show i ≠ 2*k+1 by omega)]
      omega
  have edges : Meta451.EdgeLabels (m:=m) (d:=2*k) S := by
    intro a b hab
    obtain ⟨u,v,huv,_,i,hi,e⟩ := (hS a b).mp hab
    refine ⟨u,v,ne_of_lt huv,i,hi,?_⟩
    rcases e with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inl ⟨pos _ _ _ _ h1,pos _ _ _ _ h2⟩
    · exact Or.inr ⟨pos _ _ _ _ h1,pos _ _ _ _ h2⟩
  let pt (i : ℕ) (hi : i ≤ 2*k+1) : Fin (m + 2*k*(m*m)) :=
    ⟨Meta451.label m (2*k) u.val v.val i, Meta451.label_lt u v i hi⟩
  have qat (i : ℕ) (hi : i ≤ 2*k+1) : Q u v i (pt i hi) := by
    apply (hQ u v i _).mpr
    by_cases h0 : i = 0
    · exact Or.inl ⟨h0,by simp [pt,Meta451.label,h0]⟩
    by_cases h1 : i = 2*k+1
    · exact Or.inr (Or.inl ⟨h1,by simp [pt,Meta451.label,h1]⟩)
    · right; right
      refine ⟨by omega,by omega,?_⟩
      simp only [pt, Meta451.label, ite_eq_right h0, ite_eq_right h1]
      omega
  let a := pt (p-1) (by omega)
  let b := pt (p+1) (by omega)
  have ha : S.Adj x a := by
    apply (hS x a).mpr
    refine ⟨u,v,huv,he,p-1,by omega, Or.inr ⟨qat (p-1) (by omega),?_⟩⟩
    simpa [show p-1+1=p by omega] using hqx
  have hb : S.Adj x b := (hS x b).mpr ⟨u,v,huv,he,p,hp2,Or.inl ⟨hqx, qat (p+1) (by omega)⟩⟩
  have hab : a ≠ b := by
    intro e
    exact Meta451.distinct_labels u v (ne_of_lt huv) (by omega : p-1 ≤ 2*k+1)
      (by omega : p+1 ≤ 2*k+1) (by omega) (congrArg Fin.val e)
  have ex := pos u v p x hqx
  have hx : m ≤ x.val := by
    rw [ex]
    simp [Meta451.label,show p ≠ 0 by omega,show p ≠ 2*k+1 by omega]
  have decoded : Meta451.decode m (2*k) x.val = (u.val,v.val,p) := by
    rw [ex,Meta451.decode_label v.isLt hp1 hp2]
  have neigh : S.neighborSet x = {a,b} := by
    ext y
    constructor
    · intro h
      have hh := Meta451.neighbor_labels edges hx h
      dsimp only at hh
      rw [decoded] at hh
      exact hh.elim (fun eq => Or.inl (Fin.ext eq)) (fun eq => Or.inr (Fin.ext eq))
    · rintro (rfl | rfl)
      · exact ha
      · exact hb
  rw [neigh,Set.ncard_pair hab]
