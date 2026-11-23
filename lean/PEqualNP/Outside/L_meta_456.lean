import Mathlib
import PEqualNP.Defs

namespace Meta456

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

private def along (d s u v p : ℕ) : ℕ :=
  if u = s then p else if v = s then d + 1 - p else d + 1

private def height (m d s a : ℕ) : ℕ :=
  if a < m then (if a = s then 0 else d + 1)
  else let z := decode m d a; along d s z.1 z.2.1 z.2.2

private theorem label_height {m d u v p : ℕ} (s : ℕ) (hu : u < m) (hv : v < m)
    (huv : u ≠ v) (hp : p ≤ d + 1) :
    height m d s (label m d u v p) = along d s u v p := by
  by_cases h0 : p = 0
  · subst p
    simp only [label, height, along]
    split_ifs <;> omega
  by_cases h1 : p = d + 1
  · subst p
    simp only [label, ite_eq_right (show d + 1 ≠ 0 by omega), height, along]
    split_ifs <;> omega
  · have hi : m ≤ label m d u v p := by simp [label,h0,h1]
    rw [height, ite_eq_right (by omega), decode_label hv (by omega) (by omega)]

private def EdgeLabels {m d N : ℕ} (S : SimpleGraph (Fin N)) : Prop :=
  ∀ {x y : Fin N}, S.Adj x y → ∃ u v : Fin m, u ≠ v ∧ ∃ p ≤ d,
    (x.val = label m d u.val v.val p ∧ y.val = label m d u.val v.val (p+1)) ∨
    (y.val = label m d u.val v.val p ∧ x.val = label m d u.val v.val (p+1))

private theorem edge_height {m d N : ℕ} {S : SimpleGraph (Fin N)}
    (edges : EdgeLabels (m:=m) (d:=d) S) (s : ℕ) {a b : Fin N} (hab : S.Adj a b) :
    height m d s b.val ≤ height m d s a.val + 1 := by
  obtain ⟨u,v,huv,p,hp,h | h⟩ := edges hab
  all_goals
    have hne : u.val ≠ v.val := fun eq => huv (Fin.ext eq)
    rw [h.1,h.2,label_height s u.isLt v.isLt hne (by omega),
      label_height s u.isLt v.isLt hne (by omega)]
    unfold along
    split_ifs <;> omega

private theorem walk_height {m d N : ℕ} {S : SimpleGraph (Fin N)}
    (edges : EdgeLabels (m:=m) (d:=d) S) (s : ℕ) {a b : Fin N} (p : S.Walk a b) :
    height m d s b.val ≤ height m d s a.val + p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have step := edge_height edges s h
    rw [SimpleGraph.Walk.length_cons]
    omega

end Meta456

theorem PEqualNP.Outside.L_meta_456 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ x y : Fin (m + 2 * k * (m * m)), x.val < m → y.val < m → x ≠ y → ∀ p : S.Walk x y, 2 * k + 1 ≤ p.length := by
  intro m k H Q S hk hQ hS x y hx hy hxy p
  have pos : ∀ (u v : Fin m) (i : ℕ) (z : Fin (m + 2*k*(m*m))), Q u v i z →
      z.val = Meta456.label m (2*k) u.val v.val i := by
    intro u v i z hz
    rcases (hQ u v i z).mp hz with ⟨rfl,h⟩ | ⟨rfl,h⟩ | ⟨h1,h2,h⟩
    · simpa [Meta456.label] using h
    · simpa [Meta456.label] using h
    · simp only [Meta456.label, ite_eq_right (show i ≠ 0 by omega),
        ite_eq_right (show i ≠ 2*k+1 by omega)]
      omega
  have edges : Meta456.EdgeLabels (m:=m) (d:=2*k) S := by
    intro a b hab
    obtain ⟨u,v,huv,_,i,hi,e⟩ := (hS a b).mp hab
    refine ⟨u,v,ne_of_lt huv,i,hi,?_⟩
    rcases e with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inl ⟨pos _ _ _ _ h1,pos _ _ _ _ h2⟩
    · exact Or.inr ⟨pos _ _ _ _ h1,pos _ _ _ _ h2⟩
  have hne : y.val ≠ x.val := fun h => hxy (Fin.ext h.symm)
  simpa [Meta456.height,hx,hy,hne] using Meta456.walk_height edges x.val p
