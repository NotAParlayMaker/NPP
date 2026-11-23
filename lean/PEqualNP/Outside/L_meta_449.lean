import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

namespace L449

def enc (m k u v i : ℕ) : ℕ := m + 2 * k * (u * m + v) + i

theorem enc_lt (m k u v i : ℕ) (hu : u < m) (hv : v < m) (hi : i < 2 * k) :
    enc m k u v i < m + 2 * k * (m * m) := by
  unfold enc
  have h1 : u * m + v + 1 ≤ m * m := by
    calc u * m + v + 1 ≤ u * m + m := by omega
      _ = (u + 1) * m := by ring
      _ ≤ m * m := Nat.mul_le_mul_right m hu
  have h2 : 2 * k * (u * m + v) + i < 2 * k * (u * m + v + 1) := by
    have : 2 * k * (u * m + v + 1) = 2 * k * (u * m + v) + 2 * k := by ring
    omega
  have h3 : 2 * k * (u * m + v + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ h1
  omega

/-- The value of the vertex at position `p` on the path from `u` to `v`. -/
def vval (m k u v p : ℕ) : ℕ :=
  if p = 0 then u else if p = 2 * k + 1 then v else enc m k u v (p - 1)

theorem vval_lt (m k u v p : ℕ) (hu : u < m) (hv : v < m) (hp : p ≤ 2 * k + 1) :
    vval m k u v p < m + 2 * k * (m * m) := by
  unfold vval
  split_ifs with h0 h1
  · omega
  · omega
  · exact enc_lt m k u v (p - 1) hu hv (by omega)

def vert (m k : ℕ) (u v : Fin m) (p : ℕ) : Fin (m + 2 * k * (m * m)) :=
  ⟨vval m k u.val v.val p % (m + 2 * k * (m * m)), Nat.mod_lt _ (by have := u.isLt; omega)⟩

theorem vert_val (m k : ℕ) (u v : Fin m) (p : ℕ) (hp : p ≤ 2 * k + 1) :
    (vert m k u v p).val = vval m k u.val v.val p :=
  Nat.mod_eq_of_lt (vval_lt m k u.val v.val p u.isLt v.isLt hp)

/-- Decoding of an inner vertex: its edge and its index. -/
def dec (m k z : ℕ) : ℕ × ℕ × ℕ := ((z - m) / (2 * k) / m, (z - m) / (2 * k) % m, (z - m) % (2 * k))

theorem dec_enc (m k u v i : ℕ) (hk : 1 ≤ k) (hu : u < m) (hv : v < m) (hi : i < 2 * k) :
    dec m k (enc m k u v i) = (u, v, i) := by
  have hm : 0 < m := by omega
  have hk2 : 0 < 2 * k := by omega
  have hq : enc m k u v i - m = 2 * k * (u * m + v) + i := by unfold enc; omega
  have hmod : (2 * k * (u * m + v) + i) % (2 * k) = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have hdiv : (2 * k * (u * m + v) + i) / (2 * k) = u * m + v := by
    rw [Nat.mul_add_div hk2, Nat.div_eq_of_lt hi, Nat.add_zero]
  have hdiv2 : (u * m + v) / m = u := by
    rw [Nat.mul_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt hv, Nat.add_zero]
  have hmod2 : (u * m + v) % m = v := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
  simp only [dec, hq, hmod, hdiv, hdiv2, hmod2]

/-- The segment index recovered from the values of the two ends of an edge of the subdivision. -/
def code (m k a b : ℕ) : ℕ × ℕ × ℕ :=
  if a < m then ((dec m k b).1, (dec m k b).2.1, if (dec m k b).2.2 = 0 then 0 else 2 * k)
  else ((dec m k a).1, (dec m k a).2.1, (dec m k a).2.2 + 1)

def lo {m : ℕ} (e : Sym2 (Fin m)) : Fin m := Sym2.lift ⟨fun a b => min a b, fun a b => min_comm a b⟩ e
def hi {m : ℕ} (e : Sym2 (Fin m)) : Fin m := Sym2.lift ⟨fun a b => max a b, fun a b => max_comm a b⟩ e

theorem lo_mk {m : ℕ} (a b : Fin m) : lo s(a, b) = min a b := rfl
theorem hi_mk {m : ℕ} (a b : Fin m) : hi s(a, b) = max a b := rfl

theorem mk_lo_hi {m : ℕ} (e : Sym2 (Fin m)) : s(lo e, hi e) = e := by
  induction e using Sym2.ind with
  | h a b =>
    rw [lo_mk, hi_mk]
    rcases le_total a b with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, Sym2.eq_swap]

def G (m k : ℕ) (z : Sym2 (Fin (m + 2 * k * (m * m)))) : ℕ × ℕ × ℕ :=
  Sym2.lift ⟨fun a b => code m k (min a.val b.val) (max a.val b.val),
    fun a b => by simp only [min_comm, max_comm]⟩ z

theorem G_mk (m k : ℕ) (a b : Fin (m + 2 * k * (m * m))) :
    G m k s(a, b) = code m k (min a.val b.val) (max a.val b.val) := rfl

/-- The edge of the subdivision at segment `p` of the subdivided edge `e`. -/
def f (m k : ℕ) (z : Sym2 (Fin m) × Fin (2 * k + 1)) : Sym2 (Fin (m + 2 * k * (m * m))) :=
  s(vert m k (lo z.1) (hi z.1) z.2.val, vert m k (lo z.1) (hi z.1) (z.2.val + 1))

theorem G_f (m k : ℕ) (hk : 1 ≤ k) (u v : Fin m) (huv : u < v) (p : ℕ) (hp : p ≤ 2 * k) :
    G m k s(vert m k u v p, vert m k u v (p + 1)) = (u.val, v.val, p) := by
  have hu := u.isLt
  have hv := v.isLt
  have huv' : u.val < v.val := Fin.lt_def.1 huv
  rw [G_mk, vert_val m k u v p (by omega), vert_val m k u v (p + 1) (by omega)]
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0
    have h1 : vval m k u.val v.val 0 = u.val := by simp [vval]
    have h2 : vval m k u.val v.val 1 = enc m k u.val v.val 0 := by
      simp only [vval, show (1 : ℕ) ≠ 0 by omega, ite_false, show (1 : ℕ) ≠ 2 * k + 1 by omega]
    have hlt : u.val < enc m k u.val v.val 0 := by unfold enc; omega
    rw [h1, h2, min_eq_left hlt.le, max_eq_right hlt.le]
    simp only [code, hu, ite_true, dec_enc m k u.val v.val 0 hk hu hv (by omega)]
  · rcases Nat.lt_or_ge p (2 * k) with hp2 | hp2
    · have h1 : vval m k u.val v.val p = enc m k u.val v.val (p - 1) := by
        simp only [vval, show p ≠ 0 by omega, ite_false, show p ≠ 2 * k + 1 by omega]
      have h2 : vval m k u.val v.val (p + 1) = enc m k u.val v.val p := by
        simp only [vval, show p + 1 ≠ 0 by omega, ite_false, show p + 1 ≠ 2 * k + 1 by omega, Nat.add_sub_cancel]
      have hlt : enc m k u.val v.val (p - 1) < enc m k u.val v.val p := by unfold enc; omega
      rw [h1, h2, min_eq_left hlt.le, max_eq_right hlt.le]
      have hge : ¬ (enc m k u.val v.val (p - 1) < m) := by unfold enc; omega
      simp only [code, hge, ite_false, dec_enc m k u.val v.val (p - 1) hk hu hv (by omega)]
      congr 2; omega
    · have hp' : p = 2 * k := by omega
      subst hp'
      have h1 : vval m k u.val v.val (2 * k) = enc m k u.val v.val (2 * k - 1) := by
        simp only [vval, show 2 * k ≠ 0 by omega, ite_false, show 2 * k ≠ 2 * k + 1 by omega]
      have h2 : vval m k u.val v.val (2 * k + 1) = v.val := by
        simp only [vval, show 2 * k + 1 ≠ 0 by omega, ite_false, ite_true]
      have hlt : v.val < enc m k u.val v.val (2 * k - 1) := by unfold enc; omega
      rw [h1, h2, min_eq_right hlt.le, max_eq_left hlt.le]
      simp only [code, hv, ite_true, dec_enc m k u.val v.val (2 * k - 1) hk hu hv (by omega),
        show 2 * k - 1 ≠ 0 by omega, ite_false]

end L449

end PEqualNP.Outside

theorem PEqualNP.Outside.L_meta_449 :
    ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → S.edgeSet.ncard = (2 * k + 1) * H.edgeSet.ncard := by
  intro m k H Q S hk hQ hS
  -- the position predicate against the vertex builder
  have hQv : ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), p ≤ 2 * k + 1 →
      (Q u v p x ↔ x.val = L449.vval m k u.val v.val p) := by
    intro u v p x hp
    rw [hQ]
    unfold L449.vval L449.enc
    constructor
    · rintro (⟨h0, hx⟩ | ⟨h1, hx⟩ | ⟨h1, h2, hx⟩)
      · subst h0; simpa using hx
      · subst h1; simp only [show 2 * k + 1 ≠ 0 by omega, ite_false, ite_true]; exact hx
      · simp only [show p ≠ 0 by omega, ite_false, show p ≠ 2 * k + 1 by omega]; omega
    · intro hx
      by_cases h0 : p = 0
      · subst h0; left; exact ⟨rfl, by simpa using hx⟩
      · by_cases h1 : p = 2 * k + 1
        · subst h1; right; left; refine ⟨rfl, ?_⟩; simpa [show 2 * k + 1 ≠ 0 by omega] using hx
        · right; right; refine ⟨by omega, by omega, ?_⟩
          simp only [h0, ite_false, h1] at hx; omega
  -- oriented ends of an edge of `H`
  have horient : ∀ e ∈ H.edgeSet, L449.lo e < L449.hi e ∧ H.Adj (L449.lo e) (L449.hi e) := by
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet] at he
      rw [L449.lo_mk, L449.hi_mk]
      have hne := he.ne
      rcases lt_or_gt_of_ne hne with h | h
      · rw [min_eq_left h.le, max_eq_right h.le]; exact ⟨h, he⟩
      · rw [min_eq_right h.le, max_eq_left h.le]; exact ⟨h, he.symm⟩
  set D : Set (Sym2 (Fin m) × Fin (2 * k + 1)) := H.edgeSet ×ˢ Set.univ with hD
  -- the edges of the subdivision are the image of the segments
  have himage : S.edgeSet = L449.f m k '' D := by
    ext z
    constructor
    · intro hz
      induction z using Sym2.ind with
      | h x y =>
        rw [SimpleGraph.mem_edgeSet] at hz
        obtain ⟨u, v, huv, hH, p, hp, h⟩ := (hS x y).1 hz
        have hlo : L449.lo s(u, v) = u := by rw [L449.lo_mk, min_eq_left huv.le]
        have hhi : L449.hi s(u, v) = v := by rw [L449.hi_mk, max_eq_right huv.le]
        refine ⟨(s(u, v), ⟨p, by omega⟩), ⟨(SimpleGraph.mem_edgeSet H).2 hH, Set.mem_univ _⟩, ?_⟩
        simp only [L449.f, hlo, hhi]
        rcases h with ⟨hx, hy⟩ | ⟨hy, hx⟩
        · have ex : x = L449.vert m k u v p :=
            Fin.ext (by rw [L449.vert_val m k u v p (by omega)]; exact (hQv u v p x (by omega)).1 hx)
          have ey : y = L449.vert m k u v (p + 1) :=
            Fin.ext (by rw [L449.vert_val m k u v (p + 1) (by omega)]; exact (hQv u v (p + 1) y (by omega)).1 hy)
          rw [ex, ey]
        · have ex : x = L449.vert m k u v (p + 1) :=
            Fin.ext (by rw [L449.vert_val m k u v (p + 1) (by omega)]; exact (hQv u v (p + 1) x (by omega)).1 hx)
          have ey : y = L449.vert m k u v p :=
            Fin.ext (by rw [L449.vert_val m k u v p (by omega)]; exact (hQv u v p y (by omega)).1 hy)
          rw [ex, ey, Sym2.eq_swap]
    · rintro ⟨⟨e, p⟩, ⟨he, -⟩, rfl⟩
      obtain ⟨hlt, hadj⟩ := horient e he
      simp only [L449.f]
      rw [SimpleGraph.mem_edgeSet, hS]
      refine ⟨L449.lo e, L449.hi e, hlt, hadj, p.val, by omega, Or.inl ⟨?_, ?_⟩⟩
      · exact (hQv _ _ p.val _ (by omega)).2 (L449.vert_val m k _ _ p.val (by omega))
      · exact (hQv _ _ (p.val + 1) _ (by omega)).2 (L449.vert_val m k _ _ (p.val + 1) (by omega))
  have hinj : Set.InjOn (L449.f m k) D := by
    rintro ⟨e, p⟩ ⟨he, -⟩ ⟨e', p'⟩ ⟨he', -⟩ hfe
    obtain ⟨hlt, -⟩ := horient e he
    obtain ⟨hlt', -⟩ := horient e' he'
    have h1 := L449.G_f m k hk _ _ hlt p.val (by omega)
    have h2 := L449.G_f m k hk _ _ hlt' p'.val (by omega)
    simp only [L449.f] at hfe
    rw [hfe, h2] at h1
    simp only [Prod.mk.injEq] at h1
    obtain ⟨hl, hh, hp⟩ := h1
    have hee : e = e' := by
      rw [← L449.mk_lo_hi e, ← L449.mk_lo_hi e', Fin.ext hl.symm, Fin.ext hh.symm]
    rw [hee, Fin.ext hp.symm]
  rw [himage, hinj.ncard_image, hD, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin, Nat.mul_comm]
