import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_472_aux

open Classical

/-- The index of the inner vertex number `i` on the path of the pair (u, v). -/
def code (m k u v i : ℕ) : ℕ := m + 2 * k * (u * m + v) + i

theorem code_ge (m k u v i : ℕ) : m ≤ code m k u v i :=
  Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem code_lt {m k u v i : ℕ} (hu : u < m) (hv : v < m) (hi : i < 2 * k) :
    code m k u v i < m + 2 * k * (m * m) := by
  have h0 : (u + 1) * m ≤ m * m := Nat.mul_le_mul_right m hu
  have e0 : (u + 1) * m = u * m + m := by ring
  have h1 : u * m + v + 1 ≤ m * m := by omega
  have h2 : 2 * k * (u * m + v + 1) ≤ 2 * k * (m * m) := Nat.mul_le_mul_left _ h1
  have e : 2 * k * (u * m + v + 1) = 2 * k * (u * m + v) + 2 * k := by ring
  unfold code
  omega

theorem dm_unique {b a a' r r' : ℕ} (hr : r < b) (hr' : r' < b) (h : b * a + r = b * a' + r') :
    a = a' ∧ r = r' := by
  have ha : a = a' := by
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · exfalso
      have h1 : b * (a + 1) ≤ b * a' := Nat.mul_le_mul_left _ hlt
      have e : b * (a + 1) = b * a + b := by ring
      omega
    · exact heq
    · exfalso
      have h1 : b * (a' + 1) ≤ b * a := Nat.mul_le_mul_left _ hgt
      have e : b * (a' + 1) = b * a' + b := by ring
      omega
  subst ha
  exact ⟨rfl, by omega⟩

theorem code_inj {m k u v i u' v' i' : ℕ} (hv : v < m) (hv' : v' < m) (hi : i < 2 * k)
    (hi' : i' < 2 * k) (h : code m k u v i = code m k u' v' i') : u = u' ∧ v = v' ∧ i = i' := by
  unfold code at h
  have h1 : 2 * k * (u * m + v) + i = 2 * k * (u' * m + v') + i' := by omega
  obtain ⟨h2, h3⟩ := dm_unique hi hi' h1
  have h4 : m * u + v = m * u' + v' := by
    rw [Nat.mul_comm m u, Nat.mul_comm m u']
    exact h2
  obtain ⟨h5, h6⟩ := dm_unique hv hv' h4
  exact ⟨h5, h6, h3⟩

/-- An old vertex inside the subdivision. -/
def emb (m k : ℕ) (u : Fin m) : Fin (m + 2 * k * (m * m)) :=
  ⟨u.val, Nat.lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)⟩

/-- The inner vertex number `i` (from `0`) on the path of (u, v). -/
def iv (m k : ℕ) (u v : Fin m) (i : ℕ) : Fin (m + 2 * k * (m * m)) :=
  if h : i < 2 * k then ⟨code m k u.val v.val i, code_lt u.isLt v.isLt h⟩ else emb m k u

theorem iv_val {m k : ℕ} (u v : Fin m) {i : ℕ} (h : i < 2 * k) :
    (iv m k u v i).val = code m k u.val v.val i := by
  simp [iv, h]

theorem emb_injective (m k : ℕ) : Function.Injective (emb m k) := by
  intro u v h
  have h' : (emb m k u).val = (emb m k v).val := congrArg Fin.val h
  exact Fin.ext h'

theorem iv_inj {m k : ℕ} {u v u' v' : Fin m} {i i' : ℕ} (hi : i < 2 * k) (hi' : i' < 2 * k)
    (h : iv m k u v i = iv m k u' v' i') : u = u' ∧ v = v' ∧ i = i' := by
  have hv := congrArg Fin.val h
  rw [iv_val u v hi, iv_val u' v' hi'] at hv
  obtain ⟨h1, h2, h3⟩ := code_inj v.isLt v'.isLt hi hi' hv
  exact ⟨Fin.ext h1, Fin.ext h2, h3⟩

theorem iv_ne_emb {m k : ℕ} (u v w : Fin m) {i : ℕ} (hi : i < 2 * k) :
    iv m k u v i ≠ emb m k w := by
  intro h
  have hv := congrArg Fin.val h
  rw [iv_val u v hi] at hv
  have h1 := code_ge m k u.val v.val i
  have h2 : (emb m k w).val = w.val := rfl
  have h3 := w.isLt
  omega

/-- The edges of `H`, each once. -/
noncomputable def edges {m : ℕ} (H : SimpleGraph (Fin m)) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ H.Adj e.1 e.2)

theorem mem_edges {m : ℕ} (H : SimpleGraph (Fin m)) (e : Fin m × Fin m) :
    e ∈ edges H ↔ e.1 < e.2 ∧ H.Adj e.1 e.2 := by
  simp [edges]

/-- The inner vertex chosen in pair `j` of a path: the odd ones when `u` is in the cover. -/
noncomputable def sel {m : ℕ} (T : Finset (Fin m)) (u : Fin m) (j : ℕ) : ℕ :=
  if u ∈ T then 2 * j + 1 else 2 * j

theorem sel_lt {m k : ℕ} (T : Finset (Fin m)) (u : Fin m) {j : ℕ} (hj : j < k) :
    sel T u j < 2 * k := by
  unfold sel
  split_ifs <;> omega

/-- The forward cover built from `T`. -/
noncomputable def D (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) :
    Finset (Fin (m + 2 * k * (m * m))) :=
  T.image (emb m k) ∪
    ((edges H) ×ˢ Finset.range k).image (fun z => iv m k z.1.1 z.1.2 (sel T z.1.1 z.2))

theorem mem_D_emb {m k : ℕ} (H : SimpleGraph (Fin m)) {T : Finset (Fin m)} {u : Fin m}
    (h : u ∈ T) : emb m k u ∈ D m k H T :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)

theorem mem_D_iv {m k : ℕ} (H : SimpleGraph (Fin m)) {T : Finset (Fin m)} {u v : Fin m} {i : ℕ}
    (he : u < v) (ha : H.Adj u v) (hi : i < 2 * k) (hp : i % 2 = 1 ↔ u ∈ T) :
    iv m k u v i ∈ D m k H T := by
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨((u, v), i / 2), ?_, ?_⟩
  · rw [Finset.mem_product, mem_edges, Finset.mem_range]
    exact ⟨⟨he, ha⟩, by omega⟩
  · have hs : sel T u (i / 2) = i := by
      unfold sel
      split_ifs with h
      · have := hp.mpr h
        omega
      · have : ¬ i % 2 = 1 := fun h' => h (hp.mp h')
        omega
    simp only [hs]

theorem card_D (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) :
    (D m k H T).card = T.card + k * (edges H).card := by
  have hdisj : Disjoint (T.image (emb m k))
      (((edges H) ×ˢ Finset.range k).image
        (fun z => iv m k z.1.1 z.1.2 (sel T z.1.1 z.2))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx'
    rw [Finset.mem_product, Finset.mem_range] at hz
    exact iv_ne_emb _ _ u (sel_lt T z.1.1 hz.2) hzx
  have hinj : Set.InjOn (fun z : (Fin m × Fin m) × ℕ => iv m k z.1.1 z.1.2 (sel T z.1.1 z.2))
      (((edges H) ×ˢ Finset.range k : Finset ((Fin m × Fin m) × ℕ)) : Set ((Fin m × Fin m) × ℕ)) := by
    intro z hz z' hz' h
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hz hz'
    obtain ⟨⟨u, v⟩, j⟩ := z
    obtain ⟨⟨u', v'⟩, j'⟩ := z'
    obtain ⟨h1, h2, h3⟩ := iv_inj (sel_lt T u hz.2) (sel_lt T u' hz'.2) h
    simp only at h1 h2 h3
    subst h1
    subst h2
    have hj : j = j' := by
      unfold sel at h3
      split_ifs at h3 <;> omega
    rw [hj]
  unfold D
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (emb_injective m k),
    Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range]
  ring

/-- The two hypotheses of the statement that describe the subdivision. -/
def QSpec (m k : ℕ) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) : Prop :=
  ∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔
    (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨
      (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)

def SSpec (m k : ℕ) (H : SimpleGraph (Fin m))
    (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop)
    (S : SimpleGraph (Fin (m + 2 * k * (m * m)))) : Prop :=
  ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧
    ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))

theorem Q_iv {m k : ℕ} {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    (hQ : QSpec m k Q) (u v : Fin m) (i : ℕ) (hi : i < 2 * k) : Q u v (i + 1) (iv m k u v i) := by
  refine (hQ u v (i + 1) _).mpr (Or.inr (Or.inr ⟨by omega, by omega, ?_⟩))
  rw [iv_val u v hi]
  unfold code
  omega

theorem adj0 {m k : ℕ} {H : SimpleGraph (Fin m)}
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    {S : SimpleGraph (Fin (m + 2 * k * (m * m)))} (hQ : QSpec m k Q) (hS : SSpec m k H Q S)
    (hk : 1 ≤ k) {u v : Fin m} (he : u < v) (ha : H.Adj u v) :
    S.Adj (emb m k u) (iv m k u v 0) :=
  (hS _ _).mpr ⟨u, v, he, ha, 0, by omega,
    Or.inl ⟨(hQ u v 0 _).mpr (Or.inl ⟨rfl, rfl⟩), Q_iv hQ u v 0 (by omega)⟩⟩

theorem adj1 {m k : ℕ} {H : SimpleGraph (Fin m)}
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    {S : SimpleGraph (Fin (m + 2 * k * (m * m)))} (hQ : QSpec m k Q) (hS : SSpec m k H Q S)
    {u v : Fin m} (he : u < v) (ha : H.Adj u v) (i i' : ℕ) (hi' : i' = i + 1)
    (hi : i' < 2 * k) : S.Adj (iv m k u v i) (iv m k u v i') := by
  subst hi'
  exact (hS _ _).mpr ⟨u, v, he, ha, i + 1, by omega,
    Or.inl ⟨Q_iv hQ u v i (by omega), Q_iv hQ u v (i + 1) hi⟩⟩

theorem adjL {m k : ℕ} {H : SimpleGraph (Fin m)}
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    {S : SimpleGraph (Fin (m + 2 * k * (m * m)))} (hQ : QSpec m k Q) (hS : SSpec m k H Q S)
    (hk : 1 ≤ k) {u v : Fin m} (he : u < v) (ha : H.Adj u v) :
    S.Adj (iv m k u v (2 * k - 1)) (emb m k v) := by
  have h1 := Q_iv hQ u v (2 * k - 1) (by omega)
  rw [show 2 * k - 1 + 1 = 2 * k by omega] at h1
  exact (hS _ _).mpr ⟨u, v, he, ha, 2 * k, le_refl _,
    Or.inl ⟨h1, (hQ u v (2 * k + 1) _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩⟩

/-- Two consecutive vertices of a path are of one of three shapes. -/
theorem shape {m k : ℕ} {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    (hQ : QSpec m k Q) (hk : 1 ≤ k) {u v : Fin m} {p : ℕ} (hp : p ≤ 2 * k)
    {a b : Fin (m + 2 * k * (m * m))} (ha : Q u v p a) (hb : Q u v (p + 1) b) :
    (a = emb m k u ∧ b = iv m k u v 0) ∨
      (∃ i, i + 1 < 2 * k ∧ a = iv m k u v i ∧ b = iv m k u v (i + 1)) ∨
      (a = iv m k u v (2 * k - 1) ∧ b = emb m k v) := by
  rw [hQ] at ha hb
  rcases ha with ⟨hp0, hau⟩ | ⟨hp1, _⟩ | ⟨hp1, hp2, hac⟩
  · rcases hb with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, hbc⟩
    · omega
    · omega
    · left
      refine ⟨Fin.ext hau, Fin.ext ?_⟩
      rw [iv_val u v (by omega)]
      unfold code
      omega
  · omega
  · rcases hb with ⟨h, _⟩ | ⟨h, hbv⟩ | ⟨_, h2, hbc⟩
    · omega
    · right
      right
      refine ⟨Fin.ext ?_, Fin.ext hbv⟩
      rw [iv_val u v (by omega)]
      unfold code
      omega
    · right
      left
      refine ⟨p - 1, by omega, Fin.ext ?_, Fin.ext ?_⟩
      · rw [iv_val u v (by omega)]
        unfold code
        omega
      · rw [iv_val u v (by omega)]
        unfold code
        omega

/-- The forward cover of a cover is a cover of the subdivision. -/
theorem cover_D {m k : ℕ} {H : SimpleGraph (Fin m)}
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    {S : SimpleGraph (Fin (m + 2 * k * (m * m)))} (hQ : QSpec m k Q) (hS : SSpec m k H Q S)
    (hk : 1 ≤ k) (R : Finset (Fin m)) (hR : ∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) :
    ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ D m k H R ∨ y ∈ D m k H R := by
  have core : ∀ (u v : Fin m) (p : ℕ) (a b : Fin (m + 2 * k * (m * m))), u < v → H.Adj u v →
      p ≤ 2 * k → Q u v p a → Q u v (p + 1) b → a ∈ D m k H R ∨ b ∈ D m k H R := by
    intro u v p a b he hadj hp ha hb
    rcases shape hQ hk hp ha hb with ⟨rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · by_cases hu : u ∈ R
      · exact Or.inl (mem_D_emb H hu)
      · exact Or.inr (mem_D_iv H he hadj (by omega) (by simp [hu]))
    · by_cases hpar : (i % 2 = 1 ↔ u ∈ R)
      · exact Or.inl (mem_D_iv H he hadj (by omega) hpar)
      · refine Or.inr (mem_D_iv H he hadj hi ?_)
        by_cases hu : u ∈ R
        · simp only [hu, iff_true] at hpar ⊢
          omega
        · simp only [hu, iff_false] at hpar ⊢
          omega
    · by_cases hu : u ∈ R
      · refine Or.inl (mem_D_iv H he hadj (by omega) ?_)
        simp only [hu, iff_true]
        omega
      · rcases hR u v hadj with h | h
        · exact absurd h hu
        · exact Or.inr (mem_D_emb H h)
  intro x y hxy
  obtain ⟨u, v, he, hadj, p, hp, h | h⟩ := (hS x y).mp hxy
  · exact core u v p x y he hadj hp h.1 h.2
  · exact (core u v p y x he hadj hp h.1 h.2).symm

/-- The inner vertex of a cover `U` picked in pair `j` of the path of `e`. -/
noncomputable def pk (m k : ℕ) (U : Finset (Fin (m + 2 * k * (m * m)))) (e : Fin m × Fin m)
    (j : ℕ) : ℕ :=
  if emb m k e.1 ∉ U ∧ emb m k e.2 ∉ U then
    (if iv m k e.1 e.2 (2 * j + 1) ∈ U then 2 * j + 1 else 2 * j + 2)
  else (if iv m k e.1 e.2 (2 * j) ∈ U then 2 * j else 2 * j + 1)

theorem pk_spec {m k : ℕ} {H : SimpleGraph (Fin m)}
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    {S : SimpleGraph (Fin (m + 2 * k * (m * m)))} (hQ : QSpec m k Q) (hS : SSpec m k H Q S)
    (hk : 1 ≤ k) (U : Finset (Fin (m + 2 * k * (m * m))))
    (hU : ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U)
    (e : Fin m × Fin m) (he : e ∈ edges H) (j : ℕ) (hj : j < k) :
    pk m k U e j < 2 * k ∧ iv m k e.1 e.2 (pk m k U e j) ∈ U ∧
      ((emb m k e.1 ∉ U ∧ emb m k e.2 ∉ U) → 2 * j + 1 ≤ pk m k U e j ∧ pk m k U e j ≤ 2 * j + 2) ∧
      (¬ (emb m k e.1 ∉ U ∧ emb m k e.2 ∉ U) → 2 * j ≤ pk m k U e j ∧ pk m k U e j ≤ 2 * j + 1) := by
  rw [mem_edges] at he
  unfold pk
  split_ifs with hb h1 h1
  · exact ⟨by omega, h1, fun _ => by omega, fun h => absurd hb h⟩
  · have hjk : j + 1 < k := by
      by_contra hcon
      have hj' : 2 * j + 1 = 2 * k - 1 := by omega
      rcases hU _ _ (adjL hQ hS hk he.1 he.2) with h | h
      · rw [← hj'] at h
        exact h1 h
      · exact hb.2 h
    rcases hU _ _ (adj1 hQ hS he.1 he.2 (2 * j + 1) (2 * j + 2) rfl (by omega)) with h | h
    · exact absurd h h1
    · exact ⟨by omega, h, fun _ => by omega, fun h' => absurd hb h'⟩
  · exact ⟨by omega, h1, fun h => absurd h hb, fun _ => by omega⟩
  · rcases hU _ _ (adj1 hQ hS he.1 he.2 (2 * j) (2 * j + 1) rfl (by omega)) with h | h
    · exact absurd h h1
    · exact ⟨by omega, h, fun h' => absurd h' hb, fun _ => by omega⟩

/-- From a cover of the subdivision, a cover of `H` that is smaller by `k` per edge. -/
theorem lower {m k : ℕ} {H : SimpleGraph (Fin m)}
    {Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop}
    {S : SimpleGraph (Fin (m + 2 * k * (m * m)))} (hQ : QSpec m k Q) (hS : SSpec m k H Q S)
    (hk : 1 ≤ k) (U : Finset (Fin (m + 2 * k * (m * m))))
    (hU : ∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U) :
    ∃ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) ∧
      R.card + k * (edges H).card ≤ U.card := by
  have hU0 : ∀ u : Fin m, u ∈ Finset.univ.filter (fun u : Fin m => emb m k u ∈ U)
      ↔ emb m k u ∈ U := by
    intro u
    simp
  have hbad : ∀ e : Fin m × Fin m,
      e ∈ (edges H).filter (fun e => emb m k e.1 ∉ U ∧ emb m k e.2 ∉ U)
        ↔ e ∈ edges H ∧ (emb m k e.1 ∉ U ∧ emb m k e.2 ∉ U) := by
    intro e
    rw [Finset.mem_filter]
  generalize Finset.univ.filter (fun u : Fin m => emb m k u ∈ U) = U0 at hU0
  generalize (edges H).filter (fun e => emb m k e.1 ∉ U ∧ emb m k e.2 ∉ U) = bad at hbad
  refine ⟨U0 ∪ bad.image Prod.fst, ?_, ?_⟩
  · have key : ∀ a b : Fin m, a < b → H.Adj a b →
        a ∈ U0 ∪ bad.image Prod.fst ∨ b ∈ U0 ∪ bad.image Prod.fst := by
      intro a b hab hadj
      by_cases h1 : emb m k a ∈ U
      · exact Or.inl (Finset.mem_union_left _ ((hU0 a).mpr h1))
      · by_cases h2 : emb m k b ∈ U
        · exact Or.inr (Finset.mem_union_left _ ((hU0 b).mpr h2))
        · refine Or.inl (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a, b), ?_, rfl⟩))
          exact (hbad (a, b)).mpr ⟨(mem_edges H (a, b)).mpr ⟨hab, hadj⟩, h1, h2⟩
    intro u v hadj
    rcases lt_trichotomy u v with h | h | h
    · exact key u v h hadj
    · exact absurd h hadj.ne
    · exact (key v u h hadj.symm).symm
  · -- three disjoint families inside `U`
    have hA : (U0.image (emb m k)).card = U0.card :=
      Finset.card_image_of_injective _ (emb_injective m k)
    have hBinj : Set.InjOn (fun z : (Fin m × Fin m) × ℕ => iv m k z.1.1 z.1.2 (pk m k U z.1 z.2))
        (((edges H) ×ˢ Finset.range k : Finset ((Fin m × Fin m) × ℕ)) :
          Set ((Fin m × Fin m) × ℕ)) := by
      intro z hz z' hz' h
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hz hz'
      obtain ⟨e, j⟩ := z
      obtain ⟨e', j'⟩ := z'
      have s := pk_spec hQ hS hk U hU e hz.1 j hz.2
      have s' := pk_spec hQ hS hk U hU e' hz'.1 j' hz'.2
      obtain ⟨h1, h2, h3⟩ := iv_inj s.1 s'.1 h
      have hee : e = e' := Prod.ext h1 h2
      subst hee
      have hj : j = j' := by
        by_cases hb : emb m k e.1 ∉ U ∧ emb m k e.2 ∉ U
        · have t := s.2.2.1 hb
          have t' := s'.2.2.1 hb
          omega
        · have t := s.2.2.2 hb
          have t' := s'.2.2.2 hb
          omega
      rw [hj]
    have hB : (((edges H) ×ˢ Finset.range k).image
        (fun z => iv m k z.1.1 z.1.2 (pk m k U z.1 z.2))).card = (edges H).card * k := by
      rw [Finset.card_image_of_injOn hBinj, Finset.card_product, Finset.card_range]
    have hCinj : Set.InjOn (fun e : Fin m × Fin m => iv m k e.1 e.2 0)
        ((bad : Finset (Fin m × Fin m)) : Set (Fin m × Fin m)) := by
      intro e _ e' _ h
      obtain ⟨h1, h2, _⟩ := iv_inj (by omega) (by omega) h
      exact Prod.ext h1 h2
    have hC : (bad.image (fun e : Fin m × Fin m => iv m k e.1 e.2 0)).card = bad.card :=
      Finset.card_image_of_injOn hCinj
    have dAB : Disjoint (U0.image (emb m k))
        (((edges H) ×ˢ Finset.range k).image
          (fun z => iv m k z.1.1 z.1.2 (pk m k U z.1 z.2))) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx'
      rw [Finset.mem_product, Finset.mem_range] at hz
      exact iv_ne_emb _ _ u (pk_spec hQ hS hk U hU z.1 hz.1 z.2 hz.2).1 hzx
    have dC : Disjoint (U0.image (emb m k) ∪ ((edges H) ×ˢ Finset.range k).image
          (fun z => iv m k z.1.1 z.1.2 (pk m k U z.1 z.2)))
        (bad.image (fun e : Fin m × Fin m => iv m k e.1 e.2 0)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp hx'
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hx
        exact iv_ne_emb _ _ u (by omega) hu.symm
      · obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_product, Finset.mem_range] at hz
        have s := pk_spec hQ hS hk U hU z.1 hz.1 z.2 hz.2
        obtain ⟨h1, h2, h3⟩ := iv_inj s.1 (by omega) hzx
        have hee : z.1 = e' := Prod.ext h1 h2
        have t := s.2.2.1 (hee ▸ ((hbad e').mp he').2)
        omega
    have hsub : U0.image (emb m k) ∪ ((edges H) ×ˢ Finset.range k).image
          (fun z => iv m k z.1.1 z.1.2 (pk m k U z.1 z.2))
        ∪ bad.image (fun e : Fin m × Fin m => iv m k e.1 e.2 0) ⊆ U := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hx with hx | hx
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
          exact (hU0 u).mp hu
        · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
          rw [Finset.mem_product, Finset.mem_range] at hz
          exact (pk_spec hQ hS hk U hU z.1 hz.1 z.2 hz.2).2.1
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
        have hb := (hbad e).mp he
        have hed := (mem_edges H e).mp hb.1
        rcases hU _ _ (adj0 hQ hS hk hed.1 hed.2) with h | h
        · exact absurd h hb.2.1
        · exact h
    have c1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint dC, Finset.card_union_of_disjoint dAB, hA, hB, hC] at c1
    have c2 : (U0 ∪ bad.image Prod.fst).card ≤ U0.card + bad.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
    have c3 : k * (edges H).card = (edges H).card * k := Nat.mul_comm _ _
    omega

end PEqualNP.Outside.L_meta_472_aux

open PEqualNP.Outside.L_meta_472_aux in
theorem PEqualNP.Outside.L_meta_472 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop) (S : SimpleGraph (Fin (m + 2 * k * (m * m)))), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) → ∀ (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ u v : Fin m, H.Adj u v → u ∈ T ∨ v ∈ T) → (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → (∀ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) → T.card ≤ R.card + 1) → (∀ U : Finset (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U) → T'.card ≤ U.card + 1) ∧ ((∀ U : Finset (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y → x ∈ U ∨ y ∈ U) → T'.card ≤ U.card) ↔ (∀ R : Finset (Fin m), (∀ u v : Fin m, H.Adj u v → u ∈ R ∨ v ∈ R) → T.card ≤ R.card)) := by
  intro m k H Q S hk hQ hS T T' hT hT' hnear
  have hTD : T' = D m k H T := by
    ext x
    rw [hT']
    constructor
    · rintro (⟨u, hu, hx⟩ | ⟨u, v, i, hi, he, hadj, hx, hp⟩)
      · have : x = emb m k u := Fin.ext hx
        rw [this]
        exact mem_D_emb H hu
      · have : x = iv m k u v i := by
          apply Fin.ext
          rw [iv_val u v hi]
          exact hx
        rw [this]
        exact mem_D_iv H he hadj hi hp
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        exact Or.inl ⟨u, hu, rfl⟩
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
        rw [Finset.mem_product, Finset.mem_range, mem_edges] at hz
        refine Or.inr ⟨z.1.1, z.1.2, sel T z.1.1 z.2, sel_lt T z.1.1 hz.2, hz.1.1, hz.1.2, ?_, ?_⟩
        · rw [iv_val _ _ (sel_lt T z.1.1 hz.2)]
          rfl
        · unfold sel
          split_ifs with h
          · simp only [h, iff_true]
            omega
          · simp only [h, iff_false]
            omega
  have hcard : T'.card = T.card + k * (edges H).card := by
    rw [hTD]
    exact card_D m k H T
  refine ⟨?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨R, hR, hRc⟩ := lower hQ hS hk U hU
    have := hnear R hR
    omega
  · intro hmin R hR
    have h1 := hmin (D m k H R) (cover_D hQ hS hk R hR)
    rw [card_D] at h1
    omega
  · intro hmin U hU
    obtain ⟨R, hR, hRc⟩ := lower hQ hS hk U hU
    have := hmin R hR
    omega
