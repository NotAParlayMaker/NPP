import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_469_aux

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

theorem edges_card {m : ℕ} (H : SimpleGraph (Fin m)) : (edges H).card = H.edgeSet.ncard := by
  have hinj : Set.InjOn (fun e : Fin m × Fin m => s(e.1, e.2))
      ((edges H : Finset (Fin m × Fin m)) : Set (Fin m × Fin m)) := by
    intro e he e' he' h
    rw [Finset.mem_coe, mem_edges] at he he'
    simp only at h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have h3 := he.1
      have h4 := he'.1
      rw [h1, h2] at h3
      exact lt_asymm h3 h4
  have hset : (((edges H).image (fun e : Fin m × Fin m => s(e.1, e.2)) : Finset (Sym2 (Fin m)))
      : Set (Sym2 (Fin m))) = H.edgeSet := by
    ext z
    induction z using Sym2.ind with
    | _ a b =>
      rw [Finset.mem_coe, Finset.mem_image, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨e, he, hz⟩
        rw [mem_edges] at he
        rcases Sym2.eq_iff.mp hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]
          exact he.2
        · rw [← h1, ← h2]
          exact he.2.symm
      · intro hadj
        rcases lt_trichotomy a b with h | h | h
        · exact ⟨(a, b), (mem_edges H (a, b)).mpr ⟨h, hadj⟩, rfl⟩
        · exact absurd h hadj.ne
        · exact ⟨(b, a), (mem_edges H (b, a)).mpr ⟨h, hadj.symm⟩, Sym2.eq_swap⟩
  rw [← hset, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]

end PEqualNP.Outside.L_meta_469_aux

open PEqualNP.Outside.L_meta_469_aux in
theorem PEqualNP.Outside.L_meta_469 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (T : Finset (Fin m)) (T' : Finset (Fin (m + 2 * k * (m * m)))), (∀ x : Fin (m + 2 * k * (m * m)), x ∈ T' ↔ (∃ u ∈ T, x.val = u.val) ∨ ∃ u v : Fin m, ∃ i : ℕ, i < 2 * k ∧ u < v ∧ H.Adj u v ∧ x.val = m + 2 * k * (u.val * m + v.val) + i ∧ (i % 2 = 1 ↔ u ∈ T)) → T'.card = T.card + k * H.edgeSet.ncard := by
  intro m k H T T' hT'
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
  rw [hTD, card_D, edges_card]
