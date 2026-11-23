import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_730

def OddLoop {n : ℕ} (H : SimpleGraph (Fin n)) (m : ℕ) (f : ℕ → Fin n) : Prop :=
  m % 2 = 1 ∧ f m = f 0 ∧ ∀ i < m, H.Adj (f i) (f (i + 1))

theorem oddLoop_three_le {n : ℕ} {H : SimpleGraph (Fin n)} {m : ℕ} {f : ℕ → Fin n}
    (h : OddLoop H m f) : 3 ≤ m := by
  rcases h with ⟨hm, hclose, hadj⟩
  by_contra hlt
  have hm1 : m = 1 := by omega
  subst hm1
  have ha := hadj 0 (by omega)
  rw [hclose] at ha
  exact H.irrefl ha

theorem min_oddLoop_inj {n : ℕ} {H : SimpleGraph (Fin n)} {m : ℕ} {f : ℕ → Fin n}
    (h : OddLoop H m f) (hmin : ∀ m' < m, ¬ ∃ f', OddLoop H m' f') :
    ∀ i < m, ∀ j < m, f i = f j → i = j := by
  rcases h with ⟨hm, hclose, hadj⟩
  have hlt_ne : ∀ i j, i < j → j < m → f i ≠ f j := by
    intro i j hij hjm heq
    let m1 := j - i
    let f1 : ℕ → Fin n := fun k => f (i + k)
    have hc1 : f1 m1 = f1 0 := by
      dsimp [f1, m1]
      rw [Nat.add_sub_of_le (by omega), heq]
    have ha1 : ∀ k < m1, H.Adj (f1 k) (f1 (k + 1)) := by
      intro k hk
      dsimp [f1]
      rw [← Nat.add_assoc]
      exact hadj (i + k) (by omega)
    let m2 := m - (j - i)
    let f2 : ℕ → Fin n := fun k => if k ≤ i then f k else f (k + (j - i))
    have hc2 : f2 m2 = f2 0 := by
      dsimp [f2, m2]
      rw [if_neg (by omega), Nat.sub_add_cancel (by omega), hclose]
    have ha2 : ∀ k < m2, H.Adj (f2 k) (f2 (k + 1)) := by
      intro k hk
      dsimp [f2]
      by_cases hk1 : k < i
      · rw [if_pos (by omega), if_pos (by omega)]
        exact hadj k (by omega)
      · by_cases hk2 : k = i
        · subst hk2
          rw [if_pos (by omega), if_neg (by omega), heq,
            show k + 1 + (j - k) = j + 1 by omega]
          exact hadj j (by omega)
        · rw [if_neg (by omega), if_neg (by omega),
            show k + 1 + (j - i) = (k + (j - i)) + 1 by omega]
          exact hadj (k + (j - i)) (by omega)
    by_cases h1 : m1 % 2 = 1
    · exact hmin m1 (by omega) ⟨f1, h1, hc1, ha1⟩
    · have h2 : m2 % 2 = 1 := by omega
      exact hmin m2 (by omega) ⟨f2, h2, hc2, ha2⟩
  intro i hi j hj heq
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact (hlt_ne i j hij hj heq).elim
  · rfl
  · exact (hlt_ne j i hji hi heq.symm).elim

theorem min_oddLoop_chord {n : ℕ} {H : SimpleGraph (Fin n)} {m : ℕ} {f : ℕ → Fin n}
    (h : OddLoop H m f) (hmin : ∀ m' < m, ¬ ∃ f', OddLoop H m' f') :
    ∀ i j, i < j → j < m → H.Adj (f i) (f j) → j = i + 1 ∨ (i = 0 ∧ j = m - 1) := by
  rcases h with ⟨hm, hclose, hadj⟩
  intro i j hij hjm hchord
  let m1 := j - i + 1
  let g1 : ℕ → Fin n := fun k => if k ≤ j - i then f (i + k) else f i
  have hc1 : g1 m1 = g1 0 := by
    dsimp [g1, m1]
    rw [if_neg (by omega)]
  have ha1 : ∀ k < m1, H.Adj (g1 k) (g1 (k + 1)) := by
    intro k hk
    dsimp [g1]
    by_cases hk1 : k < j - i
    · rw [if_pos (by omega), if_pos (by omega), ← Nat.add_assoc]
      exact hadj (i + k) (by omega)
    · have hk2 : k = j - i := by omega
      subst hk2
      rw [if_pos (by omega), if_neg (by omega), Nat.add_sub_of_le (by omega)]
      exact hchord.symm
  let m2 := m - (j - i) + 1
  let g2 : ℕ → Fin n := fun k => if k ≤ i then f k else f (k - 1 + (j - i))
  have hc2 : g2 m2 = g2 0 := by
    dsimp [g2, m2]
    rw [if_neg (by omega), Nat.sub_add_cancel (by omega), hclose]
  have ha2 : ∀ k < m2, H.Adj (g2 k) (g2 (k + 1)) := by
    intro k hk
    dsimp [g2]
    by_cases hk1 : k < i
    · rw [if_pos (by omega), if_pos (by omega)]
      exact hadj k (by omega)
    · by_cases hk2 : k = i
      · subst hk2
        rw [if_pos (by omega), if_neg (by omega),
          show k + (j - k) = j by omega]
        exact hchord
      · rw [if_neg (by omega), if_neg (by omega),
          show k + (j - i) = (k - 1 + (j - i)) + 1 by omega]
        exact hadj (k - 1 + (j - i)) (by omega)
  by_cases h1 : m1 % 2 = 1
  · by_cases hlt1 : m1 < m
    · exact (hmin m1 hlt1 ⟨g1, h1, hc1, ha1⟩).elim
    · right
      omega
  · have h2 : m2 % 2 = 1 := by omega
    by_cases hlt2 : m2 < m
    · exact (hmin m2 hlt2 ⟨g2, h2, hc2, ha2⟩).elim
    · left
      omega

theorem forward (n : ℕ) (H : SimpleGraph (Fin n))
    (hker : ∀ D : Fin n → Fin n → Prop,
      (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k) :
    H.Colorable 2 := by
  classical
  by_contra hnot
  have hnot' : ¬ ∀ (v : Fin n) (p : H.Walk v v), Even p.length := by
    intro h
    exact hnot (SimpleGraph.isBipartite_iff_forall_walk_even_length.mpr h)
  push Not at hnot'
  obtain ⟨v0, p0, hp0⟩ := hnot'
  have hex : ∃ m, ∃ f, OddLoop H m f := by
    refine ⟨p0.length, p0.getVert, ?_, ?_, ?_⟩
    · exact Nat.odd_iff.mp hp0
    · rw [p0.getVert_length, p0.getVert_zero]
    · intro i hi
      exact p0.adj_getVert_succ hi
  let m := Nat.find hex
  obtain ⟨f, hloop⟩ := Nat.find_spec hex
  have hmin : ∀ m' < m, ¬ ∃ f', OddLoop H m' f' := fun m' hm' => Nat.find_min hex hm'
  have hm3 : 3 ≤ m := oddLoop_three_le hloop
  have hinj : ∀ i < m, ∀ j < m, f i = f j → i = j := min_oddLoop_inj hloop hmin
  have hchord : ∀ i j, i < j → j < m → H.Adj (f i) (f j) → j = i + 1 ∨ (i = 0 ∧ j = m - 1) :=
    min_oddLoop_chord hloop hmin
  rcases hloop with ⟨hm_odd, hclose, hadj⟩
  change m % 2 = 1 at hm_odd
  change f m = f 0 at hclose
  change ∀ i < m, H.Adj (f i) (f (i + 1)) at hadj
  have hnext_eq : ∀ i < m, f ((i + 1) % m) = f (i + 1) := by
    intro i hi
    by_cases hi1 : i + 1 < m
    · rw [Nat.mod_eq_of_lt hi1]
    · have him : i + 1 = m := by omega
      rw [him, Nat.mod_self, hclose]
  let S : Set (Fin n) := {v | ∃ i < m, f i = v}
  let D : Fin n → Fin n → Prop := fun u v =>
    (∃ i < m, f i = u ∧ f ((i + 1) % m) = v) ∨
    (u ∉ S ∧ v ∈ S ∧ H.Adj u v) ∨
    (u ∉ S ∧ v ∉ S ∧ H.Adj u v ∧ u < v)
  have hG : ∀ u v, H.Adj u v ↔ (D u v ∨ D v u) := by
    intro u v
    constructor
    · intro huv
      by_cases hu : u ∈ S
      · by_cases hv : v ∈ S
        · rcases hu with ⟨i, hi, rfl⟩
          rcases hv with ⟨j, hj, rfl⟩
          have hij_ne : i ≠ j := fun h => H.irrefl (h ▸ huv)
          rcases lt_trichotomy i j with hij | rfl | hji
          · rcases hchord i j hij hj huv with rfl | ⟨rfl, rfl⟩
            · left
              left
              exact ⟨i, hi, rfl, by rw [Nat.mod_eq_of_lt hj]⟩
            · right
              left
              exact ⟨m - 1, by omega, rfl, by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]⟩
          · exact (hij_ne rfl).elim
          · rcases hchord j i hji hi huv.symm with rfl | ⟨rfl, rfl⟩
            · right
              left
              exact ⟨j, hj, rfl, by rw [Nat.mod_eq_of_lt hi]⟩
            · left
              left
              exact ⟨m - 1, by omega, rfl, by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]⟩
        · exact Or.inr (Or.inr (Or.inl ⟨hv, hu, huv.symm⟩))
      · by_cases hv : v ∈ S
        · exact Or.inl (Or.inr (Or.inl ⟨hu, hv, huv⟩))
        · have hne : u ≠ v := H.ne_of_adj huv
          rcases lt_trichotomy u v with hlt | rfl | hgt
          · exact Or.inl (Or.inr (Or.inr ⟨hu, hv, huv, hlt⟩))
          · exact (hne rfl).elim
          · exact Or.inr (Or.inr (Or.inr ⟨hv, hu, huv.symm, hgt⟩))
    · have hD_adj : ∀ a b, D a b → H.Adj a b := by
        intro a b hab
        rcases hab with ⟨i, hi, rfl, rfl⟩ | ⟨_, _, ha⟩ | ⟨_, _, ha, _⟩
        · rw [hnext_eq i hi]
          exact hadj i hi
        · exact ha
        · exact ha
      rintro (h | h)
      · exact hD_adj u v h
      · exact (hD_adj v u h).symm
  have hDasym : ∀ u v, D u v → ¬ D v u := by
    intro u v huv hvu
    have h1_in : ∀ a b, (∃ i < m, f i = a ∧ f ((i + 1) % m) = b) → a ∈ S ∧ b ∈ S := by
      rintro a b ⟨i, hi, rfl, rfl⟩
      exact ⟨⟨i, hi, rfl⟩, ⟨(i + 1) % m, Nat.mod_lt _ (by omega), rfl⟩⟩
    rcases huv with h1 | ⟨huS, hvS, _⟩ | ⟨huS, hvS, _, hlt⟩
    · have ⟨huS, hvS⟩ := h1_in u v h1
      rcases hvu with h2 | ⟨hvS', _⟩ | ⟨hvS', _⟩
      · rcases h1 with ⟨i, hi, rfl, hfi⟩
        rcases h2 with ⟨j, hj, hfj, hfj1⟩
        have hmod1 : (i + 1) % m < m := Nat.mod_lt _ (by omega)
        have hmod2 : (j + 1) % m < m := Nat.mod_lt _ (by omega)
        have hj_eq : (i + 1) % m = j := hinj _ hmod1 j hj (hfi.trans hfj.symm)
        have hi_eq : (j + 1) % m = i := hinj _ hmod2 i hi hfj1
        subst hj_eq
        by_cases hi1 : i + 1 < m
        · rw [Nat.mod_eq_of_lt hi1] at hi_eq
          by_cases hi2 : i + 1 + 1 < m
          · rw [Nat.mod_eq_of_lt hi2] at hi_eq
            omega
          · have : i + 1 + 1 = m := by omega
            rw [this, Nat.mod_self] at hi_eq
            omega
        · have : i + 1 = m := by omega
          rw [this, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hi_eq
          omega
      · exact hvS' hvS
      · exact hvS' hvS
    · rcases hvu with h2 | ⟨hvS', _⟩ | ⟨hvS', _⟩
      · exact huS (h1_in v u h2).2
      · exact hvS' hvS
      · exact hvS' hvS
    · rcases hvu with h2 | ⟨_, huS', _⟩ | ⟨_, _, _, hgt⟩
      · exact huS (h1_in v u h2).2
      · exact huS huS'
      · exact lt_asymm hlt hgt
  obtain ⟨K, hKind, hKabs⟩ := hker D hG hDasym
  have hstep : ∀ i < m, (f (i + 1) ∈ K ↔ f i ∉ K) := by
    intro i hi
    constructor
    · intro h1 h0
      exact hKind (f i) h0 (f (i + 1)) h1 (hadj i hi)
    · intro h0
      obtain ⟨k, hkK, hDk⟩ := hKabs (f i) h0
      have hfiS : f i ∈ S := ⟨i, hi, rfl⟩
      rcases hDk with ⟨j, hj, hfj, rfl⟩ | ⟨hnotS, _⟩ | ⟨hnotS, _⟩
      · have hji : i = j := hinj i hi j hj hfj.symm
        subst hji
        rwa [← hnext_eq i hi]
      · exact (hnotS hfiS).elim
      · exact (hnotS hfiS).elim
  have hparity : ∀ i ≤ m, (f i ∈ K ↔ (i % 2 = 0 ↔ f 0 ∈ K)) := by
    intro i
    induction i with
    | zero =>
      intro _
      simp
    | succ i ih =>
      intro hi
      rw [hstep i (by omega), ih (by omega)]
      by_cases h0 : f 0 ∈ K <;> simp [h0] <;> omega
  have hm_par := hparity m le_rfl
  rw [hclose] at hm_par
  by_cases h0 : f 0 ∈ K <;> simp [h0] at hm_par <;> omega

theorem backward (n : ℕ) (H : SimpleGraph (Fin n)) (hc : H.Colorable 2) :
    ∀ D : Fin n → Fin n → Prop,
      (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k := by
  classical
  obtain ⟨col⟩ := hc
  intro D hG _
  let X : Set (Fin n) := {v | col v = 0}
  let Y : Set (Fin n) := {v | col v ≠ 0}
  let cSet (A : Set (Fin n)) : Set (Fin n) := {y ∈ Y | ∀ x ∈ A, ¬ D y x}
  let aSet (C : Set (Fin n)) : Set (Fin n) := {x ∈ X | ∀ y ∈ C, ¬ D x y}
  let step (A : Set (Fin n)) : Set (Fin n) := aSet (cSet A)
  have hmono : Monotone step := by
    intro A1 A2 h12 x hx
    exact ⟨hx.1, fun y hy => hx.2 y ⟨hy.1, fun z hz => hy.2 z (h12 hz)⟩⟩
  let hom : Set (Fin n) →o Set (Fin n) := ⟨step, hmono⟩
  let A : Set (Fin n) := hom.lfp
  have hfp : aSet (cSet A) = A := hom.isFixedPt_lfp
  have hAX : ∀ x ∈ A, col x = 0 := by
    intro x hx
    rw [← hfp] at hx
    exact hx.1
  refine ⟨A ∪ cSet A, ?_, ?_⟩
  · intro u hu v hv hadj
    have hcol_ne : col u ≠ col v := col.valid hadj
    rcases hu with huA | huC <;> rcases hv with hvA | hvC
    · exact hcol_ne ((hAX u huA).trans (hAX v hvA).symm)
    · rcases (hG u v).mp hadj with hduv | hdvu
      · rw [← hfp] at huA
        exact huA.2 v hvC hduv
      · exact hvC.2 u huA hdvu
    · rcases (hG u v).mp hadj with hduv | hdvu
      · exact huC.2 v hvA hduv
      · rw [← hfp] at hvA
        exact hvA.2 u huC hdvu
    · have hu1 : col u ≠ 0 := huC.1
      have hv1 : col v ≠ 0 := hvC.1
      apply hcol_ne
      ext
      omega
  · intro v hv
    have hvA : v ∉ A := fun h => hv (Or.inl h)
    have hvC : v ∉ cSet A := fun h => hv (Or.inr h)
    by_cases hvX : col v = 0
    · rw [← hfp] at hvA
      have hnot : ¬ ∀ y ∈ cSet A, ¬ D v y := fun h => hvA ⟨hvX, h⟩
      push Not at hnot
      obtain ⟨y, hyC, hDvy⟩ := hnot
      exact ⟨y, Or.inr hyC, hDvy⟩
    · have hnot : ¬ ∀ x ∈ A, ¬ D v x := fun h => hvC ⟨hvX, h⟩
      push Not at hnot
      obtain ⟨x, hxA, hDvx⟩ := hnot
      exact ⟨x, Or.inl hxA, hDvx⟩

end PEqualNP.Outside.L_meta_730

theorem PEqualNP.Outside.L_meta_730 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
  (∀ D : Fin n → Fin n → Prop,
      (∀ u v, H.Adj u v ↔ (D u v ∨ D v u)) → (∀ u v, D u v → ¬ D v u) →
      ∃ K : Set (Fin n), (∀ u ∈ K, ∀ v ∈ K, ¬ H.Adj u v) ∧ ∀ v, v ∉ K → ∃ k ∈ K, D v k) ↔
  H.Colorable 2 := by
  intro n H
  exact ⟨PEqualNP.Outside.L_meta_730.forward n H, PEqualNP.Outside.L_meta_730.backward n H⟩
