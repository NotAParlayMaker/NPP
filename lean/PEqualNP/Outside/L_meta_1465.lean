import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1465_aux

/-- Seven relabelings of `Fin 7`; each turns the quadratic-residue tournament into another one. -/
def tbl : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 5, 4, 6], [0, 1, 2, 4, 3, 6, 5], [0, 1, 2, 5, 6, 4, 3],
   [0, 1, 2, 6, 3, 5, 4], [0, 1, 3, 2, 5, 6, 4], [0, 1, 2, 4, 5, 3, 6]]

def pm (k a : Fin 7) : ℕ := (tbl.getD k.val []).getD a.val 0

/-- `R k a b`: in tournament `k`, the point `a` beats the point `b`. -/
def R (k a b : Fin 7) : Bool := decide ((pm k b + 7 - pm k a) % 7 ∈ [1, 2, 4])

def Dom (k : Fin 7) (X : Finset (Fin 7)) : Prop := ∃ d, d ∉ X ∧ ∀ y ∈ X, R k d y = true

instance (k : Fin 7) (X : Finset (Fin 7)) : Decidable (Dom k X) := by
  unfold Dom; infer_instance

def A0 : Finset (Fin 7) := {0, 1, 3}
def B0 : Finset (Fin 7) := {0, 2, 6}

def Compat (X : Finset (Fin 7)) : Prop :=
  X = A0 ∨ X = B0 ∨ ((X ∩ A0).card = 1 ∧ (X ∩ B0).card = 1)

instance (X : Finset (Fin 7)) : Decidable (Compat X) := by
  unfold Compat; infer_instance

theorem asym : ∀ k a b : Fin 7, R k a b = true → R k b a = false := by decide +kernel

theorem small : ∀ k a b : Fin 7, ∃ d, d ≠ a ∧ d ≠ b ∧ R k d a = true ∧ R k d b = true := by
  decide +kernel

theorem one3 : ∀ X ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 7)), ∃ k, Dom k X := by
  decide +kernel

theorem two3 : ∀ X ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 7)), Compat X → ¬ Dom 0 X →
    ∀ Y ∈ Finset.powersetCard 3 (Finset.univ : Finset (Fin 7)), Compat Y →
      (Y = X ∨ (X ∩ Y).card = 1) → Dom 1 Y := by
  decide +kernel

theorem A0_card : A0.card = 3 := by decide
theorem B0_card : B0.card = 3 := by decide

theorem dom_small (k : Fin 7) (X : Finset (Fin 7)) (hX : X.card ≤ 2) : Dom k X := by
  have hab : ∃ a b : Fin 7, ∀ y ∈ X, y = a ∨ y = b := by
    have h3 : X.card = 0 ∨ X.card = 1 ∨ X.card = 2 := by omega
    rcases h3 with h | h | h
    · rw [Finset.card_eq_zero] at h
      exact ⟨0, 0, by rw [h]; simp⟩
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
      exact ⟨a, a, by rw [ha]; simp⟩
    · obtain ⟨a, b, -, ha⟩ := Finset.card_eq_two.mp h
      exact ⟨a, b, by rw [ha]; simp⟩
  obtain ⟨a, b, hab⟩ := hab
  obtain ⟨d, hda, hdb, ra, rb⟩ := small k a b
  refine ⟨d, ?_, ?_⟩
  · intro hd
    rcases hab d hd with e | e
    · exact hda e
    · exact hdb e
  · intro y hy
    rcases hab y hy with e | e
    · rw [e]; exact ra
    · rw [e]; exact rb

theorem coreII {m : ℕ} (T : Fin m → Finset (Fin 7)) (hle : ∀ i, (T i).card ≤ 3)
    (hno : ∀ i j, i ≠ j → (T i).card = 3 → (T j).card = 3 → False) :
    ∃ k, ∀ i, Dom k (T i) := by
  by_cases hx : ∃ i0, (T i0).card = 3
  · obtain ⟨i0, h0⟩ := hx
    obtain ⟨k, hk⟩ := one3 (T i0) (Finset.mem_powersetCard_univ.mpr h0)
    refine ⟨k, fun i => ?_⟩
    by_cases hi : i = i0
    · rw [hi]; exact hk
    · apply dom_small
      have h1 := hle i
      have h2 : (T i).card ≠ 3 := fun h => hno i i0 hi h h0
      omega
  · refine ⟨0, fun i => ?_⟩
    apply dom_small
    have h1 := hle i
    have h2 : (T i).card ≠ 3 := fun h => hx ⟨i, h⟩
    omega

theorem coreI {m : ℕ} (T : Fin m → Finset (Fin 7)) (hle : ∀ i, (T i).card ≤ 3)
    (hone : ∀ i j, i ≠ j → (T i).card = 3 → (T j).card = 3 → (T i ∩ T j).card = 1)
    (i0 j0 : Fin m) (hA : T i0 = A0) (hB : T j0 = B0) :
    ∃ k, ∀ i, Dom k (T i) := by
  have hA3 : (T i0).card = 3 := by rw [hA]; exact A0_card
  have hB3 : (T j0).card = 3 := by rw [hB]; exact B0_card
  have hc : ∀ i, (T i).card = 3 → Compat (T i) := by
    intro i h3
    by_cases hi : i = i0
    · left; rw [hi]; exact hA
    · by_cases hj : i = j0
      · right; left; rw [hj]; exact hB
      · right; right
        refine ⟨?_, ?_⟩
        · rw [← hA]; exact hone i i0 hi h3 hA3
        · rw [← hB]; exact hone i j0 hj h3 hB3
  have hs : ∀ (k : Fin 7) (i : Fin m), (T i).card ≠ 3 → Dom k (T i) := by
    intro k i h3
    apply dom_small
    have h1 := hle i
    omega
  by_cases hall : ∀ i, (T i).card = 3 → Dom 0 (T i)
  · refine ⟨0, fun i => ?_⟩
    by_cases h3 : (T i).card = 3
    · exact hall i h3
    · exact hs 0 i h3
  · have hex : ∃ x, (T x).card = 3 ∧ ¬ Dom 0 (T x) := by
      by_contra hcon
      apply hall
      intro i h3
      by_contra hd
      exact hcon ⟨i, h3, hd⟩
    obtain ⟨x, hx3, hxd⟩ := hex
    refine ⟨1, fun i => ?_⟩
    by_cases h3 : (T i).card = 3
    · refine two3 (T x) (Finset.mem_powersetCard_univ.mpr hx3) (hc x hx3) hxd (T i)
        (Finset.mem_powersetCard_univ.mpr h3) (hc i h3) ?_
      by_cases e : i = x
      · left; rw [e]
      · right; exact hone x i (fun h => e h.symm) hx3 h3
    · exact hs 1 i h3

/-- The trace of `S i` on `F`, read through the labeling `h`. -/
def T {n m : ℕ} (S : Fin m → Finset (Fin n)) (h : Fin 7 → Fin n) (i : Fin m) : Finset (Fin 7) :=
  Finset.univ.filter (fun u => h u ∈ S i)

theorem mem_T {n m : ℕ} (S : Fin m → Finset (Fin n)) (h : Fin 7 → Fin n) (i : Fin m) (u : Fin 7) :
    u ∈ T S h i ↔ h u ∈ S i := by
  simp [T]

theorem mem_F {n : ℕ} {F : Finset (Fin n)} {h : Fin 7 → Fin n}
    (himg : Finset.univ.image h = F) (u : Fin 7) : h u ∈ F := by
  rw [← himg]; exact Finset.mem_image_of_mem h (Finset.mem_univ u)

theorem img_T {n m : ℕ} (S : Fin m → Finset (Fin n)) (F : Finset (Fin n)) (h : Fin 7 → Fin n)
    (himg : Finset.univ.image h = F) (i : Fin m) : (T S h i).image h = S i ∩ F := by
  ext y
  rw [Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(mem_T S h i u).mp hu, mem_F himg u⟩
  · rintro ⟨hy, hyF⟩
    rw [← himg] at hyF
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hyF
    exact ⟨v, (mem_T S h i v).mpr hy, rfl⟩

theorem hypsT {n m : ℕ} (S : Fin m → Finset (Fin n)) (F : Finset (Fin n)) (h : Fin 7 → Fin n)
    (hinj : Function.Injective h) (himg : Finset.univ.image h = F)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hle : ∀ i : Fin m, (S i ∩ F).card ≤ 3)
    (hnon : ∀ i j : Fin m, i ≠ j → (S i ∩ F).card = 3 → (S j ∩ F).card = 3 →
      (S i ∩ S j ∩ F).Nonempty) :
    (∀ i, (T S h i).card ≤ 3) ∧
      (∀ i j, i ≠ j → (T S h i).card = 3 → (T S h j).card = 3 →
        (T S h i ∩ T S h j).card = 1) := by
  have hcard : ∀ i, (T S h i).card = (S i ∩ F).card := by
    intro i
    rw [← img_T S F h himg i, Finset.card_image_of_injective _ hinj]
  refine ⟨fun i => by rw [hcard i]; exact hle i, ?_⟩
  intro i j hij hi hj
  rw [hcard i] at hi
  rw [hcard j] at hj
  have h1 : (T S h i ∩ T S h j).card ≤ 1 := by
    refine le_trans ?_ (hpair i j hij)
    rw [← Finset.card_image_of_injective (T S h i ∩ T S h j) hinj]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_inter] at hu
    exact Finset.mem_inter.mpr ⟨(mem_T S h i u).mp hu.1, (mem_T S h j u).mp hu.2⟩
  have h2 : 1 ≤ (T S h i ∩ T S h j).card := by
    obtain ⟨y, hy⟩ := hnon i j hij hi hj
    rw [Finset.mem_inter, Finset.mem_inter] at hy
    obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
    rw [← himg] at hy3
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hy3
    exact Finset.card_pos.mpr
      ⟨v, Finset.mem_inter.mpr ⟨(mem_T S h i v).mpr hy1, (mem_T S h j v).mpr hy2⟩⟩
  omega

theorem transfer {n m : ℕ} (S : Fin m → Finset (Fin n)) (F : Finset (Fin n)) (h : Fin 7 → Fin n)
    (hinj : Function.Injective h) (himg : Finset.univ.image h = F)
    (hd : ∃ k, ∀ i, Dom k (T S h i)) :
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, f i ∈ F ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ F, r (f i) y := by
  obtain ⟨k, hd⟩ := hd
  choose d hd1 hd2 using hd
  refine ⟨fun a b => ∃ u v, h u = a ∧ h v = b ∧ R k u v = true, fun i => h (d i), ?_, ?_⟩
  · rintro a b ⟨u, v, rfl, rfl, huv⟩ ⟨u', v', hu', hv', huv'⟩
    rw [hinj hu', hinj hv', asym k u v huv] at huv'
    exact Bool.false_ne_true huv'
  · intro i
    refine ⟨mem_F himg (d i), ?_, ?_⟩
    · intro hc
      exact hd1 i ((mem_T S h i (d i)).mpr hc)
    · intro y hy
      rw [Finset.mem_inter] at hy
      obtain ⟨hyS, hyF⟩ := hy
      rw [← himg] at hyF
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hyF
      exact ⟨d i, v, rfl, rfl, hd2 i v ((mem_T S h i v).mpr hyS)⟩

theorem mkH {n : ℕ} (F P Q : Finset (Fin n)) (hF : F.card = 7) (hPF : P ⊆ F) (hQF : Q ⊆ F)
    (hP : P.card = 3) (hQ : Q.card = 3) (hPQ : (P ∩ Q).card = 1) :
    ∃ h : Fin 7 → Fin n, Function.Injective h ∧ Finset.univ.image h = F ∧
      (∀ u, h u ∈ P ↔ u ∈ A0) ∧ (∀ u, h u ∈ Q ↔ u ∈ B0) := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hPQ
  have hpPQ : p ∈ P ∩ Q := by rw [hp]; exact Finset.mem_singleton_self p
  have hpP : p ∈ P := (Finset.mem_inter.mp hpPQ).1
  have hpQ : p ∈ Q := (Finset.mem_inter.mp hpPQ).2
  obtain ⟨a, a', -, hPa⟩ := Finset.card_eq_two.mp
    (by rw [Finset.card_erase_of_mem hpP, hP] : (P.erase p).card = 2)
  obtain ⟨b, b', -, hQb⟩ := Finset.card_eq_two.mp
    (by rw [Finset.card_erase_of_mem hpQ, hQ] : (Q.erase p).card = 2)
  have hU : (P ∪ Q).card = 5 := by
    have := Finset.card_union_add_card_inter P Q
    omega
  have hR : (F \ (P ∪ Q)).card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.union_subset hPF hQF)]
    omega
  obtain ⟨c, c', -, hRc⟩ := Finset.card_eq_two.mp hR
  have hPe : P = {p, a, a'} := by rw [← hPa, Finset.insert_erase hpP]
  have hQe : Q = {p, b, b'} := by rw [← hQb, Finset.insert_erase hpQ]
  have hsplit : ∀ y, y ∈ F ↔ y ∈ P ∨ y ∈ Q ∨ y ∈ F \ (P ∪ Q) := by
    intro y
    constructor
    · intro hy
      by_cases h1 : y ∈ P
      · exact Or.inl h1
      · by_cases h2 : y ∈ Q
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr
            ⟨hy, fun hc => (Finset.mem_union.mp hc).elim h1 h2⟩))
    · rintro (h1 | h1 | h1)
      · exact hPF h1
      · exact hQF h1
      · exact (Finset.mem_sdiff.mp h1).1
  have hFe : ∀ y, y ∈ F ↔ (y = p ∨ y = a ∨ y = b ∨ y = a' ∨ y = c ∨ y = c' ∨ y = b') := by
    intro y
    rw [hsplit y, hRc, hPe, hQe]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  let h : Fin 7 → Fin n := ![p, a, b, a', c, c', b']
  have himg : Finset.univ.image h = F := by
    ext y
    rw [hFe y, Finset.mem_image]
    constructor
    · rintro ⟨u, -, rfl⟩
      fin_cases u
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    · rintro (e | e | e | e | e | e | e)
      · exact ⟨0, Finset.mem_univ _, e.symm⟩
      · exact ⟨1, Finset.mem_univ _, e.symm⟩
      · exact ⟨2, Finset.mem_univ _, e.symm⟩
      · exact ⟨3, Finset.mem_univ _, e.symm⟩
      · exact ⟨4, Finset.mem_univ _, e.symm⟩
      · exact ⟨5, Finset.mem_univ _, e.symm⟩
      · exact ⟨6, Finset.mem_univ _, e.symm⟩
  have hinj : Function.Injective h := by
    have hc : (Finset.univ.image h).card = (Finset.univ : Finset (Fin 7)).card := by
      rw [himg, hF]; rfl
    have hio := Finset.card_image_iff.mp hc
    intro x y hxy
    exact hio (Finset.mem_coe.mpr (Finset.mem_univ x)) (Finset.mem_coe.mpr (Finset.mem_univ y)) hxy
  refine ⟨h, hinj, himg, ?_, ?_⟩
  · intro u
    rw [hPe]
    simp only [A0, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (e | e | e)
      · exact Or.inl (hinj (a₂ := 0) e)
      · exact Or.inr (Or.inl (hinj (a₂ := 1) e))
      · exact Or.inr (Or.inr (hinj (a₂ := 3) e))
    · rintro (e | e | e)
      · rw [e]; exact Or.inl rfl
      · rw [e]; exact Or.inr (Or.inl rfl)
      · rw [e]; exact Or.inr (Or.inr rfl)
  · intro u
    rw [hQe]
    simp only [B0, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (e | e | e)
      · exact Or.inl (hinj (a₂ := 0) e)
      · exact Or.inr (Or.inl (hinj (a₂ := 2) e))
      · exact Or.inr (Or.inr (hinj (a₂ := 6) e))
    · rintro (e | e | e)
      · rw [e]; exact Or.inl rfl
      · rw [e]; exact Or.inr (Or.inl rfl)
      · rw [e]; exact Or.inr (Or.inr rfl)

end PEqualNP.Outside.L_meta_1465_aux

open PEqualNP.Outside.L_meta_1465_aux in
theorem PEqualNP.Outside.L_meta_1465 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (F : Finset (Fin n)),
    F.card = 7 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    (∀ i : Fin m, (S i ∩ F).card ≤ 3) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ F).card = 3 → (S j ∩ F).card = 3 → (S i ∩ S j ∩ F).Nonempty) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, f i ∈ F ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ F, r (f i) y := by
  intro n m S F hF hpair hle hnon
  by_cases hI : ∃ i j : Fin m, i ≠ j ∧ (S i ∩ F).card = 3 ∧ (S j ∩ F).card = 3
  · obtain ⟨i, j, hij, hi, hj⟩ := hI
    have hPQ : ((S i ∩ F) ∩ (S j ∩ F)).card = 1 := by
      have h1 : ((S i ∩ F) ∩ (S j ∩ F)).card ≤ 1 := by
        refine le_trans (Finset.card_le_card ?_) (hpair i j hij)
        intro y hy
        simp only [Finset.mem_inter] at hy ⊢
        exact ⟨hy.1.1, hy.2.1⟩
      have h2 : 1 ≤ ((S i ∩ F) ∩ (S j ∩ F)).card := by
        obtain ⟨y, hy⟩ := hnon i j hij hi hj
        refine Finset.card_pos.mpr ⟨y, ?_⟩
        simp only [Finset.mem_inter] at hy ⊢
        exact ⟨⟨hy.1.1, hy.2⟩, ⟨hy.1.2, hy.2⟩⟩
      omega
    obtain ⟨h, hinj, himg, hA, hB⟩ := mkH F (S i ∩ F) (S j ∩ F) hF
      Finset.inter_subset_right Finset.inter_subset_right hi hj hPQ
    obtain ⟨hle', hone'⟩ := hypsT S F h hinj himg hpair hle hnon
    have hTA : T S h i = A0 := by
      ext u
      rw [mem_T, ← hA u, Finset.mem_inter]
      exact ⟨fun hu => ⟨hu, mem_F himg u⟩, fun hu => hu.1⟩
    have hTB : T S h j = B0 := by
      ext u
      rw [mem_T, ← hB u, Finset.mem_inter]
      exact ⟨fun hu => ⟨hu, mem_F himg u⟩, fun hu => hu.1⟩
    exact transfer S F h hinj himg (coreI (T S h) hle' hone' i j hTA hTB)
  · let e := Finset.equivFinOfCardEq hF
    let h : Fin 7 → Fin n := fun u => (e.symm u).val
    have hinj : Function.Injective h := Subtype.val_injective.comp e.symm.injective
    have himg : Finset.univ.image h = F := by
      ext y
      rw [Finset.mem_image]
      constructor
      · rintro ⟨u, -, rfl⟩
        exact (e.symm u).property
      · intro hy
        exact ⟨e ⟨y, hy⟩, Finset.mem_univ _, by simp [h]⟩
    obtain ⟨hle', hone'⟩ := hypsT S F h hinj himg hpair hle hnon
    have hcard : ∀ i, (T S h i).card = (S i ∩ F).card := by
      intro i
      rw [← img_T S F h himg i, Finset.card_image_of_injective _ hinj]
    refine transfer S F h hinj himg (coreII (T S h) hle' ?_)
    intro i j hij hi hj
    exact hI ⟨i, j, hij, by rw [← hcard i]; exact hi, by rw [← hcard j]; exact hj⟩
