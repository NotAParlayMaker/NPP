import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Relation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_158

open PEqualNP.ProofComplexity

abbrev V := Fin 5 × Fin 4
abbrev Cl := Clause V
abbrev Formula := PHP 5 4

def reader {n : ℕ} (ax : Fin n → Prop) (p : Fin n → Bool → Fin n) (i j : Fin n) : Prop :=
  ¬ ax i ∧ ∃ b, p i b = j

abbrev Reach {n : ℕ} (ax : Fin n → Prop) (p : Fin n → Bool → Fin n) :=
  Relation.ReflTransGen (reader ax p)

lemma reach_le {n : ℕ} {ax : Fin n → Prop} {p : Fin n → Bool → Fin n}
    (ord : ∀ i, ¬ ax i → ∀ b, i < p i b) {i j : Fin n} (h : Reach ax p i j) : i ≤ j := by
  induction h with
  | refl => exact le_rfl
  | tail _ hr ih =>
    obtain ⟨ha, b, rfl⟩ := hr
    exact ih.trans (le_of_lt (ord _ ha b))

lemma parentSlot {n : ℕ} {ax : Fin n → Prop} {p : Fin n → Bool → Fin n}
    (ord : ∀ i, ¬ ax i → ∀ b, i < p i b) {r j : Fin n} (hr : ¬ ax r) (b : Bool)
    (h : Reach ax p (p r b) j) :
    ∃ (i : Fin n) (s : Bool), ¬ ax i ∧ p i s = j ∧ Reach ax p r i ∧
      (i = r → s = b) ∧ (i ≠ r → Reach ax p (p r b) i) := by
  rcases h.cases_tail with hj | ⟨i, hi, ha, s, he⟩
  · exact ⟨r, b, hr, hj.symm, .refl, fun _ => rfl, fun hn => (hn rfl).elim⟩
  · have hri := lt_of_lt_of_le (ord r hr b) (reach_le ord hi)
    exact ⟨i, s, ha, he, hi.head ⟨hr, b, rfl⟩, fun z => (hri.ne z.symm).elim, fun _ => hi⟩

lemma size_bounds {n : ℕ} (ax : Fin n → Prop) (p : Fin n → Bool → Fin n)
    (ord : ∀ i, ¬ ax i → ∀ b, i < p i b) (r : Fin n) (hr : ¬ ax r)
    (live : Finset (Fin n)) (hLive : ∀ i, i ∈ live ↔ Reach ax p r i ∧ ax i) :
    2 * live.card ≤ n + 1 ∧
      ((∃ x, Reach ax p (p r false) x ∧ Reach ax p (p r true) x) → 2 * live.card ≤ n) := by
  classical
  let S := Finset.univ.filter fun i => Reach ax p r i
  let A := S.filter ax
  let D := S.filter fun i => ¬ ax i
  let slots := D ×ˢ (Finset.univ : Finset Bool)
  let dest : Fin n × Bool → Fin n := fun t => p t.1 t.2
  have slotsCard : slots.card = D.card * 2 := by simp [slots, Finset.card_product]
  have split : A.card + D.card = S.card := S.card_filter_add_card_filter_not ax
  have hrS : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
  have huniv : S.card ≤ n := by
    simpa using (Finset.card_le_card (Finset.subset_univ S))
  have coverage : S.erase r ⊆ slots.image dest := by
    intro j hj
    obtain ⟨hne, hs⟩ := Finset.mem_erase.mp hj
    rcases (Finset.mem_filter.mp hs).2.cases_tail with z | ⟨i, hi, ha, b, he⟩
    · exact (hne z).elim
    refine Finset.mem_image.mpr ⟨(i, b), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, he⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ha⟩
  have coverCount := Finset.card_le_card coverage
  have eraseCount := Finset.card_erase_add_one hrS
  have hA : A = live := by
    ext i
    simp [hLive, A, S]
  rw [← hA]
  refine ⟨?_, ?_⟩
  · have hle : (slots.image dest).card ≤ slots.card := Finset.card_image_le
    omega
  intro shared
  let meet := Finset.univ.filter fun i => Reach ax p (p r false) i ∧ Reach ax p (p r true) i
  have hMeet : meet.Nonempty := by
    obtain ⟨i, hl, hh⟩ := shared
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl, hh⟩⟩
  let j := meet.min' hMeet
  have hj := (Finset.mem_filter.mp (Finset.min'_mem meet hMeet)).2
  obtain ⟨a, s, haa, he, hra, har, has⟩ := parentSlot ord hr false hj.1
  obtain ⟨b, t, hab, hje, hrb, hbr, hbt⟩ := parentSlot ord hr true hj.2
  have distinct : (a, s) ≠ (b, t) := by
    intro h
    have hab' := congrArg Prod.fst h
    have hst := congrArg Prod.snd h
    change a = b at hab'
    change s = t at hst
    subst b
    by_cases hroot : a = r
    · rw [har hroot, hbr hroot] at hst
      cases hst
    · have haMeet : a ∈ meet :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, has hroot, hbt hroot⟩
      have hmin : j ≤ a := Finset.min'_le meet a haMeet
      exact (not_lt_of_ge hmin) (by simpa only [he] using ord a haa s)
  have haSlot : (a, s) ∈ slots := Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hra⟩, haa⟩, Finset.mem_univ _⟩
  have hbSlot : (b, t) ∈ slots := Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrb⟩, hab⟩, Finset.mem_univ _⟩
  have lost : (slots.image dest).card < slots.card := by
    apply lt_of_le_of_ne Finset.card_image_le
    intro heq
    apply distinct
    exact (Finset.card_image_iff.mp heq) haSlot hbSlot (he.trans hje.symm)
  omega

lemma indexedStep (π : List Cl) (d : IsDerivation Formula π) (i : Fin π.length) :
    π.get i ∈ Formula ∨ ∃ a b : Fin π.length, i < a ∧ i < b ∧
      IsResolvent (π.get a) (π.get b) (π.get i) := by
  induction d with
  | nil => exact Fin.elim0 i
  | @ax π C d hC ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl hC
    · rcases ih j with h | ⟨a, b, ha, hb, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨a.succ, b.succ, Fin.succ_lt_succ_iff.mpr ha, Fin.succ_lt_succ_iff.mpr hb, h⟩
  | @res π C D R d hC hD hres ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · obtain ⟨a, ha, he⟩ := List.mem_iff_getElem.mp hC
      obtain ⟨b, hb, hf⟩ := List.mem_iff_getElem.mp hD
      refine Or.inr ⟨(⟨a, ha⟩ : Fin π.length).succ, (⟨b, hb⟩ : Fin π.length).succ,
        Fin.succ_pos _, Fin.succ_pos _, ?_⟩
      change IsResolvent π[a] π[b] R
      rwa [he, hf]
    · rcases ih j with h | ⟨a, b, ha, hb, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨a.succ, b.succ, Fin.succ_lt_succ_iff.mpr ha, Fin.succ_lt_succ_iff.mpr hb, h⟩

lemma false_parent (a : V → Bool) {A B R : Cl} {v : V}
    (hR : R = A.erase (v, true) ∪ B.erase (v, false)) (h : ¬ ClauseSat a R) :
    (a v = false → ¬ ClauseSat a A) ∧ (a v = true → ¬ ClauseSat a B) := by
  constructor
  · intro av hs
    obtain ⟨l, hl, eq⟩ := hs
    by_cases hv : l = (v, true)
    · subst l; simp [av] at eq
    · exact h ⟨l, hR.symm ▸ Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hv, hl⟩)), eq⟩
  · intro av hs
    obtain ⟨l, hl, eq⟩ := hs
    by_cases hv : l = (v, false)
    · subst l; simp [av] at eq
    · exact h ⟨l, hR.symm ▸ Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mpr ⟨hv, hl⟩)), eq⟩

lemma false_leaf {n : ℕ} (c : Fin n → Cl) (ax : Fin n → Prop) (p : Fin n → Bool → Fin n)
    (ord : ∀ i, ¬ ax i → ∀ b, i < p i b)
    (step : ∀ i, ¬ ax i → IsResolvent (c (p i false)) (c (p i true)) (c i))
    (a : V → Bool) (i : Fin n) (h : ¬ ClauseSat a (c i)) :
    ∃ j, Reach ax p i j ∧ ax j ∧ ¬ ClauseSat a (c j) := by
  classical
  by_cases hi : ax i
  · exact ⟨i, .refl, hi, h⟩
  · obtain ⟨v, _, _, hR⟩ := step i hi
    have hh := false_parent a hR h
    have hp : ¬ ClauseSat a (c (p i (a v))) := by
      cases hv : a v with
      | false => exact hh.1 hv
      | true => exact hh.2 hv
    obtain ⟨j, hj, hax, hn⟩ := false_leaf c ax p ord step a (p i (a v)) hp
    exact ⟨j, hj.head ⟨hi, a v, rfl⟩, hax, hn⟩
termination_by n - i.val
decreasing_by have hh := ord i hi (a v); omega

def pigeon (i : Fin 5) : Cl := Finset.univ.image fun j : Fin 4 => ((i, j), true)

def collision (i k : Fin 5) (j : Fin 4) : Cl := {((i, j), false), ((k, j), false)}

def collisions : Finset (Fin 5 × Fin 5 × Fin 4) := Finset.univ.filter fun t => t.1 < t.2.1

def allAxioms : Finset Cl := Finset.univ.image pigeon ∪
  collisions.image fun t => collision t.1 t.2.1 t.2.2

lemma allAxioms_mem (C : Cl) : C ∈ allAxioms ↔ C ∈ Formula := by
  simp only [allAxioms, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    collisions, Finset.mem_filter, PHP, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨i, h⟩ | ⟨⟨i, k, j⟩, hk, h⟩)
    · exact Or.inl ⟨i, h.symm⟩
    · exact Or.inr ⟨i, k, j, ne_of_lt hk, h.symm⟩
  · rintro (⟨i, h⟩ | ⟨i, k, j, hne, h⟩)
    · exact Or.inl ⟨i, h.symm⟩
    · rcases lt_or_gt_of_ne hne with hk | hk
      · exact Or.inr ⟨(i, k, j), hk, h.symm⟩
      · exact Or.inr ⟨(k, i, j), hk, by rw [h]; simp [collision, Finset.pair_comm]⟩

def rank (p i k : Fin 5) : ℕ := p.val - (if i < p then 1 else 0) - (if k < p then 1 else 0)

def skipHole (j : Fin 4) (r : ℕ) : ℕ := if r < j.val then r else r + 1

def missingPlace (i k : Fin 5) (j : Fin 4) (p : Fin 5) : Option (Fin 4) :=
  if p = i then none else some (if p = k then j else Fin.ofNat 4 (skipHole j (rank p i k)))

def doublePlace (i k : Fin 5) (j : Fin 4) (p : Fin 5) : Fin 4 :=
  if p = i ∨ p = k then j else Fin.ofNat 4 (skipHole j (rank p i k))

def asAssignment (place : Fin 5 → Option (Fin 4)) (v : V) : Bool :=
  decide (place v.1 = some v.2)

abbrev missingAssignment (i k : Fin 5) (j : Fin 4) : V → Bool :=
  asAssignment (missingPlace i k j)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
lemma missing_injective : ∀ (i k : Fin 5) (j : Fin 4), i ≠ k →
    ∀ p q : Fin 5, p ≠ q → missingPlace i k j p ≠ missingPlace i k j q := by decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
lemma double_same : ∀ (i k : Fin 5) (j : Fin 4), i < k → ∀ p q : Fin 5, p < q →
    doublePlace i k j p = doublePlace i k j q → p = i ∧ q = k := by decide

lemma sat_pigeon (place : Fin 5 → Option (Fin 4)) (p : Fin 5) (h : Fin 4)
    (he : place p = some h) : ClauseSat (asAssignment place) (pigeon p) := by
  refine ⟨((p, h), true), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨h, Finset.mem_univ _, rfl⟩
  · simp [asAssignment, he]

lemma sat_collision (place : Fin 5 → Option (Fin 4)) (p q : Fin 5) (h : Fin 4)
    (hne : ¬ (place p = some h ∧ place q = some h)) :
    ClauseSat (asAssignment place) (collision p q h) := by
  by_cases hp : place p = some h
  · have hq : place q ≠ some h := fun he => hne ⟨hp, he⟩
    exact ⟨((q, h), false), by simp [collision], by simp [asAssignment, hq]⟩
  · exact ⟨((p, h), false), by simp [collision], by simp [asAssignment, hp]⟩

lemma missing_certificate (i k : Fin 5) (j : Fin 4) (hik : i ≠ k) :
    ∀ C ∈ allAxioms, C ≠ pigeon i → ClauseSat (missingAssignment i k j) C := by
  intro C hc hne
  rcases Finset.mem_union.mp hc with hp | hn
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hp
    have hpi : p ≠ i := fun h => hne (h ▸ rfl)
    exact sat_pigeon _ p (if p = k then j else Fin.ofNat 4 (skipHole j (rank p i k))) (by simp [missingPlace, hpi])
  · obtain ⟨⟨p, q, h⟩, hmem, rfl⟩ := Finset.mem_image.mp hn
    apply sat_collision
    rintro ⟨hp, hq⟩
    exact missing_injective i k j hik p q (ne_of_lt (Finset.mem_filter.mp hmem).2) (hp.trans hq.symm)

lemma collision_certificate (i k : Fin 5) (j : Fin 4) (hik : i < k) :
    ∀ C ∈ allAxioms, C ≠ collision i k j → ClauseSat (asAssignment fun p => some (doublePlace i k j p)) C := by
  intro C hc hne
  rcases Finset.mem_union.mp hc with hp | hn
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hp
    exact sat_pigeon _ p _ rfl
  · obtain ⟨⟨p, q, h⟩, hmem, rfl⟩ := Finset.mem_image.mp hn
    apply sat_collision
    rintro ⟨hp, hq⟩
    have hpeq : doublePlace i k j p = h := Option.some.inj hp
    have hqeq : doublePlace i k j q = h := Option.some.inj hq
    obtain ⟨rfl, rfl⟩ := double_same i k j hik p q (Finset.mem_filter.mp hmem).2 (hpeq.trans hqeq.symm)
    have hj : j = h := by simpa [doublePlace] using hpeq
    exact hne (hj ▸ rfl)

lemma pigeon_next : ∀ i : Fin 5, i + 1 ≠ i := by decide

lemma hole_next : ∀ j : Fin 4, j + 1 ≠ j := by decide

lemma unique_assignment (C : Cl) (hc : C ∈ allAxioms) :
    ∃ a : V → Bool, ∀ D ∈ allAxioms, D ≠ C → ClauseSat a D := by
  change C ∈ Finset.univ.image pigeon ∪ collisions.image _ at hc
  rcases Finset.mem_union.mp hc with h | h
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨missingAssignment i (i + 1) 0, missing_certificate i _ _ (pigeon_next i).symm⟩
  · obtain ⟨⟨i, k, j⟩, ht, rfl⟩ := Finset.mem_image.mp h
    exact ⟨_, collision_certificate i k j (Finset.mem_filter.mp ht).2⟩

lemma counted : allAxioms.card = 45 := by decide

lemma no_empty : (∅ : Cl) ∉ allAxioms := by decide

lemma makeParents (π : List Cl) (d : IsDerivation Formula π) :
    ∃ p : Fin π.length → Bool → Fin π.length,
      (∀ i, π.get i ∉ Formula → ∀ b, i < p i b) ∧
      (∀ i, π.get i ∉ Formula → IsResolvent (π.get (p i false)) (π.get (p i true)) (π.get i)) := by
  classical
  have h : ∀ i : Fin π.length, ∃ f : Bool → Fin π.length, π.get i ∉ Formula →
      (∀ b, i < f b) ∧ IsResolvent (π.get (f false)) (π.get (f true)) (π.get i) := by
    intro i
    rcases indexedStep π d i with h | ⟨a, b, ha, hb, hr⟩
    · exact ⟨fun _ => i, fun h' => (h' h).elim⟩
    · exact ⟨fun x => if x then b else a, fun _ => by
        refine ⟨?_, hr⟩
        intro x
        cases x
        · exact ha
        · exact hb⟩
  exact ⟨fun i => (h i).choose, fun i hi => ((h i).choose_spec hi).1,
    fun i hi => ((h i).choose_spec hi).2⟩

end PEqualNP.Outside.L_pcx_158

open PEqualNP.Outside.L_pcx_158 PEqualNP.ProofComplexity in
theorem PEqualNP.Outside.L_pcx_158 :
    ¬ (∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 89) := by
  rintro ⟨π, ⟨derivation, emptyLine⟩, short⟩
  classical
  obtain ⟨p, ord, step⟩ := makeParents π derivation
  obtain ⟨i, hi, hempty⟩ := List.mem_iff_getElem.mp emptyLine
  let c : Fin π.length → Cl := π.get
  let ax : Fin π.length → Prop := fun j => c j ∈ Formula
  let root : Fin π.length := ⟨i, hi⟩
  have hc : c root = ∅ := hempty
  have notAx : ¬ ax root := by
    intro hr
    exact no_empty (hc ▸ (allAxioms_mem _).mpr hr)
  let leaves := Finset.univ.filter fun j => Reach ax p root j ∧ ax j
  have getLeaf (a : V → Bool) (C : Cl)
      (ha : ∀ D ∈ allAxioms, D ≠ C → ClauseSat a D)
      (start : Fin π.length) (hs : Reach ax p root start) (hfalse : ¬ ClauseSat a (c start)) :
      ∃ j ∈ leaves, Reach ax p start j ∧ c j = C := by
    obtain ⟨j, hreach, hax, hn⟩ := false_leaf c ax p ord step a start hfalse
    have he : c j = C := by
      by_contra hne
      exact hn (ha _ ((allAxioms_mem _).mpr hax) hne)
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.trans hreach, hax⟩, hreach, he⟩
  have emptyFalse (a : V → Bool) : ¬ ClauseSat a (c root) := by simp [hc, ClauseSat]
  have hsub : allAxioms ⊆ leaves.image c := by
    intro C hC
    obtain ⟨a, ha⟩ := unique_assignment C hC
    obtain ⟨j, hj, _, he⟩ := getLeaf a C ha root .refl (emptyFalse a)
    exact Finset.mem_image.mpr ⟨j, hj, he⟩
  have cCover : 45 ≤ (leaves.image c).card := counted ▸ Finset.card_le_card hsub
  have imgBound : (leaves.image c).card ≤ leaves.card := Finset.card_image_le
  have bounds : 2 * leaves.card ≤ π.length + 1 ∧
      ((∃ x, Reach ax p (p root false) x ∧ Reach ax p (p root true) x) → 2 * leaves.card ≤ π.length) :=
    size_bounds ax p ord root notAx leaves (by intro j; simp [leaves])
  have inj : Set.InjOn c leaves := Finset.card_image_iff.mp (by have h := bounds.1; omega)
  obtain ⟨v, _, _, hR⟩ := step root notAx
  let omitted := v.1 + 1
  let C := pigeon omitted
  let a0 := missingAssignment omitted v.1 (v.2 + 1)
  let a1 := missingAssignment omitted v.1 v.2
  have hh : omitted ≠ v.1 := pigeon_next v.1
  have av0 : a0 v = false := by simp [a0, missingAssignment, asAssignment, missingPlace, hh.symm]
  have av1 : a1 v = true := by simp [a1, missingAssignment, asAssignment, missingPlace, hh.symm]
  have f0 := (false_parent a0 hR (emptyFalse a0)).1 av0
  have f1 := (false_parent a1 hR (emptyFalse a1)).2 av1
  have reach0 : Reach ax p root (p root false) := .single ⟨notAx, false, rfl⟩
  have reach1 : Reach ax p root (p root true) := .single ⟨notAx, true, rfl⟩
  obtain ⟨x, hx, hp0, he0⟩ := getLeaf a0 C (missing_certificate omitted v.1 _ hh) (p root false) reach0 f0
  obtain ⟨y, hy, hp1, he1⟩ := getLeaf a1 C (missing_certificate omitted v.1 _ hh) (p root true) reach1 f1
  have hxy : x = y := inj hx hy (he0.trans he1.symm)
  have impossible := bounds.2 ⟨x, hp0, hxy.symm ▸ hp1⟩
  omega
