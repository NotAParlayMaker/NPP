import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2615_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

local instance : DecidableEq GateOp := gateOpDecEq

/-! ## Part 1: PG(2, 3) incidence geometry on Fin 13 -/

def inc (p l : Fin 13) : Prop :=
  p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9

instance : DecidableRel inc := fun p l =>
  inferInstanceAs (Decidable (p - l = 0 ∨ p - l = 1 ∨ p - l = 3 ∨ p - l = 9))

lemma inc_no_C4 : ∀ p1 p2 l1 l2 : Fin 13,
    p1 ≠ p2 → l1 ≠ l2 → inc p1 l1 → inc p1 l2 → inc p2 l1 → ¬ inc p2 l2 := by
  decide

lemma inc_unique_line_aux : ∀ p1 p2 : Fin 13, p1 ≠ p2 →
    ∃ l : Fin 13, (inc p1 l ∧ inc p2 l) ∧ ∀ l' : Fin 13, inc p1 l' ∧ inc p2 l' → l' = l := by
  decide

lemma inc_unique_line (p1 p2 : Fin 13) (hne : p1 ≠ p2) : ∃! l : Fin 13, inc p1 l ∧ inc p2 l := by
  obtain ⟨l, h1, h2⟩ := inc_unique_line_aux p1 p2 hne
  exact ⟨l, h1, h2⟩

lemma inc_card_total :
    ((Finset.univ : Finset (Fin 13 × Fin 13)).filter (fun e => inc e.1 e.2)).card = 52 := by
  decide

lemma inc_deg_p : ∀ p : Fin 13, (Finset.univ.filter (fun l : Fin 13 => inc p l)).card = 4 := by
  decide

lemma inc_deg_l : ∀ l : Fin 13, (Finset.univ.filter (fun p : Fin 13 => inc p l)).card = 4 := by
  decide

def adj26 (u v : Fin 26) : Prop :=
  (∃ p l : Fin 13, inc p l ∧ u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨
  (∃ p l : Fin 13, inc p l ∧ u = Fin.natAdd 13 l ∧ v = Fin.castAdd 13 p)

instance : DecidableRel adj26 := fun u v => by
  unfold adj26; infer_instance

lemma adj26_no_C4 : ∀ u1 u2 v1 v2 : Fin 26,
    u1 ≠ u2 → v1 ≠ v2 → adj26 u1 v1 → adj26 u1 v2 → adj26 u2 v1 → ¬ adj26 u2 v2 := by
  intro u1 u2 v1 v2 hu hv h11 h12 h21 h22
  have hdisj : ∀ (p l : Fin 13), Fin.castAdd 13 p ≠ Fin.natAdd 13 l := fun p l h => by
    have := congrArg Fin.val h; simp at this; omega
  have hcastInj : ∀ {p q : Fin 13}, Fin.castAdd 13 p = Fin.castAdd 13 q → p = q := fun h =>
    Fin.ext (by have := congrArg Fin.val h; simpa using this)
  have hnatInj : ∀ {p q : Fin 13}, Fin.natAdd 13 p = Fin.natAdd 13 q → p = q := fun h =>
    Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
  rcases h11 with ⟨p1, l1, hi11, rfl, rfl⟩ | ⟨p1, l1, hi11, rfl, rfl⟩
  · rcases h12 with ⟨p1', l2, hi12, hp1, rfl⟩ | ⟨p', l', _, hbad, _⟩
    · have := hcastInj hp1; subst this
      rcases h21 with ⟨p2, l1', hi21, rfl, hl1⟩ | ⟨p', l', _, _, hbad⟩
      · have := hnatInj hl1; subst this
        rcases h22 with ⟨p2', l2', hi22, hp2, hl2⟩ | ⟨p', l', _, hbad, _⟩
        · have := hcastInj hp2; subst this
          have := hnatInj hl2; subst this
          exact inc_no_C4 p1 p2 l1 l2 (fun h => hu (by subst h; rfl)) (fun h => hv (by subst h; rfl)) hi11 hi12 hi21 hi22
        · exact hdisj p2 l' hbad
      · exact hdisj p' l1 hbad.symm
    · exact hdisj p1 l' hbad
  · rcases h12 with ⟨p', l', _, hbad, _⟩ | ⟨p2, l1', hi12, hl1, rfl⟩
    · exact hdisj p' l1 hbad.symm
    · have := hnatInj hl1; subst this
      rcases h21 with ⟨p', l', _, _, hbad⟩ | ⟨p1', l2, hi21, rfl, hp1⟩
      · exact hdisj p1 l' hbad
      · have := hcastInj hp1; subst this
        rcases h22 with ⟨p', l', _, hbad, _⟩ | ⟨p2', l2', hi22, hl2, hp2⟩
        · exact hdisj p' l2 hbad.symm
        · have := hnatInj hl2; subst this
          have := hcastInj hp2; subst this
          exact inc_no_C4 p1 p2 l1 l2 (fun h => hv (by subst h; rfl)) (fun h => hu (by subst h; rfl)) hi11 hi21 hi12 hi22

lemma adj26_deg : ∀ u : Fin 26, (Finset.univ.filter (fun v : Fin 26 => adj26 u v)).card = 4 := by
  intro u
  have hdisj : ∀ (p l : Fin 13), Fin.castAdd 13 p ≠ Fin.natAdd 13 l := fun p l h => by
    have := congrArg Fin.val h; simp at this; omega
  have hcastInj : Function.Injective (Fin.castAdd 13 : Fin 13 → Fin 26) := fun p q h =>
    Fin.ext (by have := congrArg Fin.val h; simpa using this)
  have hnatInj : Function.Injective (Fin.natAdd 13 : Fin 13 → Fin 26) := fun p q h =>
    Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
  by_cases hu : u.val < 13
  · set p : Fin 13 := ⟨u.val, hu⟩
    have hup : u = Fin.castAdd 13 p := Fin.ext rfl
    have heq : Finset.univ.filter (fun v : Fin 26 => adj26 u v) =
        (Finset.univ.filter (fun l : Fin 13 => inc p l)).image (Fin.natAdd 13) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        rw [hup] at h
        rcases h with ⟨p', l, hinc, hp, rfl⟩ | ⟨p', l, _, hbad, _⟩
        · have := hcastInj hp; subst this; exact ⟨l, hinc, rfl⟩
        · exact False.elim (hdisj p l hbad)
      · rintro ⟨l, hinc, rfl⟩
        rw [hup]; exact Or.inl ⟨p, l, hinc, rfl, rfl⟩
    rw [heq, Finset.card_image_of_injective _ hnatInj, inc_deg_p p]
  · set l : Fin 13 := ⟨u.val - 13, by omega⟩
    have hul : u = Fin.natAdd 13 l := Fin.ext (by simp [l]; omega)
    have heq : Finset.univ.filter (fun v : Fin 26 => adj26 u v) =
        (Finset.univ.filter (fun p : Fin 13 => inc p l)).image (Fin.castAdd 13) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro h
        rw [hul] at h
        rcases h with ⟨p, l', _, hbad, _⟩ | ⟨p, l', hinc, hl, rfl⟩
        · exact False.elim (hdisj p l hbad.symm)
        · have := hnatInj hl; subst this; exact ⟨p, hinc, rfl⟩
      · rintro ⟨p, hinc, rfl⟩
        rw [hul]; exact Or.inr ⟨p, l, hinc, rfl, rfl⟩
    rw [heq, Finset.card_image_of_injective _ hcastInj, inc_deg_l l]

lemma adj26_symm {u v : Fin 26} (h : adj26 u v) : adj26 v u := by
  rcases h with ⟨p, l, hinc, rfl, rfl⟩ | ⟨p, l, hinc, rfl, rfl⟩
  · exact Or.inr ⟨p, l, hinc, rfl, rfl⟩
  · exact Or.inl ⟨p, l, hinc, rfl, rfl⟩

lemma adj26_sides {u v : Fin 26} (h : adj26 u v) :
    (u.val < 13 ∧ 13 ≤ v.val) ∨ (13 ≤ u.val ∧ v.val < 13) := by
  rcases h with ⟨p, l, _, rfl, rfl⟩ | ⟨p, l, _, rfl, rfl⟩
  · left; exact ⟨p.isLt, by simp⟩
  · right; exact ⟨by simp, p.isLt⟩

def E26 : Finset (Fin 26 × Fin 26) :=
  ((Finset.univ : Finset (Fin 13 × Fin 13)).filter (fun e => inc e.1 e.2)).image
    (fun e => (Fin.castAdd 13 e.1, Fin.natAdd 13 e.2))

lemma E26_card : E26.card = 52 := by decide

/-- Every vertex cover of PG(2, 3) has size ≥ 13, and size = 13 iff all points or all lines. -/
lemma inc_vc_bound (TP TL : Finset (Fin 13))
    (hcov : ∀ p l : Fin 13, inc p l → p ∈ TP ∨ l ∈ TL) :
    13 ≤ TP.card + TL.card ∧
    (TP.card + TL.card = 13 → TP = Finset.univ ∨ TL = Finset.univ) := by
  set A := (Finset.univ : Finset (Fin 13)) \ TP
  set B := (Finset.univ : Finset (Fin 13)) \ TL
  have hAcard : TP.card + A.card = 13 := by
    have hD : Disjoint TP A := Finset.disjoint_sdiff
    have hU : TP ∪ A = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ TP)
    rw [← Finset.card_union_of_disjoint hD, hU, Finset.card_univ, Fintype.card_fin]
  have hBcard : TL.card + B.card = 13 := by
    have hD : Disjoint TL B := Finset.disjoint_sdiff
    have hU : TL ∪ B = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ TL)
    rw [← Finset.card_union_of_disjoint hD, hU, Finset.card_univ, Fintype.card_fin]
  by_cases hA0 : A.card = 0
  · have hTP : TP = Finset.univ := by
      have : TP.card = 13 := by omega
      exact Finset.eq_univ_of_card TP (by simpa using this)
    exact ⟨by omega, fun _ => Or.inl hTP⟩
  by_cases hB0 : B.card = 0
  · have hTL : TL = Finset.univ := by
      have : TL.card = 13 := by omega
      exact Finset.eq_univ_of_card TL (by simpa using this)
    exact ⟨by omega, fun _ => Or.inr hTL⟩
  -- Both A and B are nonempty; prove TP.card + TL.card ≥ 14!
  have hApos : 1 ≤ A.card := by omega
  have hBpos : 1 ≤ B.card := by omega
  have hNoAB : ∀ p ∈ A, ∀ l ∈ B, ¬ inc p l := by
    intro p hp l hl hinc
    rcases hcov p l hinc with h1 | h2
    · exact (Finset.mem_sdiff.mp hp).2 h1
    · exact (Finset.mem_sdiff.mp hl).2 h2
  -- Define d(l) = |{ p ∈ A | inc p l }| for l ∈ TL
  set d : Fin 13 → ℕ := fun l => (A.filter (fun p => inc p l)).card
  have hsum_d : ∑ l ∈ TL, d l = 4 * A.card := by
    have h1 : ∑ l ∈ TL, d l = ∑ p ∈ A, (TL.filter (fun l => inc p l)).card := by
      simp only [d, Finset.card_filter]
      rw [Finset.sum_comm]
    rw [h1]
    have h2 : ∀ p ∈ A, (TL.filter (fun l => inc p l)).card = 4 := by
      intro p hp
      have heq : TL.filter (fun l => inc p l) = Finset.univ.filter (fun l => inc p l) := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro hinc
          refine ⟨?_, hinc⟩
          by_contra hl
          exact hNoAB p hp l (Finset.mem_sdiff.mpr ⟨Finset.mem_univ l, hl⟩) hinc
      rw [heq, inc_deg_p p]
    rw [Finset.sum_congr rfl h2]
    simp [mul_comm]
  have hsum_pairs : ∑ l ∈ TL, d l * (d l - 1) = A.card * (A.card - 1) := by
    -- Count ordered pairs (p1, p2) in A × A with p1 ≠ p2 by their unique common line (which must lie in TL)
    set pairs := (A ×ˢ A).filter (fun pq => pq.1 ≠ pq.2)
    have hpairs_card : pairs.card = A.card * (A.card - 1) := by
      have h1 : pairs.card = ∑ p ∈ A, (A.erase p).card := by
        have hbi : pairs = A.biUnion (fun p => (A.erase p).image (fun q => (p, q))) := by
          ext ⟨p, q⟩
          simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
            Finset.mem_image, Finset.mem_erase, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨hp, hq⟩, hne⟩; exact ⟨p, hp, q, ⟨hne.symm, hq⟩, rfl, rfl⟩
          · rintro ⟨p', hp', q', ⟨hne, hq'⟩, rfl, rfl⟩; exact ⟨⟨hp', hq'⟩, hne.symm⟩
        rw [hbi, Finset.card_biUnion]
        · apply Finset.sum_congr rfl
          intro p _
          exact Finset.card_image_of_injective _ (fun _ _ h => ((Prod.mk.injEq ..).mp h).2)
        · intro p1 _ p2 _ hne
          show Disjoint _ _
          rw [Finset.disjoint_left]
          intro ⟨p, q⟩ h1 h2
          obtain ⟨_, _, he1⟩ := Finset.mem_image.mp h1
          obtain ⟨_, _, he2⟩ := Finset.mem_image.mp h2
          exact hne (((Prod.mk.injEq ..).mp he1).1.trans ((Prod.mk.injEq ..).mp he2).1.symm)
      rw [h1]
      have h2 : ∀ p ∈ A, (A.erase p).card = A.card - 1 := fun p hp => Finset.card_erase_of_mem hp
      rw [Finset.sum_congr rfl h2]
      simp [mul_comm]
    have hbi2 : pairs = TL.biUnion (fun l =>
        ((A.filter (fun p => inc p l)) ×ˢ (A.filter (fun p => inc p l))).filter (fun pq => pq.1 ≠ pq.2)) := by
      ext ⟨p, q⟩
      simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion]
      constructor
      · rintro ⟨⟨hp, hq⟩, hne⟩
        obtain ⟨l, ⟨hpl, hql⟩, _⟩ := inc_unique_line p q hne
        have hlTL : l ∈ TL := by
          by_contra hl
          exact hNoAB p hp l (Finset.mem_sdiff.mpr ⟨Finset.mem_univ l, hl⟩) hpl
        exact ⟨l, hlTL, ⟨⟨hp, hpl⟩, ⟨hq, hql⟩⟩, hne⟩
      · rintro ⟨l, _, ⟨⟨hp, _⟩, ⟨hq, _⟩⟩, hne⟩
        exact ⟨⟨hp, hq⟩, hne⟩
    have hcard_l : ∀ l : Fin 13,
        (((A.filter (fun p => inc p l)) ×ˢ (A.filter (fun p => inc p l))).filter (fun pq => pq.1 ≠ pq.2)).card =
        d l * (d l - 1) := by
      intro l
      set S := A.filter (fun p => inc p l)
      have h1 : ((S ×ˢ S).filter (fun pq => pq.1 ≠ pq.2)).card = ∑ p ∈ S, (S.erase p).card := by
        have hbi : (S ×ˢ S).filter (fun pq => pq.1 ≠ pq.2) =
            S.biUnion (fun p => (S.erase p).image (fun q => (p, q))) := by
          ext ⟨p, q⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
            Finset.mem_image, Finset.mem_erase, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨hp, hq⟩, hne⟩; exact ⟨p, hp, q, ⟨hne.symm, hq⟩, rfl, rfl⟩
          · rintro ⟨p', hp', q', ⟨hne, hq'⟩, rfl, rfl⟩; exact ⟨⟨hp', hq'⟩, hne.symm⟩
        rw [hbi, Finset.card_biUnion]
        · apply Finset.sum_congr rfl
          intro p _
          exact Finset.card_image_of_injective _ (fun _ _ h => ((Prod.mk.injEq ..).mp h).2)
        · intro p1 _ p2 _ hne
          show Disjoint _ _
          rw [Finset.disjoint_left]
          intro ⟨p, q⟩ h1 h2
          obtain ⟨_, _, he1⟩ := Finset.mem_image.mp h1
          obtain ⟨_, _, he2⟩ := Finset.mem_image.mp h2
          exact hne (((Prod.mk.injEq ..).mp he1).1.trans ((Prod.mk.injEq ..).mp he2).1.symm)
      rw [h1]
      have h2 : ∀ p ∈ S, (S.erase p).card = S.card - 1 := fun p hp => Finset.card_erase_of_mem hp
      rw [Finset.sum_congr rfl h2]
      simp [d, S, mul_comm]
    rw [← hpairs_card, hbi2, Finset.card_biUnion]
    · exact (Finset.sum_congr rfl (fun l _ => hcard_l l)).symm
    · intro l1 _ l2 _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro ⟨p, q⟩ h1 h2
      simp only [Finset.mem_filter, Finset.mem_product] at h1 h2
      obtain ⟨l, _, huniq⟩ := inc_unique_line p q h1.2
      exact hne ((huniq l1 ⟨h1.1.1.2, h1.1.2.2⟩).trans (huniq l2 ⟨h2.1.1.2, h2.1.2.2⟩).symm)
  have hsum_sq : ∑ l ∈ TL, d l * d l = A.card * A.card + 3 * A.card := by
    have h1 : ∑ l ∈ TL, d l * d l = (∑ l ∈ TL, d l * (d l - 1)) + ∑ l ∈ TL, d l := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l _
      cases hdl : d l
      · simp
      · simp [Nat.mul_succ]
    rw [h1, hsum_pairs, hsum_d]
    have hA1 : A.card * (A.card - 1) + A.card = A.card * A.card := by
      cases h : A.card
      · simp
      · simp [Nat.mul_succ]
    omega
  -- Cauchy-Schwarz in ℕ: (∑ d l)^2 ≤ TL.card * ∑ (d l)^2
  have hCS : (∑ l ∈ TL, d l) ^ 2 ≤ TL.card * ∑ l ∈ TL, d l ^ 2 := by
    have hnn : (0 : ℤ) ≤ ∑ l1 ∈ TL, ∑ l2 ∈ TL, ((d l1 : ℤ) - (d l2 : ℤ)) ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hexp : ∑ l1 ∈ TL, ∑ l2 ∈ TL, ((d l1 : ℤ) - (d l2 : ℤ)) ^ 2 =
        2 * ((TL.card : ℤ) * ∑ l ∈ TL, (d l : ℤ) ^ 2 - (∑ l ∈ TL, (d l : ℤ)) ^ 2) := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    have hZ : (∑ l ∈ TL, (d l : ℤ)) ^ 2 ≤ (TL.card : ℤ) * ∑ l ∈ TL, (d l : ℤ) ^ 2 := by linarith
    exact_mod_cast hZ
  have hsq_eq : ∑ l ∈ TL, d l ^ 2 = ∑ l ∈ TL, d l * d l := by
    apply Finset.sum_congr rfl; intro l _; ring
  rw [hsum_d, hsq_eq, hsum_sq] at hCS
  -- 16 * A.card^2 ≤ TL.card * (A.card^2 + 3 * A.card) -> 16 * A.card ≤ TL.card * (A.card + 3)
  have h16 : 16 * A.card ≤ TL.card * (A.card + 3) := by nlinarith
  have hgt13 : 14 ≤ TP.card + TL.card := by nlinarith
  exact ⟨by omega, fun h => by omega⟩

/-! ## Part 2: Circuit wire evaluation, cones, and orPart -/

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    set b := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hlen⟩ := ih (w ++ [b])
    refine ⟨b :: t, ?_, by simp [hlen]⟩
    change wiresFrom gs (w ++ [b]) = w ++ b :: t
    rw [ht, List.append_assoc]
    rfl

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hlen⟩ := wiresFrom_prefix gs w
  rw [ht, List.length_append, hlen]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wiresFrom_getD_gate (gs : List Gate) : ∀ (w : List Bool) (j : ℕ) (_hj : j < gs.length),
    (∀ u ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, u < w.length + j) →
    (wiresFrom gs w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval
        ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun u => (wiresFrom gs w).getD u false) := by
  induction gs with
  | nil => intro w j hj; simp at hj
  | cons g gs ih =>
    intro w j hj hrb
    set b := g.op.eval (g.inputs.map fun i => w.getD i false)
    cases j with
    | zero =>
      have h0 : (g :: gs).getD 0 ⟨GateOp.or, []⟩ = g := rfl
      rw [h0] at hrb ⊢
      have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [b]) := rfl
      rw [hstep, Nat.add_zero]
      have hlt : w.length < (w ++ [b]).length := by simp
      rw [wiresFrom_getD_lt gs (w ++ [b]) hlt]
      have hwb : (w ++ [b]).getD w.length false = b := by simp [List.getD_eq_getElem?_getD]
      rw [hwb]
      dsimp only [b]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu' : u < w.length := by simpa using hrb u hu
      have hu'' : u < (w ++ [b]).length := by simp; omega
      rw [wiresFrom_getD_lt gs (w ++ [b]) hu'']
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hu']
    | succ j' =>
      have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [b]) := rfl
      have hget : (g :: gs).getD (j' + 1) ⟨GateOp.or, []⟩ = gs.getD j' ⟨GateOp.or, []⟩ := rfl
      rw [hget] at hrb ⊢
      rw [hstep]
      have hj' : j' < gs.length := by simpa using hj
      have hlen : (w ++ [b]).length + j' = w.length + (j' + 1) := by simp; omega
      rw [← hlen]
      apply ih (w ++ [b]) j' hj'
      intro u hu
      rw [hlen]
      exact hrb u hu

def wval (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wval_lt (C : Circuit) (x : Fin 26 → Bool) {i : ℕ} (hi : i < 26) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have h : i < (List.ofFn x).length := by rw [List.length_ofFn]; exact hi
  rw [show C.gates.foldl _ (List.ofFn x) = wiresFrom C.gates (List.ofFn x) from rfl]
  rw [wiresFrom_getD_lt C.gates (List.ofFn x) h]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true, Option.getD_some]

lemma wval_ge (C : Circuit) (x : Fin 26 → Bool) {w : ℕ} (hw : 26 + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval Circuit.wires
  rw [show C.gates.foldl _ (List.ofFn x) = wiresFrom C.gates (List.ofFn x) from rfl]
  have hlen : (wiresFrom C.gates (List.ofFn x)).length = 26 + C.gates.length := by
    rw [wiresFrom_length, List.length_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : (wiresFrom C.gates (List.ofFn x)).length ≤ w)]
  rfl

lemma wval_gate (C : Circuit) (hAO : IsAO2 26 C) (x : Fin 26 → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (26 + j) =
      if (gateAt C j).op = GateOp.and then
        wval C x ((gateAt C j).inputs.getD 0 0) && wval C x ((gateAt C j).inputs.getD 1 0)
      else
        wval C x ((gateAt C j).inputs.getD 0 0) || wval C x ((gateAt C j).inputs.getD 1 0) := by
  have hrb := hAO.2.1
  have hlen2 : (gateAt C j).inputs.length = 2 := by
    apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    apply hAO.1; unfold gateAt; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  have hmain : wval C x (26 + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) := by
    unfold wval Circuit.wires
    rw [show C.gates.foldl _ (List.ofFn x) = wiresFrom C.gates (List.ofFn x) from rfl]
    have h1 := wiresFrom_getD_gate C.gates (List.ofFn x) j hj (by
      intro u hu; rw [List.length_ofFn]; exact hrb j hj u hu)
    simpa [List.length_ofFn, gateAt] using h1
  rw [hmain]
  rcases hlist : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hlist] at hlen2
  rcases hop with hop | hop <;> simp [hop, GateOp.eval]

lemma wval_mono (C : Circuit) (hAO : IsAO2 26 C) {x y : Fin 26 → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hx
    by_cases hlt : w < 26
    · rw [wval_lt C x hlt] at hx
      rw [wval_lt C y hlt]
      exact hxy ⟨w, hlt⟩ hx
    · by_cases hge : 26 + C.gates.length ≤ w
      · rw [wval_ge C x hge] at hx; cases hx
      · have hj : w - 26 < C.gates.length := by omega
        have hw : w = 26 + (w - 26) := by omega
        have hlen2 : (gateAt C (w - 26)).inputs.length = 2 := by
          apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
        have h0mem : (gateAt C (w - 26)).inputs.getD 0 0 ∈ (gateAt C (w - 26)).inputs := by
          rcases hlist : (gateAt C (w - 26)).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hlist] at hlen2 ⊢
        have h1mem : (gateAt C (w - 26)).inputs.getD 1 0 ∈ (gateAt C (w - 26)).inputs := by
          rcases hlist : (gateAt C (w - 26)).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hlist] at hlen2 ⊢
        have ha : (gateAt C (w - 26)).inputs.getD 0 0 < w := by
          have := hAO.2.1 (w - 26) hj _ h0mem; omega
        have hb : (gateAt C (w - 26)).inputs.getD 1 0 < w := by
          have := hAO.2.1 (w - 26) hj _ h1mem; omega
        rw [hw] at hx ⊢
        rw [wval_gate C hAO x hj] at hx
        rw [wval_gate C hAO y hj]
        split_ifs at hx ⊢
        · simp only [Bool.and_eq_true] at hx ⊢
          exact ⟨ih _ ha hx.1, ih _ hb hx.2⟩
        · simp only [Bool.or_eq_true] at hx ⊢
          exact hx.elim (fun h => Or.inl (ih _ ha h)) (fun h => Or.inr (ih _ hb h))

def ind1 (u : Fin 26) : Fin 26 → Bool := fun i => decide (i = u)
def ind2 (u v : Fin 26) : Fin 26 → Bool := fun i => decide (i = u ∨ i = v)

def orPart (C : Circuit) (w : ℕ) : Finset (Fin 26) :=
  Finset.univ.filter (fun i => wval C (ind1 i) w = true)

def cone (C : Circuit) (w : ℕ) : Finset ℕ :=
  if 26 ≤ w ∧ w - 26 < C.gates.length then
    insert w (((gateAt C (w - 26)).inputs.toFinset.filter (· < w)).attach.biUnion
      (fun u => cone C u.1))
  else {w}
termination_by w
decreasing_by exact (Finset.mem_filter.mp u.2).2

def orCone (C : Circuit) (w : ℕ) : Finset ℕ :=
  if 26 ≤ w ∧ w - 26 < C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.or then
    insert w (((gateAt C (w - 26)).inputs.toFinset.filter (· < w)).attach.biUnion
      (fun u => orCone C u.1))
  else {w}
termination_by w
decreasing_by exact (Finset.mem_filter.mp u.2).2

lemma mem_cone_self (C : Circuit) (w : ℕ) : w ∈ cone C w := by
  rw [cone]; split_ifs <;> simp

lemma mem_orCone_self (C : Circuit) (w : ℕ) : w ∈ orCone C w := by
  rw [orCone]; split_ifs <;> simp

lemma mem_cone_iff_gate (C : Circuit) (hrb : ReadsBack 26 C) {w : ℕ}
    (hw1 : 26 ≤ w) (hw2 : w - 26 < C.gates.length) (z : ℕ) :
    z ∈ cone C w ↔ z = w ∨ ∃ u ∈ (gateAt C (w - 26)).inputs, z ∈ cone C u := by
  rw [cone]
  simp only [hw1, hw2, and_self, ↓reduceIte, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_attach, true_and, Subtype.exists, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro (rfl | ⟨u, ⟨hu, _⟩, hz⟩); exact Or.inl rfl; exact Or.inr ⟨u, hu, hz⟩
  · rintro (rfl | ⟨u, hu, hz⟩)
    · exact Or.inl rfl
    · have hult : u < w := by have := hrb (w - 26) hw2 u hu; omega
      exact Or.inr ⟨u, ⟨hu, hult⟩, hz⟩

lemma mem_orCone_iff_or (C : Circuit) (hrb : ReadsBack 26 C) {w : ℕ}
    (hw1 : 26 ≤ w) (hw2 : w - 26 < C.gates.length) (hop : (gateAt C (w - 26)).op = GateOp.or) (z : ℕ) :
    z ∈ orCone C w ↔ z = w ∨ ∃ u ∈ (gateAt C (w - 26)).inputs, z ∈ orCone C u := by
  rw [orCone]
  simp only [hw1, hw2, hop, and_self, ↓reduceIte, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_attach, true_and, Subtype.exists, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro (rfl | ⟨u, ⟨hu, _⟩, hz⟩); exact Or.inl rfl; exact Or.inr ⟨u, hu, hz⟩
  · rintro (rfl | ⟨u, hu, hz⟩)
    · exact Or.inl rfl
    · have hult : u < w := by have := hrb (w - 26) hw2 u hu; omega
      exact Or.inr ⟨u, ⟨hu, hult⟩, hz⟩

lemma mem_orCone_iff_not_or (C : Circuit) {w : ℕ}
    (hw : ¬ (26 ≤ w ∧ w - 26 < C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.or)) (z : ℕ) :
    z ∈ orCone C w ↔ z = w := by
  rw [orCone]; simp [hw]

lemma mem_cone_le (C : Circuit) (hrb : ReadsBack 26 C) : ∀ w z, z ∈ cone C w → z ≤ w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro z hz
    by_cases hw : 26 ≤ w ∧ w - 26 < C.gates.length
    · rw [mem_cone_iff_gate C hrb hw.1 hw.2] at hz
      rcases hz with rfl | ⟨u, hu, hzu⟩
      · exact le_rfl
      · have hult : u < w := by have := hrb (w - 26) hw.2 u hu; omega
        exact le_trans (ih u hult z hzu) (le_of_lt hult)
    · rw [cone] at hz; simp only [hw, ↓reduceIte, Finset.mem_singleton] at hz; omega

lemma mem_orCone_le (C : Circuit) (hrb : ReadsBack 26 C) : ∀ w z, z ∈ orCone C w → z ≤ w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro z hz
    by_cases hw : 26 ≤ w ∧ w - 26 < C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.or
    · rw [mem_orCone_iff_or C hrb hw.1 hw.2.1 hw.2.2] at hz
      rcases hz with rfl | ⟨u, hu, hzu⟩
      · exact le_rfl
      · have hult : u < w := by have := hrb (w - 26) hw.2.1 u hu; omega
        exact le_trans (ih u hult z hzu) (le_of_lt hult)
    · rw [mem_orCone_iff_not_or C hw] at hz; omega

lemma orCone_subset_cone (C : Circuit) (hrb : ReadsBack 26 C) : ∀ w, orCone C w ⊆ cone C w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro z hz
    by_cases hw : 26 ≤ w ∧ w - 26 < C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.or
    · rw [mem_orCone_iff_or C hrb hw.1 hw.2.1 hw.2.2] at hz
      rw [mem_cone_iff_gate C hrb hw.1 hw.2.1]
      rcases hz with rfl | ⟨u, hu, hzu⟩
      · exact Or.inl rfl
      · have hult : u < w := by have := hrb (w - 26) hw.2.1 u hu; omega
        exact Or.inr ⟨u, hu, ih u hult hzu⟩
    · rw [mem_orCone_iff_not_or C hw] at hz
      subst hz; exact mem_cone_self C z

lemma cone_subset_of_mem (C : Circuit) (hrb : ReadsBack 26 C) :
    ∀ w u, u ∈ cone C w → cone C u ⊆ cone C w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro u hu
    by_cases hw : 26 ≤ w ∧ w - 26 < C.gates.length
    · rw [mem_cone_iff_gate C hrb hw.1 hw.2] at hu
      rcases hu with rfl | ⟨v, hv, huv⟩
      · exact Finset.Subset.refl _
      · have hvlt : v < w := by have := hrb (w - 26) hw.2 v hv; omega
        intro z hz
        rw [mem_cone_iff_gate C hrb hw.1 hw.2]
        exact Or.inr ⟨v, hv, ih v hvlt u huv hz⟩
    · rw [cone] at hu; simp only [hw, ↓reduceIte, Finset.mem_singleton] at hu
      subst hu; exact Finset.Subset.refl _

lemma orCone_subset_of_mem (C : Circuit) (hrb : ReadsBack 26 C) :
    ∀ w u, u ∈ orCone C w → orCone C u ⊆ orCone C w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro u hu
    by_cases hw : 26 ≤ w ∧ w - 26 < C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.or
    · rw [mem_orCone_iff_or C hrb hw.1 hw.2.1 hw.2.2] at hu
      rcases hu with rfl | ⟨v, hv, huv⟩
      · exact Finset.Subset.refl _
      · have hvlt : v < w := by have := hrb (w - 26) hw.2.1 v hv; omega
        intro z hz
        rw [mem_orCone_iff_or C hrb hw.1 hw.2.1 hw.2.2]
        exact Or.inr ⟨v, hv, ih v hvlt u huv hz⟩
    · rw [mem_orCone_iff_not_or C hw] at hu
      subst hu; exact Finset.Subset.refl _

lemma exists_reader_of_mem_cone (C : Circuit) (hrb : ReadsBack 26 C) :
    ∀ w z, z ∈ cone C w → z < w →
    ∃ g ∈ cone C w, 26 ≤ g ∧ g - 26 < C.gates.length ∧ z ∈ (gateAt C (g - 26)).inputs := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro z hz hzw
    by_cases hw : 26 ≤ w ∧ w - 26 < C.gates.length
    · rw [mem_cone_iff_gate C hrb hw.1 hw.2] at hz
      rcases hz with rfl | ⟨u, hu, hzu⟩
      · omega
      · by_cases hzu_eq : z = u
        · subst hzu_eq; exact ⟨w, mem_cone_self C w, hw.1, hw.2, hu⟩
        · have hule := mem_cone_le C hrb u z hzu
          have hzlt : z < u := lt_of_le_of_ne hule hzu_eq
          have hult : u < w := by have := hrb (w - 26) hw.2 u hu; omega
          obtain ⟨g, hgu, hg1, hg2, hgz⟩ := ih u hult z hzu hzlt
          refine ⟨g, ?_, hg1, hg2, hgz⟩
          have huC : u ∈ cone C w := by
            rw [mem_cone_iff_gate C hrb hw.1 hw.2]; exact Or.inr ⟨u, hu, mem_cone_self C u⟩
          exact cone_subset_of_mem C hrb w u huC hgu
    · rw [cone] at hz; simp only [hw, ↓reduceIte, Finset.mem_singleton] at hz; omega

lemma orPart_or_gate (C : Circuit) (hAO : IsAO2 26 C) {w : ℕ}
    (hw1 : 26 ≤ w) (hw2 : w - 26 < C.gates.length) (hop : (gateAt C (w - 26)).op = GateOp.or) :
    orPart C w = orPart C ((gateAt C (w - 26)).inputs.getD 0 0) ∪
                 orPart C ((gateAt C (w - 26)).inputs.getD 1 0) := by
  ext i
  simp only [orPart, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  have hweq : w = 26 + (w - 26) := by omega
  conv_lhs => rw [hweq, wval_gate C hAO (ind1 i) hw2]
  simp [hop]

lemma orPart_subset_of_mem_orCone (C : Circuit) (hAO : IsAO2 26 C) :
    ∀ w u, u ∈ orCone C w → orPart C u ⊆ orPart C w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro u hu
    by_cases hw : 26 ≤ w ∧ w - 26 < C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.or
    · rw [mem_orCone_iff_or C hAO.2.1 hw.1 hw.2.1 hw.2.2] at hu
      rcases hu with rfl | ⟨v, hv, huv⟩
      · exact Finset.Subset.refl _
      · have hvlt : v < w := by have := hAO.2.1 (w - 26) hw.2.1 v hv; omega
        have hlen2 : (gateAt C (w - 26)).inputs.length = 2 := by
          apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ hw.2.1]; exact List.getElem_mem hw.2.1
        have hlist : (gateAt C (w - 26)).inputs =
            [(gateAt C (w - 26)).inputs.getD 0 0, (gateAt C (w - 26)).inputs.getD 1 0] := by
          rcases hl : (gateAt C (w - 26)).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [hl] at hlen2 ⊢
        rw [orPart_or_gate C hAO hw.1 hw.2.1 hw.2.2]
        rw [hlist] at hv; simp at hv
        rcases hv with rfl | rfl
        · exact Finset.Subset.trans (ih _ hvlt u huv) Finset.subset_union_left
        · exact Finset.Subset.trans (ih _ hvlt u huv) Finset.subset_union_right
    · rw [mem_orCone_iff_not_or C hw] at hu
      subst hu; exact Finset.Subset.refl _

lemma orPart_card_le_one_of_not_or (C : Circuit) (hAO : IsAO2 26 C)
    (hAndEmpty : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → orPart C (26 + j) = ∅)
    {w : ℕ} (hw : ¬ (26 ≤ w ∧ w - 26 < C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.or)) :
    (orPart C w).card ≤ 1 := by
  by_cases hlt : w < 26
  · have hsub : orPart C w ⊆ {⟨w, hlt⟩} := by
      intro i hi
      simp only [orPart, Finset.mem_filter, Finset.mem_univ, true_and, wval_lt C _ hlt, ind1,
        decide_eq_true_eq] at hi
      simp [hi]
    exact le_trans (Finset.card_le_card hsub) (by simp)
  · by_cases hge : 26 + C.gates.length ≤ w
    · have hemp : orPart C w = ∅ := by
        ext i; simp [orPart, wval_ge C _ hge]
      rw [hemp]; simp
    · have hj : w - 26 < C.gates.length := by omega
      have hop : (gateAt C (w - 26)).op = GateOp.and := by
        have h1 : (gateAt C (w - 26)).op = GateOp.and ∨ (gateAt C (w - 26)).op = GateOp.or := by
          apply hAO.1; unfold gateAt; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
        rcases h1 with h | h
        · exact h
        · exfalso; exact hw ⟨by omega, hj, h⟩
      have heq : w = 26 + (w - 26) := by omega
      rw [heq, hAndEmpty (w - 26) hj hop]; simp

/-- Good OR gate: an OR gate with |orPart| ≥ 2 and BOTH operands having nonempty orPart. -/
def isGoodOr (C : Circuit) (w : ℕ) : Prop :=
  26 ≤ w ∧ w - 26 < C.gates.length ∧ (gateAt C (w - 26)).op = GateOp.or ∧
  2 ≤ (orPart C w).card ∧
  (orPart C ((gateAt C (w - 26)).inputs.getD 0 0)).Nonempty ∧
  (orPart C ((gateAt C (w - 26)).inputs.getD 1 0)).Nonempty

instance (C : Circuit) (w : ℕ) : Decidable (isGoodOr C w) := by
  unfold isGoodOr; infer_instance

/-- Leaf-Union Lemma: for any set of wires S, |⋃_{w ∈ S} orPart w| ≤ |S| + |{ g ∈ orCone(S) | isGoodOr g }|. -/
lemma leaf_union_bound (C : Circuit) (hAO : IsAO2 26 C)
    (hAndEmpty : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → orPart C (26 + j) = ∅) :
    ∀ k (S : Finset ℕ), (S.biUnion (orCone C)).card ≤ k →
      (S.biUnion (orPart C)).card ≤ S.card + ((S.biUnion (orCone C)).filter (isGoodOr C)).card := by
  intro k
  induction k with
  | zero =>
    intro S hk
    have hS0 : S = ∅ := by
      ext w; simp only [Finset.notMem_empty, iff_false]
      intro hw
      have hmem : w ∈ S.biUnion (orCone C) := Finset.mem_biUnion.mpr ⟨w, hw, mem_orCone_self C w⟩
      have hpos : 0 < (S.biUnion (orCone C)).card := Finset.card_pos.mpr ⟨w, hmem⟩
      omega
    subst hS0; simp
  | succ k ih =>
    intro S hk
    set U := S.biUnion (orCone C)
    set Big := U.filter (fun w => 2 ≤ (orPart C w).card)
    by_cases hBig : Big.Nonempty
    · set m := Big.max' hBig
      have hmBig := Finset.max'_mem Big hBig
      have hmU : m ∈ U := (Finset.mem_filter.mp hmBig).1
      have hmCard : 2 ≤ (orPart C m).card := (Finset.mem_filter.mp hmBig).2
      have hmOr : 26 ≤ m ∧ m - 26 < C.gates.length ∧ (gateAt C (m - 26)).op = GateOp.or := by
        by_contra hnot
        have := orPart_card_le_one_of_not_or C hAO hAndEmpty hnot
        omega
      -- Show m ∈ S
      have hmS : m ∈ S := by
        obtain ⟨s, hsS, hms⟩ := Finset.mem_biUnion.mp hmU
        have hsCard : 2 ≤ (orPart C s).card :=
          le_trans hmCard (Finset.card_le_card (orPart_subset_of_mem_orCone C hAO s m hms))
        have hsBig : s ∈ Big := Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨s, hsS, mem_orCone_self C s⟩, hsCard⟩
        have hsle : s ≤ m := Finset.le_max' Big s hsBig
        have hmle : m ≤ s := mem_orCone_le C hAO.2.1 s m hms
        have heq : m = s := le_antisymm hmle hsle
        rwa [heq]
      set a := (gateAt C (m - 26)).inputs.getD 0 0
      set b := (gateAt C (m - 26)).inputs.getD 1 0
      have hlen2 : (gateAt C (m - 26)).inputs.length = 2 := by
        apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ hmOr.2.1]; exact List.getElem_mem hmOr.2.1
      have hlist : (gateAt C (m - 26)).inputs = [a, b] := by
        rcases hl : (gateAt C (m - 26)).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp [hl] at hlen2
        simp [a, b, hl]
      have ha_lt : a < m := by have := hAO.2.1 (m - 26) hmOr.2.1 a (by rw [hlist]; simp); omega
      have hb_lt : b < m := by have := hAO.2.1 (m - 26) hmOr.2.1 b (by rw [hlist]; simp); omega
      have hm_orPart : orPart C m = orPart C a ∪ orPart C b :=
        orPart_or_gate C hAO hmOr.1 hmOr.2.1 hmOr.2.2
      -- Note: m cannot be in orCone C s for any s ∈ S.erase m!
      have hm_not_other : ∀ s ∈ S.erase m, m ∉ orCone C s := by
        intro s hs hms
        have hsm := Finset.mem_erase.mp hs
        have hsCard : 2 ≤ (orPart C s).card :=
          le_trans hmCard (Finset.card_le_card (orPart_subset_of_mem_orCone C hAO s m hms))
        have hsBig : s ∈ Big := Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨s, hsm.2, mem_orCone_self C s⟩, hsCard⟩
        have hsle : s ≤ m := Finset.le_max' Big s hsBig
        have hmle : m ≤ s := mem_orCone_le C hAO.2.1 s m hms
        exact hsm.1 (le_antisymm hsle hmle)
      have ha_sub_U : orCone C a ⊆ U := fun z hz => by
        have hzm : z ∈ orCone C m := by
          rw [mem_orCone_iff_or C hAO.2.1 hmOr.1 hmOr.2.1 hmOr.2.2]
          exact Or.inr ⟨a, by rw [hlist]; simp, hz⟩
        exact Finset.mem_biUnion.mpr ⟨m, hmS, hzm⟩
      have hb_sub_U : orCone C b ⊆ U := fun z hz => by
        have hzm : z ∈ orCone C m := by
          rw [mem_orCone_iff_or C hAO.2.1 hmOr.1 hmOr.2.1 hmOr.2.2]
          exact Or.inr ⟨b, by rw [hlist]; simp, hz⟩
        exact Finset.mem_biUnion.mpr ⟨m, hmS, hzm⟩
      by_cases haE : orPart C a = ∅
      · -- Replace m by b
        set S' := insert b (S.erase m)
        have hU'sub : S'.biUnion (orCone C) ⊆ U.erase m := by
          intro z hz
          obtain ⟨s, hsS', hzs⟩ := Finset.mem_biUnion.mp hz
          rw [Finset.mem_insert] at hsS'
          refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · rintro rfl
            rcases hsS' with rfl | hs
            · have := mem_orCone_le C hAO.2.1 b m hzs; omega
            · exact hm_not_other s hs hzs
          · rcases hsS' with rfl | hs
            · exact hb_sub_U hzs
            · exact Finset.mem_biUnion.mpr ⟨s, (Finset.mem_erase.mp hs).2, hzs⟩
        have hU'card : (S'.biUnion (orCone C)).card ≤ k := by
          have h1 := Finset.card_le_card hU'sub
          rw [Finset.card_erase_of_mem hmU] at h1
          omega
        have hPartEq : S.biUnion (orPart C) = S'.biUnion (orPart C) := by
          ext i
          simp only [S', Finset.mem_biUnion, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨s, hs, his⟩
            by_cases hsm : s = m
            · subst hsm
              rw [hm_orPart, haE, Finset.empty_union] at his
              exact ⟨b, Or.inl rfl, his⟩
            · exact ⟨s, Or.inr ⟨hsm, hs⟩, his⟩
          · rintro ⟨s, rfl | ⟨_, hs⟩, his⟩
            · exact ⟨m, hmS, by rw [hm_orPart, haE, Finset.empty_union]; exact his⟩
            · exact ⟨s, hs, his⟩
        have hS'card : S'.card ≤ S.card := by
          have h1 : S'.card ≤ (S.erase m).card + 1 := Finset.card_insert_le b (S.erase m)
          rw [Finset.card_erase_of_mem hmS] at h1
          have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨m, hmS⟩
          omega
        have hG'card : ((S'.biUnion (orCone C)).filter (isGoodOr C)).card ≤ (U.filter (isGoodOr C)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Subset.trans hU'sub (Finset.erase_subset m U)))
        rw [hPartEq]
        exact le_trans (ih S' hU'card) (Nat.add_le_add hS'card hG'card)
      · by_cases hbE : orPart C b = ∅
        · -- Replace m by a
          set S' := insert a (S.erase m)
          have hU'sub : S'.biUnion (orCone C) ⊆ U.erase m := by
            intro z hz
            obtain ⟨s, hsS', hzs⟩ := Finset.mem_biUnion.mp hz
            rw [Finset.mem_insert] at hsS'
            refine Finset.mem_erase.mpr ⟨?_, ?_⟩
            · rintro rfl
              rcases hsS' with rfl | hs
              · have := mem_orCone_le C hAO.2.1 a m hzs; omega
              · exact hm_not_other s hs hzs
            · rcases hsS' with rfl | hs
              · exact ha_sub_U hzs
              · exact Finset.mem_biUnion.mpr ⟨s, (Finset.mem_erase.mp hs).2, hzs⟩
          have hU'card : (S'.biUnion (orCone C)).card ≤ k := by
            have h1 := Finset.card_le_card hU'sub
            rw [Finset.card_erase_of_mem hmU] at h1
            omega
          have hPartEq : S.biUnion (orPart C) = S'.biUnion (orPart C) := by
            ext i
            simp only [S', Finset.mem_biUnion, Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨s, hs, his⟩
              by_cases hsm : s = m
              · subst hsm
                rw [hm_orPart, hbE, Finset.union_empty] at his
                exact ⟨a, Or.inl rfl, his⟩
              · exact ⟨s, Or.inr ⟨hsm, hs⟩, his⟩
            · rintro ⟨s, rfl | ⟨_, hs⟩, his⟩
              · exact ⟨m, hmS, by rw [hm_orPart, hbE, Finset.union_empty]; exact his⟩
              · exact ⟨s, hs, his⟩
          have hS'card : S'.card ≤ S.card := by
            have h1 : S'.card ≤ (S.erase m).card + 1 := Finset.card_insert_le a (S.erase m)
            rw [Finset.card_erase_of_mem hmS] at h1
            have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨m, hmS⟩
            omega
          have hG'card : ((S'.biUnion (orCone C)).filter (isGoodOr C)).card ≤ (U.filter (isGoodOr C)).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Subset.trans hU'sub (Finset.erase_subset m U)))
          rw [hPartEq]
          exact le_trans (ih S' hU'card) (Nat.add_le_add hS'card hG'card)
        · -- Both a and b have nonempty orPart -> m is a good OR gate! Replace m by {a, b}!
          have hmGood : isGoodOr C m :=
            ⟨hmOr.1, hmOr.2.1, hmOr.2.2, hmCard,
             Finset.nonempty_iff_ne_empty.mpr haE, Finset.nonempty_iff_ne_empty.mpr hbE⟩
          set S' := insert a (insert b (S.erase m))
          have hU'sub : S'.biUnion (orCone C) ⊆ U.erase m := by
            intro z hz
            obtain ⟨s, hsS', hzs⟩ := Finset.mem_biUnion.mp hz
            simp only [S', Finset.mem_insert] at hsS'
            refine Finset.mem_erase.mpr ⟨?_, ?_⟩
            · rintro rfl
              rcases hsS' with rfl | rfl | hs
              · have := mem_orCone_le C hAO.2.1 a m hzs; omega
              · have := mem_orCone_le C hAO.2.1 b m hzs; omega
              · exact hm_not_other s hs hzs
            · rcases hsS' with rfl | rfl | hs
              · exact ha_sub_U hzs
              · exact hb_sub_U hzs
              · exact Finset.mem_biUnion.mpr ⟨s, (Finset.mem_erase.mp hs).2, hzs⟩
          have hU'card : (S'.biUnion (orCone C)).card ≤ k := by
            have h1 := Finset.card_le_card hU'sub
            rw [Finset.card_erase_of_mem hmU] at h1
            omega
          have hPartEq : S.biUnion (orPart C) = S'.biUnion (orPart C) := by
            ext i
            simp only [S', Finset.mem_biUnion, Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨s, hs, his⟩
              by_cases hsm : s = m
              · subst hsm
                rw [hm_orPart, Finset.mem_union] at his
                rcases his with hia | hib
                · exact ⟨a, Or.inl rfl, hia⟩
                · exact ⟨b, Or.inr (Or.inl rfl), hib⟩
              · exact ⟨s, Or.inr (Or.inr ⟨hsm, hs⟩), his⟩
            · rintro ⟨s, rfl | rfl | ⟨_, hs⟩, his⟩
              · exact ⟨m, hmS, by rw [hm_orPart]; exact Finset.mem_union_left _ his⟩
              · exact ⟨m, hmS, by rw [hm_orPart]; exact Finset.mem_union_right _ his⟩
              · exact ⟨s, hs, his⟩
          have hS'card : S'.card ≤ S.card + 1 := by
            have h1 : S'.card ≤ (insert b (S.erase m)).card + 1 := Finset.card_insert_le a _
            have h2 : (insert b (S.erase m)).card ≤ (S.erase m).card + 1 := Finset.card_insert_le b _
            rw [Finset.card_erase_of_mem hmS] at h2
            have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨m, hmS⟩
            omega
          have hG'sub : (S'.biUnion (orCone C)).filter (isGoodOr C) ⊆ (U.filter (isGoodOr C)).erase m := by
            intro z hz
            have hzm := Finset.mem_filter.mp hz
            have hzU := Finset.mem_erase.mp (hU'sub hzm.1)
            exact Finset.mem_erase.mpr ⟨hzU.1, Finset.mem_filter.mpr ⟨hzU.2, hzm.2⟩⟩
          have hmInG : m ∈ U.filter (isGoodOr C) := Finset.mem_filter.mpr ⟨hmU, hmGood⟩
          have hG'card : ((S'.biUnion (orCone C)).filter (isGoodOr C)).card + 1 ≤ (U.filter (isGoodOr C)).card := by
            have h1 := Finset.card_le_card hG'sub
            rw [Finset.card_erase_of_mem hmInG] at h1
            have hpos : 1 ≤ (U.filter (isGoodOr C)).card := Finset.card_pos.mpr ⟨m, hmInG⟩
            omega
          rw [hPartEq]
          have hIH := ih S' hU'card
          omega
    · -- Big is empty: every s ∈ S has (orPart C s).card ≤ 1
      have hle1 : ∀ s ∈ S, (orPart C s).card ≤ 1 := by
        intro s hs
        by_contra hgt
        apply hBig
        exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨s, hs, mem_orCone_self C s⟩, by omega⟩⟩
      calc (S.biUnion (orPart C)).card
          ≤ ∑ s ∈ S, (orPart C s).card := Finset.card_biUnion_le
        _ ≤ ∑ _s ∈ S, 1 := Finset.sum_le_sum hle1
        _ = S.card := by simp
        _ ≤ S.card + (U.filter (isGoodOr C)).card := Nat.le_add_right _ _

/-! ## Part 3: Main theorem proof -/

theorem main_proof : ∀ (x1 : Circuit),
    x1.size ≤ 64 →
    IsAO2 26 x1 →
    (∀ (x4 : ℕ) (x5 : Gate), x1.gates[x4]? = some x5 → x5.inputs.Nodup) →
    (∀ (x7 : Fin 26 → Bool), wval x1 x7 x1.output = true ↔
      ∃ (x8 x9 : Fin 13), inc x8 x9 ∧ x7 (Fin.castAdd 13 x8) = true ∧ x7 (Fin.natAdd 13 x9) = true) →
    (∀ (x8 : ℕ), (gateAt x1 x8).op = GateOp.and → ∀ (x10 : Fin 26 → Bool),
      wval x1 x10 (26 + x8) = true → wval x1 x10 x1.output = true) →
    ∀ (x9 x10 : Fin 13), inc x9 x10 →
      let x12 : Fin 26 := Fin.castAdd 13 x9
      let x13 : Fin 26 := Fin.natAdd 13 x10
      ∀ (x16 x17 x18 x19 x20 x21 : ℕ),
        (x1.gates[x16]? = some ⟨GateOp.and, [x17, x18]⟩ ∧ wval x1 (ind2 x12 x13) (26 + x16) = true) →
        (x1.gates[x19]? = some ⟨GateOp.and, [x20, x21]⟩ ∧ wval x1 (ind2 x12 x13) (26 + x19) = true) →
        (wval x1 (ind1 x12) x17 || wval x1 (ind1 x12) x18) = true →
        ¬ (wval x1 (ind1 x13) x17 || wval x1 (ind1 x13) x18) = true →
        (wval x1 (ind1 x13) x20 || wval x1 (ind1 x13) x21) = true →
        (wval x1 (ind1 x12) x20 || wval x1 (ind1 x12) x21) = true := by
  intro C hSize hAO _hNodup hEval hBelow p0 l0 hInc0 P0 L0 j1 a1 b1 j2 a2 b2 hj1 hj2 h1P h1nL h2L
  by_contra h2nP
  have hrb := hAO.2.1
  -- Basic facts about f on ind1 and ind2
  have hf_ind1 : ∀ u : Fin 26, wval C (ind1 u) C.output = false := by
    intro u
    cases h : wval C (ind1 u) C.output
    · rfl
    · exfalso
      obtain ⟨p, l, _, hp, hl⟩ := (hEval (ind1 u)).mp h
      simp only [ind1, decide_eq_true_eq] at hp hl
      have := congrArg Fin.val (hp.trans hl.symm)
      simp at this; omega
  have hf_ind2_same : ∀ u v : Fin 26,
      ((u.val < 13 ∧ v.val < 13) ∨ (13 ≤ u.val ∧ 13 ≤ v.val)) →
      wval C (ind2 u v) C.output = false := by
    intro u v hsame
    cases h : wval C (ind2 u v) C.output
    · rfl
    · exfalso
      obtain ⟨p, l, _, hp, hl⟩ := (hEval (ind2 u v)).mp h
      simp only [ind2, decide_eq_true_eq] at hp hl
      rcases hp with hp | hp <;> rcases hl with hl | hl <;>
        (have h1 := congrArg Fin.val hp; have h2 := congrArg Fin.val hl; simp at h1 h2; omega)
  have hf_ind2_pl : ∀ p l : Fin 13,
      wval C (ind2 (Fin.castAdd 13 p) (Fin.natAdd 13 l)) C.output = true ↔ inc p l := by
    intro p l
    rw [hEval]
    constructor
    · rintro ⟨p', l', hI', hp', hl'⟩
      simp only [ind2, decide_eq_true_eq] at hp' hl'
      have hp_eq : p' = p := by
        rcases hp' with h1 | h1
        · exact Fin.ext (by simpa using congrArg Fin.val h1)
        · exfalso; have := congrArg Fin.val h1; simp at this; omega
      have hl_eq : l' = l := by
        rcases hl' with h1 | h1
        · exfalso; have := congrArg Fin.val h1; simp at this; omega
        · exact Fin.ext (by simpa using congrArg Fin.val h1)
      subst hp_eq; subst hl_eq; exact hI'
    · intro hI; exact ⟨p, l, hI, by simp [ind2], by simp [ind2]⟩
  -- Every AND gate has empty orPart
  have hAndEmpty : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → orPart C (26 + j) = ∅ := by
    intro j _ hop
    ext u
    simp only [orPart, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro hval
    have := hBelow j hop (ind1 u) hval
    rw [hf_ind1 u] at this; cases this
  -- C.output is a valid gate wire with empty orPart
  have hOutEmpty : orPart C C.output = ∅ := by
    ext u; simp [orPart, hf_ind1 u]
  have hOutGe : 26 ≤ C.output := by
    by_contra hlt
    have hmem : (⟨C.output, by omega⟩ : Fin 26) ∈ orPart C C.output := by
      simp [orPart, wval_lt C _ (by omega : C.output < 26), ind1]
    rw [hOutEmpty] at hmem; simp at hmem
  have hOutLt : C.output < 26 + C.gates.length := by
    by_contra hge
    have h1 := (hf_ind2_pl p0 l0).mpr hInc0
    rw [wval_ge C _ (by omega)] at h1; cases h1
  -- All gate wires: G = {26, ..., 26 + C.gates.length - 1}
  set allG : Finset ℕ := (Finset.range C.gates.length).image (fun j => 26 + j)
  have hallG_card : allG.card = C.gates.length := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  have hmem_allG : ∀ w, w ∈ allG ↔ 26 ≤ w ∧ w - 26 < C.gates.length := by
    intro w
    simp only [allG, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · rintro ⟨h1, h2⟩; exact ⟨w - 26, h2, by omega⟩
  -- Live wires in cone C C.output
  set coneOut := cone C C.output
  have hGateInAll : ∀ w ∈ coneOut, 26 ≤ w → w ∈ allG := by
    intro w hw h26
    have hle := mem_cone_le C hrb C.output w hw
    exact (hmem_allG w).mpr ⟨h26, by omega⟩
  set Wlive := coneOut.filter (fun w => orPart C w = ∅)
  have hWlive_ge : ∀ w ∈ Wlive, 26 ≤ w := by
    intro w hw
    by_contra hlt
    have hmem : (⟨w, by omega⟩ : Fin 26) ∈ orPart C w := by
      simp [orPart, wval_lt C _ (by omega : w < 26), ind1]
    rw [(Finset.mem_filter.mp hw).2] at hmem; simp at hmem
  have hWlive_sub : Wlive ⊆ allG := fun w hw =>
    hGateInAll w (Finset.mem_filter.mp hw).1 (hWlive_ge w hw)
  -- Split allG into: Alive_use, Alive_nonuse, A_dead, O0_live, O0_dead, O_good, O1_rest
  have hOpOfAll : ∀ w ∈ allG, (gateAt C (w - 26)).op = GateOp.and ∨ (gateAt C (w - 26)).op = GateOp.or := by
    intro w hw
    have h2 := ((hmem_allG w).mp hw).2
    apply hAO.1; unfold gateAt; rw [List.getD_eq_getElem _ _ h2]; exact List.getElem_mem h2
  have hLenOfAll : ∀ w ∈ allG, (gateAt C (w - 26)).inputs.length = 2 := by
    intro w hw
    have h2 := ((hmem_allG w).mp hw).2
    apply hAO.2.2; unfold gateAt; rw [List.getD_eq_getElem _ _ h2]; exact List.getElem_mem h2
  set Aall := allG.filter (fun w => (gateAt C (w - 26)).op = GateOp.and)
  set Oall := allG.filter (fun w => (gateAt C (w - 26)).op = GateOp.or)
  set Alive := Aall.filter (fun w => w ∈ coneOut)
  set O0live := Oall.filter (fun w => w ∈ coneOut ∧ orPart C w = ∅)
  set Ause := Alive.filter (fun w =>
    (orPart C ((gateAt C (w - 26)).inputs.getD 0 0)).Nonempty ∧
    (orPart C ((gateAt C (w - 26)).inputs.getD 1 0)).Nonempty)
  set Anon := Alive.filter (fun w => ¬ (
    (orPart C ((gateAt C (w - 26)).inputs.getD 0 0)).Nonempty ∧
    (orPart C ((gateAt C (w - 26)).inputs.getD 1 0)).Nonempty))
  set Ogood := Oall.filter (isGoodOr C)
  set O1mix := Oall.filter (fun w => w ∈ coneOut ∧ orPart C w ≠ ∅ ∧ ¬ isGoodOr C w)
  -- Helper: Wlive = Alive ∪ O0live (disjoint)
  have hWlive_eq : Wlive = Alive ∪ O0live := by
    ext w
    simp only [Wlive, Alive, O0live, Aall, Oall, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ⟨hwC, hwE⟩
      have hwG : w ∈ allG := hGateInAll w hwC (hWlive_ge w (Finset.mem_filter.mpr ⟨hwC, hwE⟩))
      rcases hOpOfAll w hwG with hop | hop
      · exact Or.inl ⟨⟨hwG, hop⟩, hwC⟩
      · exact Or.inr ⟨⟨hwG, hop⟩, hwC, hwE⟩
    · rintro (⟨⟨hwG, hop⟩, hwC⟩ | ⟨⟨hwG, _⟩, hwC, hwE⟩)
      · have hwP := (hmem_allG w).mp hwG
        have heq : w = 26 + (w - 26) := by omega
        exact ⟨hwC, by rw [heq]; exact hAndEmpty (w - 26) hwP.2 hop⟩
      · exact ⟨hwC, hwE⟩
  have hDisj_AO0 : Disjoint Alive O0live := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    have hop1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
    have hop2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2
    rw [hop1] at hop2; cases hop2
  have hWlive_card : Wlive.card = Alive.card + O0live.card := by
    rw [hWlive_eq, Finset.card_union_of_disjoint hDisj_AO0]
  -- Helper: Alive = Ause ∪ Anon (disjoint)
  have hAlive_card : Alive.card = Ause.card + Anon.card := by
    have hD : Disjoint Ause Anon := by
      rw [Finset.disjoint_left]; intro w h1 h2; exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hU : Ause ∪ Anon = Alive := by
      ext w; simp only [Ause, Anon, Finset.mem_union, Finset.mem_filter]; tauto
    rw [← hU, Finset.card_union_of_disjoint hD]
  -- 1. Every wire in Ause is a star in adj26
  have hStar : ∀ w ∈ Ause,
      let a := (gateAt C (w - 26)).inputs.getD 0 0
      let b := (gateAt C (w - 26)).inputs.getD 1 0
      (∀ u ∈ orPart C a, ∀ v ∈ orPart C b, adj26 u v) ∧
      ((orPart C a).card = 1 ∨ (orPart C b).card = 1) := by
    intro w hw a b
    have hwA := (Finset.mem_filter.mp hw).1
    have hwG := (Finset.mem_filter.mp (Finset.mem_filter.mp hwA).1).1
    have hwOp := (Finset.mem_filter.mp (Finset.mem_filter.mp hwA).1).2
    have hwP := (hmem_allG w).mp hwG
    have haNe : (orPart C a).Nonempty := (Finset.mem_filter.mp hw).2.1
    have hbNe : (orPart C b).Nonempty := (Finset.mem_filter.mp hw).2.2
    have hPair : ∀ u ∈ orPart C a, ∀ v ∈ orPart C b, adj26 u v := by
      intro u hu v hv
      have hua : wval C (ind1 u) a = true := (Finset.mem_filter.mp hu).2
      have hvb : wval C (ind1 v) b = true := (Finset.mem_filter.mp hv).2
      have hua2 : wval C (ind2 u v) a = true :=
        wval_mono C hAO (fun i hi => by simp [ind1] at hi; subst hi; simp [ind2]) a hua
      have hvb2 : wval C (ind2 u v) b = true :=
        wval_mono C hAO (fun i hi => by simp [ind1] at hi; subst hi; simp [ind2]) b hvb
      have hgw : wval C (ind2 u v) (26 + (w - 26)) = true := by
        rw [wval_gate C hAO (ind2 u v) hwP.2, if_pos hwOp]
        dsimp only [a, b] at hua2 hvb2
        rw [hua2, hvb2]; rfl
      have hout : wval C (ind2 u v) C.output = true := hBelow (w - 26) hwOp (ind2 u v) hgw
      obtain ⟨p, l, hinc, hp, hl⟩ := (hEval (ind2 u v)).mp hout
      simp only [ind2, decide_eq_true_eq] at hp hl
      rcases hp with hp | hp <;> rcases hl with hl | hl
      · exfalso
        have := congrArg Fin.val (hp.trans hl.symm); simp at this; omega
      · exact Or.inl ⟨p, l, hinc, hp.symm, hl.symm⟩
      · exact Or.inr ⟨p, l, hinc, hl.symm, hp.symm⟩
      · exfalso
        have := congrArg Fin.val (hp.trans hl.symm); simp at this; omega
    refine ⟨hPair, ?_⟩
    by_contra hboth
    push Not at hboth
    obtain ⟨u0, hu0⟩ := haNe
    obtain ⟨v0, hv0⟩ := hbNe
    have ha2 : 1 < (orPart C a).card := by have := Finset.card_pos.mpr ⟨u0, hu0⟩; omega
    have hb2 : 1 < (orPart C b).card := by have := Finset.card_pos.mpr ⟨v0, hv0⟩; omega
    obtain ⟨u1, hu1, hu1ne⟩ := Finset.exists_mem_ne ha2 u0
    obtain ⟨v1, hv1, hv1ne⟩ := Finset.exists_mem_ne hb2 v0
    exact adj26_no_C4 u0 u1 v0 v1 hu1ne.symm hv1ne.symm
      (hPair u0 hu0 v0 hv0) (hPair u0 hu0 v1 hv1) (hPair u1 hu1 v0 hv0) (hPair u1 hu1 v1 hv1)
  -- 2. Every edge (p, l) ∈ inc is covered by some w ∈ Ause (minimal active wire in coneOut)
  have hEdgeCov : ∀ p l : Fin 13, inc p l →
      ∃ w ∈ Ause,
        let a := (gateAt C (w - 26)).inputs.getD 0 0
        let b := (gateAt C (w - 26)).inputs.getD 1 0
        (Fin.castAdd 13 p ∈ orPart C a ∧ Fin.natAdd 13 l ∈ orPart C b) ∨
        (Fin.castAdd 13 p ∈ orPart C b ∧ Fin.natAdd 13 l ∈ orPart C a) := by
    intro p l hinc
    set P : Fin 26 := Fin.castAdd 13 p
    set L : Fin 26 := Fin.natAdd 13 l
    set S := coneOut.filter (fun w => wval C (ind2 P L) w = true ∧ wval C (ind1 P) w = false ∧ wval C (ind1 L) w = false)
    have hSne : S.Nonempty := ⟨C.output, Finset.mem_filter.mpr
      ⟨mem_cone_self C C.output, (hf_ind2_pl p l).mpr hinc, hf_ind1 P, hf_ind1 L⟩⟩
    set w := S.min' hSne
    have hwS := Finset.min'_mem S hSne
    have hwC : w ∈ coneOut := (Finset.mem_filter.mp hwS).1
    have hwT : wval C (ind2 P L) w = true := (Finset.mem_filter.mp hwS).2.1
    have hwP : wval C (ind1 P) w = false := (Finset.mem_filter.mp hwS).2.2.1
    have hwL : wval C (ind1 L) w = false := (Finset.mem_filter.mp hwS).2.2.2
    have hwGe : 26 ≤ w := by
      by_contra hlt
      rw [wval_lt C _ (by omega)] at hwT hwP hwL
      simp only [ind2, decide_eq_true_eq] at hwT
      rcases hwT with h1 | h1
      · simp [ind1, h1] at hwP
      · simp [ind1, h1] at hwL
    have hwG : w ∈ allG := hGateInAll w hwC hwGe
    have hwLen := (hmem_allG w).mp hwG
    set a := (gateAt C (w - 26)).inputs.getD 0 0
    set b := (gateAt C (w - 26)).inputs.getD 1 0
    have hlen2 := hLenOfAll w hwG
    have hlist : (gateAt C (w - 26)).inputs = [a, b] := by
      rcases hl : (gateAt C (w - 26)).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp [hl] at hlen2
      simp [a, b, hl]
    have ha_lt : a < w := by have := hrb (w - 26) hwLen.2 a (by rw [hlist]; simp); omega
    have hb_lt : b < w := by have := hrb (w - 26) hwLen.2 b (by rw [hlist]; simp); omega
    have haC : a ∈ coneOut := cone_subset_of_mem C hrb C.output w hwC (by
      rw [mem_cone_iff_gate C hrb hwLen.1 hwLen.2]; exact Or.inr ⟨a, by rw [hlist]; simp, mem_cone_self C a⟩)
    have hbC : b ∈ coneOut := cone_subset_of_mem C hrb C.output w hwC (by
      rw [mem_cone_iff_gate C hrb hwLen.1 hwLen.2]; exact Or.inr ⟨b, by rw [hlist]; simp, mem_cone_self C b⟩)
    have ha_notS : a ∉ S := fun h => by have := Finset.min'_le S a h; omega
    have hb_notS : b ∉ S := fun h => by have := Finset.min'_le S b h; omega
    have hweq : w = 26 + (w - 26) := by omega
    have hwAnd : (gateAt C (w - 26)).op = GateOp.and := by
      rcases hOpOfAll w hwG with hop | hop
      · exact hop
      · exfalso
        rw [hweq, wval_gate C hAO _ hwLen.2] at hwT hwP hwL
        simp only [hop, reduceCtorEq, ↓reduceIte, Bool.or_eq_true, Bool.or_eq_false_iff] at hwT hwP hwL
        rcases hwT with hat | hbt
        · exact ha_notS (Finset.mem_filter.mpr ⟨haC, hat, hwP.1, hwL.1⟩)
        · exact hb_notS (Finset.mem_filter.mpr ⟨hbC, hbt, hwP.2, hwL.2⟩)
    rw [hweq, wval_gate C hAO _ hwLen.2] at hwT hwP hwL
    simp only [hwAnd, ↓reduceIte, Bool.and_eq_true, Bool.and_eq_false_iff] at hwT hwP hwL
    have haPL : wval C (ind1 P) a = true ∨ wval C (ind1 L) a = true := by
      cases h1 : wval C (ind1 P) a
      · cases h2 : wval C (ind1 L) a
        · exact absurd (Finset.mem_filter.mpr ⟨haC, hwT.1, h1, h2⟩) ha_notS
        · exact Or.inr rfl
      · exact Or.inl rfl
    have hbPL : wval C (ind1 P) b = true ∨ wval C (ind1 L) b = true := by
      cases h1 : wval C (ind1 P) b
      · cases h2 : wval C (ind1 L) b
        · exact absurd (Finset.mem_filter.mpr ⟨hbC, hwT.2, h1, h2⟩) hb_notS
        · exact Or.inr rfl
      · exact Or.inl rfl
    rcases haPL with haP | haL
    · rcases hbPL with hbP | hbL
      · exfalso; rcases hwP with h | h
        · rw [haP] at h; cases h
        · rw [hbP] at h; cases h
      · refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hwG, hwAnd⟩, hwC⟩,
          ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haP⟩⟩,
          ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbL⟩⟩⟩,
          Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, haP⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbL⟩⟩⟩
    · rcases hbPL with hbP | hbL
      · refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hwG, hwAnd⟩, hwC⟩,
          ⟨L, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haL⟩⟩,
          ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbP⟩⟩⟩,
          Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbP⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, haL⟩⟩⟩
      · exfalso; rcases hwL with h | h
        · rw [haL] at h; cases h
        · rw [hbL] at h; cases h
  -- 3. Assign each w ∈ Ause a center c(w) : Fin 26 and leaf wire lw(w) : ℕ
  have hChoice : ∀ w : ℕ, ∃ c : Fin 26, ∃ lw : ℕ,
      w ∈ Ause →
      ((lw = (gateAt C (w - 26)).inputs.getD 0 0 ∧ orPart C ((gateAt C (w - 26)).inputs.getD 1 0) = {c}) ∨
       (lw = (gateAt C (w - 26)).inputs.getD 1 0 ∧ orPart C ((gateAt C (w - 26)).inputs.getD 0 0) = {c})) ∧
      (∀ u ∈ orPart C lw, adj26 c u) := by
    intro w
    by_cases hw : w ∈ Ause
    · obtain ⟨hPair, h1⟩ := hStar w hw
      rcases h1 with ha1 | hb1
      · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp ha1
        refine ⟨c, (gateAt C (w - 26)).inputs.getD 1 0, fun _ => ⟨Or.inr ⟨rfl, hc⟩, ?_⟩⟩
        intro u hu
        exact hPair c (by rw [hc]; simp) u hu
      · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hb1
        refine ⟨c, (gateAt C (w - 26)).inputs.getD 0 0, fun _ => ⟨Or.inl ⟨rfl, hc⟩, ?_⟩⟩
        intro u hu
        exact adj26_symm (hPair u hu c (by rw [hc]; simp))
    · exact ⟨0, 0, fun h => absurd h hw⟩
  choose ctr lw hCtrLw using hChoice
  -- The centers form a vertex cover of PG(2, 3), hence Ause.card ≥ 13!
  set TP : Finset (Fin 13) := Finset.univ.filter (fun p => ∃ w ∈ Ause, ctr w = Fin.castAdd 13 p)
  set TL : Finset (Fin 13) := Finset.univ.filter (fun l => ∃ w ∈ Ause, ctr w = Fin.natAdd 13 l)
  have hTcov : ∀ p l : Fin 13, inc p l → p ∈ TP ∨ l ∈ TL := by
    intro p l hinc
    obtain ⟨w, hwA, hcov⟩ := hEdgeCov p l hinc
    have hcl := (hCtrLw w hwA).1
    rcases hcl with ⟨_, h1⟩ | ⟨_, h0⟩
    · rcases hcov with ⟨hp, hl⟩ | ⟨hp, hl⟩
      · rw [h1, Finset.mem_singleton] at hl
        right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hwA, hl.symm⟩
      · rw [h1, Finset.mem_singleton] at hp
        left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hwA, hp.symm⟩
    · rcases hcov with ⟨hp, hl⟩ | ⟨hp, hl⟩
      · rw [h0, Finset.mem_singleton] at hp
        left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hwA, hp.symm⟩
      · rw [h0, Finset.mem_singleton] at hl
        right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hwA, hl.symm⟩
  have hVC := inc_vc_bound TP TL hTcov
  have hTP_TL_le : TP.card + TL.card ≤ Ause.card := by
    have hdisj : Disjoint (TP.image (Fin.castAdd 13)) (TL.image (Fin.natAdd 13)) := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨l, _, heq⟩ := Finset.mem_image.mp h2
      have := congrArg Fin.val heq; simp at this; omega
    have hsub : TP.image (Fin.castAdd 13) ∪ TL.image (Fin.natAdd 13) ⊆ Ause.image ctr := by
      intro v hv
      rcases Finset.mem_union.mp hv with h1 | h2
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨w, hw, heq⟩ := (Finset.mem_filter.mp hp).2
        exact Finset.mem_image.mpr ⟨w, hw, heq⟩
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h2
        obtain ⟨w, hw, heq⟩ := (Finset.mem_filter.mp hl).2
        exact Finset.mem_image.mpr ⟨w, hw, heq⟩
    calc TP.card + TL.card
        = (TP.image (Fin.castAdd 13)).card + (TL.image (Fin.natAdd 13)).card := by
            rw [Finset.card_image_of_injective _ (Fin.castAdd_injective 13 13),
                Finset.card_image_of_injective _ (Fin.natAdd_injective 13 13)]
      _ = (TP.image (Fin.castAdd 13) ∪ TL.image (Fin.natAdd 13)).card :=
            (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Ause.image ctr).card := Finset.card_le_card hsub
      _ ≤ Ause.card := Finset.card_image_le
  have hAuse_ge13 : 13 ≤ Ause.card := le_trans hVC.1 hTP_TL_le
  -- 4. Bound 52 ≤ Ause.card + Ogood.card using Leaf-Union Lemma + disjointness per center!
  set Sv : Fin 26 → Finset ℕ := fun v => (Ause.filter (fun w => ctr w = v)).image lw
  set Gv : Fin 26 → Finset ℕ := fun v => ((Sv v).biUnion (orCone C)).filter (isGoodOr C)
  have hGv_sub : ∀ v, Gv v ⊆ Ogood := by
    intro v g hg
    have hgG : isGoodOr C g := (Finset.mem_filter.mp hg).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(hmem_allG g).mpr ⟨hgG.1, hgG.2.1⟩, hgG.2.2.1⟩, hgG⟩
  have hGv_disj : ∀ v1 v2 : Fin 26, v1 ≠ v2 → Disjoint (Gv v1) (Gv v2) := by
    intro v1 v2 hne
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    have hgGood := (Finset.mem_filter.mp hg1).2
    have hgCard : 2 ≤ (orPart C g).card := hgGood.2.2.2.1
    obtain ⟨u1, hu1, hgu1⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hg1).1
    obtain ⟨w1, hw1, rfl⟩ := Finset.mem_image.mp hu1
    have hw1A := (Finset.mem_filter.mp hw1).1
    have hc1 : ctr w1 = v1 := (Finset.mem_filter.mp hw1).2
    obtain ⟨u2, hu2, hgu2⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hg2).1
    obtain ⟨w2, hw2, rfl⟩ := Finset.mem_image.mp hu2
    have hw2A := (Finset.mem_filter.mp hw2).1
    have hc2 : ctr w2 = v2 := (Finset.mem_filter.mp hw2).2
    have hsub1 : orPart C g ⊆ orPart C (lw w1) := orPart_subset_of_mem_orCone C hAO _ g hgu1
    have hsub2 : orPart C g ⊆ orPart C (lw w2) := orPart_subset_of_mem_orCone C hAO _ g hgu2
    obtain ⟨x1, hx1⟩ := Finset.card_pos.mp (by omega : 0 < (orPart C g).card)
    obtain ⟨x2, hx2, hxne⟩ := Finset.exists_mem_ne (by omega : 1 < (orPart C g).card) x1
    have h11 := hc1 ▸ (hCtrLw w1 hw1A).2 x1 (hsub1 hx1)
    have h12 := hc1 ▸ (hCtrLw w1 hw1A).2 x2 (hsub1 hx2)
    have h21 := hc2 ▸ (hCtrLw w2 hw2A).2 x1 (hsub2 hx1)
    have h22 := hc2 ▸ (hCtrLw w2 hw2A).2 x2 (hsub2 hx2)
    exact adj26_no_C4 v1 v2 x1 x2 hne hxne.symm h11 h12 h21 h22
  have h52_bound : 52 ≤ Ause.card + Ogood.card := by
    have hE_sub : E26 ⊆ (Finset.univ : Finset (Fin 26)).biUnion (fun v =>
        if v.val < 13 then ((Sv v).biUnion (orPart C)).image (fun u => (v, u))
        else ((Sv v).biUnion (orPart C)).image (fun u => (u, v))) := by
      intro ⟨uP, uL⟩ he
      obtain ⟨⟨p, l⟩, hpl, hpair⟩ := Finset.mem_image.mp he
      have hinc := (Finset.mem_filter.mp hpl).2
      have hpe : Fin.castAdd 13 p = uP := ((Prod.mk.injEq ..).mp hpair).1
      have hle : Fin.natAdd 13 l = uL := ((Prod.mk.injEq ..).mp hpair).2
      subst hpe; subst hle
      obtain ⟨w, hwA, hcov⟩ := hEdgeCov p l hinc
      have hcl := (hCtrLw w hwA).1
      refine Finset.mem_biUnion.mpr ⟨ctr w, Finset.mem_univ _, ?_⟩
      have hlwSv : lw w ∈ Sv (ctr w) := Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hwA, rfl⟩, rfl⟩
      rcases hcl with ⟨hlw, h1⟩ | ⟨hlw, h0⟩
      · rcases hcov with ⟨hp, hl⟩ | ⟨hp, hl⟩
        · rw [h1, Finset.mem_singleton] at hl
          have hc : ¬ (ctr w).val < 13 := by rw [← hl]; simp
          rw [if_neg hc]
          exact Finset.mem_image.mpr ⟨Fin.castAdd 13 p,
            Finset.mem_biUnion.mpr ⟨lw w, hlwSv, by rw [hlw]; exact hp⟩, by rw [hl]⟩
        · rw [h1, Finset.mem_singleton] at hp
          have hc : (ctr w).val < 13 := by rw [← hp]; simp
          rw [if_pos hc]
          exact Finset.mem_image.mpr ⟨Fin.natAdd 13 l,
            Finset.mem_biUnion.mpr ⟨lw w, hlwSv, by rw [hlw]; exact hl⟩, by rw [hp]⟩
      · rcases hcov with ⟨hp, hl⟩ | ⟨hp, hl⟩
        · rw [h0, Finset.mem_singleton] at hp
          have hc : (ctr w).val < 13 := by rw [← hp]; simp
          rw [if_pos hc]
          exact Finset.mem_image.mpr ⟨Fin.natAdd 13 l,
            Finset.mem_biUnion.mpr ⟨lw w, hlwSv, by rw [hlw]; exact hl⟩, by rw [hp]⟩
        · rw [h0, Finset.mem_singleton] at hl
          have hc : ¬ (ctr w).val < 13 := by rw [← hl]; simp
          rw [if_neg hc]
          exact Finset.mem_image.mpr ⟨Fin.castAdd 13 p,
            Finset.mem_biUnion.mpr ⟨lw w, hlwSv, by rw [hlw]; exact hp⟩, by rw [hl]⟩
    have hE_le : 52 ≤ ∑ v : Fin 26, ((Sv v).biUnion (orPart C)).card := by
      rw [← E26_card]
      calc E26.card
          ≤ ((Finset.univ : Finset (Fin 26)).biUnion _).card := Finset.card_le_card hE_sub
        _ ≤ ∑ v : Fin 26, (if v.val < 13 then ((Sv v).biUnion (orPart C)).image (fun u => (v, u))
            else ((Sv v).biUnion (orPart C)).image (fun u => (u, v))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ v : Fin 26, ((Sv v).biUnion (orPart C)).card := by
            apply Finset.sum_le_sum
            intro v _
            split_ifs <;> exact Finset.card_image_le
    have hSv_sum : ∑ v : Fin 26, (Sv v).card ≤ Ause.card := by
      calc ∑ v : Fin 26, (Sv v).card
          ≤ ∑ v : Fin 26, (Ause.filter (fun w => ctr w = v)).card :=
            Finset.sum_le_sum (fun v _ => Finset.card_image_le)
        _ = Ause.card := by
            rw [← Finset.card_biUnion]
            · congr 1; ext w; simp
            · intro v1 _ v2 _ hne
              show Disjoint _ _
              rw [Finset.disjoint_left]
              intro w h1 h2
              exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hGv_sum : ∑ v : Fin 26, (Gv v).card ≤ Ogood.card := by
      rw [← Finset.card_biUnion (fun v1 _ v2 _ hne => hGv_disj v1 v2 hne)]
      exact Finset.card_le_card (Finset.biUnion_subset.mpr (fun v _ => hGv_sub v))
    calc 52 ≤ ∑ v : Fin 26, ((Sv v).biUnion (orPart C)).card := hE_le
      _ ≤ ∑ v : Fin 26, ((Sv v).card + (Gv v).card) :=
          Finset.sum_le_sum (fun v _ => leaf_union_bound C hAO hAndEmpty _ (Sv v) le_rfl)
      _ = (∑ v : Fin 26, (Sv v).card) + ∑ v : Fin 26, (Gv v).card := Finset.sum_add_distrib
      _ ≤ Ause.card + Ogood.card := Nat.add_le_add hSv_sum hGv_sum
  -- 5. Slot count on Wlive \ {C.output}
  set Wneed := Wlive.erase C.output
  have hOutW : C.output ∈ Wlive := Finset.mem_filter.mpr ⟨mem_cone_self C C.output, hOutEmpty⟩
  have hWneed_card : Wneed.card = Alive.card + O0live.card - 1 := by
    rw [Finset.card_erase_of_mem hOutW, hWlive_card]
  -- Every w ∈ Wneed is read by some live gate in coneOut
  set Glive := allG.filter (fun g => g ∈ coneOut)
  set slots : ℕ → ℕ := fun g => ((gateAt C (g - 26)).inputs.filter (fun u => u ∈ Wneed)).length
  have hSlots_ge : Wneed.card ≤ ∑ g ∈ Glive, slots g := by
    have h1 : ∀ u ∈ Wneed, 1 ≤ ∑ g ∈ Glive, (gateAt C (g - 26)).inputs.count u := by
      intro u hu
      have hmem := Finset.mem_erase.mp hu
      have huC := (Finset.mem_filter.mp hmem.2).1
      have hult : u < C.output := lt_of_le_of_ne (mem_cone_le C hrb C.output u huC) hmem.1
      obtain ⟨g, hgC, hg1, hg2, hgu⟩ := exists_reader_of_mem_cone C hrb C.output u huC hult
      have hgL : g ∈ Glive := Finset.mem_filter.mpr ⟨(hmem_allG g).mpr ⟨hg1, hg2⟩, hgC⟩
      have hcnt : 1 ≤ (gateAt C (g - 26)).inputs.count u := List.count_pos_iff.mpr hgu
      exact le_trans hcnt (Finset.single_le_sum (f := fun g => (gateAt C (g - 26)).inputs.count u)
        (fun _ _ => Nat.zero_le _) hgL)
    have h2 : ∀ g ∈ Glive, ∑ u ∈ Wneed, (gateAt C (g - 26)).inputs.count u = slots g := by
      intro g _
      have hgen : ∀ xs : List ℕ, ∑ u ∈ Wneed, xs.count u = (xs.filter (fun u => u ∈ Wneed)).length := by
        intro xs
        induction xs with
        | nil => simp
        | cons x xs ih =>
          simp only [List.count_cons, Finset.sum_add_distrib, List.filter_cons]
          have h1 : ∑ u ∈ Wneed, (if x == u then 1 else 0) = if x ∈ Wneed then 1 else 0 := by
            have : (fun u => if x == u then 1 else 0) = (fun u => if u = x then 1 else 0) := by
              funext u; by_cases h : u = x
              · subst h; simp
              · have h' : x ≠ u := Ne.symm h; simp [h, h']
            rw [this, Finset.sum_ite_eq']
          rw [ih, h1]
          by_cases hx : x ∈ Wneed <;> simp [hx]
      exact hgen _
    calc Wneed.card = ∑ _u ∈ Wneed, 1 := by simp
      _ ≤ ∑ u ∈ Wneed, ∑ g ∈ Glive, (gateAt C (g - 26)).inputs.count u := Finset.sum_le_sum h1
      _ = ∑ g ∈ Glive, ∑ u ∈ Wneed, (gateAt C (g - 26)).inputs.count u := Finset.sum_comm
      _ = ∑ g ∈ Glive, slots g := Finset.sum_congr rfl h2
  -- Partition Glive = Ause ∪ Anon ∪ O0live ∪ Ogood_live ∪ O1mix
  set OgoodLive := Ogood.filter (fun g => g ∈ coneOut)
  have hGlive_part : Glive = Ause ∪ Anon ∪ O0live ∪ OgoodLive ∪ O1mix := by
    ext g
    simp only [Glive, Ause, Anon, Alive, O0live, OgoodLive, Ogood, O1mix, Aall, Oall,
      Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hgG, hgC⟩
      rcases hOpOfAll g hgG with hop | hop
      · by_cases hboth : (orPart C ((gateAt C (g - 26)).inputs.getD 0 0)).Nonempty ∧
            (orPart C ((gateAt C (g - 26)).inputs.getD 1 0)).Nonempty
        · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨⟨⟨hgG, hop⟩, hgC⟩, hboth⟩)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨⟨hgG, hop⟩, hgC⟩, hboth⟩)))
      · by_cases hE : orPart C g = ∅
        · exact Or.inl (Or.inl (Or.inr ⟨⟨hgG, hop⟩, hgC, hE⟩))
        · by_cases hGood : isGoodOr C g
          · exact Or.inl (Or.inr ⟨⟨⟨hgG, hop⟩, hGood⟩, hgC⟩)
          · exact Or.inr ⟨⟨hgG, hop⟩, hgC, hE, hGood⟩
    · rintro ((((⟨⟨⟨hgG, _⟩, hgC⟩, _⟩ | ⟨⟨⟨hgG, _⟩, hgC⟩, _⟩) | ⟨⟨hgG, _⟩, hgC, _⟩) | ⟨⟨⟨hgG, _⟩, _⟩, hgC⟩) | ⟨⟨hgG, _⟩, hgC, _, _⟩) <;>
        exact ⟨hgG, hgC⟩
  have hSlots_zero_Ause : ∀ g ∈ Ause, slots g = 0 := by
    intro g hg
    have hgG := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).1).1
    have hlen2 := hLenOfAll g hgG
    have hlist : (gateAt C (g - 26)).inputs =
        [(gateAt C (g - 26)).inputs.getD 0 0, (gateAt C (g - 26)).inputs.getD 1 0] := by
      rcases hl : (gateAt C (g - 26)).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp [hl] at hlen2 ⊢
    have h0 : (gateAt C (g - 26)).inputs.getD 0 0 ∉ Wneed := fun h => by
      have he := (Finset.mem_filter.mp (Finset.mem_erase.mp h).2).2
      exact (Finset.mem_filter.mp hg).2.1.ne_empty he
    have h1 : (gateAt C (g - 26)).inputs.getD 1 0 ∉ Wneed := fun h => by
      have he := (Finset.mem_filter.mp (Finset.mem_erase.mp h).2).2
      exact (Finset.mem_filter.mp hg).2.2.ne_empty he
    have hpair0 : ∀ (p : ℕ → Bool) (x y : ℕ), p x = false → p y = false → ([x, y].filter p).length = 0 := by
      intro p x y hx hy; simp [hx, hy]
    change ((gateAt C (g - 26)).inputs.filter (fun u => decide (u ∈ Wneed))).length = 0
    rw [hlist]
    exact hpair0 (fun u => decide (u ∈ Wneed)) _ _ (decide_eq_false h0) (decide_eq_false h1)
  have hSlots_zero_Ogood : ∀ g ∈ OgoodLive, slots g = 0 := by
    intro g hg
    have hgGood := (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).2
    have hgG := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).1).1
    have hlen2 := hLenOfAll g hgG
    have hlist : (gateAt C (g - 26)).inputs =
        [(gateAt C (g - 26)).inputs.getD 0 0, (gateAt C (g - 26)).inputs.getD 1 0] := by
      rcases hl : (gateAt C (g - 26)).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp [hl] at hlen2 ⊢
    have h0 : (gateAt C (g - 26)).inputs.getD 0 0 ∉ Wneed := fun h => by
      have he := (Finset.mem_filter.mp (Finset.mem_erase.mp h).2).2
      exact hgGood.2.2.2.2.1.ne_empty he
    have h1 : (gateAt C (g - 26)).inputs.getD 1 0 ∉ Wneed := fun h => by
      have he := (Finset.mem_filter.mp (Finset.mem_erase.mp h).2).2
      exact hgGood.2.2.2.2.2.ne_empty he
    have hpair0 : ∀ (p : ℕ → Bool) (x y : ℕ), p x = false → p y = false → ([x, y].filter p).length = 0 := by
      intro p x y hx hy; simp [hx, hy]
    change ((gateAt C (g - 26)).inputs.filter (fun u => decide (u ∈ Wneed))).length = 0
    rw [hlist]
    exact hpair0 (fun u => decide (u ∈ Wneed)) _ _ (decide_eq_false h0) (decide_eq_false h1)
  have hSlots_le_one_O1mix : ∀ g ∈ O1mix, slots g ≤ 1 := by
    intro g hg
    have hgO := (Finset.mem_filter.mp hg).1
    have hgG := (Finset.mem_filter.mp hgO).1
    have hgOp := (Finset.mem_filter.mp hgO).2
    have hgP := (hmem_allG g).mp hgG
    have hgNe : orPart C g ≠ ∅ := (Finset.mem_filter.mp hg).2.2.1
    have hlen2 := hLenOfAll g hgG
    have hlist : (gateAt C (g - 26)).inputs =
        [(gateAt C (g - 26)).inputs.getD 0 0, (gateAt C (g - 26)).inputs.getD 1 0] := by
      rcases hl : (gateAt C (g - 26)).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp [hl] at hlen2 ⊢
    have hU := orPart_or_gate C hAO hgP.1 hgP.2 hgOp
    have hor : orPart C ((gateAt C (g - 26)).inputs.getD 0 0) ≠ ∅ ∨
        orPart C ((gateAt C (g - 26)).inputs.getD 1 0) ≠ ∅ := by
      by_contra h; push Not at h
      rw [h.1, h.2, Finset.empty_union] at hU; exact hgNe hU
    have hor' : decide ((gateAt C (g - 26)).inputs.getD 0 0 ∈ Wneed) = false ∨
        decide ((gateAt C (g - 26)).inputs.getD 1 0 ∈ Wneed) = false := by
      rcases hor with h0 | h1
      · left; exact decide_eq_false (fun h => h0 (Finset.mem_filter.mp (Finset.mem_erase.mp h).2).2)
      · right; exact decide_eq_false (fun h => h1 (Finset.mem_filter.mp (Finset.mem_erase.mp h).2).2)
    have hpair1 : ∀ (p : ℕ → Bool) (x y : ℕ), (p x = false ∨ p y = false) → ([x, y].filter p).length ≤ 1 := by
      intro p x y h; cases hx : p x <;> cases hy : p y <;> simp [hx, hy] at h ⊢
    change ((gateAt C (g - 26)).inputs.filter (fun u => decide (u ∈ Wneed))).length ≤ 1
    rw [hlist]
    exact hpair1 (fun u => decide (u ∈ Wneed)) _ _ hor'
  have hSlots_le_two : ∀ g ∈ allG, slots g ≤ 2 := by
    intro g hg
    calc slots g ≤ (gateAt C (g - 26)).inputs.length := List.length_filter_le _ _
      _ = 2 := hLenOfAll g hg
  have hSlots_upper : ∑ g ∈ Glive, slots g ≤ (∑ g ∈ Anon, slots g) + 2 * O0live.card + O1mix.card := by
    have hsum_le : ∀ S1 S2 : Finset ℕ, ∑ g ∈ S1 ∪ S2, slots g ≤ (∑ g ∈ S1, slots g) + ∑ g ∈ S2, slots g := by
      intro S1 S2
      have h1 := Finset.sum_union_inter (s₁ := S1) (s₂ := S2) (f := slots)
      omega
    have hAuse0 : ∑ g ∈ Ause, slots g = 0 := Finset.sum_eq_zero hSlots_zero_Ause
    have hOg0 : ∑ g ∈ OgoodLive, slots g = 0 := Finset.sum_eq_zero hSlots_zero_Ogood
    have hO0 : ∑ g ∈ O0live, slots g ≤ 2 * O0live.card := by
      calc ∑ g ∈ O0live, slots g ≤ ∑ _g ∈ O0live, 2 :=
            Finset.sum_le_sum (fun g hg => hSlots_le_two g (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).1)
        _ = 2 * O0live.card := by simp [mul_comm]
    have hO1 : ∑ g ∈ O1mix, slots g ≤ O1mix.card := by
      calc ∑ g ∈ O1mix, slots g ≤ ∑ _g ∈ O1mix, 1 := Finset.sum_le_sum hSlots_le_one_O1mix
        _ = O1mix.card := by simp
    rw [hGlive_part]
    have h1 := hsum_le (Ause ∪ Anon ∪ O0live ∪ OgoodLive) O1mix
    have h2 := hsum_le (Ause ∪ Anon ∪ O0live) OgoodLive
    have h3 := hsum_le (Ause ∪ Anon) O0live
    have h4 := hsum_le Ause Anon
    omega
  -- Total gate count: Ause, Anon, O0live, Ogood, O1mix are pairwise disjoint subsets of allG!
  have hDisj_5 : Ause.card + Anon.card + O0live.card + Ogood.card + O1mix.card ≤ allG.card := by
    have h1 : Ause ∪ Anon ⊆ Aall := by
      intro w hw; rcases Finset.mem_union.mp hw with h | h
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1
    have h2 : O0live ∪ Ogood ∪ O1mix ⊆ Oall := by
      intro w hw
      rcases Finset.mem_union.mp hw with h12 | h3
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · exact (Finset.mem_filter.mp h1).1
        · exact (Finset.mem_filter.mp h2).1
      · exact (Finset.mem_filter.mp h3).1
    have hDA : Disjoint Aall Oall := by
      rw [Finset.disjoint_left]; intro w ha ho
      have h1 := (Finset.mem_filter.mp ha).2
      have h2 := (Finset.mem_filter.mp ho).2
      rw [h1] at h2; cases h2
    have hDO0g : Disjoint O0live Ogood := by
      rw [Finset.disjoint_left]; intro w h0 hg
      have he := (Finset.mem_filter.mp h0).2.2
      have h2 := (Finset.mem_filter.mp hg).2.2.2.2.1
      rw [he] at h2; simp at h2
    have hDO0m : Disjoint O0live O1mix := by
      rw [Finset.disjoint_left]; intro w h0 hm
      exact (Finset.mem_filter.mp hm).2.2.1 (Finset.mem_filter.mp h0).2.2
    have hDOgm : Disjoint Ogood O1mix := by
      rw [Finset.disjoint_left]; intro w hg hm
      exact (Finset.mem_filter.mp hm).2.2.2 (Finset.mem_filter.mp hg).2
    have hO_card : O0live.card + Ogood.card + O1mix.card ≤ Oall.card := by
      have hD1 : Disjoint (O0live ∪ Ogood) O1mix := Finset.disjoint_union_left.mpr ⟨hDO0m, hDOgm⟩
      calc O0live.card + Ogood.card + O1mix.card
          = (O0live ∪ Ogood).card + O1mix.card := by rw [Finset.card_union_of_disjoint hDO0g]
        _ = (O0live ∪ Ogood ∪ O1mix).card := (Finset.card_union_of_disjoint hD1).symm
        _ ≤ Oall.card := Finset.card_le_card h2
    have hA_card : Ause.card + Anon.card ≤ Aall.card := by
      rw [← hAlive_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have hAO_card : Aall.card + Oall.card ≤ allG.card := by
      rw [← Finset.card_union_of_disjoint hDA]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    omega
  -- Also note: ∑ g ∈ Anon, slots g ≤ 2 * Anon.card
  have hAnon_le : ∑ g ∈ Anon, slots g ≤ 2 * Anon.card := by
    calc ∑ g ∈ Anon, slots g ≤ ∑ _g ∈ Anon, 2 :=
          Finset.sum_le_sum (fun g hg => hSlots_le_two g (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).1).1)
      _ = 2 * Anon.card := by simp [mul_comm]
  have hCsize : allG.card ≤ 64 := by rw [hallG_card]; exact hSize
  -- Rigidity! Since 52 ≤ Ause + Ogood and Ause - 1 ≤ O0live + O1mix + Anon and 13 ≤ Ause:
  -- We get: Ause.card = 13, allG.card = 64, ZERO dead gates, and EVERY g ∈ Anon has slots g = 2!
  have hAuse_eq13 : Ause.card = 13 := by omega
  have hNoDead : Ause.card + Anon.card + O0live.card + Ogood.card + O1mix.card = allG.card := by omega
  have hAnon_slots_eq : ∑ g ∈ Anon, slots g = 2 * Anon.card := by omega
  -- Every gate in allG is in coneOut? Even better: every gate in Aall is in Alive (no dead AND gates)!
  have hAall_eq_Alive : Aall = Alive := by
    have hle : Aall.card ≤ Alive.card := by
      have hO_card : O0live.card + Ogood.card + O1mix.card ≤ Oall.card := by
        have hDO0g : Disjoint O0live Ogood := by
          rw [Finset.disjoint_left]; intro w h0 hg
          have he := (Finset.mem_filter.mp h0).2.2; have h2 := (Finset.mem_filter.mp hg).2.2.2.2.1
          rw [he] at h2; simp at h2
        have hDO0m : Disjoint O0live O1mix := by
          rw [Finset.disjoint_left]; intro w h0 hm; exact (Finset.mem_filter.mp hm).2.2.1 (Finset.mem_filter.mp h0).2.2
        have hDOgm : Disjoint Ogood O1mix := by
          rw [Finset.disjoint_left]; intro w hg hm; exact (Finset.mem_filter.mp hm).2.2.2 (Finset.mem_filter.mp hg).2
        have hD1 : Disjoint (O0live ∪ Ogood) O1mix := Finset.disjoint_union_left.mpr ⟨hDO0m, hDOgm⟩
        calc O0live.card + Ogood.card + O1mix.card
            = (O0live ∪ Ogood ∪ O1mix).card := by rw [Finset.card_union_of_disjoint hD1, Finset.card_union_of_disjoint hDO0g]
          _ ≤ Oall.card := Finset.card_le_card (by
              intro w hw; rcases Finset.mem_union.mp hw with h12 | h3
              · rcases Finset.mem_union.mp h12 with h1 | h2
                · exact (Finset.mem_filter.mp h1).1
                · exact (Finset.mem_filter.mp h2).1
              · exact (Finset.mem_filter.mp h3).1)
      have hDA : Disjoint Aall Oall := by
        rw [Finset.disjoint_left]; intro w ha ho
        have h1 := (Finset.mem_filter.mp ha).2; have h2 := (Finset.mem_filter.mp ho).2; rw [h1] at h2; cases h2
      have hAO_card : Aall.card + Oall.card ≤ allG.card := by
        rw [← Finset.card_union_of_disjoint hDA]
        exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      omega
    exact (Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hle).symm
  -- Every g ∈ Anon has slots g = 2, hence BOTH operands have empty orPart!
  have hAnon_both_empty : ∀ g ∈ Anon,
      orPart C ((gateAt C (g - 26)).inputs.getD 0 0) = ∅ ∧
      orPart C ((gateAt C (g - 26)).inputs.getD 1 0) = ∅ := by
    intro g hg
    have hsg : slots g = 2 := by
      by_contra hne
      have hlt : slots g < 2 := by
        have := hSlots_le_two g (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).1).1
        omega
      have hsum_lt : ∑ g' ∈ Anon, slots g' < 2 * Anon.card := by
        calc ∑ g' ∈ Anon, slots g'
            = slots g + ∑ g' ∈ Anon.erase g, slots g' := (Finset.add_sum_erase Anon slots hg).symm
          _ < 2 + ∑ _g' ∈ Anon.erase g, 2 := by
              have hrest : ∑ g' ∈ Anon.erase g, slots g' ≤ ∑ _g' ∈ Anon.erase g, 2 :=
                Finset.sum_le_sum (fun g' hg' => hSlots_le_two g'
                  (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_erase.mp hg').2).1).1).1)
              omega
          _ = 2 * Anon.card := by
              simp only [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hg]
              have hpos : 1 ≤ Anon.card := Finset.card_pos.mpr ⟨g, hg⟩
              omega
      omega
    have hgG := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).1).1
    have hlen2 := hLenOfAll g hgG
    have hlist : (gateAt C (g - 26)).inputs =
        [(gateAt C (g - 26)).inputs.getD 0 0, (gateAt C (g - 26)).inputs.getD 1 0] := by
      rcases hl : (gateAt C (g - 26)).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp [hl] at hlen2 ⊢
    have hpair2 : ∀ (p : ℕ → Bool) (x y : ℕ), ([x, y].filter p).length = 2 →
        p x = true ∧ p y = true := by
      intro p x y hlen
      cases hx : p x <;> cases hy : p y <;> simp [hx, hy] at hlen ⊢
    have h01 := hpair2 (fun u => decide (u ∈ Wneed)) _ _ (by rw [← hlist]; exact hsg)
    exact ⟨(Finset.mem_filter.mp (Finset.mem_erase.mp (of_decide_eq_true h01.1)).2).2,
           (Finset.mem_filter.mp (Finset.mem_erase.mp (of_decide_eq_true h01.2)).2).2⟩
  -- Therefore j1 and j2 MUST BOTH be in Ause!
  have hj1_lt : j1 < C.gates.length := by
    by_contra hge
    have := List.getElem?_eq_none (by omega : C.gates.length ≤ j1)
    rw [this] at hj1; cases hj1.1
  have hj2_lt : j2 < C.gates.length := by
    by_contra hge
    have := List.getElem?_eq_none (by omega : C.gates.length ≤ j2)
    rw [this] at hj2; cases hj2.1
  have hj1_gate : gateAt C j1 = ⟨GateOp.and, [a1, b1]⟩ := by
    unfold gateAt; rw [List.getD_eq_getElem?_getD, hj1.1]; rfl
  have hj2_gate : gateAt C j2 = ⟨GateOp.and, [a2, b2]⟩ := by
    unfold gateAt; rw [List.getD_eq_getElem?_getD, hj2.1]; rfl
  have hj1_live : 26 + j1 ∈ Alive := by
    rw [← hAall_eq_Alive]
    exact Finset.mem_filter.mpr ⟨(hmem_allG (26 + j1)).mpr ⟨by omega, by omega⟩, by simp [hj1_gate]⟩
  have hj2_live : 26 + j2 ∈ Alive := by
    rw [← hAall_eq_Alive]
    exact Finset.mem_filter.mpr ⟨(hmem_allG (26 + j2)).mpr ⟨by omega, by omega⟩, by simp [hj2_gate]⟩
  have hj1_use : 26 + j1 ∈ Ause := by
    by_contra hnot
    have hmem : 26 + j1 ∈ Anon :=
      Finset.mem_filter.mpr ⟨hj1_live, fun h => hnot (Finset.mem_filter.mpr ⟨hj1_live, h⟩)⟩
    have he := hAnon_both_empty (26 + j1) hmem
    simp only [Nat.add_sub_cancel_left, hj1_gate, List.getD_cons_zero, List.getD_cons_succ] at he
    simp only [Bool.or_eq_true] at h1P
    rcases h1P with h | h
    · have : P0 ∈ orPart C a1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [he.1] at this; simp at this
    · have : P0 ∈ orPart C b1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [he.2] at this; simp at this
  have hj2_use : 26 + j2 ∈ Ause := by
    by_contra hnot
    have hmem : 26 + j2 ∈ Anon :=
      Finset.mem_filter.mpr ⟨hj2_live, fun h => hnot (Finset.mem_filter.mpr ⟨hj2_live, h⟩)⟩
    have he := hAnon_both_empty (26 + j2) hmem
    simp only [Nat.add_sub_cancel_left, hj2_gate, List.getD_cons_zero, List.getD_cons_succ] at he
    simp only [Bool.or_eq_true] at h2L
    rcases h2L with h | h
    · have : L0 ∈ orPart C a2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [he.1] at this; simp at this
    · have : L0 ∈ orPart C b2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [he.2] at this; simp at this
  -- 6. Rigidity of centers: TP.card + TL.card = 13, so TP = univ OR TL = univ!
  have hTsum : TP.card + TL.card = 13 := by omega
  -- Every w ∈ Ause must have (orPart C (lw w)).card = 4!
  have hLwCard_le4 : ∀ w ∈ Ause, (orPart C (lw w)).card ≤ 4 := by
    intro w hw
    have hsub : orPart C (lw w) ⊆ Finset.univ.filter (fun u : Fin 26 => adj26 (ctr w) u) :=
      fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hCtrLw w hw).2 u hu⟩
    calc (orPart C (lw w)).card
        ≤ (Finset.univ.filter (fun u : Fin 26 => adj26 (ctr w) u)).card := Finset.card_le_card hsub
      _ = 4 := adj26_deg (ctr w)
  have hSumLw_ge52 : 52 ≤ ∑ w ∈ Ause, (orPart C (lw w)).card := by
    have hE_sub : E26 ⊆ Ause.biUnion (fun w =>
        if (ctr w).val < 13 then (orPart C (lw w)).image (fun u => (ctr w, u))
        else (orPart C (lw w)).image (fun u => (u, ctr w))) := by
      intro ⟨uP, uL⟩ he
      obtain ⟨⟨p, l⟩, hpl, hpair⟩ := Finset.mem_image.mp he
      have hinc := (Finset.mem_filter.mp hpl).2
      have hpe : Fin.castAdd 13 p = uP := ((Prod.mk.injEq ..).mp hpair).1
      have hle : Fin.natAdd 13 l = uL := ((Prod.mk.injEq ..).mp hpair).2
      subst hpe; subst hle
      obtain ⟨w, hwA, hcov⟩ := hEdgeCov p l hinc
      refine Finset.mem_biUnion.mpr ⟨w, hwA, ?_⟩
      rcases (hCtrLw w hwA).1 with ⟨hlw, h1⟩ | ⟨hlw, h0⟩
      · rcases hcov with ⟨hp, hl⟩ | ⟨hp, hl⟩
        · rw [h1, Finset.mem_singleton] at hl
          have hc : ¬ (ctr w).val < 13 := by rw [← hl]; simp
          rw [if_neg hc]
          exact Finset.mem_image.mpr ⟨Fin.castAdd 13 p, by rw [hlw]; exact hp, by rw [hl]⟩
        · rw [h1, Finset.mem_singleton] at hp
          have hc : (ctr w).val < 13 := by rw [← hp]; simp
          rw [if_pos hc]
          exact Finset.mem_image.mpr ⟨Fin.natAdd 13 l, by rw [hlw]; exact hl, by rw [hp]⟩
      · rcases hcov with ⟨hp, hl⟩ | ⟨hp, hl⟩
        · rw [h0, Finset.mem_singleton] at hp
          have hc : (ctr w).val < 13 := by rw [← hp]; simp
          rw [if_pos hc]
          exact Finset.mem_image.mpr ⟨Fin.natAdd 13 l, by rw [hlw]; exact hl, by rw [hp]⟩
        · rw [h0, Finset.mem_singleton] at hl
          have hc : ¬ (ctr w).val < 13 := by rw [← hl]; simp
          rw [if_neg hc]
          exact Finset.mem_image.mpr ⟨Fin.castAdd 13 p, by rw [hlw]; exact hp, by rw [hl]⟩
    rw [← E26_card]
    calc E26.card ≤ (Ause.biUnion _).card := Finset.card_le_card hE_sub
      _ ≤ ∑ w ∈ Ause, (if (ctr w).val < 13 then (orPart C (lw w)).image (fun u => (ctr w, u))
            else (orPart C (lw w)).image (fun u => (u, ctr w))).card := Finset.card_biUnion_le
      _ ≤ ∑ w ∈ Ause, (orPart C (lw w)).card := by
          apply Finset.sum_le_sum; intro w _; split_ifs <;> exact Finset.card_image_le
  have hLwCard_eq4 : ∀ w ∈ Ause, (orPart C (lw w)).card = 4 := by
    intro w hw
    by_contra hne
    have hlt : (orPart C (lw w)).card < 4 := by have := hLwCard_le4 w hw; omega
    have hsum_lt : ∑ w' ∈ Ause, (orPart C (lw w')).card < 52 := by
      calc ∑ w' ∈ Ause, (orPart C (lw w')).card
          = (orPart C (lw w)).card + ∑ w' ∈ Ause.erase w, (orPart C (lw w')).card :=
            (Finset.add_sum_erase Ause (fun w' => (orPart C (lw w')).card) hw).symm
        _ < 4 + ∑ _w' ∈ Ause.erase w, 4 := by
            have hrest : ∑ w' ∈ Ause.erase w, (orPart C (lw w')).card ≤ ∑ _w' ∈ Ause.erase w, 4 :=
              Finset.sum_le_sum (fun w' hw' => hLwCard_le4 w' (Finset.mem_erase.mp hw').2)
            omega
        _ = 52 := by simp [Finset.card_erase_of_mem hw, hAuse_eq13]
    omega
  -- Final contradiction by cases on TP = univ vs TL = univ!
  rcases hVC.2 hTsum with hTPuniv | hTLuniv
  · have hTL0 : TL = ∅ := by
      have : TP.card = 13 := by rw [hTPuniv]; simp
      exact Finset.card_eq_zero.mp (by omega)
    have hctr_lt : ∀ w ∈ Ause, (ctr w).val < 13 := by
      intro w hw
      by_contra hge
      have hlt : (ctr w).val < 26 := (ctr w).isLt
      have hl : (⟨(ctr w).val - 13, by omega⟩ : Fin 13) ∈ TL :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, Fin.ext (by simp; omega)⟩
      rw [hTL0] at hl; simp at hl
    have hc1_lt := hctr_lt (26 + j1) hj1_use
    have hP0_not_lw : P0 ∉ orPart C (lw (26 + j1)) := by
      intro hmem
      rcases adj26_sides ((hCtrLw (26 + j1) hj1_use).2 P0 hmem) with ⟨_, hbad⟩ | ⟨hbad, _⟩
      · have : P0.val < 13 := p0.isLt; omega
      · omega
    have hctr1_eq : ctr (26 + j1) = P0 := by
      have hcl := (hCtrLw (26 + j1) hj1_use).1
      simp only [Nat.add_sub_cancel_left, hj1_gate, List.getD_cons_zero, List.getD_cons_succ] at hcl
      simp only [Bool.or_eq_true] at h1P
      rcases hcl with ⟨hlw, h1⟩ | ⟨hlw, h0⟩
      · rcases h1P with ha | hb
        · exfalso; exact hP0_not_lw (by rw [hlw]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
        · have : P0 ∈ orPart C b1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
          rw [h1, Finset.mem_singleton] at this; exact this.symm
      · rcases h1P with ha | hb
        · have : P0 ∈ orPart C a1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
          rw [h0, Finset.mem_singleton] at this; exact this.symm
        · exfalso; exact hP0_not_lw (by rw [hlw]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    set Np0 := Finset.univ.filter (fun u : Fin 26 => adj26 P0 u)
    have hsub : orPart C (lw (26 + j1)) ⊆ Np0 := fun u hu =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hctr1_eq ▸ (hCtrLw (26 + j1) hj1_use).2 u hu⟩
    have heq : orPart C (lw (26 + j1)) = Np0 :=
      Finset.eq_of_subset_of_card_le hsub (by rw [adj26_deg P0, hLwCard_eq4 _ hj1_use])
    have hL0_in : L0 ∈ orPart C (lw (26 + j1)) := by
      rw [heq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨p0, l0, hInc0, rfl, rfl⟩⟩
    have hL0_val : wval C (ind1 L0) (lw (26 + j1)) = true := (Finset.mem_filter.mp hL0_in).2
    have hcl := (hCtrLw (26 + j1) hj1_use).1
    simp only [Nat.add_sub_cancel_left, hj1_gate, List.getD_cons_zero, List.getD_cons_succ] at hcl
    rcases hcl with ⟨hlw, _⟩ | ⟨hlw, _⟩
    · rw [hlw] at hL0_val; exact h1nL (by simp [hL0_val])
    · rw [hlw] at hL0_val; exact h1nL (by simp [hL0_val])
  · have hTP0 : TP = ∅ := by
      have : TL.card = 13 := by rw [hTLuniv]; simp
      exact Finset.card_eq_zero.mp (by omega)
    have hctr_ge : ∀ w ∈ Ause, 13 ≤ (ctr w).val := by
      intro w hw
      by_contra hlt
      have hp : (⟨(ctr w).val, by omega⟩ : Fin 13) ∈ TP :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, Fin.ext rfl⟩
      rw [hTP0] at hp; simp at hp
    have hc2_ge := hctr_ge (26 + j2) hj2_use
    have hL0_not_lw : L0 ∉ orPart C (lw (26 + j2)) := by
      intro hmem
      rcases adj26_sides ((hCtrLw (26 + j2) hj2_use).2 L0 hmem) with ⟨hbad, _⟩ | ⟨_, hbad⟩
      · omega
      · have : 13 ≤ L0.val := by simp [L0]
        omega
    have hctr2_eq : ctr (26 + j2) = L0 := by
      have hcl := (hCtrLw (26 + j2) hj2_use).1
      simp only [Nat.add_sub_cancel_left, hj2_gate, List.getD_cons_zero, List.getD_cons_succ] at hcl
      simp only [Bool.or_eq_true] at h2L
      rcases hcl with ⟨hlw, h1⟩ | ⟨hlw, h0⟩
      · rcases h2L with ha | hb
        · exfalso; exact hL0_not_lw (by rw [hlw]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
        · have : L0 ∈ orPart C b2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
          rw [h1, Finset.mem_singleton] at this; exact this.symm
      · rcases h2L with ha | hb
        · have : L0 ∈ orPart C a2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
          rw [h0, Finset.mem_singleton] at this; exact this.symm
        · exfalso; exact hL0_not_lw (by rw [hlw]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
    set Nl0 := Finset.univ.filter (fun u : Fin 26 => adj26 L0 u)
    have hsub : orPart C (lw (26 + j2)) ⊆ Nl0 := fun u hu =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hctr2_eq ▸ (hCtrLw (26 + j2) hj2_use).2 u hu⟩
    have heq : orPart C (lw (26 + j2)) = Nl0 :=
      Finset.eq_of_subset_of_card_le hsub (by rw [adj26_deg L0, hLwCard_eq4 _ hj2_use])
    have hP0_in : P0 ∈ orPart C (lw (26 + j2)) := by
      rw [heq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨p0, l0, hInc0, rfl, rfl⟩⟩
    have hP0_val : wval C (ind1 P0) (lw (26 + j2)) = true := (Finset.mem_filter.mp hP0_in).2
    have hcl := (hCtrLw (26 + j2) hj2_use).1
    simp only [Nat.add_sub_cancel_left, hj2_gate, List.getD_cons_zero, List.getD_cons_succ] at hcl
    rcases hcl with ⟨hlw, _⟩ | ⟨hlw, _⟩
    · rw [hlw] at hP0_val; exact h2nP (by simp [hP0_val])
    · rw [hlw] at hP0_val; exact h2nP (by simp [hP0_val])

end PEqualNP.Outside.L_meta_2615_aux

theorem PEqualNP.Outside.L_meta_2615 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (64 : ℕ) →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →       (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x4]? = Option.some x5 → x5.inputs.Nodup) →         have x5 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x5 x6 : Fin (13 : ℕ)) => x5 - x6 = (0 : Fin (13 : ℕ)) ∨ x5 - x6 = (1 : Fin (13 : ℕ)) ∨ x5 - x6 = (3 : Fin (13 : ℕ)) ∨ x5 - x6 = (9 : Fin (13 : ℕ));         have x6 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ) => (x1.wires (List.ofFn x6)).getD x7 Bool.false;         (∀ (x7 : Fin (26 : ℕ) → Bool), x6 x7 x1.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x5 x8 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →           (∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x10 : Fin (26 : ℕ) → Bool), x6 x10 ((26 : ℕ) + x8) = Bool.true → x6 x10 x1.output = Bool.true) →             ∀ (x9 x10 : Fin (13 : ℕ)),               x5 x9 x10 →                 have x12 : Fin ((13 : ℕ) + (13 : ℕ)) := Fin.castAdd (13 : ℕ) x9;                 have x13 : Fin ((13 : ℕ) + (13 : ℕ)) := Fin.natAdd (13 : ℕ) x10;                 have x14 : ℕ → ℕ → ℕ → Prop := fun (x14 x15 x16 : ℕ) => x1.gates[x14]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x15, x16] : PEqualNP.CircuitLowerBounds.Gate } ∧ x6 (fun (x17 : Fin (26 : ℕ)) => Decidable.decide (x17 = x12 ∨ x17 = x13)) ((26 : ℕ) + x14) = Bool.true;                 have x15 : Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x15 : Fin (26 : ℕ)) (x16 x17 : ℕ) => (x6 (fun (x18 : Fin (26 : ℕ)) => Decidable.decide (x18 = x15)) x16 || x6 (fun (x18 : Fin (26 : ℕ)) => Decidable.decide (x18 = x15)) x17) = Bool.true;                 ∀ (x16 x17 x18 x19 x20 x21 : ℕ), x14 x16 x17 x18 → x14 x19 x20 x21 → x15 x12 x17 x18 → ¬x15 x13 x17 x18 → x15 x13 x20 x21 → x15 x12 x20 x21 :=
  PEqualNP.Outside.L_meta_2615_aux.main_proof
