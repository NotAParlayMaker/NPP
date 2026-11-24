import Mathlib

namespace PEqualNP.Outside.L_meta_1561

def line (t : Fin 21) : Finset (Fin 21) := {t, t + 1, t + 4, t + 14, t + 16}
def tri : Finset (Fin 21) := {0, 1, 2}
def single : Finset (Fin 21) := {2, 5, 6, 8, 9, 17, 18, 19, 20}
def base (b : Bool) (s p : Fin 21) : Finset (Fin 21) :=
  if p ∈ tri then ∅
  else if (line s ∩ tri).card = 2 then tri \ line s
  else if (line s ∩ tri).card = 1 then
    if b then (line s ∩ tri).image (fun v => if v = 2 then 0 else v + 1)
    else (line s ∩ tri).image (fun v => if v = 0 then 2 else v - 1)
  else {0}
abbrev cross (s t : Fin 21) (b d : Bool) : Prop :=
  (∃ p ∈ line s \ line t, (base b s p ∩ line t).Nonempty) ∧
  (∃ p ∈ line t \ line s, (base d t p ∩ line s).Nonempty)
def pairs (c : Fin 21 → Bool) : Finset (Fin 21 × Fin 21) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ cross e.1 e.2 (c e.1) (c e.2))
def fixed : Finset (Fin 21 × Fin 21) :=
  {(0,1), (0,2), (0,7), (0,9), (0,19), (1,5), (1,7), (1,17), (1,20), (6,7), (7,8), (7,18)}
def cycle : Finset (Fin 21 × Fin 21) :=
  {(2,5), (5,6), (6,9), (9,17), (17,18), (18,19), (19,20), (20,8), (8,2)}

lemma single_spec : ∀ s : Fin 21, (line s ∩ tri).card = 1 ↔ s ∈ single := by decide
lemma fixed_card : fixed.card = 12 := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma fixed_spec : ∀ e : Fin 21 × Fin 21, e ∈ fixed →
    e.1 < e.2 ∧ ∀ b d : Bool, cross e.1 e.2 b d := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma true_spec : ∀ s t : Fin 21, s ≠ t →
    (cross s t true true ↔
      (((line s ∩ tri).card = 2 ∧ (line t ∩ tri).card = 2) ∨
       ((line s ∩ tri).card = 2 ∧ (line t ∩ tri).card = 1 ∧ line t ∩ tri ∩ line s = ∅) ∨
       ((line t ∩ tri).card = 2 ∧ (line s ∩ tri).card = 1 ∧ line s ∩ tri ∩ line t = ∅))) := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma uniform_spec : ∀ b : Bool, pairs (fun _ => b) = fixed := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma cycle_spec : ∀ e : Fin 21 × Fin 21, e ∈ cycle →
    e.1 ≠ e.2 ∧ e ∉ fixed ∧ (e.2, e.1) ∉ fixed ∧ cross e.1 e.2 true false := by decide

lemma cross_symm (s t : Fin 21) (b d : Bool) : cross s t b d ↔ cross t s d b := by
  simp only [cross, and_comm]

lemma fixed_subset (c : Fin 21 → Bool) : fixed ⊆ pairs c := by
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, (fixed_spec e he).1, (fixed_spec e he).2 _ _⟩

lemma lower (c : Fin 21 → Bool) : 12 ≤ (pairs c).card := by
  rw [← fixed_card]
  exact Finset.card_le_card (fixed_subset c)

lemma base_congr (c d : Fin 21 → Bool) (h : ∀ s ∈ single, c s = d s) :
    ∀ s p, base (c s) s p = base (d s) s p := by
  intro s p
  unfold base
  by_cases h1 : p ∈ tri
  · simp [h1]
  by_cases h2 : (line s ∩ tri).card = 2
  · simp [h1, h2]
  by_cases h3 : (line s ∩ tri).card = 1
  · rw [h s ((single_spec s).mp h3)]
  · simp [h1, h2, h3]

lemma pairs_congr (c d : Fin 21 → Bool) (h : ∀ s ∈ single, c s = d s) :
    pairs c = pairs d := by
  ext e
  simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and, cross,
    base_congr c d h]

lemma constant_on_cycle (a b c d e f g h i : Bool)
    (hab : a = true → b = true) (hbc : b = true → c = true)
    (hcd : c = true → d = true) (hde : d = true → e = true)
    (hef : e = true → f = true) (hfg : f = true → g = true)
    (hgh : g = true → h = true) (hhi : h = true → i = true)
    (hia : i = true → a = true) :
    (a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true ∧ f = true ∧ g = true ∧ h = true ∧ i = true) ∨
    (a = false ∧ b = false ∧ c = false ∧ d = false ∧ e = false ∧ f = false ∧ g = false ∧ h = false ∧ i = false) := by
  cases ha : a
  · right
    have hnot : a ≠ true := by simp [ha]
    have ni : i ≠ true := fun hi => hnot (hia hi)
    have nh : h ≠ true := fun hh => ni (hhi hh)
    have ng : g ≠ true := fun hg => nh (hgh hg)
    have nf : f ≠ true := fun hf => ng (hfg hf)
    have ne : e ≠ true := fun he => nf (hef he)
    have nd : d ≠ true := fun hd => ne (hde hd)
    have nc : c ≠ true := fun hc => nd (hcd hc)
    have nb : b ≠ true := fun hb => nc (hbc hb)
    exact ⟨rfl, Bool.eq_false_iff.mpr nb, Bool.eq_false_iff.mpr nc, Bool.eq_false_iff.mpr nd,
      Bool.eq_false_iff.mpr ne, Bool.eq_false_iff.mpr nf, Bool.eq_false_iff.mpr ng,
      Bool.eq_false_iff.mpr nh, Bool.eq_false_iff.mpr ni⟩
  · left
    exact ⟨rfl, hab ha, hbc (hab ha), hcd (hbc (hab ha)), hde (hcd (hbc (hab ha))),
      hef (hde (hcd (hbc (hab ha)))), hfg (hef (hde (hcd (hbc (hab ha))))),
      hgh (hfg (hef (hde (hcd (hbc (hab ha)))))), hhi (hgh (hfg (hef (hde (hcd (hbc (hab ha)))))))⟩

lemma equality (c : Fin 21 → Bool) : (pairs c).card = 12 ↔
    ((∀ s : Fin 21, (line s ∩ tri).card = 1 → c s = true) ∨
     (∀ s : Fin 21, (line s ∩ tri).card = 1 → c s = false)) := by
  constructor
  · intro hc
    have hset : fixed = pairs c := Finset.eq_of_subset_of_card_le (fixed_subset c) (by rw [hc, fixed_card])
    have himp : ∀ e ∈ cycle, c e.1 = true → c e.2 = true := by
      intro e he htrue
      by_contra hfalse
      have hf : c e.2 = false := Bool.eq_false_iff.mpr hfalse
      have hs := cycle_spec e he
      have hcross : cross e.1 e.2 (c e.1) (c e.2) := by rw [htrue, hf]; exact hs.2.2.2
      rcases lt_or_gt_of_ne hs.1 with hlt | hgt
      · have hm : e ∈ pairs c := Finset.mem_filter.mpr ⟨Finset.mem_univ e, hlt, hcross⟩
        exact hs.2.1 (hset.symm ▸ hm)
      · have hm : (e.2, e.1) ∈ pairs c := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hgt, (cross_symm _ _ _ _).mp hcross⟩
        exact hs.2.2.1 (hset.symm ▸ hm)
    have hall := constant_on_cycle (c 2) (c 5) (c 6) (c 9) (c 17) (c 18) (c 19) (c 20) (c 8)
      (himp (2,5) (by decide)) (himp (5,6) (by decide)) (himp (6,9) (by decide))
      (himp (9,17) (by decide)) (himp (17,18) (by decide)) (himp (18,19) (by decide))
      (himp (19,20) (by decide)) (himp (20,8) (by decide)) (himp (8,2) (by decide))
    simp only [single_spec]
    rcases hall with ht | hf
    · left
      simpa only [single, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] using
        And.intro ht.1 (And.intro ht.2.1 (And.intro ht.2.2.1
          (And.intro ht.2.2.2.2.2.2.2.2 (And.intro ht.2.2.2.1
            (And.intro ht.2.2.2.2.1 (And.intro ht.2.2.2.2.2.1
              (And.intro ht.2.2.2.2.2.2.1 ht.2.2.2.2.2.2.2.1)))))))
    · right
      simpa only [single, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq] using
        And.intro hf.1 (And.intro hf.2.1 (And.intro hf.2.2.1
          (And.intro hf.2.2.2.2.2.2.2.2 (And.intro hf.2.2.2.1
            (And.intro hf.2.2.2.2.1 (And.intro hf.2.2.2.2.2.1
              (And.intro hf.2.2.2.2.2.2.1 hf.2.2.2.2.2.2.2.1)))))))
  · rintro (ht | hf)
    · have hp := pairs_congr c (fun _ => true) (fun s hs => ht s ((single_spec s).mpr hs))
      rw [hp, uniform_spec, fixed_card]
    · have hp := pairs_congr c (fun _ => false) (fun s hs => hf s ((single_spec s).mpr hs))
      rw [hp, uniform_spec, fixed_card]

lemma empty_no_conflict (B : Fin 21 → Fin 21 → Finset (Fin 21))
    (hB : ∀ s p, B s p ⊆ tri) (s t : Fin 21) (hs : line s ∩ tri = ∅) :
    ¬ ((∃ p ∈ line s \ line t, (B s p ∩ line t).Nonempty) ∧
       (∃ p ∈ line t \ line s, (B t p ∩ line s).Nonempty)) := by
  rintro ⟨_, p, _, v, hv⟩
  have hmem : v ∈ line s ∩ tri := Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hv).2, hB t p (Finset.mem_inter.mp hv).1⟩
  rw [hs] at hmem
  exact Finset.notMem_empty v hmem

end PEqualNP.Outside.L_meta_1561

theorem PEqualNP.Outside.L_meta_1561 : ∀ L : Fin 21 → Finset (Fin 21), (∀ t : Fin 21, L t = {t, t + 1, t + 4, t + 14, t + 16}) →
    ∀ B : (Fin 21 → Bool) → Fin 21 → Fin 21 → Finset (Fin 21),
    (∀ (c : Fin 21 → Bool) (s p : Fin 21), B c s p =
      if p ∈ ({0, 1, 2} : Finset (Fin 21)) then (∅ : Finset (Fin 21))
      else if (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 then ({0, 1, 2} : Finset (Fin 21)) \ L s
      else if (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 then
        (if c s then (L s ∩ ({0, 1, 2} : Finset (Fin 21))).image (fun v : Fin 21 => if v = 2 then 0 else v + 1)
         else (L s ∩ ({0, 1, 2} : Finset (Fin 21))).image (fun v : Fin 21 => if v = 0 then 2 else v - 1))
      else {0}) →
    (∀ s s' : Fin 21, s ≠ s' → (((∃ p ∈ L s \ L s', ((B (fun _ => true)) s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, ((B (fun _ => true)) s' p ∩ L s).Nonempty)) ↔
      (((L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (L s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2) ∨
       ((L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (L s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 ∧ L s' ∩ ({0, 1, 2} : Finset (Fin 21)) ∩ L s = ∅) ∨
       ((L s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 ∧ L s ∩ ({0, 1, 2} : Finset (Fin 21)) ∩ L s' = ∅)))) ∧
    ((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ L e.1 \ L e.2, ((B (fun _ => true)) e.1 p ∩ L e.2).Nonempty) ∧ (∃ p ∈ L e.2 \ L e.1, ((B (fun _ => true)) e.2 p ∩ L e.1).Nonempty)))).card = 12 ∧
    (∀ B' : Fin 21 → Fin 21 → Finset (Fin 21), (∀ s p : Fin 21, B' s p ⊆ ({0, 1, 2} : Finset (Fin 21))) →
      ∀ s s' : Fin 21, L s ∩ ({0, 1, 2} : Finset (Fin 21)) = ∅ → ¬ ((∃ p ∈ L s \ L s', (B' s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B' s' p ∩ L s).Nonempty))) ∧
    (∀ c : Fin 21 → Bool, 12 ≤ ((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ L e.1 \ L e.2, ((B c) e.1 p ∩ L e.2).Nonempty) ∧ (∃ p ∈ L e.2 \ L e.1, ((B c) e.2 p ∩ L e.1).Nonempty)))).card ∧
      (((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ L e.1 \ L e.2, ((B c) e.1 p ∩ L e.2).Nonempty) ∧ (∃ p ∈ L e.2 \ L e.1, ((B c) e.2 p ∩ L e.1).Nonempty)))).card = 12 ↔
        ((∀ s : Fin 21, (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → c s = true) ∨ (∀ s : Fin 21, (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → c s = false)))) := by
  intro L hL B hB
  have hLeq : L = PEqualNP.Outside.L_meta_1561.line := funext hL
  subst L
  have hBeq : B = fun c s p => PEqualNP.Outside.L_meta_1561.base (c s) s p := by
    funext c s p
    exact hB c s p
  subst B
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_1561.true_spec
  · exact (congrArg Finset.card (PEqualNP.Outside.L_meta_1561.uniform_spec true)).trans
      PEqualNP.Outside.L_meta_1561.fixed_card
  · exact PEqualNP.Outside.L_meta_1561.empty_no_conflict
  · intro c
    exact ⟨PEqualNP.Outside.L_meta_1561.lower c, PEqualNP.Outside.L_meta_1561.equality c⟩
