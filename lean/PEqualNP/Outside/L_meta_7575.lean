import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7575

def incB (p l : Fin 13) : Bool :=
  let d := (p.val + 13 - l.val) % 13
  d == 0 || d == 1 || d == 3 || d == 9

lemma mem_singerLines3_iff_incB (p l : Fin 13) :
    p ∈ PEqualNP.HeptadCover.singerLines3 l ↔ incB p l = true := by
  unfold PEqualNP.HeptadCover.singerLines3 incB
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Bool.or_eq_true, beq_iff_eq]
  tauto

def IsColl (f g : Equiv.Perm (Fin 13)) : Prop :=
  ∀ p l : Fin 13,
    f p ∈ PEqualNP.HeptadCover.singerLines3 (g l) ↔
      p ∈ PEqualNP.HeptadCover.singerLines3 l

lemma isColl_refl : IsColl (Equiv.refl (Fin 13)) (Equiv.refl (Fin 13)) :=
  fun _ _ => Iff.rfl

lemma isColl_trans {f1 g1 f2 g2 : Equiv.Perm (Fin 13)}
    (h1 : IsColl f1 g1) (h2 : IsColl f2 g2) :
    IsColl (f1.trans f2) (g1.trans g2) :=
  fun p l => (h2 (f1 p) (g1 l)).trans (h1 p l)

lemma isColl_of_incB {f g : Equiv.Perm (Fin 13)}
    (h : ∀ p l : Fin 13, incB (f p) (g l) = incB p l) :
    IsColl f g := by
  intro p l
  rw [mem_singerLines3_iff_incB, mem_singerLines3_iff_incB, h p l]

lemma coll_preserves_quadrangle_and_missLines {f g : Equiv.Perm (Fin 13)}
    (h : IsColl f g) (Q : Finset (Fin 13))
    (hQ : PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 Q) :
    PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3
        (Finset.image f.symm Q) ∧
      PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3
        (Finset.image f.symm Q) =
      Finset.image g.symm
        (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 Q) := by
  have hsymm : ∀ q l : Fin 13,
      f.symm q ∈ PEqualNP.HeptadCover.singerLines3 l ↔
        q ∈ PEqualNP.HeptadCover.singerLines3 (g l) := by
    intro q l
    have h1 := h (f.symm q) l
    rw [Equiv.apply_symm_apply] at h1
    exact h1.symm
  constructor
  · constructor
    · rw [Finset.card_image_of_injective Q f.symm.injective]
      exact hQ.1
    · intro l
      have hinter :
          Finset.image f.symm Q ∩ PEqualNP.HeptadCover.singerLines3 l =
            Finset.image f.symm (Q ∩ PEqualNP.HeptadCover.singerLines3 (g l)) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_image]
        constructor
        · rintro ⟨⟨q, hq, rfl⟩, hxl⟩
          exact ⟨q, ⟨hq, (hsymm q l).mp hxl⟩, rfl⟩
        · rintro ⟨q, ⟨hq, hqg⟩, rfl⟩
          exact ⟨⟨q, hq, rfl⟩, (hsymm q l).mpr hqg⟩
      rw [hinter, Finset.card_image_of_injective _ f.symm.injective]
      exact hQ.2 (g l)
  · ext l
    simp only [PEqualNP.HeptadCover.missLines, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.disjoint_left]
    constructor
    · intro hdisj
      refine ⟨g l, ?_, Equiv.symm_apply_apply g l⟩
      intro q hqgl hqQ
      exact hdisj ((hsymm q l).mpr hqgl) ⟨q, hqQ, rfl⟩
    · rintro ⟨m, hdisj, rfl⟩ x hxl ⟨q, hqQ, rfl⟩
      have hqg : q ∈ PEqualNP.HeptadCover.singerLines3 m := by
        have := (hsymm q (g.symm m)).mp hxl
        rwa [Equiv.apply_symm_apply] at this
      exact hdisj hqg hqQ

def shiftFun (c x : Fin 13) : Fin 13 :=
  ⟨(x.val + 13 - c.val) % 13, Nat.mod_lt _ (by decide)⟩

def shiftInvFun (c x : Fin 13) : Fin 13 :=
  ⟨(x.val + c.val) % 13, Nat.mod_lt _ (by decide)⟩

def shiftPerm (c : Fin 13) : Equiv.Perm (Fin 13) where
  toFun := shiftFun c
  invFun := shiftInvFun c
  left_inv x := by
    apply Fin.ext
    change ((x.val + 13 - c.val) % 13 + c.val) % 13 = x.val
    omega
  right_inv x := by
    apply Fin.ext
    change ((x.val + c.val) % 13 + 13 - c.val) % 13 = x.val
    omega

lemma shiftPerm_self (c : Fin 13) : shiftPerm c c = 0 := by
  apply Fin.ext
  change (c.val + 13 - c.val) % 13 = 0
  omega

lemma isColl_shiftPerm (c : Fin 13) : IsColl (shiftPerm c) (shiftPerm c) := by
  apply isColl_of_incB
  intro p l
  unfold incB
  have hmod :
      ((shiftPerm c p).val + 13 - (shiftPerm c l).val) % 13 = (p.val + 13 - l.val) % 13 := by
    change ((p.val + 13 - c.val) % 13 + 13 - (l.val + 13 - c.val) % 13) % 13 =
      (p.val + 13 - l.val) % 13
    omega
  rw [hmod]

def mul3Fun (x : Fin 13) : Fin 13 :=
  ⟨(3 * x.val) % 13, Nat.mod_lt _ (by decide)⟩

def mul9Fun (x : Fin 13) : Fin 13 :=
  ⟨(9 * x.val) % 13, Nat.mod_lt _ (by decide)⟩

def mul3Perm : Equiv.Perm (Fin 13) where
  toFun := mul3Fun
  invFun := mul9Fun
  left_inv := by decide
  right_inv := by decide

lemma isColl_mul3Perm : IsColl mul3Perm mul3Perm :=
  isColl_of_incB (by decide)

def tauPFun (x : Fin 13) : Fin 13 :=
  match x.val with
  | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 5 | 4 => 1 | 5 => 3 | 6 => 6
  | 7 => 9 | 8 => 12 | 9 => 7 | 10 => 10 | 11 => 11 | 12 => 8 | _ => 0

def tauLFun (x : Fin 13) : Fin 13 :=
  match x.val with
  | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 5 | 4 => 0 | 5 => 3 | 6 => 6
  | 7 => 9 | 8 => 11 | 9 => 7 | 10 => 10 | 11 => 8 | 12 => 12 | _ => 0

def tauP : Equiv.Perm (Fin 13) where
  toFun := tauPFun
  invFun := tauPFun
  left_inv := by decide
  right_inv := by decide

def tauL : Equiv.Perm (Fin 13) where
  toFun := tauLFun
  invFun := tauLFun
  left_inv := by decide
  right_inv := by decide

lemma isColl_tau : IsColl tauP tauL :=
  isColl_of_incB (by decide)

def g1PFun (x : Fin 13) : Fin 13 :=
  match x.val with
  | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 10 | 5 => 6 | 6 => 8
  | 7 => 11 | 8 => 5 | 9 => 9 | 10 => 2 | 11 => 12 | 12 => 7 | _ => 0

def g1LFun (x : Fin 13) : Fin 13 :=
  match x.val with
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 7 | 4 => 10 | 5 => 5 | 6 => 8
  | 7 => 2 | 8 => 9 | 9 => 6 | 10 => 12 | 11 => 11 | 12 => 4 | _ => 0

def g2PFun (x : Fin 13) : Fin 13 :=
  match x.val with
  | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 9 | 4 => 5 | 5 => 7 | 6 => 10
  | 7 => 4 | 8 => 8 | 9 => 1 | 10 => 11 | 11 => 6 | 12 => 12 | _ => 0

def g2LFun (x : Fin 13) : Fin 13 :=
  match x.val with
  | 0 => 0 | 1 => 2 | 2 => 6 | 3 => 9 | 4 => 4 | 5 => 7 | 6 => 1
  | 7 => 8 | 8 => 5 | 9 => 11 | 10 => 10 | 11 => 3 | 12 => 12 | _ => 0

def g3PFun (x : Fin 13) : Fin 13 :=
  match x.val with
  | 0 => 0 | 1 => 1 | 2 => 8 | 3 => 3 | 4 => 5 | 5 => 7 | 6 => 11
  | 7 => 4 | 8 => 12 | 9 => 9 | 10 => 6 | 11 => 10 | 12 => 2 | _ => 0

def g3LFun (x : Fin 13) : Fin 13 :=
  match x.val with
  | 0 => 0 | 1 => 5 | 2 => 7 | 3 => 2 | 4 => 4 | 5 => 11 | 6 => 8
  | 7 => 3 | 8 => 9 | 9 => 6 | 10 => 10 | 11 => 1 | 12 => 12 | _ => 0

def g1P : Equiv.Perm (Fin 13) where
  toFun := g1PFun
  invFun x := g1PFun (g1PFun x)
  left_inv := by decide
  right_inv := by decide

def g1L : Equiv.Perm (Fin 13) where
  toFun := g1LFun
  invFun x := g1LFun (g1LFun x)
  left_inv := by decide
  right_inv := by decide

def g2P : Equiv.Perm (Fin 13) where
  toFun := g2PFun
  invFun x := g2PFun (g2PFun x)
  left_inv := by decide
  right_inv := by decide

def g2L : Equiv.Perm (Fin 13) where
  toFun := g2LFun
  invFun x := g2LFun (g2LFun x)
  left_inv := by decide
  right_inv := by decide

def g3P : Equiv.Perm (Fin 13) where
  toFun := g3PFun
  invFun x := g3PFun (g3PFun x)
  left_inv := by decide
  right_inv := by decide

def g3L : Equiv.Perm (Fin 13) where
  toFun := g3LFun
  invFun x := g3LFun (g3LFun x)
  left_inv := by decide
  right_inv := by decide

lemma isColl_g1 : IsColl g1P g1L :=
  isColl_of_incB (by decide)

lemma isColl_g2 : IsColl g2P g2L :=
  isColl_of_incB (by decide)

lemma isColl_g3 : IsColl g3P g3L :=
  isColl_of_incB (by decide)

def stab0P (l : Fin 13) : Equiv.Perm (Fin 13) :=
  match l.val with
  | 4 => tauP
  | 10 => mul3Perm.trans tauP
  | 12 => (mul3Perm.trans mul3Perm).trans tauP
  | _ => Equiv.refl (Fin 13)

def stab0L (l : Fin 13) : Equiv.Perm (Fin 13) :=
  match l.val with
  | 4 => tauL
  | 10 => mul3Perm.trans tauL
  | 12 => (mul3Perm.trans mul3Perm).trans tauL
  | _ => Equiv.refl (Fin 13)

lemma isColl_stab0 (l : Fin 13) : IsColl (stab0P l) (stab0L l) := by
  unfold stab0P stab0L
  split
  · exact isColl_tau
  · exact isColl_trans isColl_mul3Perm isColl_tau
  · exact isColl_trans (isColl_trans isColl_mul3Perm isColl_mul3Perm) isColl_tau
  · exact isColl_refl

lemma stab0_maps (l : Fin 13) (h : incB 0 l = true) :
    stab0P l 0 = 0 ∧ stab0L l l = 0 := by
  revert l h
  decide

def pow3 (e : Equiv.Perm (Fin 13)) (k : Fin 3) : Equiv.Perm (Fin 13) :=
  match k.val with
  | 0 => Equiv.refl (Fin 13)
  | 1 => e
  | _ => e.trans e

def pow3Fun (f : Fin 13 → Fin 13) (k : Fin 3) (x : Fin 13) : Fin 13 :=
  match k.val with
  | 0 => x
  | 1 => f x
  | _ => f (f x)

lemma pow3_apply (e : Equiv.Perm (Fin 13)) (k : Fin 3) (x : Fin 13) :
    pow3 e k x = pow3Fun e k x := by
  fin_cases k <;> rfl

lemma isColl_pow3 {f g : Equiv.Perm (Fin 13)} (h : IsColl f g) (k : Fin 3) :
    IsColl (pow3 f k) (pow3 g k) := by
  fin_cases k
  · exact isColl_refl
  · exact h
  · exact isColl_trans h h

def sylowP (a b c : Fin 3) : Equiv.Perm (Fin 13) :=
  ((pow3 g1P a).trans (pow3 g2P b)).trans (pow3 g3P c)

def sylowL (a b c : Fin 3) : Equiv.Perm (Fin 13) :=
  ((pow3 g1L a).trans (pow3 g2L b)).trans (pow3 g3L c)

def sylowPFun (a b c : Fin 3) (x : Fin 13) : Fin 13 :=
  pow3Fun g3PFun c (pow3Fun g2PFun b (pow3Fun g1PFun a x))

def sylowLFun (a b c : Fin 3) (x : Fin 13) : Fin 13 :=
  pow3Fun g3LFun c (pow3Fun g2LFun b (pow3Fun g1LFun a x))

lemma sylowP_apply (a b c : Fin 3) (x : Fin 13) :
    sylowP a b c x = sylowPFun a b c x := by
  simp only [sylowP, Equiv.trans_apply, pow3_apply, sylowPFun]
  rfl

lemma sylowL_apply (a b c : Fin 3) (x : Fin 13) :
    sylowL a b c x = sylowLFun a b c x := by
  simp only [sylowL, Equiv.trans_apply, pow3_apply, sylowLFun]
  rfl

lemma isColl_sylow (a b c : Fin 3) : IsColl (sylowP a b c) (sylowL a b c) :=
  isColl_trans (isColl_trans (isColl_pow3 isColl_g1 a) (isColl_pow3 isColl_g2 b))
    (isColl_pow3 isColl_g3 c)

lemma sylow_fixes_zero (a b c : Fin 3) :
    sylowP a b c 0 = 0 ∧ sylowL a b c 0 = 0 := by
  rw [sylowP_apply, sylowL_apply]
  revert a b c
  decide

lemma sylowFun_covers :
    ∀ p l : Fin 13, incB p l = true → (p, l) ≠ (0, 0) →
      ∃ a b c : Fin 3,
        (sylowPFun a b c p, sylowLFun a b c l) ∈
          [((0 : Fin 13), (4 : Fin 13)), ((1 : Fin 13), (0 : Fin 13)),
           ((1 : Fin 13), (1 : Fin 13)), ((2 : Fin 13), (1 : Fin 13)),
           ((2 : Fin 13), (12 : Fin 13))] := by
  decide

lemma main_result :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
    ∀ (x2 x3 x4 x5 : Fin (13 : ℕ)),
      x2 ∈ x1 x3 → x4 ∈ x1 x5 → (x2, x3) ≠ (x4, x5) →
      ∃ (x9 : Equiv.Perm (Fin (13 : ℕ))) (x10 : Equiv.Perm (Fin (13 : ℕ))),
        x9 x2 = (0 : Fin (13 : ℕ)) ∧
        x10 x3 = (0 : Fin (13 : ℕ)) ∧
        (x9 x4, x10 x5) ∈
          [((0 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ))),
           ((1 : Fin (13 : ℕ)), (0 : Fin (13 : ℕ))),
           ((1 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ))),
           ((2 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ))),
           ((2 : Fin (13 : ℕ)), (12 : Fin (13 : ℕ)))] ∧
        (∀ (x11 x12 : Fin (13 : ℕ)), x9 x11 ∈ x1 (x10 x12) ↔ x11 ∈ x1 x12) ∧
        ∀ (x11 : Finset (Fin (13 : ℕ))),
          PEqualNP.HeptadCover.IsQuadrangle x1 x11 →
          PEqualNP.HeptadCover.IsQuadrangle x1 (Finset.image (⇑(Equiv.symm x9)) x11) ∧
          PEqualNP.HeptadCover.missLines x1 (Finset.image (⇑(Equiv.symm x9)) x11) =
            Finset.image (⇑(Equiv.symm x10)) (PEqualNP.HeptadCover.missLines x1 x11) := by
  dsimp only
  intro x2 x3 x4 x5 h23 h45 hne
  let s := shiftPerm x2
  have hs : IsColl s s := isColl_shiftPerm x2
  let l3' := s x3
  have h03' : (0 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 l3' := by
    rw [← shiftPerm_self x2]
    exact (hs x2 x3).mpr h23
  have h03'B : incB 0 l3' = true := (mem_singerLines3_iff_incB 0 l3').mp h03'
  let f1 := s.trans (stab0P l3')
  let g1 := s.trans (stab0L l3')
  have hfg1 : IsColl f1 g1 := isColl_trans hs (isColl_stab0 l3')
  have hstab := stab0_maps l3' h03'B
  have hf1_x2 : f1 x2 = 0 := by
    simp only [f1, Equiv.trans_apply, s, shiftPerm_self, hstab.1]
  have hg1_x3 : g1 x3 = 0 := by
    simp only [g1, Equiv.trans_apply, l3', s, hstab.2]
  have h45' : f1 x4 ∈ PEqualNP.HeptadCover.singerLines3 (g1 x5) :=
    (hfg1 x4 x5).mpr h45
  have h45'B : incB (f1 x4) (g1 x5) = true :=
    (mem_singerLines3_iff_incB (f1 x4) (g1 x5)).mp h45'
  have hne' : (f1 x4, g1 x5) ≠ (0, 0) := by
    intro heq
    have h4 : f1 x4 = 0 := congrArg Prod.fst heq
    have h5 : g1 x5 = 0 := congrArg Prod.snd heq
    have hx24 : x2 = x4 := f1.injective (hf1_x2.trans h4.symm)
    have hx35 : x3 = x5 := g1.injective (hg1_x3.trans h5.symm)
    exact hne (Prod.ext hx24 hx35)
  rcases sylowFun_covers (f1 x4) (g1 x5) h45'B hne' with ⟨a, b, c, hmem⟩
  let x9 := f1.trans (sylowP a b c)
  let x10 := g1.trans (sylowL a b c)
  have hcoll : IsColl x9 x10 := isColl_trans hfg1 (isColl_sylow a b c)
  have hfix := sylow_fixes_zero a b c
  refine ⟨x9, x10, ?_, ?_, ?_, hcoll, fun Q hQ => coll_preserves_quadrangle_and_missLines hcoll Q hQ⟩
  · simp only [x9, Equiv.trans_apply, hf1_x2, hfix.1]
  · simp only [x10, Equiv.trans_apply, hg1_x3, hfix.2]
  · simp only [x9, x10, Equiv.trans_apply, sylowP_apply, sylowL_apply]
    exact hmem

end PEqualNP.Outside.L_meta_7575

theorem PEqualNP.Outside.L_meta_7575 :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; ∀ (x2 x3 x4 x5 : Fin (13 : ℕ)), x2 ∈ x1 x3 → x4 ∈ x1 x5 → (x2, x3) ≠ (x4, x5) → ∃ (x9 : Equiv.Perm (Fin (13 : ℕ))) (x10 : Equiv.Perm (Fin (13 : ℕ))), x9 x2 = (0 : Fin (13 : ℕ)) ∧ x10 x3 = (0 : Fin (13 : ℕ)) ∧ (x9 x4, x10 x5) ∈ [((0 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ))), ((1 : Fin (13 : ℕ)), (0 : Fin (13 : ℕ))), ((1 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ))), ((2 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ))), ((2 : Fin (13 : ℕ)), (12 : Fin (13 : ℕ)))] ∧ (∀ (x11 x12 : Fin (13 : ℕ)), x9 x11 ∈ x1 (x10 x12) ↔ x11 ∈ x1 x12) ∧ ∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle x1 x11 → PEqualNP.HeptadCover.IsQuadrangle x1 (Finset.image (⇑(Equiv.symm x9)) x11) ∧ PEqualNP.HeptadCover.missLines x1 (Finset.image (⇑(Equiv.symm x9)) x11) = Finset.image (⇑(Equiv.symm x10)) (PEqualNP.HeptadCover.missLines x1 x11) :=
  PEqualNP.Outside.L_meta_7575.main_result
