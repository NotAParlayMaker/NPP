import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_533_aux

private lemma hall_side {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n → Bool) (hc : ∀ u v : Fin n, G.Adj u v → c u ≠ c v)
    (T : Finset (Fin n))
    (hT : ∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T)
    (hmin : ∀ T' : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → u ∈ T' ∨ v ∈ T') → T.card ≤ T'.card)
    (b : Bool) :
    ∃ f : { u : Fin n // u ∈ T.filter (fun w => c w = b) } → Fin n,
      Function.Injective f ∧
      ∀ x, G.Adj x.1 (f x) ∧ c (f x) ≠ b ∧ f x ∉ T := by
  let A : Finset (Fin n) := T.filter (fun w => c w = b)
  let nbr : { u : Fin n // u ∈ A } → Finset (Fin n) :=
    fun x => Finset.univ.filter (fun v => G.Adj x.1 v ∧ v ∉ T)
  have hhall : ∀ s : Finset { u : Fin n // u ∈ A }, s.card ≤ (s.biUnion nbr).card := by
    intro s
    let S : Finset (Fin n) := s.image Subtype.val
    let U : Finset (Fin n) := s.biUnion nbr
    have hScard : S.card = s.card := Finset.card_image_of_injective s Subtype.val_injective
    have hST : S ⊆ T := by
      intro u hu
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp x.2).1
    have hSc : ∀ u ∈ S, c u = b := by
      intro u hu
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp x.2).2
    have hcov : ∀ u v : Fin n, G.Adj u v → u ∈ (T \ S) ∪ U ∨ v ∈ (T \ S) ∪ U := by
      intro u v huv
      by_cases huS : u ∈ S
      · by_cases hvT : v ∈ T
        · right
          apply Finset.mem_union_left
          refine Finset.mem_sdiff.mpr ⟨hvT, fun hvS => ?_⟩
          exact hc u v huv ((hSc u huS).trans (hSc v hvS).symm)
        · right
          apply Finset.mem_union_right
          obtain ⟨x, hxs, hxu⟩ := Finset.mem_image.mp huS
          refine Finset.mem_biUnion.mpr ⟨x, hxs, ?_⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hxu.symm ▸ huv, hvT⟩
      · by_cases huT : u ∈ T
        · left
          exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨huT, huS⟩)
        · have hvT : v ∈ T := (hT u v huv).resolve_left huT
          by_cases hvS : v ∈ S
          · left
            apply Finset.mem_union_right
            obtain ⟨y, hys, hyv⟩ := Finset.mem_image.mp hvS
            refine Finset.mem_biUnion.mpr ⟨y, hys, ?_⟩
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hyv.symm ▸ huv.symm, huT⟩
          · right
            exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvT, hvS⟩)
    have hle1 : T.card ≤ ((T \ S) ∪ U).card := hmin ((T \ S) ∪ U) hcov
    have hle2 : ((T \ S) ∪ U).card ≤ (T \ S).card + U.card := Finset.card_union_le _ _
    have hsum : (T \ S).card + S.card = T.card := Finset.card_sdiff_add_card_eq_card hST
    have hU : U.card = (s.biUnion nbr).card := rfl
    omega
  obtain ⟨f, hfinj, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective nbr).mp hhall
  refine ⟨f, hfinj, fun x => ?_⟩
  have hx := Finset.mem_filter.mp (hfmem x)
  have hcx : c x.1 = b := (Finset.mem_filter.mp x.2).2
  exact ⟨hx.2.1, fun hcf => hc x.1 (f x) hx.2.1 (hcx.trans hcf.symm), hx.2.2⟩

private lemma side_inj {n : ℕ} (c : Fin n → Bool) (T : Finset (Fin n)) (b : Bool)
    (f : { u : Fin n // u ∈ T.filter (fun w => c w = b) } → Fin n)
    (hfc : ∀ x, c (f x) ≠ b) :
    Function.Injective (fun x => s(x.1, f x)) := by
  intro x y hxy
  rcases Sym2.eq_iff.mp hxy with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Subtype.ext h1
  · exfalso
    have hcx : c x.1 = b := (Finset.mem_filter.mp x.2).2
    exact hfc y (h1 ▸ hcx)

private lemma side_disjoint {n : ℕ} (c : Fin n → Bool) (T : Finset (Fin n)) (b : Bool)
    (f : { u : Fin n // u ∈ T.filter (fun w => c w = b) } → Fin n)
    (hfinj : Function.Injective f) (hfc : ∀ x, c (f x) ≠ b)
    (x y : { u : Fin n // u ∈ T.filter (fun w => c w = b) })
    (hne : s(x.1, f x) ≠ s(y.1, f y)) (v : Fin n)
    (hvx : v ∈ s(x.1, f x)) (hvy : v ∈ s(y.1, f y)) : False := by
  have hcx : c x.1 = b := (Finset.mem_filter.mp x.2).2
  have hcy : c y.1 = b := (Finset.mem_filter.mp y.2).2
  rcases Sym2.mem_iff.mp hvx with rfl | rfl <;> rcases Sym2.mem_iff.mp hvy with h | h
  · exact hne (congrArg (fun z => s(z.1, f z)) (Subtype.ext h))
  · exact hfc y (h ▸ hcx)
  · exact hfc x (h.symm ▸ hcy)
  · exact hne (congrArg (fun z => s(z.1, f z)) (hfinj h))

private lemma cross_disjoint {n : ℕ} (c : Fin n → Bool) (T : Finset (Fin n))
    (fF : { u : Fin n // u ∈ T.filter (fun w => c w = false) } → Fin n)
    (fT : { u : Fin n // u ∈ T.filter (fun w => c w = true) } → Fin n)
    (hF : ∀ x, c (fF x) ≠ false ∧ fF x ∉ T)
    (hT : ∀ y, c (fT y) ≠ true ∧ fT y ∉ T)
    (x : { u : Fin n // u ∈ T.filter (fun w => c w = false) })
    (y : { u : Fin n // u ∈ T.filter (fun w => c w = true) })
    (v : Fin n) (hvx : v ∈ s(x.1, fF x)) (hvy : v ∈ s(y.1, fT y)) : False := by
  have hxT : x.1 ∈ T := (Finset.mem_filter.mp x.2).1
  have hcx : c x.1 = false := (Finset.mem_filter.mp x.2).2
  have hyT : y.1 ∈ T := (Finset.mem_filter.mp y.2).1
  have hcy : c y.1 = true := (Finset.mem_filter.mp y.2).2
  rcases Sym2.mem_iff.mp hvx with rfl | rfl <;> rcases Sym2.mem_iff.mp hvy with h | h
  · rw [h] at hcx; rw [hcx] at hcy; exact Bool.false_ne_true hcy
  · exact (hT y).2 (h ▸ hxT)
  · exact (hF x).2 (h.symm ▸ hyT)
  · have hcf : c (fF x) = true := by cases h1 : c (fF x) with | false => exact absurd h1 (hF x).1 | true => rfl
    exact (hT y).1 (h ▸ hcf)

end PEqualNP.Outside.L_meta_533_aux

theorem PEqualNP.Outside.L_meta_533 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∃ c : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → c u ≠ c v) → ∃ (M : Finset (Sym2 (Fin n))) (T : Finset (Fin n)), (∀ e ∈ M, e ∈ G.edgeFinset) ∧ (∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v : Fin n, v ∈ e → v ∉ f) ∧ (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card = M.card := by
  intro n G _ ⟨c, hc⟩
  let VCs : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun T => ∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T)
  have hne : VCs.Nonempty := ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u _ _ => Or.inl (Finset.mem_univ u)⟩⟩
  obtain ⟨T, hTV, hTmin⟩ := Finset.exists_min_image VCs Finset.card hne
  have hTcov : ∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T := (Finset.mem_filter.mp hTV).2
  have hmin : ∀ T' : Finset (Fin n),
      (∀ u v : Fin n, G.Adj u v → u ∈ T' ∨ v ∈ T') → T.card ≤ T'.card := fun T' hT' =>
    hTmin T' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT'⟩)
  obtain ⟨fF, hfFinj, hfF⟩ := PEqualNP.Outside.L_meta_533_aux.hall_side G c hc T hTcov hmin false
  obtain ⟨fT, hfTinj, hfT⟩ := PEqualNP.Outside.L_meta_533_aux.hall_side G c hc T hTcov hmin true
  let TF : Finset (Fin n) := T.filter (fun w => c w = false)
  let TT : Finset (Fin n) := T.filter (fun w => c w = true)
  let MF : Finset (Sym2 (Fin n)) := Finset.univ.image (fun x : { u : Fin n // u ∈ TF } => s(x.1, fF x))
  let MT : Finset (Sym2 (Fin n)) := Finset.univ.image (fun y : { u : Fin n // u ∈ TT } => s(y.1, fT y))
  refine ⟨MF ∪ MT, T, ?_, ?_, hTcov, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
      exact G.mem_edgeFinset.mpr (hfF x).1
    · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp h
      exact G.mem_edgeFinset.mpr (hfT y).1
  · intro e he f hf hne v hve hvf
    rcases Finset.mem_union.mp he with heF | heT <;> rcases Finset.mem_union.mp hf with hfF' | hfT'
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp heF
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hfF'
      exact PEqualNP.Outside.L_meta_533_aux.side_disjoint c T false fF hfFinj (fun z => (hfF z).2.1) x y hne v hve hvf
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp heF
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hfT'
      exact PEqualNP.Outside.L_meta_533_aux.cross_disjoint c T fF fT (fun z => (hfF z).2) (fun z => (hfT z).2) x y v hve hvf
    · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp heT
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hfF'
      exact PEqualNP.Outside.L_meta_533_aux.cross_disjoint c T fF fT (fun z => (hfF z).2) (fun z => (hfT z).2) x y v hvf hve
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp heT
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hfT'
      exact PEqualNP.Outside.L_meta_533_aux.side_disjoint c T true fT hfTinj (fun z => (hfT z).2.1) x y hne v hve hvf
  · have hMF_MT : Disjoint MF MT := by
      rw [Finset.disjoint_left]
      intro e heF heT
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp heF
      obtain ⟨y, _, hxy⟩ := Finset.mem_image.mp heT
      have hmem : x.1 ∈ s(y.1, fT y) := hxy ▸ Sym2.mem_mk_left x.1 (fF x)
      exact PEqualNP.Outside.L_meta_533_aux.cross_disjoint c T fF fT (fun z => (hfF z).2) (fun z => (hfT z).2) x y x.1 (Sym2.mem_mk_left _ _) hmem
    have hMFcard : MF.card = TF.card := by
      rw [Finset.card_image_of_injective _ (PEqualNP.Outside.L_meta_533_aux.side_inj c T false fF (fun z => (hfF z).2.1))]
      simp
    have hMTcard : MT.card = TT.card := by
      rw [Finset.card_image_of_injective _ (PEqualNP.Outside.L_meta_533_aux.side_inj c T true fT (fun z => (hfT z).2.1))]
      simp
    have hTF_TT : Disjoint TF TT := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have hc1 : c w = false := (Finset.mem_filter.mp h1).2
      have hc2 : c w = true := (Finset.mem_filter.mp h2).2
      rw [hc1] at hc2
      exact Bool.false_ne_true hc2
    have hTunion : TF ∪ TT = T := by
      ext w
      simp only [TF, TT, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        cases hc' : c w with
        | false => exact Or.inl ⟨h, rfl⟩
        | true => exact Or.inr ⟨h, rfl⟩
    rw [Finset.card_union_of_disjoint hMF_MT, hMFcard, hMTcard, ← Finset.card_union_of_disjoint hTF_TT, hTunion]
