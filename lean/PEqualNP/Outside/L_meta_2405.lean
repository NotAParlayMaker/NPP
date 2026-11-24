import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2405

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

def reach {α : Type} (L : List (α × α)) : α → α → Prop :=
  Relation.ReflTransGen (fun x y => (x, y) ∈ L ∨ (y, x) ∈ L)

lemma reach_symm {α : Type} {L : List (α × α)} {x y : α} (h : reach L x y) : reach L y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih =>
    refine Relation.ReflTransGen.trans ?_ ih
    rcases hxy with h1 | h2
    · exact Relation.ReflTransGen.single (Or.inr h1)
    · exact Relation.ReflTransGen.single (Or.inl h2)

lemma reach_mono {α : Type} {L1 L2 : List (α × α)} (hsub : ∀ e ∈ L1, e ∈ L2) {x y : α}
    (h : reach L1 x y) : reach L2 x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hxy ih =>
    refine Relation.ReflTransGen.tail ih ?_
    rcases hxy with h1 | h2
    · exact Or.inl (hsub _ h1)
    · exact Or.inr (hsub _ h2)

noncomputable def cls {α : Type} (V : Finset α) (L : List (α × α)) (v : α) : Finset α :=
  V.filter (fun w => reach L v w)

noncomputable def comps {α : Type} (V : Finset α) (L : List (α × α)) : Finset (Finset α) :=
  V.image (cls V L)

lemma mem_cls {α : Type} {V : Finset α} {L : List (α × α)} {v w : α} :
    w ∈ cls V L v ↔ w ∈ V ∧ reach L v w := by
  simp [cls]

lemma cls_eq_of_reach {α : Type} {V : Finset α} {L : List (α × α)} {u v : α}
    (h : reach L u v) : cls V L u = cls V L v := by
  ext w
  simp only [mem_cls]
  constructor
  · rintro ⟨hw, huw⟩
    exact ⟨hw, Relation.ReflTransGen.trans (reach_symm h) huw⟩
  · rintro ⟨hw, hvw⟩
    exact ⟨hw, Relation.ReflTransGen.trans h hvw⟩

lemma comps_nil {α : Type} (V : Finset α) : (comps V []).card = V.card := by
  have heq : comps V [] = V.image (fun v => ({v} : Finset α)) := by
    ext c
    simp only [comps, Finset.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v, hv, ?_⟩
      ext w
      simp only [mem_cls, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hvw⟩
        exact (Relation.ReflTransGen.cases_head hvw).elim id (fun ⟨_, hstep, _⟩ => by simp at hstep)
      · rintro rfl
        exact ⟨hv, Relation.ReflTransGen.refl⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v, hv, ?_⟩
      ext w
      simp only [mem_cls, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact ⟨hv, Relation.ReflTransGen.refl⟩
      · rintro ⟨_, hvw⟩
        exact (Relation.ReflTransGen.cases_head hvw).elim id (fun ⟨_, hstep, _⟩ => by simp at hstep)
  rw [heq, Finset.card_image_of_injective _ (fun a b hab => Finset.singleton_injective hab)]

lemma reach_cons_iff {α : Type} {a b : α} {L : List (α × α)} {x y : α} :
    reach ((a, b) :: L) x y ↔
      reach L x y ∨ (reach L x a ∧ reach L b y) ∨ (reach L x b ∧ reach L a y) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      rcases hstep with h1 | h2
      · simp only [List.mem_cons] at h1
        rcases h1 with heq | hin
        · rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
          rcases ih with hL | ⟨hxa, hba⟩ | ⟨hxb, haa⟩
          · exact Or.inr (Or.inl ⟨hL, Relation.ReflTransGen.refl⟩)
          · exact Or.inr (Or.inl ⟨hxa, Relation.ReflTransGen.refl⟩)
          · exact Or.inl hxb
        · have hs : reach L b✝ c✝ := Relation.ReflTransGen.single (Or.inl hin)
          rcases ih with hL | ⟨hxa, hbz⟩ | ⟨hxb, haz⟩
          · exact Or.inl (Relation.ReflTransGen.trans hL hs)
          · exact Or.inr (Or.inl ⟨hxa, Relation.ReflTransGen.trans hbz hs⟩)
          · exact Or.inr (Or.inr ⟨hxb, Relation.ReflTransGen.trans haz hs⟩)
      · simp only [List.mem_cons] at h2
        rcases h2 with heq | hin
        · rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
          rcases ih with hL | ⟨hxa, hbb⟩ | ⟨hxb, hab⟩
          · exact Or.inr (Or.inr ⟨hL, Relation.ReflTransGen.refl⟩)
          · exact Or.inl hxa
          · exact Or.inr (Or.inr ⟨hxb, Relation.ReflTransGen.refl⟩)
        · have hs : reach L b✝ c✝ := Relation.ReflTransGen.single (Or.inr hin)
          rcases ih with hL | ⟨hxa, hbz⟩ | ⟨hxb, haz⟩
          · exact Or.inl (Relation.ReflTransGen.trans hL hs)
          · exact Or.inr (Or.inl ⟨hxa, Relation.ReflTransGen.trans hbz hs⟩)
          · exact Or.inr (Or.inr ⟨hxb, Relation.ReflTransGen.trans haz hs⟩)
  · intro h
    have hsub : ∀ e ∈ L, e ∈ ((a, b) :: L) := fun e he => List.mem_cons_of_mem _ he
    have hab : reach ((a, b) :: L) a b := Relation.ReflTransGen.single (Or.inl (by simp))
    have hba : reach ((a, b) :: L) b a := reach_symm hab
    rcases h with hL | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
    · exact reach_mono hsub hL
    · exact Relation.ReflTransGen.trans (reach_mono hsub hxa) (Relation.ReflTransGen.trans hab (reach_mono hsub hby))
    · exact Relation.ReflTransGen.trans (reach_mono hsub hxb) (Relation.ReflTransGen.trans hba (reach_mono hsub hay))

lemma comps_cons_le {α : Type} {V : Finset α} {a b : α} {L : List (α × α)}
    (ha : a ∈ V) (hb : b ∈ V) :
    (comps V L).card ≤ (comps V ((a, b) :: L)).card + 1 := by
  by_cases hab : reach L a b
  · have heq : ∀ x y, reach ((a, b) :: L) x y ↔ reach L x y := by
      intro x y
      rw [reach_cons_iff]
      constructor
      · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact h
        · exact Relation.ReflTransGen.trans h1 (Relation.ReflTransGen.trans hab h2)
        · exact Relation.ReflTransGen.trans h1 (Relation.ReflTransGen.trans (reach_symm hab) h2)
      · exact Or.inl
    have hce : comps V ((a, b) :: L) = comps V L := by
      ext c
      simp only [comps, Finset.mem_image, cls]
      simp_rw [heq]
    rw [hce]
    omega
  · have hsub : ((comps V L).erase (cls V L a)).erase (cls V L b) ⊆
        (comps V ((a, b) :: L)).erase (cls V ((a, b) :: L) a) := by
      intro c hc
      rw [Finset.mem_erase, Finset.mem_erase] at hc
      rcases hc with ⟨hcb, hca, hcL⟩
      simp only [comps, Finset.mem_image] at hcL
      rcases hcL with ⟨v, hv, rfl⟩
      have hva : ¬ reach L v a := fun h => hca (@cls_eq_of_reach α V L v a h).symm
      have hvb : ¬ reach L v b := fun h => hcb (@cls_eq_of_reach α V L v b h).symm
      have hcl : cls V ((a, b) :: L) v = cls V L v := by
        ext w
        simp only [mem_cls, reach_cons_iff]
        constructor
        · rintro ⟨hw, h1 | ⟨h2, _⟩ | ⟨h2, _⟩⟩
          · exact ⟨hw, h1⟩
          · exact absurd h2 hva
          · exact absurd h2 hvb
        · rintro ⟨hw, h1⟩
          exact ⟨hw, Or.inl h1⟩
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro hceq
        have ha_in : a ∈ cls V ((a, b) :: L) a := ⟨ha, Relation.ReflTransGen.refl⟩
        rw [← hceq, hcl, mem_cls] at ha_in
        exact hva (reach_symm ha_in.2)
      · rw [← hcl]
        exact Finset.mem_image_of_mem _ hv
    have hcard := Finset.card_le_card hsub
    have ha_mem : cls V L a ∈ comps V L := Finset.mem_image_of_mem _ ha
    have hb_mem : cls V L b ∈ (comps V L).erase (cls V L a) := by
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_image_of_mem _ hb⟩
      intro hba
      have hb_in : b ∈ cls V L b := mem_cls.mpr ⟨hb, Relation.ReflTransGen.refl⟩
      rw [hba, mem_cls] at hb_in
      exact hab hb_in.2
    have ha_mem' : cls V ((a, b) :: L) a ∈ comps V ((a, b) :: L) := Finset.mem_image_of_mem _ ha
    have hpos1 : 0 < ((comps V L).erase (cls V L a)).card := Finset.card_pos.mpr ⟨_, hb_mem⟩
    have hpos2 : 0 < (comps V ((a, b) :: L)).card := Finset.card_pos.mpr ⟨_, ha_mem'⟩
    rw [Finset.card_erase_of_mem ha_mem] at hpos1
    rw [Finset.card_erase_of_mem hb_mem, Finset.card_erase_of_mem ha_mem,
      Finset.card_erase_of_mem ha_mem'] at hcard
    omega

lemma card_le_comps_add_length {α : Type} (V : Finset α) :
    ∀ L : List (α × α), (∀ e ∈ L, e.1 ∈ V ∧ e.2 ∈ V) → V.card ≤ (comps V L).card + L.length
  | [], _ => by rw [comps_nil]; simp
  | (a, b) :: L, hL => by
    have hab := hL (a, b) (by simp)
    have ih := card_le_comps_add_length V L (fun e he => hL e (List.mem_cons_of_mem _ he))
    have hc := @comps_cons_le α V a b L hab.1 hab.2
    simp only [List.length_cons]
    omega

lemma main (n : ℕ) (C : Circuit) (α : Type) (S : Finset α) (roots labelled : Finset ℕ)
    (lab : ℕ → Finset α) (hao : IsAO2 n C)
    (R : ℕ → ℕ → Prop)
    (hR : R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧
      rj < C.gates.length ∧ (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs))
    (hlab : ∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and) ∧ (lab m).card ≤ 2)
    (hcov : ∀ a ∈ S, ∃ r ∈ roots, ∃ m1 ∈ labelled, R m1 r ∧ a ∈ lab m1) :
    S.card ≤ roots.card +
      {jm : ℕ | jm < C.gates.length ∧ (gateAt C jm).op = GateOp.or ∧
        (∃ r2 ∈ roots, R (n + jm) r2) ∧
        ({x3 : α | ∃ m3 ∈ labelled, R m3 ((gateAt C jm).inputs.getD 0 0) ∧ x3 ∈ lab m3}).Nonempty ∧
        ({x4 : α | ∃ m4 ∈ labelled, R m4 ((gateAt C jm).inputs.getD 1 0) ∧ x4 ∈ lab m4}).Nonempty ∧
        Disjoint
          {x5 : α | ∃ m5 ∈ labelled, R m5 ((gateAt C jm).inputs.getD 0 0) ∧ x5 ∈ lab m5}
          {x6 : α | ∃ m6 ∈ labelled, R m6 ((gateAt C jm).inputs.getD 1 0) ∧ x6 ∈ lab m6}}.ncard +
      {m7 : ℕ | m7 ∈ labelled ∧ (lab m7).card = 2}.ncard := by
  by_cases hS_ne : S.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS_ne, Finset.card_empty]
    exact Nat.zero_le _
  have : Nonempty α := ⟨hS_ne.choose⟩
  let sig : ℕ → Set α := fun w => {x : α | ∃ m ∈ labelled, R m w ∧ x ∈ lab m}
  let M : Finset ℕ := (Finset.range C.gates.length).filter fun jm =>
    (gateAt C jm).op = GateOp.or ∧ (∃ r2 ∈ roots, R (n + jm) r2) ∧
      (sig ((gateAt C jm).inputs.getD 0 0)).Nonempty ∧
      (sig ((gateAt C jm).inputs.getD 1 0)).Nonempty ∧
      Disjoint (sig ((gateAt C jm).inputs.getD 0 0)) (sig ((gateAt C jm).inputs.getD 1 0))
  let T : Finset ℕ := labelled.filter fun m => (lab m).card = 2
  have hM_eq : (M : Set ℕ) = {jm : ℕ | jm < C.gates.length ∧ (gateAt C jm).op = GateOp.or ∧
      (∃ r2 ∈ roots, R (n + jm) r2) ∧
      (sig ((gateAt C jm).inputs.getD 0 0)).Nonempty ∧
      (sig ((gateAt C jm).inputs.getD 1 0)).Nonempty ∧
      Disjoint (sig ((gateAt C jm).inputs.getD 0 0)) (sig ((gateAt C jm).inputs.getD 1 0))} := by
    ext jm
    simp [M, sig]
  have hT_eq : (T : Set ℕ) = {m7 : ℕ | m7 ∈ labelled ∧ (lab m7).card = 2} := by
    ext m
    simp [T]
  rw [← hM_eq, ← hT_eq, Set.ncard_coe_finset, Set.ncard_coe_finset]
  let edgeM : ℕ → α × α := fun jm =>
    if h : jm ∈ M then
      let hM := (Finset.mem_filter.mp h).2
      (hM.2.2.1.some, hM.2.2.2.1.some)
    else
      (Classical.arbitrary α, Classical.arbitrary α)
  let edgeT : ℕ → α × α := fun m =>
    if h : (lab m).card = 2 then
      let h2 := Finset.card_eq_two.mp h
      (h2.choose, h2.choose_spec.choose)
    else
      (Classical.arbitrary α, Classical.arbitrary α)
  let L_all : List (α × α) := M.toList.map edgeM ++ T.toList.map edgeT
  let U : Finset α := S ∪ labelled.biUnion lab
  have hL_len : L_all.length = M.card + T.card := by
    simp [L_all]
  have hL_U : ∀ e ∈ L_all, e.1 ∈ U ∧ e.2 ∈ U := by
    intro e he
    simp only [L_all, List.mem_append, List.mem_map, Finset.mem_toList] at he
    rcases he with ⟨jm, hjm, rfl⟩ | ⟨m, hm, rfl⟩
    · simp only [edgeM, dif_pos hjm]
      have hM := (Finset.mem_filter.mp hjm).2
      rcases hM.2.2.1.some_mem with ⟨m0, hm0, _, hx0⟩
      rcases hM.2.2.2.1.some_mem with ⟨m1, hm1, _, hx1⟩
      exact ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m0, hm0, hx0⟩),
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m1, hm1, hx1⟩)⟩
    · have hmT := (Finset.mem_filter.mp hm).2
      have hml := (Finset.mem_filter.mp hm).1
      simp only [edgeT, dif_pos hmT]
      have h2 := Finset.card_eq_two.mp hmT
      have heq := h2.choose_spec.choose_spec.2
      have h1 : h2.choose ∈ lab m := by rw [heq]; exact Finset.mem_insert_self _ _
      have h2' : h2.choose_spec.choose ∈ lab m := by rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m, hml, h1⟩),
        Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨m, hml, h2'⟩)⟩
  have h_sig_conn : ∀ w : ℕ, (∃ r ∈ roots, R w r) →
      ∀ x ∈ sig w, ∀ y ∈ sig w, reach L_all x y := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw x hx y hy
      by_cases hor : ∃ jm, w = n + jm ∧ jm < C.gates.length ∧ (gateAt C jm).op = GateOp.or
      · rcases hor with ⟨jm, rfl, hjm, hjop⟩
        have hnotlab : n + jm ∉ labelled := by
          intro hmem
          rcases (hlab (n + jm) hmem).1 with hlt | ⟨j, hj1, _, hjop2⟩
          · omega
          · have : jm = j := by omega
            subst this
            rw [hjop] at hjop2
            cases hjop2
        have hinp_len : (gateAt C jm).inputs.length = 2 := by
          have hg : gateAt C jm = C.gates[jm] := by simp [gateAt, hjm]
          rw [hg]
          exact hao.2.2 _ (List.getElem_mem hjm)
        have hback : ∀ u ∈ (gateAt C jm).inputs, u < n + jm := by
          intro u hu
          exact hao.2.1 jm hjm u hu
        let u0 := (gateAt C jm).inputs.getD 0 0
        let u1 := (gateAt C jm).inputs.getD 1 0
        have hu0_mem : u0 ∈ (gateAt C jm).inputs := by
          rw [show u0 = (gateAt C jm).inputs[0]'(by omega) from List.getD_eq_getElem _ _ (by omega)]
          exact List.getElem_mem _
        have hu1_mem : u1 ∈ (gateAt C jm).inputs := by
          rw [show u1 = (gateAt C jm).inputs[1]'(by omega) from List.getD_eq_getElem _ _ (by omega)]
          exact List.getElem_mem _
        have hu0_lt : u0 < n + jm := hback u0 hu0_mem
        have hu1_lt : u1 < n + jm := hback u1 hu1_mem
        have hstep0 : R u0 (n + jm) := by
          rw [hR]
          exact Relation.ReflTransGen.single ⟨hu0_lt, jm, rfl, hjm, hjop, hu0_mem⟩
        have hstep1 : R u1 (n + jm) := by
          rw [hR]
          exact Relation.ReflTransGen.single ⟨hu1_lt, jm, rfl, hjm, hjop, hu1_mem⟩
        have hr0 : ∃ r ∈ roots, R u0 r := by
          rcases hw with ⟨r, hr, hwr⟩
          refine ⟨r, hr, ?_⟩
          rw [hR] at hwr ⊢
          exact Relation.ReflTransGen.trans (by rw [← hR]; exact hstep0) hwr
        have hr1 : ∃ r ∈ roots, R u1 r := by
          rcases hw with ⟨r, hr, hwr⟩
          refine ⟨r, hr, ?_⟩
          rw [hR] at hwr ⊢
          exact Relation.ReflTransGen.trans (by rw [← hR]; exact hstep1) hwr
        have hsig_sub : ∀ z ∈ sig (n + jm), z ∈ sig u0 ∨ z ∈ sig u1 := by
          intro z hz
          rcases hz with ⟨m, hm, hmR, hzm⟩
          rw [hR] at hmR
          rcases Relation.ReflTransGen.cases_tail hmR with rfl | ⟨ra, _, hma, hra⟩
          · exact absurd hm hnotlab
          · let ⟨rj, hrj, _, _, hramem⟩ := hra.2
            have : rj = jm := by omega
            subst this
            have hinp_eq : (gateAt C jm).inputs = [u0, u1] := by
              cases hL : (gateAt C jm).inputs with
              | nil => simp [hL] at hinp_len
              | cons a t =>
                cases t with
                | nil => simp [hL] at hinp_len
                | cons b t' =>
                  cases t' with
                  | nil => simp [u0, u1, hL]
                  | cons c t'' => simp [hL] at hinp_len
            rw [hinp_eq] at hramem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hramem
            rcases hramem with rfl | rfl
            · exact Or.inl ⟨m, hm, by rw [hR]; exact hma, hzm⟩
            · exact Or.inr ⟨m, hm, by rw [hR]; exact hma, hzm⟩
        rcases hsig_sub x hx with hx0 | hx1 <;> rcases hsig_sub y hy with hy0 | hy1
        · exact ih u0 hu0_lt hr0 x hx0 y hy0
        · by_cases hdisj : Disjoint (sig u0) (sig u1)
          · have hjmM : jm ∈ M := by
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_range.mpr hjm, hjop, hw, ⟨x, hx0⟩, ⟨y, hy1⟩, hdisj⟩
            have heM : edgeM jm ∈ L_all := by
              simp only [L_all, List.mem_append, List.mem_map, Finset.mem_toList]
              exact Or.inl ⟨jm, hjmM, rfl⟩
            have hM := (Finset.mem_filter.mp hjmM).2
            have he_val : edgeM jm = (hM.2.2.1.some, hM.2.2.2.1.some) := by simp [edgeM, dif_pos hjmM]
            rw [he_val] at heM
            have h0c := ih u0 hu0_lt hr0 x hx0 _ hM.2.2.1.some_mem
            have h1c := ih u1 hu1_lt hr1 _ hM.2.2.2.1.some_mem y hy1
            exact Relation.ReflTransGen.trans h0c (Relation.ReflTransGen.trans (Relation.ReflTransGen.single (Or.inl heM)) h1c)
          · rw [Set.not_disjoint_iff] at hdisj
            rcases hdisj with ⟨z, hz0, hz1⟩
            exact Relation.ReflTransGen.trans (ih u0 hu0_lt hr0 x hx0 z hz0) (ih u1 hu1_lt hr1 z hz1 y hy1)
        · by_cases hdisj : Disjoint (sig u0) (sig u1)
          · have hjmM : jm ∈ M := by
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_range.mpr hjm, hjop, hw, ⟨y, hy0⟩, ⟨x, hx1⟩, hdisj⟩
            have heM : edgeM jm ∈ L_all := by
              simp only [L_all, List.mem_append, List.mem_map, Finset.mem_toList]
              exact Or.inl ⟨jm, hjmM, rfl⟩
            have hM := (Finset.mem_filter.mp hjmM).2
            have he_val : edgeM jm = (hM.2.2.1.some, hM.2.2.2.1.some) := by simp [edgeM, dif_pos hjmM]
            rw [he_val] at heM
            have h1c := ih u1 hu1_lt hr1 x hx1 _ hM.2.2.2.1.some_mem
            have h0c := ih u0 hu0_lt hr0 _ hM.2.2.1.some_mem y hy0
            exact Relation.ReflTransGen.trans h1c (Relation.ReflTransGen.trans (Relation.ReflTransGen.single (Or.inr heM)) h0c)
          · rw [Set.not_disjoint_iff] at hdisj
            rcases hdisj with ⟨z, hz0, hz1⟩
            exact Relation.ReflTransGen.trans (ih u1 hu1_lt hr1 x hx1 z hz1) (ih u0 hu0_lt hr0 z hz0 y hy0)
        · exact ih u1 hu1_lt hr1 x hx1 y hy1
      · have hR_eq : ∀ m, R m w → m = w := by
          intro m hmR
          rw [hR] at hmR
          rcases Relation.ReflTransGen.cases_tail hmR with rfl | ⟨ra, _, _, hra⟩
          · rfl
          · let ⟨rj, hrj, hrjlt, hrjop, _⟩ := hra.2
            exact absurd ⟨rj, hrj, hrjlt, hrjop⟩ hor
        rcases hx with ⟨mx, hmx, hmRx, hxmem⟩
        rcases hy with ⟨my, hmy, hmRy, hymem⟩
        have hmxw := hR_eq mx hmRx
        have hmyw := hR_eq my hmRy
        rw [hmxw] at hmx hxmem
        rw [hmyw] at hymem
        by_cases hxy : x = y
        · subst hxy; exact Relation.ReflTransGen.refl
        · have hle2 := (hlab w hmx).2
          have hge2 : 2 ≤ (lab w).card := Finset.one_lt_card.mpr ⟨x, hxmem, y, hymem, hxy⟩
          have heq2 : (lab w).card = 2 := le_antisymm hle2 hge2
          have hmT : w ∈ T := Finset.mem_filter.mpr ⟨hmx, heq2⟩
          have heT : edgeT w ∈ L_all := by
            simp only [L_all, List.mem_append, List.mem_map, Finset.mem_toList]
            exact Or.inr ⟨w, hmT, rfl⟩
          have h2 := Finset.card_eq_two.mp heq2
          have he_val : edgeT w = (h2.choose, h2.choose_spec.choose) := by simp only [edgeT, dif_pos heq2]
          rw [he_val] at heT
          have hset := h2.choose_spec.choose_spec.2
          rw [hset] at hxmem hymem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem hymem
          rcases hxmem with rfl | rfl <;> rcases hymem with rfl | rfl
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.single (Or.inl heT)
          · exact Relation.ReflTransGen.single (Or.inr heT)
          · exact Relation.ReflTransGen.refl
  let V_S : Finset α := U.filter (fun v => ∃ s ∈ S, reach L_all v s)
  let L_S : List (α × α) := L_all.filter (fun e => decide (e.1 ∈ V_S ∧ e.2 ∈ V_S))
  have hS_sub : S ⊆ V_S := by
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs, s, hs, Relation.ReflTransGen.refl⟩
  have hL_S_len : L_S.length ≤ M.card + T.card := by
    rw [← hL_len]
    exact List.length_filter_le _ _
  have hL_S_V : ∀ e ∈ L_S, e.1 ∈ V_S ∧ e.2 ∈ V_S := by
    intro e he
    simp only [L_S, List.mem_filter, decide_eq_true_eq] at he
    exact he.2
  have h_reach_VS : ∀ u ∈ V_S, ∀ v, reach L_all u v → reach L_S u v := by
    intro u hu v huv
    induction huv with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hub hbc ih =>
      have hb_VS : b ∈ V_S := by
        rcases (Finset.mem_filter.mp hu) with ⟨_, s, hs, hus⟩
        rcases hbc with hbc1 | hbc2
        · have heU := hL_U (b, c) hbc1
          exact Finset.mem_filter.mpr ⟨heU.1, s, hs, Relation.ReflTransGen.trans (reach_symm hub) hus⟩
        · have heU := hL_U (c, b) hbc2
          exact Finset.mem_filter.mpr ⟨heU.2, s, hs, Relation.ReflTransGen.trans (reach_symm hub) hus⟩
      have hc_VS : c ∈ V_S := by
        rcases (Finset.mem_filter.mp hu) with ⟨_, s, hs, hus⟩
        rcases hbc with hbc1 | hbc2
        · have heU := hL_U (b, c) hbc1
          exact Finset.mem_filter.mpr ⟨heU.2, s, hs, Relation.ReflTransGen.trans (reach_symm (Relation.ReflTransGen.tail hub (Or.inl hbc1))) hus⟩
        · have heU := hL_U (c, b) hbc2
          exact Finset.mem_filter.mpr ⟨heU.1, s, hs, Relation.ReflTransGen.trans (reach_symm (Relation.ReflTransGen.tail hub (Or.inr hbc2))) hus⟩
      refine Relation.ReflTransGen.tail ih ?_
      rcases hbc with hbc1 | hbc2
      · exact Or.inl (List.mem_filter.mpr ⟨hbc1, decide_eq_true ⟨hb_VS, hc_VS⟩⟩)
      · exact Or.inr (List.mem_filter.mpr ⟨hbc2, decide_eq_true ⟨hc_VS, hb_VS⟩⟩)
  have h_comps_le : (comps V_S L_S).card ≤ roots.card := by
    let f : ℕ → Finset α := fun r =>
      if h : ∃ s ∈ S, s ∈ sig r then cls V_S L_S h.choose else ∅
    have hsub : (comps V_S L_S).erase ∅ ⊆ roots.image f := by
      intro c hc
      rw [Finset.mem_erase] at hc
      rcases hc with ⟨hcne, hcmem⟩
      simp only [comps, Finset.mem_image] at hcmem
      rcases hcmem with ⟨v, hv, rfl⟩
      rcases (Finset.mem_filter.mp hv).2 with ⟨s, hs, hvs⟩
      rcases hcov s hs with ⟨r, hr, m1, hm1, hm1R, hsm1⟩
      have hsr : s ∈ sig r := ⟨m1, hm1, hm1R, hsm1⟩
      have hfr : ∃ s' ∈ S, s' ∈ sig r := ⟨s, hs, hsr⟩
      refine Finset.mem_image.mpr ⟨r, hr, ?_⟩
      simp only [f, dif_pos hfr]
      have h_s_pick : reach L_all hfr.choose s :=
        h_sig_conn r ⟨r, hr, hR ▸ Relation.ReflTransGen.refl⟩ _ hfr.choose_spec.2 _ hsr
      have h_v_pick : reach L_S v hfr.choose :=
        h_reach_VS v hv _ (Relation.ReflTransGen.trans hvs (reach_symm h_s_pick))
      exact (cls_eq_of_reach h_v_pick).symm
    have hle1 : (comps V_S L_S).card ≤ (roots.image f).card := by
      have hne_empty : ∅ ∉ comps V_S L_S := by
        intro hem
        simp only [comps, Finset.mem_image] at hem
        rcases hem with ⟨v, hv, hveq⟩
        have hv_in : v ∈ cls V_S L_S v := mem_cls.mpr ⟨hv, Relation.ReflTransGen.refl⟩
        rw [hveq] at hv_in
        exact Finset.notMem_empty v hv_in
      rw [Finset.erase_eq_of_notMem hne_empty] at hsub
      exact Finset.card_le_card hsub
    exact le_trans hle1 Finset.card_image_le
  have hmain := card_le_comps_add_length V_S L_S hL_S_V
  have hSV : S.card ≤ V_S.card := Finset.card_le_card hS_sub
  omega

end PEqualNP.Outside.L_meta_2405

theorem PEqualNP.Outside.L_meta_2405 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (α : Type) (S : Finset α) (roots labelled : Finset ℕ) (lab : ℕ → Finset α), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (lab m).card ≤ 2) → (∀ a ∈ S, ∃ r ∈ roots, ∃ m1 ∈ labelled, R m1 r ∧ a ∈ lab m1) → S.card ≤ roots.card + {jm : ℕ | jm < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jm).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ r2 ∈ roots, R (n + jm) r2) ∧ ({x3 : α | ∃ m3 ∈ labelled, R m3 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 0 0) ∧ x3 ∈ lab m3}).Nonempty ∧ ({x4 : α | ∃ m4 ∈ labelled, R m4 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 1 0) ∧ x4 ∈ lab m4}).Nonempty ∧ Disjoint {x5 : α | ∃ m5 ∈ labelled, R m5 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 0 0) ∧ x5 ∈ lab m5} {x6 : α | ∃ m6 ∈ labelled, R m6 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 1 0) ∧ x6 ∈ lab m6}}.ncard + {m7 : ℕ | m7 ∈ labelled ∧ (lab m7).card = 2}.ncard :=
  PEqualNP.Outside.L_meta_2405.main
