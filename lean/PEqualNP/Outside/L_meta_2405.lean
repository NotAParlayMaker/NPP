import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2405

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stp (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧
    (gateAt C rj).op = GateOp.or ∧ ra ∈ (gateAt C rj).inputs

def Lb {α : Type} (n : ℕ) (C : Circuit) (labelled : Finset ℕ) (lab : ℕ → Finset α) (w : ℕ) : Set α :=
  {x : α | ∃ m ∈ labelled, Relation.ReflTransGen (stp n C) m w ∧ x ∈ lab m}

def Cn (n : ℕ) (C : Circuit) (roots : Finset ℕ) (w : ℕ) : Prop :=
  ∃ r ∈ roots, Relation.ReflTransGen (stp n C) w r

def DP {α : Type} (n : ℕ) (C : Circuit) (roots labelled : Finset ℕ) (lab : ℕ → Finset α) (jm : ℕ) : Prop :=
  jm < C.gates.length ∧ (gateAt C jm).op = GateOp.or ∧ (∃ r2 ∈ roots, Relation.ReflTransGen (stp n C) (n + jm) r2) ∧
    (Lb n C labelled lab ((gateAt C jm).inputs.getD 0 0)).Nonempty ∧
    (Lb n C labelled lab ((gateAt C jm).inputs.getD 1 0)).Nonempty ∧
    Disjoint (Lb n C labelled lab ((gateAt C jm).inputs.getD 0 0))
      (Lb n C labelled lab ((gateAt C jm).inputs.getD 1 0))

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma leaf_eq (n : ℕ) (C : Circuit) (m w : ℕ)
    (hw : ¬ ∃ j, w = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.or)
    (h : Relation.ReflTransGen (stp n C) m w) : w = m := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, _, hc⟩
  · exact h
  · obtain ⟨_, rj, h1, h2, h3, _⟩ := hc
    exact absurd ⟨rj, h1, h2, h3⟩ hw

lemma lab_not_or (n : ℕ) (C : Circuit) (labelled : Finset ℕ) {α : Type} (lab : ℕ → Finset α)
    (hlab : ∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and) ∧ (lab m).card ≤ 2)
    (j : ℕ) (hor : (gateAt C j).op = GateOp.or) : n + j ∉ labelled := by
  intro hm
  rcases (hlab _ hm).1 with h | ⟨j2, he, _, hand⟩
  · omega
  · obtain rfl : j2 = j := by omega
    rw [hor] at hand
    cases hand

lemma or_ab (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j := by
  have hg : gateAt C j ∈ C.gates := by rw [gateAt_eq C j hj]; exact List.getElem_mem _
  have hlen := hC.2.2 _ hg
  have hrb := hC.2.1 j hj
  generalize (gateAt C j).inputs = l at hlen hrb
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · exact ⟨a, b, rfl, hrb a (by simp), hrb b (by simp)⟩
  · simp at hlen

lemma Lb_or {α : Type} (n : ℕ) (C : Circuit) (labelled : Finset ℕ) (lab : ℕ → Finset α)
    (hlab : ∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and) ∧ (lab m).card ≤ 2)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) (a b : ℕ)
    (hin : (gateAt C j).inputs = [a, b]) (x : α) (hx : x ∈ Lb n C labelled lab (n + j)) :
    x ∈ Lb n C labelled lab a ∨ x ∈ Lb n C labelled lab b := by
  obtain ⟨m, hm, hR, hxm⟩ := hx
  rcases Relation.ReflTransGen.cases_tail hR with h | ⟨c, hc, hs⟩
  · exfalso
    rw [← h] at hm
    exact lab_not_or n C labelled lab hlab j hor hm
  · obtain ⟨_, rj, h1, _, _, h4⟩ := hs
    obtain rfl : rj = j := by omega
    rw [hin] at h4
    simp at h4
    rcases h4 with rfl | rfl
    · left; exact ⟨m, hm, hc, hxm⟩
    · right; exact ⟨m, hm, hc, hxm⟩

lemma Cn_or (n : ℕ) (C : Circuit) (roots : Finset ℕ)
    (j : ℕ) (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) (a : ℕ)
    (ha : a < n + j) (hin : a ∈ (gateAt C j).inputs) (h : Cn n C roots (n + j)) : Cn n C roots a := by
  obtain ⟨r, hr, hR⟩ := h
  exact ⟨r, hr, Relation.ReflTransGen.head ⟨ha, j, rfl, hj, hor, hin⟩ hR⟩

lemma merge_card {α : Type} [DecidableEq α] (c : α → α) (u v : α) (X : Finset α) :
    (X.image c).card ≤ (X.image (fun z => if c z = v then u else c z)).card + 1 := by
  calc (X.image c).card ≤ (insert v (X.image (fun z => if c z = v then u else c z))).card := by
        apply Finset.card_le_card
        intro k hk
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hk
        by_cases h : c z = v
        · rw [h]; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z, hz, by simp [h]⟩)
    _ ≤ _ := Finset.card_insert_le _ _

lemma merged_const {α : Type} [DecidableEq α] (c : α → α) (x0 y0 x : α)
    (h : c x = c x0 ∨ c x = c y0) : (if c x = c y0 then c x0 else c x) = c x0 := by
  rcases h with h | h
  · rw [h]; split_ifs <;> rfl
  · rw [h, if_pos rfl]

def Inv {α : Type} [DecidableEq α] (n : ℕ) (C : Circuit) (roots labelled : Finset ℕ)
    (lab : ℕ → Finset α) (N : ℕ) (c : α → α) (FD FT : Finset ℕ) : Prop :=
  (∀ w < N, Cn n C roots w → ∀ x ∈ Lb n C labelled lab w, ∀ y ∈ Lb n C labelled lab w, c x = c y) ∧
  (∀ j ∈ FD, n + j < N ∧ DP n C roots labelled lab j) ∧
  (∀ m ∈ FT, m < N ∧ m ∈ labelled ∧ (lab m).card = 2) ∧
  ∀ X : Finset α, X.card ≤ (X.image c).card + FD.card + FT.card

lemma keep {α : Type} [DecidableEq α] (n : ℕ) (C : Circuit) (roots labelled : Finset ℕ)
    (lab : ℕ → Finset α) (N : ℕ) (c : α → α) (FD FT : Finset ℕ)
    (h : Inv n C roots labelled lab N c FD FT)
    (hnew : Cn n C roots N → ∀ x ∈ Lb n C labelled lab N, ∀ y ∈ Lb n C labelled lab N, c x = c y) :
    Inv n C roots labelled lab (N + 1) c FD FT := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, h4⟩
  · intro w hw hcw x hx y hy
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hlt | rfl
    · exact h1 w hlt hcw x hx y hy
    · exact hnew hcw x hx y hy
  · intro j hj
    exact ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
  · intro m hm
    exact ⟨by have := (h3 m hm).1; omega, (h3 m hm).2⟩

lemma mergeD {α : Type} [DecidableEq α] (n : ℕ) (C : Circuit) (roots labelled : Finset ℕ)
    (lab : ℕ → Finset α) (j : ℕ) (c : α → α) (FD FT : Finset ℕ)
    (h : Inv n C roots labelled lab (n + j) c FD FT) (x0 y0 : α)
    (hD : DP n C roots labelled lab j)
    (hnew : ∀ x ∈ Lb n C labelled lab (n + j), c x = c x0 ∨ c x = c y0) :
    Inv n C roots labelled lab (n + j + 1) (fun z => if c z = c y0 then c x0 else c z)
      (insert j FD) FT := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw hcw x hx y hy
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hlt | rfl
    · have e := h1 w hlt hcw x hx y hy
      show (if c x = c y0 then c x0 else c x) = (if c y = c y0 then c x0 else c y)
      rw [e]
    · show (if c x = c y0 then c x0 else c x) = (if c y = c y0 then c x0 else c y)
      rw [merged_const c x0 y0 x (hnew x hx), merged_const c x0 y0 y (hnew y hy)]
  · intro j2 hj2
    rcases Finset.mem_insert.mp hj2 with rfl | hm
    · exact ⟨by omega, hD⟩
    · exact ⟨by have := (h2 j2 hm).1; omega, (h2 j2 hm).2⟩
  · intro m hm
    exact ⟨by have := (h3 m hm).1; omega, (h3 m hm).2⟩
  · intro X
    have hni : j ∉ FD := fun hm => by have := (h2 j hm).1; omega
    have e1 : (insert j FD).card = FD.card + 1 := by simp [hni]
    have e2 := h4 X
    have e3 := merge_card c (c x0) (c y0) X
    omega

lemma mergeT {α : Type} [DecidableEq α] (n : ℕ) (C : Circuit) (roots labelled : Finset ℕ)
    (lab : ℕ → Finset α) (N : ℕ) (c : α → α) (FD FT : Finset ℕ)
    (h : Inv n C roots labelled lab N c FD FT) (x0 y0 : α)
    (hT : N ∈ labelled ∧ (lab N).card = 2)
    (hnew : ∀ x ∈ Lb n C labelled lab N, c x = c x0 ∨ c x = c y0) :
    Inv n C roots labelled lab (N + 1) (fun z => if c z = c y0 then c x0 else c z)
      FD (insert N FT) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw hcw x hx y hy
    rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hlt | rfl
    · have e := h1 w hlt hcw x hx y hy
      show (if c x = c y0 then c x0 else c x) = (if c y = c y0 then c x0 else c y)
      rw [e]
    · show (if c x = c y0 then c x0 else c x) = (if c y = c y0 then c x0 else c y)
      rw [merged_const c x0 y0 x (hnew x hx), merged_const c x0 y0 y (hnew y hy)]
  · intro j hj
    exact ⟨by have := (h2 j hj).1; omega, (h2 j hj).2⟩
  · intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm2
    · exact ⟨by omega, hT⟩
    · exact ⟨by have := (h3 m hm2).1; omega, (h3 m hm2).2⟩
  · intro X
    have hni : N ∉ FT := fun hm => by have := (h3 N hm).1; omega
    have e1 : (insert N FT).card = FT.card + 1 := by simp [hni]
    have e2 := h4 X
    have e3 := merge_card c (c x0) (c y0) X
    omega

lemma inv {α : Type} [DecidableEq α] (n : ℕ) (C : Circuit) (roots labelled : Finset ℕ)
    (lab : ℕ → Finset α) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hlab : ∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and) ∧ (lab m).card ≤ 2) :
    ∀ N : ℕ, ∃ (c : α → α) (FD FT : Finset ℕ), Inv n C roots labelled lab N c FD FT := by
  intro N
  induction N with
  | zero =>
    refine ⟨id, ∅, ∅, ?_, ?_, ?_, ?_⟩
    · intro w hw; omega
    · intro j hj; simp at hj
    · intro m hm; simp at hm
    · intro X; simp
  | succ N ih =>
    obtain ⟨c, FD, FT, hI⟩ := ih
    by_cases hor : ∃ j, N = n + j ∧ j < C.gates.length ∧ (gateAt C j).op = GateOp.or
    · obtain ⟨j, rfl, hj, hop⟩ := hor
      obtain ⟨a, b, hin, ha, hb⟩ := or_ab n C hC j hj
      have e0 : (gateAt C j).inputs.getD 0 0 = a := by rw [hin]; rfl
      have e1 : (gateAt C j).inputs.getD 1 0 = b := by rw [hin]; rfl
      have hL := Lb_or n C labelled lab hlab j hj hop a b hin
      by_cases hD : DP n C roots labelled lab j
      · have hcone : Cn n C roots (n + j) := hD.2.2.1
        have hca : Cn n C roots a := Cn_or n C roots j hj hop a ha (by rw [hin]; simp) hcone
        have hcb : Cn n C roots b := Cn_or n C roots j hj hop b hb (by rw [hin]; simp) hcone
        have hne := hD.2.2.2
        rw [e0, e1] at hne
        obtain ⟨⟨x0, hx0⟩, ⟨y0, hy0⟩, _⟩ := hne
        refine ⟨_, _, _, mergeD n C roots labelled lab j c FD FT hI x0 y0 hD ?_⟩
        intro x hx
        rcases hL x hx with hxa | hxb
        · left; exact hI.1 a ha hca x hxa x0 hx0
        · right; exact hI.1 b hb hcb x hxb y0 hy0
      · refine ⟨c, FD, FT, keep n C roots labelled lab (n + j) c FD FT hI ?_⟩
        intro hcone x hx y hy
        have hca : Cn n C roots a := Cn_or n C roots j hj hop a ha (by rw [hin]; simp) hcone
        have hcb : Cn n C roots b := Cn_or n C roots j hj hop b hb (by rw [hin]; simp) hcone
        have hDn : ¬ ((Lb n C labelled lab a).Nonempty ∧ (Lb n C labelled lab b).Nonempty ∧
            Disjoint (Lb n C labelled lab a) (Lb n C labelled lab b)) := by
          intro h
          apply hD
          refine ⟨hj, hop, hcone, ?_, ?_, ?_⟩
          · rw [e0]; exact h.1
          · rw [e1]; exact h.2.1
          · rw [e0, e1]; exact h.2.2
        rcases hL x hx with hxa | hxb <;> rcases hL y hy with hya | hyb
        · exact hI.1 a ha hca x hxa y hya
        · obtain ⟨z, hza, hzb⟩ := Set.not_disjoint_iff.mp (fun hd => hDn ⟨⟨x, hxa⟩, ⟨y, hyb⟩, hd⟩)
          exact (hI.1 a ha hca x hxa z hza).trans (hI.1 b hb hcb z hzb y hyb)
        · obtain ⟨z, hza, hzb⟩ := Set.not_disjoint_iff.mp (fun hd => hDn ⟨⟨y, hya⟩, ⟨x, hxb⟩, hd⟩)
          exact (hI.1 b hb hcb x hxb z hzb).trans (hI.1 a ha hca z hza y hya)
        · exact hI.1 b hb hcb x hxb y hyb
    · have hleaf : ∀ x ∈ Lb n C labelled lab N, N ∈ labelled ∧ x ∈ lab N := by
        rintro x ⟨m, hm, hR, hxm⟩
        have e := leaf_eq n C m N hor hR
        subst e
        exact ⟨hm, hxm⟩
      by_cases hT : N ∈ labelled ∧ (lab N).card = 2
      · obtain ⟨x0, y0, _, hxy⟩ := Finset.card_eq_two.mp hT.2
        refine ⟨_, _, _, mergeT n C roots labelled lab N c FD FT hI x0 y0 hT ?_⟩
        intro x hx
        have hxl := (hleaf x hx).2
        rw [hxy] at hxl
        simp at hxl
        rcases hxl with rfl | rfl
        · left; rfl
        · right; rfl
      · refine ⟨c, FD, FT, keep n C roots labelled lab N c FD FT hI ?_⟩
        intro _ x hx y hy
        have hm := (hleaf x hx).1
        have hc1 : (lab N).card ≤ 1 := by
          have h2 := (hlab N hm).2
          have h3 : (lab N).card ≠ 2 := fun h => hT ⟨hm, h⟩
          omega
        have exy : x = y := Finset.card_le_one.mp hc1 x (hleaf x hx).2 y (hleaf y hy).2
        rw [exy]

theorem main {α : Type} (n : ℕ) (C : Circuit) (S : Finset α) (roots labelled : Finset ℕ)
    (lab : ℕ → Finset α) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hlab : ∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧
      (gateAt C j).op = GateOp.and) ∧ (lab m).card ≤ 2)
    (hS : ∀ a ∈ S, ∃ r ∈ roots, ∃ m1 ∈ labelled, Relation.ReflTransGen (stp n C) m1 r ∧ a ∈ lab m1) :
    S.card ≤ roots.card + {jm : ℕ | DP n C roots labelled lab jm}.ncard +
      {m7 : ℕ | m7 ∈ labelled ∧ (lab m7).card = 2}.ncard := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨a0, _⟩
  · simp
  obtain ⟨c, FD, FT, h1, h2, h3, h4⟩ := inv n C roots labelled lab hC hlab (roots.sup id + 1)
  have hD : FD.card ≤ {jm : ℕ | DP n C roots labelled lab jm}.ncard := by
    rw [← Set.ncard_coe_finset FD]
    apply Set.ncard_le_ncard
    · intro j hj; exact (h2 j hj).2
    · exact (Set.finite_lt_nat C.gates.length).subset (fun j hj => hj.1)
  have hT : FT.card ≤ {m7 : ℕ | m7 ∈ labelled ∧ (lab m7).card = 2}.ncard := by
    rw [← Set.ncard_coe_finset FT]
    apply Set.ncard_le_ncard
    · intro m hm; exact (h3 m hm).2
    · exact labelled.finite_toSet.subset (fun m hm => hm.1)
  have hI : (S.image c).card ≤ roots.card := by
    haveI : Nonempty α := ⟨a0⟩
    calc (S.image c).card
        ≤ (roots.image (fun r => c (Classical.epsilon (fun x => x ∈ Lb n C labelled lab r)))).card := by
          apply Finset.card_le_card
          intro k hk
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
          obtain ⟨r, hr, m1, hm1, hR, hx⟩ := hS a ha
          have hal : a ∈ Lb n C labelled lab r := ⟨m1, hm1, hR, hx⟩
          have he : Classical.epsilon (fun x => x ∈ Lb n C labelled lab r) ∈ Lb n C labelled lab r :=
            Classical.epsilon_spec (p := fun x => x ∈ Lb n C labelled lab r) ⟨a, hal⟩
          refine Finset.mem_image.mpr ⟨r, hr, ?_⟩
          exact h1 r (Nat.lt_succ_of_le (Finset.le_sup (f := id) hr)) ⟨r, hr, Relation.ReflTransGen.refl⟩
            _ he _ hal
      _ ≤ roots.card := Finset.card_image_le
  have e := h4 S
  omega

end PEqualNP.Outside.L_meta_2405

theorem PEqualNP.Outside.L_meta_2405 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (α : Type) (S : Finset α) (roots labelled : Finset ℕ) (lab : ℕ → Finset α), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → (∀ m ∈ labelled, (m < n ∨ ∃ j, m = n + j ∧ j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ (lab m).card ≤ 2) → (∀ a ∈ S, ∃ r ∈ roots, ∃ m1 ∈ labelled, R m1 r ∧ a ∈ lab m1) → S.card ≤ roots.card + {jm : ℕ | jm < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C jm).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∃ r2 ∈ roots, R (n + jm) r2) ∧ ({x3 : α | ∃ m3 ∈ labelled, R m3 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 0 0) ∧ x3 ∈ lab m3}).Nonempty ∧ ({x4 : α | ∃ m4 ∈ labelled, R m4 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 1 0) ∧ x4 ∈ lab m4}).Nonempty ∧ Disjoint {x5 : α | ∃ m5 ∈ labelled, R m5 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 0 0) ∧ x5 ∈ lab m5} {x6 : α | ∃ m6 ∈ labelled, R m6 ((PEqualNP.MetaComplexity.NestedCover.gateAt C jm).inputs.getD 1 0) ∧ x6 ∈ lab m6}}.ncard + {m7 : ℕ | m7 ∈ labelled ∧ (lab m7).card = 2}.ncard := by
  intro n C α S roots labelled lab hC R hR hlab hS
  subst hR
  exact PEqualNP.Outside.L_meta_2405.main n C S roots labelled lab hC hlab hS
