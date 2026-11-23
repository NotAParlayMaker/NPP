import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_949_aux

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

/-! ## Section 1: AndCountCircuit evaluation and basic graph lemmas -/

theorem side_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (val val' : Fin k → Bool) (h : ∀ j, j < i → val j = val' j) :
    sideTrue U B F i val = sideTrue U B F i val' := by
  unfold sideTrue
  apply decide_eq_decide.mpr
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

theorem fuel_stable {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val = m → ∀ d d' : ℕ, m < d → m < d' →
      gateValFuel C U d i = gateValFuel C U d' i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i hi d d' hd hd'
    cases d with
    | zero => omega
    | succ d =>
      cases d' with
      | zero => omega
      | succ d' =>
        simp only [gateValFuel]
        congr 1
        · apply side_congr
          intro j hj
          have hjv : j.val < i.val := hj
          exact ih j.val (by omega) j rfl d d' (by omega) (by omega)
        · apply side_congr
          intro j hj
          have hjv : j.val < i.val := hj
          exact ih j.val (by omega) j rfl d d' (by omega) (by omega)

theorem gv_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  unfold gateVal
  rw [fuel_stable C U i.val i rfl C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)]
  simp only [gateValFuel]
  congr 1
  · apply side_congr
    intro j hj
    have hjv : j.val < i.val := hj
    exact fuel_stable C U j.val j rfl _ _ hjv j.isLt
  · apply side_congr
    intro j hj
    have hjv : j.val < i.val := hj
    exact fuel_stable C U j.val j rfl _ _ hjv j.isLt

theorem gv_iff {n : ℕ} (C : AndCountCircuit n) (hW : C.WellFormed) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i = true ↔
      ((∃ v ∈ C.leftVars i, v ∈ U) ∨ ∃ j ∈ C.leftGates i, C.gateVal U j = true) ∧
      ((∃ v ∈ C.rightVars i, v ∈ U) ∨ ∃ j ∈ C.rightGates i, C.gateVal U j = true) := by
  rw [gv_unfold]
  simp only [Bool.and_eq_true, sideTrue, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
    · rcases h2 with h | ⟨j, hj, _, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, hv⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases h1 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hW i).1 j hj, hv⟩
    · rcases h2 with h | ⟨j, hj, hv⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj, (hW i).2 j hj, hv⟩

def IsIndep {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w

def IsMIS {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  IsIndep G I ∧ ∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v

def PartialCond {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) : Prop :=
  ∀ I : Finset (Fin n), IsMIS G I →
    C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true

def HasBC {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ X Y : Fin k → Finset (Fin n),
    (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧
    (∀ a b : Fin n, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i))

theorem exists_mis_superset {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : IsIndep G S) : ∃ I : Finset (Fin n), S ⊆ I ∧ IsMIS G I := by
  classical
  have key : ∀ d : ℕ, ∀ T : Finset (Fin n), n - T.card ≤ d → IsIndep G T →
      ∃ I : Finset (Fin n), T ⊆ I ∧ IsMIS G I := by
    intro d
    induction d with
    | zero =>
      intro T hcard hT
      have hU : T = Finset.univ := Finset.eq_univ_of_card T (by
        have := T.card_le_univ
        rw [Fintype.card_fin] at this ⊢
        omega)
      refine ⟨T, Finset.Subset.refl _, hT, fun u hu => ?_⟩
      exfalso; exact hu (hU ▸ Finset.mem_univ u)
    | succ d ih =>
      intro T hcard hT
      by_cases hm : ∀ u, u ∉ T → ∃ v ∈ T, G.Adj u v
      · exact ⟨T, Finset.Subset.refl _, hT, hm⟩
      · push Not at hm
        obtain ⟨u, huT, hno⟩ := hm
        have hT' : IsIndep G (insert u T) := by
          intro a ha b hb
          rcases Finset.mem_insert.1 ha with rfl | ha' <;>
            rcases Finset.mem_insert.1 hb with rfl | hb'
          · exact G.loopless.irrefl _
          · exact hno b hb'
          · exact fun h => hno a ha' h.symm
          · exact hT a ha' b hb'
        have hc' : (insert u T).card = T.card + 1 := Finset.card_insert_of_notMem huT
        have hlt : T.card < n := by
          have hss : T ⊂ Finset.univ := Finset.ssubset_univ_iff.2 fun h => huT (by rw [h]; exact Finset.mem_univ u)
          have := Finset.card_lt_card hss
          simpa using this
        obtain ⟨I, hsub, hmis⟩ := ih (insert u T) (by omega) hT'
        exact ⟨I, (Finset.subset_insert u T).trans hsub, hmis⟩
  exact key (n - S.card) S le_rfl hS

theorem exists_mis_mem {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    ∃ I : Finset (Fin n), v ∈ I ∧ IsMIS G I := by
  have h1 : IsIndep G {v} := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst ha; subst hb; exact G.loopless.irrefl _
  obtain ⟨I, hsub, hmis⟩ := exists_mis_superset G {v} h1
  exact ⟨I, hsub (Finset.mem_singleton_self v), hmis⟩

theorem outVars_empty {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hP : PartialCond G C) : C.outVars = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro v hv
  obtain ⟨I, hvI, hmis⟩ := exists_mis_mem G v
  have hf := (hP I hmis).1
  unfold AndCountCircuit.eval at hf
  simp only [decide_eq_false_iff_not, not_or, not_exists, not_and] at hf
  exact hf.1 v hv hvI

theorem HasBC_of_vc {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n))
    (hT : ∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) : HasBC G T.card := by
  classical
  let e : Fin T.card ≃ T := (Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  refine ⟨fun i => {(e i).1}, fun i => Finset.univ.filter (fun w => G.Adj (e i).1 w), ?_, ?_⟩
  · intro i a ha b hb
    simp only [Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ha ▸ hb
  · intro a b hab
    rcases hT a b hab with haT | hbT
    · refine ⟨e.symm ⟨a, haT⟩, Or.inl ⟨?_, ?_⟩⟩
      · simp
      · simp [hab]
    · refine ⟨e.symm ⟨b, hbT⟩, Or.inr ⟨?_, ?_⟩⟩
      · simp
      · simp [hab.symm]

theorem bc_le_four_fin6 (G : SimpleGraph (Fin 6)) : ∃ k ≤ 4, HasBC G k := by
  classical
  by_cases hne : ∃ u v : Fin 6, u ≠ v ∧ ¬ G.Adj u v
  · obtain ⟨u, v, huv, hna⟩ := hne
    let T : Finset (Fin 6) := (Finset.univ.erase u).erase v
    have hcard : T.card = 4 := by
      have hv : v ∈ Finset.univ.erase u := Finset.mem_erase.2 ⟨huv.symm, Finset.mem_univ v⟩
      rw [Finset.card_erase_of_mem hv, Finset.card_erase_of_mem (Finset.mem_univ u)]
      decide
    refine ⟨T.card, by omega, HasBC_of_vc G T ?_⟩
    intro a b hab
    by_contra h
    push Not at h
    simp only [T, Finset.mem_erase, Finset.mem_univ, and_true, not_and, not_not] at h
    by_cases ha : a = v
    · by_cases hb : b = v
      · subst ha; subst hb; exact G.loopless.irrefl _ hab
      · have hbu : b = u := h.2 hb
        exact hna (hbu ▸ ha ▸ hab.symm)
    · have hau : a = u := h.1 ha
      by_cases hb : b = v
      · exact hna (hau ▸ hb ▸ hab)
      · have hbu : b = u := h.2 hb
        subst hau; subst hbu; exact G.loopless.irrefl _ hab
  · push Not at hne
    refine ⟨3, by omega,
      fun i => match i.val with | 0 => {0, 2, 4} | 1 => {0, 1, 4, 5} | _ => {0, 1, 2, 3},
      fun i => match i.val with | 0 => {1, 3, 5} | 1 => {2, 3} | _ => {4, 5}, ?_, ?_⟩
    · intro i a ha b hb
      apply hne a b
      fin_cases i <;> fin_cases a <;> fin_cases b <;> simp_all
    · intro a b hab
      have hne' : a ≠ b := G.ne_of_adj hab
      fin_cases a <;> fin_cases b <;> try exact absurd rfl hne'
      all_goals first
        | exact ⟨0, by decide⟩
        | exact ⟨1, by decide⟩
        | exact ⟨2, by decide⟩

/-! ## Section 2: General analytic proof for size ≤ 2 (any n) -/

theorem mis_eq_of_cover {n k : ℕ} (G : SimpleGraph (Fin n)) (Q : Fin k → Finset (Fin n))
    (h1 : ∀ I, IsMIS G I → ∃ t, I ⊆ Q t)
    (h2 : ∀ I, IsMIS G I → ∀ u, u ∉ I → ∀ t, ¬ insert u I ⊆ Q t) :
    ∀ I, IsMIS G I → ∃ t, I = Q t := by
  intro I hmis
  obtain ⟨t, ht⟩ := h1 I hmis
  refine ⟨t, Finset.Subset.antisymm ht ?_⟩
  intro u huQ
  by_contra huI
  exact h2 I hmis u huI t (Finset.insert_subset_iff.2 ⟨huQ, ht⟩)

theorem bc_le_zero_of_one_mis {n : ℕ} (G : SimpleGraph (Fin n)) (Q0 : Finset (Fin n))
    (hQ : ∀ I, IsMIS G I → I = Q0) : HasBC G 0 := by
  refine ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun a b hab => ?_⟩
  exfalso
  obtain ⟨Ia, ha, hma⟩ := exists_mis_mem G a
  obtain ⟨Ib, hb, hmb⟩ := exists_mis_mem G b
  rw [hQ Ia hma] at ha hma
  rw [hQ Ib hmb] at hb
  exact hma.1 a ha b hb hab

theorem bc_le_one_of_two_mis {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Fin 2 → Finset (Fin n))
    (hQ : ∀ I, IsMIS G I → ∃ t : Fin 2, I = Q t) : HasBC G 1 := by
  classical
  by_cases h0 : IsIndep G (Q 0)
  · by_cases h1 : IsIndep G (Q 1)
    · have hadj : ∀ a b, G.Adj a b ↔ ¬ (a ∈ Q 0 ∧ b ∈ Q 0) ∧ ¬ (a ∈ Q 1 ∧ b ∈ Q 1) := by
        intro a b
        constructor
        · intro hab
          exact ⟨fun ⟨ha, hb⟩ => h0 a ha b hb hab, fun ⟨ha, hb⟩ => h1 a ha b hb hab⟩
        · rintro ⟨hn0, hn1⟩
          by_contra hna
          have hind : IsIndep G {a, b} := by
            intro x hx y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact G.loopless.irrefl _
            · exact hna
            · exact fun h => hna h.symm
            · exact G.loopless.irrefl _
          obtain ⟨I, hsub, hmis⟩ := exists_mis_superset G {a, b} hind
          obtain ⟨t, ht⟩ := hQ I hmis
          rw [ht] at hsub
          fin_cases t
          · exact hn0 ⟨hsub (by simp), hsub (by simp)⟩
          · exact hn1 ⟨hsub (by simp), hsub (by simp)⟩
      refine ⟨fun _ => Q 0 \ Q 1, fun _ => Q 1 \ Q 0, ?_, ?_⟩
      · intro _ a ha b hb
        simp only [Finset.mem_sdiff] at ha hb
        exact (hadj a b).2 ⟨fun h => hb.2 h.2, fun h => ha.2 h.1⟩
      · intro a b hab
        obtain ⟨hn0, hn1⟩ := (hadj a b).1 hab
        obtain ⟨Ia, ha, hma⟩ := exists_mis_mem G a
        obtain ⟨Ib, hb, hmb⟩ := exists_mis_mem G b
        obtain ⟨ta, hta⟩ := hQ Ia hma
        obtain ⟨tb, htb⟩ := hQ Ib hmb
        rw [hta] at ha; rw [htb] at hb
        fin_cases ta <;> fin_cases tb
        · exact absurd ⟨ha, hb⟩ hn0
        · refine ⟨0, Or.inl ⟨Finset.mem_sdiff.2 ⟨ha, ?_⟩, Finset.mem_sdiff.2 ⟨hb, ?_⟩⟩⟩
          · exact fun h => hn1 ⟨h, hb⟩
          · exact fun h => hn0 ⟨ha, h⟩
        · refine ⟨0, Or.inr ⟨Finset.mem_sdiff.2 ⟨hb, ?_⟩, Finset.mem_sdiff.2 ⟨ha, ?_⟩⟩⟩
          · exact fun h => hn1 ⟨ha, h⟩
          · exact fun h => hn0 ⟨h, hb⟩
        · exact absurd ⟨ha, hb⟩ hn1
    · have honly : ∀ I, IsMIS G I → I = Q 0 := by
        intro I hmis
        obtain ⟨t, ht⟩ := hQ I hmis
        fin_cases t
        · exact ht
        · exact absurd (ht ▸ hmis.1) h1
      obtain ⟨_, _, _, hno⟩ := bc_le_zero_of_one_mis G (Q 0) honly
      exact ⟨fun _ => ∅, fun _ => ∅, by simp, fun a b hab => (hno a b hab).elim fun i => i.elim0⟩
  · have honly : ∀ I, IsMIS G I → I = Q 1 := by
      intro I hmis
      obtain ⟨t, ht⟩ := hQ I hmis
      fin_cases t
      · exact absurd (ht ▸ hmis.1) h0
      · exact ht
    obtain ⟨_, _, _, hno⟩ := bc_le_zero_of_one_mis G (Q 1) honly
    exact ⟨fun _ => ∅, fun _ => ∅, by simp, fun a b hab => (hno a b hab).elim fun i => i.elim0⟩

theorem bc_le_two_of_three_indep {n : ℕ} (G : SimpleGraph (Fin n)) (M : Fin 3 → Finset (Fin n))
    (hI : ∀ r, IsIndep G (M r))
    (hQ : ∀ I, IsMIS G I → ∃ r : Fin 3, I = M r) : HasBC G 2 := by
  classical
  have hadj : ∀ a b, G.Adj a b ↔ ∀ r : Fin 3, ¬ (a ∈ M r ∧ b ∈ M r) := by
    intro a b
    constructor
    · intro hab r ⟨ha, hb⟩; exact hI r a ha b hb hab
    · intro hall
      by_contra hna
      have hind : IsIndep G {a, b} := by
        intro x hx y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact G.loopless.irrefl _
        · exact hna
        · exact fun h => hna h.symm
        · exact G.loopless.irrefl _
      obtain ⟨I, hsub, hmis⟩ := exists_mis_superset G {a, b} hind
      obtain ⟨r, hr⟩ := hQ I hmis
      rw [hr] at hsub
      exact hall r ⟨hsub (by simp), hsub (by simp)⟩
  have hmem : ∀ x : Fin n, ∃ r : Fin 3, x ∈ M r := by
    intro x
    obtain ⟨I, hx, hm⟩ := exists_mis_mem G x
    obtain ⟨r, hr⟩ := hQ I hm
    exact ⟨r, hr ▸ hx⟩
  have hsub_of : ∀ (M0 M1 M2 : Finset (Fin n)),
      (∀ a b, G.Adj a b ↔ ¬ (a ∈ M0 ∧ b ∈ M0) ∧ ¬ (a ∈ M1 ∧ b ∈ M1) ∧ ¬ (a ∈ M2 ∧ b ∈ M2)) →
      (∀ x : Fin n, x ∈ M0 ∨ x ∈ M1 ∨ x ∈ M2) →
      (∀ x : Fin n, x ∈ M0 → x ∈ M1 → x ∈ M2) → HasBC G 2 := by
    intro M0 M1 M2 hA hM hP
    refine ⟨fun i => if i.val = 0 then M0 \ (M1 ∪ M2) else M1 \ (M0 ∪ M2),
            fun i => if i.val = 0 then Finset.univ \ M0 else Finset.univ \ M1, ?_, ?_⟩
    · intro i a ha b hb
      fin_cases i
      · simp only [Fin.zero_eta, Fin.val_zero, ↓reduceIte, Finset.mem_sdiff, Finset.mem_union,
          not_or, Finset.mem_univ, true_and] at ha hb
        exact (hA a b).2 ⟨fun h => hb h.2, fun h => ha.2.1 h.1, fun h => ha.2.2 h.1⟩
      · simp only [Fin.mk_one, Fin.val_one, one_ne_zero, ↓reduceIte, Finset.mem_sdiff,
          Finset.mem_union, not_or, Finset.mem_univ, true_and] at ha hb
        exact (hA a b).2 ⟨fun h => ha.2.1 h.1, fun h => hb h.2, fun h => ha.2.2 h.1⟩
    · intro a b hab
      obtain ⟨hn0, hn1, hn2⟩ := (hA a b).1 hab
      have hcov : ∀ x, (x ∉ M0 \ (M1 ∪ M2)) → (x ∉ M1 \ (M0 ∪ M2)) → x ∈ M2 := by
        intro x h0 h1
        simp only [Finset.mem_sdiff, Finset.mem_union, not_and, not_not] at h0 h1
        rcases hM x with hx0 | hx1 | hx2
        · rcases h0 hx0 with hx1 | hx2
          · exact hP x hx0 hx1
          · exact hx2
        · rcases h1 hx1 with hx0 | hx2
          · exact hP x hx0 hx1
          · exact hx2
        · exact hx2
      by_cases ha0 : a ∈ M0 \ (M1 ∪ M2)
      · refine ⟨0, Or.inl ⟨by simpa using ha0, ?_⟩⟩
        simp only [Fin.zero_eta, Fin.val_zero, ↓reduceIte, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact fun hb0 => hn0 ⟨(Finset.mem_sdiff.1 ha0).1, hb0⟩
      · by_cases ha1 : a ∈ M1 \ (M0 ∪ M2)
        · refine ⟨1, Or.inl ⟨by simpa using ha1, ?_⟩⟩
          simp only [Fin.mk_one, Fin.val_one, one_ne_zero, ↓reduceIte, Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact fun hb1 => hn1 ⟨(Finset.mem_sdiff.1 ha1).1, hb1⟩
        · have ha2 : a ∈ M2 := hcov a ha0 ha1
          by_cases hb0 : b ∈ M0 \ (M1 ∪ M2)
          · refine ⟨0, Or.inr ⟨by simpa using hb0, ?_⟩⟩
            simp only [Fin.zero_eta, Fin.val_zero, ↓reduceIte, Finset.mem_sdiff, Finset.mem_univ, true_and]
            exact fun ha0' => hn0 ⟨ha0', (Finset.mem_sdiff.1 hb0).1⟩
          · by_cases hb1 : b ∈ M1 \ (M0 ∪ M2)
            · refine ⟨1, Or.inr ⟨by simpa using hb1, ?_⟩⟩
              simp only [Fin.mk_one, Fin.val_one, one_ne_zero, ↓reduceIte, Finset.mem_sdiff, Finset.mem_univ, true_and]
              exact fun ha1' => hn1 ⟨ha1', (Finset.mem_sdiff.1 hb1).1⟩
            · exact absurd ⟨ha2, hcov b hb0 hb1⟩ hn2
  have hA0 : ∀ a b, G.Adj a b ↔ ¬ (a ∈ M 0 ∧ b ∈ M 0) ∧ ¬ (a ∈ M 1 ∧ b ∈ M 1) ∧ ¬ (a ∈ M 2 ∧ b ∈ M 2) := by
    intro a b; rw [hadj]; simp [Fin.forall_fin_succ]
  have hM0 : ∀ x, x ∈ M 0 ∨ x ∈ M 1 ∨ x ∈ M 2 := by
    intro x; obtain ⟨r, hr⟩ := hmem x
    fin_cases r
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr hr)
  by_cases hP2 : ∀ x, x ∈ M 0 → x ∈ M 1 → x ∈ M 2
  · exact hsub_of (M 0) (M 1) (M 2) hA0 hM0 hP2
  · by_cases hP1 : ∀ x, x ∈ M 0 → x ∈ M 2 → x ∈ M 1
    · exact hsub_of (M 0) (M 2) (M 1) (fun a b => by rw [hA0]; tauto) (fun x => by have := hM0 x; tauto) hP1
    · by_cases hP0 : ∀ x, x ∈ M 1 → x ∈ M 2 → x ∈ M 0
      · exact hsub_of (M 1) (M 2) (M 0) (fun a b => by rw [hA0]; tauto) (fun x => by have := hM0 x; tauto) hP0
      · exfalso
        push Not at hP2 hP1 hP0
        obtain ⟨p2, hp20, hp21, hp22⟩ := hP2
        obtain ⟨p1, hp10, hp12, hp11⟩ := hP1
        obtain ⟨p0, hp01, hp02, hp00⟩ := hP0
        have hind : IsIndep G {p0, p1, p2} := by
          intro x hx y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          · exact G.loopless.irrefl _
          · exact hI 2 _ hp02 _ hp12
          · exact hI 1 _ hp01 _ hp21
          · exact hI 2 _ hp12 _ hp02
          · exact G.loopless.irrefl _
          · exact hI 0 _ hp10 _ hp20
          · exact hI 1 _ hp21 _ hp01
          · exact hI 0 _ hp20 _ hp10
          · exact G.loopless.irrefl _
        obtain ⟨I, hsub, hmis⟩ := exists_mis_superset G {p0, p1, p2} hind
        obtain ⟨r, hr⟩ := hQ I hmis
        rw [hr] at hsub
        fin_cases r
        · exact hp00 (hsub (by simp))
        · exact hp11 (hsub (by simp))
        · exact hp22 (hsub (by simp))

theorem bc_le_two_of_three_mis {n : ℕ} (G : SimpleGraph (Fin n)) (Q : Fin 3 → Finset (Fin n))
    (hQ : ∀ I, IsMIS G I → ∃ r : Fin 3, I = Q r) : HasBC G 2 := by
  classical
  by_cases he : ∃ r : Fin 3, IsIndep G (Q r)
  · obtain ⟨r0, hr0⟩ := he
    let M : Fin 3 → Finset (Fin n) := fun r => if IsIndep G (Q r) then Q r else Q r0
    apply bc_le_two_of_three_indep G M
    · intro r; dsimp only [M]; split_ifs with h <;> assumption
    · intro I hmis
      obtain ⟨r, hr⟩ := hQ I hmis
      refine ⟨r, ?_⟩
      dsimp only [M]
      rw [if_pos (hr ▸ hmis.1)]
      exact hr
  · push Not at he
    refine ⟨fun _ => ∅, fun _ => ∅, by simp, fun a b hab => ?_⟩
    exfalso
    obtain ⟨I, _, hmis⟩ := exists_mis_mem G a
    obtain ⟨r, hr⟩ := hQ I hmis
    exact he r (hr ▸ hmis.1)

theorem size_zero_ok {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hsz : C.size = 0) (hP : PartialCond G C) : HasBC G 0 := by
  have hov := outVars_empty G C hP
  refine ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun a b hab => ?_⟩
  exfalso
  obtain ⟨I, ha, hmis⟩ := exists_mis_mem G a
  have hbI : b ∉ I := fun hb => hmis.1 a ha b hb hab
  have ht := (hP I hmis).2 b hbI
  unfold AndCountCircuit.eval at ht
  rw [hov] at ht
  simp only [Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_true_eq] at ht
  obtain ⟨j, _, _⟩ := ht
  have := j.isLt
  omega

theorem size_one_ok {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hW : C.WellFormed) (hsz : C.size = 1) (hP : PartialCond G C) : HasBC G 1 := by
  have hov := outVars_empty G C hP
  let g0 : Fin C.size := ⟨0, by omega⟩
  have hev : ∀ U, C.eval U = true ↔
      g0 ∈ C.outGates ∧ (∃ v ∈ C.leftVars g0, v ∈ U) ∧ (∃ v ∈ C.rightVars g0, v ∈ U) := by
    intro U
    unfold AndCountCircuit.eval
    rw [hov]
    simp only [Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_true_eq]
    constructor
    · rintro ⟨j, hj, hgv⟩
      have hjeq : j = g0 := Fin.ext (by have := j.isLt; omega)
      subst hjeq
      rw [gv_iff C hW U g0] at hgv
      have hl : ∀ k ∈ C.leftGates g0, False := fun k hk => by
        have := (hW g0).1 k hk; exact Nat.not_lt_zero k.val this
      have hr : ∀ k ∈ C.rightGates g0, False := fun k hk => by
        have := (hW g0).2 k hk; exact Nat.not_lt_zero k.val this
      rcases hgv with ⟨h1 | ⟨k, hk, _⟩, h2 | ⟨k', hk', _⟩⟩
      · exact ⟨hj, h1, h2⟩
      · exact (hr k' hk').elim
      · exact (hl k hk).elim
      · exact (hl k hk).elim
    · rintro ⟨hj, h1, h2⟩
      exact ⟨g0, hj, (gv_iff C hW U g0).2 ⟨Or.inl h1, Or.inl h2⟩⟩
  let Q : Fin 2 → Finset (Fin n) :=
    fun t => if t.val = 0 then Finset.univ \ C.leftVars g0 else Finset.univ \ C.rightVars g0
  by_cases hg0 : g0 ∈ C.outGates
  · apply bc_le_one_of_two_mis G Q
    apply mis_eq_of_cover G Q
    · intro I hmis
      have hf := (hP I hmis).1
      have hn : ¬ C.eval I = true := by simp [hf]
      rw [hev] at hn
      push Not at hn
      by_cases hL : ∃ v ∈ C.leftVars g0, v ∈ I
      · refine ⟨1, fun x hx => ?_⟩
        simp only [Q, Fin.mk_one, Fin.val_one, one_ne_zero, ↓reduceIte, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact fun hxR => hn hg0 hL x hxR hx
      · refine ⟨0, fun x hx => ?_⟩
        simp only [Q, Fin.zero_eta, Fin.val_zero, ↓reduceIte, Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact fun hxL => hL ⟨x, hxL, hx⟩
    · intro I hmis u huI t ht
      have htrue := (hev (insert u I)).1 ((hP I hmis).2 u huI)
      fin_cases t
      · obtain ⟨v, hvL, hvU⟩ := htrue.2.1
        have := ht hvU
        simp [Q, hvL] at this
      · obtain ⟨v, hvR, hvU⟩ := htrue.2.2
        have := ht hvU
        simp [Q, hvR] at this
  · refine ⟨fun _ => ∅, fun _ => ∅, by simp, fun a b hab => ?_⟩
    exfalso
    obtain ⟨I, ha, hmis⟩ := exists_mis_mem G a
    have hbI : b ∉ I := fun hb => hmis.1 a ha b hb hab
    exact hg0 ((hev (insert b I)).1 ((hP I hmis).2 b hbI)).1

theorem size_two_ok {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hW : C.WellFormed) (hsz : C.size = 2) (hP : PartialCond G C) : HasBC G 2 := by
  classical
  have hov := outVars_empty G C hP
  let g0 : Fin C.size := ⟨0, by omega⟩
  let g1 : Fin C.size := ⟨1, by omega⟩
  have hfin2 : ∀ j : Fin C.size, j = g0 ∨ j = g1 := by
    intro j; have := j.isLt
    by_cases h : j.val = 0
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (by dsimp [g1]; omega))
  have hg0_iff : ∀ U, C.gateVal U g0 = true ↔
      (∃ v ∈ C.leftVars g0, v ∈ U) ∧ (∃ v ∈ C.rightVars g0, v ∈ U) := by
    intro U
    rw [gv_iff C hW U g0]
    have hl : ∀ k ∈ C.leftGates g0, False := fun k hk => Nat.not_lt_zero k.val ((hW g0).1 k hk)
    have hr : ∀ k ∈ C.rightGates g0, False := fun k hk => Nat.not_lt_zero k.val ((hW g0).2 k hk)
    constructor
    · rintro ⟨h1 | ⟨k, hk, _⟩, h2 | ⟨k', hk', _⟩⟩
      · exact ⟨h1, h2⟩
      · exact (hr k' hk').elim
      · exact (hl k hk).elim
      · exact (hl k hk).elim
    · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, Or.inl h2⟩
  have hg1_iff : ∀ U, C.gateVal U g1 = true ↔
      ((∃ v ∈ C.leftVars g1, v ∈ U) ∨ (g0 ∈ C.leftGates g1 ∧ C.gateVal U g0 = true)) ∧
      ((∃ v ∈ C.rightVars g1, v ∈ U) ∨ (g0 ∈ C.rightGates g1 ∧ C.gateVal U g0 = true)) := by
    intro U
    rw [gv_iff C hW U g1]
    have hlt1 : ∀ k : Fin C.size, k < g1 → k = g0 := fun k hk => Fin.ext (by
      have : k.val < g1.val := Fin.lt_def.1 hk
      dsimp [g0, g1] at this ⊢; omega)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rcases h1 with h | ⟨k, hk, hv⟩
        · exact Or.inl h
        · have hk0 := hlt1 k ((hW g1).1 k hk); subst hk0; exact Or.inr ⟨hk, hv⟩
      · rcases h2 with h | ⟨k, hk, hv⟩
        · exact Or.inl h
        · have hk0 := hlt1 k ((hW g1).2 k hk); subst hk0; exact Or.inr ⟨hk, hv⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rcases h1 with h | ⟨hk, hv⟩
        · exact Or.inl h
        · exact Or.inr ⟨g0, hk, hv⟩
      · rcases h2 with h | ⟨hk, hv⟩
        · exact Or.inl h
        · exact Or.inr ⟨g0, hk, hv⟩
  have hev : ∀ U, C.eval U = true ↔
      (g0 ∈ C.outGates ∧ C.gateVal U g0 = true) ∨ (g1 ∈ C.outGates ∧ C.gateVal U g1 = true) := by
    intro U
    unfold AndCountCircuit.eval; rw [hov]
    simp only [Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_true_eq]
    constructor
    · rintro ⟨j, hj, hv⟩
      rcases hfin2 j with rfl | rfl
      · exact Or.inl ⟨hj, hv⟩
      · exact Or.inr ⟨hj, hv⟩
    · rintro (⟨hj, hv⟩ | ⟨hj, hv⟩)
      · exact ⟨g0, hj, hv⟩
      · exact ⟨g1, hj, hv⟩
  have case2A : ∀ (L0 R0 L1 R1 : Finset (Fin n)),
      (∀ U, C.eval U = true ↔
        ((∃ v ∈ L0, v ∈ U) ∧ (∃ v ∈ R0, v ∈ U)) ∨ ((∃ v ∈ L1, v ∈ U) ∧ (∃ v ∈ R1, v ∈ U))) →
      HasBC G 2 := by
    intro L0 R0 L1 R1 hE
    let Q : Fin 4 → Finset (Fin n) := fun t => match t.val with
      | 0 => Finset.univ \ (L0 ∪ L1)
      | 1 => Finset.univ \ (L0 ∪ R1)
      | 2 => Finset.univ \ (R0 ∪ L1)
      | _ => Finset.univ \ (R0 ∪ R1)
    have hQ : ∀ I, IsMIS G I → ∃ t : Fin 4, I = Q t := by
      apply mis_eq_of_cover G Q
      · intro I hmis
        have hf : ¬ C.eval I = true := by simp [(hP I hmis).1]
        rw [hE] at hf
        push Not at hf
        by_cases hL0 : ∃ v ∈ L0, v ∈ I
        · by_cases hL1 : ∃ v ∈ L1, v ∈ I
          · refine ⟨3, fun x hx => ?_⟩
            change x ∈ Finset.univ \ (R0 ∪ R1)
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
            exact ⟨fun h => hf.1 hL0 x h hx, fun h => hf.2 hL1 x h hx⟩
          · refine ⟨2, fun x hx => ?_⟩
            change x ∈ Finset.univ \ (R0 ∪ L1)
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
            exact ⟨fun h => hf.1 hL0 x h hx, fun h => hL1 ⟨x, h, hx⟩⟩
        · by_cases hL1 : ∃ v ∈ L1, v ∈ I
          · refine ⟨1, fun x hx => ?_⟩
            change x ∈ Finset.univ \ (L0 ∪ R1)
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
            exact ⟨fun h => hL0 ⟨x, h, hx⟩, fun h => hf.2 hL1 x h hx⟩
          · refine ⟨0, fun x hx => ?_⟩
            change x ∈ Finset.univ \ (L0 ∪ L1)
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
            exact ⟨fun h => hL0 ⟨x, h, hx⟩, fun h => hL1 ⟨x, h, hx⟩⟩
      · intro I hmis u huI t ht
        have htr := (hE (insert u I)).1 ((hP I hmis).2 u huI)
        fin_cases t <;> rcases htr with ⟨⟨a, ha, haU⟩, ⟨b, hb, hbU⟩⟩ | ⟨⟨a, ha, haU⟩, ⟨b, hb, hbU⟩⟩
        · have := ht haU; simp [Q, ha] at this
        · have := ht haU; simp [Q, ha] at this
        · have := ht haU; simp [Q, ha] at this
        · have := ht hbU; simp [Q, hb] at this
        · have := ht hbU; simp [Q, hb] at this
        · have := ht haU; simp [Q, ha] at this
        · have := ht hbU; simp [Q, hb] at this
        · have := ht hbU; simp [Q, hb] at this
    by_cases hall : ∀ t : Fin 4, IsIndep G (Q t)
    · refine ⟨fun i => if i.val = 0 then L0 else L1, fun i => if i.val = 0 then R0 else R1, ?_, ?_⟩
      · intro i a ha b hb
        fin_cases i
        · simp only [Fin.zero_eta, Fin.val_zero, ↓reduceIte] at ha hb
          by_contra hna
          have hind : IsIndep G {a, b} := by
            intro x hx y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact G.loopless.irrefl _
            · exact hna
            · exact fun h => hna h.symm
            · exact G.loopless.irrefl _
          obtain ⟨I, hsub, hmis⟩ := exists_mis_superset G {a, b} hind
          have htr : C.eval I = true := (hE I).2 (Or.inl ⟨⟨a, ha, hsub (by simp)⟩, ⟨b, hb, hsub (by simp)⟩⟩)
          have hf := (hP I hmis).1
          rw [htr] at hf; cases hf
        · simp only [Fin.mk_one, Fin.val_one, one_ne_zero, ↓reduceIte] at ha hb
          by_contra hna
          have hind : IsIndep G {a, b} := by
            intro x hx y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
            · exact G.loopless.irrefl _
            · exact hna
            · exact fun h => hna h.symm
            · exact G.loopless.irrefl _
          obtain ⟨I, hsub, hmis⟩ := exists_mis_superset G {a, b} hind
          have htr : C.eval I = true := (hE I).2 (Or.inr ⟨⟨a, ha, hsub (by simp)⟩, ⟨b, hb, hsub (by simp)⟩⟩)
          have hf := (hP I hmis).1
          rw [htr] at hf; cases hf
      · intro a b hab
        by_contra hunc
        push Not at hunc
        have h0 := hunc 0
        have h1 := hunc 1
        simp only [Fin.zero_eta, Fin.val_zero, ↓reduceIte, Fin.mk_one, Fin.val_one, one_ne_zero,
          not_or, not_and] at h0 h1
        have hs0 : (a ∉ L0 ∧ b ∉ L0) ∨ (a ∉ R0 ∧ b ∉ R0) := by
          by_cases haL : a ∈ L0
          · by_cases hbL : b ∈ L0
            · exact Or.inr ⟨fun haR => h0.2 hbL haR, fun hbR => h0.1 haL hbR⟩
            · exact Or.inr ⟨fun haR => (by
                obtain ⟨I, haI, hm⟩ := exists_mis_mem G a
                have ht : C.eval I = true := (hE I).2 (Or.inl ⟨⟨a, haL, haI⟩, ⟨a, haR, haI⟩⟩)
                have hf := (hP I hm).1; rw [ht] at hf; cases hf),
                fun hbR => h0.1 haL hbR⟩
          · by_cases hbL : b ∈ L0
            · exact Or.inr ⟨fun haR => h0.2 hbL haR, fun hbR => (by
                obtain ⟨I, hbI, hm⟩ := exists_mis_mem G b
                have ht : C.eval I = true := (hE I).2 (Or.inl ⟨⟨b, hbL, hbI⟩, ⟨b, hbR, hbI⟩⟩)
                have hf := (hP I hm).1; rw [ht] at hf; cases hf)⟩
            · exact Or.inl ⟨haL, hbL⟩
        have hs1 : (a ∉ L1 ∧ b ∉ L1) ∨ (a ∉ R1 ∧ b ∉ R1) := by
          by_cases haL : a ∈ L1
          · by_cases hbL : b ∈ L1
            · exact Or.inr ⟨fun haR => h1.2 hbL haR, fun hbR => h1.1 haL hbR⟩
            · exact Or.inr ⟨fun haR => (by
                obtain ⟨I, haI, hm⟩ := exists_mis_mem G a
                have ht : C.eval I = true := (hE I).2 (Or.inr ⟨⟨a, haL, haI⟩, ⟨a, haR, haI⟩⟩)
                have hf := (hP I hm).1; rw [ht] at hf; cases hf),
                fun hbR => h1.1 haL hbR⟩
          · by_cases hbL : b ∈ L1
            · exact Or.inr ⟨fun haR => h1.2 hbL haR, fun hbR => (by
                obtain ⟨I, hbI, hm⟩ := exists_mis_mem G b
                have ht : C.eval I = true := (hE I).2 (Or.inr ⟨⟨b, hbL, hbI⟩, ⟨b, hbR, hbI⟩⟩)
                have hf := (hP I hm).1; rw [ht] at hf; cases hf)⟩
            · exact Or.inl ⟨haL, hbL⟩
        rcases hs0 with ⟨ha0, hb0⟩ | ⟨ha0, hb0⟩ <;> rcases hs1 with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
        · exact hall 0 a (by simp [Q, ha0, ha1]) b (by simp [Q, hb0, hb1]) hab
        · exact hall 1 a (by simp [Q, ha0, ha1]) b (by simp [Q, hb0, hb1]) hab
        · exact hall 2 a (by simp [Q, ha0, ha1]) b (by simp [Q, hb0, hb1]) hab
        · exact hall 3 a (by simp [Q, ha0, ha1]) b (by simp [Q, hb0, hb1]) hab
    · push Not at hall
      obtain ⟨tbad, hbad⟩ := hall
      let Q' : Fin 3 → Finset (Fin n) := fun r =>
        if r.val < tbad.val then Q ⟨r.val, by omega⟩ else Q ⟨r.val + 1, by omega⟩
      apply bc_le_two_of_three_mis G Q'
      intro I hmis
      obtain ⟨t, ht⟩ := hQ I hmis
      have hne : t ≠ tbad := fun e => hbad (e ▸ ht ▸ hmis.1)
      have hne' : t.val ≠ tbad.val := fun e => hne (Fin.ext e)
      have htlt := t.isLt
      have htblt := tbad.isLt
      by_cases hlt : t.val < tbad.val
      · refine ⟨⟨t.val, by omega⟩, ?_⟩
        simp only [Q', hlt, ↓reduceIte]; exact ht
      · refine ⟨⟨t.val - 1, by omega⟩, ?_⟩
        dsimp only [Q']
        rw [if_neg (by omega)]
        exact ht.trans (congrArg Q (Fin.ext (by dsimp; omega)))
  have case2B : ∀ (A B L0 R0 : Finset (Fin n)),
      (∀ U, C.eval U = true ↔
        (∃ v ∈ A, v ∈ U) ∧ ((∃ v ∈ B, v ∈ U) ∨ ((∃ v ∈ L0, v ∈ U) ∧ (∃ v ∈ R0, v ∈ U)))) →
      HasBC G 2 := by
    intro A B L0 R0 hE
    let Q : Fin 3 → Finset (Fin n) := fun t => match t.val with
      | 0 => Finset.univ \ A
      | 1 => Finset.univ \ (B ∪ L0)
      | _ => Finset.univ \ (B ∪ R0)
    apply bc_le_two_of_three_mis G Q
    apply mis_eq_of_cover G Q
    · intro I hmis
      have hf : ¬ C.eval I = true := by simp [(hP I hmis).1]
      rw [hE] at hf
      push Not at hf
      by_cases hA : ∃ v ∈ A, v ∈ I
      · have hB := (hf hA).1
        have h0 := (hf hA).2
        by_cases hL0 : ∃ v ∈ L0, v ∈ I
        · refine ⟨2, fun x hx => ?_⟩
          change x ∈ Finset.univ \ (B ∪ R0)
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
          exact ⟨fun h => hB x h hx, fun h => h0 hL0 x h hx⟩
        · refine ⟨1, fun x hx => ?_⟩
          change x ∈ Finset.univ \ (B ∪ L0)
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
          exact ⟨fun h => hB x h hx, fun h => hL0 ⟨x, h, hx⟩⟩
      · refine ⟨0, fun x hx => ?_⟩
        change x ∈ Finset.univ \ A
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact fun h => hA ⟨x, h, hx⟩
    · intro I hmis u huI t ht
      have htr := (hE (insert u I)).1 ((hP I hmis).2 u huI)
      fin_cases t
      · obtain ⟨v, hvA, hvU⟩ := htr.1
        have := ht hvU; simp [Q, hvA] at this
      · rcases htr.2 with ⟨v, hvB, hvU⟩ | ⟨⟨v, hvL, hvU⟩, _⟩
        · have := ht hvU; simp [Q, hvB] at this
        · have := ht hvU; simp [Q, hvL] at this
      · rcases htr.2 with ⟨v, hvB, hvU⟩ | ⟨_, ⟨v, hvR, hvU⟩⟩
        · have := ht hvU; simp [Q, hvB] at this
        · have := ht hvU; simp [Q, hvR] at this
  by_cases ho1 : g1 ∈ C.outGates
  · by_cases ho0 : g0 ∈ C.outGates
    · apply case2A (C.leftVars g0) (C.rightVars g0) (C.leftVars g1) (C.rightVars g1)
      intro U; rw [hev U, hg1_iff U, hg0_iff U]
      simp only [ho0, ho1, true_and]
      constructor
      · rintro (h0 | ⟨h1 | ⟨_, h0⟩, h2 | ⟨_, h0⟩⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨h1, h2⟩
        · exact Or.inl h0
        · exact Or.inl h0
        · exact Or.inl h0
      · rintro (h0 | ⟨h1, h2⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨Or.inl h1, Or.inl h2⟩
    · by_cases hl0 : g0 ∈ C.leftGates g1
      · by_cases hr0 : g0 ∈ C.rightGates g1
        · apply case2A (C.leftVars g0) (C.rightVars g0) (C.leftVars g1) (C.rightVars g1)
          intro U; rw [hev U, hg1_iff U, hg0_iff U]
          simp only [ho0, ho1, hl0, hr0, true_and, false_and, false_or]
          constructor
          · rintro ⟨h1 | h0, h2 | h0⟩
            · exact Or.inr ⟨h1, h2⟩
            · exact Or.inl h0
            · exact Or.inl h0
            · exact Or.inl h0
          · rintro (h0 | ⟨h1, h2⟩)
            · exact ⟨Or.inr h0, Or.inr h0⟩
            · exact ⟨Or.inl h1, Or.inl h2⟩
        · apply case2B (C.rightVars g1) (C.leftVars g1) (C.leftVars g0) (C.rightVars g0)
          intro U; rw [hev U, hg1_iff U, hg0_iff U]
          simp only [ho0, ho1, hl0, hr0, true_and, false_and, false_or, or_false]
          exact and_comm
      · by_cases hr0 : g0 ∈ C.rightGates g1
        · apply case2B (C.leftVars g1) (C.rightVars g1) (C.leftVars g0) (C.rightVars g0)
          intro U; rw [hev U, hg1_iff U, hg0_iff U]
          simp only [ho0, ho1, hl0, hr0, true_and, false_and, false_or, or_false]
        · apply case2A ∅ ∅ (C.leftVars g1) (C.rightVars g1)
          intro U; rw [hev U, hg1_iff U]
          simp only [ho0, ho1, hl0, hr0, true_and, false_and, false_or, or_false,
            Finset.notMem_empty, exists_false]
  · by_cases ho0 : g0 ∈ C.outGates
    · apply case2A (C.leftVars g0) (C.rightVars g0) ∅ ∅
      intro U; rw [hev U, hg0_iff U]
      simp only [ho0, ho1, true_and, false_and, or_false, Finset.notMem_empty, exists_false]
    · apply case2A ∅ ∅ ∅ ∅
      intro U; rw [hev U]
      simp only [ho0, ho1, false_and, or_false, Finset.notMem_empty, exists_false]

/-! ## Section 3: The 5 canonical bc = 4 graphs on Fin 6 have no 3-gate circuit -/

theorem testBit_eq_false_of_lt64 {m k : ℕ} (hm : m < 64) (hk : ¬ k < 6) : m.testBit k = false := by
  apply Nat.testBit_lt_two_pow
  have h1 : 6 ≤ k := by omega
  have h2 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) h1
  omega

theorem testBit_63 {k : ℕ} (hk : k < 6) : Nat.testBit 63 k = true := by
  interval_cases k <;> decide

theorem sub_xor_ne_zero {a b u : ℕ} (ha : a < 64) (hba : (b &&& a) = 0) (hua : (u &&& a) ≠ 0) :
    (u &&& (63 ^^^ b)) ≠ 0 := by
  intro h0
  apply hua
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hk : k < 6
  · have h63 : Nat.testBit 63 k = true := testBit_63 hk
    have h1 := congrArg (fun x => x.testBit k) hba
    have h2 := congrArg (fun x => x.testBit k) h0
    rw [Nat.testBit_and, Nat.zero_testBit] at h1
    rw [Nat.testBit_and, Nat.testBit_xor, h63, Nat.zero_testBit] at h2
    cases ha' : a.testBit k <;> cases hb' : b.testBit k <;> cases hu' : u.testBit k <;> simp_all
  · simp [testBit_eq_false_of_lt64 ha hk]

def bitOf (S : Finset (Fin 6)) (k : Fin 6) : Nat :=
  if k ∈ S then 1 <<< k.val else 0

def maskOf (S : Finset (Fin 6)) : Nat :=
  bitOf S 0 ||| bitOf S 1 ||| bitOf S 2 ||| bitOf S 3 ||| bitOf S 4 ||| bitOf S 5

theorem testBit_bitOf (S : Finset (Fin 6)) (k i : Fin 6) :
    (bitOf S k).testBit i.val = (decide (k = i) && decide (k ∈ S)) := by
  unfold bitOf
  by_cases h : k ∈ S
  · rw [if_pos h, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
    by_cases hki : k = i
    · subst hki; simp [h]
    · have hne : k.val ≠ i.val := fun e => hki (Fin.ext e)
      simp [h, hki, hne]
  · rw [if_neg h]; simp [h]

theorem testBit_maskOf (S : Finset (Fin 6)) (i : Fin 6) :
    (maskOf S).testBit i.val = decide (i ∈ S) := by
  simp only [maskOf, Nat.testBit_or, testBit_bitOf]
  fin_cases i <;> simp

theorem maskOf_lt (S : Finset (Fin 6)) : maskOf S < 64 := by
  have hb : ∀ k : Fin 6, bitOf S k < 2 ^ 6 := fun k => by
    unfold bitOf
    split_ifs
    · fin_cases k <;> decide
    · omega
  show maskOf S < 2 ^ 6
  unfold maskOf
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow
    (Nat.or_lt_two_pow (hb 0) (hb 1)) (hb 2)) (hb 3)) (hb 4)) (hb 5)

theorem maskOf_and_ne_zero (A B : Finset (Fin 6)) :
    (maskOf A &&& maskOf B ≠ 0) ↔ ∃ v ∈ A, v ∈ B := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    apply h
    apply Nat.eq_of_testBit_eq
    intro m
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hm : m < 6
    · let i : Fin 6 := ⟨m, hm⟩
      change ((maskOf A).testBit i.val && (maskOf B).testBit i.val) = false
      rw [testBit_maskOf, testBit_maskOf]
      by_cases hA : i ∈ A
      · simp [hA, hno i hA]
      · simp [hA]
    · simp [testBit_eq_false_of_lt64 (maskOf_lt A) hm]
  · rintro ⟨v, hvA, hvB⟩ h0
    have := congrArg (fun x => x.testBit v.val) h0
    rw [Nat.testBit_and, testBit_maskOf, testBit_maskOf, Nat.zero_testBit] at this
    simp [hvA, hvB] at this

theorem maskOf_eq_iff (A B : Finset (Fin 6)) : maskOf A = maskOf B ↔ A = B := by
  constructor
  · intro h
    ext i
    have := congrArg (fun x => x.testBit i.val) h
    rw [testBit_maskOf, testBit_maskOf] at this
    simpa using this
  · intro h; rw [h]

def setOfMask (m : Nat) : Finset (Fin 6) :=
  Finset.univ.filter fun i : Fin 6 => m.testBit i.val

theorem mem_setOfMask (m : Nat) (i : Fin 6) : i ∈ setOfMask m ↔ m.testBit i.val = true := by
  simp [setOfMask]

theorem maskOf_setOfMask (m : Nat) (hm : m < 64) : maskOf (setOfMask m) = m := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 6
  · let i : Fin 6 := ⟨k, hk⟩
    change (maskOf (setOfMask m)).testBit i.val = m.testBit i.val
    rw [testBit_maskOf]
    cases h : m.testBit i.val <;> simp [mem_setOfMask, h]
  · rw [testBit_eq_false_of_lt64 (maskOf_lt _) hk, testBit_eq_false_of_lt64 hm hk]

def canonAdj : Nat → Nat → Nat
  | 0, 0 => 34 | 0, 1 => 33 | 0, 2 => 24 | 0, 3 => 20 | 0, 4 => 12 | 0, 5 => 3
  | 1, 0 => 38 | 1, 1 => 33 | 1, 2 => 25 | 1, 3 => 20 | 1, 4 => 12 | 1, 5 => 3
  | 2, 0 => 46 | 2, 1 => 33 | 2, 2 => 25 | 2, 3 => 21 | 2, 4 => 12 | 2, 5 => 3
  | 3, 0 => 62 | 3, 1 => 33 | 3, 2 => 25 | 3, 3 => 21 | 3, 4 => 13 | 3, 5 => 3
  | 4, 0 => 56 | 4, 1 => 36 | 4, 2 => 26 | 4, 3 => 21 | 4, 4 => 13 | 4, 5 => 3
  | _, _ => 0

theorem canonAdj_symm : ∀ c < 5, ∀ u v : Fin 6,
    (canonAdj c u.val).testBit v.val = (canonAdj c v.val).testBit u.val := by decide +kernel

theorem canonAdj_irrefl : ∀ c < 5, ∀ u : Fin 6, (canonAdj c u.val).testBit u.val = false := by
  decide +kernel

def canonG (c : Nat) (hc : c < 5) : SimpleGraph (Fin 6) where
  Adj u v := (canonAdj c u.val).testBit v.val = true
  symm := ⟨fun u v h => by rw [canonAdj_symm c hc u v] at h; exact h⟩
  loopless := ⟨fun u h => by rw [canonAdj_irrefl c hc u] at h; cases h⟩

def isIndepMask (adj : Nat → Nat) (m : Nat) : Bool :=
  (List.range 6).all fun a => !(m.testBit a) || ((adj a &&& m) == 0)

def isMISMask (adj : Nat → Nat) (m : Nat) : Bool :=
  isIndepMask adj m &&
    (List.range 6).all fun u => m.testBit u || ((adj u &&& m) != 0)

def misList (c : Nat) : List Nat :=
  (List.range 64).filter (isMISMask (canonAdj c))

def onesList (c : Nat) : List Nat :=
  (misList c).flatMap fun m =>
    (List.range 6).filterMap fun u => if m.testBit u then none else some (m ||| (1 <<< u))

def cnMask (adj : Nat → Nat) (s : Nat) : Nat :=
  (List.range 6).foldl (fun acc a => if s.testBit a then acc &&& adj a else acc) 63

def maxBicMask (c : Nat) : List (Nat × Nat) :=
  let adj := canonAdj c
  ((List.range 63).map (· + 1)).filterMap fun x =>
    let y := cnMask adj x
    if y == 0 then none
    else let x2 := cnMask adj y
    if x == x2 then some (x, y) else none

def bicHit (x y u : Nat) : Bool := ((x &&& u) != 0) && ((y &&& u) != 0)

def check3A (c : Nat) : Bool :=
  let bics := maxBicMask c
  let ones := onesList c
  !(bics.any fun p0 =>
    bics.any fun p1 =>
      bics.any fun p2 =>
        ones.all fun u => bicHit p0.1 p0.2 u || bicHit p1.1 p1.2 u || bicHit p2.1 p2.2 u)

def check3B (c : Nat) : Bool :=
  let adj := canonAdj c
  let miss := misList c
  let ones := onesList c
  let cands := ((List.range 63).map (· + 1)).filter fun l =>
    (miss.filter fun m => (m &&& l) == 0).length ≥ 3
  !(cands.any fun l1 =>
    let r1 := cnMask adj l1
    cands.any fun l2 =>
      l1 ≤ l2 &&
      let r2 := cnMask adj l2
      let rem := ones.filter fun u => !(bicHit l1 r1 u || bicHit l2 r2 u)
      let l12 := l1 ||| l2
      rem.all (fun u => (u &&& l12) != 0) &&
      let z0 := miss.filter fun m => (m &&& l12) != 0
      (List.range (1 <<< z0.length)).any fun zm =>
        let uL := (List.range z0.length).foldl
          (fun acc bi => if zm.testBit bi then acc ||| z0.getD bi 0 else acc) 0
        let uR := (List.range z0.length).foldl
          (fun acc bi => if !(zm.testBit bi) then acc ||| z0.getD bi 0 else acc) 0
        let l0 := 63 ^^^ uL
        let r0 := 63 ^^^ uR
        rem.all fun u => ((u &&& l0) != 0) && ((u &&& r0) != 0))

theorem mis_len_G0 : (misList 0).length = 9 := by decide +kernel
theorem mis_len_G1 : (misList 1).length = 8 := by decide +kernel
theorem mis_len_G2 : (misList 2).length = 7 := by decide +kernel
theorem mis_len_G3 : (misList 3).length = 7 := by decide +kernel
theorem mis_len_G4 : (misList 4).length = 7 := by decide +kernel

theorem check3A_G1 : check3A 1 = true := by decide +kernel
theorem check3A_G2 : check3A 2 = true := by decide +kernel
theorem check3A_G3 : check3A 3 = true := by decide +kernel
theorem check3A_G4 : check3A 4 = true := by decide +kernel

theorem check3B_G2 : check3B 2 = true := by decide +kernel
theorem check3B_G3 : check3B 3 = true := by decide +kernel
theorem check3B_G4 : check3B 4 = true := by decide +kernel

theorem mis_len_ge7 (c : Nat) (hc : c < 5) : 7 ≤ (misList c).length := by
  interval_cases c
  · rw [mis_len_G0]; omega
  · rw [mis_len_G1]; omega
  · rw [mis_len_G2]
  · rw [mis_len_G3]
  · rw [mis_len_G4]

theorem check3A_all (c : Nat) (hc : c < 5) (h0 : c ≠ 0) : check3A c = true := by
  interval_cases c
  · exact absurd rfl h0
  · exact check3A_G1
  · exact check3A_G2
  · exact check3A_G3
  · exact check3A_G4

theorem mis_len_eq7 (c : Nat) (hc : c < 5) (h01 : ¬ (c = 0 ∨ c = 1)) : (misList c).length = 7 := by
  interval_cases c
  · exact absurd (Or.inl rfl) h01
  · exact absurd (Or.inr rfl) h01
  · exact mis_len_G2
  · exact mis_len_G3
  · exact mis_len_G4

theorem check3B_all (c : Nat) (hc : c < 5) (h01 : ¬ (c = 0 ∨ c = 1)) : check3B c = true := by
  interval_cases c
  · exact absurd (Or.inl rfl) h01
  · exact absurd (Or.inr rfl) h01
  · exact check3B_G2
  · exact check3B_G3
  · exact check3B_G4

theorem isMIS_iff_mask (c : Nat) (hc : c < 5) (I : Finset (Fin 6)) :
    IsMIS (canonG c hc) I ↔ maskOf I ∈ misList c := by
  have h1 : ∀ a : Fin 6, (canonAdj c a.val &&& maskOf I) = 0 ↔ ∀ b ∈ I, ¬ (canonG c hc).Adj a b := by
    intro a
    constructor
    · intro h0 b hb hab
      have := congrArg (fun x => x.testBit b.val) h0
      rw [Nat.testBit_and, testBit_maskOf, Nat.zero_testBit] at this
      change (canonAdj c a.val).testBit b.val = true at hab
      simp [hab, hb] at this
    · intro hno
      apply Nat.eq_of_testBit_eq
      intro m
      rw [Nat.testBit_and, Nat.zero_testBit]
      by_cases hm : m < 6
      · let b : Fin 6 := ⟨m, hm⟩
        change ((canonAdj c a.val).testBit b.val && (maskOf I).testBit b.val) = false
        rw [testBit_maskOf]
        by_cases hb : b ∈ I
        · have : (canonAdj c a.val).testBit b.val = false := by
            cases h : (canonAdj c a.val).testBit b.val
            · rfl
            · exact absurd h (hno b hb)
          simp [this]
        · simp [hb]
      · simp [testBit_eq_false_of_lt64 (maskOf_lt I) hm]
  simp only [misList, List.mem_filter, List.mem_range, maskOf_lt I, true_and, isMISMask,
    Bool.and_eq_true, isIndepMask, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, bne_iff_ne]
  constructor
  · rintro ⟨hind, hmax⟩
    refine ⟨fun a ha => ?_, fun u hu => ?_⟩
    · let af : Fin 6 := ⟨a, ha⟩
      change (maskOf I).testBit af.val = false ∨ canonAdj c af.val &&& maskOf I = 0
      rw [testBit_maskOf]
      by_cases haI : af ∈ I
      · exact Or.inr ((h1 af).2 fun b hb => hind af haI b hb)
      · simp [haI]
    · let uf : Fin 6 := ⟨u, hu⟩
      change (maskOf I).testBit uf.val = true ∨ canonAdj c uf.val &&& maskOf I ≠ 0
      rw [testBit_maskOf]
      by_cases huI : uf ∈ I
      · simp [huI]
      · right
        intro h0
        obtain ⟨v, hvI, huv⟩ := hmax uf huI
        exact (h1 uf).1 h0 v hvI huv
  · rintro ⟨hL, hR⟩
    refine ⟨fun a ha b hb => ?_, fun u hu => ?_⟩
    · have ha' := hL a.val a.isLt
      rw [testBit_maskOf] at ha'
      simp only [ha, decide_true, Bool.true_eq_false, false_or] at ha'
      exact (h1 a).1 ha' b hb
    · have hu' := hR u.val u.isLt
      rw [testBit_maskOf] at hu'
      simp only [hu, decide_false, Bool.false_eq_true, false_or] at hu'
      by_contra hno
      push Not at hno
      exact hu' ((h1 u).2 hno)

theorem cnMask_spec (c : Nat) (hc : c < 5) (S : Finset (Fin 6)) (v : Fin 6) :
    (cnMask (canonAdj c) (maskOf S)).testBit v.val = true ↔ ∀ a ∈ S, (canonG c hc).Adj a v := by
  have hfold : ∀ (l : List ℕ) (acc : ℕ),
      (l.foldl (fun acc a => if (maskOf S).testBit a then acc &&& canonAdj c a else acc) acc).testBit v.val = true ↔
      acc.testBit v.val = true ∧ ∀ a ∈ l, (maskOf S).testBit a = true → (canonAdj c a).testBit v.val = true := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons x t ih =>
      intro acc
      simp only [List.foldl_cons, List.mem_cons]
      rw [ih]
      by_cases hx : (maskOf S).testBit x = true
      · simp only [hx, ↓reduceIte, Nat.testBit_and, Bool.and_eq_true]
        constructor
        · rintro ⟨⟨ha, hxv⟩, ht⟩
          exact ⟨ha, fun a ha' hm => by rcases ha' with rfl | hmem; exact hxv; exact ht a hmem hm⟩
        · rintro ⟨ha, hall⟩
          exact ⟨⟨ha, hall x (Or.inl rfl) hx⟩, fun a hmem hm => hall a (Or.inr hmem) hm⟩
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        constructor
        · rintro ⟨ha, ht⟩
          exact ⟨ha, fun a ha' hm => by rcases ha' with rfl | hmem; exact absurd hm hx; exact ht a hmem hm⟩
        · rintro ⟨ha, hall⟩
          exact ⟨ha, fun a hmem hm => hall a (Or.inr hmem) hm⟩
  unfold cnMask
  rw [hfold]
  have h63 : Nat.testBit 63 v.val = true := testBit_63 v.isLt
  simp only [h63, true_and, List.mem_range]
  constructor
  · intro h a ha
    have hm : (maskOf S).testBit a.val = true := by rw [testBit_maskOf]; simp [ha]
    exact h a.val a.isLt hm
  · intro h a ha hm
    let af : Fin 6 := ⟨a, ha⟩
    have haS : af ∈ S := by
      have : (maskOf S).testBit af.val = true := hm
      rw [testBit_maskOf] at this
      simpa using this
    exact h af haS

theorem cnMask_lt (c : Nat) (s : Nat) : cnMask (canonAdj c) s < 64 := by
  have hfold : ∀ (l : List ℕ) (acc : ℕ), acc < 64 →
      (l.foldl (fun acc a => if s.testBit a then acc &&& canonAdj c a else acc) acc) < 64 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons x t ih =>
      intro acc h
      simp only [List.foldl_cons]
      apply ih
      split_ifs
      · exact lt_of_le_of_lt Nat.and_le_left h
      · exact h
  exact hfold _ 63 (by omega)

theorem bic_sub_maxBic (c : Nat) (hc : c < 5) (L R : Finset (Fin 6))
    (hL : L.Nonempty) (hR : R.Nonempty)
    (hbic : ∀ a ∈ L, ∀ b ∈ R, (canonG c hc).Adj a b) :
    ∃ p ∈ maxBicMask c,
      (∀ U : Finset (Fin 6), (∃ a ∈ L, a ∈ U) → (∃ b ∈ R, b ∈ U) → bicHit p.1 p.2 (maskOf U) = true) := by
  let x := cnMask (canonAdj c) (maskOf R)
  let y := cnMask (canonAdj c) x
  have hLx : ∀ a ∈ L, x.testBit a.val = true := by
    intro a ha
    exact (cnMask_spec c hc R a).2 fun b hb => (hbic a ha b hb).symm
  have hLx_ne : x ≠ 0 := by
    obtain ⟨a, ha⟩ := hL
    intro hx0
    have := hLx a ha; rw [hx0] at this; simp at this
  have hRy : ∀ b ∈ R, y.testBit b.val = true := by
    intro b hb
    have hxm : x = maskOf (setOfMask x) := (maskOf_setOfMask x (cnMask_lt c _)).symm
    change (cnMask (canonAdj c) x).testBit b.val = true
    rw [hxm, cnMask_spec c hc]
    intro a ha
    have hax : x.testBit a.val = true := (mem_setOfMask x a).1 ha
    exact ((cnMask_spec c hc R a).1 hax b hb).symm
  have hRy_ne : y ≠ 0 := by
    obtain ⟨b, hb⟩ := hR
    intro hy0
    have := hRy b hb; rw [hy0] at this; simp at this
  have hxy : cnMask (canonAdj c) y = x := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 6
    · let af : Fin 6 := ⟨k, hk⟩
      have hym : y = maskOf (setOfMask y) := (maskOf_setOfMask y (cnMask_lt c _)).symm
      have hxm : x = maskOf (setOfMask x) := (maskOf_setOfMask x (cnMask_lt c _)).symm
      apply Bool.eq_iff_iff.2
      change (cnMask (canonAdj c) y).testBit af.val = true ↔ x.testBit af.val = true
      rw [hym, cnMask_spec c hc]
      constructor
      · intro hall
        exact (cnMask_spec c hc R af).2 fun b hb =>
          hall b ((mem_setOfMask y b).2 (hRy b hb))
      · intro hax b hb
        have hby : y.testBit b.val = true := (mem_setOfMask y b).1 hb
        rw [show y = cnMask (canonAdj c) (maskOf (setOfMask x)) from by rw [← hxm]] at hby
        exact ((cnMask_spec c hc (setOfMask x) b).1 hby af ((mem_setOfMask x af).2 hax)).symm
    · rw [testBit_eq_false_of_lt64 (cnMask_lt c y) hk, testBit_eq_false_of_lt64 (cnMask_lt c _) hk]
  have hx_lt : x < 64 := cnMask_lt c _
  have hmem : (x, y) ∈ maxBicMask c := by
    simp only [maxBicMask, List.mem_filterMap, List.mem_map, List.mem_range]
    refine ⟨x, ⟨x - 1, by omega, by omega⟩, ?_⟩
    have hyn : (y == 0) = false := by simp [hRy_ne]
    simp [y, hyn, hxy]
  refine ⟨(x, y), hmem, fun U ⟨a, haL, haU⟩ ⟨b, hbR, hbU⟩ => ?_⟩
  simp only [bicHit, Bool.and_eq_true, bne_iff_ne]
  constructor
  · intro h0
    have := congrArg (fun z => z.testBit a.val) h0
    rw [Nat.testBit_and, testBit_maskOf, Nat.zero_testBit] at this
    simp [hLx a haL, haU] at this
  · intro h0
    have := congrArg (fun z => z.testBit b.val) h0
    rw [Nat.testBit_and, testBit_maskOf, Nat.zero_testBit] at this
    simp [hRy b hbR, hbU] at this

theorem maxBicMask_nonempty (c : Nat) (hc : c < 5) : (maxBicMask c).length > 0 := by
  interval_cases c <;> decide +kernel

theorem maskOf_insert_eq (m : Nat) (hmlt : m < 64) (k : Nat) (hk : k < 6) :
    maskOf (insert ⟨k, hk⟩ (setOfMask m)) = m ||| (1 <<< k) := by
  let kf : Fin 6 := ⟨k, hk⟩
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hj : j < 6
  · let jf : Fin 6 := ⟨j, hj⟩
    change (maskOf (insert kf (setOfMask m))).testBit jf.val =
      (m.testBit jf.val || (decide (kf.val ≤ jf.val) && Nat.testBit 1 (jf.val - kf.val)))
    rw [testBit_maskOf]
    by_cases hjk : jf = kf
    · have hv : jf.val = kf.val := congrArg Fin.val hjk
      simp [hjk, hv]
    · have hsh : (decide (kf.val ≤ jf.val) && Nat.testBit 1 (jf.val - kf.val)) = false := by
        by_cases hle : kf.val ≤ jf.val
        · have : Nat.testBit 1 (jf.val - kf.val) = false := by
            have hne : kf.val ≠ jf.val := fun e => hjk (Fin.ext e.symm)
            cases hd : jf.val - kf.val with
            | zero => omega
            | succ d => simp [Nat.testBit_succ]
          simp [hle, this]
        · simp [hle]
      have hmI : (jf ∈ setOfMask m) ↔ m.testBit jf.val = true := mem_setOfMask m jf
      simp only [Finset.mem_insert, hjk, false_or, hsh, Bool.or_false]
      cases hmt : m.testBit jf.val <;> simp [hmI, hmt]
  · have h2 : (maskOf (insert kf (setOfMask m))).testBit j = false :=
      testBit_eq_false_of_lt64 (maskOf_lt _) hj
    have h3 : m.testBit j = false := testBit_eq_false_of_lt64 hmlt hj
    have h4 : Nat.testBit 1 (j - k) = false := by
      cases hd : j - k with
      | zero => omega
      | succ d => simp [Nat.testBit_succ]
    change (maskOf (insert kf (setOfMask m))).testBit j = _
    simp [h2, h3, h4]

theorem check3A_contra (c : Nat) (hchk : check3A c = true)
    (p0 p1 p2 : Nat × Nat)
    (hp0 : p0 ∈ maxBicMask c) (hp1 : p1 ∈ maxBicMask c) (hp2 : p2 ∈ maxBicMask c)
    (hall : ∀ u ∈ onesList c, bicHit p0.1 p0.2 u || bicHit p1.1 p1.2 u || bicHit p2.1 p2.2 u = true) :
    False := by
  unfold check3A at hchk
  simp only [Bool.not_eq_true', List.any_eq_false, List.any_eq_true, not_exists, not_and] at hchk
  exact hchk p0 hp0 p1 hp1 p2 hp2 (List.all_eq_true.2 hall)

theorem check3B_contra (c : Nat) (hchk : check3B c = true)
    (L1 L2 G0L G0R : Finset (Fin 6))
    (la lb : Nat)
    (hla : la ∈ ((List.range 63).map (· + 1)).filter (fun l => ((misList c).filter fun m => (m &&& l) == 0).length ≥ 3))
    (hlb : lb ∈ ((List.range 63).map (· + 1)).filter (fun l => ((misList c).filter fun m => (m &&& l) == 0).length ≥ 3))
    (hle : la ≤ lb)
    (hpair : (la = maskOf L1 ∧ lb = maskOf L2) ∨ (la = maskOf L2 ∧ lb = maskOf L1))
    (hrem_spec : ∀ u ∈ onesList c,
      (!(bicHit (maskOf L1) (cnMask (canonAdj c) (maskOf L1)) u ||
        bicHit (maskOf L2) (cnMask (canonAdj c) (maskOf L2)) u)) = true →
      (u &&& (maskOf L1 ||| maskOf L2)) ≠ 0 ∧
      (u &&& maskOf G0L) ≠ 0 ∧ (u &&& maskOf G0R) ≠ 0)
    (hg0_z0 : ∀ m ∈ (misList c).filter (fun m => (m &&& (maskOf L1 ||| maskOf L2)) != 0),
      (m &&& maskOf G0L) = 0 ∨ (m &&& maskOf G0R) = 0) : False := by
  have hL12_eq : la ||| lb = maskOf L1 ||| maskOf L2 := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Nat.or_comm _ _
  have hrem_eq : ∀ u,
      (!(bicHit la (cnMask (canonAdj c) la) u || bicHit lb (cnMask (canonAdj c) lb) u)) =
      (!(bicHit (maskOf L1) (cnMask (canonAdj c) (maskOf L1)) u ||
        bicHit (maskOf L2) (cnMask (canonAdj c) (maskOf L2)) u)) := by
    intro u
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rw [Bool.or_comm]
  let z0 := (misList c).filter fun m => (m &&& (la ||| lb)) != 0
  let zm : Nat := (List.range z0.length).foldl
    (fun acc bi => if (z0.getD bi 0 &&& maskOf G0L) == 0 then acc ||| (1 <<< bi) else acc) 0
  have hzm_lt_pow : ∀ k, ((List.range k).foldl
      (fun acc j => if (z0.getD j 0 &&& maskOf G0L) == 0 then acc ||| (1 <<< j) else acc) 0) < 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ihk =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      split_ifs
      · apply Nat.or_lt_two_pow
        · rw [pow_succ]; omega
        · rw [Nat.shiftLeft_eq, one_mul, pow_succ]; omega
      · rw [pow_succ]; omega
  have hzm_lt : zm < 1 <<< z0.length := by
    rw [Nat.shiftLeft_eq, one_mul]; exact hzm_lt_pow z0.length
  have hzm_bit : ∀ bi < z0.length,
      zm.testBit bi = ((z0.getD bi 0 &&& maskOf G0L) == 0) := by
    have hgen : ∀ (k : Nat) (bi : Nat), bi < k →
        ((List.range k).foldl
          (fun acc j => if (z0.getD j 0 &&& maskOf G0L) == 0 then acc ||| (1 <<< j) else acc) 0).testBit bi =
        ((z0.getD bi 0 &&& maskOf G0L) == 0) := by
      intro k
      induction k with
      | zero => intro bi h; omega
      | succ k ih =>
        intro bi hbi
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        by_cases hbk : bi = k
        · subst hbk
          have hprev : ((List.range bi).foldl
              (fun acc j => if (z0.getD j 0 &&& maskOf G0L) == 0 then acc ||| (1 <<< j) else acc) 0).testBit bi = false :=
            Nat.testBit_lt_two_pow (hzm_lt_pow bi)
          split_ifs with hcond
          · have h10 : Nat.testBit 1 0 = true := by decide
            rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.sub_self, h10, hprev, hcond]
            simp
          · have hcf : ((z0.getD bi 0 &&& maskOf G0L) == 0) = false := Bool.eq_false_iff.2 hcond
            rw [hprev, hcf]
        · have hlt : bi < k := by omega
          split_ifs
          · rw [Nat.testBit_or, ih bi hlt, Nat.testBit_shiftLeft]
            have : ¬ (k ≤ bi) := by omega
            simp [this]
          · exact ih bi hlt
    exact hgen z0.length
  let uL := (List.range z0.length).foldl
    (fun acc bi => if zm.testBit bi then acc ||| z0.getD bi 0 else acc) 0
  let uR := (List.range z0.length).foldl
    (fun acc bi => if !(zm.testBit bi) then acc ||| z0.getD bi 0 else acc) 0
  have huL_disj : (uL &&& maskOf G0L) = 0 := by
    have hfold : ∀ (l : List ℕ) (acc : ℕ),
        (acc &&& maskOf G0L) = 0 →
        (∀ bi ∈ l, zm.testBit bi = true → (z0.getD bi 0 &&& maskOf G0L) = 0) →
        ((l.foldl (fun acc bi => if zm.testBit bi then acc ||| z0.getD bi 0 else acc) acc) &&&
          maskOf G0L) = 0 := by
      intro l
      induction l with
      | nil => intro acc ha _; exact ha
      | cons x t ih =>
        intro acc ha hall
        simp only [List.foldl_cons]
        apply ih _ _ (fun bi hbi => hall bi (List.mem_cons_of_mem _ hbi))
        split_ifs with hx
        · rw [Nat.and_or_distrib_right, ha, hall x List.mem_cons_self hx]; rfl
        · exact ha
    apply hfold (List.range z0.length) 0 (by simp)
    intro bi hbi hzm
    have hlt := List.mem_range.1 hbi
    rw [hzm_bit bi hlt] at hzm
    exact beq_iff_eq.1 hzm
  have huR_disj : (uR &&& maskOf G0R) = 0 := by
    have hfold : ∀ (l : List ℕ) (acc : ℕ),
        (acc &&& maskOf G0R) = 0 →
        (∀ bi ∈ l, zm.testBit bi = false → (z0.getD bi 0 &&& maskOf G0R) = 0) →
        ((l.foldl (fun acc bi => if !(zm.testBit bi) then acc ||| z0.getD bi 0 else acc) acc) &&&
          maskOf G0R) = 0 := by
      intro l
      induction l with
      | nil => intro acc ha _; exact ha
      | cons x t ih =>
        intro acc ha hall
        simp only [List.foldl_cons]
        apply ih _ _ (fun bi hbi => hall bi (List.mem_cons_of_mem _ hbi))
        split_ifs with hx
        · have hxf : zm.testBit x = false := by simpa using hx
          rw [Nat.and_or_distrib_right, ha, hall x List.mem_cons_self hxf]; rfl
        · exact ha
    apply hfold (List.range z0.length) 0 (by simp)
    intro bi hbi hzm
    have hlt := List.mem_range.1 hbi
    have hneL : (z0.getD bi 0 &&& maskOf G0L) ≠ 0 := by
      rw [hzm_bit bi hlt] at hzm
      simpa using hzm
    have hmemz : z0.getD bi 0 ∈ (misList c).filter (fun m => (m &&& (maskOf L1 ||| maskOf L2)) != 0) := by
      rw [← hL12_eq]
      rw [List.getD_eq_getElem _ _ hlt]
      exact List.getElem_mem hlt
    rcases hg0_z0 _ hmemz with hL0 | hR0
    · exact absurd hL0 hneL
    · exact hR0
  unfold check3B at hchk
  simp only [Bool.not_eq_true', List.any_eq_false, List.any_eq_true, not_exists, not_and] at hchk
  apply hchk la hla lb hlb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    List.mem_range, bne_iff_ne]
  refine ⟨hle, fun u hu => ?_, zm, hzm_lt, fun u hu => ?_⟩
  · rw [List.mem_filter] at hu
    rw [hL12_eq]
    exact (hrem_spec u hu.1 (by rw [← hrem_eq]; exact hu.2)).1
  · rw [List.mem_filter] at hu
    have hsp := hrem_spec u hu.1 (by rw [← hrem_eq]; exact hu.2)
    have huR_eq : (List.range z0.length).foldl
        (fun acc bi => if zm.testBit bi = false then acc ||| z0.getD bi 0 else acc) 0 = uR := by
      dsimp only [uR]
      congr 1; funext acc bi; cases zm.testBit bi <;> rfl
    rw [huR_eq]
    exact ⟨sub_xor_ne_zero (maskOf_lt _) huL_disj hsp.2.1,
           sub_xor_ne_zero (maskOf_lt _) huR_disj hsp.2.2⟩

theorem no_size_three_canon (c : Nat) (hc : c < 5) (C : AndCountCircuit 6)
    (hW : C.WellFormed) (hsz : C.size = 3) (hP : PartialCond (canonG c hc) C) : False := by
  classical
  have hov := outVars_empty (canonG c hc) C hP
  let g0 : Fin C.size := ⟨0, by omega⟩
  let g1 : Fin C.size := ⟨1, by omega⟩
  let g2 : Fin C.size := ⟨2, by omega⟩
  have hfin3 : ∀ j : Fin C.size, j = g0 ∨ j = g1 ∨ j = g2 := by
    intro j; have := j.isLt
    by_cases h0 : j.val = 0
    · exact Or.inl (Fin.ext h0)
    · by_cases h1 : j.val = 1
      · exact Or.inr (Or.inl (Fin.ext h1))
      · exact Or.inr (Or.inr (Fin.ext (by dsimp [g2]; omega)))
  let sV : Fin C.size → Bool → Finset (Fin 6) :=
    fun i b => if b then C.rightVars i else C.leftVars i
  let sG : Fin C.size → Bool → Finset (Fin C.size) :=
    fun i b => if b then C.rightGates i else C.leftGates i
  let O : Finset (Fin C.size) := Finset.univ.filter fun i =>
    ∀ I, IsMIS (canonG c hc) I → C.gateVal I i = false
  have hsubO : C.outGates ⊆ O := by
    intro i hi
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
    intro I hmis
    have hf := (hP I hmis).1
    unfold AndCountCircuit.eval at hf
    simp only [decide_eq_false_iff_not, not_or, not_exists, not_and] at hf
    cases hv : C.gateVal I i
    · rfl
    · exact absurd hv (hf.2 i hi)
  have hO_false : ∀ I, IsMIS (canonG c hc) I → ∀ i ∈ O, C.gateVal I i = false := by
    intro I hmis i hi
    exact (Finset.mem_filter.1 hi).2 I hmis
  have hO_true : ∀ I, IsMIS (canonG c hc) I → ∀ u, u ∉ I → ∃ i ∈ O, C.gateVal (insert u I) i = true := by
    intro I hmis u hu
    have ht := (hP I hmis).2 u hu
    unfold AndCountCircuit.eval at ht
    rw [hov] at ht
    simp only [Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_true_eq] at ht
    obtain ⟨j, hj, hv⟩ := ht
    exact ⟨j, hsubO hj, hv⟩
  let F2 : (Fin 3 → Bool) → Bool := fun _ => decide (g2 ∈ O)
  let F1 : (Fin 3 → Bool) → Bool := fun b =>
    decide (g1 ∈ O) || (F2 b && decide (g1 ∈ sG g2 (b 2)))
  let F0 : (Fin 3 → Bool) → Bool := fun b =>
    decide (g0 ∈ O) || (F2 b && decide (g0 ∈ sG g2 (b 2))) || (F1 b && decide (g0 ∈ sG g1 (b 1)))
  let Q : (Fin 3 → Bool) → Finset (Fin 6) := fun b =>
    Finset.univ \
      ((if F0 b then sV g0 (b 0) else ∅) ∪
       (if F1 b then sV g1 (b 1) else ∅) ∪
       (if F2 b then sV g2 (b 2) else ∅))
  have hQ_sub : ∀ U, (∀ i ∈ O, C.gateVal U i = false) ↔ ∃ b : Fin 3 → Bool, U ⊆ Q b := by
    intro U
    constructor
    · intro hU
      let pick : Fin C.size → Bool := fun i =>
        if (∃ v ∈ C.leftVars i, v ∈ U) ∨ (∃ j ∈ C.leftGates i, C.gateVal U j = true) then true else false
      let b : Fin 3 → Bool := fun r =>
        match r.val with | 0 => pick g0 | 1 => pick g1 | _ => pick g2
      have hside : ∀ i : Fin C.size, C.gateVal U i = false →
          (∀ v ∈ sV i (pick i), v ∉ U) ∧ (∀ j ∈ sG i (pick i), C.gateVal U j = false) := by
        intro i hgi
        have hnot : ¬ C.gateVal U i = true := by simp [hgi]
        rw [gv_iff C hW U i] at hnot
        dsimp only [pick]
        split_ifs with hL
        · have hR : ¬ ((∃ v ∈ C.rightVars i, v ∈ U) ∨ ∃ j ∈ C.rightGates i, C.gateVal U j = true) :=
            fun hR => hnot ⟨hL, hR⟩
          push Not at hR
          exact ⟨fun v hv => hR.1 v hv, fun j hj => Bool.eq_false_iff.2 (hR.2 j hj)⟩
        · push Not at hL
          exact ⟨fun v hv => hL.1 v hv, fun j hj => Bool.eq_false_iff.2 (hL.2 j hj)⟩
      have hF2 : F2 b = true → C.gateVal U g2 = false := fun h => hU g2 (of_decide_eq_true h)
      have hF1 : F1 b = true → C.gateVal U g1 = false := by
        intro h
        simp only [F1, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        rcases h with h | ⟨h2, hg1⟩
        · exact hU g1 h
        · exact (hside g2 (hF2 h2)).2 g1 hg1
      have hF0 : F0 b = true → C.gateVal U g0 = false := by
        intro h
        simp only [F0, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        rcases h with (h | ⟨h2, hg0⟩) | ⟨h1, hg0⟩
        · exact hU g0 h
        · exact (hside g2 (hF2 h2)).2 g0 hg0
        · exact (hside g1 (hF1 h1)).2 g0 hg0
      refine ⟨b, fun v hvU => ?_⟩
      simp only [Q, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · split_ifs with h0
        · exact fun hv => (hside g0 (hF0 h0)).1 v hv hvU
        · simp
      · split_ifs with h1
        · exact fun hv => (hside g1 (hF1 h1)).1 v hv hvU
        · simp
      · split_ifs with h2
        · exact fun hv => (hside g2 (hF2 h2)).1 v hv hvU
        · simp
    · rintro ⟨b, hUb⟩
      have hno0 : F0 b = true → ∀ v ∈ sV g0 (b 0), v ∉ U := fun h0 v hv hvU => by
        have := hUb hvU; simp [Q, h0, hv] at this
      have hno1 : F1 b = true → ∀ v ∈ sV g1 (b 1), v ∉ U := fun h1 v hv hvU => by
        have := hUb hvU; simp [Q, h1, hv] at this
      have hno2 : F2 b = true → ∀ v ∈ sV g2 (b 2), v ∉ U := fun h2 v hv hvU => by
        have := hUb hvU; simp [Q, h2, hv] at this
      have hg0_f : F0 b = true → C.gateVal U g0 = false := by
        intro h0
        apply Bool.eq_false_iff.2
        intro h
        rw [gv_iff C hW U g0] at h
        rcases h with ⟨hL, hR⟩
        cases hb0 : b 0
        · rcases hL with ⟨v, hv, hvU⟩ | ⟨j, hj, _⟩
          · exact hno0 h0 v (by simpa [sV, hb0] using hv) hvU
          · exact Nat.not_lt_zero j.val ((hW g0).1 j hj)
        · rcases hR with ⟨v, hv, hvU⟩ | ⟨j, hj, _⟩
          · exact hno0 h0 v (by simpa [sV, hb0] using hv) hvU
          · exact Nat.not_lt_zero j.val ((hW g0).2 j hj)
      have hg1_f : F1 b = true → C.gateVal U g1 = false := by
        intro h1
        apply Bool.eq_false_iff.2
        intro h
        rw [gv_iff C hW U g1] at h
        rcases h with ⟨hL, hR⟩
        have hlt1 : ∀ j : Fin C.size, j < g1 → j = g0 := fun j hj => Fin.ext (by
          have : j.val < g1.val := Fin.lt_def.1 hj
          dsimp [g0, g1] at this ⊢; omega)
        cases hb1 : b 1
        · rcases hL with ⟨v, hv, hvU⟩ | ⟨j, hj, hjv⟩
          · exact hno1 h1 v (by simpa [sV, hb1] using hv) hvU
          · have hj0 : j = g0 := hlt1 j ((hW g1).1 j hj); subst hj0
            have h0 : F0 b = true := by simp [F0, h1, sG, hb1, hj]
            rw [hg0_f h0] at hjv; cases hjv
        · rcases hR with ⟨v, hv, hvU⟩ | ⟨j, hj, hjv⟩
          · exact hno1 h1 v (by simpa [sV, hb1] using hv) hvU
          · have hj0 : j = g0 := hlt1 j ((hW g1).2 j hj); subst hj0
            have h0 : F0 b = true := by simp [F0, h1, sG, hb1, hj]
            rw [hg0_f h0] at hjv; cases hjv
      have hg2_f : F2 b = true → C.gateVal U g2 = false := by
        intro h2
        apply Bool.eq_false_iff.2
        intro h
        rw [gv_iff C hW U g2] at h
        rcases h with ⟨hL, hR⟩
        have hlt2 : ∀ j : Fin C.size, j < g2 → j = g0 ∨ j = g1 := fun j hj => by
          have : j.val < g2.val := Fin.lt_def.1 hj
          dsimp [g2] at this
          by_cases h : j.val = 0
          · exact Or.inl (Fin.ext (by dsimp [g0]; omega))
          · exact Or.inr (Fin.ext (by dsimp [g1]; omega))
        cases hb2 : b 2
        · rcases hL with ⟨v, hv, hvU⟩ | ⟨j, hj, hjv⟩
          · exact hno2 h2 v (by simpa [sV, hb2] using hv) hvU
          · rcases hlt2 j ((hW g2).1 j hj) with rfl | rfl
            · have h0 : F0 b = true := by simp [F0, h2, sG, hb2, hj]
              rw [hg0_f h0] at hjv; cases hjv
            · have h1 : F1 b = true := by simp [F1, h2, sG, hb2, hj]
              rw [hg1_f h1] at hjv; cases hjv
        · rcases hR with ⟨v, hv, hvU⟩ | ⟨j, hj, hjv⟩
          · exact hno2 h2 v (by simpa [sV, hb2] using hv) hvU
          · rcases hlt2 j ((hW g2).2 j hj) with rfl | rfl
            · have h0 : F0 b = true := by simp [F0, h2, sG, hb2, hj]
              rw [hg0_f h0] at hjv; cases hjv
            · have h1 : F1 b = true := by simp [F1, h2, sG, hb2, hj]
              rw [hg1_f h1] at hjv; cases hjv
      intro i hiO
      rcases hfin3 i with rfl | rfl | rfl
      · exact hg0_f (by simp [F0, hiO])
      · exact hg1_f (by simp [F1, hiO])
      · exact hg2_f (by simp [F2, hiO])
  have hQ_mis : ∀ I, IsMIS (canonG c hc) I → ∃ b : Fin 3 → Bool, I = Q b := by
    intro I hmis
    obtain ⟨b, hb⟩ := (hQ_sub I).1 (hO_false I hmis)
    refine ⟨b, Finset.Subset.antisymm hb ?_⟩
    intro u huQ
    by_contra huI
    obtain ⟨i, hiO, hti⟩ := hO_true I hmis u huI
    have hf := (hQ_sub (insert u I)).2 ⟨b, Finset.insert_subset_iff.2 ⟨huQ, hb⟩⟩ i hiO
    rw [hti] at hf; cases hf
  have hmis_card : ∀ (B : Finset (Fin 3 → Bool)),
      (∀ I, IsMIS (canonG c hc) I → ∃ b ∈ B, I = Q b) → (misList c).length ≤ B.card := by
    intro B hB
    have hnd : (misList c).Nodup := List.Nodup.filter _ List.nodup_range
    rw [← List.toFinset_card_of_nodup hnd]
    have hsub : (misList c).toFinset ⊆ B.image (fun b => maskOf (Q b)) := by
      intro m hm
      rw [List.mem_toFinset] at hm
      have hmlt : m < 64 := List.mem_range.1 (List.mem_filter.1 hm).1
      have hmis : IsMIS (canonG c hc) (setOfMask m) := by
        rw [isMIS_iff_mask c hc, maskOf_setOfMask m hmlt]; exact hm
      obtain ⟨b, hbB, heq⟩ := hB _ hmis
      rw [Finset.mem_image]
      exact ⟨b, hbB, by rw [← heq, maskOf_setOfMask m hmlt]⟩
    exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
  have hge7 : 7 ≤ (misList c).length := mis_len_ge7 c hc
  have hnot_both : ∀ (g j : Fin C.size), g ∉ O → j ∈ O →
      ¬ (g ∈ C.leftGates j ∧ g ∈ C.rightGates j) := by
    intro g j hgO hjO ⟨hl, hr⟩
    apply hgO
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
    intro I hmis
    cases hv : C.gateVal I g
    · rfl
    · have hjv : C.gateVal I j = true := (gv_iff C hW I j).2 ⟨Or.inr ⟨g, hl, hv⟩, Or.inr ⟨g, hr, hv⟩⟩
      have hwf := hO_false I hmis j hjO
      rw [hjv] at hwf; cases hwf
  by_cases hO2 : g2 ∈ O
  · by_cases hO1 : g1 ∈ O
    · by_cases hO0 : g0 ∈ O
      · -- Case 3A: O = {g0, g1, g2}
        by_cases hc0 : c = 0
        · subst hc0
          have hle8 : (misList 0).length ≤ (Finset.univ : Finset (Fin 3 → Bool)).card :=
            hmis_card Finset.univ fun I hm => by obtain ⟨b, hb⟩ := hQ_mis I hm; exact ⟨b, Finset.mem_univ _, hb⟩
          have hc8 : (Finset.univ : Finset (Fin 3 → Bool)).card = 8 := by decide
          rw [mis_len_G0, hc8] at hle8; omega
        · have hbic : ∀ i : Fin C.size, ∀ a ∈ C.leftVars i, ∀ b ∈ C.rightVars i, (canonG c hc).Adj a b := by
            intro i a ha b hb
            have hiO : i ∈ O := by rcases hfin3 i with rfl | rfl | rfl <;> assumption
            by_contra hna
            have hind : IsIndep (canonG c hc) {a, b} := by
              intro x hx y hy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
              rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
              · exact (canonG c hc).loopless.irrefl _
              · exact hna
              · exact fun h => hna h.symm
              · exact (canonG c hc).loopless.irrefl _
            obtain ⟨I, hsub, hmis⟩ := exists_mis_superset (canonG c hc) {a, b} hind
            have ht : C.gateVal I i = true :=
              (gv_iff C hW I i).2 ⟨Or.inl ⟨a, ha, hsub (by simp)⟩, Or.inl ⟨b, hb, hsub (by simp)⟩⟩
            have hf := hO_false I hmis i hiO
            rw [ht] at hf; cases hf
          have hpick : ∀ i : Fin C.size, ∃ p ∈ maxBicMask c,
              ∀ U : Finset (Fin 6), (∃ a ∈ C.leftVars i, a ∈ U) → (∃ b ∈ C.rightVars i, b ∈ U) →
                bicHit p.1 p.2 (maskOf U) = true := by
            intro i
            by_cases hL : (C.leftVars i).Nonempty
            · by_cases hR : (C.rightVars i).Nonempty
              · exact bic_sub_maxBic c hc (C.leftVars i) (C.rightVars i) hL hR (hbic i)
              · rw [Finset.not_nonempty_iff_eq_empty] at hR
                have hne := maxBicMask_nonempty c hc
                obtain ⟨p, t, hpt⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hne)
                refine ⟨p, hpt ▸ List.mem_cons_self, fun U _ ⟨b, hb, _⟩ => by simp [hR] at hb⟩
            · rw [Finset.not_nonempty_iff_eq_empty] at hL
              have hne := maxBicMask_nonempty c hc
              obtain ⟨p, t, hpt⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hne)
              refine ⟨p, hpt ▸ List.mem_cons_self, fun U ⟨a, ha, _⟩ _ => by simp [hL] at ha⟩
          obtain ⟨p0, hp0, hcov0⟩ := hpick g0
          obtain ⟨p1, hp1, hcov1⟩ := hpick g1
          obtain ⟨p2, hp2, hcov2⟩ := hpick g2
          have hall_ones : ∀ u ∈ onesList c,
              bicHit p0.1 p0.2 u || bicHit p1.1 p1.2 u || bicHit p2.1 p2.2 u = true := by
            intro u hu
            simp only [onesList, List.mem_flatMap, List.mem_filterMap, List.mem_range] at hu
            obtain ⟨m, hm, k, hk, hmk⟩ := hu
            by_cases hbit : m.testBit k = true
            · simp [hbit] at hmk
            · simp [hbit] at hmk
              subst hmk
              have hmlt : m < 64 := List.mem_range.1 (List.mem_filter.1 hm).1
              let I := setOfMask m
              have hmis : IsMIS (canonG c hc) I := by
                rw [isMIS_iff_mask c hc, maskOf_setOfMask m hmlt]; exact hm
              let kf : Fin 6 := ⟨k, hk⟩
              have hkfI : kf ∉ I := by rw [mem_setOfMask]; exact hbit
              rw [← maskOf_insert_eq m hmlt k hk]
              change bicHit p0.1 p0.2 (maskOf (insert kf I)) ||
                bicHit p1.1 p1.2 (maskOf (insert kf I)) ||
                bicHit p2.1 p2.2 (maskOf (insert kf I)) = true
              obtain ⟨i, _, hti⟩ := hO_true I hmis kf hkfI
              by_cases hv0 : C.gateVal (insert kf I) g0 = true
              · rw [gv_iff C hW _ g0] at hv0
                have hL : ∃ a ∈ C.leftVars g0, a ∈ insert kf I := by
                  rcases hv0.1 with h | ⟨j, hj, _⟩
                  · exact h
                  · exact (Nat.not_lt_zero j.val ((hW g0).1 j hj)).elim
                have hR : ∃ b ∈ C.rightVars g0, b ∈ insert kf I := by
                  rcases hv0.2 with h | ⟨j, hj, _⟩
                  · exact h
                  · exact (Nat.not_lt_zero j.val ((hW g0).2 j hj)).elim
                simp [hcov0 _ hL hR]
              · by_cases hv1 : C.gateVal (insert kf I) g1 = true
                · rw [gv_iff C hW _ g1] at hv1
                  have hL : ∃ a ∈ C.leftVars g1, a ∈ insert kf I := by
                    rcases hv1.1 with h | ⟨j, hj, hjv⟩
                    · exact h
                    · have : j = g0 := Fin.ext (by have hlt := Fin.lt_def.1 ((hW g1).1 j hj); dsimp [g0, g1] at hlt ⊢; omega)
                      exact absurd (this ▸ hjv) hv0
                  have hR : ∃ b ∈ C.rightVars g1, b ∈ insert kf I := by
                    rcases hv1.2 with h | ⟨j, hj, hjv⟩
                    · exact h
                    · have : j = g0 := Fin.ext (by have hlt := Fin.lt_def.1 ((hW g1).2 j hj); dsimp [g0, g1] at hlt ⊢; omega)
                      exact absurd (this ▸ hjv) hv0
                  simp [hcov1 _ hL hR]
                · have hv2 : C.gateVal (insert kf I) g2 = true := by
                    rcases hfin3 i with rfl | rfl | rfl
                    · exact absurd hti hv0
                    · exact absurd hti hv1
                    · exact hti
                  rw [gv_iff C hW _ g2] at hv2
                  have hL : ∃ a ∈ C.leftVars g2, a ∈ insert kf I := by
                    rcases hv2.1 with h | ⟨j, hj, hjv⟩
                    · exact h
                    · rcases hfin3 j with rfl | rfl | rfl
                      · exact absurd hjv hv0
                      · exact absurd hjv hv1
                      · exact absurd ((hW g2).1 g2 hj) (Nat.lt_irrefl _)
                  have hR : ∃ b ∈ C.rightVars g2, b ∈ insert kf I := by
                    rcases hv2.2 with h | ⟨j, hj, hjv⟩
                    · exact h
                    · rcases hfin3 j with rfl | rfl | rfl
                      · exact absurd hjv hv0
                      · exact absurd hjv hv1
                      · exact absurd ((hW g2).2 g2 hj) (Nat.lt_irrefl _)
                  simp [hcov2 _ hL hR]
          exact check3A_contra c (check3A_all c hc hc0) p0 p1 p2 hp0 hp1 hp2 hall_ones
      · -- Case 3B: g2 ∈ O, g1 ∈ O, g0 ∉ O
        have hnb1 := hnot_both g0 g1 hO0 hO1
        have hnb2 := hnot_both g0 g2 hO0 hO2
        obtain ⟨s1, hs1⟩ : ∃ s1 : Bool, g0 ∉ sG g1 s1 := by
          by_cases h : g0 ∈ C.leftGates g1
          · exact ⟨true, fun hr => hnb1 ⟨h, hr⟩⟩
          · exact ⟨false, h⟩
        obtain ⟨s2, hs2⟩ : ∃ s2 : Bool, g0 ∉ sG g2 s2 := by
          by_cases h : g0 ∈ C.leftGates g2
          · exact ⟨true, fun hr => hnb2 ⟨h, hr⟩⟩
          · exact ⟨false, h⟩
        let bdrop : Fin 3 → Bool := fun r => match r.val with | 0 => true | 1 => s1 | _ => s2
        let bkeep : Fin 3 → Bool := fun r => match r.val with | 0 => false | 1 => s1 | _ => s2
        have hQeq : Q bdrop = Q bkeep := by
          have hF0d : F0 bdrop = false := by
            simp [F0, F1, F2, hO0, hO1, hO2, bdrop, hs1, hs2]
          have hF0k : F0 bkeep = false := by
            simp [F0, F1, F2, hO0, hO1, hO2, bkeep, hs1, hs2]
          simp [Q, hF0d, hF0k, F1, F2, hO1, hO2, bdrop, bkeep]
        let B7 : Finset (Fin 3 → Bool) := Finset.univ.erase bdrop
        have hB7 : ∀ I, IsMIS (canonG c hc) I → ∃ b ∈ B7, I = Q b := by
          intro I hmis
          obtain ⟨b, hb⟩ := hQ_mis I hmis
          by_cases hbd : b = bdrop
          · refine ⟨bkeep, Finset.mem_erase.2 ⟨fun e => by
              have := congrFun e 0; simp [bkeep, bdrop] at this, Finset.mem_univ _⟩, ?_⟩
            rw [hb, hbd, hQeq]
          · exact ⟨b, Finset.mem_erase.2 ⟨hbd, Finset.mem_univ _⟩, hb⟩
        have hB7_card : B7.card = 7 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ bdrop)]
          have : (Finset.univ : Finset (Fin 3 → Bool)).card = 8 := by decide
          omega
        by_cases hc01 : c = 0 ∨ c = 1
        · have hle7 := hmis_card B7 hB7
          rw [hB7_card] at hle7
          rcases hc01 with rfl | rfl
          · rw [mis_len_G0] at hle7; omega
          · rw [mis_len_G1] at hle7; omega
        · have hlen7 : (misList c).length = 7 := mis_len_eq7 c hc hc01
          have hnd : (misList c).Nodup := List.Nodup.filter _ List.nodup_range
          have hbij : ∀ b ∈ B7, IsMIS (canonG c hc) (Q b) ∧
              ∀ b' ∈ B7, Q b' = Q b → b' = b := by
            have hsub : (misList c).toFinset ⊆ B7.image (fun b => maskOf (Q b)) := by
              intro m hm
              rw [List.mem_toFinset] at hm
              have hmlt : m < 64 := List.mem_range.1 (List.mem_filter.1 hm).1
              have hmis : IsMIS (canonG c hc) (setOfMask m) := by
                rw [isMIS_iff_mask c hc, maskOf_setOfMask m hmlt]; exact hm
              obtain ⟨b, hbB, heq⟩ := hB7 _ hmis
              exact Finset.mem_image.2 ⟨b, hbB, by rw [← heq, maskOf_setOfMask m hmlt]⟩
            have hcard_eq : (B7.image (fun b => maskOf (Q b))).card = B7.card := by
              have h1 := Finset.card_le_card hsub
              have h2 := Finset.card_image_le (s := B7) (f := fun b => maskOf (Q b))
              rw [List.toFinset_card_of_nodup hnd, hlen7] at h1
              rw [hB7_card] at h2 ⊢
              omega
            have heq_set : (misList c).toFinset = B7.image (fun b => maskOf (Q b)) :=
              Finset.eq_of_subset_of_card_le hsub (by
                rw [hcard_eq, List.toFinset_card_of_nodup hnd, hlen7, hB7_card])
            have hinj := Finset.card_image_iff.1 hcard_eq
            intro b hb
            have hmem : maskOf (Q b) ∈ misList c := by
              have : maskOf (Q b) ∈ (misList c).toFinset := heq_set ▸ Finset.mem_image_of_mem _ hb
              exact List.mem_toFinset.1 this
            exact ⟨(isMIS_iff_mask c hc (Q b)).2 hmem,
              fun b' hb' hq => hinj hb' hb (by dsimp; rw [hq])⟩
          let L1 := sV g1 s1
          let R1 := sV g1 (!s1)
          let L2 := sV g2 s2
          let R2 := sV g2 (!s2)
          have hL1_ne : L1.Nonempty := by
            by_contra hE
            rw [Finset.not_nonempty_iff_eq_empty] at hE
            let b1 : Fin 3 → Bool := fun r => match r.val with | 0 => false | 1 => !s1 | _ => s2
            have hb1 : b1 ∈ B7 := Finset.mem_erase.2 ⟨fun e => by
              have := congrFun e 1; simp [b1, bdrop] at this, Finset.mem_univ _⟩
            have hbk : bkeep ∈ B7 := Finset.mem_erase.2 ⟨fun e => by
              have := congrFun e 0; simp [bkeep, bdrop] at this, Finset.mem_univ _⟩
            have hsub1 : Q b1 ⊆ Q bkeep := by
              intro x hx
              have hF0k : F0 bkeep = false := by simp [F0, F1, F2, hO0, hO1, hO2, bkeep, hs1, hs2]
              simp only [Q, hF0k, F1, F2, hO1, hO2, bkeep, Bool.false_eq_true, ↓reduceIte,
                Finset.empty_union, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
              change x ∉ L1 ∧ x ∉ L2
              refine ⟨by simp [hE], fun hx2 => ?_⟩
              simp only [Q, F2, hO2, b1, Finset.mem_sdiff, Finset.mem_union, not_or] at hx
              exact hx.2.2 (by simpa [L2] using hx2)
            have hne1 : b1 ≠ bkeep := fun e => by have := congrFun e 1; simp [b1, bkeep] at this
            have hmis1 := (hbij b1 hb1).1
            have hmisk := (hbij bkeep hbk).1
            have heq1 : Q b1 = Q bkeep := by
              apply Finset.Subset.antisymm hsub1
              intro u hu
              by_contra hu1
              obtain ⟨v, hv1, huv⟩ := hmis1.2 u hu1
              exact hmisk.1 u hu v (hsub1 hv1) huv
            exact hne1 ((hbij bkeep hbk).2 b1 hb1 heq1)
          have hL2_ne : L2.Nonempty := by
            by_contra hE
            rw [Finset.not_nonempty_iff_eq_empty] at hE
            let b2 : Fin 3 → Bool := fun r => match r.val with | 0 => false | 1 => s1 | _ => !s2
            have hb2 : b2 ∈ B7 := Finset.mem_erase.2 ⟨fun e => by
              have := congrFun e 2; simp [b2, bdrop] at this, Finset.mem_univ _⟩
            have hbk : bkeep ∈ B7 := Finset.mem_erase.2 ⟨fun e => by
              have := congrFun e 0; simp [bkeep, bdrop] at this, Finset.mem_univ _⟩
            have hsub2 : Q b2 ⊆ Q bkeep := by
              intro x hx
              have hF0k : F0 bkeep = false := by simp [F0, F1, F2, hO0, hO1, hO2, bkeep, hs1, hs2]
              simp only [Q, hF0k, F1, F2, hO1, hO2, bkeep, Bool.false_eq_true, ↓reduceIte,
                Finset.empty_union, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and, not_or]
              change x ∉ L1 ∧ x ∉ L2
              refine ⟨fun hx1 => ?_, by simp [hE]⟩
              simp only [Q, F1, hO1, b2, Finset.mem_sdiff, Finset.mem_union, not_or] at hx
              exact hx.2.1.2 (by simpa [L1] using hx1)
            have hne2 : b2 ≠ bkeep := fun e => by have := congrFun e 2; simp [b2, bkeep] at this
            have hmis2 := (hbij b2 hb2).1
            have hmisk := (hbij bkeep hbk).1
            have heq2 : Q b2 = Q bkeep := by
              apply Finset.Subset.antisymm hsub2
              intro u hu
              by_contra hu2
              obtain ⟨v, hv2, huv⟩ := hmis2.2 u hu2
              exact hmisk.1 u hu v (hsub2 hv2) huv
            exact hne2 ((hbij bkeep hbk).2 b2 hb2 heq2)
          have hmiss3 : ∀ (L : Finset (Fin 6)) (S3 : Finset (Fin 3 → Bool)),
              S3 ⊆ B7 → S3.card = 3 → (∀ b ∈ S3, ∀ v ∈ L, v ∉ Q b) →
              ((misList c).filter fun m => (m &&& maskOf L) == 0).length ≥ 3 := by
            intro L S3 hS3sub hS3card hS3disj
            have hndf : ((misList c).filter fun m => (m &&& maskOf L) == 0).Nodup := hnd.filter _
            rw [← List.toFinset_card_of_nodup hndf]
            have himg : S3.image (fun b => maskOf (Q b)) ⊆
                ((misList c).filter fun m => (m &&& maskOf L) == 0).toFinset := by
              intro m hm
              obtain ⟨b, hbS, rfl⟩ := Finset.mem_image.1 hm
              rw [List.mem_toFinset, List.mem_filter, beq_iff_eq]
              refine ⟨(isMIS_iff_mask c hc _).1 (hbij b (hS3sub hbS)).1, ?_⟩
              by_contra hne0
              obtain ⟨v, hvQ, hvL⟩ := (maskOf_and_ne_zero (Q b) L).1 hne0
              exact hS3disj b hbS v hvL hvQ
            have hinj3 : (S3.image (fun b => maskOf (Q b))).card = S3.card := by
              rw [Finset.card_image_iff]
              intro a ha b hb heq
              exact (hbij b (hS3sub hb)).2 a (hS3sub ha) ((maskOf_eq_iff _ _).1 heq)
            have := Finset.card_le_card himg
            omega
          let S1_3 : Finset (Fin 3 → Bool) :=
            {bkeep,
             fun r => match r.val with | 0 => false | 1 => s1 | _ => !s2,
             fun r => match r.val with | 0 => true  | 1 => s1 | _ => !s2}
          let S2_3 : Finset (Fin 3 → Bool) :=
            {bkeep,
             fun r => match r.val with | 0 => false | 1 => !s1 | _ => s2,
             fun r => match r.val with | 0 => true  | 1 => !s1 | _ => s2}
          have hL1_cand : ((misList c).filter fun m => (m &&& maskOf L1) == 0).length ≥ 3 := by
            apply hmiss3 L1 S1_3
            · intro b hb
              simp only [S1_3, Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl <;>
                refine Finset.mem_erase.2 ⟨fun e => ?_, Finset.mem_univ _⟩
              · have := congrFun e 0; simp [bkeep, bdrop] at this
              · have := congrFun e 2; simp [bdrop] at this
              · have := congrFun e 2; simp [bdrop] at this
            · have h12 : bkeep ≠ (fun r : Fin 3 => match r.val with | 0 => false | 1 => s1 | _ => !s2) :=
                fun e => by have := congrFun e 2; simp [bkeep] at this
              have h13 : bkeep ≠ (fun r : Fin 3 => match r.val with | 0 => true | 1 => s1 | _ => !s2) :=
                fun e => by have := congrFun e 2; simp [bkeep] at this
              have h23 : (fun r : Fin 3 => match r.val with | 0 => false | 1 => s1 | _ => !s2) ≠
                         (fun r : Fin 3 => match r.val with | 0 => true | 1 => s1 | _ => !s2) :=
                fun e => by have := congrFun e 0; simp at this
              simp [S1_3, h12, h13, h23]
            · intro b hb v hvL
              simp only [S1_3, Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl <;>
                simp [Q, F1, hO1, bkeep, L1, hvL]
          have hL2_cand : ((misList c).filter fun m => (m &&& maskOf L2) == 0).length ≥ 3 := by
            apply hmiss3 L2 S2_3
            · intro b hb
              simp only [S2_3, Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl <;>
                refine Finset.mem_erase.2 ⟨fun e => ?_, Finset.mem_univ _⟩
              · have := congrFun e 0; simp [bkeep, bdrop] at this
              · have := congrFun e 1; simp [bdrop] at this
              · have := congrFun e 1; simp [bdrop] at this
            · have h12 : bkeep ≠ (fun r : Fin 3 => match r.val with | 0 => false | 1 => !s1 | _ => s2) :=
                fun e => by have := congrFun e 1; simp [bkeep] at this
              have h13 : bkeep ≠ (fun r : Fin 3 => match r.val with | 0 => true | 1 => !s1 | _ => s2) :=
                fun e => by have := congrFun e 1; simp [bkeep] at this
              have h23 : (fun r : Fin 3 => match r.val with | 0 => false | 1 => !s1 | _ => s2) ≠
                         (fun r : Fin 3 => match r.val with | 0 => true | 1 => !s1 | _ => s2) :=
                fun e => by have := congrFun e 0; simp at this
              simp [S2_3, h12, h13, h23]
            · intro b hb v hvL
              simp only [S2_3, Finset.mem_insert, Finset.mem_singleton] at hb
              rcases hb with rfl | rfl | rfl <;>
                simp [Q, F2, hO2, bkeep, L2, hvL]
          have hR_cn : ∀ (i : Fin C.size) (si : Bool), i ∈ O →
              ∀ v ∈ sV i (!si), (cnMask (canonAdj c) (maskOf (sV i si))).testBit v.val = true := by
            intro i si hiO v hvR
            rw [cnMask_spec c hc]
            intro a haL
            by_contra hna
            have hind : IsIndep (canonG c hc) {a, v} := by
              intro x hx y hy
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
              rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
              · exact (canonG c hc).loopless.irrefl _
              · exact hna
              · exact fun h => hna h.symm
              · exact (canonG c hc).loopless.irrefl _
            obtain ⟨I, hsub, hmis⟩ := exists_mis_superset (canonG c hc) {a, v} hind
            have ht : C.gateVal I i = true := by
              rw [gv_iff C hW I i]
              cases si
              · exact ⟨Or.inl ⟨a, haL, hsub (by simp)⟩, Or.inl ⟨v, hvR, hsub (by simp)⟩⟩
              · exact ⟨Or.inl ⟨v, hvR, hsub (by simp)⟩, Or.inl ⟨a, haL, hsub (by simp)⟩⟩
            have hf := hO_false I hmis i hiO
            rw [ht] at hf; cases hf
          have hrem_spec : ∀ u ∈ onesList c,
              (!(bicHit (maskOf L1) (cnMask (canonAdj c) (maskOf L1)) u ||
                bicHit (maskOf L2) (cnMask (canonAdj c) (maskOf L2)) u)) = true →
              (u &&& (maskOf L1 ||| maskOf L2)) ≠ 0 ∧
              (u &&& maskOf (C.leftVars g0)) ≠ 0 ∧ (u &&& maskOf (C.rightVars g0)) ≠ 0 := by
            intro u hu hnot
            simp only [onesList, List.mem_flatMap, List.mem_filterMap, List.mem_range] at hu
            obtain ⟨m, hm, k, hk, hmk⟩ := hu
            by_cases hbit : m.testBit k = true
            · simp [hbit] at hmk
            · simp [hbit] at hmk
              subst hmk
              have hmlt : m < 64 := List.mem_range.1 (List.mem_filter.1 hm).1
              let I := setOfMask m
              have hmis : IsMIS (canonG c hc) I := by
                rw [isMIS_iff_mask c hc, maskOf_setOfMask m hmlt]; exact hm
              let kf : Fin 6 := ⟨k, hk⟩
              have hkfI : kf ∉ I := by rw [mem_setOfMask]; exact hbit
              let U := insert kf I
              rw [← maskOf_insert_eq m hmlt k hk] at hnot ⊢
              change (!(bicHit (maskOf L1) (cnMask (canonAdj c) (maskOf L1)) (maskOf U) ||
                bicHit (maskOf L2) (cnMask (canonAdj c) (maskOf L2)) (maskOf U))) = true at hnot
              change (maskOf U &&& (maskOf L1 ||| maskOf L2)) ≠ 0 ∧
                (maskOf U &&& maskOf (C.leftVars g0)) ≠ 0 ∧ (maskOf U &&& maskOf (C.rightVars g0)) ≠ 0
              simp only [Bool.not_eq_true', Bool.or_eq_false_iff, bicHit, Bool.and_eq_false_iff,
                bne_eq_false_iff_eq] at hnot
              have hno_LR : ∀ (i : Fin C.size) (si : Bool), i ∈ O →
                  (maskOf (sV i si) &&& maskOf U = 0 ∨ cnMask (canonAdj c) (maskOf (sV i si)) &&& maskOf U = 0) →
                  (∃ a ∈ sV i si, a ∈ U) → ∀ b ∈ sV i (!si), b ∉ U := by
                intro i si hiO hdis ⟨a, haL, haU⟩ b hbR hbU
                rcases hdis with h0 | h0
                · exact (maskOf_and_ne_zero _ _).2 ⟨a, haL, haU⟩ h0
                · have := congrArg (fun z => z.testBit b.val) h0
                  rw [Nat.testBit_and, testBit_maskOf, Nat.zero_testBit] at this
                  simp [hR_cn i si hiO b hbR, hbU] at this
              obtain ⟨i, hiO, hti⟩ := hO_true I hmis kf hkfI
              have hhit12_and_g0 : ((∃ a ∈ L1, a ∈ U) ∨ (∃ a ∈ L2, a ∈ U)) ∧ C.gateVal U g0 = true := by
                by_cases hg1t : C.gateVal U g1 = true
                · rw [gv_iff C hW U g1] at hg1t
                  have hlt1 : ∀ j : Fin C.size, j < g1 → j = g0 := fun j hj => Fin.ext (by
                    have hlt := Fin.lt_def.1 hj
                    dsimp [g0, g1] at hlt ⊢; omega)
                  have hside1 : (∃ a ∈ L1, a ∈ U) ∧ ((∃ b ∈ R1, b ∈ U) ∨ C.gateVal U g0 = true) := by
                    cases hs1' : s1
                    · constructor
                      · rcases hg1t.1 with h | ⟨j, hj, _⟩
                        · simpa [L1, sV, hs1'] using h
                        · have hj0 := hlt1 j ((hW g1).1 j hj); subst hj0
                          exact absurd hj (by simpa [sG, hs1'] using hs1)
                      · rcases hg1t.2 with h | ⟨j, hj, hjv⟩
                        · exact Or.inl (by simpa [R1, sV, hs1'] using h)
                        · have hj0 := hlt1 j ((hW g1).2 j hj); subst hj0; exact Or.inr hjv
                    · constructor
                      · rcases hg1t.2 with h | ⟨j, hj, _⟩
                        · simpa [L1, sV, hs1'] using h
                        · have hj0 := hlt1 j ((hW g1).2 j hj); subst hj0
                          exact absurd hj (by simpa [sG, hs1'] using hs1)
                      · rcases hg1t.1 with h | ⟨j, hj, hjv⟩
                        · exact Or.inl (by simpa [R1, sV, hs1'] using h)
                        · have hj0 := hlt1 j ((hW g1).1 j hj); subst hj0; exact Or.inr hjv
                  refine ⟨Or.inl hside1.1, ?_⟩
                  rcases hside1.2 with ⟨b, hbR, hbU⟩ | hg0
                  · exact absurd hbU (hno_LR g1 s1 hO1 hnot.1 hside1.1 b hbR)
                  · exact hg0
                · have hg2t : C.gateVal U g2 = true := by
                    rcases hfin3 i with rfl | rfl | rfl
                    · exact absurd hiO hO0
                    · exact absurd hti hg1t
                    · exact hti
                  rw [gv_iff C hW U g2] at hg2t
                  have hside2 : (∃ a ∈ L2, a ∈ U) ∧ ((∃ b ∈ R2, b ∈ U) ∨ C.gateVal U g0 = true) := by
                    cases hs2' : s2
                    · constructor
                      · rcases hg2t.1 with h | ⟨j, hj, hjv⟩
                        · simpa [L2, sV, hs2'] using h
                        · rcases hfin3 j with rfl | rfl | rfl
                          · exact absurd hj (by simpa [sG, hs2'] using hs2)
                          · exact absurd hjv hg1t
                          · exact absurd ((hW g2).1 g2 hj) (Nat.lt_irrefl _)
                      · rcases hg2t.2 with h | ⟨j, hj, hjv⟩
                        · exact Or.inl (by simpa [R2, sV, hs2'] using h)
                        · rcases hfin3 j with rfl | rfl | rfl
                          · exact Or.inr hjv
                          · exact absurd hjv hg1t
                          · exact absurd ((hW g2).2 g2 hj) (Nat.lt_irrefl _)
                    · constructor
                      · rcases hg2t.2 with h | ⟨j, hj, hjv⟩
                        · simpa [L2, sV, hs2'] using h
                        · rcases hfin3 j with rfl | rfl | rfl
                          · exact absurd hj (by simpa [sG, hs2'] using hs2)
                          · exact absurd hjv hg1t
                          · exact absurd ((hW g2).2 g2 hj) (Nat.lt_irrefl _)
                      · rcases hg2t.1 with h | ⟨j, hj, hjv⟩
                        · exact Or.inl (by simpa [R2, sV, hs2'] using h)
                        · rcases hfin3 j with rfl | rfl | rfl
                          · exact Or.inr hjv
                          · exact absurd hjv hg1t
                          · exact absurd ((hW g2).1 g2 hj) (Nat.lt_irrefl _)
                  refine ⟨Or.inr hside2.1, ?_⟩
                  rcases hside2.2 with ⟨b, hbR, hbU⟩ | hg0
                  · exact absurd hbU (hno_LR g2 s2 hO2 hnot.2 hside2.1 b hbR)
                  · exact hg0
              have hg0_t := hhit12_and_g0.2
              rw [gv_iff C hW U g0] at hg0_t
              have hg0L : ∃ a ∈ C.leftVars g0, a ∈ U := by
                rcases hg0_t.1 with h | ⟨j, hj, _⟩
                · exact h
                · exact (Nat.not_lt_zero j.val ((hW g0).1 j hj)).elim
              have hg0R : ∃ b ∈ C.rightVars g0, b ∈ U := by
                rcases hg0_t.2 with h | ⟨j, hj, _⟩
                · exact h
                · exact (Nat.not_lt_zero j.val ((hW g0).2 j hj)).elim
              refine ⟨?_, ?_, ?_⟩
              · rcases hhit12_and_g0.1 with ⟨a, ha1, haU⟩ | ⟨a, ha2, haU⟩
                · intro h0
                  have := congrArg (fun z => z.testBit a.val) h0
                  rw [Nat.testBit_and, Nat.testBit_or, testBit_maskOf, testBit_maskOf, testBit_maskOf, Nat.zero_testBit] at this
                  simp [haU, ha1] at this
                · intro h0
                  have := congrArg (fun z => z.testBit a.val) h0
                  rw [Nat.testBit_and, Nat.testBit_or, testBit_maskOf, testBit_maskOf, testBit_maskOf, Nat.zero_testBit] at this
                  simp [haU, ha2] at this
              · rw [Nat.and_comm]; exact (maskOf_and_ne_zero _ _).2 hg0L
              · rw [Nat.and_comm]; exact (maskOf_and_ne_zero _ _).2 hg0R
          have hg0_z0 : ∀ m ∈ (misList c).filter (fun m => (m &&& (maskOf L1 ||| maskOf L2)) != 0),
              (m &&& maskOf (C.leftVars g0)) = 0 ∨ (m &&& maskOf (C.rightVars g0)) = 0 := by
            intro m hm
            rw [List.mem_filter, bne_iff_ne] at hm
            have hmlt : m < 64 := List.mem_range.1 (List.mem_filter.1 hm.1).1
            let I := setOfMask m
            have hmis : IsMIS (canonG c hc) I := by
              rw [isMIS_iff_mask c hc, maskOf_setOfMask m hmlt]; exact hm.1
            have hmI : maskOf I = m := maskOf_setOfMask m hmlt
            have hhit : (∃ a ∈ L1, a ∈ I) ∨ (∃ a ∈ L2, a ∈ I) := by
              by_contra hno
              push Not at hno
              apply hm.2
              apply Nat.eq_of_testBit_eq
              intro k
              rw [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit]
              by_cases hk : k < 6
              · let kf : Fin 6 := ⟨k, hk⟩
                have hmbit : m.testBit kf.val = decide (kf ∈ I) := by rw [← hmI, testBit_maskOf]
                change (m.testBit kf.val && ((maskOf L1).testBit kf.val || (maskOf L2).testBit kf.val)) = false
                rw [hmbit, testBit_maskOf, testBit_maskOf]
                by_cases hkI : kf ∈ I
                · have h1 : kf ∉ L1 := fun h => hno.1 kf h hkI
                  have h2 : kf ∉ L2 := fun h => hno.2 kf h hkI
                  simp [hkI, h1, h2]
                · simp [hkI]
              · simp [testBit_eq_false_of_lt64 hmlt hk]
            have hg0_in1 : g0 ∈ sG g1 (!s1) := by
              by_contra hno1
              let b2a : Fin 3 → Bool := fun r => match r.val with | 0 => true | 1 => !s1 | _ => s2
              let b2b : Fin 3 → Bool := fun r => match r.val with | 0 => false | 1 => !s1 | _ => s2
              have hF0a : F0 b2a = false := by simp [F0, F1, F2, hO0, hO1, hO2, b2a, hno1, hs2]
              have hF0b : F0 b2b = false := by simp [F0, F1, F2, hO0, hO1, hO2, b2b, hno1, hs2]
              have heq : Q b2a = Q b2b := by simp [Q, hF0a, hF0b, F1, F2, hO1, hO2, b2a, b2b]
              have haB : b2a ∈ B7 := Finset.mem_erase.2 ⟨fun e => by
                have := congrFun e 1; simp [b2a, bdrop] at this, Finset.mem_univ _⟩
              have hbB : b2b ∈ B7 := Finset.mem_erase.2 ⟨fun e => by
                have := congrFun e 1; simp [b2b, bdrop] at this, Finset.mem_univ _⟩
              have hne : b2a ≠ b2b := fun e => by have := congrFun e 0; simp [b2a, b2b] at this
              exact hne ((hbij b2b hbB).2 b2a haB heq)
            have hg0_in2 : g0 ∈ sG g2 (!s2) := by
              by_contra hno2
              let b2a : Fin 3 → Bool := fun r => match r.val with | 0 => true | 1 => s1 | _ => !s2
              let b2b : Fin 3 → Bool := fun r => match r.val with | 0 => false | 1 => s1 | _ => !s2
              have hF0a : F0 b2a = false := by simp [F0, F1, F2, hO0, hO1, hO2, b2a, hs1, hno2]
              have hF0b : F0 b2b = false := by simp [F0, F1, F2, hO0, hO1, hO2, b2b, hs1, hno2]
              have heq : Q b2a = Q b2b := by simp [Q, hF0a, hF0b, F1, F2, hO1, hO2, b2a, b2b]
              have haB : b2a ∈ B7 := Finset.mem_erase.2 ⟨fun e => by
                have := congrFun e 2; simp [b2a, bdrop] at this, Finset.mem_univ _⟩
              have hbB : b2b ∈ B7 := Finset.mem_erase.2 ⟨fun e => by
                have := congrFun e 2; simp [b2b, bdrop] at this, Finset.mem_univ _⟩
              have hne : b2a ≠ b2b := fun e => by have := congrFun e 0; simp [b2a, b2b] at this
              exact hne ((hbij b2b hbB).2 b2a haB heq)
            have hg0f : C.gateVal I g0 = false := by
              cases hv0 : C.gateVal I g0
              · rfl
              · exfalso
                rcases hhit with ⟨a, ha1, haI⟩ | ⟨a, ha2, haI⟩
                · have h1t : C.gateVal I g1 = true := by
                    rw [gv_iff C hW I g1]
                    cases hs1' : s1
                    · exact ⟨Or.inl ⟨a, by simpa [L1, sV, hs1'] using ha1, haI⟩,
                             Or.inr ⟨g0, by simpa [sG, hs1'] using hg0_in1, hv0⟩⟩
                    · exact ⟨Or.inr ⟨g0, by simpa [sG, hs1'] using hg0_in1, hv0⟩,
                             Or.inl ⟨a, by simpa [L1, sV, hs1'] using ha1, haI⟩⟩
                  have h1f := hO_false I hmis g1 hO1
                  rw [h1t] at h1f; cases h1f
                · have h2t : C.gateVal I g2 = true := by
                    rw [gv_iff C hW I g2]
                    cases hs2' : s2
                    · exact ⟨Or.inl ⟨a, by simpa [L2, sV, hs2'] using ha2, haI⟩,
                             Or.inr ⟨g0, by simpa [sG, hs2'] using hg0_in2, hv0⟩⟩
                    · exact ⟨Or.inr ⟨g0, by simpa [sG, hs2'] using hg0_in2, hv0⟩,
                             Or.inl ⟨a, by simpa [L2, sV, hs2'] using ha2, haI⟩⟩
                  have h2f := hO_false I hmis g2 hO2
                  rw [h2t] at h2f; cases h2f
            rw [← hmI]
            by_contra hboth
            push Not at hboth
            obtain ⟨a, haI, haL⟩ := (maskOf_and_ne_zero I (C.leftVars g0)).1 hboth.1
            obtain ⟨b, hbI, hbR⟩ := (maskOf_and_ne_zero I (C.rightVars g0)).1 hboth.2
            have h0t : C.gateVal I g0 = true :=
              (gv_iff C hW I g0).2 ⟨Or.inl ⟨a, haL, haI⟩, Or.inl ⟨b, hbR, hbI⟩⟩
            rw [h0t] at hg0f; cases hg0f
          have hchk : check3B c = true := check3B_all c hc hc01
          have hm1_pos : 0 < maskOf L1 := by
            obtain ⟨a, ha⟩ := hL1_ne
            by_contra h0
            have h0' : maskOf L1 = 0 := by omega
            have := congrArg (fun x => x.testBit a.val) h0'
            rw [testBit_maskOf] at this; simp [ha] at this
          have hm2_pos : 0 < maskOf L2 := by
            obtain ⟨a, ha⟩ := hL2_ne
            by_contra h0
            have h0' : maskOf L2 = 0 := by omega
            have := congrArg (fun x => x.testBit a.val) h0'
            rw [testBit_maskOf] at this; simp [ha] at this
          have hmem1 : maskOf L1 ∈ ((List.range 63).map (· + 1)).filter
              (fun l => ((misList c).filter fun m => (m &&& l) == 0).length ≥ 3) := by
            simp only [List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
            have := maskOf_lt L1
            exact ⟨⟨maskOf L1 - 1, by omega, by omega⟩, hL1_cand⟩
          have hmem2 : maskOf L2 ∈ ((List.range 63).map (· + 1)).filter
              (fun l => ((misList c).filter fun m => (m &&& l) == 0).length ≥ 3) := by
            simp only [List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
            have := maskOf_lt L2
            exact ⟨⟨maskOf L2 - 1, by omega, by omega⟩, hL2_cand⟩
          rcases le_total (maskOf L1) (maskOf L2) with hle | hle
          · exact check3B_contra c hchk L1 L2 (C.leftVars g0) (C.rightVars g0)
              (maskOf L1) (maskOf L2) hmem1 hmem2 hle (Or.inl ⟨rfl, rfl⟩) hrem_spec hg0_z0
          · exact check3B_contra c hchk L1 L2 (C.leftVars g0) (C.rightVars g0)
              (maskOf L2) (maskOf L1) hmem2 hmem1 hle (Or.inr ⟨rfl, rfl⟩) hrem_spec hg0_z0
    · -- g2 ∈ O, g1 ∉ O: ≤ 6 MISs
      have hnb := hnot_both g1 g2 hO1 hO2
      obtain ⟨s2, hs2⟩ : ∃ s2 : Bool, g1 ∉ sG g2 s2 := by
        by_cases h : g1 ∈ C.leftGates g2
        · exact ⟨true, fun hr => hnb ⟨h, hr⟩⟩
        · exact ⟨false, h⟩
      let B6 : Finset (Fin 3 → Bool) := Finset.univ.filter fun b => b 2 ≠ s2 ∨ b 1 = false
      have hB6 : ∀ I, IsMIS (canonG c hc) I → ∃ b ∈ B6, I = Q b := by
        intro I hmis
        obtain ⟨b, hb⟩ := hQ_mis I hmis
        by_cases h2 : b 2 = s2
        · let b' : Fin 3 → Bool := fun r => match r.val with | 0 => b 0 | 1 => false | _ => s2
          refine ⟨b', by simp [B6, b'], ?_⟩
          have hF1 : F1 b = false := by simp [F1, F2, hO1, hO2, h2, hs2]
          have hF1' : F1 b' = false := by simp [F1, F2, hO1, hO2, b', hs2]
          have hF0 : F0 b = F0 b' := by simp [F0, F2, hF1, hF1', h2, b']
          have hQeq : Q b = Q b' := by simp [Q, hF0, hF1, hF1', F2, h2, b']
          rw [hb, hQeq]
        · exact ⟨b, by simp [B6, h2], hb⟩
      have hB6_card : B6.card = 6 := by
        cases s2 <;> decide
      have hle6 := hmis_card B6 hB6
      rw [hB6_card] at hle6
      omega
  · -- g2 ∉ O: ≤ 4 MISs
    let B4 : Finset (Fin 3 → Bool) := Finset.univ.filter fun b => b 2 = false
    have hB4 : ∀ I, IsMIS (canonG c hc) I → ∃ b ∈ B4, I = Q b := by
      intro I hmis
      obtain ⟨b, hb⟩ := hQ_mis I hmis
      let b' : Fin 3 → Bool := fun r => match r.val with | 0 => b 0 | 1 => b 1 | _ => false
      refine ⟨b', by simp [B4, b'], ?_⟩
      have hF2 : F2 b = false := by simp [F2, hO2]
      have hF2' : F2 b' = false := by simp [F2, hO2]
      have hF1 : F1 b = F1 b' := by simp [F1, hF2, hF2']
      have hF0 : F0 b = F0 b' := by simp [F0, hF2, hF2', hF1, b']
      have hQeq : Q b = Q b' := by simp [Q, hF0, hF1, hF2, hF2', b']
      rw [hb, hQeq]
    have hB4_card : B4.card = 4 := by decide
    have hle4 := hmis_card B4 hB4
    rw [hB4_card] at hle4
    omega

/-! ## Section 4: Ramsey R(3,3) = 6 and table-verified classification of Fin 6 graphs -/

def tab0 : Nat := 0x54ae46f81542f91b60554ae46b81542b91a60554ae467814000000560000000160000000056054ac46f81542f11b60554ac46b81542b11a60554ac46781400000056000000016000000005604cca46f81523691b6054cca46b81523291a6054cca4678140000005600000001600000000560509e85942542721650944ca8594240004a434e54884668540000005600000001600000000560589e857425627215d094cca85742562191a215589ec4703400000056000000016000000005600000001590000000564000000159000000056400000015900000005600000001600000000560000000161000000058400000016100000005840000001610000000560000000160000000056000000015900000005640000001590000000564000000159000000056000000016000000005604ccc46f81523711b6054ccc46b81523311a6054ccc467814000000560000000160000000056044ec85d42503f21740d44e885d42503a21640d44ec46503400000056000000016000000005604cc846f81523611b6054cc846b81523211a6054cc8467814000000560000000160000000056044cc85942503721640d44c885942503221640d44c846485400000056000000016000000005604ccc85742523721540d4cc885742523111a21548dcc47034000000560000000160000000056000000015900000005640000001590000000564000000159000000056000000016000000005600000001610000000584000000161000000058400000016100000005600000001600000000560000000159000000056400000015900000005640000001590000000560000000160000000056054aa46f81542e91b60554aa46b81542a91a60554aa467814000000560000000160000000056054a846f81542e11b60554a846b81542a11a60554a84678140000005600000001600000000560589a85b425626216d095c8a85b03562221640d589a4630340000005600000001600000000560509a859425426216509548a85903542221640d50984628540000005600000001600000000560589a857425626215d0954aa85303542891a215589ac4703400000056000000016000000005600000001590000000564000000159000000056400000015900000005600000001600000000560000000161000000058400000016100000005840000001610000000560000000160000000056000000015900000005640000001590000000564000000159000000056000000016000000005604898c4f03522631340d44a8c4b0340004a584e4c88467034000000560000000160000000056044a8c4d03502e21740d44a8c4903502a21640d44a846503400000056000000016000000005604898c4b03522631240d4c8885b03522221640d48984630340000005600000001600000000560000129683902621640d448885903502221640d000129682800000056000000016000000005604c8885703522621540d44a88530340004a584a4898c4703400000056000000016000000005600000001590000000564000000159000000056400000015900000005600000001600000000560000000161000000058400000016100000005840000001610000000560000000160000000056000000015900000005640000001590000000564000000159000000056000000016000000005605896c4f035625b1340d54a6c4b03562191a40d589685f424000000560000000160000000056054a6c4d03542d21740d54a6c4903542911a40d50b685d42400000056000000016000000005605896c4b035625b1240d4cc285b03523091a40d589685b4240000005600000001600000000560548685903542521640d44c28590340004a434a5096859424000000560000000160000000056054a646f81542d91b60554a646b81542991a60554a6467814000000560000000160000000056000000015900000005640000001590000000564000000159000000056000000016000000005600000001610000000584000000161000000058400000016100000005600000001600000000560000000159000000056400000015900000005640000001590000000560000000160000000056000000015a000000056800000015a000000056800000015a0000000560000000160000000056000000015a000000056800000015a000000056800000015a0000000560000000160000000056000000015a000000056800000015a000000056800000015a0000000560000000160000000056000000015a000000056800000015a000000056800000015a0000000560000000160000000056000000015a000000056800000015a000000056800000015a000000056000000016000000005600000001590000000564000000159000000056400000015900000005600000001600000000560000000161000000058400000016100000005840000001610000000560000000160000000056000000015900000005640000001590000000564000000159000000056000000016000000005600000001620000000588000000162000000058800000016200000005600000001600000000560000000162000000058800000016200000005880000001620000000560000000160000000056000000016200000005880000001620000000588000000162000000056000000016000000005600000001620000000588000000162000000058800000016200000005600000001600000000560000000162000000058800000016200000005880000001620000000560000000160000000056000000015900000005640000001590000000564000000159000000056000000016000000005600000001610000000584000000161000000058400000016100000005600000001600000000560000000159000000056400000015900000005640000001590000000560000000160000000056000000015a000000056800000015a000000056800000015a0000000560000000160000000056000000015a000000056800000015a000000056800000015a0000000560000000160000000056000000015a000000056800000015a000000056800000015a0000000560000000160000000056000000015a000000056800000015a000000056800000015a0000000560000000160000000056000000015a000000056800000015a000000056800000015a00000005600000001600000000560000000159000000056400000015900000005640000001590000000560000000160000000056000000016100000005840000001610000000584000000161000000056000000016000000005600000001590000000564000000159000000056400000015900000005600000001600000000560
def tab1 : Nat := 0xd4ae46f817627b13d09d4ae46b817232627d09d4ae467817231627d090000001600000000580d4aec4f81742fb13605d4aec4b81742bb12605d4aec4781742bb116050000001600000000580ccca46f817627b12d09ccca46b817232626d09ccca467817231626d090000001600000000580c4c94af81703642f605c4c94ab81703242e605c4c94a78170324296050000001600000000580ccc646f817627b11d09ccc646b817232625d09ccc6467817231625d090000001600000000580c4c54af81703542f605c4c54ab81703142a605c4c54a781703142d605000000160000000058000000016100000005840000001610000000584000000161000000058400000016000000005800000001610000000584000000161000000058400000016100000005840000001600000000580cccf42f817237d0b605cccf42b817233d0a605cccf427817233d096050000001600000000580c4ed42f81703f50b605c4ed42b81703b50a605c4ed42781703b5096050000001600000000580cccb42f817236d0b605cccb42b817232d0a605cccb427817232d096050000001600000000580c4c942f81703650b605c4c942b81703250a605c4c94278170325096050000001600000000580ccc742f817235d0b605ccc742b817231d0a605ccc7427817231d096050000001600000000580c4c542f81703550b605c4c542b81703150a605c4c5427817031509605000000160000000058000000016100000005840000001610000000584000000161000000058400000016000000005800000001610000000584000000161000000058400000016100000005840000001600000000580d4aa46f817626b13d09d4aa46b81742a626b11d4aa467816231627d090000001600000000580d4aac4f81742eb13605d4aac4b81742ab12605d4aac4781742ab116050000001600000000580d89a85b427626b12d09dc8a85b03642f6229198cc589b426231626d09000000160000000058094ad09ac47426b1250990bd48a85742211a21594a509ac4603942650900000016000000005808cc54af817626b11d098cc54ab81542a626b118cc54a7816231625d09000000160000000058084c54af81603542f60584c54ab81603542a60584c54a781603142d6050000001600000000580000000161000000058400000016100000005840000001610000000584000000160000000058000000016100000005840000001610000000584000000161000000058400000016000000005808ccc4af81623702f6058ccc4ab81623702a6058ccc4a78162330296050000001600000000580c4a8c4f81702e313605c4a8c4b81702a312605c4a8c4781702a31160500000016000000005808ccc89b427226312d0988dcc8b03722211a40d8cc489b426039226311000000160000000058084ec099427026312509c48885903702221640d84e40994240002a631200000016000000005808cc44af81623502f6058cc44ab81623502a6058cc44a781623102d605000000160000000058084cc09542702631150980d44a8c440002a607284c40b5424000544472000000160000000058000000016100000005840000001610000000584000000161000000058400000016000000005800000001610000000584000000161000000058400000016100000005840000001600000000580d4a646f817625b13d09d4a646b815232627d09d4a6467817429625b110000001600000000580d4a6c4f81742db13605d4a6c4b817429b12605d4a6c47817429b1160500000016000000005804cc94af817625b12d094cc94ab815232626d094cc94a7816429625b11000000160000000058044c94af81503642f60544c94ab81503242e60544c94a78150364296050000001600000000580d896857427625b11d094cc9897425232625d09dc8685703542f621919000000160000000058054ad096c47425b1150954a9096c4503a42550950bd4868574211192150000001600000000580000000161000000058400000016100000005840000001610000000584000000160000000058000000016100000005840000001610000000584000000161000000058400000016000000005804ccc4af81523702f6054ccc4ab81523302a6054ccc4a78152370296050000001600000000580c4a4c4f81702d313605c4a4c4b817029312605c4a4c4781702931160500000016000000005804cc84af81523602f6054cc84ab81523202e6054cc84a7815236029605000000160000000058044cc09942702531250944c80b94240002a447240d84a4c4400054607200000016000000005804ccc897427225311d094cc889742503a22531148dcc8703722111940d000000160000000058044ec09542702531150944e8095424000546312c48485503702121540d0000001600000000580000000161000000058400000016100000005840000001610000000584000000160000000058000000016100000005840000001610000000584000000161000000058400000016000000005800000001620000000588000000162000000058800000016200000005880000001600000000580000000162000000058800000016200000005880000001620000000588000000160000000058000000016200000005880000001620000000588000000162000000058800000016000000005800000001620000000588000000162000000058800000016200000005880000001600000000580000000162000000058800000016200000005880000001620000000588000000160000000058000000016200000005880000001620000000588000000162000000058800000016000000005800000001610000000584000000161000000058400000016100000005840000001600000000580000000161000000058400000016100000005840000001610000000584000000160000000058000000016200000005880000001620000000588000000162000000058800000016000000005800000001620000000588000000162000000058800000016200000005880000001600000000580000000162000000058800000016200000005880000001620000000588000000160000000058000000016200000005880000001620000000588000000162000000058800000016000000005800000001620000000588000000162000000058800000016200000005880000001600000000580000000162000000058800000016200000005880000001620000000588000000160000000058000000016100000005840000001610000000584000000161000000058400000016000000005800000001610000000584000000161000000058400000016100000005840000001600000000580
def tab2 : Nat := 0xa95cccf036b53237d09a95cccf426667233d09ad4cccf426b53233d09a94cccf426c4b623919ad4c4ef816b5303f605b91d4aec4646f03b509bd0d4aec46b5303b509b90d4aec46e4342b119a56cccf816d4b627b11a17cccb81646f232d09b52dc8ec46d4b623b11a16cccb426c4b62291995ac4cf81646f03760591bc4cb81646f03260595ad48ec4654b423b11b1094aec4646b422119ad4cccf816f43627b11b91dc8ec46667623b11ad4ccc7816b53231d09a94ccc7426a53621919ad4c4cf816b53037605b91d48ec46647423b11ad4c4c7816b5303160591854aec46a53421119a54cccf816d43627b11a15cccb816c42627b11a54ccc7816461627b11a14ccc3816c43230919b11d48e856d43427215b11d48a856467422215a54d486856953421215b10c4c285400046852eb52c4ef816d4b03f605b91cccf426647233d09bd0cccf426353233d09b90cccf426e43233119952c4ef81654b03f605b91c4ed42664703b509bd0c4ed42635303b509b90c4ed42644b03b119b52cccf816d4b237605b13cccb816c4b232605b52cccccc6d4b233311b12cccb426c4b232119952c4cf81654b037605913c4cb81644f032605952c4ccc4654b033311b10c4c942644b032119bd0cccf816f43237605b91cccccc6647233311bd0ccc7816f43231605b90ccc7426e432311198d4c4cf816353037605b91c4ccc466470333118d4c4c7816353031605b90c4c5426253031119b50cccf816d43237605b11cccb816c43232605b50ccc7816d43231605b10ccc3816c43230605b50c4cc856447037215b11c4c8856447032215b50c4c4856153031215b10c4c142400035052aa56d4af816b53627d09a17d4ab816a52627d09ad4dc8f426b53623d09a948ccf426a53622919ad4d4af816b5342f605a95d4ab816a5342a605ad4d4ad4a6b5342b509a94d4aac46a5342a119a5694af81695b626d09a1794ab81685a626d09a56dc8b42695b622d09a168ccb42685a42a919a5494af81695242f605a1594ab81685242e60585ed48ac46953422509a1494aac4685242a119ad4dc8f816b53627625a95dc8b816277622b11ad4dc87816b53621d09a94dc83816a53620919ad4d48f816b53427605a95d48b816a53422605ad4d487816b53421605a94d483816a53420605a548ccf816953626b11a158ccb816852626b11a548cc7816953620d09a148cc3816852230919a54d48a856953426215a15909a856852426215a54d482856953420509a1484c285400038852a8dcc4af81627702f60589dc4ab81627702a6058dccc8f426353223d09a908ccf4262732221198d4c4af81635302f605895c4ab81625702a6058d4c4ad42635302b509a9084ed42625302a119a528ccf81694a237605a138ccb81684a23660585ecc8b42615b222d09a128ccb42684a23211985ec09942615b026509a1184e94240000a634e85ec48942615b022509a1084e94240000a5a8a8dccc8f81635322760589dcc8b8162772226058dccc8781635322160589ccc838162732206058d4c48f816353027605895c48b8162570226058d4c487816353021605894c483816253020605a508ccf816942237605a118ccb816842236605a508cc7816942231605a108cc381684223060585cc488856153026215a1184c88540000a5c4a85cc481426153020509a1084c142400028c526b52d4af816f43627d09b91dc8f426667623d09b52d4a7816661627d099984ccf426c4b621919bd0d4af816f4342f605b91d4ad4a664742b509bd0d4a7816f43429605b90d4a6c46e43429119b52dc8f816d4b627625b13dc8b81646f622d09b52dc87816d4b621b11b12dc83816c4b62091995ad48f81654b42760591bd48b81646f42260595ad48781654b42160591ad48381646b4206059d854af816f43625d09b91dc87426667621d099d854a7816661625d099984cc742666142991995854af81646542f605b91d486c4664742150995854a781646142d60591854a6c464614291199584ccf816d43625b119194ccb816467620d099584cc7816461625b119184cc3816461230919b11d486856d43425215b11d482856467420509958509685646142521591844c285400046852ab52c4af816d4b02f605b91cc8f426647223d09b52c4a7816d4b0296058984ccf426c4b221119952c4af81654b02f605b91c4ad42664702b509952c4a781654b02960581a44ed42644b029119b52cc8f816d4b227605b13cc8b816c4b222605b52cc87816d4b221605b12cc83816c4b220605952c48f81654b027605913c48b81644f022605952c48781654b021605912c48381644b0206058d84ccf816265237605b91cc87426647221d098d84cc78162612356058984cc7426261231119b91c095426647025509b91c48542664702150985844e542400050634e81844e5424000505a8a8584ccf8160652376058194ccb8160652326058584cc78160612356058184cc3816061230605b11c484856447025215b11c48142644702050985844c4854000505c4a81844c142400044c526a52d4af816b43627d09a13d4ab816a42627d09a52d4a7816261627d09a12d4a3816a43428919ad0d4af816b4342f605a91d4ab816a4342a605ad0d4a7816b43429605a90d4a3816a43428605a5294af81694b626d09a1394ab81684a626d09a5294a7816069626d09a1294a381684a428919a5094af81694242f605a1194ab81684242e605a5094a7816942429605a1094a38168424286058d854af816b43625d0989954ab816a42625d098d854a7816261625d0989854a381626142891985854af81606542f60581954ab81606542a60585854a781606142d60581854a3816061428605a11d893426943624d09a119893426842624d098585893426061624d090001488d38000521a8aa50d092856943424509a11909285684242450985850928560614245090001487128000468526a91cc8f036b4322740da91cc8b03626722240da52cc8703694b22140da90c4a303400046a82ead0c4ad03624702f40da91c4a903624702a40dad0c4a503614b02940da90c4a103400035282aa52cc8b03694b22640da13889b03684a22640da52cc8303694b22040da1284a303400038a82a85ac48903614b02640da1184a90340000a634a85ac48103614b02040da1084a103400028e826a91cc87036b4322540da91cc8303626722040d8d8489703626122540d89844a303400046a82aa91c48503624702540da91c48103624702040d85844a503400050634a81844a103400044e826a50c89303694322440da11889303684222440d858489303606122440d0001488d2800046a82600011aa43800035290a0000e2a42800028e90600011aa42800044e90600011aa41800046a902

def fld (T w i : Nat) : Nat := (T >>> (w * i)) &&& (2 ^ w - 1)

def tabOf : Nat → Nat
  | 0 => tab0
  | 1 => tab1
  | _ => tab2

def normAdj (t cm u v : Nat) : Bool :=
  if u == v then false
  else
    let a := min u v
    let b := max u v
    if a < 3 && b < 3 then true
    else if a == 3 && b == 4 then true
    else if a == 3 && b == 5 then decide (1 ≤ t)
    else if a == 4 && b == 5 then decide (2 ≤ t)
    else cm.testBit (a * 3 + (b - 3))

def okBic (t cm x y : Nat) : Bool :=
  (List.range 6).all fun a => (List.range 6).all fun b =>
    !(x.testBit a && y.testBit b) || normAdj t cm a b

def covBic (x0 y0 x1 y1 x2 y2 a b : Nat) : Bool :=
  (x0.testBit a && y0.testBit b) || (x0.testBit b && y0.testBit a) ||
  (x1.testBit a && y1.testBit b) || (x1.testBit b && y1.testBit a) ||
  (x2.testBit a && y2.testBit b) || (x2.testBit b && y2.testBit a)

def verifyEntry (t cm : Nat) : Bool :=
  let v := fld (tabOf t) 38 cm
  let tag := v &&& 3
  if tag == 0 then
    let a := (v >>> 2) &&& 7
    let b := (v >>> 5) &&& 7
    let c := (v >>> 8) &&& 7
    a < 6 && b < 6 && c < 6 && a ≠ b && a ≠ c && b ≠ c &&
    !(normAdj t cm a b) && !(normAdj t cm a c) && !(normAdj t cm b c)
  else if tag == 1 then
    let x0 := (v >>> 2) &&& 63
    let y0 := (v >>> 8) &&& 63
    let x1 := (v >>> 14) &&& 63
    let y1 := (v >>> 20) &&& 63
    let x2 := (v >>> 26) &&& 63
    let y2 := (v >>> 32) &&& 63
    okBic t cm x0 y0 && okBic t cm x1 y1 && okBic t cm x2 y2 &&
    (List.range 6).all fun a => (List.range 6).all fun b =>
      !(normAdj t cm a b) || covBic x0 y0 x1 y1 x2 y2 a b
  else if tag == 2 then
    let ci := (v >>> 2) &&& 7
    ci < 5 &&
    (List.range 6).all (fun j => ((v >>> (5 + 3 * j)) &&& 7) < 6) &&
    (List.range 6).all (fun i => (List.range 6).all fun j =>
      i == j || ((v >>> (5 + 3 * i)) &&& 7) != ((v >>> (5 + 3 * j)) &&& 7)) &&
    (List.range 6).all (fun a => (List.range 6).all fun b =>
      normAdj t cm a b == (canonAdj ci ((v >>> (5 + 3 * a)) &&& 7)).testBit ((v >>> (5 + 3 * b)) &&& 7))
  else false

def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f n o} (h : span f n o = true) : ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o + a) = true) :
    span f (a + b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

theorem v0_0 : span (verifyEntry 0) 128 0 = true := by decide +kernel
theorem v0_1 : span (verifyEntry 0) 128 128 = true := by decide +kernel
theorem v0_2 : span (verifyEntry 0) 128 256 = true := by decide +kernel
theorem v0_3 : span (verifyEntry 0) 128 384 = true := by decide +kernel

theorem v1_0 : span (verifyEntry 1) 128 0 = true := by decide +kernel
theorem v1_1 : span (verifyEntry 1) 128 128 = true := by decide +kernel
theorem v1_2 : span (verifyEntry 1) 128 256 = true := by decide +kernel
theorem v1_3 : span (verifyEntry 1) 128 384 = true := by decide +kernel

theorem v2_0 : span (verifyEntry 2) 128 0 = true := by decide +kernel
theorem v2_1 : span (verifyEntry 2) 128 128 = true := by decide +kernel
theorem v2_2 : span (verifyEntry 2) 128 256 = true := by decide +kernel
theorem v2_3 : span (verifyEntry 2) 128 384 = true := by decide +kernel

theorem verifyEntry_all (t : Nat) (ht : t < 3) (cm : Nat) (hcm : cm < 512) :
    verifyEntry t cm = true := by
  interval_cases t
  · by_cases h1 : cm < 128
    · exact span_ok v0_0 cm (Nat.zero_le _) h1
    · by_cases h2 : cm < 256
      · exact span_ok v0_1 cm (by omega) h2
      · by_cases h3 : cm < 384
        · exact span_ok v0_2 cm (by omega) h3
        · exact span_ok v0_3 cm (by omega) hcm
  · by_cases h1 : cm < 128
    · exact span_ok v1_0 cm (Nat.zero_le _) h1
    · by_cases h2 : cm < 256
      · exact span_ok v1_1 cm (by omega) h2
      · by_cases h3 : cm < 384
        · exact span_ok v1_2 cm (by omega) h3
        · exact span_ok v1_3 cm (by omega) hcm
  · by_cases h1 : cm < 128
    · exact span_ok v2_0 cm (Nat.zero_le _) h1
    · by_cases h2 : cm < 256
      · exact span_ok v2_1 cm (by omega) h2
      · by_cases h3 : cm < 384
        · exact span_ok v2_2 cm (by omega) h3
        · exact span_ok v2_3 cm (by omega) hcm

def comapG (G : SimpleGraph (Fin 6)) (σ : Equiv.Perm (Fin 6)) : SimpleGraph (Fin 6) where
  Adj u v := G.Adj (σ u) (σ v)
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => G.loopless.irrefl (σ u) h⟩

def comapC (C : AndCountCircuit 6) (σ : Equiv.Perm (Fin 6)) : AndCountCircuit 6 where
  size := C.size
  leftVars i := (C.leftVars i).image σ.symm
  leftGates := C.leftGates
  rightVars i := (C.rightVars i).image σ.symm
  rightGates := C.rightGates
  outVars := C.outVars.image σ.symm
  outGates := C.outGates

theorem comapC_wf (C : AndCountCircuit 6) (σ : Equiv.Perm (Fin 6)) (hW : C.WellFormed) :
    (comapC C σ).WellFormed := hW

theorem comapC_gateVal (C : AndCountCircuit 6) (σ : Equiv.Perm (Fin 6)) (U : Finset (Fin 6)) :
    ∀ d (i : Fin C.size), gateValFuel (comapC C σ) U d i = gateValFuel C (U.image σ) d i := by
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
    intro i
    simp only [gateValFuel, comapC]
    congr 1
    · unfold sideTrue
      apply decide_eq_decide.mpr
      simp only [Finset.mem_image]
      constructor
      · rintro (⟨v, ⟨w, hw, rfl⟩, hvU⟩ | ⟨j, hj, hji, hgv⟩)
        · exact Or.inl ⟨w, hw, ⟨σ.symm w, hvU, by simp⟩⟩
        · exact Or.inr ⟨j, hj, hji, by rw [← ih j]; exact hgv⟩
      · rintro (⟨w, hw, ⟨u, huU, rfl⟩⟩ | ⟨j, hj, hji, hgv⟩)
        · exact Or.inl ⟨u, ⟨σ u, hw, by simp⟩, huU⟩
        · refine Or.inr ⟨j, hj, hji, ?_⟩
          change (comapC C σ).gateValFuel U d j = true
          rw [ih j]; exact hgv
    · unfold sideTrue
      apply decide_eq_decide.mpr
      simp only [Finset.mem_image]
      constructor
      · rintro (⟨v, ⟨w, hw, rfl⟩, hvU⟩ | ⟨j, hj, hji, hgv⟩)
        · exact Or.inl ⟨w, hw, ⟨σ.symm w, hvU, by simp⟩⟩
        · exact Or.inr ⟨j, hj, hji, by rw [← ih j]; exact hgv⟩
      · rintro (⟨w, hw, ⟨u, huU, rfl⟩⟩ | ⟨j, hj, hji, hgv⟩)
        · exact Or.inl ⟨u, ⟨σ u, hw, by simp⟩, huU⟩
        · refine Or.inr ⟨j, hj, hji, ?_⟩
          change (comapC C σ).gateValFuel U d j = true
          rw [ih j]; exact hgv

theorem comapC_eval (C : AndCountCircuit 6) (σ : Equiv.Perm (Fin 6)) (U : Finset (Fin 6)) :
    (comapC C σ).eval U = C.eval (U.image σ) := by
  unfold AndCountCircuit.eval gateVal
  apply decide_eq_decide.mpr
  simp only [comapC, Finset.mem_image]
  constructor
  · rintro (⟨v, ⟨w, hw, rfl⟩, hvU⟩ | ⟨j, hj, hgv⟩)
    · exact Or.inl ⟨w, hw, ⟨σ.symm w, hvU, by simp⟩⟩
    · exact Or.inr ⟨j, hj, by rw [← comapC_gateVal]; exact hgv⟩
  · rintro (⟨w, hw, ⟨u, huU, rfl⟩⟩ | ⟨j, hj, hgv⟩)
    · exact Or.inl ⟨u, ⟨σ u, hw, by simp⟩, huU⟩
    · refine Or.inr ⟨j, hj, ?_⟩
      change (comapC C σ).gateValFuel U C.size j = true
      rw [comapC_gateVal]; exact hgv

theorem comapG_partial (G : SimpleGraph (Fin 6)) (C : AndCountCircuit 6) (σ : Equiv.Perm (Fin 6))
    (hP : PartialCond G C) : PartialCond (comapG G σ) (comapC C σ) := by
  intro I hmis
  have hmis' : IsMIS G (I.image σ) := by
    refine ⟨fun a ha b hb => ?_, fun u hu => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
      exact hmis.1 x hx y hy
    · have hsu : σ.symm u ∉ I := fun h => hu (Finset.mem_image.2 ⟨σ.symm u, h, by simp⟩)
      obtain ⟨v, hvI, huv⟩ := hmis.2 (σ.symm u) hsu
      refine ⟨σ v, Finset.mem_image_of_mem _ hvI, ?_⟩
      simpa [comapG] using huv
  have h1 := hP (I.image σ) hmis'
  refine ⟨by rw [comapC_eval]; exact h1.1, fun u hu => ?_⟩
  rw [comapC_eval, Finset.image_insert]
  have hsu : σ u ∉ I.image σ := fun h => by
    obtain ⟨v, hvI, he⟩ := Finset.mem_image.1 h
    exact hu ((σ.injective he) ▸ hvI)
  exact h1.2 (σ u) hsu

theorem HasBC_of_comap (G : SimpleGraph (Fin 6)) (σ : Equiv.Perm (Fin 6)) (k : ℕ)
    (h : HasBC (comapG G σ) k) : HasBC G k := by
  obtain ⟨X, Y, hbic, hcov⟩ := h
  refine ⟨fun i => (X i).image σ, fun i => (Y i).image σ, ?_, ?_⟩
  · intro i a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
    exact hbic i x hx y hy
  · intro a b hab
    have hab' : (comapG G σ).Adj (σ.symm a) (σ.symm b) := by simpa [comapG] using hab
    obtain ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hcov (σ.symm a) (σ.symm b) hab'
    · exact ⟨i, Or.inl ⟨Finset.mem_image.2 ⟨_, h1, by simp⟩, Finset.mem_image.2 ⟨_, h2, by simp⟩⟩⟩
    · exact ⟨i, Or.inr ⟨Finset.mem_image.2 ⟨_, h1, by simp⟩, Finset.mem_image.2 ⟨_, h2, by simp⟩⟩⟩

theorem ramsey_triangle (G : SimpleGraph (Fin 6))
    (hno3 : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → ¬ G.Adj a b → ¬ G.Adj a c → G.Adj b c) :
    ∃ a b c : Fin 6, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  classical
  let N0 := (Finset.univ.erase (0 : Fin 6)).filter fun v => G.Adj 0 v
  let M0 := (Finset.univ.erase (0 : Fin 6)).filter fun v => ¬ G.Adj 0 v
  have hsum : N0.card + M0.card = 5 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ.erase (0 : Fin 6))
      (p := fun v => G.Adj 0 v)
    change N0.card + M0.card = (Finset.univ.erase (0 : Fin 6)).card at h1
    have h5 : (Finset.univ.erase (0 : Fin 6)).card = 5 := by decide
    omega
  by_cases hN : 3 ≤ N0.card
  · obtain ⟨S, hSN, hS3⟩ := Finset.exists_subset_card_eq hN
    obtain ⟨a, b, c, hab, hac, hbc, hSeq⟩ := Finset.card_eq_three.1 hS3
    have ha : G.Adj 0 a := (Finset.mem_filter.1 (hSN (show a ∈ S by rw [hSeq]; simp))).2
    have hb : G.Adj 0 b := (Finset.mem_filter.1 (hSN (show b ∈ S by rw [hSeq]; simp))).2
    have hc : G.Adj 0 c := (Finset.mem_filter.1 (hSN (show c ∈ S by rw [hSeq]; simp))).2
    by_cases eab : G.Adj a b
    · exact ⟨0, a, b, ha, hb, eab⟩
    · by_cases eac : G.Adj a c
      · exact ⟨0, a, c, ha, hc, eac⟩
      · exact ⟨0, b, c, hb, hc, hno3 a b c hab hac hbc eab eac⟩
  · have hM : 3 ≤ M0.card := by omega
    obtain ⟨S, hSM, hS3⟩ := Finset.exists_subset_card_eq hM
    obtain ⟨a, b, c, hab, hac, hbc, hSeq⟩ := Finset.card_eq_three.1 hS3
    have ha0 : a ≠ 0 ∧ ¬ G.Adj 0 a := by
      have h := Finset.mem_filter.1 (hSM (show a ∈ S by rw [hSeq]; simp))
      exact ⟨(Finset.mem_erase.1 h.1).1, h.2⟩
    have hb0 : b ≠ 0 ∧ ¬ G.Adj 0 b := by
      have h := Finset.mem_filter.1 (hSM (show b ∈ S by rw [hSeq]; simp))
      exact ⟨(Finset.mem_erase.1 h.1).1, h.2⟩
    have hc0 : c ≠ 0 ∧ ¬ G.Adj 0 c := by
      have h := Finset.mem_filter.1 (hSM (show c ∈ S by rw [hSeq]; simp))
      exact ⟨(Finset.mem_erase.1 h.1).1, h.2⟩
    exact ⟨a, b, c,
      hno3 0 a b ha0.1.symm hb0.1.symm hab ha0.2 hb0.2,
      hno3 0 a c ha0.1.symm hc0.1.symm hac ha0.2 hc0.2,
      hno3 0 b c hb0.1.symm hc0.1.symm hbc hb0.2 hc0.2⟩

theorem exists_perm_of_six (v0 v1 v2 v3 v4 v5 : Fin 6)
    (hnd : [v0, v1, v2, v3, v4, v5].Nodup) :
    ∃ σ : Equiv.Perm (Fin 6),
      σ 0 = v0 ∧ σ 1 = v1 ∧ σ 2 = v2 ∧ σ 3 = v3 ∧ σ 4 = v4 ∧ σ 5 = v5 := by
  let f : Fin 6 → Fin 6 := fun i => match i.val with
    | 0 => v0 | 1 => v1 | 2 => v2 | 3 => v3 | 4 => v4 | _ => v5
  have hinj : Function.Injective f := by
    intro i j hij
    have hpair : ∀ a b : Fin 6, a ≠ b → f a ≠ f b := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true] at hnd
      intro a b hab
      fin_cases a <;> fin_cases b <;> try exact absurd rfl hab
      all_goals (dsimp only [f]; tauto)
    by_contra hne
    exact hpair i j hne hij
  exact ⟨Equiv.ofBijective f ((Finite.injective_iff_bijective).1 hinj), rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem normAdj_34 (t cm : Nat) : normAdj t cm 3 4 = true := by unfold normAdj; simp
theorem normAdj_35 (t cm : Nat) : normAdj t cm 3 5 = decide (1 ≤ t) := by unfold normAdj; simp
theorem normAdj_45 (t cm : Nat) : normAdj t cm 4 5 = decide (2 ≤ t) := by unfold normAdj; simp

theorem classify_fin6 (G : SimpleGraph (Fin 6)) :
    HasBC G 3 ∨ ∃ (c : Nat) (hc : c < 5) (σ : Equiv.Perm (Fin 6)), comapG G σ = canonG c hc := by
  classical
  by_cases hi3 : ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c
  · obtain ⟨a, b, c, hab, hac, hbc, h1, h2, h3⟩ := hi3
    let T : Finset (Fin 6) := ((Finset.univ.erase a).erase b).erase c
    have hcard : T.card = 3 := by
      have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ _⟩
      have hc' : c ∈ (Finset.univ.erase a).erase b :=
        Finset.mem_erase.2 ⟨hbc.symm, Finset.mem_erase.2 ⟨hac.symm, Finset.mem_univ _⟩⟩
      rw [Finset.card_erase_of_mem hc', Finset.card_erase_of_mem hb,
        Finset.card_erase_of_mem (Finset.mem_univ a)]
      decide
    left
    rw [← hcard]
    apply HasBC_of_vc G T
    intro x y hxy
    by_contra h
    push Not at h
    simp only [T, Finset.mem_erase, Finset.mem_univ, and_true, not_and, not_not] at h
    have hx : x = a ∨ x = b ∨ x = c := by by_cases hxc : x = c; exact Or.inr (Or.inr hxc); by_cases hxb : x = b; exact Or.inr (Or.inl hxb); exact Or.inl (h.1 hxc hxb)
    have hy : y = a ∨ y = b ∨ y = c := by by_cases hyc : y = c; exact Or.inr (Or.inr hyc); by_cases hyb : y = b; exact Or.inr (Or.inl hyb); exact Or.inl (h.2 hyc hyb)
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact G.loopless.irrefl _ hxy
    · exact h1 hxy
    · exact h2 hxy
    · exact h1 hxy.symm
    · exact G.loopless.irrefl _ hxy
    · exact h3 hxy
    · exact h2 hxy.symm
    · exact h3 hxy.symm
    · exact G.loopless.irrefl _ hxy
  · push Not at hi3
    obtain ⟨v0, v1, v2, h01, h02, h12⟩ := ramsey_triangle G hi3
    have h01n : v0 ≠ v1 := G.ne_of_adj h01
    have h02n : v0 ≠ v2 := G.ne_of_adj h02
    have h12n : v1 ≠ v2 := G.ne_of_adj h12
    let R : Finset (Fin 6) := ((Finset.univ.erase v0).erase v1).erase v2
    have hR3 : R.card = 3 := by
      have hb : v1 ∈ Finset.univ.erase v0 := Finset.mem_erase.2 ⟨h01n.symm, Finset.mem_univ _⟩
      have hc' : v2 ∈ (Finset.univ.erase v0).erase v1 :=
        Finset.mem_erase.2 ⟨h12n.symm, Finset.mem_erase.2 ⟨h02n.symm, Finset.mem_univ _⟩⟩
      rw [Finset.card_erase_of_mem hc', Finset.card_erase_of_mem hb,
        Finset.card_erase_of_mem (Finset.mem_univ v0)]
      decide
    obtain ⟨w0, w1, w2, hw01, hw02, hw12, hReq⟩ := Finset.card_eq_three.1 hR3
    have hR_ne : ∀ w ∈ R, w ≠ v0 ∧ w ≠ v1 ∧ w ≠ v2 := by
      intro w hw
      simp only [R, Finset.mem_erase, Finset.mem_univ, and_true] at hw
      exact ⟨hw.2.2, hw.2.1, hw.1⟩
    have hor : G.Adj w0 w1 ∨ G.Adj w0 w2 ∨ G.Adj w1 w2 := by
      by_contra h
      push Not at h
      exact h.2.2 (hi3 w0 w1 w2 hw01 hw02 hw12 h.1 h.2.1)
    have hord : ∃ (v3 v4 v5 : Fin 6) (t : Nat), t < 3 ∧
        [v0, v1, v2, v3, v4, v5].Nodup ∧
        G.Adj v3 v4 ∧
        (G.Adj v3 v5 ↔ 1 ≤ t) ∧ (G.Adj v4 v5 ↔ 2 ≤ t) := by
      have make_nd : ∀ a b c : Fin 6, ({a, b, c} : Finset (Fin 6)) = R →
          a ≠ b → a ≠ c → b ≠ c → [v0, v1, v2, a, b, c].Nodup := by
        intro a b c heq hab hac hbc
        have ha := hR_ne a (heq ▸ by simp)
        have hb := hR_ne b (heq ▸ by simp)
        have hc' := hR_ne c (heq ▸ by simp)
        simp [h01n, h02n, h12n, hab, hac, hbc, ha.1.symm, ha.2.1.symm, ha.2.2.symm,
          hb.1.symm, hb.2.1.symm, hb.2.2.symm, hc'.1.symm, hc'.2.1.symm, hc'.2.2.symm]
      have handle_edge : ∀ a b c : Fin 6, ({a, b, c} : Finset (Fin 6)) = R →
          a ≠ b → a ≠ c → b ≠ c → G.Adj a b →
          ∃ (v3 v4 v5 : Fin 6) (t : Nat), t < 3 ∧
            [v0, v1, v2, v3, v4, v5].Nodup ∧ G.Adj v3 v4 ∧
            (G.Adj v3 v5 ↔ 1 ≤ t) ∧ (G.Adj v4 v5 ↔ 2 ≤ t) := by
        intro a b c heq hab hac hbc hAB
        by_cases hAC : G.Adj a c
        · by_cases hBC : G.Adj b c
          · exact ⟨a, b, c, 2, by omega, make_nd a b c heq hab hac hbc, hAB, by simp [hAC], by simp [hBC]⟩
          · exact ⟨a, b, c, 1, by omega, make_nd a b c heq hab hac hbc, hAB, by simp [hAC], by simp [hBC]⟩
        · by_cases hBC : G.Adj b c
          · exact ⟨b, a, c, 1, by omega,
              make_nd b a c (by rw [← heq]; ext x; simp; tauto) hab.symm hbc hac,
              hAB.symm, by simp [hBC], by simp [hAC]⟩
          · exact ⟨a, b, c, 0, by omega, make_nd a b c heq hab hac hbc, hAB, by simp [hAC], by simp [hBC]⟩
      rcases hor with e01 | e02 | e12
      · exact handle_edge w0 w1 w2 hReq.symm hw01 hw02 hw12 e01
      · exact handle_edge w0 w2 w1 (by rw [hReq]; ext x; simp; tauto) hw02 hw01 hw12.symm e02
      · exact handle_edge w1 w2 w0 (by rw [hReq]; ext x; simp; tauto) hw12 hw01.symm hw02.symm e12
    obtain ⟨v3, v4, v5, t, ht, hnd, h34, h35, h45⟩ := hord
    obtain ⟨σ, hs0, hs1, hs2, hs3, hs4, hs5⟩ := exists_perm_of_six v0 v1 v2 v3 v4 v5 hnd
    let G' := comapG G σ
    let bit9 : Fin 3 → Fin 3 → Nat := fun a b =>
      if G'.Adj ⟨a.val, by omega⟩ ⟨b.val + 3, by omega⟩ then 1 <<< (a.val * 3 + b.val) else 0
    let cm : Nat :=
      bit9 0 0 ||| bit9 0 1 ||| bit9 0 2 |||
      bit9 1 0 ||| bit9 1 1 ||| bit9 1 2 |||
      bit9 2 0 ||| bit9 2 1 ||| bit9 2 2
    have hbit9_tb : ∀ (a b c d : Fin 3),
        (bit9 a b).testBit (c.val * 3 + d.val) =
          (decide (a = c ∧ b = d) && decide (G'.Adj ⟨a.val, by omega⟩ ⟨b.val + 3, by omega⟩)) := by
      intro a b c d
      dsimp only [bit9]
      by_cases h : G'.Adj ⟨a.val, by omega⟩ ⟨b.val + 3, by omega⟩
      · rw [if_pos h, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
        have heq : (a.val * 3 + b.val = c.val * 3 + d.val) ↔ (a = c ∧ b = d) := by
          constructor
          · intro e; exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
          · rintro ⟨rfl, rfl⟩; rfl
        by_cases hc' : a = c ∧ b = d
        · rcases hc' with ⟨rfl, rfl⟩; simp [h]
        · have hne : a.val * 3 + b.val ≠ c.val * 3 + d.val := fun e => hc' (heq.1 e)
          simp [h, hc', hne]
      · rw [if_neg h]; simp [h]
    have hcm_bit : ∀ (a b : Fin 3),
        cm.testBit (a.val * 3 + b.val) = decide (G'.Adj ⟨a.val, by omega⟩ ⟨b.val + 3, by omega⟩) := by
      intro a b
      simp only [cm, Nat.testBit_or, hbit9_tb]
      fin_cases a <;> fin_cases b <;> simp
    have hcm_lt : cm < 512 := by
      have hb : ∀ a b : Fin 3, bit9 a b < 2 ^ 9 := fun a b => by
        dsimp only [bit9]
        split_ifs
        · fin_cases a <;> fin_cases b <;> decide
        · omega
      show cm < 2 ^ 9
      dsimp only [cm]
      exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow
        (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow
          (hb 0 0) (hb 0 1)) (hb 0 2)) (hb 1 0)) (hb 1 1)) (hb 1 2)) (hb 2 0)) (hb 2 1)) (hb 2 2)
    have hnorm_lt : ∀ u v : Fin 6, u.val < v.val → (normAdj t cm u.val v.val = true ↔ G'.Adj u v) := by
      intro u v huv
      have h01' : G'.Adj 0 1 := by simp [G', comapG, hs0, hs1, h01]
      have h02' : G'.Adj 0 2 := by simp [G', comapG, hs0, hs2, h02]
      have h12' : G'.Adj 1 2 := by simp [G', comapG, hs1, hs2, h12]
      have h34' : G'.Adj 3 4 := by simp [G', comapG, hs3, hs4, h34]
      have h35' : G'.Adj 3 5 ↔ 1 ≤ t := by simp [G', comapG, hs3, hs5, h35]
      have h45' : G'.Adj 4 5 ↔ 2 ≤ t := by simp [G', comapG, hs4, hs5, h45]
      have hne : (u.val == v.val) = false := by simp [Nat.ne_of_lt huv]
      have hmin : min u.val v.val = u.val := Nat.min_eq_left (Nat.le_of_lt huv)
      have hmax : max u.val v.val = v.val := Nat.max_eq_right (Nat.le_of_lt huv)
      by_cases hv3 : v.val < 3
      · have hu3 : u.val < 3 := by omega
        have htri : normAdj t cm u.val v.val = true := by
          unfold normAdj; simp [hne, hmin, hmax, hu3, hv3]
        simp only [htri, true_iff]
        have hpair : (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 1 ∧ v = 2) := by
          have : (u.val = 0 ∧ v.val = 1) ∨ (u.val = 0 ∧ v.val = 2) ∨ (u.val = 1 ∧ v.val = 2) := by omega
          rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
          · exact Or.inr (Or.inl ⟨Fin.ext h1, Fin.ext h2⟩)
          · exact Or.inr (Or.inr ⟨Fin.ext h1, Fin.ext h2⟩)
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h01'
        · exact h02'
        · exact h12'
      · by_cases hu3 : u.val < 3
        · have hnot34 : ¬ (u.val = 3 ∧ v.val = 4) := by omega
          have hnot35 : ¬ (u.val = 3 ∧ v.val = 5) := by omega
          have hnot45 : ¬ (u.val = 4 ∧ v.val = 5) := by omega
          have hna : normAdj t cm u.val v.val = cm.testBit (u.val * 3 + (v.val - 3)) := by
            unfold normAdj
            simp [hne, hmin, hmax, hv3, hnot34, hnot35, hnot45]
          rw [hna]
          let af : Fin 3 := ⟨u.val, hu3⟩
          let bf : Fin 3 := ⟨v.val - 3, by omega⟩
          have hb := hcm_bit af bf
          have hu_eq : (⟨af.val, by omega⟩ : Fin 6) = u := Fin.ext rfl
          have hv_eq : (⟨bf.val + 3, by omega⟩ : Fin 6) = v := Fin.ext (by dsimp [bf]; omega)
          rw [hu_eq, hv_eq] at hb
          change cm.testBit (af.val * 3 + bf.val) = true ↔ G'.Adj u v
          rw [hb]; simp
        · have hpair : (u = 3 ∧ v = 4) ∨ (u = 3 ∧ v = 5) ∨ (u = 4 ∧ v = 5) := by
            have hvlt := v.isLt
            have : (u.val = 3 ∧ v.val = 4) ∨ (u.val = 3 ∧ v.val = 5) ∨ (u.val = 4 ∧ v.val = 5) := by omega
            rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
            · exact Or.inr (Or.inl ⟨Fin.ext h1, Fin.ext h2⟩)
            · exact Or.inr (Or.inr ⟨Fin.ext h1, Fin.ext h2⟩)
          rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · change normAdj t cm 3 4 = true ↔ G'.Adj 3 4
            rw [normAdj_34]; simp [h34']
          · change normAdj t cm 3 5 = true ↔ G'.Adj 3 5
            rw [normAdj_35]; simp [h35']
          · change normAdj t cm 4 5 = true ↔ G'.Adj 4 5
            rw [normAdj_45]; simp [h45']
    have hnorm : ∀ u v : Fin 6, normAdj t cm u.val v.val = true ↔ G'.Adj u v := by
      intro u v
      rcases lt_trichotomy u.val v.val with hlt | heq | hgt
      · exact hnorm_lt u v hlt
      · have huv : u = v := Fin.ext heq
        subst huv
        simp [normAdj, G'.loopless.irrefl]
      · have hcomm : normAdj t cm u.val v.val = normAdj t cm v.val u.val := by
          unfold normAdj
          have h1 : (u.val == v.val) = false := by simp [Nat.ne_of_gt hgt]
          have h2 : (v.val == u.val) = false := by simp [Nat.ne_of_lt hgt]
          simp [h1, h2, Nat.min_comm, Nat.max_comm]
        rw [hcomm, G'.adj_comm]
        exact hnorm_lt v u hgt
    have hv := verifyEntry_all t ht cm hcm_lt
    unfold verifyEntry at hv
    dsimp only at hv
    set val := fld (tabOf t) 38 cm with hval
    set tag := val &&& 3 with htag
    by_cases ht0 : (tag == 0) = true
    · exfalso
      simp only [ht0, ↓reduceIte] at hv
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hv
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc'⟩, hab⟩, hac⟩, hbc⟩, hna1⟩, hna2⟩, hna3⟩ := hv
      let af : Fin 6 := ⟨(val >>> 2) &&& 7, ha⟩
      let bf : Fin 6 := ⟨(val >>> 5) &&& 7, hb⟩
      let cf : Fin 6 := ⟨(val >>> 8) &&& 7, hc'⟩
      have h1 : ¬ G'.Adj af bf := fun h => by rw [(hnorm af bf).2 h] at hna1; cases hna1
      have h2 : ¬ G'.Adj af cf := fun h => by rw [(hnorm af cf).2 h] at hna2; cases hna2
      have h3 : ¬ G'.Adj bf cf := fun h => by rw [(hnorm bf cf).2 h] at hna3; cases hna3
      exact h3 (hi3 (σ af) (σ bf) (σ cf)
        (fun e => hab (congrArg Fin.val (σ.injective e)))
        (fun e => hac (congrArg Fin.val (σ.injective e)))
        (fun e => hbc (congrArg Fin.val (σ.injective e))) h1 h2)
    · by_cases ht1 : (tag == 1) = true
      · left
        simp only [ht0, ht1, Bool.false_eq_true, ↓reduceIte] at hv
        simp only [okBic, covBic, Bool.and_eq_true, List.all_eq_true, List.mem_range,
          Bool.or_eq_true, Bool.not_eq_true'] at hv
        obtain ⟨⟨⟨hok0, hok1⟩, hok2⟩, hcov⟩ := hv
        apply HasBC_of_comap G σ 3
        let x0 := (val >>> 2) &&& 63
        let y0 := (val >>> 8) &&& 63
        let x1 := (val >>> 14) &&& 63
        let y1 := (val >>> 20) &&& 63
        let x2 := (val >>> 26) &&& 63
        let y2 := (val >>> 32) &&& 63
        refine ⟨fun i => match i.val with | 0 => setOfMask x0 | 1 => setOfMask x1 | _ => setOfMask x2,
                fun i => match i.val with | 0 => setOfMask y0 | 1 => setOfMask y1 | _ => setOfMask y2, ?_, ?_⟩
        · intro i a ha b hb
          fin_cases i
          · change a ∈ setOfMask x0 at ha; change b ∈ setOfMask y0 at hb
            rw [mem_setOfMask] at ha hb
            rcases hok0 a.val a.isLt b.val b.isLt with h | h
            · simp [x0, y0, ha, hb] at h
            · exact (hnorm a b).1 h
          · change a ∈ setOfMask x1 at ha; change b ∈ setOfMask y1 at hb
            rw [mem_setOfMask] at ha hb
            rcases hok1 a.val a.isLt b.val b.isLt with h | h
            · simp [x1, y1, ha, hb] at h
            · exact (hnorm a b).1 h
          · change a ∈ setOfMask x2 at ha; change b ∈ setOfMask y2 at hb
            rw [mem_setOfMask] at ha hb
            rcases hok2 a.val a.isLt b.val b.isLt with h | h
            · simp [x2, y2, ha, hb] at h
            · exact (hnorm a b).1 h
        · intro a b hab
          rcases hcov a.val a.isLt b.val b.isLt with h | h
          · rw [(hnorm a b).2 hab] at h; cases h
          · rcases h with (((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
            · exact ⟨0, Or.inl ⟨(mem_setOfMask x0 a).2 h1, (mem_setOfMask y0 b).2 h2⟩⟩
            · exact ⟨0, Or.inr ⟨(mem_setOfMask x0 b).2 h1, (mem_setOfMask y0 a).2 h2⟩⟩
            · exact ⟨1, Or.inl ⟨(mem_setOfMask x1 a).2 h1, (mem_setOfMask y1 b).2 h2⟩⟩
            · exact ⟨1, Or.inr ⟨(mem_setOfMask x1 b).2 h1, (mem_setOfMask y1 a).2 h2⟩⟩
            · exact ⟨2, Or.inl ⟨(mem_setOfMask x2 a).2 h1, (mem_setOfMask y2 b).2 h2⟩⟩
            · exact ⟨2, Or.inr ⟨(mem_setOfMask x2 b).2 h1, (mem_setOfMask y2 a).2 h2⟩⟩
      · by_cases ht2 : (tag == 2) = true
        · right
          simp only [ht0, ht1, ht2, Bool.false_eq_true, ↓reduceIte] at hv
          simp only [Bool.and_eq_true, decide_eq_true_eq,
            List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hv
          obtain ⟨⟨⟨hci, hplt⟩, hpinj⟩, hpadj⟩ := hv
          let ci := (val >>> 2) &&& 7
          let pf : Fin 6 → Fin 6 := fun j => ⟨(val >>> (5 + 3 * j.val)) &&& 7, hplt j.val j.isLt⟩
          have hp_inj : Function.Injective pf := by
            intro i j hij
            rcases hpinj i.val i.isLt j.val j.isLt with he | hne
            · exact Fin.ext he
            · exact absurd (congrArg Fin.val hij) hne
          let τ : Equiv.Perm (Fin 6) := Equiv.ofBijective pf ((Finite.injective_iff_bijective).1 hp_inj)
          refine ⟨ci, hci, τ.symm.trans σ, ?_⟩
          ext u v
          change G'.Adj (τ.symm u) (τ.symm v) ↔ (canonAdj ci u.val).testBit v.val = true
          rw [← hnorm (τ.symm u) (τ.symm v)]
          have h1 := hpadj (τ.symm u).val (τ.symm u).isLt (τ.symm v).val (τ.symm v).isLt
          have hpu : (val >>> (5 + 3 * (τ.symm u).val)) &&& 7 = u.val := by
            have : τ (τ.symm u) = u := τ.apply_symm_apply u
            exact congrArg Fin.val this
          have hpv : (val >>> (5 + 3 * (τ.symm v).val)) &&& 7 = v.val := by
            have : τ (τ.symm v) = v := τ.apply_symm_apply v
            exact congrArg Fin.val this
          rw [hpu, hpv] at h1
          rw [h1]
        · simp [ht0, ht1, ht2] at hv

theorem main_refutation (G : SimpleGraph (Fin 6)) (C : AndCountCircuit 6)
    (hW : C.WellFormed) (hP : PartialCond G C) :
    ∃ k ≤ C.size, HasBC G k := by
  by_cases hge4 : 4 ≤ C.size
  · obtain ⟨k, hk4, hbc⟩ := bc_le_four_fin6 G
    exact ⟨k, by omega, hbc⟩
  · have hlt4 : C.size < 4 := by omega
    cases hsz : C.size with
    | zero => exact ⟨0, le_rfl, size_zero_ok G C hsz hP⟩
    | succ s1 =>
      cases s1 with
      | zero => exact ⟨1, le_rfl, size_one_ok G C hW hsz hP⟩
      | succ s2 =>
        cases s2 with
        | zero => exact ⟨2, le_rfl, size_two_ok G C hW hsz hP⟩
        | succ s3 =>
          have hs3 : s3 = 0 := by omega
          subst hs3
          rcases classify_fin6 G with hbc3 | ⟨c, hc, σ, hGeq⟩
          · exact ⟨3, le_rfl, hbc3⟩
          · exfalso
            have hP' := comapG_partial G C σ hP
            rw [hGeq] at hP'
            exact no_size_three_canon c hc (comapC C σ) (comapC_wf C σ hW) hsz hP'

end PEqualNP.Outside.L_meta_949_aux

theorem PEqualNP.Outside.L_meta_949 : ¬ (∃ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧ ¬ (∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧ (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)))) := by
  rintro ⟨G, C, hW, hP, hno⟩
  obtain ⟨k, hk, X, Y, hbic, hcov⟩ :=
    PEqualNP.Outside.L_meta_949_aux.main_refutation G C hW (fun I ⟨h1, h2⟩ => hP I h1 h2)
  exact hno ⟨k, X, Y, hk, hbic, hcov⟩
