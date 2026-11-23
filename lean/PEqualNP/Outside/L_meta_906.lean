import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_906_aux

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

theorem gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

theorem gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

def Sep {n : ℕ} (C : AndCountCircuit n) (P : Finset (Fin n) → Prop) : Prop :=
  ∀ I, P I → C.eval I = false ∧ ∀ w, w ∉ I → C.eval (insert w I) = true

def Free {n : ℕ} (C : AndCountCircuit n) (v : Fin n) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => v ∉ C.leftVars i ∧ v ∉ C.rightVars i)

def sideL {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def sideR {n : ℕ} (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

theorem unionSide {n : ℕ} (C : AndCountCircuit n) (U I J B : Finset (Fin n))
    (F : Finset (Fin C.size)) (i : Fin C.size) (hU : U ⊆ I ∪ J)
    (ih : ∀ j < i, C.gateVal U j = true → C.gateVal I j = true ∨ C.gateVal J j = true) :
    sideTrue U B F i (C.gateVal U) = true →
    sideTrue I B F i (C.gateVal I) = true ∨ sideTrue J B F i (C.gateVal J) = true := by
  simp only [sideTrue, decide_eq_true_eq]
  rintro (⟨v, hv, hu⟩ | ⟨j, hj, hji, ht⟩)
  · rcases Finset.mem_union.mp (hU hu) with h | h
    · exact Or.inl (Or.inl ⟨v, hv, h⟩)
    · exact Or.inr (Or.inl ⟨v, hv, h⟩)
  · rcases ih j hji ht with h | h
    · exact Or.inl (Or.inr ⟨j, hj, hji, h⟩)
    · exact Or.inr (Or.inr ⟨j, hj, hji, h⟩)

theorem mergeInput {n : ℕ} (C : AndCountCircuit n) (I J U : Finset (Fin n)) (v : Fin n)
    (hi : v ∈ I) (hj : v ∈ J) (hU : U ⊆ I ∪ J)
    (hs : ∀ i ∈ Free C v, sideL C I i = sideL C J i) :
    C.eval U = true → C.eval I = true ∨ C.eval J = true := by
  have gate (i : Fin C.size) : C.gateVal U i = true →
      C.gateVal I i = true ∨ C.gateVal J i = true := by
    induction i using ((wellFounded_lt :
        WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
    | h i ih =>
      intro ht
      rw [gateVal_unfold, Bool.and_eq_true] at ht
      rw [gateVal_unfold C I, gateVal_unfold C J]
      change (sideL C I i && sideR C I i) = true ∨ (sideL C J i && sideR C J i) = true
      have hl : sideL C I i = true ∨ sideL C J i = true := unionSide C U I J _ _ i hU ih ht.1
      have hr : sideR C I i = true ∨ sideR C J i = true := unionSide C U I J _ _ i hU ih ht.2
      simp only [Bool.and_eq_true]
      by_cases h₁ : v ∈ C.leftVars i
      · have a : sideL C I i = true := decide_eq_true (Or.inl ⟨v, h₁, hi⟩)
        have b : sideL C J i = true := decide_eq_true (Or.inl ⟨v, h₁, hj⟩)
        tauto
      by_cases h₂ : v ∈ C.rightVars i
      · have a : sideR C I i = true := decide_eq_true (Or.inl ⟨v, h₂, hi⟩)
        have b : sideR C J i = true := decide_eq_true (Or.inl ⟨v, h₂, hj⟩)
        tauto
      have hh := hs i (by simp [Free, h₁, h₂])
      rw [hh] at hl ⊢
      tauto
  simp only [eval, decide_eq_true_eq]
  rintro (⟨w, hw, h⟩ | ⟨i, hi', h⟩)
  · rcases Finset.mem_union.mp (hU h) with h | h
    · exact Or.inl (Or.inl ⟨_, hw, h⟩)
    · exact Or.inr (Or.inl ⟨_, hw, h⟩)
  · rcases gate i h with h | h
    · exact Or.inl (Or.inr ⟨i, hi', h⟩)
    · exact Or.inr (Or.inr ⟨i, hi', h⟩)

theorem free_bound {n : ℕ} (C : AndCountCircuit n) (P : Finset (Fin n) → Prop)
    [DecidablePred P] (h : Sep C P) (v : Fin n) :
    (Finset.univ.filter (fun I => P I ∧ v ∈ I)).card ≤ 2 ^ (Free C v).card := by
  classical
  let S := Finset.univ.filter (fun I : Finset (Fin n) => P I ∧ v ∈ I)
  have key : ∀ X Y : Finset (Fin n), P X → P Y → v ∈ X → v ∈ Y →
      (∀ i ∈ Free C v, sideL C X i = sideL C Y i) → ∀ w ∈ X, w ∈ Y := by
    intro X Y hX hY hvX hvY hs w hwX
    by_contra hwY
    have he := mergeInput C X Y (insert w Y) v hvX hvY
      (Finset.insert_subset (Finset.mem_union_left Y hwX) Finset.subset_union_right) hs
      ((h Y hY).2 w hwY)
    simp [(h X hX).1, (h Y hY).1] at he
  let code (A : S) (i : Free C v) : Bool := sideL C A.1 i.1
  have hinj : Function.Injective code := by
    intro A B hab
    obtain ⟨hPA, hvA⟩ := (Finset.mem_filter.mp A.2).2
    obtain ⟨hPB, hvB⟩ := (Finset.mem_filter.mp B.2).2
    have hs : ∀ i ∈ Free C v, sideL C A.1 i = sideL C B.1 i := fun i hi => congrFun hab ⟨i, hi⟩
    apply Subtype.ext
    ext w
    exact ⟨key _ _ hPA hPB hvA hvB hs w, key _ _ hPB hPA hvB hvA (fun i hi => (hs i hi).symm) w⟩
  have hc := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using hc

def MaskLe {n : ℕ} (C : AndCountCircuit n) (v w : Fin n) : Prop :=
  ∀ i, (v ∈ C.leftVars i → w ∈ C.leftVars i) ∧ (v ∈ C.rightVars i → w ∈ C.rightVars i)

theorem bare_out_empty {n : ℕ} (C : AndCountCircuit n) (P : Finset (Fin n) → Prop)
    (h : Sep C P) (v : Fin n) (hv : ∃ I, P I ∧ v ∈ I) : v ∉ C.outVars := by
  intro hvo
  obtain ⟨I, hI, hvI⟩ := hv
  have he := (h I hI).1
  have ht : C.eval I = true := decide_eq_true (Or.inl ⟨v, hvo, hvI⟩)
  simp [he] at ht

theorem sideMasked {n : ℕ} (I : Finset (Fin n)) (v w : Fin n) (hw : w ∈ I) (B : Finset (Fin n))
    (hp : v ∈ B → w ∈ B) {k : ℕ} (F : Finset (Fin k)) (i : Fin k) (vals : Fin k → Bool) :
    sideTrue (insert v I) B F i vals = sideTrue I B F i vals := by
  unfold sideTrue
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨u, hu, hi⟩ | h)
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Or.inl ⟨w, hp hu, hw⟩
      · exact Or.inl ⟨u, hu, hi⟩
    · exact Or.inr h
  · rintro (⟨u, hu, hi⟩ | h)
    · exact Or.inl ⟨u, hu, Finset.mem_insert_of_mem hi⟩
    · exact Or.inr h

theorem sideAvoid {n : ℕ} (I : Finset (Fin n)) (v : Fin n) (B : Finset (Fin n))
    (hv : v ∉ B) {k : ℕ} (F : Finset (Fin k)) (i : Fin k) (vals : Fin k → Bool) :
    sideTrue (insert v I) B F i vals = sideTrue I B F i vals := by
  unfold sideTrue
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨u, hu, hi⟩ | h)
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact absurd hu hv
      · exact Or.inl ⟨u, hu, hi⟩
    · exact Or.inr h
  · rintro (⟨u, hu, hi⟩ | h)
    · exact Or.inl ⟨u, hu, Finset.mem_insert_of_mem hi⟩
    · exact Or.inr h

theorem notMasked {n : ℕ} (C : AndCountCircuit n) (P : Finset (Fin n) → Prop)
    (h : Sep C P) (hin : ∀ u, ∃ I, P I ∧ u ∈ I) {v w : Fin n} (hI : ∃ I, P I ∧ w ∈ I ∧ v ∉ I) :
    ¬ MaskLe C v w := by
  intro hm
  obtain ⟨I, hP, hw, hv⟩ := hI
  have hf (d : ℕ) : C.gateValFuel (insert v I) d = C.gateValFuel I d := by
    induction d with
    | zero => rfl
    | succ d ih =>
      funext i
      simp only [gateValFuel, ih, sideMasked I v w hw _ (hm i).1,
        sideMasked I v w hw _ (hm i).2]
  have a := (h I hP).1
  have b := (h I hP).2 v hv
  rw [eval, decide_eq_true_eq] at b
  rcases b with ⟨u, hu, _⟩ | ⟨i, hi, ht⟩
  · exact bare_out_empty C P h u (hin u) hu
  · rw [gateVal, hf] at ht
    have he : C.eval I = true := decide_eq_true (Or.inr ⟨i, hi, ht⟩)
    simp [a] at he

theorem occupancy {n : ℕ} [Nontrivial (Fin n)] (C : AndCountCircuit n)
    (P : Finset (Fin n) → Prop) (h : Sep C P) (hin : ∀ u, ∃ I, P I ∧ u ∈ I)
    (hpair : ∀ v w : Fin n, v ≠ w → ∃ I, P I ∧ w ∈ I ∧ v ∉ I)
    (hfree : ∀ v, C.size ≤ (Free C v).card + 1) :
    ∃ gate : Fin n → Fin C.size,
      (∀ v i, (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) ↔ i = gate v) ∧
      Function.Injective (fun v => (gate v, decide (v ∈ C.leftVars (gate v)))) := by
  classical
  let occ (v : Fin n) := Finset.univ \ Free C v
  have memOcc (i : Fin C.size) (v : Fin n) : i ∈ occ v ↔ v ∈ C.leftVars i ∨ v ∈ C.rightVars i := by
    simp [occ, Free]
    tauto
  have unique (v : Fin n) {i j : Fin C.size} (hi : i ∈ occ v) (hj : j ∈ occ v) : i = j := by
    have ha := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Free C v))
    have hb := hfree v
    change (occ v).card + _ = _ at ha
    simp only [Finset.card_univ, Fintype.card_fin] at ha
    exact Finset.card_le_one.mp (by omega : (occ v).card ≤ 1) _ hi _ hj
  have occupied (v : Fin n) : ∃ i, i ∈ occ v := by
    by_contra! he
    obtain ⟨w, hw⟩ := exists_ne v
    apply notMasked C P h hin (hpair v w hw.symm)
    intro i
    specialize he i
    rw [memOcc, not_or] at he
    exact ⟨fun hv => (he.1 hv).elim, fun hv => (he.2 hv).elim⟩
  choose gate hg using occupied
  have hgate (v : Fin n) (i : Fin C.size) :
      (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) ↔ i = gate v := by
    rw [← memOcc]
    exact ⟨fun hi => unique v hi (hg v), fun e => e ▸ hg v⟩
  refine ⟨gate, hgate, ?_⟩
  intro a b heq
  by_contra hne
  have he : gate a = gate b := congrArg Prod.fst heq
  have hl : a ∈ C.leftVars (gate a) ↔ b ∈ C.leftVars (gate a) := by
    have hh := congrArg Prod.snd heq
    change decide (_ ∈ _) = decide (_ ∈ _) at hh
    rw [← he] at hh
    exact decide_eq_decide.mp hh
  have other (v : Fin n) {i : Fin C.size} (hi : i ≠ gate v) :
      v ∉ C.leftVars i ∧ v ∉ C.rightVars i := by
    have hh : ¬ (v ∈ C.leftVars i ∨ v ∈ C.rightVars i) := fun hm => hi ((hgate v i).mp hm)
    rwa [not_or] at hh
  have comp {x y : Fin n} (hx : gate x = gate y)
      (hlx : x ∈ C.leftVars (gate x) → y ∈ C.leftVars (gate x))
      (hrx : x ∈ C.rightVars (gate x) → y ∈ C.rightVars (gate x)) : MaskLe C x y := by
    intro i
    by_cases hi : i = gate x
    · simpa [hi] using And.intro hlx hrx
    · exact ⟨fun h' => ((other x hi).1 h').elim, fun h' => ((other x hi).2 h').elim⟩
  by_cases hr : b ∈ C.rightVars (gate a)
  · exact notMasked C P h hin (hpair a b hne) (comp he hl.mp (fun _ => hr))
  · apply notMasked C P h hin (hpair b a (Ne.symm hne))
    apply comp he.symm <;> rw [← he]
    · exact hl.mpr
    · exact fun h' => (hr h').elim

theorem count {n : ℕ} [Nontrivial (Fin n)] (C : AndCountCircuit n)
    (P : Finset (Fin n) → Prop) (h : Sep C P) (hin : ∀ u, ∃ I, P I ∧ u ∈ I)
    (hpair : ∀ v w : Fin n, v ≠ w → ∃ I, P I ∧ w ∈ I ∧ v ∉ I)
    (hfree : ∀ v, C.size ≤ (Free C v).card + 1) : n ≤ 2 * C.size := by
  obtain ⟨gate, -, hinj⟩ := occupancy C P h hin hpair hfree
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool] at hc
  omega

theorem tight {n : ℕ} [Nontrivial (Fin n)] (C : AndCountCircuit n)
    (P : Finset (Fin n) → Prop) (h : Sep C P) (hin : ∀ u, ∃ I, P I ∧ u ∈ I)
    (hpair : ∀ v w : Fin n, v ≠ w → ∃ I, P I ∧ w ∈ I ∧ v ∉ I)
    (havoid : ∀ a b : Fin n, ∃ I, P I ∧ a ∉ I ∧ b ∉ I)
    (hfree : ∀ v, C.size ≤ (Free C v).card + 1) (hcard : n = 2 * C.size) : False := by
  classical
  obtain ⟨gate, hg, hinj⟩ := occupancy C P h hin hpair hfree
  have hbij : Function.Bijective (fun v => (gate v, decide (v ∈ C.leftVars (gate v)))) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, by simp [Fintype.card_prod, hcard, mul_comm]⟩
  have hpos : 0 < C.size := by
    have := Fintype.card_pos (α := Fin n)
    simp only [Fintype.card_fin] at this
    omega
  let g0 : Fin C.size := ⟨0, hpos⟩
  obtain ⟨a, ha⟩ := hbij.2 (g0, true)
  obtain ⟨b, hb⟩ := hbij.2 (g0, false)
  simp only [Prod.mk.injEq] at ha hb
  obtain ⟨hga, hla⟩ := ha
  obtain ⟨hgb, hlb⟩ := hb
  rw [hga, decide_eq_true_eq] at hla
  rw [hgb, decide_eq_false_iff_not] at hlb
  have hab : a ≠ b := by
    rintro rfl
    exact hlb hla
  have hbr : b ∈ C.rightVars g0 := ((hg b g0).mpr hgb.symm).resolve_left hlb
  have harb : a ∉ C.rightVars g0 := by
    intro har
    apply notMasked C P h hin (hpair b a hab.symm)
    intro i
    constructor
    · intro hbl
      have := (hg b i).mp (Or.inl hbl)
      rw [hgb] at this
      subst this
      exact absurd hbl hlb
    · intro hbr'
      have := (hg b i).mp (Or.inr hbr')
      rw [hgb] at this
      subst this
      exact har
  have hright : ∀ u ∈ C.rightVars g0, u = b := by
    intro u hu
    have hgu : g0 = gate u := (hg u g0).mp (Or.inr hu)
    by_cases hul : u ∈ C.leftVars g0
    · have : u = a := hinj (by simp only [← hgu, hga, hul, hla, decide_true])
      exact absurd (this ▸ hu) harb
    · exact hinj (by simp only [← hgu, hgb, hul, hlb, decide_false])
  obtain ⟨I, hP, haI, hbI⟩ := havoid a b
  have hsideF (U : Finset (Fin n)) (hbU : b ∉ U) (vals : Fin C.size → Bool) :
      sideTrue U (C.rightVars g0) (C.rightGates g0) g0 vals = false := by
    unfold sideTrue
    apply decide_eq_false
    rintro (⟨v, hv, hvU⟩ | ⟨j, _, hj, _⟩)
    · exact hbU (hright v hv ▸ hvU)
    · exact absurd hj (by simp [g0, Fin.lt_def])
  have hbU : b ∉ insert a I := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hab.symm, hbI⟩
  have hf (d : ℕ) : C.gateValFuel (insert a I) d = C.gateValFuel I d := by
    induction d with
    | zero => rfl
    | succ d ih =>
      funext i
      simp only [gateValFuel, ih]
      by_cases hi : i = g0
      · rw [hi, hsideF _ hbU, hsideF _ hbI, Bool.and_false, Bool.and_false]
      · have hh : ¬ (a ∈ C.leftVars i ∨ a ∈ C.rightVars i) := fun hm =>
          hi (((hg a i).mp hm).trans hga)
        rw [not_or] at hh
        rw [sideAvoid I a _ hh.1, sideAvoid I a _ hh.2]
  have hout := bare_out_empty C P h a (hin a)
  have heq : C.eval (insert a I) = C.eval I := by
    unfold eval gateVal
    rw [hf]
    apply decide_eq_decide.mpr
    apply or_congr_left
    constructor
    · rintro ⟨x, hx, hx'⟩
      rcases Finset.mem_insert.mp hx' with rfl | hx'
      · exact absurd hx hout
      · exact ⟨x, hx, hx'⟩
    · rintro ⟨x, hx, hx'⟩
      exact ⟨x, hx, Finset.mem_insert_of_mem hx'⟩
  have h1 := (h I hP).1
  have h2 := (h I hP).2 a haI
  rw [heq, h1] at h2
  exact Bool.false_ne_true h2

theorem free_of {n : ℕ} (C : AndCountCircuit n) (P : Finset (Fin n) → Prop) [DecidablePred P]
    (h : Sep C P) (m : ℕ) (hm : C.size ≤ m + 2)
    (hcard : ∀ v, 2 ^ m < (Finset.univ.filter (fun I => P I ∧ v ∈ I)).card) :
    ∀ v, C.size ≤ (Free C v).card + 1 := by
  intro v
  have h1 := free_bound C P h v
  have h2 := lt_of_lt_of_le (hcard v) h1
  have h3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
  omega

def rel {n : ℕ} (L : List (ℕ × ℕ)) (a b : Fin n) : Bool :=
  decide (a ≠ b ∧ (((a : ℕ), (b : ℕ)) ∈ L ∨ ((b : ℕ), (a : ℕ)) ∈ L))

def goodB {n : ℕ} (r : Fin n → Fin n → Bool) (I : Finset (Fin n)) : Bool :=
  decide ((∀ a ∈ I, ∀ c ∈ I, r a c = false) ∧ (∀ w, w ∉ I → ∃ a ∈ I, r a w = true))

theorem rel_adj {n : ℕ} (L : List (ℕ × ℕ)) (a b : Fin n) :
    (SimpleGraph.fromRel (fun a b : Fin n => ((a : ℕ), (b : ℕ)) ∈ L)).Adj a b ↔
      rel L a b = true := by
  simp [SimpleGraph.fromRel_adj, rel]

theorem good_iff {n : ℕ} (L : List (ℕ × ℕ)) (I : Finset (Fin n)) :
    ((∀ a ∈ I, ∀ c ∈ I,
        ¬ (SimpleGraph.fromRel (fun a b : Fin n => ((a : ℕ), (b : ℕ)) ∈ L)).Adj a c) ∧
      (∀ w : Fin n, w ∉ I → ∃ a ∈ I,
        (SimpleGraph.fromRel (fun a b : Fin n => ((a : ℕ), (b : ℕ)) ∈ L)).Adj a w)) ↔
      goodB (rel L) I = true := by
  simp only [goodB, decide_eq_true_eq, rel_adj, Bool.not_eq_true]

theorem part {n : ℕ} (L : List (ℕ × ℕ)) (C₀ : AndCountCircuit n) (s m : ℕ)
    (hwf : C₀.WellFormed) (hs : C₀.size ≤ s) (hsm : s ≤ m + 3)
    (hup : ∀ I, goodB (rel L) I = true →
      C₀.eval I = false ∧ ∀ w, w ∉ I → C₀.eval (insert w I) = true)
    (hcard : ∀ v : Fin n,
      2 ^ m < (Finset.univ.filter (fun I => goodB (rel L) I = true ∧ v ∈ I)).card)
    (hlow : ∀ C : AndCountCircuit n, C.size < s → (∀ v, C.size ≤ (Free C v).card + 1) →
      Sep C (fun I => goodB (rel L) I = true) → False) :
    ∀ G : SimpleGraph (Fin n),
      G = SimpleGraph.fromRel (fun a b : Fin n => ((a : ℕ), (b : ℕ)) ∈ L) →
      (∃ C : AndCountCircuit n, C.WellFormed ∧ C.size ≤ s ∧
        (∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
          (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w) →
          C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true)) ∧
      ∀ C : AndCountCircuit n, C.WellFormed →
        (∀ I : Finset (Fin n), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
          (∀ w : Fin n, w ∉ I → ∃ a ∈ I, G.Adj a w) →
          C.eval I = false ∧ ∀ w : Fin n, w ∉ I → C.eval (insert w I) = true) →
        s ≤ C.size := by
  intro G hG
  subst hG
  refine ⟨⟨C₀, hwf, hs, fun I hi hd => hup I ((good_iff L I).mp ⟨hi, hd⟩)⟩, ?_⟩
  intro C _ hC
  by_contra hlt
  push Not at hlt
  have hsep : Sep C (fun I => goodB (rel L) I = true) := fun I hI => by
    obtain ⟨hi, hd⟩ := (good_iff L I).mpr hI
    exact hC I hi hd
  exact hlow C hlt (free_of C _ hsep m (by omega) hcard) hsep

def L6 : List (ℕ × ℕ) := [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)]

def L5 : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

def L7 : List (ℕ × ℕ) := [(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6),
  (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)]

def circ6 : AndCountCircuit 6 where
  size := 4
  leftVars := ![{0}, {1}, {3}, {4}]
  leftGates _ := ∅
  rightVars := ![{1, 2}, {2}, {4, 5}, {5}]
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

def circ5 : AndCountCircuit 5 where
  size := 3
  leftVars := ![{0}, {2}, {3}]
  leftGates _ := ∅
  rightVars := ![{1, 4}, {1, 3}, {4}]
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

def circ7 : AndCountCircuit 7 where
  size := 3
  leftVars := ![{0, 4}, {0, 1}, {1, 2, 3}]
  leftGates := ![∅, {0}, {1}]
  rightVars := ![{2, 6}, {3, 4, 5}, {5, 6}]
  rightGates := ![∅, ∅, {0}]
  outVars := ∅
  outGates := {1, 2}

theorem wf6 : circ6.WellFormed := by
  unfold AndCountCircuit.WellFormed
  decide +kernel

theorem wf5 : circ5.WellFormed := by
  unfold AndCountCircuit.WellFormed
  decide +kernel

theorem wf7 : circ7.WellFormed := by
  unfold AndCountCircuit.WellFormed
  decide +kernel

theorem up6 : ∀ I : Finset (Fin 6), goodB (rel L6) I = true →
    circ6.eval I = false ∧ ∀ w : Fin 6, w ∉ I → circ6.eval (insert w I) = true := by
  decide +kernel

theorem up5 : ∀ I : Finset (Fin 5), goodB (rel L5) I = true →
    circ5.eval I = false ∧ ∀ w : Fin 5, w ∉ I → circ5.eval (insert w I) = true := by
  decide +kernel

theorem up7 : ∀ I : Finset (Fin 7), goodB (rel L7) I = true →
    circ7.eval I = false ∧ ∀ w : Fin 7, w ∉ I → circ7.eval (insert w I) = true := by
  decide +kernel

theorem in6 : ∀ u : Fin 6, ∃ I, goodB (rel L6) I = true ∧ u ∈ I := by decide +kernel

theorem in5 : ∀ u : Fin 5, ∃ I, goodB (rel L5) I = true ∧ u ∈ I := by decide +kernel

theorem in7 : ∀ u : Fin 7, ∃ I, goodB (rel L7) I = true ∧ u ∈ I := by decide +kernel

theorem pair6 : ∀ v w : Fin 6, v ≠ w → ∃ I, goodB (rel L6) I = true ∧ w ∈ I ∧ v ∉ I := by
  decide +kernel

theorem pair5 : ∀ v w : Fin 5, v ≠ w → ∃ I, goodB (rel L5) I = true ∧ w ∈ I ∧ v ∉ I := by
  decide +kernel

theorem pair7 : ∀ v w : Fin 7, v ≠ w → ∃ I, goodB (rel L7) I = true ∧ w ∈ I ∧ v ∉ I := by
  decide +kernel

theorem avoid6 : ∀ a b : Fin 6, ∃ I, goodB (rel L6) I = true ∧ a ∉ I ∧ b ∉ I := by
  decide +kernel

theorem card6 : ∀ v : Fin 6,
    2 ^ 1 < (Finset.univ.filter (fun I => goodB (rel L6) I = true ∧ v ∈ I)).card := by
  decide +kernel

theorem card5 : ∀ v : Fin 5,
    2 ^ 0 < (Finset.univ.filter (fun I => goodB (rel L5) I = true ∧ v ∈ I)).card := by
  decide +kernel

theorem card7 : ∀ v : Fin 7,
    2 ^ 0 < (Finset.univ.filter (fun I => goodB (rel L7) I = true ∧ v ∈ I)).card := by
  decide +kernel

end PEqualNP.Outside.L_meta_906_aux

open PEqualNP.Outside.L_meta_906_aux in
theorem PEqualNP.Outside.L_meta_906 : (∀ G : SimpleGraph (Fin 6), G = SimpleGraph.fromRel (fun a b : Fin 6 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 6, C.WellFormed ∧ C.size ≤ 4 ∧
    (∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 6, C.WellFormed →
    (∀ I : Finset (Fin 6), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 6, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 6, w ∉ I → C.eval (insert w I) = true) →
    4 ≤ C.size) ∧
(∀ G : SimpleGraph (Fin 5), G = SimpleGraph.fromRel (fun a b : Fin 5 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 5, C.WellFormed →
    (∀ I : Finset (Fin 5), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 5, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 5, w ∉ I → C.eval (insert w I) = true) →
    3 ≤ C.size) ∧
(∀ G : SimpleGraph (Fin 7), G = SimpleGraph.fromRel (fun a b : Fin 7 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 2), (0, 3), (1, 3), (1, 4), (2, 4), (2, 5), (3, 5), (3, 6), (4, 6), (4, 0), (5, 0), (5, 1), (6, 1), (6, 2)] : List (ℕ × ℕ))) →
  (∃ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed ∧ C.size ≤ 3 ∧
    (∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true)) ∧
  ∀ C : PEqualNP.AndCount.AndCountCircuit 7, C.WellFormed →
    (∀ I : Finset (Fin 7), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 7, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 7, w ∉ I → C.eval (insert w I) = true) →
    3 ≤ C.size) := by
  refine ⟨part L6 circ6 4 1 wf6 le_rfl (by norm_num) up6 card6 ?_,
    part L5 circ5 3 0 wf5 le_rfl (by norm_num) up5 card5 ?_,
    part L7 circ7 3 0 wf7 le_rfl (by norm_num) up7 card7 ?_⟩
  · intro C hlt hfree hsep
    have hc := count C _ hsep in6 pair6 hfree
    exact tight C _ hsep in6 pair6 avoid6 hfree (by omega)
  · intro C hlt hfree hsep
    have hc := count C _ hsep in5 pair5 hfree
    omega
  · intro C hlt hfree hsep
    have hc := count C _ hsep in7 pair7 hfree
    omega
