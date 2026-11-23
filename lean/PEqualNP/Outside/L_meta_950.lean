import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_950

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

def isIndep {n : Nat} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w

def isMIS {n : Nat} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  isIndep G I ∧ ∀ u : Fin n, u ∉ I → ∃ v ∈ I, G.Adj u v

def Fits {n : Nat} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n) : Prop :=
  ∀ I : Finset (Fin n), isMIS G I → C.eval I = false ∧ ∀ u : Fin n, u ∉ I → C.eval (insert u I) = true

def Cover {n : Nat} (G : SimpleGraph (Fin n)) (k : Nat) (X Y : Fin k → Finset (Fin n)) : Prop :=
  (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧
  (∀ a b : Fin n, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i))

lemma sg_symm {n : Nat} (G : SimpleGraph (Fin n)) {a b : Fin n} (h : G.Adj a b) : G.Adj b a :=
  G.adj_symm h

lemma sg_irrefl {n : Nat} (G : SimpleGraph (Fin n)) (a : Fin n) : ¬ G.Adj a a :=
  fun h => G.loopless.irrefl a h

lemma isIndep_pair {n : Nat} (G : SimpleGraph (Fin n)) (a b : Fin n) (h : ¬ G.Adj a b) :
    isIndep G {a, b} := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact sg_irrefl G _ hxy
  · exact h hxy
  · exact h (sg_symm G hxy)
  · exact sg_irrefl G _ hxy

lemma isIndep_triple {n : Nat} (G : SimpleGraph (Fin n)) (a b c : Fin n)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c) (hbc : ¬ G.Adj b c) :
    isIndep G {a, b, c} := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals
    first
    | exact sg_irrefl G _ hxy
    | exact hab hxy | exact hab (sg_symm G hxy)
    | exact hac hxy | exact hac (sg_symm G hxy)
    | exact hbc hxy | exact hbc (sg_symm G hxy)

lemma isIndep_quad {n : Nat} (G : SimpleGraph (Fin n)) (a b c d : Fin n)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d)
    (hbc : ¬ G.Adj b c) (hbd : ¬ G.Adj b d) (hcd : ¬ G.Adj c d) :
    isIndep G {a, b, c, d} := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl
  all_goals
    first
    | exact sg_irrefl G _ hxy
    | exact hab hxy | exact hab (sg_symm G hxy)
    | exact hac hxy | exact hac (sg_symm G hxy)
    | exact had hxy | exact had (sg_symm G hxy)
    | exact hbc hxy | exact hbc (sg_symm G hxy)
    | exact hbd hxy | exact hbd (sg_symm G hxy)
    | exact hcd hxy | exact hcd (sg_symm G hxy)

lemma finset_enum {α : Type} [DecidableEq α] :
    ∀ S : Finset α, ∃ f : Fin S.card → α, ∀ x, x ∈ S ↔ ∃ i, f i = x := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.card_empty]
    exact ⟨fun i => Fin.elim0 i, fun x => Iff.intro (fun h => by cases h) (fun ⟨i, _⟩ => Fin.elim0 i)⟩
  | insert a s ha ih =>
    obtain ⟨f, hf⟩ := ih
    rw [Finset.card_insert_of_notMem ha]
    refine ⟨fun i => if h0 : i.val = 0 then a else f ⟨i.val - 1, by omega⟩, fun x => ?_⟩
    constructor
    · intro hx
      rcases Finset.mem_insert.1 hx with rfl | hxs
      · exact ⟨⟨0, by omega⟩, by simp⟩
      · obtain ⟨i, hi⟩ := (hf x).1 hxs
        exact ⟨⟨i.val + 1, by omega⟩, by simp [hi]⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      by_cases h0 : i = 0
      · subst h0; exact Finset.mem_insert_self a s
      · dsimp only
        split
        · contradiction
        · exact Finset.mem_insert_of_mem ((hf _).2 ⟨⟨i - 1, by omega⟩, rfl⟩)

lemma sideTrue_congr {n k : Nat} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (h : ∀ j, j < i → v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  congr 1
  apply propext
  constructor
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [← h j hji]; exact hv⟩
  · rintro (h1 | ⟨j, hj, hji, hv⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨j, hj, hji, by rw [h j hji]; exact hv⟩

lemma sideTrue_iff {n k : Nat} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

lemma sideTrue_mono {n k : Nat} (U U' B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (hU : U ⊆ U') (h : ∀ j, j < i → v j = true → w j = true)
    (hs : sideTrue U B F i v = true) : sideTrue U' B F i w = true := by
  rw [sideTrue_iff] at hs ⊢
  rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
  · exact Or.inl ⟨x, hx, hU hxU⟩
  · exact Or.inr ⟨j, hj, hji, h j hji hv⟩

lemma fuel_succ {n : Nat} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : Nat, ∀ i : Fin C.size, i.val < d →
      gateValFuel C U (d + 1) i = gateValFuel C U d i := by
  intro d
  induction d with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ d ih =>
    intro i hi
    show (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U (d + 1)) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U (d + 1))) =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d))
    have hc : ∀ j : Fin C.size, j < i → gateValFuel C U (d + 1) j = gateValFuel C U d j := by
      intro j hji
      apply ih
      have : j.val < i.val := hji
      omega
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hc,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hc]

lemma gateVal_rec {n : Nat} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h := fuel_succ C U C.size i i.isLt
  exact h.symm

lemma eval_iff {n : Nat} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = true ↔
      ((∃ v ∈ C.outVars, v ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := by
  unfold AndCountCircuit.eval
  exact decide_eq_true_iff

lemma fuel_mono {n : Nat} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U') :
    ∀ d : Nat, ∀ i : Fin C.size, gateValFuel C U d i = true → gateValFuel C U' d i = true := by
  intro d
  induction d with
  | zero => intro i h; exact absurd h (by simp [gateValFuel])
  | succ d ih =>
    intro i h
    have h' : (sideTrue U (C.leftVars i) (C.leftGates i) i (gateValFuel C U d) &&
        sideTrue U (C.rightVars i) (C.rightGates i) i (gateValFuel C U d)) = true := h
    show (sideTrue U' (C.leftVars i) (C.leftGates i) i (gateValFuel C U' d) &&
        sideTrue U' (C.rightVars i) (C.rightGates i) i (gateValFuel C U' d)) = true
    rw [Bool.and_eq_true] at h' ⊢
    exact ⟨sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) h'.1,
      sideTrue_mono U U' _ _ i _ _ hU (fun j _ => ih j) h'.2⟩

lemma gateVal_mono {n : Nat} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
    (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal U' i = true :=
  fuel_mono C U U' hU C.size i h

lemma eval_mono {n : Nat} (C : AndCountCircuit n) (U U' : Finset (Fin n)) (hU : U ⊆ U')
    (h : C.eval U = true) : C.eval U' = true := by
  rw [eval_iff] at h ⊢
  rcases h with ⟨v, hv, hvU⟩ | ⟨j, hj, hg⟩
  · exact Or.inl ⟨v, hv, hU hvU⟩
  · exact Or.inr ⟨j, hj, gateVal_mono C U U' hU j hg⟩

def singSet {n : Nat} (C : AndCountCircuit n) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => C.gateVal {v} i = true)

lemma mem_singSet {n : Nat} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ singSet C i ↔ C.gateVal {v} i = true := by
  unfold singSet
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

def stripCircuit {n : Nat} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  leftGates := C.leftGates
  rightVars i := (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  rightGates := C.rightGates
  outVars := C.outVars ∪ C.outGates.biUnion (singSet C)
  outGates := C.outGates

lemma mem_strip_leftVars {n : Nat} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).leftVars i ↔
      (v ∈ C.leftVars i ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

lemma mem_strip_rightVars {n : Nat} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).rightVars i ↔
      (v ∈ C.rightVars i ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

lemma mem_strip_outVars {n : Nat} (C : AndCountCircuit n) (v : Fin n) :
    v ∈ (stripCircuit C).outVars ↔
      v ∈ C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal {v} j = true := by
  change v ∈ C.outVars ∪ C.outGates.biUnion (singSet C) ↔ _
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_singSet]

lemma strip_singleton_false {n : Nat} (C : AndCountCircuit n) (v : Fin n) :
    ∀ (m : Nat) (i : Fin C.size), i.val < m → (stripCircuit C).gateVal {v} i = false := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    cases h : (stripCircuit C).gateVal {v} i
    · rfl
    · exfalso
      rw [gateVal_rec (stripCircuit C) {v} i, Bool.and_eq_true] at h
      have hL := h.1
      have hR := h.2
      unfold sideTrue at hL hR
      rw [decide_eq_true_eq] at hL hR
      have hvL : v ∈ (stripCircuit C).leftVars i := by
        rcases hL with ⟨w, hwB, hwv⟩ | ⟨j, _, hji, hjv⟩
        · rw [Finset.mem_singleton] at hwv
          rwa [← hwv]
        · rw [ih j (by have : j.val < i.val := hji; omega)] at hjv
          exact absurd hjv Bool.false_ne_true
      have hvR : v ∈ (stripCircuit C).rightVars i := by
        rcases hR with ⟨w, hwB, hwv⟩ | ⟨j, _, hji, hjv⟩
        · rw [Finset.mem_singleton] at hwv
          rwa [← hwv]
        · rw [ih j (by have : j.val < i.val := hji; omega)] at hjv
          exact absurd hjv Bool.false_ne_true
      rw [mem_strip_leftVars] at hvL
      rw [mem_strip_rightVars] at hvR
      apply hvL.2
      rw [gateVal_rec C {v} i, Bool.and_eq_true]
      constructor
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hvL.1 with hvB | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hvR.1 with hvB | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩

lemma strip_disjoint {n : Nat} (C : AndCountCircuit n) (i : Fin C.size) :
    Disjoint ((stripCircuit C).leftVars i) ((stripCircuit C).rightVars i) := by
  rw [Finset.disjoint_left]
  intro v hvL hvR
  have hf := strip_singleton_false C v C.size i i.isLt
  have ht : (stripCircuit C).gateVal {v} i = true := by
    rw [gateVal_rec (stripCircuit C) {v} i, Bool.and_eq_true]
    constructor
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvL, Finset.mem_singleton_self v⟩
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvR, Finset.mem_singleton_self v⟩
  rw [hf] at ht
  exact Bool.false_ne_true ht

lemma strip_gateVal_le {n : Nat} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : Nat) (i : Fin C.size), i.val < m →
      (stripCircuit C).gateVal U i = true → C.gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    rw [gateVal_rec (stripCircuit C) U i, Bool.and_eq_true] at hval
    rw [gateVal_rec C U i, Bool.and_eq_true]
    constructor
    · have hL := hval.1
      unfold sideTrue at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_leftVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono C {v} U (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by have : j.val < i.val := hji; omega) hjv⟩
    · have hR := hval.2
      unfold sideTrue at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_rightVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono C {v} U (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by have : j.val < i.val := hji; omega) hjv⟩

lemma strip_gateVal_ge {n : Nat} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : Nat) (i : Fin C.size), i.val < m →
      C.gateVal U i = true →
        (∃ v ∈ U, C.gateVal {v} i = true) ∨ (stripCircuit C).gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    by_cases hsing : ∃ v ∈ U, C.gateVal {v} i = true
    · exact Or.inl hsing
    · right
      have hno : ∀ v ∈ U, C.gateVal {v} i ≠ true := fun v hvU hv => hsing ⟨v, hvU, hv⟩
      rw [gateVal_rec C U i, Bool.and_eq_true] at hval
      rw [gateVal_rec (stripCircuit C) U i, Bool.and_eq_true]
      constructor
      · have hL := hval.1
        unfold sideTrue at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by have : j.val < i.val := hji; omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩
      · have hR := hval.2
        unfold sideTrue at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by have : j.val < i.val := hji; omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩

lemma strip_eval_eq {n : Nat} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    (stripCircuit C).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · rw [mem_strip_outVars] at hvO
      rcases hvO with hvC | ⟨j, hjO, hvs⟩
      · exact Or.inl ⟨v, hvC, hvU⟩
      · exact Or.inr ⟨j, hjO, gateVal_mono C {v} U (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
    · exact Or.inr ⟨j, hjO, strip_gateVal_le C U C.size j j.isLt hjv⟩
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inl hvO), hvU⟩
    · rcases strip_gateVal_ge C U C.size j j.isLt hjv with ⟨v, hvU, hvs⟩ | hj'
      · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inr ⟨j, hjO, hvs⟩), hvU⟩
      · exact Or.inr ⟨j, hjO, hj'⟩

lemma exists_mis_superset {n : Nat} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : isIndep G S) : ∃ I : Finset (Fin n), S ⊆ I ∧ isMIS G I := by
  have key : ∀ d : Nat, ∀ T : Finset (Fin n), n - T.card ≤ d → isIndep G T →
      ∃ I : Finset (Fin n), T ⊆ I ∧ isMIS G I := by
    intro d
    induction d with
    | zero =>
      intro T hd hT
      refine ⟨T, Finset.Subset.rfl, hT, fun u hu => ?_⟩
      exfalso
      have hcard : (insert u T).card ≤ n := by
        have := Finset.card_le_univ (insert u T)
        simpa [Fintype.card_fin] using this
      rw [Finset.card_insert_of_notMem hu] at hcard
      omega
    | succ d ih =>
      intro T hd hT
      by_cases hmax : ∀ u : Fin n, u ∉ T → ∃ v ∈ T, G.Adj u v
      · exact ⟨T, Finset.Subset.rfl, hT, hmax⟩
      · push_neg at hmax
        rcases hmax with ⟨u, huT, hno⟩
        have hT' : isIndep G (insert u T) := by
          intro a ha b hb
          rcases Finset.mem_insert.mp ha with rfl | haT
          · rcases Finset.mem_insert.mp hb with rfl | hbT
            · exact sg_irrefl G _
            · exact hno b hbT
          · rcases Finset.mem_insert.mp hb with rfl | hbT
            · exact fun h => hno a haT (sg_symm G h)
            · exact hT a haT b hbT
        have hsub : n - (insert u T).card ≤ d := by
          rw [Finset.card_insert_of_notMem huT]
          omega
        obtain ⟨I, hsubI, hMIS⟩ := ih (insert u T) hsub hT'
        exact ⟨I, Finset.Subset.trans (Finset.subset_insert u T) hsubI, hMIS⟩
  exact key (n - S.card) S le_rfl hS

lemma outVars_empty {n : Nat} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hfit : Fits G C) : C.outVars = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro v hv
  have hind : isIndep G {v} := by
    intro a ha b hb
    rw [Finset.mem_singleton] at ha hb
    subst ha hb
    exact sg_irrefl G _
  obtain ⟨I, hsub, hMIS⟩ := exists_mis_superset G {v} hind
  have hvI : v ∈ I := hsub (Finset.mem_singleton_self v)
  have hev : C.eval I = true := (eval_iff C I).2 (Or.inl ⟨v, hv, hvI⟩)
  rw [(hfit I hMIS).1] at hev
  exact Bool.noConfusion hev

def sideVars {n : Nat} (C : AndCountCircuit n) (i : Fin C.size) (s : Bool) : Finset (Fin n) :=
  cond s (C.rightVars i) (C.leftVars i)

def sideGates {n : Nat} (C : AndCountCircuit n) (i : Fin C.size) (s : Bool) : Finset (Fin C.size) :=
  cond s (C.rightGates i) (C.leftGates i)

def sv {n : Nat} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) (s : Bool) : Bool :=
  sideTrue X (sideVars C i s) (sideGates C i s) i (C.gateVal X)

lemma gate_false_iff {n : Nat} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal X i = false ↔ (sv C X i false = false ∨ sv C X i true = false) := by
  rw [gateVal_rec, Bool.and_eq_false_iff]
  rfl

lemma sv_hit_mem {n : Nat} (C : AndCountCircuit n) (X : Finset (Fin n)) (i : Fin C.size)
    (s : Bool) {v : Fin n} (hvB : v ∈ sideVars C i s) (hvX : v ∈ X) :
    sv C X i s = true :=
  (sideTrue_iff _ _ _ _ _).2 (Or.inl ⟨v, hvB, hvX⟩)

lemma sv_merge_gen {n : Nat} (C : AndCountCircuit n) (X Y : Finset (Fin n)) (i : Fin C.size)
    (s : Bool) (hX : sv C X i s = false) (hY : sv C Y i s = false)
    (ih : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
      C.gateVal (X ∪ Y) j = false) : sv C (X ∪ Y) i s = false := by
  rw [← Bool.not_eq_true] at hX hY ⊢
  unfold sv at hX hY ⊢
  rw [sideTrue_iff] at hX hY ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩)
  · rcases Finset.mem_union.1 hxU with h | h
    · exact hX (Or.inl ⟨x, hx, h⟩)
    · exact hY (Or.inl ⟨x, hx, h⟩)
  · have h1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => hX (Or.inr ⟨j, hj, hji, hh⟩)
    have h2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => hY (Or.inr ⟨j, hj, hji, hh⟩)
    rw [ih j hji h1 h2] at hv
    exact Bool.noConfusion hv

lemma merge_gate_gen {n : Nat} (C : AndCountCircuit n) (X Y : Finset (Fin n))
    (c : Fin C.size → Bool)
    (hcX : ∀ i : Fin C.size, C.gateVal X i = false → sv C X i (c i) = false)
    (hcY : ∀ i : Fin C.size, C.gateVal Y i = false → sv C Y i (c i) = false) :
    ∀ i : Fin C.size, C.gateVal X i = false → C.gateVal Y i = false →
      C.gateVal (X ∪ Y) i = false := by
  have key : ∀ m : Nat, ∀ i : Fin C.size, i.val < m → C.gateVal X i = false →
      C.gateVal Y i = false → C.gateVal (X ∪ Y) i = false := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ m ih =>
      intro i hi h1 h2
      have ih' : ∀ j : Fin C.size, j < i → C.gateVal X j = false → C.gateVal Y j = false →
          C.gateVal (X ∪ Y) j = false := by
        intro j hji
        exact ih j (by have : j.val < i.val := hji; omega)
      have hm := sv_merge_gen C X Y i (c i) (hcX i h1) (hcY i h2) ih'
      rw [gate_false_iff]
      cases hci : c i
      · rw [hci] at hm; exact Or.inl hm
      · rw [hci] at hm; exact Or.inr hm
  intro i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

lemma merge_eval_gen {n : Nat} (C : AndCountCircuit n) (X Y : Finset (Fin n))
    (c : Fin C.size → Bool)
    (hcX : ∀ i : Fin C.size, C.gateVal X i = false → sv C X i (c i) = false)
    (hcY : ∀ i : Fin C.size, C.gateVal Y i = false → sv C Y i (c i) = false)
    (h1 : C.eval X = false) (h2 : C.eval Y = false) : C.eval (X ∪ Y) = false := by
  rw [← Bool.not_eq_true, eval_iff] at h1 h2 ⊢
  rintro (⟨x, hx, hxU⟩ | ⟨j, hj, hv⟩)
  · rcases Finset.mem_union.1 hxU with h | h
    · exact h1 (Or.inl ⟨x, hx, h⟩)
    · exact h2 (Or.inl ⟨x, hx, h⟩)
  · have g1 : C.gateVal X j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => h1 (Or.inr ⟨j, hj, hh⟩)
    have g2 : C.gateVal Y j = false := by
      rw [← Bool.not_eq_true]
      exact fun hh => h2 (Or.inr ⟨j, hj, hh⟩)
    rw [merge_gate_gen C X Y c hcX hcY j g1 g2] at hv
    exact Bool.noConfusion hv

lemma eval_union_mis_true {n m : Nat} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hfit : Fits G C) (M : Fin m → Finset (Fin n))
    (hMIS : ∀ a : Fin m, isMIS G (M a)) (hInj : ∀ a b : Fin m, a ≠ b → M a ≠ M b) :
    ∀ a b : Fin m, a ≠ b → C.eval (M a ∪ M b) = true := by
  intro a b hne
  have hnot : ¬ (M b ⊆ M a) := by
    intro hsub
    apply hInj a b hne
    ext v
    constructor
    · intro hva
      by_contra hvb
      obtain ⟨w, hwb, hadj⟩ := (hMIS b).2 v hvb
      exact (hMIS a).1 v hva w (hsub hwb) hadj
    · intro hvb
      exact hsub hvb
  rw [Finset.not_subset] at hnot
  obtain ⟨v, hvMb, hvMa⟩ := hnot
  exact eval_mono C (insert v (M a)) (M a ∪ M b)
    (Finset.insert_subset (Finset.mem_union_right _ hvMb) Finset.subset_union_left)
    ((hfit (M a) (hMIS a)).2 v hvMa)

lemma code_card_bound {n m : Nat} (C : AndCountCircuit n)
    (M : Fin m → Finset (Fin n)) (F : Finset (Fin C.size))
    (c : Fin m → Fin C.size → Bool)
    (h0 : ∀ a : Fin m, C.eval (M a) = false)
    (h1 : ∀ a b : Fin m, a ≠ b → C.eval (M a ∪ M b) = true)
    (hcOk : ∀ (a : Fin m) (i : Fin C.size), C.gateVal (M a) i = false → sv C (M a) i (c a i) = false)
    (hcConst : ∀ (a b : Fin m) (i : Fin C.size), i ∉ F → c a i = c b i) :
    m ≤ 2 ^ F.card := by
  let f : Fin m → ({i : Fin C.size // i ∈ F} → Bool) := fun a i => c a i.1
  have hf : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hc : ∀ i, c a i = c b i := by
      intro i
      by_cases hi : i ∈ F
      · exact congrFun hab ⟨i, hi⟩
      · exact hcConst a b i hi
    have hfalse := merge_eval_gen C (M a) (M b) (c a) (hcOk a)
      (fun i hi => by rw [hc i]; exact hcOk b i hi) (h0 a) (h0 b)
    rw [h1 a b hne] at hfalse
    exact Bool.noConfusion hfalse
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype] at hcard
  have hfeq : (Finset.univ.filter (fun i : Fin C.size => i ∈ F)).card = F.card := by
    congr 1
    ext i
    simp
  rwa [hfeq] at hcard

lemma family_bound {n m : Nat} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hfit : Fits G C) (M : Fin m → Finset (Fin n))
    (hMIS : ∀ a : Fin m, isMIS G (M a)) (hInj : ∀ a b : Fin m, a ≠ b → M a ≠ M b) :
    m ≤ 2 ^ C.size := by
  let c : Fin m → Fin C.size → Bool := fun a i => if sv C (M a) i false = false then false else true
  have hc := code_card_bound C M Finset.univ c (fun a => (hfit (M a) (hMIS a)).1)
    (eval_union_mis_true G C hfit M hMIS hInj)
    (fun a i hgi => by
      by_cases hs : sv C (M a) i false = false
      · simpa [c, hs] using hs
      · have hgt := (gate_false_iff C (M a) i).1 hgi
        rcases hgt with hl | hr
        · exact absurd hl hs
        · simpa [c, hs] using hr)
    (fun a b i hi => absurd (Finset.mem_univ i) hi)
  simpa [Finset.card_univ, Fintype.card_fin] using hc

def vCode {n : Nat} (C : AndCountCircuit n) (u : Fin n) (X : Finset (Fin n)) (i : Fin C.size) : Bool :=
  if u ∈ C.leftVars i then true
  else if u ∈ C.rightVars i then false
  else sv C X i false

lemma vCode_ok {n : Nat} (C : AndCountCircuit n) (u : Fin n) (X : Finset (Fin n)) (hu : u ∈ X)
    (i : Fin C.size) (h : C.gateVal X i = false) : sv C X i (vCode C u X i) = false := by
  rw [gate_false_iff] at h
  unfold vCode
  by_cases hl : u ∈ C.leftVars i
  · rw [if_pos hl]
    have hhit : sv C X i false = true := sv_hit_mem C X i false hl hu
    rcases h with h | h
    · rw [hhit] at h; exact Bool.noConfusion h
    · exact h
  · rw [if_neg hl]
    by_cases hr : u ∈ C.rightVars i
    · rw [if_pos hr]
      have hhit : sv C X i true = true := sv_hit_mem C X i true hr hu
      rcases h with h | h
      · exact h
      · rw [hhit] at h; exact Bool.noConfusion h
    · rw [if_neg hr]
      cases hb : sv C X i false with
      | false => exact hb
      | true =>
        rcases h with h | h
        · rw [hb] at h; exact Bool.noConfusion h
        · exact h

lemma vertex_proj_bound {n m : Nat} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hfit : Fits G C) (u : Fin n) (M : Fin m → Finset (Fin n))
    (hMIS : ∀ a : Fin m, isMIS G (M a)) (hInj : ∀ a b : Fin m, a ≠ b → M a ≠ M b)
    (huM : ∀ a : Fin m, u ∈ M a) :
    m ≤ 2 ^ (Finset.univ.filter (fun i : Fin C.size => u ∉ C.leftVars i ∧ u ∉ C.rightVars i)).card := by
  let F := Finset.univ.filter (fun i : Fin C.size => u ∉ C.leftVars i ∧ u ∉ C.rightVars i)
  apply code_card_bound C M F (fun a i => vCode C u (M a) i)
    (fun a => (hfit (M a) (hMIS a)).1)
    (eval_union_mis_true G C hfit M hMIS hInj)
    (fun a i hgi => vCode_ok C u (M a) (huM a) i hgi)
  intro a b i hiF
  have hhit : ¬ (u ∉ C.leftVars i ∧ u ∉ C.rightVars i) := fun hno =>
    hiF (Finset.mem_filter.2 ⟨Finset.mem_univ i, hno⟩)
  unfold vCode
  by_cases hl : u ∈ C.leftVars i
  · rw [if_pos hl, if_pos hl]
  · rw [if_neg hl, if_neg hl]
    by_cases hr : u ∈ C.rightVars i
    · rw [if_pos hr, if_pos hr]
    · exact absurd ⟨hl, hr⟩ hhit

lemma gateVal_eq_of_notMem {n : Nat} (C : AndCountCircuit n) (I : Finset (Fin n)) (u : Fin n)
    (hno : ∀ i : Fin C.size, u ∉ C.leftVars i ∧ u ∉ C.rightVars i) :
    ∀ (m : Nat) (i : Fin C.size), i.val < m → C.gateVal (insert u I) i = C.gateVal I i := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    rw [gateVal_rec C (insert u I) i, gateVal_rec C I i]
    have hc : ∀ j : Fin C.size, j < i → C.gateVal (insert u I) j = C.gateVal I j := by
      intro j hji; exact ih j (by have : j.val < i.val := hji; omega)
    have hL : sideTrue (insert u I) (C.leftVars i) (C.leftGates i) i (C.gateVal (insert u I)) =
        sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I) := by
      unfold sideTrue
      congr 1
      apply propext
      constructor
      · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩)
        · rcases Finset.mem_insert.mp hvU with rfl | hvI
          · exact absurd hvB (hno i).1
          · exact Or.inl ⟨v, hvB, hvI⟩
        · rw [hc j hji] at hjv
          exact Or.inr ⟨j, hjF, hji, hjv⟩
      · rintro (⟨v, hvB, hvI⟩ | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl ⟨v, hvB, Finset.mem_insert_of_mem hvI⟩
        · rw [← hc j hji] at hjv
          exact Or.inr ⟨j, hjF, hji, hjv⟩
    have hR : sideTrue (insert u I) (C.rightVars i) (C.rightGates i) i (C.gateVal (insert u I)) =
        sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I) := by
      unfold sideTrue
      congr 1
      apply propext
      constructor
      · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩)
        · rcases Finset.mem_insert.mp hvU with rfl | hvI
          · exact absurd hvB (hno i).2
          · exact Or.inl ⟨v, hvB, hvI⟩
        · rw [hc j hji] at hjv
          exact Or.inr ⟨j, hjF, hji, hjv⟩
      · rintro (⟨v, hvB, hvI⟩ | ⟨j, hjF, hji, hjv⟩)
        · exact Or.inl ⟨v, hvB, Finset.mem_insert_of_mem hvI⟩
        · rw [← hc j hji] at hjv
          exact Or.inr ⟨j, hjF, hji, hjv⟩
    rw [hL, hR]

lemma noniso_hits_gate {n : Nat} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hfit : Fits G C) (hout : C.outVars = ∅) {u w : Fin n} (hadj : G.Adj u w) :
    ∃ g : Fin C.size, u ∈ C.leftVars g ∨ u ∈ C.rightVars g := by
  by_contra hno
  push_neg at hno
  have hind : isIndep G {w} := by
    intro a ha b hb
    rw [Finset.mem_singleton] at ha hb
    subst ha hb
    exact sg_irrefl G _
  obtain ⟨I, hsub, hMIS⟩ := exists_mis_superset G {w} hind
  have hwI : w ∈ I := hsub (Finset.mem_singleton_self w)
  have huI : u ∉ I := fun hu => hMIS.1 u hu w hwI hadj
  have ht := (hfit I hMIS).2 u huI
  have hf := (hfit I hMIS).1
  have heq : C.eval (insert u I) = C.eval I := by
    unfold AndCountCircuit.eval
    rw [hout]
    congr 1
    apply propext
    simp [gateVal_eq_of_notMem C I u hno C.size _ (Fin.is_lt _)]
  rw [heq, hf] at ht
  exact Bool.noConfusion ht

lemma gateVal_eq_from_unique {n : Nat} (C : AndCountCircuit n) (I : Finset (Fin n)) (u : Fin n)
    (g : Fin C.size) (honly : ∀ j : Fin C.size, j ≠ g → u ∉ C.leftVars j ∧ u ∉ C.rightVars j)
    (hg : C.gateVal (insert u I) g = C.gateVal I g) :
    ∀ (m : Nat) (i : Fin C.size), i.val < m → C.gateVal (insert u I) i = C.gateVal I i := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    by_cases hig : i = g
    · subst hig; exact hg
    · rw [gateVal_rec C (insert u I) i, gateVal_rec C I i]
      have hc : ∀ j : Fin C.size, j < i → C.gateVal (insert u I) j = C.gateVal I j := by
        intro j hji; exact ih j (by have : j.val < i.val := hji; omega)
      have hL : sideTrue (insert u I) (C.leftVars i) (C.leftGates i) i (C.gateVal (insert u I)) =
          sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I) := by
        unfold sideTrue
        congr 1
        apply propext
        constructor
        · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩)
          · rcases Finset.mem_insert.mp hvU with rfl | hvI
            · exact absurd hvB (honly i hig).1
            · exact Or.inl ⟨v, hvB, hvI⟩
          · rw [hc j hji] at hjv
            exact Or.inr ⟨j, hjF, hji, hjv⟩
        · rintro (⟨v, hvB, hvI⟩ | ⟨j, hjF, hji, hjv⟩)
          · exact Or.inl ⟨v, hvB, Finset.mem_insert_of_mem hvI⟩
          · rw [← hc j hji] at hjv
            exact Or.inr ⟨j, hjF, hji, hjv⟩
      have hR : sideTrue (insert u I) (C.rightVars i) (C.rightGates i) i (C.gateVal (insert u I)) =
          sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I) := by
        unfold sideTrue
        congr 1
        apply propext
        constructor
        · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩)
          · rcases Finset.mem_insert.mp hvU with rfl | hvI
            · exact absurd hvB (honly i hig).2
            · exact Or.inl ⟨v, hvB, hvI⟩
          · rw [hc j hji] at hjv
            exact Or.inr ⟨j, hjF, hji, hjv⟩
        · rintro (⟨v, hvB, hvI⟩ | ⟨j, hjF, hji, hjv⟩)
          · exact Or.inl ⟨v, hvB, Finset.mem_insert_of_mem hvI⟩
          · rw [← hc j hji] at hjv
            exact Or.inr ⟨j, hjF, hji, hjv⟩
      rw [hL, hR]

lemma gateVal_eq_below {n : Nat} (C : AndCountCircuit n) (I : Finset (Fin n)) (u : Fin n)
    (g : Fin C.size) (honly : ∀ j : Fin C.size, j ≠ g → u ∉ C.leftVars j ∧ u ∉ C.rightVars j) :
    ∀ (m : Nat) (j : Fin C.size), j.val < m → j.val < g.val →
      C.gateVal (insert u I) j = C.gateVal I j := by
  intro m
  induction m with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro j hj hlt
    have hjne : j ≠ g := fun h => by subst h; omega
    have hc : ∀ k : Fin C.size, k < j → C.gateVal (insert u I) k = C.gateVal I k := by
      intro k hkj
      exact ih k (by have : k.val < j.val := hkj; omega) (by have : k.val < j.val := hkj; omega)
    rw [gateVal_rec C (insert u I) j, gateVal_rec C I j]
    have hL : sideTrue (insert u I) (C.leftVars j) (C.leftGates j) j (C.gateVal (insert u I)) =
        sideTrue I (C.leftVars j) (C.leftGates j) j (C.gateVal I) := by
      unfold sideTrue
      congr 1
      apply propext
      constructor
      · rintro (⟨v, hvB, hvU⟩ | ⟨k, hkF, hkj, hkv⟩)
        · rcases Finset.mem_insert.mp hvU with rfl | hvI
          · exact absurd hvB (honly j hjne).1
          · exact Or.inl ⟨v, hvB, hvI⟩
        · rw [hc k hkj] at hkv
          exact Or.inr ⟨k, hkF, hkj, hkv⟩
      · rintro (⟨v, hvB, hvI⟩ | ⟨k, hkF, hkj, hkv⟩)
        · exact Or.inl ⟨v, hvB, Finset.mem_insert_of_mem hvI⟩
        · rw [← hc k hkj] at hkv
          exact Or.inr ⟨k, hkF, hkj, hkv⟩
    have hR : sideTrue (insert u I) (C.rightVars j) (C.rightGates j) j (C.gateVal (insert u I)) =
        sideTrue I (C.rightVars j) (C.rightGates j) j (C.gateVal I) := by
      unfold sideTrue
      congr 1
      apply propext
      constructor
      · rintro (⟨v, hvB, hvU⟩ | ⟨k, hkF, hkj, hkv⟩)
        · rcases Finset.mem_insert.mp hvU with rfl | hvI
          · exact absurd hvB (honly j hjne).2
          · exact Or.inl ⟨v, hvB, hvI⟩
        · rw [hc k hkj] at hkv
          exact Or.inr ⟨k, hkF, hkj, hkv⟩
      · rintro (⟨v, hvB, hvI⟩ | ⟨k, hkF, hkj, hkv⟩)
        · exact Or.inl ⟨v, hvB, Finset.mem_insert_of_mem hvI⟩
        · rw [← hc k hkj] at hkv
          exact Or.inr ⟨k, hkF, hkj, hkv⟩
    rw [hL, hR]

lemma unique_gate_miss {n : Nat} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hfit : Fits G C) (hout : C.outVars = ∅) (u : Fin n) (g : Fin C.size) (s : Bool)
    (hside : u ∉ sideVars C g (!s))
    (honly : ∀ j : Fin C.size, j ≠ g → u ∉ C.leftVars j ∧ u ∉ C.rightVars j)
    (I : Finset (Fin n)) (hMIS : isMIS G I) (huI : u ∉ I) :
    C.gateVal I g = false ∧ sv C I g s = false ∧ sv C I g (!s) = true := by
  have hdiff : C.gateVal (insert u I) g ≠ C.gateVal I g := by
    intro heqg
    have hev : C.eval (insert u I) = C.eval I := by
      unfold AndCountCircuit.eval
      rw [hout]
      congr 1
      apply propext
      simp [gateVal_eq_from_unique C I u g honly heqg C.size _ (Fin.is_lt _)]
    have ht := (hfit I hMIS).2 u huI
    rw [hev, (hfit I hMIS).1] at ht
    exact Bool.noConfusion ht
  have hmono : C.gateVal I g = true → C.gateVal (insert u I) g = true :=
    gateVal_mono C I (insert u I) (Finset.subset_insert u I) g
  have hIg : C.gateVal I g = false := by
    cases h : C.gateVal I g
    · rfl
    · rw [h] at hdiff
      exact absurd (hmono h).symm hdiff.symm
  have hIns : C.gateVal (insert u I) g = true := by
    cases h : C.gateVal (insert u I) g
    · rw [h, hIg] at hdiff
      exact absurd rfl hdiff
    · rfl
  have hsvIns : sv C (insert u I) g (!s) = true := by
    rw [gateVal_rec, Bool.and_eq_true] at hIns
    cases hs : s
    · simpa [sv, sideVars, sideGates, hs] using hIns.2
    · simpa [sv, sideVars, sideGates, hs] using hIns.1
  have hsvEq : sv C (insert u I) g (!s) = sv C I g (!s) := by
    unfold sv
    unfold sideTrue
    congr 1
    apply propext
    constructor
    · rintro (⟨v, hvB, hvU⟩ | ⟨j, hjF, hjg, hjv⟩)
      · rcases Finset.mem_insert.mp hvU with rfl | hvI
        · exact absurd hvB hside
        · exact Or.inl ⟨v, hvB, hvI⟩
      · have hjeq := gateVal_eq_below C I u g honly C.size j j.isLt hjg
        rw [hjeq] at hjv
        exact Or.inr ⟨j, hjF, hjg, hjv⟩
    · rintro (⟨v, hvB, hvI⟩ | ⟨j, hjF, hjg, hjv⟩)
      · exact Or.inl ⟨v, hvB, Finset.mem_insert_of_mem hvI⟩
      · have hjeq := gateVal_eq_below C I u g honly C.size j j.isLt hjg
        rw [← hjeq] at hjv
        exact Or.inr ⟨j, hjF, hjg, hjv⟩
  have hns : sv C I g (!s) = true := by rw [← hsvEq]; exact hsvIns
  have hs0 : sv C I g s = false := by
    have hf := (gate_false_iff C I g).1 hIg
    cases hs : s
    · simp only [hs, Bool.not_false] at hns hf
      rcases hf with hf | hf
      · exact hf
      · rw [hns] at hf; exact Bool.noConfusion hf
    · simp only [hs, Bool.not_true] at hns hf
      rcases hf with hf | hf
      · rw [hns] at hf; exact Bool.noConfusion hf
      · exact hf
  exact ⟨hIg, hs0, hns⟩

lemma unique_gate_of_mis {n : Nat} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    {u w : Fin n} (hadj : G.Adj u w) (hk : 2 ≤ C.size) (hsize : C.size ≤ 3)
    {m : Nat} (hm : 2 ^ (C.size - 2) < m)
    (M : Fin m → Finset (Fin n)) (hMIS : ∀ a : Fin m, isMIS G (M a))
    (hInj : ∀ a b : Fin m, a ≠ b → M a ≠ M b) (huM : ∀ a : Fin m, u ∈ M a) :
    ∃ (g : Fin C.size) (s : Bool),
      u ∈ sideVars C g s ∧ u ∉ sideVars C g (!s) ∧
      ∀ j : Fin C.size, j ≠ g → u ∉ C.leftVars j ∧ u ∉ C.rightVars j := by
  obtain ⟨g0, hg0⟩ := noniso_hits_gate G C hfit hout hadj
  let F := Finset.univ.filter (fun i : Fin C.size => u ∉ C.leftVars i ∧ u ∉ C.rightVars i)
  have hvb := vertex_proj_bound G C hfit u M hMIS hInj huM
  change m ≤ 2 ^ F.card at hvb
  have hFsub : F ⊆ Finset.univ.erase g0 := by
    intro i hi
    rw [Finset.mem_filter] at hi
    refine Finset.mem_erase.2 ⟨fun heq => ?_, Finset.mem_univ i⟩
    subst heq
    rcases hg0 with hl | hr
    · exact hi.2.1 hl
    · exact hi.2.2 hr
  have hFle : F.card ≤ C.size - 1 := by
    have h1 := Finset.card_le_card hFsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ g0), Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  let Gu := Finset.univ \ F
  have hGuadd : Gu.card + F.card = C.size := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ F)
    simpa [Gu, Finset.card_univ, Fintype.card_fin] using this
  have hFge : C.size - 1 ≤ F.card := by
    by_contra hlt
    have hlt2 : F.card ≤ C.size - 2 := by omega
    have hpow : 2 ^ F.card ≤ 2 ^ (C.size - 2) := Nat.pow_le_pow_right (by decide) hlt2
    omega
  have hGucard : Gu.card = 1 := by omega
  obtain ⟨g, hg⟩ := Finset.card_eq_one.1 hGucard
  have hgmem : g ∈ Gu := by rw [hg]; exact Finset.mem_singleton_self g
  have hgnF : g ∉ F := (Finset.mem_sdiff.1 hgmem).2
  have hhitg : u ∈ C.leftVars g ∨ u ∈ C.rightVars g := by
    by_contra hno
    push_neg at hno
    exact hgnF (Finset.mem_filter.2 ⟨Finset.mem_univ g, hno⟩)
  have honly : ∀ j : Fin C.size, j ≠ g → u ∉ C.leftVars j ∧ u ∉ C.rightVars j := by
    intro j hjne
    by_contra hno
    have hjF : j ∉ F := fun hj => hno (Finset.mem_filter.1 hj).2
    have hjGu : j ∈ Gu := Finset.mem_sdiff.2 ⟨Finset.mem_univ j, hjF⟩
    rw [hg, Finset.mem_singleton] at hjGu
    exact hjne hjGu
  rcases hhitg with hl | hr
  · refine ⟨g, false, hl, fun hr => Finset.disjoint_left.1 (hdisj g) hl hr, honly⟩
  · refine ⟨g, true, hr, fun hl => Finset.disjoint_left.1 (hdisj g) hl hr, honly⟩

lemma contra_noniso_c3 {n : Nat} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hfit : Fits G C) (hout : C.outVars = ∅) (hsz : C.size = 2)
    {u w : Fin n} (hadj : G.Adj u w)
    (M : Fin 3 → Finset (Fin n)) (hMIS : ∀ a : Fin 3, isMIS G (M a))
    (hInj : ∀ a b : Fin 3, a ≠ b → M a ≠ M b) (huM : ∀ a : Fin 3, u ∈ M a) :
    False := by
  obtain ⟨g0, hg0⟩ := noniso_hits_gate G C hfit hout hadj
  let F := Finset.univ.filter (fun i : Fin C.size => u ∉ C.leftVars i ∧ u ∉ C.rightVars i)
  have hvb := vertex_proj_bound G C hfit u M hMIS hInj huM
  change 3 ≤ 2 ^ F.card at hvb
  have hFsub : F ⊆ Finset.univ.erase g0 := by
    intro i hi
    rw [Finset.mem_filter] at hi
    refine Finset.mem_erase.2 ⟨fun heq => ?_, Finset.mem_univ i⟩
    subst heq
    rcases hg0 with hl | hr
    · exact hi.2.1 hl
    · exact hi.2.2 hr
  have hFle : F.card ≤ 1 := by
    have h1 := Finset.card_le_card hFsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ g0), Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hpow : 2 ^ F.card ≤ 2 := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hFle
  omega

lemma contra_sun_c2 {n : Nat} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (hsz : C.size = 2)
    (u v w : Fin n)
    (huN : ∃ x, G.Adj u x) (hvN : ∃ x, G.Adj v x) (hwN : ∃ x, G.Adj w x)
    (I0 I1 I2 I3 : Finset (Fin n))
    (hMIS : ∀ a : Fin 4, isMIS G (![I0, I1, I2, I3] a))
    (hInj : ∀ a b : Fin 4, a ≠ b → ![I0, I1, I2, I3] a ≠ ![I0, I1, I2, I3] b)
    (hu2 : ∃ a b : Fin 4, a ≠ b ∧ u ∈ ![I0, I1, I2, I3] a ∧ u ∈ ![I0, I1, I2, I3] b)
    (hv2 : ∃ a b : Fin 4, a ≠ b ∧ v ∈ ![I0, I1, I2, I3] a ∧ v ∈ ![I0, I1, I2, I3] b)
    (hw2 : ∃ a b : Fin 4, a ≠ b ∧ w ∈ ![I0, I1, I2, I3] a ∧ w ∈ ![I0, I1, I2, I3] b)
    (huv3 : ∃ a b c : Fin 4, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (u ∈ ![I0, I1, I2, I3] a ∨ v ∈ ![I0, I1, I2, I3] a) ∧
      (u ∈ ![I0, I1, I2, I3] b ∨ v ∈ ![I0, I1, I2, I3] b) ∧
      (u ∈ ![I0, I1, I2, I3] c ∨ v ∈ ![I0, I1, I2, I3] c))
    (huv0 : ∃ d : Fin 4, u ∉ ![I0, I1, I2, I3] d ∧ v ∉ ![I0, I1, I2, I3] d)
    (huw3 : ∃ a b c : Fin 4, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (u ∈ ![I0, I1, I2, I3] a ∨ w ∈ ![I0, I1, I2, I3] a) ∧
      (u ∈ ![I0, I1, I2, I3] b ∨ w ∈ ![I0, I1, I2, I3] b) ∧
      (u ∈ ![I0, I1, I2, I3] c ∨ w ∈ ![I0, I1, I2, I3] c))
    (huw0 : ∃ d : Fin 4, u ∉ ![I0, I1, I2, I3] d ∧ w ∉ ![I0, I1, I2, I3] d)
    (hvw3 : ∃ a b c : Fin 4, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (v ∈ ![I0, I1, I2, I3] a ∨ w ∈ ![I0, I1, I2, I3] a) ∧
      (v ∈ ![I0, I1, I2, I3] b ∨ w ∈ ![I0, I1, I2, I3] b) ∧
      (v ∈ ![I0, I1, I2, I3] c ∨ w ∈ ![I0, I1, I2, I3] c))
    (hvw0 : ∃ d : Fin 4, v ∉ ![I0, I1, I2, I3] d ∧ w ∉ ![I0, I1, I2, I3] d) :
    False := by
  let xs : Fin 4 → Finset (Fin n) := ![I0, I1, I2, I3]
  have uniq : ∀ x : Fin n, (∃ y, G.Adj x y) →
      (∃ a b : Fin 4, a ≠ b ∧ x ∈ xs a ∧ x ∈ xs b) →
      ∃ (g : Fin C.size) (s : Bool),
        x ∈ sideVars C g s ∧ x ∉ sideVars C g (!s) ∧
        ∀ j : Fin C.size, j ≠ g → x ∉ C.leftVars j ∧ x ∉ C.rightVars j := by
    rintro x ⟨y, hxy⟩ ⟨a, b, hab, hxa, hxb⟩
    let M2 : Fin 2 → Finset (Fin n) := fun r => if r.val = 0 then xs a else xs b
    apply unique_gate_of_mis G C hfit hout hdisj hxy (by omega) (by omega) (by rw [hsz]; decide) M2
    · intro ⟨r, hr⟩
      match r with
      | 0 => simpa [M2] using hMIS a
      | 1 => simpa [M2] using hMIS b
      | _ + 2 => omega
    · intro r1 r2 hr
      rcases r1 with ⟨r1, hr1⟩; rcases r2 with ⟨r2, hr2⟩
      have hne : r1 ≠ r2 := fun h => hr (Fin.ext h)
      match r1, r2 with
      | 0, 0 => exact absurd rfl hne
      | 0, 1 => simpa [M2] using hInj a b hab
      | 1, 0 => simpa [M2] using fun h => hInj a b hab h.symm
      | 1, 1 => exact absurd rfl hne
      | _ + 2, _ => omega
      | _, _ + 2 => omega
    · intro ⟨r, hr⟩
      match r with
      | 0 => simpa [M2] using hxa
      | 1 => simpa [M2] using hxb
      | _ + 2 => omega
  obtain ⟨gu, su, hus, huo, huonly⟩ := uniq u huN hu2
  obtain ⟨gv, sv_, hvs, hvo, hvonly⟩ := uniq v hvN hv2
  obtain ⟨gw, sw, hws, hwo, hwonly⟩ := uniq w hwN hw2
  have kill_pair : ∀ (x y : Fin n) (gx gy : Fin C.size) (sx sy : Bool),
      x ∈ sideVars C gx sx → x ∉ sideVars C gx (!sx) →
      (∀ j, j ≠ gx → x ∉ C.leftVars j ∧ x ∉ C.rightVars j) →
      y ∈ sideVars C gy sy → y ∉ sideVars C gy (!sy) →
      (∀ j, j ≠ gy → y ∉ C.leftVars j ∧ y ∉ C.rightVars j) →
      gx = gy →
      (∃ a b c : Fin 4, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (x ∈ xs a ∨ y ∈ xs a) ∧ (x ∈ xs b ∨ y ∈ xs b) ∧ (x ∈ xs c ∨ y ∈ xs c)) →
      (∃ d : Fin 4, x ∉ xs d ∧ y ∉ xs d) →
      False := by
    rintro x y gx gy sx sy hxs hxo hxonly hys hyo hyonly rfl ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ ⟨d, hxd, hyd⟩
    by_cases hs : sx = sy
    · subst hs
      let idx3 : Fin 3 → Fin 4 := ![a, b, c]
      let M3 : Fin 3 → Finset (Fin n) := fun r => xs (idx3 r)
      have hM3inj : ∀ r1 r2 : Fin 3, r1 ≠ r2 → M3 r1 ≠ M3 r2 := by
        intro r1 r2 hr
        apply hInj
        rcases r1 with ⟨r1, _⟩; rcases r2 with ⟨r2, _⟩
        match r1, r2 with
        | 0, 0 => exact absurd rfl (fun h => hr (Fin.ext h))
        | 0, 1 => exact hab
        | 0, 2 => exact hac
        | 1, 0 => exact hab.symm
        | 1, 1 => exact absurd rfl (fun h => hr (Fin.ext h))
        | 1, 2 => exact hbc
        | 2, 0 => exact hac.symm
        | 2, 1 => exact hbc.symm
        | 2, 2 => exact absurd rfl (fun h => hr (Fin.ext h))
        | _ + 3, _ => omega
        | _, _ + 3 => omega
      have hhit3 : ∀ r : Fin 3, x ∈ M3 r ∨ y ∈ M3 r := by
        intro ⟨r, hr⟩
        match r with
        | 0 => exact ha
        | 1 => exact hb
        | 2 => exact hc
        | _ + 3 => omega
      let cf : Fin 3 → Fin C.size → Bool := fun r i =>
        if i = gx then !sx else if sv C (M3 r) i false = false then false else true
      have hcb := code_card_bound C M3 (Finset.univ.erase gx) cf
        (fun r => (hfit (M3 r) (hMIS (idx3 r))).1)
        (eval_union_mis_true G C hfit M3 (fun r => hMIS (idx3 r)) hM3inj)
        (fun r i hgi => by
          by_cases hig : i = gx
          · subst hig
            have hsvt : sv C (M3 r) i sx = true := by
              rcases hhit3 r with hxm | hym
              · exact sv_hit_mem C (M3 r) i sx hxs hxm
              · exact sv_hit_mem C (M3 r) i sx hys hym
            have hgf := (gate_false_iff C (M3 r) i).1 hgi
            simp only [cf, if_pos rfl]
            cases hsx : sx
            · rw [hsx] at hsvt
              rcases hgf with hf | hf
              · rw [hsvt] at hf; exact Bool.noConfusion hf
              · simpa using hf
            · rw [hsx] at hsvt
              rcases hgf with hf | hf
              · simpa using hf
              · rw [hsvt] at hf; exact Bool.noConfusion hf
          · simp only [cf, if_neg hig]
            by_cases hf : sv C (M3 r) i false = false
            · simpa [hf] using hf
            · have hgf := (gate_false_iff C (M3 r) i).1 hgi
              rcases hgf with hl | hr
              · exact absurd hl hf
              · simpa [hf] using hr)
        (fun r1 r2 i hi => by
          have hig : i = gx := by
            by_contra hne
            exact hi (Finset.mem_erase.2 ⟨hne, Finset.mem_univ i⟩)
          simp [cf, hig])
      have hcardF : (Finset.univ.erase gx).card = 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ gx), Finset.card_univ, Fintype.card_fin, hsz]
      rw [hcardF] at hcb
      omega
    · have hsy : sy = !sx := by cases sx <;> cases sy <;> simp_all
      subst hsy
      have h1 := unique_gate_miss G C hfit hout x gx sx hxo hxonly (xs d) (hMIS d) hxd
      have h2 := unique_gate_miss G C hfit hout y gx (!sx) hyo hyonly (xs d) (hMIS d) hyd
      rw [Bool.not_not] at h2
      rw [h1.2.2] at h2
      exact Bool.noConfusion h2.2.1
  have htwo : gu = gv ∨ gu = gw ∨ gv = gw := by
    by_cases h1 : gu = gv
    · exact Or.inl h1
    · by_cases h2 : gu = gw
      · exact Or.inr (Or.inl h2)
      · right; right
        apply Fin.ext
        have hne1 : gu.val ≠ gv.val := fun h => h1 (Fin.ext h)
        have hne2 : gu.val ≠ gw.val := fun h => h2 (Fin.ext h)
        omega
  rcases htwo with h | h | h
  · exact kill_pair u v gu gv su sv_ hus huo huonly hvs hvo hvonly h huv3 huv0
  · exact kill_pair u w gu gw su sw hus huo huonly hws hwo hwonly h huw3 huw0
  · exact kill_pair v w gv gw sv_ sw hvs hvo hvonly hws hwo hwonly h hvw3 hvw0

lemma contra_adj_c3 {n : Nat} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (hsz : C.size = 3)
    (u v : Fin n) (hadj : G.Adj u v)
    (I0 : Finset (Fin n)) (hI0 : isMIS G I0) (hu0 : u ∉ I0) (hv0 : v ∉ I0)
    (U3 : Fin 3 → Finset (Fin n)) (hU3mis : ∀ r, isMIS G (U3 r))
    (hU3inj : ∀ a b, a ≠ b → U3 a ≠ U3 b) (hU3hit : ∀ r, u ∈ U3 r)
    (V3 : Fin 3 → Finset (Fin n)) (hV3mis : ∀ r, isMIS G (V3 r))
    (hV3inj : ∀ a b, a ≠ b → V3 a ≠ V3 b) (hV3hit : ∀ r, v ∈ V3 r) :
    False := by
  obtain ⟨gu, su, hus, huo, huonly⟩ :=
    unique_gate_of_mis G C hfit hout hdisj hadj (by omega) (by omega) (by rw [hsz]; decide) U3 hU3mis hU3inj hU3hit
  obtain ⟨gv, sv_, hvs, hvo, hvonly⟩ :=
    unique_gate_of_mis G C hfit hout hdisj (sg_symm G hadj) (by omega) (by omega) (by rw [hsz]; decide) V3 hV3mis hV3inj hV3hit
  by_cases hgeq : gu = gv
  · subst hgeq
    by_cases hseq : su = sv_
    · subst hseq
      let M6 : Fin 6 → Finset (Fin n) := fun r => if hlt : r.val < 3 then U3 ⟨r.val, hlt⟩ else V3 ⟨r.val - 3, by omega⟩
      have hM6mis : ∀ r : Fin 6, isMIS G (M6 r) := by
        intro ⟨r, hr⟩
        by_cases hlt : r < 3
        · simpa [M6, hlt] using hU3mis ⟨r, hlt⟩
        · simpa [M6, hlt] using hV3mis ⟨r - 3, by omega⟩
      have hM6inj : ∀ a b : Fin 6, a ≠ b → M6 a ≠ M6 b := by
        intro ⟨a, ha⟩ ⟨b, hb⟩ hab heq
        have hne : a ≠ b := fun h => hab (Fin.ext h)
        by_cases ha3 : a < 3 <;> by_cases hb3 : b < 3
        · apply hU3inj ⟨a, ha3⟩ ⟨b, hb3⟩ (fun h => hne (by have hv := congrArg Fin.val h; dsimp at hv; exact hv))
          simpa [M6, ha3, hb3] using heq
        · have huA : u ∈ U3 ⟨a, ha3⟩ := hU3hit ⟨a, ha3⟩
          have hvB : v ∈ V3 ⟨b - 3, by omega⟩ := hV3hit ⟨b - 3, by omega⟩
          have heq' : U3 ⟨a, ha3⟩ = V3 ⟨b - 3, by omega⟩ := by simpa [M6, ha3, hb3] using heq
          rw [← heq'] at hvB
          exact (hU3mis ⟨a, ha3⟩).1 u huA v hvB hadj
        · have hvA : v ∈ V3 ⟨a - 3, by omega⟩ := hV3hit ⟨a - 3, by omega⟩
          have huB : u ∈ U3 ⟨b, hb3⟩ := hU3hit ⟨b, hb3⟩
          have heq' : V3 ⟨a - 3, by omega⟩ = U3 ⟨b, hb3⟩ := by simpa [M6, ha3, hb3] using heq
          rw [heq'] at hvA
          exact (hU3mis ⟨b, hb3⟩).1 u huB v hvA hadj
        · apply hV3inj ⟨a - 3, by omega⟩ ⟨b - 3, by omega⟩ (fun h => hne (by
            have hv := congrArg Fin.val h; dsimp at hv; omega))
          simpa [M6, ha3, hb3] using heq
      let cf : Fin 6 → Fin C.size → Bool := fun r i =>
        if i = gu then !su else if sv C (M6 r) i false = false then false else true
      have hcb := code_card_bound C M6 (Finset.univ.erase gu) cf
        (fun r => (hfit (M6 r) (hM6mis r)).1)
        (eval_union_mis_true G C hfit M6 hM6mis hM6inj)
        (fun r i hgi => by
          by_cases hig : i = gu
          · subst hig
            have hsvt : sv C (M6 r) i su = true := by
              rcases r with ⟨r, hr⟩
              by_cases hlt : r < 3
              · simpa [M6, hlt] using sv_hit_mem C (U3 ⟨r, hlt⟩) i su hus (hU3hit ⟨r, hlt⟩)
              · simpa [M6, hlt] using sv_hit_mem C (V3 ⟨r - 3, by omega⟩) i su hvs (hV3hit ⟨r - 3, by omega⟩)
            have hgf := (gate_false_iff C (M6 r) i).1 hgi
            simp only [cf, if_pos rfl]
            cases hsu : su
            · rw [hsu] at hsvt
              rcases hgf with hf | hf
              · rw [hsvt] at hf; exact Bool.noConfusion hf
              · simpa using hf
            · rw [hsu] at hsvt
              rcases hgf with hf | hf
              · simpa using hf
              · rw [hsvt] at hf; exact Bool.noConfusion hf
          · simp only [cf, if_neg hig]
            by_cases hf : sv C (M6 r) i false = false
            · simpa [hf] using hf
            · have hgf := (gate_false_iff C (M6 r) i).1 hgi
              rcases hgf with hl | hr
              · exact absurd hl hf
              · simpa [hf] using hr)
        (fun r1 r2 i hi => by
          have hig : i = gu := by
            by_contra hne
            exact hi (Finset.mem_erase.2 ⟨hne, Finset.mem_univ i⟩)
          simp [cf, hig])
      have hcardF : (Finset.univ.erase gu).card = 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ gu), Finset.card_univ, Fintype.card_fin, hsz]
      rw [hcardF] at hcb
      omega
    · have hsy : sv_ = !su := by cases su <;> cases sv_ <;> simp_all
      subst hsy
      have h1 := unique_gate_miss G C hfit hout u gu su huo huonly I0 hI0 hu0
      have h2 := unique_gate_miss G C hfit hout v gu (!su) hvo hvonly I0 hI0 hv0
      rw [Bool.not_not] at h2
      rw [h1.2.2] at h2
      exact Bool.noConfusion h2.2.1
  · let F := (Finset.univ.erase gu).erase gv
    let cf : Fin 3 → Fin C.size → Bool := fun r i =>
      if i = gu then !su
      else if i = gv then sv_
      else if sv C (U3 r) i false = false then false else true
    have hcb := code_card_bound C U3 F cf
      (fun r => (hfit (U3 r) (hU3mis r)).1)
      (eval_union_mis_true G C hfit U3 hU3mis hU3inj)
      (fun r i hgi => by
        by_cases higu : i = gu
        · subst higu
          have hsvt := sv_hit_mem C (U3 r) i su hus (hU3hit r)
          have hgf := (gate_false_iff C (U3 r) i).1 hgi
          simp only [cf, if_pos rfl]
          cases hsu : su
          · rw [hsu] at hsvt
            rcases hgf with hf | hf
            · rw [hsvt] at hf; exact Bool.noConfusion hf
            · simpa using hf
          · rw [hsu] at hsvt
            rcases hgf with hf | hf
            · simpa using hf
            · rw [hsvt] at hf; exact Bool.noConfusion hf
        · by_cases higv : i = gv
          · subst higv
            have hvnot : v ∉ U3 r := fun hv => (hU3mis r).1 u (hU3hit r) v hv hadj
            have hm := unique_gate_miss G C hfit hout v i sv_ hvo hvonly (U3 r) (hU3mis r) hvnot
            simpa [cf, higu] using hm.2.1
          · simp only [cf, if_neg higu, if_neg higv]
            by_cases hf : sv C (U3 r) i false = false
            · simpa [hf] using hf
            · have hgf := (gate_false_iff C (U3 r) i).1 hgi
              rcases hgf with hl | hr
              · exact absurd hl hf
              · simpa [hf] using hr)
      (fun r1 r2 i hi => by
        by_cases higu : i = gu
        · simp [cf, higu]
        · by_cases higv : i = gv
          · simp [cf, higu, higv]
          · exfalso
            exact hi (Finset.mem_erase.2 ⟨higv, Finset.mem_erase.2 ⟨higu, Finset.mem_univ i⟩⟩))
    have hcardF : F.card = 1 := by
      have hgvmem : gv ∈ Finset.univ.erase gu := Finset.mem_erase.2 ⟨Ne.symm hgeq, Finset.mem_univ gv⟩
      rw [show F = (Finset.univ.erase gu).erase gv from rfl,
        Finset.card_erase_of_mem hgvmem,
        Finset.card_erase_of_mem (Finset.mem_univ gu), Finset.card_univ, Fintype.card_fin, hsz]
    rw [hcardF] at hcb
    omega

lemma bc_of_indep_card {n : Nat} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : isIndep G S) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin n)), k ≤ n - S.card ∧ Cover G k X Y := by
  classical
  let T := Finset.univ \ S
  have hTadd : T.card + S.card = n := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    simpa [T, Finset.card_univ, Fintype.card_fin] using this
  obtain ⟨e, he⟩ := finset_enum T
  refine ⟨T.card, fun i => {e i}, fun i => Finset.univ.filter (fun w => G.Adj (e i) w), by omega, ?_, ?_⟩
  · intro i a ha b hb
    rw [Finset.mem_singleton] at ha
    rw [Finset.mem_filter] at hb
    rw [ha]
    exact hb.2
  · intro a b hab
    by_cases haS : a ∈ S
    · have hbT : b ∈ T := Finset.mem_sdiff.2 ⟨Finset.mem_univ b, fun hbS => hS a haS b hbS hab⟩
      obtain ⟨i, hi⟩ := (he b).1 hbT
      refine ⟨i, Or.inr ⟨Finset.mem_singleton.2 hi.symm, ?_⟩⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ a, by rw [hi]; exact sg_symm G hab⟩
    · have haT : a ∈ T := Finset.mem_sdiff.2 ⟨Finset.mem_univ a, haS⟩
      obtain ⟨i, hi⟩ := (he a).1 haT
      refine ⟨i, Or.inl ⟨Finset.mem_singleton.2 hi.symm, ?_⟩⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ b, by rw [hi]; exact hab⟩

lemma solve_size0 (G : SimpleGraph (Fin 6)) (C : AndCountCircuit 6)
    (hfit : Fits G C) (hout : C.outVars = ∅) (hsz : C.size = 0) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y := by
  refine ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, by omega,
    fun i => Fin.elim0 i, fun a b hab => ?_⟩
  exfalso
  have hind : isIndep G {a} := fun x hx y hy => by
    rw [Finset.mem_singleton] at hx hy; subst hx hy; exact sg_irrefl G _
  obtain ⟨I, hsub, hMIS⟩ := exists_mis_superset G {a} hind
  have haI : a ∈ I := hsub (Finset.mem_singleton_self a)
  have hbI : b ∉ I := fun hb => hMIS.1 a haI b hb hab
  have ht := (hfit I hMIS).2 b hbI
  rw [eval_iff, hout] at ht
  rcases ht with ⟨v, hv, _⟩ | ⟨⟨j, hj⟩, _⟩
  · cases hv
  · omega

lemma solve_size1 (G : SimpleGraph (Fin 6)) (C : AndCountCircuit 6)
    (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (hsz : C.size = 1) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y := by
  by_cases hedge : ∃ a b : Fin 6, G.Adj a b
  · obtain ⟨a0, b0, hab0⟩ := hedge
    have h0out : (⟨0, by omega⟩ : Fin C.size) ∈ C.outGates := by
      have hind : isIndep G {a0} := fun x hx y hy => by
        rw [Finset.mem_singleton] at hx hy; subst hx hy; exact sg_irrefl G _
      obtain ⟨I, hsub, hMIS⟩ := exists_mis_superset G {a0} hind
      have hbI : b0 ∉ I := fun hb => hMIS.1 a0 (hsub (Finset.mem_singleton_self a0)) b0 hb hab0
      have ht := (hfit I hMIS).2 b0 hbI
      rw [eval_iff, hout] at ht
      rcases ht with ⟨v, hv, _⟩ | ⟨⟨j, hj⟩, hjmem, _⟩
      · cases hv
      · have hj0 : j = 0 := by omega
        subst hj0
        exact hjmem
    let g0 : Fin C.size := ⟨0, by omega⟩
    let L := C.leftVars g0
    let R := C.rightVars g0
    have hLR : ∀ U : Finset (Fin 6), C.eval U = true ↔ (∃ x ∈ L, x ∈ U) ∧ (∃ y ∈ R, y ∈ U) := by
      intro U
      rw [eval_iff, hout]
      constructor
      · rintro (⟨v, hv, _⟩ | ⟨⟨j, hj⟩, _, hgv⟩)
        · cases hv
        · have hj0 : j = 0 := by omega
          subst hj0
          change C.gateVal U g0 = true at hgv
          rw [gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff] at hgv
          rcases hgv with ⟨hl | ⟨⟨k, hk⟩, _, hkg, _⟩, hr | ⟨⟨k, hk⟩, _, hkg, _⟩⟩
          · exact ⟨hl, hr⟩
          · exact absurd (show k < 0 from hkg) (Nat.not_lt_zero _)
          · exact absurd (show k < 0 from hkg) (Nat.not_lt_zero _)
          · exact absurd (show k < 0 from hkg) (Nat.not_lt_zero _)
      · rintro ⟨hl, hr⟩
        refine Or.inr ⟨g0, h0out, ?_⟩
        rw [gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]
        exact ⟨Or.inl hl, Or.inl hr⟩
    refine ⟨1, fun _ => L, fun _ => R, by omega, ?_, ?_⟩
    · intro _ a ha b hb
      by_contra hno
      have habne : a ≠ b := fun heq => by
        subst heq
        exact Finset.disjoint_left.1 (hdisj g0) ha hb
      have hind : isIndep G {a, b} := isIndep_pair G a b hno
      obtain ⟨I, hsub, hMIS⟩ := exists_mis_superset G {a, b} hind
      have hev : C.eval I = true := (hLR I).2
        ⟨⟨a, ha, hsub (Finset.mem_insert_self a _)⟩,
         ⟨b, hb, hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))⟩⟩
      rw [(hfit I hMIS).1] at hev
      exact Bool.noConfusion hev
    · intro a b hab
      by_contra hnot
      push_neg at hnot
      have checkSide : ∀ u w : Fin 6, G.Adj u w → w ∈ R → u ∈ L := by
        intro u w huw hwR
        have hind : isIndep G {w} := fun x hx y hy => by
          rw [Finset.mem_singleton] at hx hy; subst hx hy; exact sg_irrefl G _
        obtain ⟨I, hsub, hMIS⟩ := exists_mis_superset G {w} hind
        have hwI : w ∈ I := hsub (Finset.mem_singleton_self w)
        have huI : u ∉ I := fun hu => hMIS.1 u hu w hwI huw
        have hf : C.eval I = false := (hfit I hMIS).1
        have ht : C.eval (insert u I) = true := (hfit I hMIS).2 u huI
        have hL0 : ¬ ∃ x ∈ L, x ∈ I := by
          intro hxL
          have hev := (hLR I).2 ⟨hxL, ⟨w, hwR, hwI⟩⟩
          rw [hf] at hev
          exact Bool.noConfusion hev
        obtain ⟨⟨x, hxL, hxU⟩, _⟩ := (hLR (insert u I)).1 ht
        rcases Finset.mem_insert.mp hxU with rfl | hxI
        · exact hxL
        · exact absurd ⟨x, hxL, hxI⟩ hL0
      have checkSideL : ∀ u w : Fin 6, G.Adj u w → w ∈ L → u ∈ R := by
        intro u w huw hwL
        have hind : isIndep G {w} := fun x hx y hy => by
          rw [Finset.mem_singleton] at hx hy; subst hx hy; exact sg_irrefl G _
        obtain ⟨I, hsub, hMIS⟩ := exists_mis_superset G {w} hind
        have hwI : w ∈ I := hsub (Finset.mem_singleton_self w)
        have huI : u ∉ I := fun hu => hMIS.1 u hu w hwI huw
        have hf : C.eval I = false := (hfit I hMIS).1
        have ht : C.eval (insert u I) = true := (hfit I hMIS).2 u huI
        have hR0 : ¬ ∃ y ∈ R, y ∈ I := by
          intro hyR
          have hev := (hLR I).2 ⟨⟨w, hwL, hwI⟩, hyR⟩
          rw [hf] at hev
          exact Bool.noConfusion hev
        obtain ⟨_, ⟨y, hyR, hyU⟩⟩ := (hLR (insert u I)).1 ht
        rcases Finset.mem_insert.mp hyU with rfl | hyI
        · exact hyR
        · exact absurd ⟨y, hyR, hyI⟩ hR0
      have hbR : b ∉ R := fun hb => (hnot 0).1 (checkSide a b hab hb) hb
      have hbL : b ∉ L := fun hb => (hnot 0).2 hb (checkSideL a b hab hb)
      have hind : isIndep G {a} := fun x hx y hy => by
        rw [Finset.mem_singleton] at hx hy; subst hx hy; exact sg_irrefl G _
      obtain ⟨I, hsub, hMIS⟩ := exists_mis_superset G {a} hind
      have haI : a ∈ I := hsub (Finset.mem_singleton_self a)
      have hbI : b ∉ I := fun hb => hMIS.1 a haI b hb hab
      have hf : C.eval I = false := (hfit I hMIS).1
      have ht : C.eval (insert b I) = true := (hfit I hMIS).2 b hbI
      obtain ⟨⟨x, hxL, hxU⟩, ⟨y, hyR, hyU⟩⟩ := (hLR (insert b I)).1 ht
      have hxI : x ∈ I := by
        rcases Finset.mem_insert.mp hxU with rfl | h
        · exact absurd hxL hbL
        · exact h
      have hyI : y ∈ I := by
        rcases Finset.mem_insert.mp hyU with rfl | h
        · exact absurd hyR hbR
        · exact h
      have hev := (hLR I).2 ⟨⟨x, hxL, hxI⟩, ⟨y, hyR, hyI⟩⟩
      rw [hf] at hev
      exact Bool.noConfusion hev
  · push_neg at hedge
    exact ⟨0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, by omega,
      fun i => Fin.elim0 i, fun a b hab => absurd hab (hedge a b)⟩

lemma cover_k6 (G : SimpleGraph (Fin 6)) (hK : ∀ a b : Fin 6, a ≠ b → G.Adj a b) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ 3 ∧ Cover G k X Y := by
  refine ⟨3, ![{0, 1, 2}, {0, 3}, {1, 4}], ![{3, 4, 5}, {1, 2, 4, 5}, {2, 5}], le_rfl, ?_, ?_⟩
  · intro i a ha b hb
    apply hK
    intro heq
    subst heq
    have hdisj : ∀ (i : Fin 3) (a : Fin 6),
        a ∈ (![{0, 1, 2}, {0, 3}, {1, 4}] : Fin 3 → Finset (Fin 6)) i →
        a ∉ (![{3, 4, 5}, {1, 2, 4, 5}, {2, 5}] : Fin 3 → Finset (Fin 6)) i := by
      decide +kernel
    exact hdisj i a ha hb
  · intro a b hab
    have hne : a ≠ b := fun h => by subst h; exact sg_irrefl G _ hab
    have hcov : ∀ a b : Fin 6, a ≠ b → ∃ i : Fin 3,
        (a ∈ (![{0, 1, 2}, {0, 3}, {1, 4}] : Fin 3 → Finset (Fin 6)) i ∧
          b ∈ (![{3, 4, 5}, {1, 2, 4, 5}, {2, 5}] : Fin 3 → Finset (Fin 6)) i) ∨
        (b ∈ (![{0, 1, 2}, {0, 3}, {1, 4}] : Fin 3 → Finset (Fin 6)) i ∧
          a ∈ (![{3, 4, 5}, {1, 2, 4, 5}, {2, 5}] : Fin 3 → Finset (Fin 6)) i) := by
      decide +kernel
    exact hcov a b hne

lemma mis_singleton_k6 (G : SimpleGraph (Fin 6)) (hK : ∀ a b : Fin 6, a ≠ b → G.Adj a b) :
    ∀ v : Fin 6, isMIS G {v} := by
  intro v
  refine ⟨fun a ha b hb => by rw [Finset.mem_singleton] at ha hb; subst ha hb; exact sg_irrefl G _, ?_⟩
  intro u hu
  refine ⟨v, Finset.mem_singleton_self v, hK u v fun h => hu (Finset.mem_singleton.2 h)⟩

def pairIdx (a b : Nat) : Nat :=
  if a == 0 then b - 1
  else if a == 1 then b + 3
  else if a == 2 then b + 6
  else if a == 3 then b + 8
  else 14

def hasBit (x k : Nat) : Bool := (x / 2 ^ k) % 2 == 1

def hasEdgeNat (m a b : Nat) : Bool :=
  if a < b then hasBit m (pairIdx a b)
  else if b < a then hasBit m (pairIdx b a)
  else false

def all6 (p : Nat → Bool) : Bool :=
  p 0 && p 1 && p 2 && p 3 && p 4 && p 5

def any6 (p : Nat → Bool) : Bool :=
  p 0 || p 1 || p 2 || p 3 || p 4 || p 5

def isMISNat (m s : Nat) : Bool :=
  all6 (fun u =>
    if hasBit s u then
      all6 (fun v => !(hasBit s v) || !(hasEdgeNat m u v))
    else
      any6 (fun v => hasBit s v && hasEdgeNat m u v))

def bicliqueOkNat (m X Y : Nat) : Bool :=
  all6 (fun a => !(hasBit X a) || all6 (fun b => !(hasBit Y b) || hasEdgeNat m a b))

def cov2OkNat (m X0 Y0 X1 Y1 : Nat) : Bool :=
  all6 (fun a => all6 (fun b =>
    !(a < b) || !(hasEdgeNat m a b) ||
    (hasBit X0 a && hasBit Y0 b) || (hasBit X0 b && hasBit Y0 a) ||
    (hasBit X1 a && hasBit Y1 b) || (hasBit X1 b && hasBit Y1 a)))

def cov3OkNat (m X0 Y0 X1 Y1 X2 Y2 : Nat) : Bool :=
  all6 (fun a => all6 (fun b =>
    !(a < b) || !(hasEdgeNat m a b) ||
    (hasBit X0 a && hasBit Y0 b) || (hasBit X0 b && hasBit Y0 a) ||
    (hasBit X1 a && hasBit Y1 b) || (hasBit X1 b && hasBit Y1 a) ||
    (hasBit X2 a && hasBit Y2 b) || (hasBit X2 b && hasBit Y2 a)))

def allDistinctAux : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.elem x) && allDistinctAux xs

def countHits (x : Nat) : List Nat → Nat
  | [] => 0
  | s :: rest => (if hasBit s x then 1 else 0) + countHits x rest

def countHitsPair (a b : Nat) : List Nat → Nat
  | [] => 0
  | s :: rest => (if hasBit s a || hasBit s b then 1 else 0) + countHitsPair a b rest

def anyMissPair (a b : Nat) : List Nat → Bool
  | [] => false
  | s :: rest => (!(hasBit s a) && !(hasBit s b)) || anyMissPair a b rest

def validWit (m w mode : Nat) : Bool :=
  let tag := w % 8
  if tag == 0 && (mode == 2 || mode == 3) then
    let a := (w / 8) % 8
    let b := (w / 64) % 8
    let c := (w / 512) % 8
    a < b && b < c && c < 6 && !(hasEdgeNat m a b) && !(hasEdgeNat m b c) && !(hasEdgeNat m a c)
  else if tag == 1 then
    let X0 := (w / 8) % 64
    let Y0 := (w / 512) % 64
    let X1 := (w / 32768) % 64
    let Y1 := (w / 2097152) % 64
    bicliqueOkNat m X0 Y0 && bicliqueOkNat m X1 Y1 && cov2OkNat m X0 Y0 X1 Y1
  else if tag == 2 && mode == 3 then
    let X0 := (w / 8) % 64
    let Y0 := (w / 512) % 64
    let X1 := (w / 32768) % 64
    let Y1 := (w / 2097152) % 64
    let X2 := (w / 134217728) % 64
    let Y2 := (w / 8589934592) % 64
    bicliqueOkNat m X0 Y0 && bicliqueOkNat m X1 Y1 && bicliqueOkNat m X2 Y2 &&
      cov3OkNat m X0 Y0 X1 Y1 X2 Y2
  else if tag == 3 && (mode == 2 || mode == 4) then
    let i0 := (w / 8) % 64
    let i1 := (w / 512) % 64
    let i2 := (w / 32768) % 64
    let i3 := (w / 2097152) % 64
    let i4 := (w / 134217728) % 64
    isMISNat m i0 && isMISNat m i1 && isMISNat m i2 && isMISNat m i3 && isMISNat m i4 &&
      allDistinctAux [i0, i1, i2, i3, i4]
  else if tag == 4 && mode == 3 then
    let i0 := (w / 8) % 64
    let i1 := (w / 512) % 64
    let i2 := (w / 32768) % 64
    let i3 := (w / 2097152) % 64
    let i4 := (w / 134217728) % 64
    let i5 := (w / 8589934592) % 64
    let i6 := (w / 549755813888) % 64
    let i7 := (w / 35184372088832) % 64
    let i8 := (w / 2251799813685248) % 64
    isMISNat m i0 && isMISNat m i1 && isMISNat m i2 && isMISNat m i3 && isMISNat m i4 &&
      isMISNat m i5 && isMISNat m i6 && isMISNat m i7 && isMISNat m i8 &&
      allDistinctAux [i0, i1, i2, i3, i4, i5, i6, i7, i8]
  else if tag == 5 && (mode == 2 || mode == 4) then
    let v := (w / 8) % 8
    let wn := (w / 64) % 8
    let i0 := (w / 512) % 64
    let i1 := (w / 32768) % 64
    let i2 := (w / 2097152) % 64
    v < 6 && wn < 6 && hasEdgeNat m v wn &&
      isMISNat m i0 && hasBit i0 v &&
      isMISNat m i1 && hasBit i1 v &&
      isMISNat m i2 && hasBit i2 v &&
      allDistinctAux [i0, i1, i2]
  else if tag == 6 && (mode == 2 || mode == 4) then
    let u := (w / 8) % 8
    let v := (w / 64) % 8
    let wv := (w / 512) % 8
    let i0 := (w / 4096) % 64
    let i1 := (w / 262144) % 64
    let i2 := (w / 16777216) % 64
    let i3 := (w / 1073741824) % 64
    let xs := [i0, i1, i2, i3]
    u < 6 && v < 6 && wv < 6 && u != v && u != wv && v != wv &&
      any6 (hasEdgeNat m u) && any6 (hasEdgeNat m v) && any6 (hasEdgeNat m wv) &&
      isMISNat m i0 && isMISNat m i1 && isMISNat m i2 && isMISNat m i3 &&
      allDistinctAux xs &&
      2 <= countHits u xs && 2 <= countHits v xs && 2 <= countHits wv xs &&
      3 <= countHitsPair u v xs && anyMissPair u v xs &&
      3 <= countHitsPair u wv xs && anyMissPair u wv xs &&
      3 <= countHitsPair v wv xs && anyMissPair v wv xs
  else if tag == 7 && mode == 3 then
    let u := (w / 8) % 8
    let v := (w / 64) % 8
    let i0 := (w / 512) % 64
    let u1 := (w / 32768) % 64
    let u2 := (w / 2097152) % 64
    let u3 := (w / 134217728) % 64
    let v1 := (w / 8589934592) % 64
    let v2 := (w / 549755813888) % 64
    let v3 := (w / 35184372088832) % 64
    u < 6 && v < 6 && hasEdgeNat m u v &&
      isMISNat m i0 && !(hasBit i0 u) && !(hasBit i0 v) &&
      isMISNat m u1 && hasBit u1 u &&
      isMISNat m u2 && hasBit u2 u &&
      isMISNat m u3 && hasBit u3 u && allDistinctAux [u1, u2, u3] &&
      isMISNat m v1 && hasBit v1 v &&
      isMISNat m v2 && hasBit v2 v &&
      isMISNat m v3 && hasBit v3 v && allDistinctAux [v1, v2, v3]
  else false

def tfTuples : List (Nat × Nat × Nat × Nat) :=
  [(0,0,0,0),(0,0,0,1),(0,0,0,2),(0,0,1,1),(0,0,1,2),(0,0,2,2),(0,1,1,1),(0,1,1,2),
   (0,1,2,2),(0,2,2,2),(1,1,1,1),(1,1,1,2),(1,1,2,2),(1,2,2,2),(2,2,2,2)]

def tfEdge (t : Nat × Nat × Nat × Nat) (sm a b : Nat) : Bool :=
  if a == 0 && b == 1 then false
  else if a == 0 then
    let tv := if b == 2 then t.1 else if b == 3 then t.2.1 else if b == 4 then t.2.2.1 else t.2.2.2
    tv != 0
  else if a == 1 then
    let tv := if b == 2 then t.1 else if b == 3 then t.2.1 else if b == 4 then t.2.2.1 else t.2.2.2
    tv != 1
  else
    let subIdx := if a == 2 then b - 3 else if a == 3 then b - 1 else 5
    !(hasBit sm subIdx)

def bitsToNat : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

def adjMask (adj : Fin 6 → Fin 6 → Bool) : Nat :=
  bitsToNat [adj 0 1, adj 0 2, adj 0 3, adj 0 4, adj 0 5,
    adj 1 2, adj 1 3, adj 1 4, adj 1 5,
    adj 2 3, adj 2 4, adj 2 5, adj 3 4, adj 3 5, adj 4 5]

def tfMask (t : Nat × Nat × Nat × Nat) (sm : Nat) : Nat :=
  bitsToNat [tfEdge t sm 0 1, tfEdge t sm 0 2, tfEdge t sm 0 3, tfEdge t sm 0 4, tfEdge t sm 0 5,
    tfEdge t sm 1 2, tfEdge t sm 1 3, tfEdge t sm 1 4, tfEdge t sm 1 5,
    tfEdge t sm 2 3, tfEdge t sm 2 4, tfEdge t sm 2 5, tfEdge t sm 3 4, tfEdge t sm 3 5, tfEdge t sm 4 5]

def a3Edge (t : Nat × Nat × Nat) (sm a b : Nat) : Bool :=
  if b < 3 then false
  else if a < 3 then
    let mv := if b == 3 then t.1 else if b == 4 then t.2.1 else t.2.2
    hasBit mv a
  else
    let subIdx := if a == 3 && b == 4 then 0 else if a == 3 && b == 5 then 1 else 2
    hasBit sm subIdx

def a3Mask (t : Nat × Nat × Nat) (sm : Nat) : Nat :=
  bitsToNat [a3Edge t sm 0 1, a3Edge t sm 0 2, a3Edge t sm 0 3, a3Edge t sm 0 4, a3Edge t sm 0 5,
    a3Edge t sm 1 2, a3Edge t sm 1 3, a3Edge t sm 1 4, a3Edge t sm 1 5,
    a3Edge t sm 2 3, a3Edge t sm 2 4, a3Edge t sm 2 5, a3Edge t sm 3 4, a3Edge t sm 3 5, a3Edge t sm 4 5]

def a3Tuples : List (Nat × Nat × Nat) :=
  [(1, 1, 1), (1, 1, 2), (1, 1, 3), (1, 1, 4), (1, 1, 5), (1, 1, 6), (1, 1, 7), (1, 2, 2), (1, 2, 3), (1, 2, 4), (1, 2, 5), (1, 2, 6), (1, 2, 7), (1, 3, 3), (1, 3, 4), (1, 3, 5), (1, 3, 6), (1, 3, 7), (1, 4, 4), (1, 4, 5), (1, 4, 6), (1, 4, 7), (1, 5, 5), (1, 5, 6), (1, 5, 7), (1, 6, 6), (1, 6, 7), (1, 7, 7), (2, 2, 2), (2, 2, 3), (2, 2, 4), (2, 2, 5), (2, 2, 6), (2, 2, 7), (2, 3, 3), (2, 3, 4), (2, 3, 5), (2, 3, 6), (2, 3, 7), (2, 4, 4), (2, 4, 5), (2, 4, 6), (2, 4, 7), (2, 5, 5), (2, 5, 6), (2, 5, 7), (2, 6, 6), (2, 6, 7), (2, 7, 7), (3, 3, 3), (3, 3, 4), (3, 3, 5), (3, 3, 6), (3, 3, 7), (3, 4, 4), (3, 4, 5), (3, 4, 6), (3, 4, 7), (3, 5, 5), (3, 5, 6), (3, 5, 7), (3, 6, 6), (3, 6, 7), (3, 7, 7), (4, 4, 4), (4, 4, 5), (4, 4, 6), (4, 4, 7), (4, 5, 5), (4, 5, 6), (4, 5, 7), (4, 6, 6), (4, 6, 7), (4, 7, 7), (5, 5, 5), (5, 5, 6), (5, 5, 7), (5, 6, 6), (5, 6, 7), (5, 7, 7), (6, 6, 6), (6, 6, 7), (6, 7, 7), (7, 7, 7)]

def checkBlock (mode : Nat) (mkMask : Nat → Nat) : Nat → Nat → List Nat → Option (List Nat)
  | 0, _, ws => some ws
  | rem + 1, sm, w :: ws =>
      if validWit (mkMask sm) w mode then checkBlock mode mkMask rem (sm + 1) ws else none
  | _ + 1, _, [] => none

def checkGroups {α : Type} (mode blockLen : Nat) (mkMask : α → Nat → Nat) :
    List α → List Nat → Bool
  | [], [] => true
  | t :: ts, ws =>
      match checkBlock mode (mkMask t) blockLen 0 ws with
      | some rest => checkGroups mode blockLen mkMask ts rest
      | none => false
  | _, _ => false

def table_tf_2 : List Nat := [
  4465134107, 1664, 2176, 1664, 2688, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  2688, 1664, 2176, 1664, 2752, 1664, 2176, 1664, 2688, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 2688, 1664, 2176, 1664, 2816, 1664, 2176, 1664,
  2688, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 2688, 1664, 2176, 1664,
  2752, 1664, 2176, 1664, 2688, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  2688, 1664, 2176, 1664, 4599351835, 1664, 2176, 1664, 4599351835, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 4599351835, 1664, 2176, 1664,
  4599351835, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  4599351835, 1664, 2176, 1664, 4599351835, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 4599351835, 1664, 2176, 1664, 4599351835, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 4330916379, 1664, 2176, 1664,
  4867787291, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  5404658203, 1664, 2176, 1664, 4867787291, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 6478400027, 1664, 2176, 1664, 4867787291, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 5404658203, 1664, 2176, 1664,
  4867787291, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  4601448987, 1664, 2722400795, 1664, 4601448987, 1664, 2722400795, 1664, 3259271707, 1664, 2722400795, 1664,
  3259271707, 1664, 2722400795, 1664, 4601448987, 1664, 2722400795, 1664, 4601448987, 1664, 2722400795, 1664,
  3259271707, 1664, 2722400795, 1664, 3259271707, 1664, 2722400795, 1664, 2824, 1664, 2824, 1664,
  2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664,
  2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664,
  2824, 1664, 2824, 1664, 4333013531, 1664, 2722400795, 1664, 4869884443, 1664, 2722400795, 1664,
  3259271707, 1664, 2722400795, 1664, 3259271707, 1664, 2722400795, 1664, 5406755355, 1664, 2722400795, 1664,
  4869884443, 1664, 2722400795, 1664, 3259271707, 1664, 2722400795, 1664, 3259271707, 1664, 2722400795, 1664,
  6480497179, 1664, 2722400795, 1664, 4869884443, 1664, 2832, 1664, 3259271707, 1664, 2722400795, 1664,
  3259271707, 1664, 2832, 1664, 5406755355, 1664, 2722400795, 1664, 4869884443, 1664, 2832, 1664,
  2840, 1664, 2840, 1664, 2840, 1664, 2832, 1664, 4328819227, 1664, 4337207835, 1664,
  4865690139, 1664, 4874078747, 1664, 4345596443, 1664, 3263466011, 1664, 4882467355, 1664, 3263466011, 1664,
  5402561051, 1664, 5410949659, 1664, 4865690139, 1664, 4874078747, 1664, 5419338267, 1664, 3263466011, 1664,
  4882467355, 1664, 3263466011, 1664, 19040005, 1664, 6484691483, 1664, 6518245915, 1664, 2832, 1664,
  6493080091, 1664, 3263466011, 1664, 4882467355, 1664, 2832, 1664, 6526634523, 1664, 5410949659, 1664,
  5444504091, 1664, 2832, 1664, 2840, 1664, 2840, 1664, 2840, 1664, 2832, 1664,
  4601481755, 2441415195, 2722433563, 2441415195, 4601481755, 2441415195, 2722433563, 2441415195, 2248, 2248, 2248, 2248,
  2248, 2248, 2248, 2248, 2760, 2760, 2760, 2760, 2760, 2760, 2760, 2760,
  2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2824, 2824, 2824, 2824,
  2824, 2824, 2824, 2824, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248,
  2760, 2760, 2760, 2760, 2760, 2760, 2760, 2760, 2248, 2248, 2248, 2248,
  2248, 2248, 2248, 2248, 4333046299, 2441415195, 2722433563, 2441415195, 4869917211, 2441415195, 2722433563, 2441415195,
  2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 5406788123, 2441415195, 2722433563, 2441415195,
  4869917211, 2768, 2722433563, 2768, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248,
  6480529947, 2441415195, 2722433563, 2441415195, 4869917211, 2441415195, 2832, 2832, 2248, 2248, 2248, 2248,
  2248, 2248, 2248, 2248, 5406788123, 2441415195, 2722433563, 2441415195, 4869917211, 2768, 2832, 2768,
  2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 4328851995, 2172979739, 4337240603, 2709850651,
  4865722907, 2172979739, 4874111515, 2709850651, 4345629211, 3246721563, 3263498779, 2256, 4882500123, 3246721563, 3263498779, 2256,
  5402593819, 2172979739, 5410982427, 2709850651, 4865722907, 2768, 4874111515, 2768, 5419371035, 3246721563, 3263498779, 2256,
  4882500123, 2768, 3263498779, 2256, 109408297, 6467947035, 6484724251, 2709850651, 6518278683, 4857334299, 2832, 2832,
  6493112859, 3246721563, 3263498779, 2256, 4882500123, 3246721563, 2832, 2256, 6526667291, 5394205211, 5410982427, 2709850651,
  5444536859, 2768, 2832, 2768, 2840, 2840, 2840, 2256, 2840, 2768, 2832, 2256,
  4328786459, 4328917531, 4337175067, 4337306139, 4865657371, 4865788443, 4874045979, 4874177051, 76378169, 4345694747, 4345956891, 2256,
  76378137, 4882565659, 4882827803, 2256, 92893241, 5402659355, 88764441, 5411047963, 5444733467, 2768, 5444864539, 2768,
  76116025, 5419436571, 5419698715, 2256, 5444995611, 2768, 4882827803, 2256, 109408313, 105279513, 6484658715, 6484789787,
  6518213147, 6518344219, 2832, 2832, 75853881, 6493178395, 6493440539, 2256, 6518737435, 4882565659, 2832, 2256,
  42299449, 6526732827, 6526994971, 5411047963, 6527519259, 2768, 2832, 2768, 2840, 2840, 2840, 2256,
  2840, 2768, 2832, 2256, 4601482267, 1672, 2184, 1672, 2696, 1672, 2184, 1672,
  2248, 1672, 2184, 1672, 2696, 1672, 2184, 1672, 2760, 1672, 2184, 1672,
  2696, 1672, 2184, 1672, 2248, 1672, 2184, 1672, 2696, 1672, 2184, 1672,
  2824, 1672, 2184, 1672, 2696, 1672, 2184, 1672, 2248, 1672, 2184, 1672,
  2696, 1672, 2184, 1672, 2760, 1672, 2184, 1672, 2696, 1672, 2184, 1672,
  2248, 1672, 2184, 1672, 2696, 1672, 2184, 1672, 4333046811, 1672, 2184, 1672,
  4869917723, 1672, 2184, 1672, 2248, 1672, 2184, 1672, 2248, 1672, 2184, 1672,
  5406788635, 1672, 2184, 1672, 4869917723, 1672, 2184, 1672, 2248, 1672, 2184, 1672,
  2248, 1672, 2184, 1672, 6480530459, 1672, 2184, 1672, 4869917723, 1672, 2184, 1672,
  2248, 1672, 2184, 1672, 2248, 1672, 2184, 1672, 5406788635, 1672, 2184, 1672,
  4869917723, 1672, 2184, 1672, 2248, 1672, 2184, 1672, 2248, 1672, 2184, 1672,
  4328852507, 1672, 4337241115, 1672, 4865723419, 1672, 4874112027, 1672, 4345629723, 1672, 3263499291, 1672,
  4882500635, 1672, 3263499291, 1672, 5402594331, 1672, 5410982939, 1672, 4865723419, 1672, 4874112027, 1672,
  5419371547, 1672, 3263499291, 1672, 4882500635, 1672, 3263499291, 1672, 21169933, 1672, 6484724763, 1672,
  6518279195, 1672, 2832, 1672, 6493113371, 1672, 3263499291, 1672, 4882500635, 1672, 2832, 1672,
  6526667803, 1672, 5410982939, 1672, 5444537371, 1672, 2832, 1672, 2840, 1672, 2840, 1672,
  2840, 1672, 2832, 1672, 4328786971, 4328918043, 4337175579, 4337306651, 4865657883, 4865788955, 4874046491, 4874177563,
  76345401, 4345695259, 4345957403, 2256, 76345369, 4882566171, 4882828315, 2256, 92860473, 5402659867, 86667289, 5411048475,
  5444733979, 2768, 5444865051, 2768, 76083257, 5419437083, 5419699227, 2256, 5444996123, 2768, 4882828315, 2256,
  109375545, 103182361, 6484659227, 6484790299, 6518213659, 6518344731, 2832, 2832, 75821113, 6493178907, 6493441051, 2256,
  6518737947, 4882566171, 2832, 2256, 42266681, 6526733339, 6526995483, 5411048475, 6527519771, 2768, 2832, 2768,
  2840, 2840, 2840, 2256, 2840, 2768, 2832, 2256, 4328785947, 92921977, 109433017, 101041889,
  92923993, 92921945, 84535385, 76158997, 76410937, 74342457, 74338361, 2256, 82606105, 76138177, 74205273, 2256,
  92926009, 92921913, 90863641, 84526753, 92909625, 2768, 84519001, 2768, 76148793, 84678685, 74076217, 2256,
  76132409, 2768, 5445003291, 2256, 109441081, 107378713, 109432889, 101041761, 109424697, 101033569, 2832, 2832,
  75886649, 73818169, 101460005, 2256, 75870265, 6518741019, 2832, 2256, 42332217, 40263737, 42324025, 6526998555,
  101992493, 2768, 2832, 2768, 2840, 2840, 2840, 2256, 2840, 2768, 2832, 2256
]

def table_tf_3 : List Nat := [
  363566888978, 1664, 2176, 1664, 2688, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  2688, 1664, 2176, 1664, 2752, 1664, 2176, 1664, 2688, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 2688, 1664, 2176, 1664, 2816, 1664, 2176, 1664,
  2688, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 2688, 1664, 2176, 1664,
  2752, 1664, 2176, 1664, 2688, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  2688, 1664, 2176, 1664, 363566874858, 1664, 2176, 1664, 156271722698, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 156279980202, 1664, 2176, 1664,
  173191413898, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  173191413866, 1664, 2176, 1664, 173191413834, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 173191413802, 1664, 2176, 1664, 173191413770, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 448136429818, 1664, 2176, 1664,
  380482437338, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  380490694842, 1664, 2176, 1664, 173191413914, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 448136429690, 1664, 2176, 1664, 448069320794, 1664, 2176, 1664,
  2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 173258522682, 1664, 2176, 1664,
  173191413786, 1664, 2176, 1664, 2240, 1664, 2176, 1664, 2240, 1664, 2176, 1664,
  346387013738, 1664, 346353459274, 1664, 312497037386, 1664, 1277680062403215, 1664, 312530591786, 1664, 855575883793671, 1664,
  312484126730, 1664, 855575883793671, 1664, 346319904810, 1664, 346306994186, 1664, 1427459369182535, 1664, 1427459369182535, 1664,
  1420650933750479, 1664, 855575883793671, 1664, 1427459369182535, 1664, 91357530521111068, 1664, 2824, 1664, 2824, 1664,
  2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664,
  2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664, 2824, 1664,
  2824, 1664, 2824, 1664, 498845966442, 1664, 346642538570, 1664, 465023098954, 1664, 346089152586, 1664,
  312819671082, 1664, 855575883792647, 1664, 312819671050, 1664, 855575883794695, 1664, 498845966378, 1664, 346642538506, 1664,
  223968059402, 1664, 346034429962, 1664, 311737671722, 1664, 855575883796743, 1664, 311670562826, 1664, 855575883794695, 1664,
  498845442154, 1664, 361406488650, 1664, 223967535178, 1664, 2832, 1664, 327583621162, 1664, 310663929866, 1664,
  1702199837182215, 1664, 2832, 1664, 190144667690, 1664, 1700000813928711, 1664, 1711150549017927, 1664, 2832, 1664,
  2840, 1664, 2840, 1664, 2840, 1664, 2832, 1664, 363587526778, 1664, 363587526746, 1664,
  329764659290, 1664, 346122707034, 1664, 329764659258, 1664, 295904108570, 1664, 329764659226, 1664, 295354851354, 1664,
  363587526714, 1664, 363587526682, 1664, 380427722778, 1664, 346055598106, 1664, 311771226170, 1664, 294826237978, 1664,
  311704117274, 1664, 1420651206444759, 1664, 498878996602, 1664, 361440043098, 1664, 224001089626, 1664, 2832, 1664,
  327617175610, 1664, 327579492378, 1664, 327545937946, 1664, 2832, 1664, 190178222138, 1664, 190140538906, 1664,
  190106984474, 1664, 2832, 1664, 2840, 1664, 2840, 1664, 2840, 1664, 2832, 1664,
  346517074978, 345980199970, 413609415714, 345980060706, 345980056610, 345980052514, 345980048418, 345980045330, 2248, 2248, 2248, 2248,
  2248, 2248, 2248, 2248, 2760, 2760, 2760, 2760, 2760, 2760, 2760, 2760,
  2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2824, 2824, 2824, 2824,
  2824, 2824, 2824, 2824, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248,
  2760, 2760, 2760, 2760, 2760, 2760, 2760, 2760, 2248, 2248, 2248, 2248,
  2248, 2248, 2248, 2248, 456416653354, 414137806858, 346491809802, 710329898221711, 456416653322, 422056652810, 354410655754, 345980061714,
  2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 388770656298, 345979930770, 346491547658, 710329898225807,
  181538484234, 2768, 1277677898158223, 2768, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248,
  456416129066, 414137282570, 413608888402, 710329898229903, 139259637770, 1273279851651215, 2832, 2832, 2248, 2248, 2248, 2248,
  2248, 2248, 2248, 2248, 181537959978, 147203475474, 138730981394, 710329898225807, 1711151767456591, 2768, 2832, 2768,
  2248, 2248, 2248, 2248, 2248, 2248, 2248, 2248, 405983817770, 311754747914, 363571015690, 294843183114,
  405983817738, 311754616842, 371624079370, 345980135442, 321157951530, 286789986322, 294817984522, 2256, 321157951498, 311723581466, 302871048202, 2256,
  405983555626, 345980004370, 363570753546, 345951068186, 311695863818, 2768, 277470343178, 2768, 337264078890, 311754485770, 302879270930, 2256,
  277478565906, 2768, 1420659796379351, 2256, 109408298, 414439272458, 361423532042, 292695699466, 223984578570, 155256745994, 2832, 2832,
  319010467882, 284642502674, 318989557786, 2256, 310613635082, 284579487770, 2832, 2256, 181571514410, 147203549202, 173208236042, 147174088730,
  181517049882, 2768, 2832, 2768, 2840, 2840, 2840, 2256, 2840, 2768, 2832, 2256,
  380488675386, 405979688986, 473608908826, 439232655386, 380488675354, 380480286746, 371624079386, 346248574994, 76378170, 303973953562, 279126896666, 2256,
  76378138, 311727779866, 310647844890, 2256, 92893242, 405979426842, 88764442, 371586658330, 405929095194, 2768, 371556970522, 2768,
  76116026, 337259950106, 302883434522, 2256, 337209618458, 2768, 302816325658, 2256, 109408314, 105279514, 473608384538, 439232131098,
  473574830106, 439198576666, 2832, 2832, 75853882, 301826469914, 336169431066, 2256, 336135876634, 301759361050, 2832, 2256,
  42299450, 164387516442, 198730477594, 164353962010, 198696923162, 2768, 2832, 2768, 2840, 2840, 2840, 2256,
  2840, 2768, 2832, 2256, 354974857226, 1672, 2184, 1672, 2696, 1672, 2184, 1672,
  2248, 1672, 2184, 1672, 2696, 1672, 2184, 1672, 2760, 1672, 2184, 1672,
  2696, 1672, 2184, 1672, 2248, 1672, 2184, 1672, 2696, 1672, 2184, 1672,
  2824, 1672, 2184, 1672, 2696, 1672, 2184, 1672, 2248, 1672, 2184, 1672,
  2696, 1672, 2184, 1672, 2760, 1672, 2184, 1672, 2696, 1672, 2184, 1672,
  2248, 1672, 2184, 1672, 2696, 1672, 2184, 1672, 448002179322, 1672, 2184, 1672,
  380348186842, 1672, 2184, 1672, 2248, 1672, 2184, 1672, 2248, 1672, 2184, 1672,
  380356444346, 1672, 2184, 1672, 173057163418, 1672, 2184, 1672, 2248, 1672, 2184, 1672,
  2248, 1672, 2184, 1672, 448002179194, 1672, 2184, 1672, 447935070298, 1672, 2184, 1672,
  2248, 1672, 2184, 1672, 2248, 1672, 2184, 1672, 173124272186, 1672, 2184, 1672,
  173057163290, 1672, 2184, 1672, 2248, 1672, 2184, 1672, 2248, 1672, 2184, 1672,
  354972858378, 1672, 354972727306, 1672, 321149859850, 1672, 345988456538, 1672, 321149728778, 1672, 287312076826, 1672,
  321149597706, 1672, 286764883994, 1672, 354972596234, 1672, 354972465162, 1672, 380291407898, 1672, 345921347610, 1672,
  311636975674, 1672, 286236270618, 1672, 311569866778, 1672, 1420659796412119, 1672, 490264328202, 1672, 352825243658, 1672,
  215386290186, 1672, 2832, 1672, 319002245130, 1672, 318987460634, 1672, 318953906202, 1672, 2832, 1672,
  181563291658, 1672, 181548507162, 1672, 181514952730, 1672, 2832, 1672, 2840, 1672, 2840, 1672,
  2840, 1672, 2832, 1672, 346785576970, 346248706058, 413877925898, 439230558234, 338329729034, 380346069018, 371624046618, 346248574986,
  76345402, 303969859594, 303953082378, 2256, 76345370, 311593562138, 278577606682, 2256, 92860474, 346248443914, 86667290, 371584561178,
  346198112266, 2768, 371556937754, 2768, 76083258, 337257852954, 302879340554, 2256, 277478635530, 2768, 302814228506, 2256,
  109375546, 103182362, 413877401610, 439230033946, 413843847178, 439196479514, 2832, 2832, 75821114, 301822375946, 336167333914, 2256,
  276404893706, 301757263898, 2832, 2256, 42266682, 164383422474, 138999494666, 164351864858, 198694826010, 2768, 2832, 2768,
  2840, 2840, 2840, 2256, 2840, 2768, 2832, 2256, 372158920730, 92921978, 109433018, 101041890,
  92923994, 92921946, 84535386, 371621918746, 76410938, 74342458, 74338362, 2256, 82606106, 76138178, 74205274, 2256,
  92926010, 92921914, 90863642, 84526754, 92909626, 2768, 84519002, 2768, 76148794, 337262049306, 74076218, 2256,
  76132410, 2768, 302818424858, 2256, 109441082, 107378714, 109432890, 101041762, 109424698, 101033570, 2832, 2832,
  75886650, 73818170, 336171530266, 2256, 75870266, 301761460250, 2832, 2256, 42332218, 40263738, 42324026, 164356061210,
  198699022362, 2768, 2832, 2768, 2840, 2840, 2840, 2256, 2840, 2768, 2832, 2256
]

def table_a3_2 : List Nat := [
  28681, 35942409, 69496841, 103051273, 69758985, 86536201, 70021129, 84467785, 67186697, 5983902779, 67448841, 7057644603,
  67710985, 5983902779, 70009041, 46600013, 67235849, 7072324667, 67497993, 46600013, 67760137, 46600013, 68022281, 46600013,
  67252233, 5711273019, 67514377, 6785014843, 67776521, 5711273019, 70009057, 46600021, 67301385, 6799694907, 67563529, 46600021,
  67825673, 46600021, 68087817, 46600021, 67317769, 5438643259, 67579913, 6512385083, 67842057, 5438643259, 70009073, 46600013,
  67366921, 6527065147, 67629065, 46600013, 67891209, 46600013, 68153353, 46600013, 100732937, 35938321, 69492753, 103047249,
  5025471547, 5983870011, 5025471547, 78286533, 100749321, 7072291899, 7038737467, 101011465, 5964995643, 100749449, 4891253819, 101011593,
  4757036091, 5711240251, 4757036091, 6650764347, 4757036091, 5711240251, 4757036091, 74092229, 5696560187, 6531226683, 4622818363, 6514449467,
  5696560187, 88542989, 4622818363, 71765773, 6636084283, 6661250107, 6636084283, 103452357, 4488600635, 5438610491, 4488600635, 69897925,
  7575608379, 6527032379, 6501866555, 44502869, 5428124731, 44502869, 4354382907, 44502869, 100790281, 35938329, 69492761, 101052425,
  93199389, 84467737, 70017049, 84467801, 5711469627, 5711207483, 6516775995, 6516513851, 5711469627, 5711207483, 73862925, 73862925,
  7605197883, 6531193915, 6514678843, 6514416699, 88542989, 88542989, 71765773, 71765773, 7586323515, 5438577723, 6512581691, 6512319547,
  5438839867, 5438577723, 59182933, 42405717, 59182933, 6526999611, 59182933, 42405717, 59182933, 42405717, 59182933, 42405717,
  100798473, 35938337, 69492769, 103047265, 4752776251, 5711174715, 4752776251, 74026693, 100814857, 6799596603, 6766042171, 101077001,
  5692300347, 100814985, 4618558523, 101077129, 6631824443, 6661184571, 6631824443, 103386821, 4484340795, 5438544955, 4484340795, 69832389,
  7571348539, 6526966843, 6497606715, 40308557, 5423864891, 40308557, 4350123067, 40308557, 100855817, 35938345, 69492777, 101117961,
  88939549, 84467753, 70017065, 84467817, 7586257979, 5438512187, 6512516155, 6512254011, 5438774331, 5438512187, 54988621, 38211405,
  54988621, 6526934075, 54988621, 38211405, 54988621, 38211405, 54988621, 38211405, 100864009, 35938353, 69492785, 103047281,
  4480080955, 5438479419, 4480080955, 69766853, 100880393, 6526901307, 6493346875, 101142537, 5419605051, 100880521, 4345863227, 101142665,
  100921353, 35938361, 69492793, 101183497, 84679709, 84467769, 70017081, 84467833, 28689, 38039569, 71594001, 105148433,
  71856145, 88633361, 72118289, 84500561, 117522457, 7072291387, 117522521, 44470085, 117522585, 44470085, 117522649, 44470085,
  67252241, 5577022011, 67514385, 6650763835, 67776529, 5577022011, 72106209, 44470101, 50413609, 5440707131, 50413673, 6514448955,
  50413737, 5440707131, 72106217, 44470085, 67334161, 6663346747, 67596305, 44470101, 67858449, 44470101, 68120593, 44470101,
  117522489, 6527031867, 117522553, 44470085, 117522617, 44470085, 117522681, 44470085, 117530649, 38035481, 71589913, 117530713,
  93198941, 84500505, 72114201, 84500569, 5577251387, 5576989243, 6516775483, 6516513339, 5577251387, 5576989243, 73830149, 73830149,
  7588420155, 5440674363, 6514678331, 6514416187, 5440936507, 5440674363, 59150165, 42372949, 7603100219, 6529096251, 6512581179, 6512319035,
  86413061, 86413061, 69635845, 69635845, 59150165, 6526999099, 59150165, 42372949, 59150165, 42372949, 59150165, 42372949,
  100798481, 38035489, 71589921, 105144417, 4750678587, 5576956475, 4750678587, 74026701, 6763944507, 6795401787, 6763944507, 40275781,
  4616460859, 5440641595, 4616460859, 40275781, 100814865, 6663281211, 6629726779, 101077009, 5555984955, 100814993, 4482243131, 101077137,
  7569250875, 6526966331, 6495509051, 40275781, 5421767227, 40275781, 4348025403, 40275781, 16867369, 38035497, 71589929, 105144425,
  4614330939, 5440608827, 4614330939, 71896781, 7602772539, 6529030715, 4480113211, 6512253499, 5553855035, 86413061, 4480113211, 69635845,
  83976233, 6526933563, 6493379131, 83976297, 5419637307, 84500521, 4345895483, 84500585, 100888593, 38035505, 71589937, 101150737,
  86809181, 84500529, 72114225, 84500593, 52858693, 6526900795, 52858693, 36081477, 52858693, 36081477, 52858693, 36081477,
  117530681, 38035513, 71589945, 117530745, 84679261, 84500537, 72114233, 84500601, 28697, 40136729, 73691161, 107245593,
  73953305, 90730521, 74215449, 84533337, 67252249, 5442771003, 67514393, 6516512827, 67776537, 5442771003, 74203361, 42340181,
  67285017, 5440673851, 67547161, 6514415675, 67809305, 5440673851, 74203369, 42340181, 67317785, 5438576699, 67579929, 6512318523,
  67842073, 5438576699, 74203377, 42340181, 67366937, 6526998587, 67629081, 42340181, 67891225, 42340181, 68153369, 42340181,
  100798489, 40132641, 73687073, 107241569, 4748580923, 5442738235, 4748580923, 74026693, 7621679163, 6795401275, 6761846843, 105483981,
  4614363195, 5440641083, 4614363195, 71929549, 7619582011, 6661183547, 6627629115, 103386821, 4480145467, 5438543931, 4480145467, 69832389,
  100814873, 6526965819, 6493411387, 101077017, 5419669563, 100815001, 4345927739, 101077145, 100831257, 40132649, 73687081, 107241577,
  4614330427, 5440608315, 4614330427, 71896781, 7585994811, 5438511163, 4480112699, 6512252987, 4480112699, 5438511163, 4480112699, 35738645574,
  100847641, 6526933051, 6493378619, 101109785, 5419636795, 100847769, 4345894971, 101109913, 100864025, 40132657, 73687089, 107241585,
  4480079931, 5438478395, 4480079931, 69766853, 100880409, 6526900283, 6493345851, 101142553, 5419604027, 100880537, 4345862203, 101142681,
  100921369, 40132665, 73687097, 101183513, 84678685, 84533305, 74211385, 84533369, 28705, 42233889, 75788321, 109342753,
  76050465, 92827681, 76312609, 84566113, 117588009, 6799595067, 117588073, 40210245, 117588137, 40210245, 117588201, 40210245,
  117588017, 6663280187, 117588081, 40210253, 117588145, 40210253, 117588209, 40210253, 117588025, 6526965307, 117588089, 40210245,
  117588153, 40210245, 117588217, 40210245, 117596201, 42229801, 75784233, 117596265, 88938141, 84566057, 76308521, 84566121,
  7603033659, 6529029691, 6512514619, 6512252475, 86347525, 86347525, 69570309, 69570309, 54890317, 6526932539, 54890317, 38113101,
  54890317, 38113101, 54890317, 38113101, 117596209, 42229809, 75784241, 117596273, 86808221, 84566065, 76308529, 84566129,
  52793157, 6526899771, 52793157, 36015941, 52793157, 36015941, 52793157, 36015941, 117596217, 42229817, 75784249, 117596281,
  84678301, 84566073, 76308537, 84566137, 28713, 44331049, 77885481, 111439913, 78147625, 94924841, 78409769, 84598889,
  67317801, 5438510139, 67579945, 6512251963, 67842089, 5438510139, 78397681, 38080333, 67366953, 6526932027, 67629097, 38080333,
  67891241, 38080333, 68153385, 38080333, 100864041, 44326961, 77881393, 111435889, 4480078907, 5438477371, 4480078907, 69766853,
  100880425, 6526899259, 6493344827, 101142569, 5419603003, 100880553, 4345861179, 101142697, 100921385, 44326969, 77881401, 101183529,
  84677661, 84598841, 78405689, 84598905, 28721, 46428209, 79982641, 113537073, 80244785, 97022001, 80506929, 84631665,
  117653561, 6526898747, 117653625, 35950405, 117653689, 35950405, 117653753, 35950405, 117661753, 46424121, 79978553, 117661817,
  84677213, 84631609, 80502841, 84631673, 28729, 48525369, 82079801, 115634233, 82341945, 99119161, 82604089, 84664441
]


set_option maxHeartbeats 2000000 in
theorem check_tf_2 : checkGroups 2 64 tfMask tfTuples table_tf_2 = true := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem check_tf_3 : checkGroups 3 64 tfMask tfTuples table_tf_3 = true := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem check_a3_2 : checkGroups 4 8 a3Mask a3Tuples table_a3_2 = true := by decide +kernel

lemma lookup_block (mode : Nat) (mkMask : Nat → Nat) :
    ∀ (rem sm : Nat) (ws rest : List Nat),
      checkBlock mode mkMask rem sm ws = some rest →
      ∀ j : Nat, j < rem → ∃ w : Nat, validWit (mkMask (sm + j)) w mode = true := by
  intro rem
  induction rem with
  | zero => intro _ _ _ _ j hj; omega
  | succ rem ih =>
    intro sm ws rest h j hj
    cases ws with
    | nil => simp [checkBlock] at h
    | cons w ws' =>
      by_cases hw : validWit (mkMask sm) w mode = true
      · simp only [checkBlock, hw, ite_true] at h
        cases j with
        | zero => exact ⟨w, by simpa using hw⟩
        | succ j' =>
          obtain ⟨w', hw'⟩ := ih (sm + 1) ws' rest h j' (by omega)
          refine ⟨w', ?_⟩
          have hadd : sm + 1 + j' = sm + (j' + 1) := by omega
          rw [hadd] at hw'
          exact hw'
      · simp only [checkBlock, hw, ite_false] at h
        cases h

lemma lookup_groups {α : Type} (mode blockLen : Nat) (mkMask : α → Nat → Nat) :
    ∀ (ts : List α) (ws : List Nat),
      checkGroups mode blockLen mkMask ts ws = true →
      ∀ t ∈ ts, ∀ j : Nat, j < blockLen → ∃ w : Nat, validWit (mkMask t j) w mode = true := by
  intro ts
  induction ts with
  | nil => intro _ _ t ht; cases ht
  | cons t0 ts' ih =>
    intro ws h t ht j hj
    simp only [checkGroups] at h
    cases hb : checkBlock mode (mkMask t0) blockLen 0 ws with
    | none => rw [hb] at h; cases h
    | some rest =>
      rw [hb] at h
      rcases List.mem_cons.mp ht with rfl | hmem
      · obtain ⟨w, hw⟩ := lookup_block mode (mkMask t) blockLen 0 ws rest hb j hj
        rw [Nat.zero_add] at hw
        exact ⟨w, hw⟩
      · exact ih rest h t hmem j hj

lemma hasBit_bitsToNat :
    ∀ (k : Nat) (bs : List Bool) (hk : k < bs.length),
      hasBit (bitsToNat bs) k = bs[k]'hk := by
  intro k
  induction k with
  | zero =>
    intro bs hk
    cases bs with
    | nil => simp at hk
    | cons b bs' =>
      unfold hasBit bitsToNat
      cases b <;> dsimp
      · have h0 : (0 + 2 * bitsToNat bs') % 2 = 0 := by omega
        simp [h0]
      · have h1 : (1 + 2 * bitsToNat bs') % 2 = 1 := by omega
        simp [h1]
  | succ k ih =>
    intro bs hk
    cases bs with
    | nil => simp at hk
    | cons b bs' =>
      have hk' : k < bs'.length := by simp at hk; omega
      have hstep1 : ((if b then 1 else 0) + 2 * bitsToNat bs') / 2 = bitsToNat bs' := by
        cases b <;> dsimp <;> omega
      have hdiv : bitsToNat (b :: bs') / 2 ^ (k + 1) = bitsToNat bs' / 2 ^ k := by
        have hdef : bitsToNat (b :: bs') = (if b then 1 else 0) + 2 * bitsToNat bs' := rfl
        rw [hdef, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.div_div_eq_div_mul, hstep1]
      unfold hasBit
      rw [hdiv]
      simpa [hasBit] using ih bs' hk'

lemma hasEdgeNat_adjMask (adj : Fin 6 → Fin 6 → Bool)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false) :
    ∀ a b : Fin 6, hasEdgeNat (adjMask adj) a.val b.val = adj a b := by
  intro ⟨a, ha⟩ ⟨b, hb⟩
  have hcheck : ∀ i j : Fin 6, i.val < j.val →
      hasBit (adjMask adj) (pairIdx i.val j.val) = adj i j := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    have hij' : i < j := hij
    unfold adjMask
    match i with
    | 0 => match j with
      | 0 => omega
      | 1 => exact hasBit_bitsToNat 0 _ (by simp)
      | 2 => exact hasBit_bitsToNat 1 _ (by simp)
      | 3 => exact hasBit_bitsToNat 2 _ (by simp)
      | 4 => exact hasBit_bitsToNat 3 _ (by simp)
      | 5 => exact hasBit_bitsToNat 4 _ (by simp)
      | _ + 6 => omega
    | 1 => match j with
      | 0 | 1 => omega
      | 2 => exact hasBit_bitsToNat 5 _ (by simp)
      | 3 => exact hasBit_bitsToNat 6 _ (by simp)
      | 4 => exact hasBit_bitsToNat 7 _ (by simp)
      | 5 => exact hasBit_bitsToNat 8 _ (by simp)
      | _ + 6 => omega
    | 2 => match j with
      | 0 | 1 | 2 => omega
      | 3 => exact hasBit_bitsToNat 9 _ (by simp)
      | 4 => exact hasBit_bitsToNat 10 _ (by simp)
      | 5 => exact hasBit_bitsToNat 11 _ (by simp)
      | _ + 6 => omega
    | 3 => match j with
      | 0 | 1 | 2 | 3 => omega
      | 4 => exact hasBit_bitsToNat 12 _ (by simp)
      | 5 => exact hasBit_bitsToNat 13 _ (by simp)
      | _ + 6 => omega
    | 4 => match j with
      | 0 | 1 | 2 | 3 | 4 => omega
      | 5 => exact hasBit_bitsToNat 14 _ (by simp)
      | _ + 6 => omega
    | 5 => omega
    | _ + 6 => omega
  unfold hasEdgeNat
  by_cases hlt : a < b
  · rw [if_pos hlt]
    exact hcheck ⟨a, ha⟩ ⟨b, hb⟩ hlt
  · rw [if_neg hlt]
    by_cases hgt : b < a
    · rw [if_pos hgt, hsymm ⟨a, ha⟩ ⟨b, hb⟩]
      exact hcheck ⟨b, hb⟩ ⟨a, ha⟩ hgt
    · rw [if_neg hgt]
      have heq : a = b := by omega
      subst heq
      rw [hdiag ⟨a, ha⟩]

lemma all6_iff (p : Nat → Bool) : all6 p = true ↔ ∀ u : Fin 6, p u.val = true := by
  constructor
  · intro h ⟨u, hu⟩
    unfold all6 at h
    simp only [Bool.and_eq_true] at h
    match u with
    | 0 => exact h.1.1.1.1.1
    | 1 => exact h.1.1.1.1.2
    | 2 => exact h.1.1.1.2
    | 3 => exact h.1.1.2
    | 4 => exact h.1.2
    | 5 => exact h.2
    | _ + 6 => omega
  · intro h
    unfold all6
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩, h 4⟩, h 5⟩

lemma any6_iff (p : Nat → Bool) : any6 p = true ↔ ∃ u : Fin 6, p u.val = true := by
  constructor
  · intro h
    unfold any6 at h
    simp only [Bool.or_eq_true] at h
    rcases h with ((((h0 | h1) | h2) | h3) | h4) | h5
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
    · exact ⟨3, h3⟩
    · exact ⟨4, h4⟩
    · exact ⟨5, h5⟩
  · rintro ⟨⟨u, hu⟩, hpu⟩
    unfold any6
    simp only [Bool.or_eq_true]
    match u with
    | 0 => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hpu))))
    | 1 => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hpu))))
    | 2 => exact Or.inl (Or.inl (Or.inl (Or.inr hpu)))
    | 3 => exact Or.inl (Or.inl (Or.inr hpu))
    | 4 => exact Or.inl (Or.inr hpu)
    | 5 => exact Or.inr hpu
    | _ + 6 => omega

def ofMask6 (s : Nat) : Finset (Fin 6) :=
  Finset.univ.filter (fun v : Fin 6 => hasBit s v.val = true)

lemma mem_ofMask6 (s : Nat) (v : Fin 6) : v ∈ ofMask6 s ↔ hasBit s v.val = true := by
  unfold ofMask6
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

lemma bit_eq_of_hasBit {a b k : Nat} (h : hasBit a k = hasBit b k) :
    (a / 2 ^ k) % 2 = (b / 2 ^ k) % 2 := by
  unfold hasBit at h
  have ha2 : (a / 2 ^ k) % 2 = 0 ∨ (a / 2 ^ k) % 2 = 1 := by omega
  have hb2 : (b / 2 ^ k) % 2 = 0 ∨ (b / 2 ^ k) % 2 = 1 := by omega
  rcases ha2 with ha0 | ha1 <;> rcases hb2 with hb0 | hb1
  · omega
  · rw [ha0, hb1] at h; cases h
  · rw [ha1, hb0] at h; cases h
  · omega

lemma ofMask6_ne {a b : Nat} (ha : a < 64) (hb : b < 64) (hab : a ≠ b) :
    ofMask6 a ≠ ofMask6 b := by
  intro heq
  apply hab
  have hk : ∀ k : Fin 6, (a / 2 ^ k.val) % 2 = (b / 2 ^ k.val) % 2 := by
    intro k
    apply bit_eq_of_hasBit
    have hmem : k ∈ ofMask6 a ↔ k ∈ ofMask6 b := by rw [heq]
    rw [mem_ofMask6, mem_ofMask6] at hmem
    exact Bool.eq_iff_iff.mpr hmem
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  have h5 := hk 5
  change a / 1 % 2 = b / 1 % 2 at h0
  change a / 2 % 2 = b / 2 % 2 at h1
  change a / 4 % 2 = b / 4 % 2 at h2
  change a / 8 % 2 = b / 8 % 2 at h3
  change a / 16 % 2 = b / 16 % 2 at h4
  change a / 32 % 2 = b / 32 % 2 at h5
  omega

lemma allDistinctAux_pw :
    ∀ xs : List Nat, allDistinctAux xs = true → xs.Pairwise (· ≠ ·) := by
  intro xs
  induction xs with
  | nil => intro _; exact List.Pairwise.nil
  | cons x xs ih =>
    intro h
    simp only [allDistinctAux, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.Pairwise.cons (fun y hy hxy => ?_) (ih h.2)
    subst hxy
    have hmem := List.elem_eq_true_of_mem hy
    rw [h.1] at hmem
    cases hmem

lemma isMISNat_sound (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (s : Nat) (hs : isMISNat (adjMask adj) s = true) :
    isMIS G (ofMask6 s) := by
  rw [isMISNat, all6_iff] at hs
  constructor
  · intro u hu v hv huv
    have hsu := hs u
    rw [mem_ofMask6] at hu hv
    rw [if_pos hu, all6_iff] at hsu
    have hsv := hsu v
    simp only [Bool.or_eq_true, Bool.not_eq_true', hv, Bool.true_eq_false, false_or] at hsv
    rw [hasEdgeNat_adjMask adj hsymm hdiag u v] at hsv
    have htrue := (hadj u v).2 huv
    rw [hsv] at htrue
    cases htrue
  · intro u hu
    have hsu := hs u
    have hnu : hasBit s u.val = false := by
      rw [mem_ofMask6] at hu
      cases hb : hasBit s u.val
      · rfl
      · exact absurd hb hu
    rw [if_neg (by rw [hnu]; exact Bool.false_ne_true), any6_iff] at hsu
    obtain ⟨v, hv⟩ := hsu
    rw [Bool.and_eq_true] at hv
    refine ⟨v, (mem_ofMask6 s v).2 hv.1, (hadj u v).1 ?_⟩
    rw [← hasEdgeNat_adjMask adj hsymm hdiag u v]
    exact hv.2

lemma bicliqueOkNat_sound (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (X Y : Nat) (h : bicliqueOkNat (adjMask adj) X Y = true) :
    ∀ a ∈ ofMask6 X, ∀ b ∈ ofMask6 Y, G.Adj a b := by
  rw [bicliqueOkNat, all6_iff] at h
  intro a ha b hb
  have ha' := h a
  rw [mem_ofMask6] at ha hb
  simp only [Bool.or_eq_true, Bool.not_eq_true', ha, Bool.true_eq_false, false_or] at ha'
  rw [all6_iff] at ha'
  have hb' := ha' b
  simp only [Bool.or_eq_true, Bool.not_eq_true', hb, Bool.true_eq_false, false_or] at hb'
  rw [hasEdgeNat_adjMask adj hsymm hdiag a b] at hb'
  exact (hadj a b).1 hb'

lemma cov2_cover (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (X0 Y0 X1 Y1 : Nat)
    (hb0 : bicliqueOkNat (adjMask adj) X0 Y0 = true)
    (hb1 : bicliqueOkNat (adjMask adj) X1 Y1 = true)
    (hc : cov2OkNat (adjMask adj) X0 Y0 X1 Y1 = true) :
    Cover G 2 ![ofMask6 X0, ofMask6 X1] ![ofMask6 Y0, ofMask6 Y1] := by
  refine ⟨?_, ?_⟩
  · intro i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => exact bicliqueOkNat_sound G adj hadj hsymm hdiag X0 Y0 hb0
    | 1 => exact bicliqueOkNat_sound G adj hadj hsymm hdiag X1 Y1 hb1
    | _ + 2 => omega
  · rw [cov2OkNat, all6_iff] at hc
    have hlt_cov : ∀ a b : Fin 6, a.val < b.val → G.Adj a b →
        (∃ i : Fin 2, (a ∈ ![ofMask6 X0, ofMask6 X1] i ∧ b ∈ ![ofMask6 Y0, ofMask6 Y1] i) ∨
          (b ∈ ![ofMask6 X0, ofMask6 X1] i ∧ a ∈ ![ofMask6 Y0, ofMask6 Y1] i)) := by
      intro a b hablt hadjab
      have h1 := (all6_iff _).1 (hc a) b
      have hltb : decide (a.val < b.val) = true := decide_eq_true hablt
      have heab : hasEdgeNat (adjMask adj) a.val b.val = true := by
        rw [hasEdgeNat_adjMask adj hsymm hdiag a b]
        exact (hadj a b).2 hadjab
      simp only [Bool.or_eq_true, Bool.not_eq_true', hltb, Bool.true_eq_false, heab,
        false_or, Bool.and_eq_true, ← mem_ofMask6] at h1
      rcases h1 with ((⟨ha0, hb0'⟩ | ⟨hb0', ha0⟩) | ⟨ha1, hb1'⟩) | ⟨hb1', ha1⟩
      · exact ⟨0, Or.inl ⟨ha0, hb0'⟩⟩
      · exact ⟨0, Or.inr ⟨hb0', ha0⟩⟩
      · exact ⟨1, Or.inl ⟨ha1, hb1'⟩⟩
      · exact ⟨1, Or.inr ⟨hb1', ha1⟩⟩
    intro a b hadjab
    have hne : a.val ≠ b.val := fun heq => sg_irrefl G _ (by rwa [Fin.ext heq] at hadjab)
    by_cases hlt : a.val < b.val
    · exact hlt_cov a b hlt hadjab
    · obtain ⟨i, hi⟩ := hlt_cov b a (by omega) (sg_symm G hadjab)
      exact ⟨i, hi.symm⟩

lemma cov3_cover (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (X0 Y0 X1 Y1 X2 Y2 : Nat)
    (hb0 : bicliqueOkNat (adjMask adj) X0 Y0 = true)
    (hb1 : bicliqueOkNat (adjMask adj) X1 Y1 = true)
    (hb2 : bicliqueOkNat (adjMask adj) X2 Y2 = true)
    (hc : cov3OkNat (adjMask adj) X0 Y0 X1 Y1 X2 Y2 = true) :
    Cover G 3 ![ofMask6 X0, ofMask6 X1, ofMask6 X2] ![ofMask6 Y0, ofMask6 Y1, ofMask6 Y2] := by
  refine ⟨?_, ?_⟩
  · intro i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => exact bicliqueOkNat_sound G adj hadj hsymm hdiag X0 Y0 hb0
    | 1 => exact bicliqueOkNat_sound G adj hadj hsymm hdiag X1 Y1 hb1
    | 2 => exact bicliqueOkNat_sound G adj hadj hsymm hdiag X2 Y2 hb2
    | _ + 3 => omega
  · rw [cov3OkNat, all6_iff] at hc
    have hlt_cov : ∀ a b : Fin 6, a.val < b.val → G.Adj a b →
        (∃ i : Fin 3, (a ∈ ![ofMask6 X0, ofMask6 X1, ofMask6 X2] i ∧ b ∈ ![ofMask6 Y0, ofMask6 Y1, ofMask6 Y2] i) ∨
          (b ∈ ![ofMask6 X0, ofMask6 X1, ofMask6 X2] i ∧ a ∈ ![ofMask6 Y0, ofMask6 Y1, ofMask6 Y2] i)) := by
      intro a b hablt hadjab
      have h1 := (all6_iff _).1 (hc a) b
      have hltb : decide (a.val < b.val) = true := decide_eq_true hablt
      have heab : hasEdgeNat (adjMask adj) a.val b.val = true := by
        rw [hasEdgeNat_adjMask adj hsymm hdiag a b]
        exact (hadj a b).2 hadjab
      simp only [Bool.or_eq_true, Bool.not_eq_true', hltb, Bool.true_eq_false, heab,
        false_or, Bool.and_eq_true, ← mem_ofMask6] at h1
      rcases h1 with ((((⟨ha0, hb0'⟩ | ⟨hb0', ha0⟩) | ⟨ha1, hb1'⟩) | ⟨hb1', ha1⟩) | ⟨ha2, hb2'⟩) | ⟨hb2', ha2⟩
      · exact ⟨0, Or.inl ⟨ha0, hb0'⟩⟩
      · exact ⟨0, Or.inr ⟨hb0', ha0⟩⟩
      · exact ⟨1, Or.inl ⟨ha1, hb1'⟩⟩
      · exact ⟨1, Or.inr ⟨hb1', ha1⟩⟩
      · exact ⟨2, Or.inl ⟨ha2, hb2'⟩⟩
      · exact ⟨2, Or.inr ⟨hb2', ha2⟩⟩
    intro a b hadjab
    have hne : a.val ≠ b.val := fun heq => sg_irrefl G _ (by rwa [Fin.ext heq] at hadjab)
    by_cases hlt : a.val < b.val
    · exact hlt_cov a b hlt hadjab
    · obtain ⟨i, hi⟩ := hlt_cov b a (by omega) (sg_symm G hadjab)
      exact ⟨i, hi.symm⟩

lemma list_pw_get {α : Type} {R : α → α → Prop} :
    ∀ (xs : List α), xs.Pairwise R →
    ∀ (i j : Nat) (hi : i < xs.length) (hj : j < xs.length), i < j →
      R (xs[i]'hi) (xs[j]'hj) := by
  intro xs h
  induction h with
  | nil => intro i _ hi; simp at hi
  | cons ha hp ih =>
    rename_i a l
    intro i j hi hj hij
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j' => exact ha (l[j']'(by simp at hj; omega)) (List.getElem_mem _)
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' => exact ih i' j' (by simp at hi; omega) (by simp at hj; omega) (by omega)

lemma allDistinctAux_get_ne (xs : List Nat) (h : allDistinctAux xs = true)
    (i j : Fin xs.length) (hij : i ≠ j) : xs[i.val] ≠ xs[j.val] := by
  have hpw := allDistinctAux_pw xs h
  rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact list_pw_get xs hpw i.val j.val i.isLt j.isLt hlt
  · exact absurd (Fin.ext heq) hij
  · exact Ne.symm (list_pw_get xs hpw j.val i.val j.isLt i.isLt hgt)

lemma countHits_ge1 (x : Nat) : ∀ xs : List Nat, 1 ≤ countHits x xs →
    ∃ a : Fin xs.length, hasBit (xs[a.val]'a.isLt) x = true := by
  intro xs h
  induction xs with
  | nil => simp [countHits] at h
  | cons s rest ih =>
    by_cases hs : hasBit s x = true
    · exact ⟨⟨0, by simp⟩, hs⟩
    · have hs0 : hasBit s x = false := Bool.eq_false_iff.mpr hs
      have h1 : 1 ≤ countHits x rest := by simp [countHits, hs0] at h; omega
      obtain ⟨a, ha⟩ := ih h1
      exact ⟨⟨a.val + 1, by simp⟩, ha⟩

lemma countHits_ge2 (x : Nat) : ∀ xs : List Nat, 2 ≤ countHits x xs →
    ∃ a b : Fin xs.length, a ≠ b ∧
      hasBit (xs[a.val]'a.isLt) x = true ∧ hasBit (xs[b.val]'b.isLt) x = true := by
  intro xs h
  induction xs with
  | nil => simp [countHits] at h
  | cons s rest ih =>
    by_cases hs : hasBit s x = true
    · have h1 : 1 ≤ countHits x rest := by simp [countHits, hs] at h; omega
      obtain ⟨b, hb⟩ := countHits_ge1 x rest h1
      exact ⟨⟨0, by simp⟩, ⟨b.val + 1, by simp⟩,
        fun heq => by have hv := congrArg Fin.val heq; dsimp at hv; omega,
        hs, hb⟩
    · have hs0 : hasBit s x = false := Bool.eq_false_iff.mpr hs
      have h2 : 2 ≤ countHits x rest := by simp [countHits, hs0] at h; omega
      obtain ⟨a, b, hab, ha, hb⟩ := ih h2
      exact ⟨⟨a.val + 1, by simp⟩, ⟨b.val + 1, by simp⟩,
        fun heq => hab (Fin.ext (by have hv := congrArg Fin.val heq; dsimp at hv; omega)),
        ha, hb⟩

lemma countHitsPair_ge1 (x y : Nat) : ∀ xs : List Nat, 1 ≤ countHitsPair x y xs →
    ∃ a : Fin xs.length,
      hasBit (xs[a.val]'a.isLt) x = true ∨ hasBit (xs[a.val]'a.isLt) y = true := by
  intro xs h
  induction xs with
  | nil => simp [countHitsPair] at h
  | cons s rest ih =>
    by_cases hs : (hasBit s x || hasBit s y) = true
    · exact ⟨⟨0, by simp⟩, Bool.or_eq_true _ _ |>.mp hs⟩
    · have hs0 : (hasBit s x || hasBit s y) = false := Bool.eq_false_iff.mpr hs
      have h1 : 1 ≤ countHitsPair x y rest := by simp [countHitsPair, hs0] at h; omega
      obtain ⟨a, ha⟩ := ih h1
      exact ⟨⟨a.val + 1, by simp⟩, ha⟩

lemma countHitsPair_ge2 (x y : Nat) : ∀ xs : List Nat, 2 ≤ countHitsPair x y xs →
    ∃ a b : Fin xs.length, a ≠ b ∧
      (hasBit (xs[a.val]'a.isLt) x = true ∨ hasBit (xs[a.val]'a.isLt) y = true) ∧
      (hasBit (xs[b.val]'b.isLt) x = true ∨ hasBit (xs[b.val]'b.isLt) y = true) := by
  intro xs h
  induction xs with
  | nil => simp [countHitsPair] at h
  | cons s rest ih =>
    by_cases hs : (hasBit s x || hasBit s y) = true
    · have h1 : 1 ≤ countHitsPair x y rest := by simp [countHitsPair, hs] at h; omega
      obtain ⟨b, hb⟩ := countHitsPair_ge1 x y rest h1
      exact ⟨⟨0, by simp⟩, ⟨b.val + 1, by simp⟩,
        fun heq => by have hv := congrArg Fin.val heq; dsimp at hv; omega,
        Bool.or_eq_true _ _ |>.mp hs, hb⟩
    · have hs0 : (hasBit s x || hasBit s y) = false := Bool.eq_false_iff.mpr hs
      have h2 : 2 ≤ countHitsPair x y rest := by simp [countHitsPair, hs0] at h; omega
      obtain ⟨a, b, hab, ha, hb⟩ := ih h2
      exact ⟨⟨a.val + 1, by simp⟩, ⟨b.val + 1, by simp⟩,
        fun heq => hab (Fin.ext (by have hv := congrArg Fin.val heq; dsimp at hv; omega)),
        ha, hb⟩

lemma countHitsPair_ge3 (x y : Nat) : ∀ xs : List Nat, 3 ≤ countHitsPair x y xs →
    ∃ a b c : Fin xs.length, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (hasBit (xs[a.val]'a.isLt) x = true ∨ hasBit (xs[a.val]'a.isLt) y = true) ∧
      (hasBit (xs[b.val]'b.isLt) x = true ∨ hasBit (xs[b.val]'b.isLt) y = true) ∧
      (hasBit (xs[c.val]'c.isLt) x = true ∨ hasBit (xs[c.val]'c.isLt) y = true) := by
  intro xs h
  induction xs with
  | nil => simp [countHitsPair] at h
  | cons s rest ih =>
    by_cases hs : (hasBit s x || hasBit s y) = true
    · have h2 : 2 ≤ countHitsPair x y rest := by simp [countHitsPair, hs] at h; omega
      obtain ⟨b, c, hbc, hb, hc⟩ := countHitsPair_ge2 x y rest h2
      exact ⟨⟨0, by simp⟩, ⟨b.val + 1, by simp⟩, ⟨c.val + 1, by simp⟩,
        fun heq => by have hv := congrArg Fin.val heq; dsimp at hv; omega,
        fun heq => by have hv := congrArg Fin.val heq; dsimp at hv; omega,
        fun heq => hbc (Fin.ext (by have hv := congrArg Fin.val heq; dsimp at hv; omega)),
        Bool.or_eq_true _ _ |>.mp hs, hb, hc⟩
    · have hs0 : (hasBit s x || hasBit s y) = false := Bool.eq_false_iff.mpr hs
      have h3 : 3 ≤ countHitsPair x y rest := by simp [countHitsPair, hs0] at h; omega
      obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ := ih h3
      exact ⟨⟨a.val + 1, by simp⟩, ⟨b.val + 1, by simp⟩, ⟨c.val + 1, by simp⟩,
        fun heq => hab (Fin.ext (by have hv := congrArg Fin.val heq; dsimp at hv; omega)),
        fun heq => hac (Fin.ext (by have hv := congrArg Fin.val heq; dsimp at hv; omega)),
        fun heq => hbc (Fin.ext (by have hv := congrArg Fin.val heq; dsimp at hv; omega)),
        ha, hb, hc⟩

lemma anyMissPair_mem (u v : Nat) : ∀ xs : List Nat, anyMissPair u v xs = true →
    ∃ d : Fin xs.length,
      hasBit (xs[d.val]'d.isLt) u ≠ true ∧ hasBit (xs[d.val]'d.isLt) v ≠ true := by
  intro xs h
  induction xs with
  | nil => simp [anyMissPair] at h
  | cons s rest ih =>
    simp only [anyMissPair, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with ⟨hu, hv⟩ | hrest
    · exact ⟨⟨0, by simp⟩, by simp [hu], by simp [hv]⟩
    · obtain ⟨d, hu, hv⟩ := ih hrest
      exact ⟨⟨d.val + 1, by simp⟩, hu, hv⟩

lemma get4_ofMask6 (i0 i1 i2 i3 : Nat) (r : Fin 4) :
    ofMask6 ([i0, i1, i2, i3][r.val]'r.isLt) = ![ofMask6 i0, ofMask6 i1, ofMask6 i2, ofMask6 i3] r := by
  rcases r with ⟨r, hr⟩
  match r with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | _ + 4 => omega

lemma adj_of_hasEdgeNat (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    {u v : Nat} (hu : u < 6) (hv : v < 6)
    (h : hasEdgeNat (adjMask adj) u v = true) :
    G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  rw [hasEdgeNat_adjMask adj hsymm hdiag ⟨u, hu⟩ ⟨v, hv⟩] at h
  exact (hadj ⟨u, hu⟩ ⟨v, hv⟩).1 h

lemma not_adj_of_hasEdgeNat (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    {u v : Nat} (hu : u < 6) (hv : v < 6)
    (h : hasEdgeNat (adjMask adj) u v = false) :
    ¬ G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  rw [hasEdgeNat_adjMask adj hsymm hdiag ⟨u, hu⟩ ⟨v, hv⟩] at h
  intro hadjv
  have ht := (hadj ⟨u, hu⟩ ⟨v, hv⟩).2 hadjv
  rw [ht] at h
  cases h

lemma contra_mis_list (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (C : AndCountCircuit 6) (hfit : Fits G C)
    (xs : List Nat) (hpow : 2 ^ C.size < xs.length)
    (hlt : ∀ r : Fin xs.length, xs[r.val]'r.isLt < 64)
    (hmis : ∀ r : Fin xs.length, isMISNat (adjMask adj) (xs[r.val]'r.isLt) = true)
    (hdist : allDistinctAux xs = true) : False := by
  let M : Fin xs.length → Finset (Fin 6) := fun r => ofMask6 (xs[r.val]'r.isLt)
  have hfb := family_bound G C hfit M
    (fun r => isMISNat_sound G adj hadj hsymm hdiag _ (hmis r))
    (fun a b hab => ofMask6_ne (hlt a) (hlt b) (allDistinctAux_get_ne xs hdist a b hab))
  omega

lemma use_wit_tag1 (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (C : AndCountCircuit 6) (hle : 2 ≤ C.size) (w : Nat)
    (hb : bicliqueOkNat (adjMask adj) ((w / 8) % 64) ((w / 512) % 64) = true ∧
          bicliqueOkNat (adjMask adj) ((w / 32768) % 64) ((w / 2097152) % 64) = true ∧
          cov2OkNat (adjMask adj) ((w / 8) % 64) ((w / 512) % 64) ((w / 32768) % 64) ((w / 2097152) % 64) = true) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y :=
  ⟨2, ![ofMask6 ((w / 8) % 64), ofMask6 ((w / 32768) % 64)],
      ![ofMask6 ((w / 512) % 64), ofMask6 ((w / 2097152) % 64)], hle,
      cov2_cover G adj hadj hsymm hdiag _ _ _ _ hb.1 hb.2.1 hb.2.2⟩

lemma use_wit_tag3 (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (C : AndCountCircuit 6) (hfit : Fits G C) (hsz : C.size = 2) (w : Nat)
    (hm : isMISNat (adjMask adj) ((w / 8) % 64) = true ∧
          isMISNat (adjMask adj) ((w / 512) % 64) = true ∧
          isMISNat (adjMask adj) ((w / 32768) % 64) = true ∧
          isMISNat (adjMask adj) ((w / 2097152) % 64) = true ∧
          isMISNat (adjMask adj) ((w / 134217728) % 64) = true ∧
          allDistinctAux [(w / 8) % 64, (w / 512) % 64, (w / 32768) % 64, (w / 2097152) % 64, (w / 134217728) % 64] = true) :
    False := by
  let xs := [(w / 8) % 64, (w / 512) % 64, (w / 32768) % 64, (w / 2097152) % 64, (w / 134217728) % 64]
  apply contra_mis_list G adj hadj hsymm hdiag C hfit xs (by simp [xs, hsz])
  · intro ⟨r, hr⟩
    match r with
    | 0 => exact Nat.mod_lt _ (by decide)
    | 1 => exact Nat.mod_lt _ (by decide)
    | 2 => exact Nat.mod_lt _ (by decide)
    | 3 => exact Nat.mod_lt _ (by decide)
    | 4 => exact Nat.mod_lt _ (by decide)
    | _ + 5 => simp [xs] at hr
  · intro ⟨r, hr⟩
    match r with
    | 0 => exact hm.1
    | 1 => exact hm.2.1
    | 2 => exact hm.2.2.1
    | 3 => exact hm.2.2.2.1
    | 4 => exact hm.2.2.2.2.1
    | _ + 5 => simp [xs] at hr
  · exact hm.2.2.2.2.2

lemma use_wit_tag5 (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (C : AndCountCircuit 6) (hfit : Fits G C) (hout : C.outVars = ∅) (hsz : C.size = 2) (w : Nat)
    (hv : (w / 8) % 8 < 6) (hwn : (w / 64) % 8 < 6)
    (he : hasEdgeNat (adjMask adj) ((w / 8) % 8) ((w / 64) % 8) = true)
    (hm0 : isMISNat (adjMask adj) ((w / 512) % 64) = true) (hb0 : hasBit ((w / 512) % 64) ((w / 8) % 8) = true)
    (hm1 : isMISNat (adjMask adj) ((w / 32768) % 64) = true) (hb1 : hasBit ((w / 32768) % 64) ((w / 8) % 8) = true)
    (hm2 : isMISNat (adjMask adj) ((w / 2097152) % 64) = true) (hb2 : hasBit ((w / 2097152) % 64) ((w / 8) % 8) = true)
    (hdist : allDistinctAux [(w / 512) % 64, (w / 32768) % 64, (w / 2097152) % 64] = true) :
    False := by
  let xs := [(w / 512) % 64, (w / 32768) % 64, (w / 2097152) % 64]
  let M : Fin 3 → Finset (Fin 6) := fun r => ofMask6 (xs[r.val]'r.isLt)
  apply contra_noniso_c3 G C hfit hout hsz (adj_of_hasEdgeNat G adj hadj hsymm hdiag hv hwn he) M
  · intro ⟨r, hr⟩
    match r with
    | 0 => exact isMISNat_sound G adj hadj hsymm hdiag _ hm0
    | 1 => exact isMISNat_sound G adj hadj hsymm hdiag _ hm1
    | 2 => exact isMISNat_sound G adj hadj hsymm hdiag _ hm2
    | _ + 3 => omega
  · intro a b hab
    apply ofMask6_ne
    · rcases a with ⟨a, ha⟩; match a with | 0 => exact Nat.mod_lt _ (by decide) | 1 => exact Nat.mod_lt _ (by decide) | 2 => exact Nat.mod_lt _ (by decide) | _ + 3 => omega
    · rcases b with ⟨b, hb⟩; match b with | 0 => exact Nat.mod_lt _ (by decide) | 1 => exact Nat.mod_lt _ (by decide) | 2 => exact Nat.mod_lt _ (by decide) | _ + 3 => omega
    · exact allDistinctAux_get_ne xs hdist a b hab
  · intro ⟨r, hr⟩
    rw [mem_ofMask6]
    match r with
    | 0 => exact hb0
    | 1 => exact hb1
    | 2 => exact hb2
    | _ + 3 => omega

lemma use_wit_tag6 (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (C : AndCountCircuit 6) (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (hsz : C.size = 2) (w : Nat)
    (hu6 : (w / 8) % 8 < 6) (hv6 : (w / 64) % 8 < 6) (hw6 : (w / 512) % 8 < 6)
    (_huv : (w / 8) % 8 ≠ (w / 64) % 8) (_huw : (w / 8) % 8 ≠ (w / 512) % 8) (_hvw : (w / 64) % 8 ≠ (w / 512) % 8)
    (huN : any6 (hasEdgeNat (adjMask adj) ((w / 8) % 8)) = true)
    (hvN : any6 (hasEdgeNat (adjMask adj) ((w / 64) % 8)) = true)
    (hwN : any6 (hasEdgeNat (adjMask adj) ((w / 512) % 8)) = true)
    (hm0 : isMISNat (adjMask adj) ((w / 4096) % 64) = true)
    (hm1 : isMISNat (adjMask adj) ((w / 262144) % 64) = true)
    (hm2 : isMISNat (adjMask adj) ((w / 16777216) % 64) = true)
    (hm3 : isMISNat (adjMask adj) ((w / 1073741824) % 64) = true)
    (hdist : allDistinctAux [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] = true)
    (hcu : 2 ≤ countHits ((w / 8) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64])
    (hcv : 2 ≤ countHits ((w / 64) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64])
    (hcw : 2 ≤ countHits ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64])
    (hcuv : 3 ≤ countHitsPair ((w / 8) % 8) ((w / 64) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64])
    (hmuv : anyMissPair ((w / 8) % 8) ((w / 64) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] = true)
    (hcuw : 3 ≤ countHitsPair ((w / 8) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64])
    (hmuw : anyMissPair ((w / 8) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] = true)
    (hcvw : 3 ≤ countHitsPair ((w / 64) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64])
    (hmvw : anyMissPair ((w / 64) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] = true) :
    False := by
  let u := (w / 8) % 8
  let v := (w / 64) % 8
  let wv := (w / 512) % 8
  let i0 := (w / 4096) % 64
  let i1 := (w / 262144) % 64
  let i2 := (w / 16777216) % 64
  let i3 := (w / 1073741824) % 64
  let xs := [i0, i1, i2, i3]
  let I0 := ofMask6 i0
  let I1 := ofMask6 i1
  let I2 := ofMask6 i2
  let I3 := ofMask6 i3
  have hasN : ∀ x (hx : x < 6), any6 (hasEdgeNat (adjMask adj) x) = true → ∃ y : Fin 6, G.Adj ⟨x, hx⟩ y := by
    intro x hx hany
    rw [any6_iff] at hany
    obtain ⟨y, hy⟩ := hany
    exact ⟨y, adj_of_hasEdgeNat G adj hadj hsymm hdiag hx y.isLt hy⟩
  have hhit2 : ∀ x (hx : x < 6), 2 ≤ countHits x xs →
      ∃ a b : Fin 4, a ≠ b ∧ ⟨x, hx⟩ ∈ ![I0, I1, I2, I3] a ∧ ⟨x, hx⟩ ∈ ![I0, I1, I2, I3] b := by
    intro x hx hcnt
    obtain ⟨a, b, hab, ha, hb⟩ := countHits_ge2 x xs hcnt
    refine ⟨a, b, hab, ?_, ?_⟩
    · rw [← get4_ofMask6 i0 i1 i2 i3 a, mem_ofMask6]; exact ha
    · rw [← get4_ofMask6 i0 i1 i2 i3 b, mem_ofMask6]; exact hb
  have hhit3 : ∀ x y (hx : x < 6) (hy : y < 6), 3 ≤ countHitsPair x y xs →
      ∃ a b c : Fin 4, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        (⟨x, hx⟩ ∈ ![I0, I1, I2, I3] a ∨ ⟨y, hy⟩ ∈ ![I0, I1, I2, I3] a) ∧
        (⟨x, hx⟩ ∈ ![I0, I1, I2, I3] b ∨ ⟨y, hy⟩ ∈ ![I0, I1, I2, I3] b) ∧
        (⟨x, hx⟩ ∈ ![I0, I1, I2, I3] c ∨ ⟨y, hy⟩ ∈ ![I0, I1, I2, I3] c) := by
    intro x y hx hy hcnt
    obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ := countHitsPair_ge3 x y xs hcnt
    refine ⟨a, b, c, hab, hac, hbc, ?_, ?_, ?_⟩
    · rcases ha with ha | ha <;> [left; right] <;> rw [← get4_ofMask6 i0 i1 i2 i3 a, mem_ofMask6] <;> exact ha
    · rcases hb with hb | hb <;> [left; right] <;> rw [← get4_ofMask6 i0 i1 i2 i3 b, mem_ofMask6] <;> exact hb
    · rcases hc with hc | hc <;> [left; right] <;> rw [← get4_ofMask6 i0 i1 i2 i3 c, mem_ofMask6] <;> exact hc
  have hmiss : ∀ x y (hx : x < 6) (hy : y < 6), anyMissPair x y xs = true →
      ∃ d : Fin 4, ⟨x, hx⟩ ∉ ![I0, I1, I2, I3] d ∧ ⟨y, hy⟩ ∉ ![I0, I1, I2, I3] d := by
    intro x y hx hy hany
    obtain ⟨d, hdx, hdy⟩ := anyMissPair_mem x y xs hany
    refine ⟨d, ?_, ?_⟩
    · rw [← get4_ofMask6 i0 i1 i2 i3 d, mem_ofMask6]; exact hdx
    · rw [← get4_ofMask6 i0 i1 i2 i3 d, mem_ofMask6]; exact hdy
  apply contra_sun_c2 G C hfit hout hdisj hsz ⟨u, hu6⟩ ⟨v, hv6⟩ ⟨wv, hw6⟩
    (hasN u hu6 huN) (hasN v hv6 hvN) (hasN wv hw6 hwN) I0 I1 I2 I3
  · intro ⟨r, hr⟩
    match r with
    | 0 => exact isMISNat_sound G adj hadj hsymm hdiag _ hm0
    | 1 => exact isMISNat_sound G adj hadj hsymm hdiag _ hm1
    | 2 => exact isMISNat_sound G adj hadj hsymm hdiag _ hm2
    | 3 => exact isMISNat_sound G adj hadj hsymm hdiag _ hm3
    | _ + 4 => omega
  · intro a b hab
    rw [← get4_ofMask6 i0 i1 i2 i3 a, ← get4_ofMask6 i0 i1 i2 i3 b]
    apply ofMask6_ne
    · rcases a with ⟨a, ha⟩; match a with | 0 => exact Nat.mod_lt _ (by decide) | 1 => exact Nat.mod_lt _ (by decide) | 2 => exact Nat.mod_lt _ (by decide) | 3 => exact Nat.mod_lt _ (by decide) | _ + 4 => omega
    · rcases b with ⟨b, hb⟩; match b with | 0 => exact Nat.mod_lt _ (by decide) | 1 => exact Nat.mod_lt _ (by decide) | 2 => exact Nat.mod_lt _ (by decide) | 3 => exact Nat.mod_lt _ (by decide) | _ + 4 => omega
    · exact allDistinctAux_get_ne xs hdist a b hab
  · exact hhit2 u hu6 hcu
  · exact hhit2 v hv6 hcv
  · exact hhit2 wv hw6 hcw
  · exact hhit3 u v hu6 hv6 hcuv
  · exact hmiss u v hu6 hv6 hmuv
  · exact hhit3 u wv hu6 hw6 hcuw
  · exact hmiss u wv hu6 hw6 hmuw
  · exact hhit3 v wv hv6 hw6 hcvw
  · exact hmiss v wv hv6 hw6 hmvw

lemma use_validWit_tf2 (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (C : AndCountCircuit 6) (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (hsz : C.size = 2)
    (hno3 : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj b c ∨ G.Adj a c)
    (w : Nat) (hw : validWit (adjMask adj) w 2 = true) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y := by
  have hmod : w % 8 < 8 := Nat.mod_lt w (by decide)
  match ht : w % 8 with
  | 0 =>
    exfalso
    simp only [validWit, ht] at hw
    change decide ((w / 8) % 8 < (w / 64) % 8) && decide ((w / 64) % 8 < (w / 512) % 8) &&
      decide ((w / 512) % 8 < 6) &&
      !(hasEdgeNat (adjMask adj) ((w / 8) % 8) ((w / 64) % 8)) &&
      !(hasEdgeNat (adjMask adj) ((w / 64) % 8) ((w / 512) % 8)) &&
      !(hasEdgeNat (adjMask adj) ((w / 8) % 8) ((w / 512) % 8)) = true at hw
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_iff] at hw
    rcases hw with ⟨⟨⟨⟨⟨hab, hbc⟩, hc6⟩, heab⟩, hebc⟩, heac⟩
    have ha6 : (w / 8) % 8 < 6 := by omega
    have hb6 : (w / 64) % 8 < 6 := by omega
    rcases hno3 ⟨(w / 8) % 8, ha6⟩ ⟨(w / 64) % 8, hb6⟩ ⟨(w / 512) % 8, hc6⟩
      (fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega)
      (fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega)
      (fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega) with h | h | h
    · exact not_adj_of_hasEdgeNat G adj hadj hsymm hdiag ha6 hb6 heab h
    · exact not_adj_of_hasEdgeNat G adj hadj hsymm hdiag hb6 hc6 hebc h
    · exact not_adj_of_hasEdgeNat G adj hadj hsymm hdiag ha6 hc6 heac h
  | 1 =>
    simp only [validWit, ht] at hw
    change bicliqueOkNat (adjMask adj) ((w / 8) % 64) ((w / 512) % 64) &&
      bicliqueOkNat (adjMask adj) ((w / 32768) % 64) ((w / 2097152) % 64) &&
      cov2OkNat (adjMask adj) ((w / 8) % 64) ((w / 512) % 64) ((w / 32768) % 64) ((w / 2097152) % 64) = true at hw
    rw [Bool.and_eq_true, Bool.and_eq_true] at hw
    exact use_wit_tag1 G adj hadj hsymm hdiag C (by omega) w ⟨hw.1.1, hw.1.2, hw.2⟩
  | 2 => simp only [validWit, ht] at hw; cases hw
  | 3 =>
    exfalso
    simp only [validWit, ht] at hw
    change isMISNat (adjMask adj) ((w / 8) % 64) && isMISNat (adjMask adj) ((w / 512) % 64) &&
      isMISNat (adjMask adj) ((w / 32768) % 64) && isMISNat (adjMask adj) ((w / 2097152) % 64) &&
      isMISNat (adjMask adj) ((w / 134217728) % 64) &&
      allDistinctAux [(w / 8) % 64, (w / 512) % 64, (w / 32768) % 64, (w / 2097152) % 64, (w / 134217728) % 64] = true at hw
    simp only [Bool.and_eq_true] at hw
    exact use_wit_tag3 G adj hadj hsymm hdiag C hfit hsz w ⟨hw.1.1.1.1.1, hw.1.1.1.1.2, hw.1.1.1.2, hw.1.1.2, hw.1.2, hw.2⟩
  | 4 => simp only [validWit, ht] at hw; cases hw
  | 5 =>
    exfalso
    simp only [validWit, ht] at hw
    change (w / 8) % 8 < 6 && (w / 64) % 8 < 6 && hasEdgeNat (adjMask adj) ((w / 8) % 8) ((w / 64) % 8) &&
      isMISNat (adjMask adj) ((w / 512) % 64) && hasBit ((w / 512) % 64) ((w / 8) % 8) &&
      isMISNat (adjMask adj) ((w / 32768) % 64) && hasBit ((w / 32768) % 64) ((w / 8) % 8) &&
      isMISNat (adjMask adj) ((w / 2097152) % 64) && hasBit ((w / 2097152) % 64) ((w / 8) % 8) &&
      allDistinctAux [(w / 512) % 64, (w / 32768) % 64, (w / 2097152) % 64] = true at hw
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hw
    exact use_wit_tag5 G adj hadj hsymm hdiag C hfit hout hsz w
      hw.1.1.1.1.1.1.1.1.1 hw.1.1.1.1.1.1.1.1.2 hw.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.2 hw.1.1.1.1.1.2 hw.1.1.1.1.2 hw.1.1.1.2 hw.1.1.2 hw.1.2 hw.2
  | 6 =>
    exfalso
    simp only [validWit, ht] at hw
    change (w / 8) % 8 < 6 && (w / 64) % 8 < 6 && (w / 512) % 8 < 6 &&
      (w / 8) % 8 != (w / 64) % 8 && (w / 8) % 8 != (w / 512) % 8 && (w / 64) % 8 != (w / 512) % 8 &&
      any6 (hasEdgeNat (adjMask adj) ((w / 8) % 8)) &&
      any6 (hasEdgeNat (adjMask adj) ((w / 64) % 8)) &&
      any6 (hasEdgeNat (adjMask adj) ((w / 512) % 8)) &&
      isMISNat (adjMask adj) ((w / 4096) % 64) && isMISNat (adjMask adj) ((w / 262144) % 64) &&
      isMISNat (adjMask adj) ((w / 16777216) % 64) && isMISNat (adjMask adj) ((w / 1073741824) % 64) &&
      allDistinctAux [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      2 <= countHits ((w / 8) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      2 <= countHits ((w / 64) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      2 <= countHits ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      3 <= countHitsPair ((w / 8) % 8) ((w / 64) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      anyMissPair ((w / 8) % 8) ((w / 64) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      3 <= countHitsPair ((w / 8) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      anyMissPair ((w / 8) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      3 <= countHitsPair ((w / 64) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      anyMissPair ((w / 64) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] = true at hw
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_iff] at hw
    exact use_wit_tag6 G adj hadj hsymm hdiag C hfit hout hdisj hsz w
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.2
      hw.1.1.1.1.1.2
      hw.1.1.1.1.2
      hw.1.1.1.2
      hw.1.1.2
      hw.1.2
      hw.2
  | 7 => simp only [validWit, ht] at hw; cases hw
  | _ + 8 => omega

lemma use_validWit_a3 (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (C : AndCountCircuit 6) (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (hsz : C.size = 2) (w : Nat) (hw : validWit (adjMask adj) w 4 = true) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y := by
  have hmod : w % 8 < 8 := Nat.mod_lt w (by decide)
  match ht : w % 8 with
  | 0 => simp only [validWit, ht] at hw; cases hw
  | 1 =>
    simp only [validWit, ht] at hw
    change bicliqueOkNat (adjMask adj) ((w / 8) % 64) ((w / 512) % 64) &&
      bicliqueOkNat (adjMask adj) ((w / 32768) % 64) ((w / 2097152) % 64) &&
      cov2OkNat (adjMask adj) ((w / 8) % 64) ((w / 512) % 64) ((w / 32768) % 64) ((w / 2097152) % 64) = true at hw
    rw [Bool.and_eq_true, Bool.and_eq_true] at hw
    exact use_wit_tag1 G adj hadj hsymm hdiag C (by omega) w ⟨hw.1.1, hw.1.2, hw.2⟩
  | 2 => simp only [validWit, ht] at hw; cases hw
  | 3 =>
    exfalso
    simp only [validWit, ht] at hw
    change isMISNat (adjMask adj) ((w / 8) % 64) && isMISNat (adjMask adj) ((w / 512) % 64) &&
      isMISNat (adjMask adj) ((w / 32768) % 64) && isMISNat (adjMask adj) ((w / 2097152) % 64) &&
      isMISNat (adjMask adj) ((w / 134217728) % 64) &&
      allDistinctAux [(w / 8) % 64, (w / 512) % 64, (w / 32768) % 64, (w / 2097152) % 64, (w / 134217728) % 64] = true at hw
    simp only [Bool.and_eq_true] at hw
    exact use_wit_tag3 G adj hadj hsymm hdiag C hfit hsz w ⟨hw.1.1.1.1.1, hw.1.1.1.1.2, hw.1.1.1.2, hw.1.1.2, hw.1.2, hw.2⟩
  | 4 => simp only [validWit, ht] at hw; cases hw
  | 5 =>
    exfalso
    simp only [validWit, ht] at hw
    change (w / 8) % 8 < 6 && (w / 64) % 8 < 6 && hasEdgeNat (adjMask adj) ((w / 8) % 8) ((w / 64) % 8) &&
      isMISNat (adjMask adj) ((w / 512) % 64) && hasBit ((w / 512) % 64) ((w / 8) % 8) &&
      isMISNat (adjMask adj) ((w / 32768) % 64) && hasBit ((w / 32768) % 64) ((w / 8) % 8) &&
      isMISNat (adjMask adj) ((w / 2097152) % 64) && hasBit ((w / 2097152) % 64) ((w / 8) % 8) &&
      allDistinctAux [(w / 512) % 64, (w / 32768) % 64, (w / 2097152) % 64] = true at hw
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hw
    exact use_wit_tag5 G adj hadj hsymm hdiag C hfit hout hsz w
      hw.1.1.1.1.1.1.1.1.1 hw.1.1.1.1.1.1.1.1.2 hw.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.2 hw.1.1.1.1.1.2 hw.1.1.1.1.2 hw.1.1.1.2 hw.1.1.2 hw.1.2 hw.2
  | 6 =>
    exfalso
    simp only [validWit, ht] at hw
    change (w / 8) % 8 < 6 && (w / 64) % 8 < 6 && (w / 512) % 8 < 6 &&
      (w / 8) % 8 != (w / 64) % 8 && (w / 8) % 8 != (w / 512) % 8 && (w / 64) % 8 != (w / 512) % 8 &&
      any6 (hasEdgeNat (adjMask adj) ((w / 8) % 8)) &&
      any6 (hasEdgeNat (adjMask adj) ((w / 64) % 8)) &&
      any6 (hasEdgeNat (adjMask adj) ((w / 512) % 8)) &&
      isMISNat (adjMask adj) ((w / 4096) % 64) && isMISNat (adjMask adj) ((w / 262144) % 64) &&
      isMISNat (adjMask adj) ((w / 16777216) % 64) && isMISNat (adjMask adj) ((w / 1073741824) % 64) &&
      allDistinctAux [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      2 <= countHits ((w / 8) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      2 <= countHits ((w / 64) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      2 <= countHits ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      3 <= countHitsPair ((w / 8) % 8) ((w / 64) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      anyMissPair ((w / 8) % 8) ((w / 64) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      3 <= countHitsPair ((w / 8) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      anyMissPair ((w / 8) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      3 <= countHitsPair ((w / 64) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] &&
      anyMissPair ((w / 64) % 8) ((w / 512) % 8) [(w / 4096) % 64, (w / 262144) % 64, (w / 16777216) % 64, (w / 1073741824) % 64] = true at hw
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_iff] at hw
    exact use_wit_tag6 G adj hadj hsymm hdiag C hfit hout hdisj hsz w
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.1.2
      hw.1.1.1.1.1.1.2
      hw.1.1.1.1.1.2
      hw.1.1.1.1.2
      hw.1.1.1.2
      hw.1.1.2
      hw.1.2
      hw.2
  | 7 => simp only [validWit, ht] at hw; cases hw
  | _ + 8 => omega

lemma use_validWit_tf3 (G : SimpleGraph (Fin 6)) (adj : Fin 6 → Fin 6 → Bool)
    (hadj : ∀ a b : Fin 6, adj a b = true ↔ G.Adj a b)
    (hsymm : ∀ a b : Fin 6, adj a b = adj b a) (hdiag : ∀ a : Fin 6, adj a a = false)
    (C : AndCountCircuit 6) (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (hsz : C.size = 3) (w : Nat) (hw : validWit (adjMask adj) w 3 = true) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y := by
  have hmod : w % 8 < 8 := Nat.mod_lt w (by decide)
  match ht : w % 8 with
  | 0 =>
    simp only [validWit, ht] at hw
    change decide ((w / 8) % 8 < (w / 64) % 8) && decide ((w / 64) % 8 < (w / 512) % 8) &&
      decide ((w / 512) % 8 < 6) &&
      !(hasEdgeNat (adjMask adj) ((w / 8) % 8) ((w / 64) % 8)) &&
      !(hasEdgeNat (adjMask adj) ((w / 64) % 8) ((w / 512) % 8)) &&
      !(hasEdgeNat (adjMask adj) ((w / 8) % 8) ((w / 512) % 8)) = true at hw
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_iff] at hw
    rcases hw with ⟨⟨⟨⟨⟨hab, hbc⟩, hc6⟩, heab⟩, hebc⟩, heac⟩
    have ha6 : (w / 8) % 8 < 6 := by omega
    have hb6 : (w / 64) % 8 < 6 := by omega
    let fa : Fin 6 := ⟨(w / 8) % 8, ha6⟩
    let fb : Fin 6 := ⟨(w / 64) % 8, hb6⟩
    let fc : Fin 6 := ⟨(w / 512) % 8, hc6⟩
    let S : Finset (Fin 6) := {fa, fb, fc}
    have hnab : fa ≠ fb := fun h => by have hv := congrArg Fin.val h; dsimp [fa, fb] at hv; omega
    have hnac : fa ≠ fc := fun h => by have hv := congrArg Fin.val h; dsimp [fa, fc] at hv; omega
    have hnbc : fb ≠ fc := fun h => by have hv := congrArg Fin.val h; dsimp [fb, fc] at hv; omega
    have hS : isIndep G S := isIndep_triple G fa fb fc
      (not_adj_of_hasEdgeNat G adj hadj hsymm hdiag ha6 hb6 heab)
      (not_adj_of_hasEdgeNat G adj hadj hsymm hdiag ha6 hc6 heac)
      (not_adj_of_hasEdgeNat G adj hadj hsymm hdiag hb6 hc6 hebc)
    have hcard : S.card = 3 := by
      have h1 : fa ∉ ({fb, fc} : Finset (Fin 6)) := by simp [hnab, hnac]
      have h2 : fb ∉ ({fc} : Finset (Fin 6)) := by simp [hnbc]
      rw [show S = insert fa (insert fb {fc}) from rfl,
        Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_singleton]
    obtain ⟨k, X, Y, hk, hcov⟩ := bc_of_indep_card G S hS
    exact ⟨k, X, Y, by rw [hcard] at hk; omega, hcov⟩
  | 1 =>
    simp only [validWit, ht] at hw
    change bicliqueOkNat (adjMask adj) ((w / 8) % 64) ((w / 512) % 64) &&
      bicliqueOkNat (adjMask adj) ((w / 32768) % 64) ((w / 2097152) % 64) &&
      cov2OkNat (adjMask adj) ((w / 8) % 64) ((w / 512) % 64) ((w / 32768) % 64) ((w / 2097152) % 64) = true at hw
    rw [Bool.and_eq_true, Bool.and_eq_true] at hw
    exact use_wit_tag1 G adj hadj hsymm hdiag C (by omega) w ⟨hw.1.1, hw.1.2, hw.2⟩
  | 2 =>
    simp only [validWit, ht] at hw
    change bicliqueOkNat (adjMask adj) ((w / 8) % 64) ((w / 512) % 64) &&
      bicliqueOkNat (adjMask adj) ((w / 32768) % 64) ((w / 2097152) % 64) &&
      bicliqueOkNat (adjMask adj) ((w / 134217728) % 64) ((w / 8589934592) % 64) &&
      cov3OkNat (adjMask adj) ((w / 8) % 64) ((w / 512) % 64) ((w / 32768) % 64) ((w / 2097152) % 64)
        ((w / 134217728) % 64) ((w / 8589934592) % 64) = true at hw
    simp only [Bool.and_eq_true] at hw
    exact ⟨3, ![ofMask6 ((w / 8) % 64), ofMask6 ((w / 32768) % 64), ofMask6 ((w / 134217728) % 64)],
      ![ofMask6 ((w / 512) % 64), ofMask6 ((w / 2097152) % 64), ofMask6 ((w / 8589934592) % 64)],
      by omega,
      cov3_cover G adj hadj hsymm hdiag _ _ _ _ _ _ hw.1.1.1 hw.1.1.2 hw.1.2 hw.2⟩
  | 3 => simp only [validWit, ht] at hw; cases hw
  | 4 =>
    exfalso
    simp only [validWit, ht] at hw
    change isMISNat (adjMask adj) ((w / 8) % 64) && isMISNat (adjMask adj) ((w / 512) % 64) &&
      isMISNat (adjMask adj) ((w / 32768) % 64) && isMISNat (adjMask adj) ((w / 2097152) % 64) &&
      isMISNat (adjMask adj) ((w / 134217728) % 64) && isMISNat (adjMask adj) ((w / 8589934592) % 64) &&
      isMISNat (adjMask adj) ((w / 549755813888) % 64) && isMISNat (adjMask adj) ((w / 35184372088832) % 64) &&
      isMISNat (adjMask adj) ((w / 2251799813685248) % 64) &&
      allDistinctAux [(w / 8) % 64, (w / 512) % 64, (w / 32768) % 64, (w / 2097152) % 64,
        (w / 134217728) % 64, (w / 8589934592) % 64, (w / 549755813888) % 64,
        (w / 35184372088832) % 64, (w / 2251799813685248) % 64] = true at hw
    simp only [Bool.and_eq_true] at hw
    let xs := [(w / 8) % 64, (w / 512) % 64, (w / 32768) % 64, (w / 2097152) % 64,
      (w / 134217728) % 64, (w / 8589934592) % 64, (w / 549755813888) % 64,
      (w / 35184372088832) % 64, (w / 2251799813685248) % 64]
    apply contra_mis_list G adj hadj hsymm hdiag C hfit xs (by simp [xs, hsz])
    · intro ⟨r, hr⟩
      match r with
      | 0 => exact Nat.mod_lt _ (by decide)
      | 1 => exact Nat.mod_lt _ (by decide)
      | 2 => exact Nat.mod_lt _ (by decide)
      | 3 => exact Nat.mod_lt _ (by decide)
      | 4 => exact Nat.mod_lt _ (by decide)
      | 5 => exact Nat.mod_lt _ (by decide)
      | 6 => exact Nat.mod_lt _ (by decide)
      | 7 => exact Nat.mod_lt _ (by decide)
      | 8 => exact Nat.mod_lt _ (by decide)
      | _ + 9 => simp [xs] at hr
    · intro ⟨r, hr⟩
      match r with
      | 0 => exact hw.1.1.1.1.1.1.1.1.1
      | 1 => exact hw.1.1.1.1.1.1.1.1.2
      | 2 => exact hw.1.1.1.1.1.1.1.2
      | 3 => exact hw.1.1.1.1.1.1.2
      | 4 => exact hw.1.1.1.1.1.2
      | 5 => exact hw.1.1.1.1.2
      | 6 => exact hw.1.1.1.2
      | 7 => exact hw.1.1.2
      | 8 => exact hw.1.2
      | _ + 9 => simp [xs] at hr
    · exact hw.2
  | 5 => simp only [validWit, ht] at hw; cases hw
  | 6 => simp only [validWit, ht] at hw; cases hw
  | 7 =>
    exfalso
    simp only [validWit, ht] at hw
    change (w / 8) % 8 < 6 && (w / 64) % 8 < 6 && hasEdgeNat (adjMask adj) ((w / 8) % 8) ((w / 64) % 8) &&
      isMISNat (adjMask adj) ((w / 512) % 64) && !(hasBit ((w / 512) % 64) ((w / 8) % 8)) &&
      !(hasBit ((w / 512) % 64) ((w / 64) % 8)) &&
      isMISNat (adjMask adj) ((w / 32768) % 64) && hasBit ((w / 32768) % 64) ((w / 8) % 8) &&
      isMISNat (adjMask adj) ((w / 2097152) % 64) && hasBit ((w / 2097152) % 64) ((w / 8) % 8) &&
      isMISNat (adjMask adj) ((w / 134217728) % 64) && hasBit ((w / 134217728) % 64) ((w / 8) % 8) &&
      allDistinctAux [(w / 32768) % 64, (w / 2097152) % 64, (w / 134217728) % 64] &&
      isMISNat (adjMask adj) ((w / 8589934592) % 64) && hasBit ((w / 8589934592) % 64) ((w / 64) % 8) &&
      isMISNat (adjMask adj) ((w / 549755813888) % 64) && hasBit ((w / 549755813888) % 64) ((w / 64) % 8) &&
      isMISNat (adjMask adj) ((w / 35184372088832) % 64) && hasBit ((w / 35184372088832) % 64) ((w / 64) % 8) &&
      allDistinctAux [(w / 8589934592) % 64, (w / 549755813888) % 64, (w / 35184372088832) % 64] = true at hw
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_iff] at hw
    let u := (w / 8) % 8
    let v := (w / 64) % 8
    let uxs := [(w / 32768) % 64, (w / 2097152) % 64, (w / 134217728) % 64]
    let vxs := [(w / 8589934592) % 64, (w / 549755813888) % 64, (w / 35184372088832) % 64]
    let hu6 := hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
    let hv6 := hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    let hadjuv := adj_of_hasEdgeNat G adj hadj hsymm hdiag hu6 hv6 hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    let hI0 := isMISNat_sound G adj hadj hsymm hdiag _ hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    have hu0 : ⟨u, hu6⟩ ∉ ofMask6 ((w / 512) % 64) := by
      rw [mem_ofMask6]; exact fun h => by rw [hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2] at h; cases h
    have hv0 : ⟨v, hv6⟩ ∉ ofMask6 ((w / 512) % 64) := by
      rw [mem_ofMask6]; exact fun h => by rw [hw.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2] at h; cases h
    let U3 : Fin 3 → Finset (Fin 6) := fun r => ofMask6 (uxs[r.val]'r.isLt)
    let V3 : Fin 3 → Finset (Fin 6) := fun r => ofMask6 (vxs[r.val]'r.isLt)
    apply contra_adj_c3 G C hfit hout hdisj hsz ⟨u, hu6⟩ ⟨v, hv6⟩ hadjuv (ofMask6 ((w / 512) % 64)) hI0 hu0 hv0 U3 _ _ _ V3 _ _ _
    · intro ⟨r, hr⟩; match r with
      | 0 => exact isMISNat_sound G adj hadj hsymm hdiag _ hw.1.1.1.1.1.1.1.1.1.1.1.1.1.2
      | 1 => exact isMISNat_sound G adj hadj hsymm hdiag _ hw.1.1.1.1.1.1.1.1.1.1.1.2
      | 2 => exact isMISNat_sound G adj hadj hsymm hdiag _ hw.1.1.1.1.1.1.1.1.1.2
      | _ + 3 => omega
    · intro a b hab; apply ofMask6_ne
      · rcases a with ⟨a, ha⟩; match a with | 0 => exact Nat.mod_lt _ (by decide) | 1 => exact Nat.mod_lt _ (by decide) | 2 => exact Nat.mod_lt _ (by decide) | _ + 3 => omega
      · rcases b with ⟨b, hb⟩; match b with | 0 => exact Nat.mod_lt _ (by decide) | 1 => exact Nat.mod_lt _ (by decide) | 2 => exact Nat.mod_lt _ (by decide) | _ + 3 => omega
      · exact allDistinctAux_get_ne uxs hw.1.1.1.1.1.1.1.2 a b hab
    · intro ⟨r, hr⟩; rw [mem_ofMask6]; match r with
      | 0 => exact hw.1.1.1.1.1.1.1.1.1.1.1.1.2
      | 1 => exact hw.1.1.1.1.1.1.1.1.1.1.2
      | 2 => exact hw.1.1.1.1.1.1.1.1.2
      | _ + 3 => omega
    · intro ⟨r, hr⟩; match r with
      | 0 => exact isMISNat_sound G adj hadj hsymm hdiag _ hw.1.1.1.1.1.1.2
      | 1 => exact isMISNat_sound G adj hadj hsymm hdiag _ hw.1.1.1.1.2
      | 2 => exact isMISNat_sound G adj hadj hsymm hdiag _ hw.1.1.2
      | _ + 3 => omega
    · intro a b hab; apply ofMask6_ne
      · rcases a with ⟨a, ha⟩; match a with | 0 => exact Nat.mod_lt _ (by decide) | 1 => exact Nat.mod_lt _ (by decide) | 2 => exact Nat.mod_lt _ (by decide) | _ + 3 => omega
      · rcases b with ⟨b, hb⟩; match b with | 0 => exact Nat.mod_lt _ (by decide) | 1 => exact Nat.mod_lt _ (by decide) | 2 => exact Nat.mod_lt _ (by decide) | _ + 3 => omega
      · exact allDistinctAux_get_ne vxs hw.2 a b hab
    · intro ⟨r, hr⟩; rw [mem_ofMask6]; match r with
      | 0 => exact hw.1.1.1.1.1.2
      | 1 => exact hw.1.1.1.2
      | 2 => exact hw.1.2
      | _ + 3 => omega
  | _ + 8 => omega

def permGraph (G : SimpleGraph (Fin 6)) (p : Fin 6 → Fin 6) : SimpleGraph (Fin 6) where
  Adj a b := G.Adj (p a) (p b)
  symm := { symm := fun _ _ h => G.adj_symm h }
  loopless := { irrefl := fun a h => G.loopless.irrefl (p a) h }

def permCircuit (C : AndCountCircuit 6) (q : Fin 6 → Fin 6) : AndCountCircuit 6 where
  size := C.size
  leftVars i := (C.leftVars i).image q
  leftGates i := C.leftGates i
  rightVars i := (C.rightVars i).image q
  rightGates i := C.rightGates i
  outVars := C.outVars.image q
  outGates := C.outGates

lemma sideTrue_perm {k : Nat} (p q : Fin 6 → Fin 6) (hpq : ∀ x, p (q x) = x) (hqp : ∀ x, q (p x) = x)
    (U B : Finset (Fin 6)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (hvw : ∀ j, j < i → v j = w j) :
    sideTrue U (B.image q) F i v = sideTrue (U.image p) B F i w := by
  unfold sideTrue
  congr 1
  apply propext
  constructor
  · rintro (⟨x, hxB, hxU⟩ | ⟨j, hjF, hji, hvj⟩)
    · obtain ⟨y, hyB, rfl⟩ := Finset.mem_image.1 hxB
      exact Or.inl ⟨y, hyB, Finset.mem_image.2 ⟨q y, hxU, hpq y⟩⟩
    · exact Or.inr ⟨j, hjF, hji, by rw [← hvw j hji]; exact hvj⟩
  · rintro (⟨y, hyB, hyU⟩ | ⟨j, hjF, hji, hwj⟩)
    · obtain ⟨x, hxU, hpx⟩ := Finset.mem_image.1 hyU
      exact Or.inl ⟨q y, Finset.mem_image_of_mem q hyB, by rw [← hpx, hqp]; exact hxU⟩
    · exact Or.inr ⟨j, hjF, hji, by rw [hvw j hji]; exact hwj⟩

lemma permCircuit_gateVal (C : AndCountCircuit 6) (p q : Fin 6 → Fin 6)
    (hpq : ∀ x, p (q x) = x) (hqp : ∀ x, q (p x) = x) (U : Finset (Fin 6)) :
    ∀ (m : Nat) (i : Fin C.size), i.val < m → (permCircuit C q).gateVal U i = C.gateVal (U.image p) i := by
  intro m
  induction m with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    have hlt : ∀ j : Fin C.size, j < i → (permCircuit C q).gateVal U j = C.gateVal (U.image p) j := by
      intro j hji
      exact ih j (by have : j.val < i.val := hji; omega)
    rw [gateVal_rec (permCircuit C q) U i, gateVal_rec C (U.image p) i]
    change (sideTrue U ((C.leftVars i).image q) (C.leftGates i) i ((permCircuit C q).gateVal U) &&
        sideTrue U ((C.rightVars i).image q) (C.rightGates i) i ((permCircuit C q).gateVal U)) =
      (sideTrue (U.image p) (C.leftVars i) (C.leftGates i) i (C.gateVal (U.image p)) &&
        sideTrue (U.image p) (C.rightVars i) (C.rightGates i) i (C.gateVal (U.image p)))
    rw [sideTrue_perm p q hpq hqp U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_perm p q hpq hqp U (C.rightVars i) (C.rightGates i) i _ _ hlt]

lemma permCircuit_eval (C : AndCountCircuit 6) (p q : Fin 6 → Fin 6)
    (hpq : ∀ x, p (q x) = x) (hqp : ∀ x, q (p x) = x) (U : Finset (Fin 6)) :
    (permCircuit C q).eval U = C.eval (U.image p) := by
  rw [Bool.eq_iff_iff, eval_iff, eval_iff]
  change ((∃ v ∈ C.outVars.image q, v ∈ U) ∨ ∃ j ∈ C.outGates, (permCircuit C q).gateVal U j = true) ↔
    ((∃ v ∈ C.outVars, v ∈ U.image p) ∨ ∃ j ∈ C.outGates, C.gateVal (U.image p) j = true)
  constructor
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · obtain ⟨y, hyO, rfl⟩ := Finset.mem_image.1 hvO
      exact Or.inl ⟨y, hyO, Finset.mem_image.2 ⟨q y, hvU, hpq y⟩⟩
    · exact Or.inr ⟨j, hjO, by rwa [← permCircuit_gateVal C p q hpq hqp U C.size j j.isLt]⟩
  · rintro (⟨y, hyO, hyU⟩ | ⟨j, hjO, hjv⟩)
    · obtain ⟨x, hxU, hpx⟩ := Finset.mem_image.1 hyU
      exact Or.inl ⟨q y, Finset.mem_image_of_mem q hyO, by rw [← hpx, hqp]; exact hxU⟩
    · exact Or.inr ⟨j, hjO, by rwa [permCircuit_gateVal C p q hpq hqp U C.size j j.isLt]⟩

lemma perm_isMIS (G : SimpleGraph (Fin 6)) (p q : Fin 6 → Fin 6)
    (hpq : ∀ x, p (q x) = x) (_hqp : ∀ x, q (p x) = x) (I : Finset (Fin 6)) :
    isMIS (permGraph G p) I → isMIS G (I.image p) := by
  intro ⟨hind, hmax⟩
  constructor
  · intro a ha b hb hab
    obtain ⟨xa, hxa, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨xb, hxb, rfl⟩ := Finset.mem_image.1 hb
    exact hind xa hxa xb hxb hab
  · intro u hu
    have hqu : q u ∉ I := fun hq => hu (Finset.mem_image.2 ⟨q u, hq, hpq u⟩)
    obtain ⟨v, hvI, hadj⟩ := hmax (q u) hqu
    refine ⟨p v, Finset.mem_image_of_mem p hvI, ?_⟩
    change G.Adj (p (q u)) (p v) at hadj
    rwa [hpq u] at hadj

lemma perm_transfer (G : SimpleGraph (Fin 6)) (C : AndCountCircuit 6)
    (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (p q : Fin 6 → Fin 6) (hpq : ∀ x, p (q x) = x) (hqp : ∀ x, q (p x) = x)
    (hsub : ∀ (C' : AndCountCircuit 6), C'.size = C.size → Fits (permGraph G p) C' → C'.outVars = ∅ →
      (∀ i : Fin C'.size, Disjoint (C'.leftVars i) (C'.rightVars i)) →
      ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C'.size ∧ Cover (permGraph G p) k X Y) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y := by
  let C' := permCircuit C q
  have hfit' : Fits (permGraph G p) C' := by
    intro I hMIS
    have hMIS' := perm_isMIS G p q hpq hqp I hMIS
    have hf := hfit (I.image p) hMIS'
    constructor
    · rw [permCircuit_eval C p q hpq hqp I, hf.1]
    · intro u hu
      rw [permCircuit_eval C p q hpq hqp (insert u I), Finset.image_insert]
      apply hf.2 (p u)
      intro hmem
      obtain ⟨x, hxI, hpx⟩ := Finset.mem_image.1 hmem
      have hxq : x = u := by have := congrArg q hpx; rwa [hqp, hqp] at this
      subst hxq
      exact hu hxI
  have hout' : C'.outVars = ∅ := by simp [C', permCircuit, hout]
  have hdisj' : ∀ i : Fin C'.size, Disjoint (C'.leftVars i) (C'.rightVars i) := by
    intro i
    rw [Finset.disjoint_left]
    intro x hxL hxR
    obtain ⟨y, hyL, rfl⟩ := Finset.mem_image.1 hxL
    obtain ⟨z, hzR, hqz⟩ := Finset.mem_image.1 hxR
    have hyz : z = y := by have := congrArg p hqz; rwa [hpq, hpq] at this
    subst hyz
    exact Finset.disjoint_left.1 (hdisj i) hyL hzR
  obtain ⟨k, X, Y, hk, hc1, hc2⟩ := hsub C' rfl hfit' hout' hdisj'
  refine ⟨k, fun i => (X i).image p, fun i => (Y i).image p, hk, ?_, ?_⟩
  · intro i a ha b hb
    obtain ⟨xa, hxa, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨xb, hxb, rfl⟩ := Finset.mem_image.1 hb
    exact hc1 i xa hxa xb hxb
  · intro a b hab
    have hadjp : (permGraph G p).Adj (q a) (q b) := by
      change G.Adj (p (q a)) (p (q b))
      rwa [hpq a, hpq b]
    obtain ⟨i, hi | hi⟩ := hc2 (q a) (q b) hadjp
    · exact ⟨i, Or.inl ⟨Finset.mem_image.2 ⟨q a, hi.1, hpq a⟩, Finset.mem_image.2 ⟨q b, hi.2, hpq b⟩⟩⟩
    · exact ⟨i, Or.inr ⟨Finset.mem_image.2 ⟨q b, hi.1, hpq b⟩, Finset.mem_image.2 ⟨q a, hi.2, hpq a⟩⟩⟩

def swap6 (a b x : Fin 6) : Fin 6 :=
  if x = a then b else if x = b then a else x

lemma swap6_involutive (a b x : Fin 6) : swap6 a b (swap6 a b x) = x := by
  unfold swap6
  by_cases hab : a = b <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all

lemma perm_pair (a0 b0 : Fin 6) (hab : a0 ≠ b0) :
    ∃ (p q : Fin 6 → Fin 6), (∀ x, p (q x) = x) ∧ (∀ x, q (p x) = x) ∧ p 0 = a0 ∧ p 1 = b0 := by
  let s := swap6 0 a0 b0
  let p : Fin 6 → Fin 6 := fun x => swap6 0 a0 (swap6 1 s x)
  let q : Fin 6 → Fin 6 := fun x => swap6 1 s (swap6 0 a0 x)
  refine ⟨p, q, ?_, ?_, ?_, ?_⟩
  · intro x; simp [p, q, swap6_involutive]
  · intro x; simp [p, q, swap6_involutive]
  · have hs0 : s ≠ 0 := by
      unfold s swap6
      by_cases hb0 : b0 = 0
      · subst hb0; simp [hab]
      · by_cases hba : b0 = a0
        · exact absurd hba.symm hab
        · simp [hb0, hba]
    have h01 : (0 : Fin 6) ≠ 1 := by decide
    have hsw : swap6 1 s 0 = 0 := by unfold swap6; simp [h01, hs0.symm]
    dsimp only [p]
    rw [hsw]
    unfold swap6
    simp
  · have hsw1 : swap6 1 s 1 = s := by unfold swap6; simp
    dsimp only [p]
    rw [hsw1]
    exact swap6_involutive 0 a0 b0

lemma perm_triple (s0 s1 s2 : Fin 6) (h01 : s0 ≠ s1) (h02 : s0 ≠ s2) (h12 : s1 ≠ s2) :
    ∃ (p q : Fin 6 → Fin 6), (∀ x, p (q x) = x) ∧ (∀ x, q (p x) = x) ∧
      p 0 = s0 ∧ p 1 = s1 ∧ p 2 = s2 := by
  obtain ⟨p1, q1, hpq1, hqp1, h0, h1⟩ := perm_pair s0 s1 h01
  let r2 := q1 s2
  have hr20 : r2 ≠ 0 := by
    intro h
    have heq : p1 r2 = p1 0 := congrArg p1 h
    rw [hpq1 s2, h0] at heq
    exact h02 heq.symm
  have hr21 : r2 ≠ 1 := by
    intro h
    have heq : p1 r2 = p1 1 := congrArg p1 h
    rw [hpq1 s2, h1] at heq
    exact h12 heq.symm
  let p : Fin 6 → Fin 6 := fun x => p1 (swap6 2 r2 x)
  let q : Fin 6 → Fin 6 := fun x => swap6 2 r2 (q1 x)
  refine ⟨p, q, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; simp [p, q, swap6_involutive, hpq1]
  · intro x; simp [p, q, hqp1, swap6_involutive]
  · have h20 : (0 : Fin 6) ≠ 2 := by decide
    have hsw : swap6 2 r2 0 = 0 := by unfold swap6; simp [h20, hr20.symm]
    dsimp only [p]; rw [hsw, h0]
  · have h21 : (1 : Fin 6) ≠ 2 := by decide
    have hsw : swap6 2 r2 1 = 1 := by unfold swap6; simp [h21, hr21.symm]
    dsimp only [p]; rw [hsw, h1]
  · have hsw : swap6 2 r2 2 = r2 := by unfold swap6; simp
    dsimp only [p]; rw [hsw]; exact hpq1 s2

def swap4 (a b x : Fin 4) : Fin 4 := if x = a then b else if x = b then a else x

def cstep4 (f : Fin 4 → Nat) (a b : Fin 4) (st : (Fin 4 → Fin 4) × (Fin 4 → Fin 4)) :
    (Fin 4 → Fin 4) × (Fin 4 → Fin 4) :=
  if f (st.1 b) < f (st.1 a) then
    (fun x => st.1 (swap4 a b x), fun x => swap4 a b (st.2 x))
  else st

def sort4Perm (f : Fin 4 → Nat) : (Fin 4 → Fin 4) × (Fin 4 → Fin 4) :=
  let s0 : (Fin 4 → Fin 4) × (Fin 4 → Fin 4) := (id, id)
  let s1 := cstep4 f 0 1 s0
  let s2 := cstep4 f 2 3 s1
  let s3 := cstep4 f 0 2 s2
  let s4 := cstep4 f 1 3 s3
  cstep4 f 1 2 s4

def permInv4Check (p q : Fin 4 → Fin 4) : Bool :=
  p (q 0) == 0 && p (q 1) == 1 && p (q 2) == 2 && p (q 3) == 3

lemma permInv4_sound (p q : Fin 4 → Fin 4) (h : permInv4Check p q = true) :
    ∀ x : Fin 4, p (q x) = x := by
  unfold permInv4Check at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  intro ⟨x, hx⟩
  match x with
  | 0 => exact h.1.1.1
  | 1 => exact h.1.1.2
  | 2 => exact h.1.2
  | 3 => exact h.2
  | _ + 4 => omega

def memTfList (x : Nat × Nat × Nat × Nat) : List (Nat × Nat × Nat × Nat) → Bool
  | [] => false
  | y :: ys => (x == y) || memTfList x ys

lemma mem_of_memTfList (x : Nat × Nat × Nat × Nat) :
    ∀ xs : List (Nat × Nat × Nat × Nat), memTfList x xs = true → x ∈ xs := by
  intro xs h
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [memTfList, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem y (ih h')

def checkSort4With (f : Fin 4 → Nat) (pq : (Fin 4 → Fin 4) × (Fin 4 → Fin 4)) : Bool :=
  permInv4Check pq.1 pq.2 && permInv4Check pq.2 pq.1 &&
    memTfList (f (pq.1 0), f (pq.1 1), f (pq.1 2), f (pq.1 3)) tfTuples

def sort4Check (c0 c1 c2 c3 : Fin 3) : Bool :=
  let f : Fin 4 → Nat := fun i => match i.val with | 0 => c0.val | 1 => c1.val | 2 => c2.val | _ => c3.val
  checkSort4With f (sort4Perm f)

theorem sort4_ok : ∀ c0 c1 c2 c3 : Fin 3, sort4Check c0 c1 c2 c3 = true := by decide +kernel

lemma sort4_extract (f : Fin 4 → Nat) (pq : (Fin 4 → Fin 4) × (Fin 4 → Fin 4))
    (h : checkSort4With f pq = true) :
    ∃ (σ σ' : Fin 4 → Fin 4),
      (∀ x : Fin 4, σ (σ' x) = x) ∧
      (∀ x : Fin 4, σ' (σ x) = x) ∧
      (f (σ 0), f (σ 1), f (σ 2), f (σ 3)) ∈ tfTuples := by
  unfold checkSort4With at h
  simp only [Bool.and_eq_true] at h
  exact ⟨pq.1, pq.2, permInv4_sound pq.1 pq.2 h.1.1, permInv4_sound pq.2 pq.1 h.1.2,
    mem_of_memTfList _ tfTuples h.2⟩

lemma exists_sort4 (c0 c1 c2 c3 : Fin 3) :
    let f : Fin 4 → Nat := fun i => match i.val with | 0 => c0.val | 1 => c1.val | 2 => c2.val | _ => c3.val
    ∃ (σ σ' : Fin 4 → Fin 4),
      (∀ x : Fin 4, σ (σ' x) = x) ∧
      (∀ x : Fin 4, σ' (σ x) = x) ∧
      (f (σ 0), f (σ 1), f (σ 2), f (σ 3)) ∈ tfTuples := by
  let f : Fin 4 → Nat := fun i => match i.val with | 0 => c0.val | 1 => c1.val | 2 => c2.val | _ => c3.val
  have h0 := sort4_ok c0 c1 c2 c3
  unfold sort4Check at h0
  exact sort4_extract f (sort4Perm f) h0

def swap3 (a b x : Fin 3) : Fin 3 := if x = a then b else if x = b then a else x

def cstep3 (f : Fin 3 → Nat) (a b : Fin 3) (st : (Fin 3 → Fin 3) × (Fin 3 → Fin 3)) :
    (Fin 3 → Fin 3) × (Fin 3 → Fin 3) :=
  if f (st.1 b) < f (st.1 a) then
    (fun x => st.1 (swap3 a b x), fun x => swap3 a b (st.2 x))
  else st

def sort3Perm (f : Fin 3 → Nat) : (Fin 3 → Fin 3) × (Fin 3 → Fin 3) :=
  let s0 : (Fin 3 → Fin 3) × (Fin 3 → Fin 3) := (id, id)
  let s1 := cstep3 f 0 1 s0
  let s2 := cstep3 f 0 2 s1
  cstep3 f 1 2 s2

def permInv3Check (p q : Fin 3 → Fin 3) : Bool :=
  p (q 0) == 0 && p (q 1) == 1 && p (q 2) == 2

lemma permInv3_sound (p q : Fin 3 → Fin 3) (h : permInv3Check p q = true) :
    ∀ x : Fin 3, p (q x) = x := by
  unfold permInv3Check at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  intro ⟨x, hx⟩
  match x with
  | 0 => exact h.1.1
  | 1 => exact h.1.2
  | 2 => exact h.2
  | _ + 3 => omega

def memA3List (x : Nat × Nat × Nat) : List (Nat × Nat × Nat) → Bool
  | [] => false
  | y :: ys => (x == y) || memA3List x ys

lemma mem_of_memA3List (x : Nat × Nat × Nat) :
    ∀ xs : List (Nat × Nat × Nat), memA3List x xs = true → x ∈ xs := by
  intro xs h
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [memA3List, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem y (ih h')

def checkSort3With (f : Fin 3 → Nat) (pq : (Fin 3 → Fin 3) × (Fin 3 → Fin 3)) : Bool :=
  permInv3Check pq.1 pq.2 && permInv3Check pq.2 pq.1 &&
    memA3List (f (pq.1 0), f (pq.1 1), f (pq.1 2)) a3Tuples

def sort3Check (c0 c1 c2 : Fin 7) : Bool :=
  let f : Fin 3 → Nat := fun i => match i.val with | 0 => c0.val + 1 | 1 => c1.val + 1 | _ => c2.val + 1
  checkSort3With f (sort3Perm f)

theorem sort3_ok : ∀ c0 c1 c2 : Fin 7, sort3Check c0 c1 c2 = true := by decide +kernel

lemma sort3_extract (f : Fin 3 → Nat) (pq : (Fin 3 → Fin 3) × (Fin 3 → Fin 3))
    (h : checkSort3With f pq = true) :
    ∃ (σ σ' : Fin 3 → Fin 3),
      (∀ x : Fin 3, σ (σ' x) = x) ∧
      (∀ x : Fin 3, σ' (σ x) = x) ∧
      (f (σ 0), f (σ 1), f (σ 2)) ∈ a3Tuples := by
  unfold checkSort3With at h
  simp only [Bool.and_eq_true] at h
  exact ⟨pq.1, pq.2, permInv3_sound pq.1 pq.2 h.1.1, permInv3_sound pq.2 pq.1 h.1.2,
    mem_of_memA3List _ a3Tuples h.2⟩

lemma exists_sort3 (c0 c1 c2 : Fin 7) :
    let f : Fin 3 → Nat := fun i => match i.val with | 0 => c0.val + 1 | 1 => c1.val + 1 | _ => c2.val + 1
    ∃ (σ σ' : Fin 3 → Fin 3),
      (∀ x : Fin 3, σ (σ' x) = x) ∧
      (∀ x : Fin 3, σ' (σ x) = x) ∧
      (f (σ 0), f (σ 1), f (σ 2)) ∈ a3Tuples := by
  let f : Fin 3 → Nat := fun i => match i.val with | 0 => c0.val + 1 | 1 => c1.val + 1 | _ => c2.val + 1
  have h0 := sort3_ok c0 c1 c2
  unfold sort3Check at h0
  exact sort3_extract f (sort3Perm f) h0

def lift4 (σ : Fin 4 → Fin 4) (x : Fin 6) : Fin 6 :=
  if _h0 : x.val = 0 then 0
  else if _h1 : x.val = 1 then 1
  else ⟨(σ ⟨x.val - 2, by omega⟩).val + 2, by omega⟩

lemma lift4_comp (σ σ' : Fin 4 → Fin 4) (h : ∀ k : Fin 4, σ (σ' k) = k) :
    ∀ x : Fin 6, lift4 σ (lift4 σ' x) = x := by
  intro ⟨x, hx⟩
  match x with
  | 0 => rfl
  | 1 => rfl
  | 2 =>
    apply Fin.ext
    change (σ ⟨(σ' 0).val, _⟩).val + 2 = 2
    have heq : (⟨(σ' 0).val, (σ' 0).isLt⟩ : Fin 4) = σ' 0 := Fin.ext rfl
    rw [heq, h 0]; rfl
  | 3 =>
    apply Fin.ext
    change (σ ⟨(σ' 1).val, _⟩).val + 2 = 3
    have heq : (⟨(σ' 1).val, (σ' 1).isLt⟩ : Fin 4) = σ' 1 := Fin.ext rfl
    rw [heq, h 1]; rfl
  | 4 =>
    apply Fin.ext
    change (σ ⟨(σ' 2).val, _⟩).val + 2 = 4
    have heq : (⟨(σ' 2).val, (σ' 2).isLt⟩ : Fin 4) = σ' 2 := Fin.ext rfl
    rw [heq, h 2]; rfl
  | 5 =>
    apply Fin.ext
    change (σ ⟨(σ' 3).val, _⟩).val + 2 = 5
    have heq : (⟨(σ' 3).val, (σ' 3).isLt⟩ : Fin 4) = σ' 3 := Fin.ext rfl
    rw [heq, h 3]; rfl
  | _ + 6 => omega

def lift3 (σ : Fin 3 → Fin 3) (x : Fin 6) : Fin 6 :=
  if _h0 : x.val = 0 then 0
  else if _h1 : x.val = 1 then 1
  else if _h2 : x.val = 2 then 2
  else ⟨(σ ⟨x.val - 3, by omega⟩).val + 3, by omega⟩

lemma lift3_comp (σ σ' : Fin 3 → Fin 3) (h : ∀ k : Fin 3, σ (σ' k) = k) :
    ∀ x : Fin 6, lift3 σ (lift3 σ' x) = x := by
  intro ⟨x, hx⟩
  match x with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 =>
    apply Fin.ext
    change (σ ⟨(σ' 0).val, _⟩).val + 3 = 3
    have heq : (⟨(σ' 0).val, (σ' 0).isLt⟩ : Fin 3) = σ' 0 := Fin.ext rfl
    rw [heq, h 0]; rfl
  | 4 =>
    apply Fin.ext
    change (σ ⟨(σ' 1).val, _⟩).val + 3 = 4
    have heq : (⟨(σ' 1).val, (σ' 1).isLt⟩ : Fin 3) = σ' 1 := Fin.ext rfl
    rw [heq, h 1]; rfl
  | 5 =>
    apply Fin.ext
    change (σ ⟨(σ' 2).val, _⟩).val + 3 = 5
    have heq : (⟨(σ' 2).val, (σ' 2).isLt⟩ : Fin 3) = σ' 2 := Fin.ext rfl
    rw [heq, h 2]; rfl
  | _ + 6 => omega

lemma perm_no3 (G : SimpleGraph (Fin 6)) (p q : Fin 6 → Fin 6) (hqp : ∀ x, q (p x) = x)
    (hno : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj b c ∨ G.Adj a c) :
    ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c →
      (permGraph G p).Adj a b ∨ (permGraph G p).Adj b c ∨ (permGraph G p).Adj a c := by
  intro a b c hab hac hbc
  exact hno (p a) (p b) (p c)
    (fun h => hab (by simpa [hqp] using congrArg q h))
    (fun h => hac (by simpa [hqp] using congrArg q h))
    (fun h => hbc (by simpa [hqp] using congrArg q h))

lemma perm_no4 (G : SimpleGraph (Fin 6)) (p q : Fin 6 → Fin 6) (hqp : ∀ x, q (p x) = x)
    (hno : ¬ ∃ a b c d : Fin 6, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d ∧ ¬ G.Adj c d) :
    ¬ ∃ a b c d : Fin 6, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ¬ (permGraph G p).Adj a b ∧ ¬ (permGraph G p).Adj a c ∧ ¬ (permGraph G p).Adj a d ∧
      ¬ (permGraph G p).Adj b c ∧ ¬ (permGraph G p).Adj b d ∧ ¬ (permGraph G p).Adj c d := by
  rintro ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, eab, eac, ead, ebc, ebd, ecd⟩
  apply hno
  exact ⟨p a, p b, p c, p d,
    fun h => hab (by simpa [hqp] using congrArg q h),
    fun h => hac (by simpa [hqp] using congrArg q h),
    fun h => had (by simpa [hqp] using congrArg q h),
    fun h => hbc (by simpa [hqp] using congrArg q h),
    fun h => hbd (by simpa [hqp] using congrArg q h),
    fun h => hcd (by simpa [hqp] using congrArg q h),
    eab, eac, ead, ebc, ebd, ecd⟩

def tfTyp (adj : Fin 6 → Fin 6 → Bool) (v : Fin 6) : Fin 3 :=
  if !(adj 0 v) then 0 else if !(adj 1 v) then 1 else 2

lemma adj_eq_tfTyp_0 (adj : Fin 6 → Fin 6 → Bool) (v : Fin 6) :
    adj 0 v = ((tfTyp adj v).val != 0) := by
  unfold tfTyp
  cases adj 0 v <;> cases adj 1 v <;> decide

lemma adj_eq_tfTyp_1 (adj : Fin 6 → Fin 6 → Bool) (v : Fin 6)
    (hcov : adj 0 v = true ∨ adj 1 v = true) :
    adj 1 v = ((tfTyp adj v).val != 1) := by
  unfold tfTyp
  cases h0 : adj 0 v <;> cases h1 : adj 1 v <;> simp_all

set_option maxHeartbeats 2000000 in
lemma solve_tf_canon (G : SimpleGraph (Fin 6)) (C : AndCountCircuit 6)
    (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (hsz23 : C.size = 2 ∨ C.size = 3)
    (hno3 : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj b c ∨ G.Adj a c)
    (a0 b0 : Fin 6) (hab : a0 ≠ b0) (hnab : ¬ G.Adj a0 b0) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y := by
  classical
  obtain ⟨p1, q1, hpq1, hqp1, h0, h1⟩ := perm_pair a0 b0 hab
  apply perm_transfer G C hfit hout hdisj p1 q1 hpq1 hqp1
  intro C1 hsz1 hfit1 hout1 hdisj1
  let G1 := permGraph G p1
  have hn01 : ¬ G1.Adj 0 1 := by
    change ¬ G.Adj (p1 0) (p1 1)
    rw [h0, h1]; exact hnab
  have hno3_1 := perm_no3 G p1 q1 hqp1 hno3
  let adj1 : Fin 6 → Fin 6 → Bool := fun a b => decide (G1.Adj a b)
  have hadj1 : ∀ a b : Fin 6, adj1 a b = true ↔ G1.Adj a b := fun a b => decide_eq_true_iff
  let c2 := tfTyp adj1 2
  let c3 := tfTyp adj1 3
  let c4 := tfTyp adj1 4
  let c5 := tfTyp adj1 5
  let f : Fin 4 → Nat := fun i => match i.val with | 0 => c2.val | 1 => c3.val | 2 => c4.val | _ => c5.val
  obtain ⟨σ, σ', hpq4, hqp4, htmem⟩ := exists_sort4 c2 c3 c4 c5
  let p2 := lift4 σ
  let q2 := lift4 σ'
  apply perm_transfer G1 C1 hfit1 hout1 hdisj1 p2 q2 (lift4_comp σ σ' hpq4) (lift4_comp σ' σ hqp4)
  intro C2 hsz2 hfit2 hout2 hdisj2
  let G2 := permGraph G1 p2
  have hno3_2 := perm_no3 G1 p2 q2 (lift4_comp σ' σ hqp4) hno3_1
  let adj : Fin 6 → Fin 6 → Bool := fun a b => decide (G2.Adj a b)
  have hadj : ∀ a b : Fin 6, adj a b = true ↔ G2.Adj a b := fun a b => decide_eq_true_iff
  have hsymm : ∀ a b : Fin 6, adj a b = adj b a := fun a b =>
    Bool.eq_iff_iff.mpr (by rw [hadj, hadj]; exact ⟨fun h => sg_symm G2 h, fun h => sg_symm G2 h⟩)
  have hdiag : ∀ a : Fin 6, adj a a = false := fun a =>
    Bool.eq_false_iff.mpr (fun h => sg_irrefl G2 a ((hadj a a).1 h))
  let t := (f (σ 0), f (σ 1), f (σ 2), f (σ 3))
  let sm := bitsToNat [!adj 2 3, !adj 2 4, !adj 2 5, !adj 3 4, !adj 3 5, !adj 4 5]
  have hsm64 : sm < 64 := by
    have b_lt : ∀ b : Bool, (if b then 1 else 0) ≤ 1 := fun b => by cases b <;> decide
    simp only [sm, bitsToNat]
    have := b_lt (!adj 2 3); have := b_lt (!adj 2 4); have := b_lt (!adj 2 5)
    have := b_lt (!adj 3 4); have := b_lt (!adj 3 5); have := b_lt (!adj 4 5)
    omega
  have hcov01 : ∀ x : Fin 6, x ≠ 0 → x ≠ 1 → adj1 0 x = true ∨ adj1 1 x = true := by
    intro x hx0 hx1
    rw [hadj1, hadj1]
    rcases hno3_1 0 1 x (by decide) hx0.symm hx1.symm with h | h | h
    · exact absurd h hn01
    · exact Or.inr h
    · exact Or.inl h
  have hp2_0 : p2 0 = 0 := rfl
  have hp2_1 : p2 1 = 1 := rfl
  have hp2_off : ∀ j : Fin 4, p2 ⟨j.val + 2, by omega⟩ = ⟨(σ j).val + 2, by omega⟩ := by
    intro ⟨j, hj⟩; match j with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | _ + 4 => omega
  have hf_eq : ∀ j : Fin 4, f j = (tfTyp adj1 ⟨j.val + 2, by omega⟩).val := by
    intro ⟨j, hj⟩; match j with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl | _ + 4 => omega
  have htf0 : ∀ j : Fin 4, adj 0 ⟨j.val + 2, by omega⟩ = (f (σ j) != 0) := by
    intro j
    have heq_adj : adj 0 ⟨j.val + 2, by omega⟩ = adj1 0 ⟨(σ j).val + 2, by omega⟩ := by
      rw [Bool.eq_iff_iff, hadj, hadj1]
      change G1.Adj (p2 0) (p2 ⟨j.val + 2, by omega⟩) ↔ _
      rw [hp2_0, hp2_off j]
    rw [heq_adj, adj_eq_tfTyp_0 adj1 ⟨(σ j).val + 2, by omega⟩, hf_eq (σ j)]
  have htf1 : ∀ j : Fin 4, adj 1 ⟨j.val + 2, by omega⟩ = (f (σ j) != 1) := by
    intro j
    have heq_adj : adj 1 ⟨j.val + 2, by omega⟩ = adj1 1 ⟨(σ j).val + 2, by omega⟩ := by
      rw [Bool.eq_iff_iff, hadj, hadj1]
      change G1.Adj (p2 1) (p2 ⟨j.val + 2, by omega⟩) ↔ _
      rw [hp2_1, hp2_off j]
    have hcov := hcov01 ⟨(σ j).val + 2, by omega⟩
      (fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega)
      (fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega)
    rw [heq_adj, adj_eq_tfTyp_1 adj1 ⟨(σ j).val + 2, by omega⟩ hcov, hf_eq (σ j)]
  have hmask : adjMask adj = tfMask t sm := by
    unfold adjMask tfMask
    congr 1
    have e01 : adj 0 1 = tfEdge t sm 0 1 := by
      change adj 0 1 = false
      apply Bool.eq_false_iff.mpr
      intro h
      have h2 : G1.Adj (p2 0) (p2 1) := (hadj 0 1).1 h
      rw [hp2_0, hp2_1] at h2
      exact hn01 h2
    have e02 : adj 0 2 = tfEdge t sm 0 2 := htf0 0
    have e03 : adj 0 3 = tfEdge t sm 0 3 := htf0 1
    have e04 : adj 0 4 = tfEdge t sm 0 4 := htf0 2
    have e05 : adj 0 5 = tfEdge t sm 0 5 := htf0 3
    have e12 : adj 1 2 = tfEdge t sm 1 2 := htf1 0
    have e13 : adj 1 3 = tfEdge t sm 1 3 := htf1 1
    have e14 : adj 1 4 = tfEdge t sm 1 4 := htf1 2
    have e15 : adj 1 5 = tfEdge t sm 1 5 := htf1 3
    have e23 : adj 2 3 = tfEdge t sm 2 3 := by
      change adj 2 3 = !(hasBit sm 0)
      unfold sm; rw [hasBit_bitsToNat 0 _ (by simp)]; simp
    have e24 : adj 2 4 = tfEdge t sm 2 4 := by
      change adj 2 4 = !(hasBit sm 1)
      unfold sm; rw [hasBit_bitsToNat 1 _ (by simp)]; simp
    have e25 : adj 2 5 = tfEdge t sm 2 5 := by
      change adj 2 5 = !(hasBit sm 2)
      unfold sm; rw [hasBit_bitsToNat 2 _ (by simp)]; simp
    have e34 : adj 3 4 = tfEdge t sm 3 4 := by
      change adj 3 4 = !(hasBit sm 3)
      unfold sm; rw [hasBit_bitsToNat 3 _ (by simp)]; simp
    have e35 : adj 3 5 = tfEdge t sm 3 5 := by
      change adj 3 5 = !(hasBit sm 4)
      unfold sm; rw [hasBit_bitsToNat 4 _ (by simp)]; simp
    have e45 : adj 4 5 = tfEdge t sm 4 5 := by
      change adj 4 5 = !(hasBit sm 5)
      unfold sm; rw [hasBit_bitsToNat 5 _ (by simp)]; simp
    simp only [e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45]
  rcases hsz23 with hcsz | hcsz
  · have hcsz' : C2.size = 2 := by omega
    obtain ⟨w, hw⟩ := lookup_groups 2 64 tfMask tfTuples table_tf_2 check_tf_2 t htmem sm hsm64
    rw [← hmask] at hw
    exact use_validWit_tf2 G2 adj hadj hsymm hdiag C2 hfit2 hout2 hdisj2 hcsz' hno3_2 w hw
  · have hcsz' : C2.size = 3 := by omega
    obtain ⟨w, hw⟩ := lookup_groups 3 64 tfMask tfTuples table_tf_3 check_tf_3 t htmem sm hsm64
    rw [← hmask] at hw
    exact use_validWit_tf3 G2 adj hadj hsymm hdiag C2 hfit2 hout2 hdisj2 hcsz' w hw

def a3Mv (adj : Fin 6 → Fin 6 → Bool) (v : Fin 6) : Nat :=
  (if adj 0 v then 1 else 0) + (if adj 1 v then 2 else 0) + (if adj 2 v then 4 else 0)

lemma a3Mv_bounds (adj : Fin 6 → Fin 6 → Bool) (v : Fin 6)
    (hcov : adj 0 v = true ∨ adj 1 v = true ∨ adj 2 v = true) :
    1 ≤ a3Mv adj v ∧ a3Mv adj v < 8 := by
  unfold a3Mv
  cases h0 : adj 0 v <;> cases h1 : adj 1 v <;> cases h2 : adj 2 v <;> simp_all

lemma a3Mv_bit (adj : Fin 6 → Fin 6 → Bool) (v : Fin 6) (k : Fin 3) :
    adj ⟨k.val, by omega⟩ v = hasBit (a3Mv adj v) k.val := by
  rcases k with ⟨k, hk⟩
  match k with
  | 0 =>
    change adj 0 v = hasBit (a3Mv adj v) 0
    cases h0 : adj 0 v <;> cases h1 : adj 1 v <;> cases h2 : adj 2 v <;> simp [a3Mv, hasBit, h0, h1, h2]
  | 1 =>
    change adj 1 v = hasBit (a3Mv adj v) 1
    cases h0 : adj 0 v <;> cases h1 : adj 1 v <;> cases h2 : adj 2 v <;> simp [a3Mv, hasBit, h0, h1, h2]
  | 2 =>
    change adj 2 v = hasBit (a3Mv adj v) 2
    cases h0 : adj 0 v <;> cases h1 : adj 1 v <;> cases h2 : adj 2 v <;> simp [a3Mv, hasBit, h0, h1, h2]
  | _ + 3 => omega

set_option maxHeartbeats 2000000 in
lemma solve_a3_canon (G : SimpleGraph (Fin 6)) (C : AndCountCircuit 6)
    (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (hsz : C.size = 2)
    (hno4 : ¬ ∃ a b c d : Fin 6, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d ∧ ¬ G.Adj c d)
    (s0 s1 s2 : Fin 6) (h01 : s0 ≠ s1) (h02 : s0 ≠ s2) (h12 : s1 ≠ s2)
    (hn01 : ¬ G.Adj s0 s1) (hn02 : ¬ G.Adj s0 s2) (hn12 : ¬ G.Adj s1 s2) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y := by
  classical
  obtain ⟨p1, q1, hpq1, hqp1, hs0, hs1, hs2⟩ := perm_triple s0 s1 s2 h01 h02 h12
  apply perm_transfer G C hfit hout hdisj p1 q1 hpq1 hqp1
  intro C1 hsz1 hfit1 hout1 hdisj1
  let G1 := permGraph G p1
  have h1_01 : ¬ G1.Adj 0 1 := by change ¬ G.Adj (p1 0) (p1 1); rw [hs0, hs1]; exact hn01
  have h1_02 : ¬ G1.Adj 0 2 := by change ¬ G.Adj (p1 0) (p1 2); rw [hs0, hs2]; exact hn02
  have h1_12 : ¬ G1.Adj 1 2 := by change ¬ G.Adj (p1 1) (p1 2); rw [hs1, hs2]; exact hn12
  have hno4_1 := perm_no4 G p1 q1 hqp1 hno4
  let adj1 : Fin 6 → Fin 6 → Bool := fun a b => decide (G1.Adj a b)
  have hadj1 : ∀ a b : Fin 6, adj1 a b = true ↔ G1.Adj a b := fun a b => decide_eq_true_iff
  have hcov1 : ∀ x : Fin 6, 3 ≤ x.val → adj1 0 x = true ∨ adj1 1 x = true ∨ adj1 2 x = true := by
    intro x hx
    rw [hadj1, hadj1, hadj1]
    by_contra hnone
    push_neg at hnone
    apply hno4_1
    refine ⟨0, 1, 2, x, by decide, by decide, fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega,
      by decide, fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega,
      fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega,
      h1_01, h1_02, hnone.1, h1_12, hnone.2.1, hnone.2.2⟩
  have hb3 := a3Mv_bounds adj1 3 (hcov1 3 (by decide))
  have hb4 := a3Mv_bounds adj1 4 (hcov1 4 (by decide))
  have hb5 := a3Mv_bounds adj1 5 (hcov1 5 (by decide))
  let c3 : Fin 7 := ⟨a3Mv adj1 3 - 1, by have := hb3.2; omega⟩
  let c4 : Fin 7 := ⟨a3Mv adj1 4 - 1, by have := hb4.2; omega⟩
  let c5 : Fin 7 := ⟨a3Mv adj1 5 - 1, by have := hb5.2; omega⟩
  let f : Fin 3 → Nat := fun i => match i.val with | 0 => c3.val + 1 | 1 => c4.val + 1 | _ => c5.val + 1
  obtain ⟨σ, σ', hpq3, hqp3, htmem⟩ := exists_sort3 c3 c4 c5
  let p2 := lift3 σ
  let q2 := lift3 σ'
  apply perm_transfer G1 C1 hfit1 hout1 hdisj1 p2 q2 (lift3_comp σ σ' hpq3) (lift3_comp σ' σ hqp3)
  intro C2 hsz2 hfit2 hout2 hdisj2
  let G2 := permGraph G1 p2
  let adj : Fin 6 → Fin 6 → Bool := fun a b => decide (G2.Adj a b)
  have hadj : ∀ a b : Fin 6, adj a b = true ↔ G2.Adj a b := fun a b => decide_eq_true_iff
  have hsymm : ∀ a b : Fin 6, adj a b = adj b a := fun a b =>
    Bool.eq_iff_iff.mpr (by rw [hadj, hadj]; exact ⟨fun h => sg_symm G2 h, fun h => sg_symm G2 h⟩)
  have hdiag : ∀ a : Fin 6, adj a a = false := fun a =>
    Bool.eq_false_iff.mpr (fun h => sg_irrefl G2 a ((hadj a a).1 h))
  let t := (f (σ 0), f (σ 1), f (σ 2))
  let sm := bitsToNat [adj 3 4, adj 3 5, adj 4 5]
  have hsm8 : sm < 8 := by
    have b_lt : ∀ b : Bool, (if b then 1 else 0) ≤ 1 := fun b => by cases b <;> decide
    simp only [sm, bitsToNat]
    have := b_lt (adj 3 4); have := b_lt (adj 3 5); have := b_lt (adj 4 5)
    omega
  have hp2_0 : p2 0 = 0 := rfl
  have hp2_1 : p2 1 = 1 := rfl
  have hp2_2 : p2 2 = 2 := rfl
  have hp2_off : ∀ j : Fin 3, p2 ⟨j.val + 3, by omega⟩ = ⟨(σ j).val + 3, by omega⟩ := by
    intro ⟨j, hj⟩; match j with | 0 => rfl | 1 => rfl | 2 => rfl | _ + 3 => omega
  have hf_eq : ∀ j : Fin 3, f j = a3Mv adj1 ⟨j.val + 3, by omega⟩ := by
    intro ⟨j, hj⟩
    match j with
    | 0 => change (a3Mv adj1 3 - 1) + 1 = a3Mv adj1 3; have := hb3.1; omega
    | 1 => change (a3Mv adj1 4 - 1) + 1 = a3Mv adj1 4; have := hb4.1; omega
    | 2 => change (a3Mv adj1 5 - 1) + 1 = a3Mv adj1 5; have := hb5.1; omega
    | _ + 3 => omega
  have ha3b : ∀ (a b : Fin 3),
      adj ⟨a.val, by omega⟩ ⟨b.val + 3, by omega⟩ = hasBit (f (σ b)) a.val := by
    intro a b
    have ha_fix : p2 ⟨a.val, by omega⟩ = ⟨a.val, by omega⟩ := by
      rcases a with ⟨a, ha⟩; match a with | 0 => rfl | 1 => rfl | 2 => rfl | _ + 3 => omega
    have heq_adj : adj ⟨a.val, by omega⟩ ⟨b.val + 3, by omega⟩ =
        adj1 ⟨a.val, by omega⟩ ⟨(σ b).val + 3, by omega⟩ := by
      rw [Bool.eq_iff_iff, hadj, hadj1]
      change G1.Adj (p2 ⟨a.val, by omega⟩) (p2 ⟨b.val + 3, by omega⟩) ↔ _
      rw [ha_fix, hp2_off b]
    rw [heq_adj, a3Mv_bit adj1 ⟨(σ b).val + 3, by omega⟩ a, hf_eq (σ b)]
  have hmask : adjMask adj = a3Mask t sm := by
    unfold adjMask a3Mask
    congr 1
    have e01 : adj 0 1 = a3Edge t sm 0 1 := by
      change adj 0 1 = false
      apply Bool.eq_false_iff.mpr; intro h
      have h2 : G1.Adj (p2 0) (p2 1) := (hadj 0 1).1 h
      rw [hp2_0, hp2_1] at h2; exact h1_01 h2
    have e02 : adj 0 2 = a3Edge t sm 0 2 := by
      change adj 0 2 = false
      apply Bool.eq_false_iff.mpr; intro h
      have h2 : G1.Adj (p2 0) (p2 2) := (hadj 0 2).1 h
      rw [hp2_0, hp2_2] at h2; exact h1_02 h2
    have e12 : adj 1 2 = a3Edge t sm 1 2 := by
      change adj 1 2 = false
      apply Bool.eq_false_iff.mpr; intro h
      have h2 : G1.Adj (p2 1) (p2 2) := (hadj 1 2).1 h
      rw [hp2_1, hp2_2] at h2; exact h1_12 h2
    have e03 : adj 0 3 = a3Edge t sm 0 3 := ha3b 0 0
    have e04 : adj 0 4 = a3Edge t sm 0 4 := ha3b 0 1
    have e05 : adj 0 5 = a3Edge t sm 0 5 := ha3b 0 2
    have e13 : adj 1 3 = a3Edge t sm 1 3 := ha3b 1 0
    have e14 : adj 1 4 = a3Edge t sm 1 4 := ha3b 1 1
    have e15 : adj 1 5 = a3Edge t sm 1 5 := ha3b 1 2
    have e23 : adj 2 3 = a3Edge t sm 2 3 := ha3b 2 0
    have e24 : adj 2 4 = a3Edge t sm 2 4 := ha3b 2 1
    have e25 : adj 2 5 = a3Edge t sm 2 5 := ha3b 2 2
    have e34 : adj 3 4 = a3Edge t sm 3 4 := by
      change adj 3 4 = hasBit sm 0
      unfold sm; rw [hasBit_bitsToNat 0 _ (by simp)]; rfl
    have e35 : adj 3 5 = a3Edge t sm 3 5 := by
      change adj 3 5 = hasBit sm 1
      unfold sm; rw [hasBit_bitsToNat 1 _ (by simp)]; rfl
    have e45 : adj 4 5 = a3Edge t sm 4 5 := by
      change adj 4 5 = hasBit sm 2
      unfold sm; rw [hasBit_bitsToNat 2 _ (by simp)]; rfl
    simp only [e01, e02, e03, e04, e05, e12, e13, e14, e15, e23, e24, e25, e34, e35, e45]
  have hcsz : C2.size = 2 := by omega
  obtain ⟨w, hw⟩ := lookup_groups 4 8 a3Mask a3Tuples table_a3_2 check_a3_2 t htmem sm hsm8
  rw [← hmask] at hw
  exact use_validWit_a3 G2 adj hadj hsymm hdiag C2 hfit2 hout2 hdisj2 hcsz w hw

lemma solve_size2 (G : SimpleGraph (Fin 6)) (C : AndCountCircuit 6)
    (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (hsz : C.size = 2) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y := by
  classical
  by_cases h4 : ∃ a b c d : Fin 6, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d ∧ ¬ G.Adj c d
  · obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, eab, eac, ead, ebc, ebd, ecd⟩ := h4
    let S : Finset (Fin 6) := {a, b, c, d}
    have hS : isIndep G S := isIndep_quad G a b c d eab eac ead ebc ebd ecd
    have hcard : S.card = 4 := by
      have ha : a ∉ ({b, c, d} : Finset (Fin 6)) := by simp [hab, hac, had]
      have hb : b ∉ ({c, d} : Finset (Fin 6)) := by simp [hbc, hbd]
      have hc : c ∉ ({d} : Finset (Fin 6)) := by simp [hcd]
      rw [show S = insert a (insert b (insert c {d})) from rfl,
        Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb,
        Finset.card_insert_of_notMem hc, Finset.card_singleton]
    obtain ⟨k, X, Y, hk, hcov⟩ := bc_of_indep_card G S hS
    exact ⟨k, X, Y, by rw [hcard] at hk; omega, hcov⟩
  · by_cases h3 : ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c
    · obtain ⟨s0, s1, s2, h01, h02, h12, hn01, hn02, hn12⟩ := h3
      exact solve_a3_canon G C hfit hout hdisj hsz h4 s0 s1 s2 h01 h02 h12 hn01 hn02 hn12
    · by_cases h2 : ∃ a b : Fin 6, a ≠ b ∧ ¬ G.Adj a b
      · obtain ⟨a0, b0, hab, hnab⟩ := h2
        have hno3 : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj b c ∨ G.Adj a c := by
          intro a b c hab' hac' hbc'
          by_contra hnone
          push_neg at hnone
          exact h3 ⟨a, b, c, hab', hac', hbc', hnone.1, hnone.2.2, hnone.2.1⟩
        exact solve_tf_canon G C hfit hout hdisj (Or.inl hsz) hno3 a0 b0 hab hnab
      · exfalso
        have hK : ∀ a b : Fin 6, a ≠ b → G.Adj a b := by
          intro a b hab
          by_contra hna
          exact h2 ⟨a, b, hab, hna⟩
        have hfb := family_bound G C hfit (fun v : Fin 6 => ({v} : Finset (Fin 6)))
          (mis_singleton_k6 G hK)
          (fun a b hab heq => hab (Finset.singleton_injective heq))
        rw [hsz] at hfb
        omega

lemma solve_size3 (G : SimpleGraph (Fin 6)) (C : AndCountCircuit 6)
    (hfit : Fits G C) (hout : C.outVars = ∅)
    (hdisj : ∀ i : Fin C.size, Disjoint (C.leftVars i) (C.rightVars i))
    (hsz : C.size = 3) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y := by
  classical
  by_cases h3 : ∃ a b c : Fin 6, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬ G.Adj a b ∧ ¬ G.Adj a c ∧ ¬ G.Adj b c
  · obtain ⟨a, b, c, hab, hac, hbc, eab, eac, ebc⟩ := h3
    let S : Finset (Fin 6) := {a, b, c}
    have hS : isIndep G S := isIndep_triple G a b c eab eac ebc
    have hcard : S.card = 3 := by
      have ha : a ∉ ({b, c} : Finset (Fin 6)) := by simp [hab, hac]
      have hb : b ∉ ({c} : Finset (Fin 6)) := by simp [hbc]
      rw [show S = insert a (insert b {c}) from rfl,
        Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb, Finset.card_singleton]
    obtain ⟨k, X, Y, hk, hcov⟩ := bc_of_indep_card G S hS
    exact ⟨k, X, Y, by rw [hcard] at hk; omega, hcov⟩
  · by_cases h2 : ∃ a b : Fin 6, a ≠ b ∧ ¬ G.Adj a b
    · obtain ⟨a0, b0, hab, hnab⟩ := h2
      have hno3 : ∀ a b c : Fin 6, a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj b c ∨ G.Adj a c := by
        intro a b c hab' hac' hbc'
        by_contra hnone
        push_neg at hnone
        exact h3 ⟨a, b, c, hab', hac', hbc', hnone.1, hnone.2.2, hnone.2.1⟩
      exact solve_tf_canon G C hfit hout hdisj (Or.inr hsz) hno3 a0 b0 hab hnab
    · have hK : ∀ a b : Fin 6, a ≠ b → G.Adj a b := by
        intro a b hab
        by_contra hna
        exact h2 ⟨a, b, hab, hna⟩
      obtain ⟨k, X, Y, hk, hcov⟩ := cover_k6 G hK
      exact ⟨k, X, Y, by omega, hcov⟩

lemma solve_size_ge4 (G : SimpleGraph (Fin 6)) (C : AndCountCircuit 6) (hle : 4 ≤ C.size) :
    ∃ (k : Nat) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ Cover G k X Y := by
  classical
  by_cases h2 : ∃ a b : Fin 6, a ≠ b ∧ ¬ G.Adj a b
  · obtain ⟨a, b, hab, hnab⟩ := h2
    let S : Finset (Fin 6) := {a, b}
    have hS : isIndep G S := isIndep_pair G a b hnab
    have hcard : S.card = 2 := by
      rw [show S = insert a {b} from rfl,
        Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
    obtain ⟨k, X, Y, hk, hcov⟩ := bc_of_indep_card G S hS
    exact ⟨k, X, Y, by rw [hcard] at hk; omega, hcov⟩
  · have hK : ∀ a b : Fin 6, a ≠ b → G.Adj a b := by
      intro a b hab
      by_contra hna
      exact h2 ⟨a, b, hab, hna⟩
    obtain ⟨k, X, Y, hk, hcov⟩ := cover_k6 G hK
    exact ⟨k, X, Y, by omega, hcov⟩

theorem main : ∀ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → ∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧ (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)) := by
  intro G C ⟨_, hfit⟩
  let C' := stripCircuit C
  have hfit' : Fits G C' := by
    intro I hMIS
    have hf := hfit I hMIS.1 hMIS.2
    exact ⟨by rw [strip_eval_eq]; exact hf.1, fun u hu => by rw [strip_eval_eq]; exact hf.2 u hu⟩
  have hout' : C'.outVars = ∅ := outVars_empty G C' hfit'
  have hdisj' : ∀ i : Fin C'.size, Disjoint (C'.leftVars i) (C'.rightVars i) :=
    strip_disjoint C
  by_cases h0 : C'.size = 0
  · exact solve_size0 G C' hfit' hout' h0
  · by_cases h1 : C'.size = 1
    · exact solve_size1 G C' hfit' hout' hdisj' h1
    · by_cases h2 : C'.size = 2
      · exact solve_size2 G C' hfit' hout' hdisj' h2
      · by_cases h3 : C'.size = 3
        · exact solve_size3 G C' hfit' hout' hdisj' h3
        · exact solve_size_ge4 G C' (by omega)

end PEqualNP.Outside.L_meta_950

theorem PEqualNP.Outside.L_meta_950 :
    ∀ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → ∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧ (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)) :=
  PEqualNP.Outside.L_meta_950.main
