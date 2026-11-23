import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_958

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

def ind958 (s : Finset V) : Prop :=
  ∀ v ∈ s, ∀ w ∈ s, ¬ G.Adj v w

def common958 (s : Finset V) (F : Finset (Finset V)) : Finset V :=
  s.filter fun v => ∀ t ∈ F, v ∈ t

def union958 (s : Finset V) (F : Finset (Finset V)) : Finset V :=
  s ∪ F.biUnion id

theorem hajnal958 (a : ℕ) (bound : ∀ s, ind958 G s → s.card ≤ a)
    (s : Finset V) (hs : ind958 G s) (hcard : s.card = a)
    (F : Finset (Finset V))
    (hF : ∀ t ∈ F, ind958 G t ∧ t.card = a) :
    2 * a ≤ (common958 s F).card + (union958 s F).card := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [common958,union958,hcard]; omega
  | @insert t F ht ih =>
    have hF' : ∀ u ∈ F, ind958 G u ∧ u.card = a := by
      intro u hu
      exact hF u (Finset.mem_insert_of_mem hu)
    have ht' := hF t (Finset.mem_insert_self t F)
    have prev := ih hF'
    let A := common958 s F
    let B := union958 s F
    have nextA : common958 s (insert t F) = A ∩ t := by
      ext v
      simp [A,common958,and_comm,and_left_comm]
    have nextB : union958 s (insert t F) = B ∪ t := by
      ext v
      simp [B,union958,or_comm]
    have agrees : ∀ v ∈ A, ∀ w ∈ B, ¬ G.Adj v w := by
      intro v hv w hw
      obtain ⟨vs, vf⟩ := Finset.mem_filter.mp hv
      rcases Finset.mem_union.mp hw with ws|wf
      · exact hs v vs w ws
      · obtain ⟨u, uf, wu⟩ := Finset.mem_biUnion.mp wf
        exact (hF' u uf).1 v (vf u uf) w wu
    have a_in_b : A ⊆ B := by
      intro v hv
      exact Finset.mem_union_left _ (Finset.mem_filter.mp hv).1
    have independent : ind958 G ((A \ t) ∪ (t ∩ B)) := by
      intro v hv w hw
      rcases Finset.mem_union.mp hv with va|vt <;> rcases Finset.mem_union.mp hw with wa|wt
      · exact agrees v (Finset.mem_sdiff.mp va).1 w (a_in_b (Finset.mem_sdiff.mp wa).1)
      · exact agrees v (Finset.mem_sdiff.mp va).1 w (Finset.mem_inter.mp wt).2
      · intro edge
        exact agrees w (Finset.mem_sdiff.mp wa).1 v (Finset.mem_inter.mp vt).2 edge.symm
      · exact ht'.1 v (Finset.mem_inter.mp vt).1 w (Finset.mem_inter.mp wt).1
    have dis : Disjoint (A \ t) (t ∩ B) := by
      rw [Finset.disjoint_left]
      exact fun v hv hw => (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp hw).1
    have q := bound _ independent
    rw [Finset.card_union_of_disjoint dis] at q
    have part := Finset.card_sdiff_add_card_inter A t
    have cover := Finset.card_union_add_card_inter B t
    rw [Finset.inter_comm B t] at cover
    rw [nextA,nextB]
    change 2 * a ≤ A.card + B.card at prev
    omega

theorem coreOrder958 (a : ℕ) (bound : ∀ s, ind958 G s → s.card ≤ a)
    (s : Finset V) (hs : ind958 G s) (hsize : s.card = a)
    (avoidable : ∀ v : V, ∃ t : Finset V, ind958 G t ∧ t.card = a ∧ v ∉ t) :
    2 * a ≤ Fintype.card V := by
  classical
  let F := Finset.univ.filter fun t : Finset V => ind958 G t ∧ t.card = a
  have h := hajnal958 G a bound s hs hsize F (fun t ht => (Finset.mem_filter.mp ht).2)
  have e : common958 s F = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    obtain ⟨t, hi, hc, hn⟩ := avoidable v
    exact hn ((Finset.mem_filter.mp hv).2 t (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,hc⟩))
  rw [e,Finset.card_empty,Nat.zero_add] at h
  exact h.trans (Finset.card_le_univ _)

def defect958 (D : Finset V) : Prop :=
  ∀ I ⊆ D, ind958 G I → I.card + 4 ≤ D.card

theorem extractSet958 {n : ℕ} (G : SimpleGraph (Fin n))
    (minimum : ∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → 4 ≤ T.card) :
    ∃ D : Finset (Fin n), defect958 G D ∧ 4 ≤ D.card ∧
      ∀ v ∈ D, ∃ I ⊆ D, ind958 G I ∧ I.card + 4 = D.card ∧ v ∉ I := by
  classical
  have whole : defect958 G Finset.univ := by
    intro I _ hi
    have hc := minimum (Finset.univ \ I) (by
      intro v w edge
      by_cases hv : v ∈ I
      · right
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hw => hi _ hv _ hw edge⟩
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩))
    have eq := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I)
    omega
  let family := Finset.univ.filter (defect958 G)
  obtain ⟨D, hD, least⟩ := Finset.exists_min_image family Finset.card
    ⟨Finset.univ,Finset.mem_filter.mpr ⟨Finset.mem_univ _,whole⟩⟩
  have hard : defect958 G D := (Finset.mem_filter.mp hD).2
  have nontriv := hard ∅ (Finset.empty_subset _) (by simp [ind958])
  refine ⟨D,hard,by simpa using nontriv,?_⟩
  intro v hv
  have hdrop : ¬ defect958 G (D.erase v) := by
    intro good
    exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem hv))
      (least _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, good⟩))
  unfold defect958 at hdrop
  push Not at hdrop
  obtain ⟨I,his,hi,hsmall⟩ := hdrop
  have inside := his.trans (Finset.erase_subset v D)
  have bound := hard I inside hi
  have erased := Finset.card_erase_of_mem hv
  refine ⟨I,inside,hi,by omega,?_⟩
  exact fun member => Finset.notMem_erase _ _ (his member)

def critical958 {m : ℕ} (H : SimpleGraph (Fin m)) : Prop :=
  4 ≤ m ∧ (∀ I, ind958 H I → I.card + 4 ≤ m) ∧
    ∀ v : Fin m, ∃ I, ind958 H I ∧ I.card + 4 = m ∧ v ∉ I

theorem extractCore958 {n : ℕ} (G : SimpleGraph (Fin n))
    (minimum : ∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → 4 ≤ T.card) :
    ∃ (m : ℕ) (f : Fin m ↪ Fin n), m ≤ 8 ∧ critical958 (G.comap f) := by
  classical
  obtain ⟨D,hard,hd,avoid⟩ := extractSet958 G minimum
  let f := (D.orderEmbOfFin rfl).toEmbedding
  let H := G.comap f
  have all : Finset.map f Finset.univ = D := Finset.map_orderEmbOfFin_univ _ _
  have transfer (I : Finset (Fin D.card)) : ind958 H I ↔ ind958 G (I.map f) := by
    constructor
    · intro hi v hv w hw
      obtain ⟨v, vi, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨w, wi, rfl⟩ := Finset.mem_map.mp hw
      exact hi v vi w wi
    · intro hi v hv w hw
      exact hi (f v) (Finset.mem_map.mpr ⟨v,hv,rfl⟩) (f w) (Finset.mem_map.mpr ⟨w,hw,rfl⟩)
  have upper (I : Finset (Fin D.card)) (hi : ind958 H I) : I.card + 4 ≤ D.card := by
    have h := hard (I.map f) ((Finset.map_subset_map.mpr (Finset.subset_univ I)).trans all.subset) ((transfer I).mp hi)
    simpa using h
  have omitV (v : Fin D.card) : ∃ I, ind958 H I ∧ I.card + 4 = D.card ∧ v ∉ I := by
    obtain ⟨J,js,ji,jc,jv⟩ := avoid (f v) (D.orderEmbOfFin_mem rfl v)
    let I := Finset.univ.filter fun i => f i ∈ J
    have eq : I.map f = J := by
      ext w
      constructor
      · intro hw
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hw
        exact (Finset.mem_filter.mp hi).2
      · intro hw
        have hd' := js hw
        rw [← all] at hd'
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hd'
        exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩,rfl⟩
    refine ⟨I,(transfer I).mpr (eq ▸ ji),?_,fun hi => jv (Finset.mem_filter.mp hi).2⟩
    rw [← eq,Finset.card_map] at jc
    exact jc
  obtain ⟨s,si,sz,_⟩ := omitV ⟨0,by omega⟩
  have bound : 2 * (D.card - 4) ≤ Fintype.card (Fin D.card) :=
    coreOrder958 H _ (fun I hi => by have := upper I hi; omega) s si (by omega) (by
      intro v
      obtain ⟨I,hi,hc,hn⟩ := omitV v
      exact ⟨I,hi,by omega,hn⟩)
  rw [Fintype.card_fin] at bound
  exact ⟨D.card,f,by omega,hd,upper,omitV⟩


def maxInd958 {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  ind958 G I ∧ ∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v

theorem extendInd958 {n : ℕ} (G : SimpleGraph (Fin n)) (J : Finset (Fin n)) (hj : ind958 G J) :
    ∃ K, J ⊆ K ∧ maxInd958 G K := by
  classical
  let F := Finset.univ.filter fun T : Finset (Fin n) => J ⊆ T ∧ ind958 G T
  obtain ⟨K,hK,large⟩ := Finset.exists_max_image F Finset.card
    ⟨J,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.Subset.rfl,hj⟩⟩
  obtain ⟨jk,ki⟩ := (Finset.mem_filter.mp hK).2
  refine ⟨K,jk,ki,?_⟩
  intro u hu
  by_contra! isolated
  have more : ind958 G (insert u K) := by
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with ea | haK
    · subst a
      rcases Finset.mem_insert.mp hb with eb | hbK
      · subst b
        exact G.loopless.irrefl _
      · exact isolated _ hbK
    · rcases Finset.mem_insert.mp hb with eb | hbK
      · subst b
        exact fun e => isolated _ haK e.symm
      · exact ki _ haK _ hbK
  have greater := large (insert u K) (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,jk.trans (Finset.subset_insert _ _),more⟩)
  rw [Finset.card_insert_of_notMem hu] at greater
  omega

theorem extendCore958 {n m : ℕ} (G : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n)
    (I : Finset (Fin m)) (hi : maxInd958 (G.comap f) I) :
    ∃ K, maxInd958 G K ∧ ∀ v, f v ∈ K ↔ v ∈ I := by
  have ji : ind958 G (I.map f) := by
    intro v hv w hw
    obtain ⟨v,vi,rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨w,wi,rfl⟩ := Finset.mem_map.mp hw
    exact hi.1 v vi w wi
  obtain ⟨K,ik,mk⟩ := extendInd958 G (I.map f) ji
  refine ⟨K,mk,fun v => ⟨?_,fun hv => ik (Finset.mem_map.mpr ⟨v,hv,rfl⟩)⟩⟩
  intro vk
  by_contra hv
  obtain ⟨w,wi,e⟩ := hi.2 v hv
  exact mk.1 _ vk _ (ik (Finset.mem_map.mpr ⟨w,wi,rfl⟩)) e

theorem outEmpty958 {n : ℕ} (G : SimpleGraph (Fin n))
    (C : PEqualNP.AndCount.AndCountCircuit n)
    (rows : ∀ K, maxInd958 G K → C.eval K = false) :
    C.outVars = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro v read
  have ind : ind958 G {v} := by simp [ind958]
  obtain ⟨K,mem,mk⟩ := extendInd958 G {v} ind
  have value : C.eval K = true := by
    unfold PEqualNP.AndCount.AndCountCircuit.eval
    apply decide_eq_true
    exact Or.inl ⟨v,read,mem (Finset.mem_singleton_self _)⟩
  rw [rows K mk] at value
  exact Bool.noConfusion value

def encode958 (p : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k+1 => if p k then encode958 p k ||| 2^k else encode958 p k

theorem bit_encode958 (p : ℕ → Bool) (k i : ℕ) :
    (encode958 p k).testBit i = (decide (i < k) && p i) := by
  induction k with
  | zero => simp [encode958]
  | succ k ih =>
    by_cases eq : k = i
    · subst i
      cases h : p k <;> simp [encode958,h,ih,Nat.testBit_or]
    · have lt : (i < k+1) = (i < k) := propext (by omega)
      cases h : p k <;> simp [encode958,h,ih,Nat.testBit_or,eq,lt]

theorem bound_encode958 (p : ℕ → Bool) (k : ℕ) : encode958 p k < 2^k := by
  induction k with
  | zero => simp [encode958]
  | succ k ih =>
    have h : 2^k < 2^(k+1) := Nat.pow_lt_pow_right (by decide) (by omega)
    cases b : p k
    · simpa [encode958,b] using ih.trans h
    · simpa [encode958,b] using Nat.or_lt_two_pow (ih.trans h) h

theorem mask_eq_zero958 (a b : ℕ) :
    a &&& b = 0 ↔ ∀ i, a.testBit i = true → b.testBit i = false := by
  constructor
  · intro h i hi
    have hb := congrArg (fun x : Nat => x.testBit i) h
    simpa [Nat.testBit_and,hi] using hb
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    cases hi : a.testBit i with
    | false => simp [Nat.testBit_and,hi]
    | true => simp [Nat.testBit_and,hi,h i hi]

def inMask958 {k : ℕ} (S : Finset (Fin k)) : ℕ :=
  encode958 (fun i => if h : i < k then decide (⟨i,h⟩ ∈ S) else false) k

theorem bit_inMask958 {k : ℕ} (S : Finset (Fin k)) (i : ℕ) :
    (inMask958 S).testBit i = if h : i < k then decide (⟨i,h⟩ ∈ S) else false := by
  unfold inMask958
  rw [bit_encode958]
  split <;> simp_all


-- The fuel recurrence is adapted from the checked L-meta-906.
open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
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

theorem sideTrue_iff {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v : Fin k → Bool) :
    sideTrue U B F i v = true ↔ ((∃ x ∈ B, x ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := by
  unfold sideTrue
  exact decide_eq_true_iff

theorem sideTrue_mono {n k : ℕ} (U U' B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v w : Fin k → Bool) (hU : U ⊆ U') (h : ∀ j, j < i → v j = true → w j = true)
    (hs : sideTrue U B F i v = true) : sideTrue U' B F i w = true := by
  rw [sideTrue_iff] at hs ⊢
  rcases hs with ⟨x, hx, hxU⟩ | ⟨j, hj, hji, hv⟩
  · exact Or.inl ⟨x, hx, hU hxU⟩
  · exact Or.inr ⟨j, hj, hji, h j hji hv⟩

theorem fuel_succ {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ d : ℕ, ∀ i : Fin C.size, i.val < d →
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

theorem gateVal_rec {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h := fuel_succ C U C.size i i.isLt
  exact h.symm

theorem gateVal_iff {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔
      (((∃ x ∈ C.leftVars i, x ∈ U) ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal U j = true) ∧
       ((∃ x ∈ C.rightVars i, x ∈ U) ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal U j = true)) := by
  rw [gateVal_rec, Bool.and_eq_true, sideTrue_iff, sideTrue_iff]




def hit958 (a b : Nat) : Bool := a &&& b != 0

def pickBool958 : Nat → List Bool → Bool
  | _, [] => false
  | m, x :: xs => (m % 2 == 1 && x) || pickBool958 (m / 2) xs

def pickMask958 : Nat → List Nat → Nat
  | _, [] => 0
  | m, x :: xs => (if m % 2 == 1 then x else 0) ||| pickMask958 (m / 2) xs

def evalGates958 (bare : Nat) : Nat → List Bool → List (Nat × Nat) → List Bool
  | _, ys, [] => ys
  | j, ys, ab :: tail =>
    let left := hit958 (2 ^ (2*j)) bare || pickBool958 ab.1 ys
    let right := hit958 (2 ^ (2*j+1)) bare || pickBool958 ab.2 ys
    evalGates958 bare (j+1) (ys ++ [left && right]) tail

def evalShape958 (links : List (Nat × Nat)) (outs bare : Nat) : Bool :=
  pickBool958 outs (evalGates958 bare 0 [] links)

def resolveGates958 : Nat → Nat → List Nat → List (Nat × Nat) → List Nat
  | _, _, ys, [] => ys
  | sig, j, ys, ab :: tail =>
    let side := if sig % 2 == 1 then ab.2 else ab.1
    let col := 2 ^ (2*j + sig % 2) ||| pickMask958 side ys
    resolveGates958 (sig/2) (j+1) (ys ++ [col]) tail

def resolve958 (links : List (Nat × Nat)) (outs sig : Nat) : Nat :=
  pickMask958 outs (resolveGates958 sig 0 [] links)

def insertClause958 (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a < b then a :: b :: bs else if a = b then b :: bs else b :: insertClause958 a bs

def trimClauses958 (cs : List Nat) : List Nat := cs.foldr insertClause958 []

theorem memInsertClause958 (x a : Nat) (cs : List Nat) :
    x ∈ insertClause958 a cs ↔ x = a ∨ x ∈ cs := by
  induction cs with
  | nil => simp [insertClause958]
  | cons b bs ih =>
    by_cases lt : a < b
    · simp [insertClause958,lt]
    · by_cases eq : a = b
      · subst b; simp [insertClause958]
      · simp [insertClause958,lt,eq,ih,or_left_comm]

theorem memTrimClauses958 (x : Nat) (cs : List Nat) : x ∈ trimClauses958 cs ↔ x ∈ cs := by
  induction cs with
  | nil => rfl
  | cons a xs ih =>
    simpa only [trimClauses958,List.foldr_cons,memInsertClause958,List.mem_cons] using or_congr Iff.rfl ih

theorem lenTrimClauses958 (cs : List Nat) : (trimClauses958 cs).length ≤ cs.length := by
  have add (a : Nat) (l : List Nat) : (insertClause958 a l).length ≤ l.length+1 := by
    induction l with
    | nil => simp [insertClause958]
    | cons b bs ih =>
      simp only [insertClause958]
      split <;> simp_all
      split <;> simp_all
  induction cs with
  | nil => decide
  | cons a xs ih =>
    exact (add a _).trans (Nat.succ_le_succ ih)

def clauseList958 (links : List (Nat × Nat)) (outs : Nat) : List Nat :=
  trimClauses958 ((List.range 8).map (resolve958 links outs))

theorem hit_or958 (a b x : Nat) :
    hit958 (a ||| b) x = (hit958 a x || hit958 b x) := by
  apply Bool.eq_iff_iff.mpr
  simp [hit958,Nat.and_or_distrib_right,Nat.or_eq_zero_iff]
  tauto

theorem pickHit958 (r b : Nat) (xs : List Nat) :
    hit958 (pickMask958 r xs) b = pickBool958 r (xs.map fun x => hit958 x b) := by
  induction xs generalizing r with
  | nil => simp [pickMask958,pickBool958,hit958]
  | cons x xs ih =>
    cases h : (r % 2 == 1) <;> simp [pickMask958,pickBool958,h,hit_or958,ih]

def Below958 (a b : Bool) : Prop := a = true → b = true

theorem pickMono958 {a b : List Bool} (hs : List.Forall₂ Below958 a b) (m : Nat) :
    Below958 (pickBool958 m a) (pickBool958 m b) := by
  induction hs generalizing m with
  | nil => exact id
  | cons h _ ih =>
    intro e
    simp only [pickBool958,Bool.or_eq_true,Bool.and_eq_true] at *
    rcases e with ⟨r,t⟩|t
    · exact Or.inl ⟨r,h t⟩
    · exact Or.inr (ih _ t)

theorem resolveUpperAux958 (bare : Nat) (links : List (Nat × Nat))
    (sig j : Nat) (bs : List Bool) (ms : List Nat)
    (le : List.Forall₂ Below958 bs (ms.map fun c => hit958 c bare)) :
    List.Forall₂ Below958 (evalGates958 bare j bs links)
      ((resolveGates958 sig j ms links).map fun c => hit958 c bare) := by
  induction links generalizing sig j bs ms with
  | nil => exact le
  | cons ab tail ih =>
    simp only [evalGates958,resolveGates958]
    apply ih
    rw [List.map_append]
    apply List.rel_append le
    apply List.Forall₂.cons _ .nil
    intro h
    simp only [Bool.and_eq_true,Bool.or_eq_true] at h
    have bit : sig % 2 = 0 ∨ sig % 2 = 1 := by omega
    rcases bit with z|o
    · simp [z,hit_or958,pickHit958]
      exact h.1.imp_right (pickMono958 le ab.1)
    · simp only [o, beq_self_eq_true, ↓reduceIte, hit_or958,pickHit958,Bool.or_eq_true]
      exact h.2.imp_right (pickMono958 le ab.2)

theorem resolveEqualAux958 (bare : Nat) (links : List (Nat × Nat)) (j : Nat)
    (ms : List Nat) :
    ∃ sig < 2^links.length,
      ((resolveGates958 sig j ms links).map fun c => hit958 c bare) =
        evalGates958 bare j (ms.map fun c => hit958 c bare) links := by
  induction links generalizing j ms with
  | nil => exact ⟨0,by simp,rfl⟩
  | cons ab tail ih =>
    let l := 2 ^ (2*j) ||| pickMask958 ab.1 ms
    let r := 2 ^ (2*j+1) ||| pickMask958 ab.2 ms
    let choose := if hit958 l bare then 1 else 0
    let c := if choose = 1 then r else l
    obtain ⟨sig,lt,eq⟩ := ih (j+1) (ms++[c])
    have bound : choose ≤ 1 := by simp [choose]; split <;> omega
    have mod : (2*sig+choose) % 2 = choose := by omega
    have div : (2*sig+choose)/2 = sig := by omega
    refine ⟨2*sig+choose,?_,?_⟩
    · simp [pow_succ]; omega
    · simp only [resolveGates958,evalGates958,div,mod]
      by_cases hl : hit958 l bare = true
      · have hc : choose = 1 := by simp [choose,hl]
        have eq' := eq
        rw [List.map_append] at eq'
        have hh := hl
        simp only [l,hit_or958,pickHit958] at hh
        simpa [hc,c,r,hit_or958,pickHit958,hh] using eq'
      · have hc : choose = 0 := by simp [choose,hl]
        have eq' := eq
        rw [List.map_append] at eq'
        have hh : hit958 l bare = false := Bool.eq_false_iff.mpr hl
        simp only [l,hit_or958,pickHit958] at hh
        simpa [hc,c,l,hit_or958,pickHit958,hh] using eq'

theorem eval_allClauses958 (links : List (Nat × Nat)) (three : links.length = 3)
    (outs bare : Nat) :
    evalShape958 links outs bare = true ↔
      ∀ c ∈ clauseList958 links outs, hit958 c bare = true := by
  have members (c : Nat) : c ∈ clauseList958 links outs ↔
      ∃ sig < 8, resolve958 links outs sig = c := by
    simp [clauseList958,memTrimClauses958]
  constructor
  · intro e c hc
    obtain ⟨sig,_,rfl⟩ := (members c).mp hc
    rw [resolve958,pickHit958]
    exact pickMono958 (resolveUpperAux958 bare links sig 0 [] [] .nil) outs e
  · intro h
    obtain ⟨sig,lt,exactSig⟩ := resolveEqualAux958 bare links 0 []
    have t := h _ ((members _).mpr ⟨sig,by simpa [three] using lt,rfl⟩)
    simpa only [resolve958,pickHit958,exactSig,evalShape958,List.map_nil] using t

theorem clauseCap958 (links : List (Nat × Nat)) (outs : Nat) :
    (clauseList958 links outs).length ≤ 8 := by
  simpa [clauseList958] using lenTrimClauses958 ((List.range 8).map (resolve958 links outs))




def occ958 {n : ℕ} (side : ℕ → Finset (Fin n)) (v : Fin n) : ℕ :=
  encode958 (fun i => decide (v ∈ side i)) 6

def row958 {n : ℕ} (side : ℕ → Finset (Fin n)) (K : Finset (Fin n)) : ℕ :=
  encode958 (fun i => decide (∃ v ∈ K, v ∈ side i)) 6

theorem row_insert958 {n : ℕ} (side : ℕ → Finset (Fin n)) (K : Finset (Fin n)) (u : Fin n) :
    row958 side (insert u K) = row958 side K ||| occ958 side u := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < 6
  · simp [row958,occ958,bit_encode958,Nat.testBit_or,h,Bool.or_comm]
  · simp [row958,occ958,bit_encode958,Nat.testBit_or,h]

theorem realizeCore958 {n m : ℕ} (G : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n)
    (C : PEqualNP.AndCount.AndCountCircuit n) (side : ℕ → Finset (Fin n)) (clauses : List ℕ)
    (character : ∀ K, C.eval K = true ↔ ∀ c ∈ clauses, row958 side K &&& c ≠ 0)
    (rows : ∀ K, maxInd958 G K → C.eval K = false ∧ ∀ u, u ∉ K → C.eval (insert u K) = true)
    (I : Finset (Fin m)) (hi : maxInd958 (G.comap f) I) :
    ∃ c ∈ clauses, ∀ v : Fin m, decide (v ∈ I) = decide (occ958 side (f v) &&& c = 0) := by
  classical
  obtain ⟨K,hK,agrees⟩ := extendCore958 G f I hi
  obtain ⟨base,more⟩ := rows K hK
  have missing : ¬ ∀ c ∈ clauses, row958 side K &&& c ≠ 0 := by
    intro h
    have t := (character K).mpr h
    rw [base] at t
    exact Bool.noConfusion t
  push Not at missing
  obtain ⟨c,hc,zero⟩ := missing
  refine ⟨c,hc,?_⟩
  intro v
  have joined : row958 side (insert (f v) K) &&& c = occ958 side (f v) &&& c := by
    rw [row_insert958,Nat.and_or_distrib_right,zero,Nat.zero_or]
  by_cases hv : v ∈ I
  · rw [Finset.insert_eq_of_mem ((agrees v).mpr hv),zero] at joined
    simp [hv,joined.symm]
  · have hk : f v ∉ K := fun h => hv ((agrees v).mp h)
    have nonzero := (character _).mp (more _ hk) c hc
    rw [joined] at nonzero
    simp [hv,nonzero]

theorem chooseBool958 (mask : ℕ) (xs : List Bool) :
    pickBool958 mask xs = true ↔ ∃ j, xs[j]? = some true ∧ mask.testBit j = true := by
  induction xs generalizing mask with
  | nil => simp [pickBool958]
  | cons x xs ih =>
    rw [pickBool958,Bool.or_eq_true,Bool.and_eq_true,ih]
    constructor
    · rintro (⟨hm,hx⟩|⟨j,hj,hm⟩)
      · exact ⟨0,by simp [hx],by simpa using hm⟩
      · exact ⟨j+1,by simpa using hj,by simpa [Nat.testBit_succ] using hm⟩
    · rintro ⟨j,hj,hm⟩
      cases j with
      | zero => exact Or.inl ⟨by simpa using hm,by simpa using hj⟩
      | succ j => exact Or.inr ⟨j,by simpa using hj,by simpa [Nat.testBit_succ] using hm⟩

theorem hitBit958 (i b : ℕ) : hit958 (2^i) b = b.testBit i := by
  have h : 2^i &&& b = 0 ↔ b.testBit i = false := by
    rw [mask_eq_zero958]
    constructor
    · exact fun t => t i (by simp)
    · intro h j hj
      have ij : i = j := by simpa [Nat.testBit_two_pow] using hj
      simpa [← ij] using h
  cases e : b.testBit i <;> simp [hit958,h,e]

def readVars958 {n : ℕ} (C : AndCountCircuit n) (j : ℕ) (r : Bool) : Finset (Fin n) :=
  if h : j < C.size then
    if r then C.rightVars ⟨j,h⟩ else C.leftVars ⟨j,h⟩
  else ∅

def readGates958 {n : ℕ} (C : AndCountCircuit n) (j : ℕ) (r : Bool) : Finset (Fin C.size) :=
  if h : j < C.size then
    if r then C.rightGates ⟨j,h⟩ else C.leftGates ⟨j,h⟩
  else ∅

def selected958 {k : ℕ} (S : Finset (Fin k)) (j : ℕ) : ℕ :=
  encode958 (fun i => if h : i < k then decide (⟨i,h⟩ ∈ S) else false) j

def rawLink958 {n : ℕ} (C : AndCountCircuit n) (j : ℕ) (r : Bool) :=
  selected958 (readGates958 C j r) j

def link958 {n : ℕ} (C : AndCountCircuit n) (j : ℕ) : ℕ × ℕ :=
  let l := rawLink958 C j false
  let r := rawLink958 C j true
  if l ≤ r then (l,r) else (r,l)

def physical958 {n : ℕ} (C : AndCountCircuit n) (i : ℕ) : Finset (Fin n) :=
  let j := i / 2
  let right := decide (i % 2 = 1)
  if rawLink958 C j false ≤ rawLink958 C j true then readVars958 C j right
  else readVars958 C j (!right)

theorem linkBounds958 {n : ℕ} (C : AndCountCircuit n) (j : ℕ) :
    (link958 C j).1 ≤ (link958 C j).2 ∧ (link958 C j).2 < 2^j := by
  have hl := bound_encode958 (fun i => if h : i < C.size then decide (⟨i,h⟩ ∈ readGates958 C j false) else false) j
  have hr := bound_encode958 (fun i => if h : i < C.size then decide (⟨i,h⟩ ∈ readGates958 C j true) else false) j
  change rawLink958 C j false < 2^j at hl
  change rawLink958 C j true < 2^j at hr
  by_cases h : rawLink958 C j false ≤ rawLink958 C j true
  · simpa only [link958,ite_eq_left h] using And.intro h hr
  · simpa only [link958,ite_eq_right h] using And.intro (le_of_not_ge h) hl

def value958 {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin n)) (i : ℕ) : Bool :=
  if h : i < C.size then C.gateVal K ⟨i,h⟩ else false

def prefix958 {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin n)) (j : ℕ) : List Bool :=
  (List.range j).map (value958 C K)

theorem selectPrefix958 {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin n)) (j : ℕ)
    (S : Finset (Fin C.size)) :
    pickBool958 (selected958 S j) (prefix958 C K j) = true ↔
      ∃ i ∈ S, i.val < j ∧ C.gateVal K i = true := by
  rw [chooseBool958]
  constructor
  · rintro ⟨i,atI,mem⟩
    rw [selected958,bit_encode958,Bool.and_eq_true] at mem
    obtain ⟨hj,mem⟩ := mem
    have hj' : i < j := of_decide_eq_true hj
    split at mem
    next hi =>
      refine ⟨⟨i,hi⟩,of_decide_eq_true mem,hj',?_⟩
      simpa [prefix958,List.getElem?_eq_getElem,hj',value958,hi] using atI
    next => contradiction
  · rintro ⟨i,hi,hj,hv⟩
    refine ⟨i.val,?_,?_⟩
    · simp [prefix958,hj,value958,i.isLt,hv]
    · simp [selected958,bit_encode958,hj,i.isLt,hi]

theorem bareAt958 {n : ℕ} (side : ℕ → Finset (Fin n)) (K : Finset (Fin n)) {i : ℕ} (hi : i < 6) :
    hit958 (2^i) (row958 side K) = decide (∃ v ∈ side i, v ∈ K) := by
  rw [hitBit958,row958,bit_encode958]
  simp [hi,and_comm]

def rawValue958 {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin n)) (j : ℕ) (r : Bool) : Bool :=
  decide (∃ v ∈ readVars958 C j r, v ∈ K) || pickBool958 (rawLink958 C j r) (prefix958 C K j)

theorem rawAnd958 {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin n)) (j : ℕ) :
    (rawValue958 C K j false && rawValue958 C K j true) = value958 C K j := by
  apply Bool.eq_iff_iff.mpr
  by_cases hj : j < C.size
  · rw [show value958 C K j = C.gateVal K ⟨j,hj⟩ by simp [value958,hj],gateVal_iff]
    simp only [rawValue958,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,rawLink958,selectPrefix958]
    simp [readVars958,readGates958,hj]
    rfl
  · simp [rawValue958,rawLink958,selectPrefix958,readVars958,readGates958,hj,value958]

theorem step958 {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin n)) {j : ℕ} (hj : j < 3) :
    ((hit958 (2^(2*j)) (row958 (physical958 C) K) || pickBool958 (link958 C j).1 (prefix958 C K j)) &&
     (hit958 (2^(2*j+1)) (row958 (physical958 C) K) || pickBool958 (link958 C j).2 (prefix958 C K j))) =
    value958 C K j := by
  have half : (2*j+1)/2 = j := by omega
  rw [bareAt958 _ _ (by omega),bareAt958 _ _ (by omega),← rawAnd958]
  by_cases h : rawLink958 C j false ≤ rawLink958 C j true
  · simp [physical958,link958,rawValue958,half,h]
  · simp [physical958,link958,rawValue958,half,h,Bool.and_comm]

def links958 {n : ℕ} (C : AndCountCircuit n) : List (ℕ × ℕ) :=
  [link958 C 0,link958 C 1,link958 C 2]

theorem prefixNext958 {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin n)) (j : ℕ) :
    prefix958 C K j ++ [value958 C K j] = prefix958 C K (j+1) := by
  simp [prefix958,List.range_succ]

theorem fullEval958 {n : ℕ} (C : AndCountCircuit n) (K : Finset (Fin n)) (size : C.size ≤ 3)
    (out : C.outVars = ∅) :
    evalShape958 (links958 C) (selected958 C.outGates 3) (row958 (physical958 C) K) = C.eval K := by
  have histories :
      evalGates958 (row958 (physical958 C) K) 0 (prefix958 C K 0) (links958 C) = prefix958 C K 3 := by
    simp only [links958,evalGates958,step958 C K (by decide : 0 < 3),
      step958 C K (by decide : 1 < 3),step958 C K (by decide : 2 < 3),
      prefixNext958]
  unfold evalShape958
  rw [show ([] : List Bool) = prefix958 C K 0 from rfl,histories]
  apply Bool.eq_iff_iff.mpr
  rw [selectPrefix958,AndCountCircuit.eval,decide_eq_true_iff]
  simp only [out,Finset.notMem_empty,false_and,exists_false, false_or]
  exact ⟨fun ⟨i,hi,_,hv⟩ => ⟨i,hi,hv⟩,fun ⟨i,hi,hv⟩ => ⟨i,hi,lt_of_lt_of_le i.isLt size,hv⟩⟩

theorem physicalClauses958 {n : ℕ} (C : AndCountCircuit n) (size : C.size ≤ 3) (out : C.outVars = ∅)
    (K : Finset (Fin n)) :
    C.eval K = true ↔ ∀ c ∈ clauseList958 (links958 C) (selected958 C.outGates 3),
      row958 (physical958 C) K &&& c ≠ 0 := by
  rw [← fullEval958 C K size out,eval_allClauses958 _ (by rfl)]
  simp [hit958,Nat.and_comm]

theorem coreAssignment958 {n m : ℕ} (G : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n)
    (C : AndCountCircuit n) (size : C.size ≤ 3)
    (rows : ∀ K, maxInd958 G K → C.eval K = false ∧ ∀ u, u ∉ K → C.eval (insert u K) = true) :
    ∀ I, maxInd958 (G.comap f) I →
      ∃ c ∈ clauseList958 (links958 C) (selected958 C.outGates 3),
        ∀ v : Fin m, decide (v ∈ I) = decide (occ958 (physical958 C) (f v) &&& c = 0) := by
  have out := outEmpty958 G C (fun K h => (rows K h).1)
  exact realizeCore958 G f C _ _ (physicalClauses958 C size out) rows

theorem outputMask958 {n : ℕ} (G : SimpleGraph (Fin n)) (C : AndCountCircuit n)
    (size : C.size ≤ 3)
    (minimum : ∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → 4 ≤ T.card)
    (rows : ∀ K, maxInd958 G K → C.eval K = false ∧ ∀ u, u ∉ K → C.eval (insert u K) = true) :
    0 < selected958 C.outGates 3 ∧ selected958 C.outGates 3 < 8 := by
  classical
  have edge : ∃ v w, G.Adj v w := by
    by_contra! none
    have imposs := minimum ∅ (fun v w hvw => (none v w hvw).elim)
    simp at imposs
  obtain ⟨v,w,adj⟩ := edge
  obtain ⟨K,vk,hK⟩ := extendInd958 G {v} (by simp [ind958])
  have wk : w ∉ K := fun h => hK.1 _ (vk (Finset.mem_singleton_self v)) _ h adj
  have yes := (rows K hK).2 w wk
  have empty := outEmpty958 G C (fun K k => (rows K k).1)
  rw [AndCountCircuit.eval,decide_eq_true_iff,empty] at yes
  simp only [Finset.notMem_empty,false_and,exists_false,false_or] at yes
  obtain ⟨i,mem,_⟩ := yes
  have below : i.val < 3 := lt_of_lt_of_le i.isLt size
  have on : (selected958 C.outGates 3).testBit i.val = true := by
    simp [selected958,bit_encode958,below,i.isLt,mem]
  have ne : selected958 C.outGates 3 ≠ 0 := by
    intro h
    simp [h] at on
  exact ⟨Nat.pos_of_ne_zero ne,bound_encode958 _ 3⟩


def prefixRow958 (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * prefixRow958 f n + (f n).toNat

def prefixCode958 (A : ℕ → ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => prefixCode958 A n * 2 ^ n + prefixRow958 (A n) n

def permOn958 (n : ℕ) (p : ℕ → ℕ) : Prop :=
  (∀ i < n, p i < n) ∧ ∀ i < n, ∀ j < n, p i = p j → i = j

def maximalCode958 (A : ℕ → ℕ → Bool) (n : ℕ) : Prop :=
  ∀ p, permOn958 n p → prefixCode958 (fun i j => A (p i) (p j)) n ≤ prefixCode958 A n

theorem rowSmall958 (f : ℕ → Bool) (n : ℕ) : prefixRow958 f n < 2^n := by
  induction n with
  | zero => simp [prefixRow958]
  | succ n ih =>
    rw [prefixRow958,pow_succ]
    cases f n <;> simp <;> omega

theorem rowCong958 {f g : ℕ → Bool} {n : ℕ} (h : ∀ i < n, f i = g i) :
    prefixRow958 f n = prefixRow958 g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixRow958,prefixRow958,h n (by omega), ih (fun i hi => h i (by omega))]

theorem codeCong958 {A B : ℕ → ℕ → Bool} {n : ℕ}
    (h : ∀ i < n, ∀ j < n, A i j = B i j) :
    prefixCode958 A n = prefixCode958 B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixCode958,prefixCode958,ih (fun i hi j hj => h i (by omega) j (by omega)),
      rowCong958 (fun j hj => h n (by omega) j (by omega))]

theorem prefixQuot958 (A : ℕ → ℕ → Bool) (n : ℕ) :
    prefixCode958 A (n+1) / 2^n = prefixCode958 A n := by
  rw [prefixCode958,Nat.mul_comm,Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (rowSmall958 _ _),Nat.add_zero]

theorem maximalPrefix958 {A : ℕ → ℕ → Bool} {n : ℕ} (h : maximalCode958 A (n+1)) :
    maximalCode958 A n := by
  intro p hp
  let q : ℕ → ℕ := fun i => if i<n then p i else i
  have hq : permOn958 (n+1) q := by
    constructor
    · intro i hi
      dsimp [q]
      split_ifs with h'
      · have := hp.1 i h'
        omega
      · exact hi
    · intro i hi j hj he
      dsimp [q] at he
      split_ifs at he with h' h'' h''
      · exact hp.2 i h' j h'' he
      · have := hp.1 i h'
        omega
      · have := hp.1 j h''
        omega
      · exact he
  have hle := Nat.div_le_div_right (c:=2^n) (h q hq)
  rw [prefixQuot958,prefixQuot958] at hle
  rw [← codeCong958 (A:=fun i j => A (q i) (q j))
    (B:=fun i j => A (p i) (p j)) (n:=n) (by
      intro i hi j hj
      simp [q,hi,hj])]
  exact hle

def widths958 : ℕ → ℕ
  | 0 => 0
  | n+1 => widths958 n + n

theorem codeSmall958 (A : ℕ → ℕ → Bool) (n : ℕ) :
    prefixCode958 A n < 2^(widths958 n) := by
  induction n with
  | zero => simp [widths958,prefixCode958]
  | succ n ih =>
    have hr := rowSmall958 (A n) n
    rw [prefixCode958,widths958,pow_add]
    calc
      _ < prefixCode958 A n * 2 ^ n + 2^n := by omega
      _ = (prefixCode958 A n + 1) * 2^n := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ ih

theorem hasMaximalCode958 (A : ℕ → ℕ → Bool) (n : ℕ) :
    ∃ p, permOn958 n p ∧ maximalCode958 (fun i j => A (p i) (p j)) n := by
  classical
  let S := (Finset.range (2^(widths958 n))).filter fun c =>
    ∃ p, permOn958 n p ∧ prefixCode958 (fun i j => A (p i) (p j)) n = c
  have hS : S.Nonempty := by
    refine ⟨prefixCode958 A n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (codeSmall958 A n), ?_⟩⟩
    exact ⟨id, (by simp [permOn958]), rfl⟩
  have hm := S.max'_mem hS
  obtain ⟨p,hp,he⟩ := (Finset.mem_filter.mp hm).2
  refine ⟨p,hp,?_⟩
  intro q hq
  rw [he]
  apply Finset.le_max'
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (codeSmall958 _ _), ⟨p ∘ q, ?_, rfl⟩⟩
  exact ⟨fun i hi => hp.1 _ (hq.1 i hi), fun i hi j hj h =>
    hq.2 i hi j hj (hp.2 _ (hq.1 i hi) _ (hq.1 j hj) h)⟩


def decodeEdge958 (n c i j : ℕ) : Bool :=
  let a := max i j
  let b := min i j
  decide (b<a ∧ a<n) && c.testBit (widths958 n - widths958 (a+1) + (a-1-b))

theorem widthsMono958 : Monotone widths958 :=
  monotone_nat_of_le_succ (fun n => by simp [widths958])

theorem rowBit958 (f : ℕ → Bool) {n j : ℕ} (hj : j<n) :
    (prefixRow958 f n).testBit (n-1-j) = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    have small : (f n).toNat < 2^1 := by cases f n <;> decide
    rw [prefixRow958,show 2 = 2^1 by decide,Nat.testBit_two_pow_mul_add _ small]
    by_cases eq : j=n
    · subst j
      simp
      cases f n <;> rfl
    · have hj' : j<n := by omega
      have hge : ¬ (n+1-1-j < 1) := by omega
      rw [ite_eq_right hge,show n+1-1-j-1 = n-1-j by omega]
      exact ih hj'

theorem codeBit958 (A : ℕ → ℕ → Bool) {n i j : ℕ} (hi : i<n) (hj : j < i) :
    (prefixCode958 A n).testBit (widths958 n - widths958 (i+1) + (i-1-j)) = A i j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [prefixCode958,Nat.mul_comm,Nat.testBit_two_pow_mul_add _ (rowSmall958 _ _)]
    by_cases e : i=n
    · subst i
      rw [Nat.sub_self,Nat.zero_add,ite_eq_left (by omega)]
      exact rowBit958 _ hj
    · have hin : i<n := by omega
      have hh := widthsMono958 (show i+1≤n by omega)
      rw [widths958,ite_eq_right (by omega), show widths958 n + n - widths958 (i+1) + (i-1-j) - n =
        widths958 n - widths958 (i+1) + (i-1-j) by omega]
      exact ih hin

theorem decodeCorrect958 (A : ℕ → ℕ → Bool) {n i j : ℕ} (hi : i<n) (hj : j<n)
    (symm : ∀ i<n, ∀ j<n, A i j = A j i)
    (loop : ∀ i<n, A i i = false) :
    decodeEdge958 n (prefixCode958 A n) i j = A i j := by
  rcases lt_trichotomy i j with h|h|h
  · simp [decodeEdge958,Nat.max_eq_right h.le,Nat.min_eq_left h.le,h,hj,
      codeBit958 A hj h,symm j hj i hi]
  · subst j
    simp [decodeEdge958,loop i hi]
  · simp [decodeEdge958,Nat.max_eq_left h.le,Nat.min_eq_right h.le,h,hi,codeBit958 A hi h]

theorem rowMod958 (A : ℕ → ℕ → Bool) (n : ℕ) :
    prefixCode958 A (n+1) % 2^n = prefixRow958 (A n) n := by
  rw [prefixCode958,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt (rowSmall958 _ _)]

theorem rowHalf958 (f : ℕ → Bool) (n : ℕ) :
    prefixRow958 f (n+1)/2 = prefixRow958 f n := by
  rw [prefixRow958,Nat.mul_add_div (by decide : 0 < 2)]
  cases f n <;> simp

theorem lastOrder958 (A : ℕ → ℕ → Bool) (k : ℕ) (h : maximalCode958 A (k+2)) :
    prefixRow958 (A (k+1)) (k+1) < 2 * (prefixCode958 A (k+1) % 2^k + 1) := by
  let q : ℕ → ℕ := Equiv.swap k (k+1)
  have small : ∀ i<k, q i = i := by
    intro i hi
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have qk : q k = k+1 := Equiv.swap_apply_left _ _
  have hq : permOn958 (k+2) q := by
    refine ⟨?_,fun _ _ _ _ he => (Equiv.swap k (k+1)).injective he⟩
    intro i hi
    rcases lt_trichotomy i k with hl|he|hr
    · rw [small i hl]
      omega
    · subst i
      rw [qk]
      omega
    · have e : i=k+1 := by omega
      subst i
      change Equiv.swap k (k+1) (k+1) < _
      rw [Equiv.swap_apply_right]
      omega
  have hle := Nat.div_le_div_right (c:=2^(k+1)) (h q hq)
  rw [prefixQuot958,prefixQuot958,prefixCode958,prefixCode958] at hle
  have e1 := codeCong958 (A:=fun i j => A (q i) (q j)) (B:=A) (n:=k) (by
    intro i hi j hj
    rw [small i hi,small j hj])
  have e2 := rowCong958 (f:=fun j => A (q k) (q j)) (g:=A (k+1)) (n:=k) (by
    intro i hi
    rw [qk,small i hi])
  rw [e1,e2] at hle
  rw [rowMod958]
  have fraction := rowHalf958 (A (k+1)) k
  omega


def graphWords958 : ℕ → Array ℕ
  | 0 => #[0x0]
  | 1 => #[0x0]
  | 2 => #[0x10000000]
  | 3 => #[0x7000000600000040000000]
  | 4 => #[0x3c0000038000003400000320000030000002100000200000000]
  | 5 => #[0x3c900003c800003c400003c100003c00000381000038000003480000344000034000003230000322000032000003010000300000021000002000000000]
  | 6 => #[0x78220007821000782000078010007800000702300070220007020000700000069100006908000690000068880006885000688400068810006880000680100068000006460000644300064420006440000640100064000006022000602000060000004201000420000040000000000,0x793000079280007920000791000079080007902000790000078840007883000788200078800007823]
  | 7 => #[0x1a214001a210401a210301a210201a210001a204201a204101a204001a200101a200001a004201a004001a00000191801019180001910c00191083019108201910800191001019100001900420190040019000001808800180801018080001800000108040010800001000000000000,0x1e084201e084101e084001e080101e080001e004301e004201e004001e000001c08c001c088401c088201c088001c080101c080001c000001a442001a441001a440001a421001a420901a420801a420101a420001a400101a400001a220a01a220801a220001a214601a214401a2142,0x1e420401e420101e420001e408501e408401e408301e408201e408101e408001e400101e400001e210701e210601e210401e210001e20c501e20c401e20c101e20c001e208501e208401e208301e208201e208101e208001e200101e200001e08c001e088401e088201e088001e0843,0x1e4c2101e4c2001e4c1001e4c0101e4c0001e4a1101e4a1001e4a0801e4a0501e4a0401e4a0101e4a0001e480101e480001e442001e441001e440401e440001e421001e420801e4205]
  | 8 => #[0xd002001d002000d000000c8c0082c8c0080c8c0000c886001c886000c884180c884103c884102c884100c884001c884000c880082c880080c880000c802102c802100c802001c802000c800000c044001c044000c040080c040000c00000084020018402000840000080000000000000,0xd10a204d10a201d10a200d10a100d10a001d10a000d108207d108206d108204d108200d108184d108181d108180d108104d108103d108102d108101d108100d108001d108000d102100d102082d102081d102080d102001d102000d100082d100080d100000d002104d002102d002100,0xd210480d210408d210403d210402d210400d210082d210081d210080d210001d210000d200082d200080d200000d110512d110510d11050bd11050ad110509d110508d110501d110500d110410d110409d110408d110405d110404d110401d110400d110001d110000d10a300d10a205,0xf000000e046001e046000e044208e044204e044200e044103e044102e044100e044001e044000e040080e040000e000000d221040d221020d221000d220820d220811d220810d220801d220800d220001d220000d210820d210812d210810d210802d210800d21048ad210488d210482,0xf044208f044204f044200f044105f044104f044103f044102f044101f044100f044001f044000f042180f042104f042102f042100f042083f042082f042081f042080f042001f042000f040083f040082f040080f040000f002184f002180f002104f002102f002100f002001f002000,0xf106082f106081f106080f106001f106000f104286f104284f104282f104280f104208f104206f104204f104202f104200f104183f104182f104180f104103f104102f104100f104083f104082f104081f104080f104001f104000f100083f100082f100080f100000f046001f046000,0xf204000f200083f200082f200080f200000f108388f108381f108380f10830bf10830af108309f108308f108303f108302f108301f108300f108209f108208f108205f108204f108201f108200f108001f108000f106284f106280f106208f106205f106204f106202f106201f106200,0xf210204f210203f210202f210201f210200f210083f210082f210081f210080f210001f210000f204288f204286f204284f204282f204280f204208f204206f204204f204202f204200f204183f204182f204180f204103f204102f204100f204083f204082f204081f204080f204001,0xf220800f220209f220208f220205f220204f220201f220200f220001f220000f210810f21080af210808f210800f21040bf21040af210408f210403f210402f210400f210289f210288f210287f210286f210285f210284f210283f210282f210281f210280f210209f210208f210205,0xf250800f25040bf25040af250408f250403f250402f250400f250283f250282f250280f250203f250202f250200f250083f250082f250081f250080f250001f250000f240083f240082f240080f240000f221040f221020f221008f221000f220820f220810f220809f220808f220801,0xf2610c0f2610a0f261080f261040f261020f261002f261000f260821f260820f260810f260809f260808f260803f260802f260801f260800f260083f260082f260081f260080f260001f260000f250890f25088af250888f250880f250820f250810f25080af250808f250802]
  | _ => #[]

def catalogSize958 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 8
  | 5 => 18
  | 6 => 44
  | 7 => 117
  | 8 => 351
  | _ => 0

def hintWords958 : ℕ → Array ℕ
  | 0 => #[0x0]
  | 1 => #[0x20000]
  | 2 => #[0x8000,0x1800200008004]
  | 3 => #[0x8000,0x40004,0x8014010c0040000800c,0x10842108241001c010c00140008018]
  | 4 => #[0x8000,0x8004,0xa00140008008,0x8000c,0x48009003800600048014,0x8028010c02180630024019400340008020,0x18002c,0x220040010c0218063003c0194003401c0034]
  | 5 => #[0x8000,0x8004,0x60008,0x8010,0xa00600008014,0x10001c,0x48009005800a00048024,0x219443280048009001a00340048030,0x1c0034,0xa804c01940328024004400220044020003c,0x8058010c02180430086018c03180830054019403280850019021c00440008050,0x805c,0xd001900008060,0x38006c,0x10001f003c0074,0xe801d0194032828500900118022000e8084,0x80a0010c02180430086018c0318083009c019403280850019021c02600008094,0x2184430868100ac010c02180430086018c031808300a8019403280850019021c008400080a4]
  | 6 => #[0x8000,0x8004,0x8008,0xa0014000800c,0x8010,0xc0014,0x80091aa40024000801c,0x8020,0x1a00a00008024,0x18002c,0x88011007800e00088034,0x2a1c54380088011002a00540088040,0x240044,0x804c,0x1a01500008050,0x2e0058,0x3201a00320060,0xe801d0042008400e807800e801c000e806c,0x2a14542800e801d0032022000e80840032020000e807c,0x80250194032806500ca0aa4025000080900aa400a400080290aa40094000808c,0x4e0098,0x1880b00194032806500ca0214042805600a8021c04380148029005a00b405200a0,0x80bc010c02180430086010c02180430086018c031806300c6020c04180a300b80194032806500ca021404280a50035021c04380a7002902a400b400080b4,0x80c0,0x6400c4,0x80d41aa4034000080cc,0x2a1c54388a700091aa400b400080d8,0x80dc,0x1d0039000080e0,0x7800ec,0x20003f007c00f4,0x810c1aa404200008104,0x2a1c54388a700091aa400240008110,0x8c0114,0x98012c02500490090011c,0x2a1c54380a0013c007200e409c0134,0xe801d02a0053000e8148007200e400e8144,0xac0154,0xb8016c02d005900b0015c,0x1e81880194032806500ca021404282a50184021c04380c0017c005a00b40bc0174,0x8198010c02180430086010c02180430086018c031806300c6020c04180a301940194032806500ca021404280a50035021c04380a7019002a400b4000818c,0xd0019c,0xde01b80194032806500ca021404282a501b4021c04380d801ac005a00b40d401a4,0xe801cc010c02180430086010c02180430086018c031806300c6020c04180a301c80194032806500ca021404280a50035021c04380a7004102a400b40e201c0]
  | 7 => #[0x8000,0x8004,0x8008,0x8000c,0x8014,0x8018,0xa0014000801c,0x120020,0x8028,0x18002c,0x8009232c00e00008034,0x803c,0x1a01100008040,0x260048,0x8801100b001500088050,0x32a465480088011002a0054008805c,0x320060,0x8068,0x1a01c0000806c,0x8074,0x3e0078,0x8088232c02100008080,0x808c,0x1a02500008090,0x4e0098,0x3202a005200a0,0x801d232c007400080ac,0x5a00b0,0x1080c80188030005e00b8,0x32a4654801080d4004a009406800cc,0x14802901c8038001480dc004a009401480d8,0x7600e8,0xe801d232c007400e80f0,0x188031005a00b408000fc004a009407c00f4,0xc87190e232c00a40148029232c0074014801d232c00740148104,0x860108,0x1e81280aa4154801c8039006a00d409201200aa4154808e0118006a00d408a0110,0xc85190a007a052001e81440aa415480208041028004f009c01340aa41548020804100820104098012c,0x814c,0x1a05500008150,0xae0158,0x8a05a00b20160,0x248049021c0438087010e007200e40248178009a0134026804d02e805c0024816c,0x329465280248049021c0438087010e008a06200248184009a0134026804d008a0600024817c,0x819c0194032806500ca0194032806500ca02140428085010a0b2c06600008194021c0438087010e0b2c014400080510b2c0134000804d0b2c0640000818c,0xd201a0,0x2a81b80194032806500ca0194032806500ca02140428085010a029405280da01b0021c0438087010e029c0538028805102a40548026804d006a00d40d601a8,0x81c4010c02180430086010c02180430086010c02180430086010c02180430086018c031806300c6018c031806300c6020c04180830106028c05180c301c00194032806500ca0194032806500ca02140428085010a029405280c50059021c0438087010e029c05380c7005102a405480c9004d032c00d400081bc,0x81c8,0x81cc,0xa001400081d0,0xec01d4,0x2e805d03c8078002e81dc,0x81f01aa435486c901ec1b2c00d400081e8,0xfc01f4,0x81fc,0x1020200,0x8210232c08300008208,0x32a46548ac90218232c00d40008214,0x821c,0x45008900008220,0x118022c,0x48008f011c0234,0x824c232c09200008244,0x32a46548ac90061232c01840008250,0x12c0254,0x138026c04d00990130025c,0x827c1aa435486c902781b2c00d40008274,0x1420280,0x8288,0x5280a40000828c,0x14e0298,0x5580aa015202a0,0x32806505700ad003282b0,0x32a46548032806505880b0003282bc,0x82d81b2c0b5000082d01b2c0b3000082c8,0x329c6538ac700691b2c0ba000082e41b2c0b8000082dc,0x17802ec,0xda0bf017c02f4,0x3a83141b2c01c4188030c1b2c0c201820300,0x329c6538ac700792b2401e4ac9031c1b2c01e403c8318,0x1920320,0x19e033800e201c419a0330004a00941960328,0xc87190e06b80d601aa035000fa01f403e807d06980d201a20340,0x321c6438c87190e329c6538040836832a4654803e807d004a00941b20360,0x836c,0x6f00dd00008370,0x1c0037c,0x7200e301c40384,0x2e805d07380e6002e8394,0x32a4654802e805d07500e9002e83a0,0x83bc1b2c0ee000083b41b2c0ec000083ac,0x329c6538ac703d01b2c0f3000083c81b2c0f1000083c0,0x1ec03d4,0x7d00f901f003dc,0x2040404010a021420003fc07f00fd01f803ec,0x329c6538218042c08501090210041c08301050208040c,0x248049021c0438087010e089011100248440009a0134026804d087810e00248434,0x80890194032806500ca0194032806500ca02140428085010a0a9415282c50458021c0438087010e0b2c115000084500b2c0134000804d0b2c0224000844c,0x230045c,0x23c047402a40548238046c006a00d42340464,0x4684900194032806500ca0194032806500ca02140428085010a029405282c5048c021c0438087010e029c0538244048402a40548026804d006a00d4240047c,0x84a0010c02180430086010c02180430086010c02180430086010c02180430086018c031806300c6018c031806300c6020c04180830106028c05180c3049c0194032806500ca0194032806500ca02140428085010a029405280c50059021c0438087010e029c05380c7049802a405480c9004d032c00d40008494,0x84a4,0x96012b000084a8,0x25c04b4,0x990131026004bc,0x4880911b2402146c9009109a8134004884cc,0x329c653804880911b2402446c9009109c0137004884d8,0x248049021c0438087010e09f013d002484f0009a0134026804d09d813a002484e4,0x85100194032806500ca0194032806500ca02140428085010a0a9415282c5050c021c0438087010e0b2c142000085040b2c0134000804d0b2c140000084fc,0x328c6518ac300890194032806500ca0194032806500ca02140428085010a0a9415282c50520021c0438087010e0b2c147000085180b2c0134000804d0b2c02240008514,0x2940524,0xa7014d0298052c,0x2ae05580194032806500ca0194032806500ca02140428085010a029405282c50554021c0438087010e029c05382a8054c02a40548026804d0a9015102a0053c,0x856c010c02180430086010c02180430086010c02180430086010c02180430086018c031806300c6018c031806300c6020c04180830106028c05180c305680194032806500ca0194032806500ca02140428085010a029405280c50059021c0438087010e029c05380c7009502a405480c9004d032c15900008560,0x32846508ac10578010c02180430086010c02180430086010c02180430086010c02180430086018c031806300c6018c031806300c6020c04180830106028c05180c305740194032806500ca0194032806500ca02140428085010a029405280c50059021c0438087010e029c05380c7009502a405480c9004d032c00140008570]
  | _ => #[]

def permWords958 : ℕ → Array ℕ
  | 1 => #[]
  | 2 => #[]
  | 3 => #[0x201]
  | 4 => #[0x320100003120]
  | 5 => #[0x43120000423010004103200042310]
  | 6 => #[0x5214300053420100543120003254010054231000542301005341200021054300534210]
  | 7 => #[0x652143004365201065342010654312004326501065342100654231006325401056423100645312003206514065341200645230103210654062105430632541006453210]
  | 8 => #[0x7653420172140653421507636753420121043765421706537563420172103654756342107654312054327601765423107653421075643120432076157632540154763120675423107645321054762130632075147564231076453120532076147320651432107645764523017563412043210765321076547436521075643210,0x765214307562143054376201743652016753421021540763]
  | _ => #[]

def terminalWords958 : ℕ → Array ℕ
  | 0 => #[0x1]
  | 1 => #[0x1]
  | 2 => #[0x2001]
  | 3 => #[0x8004002001]
  | 4 => #[0x2801400a005002801400a005]
  | 5 => #[0x5202901480a4052025012806403201900c806403201900c805402a00d]
  | 6 => #[0x6282a4152069034800c18a0a503280e407203901c80e407203901c80e407209903281940ca05902c80e407203902a815406a01d,0x5482c415206903481a40d207103881c40e2000]
  | 7 => #[0x9c871427213909c82e41720b905c82e40f207903c801c33216500206642ca0e507286642b20d906c82e41720790aa83540ea03d,0xd480403520130d48038352169074806838a00f0e2802c34a0e503c81e40f207903c81e40f207903c81e41e20f10788030010139,0x7883c41e20120e480b002e1690b483a41d202801207142e201201005c42e20120e280700301710b883c41e201a0e2805038a00e,0x230d486c403e1a900506c40700340e880c036201b0d483a41d20e907483c41e20f1]
  | 8 => #[0xbc85e41f201a00f0e6407e36500f00ec06e3990198d946ca2e50f280bc73202b1ac87643b21d915c86e41f20271aa87541ea07d,0xf003803c3390070ce409e04b0238f1467204019c8ce401c33901e0ce40863390dc8ce45722b90dc86e46722b90dc86e43721b9,0x13c814c4f227913c85e42f21790bc85e41f20f907c803809800a005004802c2f11788f140243c502401105e22f10f887c403c006,0xf480080343c500b0f1400400e00f004878a01e1d287941f20f907c83e41f20f907c83e41f20f90f887c43e21f10f88048024279,0x1e2805878a00200d000801c01200f004878a00e1d4803875200200d003803c00e1d4800803401e1d4803801c3a90070ea401c369,0x1b880286e200a1b880080040120090f140240160090f1401400e00f002801c01e0050dc40243710090dc401437117887c400401a,0x1b480386d22e90f4800803c01e0010008004016005002803c01e0010f1402c01602a0f140a0371001004803400200b004801401e,0xb00480242f117880386d22f117887c43e201200100080240121e4804802c0121e4803801c01e007003803c00e1b480486d2012,0xf8804879201600b0ba45d21e90f487c43e21f10f880380240580070da45e200a009002801400a00500380242f117880287a200a,0x1d8800800c01e001001803c00200900780140121e8800803400a00f002876200200d00787521e90f487a43d21f10f887c43e21f1,0x7801401e1d48ec40343a90050ec402c0161e880280140161d8800803401600f005875200200500280143b100b00287a200a]
  | _ => #[]

def manyWords958 : ℕ → Array ℕ
  | 0 => #[0x2422211412110c0a09,0x514c494632312c2926,0x4c4a493432312c2a29,0x6462614c4a49343231,0x52514c4a3432312c2a,0x6462614c4a34321c1a,0x524c4a4134322c2a21,0x54524c4a4134322c2a,0x54524c4a34322c2a01,0x956a6966655a595655,0x9c99966c69665c5956,0xccc9c69c99966c6966,0xb1a6998c727166594c,0xccc9c6999266613231,0x928c8666614c493231,0xa199928c666159524c,0xb1aa9c8e78716a5c4e,0xe2e1c6aa8e7154381c,0xc6c18e716254382a1c,0x8e8171625446382a1c,0xf0e1d2b496785a3c1e]
  | _ => #[]

def coreWords958 : ℕ → Array ℕ
  | 0 => #[0x8f2104088f1082018f1080018d1105108d1104058d1104048d1081818d108101701e4a08701e4a05701e4a01701e4083701e2107701e2106701e20c4701e2083701e2082701e0882701e0841701a2146701a21447019108360007823]
  | _ => #[]

def vertexWords958 : ℕ → Array ℕ
  | 0 => #[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
  | _ => #[]

def avoidWords958 : ℕ → Array ℕ
  | 0 => #[]
  | 1 => #[0x0]
  | 2 => #[0x0,0x0]
  | 3 => #[0x0,0x0,0x0]
  | 4 => #[0x1,0x1,0x1,0x1]
  | 5 => #[0x10114,0x10112,0x10106,0x10016,0x116]
  | 6 => #[0x1011401141440,0x1011201121220,0x1010601060608,0x1001600160068,0x11600001668,0x1161668]
  | 7 => #[0x10114011414400114144014404000,0x10112011212200112122012202000,0x10106010606080106060806080800,0x10016001600680016006800680080,0x116000016680000166800006880,0x11616680000000016686880,0x116166816686880]
  | 8 => #[0x1011401141440011414401440400001141440144040001440400040000000,0x1011201121220011212201220200001121220122020001220200020000000,0x1010601060608010606080608080001060608060808000608080008000000,0x1001600160068001600680068008000160068006800800068008000800000,0x11600001668000016680000688000001668000068800000688000008000,0x1161668000000001668688000000000166868800000000068808000,0x11616681668688000000000000000001668688068808000,0x1161668166868801668688068808000]
  | _ => #[]

def slice958 (x w i : ℕ) : ℕ := (x >>> (w*i)) % 2^w

def field958 (a : Array ℕ) (w i : ℕ) : ℕ := slice958 (a[i/32]?.getD 0) w (i % 32)

def gc958 (n idx : ℕ) : ℕ := field958 (graphWords958 n) 28 idx

def permWord958 (n idx : ℕ) : ℕ := field958 (permWords958 n) 32 idx

def allUp958 (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).all p

theorem allUpIff958 (n : ℕ) (p : ℕ → Bool) :
    allUp958 n p = true ↔ ∀ i<n, p i = true := by simp [allUp958]

def permTest958 (n w : ℕ) : Bool :=
  allUp958 n fun i => decide (slice958 w 4 i < n) &&
    allUp958 i fun j => decide (slice958 w 4 i ≠ slice958 w 4 j)

theorem permTestSound958 {n w : ℕ} (h : permTest958 n w = true) :
    permOn958 n (slice958 w 4) := by
  simp only [permTest958,allUpIff958,Bool.and_eq_true,decide_eq_true_eq] at h
  refine ⟨fun i hi => (h i hi).1, ?_⟩
  intro i hi j hj e
  rcases lt_trichotomy i j with lt|eq|gt
  · exact False.elim ((h j hj).2 i lt e.symm)
  · exact eq
  · exact False.elim ((h i hi).2 j gt e)

def extensionCap958 (k p : ℕ) : ℕ :=
  if k = 0 then 1 else 2 * (p % 2^(k-1) + 1)

def lookupEntry958 (k idx r : ℕ) : Bool :=
  let c := gc958 k idx * 2^k + r
  let tag := slice958 ((hintWords958 k)[idx]?.getD 0) 15 r
  let a := tag/4
  if tag % 4 = 0 then decide (a < catalogSize958 (k+1)) && (gc958 (k+1) a == c)
  else if tag % 4 = 1 then
    let p := permWord958 (k+1) a
    permTest958 (k+1) p && decide (c <
      prefixCode958 (fun i j => decodeEdge958 (k+1) c (slice958 p 4 i) (slice958 p 4 j)) (k+1))
  else
    let i := slice958 a 4 0
    let j := slice958 a 4 1
    let v := slice958 a 4 2
    decide (i<k ∧ j<k ∧ v<k ∧ i≠j) &&
    decodeEdge958 (k+1) c k i && decodeEdge958 (k+1) c i v &&
    decodeEdge958 (k+1) c v j && decodeEdge958 (k+1) c j k

def maskCard958 (n s : ℕ) : ℕ := ((List.range n).filter (s.testBit ·)).length

def maskInd958 (n c s : ℕ) : Bool :=
  allUp958 n fun i => !s.testBit i ||
    allUp958 i fun j => !(s.testBit j && decodeEdge958 n c i j)

def maskMax958 (n c s : ℕ) : Bool :=
  maskInd958 n c s && allUp958 n fun i => s.testBit i ||
    (List.range n).any fun j => s.testBit j && decodeEdge958 n c i j

def badWord958 (n c : ℕ) : ℕ :=
  (List.range n).foldl (fun acc i =>
    (List.range i).foldl (fun val j =>
      if decodeEdge958 n c i j then val ||| ((vertexWords958 0)[i]?.getD 0 &&& (vertexWords958 0)[j]?.getD 0)
      else val) acc) 0

def manyTest958 (n c w : ℕ) : Bool :=
  allUp958 9 fun i =>
    let s := slice958 w 8 i
    decide (s < 2^n) && maskMax958 n c s &&
    allUp958 i fun j => decide (s ≠ slice958 w 8 j)

def terminalTest958 (n idx : ℕ) : Bool :=
  let c := gc958 n idx
  let t := field958 (terminalWords958 n) 13 idx
  let a := t/4
  if t % 4=0 then decide (a<23) && (field958 (coreWords958 0) 32 a == n*2^28+c)
  else if t % 4=1 then decide (a<2^n ∧ n < maskCard958 n a + 4) && maskInd958 n c a
  else if t % 4=2 then
    let av := (avoidWords958 n)[a]?.getD 0
    decide (a<n) && (av &&& badWord958 n c == av)
  else manyTest958 n c ((manyWords958 0)[a]?.getD 0)

def auditParent958 (k idx : ℕ) : Bool :=
  allUp958 (extensionCap958 k (gc958 k idx)) fun r => lookupEntry958 k idx r

def sampleRows958 (n start len : ℕ) : Bool :=
  allUp958 len fun d => auditParent958 n (start+d)

def sampleTerms958 (n start len : ℕ) : Bool :=
  allUp958 len fun d => terminalTest958 n (start+d)

def boundedFourFree958 (A : ℕ → ℕ → Bool) (n : ℕ) : Prop :=
  ∀ a<n, ∀ b<n, ∀ c<n, ∀ d<n, a≠c → b≠d →
    A a b = true → A b c = true → A c d = true → A d a ≠ true

theorem useEntry958 {A : ℕ → ℕ → Bool} {k i : ℕ}
    (hparent : gc958 k i = prefixCode958 A k)
    (check : lookupEntry958 k i (prefixRow958 (A k) k) = true)
    (maximum : maximalCode958 A (k+1)) (free : boundedFourFree958 A (k+1))
    (symm : ∀ i<k+1, ∀ j<k+1, A i j = A j i) (loop : ∀ i<k+1, A i i = false) :
    ∃ j<catalogSize958 (k+1), gc958 (k+1) j = prefixCode958 A (k+1) := by
  let n := k + 1
  let code := prefixCode958 A n
  let tag := slice958 ((hintWords958 k)[i]?.getD 0) 15 (prefixRow958 (A k) k)
  let a := tag / 4
  have hc : gc958 k i * 2^k + prefixRow958 (A k) k = code := by rw [hparent]; rfl
  simp only [lookupEntry958,hc] at check
  change (if tag % 4=0 then _ else if tag % 4=1 then _ else _) = true at check
  split at check
  · exact ⟨a,of_decide_eq_true (Bool.and_eq_true_iff.mp check).1,
      eq_of_beq (Bool.and_eq_true_iff.mp check).2⟩
  · split at check
    · let p := permWord958 n a
      obtain ⟨hp,impr⟩ := Bool.and_eq_true_iff.mp check
      have gp : permOn958 n (slice958 p 4) := permTestSound958 hp
      have bigger := of_decide_eq_true impr
      have swapped := maximum (slice958 p 4) gp
      have same : prefixCode958 (fun x y => decodeEdge958 n code (slice958 p 4 x) (slice958 p 4 y)) n =
          prefixCode958 (fun x y => A (slice958 p 4 x) (slice958 p 4 y)) n := by
        apply codeCong958
        intro x hx y hy
        exact decodeCorrect958 A (gp.1 x hx) (gp.1 y hy) symm loop
      exact False.elim ((not_lt_of_ge swapped) (same ▸ bigger))
    · let x := slice958 a 4 0
      let y := slice958 a 4 1
      let v := slice958 a 4 2
      simp only [Bool.and_eq_true,decide_eq_true_eq] at check
      obtain ⟨⟨⟨⟨⟨hx,hy,hv,xy⟩,hkx⟩,hxv⟩,hvy⟩,hyk⟩ := check
      change x<k at hx
      change y<k at hy
      change v<k at hv
      have xlt : x<n := by change x<k+1; omega
      have ylt : y<n := by change y<k+1; omega
      have vlt : v<n := by change v<k+1; omega
      have klt : k<n := Nat.lt_succ_self _
      have hkx' : A k x = true := (decodeCorrect958 A klt xlt symm loop) ▸ hkx
      have hxv' : A x v = true := (decodeCorrect958 A xlt vlt symm loop) ▸ hxv
      have hvy' : A v y = true := (decodeCorrect958 A vlt ylt symm loop) ▸ hvy
      have hyk' : A y k = true := (decodeCorrect958 A ylt klt symm loop) ▸ hyk
      exact False.elim (free k klt x xlt v vlt y ylt (by omega) xy hkx' hxv' hvy' hyk')

theorem catalogCoverage958 {A : ℕ → ℕ → Bool} {n : ℕ} (hn : n≤8)
    (allChecked : ∀ k<8, ∀ i<catalogSize958 k, auditParent958 k i = true)
    (maximum : maximalCode958 A n) (free : boundedFourFree958 A n)
    (symm : ∀ i<n, ∀ j<n, A i j = A j i) (loop : ∀ i<n, A i i = false) :
    ∃ i<catalogSize958 n, gc958 n i = prefixCode958 A n := by
  induction n with
  | zero => exact ⟨0,by decide,rfl⟩
  | succ k ih =>
    obtain ⟨i,hi,g⟩ := ih (by omega) (maximalPrefix958 maximum)
      (fun a ha b hb c hc d hd => free a (by omega) b (by omega) c (by omega) d (by omega))
      (fun i hi j hj => symm i (by omega) j (by omega)) (fun i hi => loop i (by omega))
    apply useEntry958 g _ maximum free symm loop
    apply (allUpIff958 _ _).mp (allChecked k (by omega) i hi)
    cases k with
    | zero => change 0 < 1; decide
    | succ k =>
      simpa [extensionCap958,g] using lastOrder958 A k maximum

theorem foldFlag958 (xs : List ℕ) (f : ℕ → ℕ → ℕ) (s a : ℕ)
    (ha : a.testBit s = false)
    (hf : ∀ i ∈ xs, ∀ z, z.testBit s = false → (f z i).testBit s = false) :
    (xs.foldl f a).testBit s = false := by
  induction xs generalizing a with
  | nil => exact ha
  | cons i xs ih =>
    exact ih _ (hf i (List.mem_cons_self ..) a ha)
      (fun j h => hf j (List.mem_cons_of_mem _ h))

theorem badWordMiss958 {n c s : ℕ} (h : maskInd958 n c s = true)
    (vBits : ∀ i<n, ((vertexWords958 0)[i]?.getD 0).testBit s = s.testBit i) :
    (badWord958 n c).testBit s = false := by
  simp only [maskInd958,allUpIff958,Bool.or_eq_true,Bool.not_eq_true'] at h
  unfold badWord958
  apply foldFlag958 _ _ _ _ (by simp)
  intro i hi z hz
  have hi' := List.mem_range.mp hi
  apply foldFlag958 _ _ _ _ hz
  intro j hj u hu
  have hj' := List.mem_range.mp hj
  split
  next hEdge =>
    rw [Nat.testBit_or,Nat.testBit_and,vBits i hi',vBits j (by omega),hu]
    rcases h i hi' with hsi|pair
    · simp [hsi]
    · have q := pair j hj'
      cases a : s.testBit j <;> simp_all
  next => exact hu

def vertexAudit958 : Bool :=
  allUp958 8 fun i => allUp958 256 fun s =>
    (((vertexWords958 0)[i]?.getD 0).testBit s == s.testBit i)

def avoidAudit958 : Bool :=
  allUp958 9 fun n => allUp958 n fun v => allUp958 (2^n) fun s =>
    (maskCard958 n s + 4 != n) || s.testBit v || ((avoidWords958 n)[v]?.getD 0).testBit s

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem vertexAudited958 : vertexAudit958 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem avoidAudited958 : avoidAudit958 = true := by decide +kernel

theorem useTerminal958 {n i : ℕ} (hn : n≤8) (test : terminalTest958 n i = true)
    (bound : ∀ s<2^n, maskInd958 n (gc958 n i) s = true → maskCard958 n s + 4 ≤ n)
    (avoid : ∀ v<n, ∃ s<2^n, maskInd958 n (gc958 n i) s = true ∧
      maskCard958 n s + 4 = n ∧ s.testBit v = false)
    (few : ∀ w, manyTest958 n (gc958 n i) w = false) :
    ∃ a<23, field958 (coreWords958 0) 32 a = n*2^28+gc958 n i := by
  unfold terminalTest958 at test
  let t := field958 (terminalWords958 n) 13 i
  let a := t/4
  change (if t % 4=0 then _ else if t % 4=1 then _ else if t % 4=2 then _ else _) = true at test
  split at test
  · exact ⟨a,of_decide_eq_true (Bool.and_eq_true_iff.mp test).1,
      eq_of_beq (Bool.and_eq_true_iff.mp test).2⟩
  · split at test
    · obtain ⟨props,ind⟩ := Bool.and_eq_true_iff.mp test
      obtain ⟨small,gt⟩ := of_decide_eq_true props
      exact False.elim (Nat.not_lt_of_ge (bound a small ind) gt)
    · split at test
      · obtain ⟨lt,e⟩ := Bool.and_eq_true_iff.mp test
        have hav : a<n := of_decide_eq_true lt
        obtain ⟨s,hs,ind,sz,no⟩ := avoid a hav
        have vertexOk := vertexAudited958
        simp only [vertexAudit958,allUpIff958,beq_iff_eq] at vertexOk
        have lpow : 2^n ≤ 256 := Nat.pow_le_pow_right (by decide : 0<2) hn
        have miss := badWordMiss958 ind (fun j hj => vertexOk j (by omega) s (by omega))
        have avoidOk := avoidAudited958
        simp only [avoidAudit958,allUpIff958] at avoidOk
        have mem := avoidOk n (by omega) a hav s hs
        simp only [sz,bne_self_eq_false, Bool.false_or,no] at mem
        let av := (avoidWords958 n)[a]?.getD 0
        have he : av &&& badWord958 n (gc958 n i) = av := eq_of_beq e
        have ee : (av &&& badWord958 n (gc958 n i)).testBit s = av.testBit s :=
          congrArg (fun x : ℕ => x.testBit s) he
        change av.testBit s = true at mem
        rw [Nat.testBit_and,miss,Bool.and_false,mem] at ee
        exact Bool.noConfusion ee
      · exact False.elim (Bool.noConfusion ((few _).symm.trans test))



set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedstep0 : allUp958 (catalogSize958 0) (auditParent958 0) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedterm0 : allUp958 (catalogSize958 0) (terminalTest958 0) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedstep1 : allUp958 (catalogSize958 1) (auditParent958 1) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedterm1 : allUp958 (catalogSize958 1) (terminalTest958 1) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedstep2 : allUp958 (catalogSize958 2) (auditParent958 2) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedterm2 : allUp958 (catalogSize958 2) (terminalTest958 2) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedstep3 : allUp958 (catalogSize958 3) (auditParent958 3) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedterm3 : allUp958 (catalogSize958 3) (terminalTest958 3) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedstep4 : allUp958 (catalogSize958 4) (auditParent958 4) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedterm4 : allUp958 (catalogSize958 4) (terminalTest958 4) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedstep5 : allUp958 (catalogSize958 5) (auditParent958 5) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedterm5 : allUp958 (catalogSize958 5) (terminalTest958 5) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedstep6 : allUp958 (catalogSize958 6) (auditParent958 6) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedterm6 : allUp958 (catalogSize958 6) (terminalTest958 6) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedstep7 : allUp958 (catalogSize958 7) (auditParent958 7) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedterm7 : allUp958 (catalogSize958 7) (terminalTest958 7) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem verifiedterm8 : allUp958 (catalogSize958 8) (terminalTest958 8) = true := by decide +kernel


theorem allParents958 (k : ℕ) (hk : k<8) (i : ℕ) (hi : i<catalogSize958 k) :
    auditParent958 k i = true := by
  have ks : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 := by omega
  rcases ks with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (allUpIff958 _ _).mp verifiedstep0 i hi
  · exact (allUpIff958 _ _).mp verifiedstep1 i hi
  · exact (allUpIff958 _ _).mp verifiedstep2 i hi
  · exact (allUpIff958 _ _).mp verifiedstep3 i hi
  · exact (allUpIff958 _ _).mp verifiedstep4 i hi
  · exact (allUpIff958 _ _).mp verifiedstep5 i hi
  · exact (allUpIff958 _ _).mp verifiedstep6 i hi
  · exact (allUpIff958 _ _).mp verifiedstep7 i hi

theorem allTerminals958 (k : ℕ) (hk : k≤8) (i : ℕ) (hi : i<catalogSize958 k) :
    terminalTest958 k i = true := by
  have ks : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 := by omega
  rcases ks with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (allUpIff958 _ _).mp verifiedterm0 i hi
  · exact (allUpIff958 _ _).mp verifiedterm1 i hi
  · exact (allUpIff958 _ _).mp verifiedterm2 i hi
  · exact (allUpIff958 _ _).mp verifiedterm3 i hi
  · exact (allUpIff958 _ _).mp verifiedterm4 i hi
  · exact (allUpIff958 _ _).mp verifiedterm5 i hi
  · exact (allUpIff958 _ _).mp verifiedterm6 i hi
  · exact (allUpIff958 _ _).mp verifiedterm7 i hi
  · exact (allUpIff958 _ _).mp verifiedterm8 i hi

theorem coveredCoreCode958 {A : ℕ → ℕ → Bool} {n : ℕ} (hn : n≤8)
    (maximum : maximalCode958 A n) (free : boundedFourFree958 A n)
    (symm : ∀ i<n, ∀ j<n, A i j = A j i) (loop : ∀ i<n, A i i = false)
    (bound : ∀ s<2^n, maskInd958 n (prefixCode958 A n) s = true → maskCard958 n s + 4 ≤ n)
    (avoid : ∀ v<n, ∃ s<2^n, maskInd958 n (prefixCode958 A n) s = true ∧
      maskCard958 n s + 4 = n ∧ s.testBit v = false)
    (few : ∀ w, manyTest958 n (prefixCode958 A n) w = false) :
    ∃ a<23, field958 (coreWords958 0) 32 a = n*2^28+prefixCode958 A n := by
  obtain ⟨i,hi,g⟩ := catalogCoverage958 hn allParents958 maximum free symm loop
  rw [← g] at bound avoid few ⊢
  exact useTerminal958 hn (allTerminals958 n hn i hi) bound avoid few

theorem transferInd958 {n m : ℕ} (G : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n)
    (J : Finset (Fin m)) :
    ind958 (G.comap f) J ↔ ind958 G (J.map f) := by
  constructor
  · intro h v hv w hw
    obtain ⟨v,vi,rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨w,wi,rfl⟩ := Finset.mem_map.mp hw
    exact h _ vi _ wi
  · intro h v hv w hw
    exact h _ (Finset.mem_map.mpr ⟨v,hv,rfl⟩) _ (Finset.mem_map.mpr ⟨w,hw,rfl⟩)

theorem relabelCritical958 {n m : ℕ} (G : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n)
    (e : Fin m ≃ Fin m) (h : critical958 (G.comap f)) :
    critical958 (G.comap (e.toEmbedding.trans f)) := by
  obtain ⟨lo,bound,avoid⟩ := h
  refine ⟨lo,?_,?_⟩
  · intro I hi
    have h' : ind958 ((G.comap f).comap e.toEmbedding) I := hi
    simpa using bound _ ((transferInd958 (G.comap f) e.toEmbedding I).mp h')
  · intro v
    obtain ⟨J,hj,jc,nj⟩ := avoid (e v)
    let I := J.map e.symm.toEmbedding
    have back : I.map e.toEmbedding = J := by
      ext w
      simp [I]
    have hi := (transferInd958 (G.comap f) e.toEmbedding I).mpr (back ▸ hj)
    refine ⟨I,hi,by simpa [I] using jc,?_⟩
    intro hv
    exact nj (back ▸ Finset.mem_map.mpr ⟨v,hv,rfl⟩)

theorem canonicalCore958 {n : ℕ} (G : SimpleGraph (Fin n))
    (minimum : ∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → 4 ≤ T.card) :
    ∃ (m : ℕ) (f : Fin m ↪ Fin n) (A : ℕ → ℕ → Bool),
      m ≤ 8 ∧ critical958 (G.comap f) ∧ maximalCode958 A m ∧
      ∀ i j : Fin m, A i.val j.val = true ↔ G.Adj (f i) (f j) := by
  classical
  obtain ⟨m,f,hm,hc⟩ := extractCore958 G minimum
  let A (i j : ℕ) := if hi : i < m then if hj : j < m then
      decide (G.Adj (f ⟨i,hi⟩) (f ⟨j,hj⟩)) else false else false
  obtain ⟨p,perm,maximal⟩ := hasMaximalCode958 A m
  let q (i : Fin m) : Fin m := ⟨p i,(perm.1 _ i.isLt)⟩
  have inj : Function.Injective q := by
    intro i j eq
    exact Fin.ext (perm.2 i i.isLt j j.isLt (congrArg Fin.val eq))
  let e := Equiv.ofBijective q ⟨inj,Finite.surjective_of_injective inj⟩
  refine ⟨m,e.toEmbedding.trans f,fun i j => A (p i) (p j),hm,
    relabelCritical958 G f e hc,maximal,?_⟩
  intro i j
  change A (p i) (p j) = true ↔ G.Adj (f (q i)) (f (q j))
  simp [A,q,perm.1 _ i.isLt,perm.1 _ j.isLt]

def maskSet958 (m s : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => s.testBit i.val

theorem maskSetCard958 (m s : ℕ) : (maskSet958 m s).card = maskCard958 m s := by
  have eq : (maskSet958 m s).map Fin.valEmbedding =
      ((List.range m).filter (s.testBit ·)).toFinset := by
    ext i
    simp only [Finset.mem_map,List.mem_toFinset,List.mem_filter,List.mem_range,maskSet958,
      Finset.mem_filter,Finset.mem_univ,true_and,Fin.valEmbedding_apply]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ⟨j.isLt,hj⟩
    · rintro ⟨hi,hb⟩
      exact ⟨⟨i,hi⟩,hb,rfl⟩
  rw [← Finset.card_map (f := Fin.valEmbedding),eq]
  exact List.toFinset_card_of_nodup ((List.nodup_range).filter _)

theorem maskSetInv958 {m : ℕ} (I : Finset (Fin m)) :
    maskSet958 m (inMask958 I) = I := by
  ext i
  simp [maskSet958,bit_inMask958]

theorem invMaskSet958 {m s : ℕ} (hs : s < 2^m) : inMask958 (maskSet958 m s) = s := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · simp [bit_inMask958,maskSet958,hi]
  · have le : 2^m ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    simp [bit_inMask958,hi,Nat.testBit_lt_two_pow (hs.trans_le le)]

theorem indMask958 {m c s : ℕ} (H : SimpleGraph (Fin m))
    (edge : ∀ i j : Fin m, decodeEdge958 m c i j = true ↔ H.Adj i j) :
    maskInd958 m c s = true ↔ ind958 H (maskSet958 m s) := by
  have norm : maskInd958 m c s = true ↔
     ∀ i < m, s.testBit i = true → ∀ j < i, s.testBit j = true → decodeEdge958 m c i j = false := by
    simp only [maskInd958,allUpIff958,Bool.or_eq_true,Bool.not_eq_true',
      Bool.and_eq_false_iff]
    constructor
    · intro h i hi bi j ji bj
      rcases h i hi with q|q
      · simp [bi] at q
      · rcases q j ji with x|x
        · simp [bj] at x
        · exact x
    · intro h i hi
      cases b : s.testBit i
      · exact Or.inl rfl
      · exact Or.inr (fun j ji => by
          cases t : s.testBit j
          · exact Or.inl rfl
          · exact Or.inr (h i hi b j ji t))
  rw [norm]
  constructor
  · intro h v hv w hw e
    have bv := (Finset.mem_filter.mp hv).2
    have bw := (Finset.mem_filter.mp hw).2
    rcases lt_trichotomy v.val w.val with smaller|same|larger
    · have b := (edge w v).mpr e.symm
      rw [h w w.isLt bw v smaller bv] at b
      exact Bool.noConfusion b
    · exact H.loopless.irrefl _ ((Fin.ext same) ▸ e)
    · have b := (edge v w).mpr e
      rw [h v v.isLt bv w larger bw] at b
      exact Bool.noConfusion b
  · intro h i hi bi j ji bj
    let v : Fin m := ⟨i,hi⟩
    let w : Fin m := ⟨j,by omega⟩
    apply Bool.eq_false_iff.mpr
    intro e
    exact h v (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bi⟩) w
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bj⟩) ((edge v w).mp e)

theorem maxMask958 {m c s : ℕ} (H : SimpleGraph (Fin m))
    (edge : ∀ i j : Fin m, decodeEdge958 m c i j = true ↔ H.Adj i j)
    (mx : maskMax958 m c s = true) : maxInd958 H (maskSet958 m s) := by
  rw [maskMax958,Bool.and_eq_true,allUpIff958] at mx
  refine ⟨(indMask958 H edge).mp mx.1,?_⟩
  intro v hv
  have bv : s.testBit v.val = false := by simpa [maskSet958] using hv
  have h := mx.2 v v.isLt
  rw [bv,Bool.false_or,List.any_eq_true] at h
  obtain ⟨j,hj,b⟩ := h
  let w : Fin m := ⟨j,List.mem_range.mp hj⟩
  rw [Bool.and_eq_true] at b
  refine ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,b.1⟩,?_⟩
  exact (edge v w).mp b.2

theorem terminalBounds958 {m c : ℕ} (H : SimpleGraph (Fin m))
    (edge : ∀ i j : Fin m, decodeEdge958 m c i j = true ↔ H.Adj i j)
    (crit : critical958 H) :
    (∀ s < 2^m, maskInd958 m c s = true → maskCard958 m s + 4 ≤ m) ∧
    (∀ v < m, ∃ s < 2^m, maskInd958 m c s = true ∧ maskCard958 m s + 4 = m ∧ s.testBit v = false) := by
  refine ⟨fun s _ h => ?_,?_⟩
  · rw [← maskSetCard958]
    exact crit.2.1 _ ((indMask958 H edge).mp h)
  · intro v hv
    obtain ⟨I,hi,hs,hn⟩ := crit.2.2 ⟨v,hv⟩
    refine ⟨inMask958 I,bound_encode958 _ _,(indMask958 H edge).mpr (by rwa [maskSetInv958]),?_,?_⟩
    · rwa [← maskSetCard958,maskSetInv958]
    · simp [bit_inMask958,hv,hn]

def realizesRows958 (m c : ℕ) (cs : List ℕ) (occ : Fin m → ℕ) : Prop :=
  ∀ s < 2^m, maskMax958 m c s = true →
    ∃ x ∈ cs, ∀ v : Fin m, s.testBit v.val = decide (occ v &&& x = 0)

theorem physicalRows958 {n m c : ℕ} (G : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n)
    (edge : ∀ i j : Fin m, decodeEdge958 m c i j = true ↔ (G.comap f).Adj i j)
    (C : AndCountCircuit n) (size : C.size ≤ 3)
    (rows : ∀ K, maxInd958 G K → C.eval K = false ∧ ∀ u, u ∉ K → C.eval (insert u K) = true) :
    realizesRows958 m c (clauseList958 (links958 C) (selected958 C.outGates 3))
      (fun v => occ958 (physical958 C) (f v)) := by
  intro s _ mx
  obtain ⟨x,hx,q⟩ := coreAssignment958 G f C size rows (maskSet958 m s) (maxMask958 _ edge mx)
  exact ⟨x,hx,fun v => by simpa [maskSet958] using q v⟩

theorem fewRows958 {m c : ℕ} {cs : List ℕ} {occ : Fin m → ℕ}
    (cap : cs.length ≤ 8) (realizes : realizesRows958 m c cs occ) (w : ℕ) :
    manyTest958 m c w = false := by
  classical
  apply Bool.eq_false_iff.mpr
  intro test
  rw [manyTest958,allUpIff958] at test
  let row (i : Fin 9) := slice958 w 8 i.val
  have data (i : Fin 9) : row i < 2^m ∧ maskMax958 m c (row i) = true ∧
      ∀ j < i.val, row i ≠ slice958 w 8 j := by
    have h := test i i.isLt
    simpa only [Bool.and_eq_true,decide_eq_true_eq,allUpIff958,and_assoc,row] using h
  have choose (i : Fin 9) := realizes (row i) (data i).1 (data i).2.1
  choose target mem agree using choose
  let encode (i : Fin 9) : cs.toFinset := ⟨target i,List.mem_toFinset.mpr (mem i)⟩
  have inj : Function.Injective encode := by
    intro i j eq
    have code : target i = target j := congrArg Subtype.val eq
    have same : row i = row j := by
      apply Nat.eq_of_testBit_eq
      intro v
      by_cases hv : v < m
      · exact (agree i ⟨v,hv⟩).trans (code ▸ (agree j ⟨v,hv⟩).symm)
      · have le : 2^m ≤ 2^v := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_lt_two_pow ((data i).1.trans_le le),Nat.testBit_lt_two_pow ((data j).1.trans_le le)]
    rcases lt_trichotomy i.val j.val with hij|hij|hij
    · exact ((data j).2.2 i hij same.symm).elim
    · exact Fin.ext hij
    · exact ((data i).2.2 j hij same).elim
  have h := Fintype.card_le_of_injective encode inj
  rw [Fintype.card_fin,Fintype.card_coe] at h
  have q := cs.toFinset_card_le
  omega

theorem codeFacts958 {n m : ℕ} (G : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n) (A : ℕ → ℕ → Bool)
    (label : ∀ i j : Fin m, A i j = true ↔ G.Adj (f i) (f j))
    (free : ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) :
    (∀ i < m, ∀ j < m, A i j = A j i) ∧ (∀ i < m, A i i = false) ∧
    (∀ a < m, ∀ b < m, ∀ c < m, ∀ d < m, a≠c → b≠d →
      A a b = true → A b c = true → A c d = true → A d a ≠ true) ∧
    ∀ i j : Fin m, decodeEdge958 m (prefixCode958 A m) i j = true ↔ (G.comap f).Adj i j := by
  have symm (i : ℕ) (hi : i < m) (j : ℕ) (hj : j < m) : A i j = A j i := by
    apply Bool.eq_iff_iff.mpr
    exact (label ⟨i,hi⟩ ⟨j,hj⟩).trans ((G.adj_comm _ _).trans (label ⟨j,hj⟩ ⟨i,hi⟩).symm)
  have loop (i : ℕ) (hi : i < m) : A i i = false := by
    apply Bool.eq_false_iff.mpr
    exact fun h => G.loopless.irrefl _ ((label ⟨i,hi⟩ ⟨i,hi⟩).mp h)
  refine ⟨symm,loop,?_,?_⟩
  · intro a ha b hb c hc d hd ac bd ab bc cd da
    let aa : Fin m := ⟨a,ha⟩
    let bb : Fin m := ⟨b,hb⟩
    let cc : Fin m := ⟨c,hc⟩
    let dd : Fin m := ⟨d,hd⟩
    exact free (f aa) (f bb) (f cc) (f dd)
      (fun h => ac (congrArg Fin.val (f.injective h)))
      (fun h => bd (congrArg Fin.val (f.injective h))) ((label aa bb).mp ab)
      ((label bb cc).mp bc) ((label cc dd).mp cd) ((label dd aa).mp da)
  · intro i j
    rw [decodeCorrect958 A i.isLt j.isLt symm loop]
    exact label i j

theorem codeLimit958 (A : ℕ → ℕ → Bool) {m : ℕ} (hm : m ≤ 8) : prefixCode958 A m < 2^28 := by
  have bound : widths958 m ≤ 28 := widthsMono958 hm
  exact (codeSmall958 A m).trans_le (Nat.pow_le_pow_right (by decide) bound)

theorem finish958
    (closed : ∀ (m : ℕ) (A : ℕ → ℕ → Bool), m ≤ 8 →
      maximalCode958 A m → (∀ i < m, ∀ j < m, A i j = A j i) → (∀ i < m, A i i = false) →
      (∀ a < m, ∀ b < m, ∀ c < m, ∀ d < m, a≠c → b≠d →
        A a b = true → A b c = true → A c d = true → A d a ≠ true) →
      (∀ s < 2^m, maskInd958 m (prefixCode958 A m) s = true → maskCard958 m s + 4 ≤ m) →
      (∀ v < m, ∃ s < 2^m, maskInd958 m (prefixCode958 A m) s = true ∧
        maskCard958 m s + 4 = m ∧ s.testBit v = false) →
      (∀ w, manyTest958 m (prefixCode958 A m) w = false) →
      ∀ (a b : ℕ × ℕ) (o : ℕ) (occ : Fin m → ℕ),
      a.1 ≤ a.2 → a.2 < 2 → b.1 ≤ b.2 → b.2 < 4 → o < 8 →
      (∀ v, occ v < 64) →
      realizesRows958 m (prefixCode958 A m) (clauseList958 [(0,0),a,b] o) occ → False)
    {n : ℕ} (G : SimpleGraph (Fin n))
    (free : ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a)
    (minimum : ∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → 4 ≤ T.card)
    (C : AndCountCircuit n)
    (rows : ∀ K, maxInd958 G K → C.eval K = false ∧ ∀ u, u ∉ K → C.eval (insert u K) = true) :
    4 ≤ C.size := by
  by_contra! small
  have size : C.size ≤ 3 := by omega
  obtain ⟨m,f,A,hm,critical,maximal,label⟩ := canonicalCore958 G minimum
  obtain ⟨symm,loop,free',edge⟩ := codeFacts958 G f A label free
  obtain ⟨bound,avoid⟩ := terminalBounds958 _ edge critical
  have rows' := physicalRows958 G f edge C size rows
  have few := fewRows958 (clauseCap958 _ _) rows'
  have b0 := linkBounds958 C 0
  have z : link958 C 0 = (0,0) := by
    apply Prod.ext <;> dsimp <;> omega
  have b1 := linkBounds958 C 1
  have b2 := linkBounds958 C 2
  have valid := (outputMask958 G C size minimum rows).2
  apply closed m A hm maximal symm loop free' bound avoid few (link958 C 1) (link958 C 2)
    (selected958 C.outGates 3) (fun v => occ958 (physical958 C) (f v)) b1.1 b1.2 b2.1 b2.2 valid (fun v => bound_encode958 _ 6)
  simpa only [links958,z] using rows'

def bits958 (f : Nat → Bool) : List Nat → Nat
  | [] => 0
  | c :: cs => Nat.bit (f c) (bits958 f cs)

theorem bitAt958 (f : Nat → Bool) (cs : List Nat) (i : Nat) (h : i < cs.length) :
    (bits958 f cs).testBit i = f cs[i] := by
  induction cs generalizing i with
  | nil => simp at h
  | cons c cs ih =>
    cases i with
    | zero => simp [bits958]
    | succ i => simpa [bits958,Nat.testBit_bit_succ] using ih i (by simpa using h)

def bitsSet958 (m : Nat) : Finset (Fin 8) :=
  Finset.univ.filter fun i => m.testBit i.val

def countBits958 (m : Nat) : Nat :=
  (List.finRange 8).countP (fun i => m.testBit i.val)

theorem countBitsEq958 (m : Nat) : countBits958 m = (bitsSet958 m).card := by
  simpa [countBits958,bitsSet958] using
    ((List.nodup_finRange 8).card_eq_countP (P := fun i : Fin 8 => m.testBit i.val = true)).symm

def slots958 (a b : Nat) (f : Fin 8 → Fin 8) : Prop :=
  ∀ i, a.testBit i.val = true → b.testBit (f i).val = true

theorem cardSlots958 (a b : Nat) (f : Fin 8 → Fin 8) (hf : slots958 a b f)
    (inj : Set.InjOn f (bitsSet958 a)) : countBits958 a ≤ countBits958 b := by
  rw [countBitsEq958,countBitsEq958]
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf i (Finset.mem_filter.mp hi).2⟩
  · exact inj

def eraseMask958 (src col : Nat) : Nat := src ^^^ (src &&& col)

def split958 (col prof : Nat) (groups : List (Nat × Nat)) : List (Nat × Nat) :=
  groups.flatMap fun g =>
    let a := eraseMask958 g.1 col
    let b := g.1 &&& col
    (if a = 0 then [] else [(a,eraseMask958 g.2 prof)]) ++
    (if b = 0 then [] else [(b,g.2 &&& prof)])

theorem splitSound958 {col prof : Nat} {groups : List (Nat × Nat)} {f : Fin 8 → Fin 8}
    (ok : ∀ g ∈ groups, slots958 g.1 g.2 f ∧ Set.InjOn f (bitsSet958 g.1))
    (compat : ∀ g ∈ groups, ∀ i : Fin 8, g.1.testBit i.val = true →
      col.testBit i.val = prof.testBit (f i).val) :
    ∀ g ∈ split958 col prof groups, slots958 g.1 g.2 f ∧ Set.InjOn f (bitsSet958 g.1) := by
  intro g hg
  obtain ⟨p,hp,gh⟩ := List.mem_flatMap.mp hg
  obtain ⟨maps,inj⟩ := ok p hp
  have step (m k : Nat) (i : Nat) : (eraseMask958 m k).testBit i =
      (m.testBit i && !(k.testBit i)) := by
    simp only [eraseMask958,Nat.testBit_xor,Nat.testBit_and]
    cases m.testBit i <;> cases k.testBit i <;> decide
  have sub {a : Nat} (proj : ∀ i : Fin 8, a.testBit i.val = true → p.1.testBit i.val = true) :
      Set.InjOn f (bitsSet958 a) := by
    apply inj.mono
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,proj i (Finset.mem_filter.mp hi).2⟩
  rcases List.mem_append.mp gh with hn|hy
  · split at hn
    · simp at hn
    replace hn := List.mem_singleton.mp hn
    subst g
    have proj (i : Fin 8) (hi : (eraseMask958 p.1 col).testBit i.val = true) :
        p.1.testBit i.val = true := (Bool.and_eq_true_iff.mp ((step ..) ▸ hi)).1
    refine ⟨?_,sub proj⟩
    intro i hi
    simp only [step,Bool.and_eq_true,Bool.not_eq_true'] at hi ⊢
    exact ⟨maps i hi.1,(compat p hp i hi.1).symm.trans hi.2⟩
  · split at hy
    · simp at hy
    replace hy := List.mem_singleton.mp hy
    subst g
    have proj (i : Fin 8) (hi : (p.1 &&& col).testBit i.val = true) :
        p.1.testBit i.val = true := (Bool.and_eq_true_iff.mp ((Nat.testBit_and ..) ▸ hi)).1
    refine ⟨?_,sub proj⟩
    intro i hi
    simp only [Nat.testBit_and,Bool.and_eq_true] at hi ⊢
    exact ⟨maps i hi.1,(compat p hp i hi.1).symm.trans hi.2⟩

def goodSlots958 (groups : List (Nat × Nat)) : Bool :=
  groups.all fun p => decide (countBits958 p.1 ≤ countBits958 p.2)

def fit958 (patterns : List Nat) : List Nat → List (Nat × Nat) → Bool
  | [], gs => goodSlots958 gs
  | col :: cols, gs => goodSlots958 gs && patterns.any fun p => fit958 patterns cols (split958 col p gs)

theorem fitSound958 (patterns : List Nat) (cols : List Nat) (groups : List (Nat × Nat))
    (f : Fin 8 → Fin 8) (full : Nat)
    (sound : ∀ p ∈ groups, slots958 p.1 p.2 f ∧ Set.InjOn f (bitsSet958 p.1))
    (inside : ∀ p ∈ groups, ∀ i : Fin 8, p.1.testBit i.val = true → full.testBit i.val = true)
    (witness : ∀ c ∈ cols, ∃ p ∈ patterns, ∀ i : Fin 8, full.testBit i.val = true →
        c.testBit i.val = p.testBit (f i).val) : fit958 patterns cols groups = true := by
  have good : goodSlots958 groups = true := by
    apply List.all_eq_true.mpr
    intro p hp
    exact decide_eq_true (cardSlots958 _ _ _ (sound p hp).1 (sound p hp).2)
  induction cols generalizing groups with
  | nil => exact good
  | cons c cs ih =>
    obtain ⟨p,hp,hc⟩ := witness c (by simp)
    simp only [fit958,good,Bool.true_and,List.any_eq_true]
    refine ⟨p,hp,ih _ (splitSound958 sound (fun g hg i hi => hc i (inside g hg i hi))) ?_
      (fun x hx => witness x (List.mem_cons_of_mem _ hx)) ?_⟩
    · intro q hq i hi
      obtain ⟨r,hr,e⟩ := List.mem_flatMap.mp hq
      apply inside r hr i
      rcases List.mem_append.mp e with ha|hb
      · split at ha
        · simp at ha
        replace ha := List.mem_singleton.mp ha
        subst q
        simp only [eraseMask958,Nat.testBit_xor,Nat.testBit_and] at hi
        cases h : r.1.testBit i.val <;> simp_all
      · split at hb
        · simp at hb
        replace hb := List.mem_singleton.mp hb
        subst q
        exact (Bool.and_eq_true_iff.mp ((Nat.testBit_and ..) ▸ hi)).1
    · apply List.all_eq_true.mpr
      intro q hq
      have h := splitSound958 sound (fun g hg i hi => hc i (inside g hg i hi)) q hq
      exact decide_eq_true (cardSlots958 _ _ _ h.1 h.2)


def profileBook958 : List (Nat × List Nat) := [(8,[0,1,2,3,4,5,8,10,12,15,16,17,32,34,48,51,64,68,80,85,128,136,160,170,192,204,240,255]),
(7,[0,1,2,3,4,5,6,7,8,9,16,17,24,25,32,34,40,43,64,68,80,85,96,102,120,127]),
(7,[0,1,2,3,4,5,8,10,12,15,16,17,18,19,32,36,48,53,64,72,80,90,96,108,112,127])]

def clauseBook958 : List (List Nat × Nat) := [([21,22,25,26,37,38,41,42],0),
([20,25,26,37,38,41,42],1),
([21,22,25,26,36,41,42],2)]

def graphPlans958 : List (Nat × Nat × List Nat × List Nat) := [
(6,30755,[10,12,17,18,20,33,34,36],[2,0,0]),
(7,1642627,[25,38,49,50,70,73,76],[19,19,19]),
(7,1712452,[14,28,42,70,81,84,97,98],[4,0,0]),
(7,1712454,[14,17,28,42,70,97,98],[39,39,39]),
(7,1968193,[33,42,44,74,76,81,82,84],[2,0,0]),
(7,1968258,[49,50,52,74,76,97,98,100],[2,0,0]),
(7,1974402,[28,49,52,74,76,97,98,100],[4,0,0]),
(7,1974403,[28,34,49,52,65,74,76],[39,39,39]),
(7,1974468,[10,28,81,84,97,98,100],[7,7,7]),
(7,1974534,[28,42,49,56,68,97,98],[6,6,6]),
(7,1974535,[28,42,49,56,65,66,68],[49,49,49]),
(7,1982595,[26,28,33,50,52,65,74,76],[2,0,0]),
(7,1985025,[33,44,52,65,74,76,82,84],[4,0,0]),
(7,1985029,[10,33,44,52,65,82,84],[48,48,48]),
(7,1985032,[44,52,74,82,97,104,112],[6,6,6]),
(8,219185409,[78,97,106,142,156,170,177,184],[3,0,0]),
(8,219185537,[65,78,142,156,170,177,184],[4,4,4]),
(8,219218948,[60,113,120,142,172,202,225,232],[3,0,0]),
(8,219218949,[60,74,113,120,142,161,172],[4,4,4]),
(8,219219216,[14,60,177,184,202,225,232],[4,4,4]),
(8,252739585,[92,106,113,120,156,170,177,184],[4,0,0]),
(8,252740097,[84,98,113,156,170,177,184],[5,5,5]),
(8,253821960,[60,90,120,180,210,225,240],[5,5,5])
]


def packedProbes958 : Nat → Nat → List Nat
  | 0, _ => []
  | fuel+1, value => if value = 0 then [] else (value % 9-1) :: packedProbes958 fuel (value/9)

def screenCase958 (rows : List Nat) (t : Nat) (patterns : List Nat) (hint : Nat) : Bool :=
  if t < rows.length then true else
    let cols := (packedProbes958 2 hint).map fun v => bits958 (fun r => r.testBit v) rows
    !(fit958 patterns cols [(2^rows.length-1,2^t-1)])

def screenPlan958 (plan : Nat × Nat × List Nat × List Nat) : Bool :=
  (profileBook958.zip plan.2.2.2).all fun entry =>
    screenCase958 plan.2.2.1 entry.1.1 entry.1.2 entry.2

def screenedBook958 : Bool :=
  clauseBook958.all fun entry =>
    let cs := entry.1
    let target := profileBook958[entry.2]?.getD (0,[])
    decide (entry.2 < profileBook958.length) && (target.1 == cs.length) && decide (cs.length ≤ 8) && (List.range 64).all fun w =>
      target.2.contains (bits958 (fun c => !(hit958 c w)) cs)

def linkChoices958 (j : Nat) : List (Nat × Nat) :=
  (List.range (2^j)).flatMap fun l =>
    ((List.range (2^j)).filter fun r => decide (l ≤ r)).map fun r => (l,r)

def shapeAccepted958 (ls : List (Nat × Nat)) (out : Nat) : Bool :=
  let cs := clauseList958 ls out
  cs.length < 7 || clauseBook958.any (fun entry => trimClauses958 entry.1 == cs)

def shapeSuffix958 (a b : Nat × Nat) : Bool :=
  (List.range 8).all fun o => shapeAccepted958 [(0,0),a,b] o


theorem matchIndex958 (n : Nat) (rows cs : List Nat) (occ : Fin n → Nat)
    (nodup : rows.Nodup) (bound : ∀ r ∈ rows, r < 2^n)
    (has : ∀ r ∈ rows, ∃ c ∈ cs, ∀ v : Fin n, r.testBit v.val = !(hit958 c (occ v))) :
    ∃ f : Fin rows.length → Fin cs.length, Function.Injective f ∧
      ∀ (i : Fin rows.length) (v : Fin n), (rows.get i).testBit v.val =
          !(hit958 (cs.get (f i)) (occ v)) := by
  classical
  have pick (i : Fin rows.length) : ∃ j : Fin cs.length,
        ∀ v : Fin n, (rows.get i).testBit v.val = !(hit958 (cs.get j) (occ v)) := by
    obtain ⟨c,hc,hh⟩ := has _ (List.get_mem rows i)
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hc
    exact ⟨j,hh⟩
  choose f hf using pick
  refine ⟨f,?_,hf⟩
  intro i j e
  apply nodup.get_inj_iff.mp
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases h : t<n
  · exact (hf i ⟨t,h⟩).trans ((e ▸ hf j ⟨t,h⟩).symm)
  · have lim := Nat.pow_le_pow_right (by decide : 0<2) (show n≤t by omega)
    rw [Nat.testBit_lt_two_pow ((bound _ (List.get_mem rows i)).trans_le lim),
        Nat.testBit_lt_two_pow ((bound _ (List.get_mem rows j)).trans_le lim)]

theorem fitEmb958 (n t : Nat) (rows cs pats : List Nat) (occ : Fin n → Nat)
    (nodup : rows.Nodup) (bound : ∀ r ∈ rows, r < 2^n)
    (tlen : cs.length = t) (tlim : t ≤ 8)
    (has : ∀ r ∈ rows, ∃ c ∈ cs, ∀ v : Fin n, r.testBit v.val = !(hit958 c (occ v)))
    (cover : ∀ v : Fin n, bits958 (fun c => !(hit958 c (occ v))) cs ∈ pats)
    (ids : List Nat) (good : ∀ u ∈ ids, u < n) :
    fit958 pats (ids.map fun v => bits958 (fun r => r.testBit v) rows)
      [(2^rows.length-1,2^t-1)] = true := by
  obtain ⟨q,inj,eq⟩ := matchIndex958 n rows cs occ nodup bound has
  let f (i : Fin 8) : Fin 8 := if h : i.val < rows.length then
    ⟨(q ⟨i.val,h⟩).val,by have := (q ⟨i.val,h⟩).isLt; omega⟩ else 0
  apply fitSound958 pats _ _ f (2^rows.length-1)
  · intro p hp
    obtain rfl := List.mem_singleton.mp hp
    constructor
    · intro i hi
      simp only [Nat.testBit_two_pow_sub_one,decide_eq_true_iff] at hi ⊢
      simpa [f,hi,tlen] using (q ⟨i.val,hi⟩).isLt
    · intro i hi j hj e
      have ub (v : Fin 8) (hv : v ∈ bitsSet958 (2^rows.length-1)) : v.val < rows.length := by
        simpa [bitsSet958] using hv
      have ie := ub i hi
      have je := ub j hj
      have qeq : q ⟨i.val,ie⟩ = q ⟨j.val,je⟩ := by
        apply Fin.ext
        simpa [f,ie,je] using congrArg Fin.val e
      exact Fin.ext (congrArg (fun x : Fin rows.length => x.val) (inj qeq))
  · intro p hp
    obtain rfl := List.mem_singleton.mp hp
    exact fun _ h => h
  · intro c hc
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hc
    let u : Fin n := ⟨v,good v hv⟩
    refine ⟨_,cover u,?_⟩
    intro i hi
    have il : i.val < rows.length := by simpa only [Nat.testBit_two_pow_sub_one,decide_eq_true_iff] using hi
    have jl : (f i).val < cs.length := by simp [f,il]
    rw [bitAt958 _ _ _ il,bitAt958 _ _ _ jl]
    simpa [f,il,u] using eq ⟨i.val,il⟩ u

theorem screenContradiction958 (n : Nat) (rows cs pats : List Nat) (t hint : Nat) (occ : Fin n → Nat)
    (nodup : rows.Nodup) (bound : ∀ r ∈ rows, r < 2^n)
    (tlen : cs.length=t) (tlim : t≤8)
    (has : ∀ r ∈ rows, ∃ c ∈ cs, ∀ v : Fin n, r.testBit v.val = !(hit958 c (occ v)))
    (cover : ∀ v : Fin n, bits958 (fun c => !(hit958 c (occ v))) cs ∈ pats)
    (ids : ∀ v ∈ packedProbes958 2 hint, v<n)
    (screen : screenCase958 rows t pats hint = true) : False := by
  obtain ⟨f,inj,_⟩ := matchIndex958 n rows cs occ nodup bound has
  have le := Fintype.card_le_of_injective f inj
  have lt : ¬ t < rows.length := by simpa [tlen] using le
  have hm := fitEmb958 n t rows cs pats occ nodup bound tlen tlim has cover _ ids
  simp [screenCase958,lt,hm] at screen


theorem linkChoice958 (ab : Nat × Nat) (j : Nat) (h : ab.1 ≤ ab.2 ∧ ab.2 < 2^j) :
    ab ∈ linkChoices958 j := by
  obtain ⟨a,b⟩ := ab
  exact List.mem_flatMap.mpr ⟨a,List.mem_range.mpr (h.1.trans_lt h.2),
    List.mem_map.mpr ⟨b,List.mem_filter.mpr ⟨List.mem_range.mpr h.2,decide_eq_true h.1⟩,rfl⟩⟩

theorem chartActual958 (a b : Nat × Nat) (out : Nat)
    (ha : a.1 ≤ a.2 ∧ a.2 < 2^1) (hb : b.1 ≤ b.2 ∧ b.2 < 2^2)
    (ho : out < 8)
    (table : (linkChoices958 1).all (fun x => (linkChoices958 2).all (shapeSuffix958 x)) = true) :
    shapeAccepted958 [(0,0),a,b] out = true := by
  have x := List.all_eq_true.mp table _ (linkChoice958 _ _ ha)
  have y := List.all_eq_true.mp x _ (linkChoice958 _ _ hb)
  exact List.all_eq_true.mp y _ (List.mem_range.mpr ho)

theorem noPlan958 (n : Nat) (rows hints : List Nat) (ls : List (Nat × Nat)) (out : Nat)
    (occ : Fin n → Nat) (small : ∀ v, occ v < 64)
    (huge : 7 ≤ rows.length) (nd : rows.Nodup) (bound : ∀ r ∈ rows, r<2^n)
    (has : ∀ r ∈ rows, ∃ c ∈ clauseList958 ls out, ∀ v : Fin n, r.testBit v.val = !(hit958 c (occ v)))
    (shape : shapeAccepted958 ls out = true) (book : screenedBook958 = true)
    (tableLen : hints.length = profileBook958.length)
    (cols : ∀ h ∈ hints, ∀ v ∈ packedProbes958 2 h, v < n)
    (screen : screenPlan958 (n,0,rows,hints) = true) : False := by
  have idx := matchIndex958 n rows _ occ nd bound has
  obtain ⟨f,inj,_⟩ := idx
  have cn : rows.length ≤ (clauseList958 ls out).length := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f inj
  have big : ¬ (clauseList958 ls out).length < 7 := by omega
  simp only [shapeAccepted958,big,decide_false,Bool.false_or,List.any_eq_true,beq_iff_eq] at shape
  obtain ⟨⟨cs,k⟩,km,e⟩ := shape
  have checked := List.all_eq_true.mp book (cs,k) km
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at checked
  obtain ⟨⟨⟨emp,lens⟩,cap'⟩,accept⟩ := checked
  let entry := profileBook958[k]
  have ee : profileBook958[k]? = some entry := List.getElem?_eq_getElem emp
  change (profileBook958[k]?.getD (0,[])).1 = cs.length at lens
  change (List.range 64).all (fun w => (profileBook958[k]?.getD (0,[])).2.contains
    (bits958 (fun c => !(hit958 c w)) cs)) = true at accept
  simp only [ee,Option.getD_some] at lens
  simp only [ee,Option.getD_some,List.all_eq_true,List.mem_range,List.contains_iff_mem] at accept
  have hkm : k < hints.length := by omega
  let hint := hints[k]
  have contain : (entry,hint) ∈ profileBook958.zip hints := by
    apply List.mem_iff_getElem.mpr
    refine ⟨k,by simp; omega,?_⟩
    simp [entry,hint]
  have sc := List.all_eq_true.mp screen _ contain
  have cap : entry.1 ≤ 8 := lens.trans_le cap'
  apply screenContradiction958 n rows cs entry.2 entry.1 hint occ nd bound lens.symm cap _ _
    (cols _ (List.getElem_mem hkm)) sc
  · intro r hr
    obtain ⟨c,hc,h⟩ := has _ hr
    refine ⟨c,?_,h⟩
    exact (memTrimClauses958 c cs).mp (e.symm ▸ hc)
  · exact fun v => accept _ (small v)


def planAt958 (i : Nat) : Nat × Nat × List Nat × List Nat := graphPlans958[i]?.getD default

def metadata958 (i : Nat) : Bool :=
  let p := planAt958 i
  let n := p.1
  let c := p.2.1
  let rows := p.2.2.1
  let hints := p.2.2.2
  (field958 (coreWords958 0) 32 i == n*2^28+c) &&
  decide (c<2^28) && decide (7≤rows.length) && decide rows.Nodup &&
  rows.all (fun r => decide (r<2^n) && maskMax958 n c r) &&
  (hints.length == profileBook958.length) &&
  hints.all (fun h => (packedProbes958 2 h).all (fun v => decide (v<n)))

theorem coreIndexImpossible958 (n code i out : Nat) (a b : Nat × Nat)
    (id : field958 (coreWords958 0) 32 i = n*2^28+code) (csmall : code<2^28)
    (occ : Fin n → Nat) (small : ∀ v, occ v < 64)
    (ha : a.1 ≤ a.2 ∧ a.2 < 2^1) (hb : b.1 ≤ b.2 ∧ b.2 < 2^2)
    (ho : out < 8)
    (has : ∀ r<2^n, maskMax958 n code r = true → ∃ cl ∈ clauseList958 [(0,0),a,b] out,
      ∀ v : Fin n, r.testBit v.val = !(hit958 cl (occ v)))
    (info : metadata958 i = true) (screener : screenPlan958 (planAt958 i) = true)
    (shapes : (linkChoices958 1).all (fun x => (linkChoices958 2).all (shapeSuffix958 x)) = true)
    (book : screenedBook958 = true) : False := by
  obtain ⟨pn,pc,rows,hints,rec⟩ : ∃ pn pc rows hints, planAt958 i = (pn,pc,rows,hints) :=
    ⟨_,_,_,_,rfl⟩
  simp only [metadata958,rec,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,
    List.all_eq_true] at info
  obtain ⟨⟨⟨⟨⟨⟨hw,cap⟩,cnt⟩,nd⟩,vrows⟩,hl⟩,ids⟩ := info
  have nn : n=pn := by omega
  have cc : code=pc := by omega
  subst pn pc
  have hr : ∀ r ∈ rows, ∃ cl ∈ clauseList958 [(0,0),a,b] out,
      ∀ v : Fin n, r.testBit v.val = !(hit958 cl (occ v)) :=
    fun r h => has r (vrows r h).1 (vrows r h).2
  exact noPlan958 n rows hints _ out occ small cnt nd (fun r h => (vrows r h).1) hr
    (chartActual958 a b out ha hb ho shapes) book hl ids
    (by simpa only [rec,screenPlan958] using screener)


set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem allShapesScreened958 :
    (linkChoices958 1).all (fun x => (linkChoices958 2).all (shapeSuffix958 x)) = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem checkedProfileBook958 : screenedBook958 = true := by decide +kernel

def allGraphFacts958 (i : Nat) : Bool := metadata958 i && screenPlan958 (planAt958 i)

theorem checkedGraphFacts958 (i : Nat) (hi : i<23) : allGraphFacts958 i = true := by
  have h : (List.range 23).all allGraphFacts958 = true := by decide +kernel
  exact List.all_eq_true.mp h _ (List.mem_range.mpr hi)


theorem checkedCore958 (n code i out : Nat) (a b : Nat × Nat)
    (hi : i<23) (id : field958 (coreWords958 0) 32 i = n*2^28+code) (csmall : code<2^28)
    (occ : Fin n → Nat) (small : ∀ v, occ v < 64)
    (ha : a.1 ≤ a.2 ∧ a.2 < 2^1) (hb : b.1 ≤ b.2 ∧ b.2 < 2^2)
    (ho : out < 8)
    (has : ∀ r<2^n, maskMax958 n code r = true → ∃ cl ∈ clauseList958 [(0,0),a,b] out,
      ∀ v : Fin n, r.testBit v.val = !(hit958 cl (occ v))) : False := by
  have tested := Bool.and_eq_true_iff.mp (checkedGraphFacts958 i hi)
  exact coreIndexImpossible958 n code i out a b id csmall occ small ha hb ho has
    tested.1 tested.2 allShapesScreened958 checkedProfileBook958

end PEqualNP.Outside.L_meta_958

open PEqualNP.Outside.L_meta_958 in
theorem PEqualNP.Outside.L_meta_958 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∀ T : Finset (Fin n), (∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) → 4 ≤ T.card) → ∀ C : PEqualNP.AndCount.AndCountCircuit n, C.WellFormed → (∀ I : Finset (Fin n), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) → 4 ≤ C.size := by
  intro n G free minimum C _hw partialRows
  refine finish958 ?_ G free minimum C (fun K hK => partialRows K hK.1 hK.2)
  · intro m A hm maximum symm loop free' bound avoid few a b o occ aord acap bord bcap ocap occCap realizes
    obtain ⟨i,hi,key⟩ := coveredCoreCode958 hm maximum free' symm loop bound avoid few
    apply checkedCore958 m (prefixCode958 A m) i o a b hi key (codeLimit958 A hm) occ occCap
      ⟨aord,acap⟩ ⟨bord,bcap⟩ ocap
    intro r hr independent
    obtain ⟨cl,hcl,hv⟩ := realizes r hr independent
    refine ⟨cl,hcl,?_⟩
    intro v
    rw [hv v, Nat.and_comm (occ v) cl]
    by_cases disjoint : cl &&& occ v = 0 <;> simp [hit958, bne, disjoint]
