import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_908_aux

open PEqualNP.AndCount AndCountCircuit

variable {n : Nat}

def left (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def right (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

private theorem side_congr {k : Nat} (I B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) {a b : Fin k → Bool} (h : ∀ j, j < i → a j = b j) :
    sideTrue I B F i a = sideTrue I B F i b := by
  unfold sideTrue
  congr 1
  apply propext
  constructor <;> rintro (raw | ⟨j, hj, lt, val⟩)
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt) ▸ val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, lt, (h j lt).symm ▸ val⟩

private theorem stable (C : AndCountCircuit n) (I : Finset (Fin n)) (m : Nat) :
    ∀ i : Fin C.size, i.val < m → ∀ a b : Nat, i.val < a → i.val < b →
    C.gateValFuel I a i = C.gateValFuel I b i := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    intro i hi a b ha hb
    cases a with
    | zero => omega
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        simp only [gateValFuel]
        have eq (j : Fin C.size) (lt : j < i) :
            C.gateValFuel I a j = C.gateValFuel I b j :=
          ih j (by change j.val < i.val at lt; omega) a b
            (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
        rw [side_congr I _ _ i eq, side_congr I _ _ i eq]

theorem gate_eq (C : AndCountCircuit n) (I : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal I i = (left C I i && right C I i) := by
  have h := stable C I C.size i i.isLt C.size (C.size + 1) i.isLt (by omega)
  exact h

def vars (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightVars i else C.leftVars i

def parents (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :=
  if q i then C.rightGates i else C.leftGates i

def support (C : AndCountCircuit n) (q : Fin C.size → Bool) :
    Nat → Fin C.size → Finset (Fin n)
  | 0, _ => ∅
  | d+1, i => vars C q i ∪ ((parents C q i).filter (· < i)).biUnion (support C q d)

def hits (I S : Finset (Fin n)) := ∃ v ∈ S, v ∈ I

theorem hit_step (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (i : Fin C.size) (I : Finset (Fin n)) :
    hits I (support C q (d+1) i) ↔ hits I (vars C q i) ∨
      ∃ j ∈ parents C q i, j < i ∧ hits I (support C q d j) := by
  simp only [hits, support, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv | ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩
    · exact Or.inl ⟨v, hv, hI⟩
    · exact Or.inr ⟨j, hj, lt, v, hv, hI⟩
  · rintro (⟨v, hv, hI⟩ | ⟨j, hj, lt, v, hv, hI⟩)
    · exact ⟨v, Or.inl hv, hI⟩
    · exact ⟨v, Or.inr ⟨j, ⟨hj, lt⟩, hv⟩, hI⟩

def clause (C : AndCountCircuit n) (q : Fin C.size → Bool) :=
  C.outVars ∪ C.outGates.biUnion (support C q C.size)

theorem clause_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n)) :
    hits I (clause C q) ↔ hits I C.outVars ∨ ∃ j ∈ C.outGates, hits I (support C q C.size j) := by
  simp only [hits, clause, Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv | ⟨j, hj, hv⟩, hi⟩
    · exact Or.inl ⟨v, hv, hi⟩
    · exact Or.inr ⟨j, hj, v, hv, hi⟩
  · rintro (⟨v, hv, hi⟩ | ⟨j, hj, v, hv, hi⟩)
    · exact ⟨v, Or.inl hv, hi⟩
    · exact ⟨v, Or.inr ⟨j, hj, hv⟩, hi⟩

theorem dominates (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (d : Nat) (i : Fin C.size) (hd : i.val < d) :
    C.gateVal I i = true → hits I (support C q d i) := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    rw [gate_eq, Bool.and_eq_true] at h
    apply (hit_step C q d i I).2
    have hs : sideTrue I (vars C q i) (parents C q i) i (C.gateVal I) = true := by
      cases e : q i <;> simp [vars, parents, e]
      · exact h.1
      · exact h.2
    rw [sideTrue, decide_eq_true_eq] at hs
    rcases hs with raw | ⟨j, hj, lt, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩

theorem chosen (C : AndCountCircuit n) (I : Finset (Fin n)) (d : Nat)
    (i : Fin C.size) (hd : i.val < d) :
    hits I (support C (left C I) d i) → C.gateVal I i = true := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    intro h
    have hs : sideTrue I (vars C (left C I) i) (parents C (left C I) i) i (C.gateVal I) = true := by
      rw [sideTrue, decide_eq_true_eq]
      rcases (hit_step _ _ _ _ _).1 h with raw | ⟨j, hj, lt, val⟩
      · exact Or.inl raw
      · exact Or.inr ⟨j, hj, lt, ih j (by change j.val < i.val at lt; omega) val⟩
    rw [gate_eq, Bool.and_eq_true]
    cases hl : left C I i with
    | false =>
      simp [vars, parents, hl] at hs
      change left C I i = true at hs
      simp [hl] at hs
    | true =>
      exact ⟨rfl, by simpa [vars, parents, hl, right] using hs⟩

theorem gives_hit (C : AndCountCircuit n) (q : Fin C.size → Bool) (I : Finset (Fin n))
    (h : C.eval I = true) : hits I (clause C q) := by
  rw [eval, decide_eq_true_eq] at h
  apply (clause_hit _ _ _).2
  rcases h with raw | ⟨j, hj, val⟩
  · exact Or.inl raw
  · exact Or.inr ⟨j, hj, dominates C q I C.size j j.isLt val⟩

theorem avoids (C : AndCountCircuit n) (I : Finset (Fin n)) (h : C.eval I = false) :
    ¬ hits I (clause C (left C I)) := by
  intro hit
  have ht : C.eval I = true := by
    rw [eval, decide_eq_true_eq]
    rcases (clause_hit _ _ _).1 hit with raw | ⟨j, hj, val⟩
    · exact Or.inl raw
    · exact Or.inr ⟨j, hj, chosen C I C.size j j.isLt val⟩
  simp [h] at ht

theorem complement_clause (C : AndCountCircuit n) (I : Finset (Fin n))
    (h : C.eval I = false) (positive : ∀ u, u ∉ I → C.eval (insert u I) = true) :
    ∀ u, u ∈ I ↔ u ∉ clause C (left C I) := by
  intro u
  constructor
  · intro hu hc
    exact avoids C I h ⟨u, hc, hu⟩
  · intro absent
    by_contra missing
    obtain ⟨v, hv, hin⟩ := gives_hit C (left C I) _ (positive u missing)
    rcases Finset.mem_insert.mp hin with rfl | inside
    · exact absent hv
    · exact avoids C I h ⟨v, hv, inside⟩

def packBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | k+1, f => Nat.bit (f 0) (packBits k (fun j => f (j+1)))

theorem pack_test (k j : Nat) (f : Nat → Bool) :
    (packBits k f).testBit j = (decide (j < k) && f j) := by
  induction k generalizing j f with
  | zero => simp [packBits]
  | succ k ih =>
    cases j with
    | zero => simp [packBits]
    | succ j => simp [packBits, Nat.testBit_bit_succ, ih]

theorem pack_lt (k : Nat) (f : Nat → Bool) : packBits k f < 2^k := by
  induction k generalizing f with
  | zero => simp [packBits]
  | succ k ih =>
    have h := ih (fun j => f (j+1))
    cases hb : f 0 <;> simp [packBits, hb, Nat.bit, pow_succ] <;> omega


def bare (C : AndCountCircuit n) (side : Fin C.size × Bool) :=
  if side.2 then C.rightVars side.1 else C.leftVars side.1

def liveSides (C : AndCountCircuit n) (q : Fin C.size → Bool) :
    Nat → Fin C.size → Finset (Fin C.size × Bool)
  | 0, _ => ∅
  | d+1, i => insert (i,q i) (((parents C q i).filter (· < i)).biUnion (liveSides C q d))

theorem support_sides (C : AndCountCircuit n) (q : Fin C.size → Bool)
    (d : Nat) (i : Fin C.size) (v : Fin n) :
    v ∈ support C q d i ↔ ∃ side ∈ liveSides C q d i, v ∈ bare C side := by
  induction d generalizing i with
  | zero => simp [support, liveSides]
  | succ d ih =>
    simp only [support, liveSides, Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert]
    constructor
    · rintro (here | ⟨j,hj,previous⟩)
      · exact ⟨(i,q i), Or.inl rfl, here⟩
      · obtain ⟨s,hs,hv⟩ := (ih j).mp previous
        exact ⟨s, Or.inr ⟨j,hj,hs⟩, hv⟩
    · rintro ⟨s,hs,hv⟩
      rcases hs with rfl | ⟨j,hj,prev⟩
      · exact Or.inl hv
      · exact Or.inr ⟨j,hj,(ih j).mpr ⟨s,prev,hv⟩⟩

def reached (C : AndCountCircuit n) (q : Fin C.size → Bool) :=
  C.outGates.biUnion (liveSides C q C.size)

theorem clause_sides (C : AndCountCircuit n) (q : Fin C.size → Bool) (v : Fin n) :
    v ∈ clause C q ↔ v ∈ C.outVars ∨ ∃ s ∈ reached C q, v ∈ bare C s := by
  simp only [clause, reached, Finset.mem_union, Finset.mem_biUnion, support_sides]
  grind

def choice (C : AndCountCircuit n) (c : Fin 32) (i : Fin C.size) := c.val.testBit i.val

theorem choices_surject (C : AndCountCircuit n) (bound : C.size ≤ 5) :
    Function.Surjective (choice C) := by
  intro q
  let bits (i : Nat) := if h : i < C.size then q ⟨i,h⟩ else false
  refine ⟨⟨packBits 5 bits, pack_lt 5 bits⟩, ?_⟩
  funext i
  have hi := lt_of_lt_of_le i.isLt bound
  simp [choice, pack_test, hi, bits, i.isLt]

def encSide (s : Fin k × Bool) : Nat := 2*s.1.val + s.2.toNat

theorem side_lt (bound : k ≤ 5) (s : Fin k × Bool) : encSide s < 10 := by
  obtain ⟨i,b⟩ := s
  have hi := i.isLt
  cases b <;> simp [encSide] <;> omega

theorem side_injective : Function.Injective (@encSide k) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ eq
  cases a <;> cases b <;> simp [encSide] at eq ⊢ <;> first | exact Fin.ext (by omega) | omega

def sideMask (S : Finset (Fin k × Bool)) := packBits 10 fun j => decide (j ∈ S.image encSide)

theorem side_bit (S : Finset (Fin k × Bool)) (s : Fin k × Bool) (bound : k ≤ 5) :
    (sideMask S).testBit (encSide s) = decide (s ∈ S) := by
  have eq : encSide s ∈ S.image encSide ↔ s ∈ S := by
    constructor
    · intro h
      obtain ⟨t,ht,he⟩ := Finset.mem_image.mp h
      exact side_injective he ▸ ht
    · exact Finset.mem_image_of_mem _
  simp only [sideMask, pack_test, decide_eq_true (side_lt bound s), Bool.true_and, eq]

theorem sideMask_disjoint (S T : Finset (Fin k × Bool)) (bound : k ≤ 5) :
    sideMask S &&& sideMask T = 0 ↔ ∀ s ∈ S, s ∉ T := by
  constructor
  · intro eq s hs ht
    have bit := congrArg (fun x : Nat => x.testBit (encSide s)) eq
    simp [Nat.testBit_and, side_bit _ _ bound, hs, ht] at bit
  · intro disjoint
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases pos : j ∈ S.image encSide
    · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp pos
      simp [Nat.testBit_and, side_bit _ _ bound, disjoint s hs]
    · have absent : (sideMask S).testBit j = false := by
        simp only [sideMask, pack_test, decide_eq_false pos, Bool.and_false]
      simp [Nat.testBit_and, absent]

def variableSides (C : AndCountCircuit n) (v : Fin n) :=
  Finset.univ.filter fun s : Fin C.size × Bool => v ∈ bare C s

theorem corner_witness (C : AndCountCircuit n) (bound : C.size ≤ 5) (I : Finset (Fin n))
    (noRaw : C.outVars = ∅) (neg : C.eval I = false)
    (positive : ∀ u, u ∉ I → C.eval (insert u I) = true) :
    ∃ c : Fin 32, ∀ v, v ∈ I ↔
      sideMask (reached C (choice C c)) &&& sideMask (variableSides C v) = 0 := by
  obtain ⟨c,hc⟩ := choices_surject C bound (left C I)
  refine ⟨c, fun v => ?_⟩
  rw [hc, complement_clause C I neg positive v, clause_sides, noRaw, sideMask_disjoint _ _ bound]
  simp [variableSides]

def edgeList : List (Nat × Nat) :=
  [(0,1), (0,2), (1,3), (1,4), (2,5), (2,6), (3,5),
   (3,7), (4,6), (4,8), (5,7), (6,8), (7,8)]

abbrev graph := SimpleGraph.fromRel (fun a b : Fin 9 => (a.val,b.val) ∈ edgeList)
def negatives : List Nat := [25,28,49,73,97,98,134,145,148,193,194,262,265,268,289,290]
def rowSet (m : Nat) : Finset (Fin 9) := Finset.univ.filter fun i => m.testBit i.val

abbrev independent (I : Finset (Fin 9)) := ∀ v ∈ I, ∀ w ∈ I, ¬ graph.Adj v w
abbrev maximal (I : Finset (Fin 9)) := ∀ w : Fin 9, w ∉ I → ∃ a ∈ I, graph.Adj a w
abbrev correct (C : AndCountCircuit 9) := ∀ I, independent I → maximal I →
  C.eval I = false ∧ ∀ w, w ∉ I → C.eval (insert w I) = true

def rowCheck (I : Finset (Fin 9)) := decide (independent I) && decide (maximal I)

theorem rowCheck_spec (I : Finset (Fin 9)) : rowCheck I = true ↔ independent I ∧ maximal I := by
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq]

theorem negative_rows : ∀ m ∈ negatives, independent (rowSet m) ∧ maximal (rowSet m) := by
  have checked : negatives.all (fun m => rowCheck (rowSet m)) = true := by
    decide +kernel
  intro m hm
  exact (rowCheck_spec _).mp (List.all_eq_true.mp checked m hm)

theorem all_vertices : ∀ v : Fin 9, ∃ m ∈ negatives, v ∈ rowSet m := by decide +kernel

theorem empty_outVars (C : AndCountCircuit 9) (ok : correct C) : C.outVars = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨m,hm,member⟩ := all_vertices v
  obtain ⟨ind,maxI⟩ := negative_rows m hm
  exact avoids C _ (ok _ ind maxI).1 ⟨v, Finset.mem_union_left _ hv, member⟩

theorem required_rows (C : AndCountCircuit 9) (bound : C.size ≤ 5) (ok : correct C) :
    ∀ m ∈ negatives, ∃ c : Fin 32, ∀ v : Fin 9, m.testBit v.val = true ↔
      sideMask (reached C (choice C c)) &&& sideMask (variableSides C v) = 0 := by
  intro m hm
  obtain ⟨ind, maxI⟩ := negative_rows m hm
  obtain ⟨neg, pos⟩ := ok _ ind maxI
  obtain ⟨c,hc⟩ := corner_witness C bound _ (empty_outVars C ok) neg pos
  exact ⟨c, fun v => by simpa [rowSet] using hc v⟩

theorem live_stable (C : AndCountCircuit n) (q : Fin C.size → Bool) (a b : Nat)
    (i : Fin C.size) (ha : i.val < a) (hb : i.val < b) :
    liveSides C q a i = liveSides C q b i := by
  induction a generalizing b i with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      simp only [liveSides]
      congr 1
      apply Finset.biUnion_congr rfl
      intro j hj
      have hji : j.val < i.val := (Finset.mem_filter.mp hj).2
      exact ih b j (by omega) (by omega)

theorem live_root (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (j : Fin C.size) (hj : j.val < d) : (j,q j) ∈ liveSides C q d j := by
  cases d with
  | zero => omega
  | succ d => exact Finset.mem_insert_self _ _

theorem live_subtree (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (i j : Fin C.size) (depth : i.val < d) (found : (j,q j) ∈ liveSides C q d i) :
    liveSides C q C.size j ⊆ liveSides C q d i := by
  induction d generalizing i with
  | zero => omega
  | succ d ih =>
    rw [liveSides, Finset.mem_insert] at found
    rcases found with eq | child
    · have same : j = i := congrArg Prod.fst eq
      subst j
      exact (live_stable C q C.size (d+1) i i.isLt depth).subset
    · obtain ⟨k,hk,prev⟩ := Finset.mem_biUnion.mp child
      have lt : k.val < i.val := (Finset.mem_filter.mp hk).2
      intro s hs
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨k,hk,ih k (by omega) prev hs⟩)

theorem live_predecessor (C : AndCountCircuit n) (q : Fin C.size → Bool) (d : Nat)
    (i j : Fin C.size) (found : (j,q j) ∈ liveSides C q d i) :
    j = i ∨ ∃ k : Fin C.size, (k,q k) ∈ liveSides C q d i ∧
      j < k ∧ j ∈ parents C q k := by
  induction d generalizing i with
  | zero => simp [liveSides] at found
  | succ d ih =>
    rw [liveSides, Finset.mem_insert] at found
    rcases found with eq | child
    · exact Or.inl (congrArg Prod.fst eq)
    · obtain ⟨v,hv,prev⟩ := Finset.mem_biUnion.mp child
      rcases ih v prev with rfl | ⟨k,hk,lt,parent⟩
      · obtain ⟨parent,lt⟩ := Finset.mem_filter.mp hv
        exact Or.inr ⟨i, Finset.mem_insert_self _ _, lt, parent⟩
      · exact Or.inr ⟨k,Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨v,hv,hk⟩),lt,parent⟩

theorem reached_rule (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :
    (i,q i) ∈ reached C q ↔ i ∈ C.outGates ∨ ∃ j : Fin C.size,
      (j,q j) ∈ reached C q ∧ i < j ∧ i ∈ parents C q j := by
  constructor
  · intro hit
    obtain ⟨root,hr,mem⟩ := Finset.mem_biUnion.mp hit
    rcases live_predecessor C q C.size root i mem with rfl | ⟨j,hj,lt,parent⟩
    · exact Or.inl hr
    · exact Or.inr ⟨j,Finset.mem_biUnion.mpr ⟨root,hr,hj⟩,lt,parent⟩
  · rintro (out | ⟨j,seen,lt,parent⟩)
    · exact Finset.mem_biUnion.mpr ⟨i,out,live_root C q C.size i i.isLt⟩
    · obtain ⟨root,hr,mem⟩ := Finset.mem_biUnion.mp seen
      apply Finset.mem_biUnion.mpr
      refine ⟨root,hr,live_subtree C q C.size root j root.isLt mem ?_⟩
      rw [live_stable C q C.size (C.size+1) j j.isLt (by omega)]
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_filter.mpr ⟨parent,lt⟩,live_root C q C.size i i.isLt⟩)

theorem reached_choice (C : AndCountCircuit n) (q : Fin C.size → Bool) (s : Fin C.size × Bool)
    (hs : s ∈ reached C q) : s.2 = q s.1 := by
  have step (d : Nat) (i : Fin C.size) (mem : s ∈ liveSides C q d i) : s.2 = q s.1 := by
    induction d generalizing i with
    | zero => simp [liveSides] at mem
    | succ d ih =>
      rcases Finset.mem_insert.mp mem with eq | child
      · rw [eq]
      · obtain ⟨k,_,found⟩ := Finset.mem_biUnion.mp child
        exact ih k found
  obtain ⟨i,_,hit⟩ := Finset.mem_biUnion.mp hs
  exact step C.size i hit

def suffix (C : AndCountCircuit n) (q : Fin C.size → Bool) (k : Nat) :=
  (reached C q).filter fun s => k ≤ s.1.val

def incoming (C : AndCountCircuit n) (i : Fin C.size) :=
  Finset.univ.filter fun s : Fin C.size × Bool =>
    i < s.1 ∧ i ∈ if s.2 then C.rightGates s.1 else C.leftGates s.1

theorem active_iff (C : AndCountCircuit n) (bound : C.size ≤ 5)
    (q : Fin C.size → Bool) (i : Fin C.size) :
    (i,q i) ∈ reached C q ↔ i ∈ C.outGates ∨
      sideMask (suffix C q (i.val+1)) &&& sideMask (incoming C i) ≠ 0 := by
  rw [reached_rule]
  apply or_congr Iff.rfl
  rw [ne_eq, sideMask_disjoint _ _ bound]
  constructor
  · rintro ⟨j,hj,lt,parent⟩ disjoint
    have hs : (j,q j) ∈ suffix C q (i.val+1) :=
      Finset.mem_filter.mpr ⟨hj, show i.val < j.val from lt⟩
    exact disjoint _ hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt,parent⟩)
  · intro h
    push Not at h
    obtain ⟨⟨j,b⟩,hs,hi⟩ := h
    have seen := (Finset.mem_filter.mp hs).1
    have eq : b = q j := reached_choice C q (j,b) seen
    subst b
    obtain ⟨lt,parent⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨j,seen,lt,parent⟩

theorem suffix_step (C : AndCountCircuit n) (q : Fin C.size → Bool) (i : Fin C.size) :
    suffix C q i.val = if (i,q i) ∈ reached C q then insert (i,q i) (suffix C q (i.val+1))
      else suffix C q (i.val+1) := by
  ext s
  have atGate (h : s ∈ reached C q) (eq : s.1.val = i.val) : s = (i,q i) :=
    Prod.ext (Fin.ext eq) (by rw [reached_choice C q s h, Fin.ext eq])
  by_cases hit : (i,q i) ∈ reached C q
  · simp only [hit, ite_true, Finset.mem_insert, suffix, Finset.mem_filter]
    constructor
    · rintro ⟨h,le⟩
      by_cases eq : s.1.val = i.val
      · exact Or.inl (atGate h eq)
      · exact Or.inr ⟨h, by omega⟩
    · rintro (rfl | ⟨h,le⟩)
      · exact ⟨hit,le_rfl⟩
      · exact ⟨h,by omega⟩
  · simp only [hit, ite_false, suffix, Finset.mem_filter]
    constructor
    · rintro ⟨h,le⟩
      have ne : s.1.val ≠ i.val := fun eq => hit (atGate h eq ▸ h)
      exact ⟨h,by omega⟩
    · rintro ⟨h,le⟩; exact ⟨h,by omega⟩

theorem mask_empty : sideMask (∅ : Finset (Fin k × Bool)) = 0 := by
  apply Nat.eq_of_testBit_eq
  simp [sideMask, pack_test]

theorem mask_insert (S : Finset (Fin k × Bool)) (s : Fin k × Bool) (bound : k ≤ 5) :
    sideMask (insert s S) = sideMask S ||| 2^(encSide s) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases eq : j = encSide s
  · subst j
    simp [Nat.testBit_or, side_bit _ _ bound]
  · have same : j ∈ (insert s S).image encSide ↔ j ∈ S.image encSide := by
      rw [Finset.image_insert, Finset.mem_insert]
      simp [eq]
    simp only [Nat.testBit_or, Nat.testBit_two_pow, decide_eq_false (Ne.symm eq),
      Bool.or_false, sideMask, pack_test, same]

def expand (F : Finset Nat) (k control : Nat) (output : Bool) : Finset Nat :=
  F.biUnion fun r =>
    if output || decide (r &&& control ≠ 0) then {r ||| 2^(2*k), r ||| 2^(2*k+1)} else {r}

def fitsRows (F : Finset Nat) := ∃ f : Fin 9 → Nat, (∀ v, f v < 1024) ∧
  ∀ m ∈ negatives, ∃ r ∈ F, ∀ v : Fin 9, m.testBit v.val = true ↔ r &&& f v = 0

def realizable : Nat → Finset Nat → Prop
  | 0, F => fitsRows F
  | k+1, F => ∃ w < 1024, ∃ output : Bool, realizable k (expand F k w output)

theorem circuit_realizable_at (C : AndCountCircuit 9) (bound : C.size ≤ 5) (ok : correct C)
    (count : Nat) (above : C.size ≤ count) : realizable count {0} := by
  have build (k : Nat) (F : Finset Nat)
      (includes : ∀ c : Fin 32, sideMask (suffix C (choice C c) k) ∈ F) : realizable k F := by
    induction k generalizing F with
    | zero =>
      refine ⟨fun v => sideMask (variableSides C v), fun _ => pack_lt 10 _, ?_⟩
      intro m hm
      obtain ⟨c,eq⟩ := required_rows C bound ok m hm
      refine ⟨_,?_,eq⟩
      simpa [suffix] using includes c
    | succ k ih =>
      by_cases existsGate : k < C.size
      · let i : Fin C.size := ⟨k,existsGate⟩
        let w := sideMask (incoming C i)
        let out := decide (i ∈ C.outGates)
        refine ⟨w,pack_lt 10 _,out,ih _ ?_⟩
        intro c
        let q := choice C c
        let old := sideMask (suffix C q (k+1))
        apply Finset.mem_biUnion.mpr
        refine ⟨old,includes c,?_⟩
        have step := suffix_step C q i
        change suffix C q k = _ at step
        have cond := active_iff C bound q i
        change (i,q i) ∈ reached C q ↔ i ∈ C.outGates ∨ old &&& w ≠ 0 at cond
        change sideMask (suffix C q k) ∈
          (if out || decide (old &&& w ≠ 0) then {old ||| 2^(2*k),old ||| 2^(2*k+1)} else {old})
        rw [step]
        by_cases active : (i,q i) ∈ reached C q
        · have test : (out || decide (old &&& w ≠ 0)) = true := by
            simpa [out, Bool.or_eq_true] using cond.mp active
          rw [ite_eq_left active, test, ite_eq_left rfl, mask_insert _ _ bound]
          cases q i <;> simp [encSide, i, old]
        · have test : (out || decide (old &&& w ≠ 0)) = false := by
            have neg := mt cond.mpr active
            simp_all [out]
          rw [ite_eq_right active, test, ite_eq_right (by decide : ¬ false = true)]
          exact Finset.mem_singleton_self _
      · refine ⟨0,by decide,false,ih _ ?_⟩
        intro c
        have empty (j : Nat) (hj : k ≤ j) : suffix C (choice C c) j = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro s hs
          have := (Finset.mem_filter.mp hs).2
          have := s.1.isLt
          omega
        have zero := includes c
        rw [empty (k+1) (by omega), mask_empty] at zero
        rw [empty k le_rfl, mask_empty]
        exact Finset.mem_biUnion.mpr ⟨0,zero,by simp⟩
  apply build
  intro c
  have empty : suffix C (choice C c) count = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have five := (Finset.mem_filter.mp hs).2
    have small := s.1.isLt
    omega
  simp [empty, mask_empty]

theorem circuit_realizable (C : AndCountCircuit 9) (bound : C.size ≤ 5) (ok : correct C) :
    realizable 5 {0} := circuit_realizable_at C bound ok 5 bound

def rowValue (f : Fin 9 → Nat) (r : Nat) := packBits 9 fun i =>
  if hi : i < 9 then decide (r &&& f ⟨i,hi⟩ = 0) else false

theorem negative_bound : ∀ m ∈ negatives, m < 512 := by
  have all : negatives.all (fun m => decide (m < 512)) = true := by decide +kernel
  intro m hm; exact of_decide_eq_true (List.all_eq_true.mp all _ hm)

theorem rowValue_eq (f : Fin 9 → Nat) (m r : Nat) (bound : m < 512)
    (e : ∀ v : Fin 9, m.testBit v.val = true ↔ r &&& f v = 0) : rowValue f r = m := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j < 9
  · have eq := e ⟨j,h⟩
    cases b : m.testBit j <;> simp_all [rowValue, pack_test]
  · have large : 2^9 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    simp [rowValue, pack_test, h, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le bound large)]

theorem required_card (F : Finset Nat) (ok : fitsRows F) : 16 ≤ F.card := by
  obtain ⟨f,_,all⟩ := ok
  have sub : negatives.toFinset ⊆ F.image (rowValue f) := by
    intro m hm
    have mem := List.mem_toFinset.mp hm
    obtain ⟨r,hr,e⟩ := all m mem
    exact Finset.mem_image.mpr ⟨r,hr,rowValue_eq f m r (negative_bound m mem) e⟩
  have sz : negatives.toFinset.card = 16 := by decide +kernel
  exact sz ▸ (Finset.card_le_card sub).trans Finset.card_image_le

theorem expand_card (F : Finset Nat) (k w : Nat) (out : Bool) :
    (expand F k w out).card ≤ 2 * F.card := by
  unfold expand
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _r ∈ F, 2 := by
      apply Finset.sum_le_sum
      intro r hr
      split
      · exact (Finset.card_insert_le _ _).trans (by simp)
      · simp
    _ = _ := by simp [Nat.mul_comm]

theorem capacity (k : Nat) (F : Finset Nat) (ok : realizable k F) : 16 ≤ 2^k * F.card := by
  induction k generalizing F with
  | zero => simpa using required_card F ok
  | succ k ih =>
    obtain ⟨w,_,out,next⟩ := ok
    calc
      16 ≤ 2^k * (expand F k w out).card := ih _ next
      _ ≤ 2^k * (2 * F.card) := Nat.mul_le_mul_left _ (expand_card F k w out)
      _ = _ := by rw [pow_succ, Nat.mul_assoc]

theorem forced_expansion (k : Nat) (F : Finset Nat) (full : 2^(k+1) * F.card = 16)
    (ok : realizable (k+1) F) : realizable k (expand F k 0 true) := by
  obtain ⟨w,_,out,next⟩ := ok
  have cap := capacity k _ next
  have maxed : 2 * F.card ≤ (expand F k w out).card := by
    rw [← full, pow_succ, Nat.mul_assoc] at cap
    exact Nat.le_of_mul_le_mul_left cap (by positivity)
  have every (r : Nat) (hr : r ∈ F) : (out || decide (r &&& w ≠ 0)) = true := by
    by_contra miss
    have bounds : expand F k w out ⊆ insert r (expand (F.erase r) k w out) := by
      intro x hx
      obtain ⟨s,hs,hx⟩ := Finset.mem_biUnion.mp hx
      by_cases eq : s = r
      · subst s
        have same : x = r := by simpa only [ite_eq_right miss, Finset.mem_singleton] using hx
        exact Finset.mem_insert.mpr (Or.inl same)
      · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨s,Finset.mem_erase.mpr ⟨eq,hs⟩,hx⟩)
    have one := (Finset.card_le_card bounds).trans (Finset.card_insert_le _ _)
    have two := expand_card (F.erase r) k w out
    have rm := Finset.card_erase_add_one hr
    omega
  have same : expand F k 0 true = expand F k w out := by
    unfold expand
    apply Finset.biUnion_congr rfl
    intro r hr
    simp only [every r hr, Bool.true_or]
  rwa [same]

def targetGroup (v : Fin 9) (b : Bool) := negatives.toFinset.filter fun m => m.testBit v.val = b

def cornerGroup (F : Finset Nat) (w : Nat) (b : Bool) := F.filter fun r => decide (r &&& w = 0) = b

theorem group_bound (F : Finset Nat) (f : Fin 9 → Nat)
    (all : ∀ m ∈ negatives, ∃ r ∈ F, ∀ v : Fin 9, m.testBit v.val = true ↔ r &&& f v = 0)
    (v : Fin 9) (b : Bool) : (targetGroup v b).card ≤ (cornerGroup F (f v) b).card := by
  have sub : targetGroup v b ⊆ (cornerGroup F (f v) b).image (rowValue f) := by
    intro m hm
    obtain ⟨inList,bit⟩ := Finset.mem_filter.mp hm
    have mem := List.mem_toFinset.mp inList
    obtain ⟨r,hr,e⟩ := all m mem
    refine Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr,?_⟩, rowValue_eq f m r (negative_bound m mem) e⟩
    have atV := e v
    cases b <;> simp_all
  exact (Finset.card_le_card sub).trans Finset.card_image_le

def first : Finset Nat := expand {0} 3 0 true
def second := expand first 2 0 true
def third := expand second 1 0 true
def fourth := expand third 0 0 true

theorem four_impossible : ¬ realizable 4 {0} := by
  intro ok
  have a : realizable 3 first := forced_expansion 3 {0} (by decide +kernel) ok
  have b : realizable 2 second := forced_expansion 2 first (by decide +kernel) a
  have c : realizable 1 third := forced_expansion 1 second (by decide +kernel) b
  have d : fitsRows fourth := forced_expansion 0 third (by decide +kernel) c
  obtain ⟨f,bounded,all⟩ := d
  have need := group_bound fourth f all 1 true
  have other := group_bound fourth f all 1 false
  have yesCount : (targetGroup 1 true).card = 5 := by decide +kernel
  have noCount : (targetGroup 1 false).card = 11 := by decide +kernel
  rw [yesCount] at need
  rw [noCount] at other
  have test : (List.range 1024).all (fun w =>
      decide (¬ (5 ≤ (cornerGroup fourth w true).card ∧ 11 ≤ (cornerGroup fourth w false).card))) = true := by
    decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp test (f 1) (List.mem_range.mpr (bounded 1)))) ⟨need,other⟩

theorem five_necessary (C : AndCountCircuit 9) (ok : correct C) : 5 ≤ C.size := by
  by_contra low
  exact four_impossible (circuit_realizable_at C (by omega) ok 4 (by omega))

def oldIndex (perm j : Nat) := (perm >>> (4*j)) % 16
def relabel (perm a : Nat) := packBits 10 fun j => a.testBit (oldIndex perm j)
abbrev permOK (perm : Nat) := ∀ i : Fin 10, ∃ j : Fin 10, oldIndex perm j.val = i.val
theorem relabel_inter (p a b : Nat) : relabel p (a &&& b) = relabel p a &&& relabel p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10 <;> simp [relabel, pack_test, Nat.testBit_and, hi]

theorem relabel_zero (p a : Nat) (hp : permOK p) (ha : a < 1024) :
    relabel p a = 0 ↔ a = 0 := by
  constructor
  · intro eq
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 10
    · obtain ⟨j,hj⟩ := hp ⟨i,hi⟩
      have bit := congrArg (fun x : Nat => x.testBit j.val) eq
      simpa [relabel, pack_test, j.isLt, hj] using bit
    · have large : 2^10 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha large)
  · rintro rfl
    apply Nat.eq_of_testBit_eq
    simp [relabel, pack_test]

theorem relabeled_pair (perm : Nat) (ok : permOK perm) (a b : Nat) (hb : b < 1024) :
    relabel perm a &&& relabel perm b = 0 ↔ a &&& b = 0 := by
  rw [← relabel_inter]
  exact relabel_zero _ _ ok (lt_of_le_of_lt Nat.and_le_right hb)


theorem relabel_or (p a b : Nat) : relabel p (a ||| b) = relabel p a ||| relabel p b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 10 <;> simp [relabel, pack_test, Nat.testBit_or, hi]

abbrev fixesLow (p k : Nat) := ∀ i : Fin (2*k), relabel p (2^i.val) = 2^i.val

theorem realizable_transfer (k : Nat) (F H : Finset Nat) (p : Nat) (hp : permOK p)
    (fixes : fixesLow p k) (sub : ∀ r ∈ F, relabel p r ∈ H)
    (ok : realizable k F) : realizable k H := by
  induction k generalizing F H with
  | zero =>
    obtain ⟨f,bound,all⟩ := ok
    refine ⟨fun v => relabel p (f v),fun _ => pack_lt 10 _,?_⟩
    intro m hm
    obtain ⟨r,hr,eq⟩ := all m hm
    exact ⟨_,sub r hr,fun v => (eq v).trans (relabeled_pair p hp r (f v) (bound v)).symm⟩
  | succ k ih =>
    obtain ⟨w,hw,out,next⟩ := ok
    refine ⟨relabel p w,pack_lt 10 _,out,ih _ _ (fun i => fixes ⟨i.val,by have := i.isLt; omega⟩) ?_ next⟩
    intro x hx
    obtain ⟨r,hr,hx⟩ := Finset.mem_biUnion.mp hx
    refine Finset.mem_biUnion.mpr ⟨relabel p r,sub r hr,?_⟩
    have hit := relabeled_pair p hp r w hw
    by_cases h : (out || decide (r &&& w ≠ 0)) = true
    · have h' : (out || decide (relabel p r &&& relabel p w ≠ 0)) = true := by simpa only [ne_eq, hit] using h
      simp only [h, ite_true, Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [h', ite_true, Finset.mem_insert, Finset.mem_singleton]
      rcases hx with rfl | rfl
      · exact Or.inl ((relabel_or _ _ _).trans (congrArg _ (fixes ⟨2*k,by omega⟩)))
      · exact Or.inr ((relabel_or _ _ _).trans (congrArg _ (fixes ⟨2*k+1,by omega⟩)))
    · have h' : ¬ (out || decide (relabel p r &&& relabel p w ≠ 0)) = true := by simpa only [ne_eq, hit] using h
      rw [ite_eq_right h] at hx
      have eq := Finset.mem_singleton.mp hx
      rw [ite_eq_right h', Finset.mem_singleton, eq]


def freeBits (k : Nat) := 2*(k+1)

def domain (k : Nat) := (1023 >>> freeBits k) <<< freeBits k

theorem controls_recovered (k : Fin 5) (w : Fin 1024) :
    ((w.val >>> freeBits k.val) <<< freeBits k.val) = (w.val &&& domain k.val) ∧
    w.val >>> freeBits k.val < 2^(8-2*k.val) := by
  have yes : ∀ i : Fin 5, ∀ u : Fin 1024,
      ((u.val >>> freeBits i.val) <<< freeBits i.val) = (u.val &&& domain i.val) ∧
      u.val >>> freeBits i.val < 2^(8-2*i.val) := by decide +kernel
  exact yes k w

theorem expand_collapses (F : Finset Nat) (k w : Nat) (out : Bool)
    (stored : ∀ r ∈ F, r &&& domain k = r) :
    expand F k w out = expand F k (w &&& domain k) out := by
  apply Finset.biUnion_congr rfl
  intro r hr
  have eq : r &&& (w &&& domain k) = r &&& w := by
    rw [Nat.and_comm w, ← Nat.and_assoc, stored r hr]
  rw [eq]

def nextRows (rows : List Nat) (k j : Nat) : List Nat :=
  rows.flatMap fun r =>
    if j = 2^(8-2*k) ∨ r &&& (j <<< freeBits k) ≠ 0 then
      [r ||| 2^(2*k), r ||| 2^(2*k+1)] else [r]

theorem children_rows (rows : List Nat) (k j : Nat) (_le : j ≤ 2^(8-2*k)) :
    (nextRows rows k j).toFinset =
      expand rows.toFinset k (j <<< freeBits k) (decide (j = 2^(8-2*k))) := by
  ext x
  simp only [nextRows, List.mem_toFinset, List.mem_flatMap, expand, Finset.mem_biUnion]
  apply exists_congr
  intro r
  by_cases h : j = 2^(8-2*k) ∨ r &&& (j <<< freeBits k) ≠ 0
  · simp [h, Bool.or_eq_true, List.mem_cons, Finset.mem_insert]
  · simp [h, Bool.or_eq_true]

theorem choose_child (rows : List Nat) (k : Fin 5)
    (stored : ∀ r ∈ rows, r &&& domain k.val = r) (ok : realizable (k.val+1) rows.toFinset) :
    ∃ j ≤ 2^(8-2*k.val), realizable k.val (nextRows rows k.val j).toFinset := by
  obtain ⟨w,hw,out,good⟩ := ok
  have norm := controls_recovered k ⟨w,hw⟩
  cases out with
  | false =>
    refine ⟨_,norm.2.le,?_⟩
    rw [children_rows _ _ _ norm.2.le, norm.1]
    simpa only [decide_eq_false (Nat.ne_of_lt norm.2)] using
      expand_collapses rows.toFinset k.val w false (by simpa using stored) ▸ good
  | true =>
    refine ⟨_,Nat.le_refl _,?_⟩
    rw [children_rows _ _ _ le_rfl]
    simpa [expand] using good


def hostAt (hosts : Array (List Nat)) (j : Nat) := hosts[j]?.getD []

def entryAt (width bits : Nat) (tags : Array Nat) (j : Nat) :=
  tags[((bits >>> (width*j)) % (2^width))]?.getD 0

def transitionOK (hosts : Array (List Nat)) (rows : List Nat) (k j tag : Nat) : Bool :=
  let child := nextRows rows k j
  if tag = 0 then decide (2^k * child.length < 16) else
    let idx := tag % 512
    let p := tag >>> 9
    decide (idx < hosts.size) && decide (permOK p) && decide (fixesLow p k) &&
      child.all fun r => (hostAt hosts idx).contains (relabel p r)

theorem transition_sound (hosts : Array (List Nat)) (rows : List Nat) (k j tag : Nat)
    (checked : transitionOK hosts rows k j tag = true)
    (possible : realizable k (nextRows rows k j).toFinset) :
    ∃ i < hosts.size, realizable k (hostAt hosts i).toFinset := by
  unfold transitionOK at checked
  dsimp only at checked
  split at checked
  · have cap := capacity k _ possible
    have large := cap.trans (Nat.mul_le_mul_left (2^k) (List.toFinset_card_le (l := nextRows rows k j)))
    exact False.elim ((Nat.not_lt_of_le large) (of_decide_eq_true checked))
  · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checked
    refine ⟨_,checked.1.1.1,realizable_transfer k _ _ _ checked.1.1.2 checked.1.2 ?_ possible⟩
    intro r hr
    simpa using checked.2 r (List.mem_toFinset.mp hr)

def checkParent (hosts : Array (List Nat)) (rows : List Nat) (k width bits : Nat) (tags : Array Nat) :=
  rows.all (fun r => r &&& domain k == r) &&
    (List.range (2^(8-2*k)+1)).all (fun j => transitionOK hosts rows k j (entryAt width bits tags j))

theorem descend (hosts : Array (List Nat)) (rows : List Nat) (k : Fin 5) (width bits : Nat) (tags : Array Nat)
    (checked : checkParent hosts rows k.val width bits tags = true)
    (possible : realizable (k.val+1) rows.toFinset) : ∃ i < hosts.size, realizable k.val (hostAt hosts i).toFinset := by
  simp only [checkParent, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at checked
  obtain ⟨j,le,good⟩ := choose_child rows k checked.1 possible
  exact transition_sound hosts rows k.val j _ (checked.2 j (List.mem_range.mpr (by omega))) good

def hosts0 : Array (List Nat) := #[[0]]

def hosts1 : Array (List Nat) := #[[0],[256,512]]

def hosts2 : Array (List Nat) := #[[256,512],[320,384,512],[320,384,576,640]]

def hosts3 : Array (List Nat) := #[[272,288,576,640],[288,336,400,576,640],[320,384,576,640],[336,352,384,512],[336,352,384,592,608,640],[336,352,400,416,512],[336,352,400,416,592,608,640],[336,352,400,416,592,608,656,672]]

def hosts4 : Array (List Nat) := #[[88,104,340,356,384,596,612,640],[104,340,344,356,384,596,600,612,640],[264,340,356,404,420,592,608,640],[276,292,328,392,592,608,656,672],[280,296,340,356,388,592,608,640],[280,296,340,356,404,420,584,596,612,648,660,676],[280,296,340,356,404,420,592,608,640],[292,328,340,392,404,592,608,656,672],[296,340,344,356,404,408,420,596,600,608,660,664,672],[324,328,388,392,592,608,656,672],[324,328,404,408,420,424,596,600,612,616,656,672],[328,340,356,392,404,420,596,600,612,616,656,672],[328,340,356,400,416,584,596,612,656,672],[328,340,356,404,408,420,424,596,600,612,616,656,672],[336,352,400,416,520,596,612,644],[336,352,400,416,520,596,612,660,676],[336,352,400,416,592,608,656,672],[340,344,352,384,596,600,608,640],[340,344,352,404,408,416,536,596,608,660,672],[340,344,352,404,408,416,544,596,600,660,664],[340,344,352,404,408,416,596,600,608,640],[340,344,352,404,408,416,596,600,608,660,664,672],[340,344,356,360,384,596,600,612,616,640],[340,344,356,360,388,392,592,608,640],[340,344,356,360,388,392,592,608,656,672],[340,344,356,360,400,416,584,596,612,640],[340,344,356,360,404,408,416,512],[340,344,356,360,404,408,416,596,600,612,616,640],[340,344,356,360,404,408,416,596,600,612,616,660,664,672],[340,344,356,360,404,408,420,424,512],[340,344,356,360,404,408,420,424,596,600,612,616,640],[340,344,356,360,404,408,420,424,596,600,612,616,660,664,672],[340,344,356,360,404,408,420,424,596,600,612,616,660,664,676,680]]

def hosts5 : Array (List Nat) := #[[26,341,342,345,352,405,406,409,416,534,597,601,608,661,665,672],[26,341,342,345,352,405,406,409,416,597,598,601,608,661,662,665,672],[74,326,341,345,357,361,404,408,416,582,597,601,613,617,660,664,672],[74,341,342,345,357,358,361,400,416,597,598,601,613,614,617,640],[85,86,89,90,101,102,105,106,386,405,409,421,425,660,664,672],[85,86,89,90,101,102,105,106,405,406,408,416,661,662,664,672],[85,86,89,90,101,102,105,106,405,406,409,410,416,661,662,665,666,672],[85,86,89,90,356,360,402,405,409,416,612,616,658,661,665,672],[85,86,89,90,356,360,405,406,409,410,416,612,616,661,662,665,666,672],[85,86,89,90,357,358,360,405,406,409,410,416,613,614,616,661,662,665,666,672],[85,86,89,90,357,358,361,362,405,406,409,410,416,613,614,617,618,661,662,665,666,672],[85,86,101,102,344,360,405,406,408,416,600,616,661,662,664,672],[85,86,344,357,358,360,405,406,408,416,600,613,614,616,661,662,664,672],[85,86,345,346,357,358,360,405,406,409,410,416,601,602,613,614,616,661,662,665,666,672],[85,89,326,330,357,361,404,408,416,582,586,613,617,660,664,672],[85,89,342,346,356,360,402,405,409,416,598,602,612,616,658,661,665,672],[85,149,282,342,345,352,406,409,416,538,598,601,608,662,665,672],[86,90,102,106,341,345,353,404,408,416,597,601,609,660,664,672],[86,90,102,106,341,345,357,361,386,405,409,421,425,597,601,613,617,642,661,665,677,681],[86,90,102,106,341,345,357,361,402,405,409,416,597,601,613,617,658,661,665,672],[86,90,102,106,341,345,357,361,404,408,416,581,585,660,664,672],[86,90,102,106,341,345,357,361,404,408,416,597,601,613,617,640],[86,90,102,106,341,345,357,361,405,406,408,416,597,601,613,617,661,662,664,672],[86,90,102,106,341,345,357,361,405,406,409,410,416,597,601,613,617,661,662,665,666,672],[86,90,150,154,341,345,356,360,405,409,416,597,601,612,616,661,665,672],[86,90,341,345,353,354,404,408,416,597,601,609,610,660,664,672],[86,90,341,345,354,357,361,386,405,409,421,425,597,601,610,613,617,642,661,665,677,681],[86,90,341,345,354,357,361,405,406,409,410,416,597,601,610,613,617,661,662,665,666,672],[86,90,341,345,356,360,402,405,409,416,597,601,612,616,658,661,665,672],[86,90,341,345,357,358,360,392,405,406,421,422,597,601,613,614,616,648,661,662,677,678],[86,90,341,345,357,358,360,405,406,409,410,416,597,601,613,614,616,661,662,665,666,672],[86,90,341,345,357,358,361,362,405,406,409,410,416,597,601,613,614,617,618,661,662,665,666,672],[86,102,150,166,280,296,341,357,405,421,584,597,613,648,661,677],[86,102,341,344,357,360,392,405,406,421,422,597,600,613,616,648,661,662,677,678],[86,102,341,344,357,360,405,406,408,416,597,600,613,616,661,662,664,672],[86,150,282,341,345,352,405,409,416,538,597,601,608,661,665,672],[86,150,341,345,346,357,358,360,405,409,410,416,597,601,602,613,614,616,661,665,666,672],[86,341,344,357,358,360,405,406,408,416,597,600,613,614,616,661,662,664,672],[86,341,345,346,357,358,360,405,406,409,410,416,597,601,602,613,614,616,661,662,665,666,672],[89,90,105,106,341,342,356,405,406,409,410,416,597,598,612,661,662,665,666,672],[89,90,105,106,341,342,357,358,404,409,410,416,597,598,613,614,660,665,666,672],[89,90,153,154,341,342,356,360,405,406,416,597,598,612,616,661,662,672],[89,90,341,342,356,360,402,405,409,416,597,598,612,616,658,661,665,672],[89,90,341,342,356,360,405,406,409,410,416,597,598,612,616,661,662,665,666,672],[89,104,278,282,341,356,405,409,416,534,538,597,612,661,665,672],[89,105,326,330,341,357,404,408,416,582,586,597,613,660,664,672],[89,105,338,341,354,357,392,404,420,594,597,610,613,648,660,676],[89,153,282,341,342,356,360,405,406,420,424,538,597,598,612,616,661,662,676,680],[89,153,294,341,342,346,357,360,405,406,410,421,424,550,597,598,602,613,616,661,662,666,677,680],[89,153,341,342,346,356,360,402,405,416,597,598,602,612,616,658,661,672],[89,326,330,341,357,361,404,408,416,582,586,597,613,617,660,664,672],[89,341,342,346,356,360,402,405,409,416,597,598,602,612,616,658,661,665,672],[90,98,341,342,345,357,361,404,408,416,597,598,601,613,617,660,664,672],[90,106,341,342,345,357,358,361,384,597,598,601,613,614,617,640],[90,106,341,342,345,357,358,361,392,405,406,421,422,597,598,601,613,614,617,648,661,662,677,678],[90,106,341,342,345,357,358,361,405,406,409,410,416,597,598,601,613,614,617,661,662,665,666,672],[90,154,294,341,342,345,357,360,405,406,409,421,424,550,597,598,601,613,616,661,662,665,677,680],[90,154,341,342,345,352,405,406,409,416,533,544,598,601,662,665],[90,154,341,342,345,352,405,406,409,416,534,544,597,601,661,665],[90,154,341,342,345,352,405,406,409,416,544,597,598,601,661,662,665],[90,154,341,342,345,356,360,405,406,409,416,597,598,601,612,616,661,662,665,672],[90,154,341,342,345,357,358,360,405,406,409,416,597,598,601,613,614,616,661,662,665,672],[90,341,342,345,353,354,404,408,416,597,598,601,609,610,660,664,672],[90,341,342,345,353,354,404,408,420,424,597,598,601,609,610,660,664,676,680],[90,341,342,345,356,360,402,405,409,416,597,598,601,612,616,658,661,665,672],[90,341,342,345,357,358,360,392,405,406,421,422,597,598,601,613,614,616,648,661,662,677,678],[90,341,342,345,357,358,360,405,406,409,410,416,597,598,601,613,614,616,661,662,665,666,672],[90,341,342,345,357,358,361,362,405,406,409,410,416,597,598,601,613,614,617,618,661,662,665,666,672],[98,105,341,342,345,346,357,404,408,416,597,598,601,602,613,660,664,672],[98,341,342,345,346,357,361,404,408,416,597,598,601,602,613,617,660,664,672],[101,102,105,106,341,342,345,346,404,408,416,597,598,601,602,660,664,672],[101,102,105,106,341,342,345,346,405,406,408,416,597,598,601,602,661,662,664,672],[101,102,341,342,344,360,405,406,408,416,597,598,600,616,661,662,664,672],[101,102,341,342,345,346,361,362,405,406,408,416,597,598,601,602,617,618,661,662,664,672],[101,105,341,342,345,346,354,404,408,416,597,598,601,602,610,660,664,672],[102,106,341,342,345,346,357,361,402,405,409,416,597,598,601,602,613,617,658,661,665,672],[102,106,341,342,345,346,357,361,405,406,408,416,597,598,601,602,613,617,661,662,664,672],[102,341,342,344,357,360,392,405,406,421,422,597,598,600,613,616,648,661,662,677,678],[102,341,342,344,357,360,405,406,408,416,597,598,600,613,616,661,662,664,672],[104,278,282,341,345,356,405,409,416,534,538,597,601,612,661,665,672],[104,341,342,345,346,356,401,402,416,597,598,601,602,612,657,658,672],[105,106,341,342,345,346,357,358,402,405,409,420,424,597,598,601,602,613,614,658,661,665,676,680],[105,326,330,341,345,357,404,408,416,582,586,597,601,613,660,664,672],[106,341,342,345,346,357,358,361,384,597,598,601,602,613,614,617,640],[106,341,342,345,346,357,358,361,405,406,409,410,416,597,598,601,602,613,614,617,661,662,665,666,672],[149,150,282,341,342,345,352,409,416,538,597,598,601,608,665,672],[149,282,341,342,345,352,406,409,416,538,597,598,601,608,662,665,672],[150,166,341,342,344,357,358,360,392,405,421,597,598,600,613,614,616,648,661,677],[150,282,341,342,345,352,405,409,416,538,597,598,601,608,661,665,672],[150,341,342,345,346,357,358,360,405,409,410,416,597,598,601,602,613,614,616,661,665,666,672],[153,154,341,342,345,346,356,360,405,406,416,597,598,601,602,612,616,661,662,672],[153,169,340,344,356,360,386,405,421,596,600,612,616,642,661,677],[153,341,342,345,346,356,360,402,405,416,597,598,601,602,612,616,658,661,672],[154,341,342,345,346,357,358,360,405,406,409,416,597,598,601,602,613,614,616,661,662,665,672],[165,330,341,342,345,357,358,361,405,406,408,422,424,586,597,598,601,613,614,617,661,662,664,678,680],[165,341,342,344,357,358,360,390,405,408,424,597,598,600,613,614,616,646,661,664,680],[166,330,341,342,345,357,358,361,405,406,408,421,424,586,597,598,601,613,614,617,661,662,664,677,680],[166,341,342,344,357,358,360,392,405,406,421,597,598,600,613,614,616,648,661,662,677],[168,341,342,345,346,353,354,404,408,420,597,598,601,602,609,610,660,664,676],[169,340,344,356,360,386,405,409,421,596,600,612,616,642,661,665,677],[266,278,294,341,345,357,361,405,409,421,425,584,596,612,656,672],[266,281,326,341,357,361,390,405,421,425,596,600,608,660,664,672],[266,297,326,341,345,357,390,405,409,421,596,600,608,660,664,672],[266,337,342,353,358,401,406,417,422,596,600,612,616,648,660,676],[266,341,342,345,357,358,361,405,406,409,421,422,425,597,598,600,613,614,616,648,661,662,677,678],[274,290,341,345,357,361,405,409,421,425,584,596,612,648,660,676],[277,278,281,282,293,294,296,597,598,601,602,608,661,662,665,666,672],[277,280,293,296,342,358,406,422,582,584,597,613,646,648,661,677],[277,281,326,330,357,361,386,421,425,596,600,612,616,660,664,672],[277,293,329,338,354,393,402,418,596,600,612,616,660,664,676,680],[277,293,330,342,345,358,361,394,406,409,422,425,597,598,600,613,614,616,661,662,664,677,678,680],[277,293,338,345,354,361,393,402,418,596,600,612,616,648,660,676],[277,293,338,345,354,361,402,409,418,425,596,600,612,616,648,660,676],[277,293,342,344,358,360,406,408,422,424,582,597,600,613,616,646,661,664,677,680],[278,280,294,296,341,357,405,421,582,584,597,613,646,648,661,677],[278,282,290,341,345,357,361,405,409,421,425,578,597,601,613,617,642,661,665,677,681],[278,282,290,341,345,357,361,405,409,421,425,582,586,597,601,613,617,642,661,665,677,681],[278,282,290,341,345,357,361,405,409,421,425,596,600,608,660,664,672],[278,282,290,341,345,357,361,405,409,421,425,596,600,612,616,640],[278,282,290,341,345,357,361,405,409,421,425,597,598,601,602,608,661,662,665,666,672],[278,282,294,296,341,345,357,405,409,421,597,598,601,602,608,661,662,665,666,672],[278,282,294,298,341,345,357,361,405,409,417,596,600,612,616,640],[278,282,294,298,341,345,357,361,405,409,421,425,596,600,612,616,640],[278,282,341,345,352,405,409,416,534,538,597,601,608,661,665,672],[278,294,330,341,345,357,361,394,405,409,421,425,594,597,601,610,613,617,658,661,665,674,677,681],[278,294,330,341,345,357,361,394,405,409,421,425,597,598,600,613,614,616,661,662,664,677,678,680],[278,294,341,344,357,360,405,408,421,424,582,597,600,613,616,646,661,664,677,680],[278,294,341,344,357,360,405,408,421,424,597,598,600,613,614,616,645,648,662,678],[278,294,341,344,357,360,405,408,421,424,597,598,600,613,614,616,646,648,661,677],[278,294,341,344,357,360,405,408,421,424,597,598,600,613,614,616,648,661,662,677,678],[280,296,341,342,357,358,405,406,421,422,581,582,584,645,646,648],[280,296,341,342,357,358,405,406,421,422,582,584,597,613,646,648,661,677],[280,296,341,342,357,358,405,406,421,422,584,597,598,613,614,648,661,662,677,678],[281,282,290,297,341,342,357,405,406,421,596,600,608,660,664,672],[281,282,296,341,342,356,405,406,420,594,597,601,608,658,661,665,672],[281,282,296,341,342,356,405,406,420,597,598,601,602,608,661,662,665,666,672],[281,282,341,342,354,357,361,405,406,418,421,425,597,598,601,602,612,616,661,662,665,666,676,680],[281,282,341,342,356,360,405,406,420,424,594,597,601,612,616,658,661,665,676,680],[281,296,341,342,346,356,405,406,410,420,594,597,601,608,658,661,665,672],[281,297,338,341,354,357,386,405,421,596,600,612,616,648,660,676],[281,297,338,341,354,357,402,405,418,421,596,600,612,616,648,660,676],[281,341,342,346,354,357,361,405,406,410,418,421,425,537,597,598,602,612,616,661,662,666,676,680],[281,341,342,346,356,360,405,406,410,420,424,537,594,597,612,616,658,661,676,680],[282,296,341,342,345,356,405,406,409,420,593,594,608,657,658,672],[282,296,341,342,345,356,405,406,409,420,594,597,601,608,658,661,665,672],[282,296,341,342,345,357,358,405,406,409,421,422,584,597,598,613,614,648,661,662,677,678],[282,296,341,342,345,357,358,405,406,409,421,422,597,598,601,602,608,661,662,665,666,672],[282,298,341,342,345,357,358,361,390,405,409,421,425,594,597,601,610,613,617,642,661,665,677,681],[282,298,341,342,345,357,358,361,405,406,409,421,422,425,586,597,598,601,613,614,617,650,661,662,665,677,678,681],[282,298,341,342,345,357,358,361,405,406,409,421,422,425,597,598,600,613,614,616,645,648,662,678],[282,298,341,342,345,357,358,361,405,406,409,421,422,425,597,598,600,613,614,616,646,648,661,677],[282,298,341,342,345,357,358,361,405,406,409,421,422,425,597,598,600,613,614,616,648,661,662,677,678],[282,341,342,345,352,405,406,409,416,538,597,598,601,608,661,662,665,672],[282,341,342,345,353,354,405,406,409,417,418,538,597,598,601,612,616,661,662,665,676,680],[282,341,342,345,354,357,361,405,406,409,418,421,425,538,597,598,601,612,616,661,662,665,676,680],[290,293,297,341,342,345,346,405,406,409,410,596,600,608,660,664,672],[290,341,342,345,346,357,361,402,405,409,421,425,582,586,597,601,613,617,642,661,665,677,681],[293,294,296,341,342,344,405,406,408,597,598,600,608,661,662,664,672],[293,294,330,341,342,345,361,394,405,406,409,425,594,597,601,610,613,617,658,661,665,674,677,681],[293,329,338,341,354,393,402,405,418,596,600,612,616,660,664,676,680],[293,330,341,342,345,358,361,394,405,406,409,422,425,597,598,600,613,614,616,661,662,664,677,678,680],[293,341,342,344,358,360,405,406,408,422,424,582,597,600,613,616,646,661,664,677,680],[294,296,341,342,344,357,405,406,408,421,584,597,598,613,614,648,661,662,677,678],[294,296,341,342,344,357,405,406,408,421,597,598,600,608,661,662,664,672],[294,330,341,342,345,357,361,394,405,406,409,421,425,594,597,601,610,613,617,658,661,665,674,677,681],[294,330,341,342,345,357,361,394,405,406,409,421,425,597,598,600,613,614,616,661,662,664,677,678,680],[294,341,342,344,357,360,405,406,408,421,424,582,597,600,613,616,646,661,664,677,680],[296,340,344,356,404,408,420,553,578,597,601,613,642,661,665,677],[296,340,344,356,404,408,420,578,597,601,613,617,642,661,665,677,681],[296,341,342,344,357,358,405,406,408,421,422,584,597,598,613,614,648,661,662,677,678],[296,341,342,344,357,358,405,406,408,421,422,597,598,600,608,661,662,664,672],[296,341,342,345,346,356,405,406,409,410,420,594,597,601,608,658,661,665,672],[296,341,342,345,346,357,358,405,406,409,410,421,422,597,598,601,602,608,661,662,665,666,672],[297,298,338,341,345,357,358,402,405,409,421,422,597,598,601,602,612,616,661,662,665,666,676,680],[297,338,341,345,354,357,402,405,409,418,421,552,597,598,601,602,612,661,662,665,666,676],[297,338,341,345,357,358,362,402,405,409,421,422,426,597,598,601,602,612,616,661,662,665,666,676,680],[298,338,341,345,357,358,361,402,405,409,421,422,425,597,598,601,602,612,616,661,662,665,666,676,680],[298,341,342,345,346,357,358,361,405,406,409,410,421,422,425,597,598,601,602,613,614,616,661,662,665,666,677,678,680],[322,341,345,357,361,404,408,416,578,597,601,613,617,660,664,672],[322,341,345,357,361,405,406,409,410,418,421,425,597,598,601,602,610,613,617,660,664,672],[325,326,328,405,406,408,421,422,424,597,598,600,613,614,616,656,672],[325,326,328,405,406,409,410,421,422,424,597,598,601,602,613,614,616,657,658,672],[325,326,329,330,401,402,417,418,596,600,612,616,660,664,676,680],[325,326,329,330,401,402,421,422,425,426,597,598,601,602,612,616,657,658,676,680],[325,326,345,346,360,405,406,409,410,421,422,424,597,598,601,602,613,614,616,657,658,672],[325,329,338,354,389,393,402,418,596,600,612,616,660,664,676,680],[325,329,338,354,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,660,664,676,680],[326,328,341,357,390,392,405,421,597,598,600,613,614,616,656,672],[326,328,341,357,405,406,408,421,422,424,597,598,600,613,614,616,656,672],[326,330,341,345,353,404,408,416,582,586,597,601,609,660,664,672],[326,330,341,345,357,361,386,405,409,417,596,600,612,616,660,664,672],[326,330,341,345,357,361,386,405,409,421,425,596,600,612,616,660,664,672],[326,330,341,345,357,361,386,405,409,421,425,597,598,601,602,613,614,617,618,660,664,672],[326,330,341,345,357,361,390,394,405,409,421,425,546,553,594,597,601,613,658,661,665,677],[326,330,341,345,357,361,390,394,405,409,421,425,546,594,597,601,613,617,658,661,665,677,681],[326,330,341,345,357,361,390,394,405,409,421,425,553,594,597,601,610,613,658,661,665,674,677],[326,330,341,345,357,361,390,394,405,409,421,425,594,597,601,610,613,617,658,661,665,674,677,681],[326,330,341,345,357,361,401,402,417,418,582,586,597,601,613,617,660,664,676,680],[326,330,341,345,357,361,401,402,417,418,596,600,612,616,660,664,676,680],[326,330,341,345,357,361,402,405,409,418,421,425,514,597,601,613,617,661,665,677,681],[326,330,341,345,357,361,404,408,416,582,586,597,601,613,617,660,664,672],[326,330,341,345,357,361,404,408,420,424,597,598,601,602,609,610,660,664,672],[326,330,341,345,357,361,405,406,409,410,417,418,597,598,601,602,613,614,617,618,660,664,672],[326,330,341,345,357,361,405,406,409,410,417,422,426,597,598,601,602,613,614,617,618,660,664,672],[326,330,341,345,357,361,405,406,409,410,418,421,425,597,598,601,602,613,614,617,618,660,664,672],[326,330,341,345,357,361,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,658,661,665,674,677,681],[326,330,341,345,357,361,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,660,664,672],[326,341,344,357,360,405,406,408,421,422,424,582,597,601,602,613,617,618,657,658,673,674],[328,341,342,357,358,392,405,406,421,422,597,598,600,613,614,616,656,672],[328,341,342,357,358,405,406,408,421,422,424,597,598,600,613,614,616,656,672],[329,330,341,342,357,358,393,394,405,406,421,422,534,550,597,600,613,616,661,664,677,680],[329,330,341,342,357,358,393,394,405,406,421,422,594,597,601,610,613,617,660,664,676,680],[329,330,341,342,357,358,401,402,417,418,596,600,612,616,660,664,676,680],[329,338,341,354,357,393,405,406,410,421,422,426,597,598,601,602,613,614,617,618,660,664,676,680],[329,338,341,354,357,404,408,420,424,585,594,597,610,613,660,664,676,680],[329,338,341,354,357,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,660,664,676,680],[330,341,342,345,357,358,361,394,405,406,409,421,422,425,597,598,601,602,613,614,617,618,661,662,664,677,678,680],[330,341,342,345,357,358,361,405,406,408,421,422,424,520,597,598,613,614,661,662,677,678],[330,341,342,345,357,358,361,405,406,408,421,422,424,586,597,598,601,613,614,617,661,662,664,677,678,680],[330,341,342,345,357,358,361,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,664,677,678,680],[337,338,353,354,390,394,405,409,421,425,597,598,600,613,614,616,646,648,661,677],[337,338,353,354,394,405,406,409,421,422,425,597,598,601,602,613,614,617,618,648,660,676],[337,338,353,354,401,402,417,418,596,600,612,616,660,664,676,680],[337,338,353,354,404,408,420,424,585,586,597,598,613,614,648,660,676],[337,338,353,354,404,408,420,424,586,597,598,601,613,614,617,648,660,676],[337,338,353,354,405,406,409,410,420,424,597,598,601,602,613,614,617,618,648,661,662,676],[337,338,353,354,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,648,660,676],[337,338,353,354,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,660,664,676,680],[337,338,356,360,401,402,420,424,552,597,598,601,602,612,661,662,665,666,676],[337,338,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,676,680],[338,341,345,354,357,361,389,393,402,418,596,600,612,616,660,664,676,680],[338,341,345,354,357,361,389,393,406,410,422,426,594,597,601,610,613,617,660,664,676,680],[338,341,345,354,357,361,390,394,405,409,421,425,594,597,601,610,613,617,660,664,676,680],[338,341,345,354,357,361,393,394,405,406,421,422,594,597,601,610,613,617,648,660,676],[338,341,345,354,357,361,393,394,405,406,421,422,594,597,601,610,613,617,660,664,676,680],[338,341,345,354,357,361,402,405,409,418,421,425,522,597,598,601,613,614,617,646,661,665,677,681],[338,341,345,354,357,361,402,405,409,418,421,425,537,597,598,602,612,616,661,662,666,676,680],[338,341,345,354,357,361,402,405,409,418,421,425,538,597,598,601,612,616,661,662,665,676,680],[338,341,345,354,357,361,402,405,409,418,421,425,552,597,598,601,602,612,661,662,665,666,676],[338,341,345,354,357,361,402,405,409,418,421,425,585,597,598,602,613,614,618,648,660,676],[338,341,345,354,357,361,402,405,409,418,421,425,586,597,598,601,613,614,617,648,660,676],[338,341,345,354,357,361,402,405,409,418,421,425,597,598,601,602,612,616,661,662,665,666,676,680],[338,341,345,354,357,361,404,408,420,424,585,594,597,610,613,648,660,676],[338,341,345,354,357,361,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,676,680],[338,341,345,356,360,402,405,409,420,424,537,594,597,612,616,658,661,676,680],[338,341,345,356,360,402,405,409,420,424,552,594,597,601,612,658,661,665,676],[338,341,345,356,360,402,405,409,420,424,594,597,601,612,616,640],[338,341,345,356,360,402,405,409,420,424,594,597,601,612,616,658,661,665,676,680],[338,341,345,356,360,402,405,409,420,424,594,597,601,613,614,617,618,642,645,649],[338,341,345,357,358,361,362,405,406,409,410,420,424,594,597,601,613,614,617,618,661,662,665,666,676,680],[338,341,345,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,676,680],[340,344,356,360,386,405,409,417,596,600,612,616,642,661,665,673],[340,344,356,360,386,405,409,421,425,596,600,612,616,642,661,665,677,681],[340,344,356,360,390,394,405,409,421,425,594,597,601,610,613,617,642,661,665,677,681],[340,344,356,360,390,394,405,409,421,425,597,598,601,602,613,614,617,618,642,657,673],[340,344,356,360,402,405,409,418,421,425,586,597,598,601,613,614,617,642,661,665,677,681],[340,344,356,360,402,405,409,418,421,425,597,598,601,602,613,614,617,618,642,649,661,677],[340,344,356,360,402,405,409,418,421,425,597,598,601,602,613,614,617,618,642,661,665,677,681],[340,344,356,360,404,408,416,514,597,601,613,617,661,665,677,681],[340,344,356,360,404,408,420,424,514,597,601,613,617,661,665,673],[340,344,356,360,404,408,420,424,514,597,601,613,617,661,665,677,681],[340,344,356,360,404,408,420,424,522,593,598,609,614,646,657,673],[340,344,356,360,404,408,420,424,522,593,598,609,614,657,662,673,678],[340,344,356,360,404,408,420,424,537,553,594,597,610,613,642,645],[340,344,356,360,404,408,420,424,537,553,594,597,610,613,642,661,677],[340,344,356,360,404,408,420,424,546,597,598,601,602,609,661,662,665,666,673],[340,344,356,360,404,408,420,424,582,586,597,601,613,617,642,657,673],[340,344,356,360,404,408,420,424,586,597,598,601,613,614,617,642,657,673],[340,344,356,360,404,408,420,424,594,597,601,610,613,617,642,649,661,677],[340,344,356,360,404,408,420,424,594,597,601,610,613,617,642,661,665,677,681],[340,344,356,360,404,408,420,424,596,600,612,616,660,664,676,680],[340,344,356,360,404,408,420,424,597,598,601,602,609,610,642,661,665,673],[340,344,356,360,404,408,420,424,597,598,601,602,610,613,617,642,661,665,677,681],[340,344,356,360,404,408,420,424,597,598,601,602,613,614,617,618,642,661,665,673],[340,344,356,360,404,408,420,424,597,598,601,602,613,614,617,618,642,661,665,677,681],[340,344,356,360,405,406,409,410,418,421,425,597,598,601,602,613,614,617,618,642,661,665,677,681],[340,344,356,360,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,642,661,665,673],[340,344,356,360,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,642,661,665,677,681],[341,342,344,352,405,406,408,416,597,598,600,608,661,662,664,672],[341,342,344,352,405,406,408,421,422,424,597,598,600,613,614,616,645,646,648],[341,342,344,357,358,360,389,390,392,597,598,600,608,661,662,664,672],[341,342,344,357,358,360,389,390,408,424,597,598,600,613,614,616,640],[341,342,344,357,358,360,390,392,405,421,597,598,600,613,614,616,640],[341,342,344,357,358,360,390,405,408,421,424,597,598,600,613,614,616,640],[341,342,344,357,358,360,390,405,408,421,424,597,598,600,613,614,616,646,661,664,677,680],[341,342,344,357,358,360,392,405,406,421,422,520,597,598,613,614,661,662,677,678],[341,342,344,357,358,360,392,405,406,421,422,534,550,597,600,613,616,648,661,677],[341,342,344,357,358,360,392,405,406,421,422,597,598,600,613,614,616,640],[341,342,344,357,358,360,392,405,406,421,422,597,598,600,613,614,616,648,661,662,677,678],[341,342,344,357,358,360,405,406,408,416,597,598,600,613,614,616,640],[341,342,344,357,358,360,405,406,408,416,597,598,600,613,614,616,645,646,648],[341,342,344,357,358,360,405,406,408,416,597,598,600,613,614,616,661,662,664,672],[341,342,344,357,358,360,405,406,408,421,422,424,520,597,598,613,614,646,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,520,597,598,613,614,661,662,677,678],[341,342,344,357,358,360,405,406,408,421,422,424,522,534,550,585,597,613,649,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,522,597,598,601,613,614,617,646,661,665,677,681],[341,342,344,357,358,360,405,406,408,421,422,424,522,597,598,601,613,614,617,661,662,665,677,678,681],[341,342,344,357,358,360,405,406,408,421,422,424,534,550,585,586,597,613,649,650,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,534,550,597,600,613,616,645,648],[341,342,344,357,358,360,405,406,408,421,422,424,534,550,597,600,613,616,648,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,537,553,582,586,597,613,646,650,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,640],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,645,646,648],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,645,646,664,680],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,646,648,661,677],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,646,661,664,677,680],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,648,661,662,677,678],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,661,662,664,672],[341,342,344,357,358,360,405,406,408,421,422,424,597,598,600,613,614,616,661,662,664,677,678,680],[341,342,345,346,352,405,406,409,410,416,533,534,537,538,608,672],[341,342,345,346,352,405,406,409,410,416,534,538,544,597,601,661,665],[341,342,345,346,352,405,406,409,410,416,534,538,597,601,608,661,665,672],[341,342,345,346,352,405,406,409,410,416,538,544,597,598,601,661,662,665],[341,342,345,346,352,405,406,409,410,416,538,597,598,601,608,661,662,665,672],[341,342,345,346,352,405,406,409,410,416,544,597,598,601,602,661,662,665,666],[341,342,345,346,352,405,406,409,410,416,597,598,601,602,608,640],[341,342,345,346,352,405,406,409,410,416,597,598,601,602,608,661,662,665,666,672],[341,342,345,346,353,354,404,408,416,597,598,601,602,609,610,660,664,672],[341,342,345,346,353,354,404,408,420,424,597,598,601,602,609,610,660,664,676,680],[341,342,345,346,353,354,405,406,409,410,417,418,534,550,597,600,613,616,661,664,677,680],[341,342,345,346,353,354,405,406,409,410,417,418,597,598,601,602,613,614,617,618,660,664,676,680],[341,342,345,346,353,354,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,660,664,676,680],[341,342,345,346,353,358,362,404,408,416,582,586,597,601,609,640],[341,342,345,346,353,358,362,404,408,416,582,586,597,601,609,660,664,672],[341,342,345,346,354,357,361,386,389,393,596,600,608,660,664,672],[341,342,345,346,354,357,361,386,405,409,421,425,597,598,601,602,610,613,617,660,664,672],[341,342,345,346,354,357,361,404,408,416,578,597,601,613,617,640],[341,342,345,346,354,357,361,404,408,416,578,597,601,613,617,642,661,665,677,681],[341,342,345,346,354,357,361,404,408,416,578,597,601,613,617,660,664,672],[341,342,345,346,354,357,361,404,408,416,597,598,601,602,610,613,617,640],[341,342,345,346,354,357,361,404,408,418,421,425,597,598,601,602,610,613,617,640],[341,342,345,346,354,357,361,405,406,409,410,418,421,425,597,598,601,602,610,613,617,660,664,672],[341,342,345,346,354,357,361,405,406,409,410,418,421,425,597,598,601,602,610,613,617,660,664,674,677,681],[341,342,345,346,356,360,401,402,416,584,597,598,612,657,658,672],[341,342,345,346,356,360,401,402,416,597,598,601,602,612,616,640],[341,342,345,346,356,360,402,405,409,416,597,598,601,602,612,616,658,661,665,672],[341,342,345,346,356,360,405,406,409,410,420,424,537,594,597,610,613,617,658,661,674,677,681],[341,342,345,346,356,360,405,406,409,410,420,424,544,594,597,601,658,661,665],[341,342,345,346,356,360,405,406,409,410,420,424,546,553,594,597,601,613,658,661,665,677],[341,342,345,346,356,360,405,406,409,410,420,424,546,594,597,601,613,617,658,661,665,677,681],[341,342,345,346,356,360,405,406,409,410,420,424,553,594,597,601,610,613,658,661,665,674,677],[341,342,345,346,357,358,360,384,597,598,601,602,613,614,616,640],[341,342,345,346,357,358,360,389,390,392,597,598,601,602,613,614,616,657,658,672],[341,342,345,346,357,358,360,389,390,409,410,424,597,598,601,602,613,614,616,657,658,672],[341,342,345,346,357,358,360,405,406,409,410,416,544,597,598,601,602,661,662,665,666],[341,342,345,346,357,358,360,405,406,409,410,416,597,598,601,602,613,614,616,640],[341,342,345,346,357,358,360,405,406,409,410,416,597,598,601,602,613,614,616,661,662,665,666,672],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,534,597,601,602,613,614,616,661,665,666,677,678,680],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,538,597,598,601,613,614,616,661,662,665,677,678,680],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,544,597,598,601,602,661,662,665,666],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,552,597,598,601,602,613,614,661,662,665,666,677,678],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,597,598,601,602,613,614,616,640],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,597,598,601,602,613,614,616,661,662,665,666,672],[341,342,345,346,357,358,360,405,406,409,410,421,422,424,597,598,601,602,613,614,616,661,662,665,666,677,678,680],[341,342,345,346,357,358,361,362,384,597,598,601,602,613,614,617,618,640],[341,342,345,346,357,358,361,362,386,389,393,596,600,612,616,660,664,672],[341,342,345,346,357,358,361,362,386,405,409,417,596,600,612,616,640],[341,342,345,346,357,358,361,362,386,405,409,417,596,600,612,616,660,664,672],[341,342,345,346,357,358,361,362,386,405,409,421,425,596,600,612,616,640],[341,342,345,346,357,358,361,362,386,405,409,421,425,596,600,612,616,642,661,665,677,681],[341,342,345,346,357,358,361,362,386,405,409,421,425,596,600,612,616,660,664,672],[341,342,345,346,357,358,361,362,389,390,393,394,593,594,609,610,660,664,676,680],[341,342,345,346,357,358,361,362,389,390,393,394,593,594,612,616,657,658,676,680],[341,342,345,346,357,358,361,362,389,393,402,418,596,600,612,616,640],[341,342,345,346,357,358,361,362,389,393,402,418,596,600,612,616,658,661,665,674,677,681],[341,342,345,346,357,358,361,362,390,394,405,409,421,425,594,597,601,610,613,617,640],[341,342,345,346,357,358,361,362,390,394,405,409,421,425,594,597,601,610,613,617,642,661,665,677,681],[341,342,345,346,357,358,361,362,390,394,405,409,421,425,594,597,601,610,613,617,658,661,665,674,677,681],[341,342,345,346,357,358,361,362,390,394,405,409,421,425,597,598,600,613,614,616,661,662,664,677,678,680],[341,342,345,346,357,358,361,362,390,394,405,409,421,425,597,598,601,602,609,610,660,664,672],[341,342,345,346,357,358,361,362,392,404,420,593,594,609,610,640],[341,342,345,346,357,358,361,362,401,402,417,418,596,600,612,616,640],[341,342,345,346,357,358,361,362,401,402,417,418,596,600,612,616,646,650,661,665,677,681],[341,342,345,346,357,358,361,362,401,402,417,418,596,600,612,616,650,661,662,665,677,678,681],[341,342,345,346,357,358,361,362,401,402,417,418,597,598,601,602,612,616,648,661,662,676],[341,342,345,346,357,358,361,362,401,402,421,422,425,426,597,598,601,602,612,616,640],[341,342,345,346,357,358,361,362,402,405,409,418,421,425,597,598,601,602,612,616,640],[341,342,345,346,357,358,361,362,404,408,416,581,582,585,586,660,664,672],[341,342,345,346,357,358,361,362,404,408,416,582,586,597,601,613,617,640],[341,342,345,346,357,358,361,362,404,408,416,582,586,597,601,613,617,642,661,665,673],[341,342,345,346,357,358,361,362,404,408,420,424,585,594,597,610,613,640],[341,342,345,346,357,358,361,362,404,408,420,424,597,598,601,602,609,610,640],[341,342,345,346,357,358,361,362,405,406,408,416,581,582,585,586,661,662,664,672],[341,342,345,346,357,358,361,362,405,406,408,421,422,424,586,597,598,601,613,614,617,640],[341,342,345,346,357,358,361,362,405,406,408,421,422,424,586,597,598,601,613,614,617,648,661,662,677,678],[341,342,345,346,357,358,361,362,405,406,409,410,416,597,598,601,602,613,614,617,618,640],[341,342,345,346,357,358,361,362,405,406,409,410,416,597,598,601,602,613,614,617,618,661,662,665,666,672],[341,342,345,346,357,358,361,362,405,406,409,410,420,424,594,597,601,613,614,617,618,640],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,424,512],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,424,597,598,601,602,613,614,617,618,640],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,424,597,598,601,602,613,614,617,618,661,662,665,666,672],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,424,597,598,601,602,613,614,617,618,661,662,665,666,677,678,680],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,425,426,512],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,640],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,672],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,677,678,680],[341,342,345,346,357,358,361,362,405,406,409,410,421,422,425,426,597,598,601,602,613,614,617,618,661,662,665,666,677,678,681,682]]

def tags0_0 : Array Nat := #[0x130eca8642000,0x130eca8642001]

theorem move0_0 (h : realizable 5 (hostAt hosts0 0).toFinset) :
    ∃ i < hosts1.size, realizable 4 (hostAt hosts1 i).toFinset :=
  descend hosts1 (hostAt hosts0 0) ⟨4,by decide⟩ 1 0x2 tags0_0 (by decide +kernel) h

theorem layer0 (h : ∃ i < hosts0.size, realizable 5 (hostAt hosts0 i).toFinset) :
    ∃ i < hosts1.size, realizable 4 (hostAt hosts1 i).toFinset := by
  obtain ⟨i,hi,h⟩ := h
  change i < 1 at hi
  interval_cases i

  · exact move0_0 h

def tags1_0 : Array Nat := #[0x0,0xed30a8642000]

theorem move1_0 (h : realizable 4 (hostAt hosts1 0).toFinset) :
    ∃ i < hosts2.size, realizable 3 (hostAt hosts2 i).toFinset :=
  descend hosts2 (hostAt hosts1 0) ⟨3,by decide⟩ 1 0x10 tags1_0 (by decide +kernel) h

def tags1_1 : Array Nat := #[0x130eca8642000,0x130eca8642001,0x112eca8642001,0x130eca8642002]

theorem move1_1 (h : realizable 4 (hostAt hosts1 1).toFinset) :
    ∃ i < hosts2.size, realizable 3 (hostAt hosts2 i).toFinset :=
  descend hosts2 (hostAt hosts1 1) ⟨3,by decide⟩ 2 0x3e4 tags1_1 (by decide +kernel) h

theorem layer1 (h : ∃ i < hosts1.size, realizable 4 (hostAt hosts1 i).toFinset) :
    ∃ i < hosts2.size, realizable 3 (hostAt hosts2 i).toFinset := by
  obtain ⟨i,hi,h⟩ := h
  change i < 2 at hi
  interval_cases i

  · exact move1_0 h

  · exact move1_1 h

def tags2_0 : Array Nat := #[0x0,0x130a8ec642002]

theorem move2_0 (h : realizable 3 (hostAt hosts2 0).toFinset) :
    ∃ i < hosts3.size, realizable 2 (hostAt hosts3 i).toFinset :=
  descend hosts3 (hostAt hosts2 0) ⟨2,by decide⟩ 1 0x1f000 tags2_0 (by decide +kernel) h

def tags2_1 : Array Nat := #[0x0,0x130eca8642003,0x130cea8642003,0x130eca8642005,0x112eca8642000,0x130a8ec642001,0x130a8ce642001,0xa930ec642004]

theorem move2_1 (h : realizable 3 (hostAt hosts2 1).toFinset) :
    ∃ i < hosts3.size, realizable 2 (hostAt hosts3 i).toFinset :=
  descend hosts3 (hostAt hosts2 1) ⟨2,by decide⟩ 3 0x7ffffac6db688 tags2_1 (by decide +kernel) h

def tags2_2 : Array Nat := #[0x130eca8642002,0x130eca8642004,0x130cea8642004,0x130eca8642007,0xed30a8642004,0x130eca8642006,0x130cea8642006,0xed12a8642004,0x112eca8642006,0x112cea8642006]

theorem move2_2 (h : realizable 3 (hostAt hosts2 2).toFinset) :
    ∃ i < hosts3.size, realizable 2 (hostAt hosts3 i).toFinset :=
  descend hosts3 (hostAt hosts2 2) ⟨2,by decide⟩ 4 0x33333398736543210 tags2_2 (by decide +kernel) h

theorem layer2 (h : ∃ i < hosts2.size, realizable 3 (hostAt hosts2 i).toFinset) :
    ∃ i < hosts3.size, realizable 2 (hostAt hosts3 i).toFinset := by
  obtain ⟨i,hi,h⟩ := h
  change i < 3 at hi
  interval_cases i

  · exact move2_0 h

  · exact move2_1 h

  · exact move2_2 h

def tags3_0 : Array Nat := #[0x0,0x13064eca82009]

theorem move3_0 (h : realizable 2 (hostAt hosts3 0).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 0) ⟨1,by decide⟩ 1 0x1ffff8888f0008000 tags3_0 (by decide +kernel) h

def tags3_1 : Array Nat := #[0x0,0xed3064a82000,0x130ec64a82002,0x130ec64a82004,0x130ec64a82006,0x130ce64a82002,0x130ce64a82004,0x130ce64a82006,0x112ec64a8200f,0x6530eca8200c,0x130ec648a2003,0x112ec64a8200e,0x13064eca82007,0x112ce64a8200e,0x13064cea82007]

theorem move3_1 (h : realizable 2 (hostAt hosts3 1).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 1) ⟨1,by decide⟩ 4 0x9999999999999999999889e8d9c8b9a8099997777444411119988765043201000 tags3_1 (by decide +kernel) h

def tags3_2 : Array Nat := #[0x0,0x130ec64a82010]

theorem move3_2 (h : realizable 2 (hostAt hosts3 2).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 2) ⟨1,by decide⟩ 1 0x1fffff000f000f000 tags3_2 (by decide +kernel) h

def tags3_3 : Array Nat := #[0x0,0x6530eca82011]

theorem move3_3 (h : realizable 2 (hostAt hosts3 3).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 3) ⟨1,by decide⟩ 1 0x1fffff80000000000 tags3_3 (by decide +kernel) h

def tags3_4 : Array Nat := #[0x0,0x130eca8642011,0x130ec8a642011,0x130eca8642016,0xcf30a8642009,0x130ec64a8200c,0x130ec648a200c,0x13064eca82015,0x130eca8642017,0x130ec64a82019,0x130ec648a2019,0x13064eca82013,0xed3064a82018,0x13064eca82012,0x13064ec8a2012,0x112eca8642017,0x112ec64a82019,0x112ec648a2019,0x11264eca82013,0xed1264a82018,0x11264eca82012,0x11264ec8a2012]

theorem move3_4 (h : realizable 2 (hostAt hosts3 4).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 4) ⟨1,by decide⟩ 5 0x739ce739ce739ce739ce739ce73d69394a529460f39ce73b9ac5ad6b5a92839ce7398a418c6318820 tags3_4 (by decide +kernel) h

def tags3_5 : Array Nat := #[0x0,0x130eca864201d,0x130eca864201a,0x130ec8a64201a,0x130cea864201a,0x130ce8a64201a,0x6530eca82000,0x6530ec8a2000,0x6530eca82016,0x6530a8ec2000,0x6530eca82001,0x6530ec8a2001,0x6530a8ce2000,0x6530cea82001,0x6530ce8a2001]

theorem move3_5 (h : realizable 2 (hostAt hosts3 5).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 5) ⟨1,by decide⟩ 4 0x8888888888888888888888edc8ba9876011111111111111111111154013201000 tags3_5 (by decide +kernel) h

def tags3_6 : Array Nat := #[0x0,0x130eca8642014,0x130ec8a642014,0x130eca864201e,0x130a8ec642013,0x130eca864201b,0x130ec8a64201b,0xcf30a8642018,0xed3064a8200b,0xed30648a200b,0x6530eca8201c,0xeca930642013,0xed30a864201b,0xed308a64201b,0xcea865302005,0xec6530a82008,0xec65308a2008,0x112eca8642018,0x130ec64a8200b,0x130ec648a200b,0x112a864ec2005,0x13064eca82008,0x13064ec8a2008,0x112cea864200a,0x130ec64a8200d,0x130ec648a200d]

theorem move3_6 (h : realizable 2 (hostAt hosts3 6).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 6) ⟨1,by decide⟩ 5 0xa5294a5294a5294a5294a5294a5671755ab454e515294a541ee18c631b58b5294a52507198a418820 tags3_6 (by decide +kernel) h

def tags3_7 : Array Nat := #[0x130eca8642010,0x130eca8642015,0x130ec8a642015,0x130eca8642020,0x130a8ec642015,0x130eca864201c,0x130ec8a64201c,0x130a8ce642015,0x130cea864201c,0x130ce8a64201c,0xeca930642015,0xed30a864201c,0xed308a64201c,0xa930ec64201c,0x130eca864201f,0x130ec8a64201f,0xa930ce64201c,0x130cea864201f,0x130ce8a64201f,0xeca912642015,0xed12a864201c,0xed128a64201c,0xa912ec64201c,0x112eca864201f,0x112ec8a64201f,0xa912ce64201c,0x112cea864201f,0x112ce8a64201f]

theorem move3_7 (h : realizable 2 (hostAt hosts3 7).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset :=
  descend hosts4 (hostAt hosts3 7) ⟨1,by decide⟩ 5 0x318c6318c6318c6318c6318c631ef591e2f61d69318c631ca301bdcd1b16a18c631a507198a418820 tags3_7 (by decide +kernel) h

theorem layer3 (h : ∃ i < hosts3.size, realizable 2 (hostAt hosts3 i).toFinset) :
    ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset := by
  obtain ⟨i,hi,h⟩ := h
  change i < 8 at hi
  interval_cases i

  · exact move3_0 h

  · exact move3_1 h

  · exact move3_2 h

  · exact move3_3 h

  · exact move3_4 h

  · exact move3_5 h

  · exact move3_6 h

  · exact move3_7 h

def tags4_0 : Array Nat := #[0x0,0x2130eca8647b]

theorem move4_0 (h : realizable 1 (hostAt hosts4 0).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 0) ⟨0,by decide⟩ 1 0x1fffffcccfffffcccfffff88800000000fffff88800000000fffff88800000000 tags4_0 (by decide +kernel) h

def tags4_1 : Array Nat := #[0x0,0x130ec20a86435,0x2130eca86498,0x13020eca86401,0x13020ec46a823,0x13020ec8a6423,0x13020ec8a4610,0x13020eca8643b,0x130ec20a86403,0x13020ec64a83a,0x13020eca8643a,0x13020eca86439,0x13020eca86400,0x2130ec64a855,0x13020ec64a800,0x2130ec64a858,0x2130eca86455,0x2130eca86458,0x2130eca86456,0x11220eca8643b,0x112ec20a86403,0x11220ec64a83a,0x11220eca8643a,0x11220eca86439,0x11220eca86400,0x2112ec64a855,0x11220ec64a800,0x2112ec64a858,0x2112eca86455,0x2112eca86458,0x2112eca86456]

theorem move4_1 (h : realizable 1 (hostAt hosts4 1).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 1) ⟨0,by decide⟩ 5 0x210842108421084210842108421084210863108631084210842108421084210842108421086310863108421084210842108421084217bbc16c7a167009ce739ce739ce739ce739ce739dec09d68098000108421084210842108421084214a3013c6e1358039ce739ce739ce739ce739ce73ad403a500380001084210842108421084210842118a011060100000842108421084210842108421080000800008000 tags4_1 (by decide +kernel) h

def tags4_2 : Array Nat := #[0x0,0x2130eca864b2]

theorem move4_2 (h : realizable 1 (hostAt hosts4 2).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 2) ⟨0,by decide⟩ 1 0x1ffffffffffffffffccccc888c888c888fffff00000000000ccccc00000000000 tags4_2 (by decide +kernel) h

def tags4_3 : Array Nat := #[0x0,0x13020eca864b9]

theorem move4_3 (h : realizable 1 (hostAt hosts4 3).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 3) ⟨0,by decide⟩ 1 0x1fffffffffffffffffaaac888c888c888fffff000f000f000faaac000c000c000 tags4_3 (by decide +kernel) h

def tags4_4 : Array Nat := #[0x0,0x2130eca864bd]

theorem move4_4 (h : realizable 1 (hostAt hosts4 4).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 4) ⟨0,by decide⟩ 1 0x1fffffffffffffffffcccf888a888a888fffff00000000000fcccf00000000000 tags4_4 (by decide +kernel) h

def tags4_5 : Array Nat := #[0x0,0x130eca8642084,0x4730eca820b6,0x13020eca864c4,0x130ec64a8209d,0x130eca8206473,0x1306420eca8c5,0x130ec648a209d,0x130ec8a206473,0x1306420ec8ac5,0xed30a8206412,0x112a864ec209d,0x112a8ec206473,0x1126420a8ecc5,0x13064eca82156,0x130eca8206474,0x1302064eca899,0x13064ec8a2156,0x130ec8a206474,0x1302064ec8a99,0x13020eca864c2,0x112a864ce209d,0x112a8ce206473,0x1126420a8cec5,0x13064cea82156,0x130cea8206474,0x1302064cea899,0x13064ce8a2156,0x130ce8a206474,0x1302064ce8a99,0x13020cea864c2,0xa912ec206412,0x11220a8ec64c2,0x112208aec64c2,0xed3064a82046,0x13064ec20a969,0xed3064a82047,0x13020ec64a8d2,0xed30648a2047,0x13020ec648ad2,0x13020a864ed26,0x13020a864ed29,0x13020eca864c1,0x13020eca864c3,0x13020ec8a64c1,0x13020ec8a64c3,0x13020a864cf26,0x13020a864cf29,0x13020cea864c1,0x13020cea864c3,0x13020ce8a64c1,0x13020ce8a64c3,0xa91264ec2046,0x11264a820ed69,0x11220ec64a926,0x11220ec64a929,0x11220ec648b26,0x11220ec648b29,0xa91264ec2047,0x11220a864ecd2,0x11220a8ec64c1,0x11220a8ec64c3,0x112208aec64c1,0x112208aec64c3,0xa91264ce2047,0x11220a864ced2,0x11220a8ce64c1,0x11220a8ce64c3,0x112208ace64c1,0x112208ace64c3]

theorem move4_5 (h : realizable 1 (hostAt hosts4 5).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 5) ⟨0,by decide⟩ 7 0x3060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060d0a1060d020060cf9f060c18307150c4070d0420704fc0060c18306fd0be06f503c06ecfba060c18306e50b806dd03606d4fb4060c183060c183060c183060c183060cf1e06ccf3206c4f3006bcf2e060ca1406b4a2c06aca2a06a4a28060c50a069c5260694524068c522060c183060d0a1060d020060cf9f060cf1e0674e1b0668c98065cb15060ca14064c911064078e063460b060c50a062440706182840608080 tags4_5 (by decide +kernel) h

def tags4_6 : Array Nat := #[0x0,0xed30a8206415,0xed308a206415,0x130eca820647a,0x130eca8206476,0x130eca8206479,0x130ec8a206476,0x130ec8a206479,0xcea821306420,0x130ec20a86464,0x20ed30a8642c,0x20ed30a8644f,0x130ec208a6464,0x20ed308a642c,0x20ed308a644f,0x2130eca864c8,0x13020a8ec6469,0x2130eca86402,0x2130ec8a6402,0x2130eca8642d,0x2130ec8a642d,0x2130a8ec642e,0x13020eca86466,0x2130eca86452,0x13020ec8a6466,0x2130ec8a6452,0x2130eca8640e,0x13020eca86465,0x2130eca86432,0x13020ec8a6465,0x2130ec8a6432]

theorem move4_6 (h : realizable 1 (hostAt hosts4 6).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 6) ⟨0,by decide⟩ 5 0xf7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7bdef7be527be317be107bdef7fa5d7f23b7ea007bdef7e6587de367d6007bdef7d2407ce20782007bdef7bdef7bdef7bdef7bdef739ce5ad6b4210818c6318c6318c6318c6318c631084208421000007bdef7be527be317be107bdef735805a9204000018c6319cc0194801800018c63100000800000000 tags4_6 (by decide +kernel) h

def tags4_7 : Array Nat := #[0x0,0xed3020a8642e,0xed308a20640e,0xed1220a8645b,0x2130eca864d6,0xa930ec206414,0x130ec20a8648b,0x130ec20a84667,0x130ec20a8648c,0x130ec8a20646c,0x130ec208a646f,0x130ec208a6470,0x112ec20a86508,0xa930ce206414,0x130ce20a8648b,0x130ce20a84667,0x130ce20a8648c,0x130ce8a20646c,0x130ce208a646f,0x130ce208a6470,0x112ce20a86508,0x112ec20a84706,0x130ec208a646d,0x112ec20a84705,0x6512ec20a804,0x112ec20a86507,0x13020eca8649f,0x112ce20a84705,0x6512ce20a804,0x112ce20a86507,0x13020cea8649f]

theorem move4_7 (h : realizable 1 (hostAt hosts4 7).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 7) ⟨0,by decide⟩ 5 0x421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108425495254952129427a9d2569c26e802118c269992559825d802106325860254602006021084210842108421084210849ce73842106b5ad210845ad6b42108294a52108410842084210000021084210842549525495212949ca2083dc0680002118c5a92041cc02800021063100000800000000 tags4_7 (by decide +kernel) h

def tags4_8 : Array Nat := #[0x0,0x130eca86420aa,0xed30a8462048,0xed3020a86436,0x130ec64a820a9,0x130eca86420ac,0xed304620a81a,0x8b30ec6420d4,0x130a8ec2064e8,0x130a8ec2046e7,0x2130eca864da,0x130a864ec2122,0x130a8ec206545,0x130a8ec462157,0x130ec20a86497,0x130ec6420a89c,0x130ec20a86468,0x130ec2064a893,0xa93020ec64d3,0x13020a8ec649a,0x13020a8ec648d,0x130a864ce2122,0x130a8ce206545,0x130a8ce462157,0x130ce20a86497,0x130ce6420a89c,0x130ce20a86468,0x130ce2064a893,0xa93020ce64d3,0x13020a8ce649a,0x13020a8ce648d,0x112ec20a86528,0xeca93064205a,0xed30a820644b,0xed30a8462049,0xa8ec213064d2,0xec2130a86438,0xec2130a84630,0x130a8ec206571,0x130ec20a86496,0x130ec20a86495,0x20a930ec6451,0x2130eca86460,0x2130eca8645e,0x130a8ce206571,0x130ce20a86496,0x130ce20a86495,0x20a930ce6451,0x2130cea86460,0x2130cea8645e,0xed12a8642062,0x112eca8206553,0x112ec20a8472c,0x112ec6420a8c2,0x130ec2046a87c,0xa912ec206574,0x13020eca8647d,0x13020eca8646e,0x112a8ec642176,0x112ec20a86527,0x13020ec64a89e,0x112ec2064a8eb,0x13020ec64a8a4,0x13020a8ec6488,0x13020eca864a5,0x13020eca864a0,0x112a8ce642176,0x112ce20a86527,0x13020ce64a89e,0x112ce2064a8eb,0x13020ce64a8a4,0x13020a8ce6488,0x13020cea864a5,0x13020cea864a0]

theorem move4_8 (h : realizable 1 (hostAt hosts4 8).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 8) ⟨0,by decide⟩ 7 0xa142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a1428f9f1428f9f142850a15264471518fc515121c2142850a150603f14f8fbd14f1dba142850a14e5c3714d8fb514d19b2142850a142850a142850a142850a142850a14c582f3060c1830b96ac142850a14ad5291c3870e1ca13a6142850a1495223060c18306890a0142850a142850a1428f9f1428f9f142850a1478e9c306cd19305cb15142850a14509921c4480f1c3460b142850a142440706182840608080 tags4_8 (by decide +kernel) h

def tags4_9 : Array Nat := #[0x0,0x130ec20a864de]

theorem move4_9 (h : realizable 1 (hostAt hosts4 9).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 9) ⟨0,by decide⟩ 1 0x1ffffffffffffffffffff888888888888fffff000f000f000ffff800080008000 tags4_9 (by decide +kernel) h

def tags4_10 : Array Nat := #[0x0,0x130eca86420b4,0x130eca84620b4,0xa930ec64200a,0x112ce64a820b4,0x130eca86420b5,0x130eca84620b5,0x130ec20a864e2,0x112ce648a20b4,0x130ec8a6420b5,0x130ec8a4620b5,0x130ec208a64e2,0x6512cea8200a,0x112ce2064a8e2,0x112ce2046a8e2,0x130ec20a864e3,0xa930ec642008,0xa930ec642009,0xa930ec462009,0x130ec2064a8fe,0x130ec20a864dd,0x130ec20a846dd,0x130ec20648afe,0x130ec208a64dd,0x130ec208a46dd,0x6512cea82008,0x112ce20a864fe,0x112ce20a846fe,0x6512cea82009,0x112ce2064a8dd,0x112ce2046a8dd,0x6512ce8a2009,0x112ce20648add,0x112ce20468add,0xa8ed30642008,0xa8ed30642009,0xa8ed30462009,0xed302064a8fe,0xed3020a864dd,0xed3020a846dd,0xed3020648afe,0xed30208a64dd,0xed30208a46dd,0x130cea8642169,0x130ce20a86574,0x130ce20a84774,0xcf302064a974,0x130ce20a86575,0x130ce20a84775,0xcf3020648b74,0x130ce208a6575,0x130ce208a4775,0x64cf12a82008,0xcf1220a864fe,0xcf1220a846fe,0x64cf12a82009,0xcf122064a8dd,0xcf122046a8dd,0x64cf128a2009,0xcf1220648add,0xcf1220468add,0xed12a8642169,0xed1220a86574,0xed1220a84774,0x112ec2064a974,0xed1220a86575,0xed1220a84775,0x112ec20648b74,0xed12208a6575,0xed12208a4775]

theorem move4_10 (h : realizable 1 (hostAt hosts4 10).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 10) ⟨0,by decide⟩ 7 0xf1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1e3868c1e3868c1e3868c1e3868c1e3c78f1f162431f0a0c01efdf3d1e3868c1ef1dba1ee5c371ed9ab41e3c78f1e3c78f1e3c78f1e3c78f1e3c78f1ecd9311ec17ae1eb562b1e3c78f162c58b0e1c387060c1831e3c78f16a94a80e9d32506911a21e3c78f1e3c78f1e3c78f1e3c78f1e3868c1e8501f1e78e9c1e6cd191e3c78f1660b960e54a1306488901e3868c16284880e182840608080 tags4_10 (by decide +kernel) h

def tags4_11 : Array Nat := #[0x0,0x130eca86420d0,0xa930ec46200b,0xa930ec206417,0x112ec64a82118,0x112eca8206547,0x130ec6420a8f8,0x13020eca864ee,0x112ec648a2118,0x112ec8a206547,0x130ec64208af8,0x13020ec8a64ee,0xed12a8206567,0x13020eca864f1,0x130a8ec642087,0x130a8ec206477,0xa930ec642027,0x112eca820657b,0x130eca82064c0,0x13020eca864ae,0x112ec8a20657b,0x130ec8a2064c0,0x13020ec8a64ae,0x11220eca86553,0x112cea86420df,0xcf12a82064fd,0xcf1246a820b7,0x112ce2064a8dc,0xcf1220a864ff,0x130ec2064a8cf,0x112ce20648adc,0xcf12208a64ff,0x130ec20648acf,0xcf1220a86501,0xa8ed30642029,0xa930ec206413,0xa930ec642028,0xed3020a864e9,0x130ec20a864f0,0x130ec20a864ef,0xed30208a64e9,0x130ec208a64f0,0x130ec208a64ef,0xed30a82064c5,0xed3020a864e8,0xed3020a864e7,0xed3020a864ea,0x13020eca864ed,0x13020eca864ec,0xed30208a64ea,0x13020ec8a64ed,0x13020ec8a64ec,0xed1264a82179,0x112ec46a8216a,0xed1264a8217e,0x11220ec64a93f,0xed12648a217e,0x11220ec648b3f,0x112a820ec6526,0x11220a8ec652c,0x11220eca86552,0x11220eca86554,0x11220ec8a6552,0x11220ec8a6554,0xcf12a82064fe,0xed1220a8656c,0xcf1220a86500,0x11220eca86550,0xcf12208a6500,0x11220ec8a6550]

theorem move4_11 (h : realizable 1 (hostAt hosts4 11).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 11) ⟨0,by decide⟩ 7 0xd1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a350a11b150c41b0d0c21b050c01a34b971afcbbe1af4bbc1aecbba1a3460c1ae46381adc6361ad46341a3468d1a3468d1a3468d1a3468d1a3468d1acd9311ac17ae1ab562b1a3468d162c58b0e1c387060c1831a3468d16a94a80e9d32506911a21a3468d1a3468d1a3468d1a3468d1a350a11a80f9e1a74e1b1a68c981a34b971658a940e4c911064078e1a3460c16284880e182840608080 tags4_11 (by decide +kernel) h

def tags4_12 : Array Nat := #[0x0,0x130a8ec20647b,0x130eca82064b2,0x130eca82064bd,0x130eca82064c8,0x130ec8a2064b2,0x130ec8a2064bd,0x130ec8a2064c8,0x130cea82064fc,0x13020eca864f7,0xed30a82046b9,0x130cea82064fb,0x130ec20a864d6,0x130ce8a2064fb,0x130ec208a64d6,0xeca930206475,0xa8ed30206411,0xa930ec206418,0xed30a82064be,0xed30a82064bf,0x130ec20a864f2,0x13020eca864f5,0xed308a2064be,0xed308a2064bf,0x130ec208a64f2,0x13020ec8a64f5,0xcf3020a8650d,0xcf30a820650a,0xed3020a864e6,0xcf3020a8650c,0x13020eca864f4,0xcf30208a650c,0x13020ec8a64f4,0xeca912206475,0xa8ed12206411,0xa912ec206418,0xed12a82064be,0xed12a82064bf,0x112ec20a864f2,0x11220eca864f5,0xed128a2064be,0xed128a2064bf,0x112ec208a64f2,0x11220ec8a64f5,0xcf1220a8650d,0xcf12a820650a,0xed1220a864e6,0xcf1220a8650c,0x11220eca864f4,0xcf12208a650c,0x11220ec8a64f4]

theorem move4_12 (h : realizable 1 (hostAt hosts4 12).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 12) ⟨0,by decide⟩ 6 0x9249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249249b2c272b31270b2f26eb2d249249aebaeb9e79e78e38e3249b2caeaa689e69648e284024924924924924924924924924969a26069f25e69d25c69b24924965965955555545145124969a6585d65544d24503c024924924924924924924924924920824e20d24c20b24a2002492491c71c71041040410412492081c6140103080040000 tags4_12 (by decide +kernel) h

def tags4_13 : Array Nat := #[0x0,0x130eca86420d1,0xa930ec46200c,0xa930ec20641f,0x130ec64a82117,0x130eca82064b3,0x130eca84620b8,0x130eca82064ce,0x130ec648a2117,0x130ec8a2064b3,0x130ec8a4620b8,0x130ec8a2064ce,0x112cea8206515,0x2130eca864f9,0xa930ec64202b,0xa930ec20641b,0xa930ec46200d,0x130eca82064ca,0x130eca82064cc,0x130eca82064cb,0x130ec8a2064ca,0x130ec8a2064cc,0x130ec8a2064cb,0x112a8ce6420e4,0x112cea8206501,0x130cea820476c,0x112cea86420e1,0x112cea8206513,0xed3020a864d5,0x112ce8a6420e1,0x112ce8a206513,0xed30208a64d5,0xa8ed3064202b,0xa8ed3020641b,0xa8ed3046200d,0xed30a82064ca,0xed30a82064cc,0xed30a82064cb,0xed308a2064ca,0xed308a2064cc,0xed308a2064cb,0xcea821306529,0xeca82130647d,0xeca82130466e,0xec2130a864ad,0xec2130a864b0,0xec2130a864af,0xec21308a64ad,0xec21308a64b0,0xec21308a64af,0xcea9126420e4,0xcf12a8206501,0xed12a820476c,0xcf12a86420e1,0xcf12a8206513,0x130ec20a864d5,0xcf128a6420e1,0xcf128a206513,0x130ec208a64d5,0x112a820ec6529,0x130a820ec647d,0x130a820ec466e,0x13020eca864ad,0x13020eca864b0,0x13020eca864af,0x13020ec8a64ad,0x13020ec8a64b0,0x13020ec8a64af,0x112cea86420e2,0x130eca82046ba,0x112cea8206514,0x130ec20a864d7,0x112ce8a206514,0x130ec208a64d7]

theorem move4_13 (h : realizable 1 (hostAt hosts4 13).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 13) ⟨0,by decide⟩ 7 0xd1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3468d1a3460c1b246481b1c6461b146441a3468d1b0e1411b01fbe1af5e3b1a3460c1ae9cb81addb351ad19b21a3468d1a3468d1a3468d1a3468d1a3468d1ac582f1ab96ac1aad5291a3468d162c58b0e1c387060c1831a3468d16a13a60e9522306890a01a3468d1a3468d1a3468d1a3468d1a3460c1a7cf1d1a70d9a1a64c171a3468d1658a940e4c911064078e1a3460c16284880e182840608080 tags4_13 (by decide +kernel) h

def tags4_14 : Array Nat := #[0x0,0x2130eca864fb]

theorem move4_14 (h : realizable 1 (hostAt hosts4 14).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 14) ⟨0,by decide⟩ 1 0x1fffffffffffffffffffff000f000f000ccccc88888888888ccccc00080008000 tags4_14 (by decide +kernel) h

def tags4_15 : Array Nat := #[0x0,0x112ec20a86469,0x112ec208a6469,0x130eca8206504,0x2130eca864fc,0x112a820ec6469,0x130eca8206502,0x13020eca864a7,0x13020eca864a8,0x130ec8a206502,0x13020ec8a64a7,0x13020ec8a64a8,0x112a820ce6469,0x130cea8206502,0x13020cea864a7,0x13020cea864a8,0x130ce8a206502,0x13020ce8a64a7,0x13020ce8a64a8,0x2130eca8645b,0x2130ec8a645b,0x2130a8ec645b,0x130eca8206503,0x2130eca86463,0x130ec8a206503,0x2130ec8a6463,0x2130a8ce645b,0x130cea8206503,0x2130cea86463,0x130ce8a206503,0x2130ce8a6463]

theorem move4_15 (h : realizable 1 (hostAt hosts4 15).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 15) ⟨0,by decide⟩ 5 0x421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108494a527bdef6318c210845ad6b42108294a52108410842084210000021063210632106321063210632787d2707b26860210632647825c7625460210632506024c60200602106321063210632106321063946007b9a060000210635a92041cc02800021063100000800000000 tags4_15 (by decide +kernel) h

def tags4_16 : Array Nat := #[0x0,0x130eca820650e]

theorem move4_16 (h : realizable 1 (hostAt hosts4 16).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 16) ⟨0,by decide⟩ 1 0x1fffffffffffffffffffff000f000f000fffff000f000f000fffff000f000f000 tags4_16 (by decide +kernel) h

def tags4_17 : Array Nat := #[0x0,0x13020eca86516]

theorem move4_17 (h : realizable 1 (hostAt hosts4 17).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 17) ⟨0,by decide⟩ 1 0x1fffffffffffffffffffff80000000000fffff80000000000fffff80000000000 tags4_17 (by decide +kernel) h

def tags4_18 : Array Nat := #[0x0,0x130eca8206537,0x8b30ec20650d,0xa930ec2046e6,0x2130eca8651c,0x130a8ec64214d,0x130a8ec206548,0x130a8ec206543,0x130ec20a8651e,0x8b30ec20650f,0x8b30ec206510,0x13020a8ec648e,0x130a8ce64214d,0x130a8ce206548,0x130a8ce206543,0x130ce20a8651e,0x8b30ce20650f,0x8b30ce206510,0x13020a8ce648e,0x8b30ec206512,0xeca930642050,0xeca930206445,0xeca93020464a,0xed3020a86457,0x8aed30206509,0xec20a930462f,0xa930ec206565,0xa930ec206568,0x130ec20a8652a,0x130ec20a8652b,0x8b30ec206511,0x2130eca8645f,0xa930ce206565,0xa930ce206568,0x130ce20a8652a,0x130ce20a8652b,0x8b30ce206511,0x2130cea8645f,0xeca912206419,0xed12a820641c,0xed12a820460f,0xed1220a86421,0xa912ec2064c6,0x112ec20a8647e,0x112ec20a84671,0x112a8ec2064c9,0x112ec20a86480,0x112ec20a8647f,0x112ec20a86481,0x13020a8ec6489,0x13020eca864a6,0x13020eca864a1,0x112a8ce2064c9,0x112ce20a86480,0x112ce20a8647f,0x112ce20a86481,0x13020a8ce6489,0x13020cea864a6,0x13020cea864a1]

theorem move4_18 (h : realizable 1 (hostAt hosts4 18).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 18) ⟨0,by decide⟩ 6 0x410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410413ae78df7df7df6d74104104133cb1c30c30c2fbad10410412caeaa69a69a689e61041041044d31041041044d31041041254e48e38e38e286010410411f4de75d75d75c6da1041041194d85d75d75d65541041041044d31041041044d31041041124503cf3cf3ce34c10410410b289208208207185104104103080041041040000 tags4_18 (by decide +kernel) h

def tags4_19 : Array Nat := #[0x0,0x130eca864213a,0x2130a8ec6418,0x2130a8ec4618,0x2130eca86520,0x130a8ec64214e,0x130a8ec206549,0x130a8ec204749,0x130ec20a8651d,0x2130a8ec6429,0x2130a8ec643c,0x2130a8ec463c,0x130a8ce64214e,0x130a8ce206549,0x130a8ce204749,0x130ce20a8651d,0x2130a8ce6429,0x2130a8ce643c,0x2130a8ce463c,0x130ec20a86525,0x130a8ec642173,0x130eca8206551,0x130eca8204751,0x20a930ec6446,0x2130eca86457,0x2130eca84657,0x130a8ec20657d,0x130ec20a86524,0x130ec20a84724,0x2130a8ec645a,0x2130eca86461,0x2130eca84661,0x130a8ce20657d,0x130ce20a86524,0x130ce20a84724,0x2130a8ce645a,0x2130cea86461,0x2130cea84661,0x112ec20a86482,0x112ec20a86483,0x112ec20a84683,0x112ec20a86484,0x2130a8ec6408,0x2130eca86421,0x2130eca84621,0x13020a8ec6487,0x13020eca864a2,0x13020eca846a2,0x13020eca864a9,0x2130a8ec642b,0x2130eca8644d,0x2130eca8464d,0x13020a8ce6487,0x13020cea864a2,0x13020cea846a2,0x13020cea864a9,0x2130a8ce642b,0x2130cea8644d,0x2130cea8464d]

theorem move4_19 (h : realizable 1 (hostAt hosts4 19).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 19) ⟨0,by decide⟩ 6 0x410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410410413ae78df7df7df6d74104104133cb1c30c30c2fbad10410412caeaa69a69a689e61041041041044d34d34d34d31041041259234d34d34e286010410411f79d4d34d34dc6da1041041196174d34d34d65541041041041044d34d34d34d31041041124503cf3cf3ce34c10410410b289208208207185104104103080041041040000 tags4_19 (by decide +kernel) h

def tags4_20 : Array Nat := #[0x0,0x130eca864213b,0x130eca82064f6,0x130eca82046f6,0x130ec20a8652d,0x130eca820654e,0x130ec20a8651a,0x130ec20a8471a,0x130ec20a8651f,0x130ec20a86519,0x130ec20a8651b,0x130ec20a8471b,0xed3020a864bb,0xed3020a846bb,0xed3020a864d0,0x20ed30a8640b,0x20ed30a86422,0x20ed30a84622,0x2130eca86523,0xed30a820654e,0xed3020a8651a,0xed3020a8471a,0xed3020a8651f,0xed3020a86519,0xed3020a8651b,0xed3020a8471b,0xec2130a8649d,0xec2130a864a3,0xec2130a846a3,0xec2130a864aa,0x20ed30a86448,0x20ed30a8644e,0x20ed30a8464e,0x130ec20a864bb,0x130ec20a846bb,0x130ec20a864d0,0x2130eca8640b,0x2130eca86422,0x2130eca84622,0x13020eca8649d,0x13020eca864a3,0x13020eca846a3,0x13020eca864aa,0x2130eca86448,0x2130eca8644e,0x2130eca8464e,0x130ec20a864b4,0x130ec20a864bc,0x130ec20a846bc,0x130ec20a864d1,0x2130eca8640c,0x2130eca86425,0x2130eca84625]

theorem move4_20 (h : realizable 1 (hostAt hosts4 20).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 20) ⟨0,by decide⟩ 6 0x124924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924924b4cf2c71c71c70bee4924924adb2baaaaaaaa9a274924924a69648e38e38e28404924924924924924924924924924924a07de75d75d75c6da10410410410410410410410410410411961759659659551349249249249249249249249249249249140f38e38e38d30010410410b289208208207185104104103080041041040000 tags4_20 (by decide +kernel) h

def tags4_21 : Array Nat := #[0x0,0x130eca8642116,0x130eca8462116,0x130eca864213c,0x8b30ec6420de,0x130eca82064f7,0x130eca82046f7,0x130ec20a86534,0x130eca864213d,0x130eca820654f,0x130eca820474f,0x130ec20a86520,0x130a8ec20653e,0x130ec20a8651c,0x130ec20a8471c,0x130cea864213d,0x130cea820654f,0x130cea820474f,0x130ce20a86520,0x130a8ce20653e,0x130ce20a8651c,0x130ce20a8471c,0xed30a864213d,0xed30a820654f,0xed30a820474f,0xed3020a86520,0xeca93020653e,0xed3020a8651c,0xed3020a8471c,0x130ec20a8652e,0x130ec20a86530,0x130ec20a84730,0x130ec20a86532,0x130ec20a8652f,0x130ec20a86531,0x130ec20a84731,0x130ce20a8652e,0x130ce20a86530,0x130ce20a84730,0x130ce20a86532,0x130ce20a8652f,0x130ce20a86531,0x130ce20a84731,0xed12a864213d,0xed12a820654f,0xed12a820474f,0xed1220a86520,0xeca91220653e,0xed1220a8651c,0xed1220a8471c,0x112ec20a8652e,0x112ec20a86530,0x112ec20a84730,0x112ec20a86532,0x112ec20a8652f,0x112ec20a86531,0x112ec20a84731,0x112ce20a8652e,0x112ce20a86530,0x112ce20a84730,0x112ce20a86532,0x112ce20a8652f,0x112ce20a86531,0x112ce20a84731]

theorem move4_21 (h : realizable 1 (hostAt hosts4 21).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 21) ⟨0,by decide⟩ 6 0x71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71fffbdf3cf3cf3beb91c71c71f8df6d75d75d74cf21c71c71f1c2fbaebaebadb2b1c71c71c71c71c71c71c71c71c71c71eaa689e79e79e69641c71c71e38a182082081f79d1c71c71dc6da6596596585d61c71c71c71c71c71c71c71c71c71c71d551349249249140f1c71c71ce34c2cb2cb2ca2481c71c71c61440c30c30c2040 tags4_21 (by decide +kernel) h

def tags4_22 : Array Nat := #[0x0,0x130eca8642162,0x130eca8642155,0x130eca8462155,0x130ec8a642155,0x130ec8a462155,0x13020eca8647b,0x13020eca8467b,0x13020eca8653c,0x13020ec64a87b,0x13020eca86498,0x13020eca84698,0x13020ec648a7b,0x13020ec8a6498,0x13020ec8a4698,0x13020eca86536,0x13020eca84736,0x13020eca8653a,0x13020ec64a936,0x13020eca86538,0x13020eca84738,0x13020ec648b36,0x13020ec8a6538,0x13020ec8a4738,0x13020eca86535,0x13020eca86537,0x13020eca84737,0x13020ec64a937,0x13020eca86539,0x13020eca84739,0x13020ec648b37,0x13020ec8a6539,0x13020ec8a4739,0x11220eca86536,0x11220eca84736,0x11220eca8653a,0x11220ec64a936,0x11220eca86538,0x11220eca84738,0x11220ec648b36,0x11220ec8a6538,0x11220ec8a4738,0x11220eca86535,0x11220eca86537,0x11220eca84737,0x11220ec64a937,0x11220eca86539,0x11220eca84739,0x11220ec648b37,0x11220ec8a6539,0x11220ec8a4739]

theorem move4_22 (h : realizable 1 (hostAt hosts4 22).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 22) ⟨0,by decide⟩ 6 0x8208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208208232c7022fbad22caea8e38e38e38e38e38e38e38e38e38e38e9a278e69648e28402082082082082082082082082082082207de21d71b21a6584514514514514514514514514514514575954544d24503c020820820820820820820820820820820e34c20b289207180041041041041041041041041041041045100043080040000 tags4_22 (by decide +kernel) h

def tags4_23 : Array Nat := #[0x0,0xed3020a86572,0xed30208a6572,0x130ec2064a972,0x130ec2046a972,0x130ec20a86573,0xec20a9306482,0xec2130a8648f,0xec2130a8468f,0x20ed30a86450,0xec21308a648f,0xec21308a468f,0x20ed308a6450,0x2130eca8653d,0x13020ec64a88f,0x13020ec46a88f,0x13020ec648a8f,0x13020ec468a8f,0x1302064eca882,0x2130ec64a850,0x2130ec46a850,0x2130eca86419,0x2130eca84619,0x20ed3064a819,0x2130eca8643e,0x2130eca8463e,0x20ed30648a19,0x2130ec8a643e,0x2130ec8a463e]

theorem move4_23 (h : realizable 1 (hostAt hosts4 23).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 23) ⟨0,by decide⟩ 5 0xd6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad6f37a6e7176daa06d2726d2726d2726d2726d2726c6006bdc0680006b5ad6b5ad6b5ad6b5ad6b5ad6318c4a529318c6294a5294a5294a5294a5294a51084208421000006b5ad6b5ad6b5ad6b5ad6b5ad62d404a0e0300002906029060290602906029060100000800000000 tags4_23 (by decide +kernel) h

def tags4_24 : Array Nat := #[0x0,0xeca930642135,0x130eca8206544,0x130eca8204744,0xed30a8206579,0x130ec8a206544,0x130ec8a204744,0xed308a206579,0x6512eca82006,0x11220eca86509,0x11220eca84709,0x2130eca8653e,0x130a864ec2082,0x130a8ec20649b,0x130a8ec20469b,0xa930ec206446,0x11264eca8206a,0x130eca8206563,0x130eca8204763,0x2130eca86462,0x11264ec8a206a,0x130ec8a206563,0x130ec8a204763,0x2130ec8a6462,0xa8cf30206407,0xa8cf30204607,0xa8cf30206408,0xcf3020a864df,0xcf3020a864e0,0xcf3020a846e0,0xce2130a864e4,0xcf30208a64df,0xcf30208a64e0,0xcf30208a46e0,0xce21308a64e4,0x112ec20a8650a,0x112ec20a8470a,0x6512eca82005,0x112ec20a8650b,0x112ec20a8470b,0x6512ec8a2005,0x112ec208a650b,0x112ec208a470b,0x130cea82064b6,0x130ec20a864c6,0x130ec20a846c6,0x130ec20a864d4,0x2130eca8643f,0x2130eca8463f,0x130ec208a64d4,0x2130ec8a643f,0x2130ec8a463f]

theorem move4_24 (h : realizable 1 (hostAt hosts4 24).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 24) ⟨0,by decide⟩ 6 0xb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2f3cb12f0bee2edb2b2ca2482ca2482ca2482ca2482ca2482eaa682e79a52e48c02cb2cb2cb2cb2cb2cb2cb2cb2cb2cb8a28a279e79e69a69a2cb2cb5d75d74d34d33cf3cf2cb2cb1c71c71041040410412cb2cb2cb2cb2cb2cb2cb2cb2cb2cb8a181f79d71b6996002ca2485d65544d24503ce34c2ca2481c6140103080040000 tags4_24 (by decide +kernel) h

def tags4_25 : Array Nat := #[0x0,0x130a8ec206536,0x130eca8206546,0x130eca8206542,0x130eca820657a,0x130ec8a206546,0x130ec8a206542,0x130ec8a20657a,0xed30a8206566,0x13020eca86551,0xec2130a86475,0x20ed30a84611,0x2130eca8654f,0xec2130a86485,0x20ed30a86434,0x2130eca86431,0xec21308a6485,0x20ed308a6434,0x2130ec8a6431,0x20ed30a86445,0xed30a8642172,0xed30a820476b,0xed30a8206564,0x130ec20a8657c,0xed308a206564,0x130ec208a657c,0xec2130a8649b,0x20ed30a8644a,0x20ed30a86444,0x2130eca8645c,0x20ed308a6444,0x2130ec8a645c,0x112a820ec6472,0x112a820ec466b,0x13020a8ec6483,0x13020eca86486,0x13020eca86490,0x13020eca8648a,0x13020eca864ab,0x13020ec8a6486,0x13020ec8a6490,0x13020ec8a648a,0x13020ec8a64ab,0x2130eca86407,0x2130eca8641c,0x2130eca8640f,0x2130eca8642a,0x2130eca86440,0x2130eca86433,0x2130ec8a642a,0x2130ec8a6440,0x2130ec8a6433]

theorem move4_25 (h : realizable 1 (hostAt hosts4 25).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 25) ⟨0,by decide⟩ 6 0xc30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c333cb1330bee32db2b30c30caaaaaa9a69a68a28a230c30caa9a279a59238a180030c30c30c30c30c30c30c30c30c4d331f4de31d4dc31b4da24924924924924924924924924920825921825721625521430c30c30c30c30c30c30c30c30c4d331245030f38d30b2802492491c71c71041040410412492081c6140103080040000 tags4_25 (by decide +kernel) h

def tags4_26 : Array Nat := #[0x0,0x2130eca86555]

theorem move4_26 (h : realizable 1 (hostAt hosts4 26).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 26) ⟨0,by decide⟩ 1 0x1fffffffffffffffffffff888f800f80000000000000000000000000000000000 tags4_26 (by decide +kernel) h

def tags4_27 : Array Nat := #[0x0,0x130eca8642121,0x130eca8462121,0x130eca8642181,0x130ec64a8211f,0x130eca8642159,0x130eca8462159,0x130ec648a2119,0x130ec8a20654a,0x130ec8a20474a,0x13020eca8655d,0x130a864ec211d,0x130a8ec642158,0x130a8ec462158,0x1308a6420ecc7,0x130a820ec64d9,0x130a820ec46d9,0x20ed30a86405,0x20ed30a86416,0x20ed30a84616,0x2130eca8655a,0x20ed3064a813,0x2130eca8643d,0x2130eca8463d,0x20ed308a6428,0x2130eca86424,0x2130eca84624,0xed30a864217d,0xed30a8206578,0xed30a8204778,0x130ec6420a96d,0x130ec20a8657f,0x130ec20a8477f,0x130ec8a642177,0x130eca8206583,0x130eca8204783,0x20ed30a86447,0x20ed30a8644c,0x20ed30a8464c,0x20ed3064a84b,0x2130eca8645d,0x2130eca8465d,0x20ed30a86449,0x2130eca86459,0x2130eca84659,0x13020eca8646a,0x13020eca86478,0x13020eca84678,0x13020eca864ac,0x13020ec64a877,0x13020eca86492,0x13020eca84692,0x2130ec8a6427,0x2130a8ec641d,0x2130a8ec461d,0x13020a864ec73,0x13020a8ec6491,0x13020a8ec4691,0x2130a864ec1a,0x2130a8ec6441,0x2130a8ec4641,0x2130eca86409,0x2130eca8641e,0x2130eca8461e,0x2130ec64a81b,0x2130eca86442,0x2130eca84642,0x2130eca8640d,0x2130eca86426,0x2130eca84626]

theorem move4_27 (h : realizable 1 (hostAt hosts4 27).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 27) ⟨0,by decide⟩ 7 0x142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142916243290a0c028fdf3d2850a1428f1dba60c183060e5c372850a1428d9ab460cd93160bd72d2850a142850a142850a142850a142850a1428b15aa28a542728992a4142850a142850a142850a142850a142850a148d1211480f9e1474e1b2850a142850a142850a142850a142850a142868c98285cb15284c911142850a144078e060c183063460b142850a142440706182840608080 tags4_27 (by decide +kernel) h

def tags4_28 : Array Nat := #[0x0,0x130eca8642123,0x130eca8462123,0x130eca8642182,0x130ec64a82120,0x130eca864215a,0x130eca846215a,0x1308aec64213e,0xa930ec2064f1,0xa930ec2046f1,0x13020eca86561,0x130a864ec2120,0x130a8ec64215a,0x130a8ec46215a,0x8b306420ecc4,0x130a820ec64da,0x130a820ec46da,0x130cea864213e,0xed30a82064f1,0xed30a82046f1,0xcf306420a8c4,0x130ec20a864da,0x130ec20a846da,0xce8b306420e3,0x130eca82064f9,0x130eca82046f9,0xeca86530212e,0xeca93020654b,0xeca93020474b,0x13020eca8655e,0x130ec6420a96e,0x130ec20a86580,0x130ec20a84780,0x8b30ec642140,0xa93020ec6570,0xa93020ec4770,0x130a86420ed6e,0x130a820ec6580,0x130a820ec4780,0xa9302064ed6f,0x13020a8ec655c,0x13020a8ec475c,0xcf30a8642140,0xed3020a86570,0xed3020a84770,0xed302064a96f,0x13020eca8655c,0x13020eca8475c,0xeca930206541,0x13020eca8655b,0x13020eca8475b,0xeca86512212e,0xeca91220654b,0xeca91220474b,0x11220eca8655e,0x112ec6420a96e,0x112ec20a86580,0x112ec20a84780,0x8b12ec642140,0xa91220ec6570,0xa91220ec4770,0x112a86420ed6e,0x112a820ec6580,0x112a820ec4780,0xa9122064ed6f,0x11220a8ec655c,0x11220a8ec475c,0xcf12a8642140,0xed1220a86570,0xed1220a84770,0xed122064a96f,0x11220eca8655c,0x11220eca8475c,0xeca912206541,0x11220eca8655b,0x11220eca8475b]

theorem move4_28 (h : realizable 1 (hostAt hosts4 28).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 28) ⟨0,by decide⟩ 7 0xa142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a152e54915223c61516243142850a150a0c06cd9b366cfdf3d142850a14f1dba6ce5c376cd5a33142850a142850a142850a142850a142850a14c98b014bd72d14b15aa142850a14a54273a74e9d3a992a4142850a148d1213a80f9e3a70d9a142850a142850a142850a142850a142850a1464c171458a94144c911142850a144078e060c183063460b142850a142440706182840608080 tags4_28 (by decide +kernel) h

def tags4_29 : Array Nat := #[0x0,0x130eca8642188,0x130eca8642184,0x130eca8462184,0x130ec8a642184,0x130ec8a462184,0x130cea8642184,0x130cea8462184,0x130ce8a642184,0x130ce8a462184,0x2130eca86562,0x2130eca86435,0x2130eca84635,0x2130ec8a6435,0x2130ec8a4635,0x2130a8ec6435,0x2130a8ec4635,0x213064eca835,0x2130eca86453,0x2130eca84653,0x213064ec8a35,0x2130ec8a6453,0x2130ec8a4653,0x2130a8ce6435,0x2130a8ce4635,0x213064cea835,0x2130cea86453,0x2130cea84653,0x213064ce8a35,0x2130ce8a6453,0x2130ce8a4653]

theorem move4_29 (h : realizable 1 (hostAt hosts4 29).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 29) ⟨0,by decide⟩ 5 0xa5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a5294a57bbc56f59562e05294a55ab454e51541e05294a539a053160500000842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210a50009cc008000084210948008c400800008421080000800008000 tags4_29 (by decide +kernel) h

def tags4_30 : Array Nat := #[0x0,0x130eca864212d,0x130eca846212d,0x130eca8642189,0x130ec64a8212d,0x130eca864215f,0x130eca846215f,0x130ec648a212d,0x130ec8a64215f,0x130ec8a46215f,0x130a864ec2125,0x130a8ec64215d,0x130a8ec46215d,0x13064eca8215d,0x130eca8642185,0x130eca8462185,0x13064ec8a215d,0x130ec8a642185,0x130ec8a462185,0x20ed30a86406,0x20ed30a86417,0x20ed30a84617,0x2130eca86582,0x20ed3064a817,0x20ed30a86437,0x20ed30a84637,0x20ed30648a17,0x20ed308a6437,0x20ed308a4637,0xeca865302125,0xeca93064215d,0xeca93046215d,0xec6530a8215d,0xed30a8642185,0xed30a8462185,0xec65308a215d,0xed308a642185,0xed308a462185,0x20eca8653012,0x20eca9306436,0x20eca9304636,0x20ec6530a836,0x20ed30a86454,0x20ed30a84654,0x20ec65308a36,0x20ed308a6454,0x20ed308a4654,0x2130eca86406,0x2130eca86417,0x2130eca84617,0x2130ec64a817,0x2130eca86437,0x2130eca84637,0x2130ec648a17,0x2130ec8a6437,0x2130ec8a4637,0x2130a864ec12,0x2130a8ec6436,0x2130a8ec4636,0x213064eca836,0x2130eca86454,0x2130eca84654,0x213064ec8a36,0x2130ec8a6454,0x2130ec8a4654,0x2130eca8640a,0x2130eca8641f,0x2130eca8461f,0x2130ec64a81f,0x2130eca86443,0x2130eca84643,0x2130ec648a1f,0x2130ec8a6443,0x2130ec8a4643]

theorem move4_30 (h : realizable 1 (hostAt hosts4 30).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 30) ⟨0,by decide⟩ 7 0x162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162c58b162d264472d1a2c42d0e1412c58b162d01fbe2cf5e3b2ce9cb82c58b162cddb352cd19b22cc582f2c58b162c58b162c58b162c58b162c58b162cb96ac2cad5292ca13a6060c183060c183060c183060c183060c183069522306890a0067cf1d2c58b162c58b162c58b162c58b162c58b162c70d9a2c64c172c54a13060c1830648890063c70d063058a060c183062440706182840608080 tags4_30 (by decide +kernel) h

def tags4_31 : Array Nat := #[0x0,0x130eca8642133,0x130eca8462133,0x130eca864218a,0x130ec64a82132,0x130eca8642160,0x130eca8462160,0x130ec648a212f,0x130ec8a20654c,0x130ec8a20474c,0x2130eca86587,0x130a864ec2132,0x130a8ec642160,0x130a8ec462160,0x13064eca8215e,0x130eca8642186,0x130eca8462186,0x8b306420ed6f,0xa93020ec64d8,0xa93020ec46d8,0x130a864ce212f,0x130a8ce20654c,0x130a8ce20474c,0xcf306420a96f,0xed3020a864d8,0xed3020a846d8,0xce8b30642141,0xeca9302064f3,0xeca9302046f3,0xeca865302132,0xeca930642160,0xeca930462160,0xec6530a8215e,0xed30a8642186,0xed30a8462186,0x8aec6421316f,0xa8ec213064d8,0xa8ec213046d8,0xa86530ec215e,0xa930ec642186,0xa930ec462186,0x8a642130ec94,0xa82130ec64b1,0xa82130ec46b1,0xcea86421316f,0xeca8213064d8,0xeca8213046d8,0xce642130a894,0xec2130a864b1,0xec2130a846b1,0xce8a642130cd,0xeca8213064db,0xeca8213046db,0xeca86512212f,0xeca91220654c,0xeca91220474c,0x112ec6420a96f,0x130ec20a864d8,0x130ec20a846d8,0x1128aec642141,0x130a8ec2064f3,0x130a8ec2046f3,0x112a86420ed6f,0x130a820ec64d8,0x130a820ec46d8,0x1126420eca894,0x13020eca864b1,0x13020eca846b1,0x1128a6420eccd,0x130a820ec64db,0x130a820ec46db,0x112cea8642141,0x130eca82064f3,0x130eca82046f3,0x112ce6420a8cd,0x130ec20a864db,0x130ec20a846db,0x112ce8a6420e5,0x130eca82064fa,0x130eca82046fa]

theorem move4_31 (h : realizable 1 (hostAt hosts4 31).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 31) ⟨0,by decide⟩ 7 0xa142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a153e74d15325ca1526447142850a151a2c4150e1411501fbe142850a14f5e3b14e9cb814ddb35142850a142850a142850a142850a142850a14d19b214c582f14b96ac142850a14ad529060c18306a13a6142850a149522306890a0067cf1d142850a142850a142850a142850a142850a1470d9a1464c171458a94142850a144c911064078e063460b142850a142440706182840608080 tags4_31 (by decide +kernel) h

def tags4_32 : Array Nat := #[0x130eca864210e,0x130eca8642134,0x130eca8462134,0x130eca864218c,0x130ec64a82134,0x130eca8642161,0x130eca8462161,0x130ec648a2134,0x130ec8a642161,0x130ec8a462161,0x130a864ec2134,0x130a8ec642161,0x130a8ec462161,0x13064eca82161,0x130eca8642187,0x130eca8462187,0x13064ec8a2161,0x130ec8a642187,0x130ec8a462187,0x130a864ce2134,0x130a8ce642161,0x130a8ce462161,0x13064cea82161,0x130cea8642187,0x130cea8462187,0x13064ce8a2161,0x130ce8a642187,0x130ce8a462187,0xeca865302134,0xeca930642161,0xeca930462161,0xec6530a82161,0xed30a8642187,0xed30a8462187,0xec65308a2161,0xed308a642187,0xed308a462187,0xa86530ec2161,0xa930ec642187,0xa930ec462187,0x6530eca82187,0x130eca864218b,0x130eca846218b,0x6530ec8a2187,0x130ec8a64218b,0x130ec8a46218b,0xa86530ce2161,0xa930ce642187,0xa930ce462187,0x6530cea82187,0x130cea864218b,0x130cea846218b,0x6530ce8a2187,0x130ce8a64218b,0x130ce8a46218b,0xeca865122134,0xeca912642161,0xeca912462161,0xec6512a82161,0xed12a8642187,0xed12a8462187,0xec65128a2161,0xed128a642187,0xed128a462187,0xa86512ec2161,0xa912ec642187,0xa912ec462187,0x6512eca82187,0x112eca864218b,0x112eca846218b,0x6512ec8a2187,0x112ec8a64218b,0x112ec8a46218b,0xa86512ce2161,0xa912ce642187,0xa912ce462187,0x6512cea82187,0x112cea864218b,0x112cea846218b,0x6512ce8a2187,0x112ce8a64218b,0x112ce8a46218b]

theorem move4_32 (h : realizable 1 (hostAt hosts4 32).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset :=
  descend hosts5 (hostAt hosts4 32) ⟨0,by decide⟩ 7 0x3060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183074684f073a6cc072e549060c18307223c60716243070a0c0060c18306fdf3d06f1dba06e5c37060c183060c183060c183060c183060c18306d9ab406cd93106c17ae060c18306b562b06a94a8069d325060c18306911a2068501f0678e9c060c183060c183060c183060c183060c183066cd190660b960654a13060c1830648890063c70d063058a060c183062440706182840608080 tags4_32 (by decide +kernel) h

theorem layer4 (h : ∃ i < hosts4.size, realizable 1 (hostAt hosts4 i).toFinset) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset := by
  obtain ⟨i,hi,h⟩ := h
  change i < 33 at hi
  interval_cases i

  · exact move4_0 h

  · exact move4_1 h

  · exact move4_2 h

  · exact move4_3 h

  · exact move4_4 h

  · exact move4_5 h

  · exact move4_6 h

  · exact move4_7 h

  · exact move4_8 h

  · exact move4_9 h

  · exact move4_10 h

  · exact move4_11 h

  · exact move4_12 h

  · exact move4_13 h

  · exact move4_14 h

  · exact move4_15 h

  · exact move4_16 h

  · exact move4_17 h

  · exact move4_18 h

  · exact move4_19 h

  · exact move4_20 h

  · exact move4_21 h

  · exact move4_22 h

  · exact move4_23 h

  · exact move4_24 h

  · exact move4_25 h

  · exact move4_26 h

  · exact move4_27 h

  · exact move4_28 h

  · exact move4_29 h

  · exact move4_30 h

  · exact move4_31 h

  · exact move4_32 h

theorem classified5 (possible : realizable 5 {0}) :
    ∃ i < hosts5.size, realizable 0 (hostAt hosts5 i).toFinset := by
  have initial : ∃ i < hosts0.size, realizable 5 (hostAt hosts0 i).toFinset := ⟨0,by decide,by simpa [hosts0, hostAt] using possible⟩
  exact layer4 (layer3 (layer2 (layer1 (layer0 (initial)))))


def slots (n m : Nat) : Finset Nat := (Finset.range n).filter fun i => m.testBit i = true

def nibbleCount (a : Nat) := (0x4332322132212110 >>> (4*(a % 16))) % 16

def pop4 : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, a => nibbleCount a + pop4 n (a >>> 4)

theorem nibble_correct (a : Nat) : nibbleCount a = (slots 4 a).card := by
  have cases16 : ∀ b : Fin 16, nibbleCount b.val = (slots 4 b.val).card := by decide +kernel
  have eq : slots 4 (a % 16) = slots 4 a := by
    ext i
    by_cases h : i < 4
    · have bit : (a % 16).testBit i = a.testBit i := by simpa [h] using Nat.testBit_mod_two_pow a 4 i
      simp [slots,bit]
    · simp [slots, h]
  simpa [nibbleCount, eq, Nat.mod_mod] using cases16 ⟨a % 16,Nat.mod_lt _ (by decide)⟩

theorem pop4_correct (n a : Nat) : pop4 n a = (slots (4*n) a).card := by
  induction n generalizing a with
  | zero => simp [pop4,slots]
  | succ n ih =>
    have split : slots (4*(n+1)) a = slots 4 a ∪ (slots (4*n) (a >>> 4)).image (4+·) := by
      ext i
      by_cases h : i < 4
      · simp [slots, h, show i < 4*(n+1) by omega]
        intro t _ _
        omega
      · constructor
        · intro mem
          obtain ⟨bound,bit⟩ := Finset.mem_filter.mp mem
          apply Finset.mem_union_right
          refine Finset.mem_image.mpr ⟨i-4,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,?_⟩,by omega⟩
          · have := Finset.mem_range.mp bound
            omega
          · simpa [Nat.testBit_shiftRight,show 4+(i-4)=i by omega] using bit
        · intro mem
          rcases Finset.mem_union.mp mem with small | big
          · exact False.elim (h (Finset.mem_range.mp (Finset.mem_filter.mp small).1))
          · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp big
            obtain ⟨bound,bit⟩ := Finset.mem_filter.mp hj
            have := Finset.mem_range.mp bound
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by simpa [Nat.testBit_shiftRight] using bit⟩
    have disj : Disjoint (slots 4 a) ((slots (4*n) (a >>> 4)).image (4+·)) := by
      apply Finset.disjoint_left.mpr
      intro i hi him
      obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp him
      have := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      omega
    rw [pop4, nibble_correct, ih, split, Finset.card_union_of_disjoint disj, Finset.card_image_of_injective]
    exact fun x y h => by omega

def pointAt (i : Nat) := negatives[i]?.getD 0

theorem point_valid (i : Fin 16) : pointAt i.val ∈ negatives := by
  have ok : ∀ j : Fin 16, pointAt j.val ∈ negatives := by decide +kernel
  exact ok i

theorem point_inj (i j : Fin 16) (e : pointAt i.val = pointAt j.val) : i = j := by
  have ok : ∀ a b : Fin 16, pointAt a.val = pointAt b.val → a = b := by decide +kernel
  exact ok i j e

def wanted (v : Fin 9) := packBits 16 fun i => (pointAt i).testBit v.val

def vertexProfile (rows : List Nat) (w : Nat) := packBits 32 fun j =>
  decide (j < rows.length) && decide (rows[j]?.getD 0 &&& w = 0)

def mapsCell (g : Nat → Nat) (u a : Nat) := ∀ i ∈ slots 16 u, g i ∈ slots 32 a

theorem makeEmbedding (rows : List Nat) (size : rows.length ≤ 32) (ok : fitsRows rows.toFinset) :
    ∃ (g : Nat → Nat) (f : Fin 9 → Nat), (∀ v, f v < 1024) ∧
      (∀ i < 16, g i < rows.length) ∧
      (∀ i < 16, ∀ j < 16, g i = g j → i = j) ∧
      ∀ i < 16, ∀ v, (wanted v).testBit i = (vertexProfile rows (f v)).testBit (g i) := by
  obtain ⟨f,bounds,all⟩ := ok
  have each (i : Fin 16) : ∃ j : Fin rows.length, ∀ v : Fin 9,
      (pointAt i.val).testBit v.val = true ↔ rows[j.val] &&& f v = 0 := by
    obtain ⟨r,hr,e⟩ := all _ (point_valid i)
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hr)
    exact ⟨j,by simpa [← hj] using e⟩
  choose pos matchAt using each
  let g (i : Nat) := if hi : i < 16 then (pos ⟨i,hi⟩).val else 0
  refine ⟨g,f,bounds,?_,?_,?_⟩
  · intro i hi
    simp [g,hi]
  · intro i hi j hj eq
    simp [g,hi,hj] at eq
    have same : pos ⟨i,hi⟩ = pos ⟨j,hj⟩ := Fin.ext eq
    have a := rowValue_eq f _ _ (negative_bound _ (point_valid ⟨i,hi⟩)) (matchAt ⟨i,hi⟩)
    have b := rowValue_eq f _ _ (negative_bound _ (point_valid ⟨j,hj⟩)) (matchAt ⟨j,hj⟩)
    rw [same] at a
    exact congrArg Fin.val (point_inj ⟨i,hi⟩ ⟨j,hj⟩ (a.symm.trans b))
  · intro i hi v
    have loc := (pos ⟨i,hi⟩).isLt
    have under : (pos ⟨i,hi⟩).val < 32 := by omega
    simp [g,hi,wanted,vertexProfile,pack_test,under,loc]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using matchAt ⟨i,hi⟩ v

theorem cell_bound (g : Nat → Nat) (inj : ∀ i < 16, ∀ j < 16, g i = g j → i = j)
    (u a : Nat) (ok : mapsCell g u a) : pop4 4 u ≤ pop4 8 a := by
  rw [pop4_correct,pop4_correct]
  apply Finset.card_le_card_of_injOn g ok
  intro x hx y hy e
  exact inj x (Finset.mem_range.mp (Finset.mem_filter.mp hx).1) y (Finset.mem_range.mp (Finset.mem_filter.mp hy).1) e

def cutBits (s p : Nat) := s ^^^ (s &&& p)

theorem cell_split (g : Nat → Nat) (u a t p : Nat) (ok : mapsCell g u a)
    (agrees : ∀ i < 16, t.testBit i = p.testBit (g i)) :
    mapsCell g (u &&& t) (a &&& p) ∧ mapsCell g (cutBits u t) (cutBits a p) := by
  have both (i : Nat) (hi : i < 16) (hu : u.testBit i = true) :=
    Finset.mem_filter.mp (ok i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,hu⟩))
  constructor <;> intro i hi
  · obtain ⟨lt,bits⟩ := Finset.mem_filter.mp hi
    have bound := Finset.mem_range.mp lt
    simp only [Nat.testBit_and, Bool.and_eq_true] at bits
    obtain ⟨gl,ga⟩ := both i bound bits.1
    exact Finset.mem_filter.mpr ⟨gl,by simp [Nat.testBit_and, ga, ← agrees i bound, bits.2]⟩
  · obtain ⟨lt,bits⟩ := Finset.mem_filter.mp hi
    have bound := Finset.mem_range.mp lt
    have eq := agrees i bound
    simp only [cutBits, Nat.testBit_xor, Nat.testBit_and] at bits
    have hu : u.testBit i = true := by cases h : u.testBit i <;> simp_all
    have ht : t.testBit i = false := by cases h : t.testBit i <;> simp_all
    obtain ⟨gl,ga⟩ := both i bound hu
    exact Finset.mem_filter.mpr ⟨gl,by simp [cutBits, Nat.testBit_xor, Nat.testBit_and, ga, ← eq, ht]⟩

theorem profile_union (rows : List Nat) (a b : Nat) :
    vertexProfile rows (a ||| b) = vertexProfile rows a &&& vertexProfile rows b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hi : j < 32 <;> by_cases hl : j < rows.length <;>
    simp [vertexProfile, pack_test, Nat.testBit_and, hi, hl, Nat.and_or_distrib_left]

def profileList (rows : List Nat) : Nat → List Nat
  | 0 => [vertexProfile rows 0]
  | k+1 =>
    let earlier := profileList rows k
    (earlier ++ earlier.map (· &&& vertexProfile rows (2^k))).eraseDups

theorem all_profiles (rows : List Nat) (k w : Nat) (bound : w < 2^k) :
    vertexProfile rows w ∈ profileList rows k := by
  induction k generalizing w with
  | zero => have eql : w = 0 := by simpa using bound
            simp [eql,profileList]
  | succ k ih =>
    simp only [profileList, List.mem_eraseDups, List.mem_append, List.mem_map]
    by_cases small : w < 2^k
    · exact Or.inl (ih w small)
    · have b : w-2^k < 2^k := by rw [pow_succ] at bound; omega
      have eq : (w-2^k) ||| 2^k = w := by rw [Nat.or_two_pow_eq_add_of_lt b]; omega
      exact Or.inr ⟨_,ih _ b,by rw [← profile_union,eq]⟩

def cellOK (point profile : Nat) (cell : Nat × Nat) :=
  decide (pop4 4 (cell.1 &&& point) ≤ pop4 8 (cell.2 &&& profile)) &&
  decide (pop4 4 (cutBits cell.1 point) ≤ pop4 8 (cutBits cell.2 profile))

def cellChildren (point profile : Nat) (cells : List (Nat × Nat)) :=
  cells.flatMap fun c => [(c.1 &&& point,c.2 &&& profile),(cutBits c.1 point,cutBits c.2 profile)]


def byteWeight (a : Nat) := (0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110 >>> (4*(a % 256))) % 16
theorem byte_weight (a : Nat) : byteWeight a = nibbleCount a + nibbleCount (a >>> 4) := by
  have table : ∀ b : Fin 256, byteWeight b.val = nibbleCount b.val + nibbleCount (b.val >>> 4) := by decide +kernel
  have low : (a % 256) % 16 = a % 16 := by omega
  have high : ((a % 256) >>> 4) % 16 = (a >>> 4) % 16 := by simp only [Nat.shiftRight_eq_div_pow]; omega
  simpa only [byteWeight,nibbleCount,Nat.mod_mod,low,high] using table ⟨a % 256,Nat.mod_lt _ (by decide)⟩

def weight16 (a : Nat) := byteWeight a + byteWeight (a >>> 8)
def weight32 (a : Nat) := weight16 a + weight16 (a >>> 16)
theorem weight16_correct (a : Nat) : weight16 a = pop4 4 a := by
  simp [weight16,byte_weight,pop4,← Nat.shiftRight_add,Nat.add_assoc]
theorem weight32_correct (a : Nat) : weight32 a = pop4 8 a := by
  simp [weight32,weight16,byte_weight,pop4,← Nat.shiftRight_add,Nat.add_assoc]

theorem weight_parts (n a p : Nat) : pop4 n (a &&& p) + pop4 n (cutBits a p) = pop4 n a := by
  simp only [pop4_correct]
  have dis : Disjoint (slots (4*n) (a &&& p)) (slots (4*n) (cutBits a p)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have x := (Finset.mem_filter.mp hi).2
    have y := (Finset.mem_filter.mp hj).2
    simp only [Nat.testBit_and, Bool.and_eq_true] at x
    simp [cutBits,Nat.testBit_xor,Nat.testBit_and,x.1,x.2] at y
  rw [← Finset.card_union_of_disjoint dis]
  congr 1
  ext i
  cases ha : a.testBit i <;> cases hp : p.testBit i <;> simp [slots, cutBits,Nat.testBit_and,Nat.testBit_xor,ha,hp]

def cutLimit (t : Nat) (c : Nat × Nat) :=
  (c.2,weight16 (c.1 &&& t),weight16 (cutBits c.1 t),weight32 c.2)

def limitPass (p : Nat) (lim : Nat × Nat × Nat × Nat) :=
  let n := weight32 (lim.1 &&& p)
  decide (lim.2.1 ≤ n ∧ n+lim.2.2.1 ≤ lim.2.2.2)

theorem limitPass_eq (t p : Nat) (c : Nat × Nat) :
    limitPass p (cutLimit t c) = cellOK t p c := by
  have eq := weight_parts 8 c.2 p
  simp only [limitPass,cutLimit,cellOK,weight16_correct,weight32_correct]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,Bool.and_eq_true]
  omega

def allowed (profiles : List Nat) (cells : List (Nat × Nat)) (v : Fin 9) :=
  let limits := cells.map (cutLimit (wanted v))
  profiles.filter (fun p => limits.all (limitPass p))

theorem keep_profile (rows : List Nat) (g : Nat → Nat) (f : Fin 9 → Nat)
    (inj : ∀ i < 16, ∀ j < 16, g i = g j → i = j)
    (agrees : ∀ i < 16, ∀ v, (wanted v).testBit i = (vertexProfile rows (f v)).testBit (g i))
    (cells : List (Nat × Nat)) (ok : ∀ c ∈ cells, mapsCell g c.1 c.2)
    (P : List Nat) (v : Fin 9) (hp : vertexProfile rows (f v) ∈ P) :
    vertexProfile rows (f v) ∈ allowed P cells v ∧
      ∀ c ∈ cellChildren (wanted v) (vertexProfile rows (f v)) cells, mapsCell g c.1 c.2 := by
  have both (c : Nat × Nat) (hc : c ∈ cells) :=
    cell_split _ _ _ _ _ (ok c hc) (fun i hi => agrees i hi v)
  constructor
  · apply List.mem_filter.mpr
    refine ⟨hp,List.all_eq_true.mpr ?_⟩
    intro lim hl
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hl
    rw [limitPass_eq]
    simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨cell_bound g inj _ _ (both c hc).1, cell_bound g inj _ _ (both c hc).2⟩
  · intro c hc
    obtain ⟨d,hd,hc⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact (both d hd).1
    · exact (both d hd).2

def seedCells (rows : List Nat) := [(65535,vertexProfile rows 0)]

theorem seed_maps (rows : List Nat) (size : rows.length ≤ 32)
    (g : Nat → Nat) (bound : ∀ i < 16, g i < rows.length) :
    ∀ c ∈ seedCells rows, mapsCell g c.1 c.2 := by
  intro c hc
  simp only [seedCells,List.mem_cons,List.not_mem_nil,or_false] at hc
  subst c
  intro i hi
  have lt := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  have loc := bound i lt
  have small : g i < 32 := by omega
  simp [slots,vertexProfile,pack_test,small,loc]

theorem root_reject (rows : List Nat) (size : rows.length ≤ 32) (v : Fin 9)
    (checked : allowed (profileList rows 10) (seedCells rows) v = []) : ¬ fitsRows rows.toFinset := by
  intro fits
  obtain ⟨g,f,bounds,loc,inj,matchAt⟩ := makeEmbedding rows size fits
  have needed := (keep_profile rows g f inj matchAt _ (seed_maps rows size g loc) _ v
    (all_profiles rows 10 (f v) (bounds v))).1
  simp [checked] at needed

def compactChildren (point profile : Nat) (cells : List (Nat × Nat)) :=
  (cellChildren point profile cells).filter (fun c => c.1 != 0)

def readPivot (book : Nat) (cursor : Nat) : Fin 9 :=
  ⟨((book >>> (4*cursor)) % 16) % 9,Nat.mod_lt _ (by decide)⟩

def rejectTree (profiles : List Nat) (book : Nat) : Nat → Nat → List (Nat × Nat) → Option Nat
  | 0, _, _ => none
  | d+1, pos, cells =>
    let v := readPivot book pos
    (allowed profiles cells v).foldlM (fun next p =>
      rejectTree profiles book d next (compactChildren (wanted v) p cells)) (pos+1)

theorem fold_visits {xs : List Nat} {s n p : Nat} {step : Nat → Nat → Option Nat}
    (ok : xs.foldlM step s = some n) (mem : p ∈ xs) : ∃ a b, step a p = some b := by
  induction xs generalizing s with
  | nil => simp at mem
  | cons h t ih =>
    cases e : step s h with
    | none => simp [List.foldlM, e] at ok
    | some mid =>
      rcases List.mem_cons.mp mem with rfl | inside
      · exact ⟨s,mid,e⟩
      · apply ih (s := mid) _ inside
        simpa [List.foldlM,e] using ok

theorem rejectTree_sound (rows : List Nat) (g : Nat → Nat) (f : Fin 9 → Nat)
    (inj : ∀ i < 16, ∀ j < 16, g i = g j → i = j)
    (agrees : ∀ i < 16, ∀ v, (wanted v).testBit i = (vertexProfile rows (f v)).testBit (g i))
    (P : List Nat) (hp : ∀ v, vertexProfile rows (f v) ∈ P)
    (book fuel pos final : Nat) (cells : List (Nat × Nat))
    (ok : ∀ c ∈ cells, mapsCell g c.1 c.2) : rejectTree P book fuel pos cells ≠ some final := by
  induction fuel generalizing pos cells final with
  | zero => simp [rejectTree]
  | succ fuel ih =>
    intro complete
    let v := readPivot book pos
    obtain ⟨mem,children⟩ := keep_profile rows g f inj agrees cells ok P v (hp v)
    obtain ⟨a,b,childOK⟩ := fold_visits complete mem
    exact ih a b _ (fun c hc => children c (List.mem_filter.mp hc).1) childOK

theorem terminal_reject (rows : List Nat) (size : rows.length ≤ 32) (book final : Nat)
    (checked : rejectTree (profileList rows 10) book 10 0 (seedCells rows) = some final) :
    ¬ fitsRows rows.toFinset := by
  intro fit
  obtain ⟨g,f,bounds,loc,inj,matchAt⟩ := makeEmbedding rows size fit
  exact rejectTree_sound rows g f inj matchAt _ (fun v => all_profiles rows 10 _ (bounds v))
    book 10 0 final _ (seed_maps rows size g loc) checked

def siteAt (s i : Nat) := (s >>> (5*i)) % 32
def siteImage (s p : Nat) := packBits 32 fun i => p.testBit (siteAt s i)
abbrev siteInvolution (s : Nat) := ∀ i : Fin 32, siteAt s (siteAt s i.val) = i.val

theorem site_bounded (s i : Nat) : siteAt s i < 32 := Nat.mod_lt _ (by decide)

theorem site_mapped (s p j : Nat) (hs : siteInvolution s) (hj : j < 32) :
    (siteImage s p).testBit (siteAt s j) = p.testBit j := by
  simp [siteImage,pack_test,site_bounded,hs ⟨j,hj⟩]

theorem image_and (s p q : Nat) : siteImage s (p &&& q) = siteImage s p &&& siteImage s q := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < 32 <;> simp [siteImage,pack_test,Nat.testBit_and,h]

theorem image_cut (s p q : Nat) : siteImage s (cutBits p q) = cutBits (siteImage s p) (siteImage s q) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i < 32 <;> simp [siteImage,pack_test,Nat.testBit_and,Nat.testBit_xor,cutBits,h]

def modelData (P : List Nat) (cells : List (Nat × Nat)) (g : Nat → Nat) (f : Fin 9 → Nat) :=
  (∀ i < 16, g i < 32) ∧
  (∀ i < 16, ∀ j < 16, g i = g j → i = j) ∧
  (∀ c ∈ cells, mapsCell g c.1 c.2) ∧
  (∀ v, f v ∈ P) ∧
  ∀ i < 16, ∀ v, (wanted v).testBit i = (f v).testBit (g i)

def hasModel (P : List Nat) (cells : List (Nat × Nat)) :=
  ∃ (g : Nat → Nat) (f : Fin 9 → Nat), modelData P cells g f

def symGood (P : List Nat) (s : Nat) := siteInvolution s ∧ ∀ p ∈ P, siteImage s p ∈ P
def symStable (cells : List (Nat × Nat)) (s : Nat) := ∀ c ∈ cells, siteImage s c.2 = c.2

theorem transform_model (P : List Nat) (cells : List (Nat × Nat))
    (g : Nat → Nat) (f : Fin 9 → Nat) (m : modelData P cells g f)
    (s : Nat) (good : symGood P s) (stable : symStable cells s) :
    modelData P cells (fun i => siteAt s (g i)) (fun v => siteImage s (f v)) := by
  obtain ⟨bound,inj,tracked,allow,agrees⟩ := m
  refine ⟨fun i _ => site_bounded _ _,?_,?_,fun v => good.2 _ (allow v),?_⟩
  · intro i hi j hj eq
    apply inj i hi j hj
    have same := congrArg (siteAt s) eq
    simpa only [good.1 ⟨g i,bound i hi⟩,good.1 ⟨g j,bound j hj⟩] using same
  · intro c hc i mem
    obtain ⟨_,bit⟩ := Finset.mem_filter.mp (tracked c hc i mem)
    have hi := Finset.mem_range.mp (Finset.mem_filter.mp mem).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (site_bounded _ _),?_⟩
    calc
      c.2.testBit (siteAt s (g i)) = (siteImage s c.2).testBit (siteAt s (g i)) := congrArg (fun a : Nat => a.testBit _) (stable c hc).symm
      _ = c.2.testBit (g i) := site_mapped s c.2 (g i) good.1 (bound i hi)
      _ = true := bit
  · intro i hi v
    rw [site_mapped _ _ _ good.1 (bound i hi)]
    exact agrees i hi v

theorem minimal_model (P : List Nat) (cells : List (Nat × Nat)) (v : Fin 9)
    (has : hasModel P cells) :
    ∃ g f, modelData P cells g f ∧ ∀ s, symGood P s → symStable cells s → f v ≤ siteImage s (f v) := by
  classical
  let possible (p : Nat) := ∃ g f, modelData P cells g f ∧ f v = p
  have existsP : ∃ p, possible p := by obtain ⟨g,f,m⟩ := has; exact ⟨f v,g,f,m,rfl⟩
  obtain ⟨g,f,m,e⟩ := Nat.find_spec existsP
  refine ⟨g,f,m,?_⟩
  intro s good stable
  have newP : possible (siteImage s (f v)) :=
    ⟨_,_,transform_model P cells g f m s good stable,rfl⟩
  calc
    f v = Nat.find existsP := e
    _ ≤ siteImage s (f v) := Nat.find_min' existsP newP

theorem model_keeps (P : List Nat) (cells : List (Nat × Nat)) (g : Nat → Nat) (f : Fin 9 → Nat)
    (model : modelData P cells g f) (v : Fin 9) :
    f v ∈ allowed P cells v ∧ modelData P (compactChildren (wanted v) (f v) cells) g f := by
  obtain ⟨bound,inj,tracked,mem,agree⟩ := model
  have both (c : Nat × Nat) (hc : c ∈ cells) :=
    cell_split _ _ _ _ _ (tracked c hc) (fun i hi => agree i hi v)
  constructor
  · apply List.mem_filter.mpr
    refine ⟨mem v,List.all_eq_true.mpr ?_⟩
    intro l hl
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hl
    rw [limitPass_eq]
    simp only [cellOK,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨cell_bound g inj _ _ (both c hc).1,cell_bound g inj _ _ (both c hc).2⟩
  · refine ⟨bound,inj,?_,mem,agree⟩
    intro c hc
    obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp (List.mem_filter.mp hc).1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl
    · exact (both d hd).1
    · exact (both d hd).2

theorem stable_children (s t p : Nat) (cells : List (Nat × Nat)) (stable : symStable cells s)
    (fixes : siteImage s p = p) : symStable (compactChildren t p cells) s := by
  intro c hc
  obtain ⟨d,hd,which⟩ := List.mem_flatMap.mp (List.mem_filter.mp hc).1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at which
  rcases which with rfl | rfl
  · simp only [image_and,stable d hd,fixes]
  · simp only [image_cut,stable d hd,fixes]

theorem initialModel (rows : List Nat) (size : rows.length ≤ 32) (fit : fitsRows rows.toFinset) :
    hasModel (profileList rows 10) (seedCells rows) := by
  obtain ⟨g,f,bounds,loc,inj,matchAt⟩ := makeEmbedding rows size fit
  exact ⟨g,fun v => vertexProfile rows (f v),fun i hi => lt_of_lt_of_le (loc i hi) size,inj,
    seed_maps rows size g loc,fun v => all_profiles rows 10 _ (bounds v),matchAt⟩

def sideSymMask (S : List Nat) (f : Nat → Bool) :=
  packBits S.length fun i => f (S[i]?.getD 0)

def symRows (P S : List Nat) := P.map fun p =>
  (p,sideSymMask S (fun s => decide (siteImage s p < p)),sideSymMask S (fun s => siteImage s p == p))

def liveSyms (P : List Nat) (cells : List (Nat × Nat)) (S : List Nat) (active : Nat) :=
  ∀ j : Fin S.length, active.testBit j.val = true → symGood P S[j.val] ∧ symStable cells S[j.val]

theorem fold_member {α : Type} {xs : List α} {s n : Nat} {x : α} {step : Nat → α → Option Nat}
    (ok : xs.foldlM step s = some n) (mem : x ∈ xs) : ∃ a b, step a x = some b := by
  induction xs generalizing s with
  | nil => simp at mem
  | cons h t ih =>
    cases e : step s h with
    | none => simp [List.foldlM,e] at ok
    | some mid =>
      rcases List.mem_cons.mp mem with rfl | inside
      · exact ⟨s,mid,e⟩
      · apply ih (s := mid) _ inside
        simpa [List.foldlM,e] using ok


theorem profile_witness (rows : List Nat) (k p : Nat) (hp : p ∈ profileList rows k) :
    ∃ w < 2^k, vertexProfile rows w = p := by
  induction k generalizing p with
  | zero =>
    have e : p = vertexProfile rows 0 := by simpa [profileList] using hp
    exact ⟨0,by decide,e.symm⟩
  | succ k ih =>
    simp only [profileList,List.mem_eraseDups,List.mem_append,List.mem_map] at hp
    rcases hp with prev | ⟨a,prev,rfl⟩
    · obtain ⟨w,hw,eq⟩ := ih _ prev
      exact ⟨w,by rw [pow_succ]; omega,eq⟩
    · obtain ⟨w,hw,rfl⟩ := ih _ prev
      refine ⟨w ||| 2^k,?_,profile_union _ _ _⟩
      rw [Nat.or_two_pow_eq_add_of_lt hw,pow_succ]
      omega

def checkSite (rows : List Nat) (s q j : Nat) :=
  let dest := siteAt s j
  (siteAt s dest == j) && if j < rows.length then
    decide (dest < rows.length) && (rows[j]?.getD 0 == relabel q (rows[dest]?.getD 0))
  else decide (rows.length ≤ dest)

def checkPair (rows : List Nat) (s q : Nat) :=
  decide (permOK q) && (List.range 32).all (checkSite rows s q)

theorem moves_profile (rows : List Nat) (s q w : Nat) (good : checkPair rows s q = true)
    (bw : w < 1024) : siteImage s (vertexProfile rows w) = vertexProfile rows (relabel q w) := by
  simp only [checkPair,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at good
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j < 32
  · have rule := good.2 j (List.mem_range.mpr h)
    by_cases hr : j < rows.length
    · simp only [checkSite,hr,ite_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at rule
      have eq := relabeled_pair q good.1 (rows[siteAt s j]?.getD 0) w bw
      rw [← rule.2.2] at eq
      simp only [siteImage,vertexProfile,pack_test,h,site_bounded,hr,rule.2.1,decide_true,
        Bool.true_and,eq]
    · simp only [checkSite,hr,ite_false,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at rule
      have no : ¬ siteAt s j < rows.length := Nat.not_lt.mpr rule.2
      simp [siteImage,vertexProfile,pack_test,h,hr,no,site_bounded]
  · simp [siteImage,vertexProfile,pack_test,h]

theorem checkPair_sound (rows : List Nat) (s q : Nat) (good : checkPair rows s q = true) :
    symGood (profileList rows 10) s ∧ symStable (seedCells rows) s := by
  have test := good
  simp only [checkPair,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at test
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i
    have eq := test.2 i.val (List.mem_range.mpr i.isLt)
    exact eq_of_beq ((Bool.and_eq_true_iff.mp eq).1)
  · intro p hp
    obtain ⟨w,bw,rfl⟩ := profile_witness rows 10 p hp
    rw [moves_profile _ _ _ _ good bw]
    exact all_profiles _ _ _ (pack_lt 10 _)
  · intro c hc
    simp only [seedCells,List.mem_cons,List.not_mem_nil,or_false] at hc
    subst c
    exact (moves_profile rows s q 0 good (by decide)).trans
      (congrArg (vertexProfile rows) ((relabel_zero q 0 test.1 (by decide)).mpr rfl))

def orbitSites (pairs : List (Nat × Nat)) := pairs.map Prod.fst

theorem model_restrict (P : List Nat) (A B : List (Nat × Nat)) (g : Nat → Nat) (f : Fin 9 → Nat)
    (subset : ∀ c ∈ B, c ∈ A) (model : modelData P A g f) : modelData P B g f := by
  obtain ⟨a,b,c,d,e⟩ := model
  exact ⟨a,b,fun x hx => c x (subset x hx),d,e⟩

theorem model_append (P : List Nat) (A B : List (Nat × Nat)) (g : Nat → Nat) (f : Fin 9 → Nat)
    (left : modelData P A g f) (right : modelData P B g f) : modelData P (A++B) g f := by
  obtain ⟨a,b,c,d,e⟩ := left
  refine ⟨a,b,?_,d,e⟩
  intro x hx
  rcases List.mem_append.mp hx with l | r
  · exact c x l
  · exact right.2.2.1 x r

theorem stable_append (A B : List (Nat × Nat)) (s : Nat) (l : symStable A s) (r : symStable B s) :
    symStable (A++B) s := by
  intro x hx
  exact (List.mem_append.mp hx).elim (l x) (r x)

def rootRows (rows : List Nat) (v : Fin 9) :=
  allowed (profileList rows 10) (seedCells rows) v

def representativeV (v : Fin 9) : Fin 9 := if v = 0 then 0 else 1

theorem root_same (rows : List Nat) (v : Fin 9) : rootRows rows (representativeV v) = rootRows rows v := by
  have all : ∀ i : Fin 9, weight16 (65535 &&& wanted (representativeV i)) = weight16 (65535 &&& wanted i) ∧
      weight16 (cutBits 65535 (wanted (representativeV i))) = weight16 (cutBits 65535 (wanted i)) := by decide +kernel
  obtain ⟨a,b⟩ := all v
  simp only [rootRows,allowed,seedCells,List.map_cons,List.map_nil,cutLimit,a,b]

def pickData (A B : List (Nat × Nat × Nat)) (v : Fin 9) := if v = 0 then A else B


def quickWanted (v : Fin 9) := (0xf80007c00638c0340187300b29428c60529d >>> (16*v.val)) % 65536

theorem quick_wanted (v : Fin 9) : quickWanted v = wanted v := by
  have check : ∀ j : Fin 9, quickWanted j = wanted j := by decide +kernel
  exact check v

def enough (k x : Nat) :=
  if k = 0 then true else if k = 1 then x != 0 else if k = 2 then (x &&& (x-1)) != 0
  else decide (k ≤ weight32 x)

theorem enough_true (k x : Nat) (en : k ≤ weight32 x) : enough k x = true := by
  have zero : weight32 0 = 0 := by decide
  unfold enough
  split
  · rfl
  split
  · rename_i h
    subst k
    by_contra! no
    have eq : x = 0 := by simpa using no
    rw [eq,zero] at en
    omega
  split
  · rename_i h
    subst k
    have xpos : x ≠ 0 := by intro eq; rw [eq,zero] at en; omega
    by_contra! no
    have low : x &&& (x-1) = 0 := by simpa using no
    obtain ⟨j,rfl⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo xpos).mp low
    have small : (slots 32 (2^j)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have aa := (Finset.mem_filter.mp ha).2
      have bb := (Finset.mem_filter.mp hb).2
      simp only [Nat.testBit_two_pow,decide_eq_true_eq] at aa bb
      omega
    rw [weight32_correct,pop4_correct] at en
    change 2 ≤ (slots 32 (2^j)).card at en
    omega
  · exact decide_eq_true en

def requirements (t : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat × Bool)
  | _, [] => []
  | w, c::cs =>
    if w = 0 then [] else
      let rest := requirements t (w >>> 2) cs
      let neg := if w.testBit 1 then (c.2,weight16 (cutBits c.1 t),false)::rest else rest
      if w.testBit 0 then (c.2,weight16 (c.1 &&& t),true)::neg else neg

def passes (p : Nat) (r : Nat × Nat × Bool) :=
  enough r.2.1 (if r.2.2 then r.1 &&& p else cutBits r.1 p)

theorem requirements_true (cells : List (Nat × Nat)) (t p mask : Nat)
    (all : ∀ c ∈ cells, cellOK t p c = true) :
    (requirements t mask cells).all (passes p) = true := by
  induction cells generalizing mask with
  | nil => rfl
  | cons c cs ih =>
    have next := ih (mask >>> 2) (fun q h => all q (List.mem_cons_of_mem _ h))
    have here := all c (by simp)
    simp only [cellOK,Bool.and_eq_true,decide_eq_true_eq,← weight32_correct,← weight16_correct] at here
    have yes := enough_true _ _ here.1
    have no := enough_true _ _ here.2
    by_cases z : mask = 0
    · simp [requirements,z]
    · cases b : mask.testBit 0 <;> cases d : mask.testBit 1 <;> simp [requirements,z,b,d,passes,next,yes,no]

def sparseOptions (data : List (Nat × Nat × Nat)) (t mask active : Nat) (cells : List (Nat × Nat)) :=
  let req := requirements t mask cells
  data.filter fun r => r.2.1 &&& active == 0 && req.all (passes r.1)

def hintMask (hints : Array Nat) (i : Nat) := ((hints[i/64]?.getD 0) >>> (32*(i % 64))) % 4294967296

def sparseTree (A B : List (Nat × Nat × Nat)) (hints : Array Nat) (book : Nat) :
    Nat → Nat → List (Nat × Nat) → Nat → Option Nat
  | 0, _, _, _ => none
  | d+1,pos,cells,active =>
    let entry := (book >>> (16*pos)) % 65536
    let word := entry % 16 + 16 * hintMask hints (entry >>> 4)
    let v : Fin 9 := ⟨(word % 16) % 9,Nat.mod_lt _ (by decide)⟩
    let t := quickWanted v
    (sparseOptions (pickData A B v) t (word >>> 4) active cells).foldlM (fun next r =>
      sparseTree A B hints book d next (compactChildren t r.1 cells) (active &&& r.2.2)) (pos+1)
theorem sparse_sound (rows S : List Nat) (hints : Array Nat) (book depth pos last : Nat) (cells : List (Nat × Nat)) (active : Nat)
    (home : ∀ j : Fin S.length, symGood (profileList rows 10) S[j.val] ∧ symStable (seedCells rows) S[j.val])
    (valid : liveSyms (profileList rows 10) cells S active)
    (has : hasModel (profileList rows 10) (seedCells rows ++ cells)) :
    sparseTree (symRows (rootRows rows 0) S) (symRows (rootRows rows 1) S) hints book depth pos cells active ≠ some last := by
  let P := profileList rows 10
  induction depth generalizing pos last cells active with
  | zero => simp [sparseTree]
  | succ d ih =>
    intro complete
    let entry := (book >>> (16*pos)) % 65536
    let word := entry % 16 + 16 * hintMask hints (entry >>> 4)
    let v : Fin 9 := ⟨(word % 16) % 9,Nat.mod_lt _ (by decide)⟩
    obtain ⟨g,f,model,minimum⟩ := minimal_model P _ v has
    let p := f v
    let bad := sideSymMask S (fun s => decide (siteImage s p < p))
    let fix := sideSymMask S (fun s => siteImage s p == p)
    have seed := model_restrict P _ (seedCells rows) g f (fun _ h => List.mem_append_left _ h) model
    have tracked := model_restrict P _ cells g f (fun _ h => List.mem_append_right _ h) model
    obtain ⟨rootMem,_⟩ := model_keeps P _ g f seed v
    obtain ⟨mem,child⟩ := model_keeps P _ g f tracked v
    have clean : bad &&& active = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < S.length
      · by_cases live : active.testBit i = true
        · have min := minimum S[i] (home ⟨i,hi⟩).1 (stable_append _ _ _ (home ⟨i,hi⟩).2 (valid ⟨i,hi⟩ live).2)
          simp [bad,sideSymMask,pack_test,hi,live,Nat.testBit_and,p,Nat.not_lt_of_ge min]
        · simp [Nat.testBit_and,live]
      · simp [Nat.testBit_and,bad,sideSymMask,pack_test,hi]
    have pivot : pickData (symRows (rootRows rows 0) S) (symRows (rootRows rows 1) S) v =
        symRows (rootRows rows v) S := by
      rw [← root_same rows v]
      by_cases h : v = 0 <;> simp [pickData,representativeV,h]
    have rowMem : (p,bad,fix) ∈ sparseOptions (pickData (symRows (rootRows rows 0) S)
        (symRows (rootRows rows 1) S) v) (quickWanted v) (word >>> 4) active cells := by
      rw [pivot]
      apply List.mem_filter.mpr
      refine ⟨List.mem_map.mpr ⟨p,rootMem,rfl⟩,?_⟩
      simp only [clean,beq_self_eq_true,Bool.true_and,quick_wanted]
      apply requirements_true
      intro c hc
      have good := (List.all_eq_true.mp (List.mem_filter.mp mem).2) _ (List.mem_map.mpr ⟨c,hc,rfl⟩)
      simpa only [limitPass_eq] using good
    obtain ⟨a,b,cert⟩ := fold_member complete rowMem
    simp only [quick_wanted] at cert
    apply ih a b _ (active &&& fix) _ ⟨g,f,model_append P _ _ g f seed child⟩ cert
    intro j h
    simp only [Nat.testBit_and,Bool.and_eq_true] at h
    have fixed : siteImage S[j.val] p = p := by simpa [fix,sideSymMask,pack_test,j.isLt] using h.2
    exact ⟨(valid j h.1).1,stable_children _ _ _ _ (valid j h.1).2 fixed⟩

theorem sparse_reject (rows : List Nat) (size : rows.length ≤ 32) (pairs : List (Nat × Nat)) (hints : Array Nat) (book final : Nat)
    (valid : pairs.all (fun e => checkPair rows e.1 e.2) = true)
    (checked : sparseTree (symRows (rootRows rows 0) (orbitSites pairs)) (symRows (rootRows rows 1) (orbitSites pairs))
        hints book 10 0 (seedCells rows) (2^pairs.length-1) = some final) : ¬ fitsRows rows.toFinset := by
  intro fit
  have home (j : Fin (orbitSites pairs).length) :
      symGood (profileList rows 10) (orbitSites pairs)[j.val] ∧ symStable (seedCells rows) (orbitSites pairs)[j.val] := by
    obtain ⟨e,he,h⟩ := List.mem_map.mp (List.getElem_mem (l := orbitSites pairs) j.isLt)
    rw [← h]
    exact checkPair_sound _ _ _ (List.all_eq_true.mp valid e he)
  obtain ⟨g,f,m⟩ := initialModel rows size fit
  exact sparse_sound rows _ hints book 10 0 final _ _ home (fun j _ => home j) ⟨g,f,model_append _ _ _ _ _ m m⟩ checked

def hints908 : Array Nat := #[0x750006006000000320000001a100000681000006000000005d00000004004001020001222000002920000003a0000007a000000006000006060001483000001218000000390000000b000001240000042400012100000000c9000004a10000061200000063000004a400009220000004a50000400c000012200000072000001018000004200006003000000069000000e9000000160000005f000000120000001400006080000000b1000000000000004300012430000000b00000092400000621000000e1000000b80000001a000000380000000c00000423000000e0000090240000000e000000c800000057000000e80000001e0000001c00000003,0x21a00000066000004a3000004a2000000d70000102c00000524000060880000488400000143000004830000040300000384000400600000042500000031000009810000102400000c8100000625000006a1000006040000600c0000408c0001a0200001009000000180000004a000010240000003a400000c2400010212000040900000012600000055000002c100010460000000b900000186000005a400000724000001a40000005300001224000100180000009900000061000000e400000784000092400000902000000123000000020000000a00010430000004270000061000000324000004840000902200000922000000d500000421000000c1,0x586000001130002600800000091000402600000124000000487000000100000068500000382000000cc000086040000068800000640000008e0000011180000096400006820000009e0000006a0000004430000003c00048400000048040000402c000004060000012c00021200000180910000400e0000016400000c1000000418000008c4000001060000001900000013000040600000444c0004024000000925000004810000024100000e240000000f0000040700000120000060100000446c0000121000001090000001e40240212000180030000000680000012700006800000009c4000007800000408400000584000000770108004000010040,0x1a600000071000098200000840400004a200000062300000306004000400001a100000018100000064600000183000060000000480c00000d25000009200000004600012460000009440000064c0000044c000001a20180200600024094000182100001406000000c04000000e2000000640001010c0000100e00000c22000004c3000001e00001011800009026000003430000017200001204000001070000004900000017000400400000922400000c210000052600000184000102100000d0250000980800000159000000f0000000d10000d02100002124000001a50000007300000c01000009a10000016600010130000068040040024000020610,0x100102000100120000848400000e50000009a0000006020000060100000520000004590000010e000040860000040c0000026100012130000101c00000440c0000101000000e10000001a30000004c000182120000122c00000c26000008620000060800000133000000c00000006c000019a000000e260000044601000240000250000000058c000000d300000985000008e4000000cb0000006700012700000121060001041200010092000009260000048c001025000000650000000e440000042600000404000001250000400400000530000000410000610000000864000000180041800000011240000062080000014600000826000007a400000506,0x602500001488400001e042000122500000982400006404000046480000292400000e4600000c23000008c2000006200000044e000001a00000009800000033001000b0000040480000100600000c4c000300100001424000010d1000010c20000106600000124200000630000000f4004012400002111000018010000060840000060500000103000000c600018006000120040000406c00002484000012c00000050400000243000000e60001006000009202000090060000122100000846000004850000046c000000c30040010000014030000120380001010200000d21000006240000060c0000023200000190000000e3000000600000002a00240202,0x640c00004098000010260000090700000785000006a50000064e000002630000002d020400400004004800004284000040060000121200000e8100000ca20000082e00000650000002c5000000370000002300481060000210180001251000010010000060040000164000000c50000009c00000052700000442000004100000022c000001d00000018200000116000000ca000000b30000006500000036034020200100804000402400000124000000822c0000401200001891000004900000040d000003220000002b004084000040010c000480400002408c000106040000d0200000606000004838000048100000122800000ca40000050c00000144,0x80120000652400005118000048300000212800000d2000000ac1000006c00000066000000464000004120000027000000251000000c70000004b001821000010009000100038000401a00004010a000401020002041000014910000124200001010e00000e5800000d8000000c68000009100000072100000704000004c000000416000002500000004e00000011001200300006004800060018000180900001210400010640000103040000d0240000d007000060820000110e00000c25000009e40000094600000923000008e60000003b0000003a0000001b006081020020401000180010001600000003025000021c4200012412000104040000c023,0x19200000101200000d0700000c700000095100000844000006830000068000000652000006070000041e00000370000000a30000005b000000400000002e0120004000402100002402400018801000100600000602400006012000060100000400420002400900020412000181000000688400004c4c00004080000021840000210400000d2400000c85000009300000090500000843000006a3000004a70000042c0000040e00000265000001c400000185000001810000016700000162000001510000012200000104000000c5000000720040a4000040090000400120001000d000021012000148600001218000012030000105180001034000008680,0x407000004024000012440000104800000e4800000c2700000a41000009d100000903000005030000045800000438000002c0000001e1000000470182200001802020009000400080610000400012002040700012001000108850000921000008401000068000000608200006004000024081000120840001201000010d00000042400000409100000c0500000ac8000009d0000009c50000094300000904000006a4000004f0000004a600000428000002e4000001600000014c0000014200000140000000c400000062001a003000040068000302460001c090000123000001011200010004000090420000892400004824000044100000401800001c90,0x24020800118060001021000010010000100032000424000003025800024014000161000001089000010442000102460001023000010093000100480001001a0000909000009004000062020000502d000040f00000401900002921000024060000212000001a0800001650000012060000113200000ea200000e6600000c4e00000a06000006c3000006580000065400000638000004780000022e000001d3000001b800000179000000f10000006e01a0200201402420004020840018406000100460001000600009218000034110000302440002444800024015000202c80001a40000018000000101000001004200009226000092210000892000004b00,0x560300202402040010010441000100001800602400004400400040030400204032001100100010004800100012000680020004810200040440000400620002500400024091000211060002101000019048000184000001803800012d00000124420001200c0001051000010508000102500001014800009260000092060000920400004d040000486000004204000040680000401d00002610000018060000120000001112000011100000109800000ea400000c51000009c1000007860000078100000644000006180000052d00000502000004660000045100000405000004010000011e0000010c0000004f00000044000000260180204201001920,0x2040300018210200140040001088120010466000100024000620060004840200041980000404000004020400040120000302660002144a00020640000162400001604000012410000123400001224000012110000120600001201200010584000105480001048600010440000100620000c0680000500d00004a4000004930000044400000422c000040310000212c00001a06000012a000001284000012460000111a000010840000100c00000e0600000cc200000ca600000c5300000c4400000c06000009060000081a00000643000004790000041a0000040800000386000002780000019c00000196000001210000011a000000e5000000a70000008c,0x1040a0001011000010068000100130000d00d0000c09400006880000050400000501800004918000045840000446e0000444800004400000042600000414800004118000040d00000404e0000401000001a12000012250000120c0000109300000e5a00000e5200000ca300000c0e00000b4300000b0000000ae200000921000006280000060d000005940000058e0000048a0000046e0000045e00000444000004220000041c0000038000000346000002c8000001c7000001a8000001940000018c000001880000010b00000105000000d4000000aa000000920000008a00000074000000520000004d0000003501000048004480000040034000240220,0x8660000084e000007a60000072500000701000006d0000006320000062600000609000005a800000587000004c60000045a000004560000044800000304000002d800000231000001870000015300000128000000ed000000da000000930000008e0000002c0000001f00000001026020200102208001000040004100400040404000402520004009020040040200140840000618000006086000060640000604600004a1040004204200040a60000406000004050a000400e0000400c0000340900003025a0003025200025840000240900002401100021440000212500002100e0001888000018460000182180001400c0001242800012202000111a4,0x460000004084800040402000402480004004600034020000216400001850000018011000140c00001401a0001220000012118000120240001054a000105000001046800010258000101200001011a00010024000100060000e0420000d0220000c8050000c0050000868400008424000069000000680c0000624000006090000060020000502200004a0000004848000048280000456200004560000042850000424800004160000040390000401c000040140000400d00004009000029060000249400001a6000001a240000190200001824000011840000104200000e6000000e4000000d0d00000ca500000c2d00000c1200000c1100000ae0000009e6,0x40f0000040b0000034a0000034400000326000002e2000002d0000002c40000020e000001d1000001b200000171000001700000015c000001380000010d000000f2000000d8000000b2000000ab000000960000008b0000007c000000760000006b0000005c00000034400040000120001001022008010080420100200e0100006000804100006800600060800200600102006000040050000c0048026000420100004104000040600000402420004023200040202400401900004000240024010800240042002092200011800000110020001040c0001040200010232000100204000924400006026000060210000600c00006000c0004826000048042,0x602c000050840000486800004812000048060000466000004600000045240000444e0000413000004100000040c0000040a40000409c000040940000406e00004046000040360000248c0000248500001a4200001a1000001a0200001982000019280000190a00001440000012a4000012500000116000001106000010a6000010890000106200000ea000000e8500000e5100000e0400000d9000000c8900000c1800000c0700000b1000000b0400000ac500000a26000009a4000009530000094c000009470000094000000813000006480000061600000580000005160000050e0000050a000004dc000004920000048600000453000004500000043a,0x4850000040408000400440003024800024034000224100002182000021818000218080002124400021204000206500001e0020001c2400001a104000184400001820200018060000165000001601100014270000141480001411000012590000125180001244000012302000122440001209900012068000120400001202800010d2400010c40000106700001061200010590000104840001048200010438000104220001040c0001025200010244000101420001009800010091000100580001004a000100090000e0400000c03800009880000098020000926400009040000090250000840c000081820000812200006584000064000000612400006030,0x2420000023a000002340000022300000218000001c10000018900000173000001650000015b0000014e0000014b00000149000001470000011c000000dd000000dc000000d0000000ce000000cd000000a60000009c0000007d00000059000000510000001d00000007020606000190004001080042010800100100640001002400008061020064000000608400006000020040410200401108004010420040040000400122004000480030240200284010002620000020405000201820001a001000180090001800500016080000148040001400c0001100400010805000100180001001200010008400092004000606000006044000060400000600e0,0x1281000012640000124800001190000011860000110c00001100000010c2000010910000106c0000104400001043000010230000101b0000100400000ea600000e6800000e4c00000e2800000e0a00000d0800000ca100000c9400000c8d00000c7800000c3800000c0300000b4000000b3000000a4a000008c00000086300000806000006e0000006c80000065c00000603000005a2000005a00000052c000005110000050d000004d0000004c80000049c000004910000048d00000489000004540000044b000004300000042d0000041300000409000003a60000030c00000303000002e5000002e1000002e0000002540000024a0000024900000248,0x864000008324000082e6000082e4000080c20000806600006c4000006a84000068080000646000006424000062140000610c0000608c000060400000600e0000600100005805000058000000562000005608000050260000501000005005000050040000488c0000481100004742000047060000452e0000446000004420000044040000428c00004242000042240000420c000041420000410c000040e2000040a10000406a0000404a0000404200004040000040260000401700004013000024c000002491000024180000241000002380000021810000206200001b0000001a400000198000001930000019100000164800001402000013a200001310,0x1e2400001c202000184100001818000018110000180880001801200018004000180020001600400014b000001490800014248000142000001414a00014118000140900001403200012891000126400001251200012508000124060001240200012304000119240001100c00010d4000010c0400010a5000010a4000010a0c00010542000104c00001049200010462000104240001040200010268000102420001020c00010204000101840001018000010038000100330001001b0000e1020000e0220000e00a0000d2250000d0260000ca210000c44c0000c4420000c2400000c2240000980600009608000092660000920c000090230000902100008e46,0x180070001680400014a04000148a40001200700012003800110402001100600011000200108070001046400010406000100900001008040010066000100402001004000010024800100224001000f0001000e200100070001000500010003000100018000c6100000c41000009240400084090000640000006204200061000000608400006006800060038000530200004810400048000000430080004200e00041042000408440004084200040640000405a0000404200004010800040012000340120003224600030210000300700003004c000300180002501000024016000211040002104c0002100600020e4000020c4200020462000204180001e242,0x216000001e5000001d9000001c5000001c0000001ac000001910000018d0000017b0000016c000001540000014100000136000001300000011200000109000000f3000000ec000000eb000000e7000000d6000000c2000000ae0000009e00000083000000700000005e00000054000000450000003e00000032000000300240202002402004024005000204046001208048012024040108005001061000010001200050210000484000004821400044040000410402004085000040210200402004004010060040100200401000004004240040009000400042003002240029240000248400002402420020818200206030002060100020487000201880,0x94200000914000009110000090d000008c6000008a7000008a3000008720000086a0000086100000853000008320000082f0000082b0000080e0000070c000007050000066800000659000006530000062c0000061c000006130000060e0000060a000005a60000059c000005250000052200000505000004e0000004db000004d4000004b0000004ac0000047b000004620000045b000004490000043600000432000004310000042a00000411000003c8000003c2000003940000038c0000035c000003540000032c00000313000002e6000002c9000002c20000026600000264000002620000024e0000024d00000245000002380000023600000226,0x2409000023060000219400002189000021260000210c000021060000204500001aa400001a2000001a180000190c00001908000018c2000018640000185800001842000018120000149200001294000012080000118200001150000011430000113800001128000011240000112200001120000010c40000109c00001094000010860000106a000010600000104900001041000010400000101a00001019000010110000100900000e3800000e2200000e2000000e0800000d8800000d0400000d0000000ca700000ca000000c8300000c6000000c0f00000c0d00000c0900000b5000000a6200000a6100000a4500000a2e000009660000095900000958,0x60140000600800005808000051840000514000005104000050c000005090000050820000502c000050240000500f0000500c0000500300004c6000004c4e00004c0c00004b4000004a6000004a04000048a400004842000048400000470800004642000045260000440e0000440800004402000042c2000042900000426800004262000042180000421200004210000040e8000040e0000040b1000040ac000040950000408e000040890000408500004081000040780000406600004062000040500000403c0000401b000040110000400b000034800000310000002ca100002c4200002c1000002c030000298400002926000029040000260500002411,0x1003a00010032000100310001002c00010011000100050000e4400000e4200000e2420000e2400000e0600000d2210000d1840000d0860000d0840000d02d0000d0060000d0040000c4600000c4400000c40c0000c2a10000c2030000c08c0000c0620000c0140000a10600009e00000099000000928400009242000092220000900c00008e6400008c0c00008600000084a40000848c000083060000821a0000821200008126000080c6000080920000803200006d4000006d000000688c0000688200006840000068240000660000006520000065020000632000006120000060c00000609c000060920000608600006070000060680000604a00006024,0x14092000140910001404800014040000140210001401900014015000140120001401000012c00000128040001227000012252000122460001220e0001214000012112000121080001209100012080000120700001204e0001204800012002000119840001180c000113800001116000011048000110420001100200010d84000109020001088200010740000107100001067800010540000105240001051200010502000104e0000104c2000104480001041a000104100001040600010400000102e000010262000102480001022c000102180001020e00010164000101260001012400010104000100d0000100c0000100b1000100780001006a0001004c,0x3825800034080000340100003226400031940000311040003026000030204000300780003005000026100000260900002504200024804000240b00002401900021e0200021c4000021a0000021830000218100002164200021246000211120002103800020e5800020e1000020e0200020c3000020c10000204800002044a00020401000202e0000202620002024a000201280002010a000200720002006a0001e0400001c2000001a3000001a0900001a0520001a0400001a0060001a0040001a0000001851000018058000180400001802c00016242000160600001604a00014a0800014990000148400001482800014820000143400001427800014095,0x1043200010400800102404001024000010130000101040001010240010100400100a00001009020010086000100850001008120010040c00100292001000980010006200100040001000060009050000086030000860020008440000084050000810680008012c000800c800080062000720020006810200060808000608020006050200060448000604200006040800060220000600420006001000060000000498000004844800048108000480480004640000046100000449000004460000042242000421040004204000041920000411800004110800040a4200040980000405020004050000040244000402420004018000040128000401000004004a,0x1000980010006000100042001000182010000700100005800c02102008604080084004000804308006802000064800000614000006024200060240600600400006001200060004200484060004824000048214200482100004810000044060000420050004106000040a4040040818000408100004044020040430000402d0000402804004025000040240200402380004023040040210400400700004004200040040400400018004000100024200800240224002001820020010a001a0400001a0080001904600018001200160040001600100014204200142040001408c000140060001208000012000400108a1000108a00001088320010809000108040,0x30021240206004001c02002018460000180180001800440018004080180008101800042018000010140040001202400012020820120200a0110010801080448010800480104640001046100010449000100844801008404010060000100442001001182]

set_option maxRecDepth 16384 in
theorem terminal0 : ¬ fitsRows (hostAt hosts5 0).toFinset :=
  terminal_reject _ (by decide) 0x133110 6 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal1 : ¬ fitsRows (hostAt hosts5 1).toFinset :=
  terminal_reject _ (by decide) 0x111133333110 12 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal2 : ¬ fitsRows (hostAt hosts5 2).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca28398a4188307b9ac5a920,0x8976543210)] hints908 0x1720172017203810003000303810003000300a103810140 12 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal3 : ¬ fitsRows (hostAt hosts5 3).toFinset :=
  terminal_reject _ (by decide) 0x133110 6 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal4 : ¬ fitsRows (hostAt hosts5 4).toFinset :=
  terminal_reject _ (by decide) 0x331110 6 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal5 : ¬ fitsRows (hostAt hosts5 5).toFinset :=
  terminal_reject _ (by decide) 0x001 3 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal6 : ¬ fitsRows (hostAt hosts5 6).toFinset :=
  terminal_reject _ (by decide) 0x3333111110 10 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal7 : ¬ fitsRows (hostAt hosts5 7).toFinset :=
  terminal_reject _ (by decide) 0x1 1 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal8 : ¬ fitsRows (hostAt hosts5 8).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f835cc5a90931ca410c01,0x9876543201),(0xffbbcdeb38bdab49ca2e6c1eb628e64a08508062,0x9876542310),(0xffbbcdeb38bdab49c94941cc52460f7358b18820,0x8976543210)] hints908 0x3093423110003000300a118d518d300a10140 10 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal9 : ¬ fitsRows (hostAt hosts5 9).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c64f8398d5a5474188510c01,0x9876543201),(0xffbbcdeb38bdab45a928398a49ca307b9ac18820,0x8976543210)] hints908 0x3017201721b750381002201c3001201c3001201c3001200a10003091409141dc30bc5018205a500c201b31f780aa700c20003038100a112510934093400031b7502e300a11f130b82061302e5017202c402930172002203811b75001200a10140 49 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal10 : ¬ fitsRows (hostAt hosts5 10).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a464f835cc52d0931c8510c01,0x9876543201),(0xffbbcdeb38bdab494e3073dac5a548394c418440,0x9876541032),(0xffbbcdeb38bdab19ca8d7ba0c4292b218a700823,0x9876540123),(0xffbbcdeb38bdab28d26e6c1ec4a16a290e608062,0x9876542310),(0xffbbcdeb38bdab07b9b49ca2c398a45a92818820,0x9854763210),(0xffbbcdeb38bd98b5250731495a4e5183dcd18820,0x8976543210)] hints908 0x301720172017203810003001201c3001200a10ef41dc30bc5018209b3092402930012038101c30b8218e4046400530172001203810140 28 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal11 : ¬ fitsRows (hostAt hosts5 11).toFinset :=
  terminal_reject _ (by decide) 0x001 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal12 : ¬ fitsRows (hostAt hosts5 12).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca3073dab6292831ca320801,0x9876543201),(0xffbbcdeb38bdab49ca2d62e0f7292520d0730820,0x9854763210),(0xffbbcdeb38bdab49c928398a418a307b9ac5a820,0x8976543210)] hints908 0x107200a100a11dd80068000700030140 8 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal13 : ¬ fitsRows (hostAt hosts5 13).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a465073d8d5a5474188510c01,0x9876543201),(0xffbbcdeb38bd96a4a0e629062ad2728c1ee6b020,0x8976543210)] hints908 0x316030aa7061305a50022001210c30b57061305a500d50182023401b305e401b3001201720033041408930182032100120033001201c300120033001200a1000306830a7303970454051307c40033157401e4040310a301822c3409c325860bc5553520d64e67001209c50d8602e50012129300d50d535314345710a300121806091607050094003309240293158605440397018200030381000300a109340934093400030012001201b300c200a1000301c30b821af302e5017202c4029301720012038100120012001200a10140 104 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal14 : ¬ fitsRows (hostAt hosts5 14).toFinset :=
  terminal_reject _ (by decide) 0x110 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal15 : ¬ fitsRows (hostAt hosts5 15).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f8398d52d274188510c01,0x9876542310),(0xffbbcdeb38bdab49c928398a418a307b9ac5a820,0x8976543210)] hints908 0x18d318d518d300a1000300a1231142a42311000300030140 12 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal16 : ¬ fitsRows (hostAt hosts5 16).toFinset :=
  terminal_reject _ (by decide) 0x110 3 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal17 : ¬ fitsRows (hostAt hosts5 17).toFinset :=
  terminal_reject _ (by decide) 0x3330 4 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal18 : ¬ fitsRows (hostAt hosts5 18).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda9594e2f835cb6254831c8510c01,0x9876542310),(0xffbbcdeb38bdab3a4a3073dac52d28394c418440,0x9876325410),(0xffbbcdeb38bda549d62d7ba095a988218a700823,0x9876234510),(0xffbbcdeb38bda72ad22e6c1ea4b168290e608062,0x9876453210),(0xffbbcdeb38bd98b5250731495a4e5183dcd18820,0x8976543210)] hints908 0x300030012001200c200a1000300120033001200a10003059400e3101400e30182009406c4005300220d84051301720381000301b300c20012001200a10140 32 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal19 : ¬ fitsRows (hostAt hosts5 19).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c65073d8d5a54831c8510c01,0x9876542310),(0xffbbcdeb38bdab45a928398a49ca307b9ac18820,0x8976543210)] hints908 0x300121f1300c200a1000300a10934093412510003000300b300b300a10068006812c80007000300b3001200a10843055704a210c3170704a204b10140 31 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal20 : ¬ fitsRows (hostAt hosts5 20).toFinset :=
  terminal_reject _ (by decide) 0x3310 4 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal21 : ¬ fitsRows (hostAt hosts5 21).toFinset :=
  terminal_reject _ (by decide) 0x313110 6 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal22 : ¬ fitsRows (hostAt hosts5 22).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab45a928398a49ca307b9ac18820,0x8976543210)] hints908 0x30012001200a1000300a109340934125112510003000300b300b300b300a100680068006812c80007000300b3001200a100030047003300c2315410f30a1600b501722755048407940053017200d50012038104a204a200c200a10140 47 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal23 : ¬ fitsRows (hostAt hosts5 23).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab28d26f835cc4a16a31c8510c01,0x9876542310),(0xffbbcdeb38bd98b5250731495a4e5183dcd18820,0x8976543210)] hints908 0x3000300120012001200c200a100030012003300120da209c30033001202d300a100030834059400e30584058400e3018209c3358600f42c350053001209c50924157410a310a300120af60af60155018200030381000300b300b300a100680068006812c8000700030b9401c3003300c20e6708860a1600b5017205b7048407940053017200d50012038100a111a3002210e51d2305d7017210c310c305d701721cb5002203810140 85 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal24 : ¬ fitsRows (hostAt hosts5 24).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f835cb6290931c8510c01,0x9876542310),(0xffbbcdeb38bdab49c94941cc52460f7358b18820,0x8976543210)] hints908 0x30003125100a312c800070003000300b3001200a103810140 13 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal25 : ¬ fitsRows (hostAt hosts5 25).toFinset :=
  terminal_reject _ (by decide) 0x221 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal26 : ¬ fitsRows (hostAt hosts5 26).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda9594e2f8398d52d09394c410c01,0x9876542310),(0xffbbcdeb38bd96a4a0e629062ad2728c1ee6b020,0x8976543210)] hints908 0x31af300d5002200120234003300120012003300c200610003001200330012003300120033001200a1000306930ef8039707d4071400532e27276413c514f467e83d6804140403009400940bc5018204c6061300b500220e0310d600b5002205160cd81b970475526504540403009406c40053158605440397122310230bc5018202b4071405130b9402b405130172038100030012001201b300c200a10003000301b300c20012001200a1000300120012001200a10140 92 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal27 : ¬ fitsRows (hostAt hosts5 27).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab28d26f8398d5a0ea494c410c01,0x9876542310),(0xffbbcdeb38bd96a4a0e629062ad2728c1ee6b020,0x8976543210)] hints908 0x322330aa70022001208430b5700d500c200330644089300c20172032100030012003300120da209c30033001204a300a1000306830a7303970454157410a31574064404030564056400e310a3018202b401c30012258618061dc50012180625260705102305251f780397516603f7018210861086015532240427018200030381000300a10934093409340003000300120012001200a101c3107202e300a1009419b3002210e51d2305d7017210c3084305d7017210e31ca5002203810140 96 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal28 : ¬ fitsRows (hostAt hosts5 28).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f8398d52d274188510c01,0x9876542310),(0xffbbcdeb38bdab49c928398a418a307b9ac5a820,0x8976543210)] hints908 0x1218d500a1000304a112c8300300070003000303810140 12 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal29 : ¬ fitsRows (hostAt hosts5 29).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd96a4a0e629062ad2728c1ee6b020,0x8976543210)] hints908 0x3061305a50613052500120012023401b302b3052500120012028409760115017202340234008306130525017202c409c30321000300120033001200330012003300120033001200a10003184402232f751bd41844022312f512f5084307730397071407d400330414009404141dc50dd708340564025420f800e3018209c507e6061302e5001210d6129300d5092420d410a310a3001202b402b402b410a30d7306e4054405d701c301720d862c361dc5006236f71036108601062c9801550cf40d4405d7158605440b57018205e4046402930525800305440aa700c20003038100030012001201b300c201b300c200a1000300030003023401c3003300c20a1602e5017207940293017200d500120381000301c3001200a100120012001200a10140 146 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal30 : ¬ fitsRows (hostAt hosts5 30).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd96a4a0e629062ad2728c1ee6b020,0x8976543210)] hints908 0x316031603019700d5061305250022001210c30843019700d505a500c2003300120033001204140d730b82091409c3032100030012003300220033001201c30012003300120061000302b40564056405640d7309d408340513157401e4040305640564025400e310a3018220d40d7301c300120ef60ed60bc5049700f4049703d400530022180609160705102309c506a503f76f640427017214b703c6697410e300b510a3002210861086010601551a63042718680b570182052570d303f71f780aa700c200030321000300a10934093400240934000300030012001201b3001202e300a100030033001214d60a160a1602e501725074079407940293017200d500220022038101c30b82001200a100120012001200a10140 141 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal31 : ¬ fitsRows (hostAt hosts5 31).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd276ac1f28b5cc4a16a290e610c01,0x9876542310),(0xffbbcdeb38bca307dab49b9ac398a45a92818820,0x9854763210),(0xffbbcdeb3862d4941cc520c57b56939460f73420,0x8976543210)] hints908 0x32233019700d5061305a500220012003300120012062401b3002200620061000300030012003300220da209c30033001202d3006106830683019709d409d405130003100402b40403047509d40cd8058400e301a20e3409c30ef60ef60bc509a513665de30ca411d709a51366055701a20003103602c6070510231c9507230e1407230e140c77000306a503f70924029301a2705430f313780af6015507230e14055700031a63042701a209c50d8602e5002203210003003300120c3705e4057405740be80033001200d500220012006101c300c205e4046400530012001200610ef50053002204e600741d23004701720e450053002203210140 126 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal32 : ¬ fitsRows (hostAt hosts5 32).toFinset :=
  terminal_reject _ (by decide) 0x11310 5 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal33 : ¬ fitsRows (hostAt hosts5 33).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab48c2727b16e6a0ea4986229001,0x9876453210),(0xffbbcdeb38bdab4525073148314e5183dcd62c20,0x8976543210)] hints908 0x30012001201b300c202e300a100030022003300c201c30012003300c200a10003003300c2002201c30012003300c200a100030012001201b300c202e300a1000300a10140 35 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal34 : ¬ fitsRows (hostAt hosts5 34).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c928398a418a307b9ac5a820,0x8976543210)] hints908 0xc202d302d300a1000300a102d423111251231100030003000300030140 15 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal35 : ¬ fitsRows (hostAt hosts5 35).toFinset :=
  terminal_reject _ (by decide) 0x31110 5 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal36 : ¬ fitsRows (hostAt hosts5 36).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd96a4a0e629062ad2728c1ee6b020,0x8976543210)] hints908 0x3079407940053041400d500120a160a1600b5061305a505a500c205e401b302b30525001207540033001204140d730b82091409c303810003001200b3003300120033001200b300a10c7710c31f27157401e4040318f4155507e500530dd708340aa80a54025400e3157401e404030062055720d40d7306e40544004720d401c301a206931ac7124820d64e670062180621730705102309c508272a08004701a2050534f407e50293124853143457006242681b864ad508040956006704030f230d44004707b731c603970182180621730705102305252a08004712a40397018204b10003000300a10934093400240934000300030012001201c3001201b300c200a10003000302b40893003300120484057400530172088608c600b5017200d50012038101c30b82001200a100120012001200a10140 156 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal37 : ¬ fitsRows (hostAt hosts5 37).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c9cd6460f5a92520d0730820,0x9854763210),(0xffbbcdeb38bdab49a507314831065183dcd62d40,0x8976543210)] hints908 0x198704a2064400e300c2064400e300c204a1000300a102d40064006400640003000300030140 19 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal38 : ¬ fitsRows (hostAt hosts5 38).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bad4941cc520c41b56939460f73580,0x8976543210)] hints908 0x3007400740074082704360f672c740f871a73010600d5041400d50f0624682c740f871a7306f601550022001200740106731407b712860ab8442800d50284097601151286128600d5001207c4208710e607c408071a050254003307c407683ac8003312f72c740f060f871a7306f6015500120754003300120234023400830564056404140d73001206441a7810e601e408071a0503b400e30ea40ea4003314c710e601e4064408071a0503b400e310861086304609c500c2006100030012003300220033001200330012003300120061000304140094041409c509d413a713a70403100401e4040307141555155500530dd708340cd80564025400e3100401e414d3013301a209d402b402b40d7302c40d7306e4054403f702c401c301a20ef619d719d7070509a509d609a509d63a570062103609160705102309c506a503f7405307a40d041353004701a205054ed764850293072316d4072316d42c47013300224e8802664ad5063409561b9704030cf4024404271a630427158602140197018210360916170510230525068470036dc4084300471586021401970182000303210003000300a10934093400240934000300030012001201b3001201b300c2006100030003003300120de60a160a1602e501720204079407940293017200d5002200220321001200120012006100120012001200610140 253 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal39 : ¬ fitsRows (hostAt hosts5 39).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c64f8398d5a5474188510c01,0x9876543201),(0xffbbcdeb38bdab45a928398a49ca307b9ac18820,0x8976543210)] hints908 0x3001200b300a1002201c30012003300c2003300c200a1000314f407c400830033018209c300d5018200336d6422330aa700c203810003000300a10022001242c300c200a11b7500a10140 38 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal40 : ¬ fitsRows (hostAt hosts5 40).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c65073d8d5a54831c8510c01,0x9876543201),(0xffbbcdeb38bdab45a928398a49ca307b9ac18820,0x8976543210)] hints908 0x300121b7500a1000300a1093412510934000300b300b300a10068006812c80007000300a1002200121f1300c200a11b75001200a10140 28 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal41 : ¬ fitsRows (hostAt hosts5 41).toFinset :=
  terminal_reject _ (by decide) 0x331387333210 12 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal42 : ¬ fitsRows (hostAt hosts5 42).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c928398a418a307b9ac5a820,0x8976543210)] hints908 0x141300b300a100a14852175112c8313200a33003000700030003000300a10140 16 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal43 : ¬ fitsRows (hostAt hosts5 43).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c64f839ab6290931ca410c01,0x9876543201),(0xffbbcdeb38bdab4525073148314e5183dcd62c20,0x8976543210)] hints908 0x3001200d50182017220e400b30381002201c30012003300c2003300c200a1000302b40893003300c200d5017200d500c2003307540ac40083018203810003000301c30b8202e300a10022001211a300c200a10140 43 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal44 : ¬ fitsRows (hostAt hosts5 44).toFinset :=
  terminal_reject _ (by decide) 0x3310 4 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal45 : ¬ fitsRows (hostAt hosts5 45).toFinset :=
  terminal_reject _ (by decide) 0x3310 4 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal46 : ¬ fitsRows (hostAt hosts5 46).toFinset :=
  terminal_reject _ (by decide) 0x13110 5 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal47 : ¬ fitsRows (hostAt hosts5 47).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab47b9ac9ca30598a41a92838801,0x9867543210),(0xffbbcdeb38bdab4525073148314e5183dcd62c20,0x8976543210)] hints908 0x3001202e30012003300c200a10003001202e30012003300c200a1000300a10003000300b300b300a10a0500630a050063000700030140 28 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal48 : ¬ fitsRows (hostAt hosts5 48).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb389460f75ed5a4da73148362d4940801,0x9867543210),(0xffbbcdeb3862d4941cc520c57b56939460f73420,0x8976543210)] hints908 0x3000300330033001200d5223301970022001216a30d3422061223055800d5001200d53e5501970356019700221a5500e60a0502040be80033024401970012006200610003000300330033001216a30d3405582206122300d5001200d522330197002200121a5500e60be80a050204003302440197001200d53e550197035601970022006200610003000300120ac40033002200d50012003300120061000328f80214068301971c540768066403174328177601e4040302440f2300470f230244113500470182140329e808d60597445805f42c2307050f160ba6007403f70fa405e40053009404640053098503e300741766022303f701a20356486500470cf40a580a2304270074004701a212d607e600b522a30074055700220ff406c401b322a30074055700221465035606830047343322d401061c04022304270106004701a2032100030ac400330022001200d500120033001200610003445805f42c23140329e808d6059707050ba600740f1603f70fa405e40053098503e300741766022303f700940464005301a24328177601e41c54076806640317040328f80214068301970f23024400470f2302441135004701820a580a230cf404274865035600470074004701a212d607e600b522a3007405570022343322d401061c040223042714650356068300470106004701a20ff406c401b322a30074055700220321001201b300220012006101b300220012001200610140 268 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal49 : ¬ fitsRows (hostAt hosts5 49).toFinset :=
  terminal_reject _ (by decide) 0x233123313333310 15 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal50 : ¬ fitsRows (hostAt hosts5 50).toFinset :=
  terminal_reject _ (by decide) 0x44344333310 11 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal51 : ¬ fitsRows (hostAt hosts5 51).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49a507314831065183dcd62d40,0x8976543210)] hints908 0xd504a20ea407c400330033018201c30b82091404a30ea407c400330033018200d500d5018204b1000300a157b257b21751006830d400a330d400a30007000300030003000300a10140 37 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal52 : ¬ fitsRows (hostAt hosts5 52).toFinset :=
  terminal_reject _ (by decide) 0x222122213333110 15 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal53 : ¬ fitsRows (hostAt hosts5 53).toFinset :=
  terminal_reject _ (by decide) 0x3333110 7 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal54 : ¬ fitsRows (hostAt hosts5 54).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38ad2f69bdcd9460a4b16820c4731401,0x9876453210),(0xffbbcdeb3862d4941cc520c57b56939460f73420,0x8976543210)] hints908 0x300030c5600d5061305a5002200120234003300121c750074035608e516030427001204e60fd4024408e51b4303f70012034401b3002200620061000300030012003300220da200b30033001202d3006100030ef80693019725c518f43f372764481801e4432804033e230693004705f40f23024437c4135300470182288343063767076612f70414503807050d8610233a85092405e41f13158607a407f5135303f7009405740053013301a224330a730047092402c4026306e4004701a20d8607e61c9509a509d6019700221a9531e3035608e501630047158607a408e50163042702c6004701a205e406240293072316d401970133002202d303210003000302340033001212f7009408d609d71f38285806030ed6015500121a77026606640a6723b82bc80275083400e30012061300d50022001200610003000300b302d300b302d300a100247e6600d701a400677ea56ca2021102d80067000301b300220012001200610eb705050053002201061d23004701720094071400530022007408430047017203210140 198 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal55 : ¬ fitsRows (hostAt hosts5 55).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda959c65073dac5a54831ca320820,0x9876541032),(0xffbbcdeb3862d4941cc520c57b56939460f73420,0x8976543210)] hints908 0x300030a1600b5129305a50022001207940053041401060115001202340254008304970807047515f414c706a601e405b70807047515f414c706a601e404030012062401b3049701e4049707140d73002200620061000300120da200b30033001202d30061000318440a730d552bb30214077303972c460e3504031004040315440d760dd709d40cd82357235700e3013301a209d402b41f1306e406e408270d730062103607050d8615063a85049700f410b70464005301a2474350a436f70ef613782c672c67015502c60cf407b7092405940263158607a408e513530047013301a209c50ae703c605f406a300b505e4046402930003002200030321000300120da200b300b302d3006105571b33004702441146010607730047100402b4040301a202c402c40d67069300471ff321651366055712f50a2359240a23055701a203560dc4007413d5004702c602c6004719240a230e1405571dd8004711d701a210362303070510231c95072316d41b5316d40c770c771308055701a20321000300030b9401c300330022088608c600b50012048405740053001200d500220061129302e50eb737d715f4005300220b07009436f70ef6137837070ed62cb7015501720dd702660dd709d40cd82e2708341a1700e301720484029300220eb7049707140053002203210140 246 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal56 : ¬ fitsRows (hostAt hosts5 56).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb389460f75ed5a4da73148362d4940801,0x9867543210),(0xffbbcdeb3862d4941cc520c57b56939460f73420,0x8976543210)] hints908 0x30003023400330012097600d5094305a5002200121b6503e30074396603e35e583953024408e5160303f700122fa422c3010613d631f82f2522855ad41b3308e51b43042718680b570022034401b31f780aa700c200620061000300030234003300121b6503e30074396603e35e583953024408e5160303f70012097600d5094305a5002200122fa422c3010613d631f82f2522855ad41b3308e51b43042718680b570022034401b31f780aa700c20062006100030003001207c40033002200d5000300120033001202d30061000312030ba6021418440a73019738360475074425c518143c1601e43f6506a601e4040305f40f23024400473e23024404550047018241940d0315e62883251608d44eb301f70414070514e823d608270fa40d2400530d8616d645644523015509240464005301a21a9524330356004715a81d3407b70074004701a212d60c4600b5098306e40557002231e3035608430047092416c60924155500e30106004701a20d86050600b525f502c6055700220321000307c400330022001200d5000300120033001202d30061000308d44eb301f7041441940d0315e628832516070514e823d608270fa40d2400530d86452316d64564015509240464005301a23c1601e43f6506a601e438360475074425c51814040312030ba6021418440a73019705f40f23024400473e23024404550047018215a81d3407b71a952433035600470074004701a212d60c4600b5098306e4055700220924155516c6092400e331e30356084300470106004701a20d86050600b525f502c60557002203214ee1238312720cc1238312720cc100a735e4009400530022009435e4005300223f0603e300742da413534ac413532ff701723f0603e300744ac413532da413532ff7017203210140 329 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal57 : ¬ fitsRows (hostAt hosts5 57).toFinset :=
  terminal_reject _ (by decide) 0x110 3 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal58 : ¬ fitsRows (hostAt hosts5 58).toFinset :=
  terminal_reject _ (by decide) 0x31310 5 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal59 : ¬ fitsRows (hostAt hosts5 59).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f8398d5a927418a320820,0x9876541032),(0xffbbcdeb38bdab49ca2d62e0f728a41892839801,0x9867543210)] hints908 0x3000300a1017201720381000303810140 9 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal60 : ¬ fitsRows (hostAt hosts5 60).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab4525073148314e5183dcd62c20,0x8976543210)] hints908 0x3002201b300c2001202e300a1000300120033001200b30033001200b300a107c4003300220253146301150d1401c30182061300d50062006202540564008307c40d140083018205940033102343730115018204b1000300030003000300b3001200a10003002200120d670d6700a100a10140 58 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal61 : ¬ fitsRows (hostAt hosts5 61).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd96a4a0e629062ad2728c1ee6b020,0x8976543210)] hints908 0x307940794005300120a160a1600b505a500c212f704140f060f870d0306f60155017214c706a601e406440807047503b400e3147305250172091409c303810003000300120da200b300b30033001200b302d300a10c7710c31f270dd709d40aa805640a5400e30dd709d40aa80564518400e315741574040301a2055706e406e4004706e406e4004702b401c301a206931ac7345612c50053006236f70ef60aa810861246015502c602c600471dd8004707b701a218f4134300b5006225440266307507441814040302c602c600471dd8004731c60397018218062173070510230525082712a40397018204b10003000300a1093409340024093400030003000300b3001200a1000343e419b31ca5002205f4069300741a631d2305d70172045610c301060843084305d7017218f40293002219b30022038100b3001200a100120012001200a10140 165 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal62 : ¬ fitsRows (hostAt hosts5 62).toFinset :=
  terminal_reject _ (by decide) 0x113113333330 12 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal63 : ¬ fitsRows (hostAt hosts5 63).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49a507314831065183dcd62d40,0x8976543210)] hints908 0x141300d504a201c300c2091404a3003300c204a1000300a1000300a13f821751006830d400a344c400a3000700030003000300a100030140 28 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal64 : ¬ fitsRows (hostAt hosts5 64).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49a507314831065183dcd62d40,0x8976543210)] hints908 0xd504a2003300c201c300c2091404a3141304a1000300a13f821751006844c400a330d400a300070003000300030003000300a100a10140 28 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal65 : ¬ fitsRows (hostAt hosts5 65).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bad4941cc520c41b56939460f73580,0x8976543210)] hints908 0x30f6704143df7061300d5061300d5246804142427061305a500220012208706a607c4080704750234003312f704142427061305a500120234003300120b1602840b160b1601150012034403440344034400830c641af3171500121a7806a601e40807047503b401b314c706a601e40807047503b401b304066295089300c20061000300030012003300220033001200330012003300120061000325c52c842e57276420f80eb70403071415550e45005300940094009409c50094137835c7204677c32d573b7407052e57276413c514f40eb70cd814d301a2288334c64a9707662c98181707050d8610230bc5158607a408e5135303f707e61af302e501a205054ed71b970293092402c40d730133002202b4079402b40d73092402c4051306e4054400470b9402b4051301a20d860e3609c5006202660cd81b97307552753bb40403158607a408e50843042702c602440047158602140197018205160cd81b97047552651394040305e405740293122310230bc5158602140197018202d30321000300030012001201b300c201b300c2006100030003000307140033001200940de619d7015501720266020413a700e3017210d600d500220022032100030003001200120012006100120012001200610140 234 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal66 : ¬ fitsRows (hostAt hosts5 66).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bad4941cc520c41b56939460f73580,0x8976543210)] hints908 0x312f704140bf719d70a1602e5061300d50f060c5605a5002200121a7705160f5713a7079402930414010601150284097601151286128600d5001202340254008312f704140f060f870d0306f60155001206240033001202340234008314c706a601e406440807047503b400e3128612860f0617150012064406b401b30ea40ea400330ea40ea40644089300c200610003000300120da200b300330012003300120033001202d30061000300940094041409c509d413a713a704030dd709d420f80564056400e30dd709d40cd80564058400e3100405640403013301a209d402b402b40d7306e406e403f706e40544082702b401c301a20ef619d719d70705049700f410b703d40053006236f70ef62c9810861086015502c60cf40427158607a408e5135300473224042701a20ae703c653740a6300b5013300224e8802661115063409566257040302c60cf407b7158607a408e50843004718680197018210360a16070510230525516603f71f7801970182000303210003000300a109340934002409340003000300030012001201b3001202e300610003009418f40053009407140053002227f5007427f500741d231d2300470172045602237be40223084308430047017207e50505005300220b560505005300220321001200120012006100120012001200610140 246 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal67 : ¬ fitsRows (hostAt hosts5 67).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d49c65073dac5a548394c410c20,0x9876541032),(0xffbbcdeb389ca30bdab47b9ac398a45a92818820,0x9854763210),(0xffbbcdeb2c5a928398a418838bdab49ca307b9a0,0x8976543210)] hints908 0x3121712173ec7026601b304140106011504364428476713b600d50022001202340254008304970807047515f414c706a601e40403002207c43ac80c370ac400333ac804970497139404030022006200610003000300120da200b30033002202d300612c460e35008309d409d414d3013305f4069302440436043637930047100402b414d301a209d409d41f1306e406e4082705e41f1300620ef60ef6170509a5136609a51366055709a513665de30ca411d701a200031a950a730356044404442005004702c60cf407b707230e1407230e1405570003158607a407f5016300471a63042701a2103602c6170510231c9507230e1407230e140c77000306a503f7068447f30d040163004701a203210003000300330022104805e405740574036702040033001200d500220012006107e5005305b700f40053002210480c3709d40dd702662e4704f42e4704f4036702040be8008300120e450053002205b700f40053002200610140 181 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal68 : ¬ fitsRows (hostAt hosts5 68).toFinset :=
  terminal_reject _ (by decide) 0x32313231333310 14 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal69 : ¬ fitsRows (hostAt hosts5 69).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173d6a6b127414c209060,0x9876542310),(0xffbbcdeb38bdab49a507314831065183dcd62d40,0x8976543210)] hints908 0x3300c200c2006218d304a10003000300030003000300a100a10140 14 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal70 : ¬ fitsRows (hostAt hosts5 70).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca307b5cb6292831c8510c01,0x9876543201),(0xffbbcdeb38bdab49ca2f8316e6a909290e608062,0x9876542310),(0xffbbcdeb38bdab49c94941cc52460f7358b18820,0x8976543210)] hints908 0x3000300031413141304a10140 7 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal71 : ¬ fitsRows (hostAt hosts5 71).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173d8d5a90931c8510c01,0x9876543201),(0xffbbcdeb38bdab45a928398a49ca307b9ac18820,0x8976543210)] hints908 0x300121b7500a1000300a112510934093400030003000300b300b300a1003300c20012002200a100b3001200a10140 24 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal72 : ¬ fitsRows (hostAt hosts5 72).toFinset :=
  terminal_reject _ (by decide) 0x21211888733330 14 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal73 : ¬ fitsRows (hostAt hosts5 73).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e1173d8d5a90931c8510c01,0x9876543201),(0xffbbcdeb38bd96a4a0e629062ad2728c1ee6b020,0x8976543210)] hints908 0x3061305a500d500c2079454d504840053017204c401b3001203440f440033017200330644089300c203810003000300a109340934093400030003000300b300b300a114441f81006309a66244006322430ce1346400680a05006300070012001201b300c200a10003003300120012001200a100120012001200a10140 63 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal74 : ¬ fitsRows (hostAt hosts5 74).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f8396a6b1274186229001,0x9876542310),(0xffbbcdeb38bdab49c928398a418a307b9ac5a820,0x8976543210)] hints908 0x14131413141304a100030003000300030140 9 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal75 : ¬ fitsRows (hostAt hosts5 75).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a4a116b1ee5a54831c6229001,0x9876542310),(0xffbbcdeb38bd96a4a0e629062ad2728c1ee6b020,0x8976543210)] hints908 0x300d500c20c560f870d0321b60f6704140115017200330644089300c202340807047514f4208706a602540083017203810003000300a109340934002400030003000300b300b300a1715663040063264548223464006872c612c400630a0500630007000300120012001200a100b300b300a1009419b300220106084305d701720074084305d70172009419b3002203810140 74 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal76 : ¬ fitsRows (hostAt hosts5 76).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd96a4a0e629062ad2728c1ee6b020,0x8976543210)] hints908 0x304c600d505a500c20f060f870d0306f62468041401550172009400330012001206440807047503b41a7806a601e400e3147305250172091409c303210003000300a10934093400240934000300030003000300b300b300b302d300a114446a2646511a0500636b22652100686c96346400687d326fd1539634640068228382757fe15396346412c800070003001200120033001202e300a1000300940033001204e600747ef800740843347701726cf50074324801061d2334b70172061300d500220022038100b3001200a100120012001200a10140 108 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal77 : ¬ fitsRows (hostAt hosts5 77).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdaaa4a0e6290620d2728c1ee6b160,0x8976543210)] hints908 0x3061300d500220012001202540033002245d309430115056407c4003301820234023400830754003301820ea40ea4003307540033018203210003001200330012003300c200330012003300c200a1000307c4003300220e0300d5002200220253147301150d1401c3017206b4062400830754073400830182062400331b0329f30115018203810003000300030012001201b300c202e300a100030022001201b300c201b300c200a1000300a10140 88 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal78 : ¬ fitsRows (hostAt hosts5 78).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49a507314831065183dcd62d40,0x8976543210)] hints908 0x4a200c20644003300c20644003300c204a1000300a102d40064006400640003000300030003000300030140 22 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal79 : ¬ fitsRows (hostAt hosts5 79).toFinset :=
  terminal_reject _ (by decide) 0x332133213333110 15 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal80 : ¬ fitsRows (hostAt hosts5 80).toFinset :=
  terminal_reject _ (by decide) 0x113113333330 12 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal81 : ¬ fitsRows (hostAt hosts5 81).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb3862d4941cc520c57b56939460f73420,0x8976543210)] hints908 0x3000304c6061305a504c6097600b5097600d5002200121a480f870d030307213608d7041424061e57070500740f337d1833d30244164711b61cd600d5002219e808070475049715f4209706a601e424941e07040302340254008300120094062401b30012009402340053010603a55f5858b416470d340af601151cd6026609761715002202340033062407d4003307d404c40234089300120062006100030003001200d500220da200b300d500120033001202d30061000318440a7318440a7318440a73068301970f23007402440244004705f40f2304360d4400740b350047076812171996036701e404030768100413e701e4040301824865010603560356004715a804e60074004706c4046400e30924046400e301a205e4046402930d86050600b5186703c61fc7050600b500621a9531e30444178601060783004714e83c96007400472dc600740436022304270924143623c5073400e301a207e6050602e5088602e55cb403c61446094300b500220ab81007071405f410f307050c86050601550924046400532f0300740444022303f70484029301a20df810361927091607050d8605060155049700f40497046400530d8617645cc309e6015516c600f423c50464005301a2032100030003000307c4058408930033002200d500d50003001200d50022003307540734008301330012003306b403440083001209b300610094055808c6059701550fa40fa40d2400536df7091602c637071036070513787fd442e3091677b4161311e708d60bf70705393503e307a4044417661766068303f7057400940094005301a202660be80574031700e30106010600470a830223004704640464092400e301a212d612d60c4600b5049702c4049702c40293002274e701e402b42e27100404033cb40544004728f8021405440197007402440843004701a20cd817a642e501e47a1573d40ec706640f5704030fc5183400476aa80ba60214183401973b151da307a4024406830047018226a307a404361c041c0411350427050605060d86015501060356045500477035152403561135004701a208c604c604c600b514b70e360fb70e3602e50022032100030003023401c3003300225a230d342206122300b5001200d5094305a500220e560ac40a050204005328240b570022034401b32a960aa70012006107e51f661e24005314b710d63fa710d600b50ff40094005300220b07028470a632f36894137822d344580155017210f305f4147300b50a730197002204970714168707140053002200c203770b4605842b7548d44ec60cd804e564f800e30d44019701a20c4604c600b5217501971786019700c20321001200120033002201b3001200c2006100940033001204842ba639c3263406571f383fc327380115017211967c751d8403a723b853d50ed800830172061300d50022002203210140 522 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal82 : ¬ fitsRows (hostAt hosts5 82).toFinset :=
  terminal_reject _ (by decide) 0x323132313331310 15 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal83 : ¬ fitsRows (hostAt hosts5 83).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca3073dac52d2831ca410c20,0x9876541032),(0xffbbcdeb38bdab49ca306394f5b5282184719420,0x9876103254),(0xffbbcdeb38bdab49ca307b16e6a9283906628820,0x9876325410),(0xffbbcdeb38bdab49ca28398a4188307b9ac5a920,0x8976543210)] hints908 0x301720381000303810140 6 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal84 : ¬ fitsRows (hostAt hosts5 84).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d494e3073dac5a54831ca410c20,0x9876541032),(0xffbbcdeb2c5a928398a418838bdab49ca307b9a0,0x8976543210)] hints908 0x3000301f7009410070115010653c700940f87060321b601150414246800946de7129300d50022001205b700f41217008313b60f8706030f87060306f6041424680094246800940115002202544117031600f40807027514f400830ac4080702750807027503b403444117031603444117031603440083049708070475139414c706a601e405b708070475139414c706a601e4040300220ea4411703160ea40807027506b4003314c706a601e4049700f408e550f702930022006200610003000300120da200b30033002202d300610003009400941c95100414d305f4069305f406930436024437c40163004725c518f4202727640cd80eb70083013301a209d402b41f1306e406e4004702b405e402630062103617050d8615063a8509a5136609a51366055701a21a950a7304560a73044458c407f50163004702c602c60047092405940263158607a407f501630047158607a407f501630427013301a2288343065b07076613781817011502c610233a8507230e1407230e140557158607a407f5016303f705e405740293000301a20003032100030003001200220da200b300b302d302d300a1570300471b33055705f40a230436010637c40163004705f40a230436043637c40163004701a21b33004706e406e4004706e406e400470062570305571ff321651366055709a5136624b30074055701a204560a230444007407f50163004702c60074004719240a230e1405571dd800472168004701a204560a230444044407f50163004702c602c6004707230e1407230e140557671800473648004701a203210003000306b40033002201f7009410970d861f385b07086601550012478800f42247092423b8202704f400e300120c5600d5002200120061110600f40505005305b700f405b700f400530022104829d509d4202702662e4704f42e4704f4036702041196008300120dd7026606640a67036702040266327708341a1700830012009407140053002205b700f405b700f40053002200610140 369 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal85 : ¬ fitsRows (hostAt hosts5 85).toFinset :=
  terminal_reject _ (by decide) 0x3130 4 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal86 : ¬ fitsRows (hostAt hosts5 86).toFinset :=
  terminal_reject _ (by decide) 0x44344331330 11 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal87 : ¬ fitsRows (hostAt hosts5 87).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e2d62e0f7254820c4731401,0x9876453210),(0xffbbcdeb38bdab4525073148314e5183dcd62c20,0x8976543210)] hints908 0x300120012003300c202e300a100030003000300b300b300a10a0500630a0500630007000300120012003300c202e300a1000300a10140 28 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal88 : ¬ fitsRows (hostAt hosts5 88).toFinset :=
  terminal_reject _ (by decide) 0x233123313133310 15 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal89 : ¬ fitsRows (hostAt hosts5 89).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bad4941cc520c41b56939460f73580,0x8976543210)] hints908 0x3007410c300740cc70414061300d50f06246804140f870d0306f601550022007410e501060cc70ab804142468041400d50976097601150284128600d5001207680ea403670ea400330f060c5605a50012059403440033001206441a7806a601e40807047503b400e3023402340083128612860f06171500120ea40ea40033064406b401b30ea40ea40644089300c200610003000300030003001200b3003300120033001200b302d3006106930c771b331f2705f40a230f760723152440a82ae4192413531ac718f4155507e500531378002722d30ab8006707053ab6002722d34ea835c7070500621b3311d706e416d4004706e40544004716d40544004701a206931ac7124809d63a5700620456069351e80dc447c50dc408e501631f2702c609d600473be800472a08004701a2050534f407e50293124816d42c4700620cd800277ed4076800670403007402440047173800471fb60197018225440027805442681b97040309d6183400472a08004718340197018204b10003000300a10934093400240934000300030012001201b3001201b300c200610003000300940033001227f500740cf41d2334b7017204e600740f160843347701720e0300d5002200220321001200120012006100120012001200610140 236 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal90 : ¬ fitsRows (hostAt hosts5 90).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c6507b5cb629093988510c01,0x9876543201),(0xffbbcdeb38bdab4525073148314e5183dcd62c20,0x8976543210)] hints908 0x3061300d5017200d5018202540033017200b303810003000300b300b300a154f20b2100631e01006300070003000300b300b300a10022001201b300c200a10140 33 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal91 : ¬ fitsRows (hostAt hosts5 91).toFinset :=
  terminal_reject _ (by decide) 0x3313130 7 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal92 : ¬ fitsRows (hostAt hosts5 92).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49a507314831065183dcd62d40,0x8976543210)] hints908 0xd5018220e400b300330033018200d504a220e400b300b304b1000300030003000300030003000300a10140 22 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal93 : ¬ fitsRows (hostAt hosts5 93).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bad4941cc520c41b56939460f73580,0x8976543210)] hints908 0x3121712170cb805b700f4040301060f6704140f6704140f870d030f870d0321b601150f06246804140f870d0306f601550012100710072c9812f7041407050c560ab82d57041401150976097601150284128600d500120254208706a60254208706a60254080704750807047514f4008302340768036700f4008312f704140f060f870d0306f601550012001206441a7806a601e40807047503b400e302340234008314c706a601e406440807047503b400e3128612860f06171500120ea40ea400330ea40ea40644089300c20061000300030003000300120da200b300b30033001200b302d3006106930c771b331f2705f40a230f760723152440a81524192413531ac707141555155500533ab60094307315e6251607053ab6009422d34ea835c7070500621b3311d706e406e4004706e406e4004706e40d94004701a206931ac712482b8406833a5700620456069351e80dc447c50dc408e501631f2702c6007400471dd800471738004701a205051b971b97029312481b5316d42c47006225440266307507441814040302c6007400471dd800471fb6019701822544026604e542681b97040302c6183400473be8004718340197018204b10003000300a10934093400240934000300030003001200120033001202e300610003009418f40053009418f40053001227f5007400741d231d230047017204e600740106084308430047017218f40094005300223aa60505005300220321001200120012006100120012001200610140 278 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal94 : ¬ fitsRows (hostAt hosts5 94).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb2c5a928398a418838bdab49ca307b9a0,0x8976543210)] hints908 0x300031a4808d704140f870d030307213624061e57070500740f335f4800740cc700740f332fc84c830d441647055816a30c6417c30d342206094300d5002222d3439812b30657144700b5030710d60fb710d600b5002219e8209706a601e408070475049715f424941e0704030234023400830234023400832607236400e612e504f42788008300223fe4455836b503a7047700530768051604752574036707c400330e26737309642d67041408c602e50022010603a55f8801060cc7097609760115111549440956247705160794066403a702930ab8299602842206122331770284061300d5041428c721b613c801150022012707140367071400530022010603a55f5858b416470af60d3401150e260475074417a61ea513840574029307682994133604751ba403670ff40505003319631c750214576861887e5339442a760683019700220be81a5504062a5500e6319411b5003300e602a515c4040615b6047501e412e509f503b400e30234169714f425b8008361930ba6021447a884687f4302140f230197002200620061000300030003000300940033002204c600d5002200120ad600d502340ad6011500030012033400330964096401150003001206b40334008306b403340083001209b3006100030fb709160fb70916140329e808d6059707055a6809162f5328b4091633a41c430e67212608d60bf707050094055808c6059701550fa40fa40d240053098503e300741766098503e30074176608e5160303f700940094057400530022036701e4036701e41c540db806640317040328f802141a155ea302140197007402440047007402440998004700221fe801e416e5110601e427e613c505b7139406640f5704037cb80ba6021420730214019726b50074024400473b1503e30074024409980047002202660be80574031700e30106035600475cf42433035600470464046409d400e3002212d612d60c4600b538f4068401637db3007423270022343340e401061c0485841ee301061c0408e5016304270106035609980047284540e40106035609980047050605060ef60155002204c604c608c600b538f40684016303e3007423270022006100030003000300330033002200d516a30c64122305a500220012006216a30d342206122319f6028400d500121a5500e60a05020406a604640033024406830397002200d50e5606241cc501b303560f230397002200610003275500f427551e240053030703c6030703c600b500941a2400530022490303c64903272600b5223301970022049700f4168700f40053002200c20b0702844de632f306d40b07028416370e7316b31a3605580115001203770b46101433e4389505c61187020410570c050a0508540be8008302440197002204c6211600b53e55019703560197002200610003001200d500220ac40033000300120ac40033002202d3003300220061000305f40693007402440074004712171004119614d305f4069304360d4400740b3500471c544f48066412170eb70eb700830768121711960eb714d306930693043602441135004701a21a950a73010603560106004715a804e6007400470cf463a80a23042706c4046400e300740074055701a210071036048417052cc61925007403f715a8166600740047399300744053007400470ae7638614b709e6015501a204560a730444178601060783004714e80ba6007400472ac447240a2304270d960074043602230427098503e3007404360223055701a2140350e808d605973b673b6701150f160ba6007403f714e8072307a400470c46050605a5098503e300741cd602230fe701a20ab81007048411e717050c860506015503e3007403e3007400472f0300740444022303f70d24046401b301a20693069304443e8406830047010601060557049735e40497073400e326c322d40106044406830557343322d40106582406830cb701a203210012001201b3002201b3002200c200610094003300220a3403a7119653d552481e380083017209b30e0300d5002200121916065704843fc327381de801150133017203210140 745 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal95 : ¬ fitsRows (hostAt hosts5 95).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdaaa4a0e6290620d2728c1ee6b160,0x8976543210)] hints908 0x3061300d500120254003300120022102300d500d5018207c40033182309430115018200330234023400830182038100030003000300120033001200b300b30033001200a1113511461987113504361987006206830dc419870062068304441987006212a412a4004712a412a40047018205440d940047054406e4004701820d442df400470d4400740047018204b10003000300030012001202e3003300c200a100030022001201b300c201b300c200a100a100030140 92 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal96 : ¬ fitsRows (hostAt hosts5 96).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb2c5a928398a418838bdab49ca307b9a0,0x8976543210)] hints908 0x300031a4808d704140f870d030307212624061e5707050768327714f43d9800f419e800e3857503e30074396601d32fc8395302441b6503e30074396603e32fc83953024408e5160303f71cd611b600d500223dc64398144708070e730c6400b5030710d60fb710d600b5002219e8209706a601e4080704750497139424941e0704030cb8169714f40254008312f7028411230e1609640b07041428580e730866011500223fe4455804772f685984040600530768051604751ba403670ea4003316270c6423e70414053303c602e500220ab84aa70ed608d7009413c801552d2828c721b60106011510954a44095613e713360c37023430a50094003301f702840ab801f7028428c721b6011528c70c561286311800d50022168707140367071400530022832422c3010613d631f82f2522854a341a632fa41db3010613d631f82f2522854a341a6308e50163042714c70b4601e40e260475074417a61ea513842bc80c0504f40083118700f40768036700f4169714f400834a5633f50214186861882fb35d542a7606834f07002207d40624003332b7040615b6047501e409f500f40293169706b40ea429880033098533c302141f785e0884836af602140f234e97002200620061000300030003000306b4003300220c5600d5002200120c560ad601150ad600d50003001206b40334008307c403340083013300120334003309640284011500120003006100037648091601f7041441940d0315e64aa70a1607055a68091601f7041459482e330e67212608d60bf707050094055808c6059701550fa40fa40d240053393503e3007417662dc60074176608e5160303f7009400940574005300223d9801e43f6506a601e438360475074432770794040312036a680ba602141a1520b30214019736e5007402440047007402440998004700221fe801e420872ce601e44c781ae505b7139406640f57040312036a480ba6021480830214019726b50074024400470b2503e30074024409980047002202660be80574031700e304e60074035600474b8524330356004704640464046400e3002212d612d60c4600b55af4189408430bb300742327002226a300741c04407401061c0408e50163042701060356099800477eb515240356099800470506050605060155002204c604c608c600b50e840e84016337150106232700220061000300030003023400330022097600d5094305a50022001200621b6503e300742a9602f5160303f7001208b422c30106282402f51b43042728240b570022034401b32a960aa700220061000305b700f405b71e240053030703c6030703c600b500941a2400530022242710f300c7094300b5152401970022049700f4168700f40053002200c20b07028426d632f31b140b07028482870e735ca31a3607d40115001203770b4605841f0438951f961187020482670c05457508541b86008302440197002204c6211600b530e601970356019700c200610003001200d50003001207c40033000300120ac40033002202d30033002202d30061000305f40693007405f4069302440047076851841df714d305f40693043605f4069300740b35004738360475074425c518140eb73f6506a601e4008306930693043602440455004707681004121714d301a21a950a73010604560a730356004715a804e60074004715a81d3407b700740074004706c4046400e301a20ab8636619c7170515a823d6082715a835a800470d8609e601555d5307a47c4307a4055701a21a950a73044404560a7301060783004714e80ba60074004714e81d3407b70d9600740436022300470924143667850734143301a241940d0315e628832516181701f70414011514e823d6082714e8470800470c8616d668a4452319a549b705940464296801b301a20a730a7304443e84084300470106010600470924073400e32f03007404440223004706c43be643f41555143301a20ab810360bf717050c86050601556ea50a5655d50a5605570d861764799309e619a516c605b7062423c50464251801b301a20321001200c2001200c20033002200c201b3002200c200a1009404840053009404840053002211151095727440842bd45c3545361196130629a52375085423750f9473950316020402660083017206c4009400530022110600f405050053002202662ad823750f94381702041196145504f4145504f4008301a203210140 799 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal97 : ¬ fitsRows (hostAt hosts5 97).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdaaa4a0e6290620d2728c1ee6b160,0x8976543210)] hints908 0x3061300d50012025400330012002218230943011507c40033018202340234008300330182102300d500d50182038100030003000300120033001200b30033001200b300a1113511461987113504361987006206830dc4198700620683044419870062054406e4004705440d94004701820d44007400470d442df40047018212a412a4004712a412a40047018204b100030003000300120012003300c202e300a100030022001201b300c201b300c200a1000300a10140 92 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal98 : ¬ fitsRows (hostAt hosts5 98).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca3073d8d52d28394c320440,0x9876543201),(0xffbbcdeb38bdab49a507314831065183dcd62d40,0x8976543210)] hints908 0xb300d5018220b2141300d504a220e400b304b10003000300030003000300a10140 17 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal99 : ¬ fitsRows (hostAt hosts5 99).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f839ac52d27418a410c20,0x9876325410),(0xffbbcdeb38bdab49ca28398a4188307b9ac5a920,0x8976543210)] hints908 0x301720172038103810003038100030140 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal100 : ¬ fitsRows (hostAt hosts5 100).toFinset :=
  terminal_reject _ (by decide) 0x33110 5 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal101 : ¬ fitsRows (hostAt hosts5 101).toFinset :=
  terminal_reject _ (by decide) 0x110 3 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal102 : ¬ fitsRows (hostAt hosts5 102).toFinset :=
  terminal_reject _ (by decide) 0x31310 5 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal103 : ¬ fitsRows (hostAt hosts5 103).toFinset :=
  terminal_reject _ (by decide) 0x113310 6 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal104 : ¬ fitsRows (hostAt hosts5 104).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38ad2f69bdcd9460941d8b50c4131480,0x9876453210)] hints908 0x300030c5600d50022001206b4003300220b1602840b16011502340284023401150003001203440344034400830b64003300030012034403440344008303340033001200030061000318a549370714202727640cd8790648f701e404030074024408270b2507230fd4024407f51b430047002205b73a071ae51394066412170cd839f72ce601e4040321750244082703a503e30fd4024408e51353344700220cd839f706a601e42b17047505b713940664121704030cd80266165505b7139406641217040307d41b030a1651b40155098503e30fd4024404e6007407f5135303f7002206e46f4407b70a7327e307b71b8643a5079421a600e302b40f9405e400e30022002233651ef30106035608e50163004703a51ef30106035608e5016320c7413416f301061c041c75007408e50163042702c615d607e601550022002200620061000300030c5600d5061305a50022001206b4003300220074035609980427001217b402440ec803f70012034401b30022006100033df7129319273b8300b508f80197002205b700f405b700f40053002205b700f405b71e24005300c706130e6703c600b500941a240053002200740356099800470012010602440998004702440197002208f8019704c6211600b50356019700c2006100030003205703c60e670c4600b50094023400530022047705b700f4005300220ee700f405b70d240053002214470e6703c600b500941a24005300221038560800f41a170367174400e3001212180b0700942cb701f70284015500120ff4062401b302b6071405050053002200610003000305160085142100a302d4006800680063000700120012001200c20012006100940094009409d709d7011501720557002200940484005300220c7700940484005300220266026602660a670a67008301a203210140 336 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal105 : ¬ fitsRows (hostAt hosts5 105).toFinset :=
  terminal_reject _ (by decide) 0x3333110 7 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal106 : ¬ fitsRows (hostAt hosts5 106).toFinset :=
  terminal_reject _ (by decide) 0x33310 5 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal107 : ¬ fitsRows (hostAt hosts5 107).toFinset :=
  terminal_reject _ (by decide) 0x1 1 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal108 : ¬ fitsRows (hostAt hosts5 108).toFinset :=
  terminal_reject _ (by decide) 0x110 3 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal109 : ¬ fitsRows (hostAt hosts5 109).toFinset :=
  terminal_reject _ (by decide) 0x11130 5 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal110 : ¬ fitsRows (hostAt hosts5 110).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38a4e57b55cd6460f4a16a3906628801,0x9876453210),(0xffbbcdeb388c1ee6b2f6ad2723148312d4941c20,0x9867543210)] hints908 0x275506241f6600f40094005300220e450a66009406c400530022035600470c96004700120244004702440047001205440047054400470012006100030003000317e30214054422130397058402b400e30fa401c300940033013300220af604140155120339a80ba602140d5520730214221303970094003307c40033002204c600d50293002212d600d5012703d4036703d400530022043602e502e5002204c600d5012703d4036703d400530003002200030061000300030b280aa70b280aa7001232580c640f6706d400d51c167c15115403a70bd803d40053013300220bd805640677025400330094003307d40033002257180b5704c600d503560197002225e412b306570ce8008600b5002257180b571cd600d50244019730460e3605250022041402c401c3107202d300610003010605a50012010600d500220254003300940033002205583506122316a306d400d500120be80a0502041a5505c60033024401970012025401b304c600d50356019700220061000305250012000300120254003300220da209c3006100030d86050600b5029300620c960fc500472ac42f43007404270985072307a4004701a205440a8300470a7306830197100402b400e329b702b60834058400e301a20924046400532cc6072307a403f7103602c6015504840293241500740436082701a202e5088602e5002208b416f30a56004729773b1651040af601554bb40c23044407b701a20321001200c2001201b300220061167703d4179803d40053017202d301c30182001205e4046400530133017203210140 290 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal111 : ¬ fitsRows (hostAt hosts5 111).toFinset :=
  terminal_reject _ (by decide) 0x3130 4 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal112 : ¬ fitsRows (hostAt hosts5 112).toFinset :=
  terminal_reject _ (by decide) 0x33144344330 11 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal113 : ¬ fitsRows (hostAt hosts5 113).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab48c2727b16e6a8e64a06229001,0x9876453210),(0xffbbcdeb38bdab47358b54e5183ca41892839820,0x9867543210)] hints908 0x30022003300c2003300c201c3001200a10003003300c20022003300c201c3001200a100030012001202e301b300c200a100030012001202e301b300c200a100a100030140 35 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal114 : ¬ fitsRows (hostAt hosts5 114).toFinset :=
  terminal_reject _ (by decide) 0x1 1 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal115 : ¬ fitsRows (hostAt hosts5 115).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a465073d8d5a547414c320801,0x9876542310),(0xffbbcdeb38bdaaf7358ba4e51818a41a92838820,0x9867543210)] hints908 0x30012003300c2003300c2003300c200a100030594003353031b030bc50182061300d50022006206c4003300220d840714051301720381000300120012001200120061000300120012001200a10003001201b300c2002200a1000300120012001200a10140 51 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal116 : ¬ fitsRows (hostAt hosts5 116).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda9594e2f835cb62547414c320801,0x9876542310)] hints908 0x30c8600d500120012059400330074007405d700c204f400330d440d4405d700c206c40033001206e456e405d70a830a8305d7001200a10003059400330074007405d700c204f400330d440d4405d700c20c8600d50012001206c40033001206e456e405d70a830a8305d7001200a100030003001200120012001200610003001201b300c201b300c2002200610003001200120012001200610003001201b300c201b300c200220061000300940254005300120094025400530012001207c4023400330094025400530022001207c402340033009402540053002200610140 112 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal117 : ¬ fitsRows (hostAt hosts5 117).toFinset :=
  terminal_reject _ (by decide) 0x333310 6 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal118 : ¬ fitsRows (hostAt hosts5 118).toFinset :=
  terminal_reject _ (by decide) 0x331110 6 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal119 : ¬ fitsRows (hostAt hosts5 119).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab48c2727b16e6a547414c320801,0x9876542310),(0xffbbcdeb38bdaaf7358ba4e51818a41a92838820,0x9867543210)] hints908 0x30012003300120da209c3003300c204a300a1000300330564056400e3018209c3001209c500121086108601550182001203810003001200c2001200610003000300120012001200a11d230047018204a210c3004701a203210140 46 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal120 : ¬ fitsRows (hostAt hosts5 120).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab47358b54e5183cc52250718820,0x9867543210)] hints908 0x2234a300c234a300c218d3001234a300c200a10003064406440083064406440083018209c309c500c20f060f0601150182038100030012001200a1000300031b75001200a105e600b501724e57003300c210f4005301720d67038100c204a200c200a10140 51 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal121 : ¬ fitsRows (hostAt hosts5 121).toFinset :=
  terminal_reject _ (by decide) 0x331110 6 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal122 : ¬ fitsRows (hostAt hosts5 122).toFinset :=
  terminal_reject _ (by decide) 0x333331111110 12 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal123 : ¬ fitsRows (hostAt hosts5 123).toFinset :=
  terminal_reject _ (by decide) 0x331111110 9 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal124 : ¬ fitsRows (hostAt hosts5 124).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38a4e57b55cd6460f4a16a3906628801,0x9876453210),(0xffbbcdeb388c1ee6b2f6ad2723148312d4941c20,0x9867543210)] hints908 0x316c600f4009423c5062400530022009416c600f423c506240053002202440047024400470012024400470244004700120d4400470d440047001200610003000300031a1520730214120323f82a4615140683039706640f5709f50475085405161fe81384040300940574005302440f1603f7002205161fe8138406640f57047509f5085404031a1520730214120323f82a461514068303970094057400530f16024403f7002204c608c600b5002204c608c600b5002203560cf404270cf40356042700220061000300031e480aa7001200940ff4005300220e56025405050033009402340053002232380b5704c6097600b50356019700220244019716973554034403442de803440083001223b84d9754a636155bb7095613f802750834008300120061000300031e480aa7001200940ff4005300220e5602540505003300940234005300220244019716973554034403442de803440083001232380b5704c6097600b503560197002223b84d9754a636155bb7095613f8027508340083001200610003001200c2001201b3002200610003001200c201b3002200120061172400b302d3172400b302d300a157a634d4006357a634d4006345e319424b710038093445e319424b710038093400070140 233 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal125 : ¬ fitsRows (hostAt hosts5 125).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38a4e57b55cd6460f4a16a3906628801,0x9876453210),(0xffbbcdeb388c1ee6b2f6ad2723148312d4941c20,0x9867543210)] hints908 0x3049706244b0700f40094005300220e4506c43646009400530022010600470356004700030012054400470a830047000300120244004702440047001209b3006100030003000317e3021436a40683039704f4071400e30fa40d240053062403440ac400e301330022086610d6015508130ba602142f1580931514068303970094057400535d4503e30fd4024403f7002210f308c600b5002212d60c4600b5002211b60b1613b6015560350ca403560427002202d30061000300031e480aa7001233160c64449700d51c164bf51d8403a70bd803d40053013300220e5605640b270033009402340053002232380b5704c6097600b5094305a500222aa412b306570ce8008600b5002202c40d7300c2062401b3094309c5002202d3006100030012061300d500220254003300221f380f6702840f6706d40115001223b828770254161705c6008302440b57002203560aa700220061000300d50003001202d300120ac4003300220da200b302d30061000310f308c600b5029300621a9531e30a560047130858e811d724560074004701a205f40a8307a4004706933694019711e402b400e3069304360f23004701a2009405740053146852c80c7744f602c6015509050074043608270484029301a203e3007400470a730444077300472ee40c23044407b701a202e5088602e50022032101c300c2018201b3002200c200a11865010608e5016308e501632ff7017209b3009404840053002207e50e450053002203e300742da401634ac401632ff70133017203210140 284 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal126 : ¬ fitsRows (hostAt hosts5 126).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab48c2727b16e6a8e64a06229001,0x9876453210),(0xffbbcdeb38bdab47358b54e5183ca41892839820,0x9867543210)] hints908 0x30062003300c2003300c2003300c204a10003003300c20062003300c2003300c204a10003001200120012001200a10003001200120012001200a1000300a1000300a10140 35 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal127 : ¬ fitsRows (hostAt hosts5 127).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e3062d4f734e64a06229001,0x9876453210)] hints908 0x300d500c2003302b4089300c200330ac407540083018200d500d501720ac40754008300330182038101c30012003300c20022003300c2003300c200a100030003000301c30b8202e302e300a10012002211a300c211a300c200a100030012017220e400b300d500d5018220e400b303810140 58 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal128 : ¬ fitsRows (hostAt hosts5 128).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e3062d4f734e64a06229001,0x9876453210)] hints908 0x300d500c200330644089300c206b406b400830033018202540b94051301c3017200d5052501820381003300c2003300c20022003300c2003300c200a100030003000301c300c2001200a10012002201b300c20d6700a1000300120012003300c200b300a1000300a10140 54 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal129 : ¬ fitsRows (hostAt hosts5 129).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab28d27062d4f734e64a06229001,0x9876453210)] hints908 0x30e0300d50022002207c400330022062406b4008307340754008301821473025301150d1401c3017229f31b0301150624003301820381000300330012003300c2001200330012003300c200a10003000300030012001201b300c202e300a100030012002201b300c201b300c200a100030012061300d50022001202540033002202340234008307540033018245d309430115056407c400330182075400330ea40ea4003301820321000300a10140 88 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal130 : ¬ fitsRows (hostAt hosts5 130).toFinset :=
  terminal_reject _ (by decide) 0x221 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal131 : ¬ fitsRows (hostAt hosts5 131).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117b98d5a8e64a06229001,0x9876453210),(0xffbbcdeb38bdab49c9ac5aa307b8a41892839820,0x9867543210)] hints908 0x304a112c83003000718d5001200a10003000303810140 12 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal132 : ¬ fitsRows (hostAt hosts5 132).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e117b5cb6290931c8510c20,0x9876543201),(0xffbbcdeb38bdab48c2727b16e6a8e64a06229001,0x9876453210),(0xffbbcdeb38bdab47358b54e5183ca41892839820,0x9867543210)] hints908 0x30062003300c2003300c204a10003003300c20062003300c204a1000300120012001200a1000300120012001200a1000300a10140 27 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal133 : ¬ fitsRows (hostAt hosts5 133).toFinset :=
  terminal_reject _ (by decide) 0x110 3 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal134 : ¬ fitsRows (hostAt hosts5 134).toFinset :=
  terminal_reject _ (by decide) 0x11111333110 11 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal135 : ¬ fitsRows (hostAt hosts5 135).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173dab6254831ca320801,0x9876543201),(0xffbbcdeb38bdab49b58b5265183dc520d0730820,0x9867543210)] hints908 0x6201c300c2003300c2003300c204a1000300b309c300d5018200b303810003001200b300a10003000300c204a204a10140 25 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal136 : ¬ fitsRows (hostAt hosts5 136).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb388c1ee6b2f6ad2723148312d4941c20,0x9867543210)] hints908 0x30886088602e510b704644ae715f40924005300220af60ad601551ba40af601550022048404840293002213a70505067700f416c600f4005300220584058400e3059408340ac4008300220584058400e305840584239400830012006100030003000326b5021426b50214054436a401970fa4058401c305640564025400e310480b94036701e402b400e30133002202c402b401b306c401b3002212d60c4600d5067700f410b703d400530022108610860284015518c34d3502147e8515140b570cf402440427002204c4046400331496804302144c8302140aa7062403440033001219535c66074405f410f302c601550c8605a50f16035603f708c6041400d500220ae703c60c37008600b50003001202d300610003000303e3007403e30074019709980197010600d500221c164bf51d8403a71c161eb5115403a70bd8130803d400530ce816b30de631d412b30657080749530d3400b50133001205f4069374b4016301970266129305a5097600d500d500222aa412b306576cc412b306570ce80ce8008600b500220bd80a0502042285115403a75f782b4400e6005312e50754025400e6008300220998019704c4062401b300220234003311f707440d340d34011504143d843b830fc610f31715002202540033003304c44405028430a502840893002202d30061000300d5002202d30012025400330003001206b4003300120da200b302d30061000302c402b4029306c411a306c411a300220fc50a560c960a56004715a8166600740047245600740cf407b7098524b307a41d34055701a20a8307a4054407a400470683081312380ba6021405440683019729b73c7508344f680584058400e30e350b253b5402b400e3036701e42b170bf402b400e301a214e8072307a4004729777443511465a80af60af601550cf4043607b70cf4043611d701a20613061302e505060d8600b5046405e411a300220c861cb503e315240f16082702b3063344e602c601550f160444082704640924005301a20c861cb561d426a30a5623d6055705f402b316e71ce602c601550f1604440c77258878c700f4005301a203210003000300d5002200c200330b9401c3002213b600d500120ac4003302440b57002203560aa70012006118172db7214600b51da30e14019700220484029300220eb737d71e140053088602e500941a2400530022121813780b070284328845840155017210380cd8284705840475073400e30244019701a22b840223019704c60e5300b50356019700c20321001200c2001201b3002201b3001200c200611a551a551ad6496629a5020413063b3500f40be80033017209b30033001214570c3705e40574057400330133017200d50022002203210140 497 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal137 : ¬ fitsRows (hostAt hosts5 137).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab47358b54e5183ca41892839820,0x9867543210)] hints908 0x22003300c2003300c2003300c2003300c200a1000306440893003300c2052500d5018200d500c201c30b94025405130172003306b406b40083018203810003001200b30012003300c200a1000300a10003000301c300c2001200a1001200220d6701b300c200a100030140 54 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal138 : ¬ fitsRows (hostAt hosts5 138).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c9ac5aa307b8a41892839820,0x9867543210)] hints908 0xa14852175112c83003313200a30007141300b300a100030003000300a10140 16 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal139 : ¬ fitsRows (hostAt hosts5 139).toFinset :=
  terminal_reject _ (by decide) 0x31310 5 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal140 : ¬ fitsRows (hostAt hosts5 140).toFinset :=
  terminal_reject _ (by decide) 0x331323132313310 15 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal141 : ¬ fitsRows (hostAt hosts5 141).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb389460f75ed5a4da6290620b16a4a0e0,0x9867543210)] hints908 0x3009400330012277600d502340af60115001204c600d5002200120754003309640964011500120254058400830254058400830012006100031d440f330f160fe70fa40fa40ff400532e57083420f80564025400e304f402b400e349e70b94214802b400e30624009400940053002221e60cf40cf40cb71c750074035603f76eb308430047092401b3002212d612d60c4600b538f4068401634053007423270022036701e4036701e44ad5740409564d8777d46436040301f50a830244042728f802142f1580730214019701f50a8302440427002208660414015571b50244004784080ba602142073021401970c3705e405740be8029300225c970744310802c601550d8605a505330fc5035603f76e864b232c7408c6055802e5002208c604c604c600b538f40684016303e300742327002200610003000300940794005307d407940033055825f30c6400d50012030710d60fb710d600b504970094012700f40053002204c60a1600b507e6061305a512231223061305a500220497071404970714005300222607236400e612e504f4278800e300120bd8056406770254003305e4062401b32184062401b300221cd60a1600d505e40624257401b3092402c40d7304c60d3478270d862568052500220be8047503b4003300e602a515c420c615b61ae501e412e509f503b400e30094056475d70924434801c30022006200610003000300d500120012025401c30003001206b4003300120033002202d30061000307141036092407052cc604e6007403f702c40293029300740074082701a207141007103607052cc61925007403f7048402930094046400531867213614b709e6015501a2199610042716040319961217100404030a7318440a734be539b302140683068301976a1467b529b706640a6706a60584235700e3076829b72b17059409f5058413e7058400e301a22ac43c96007404272ac418940a2304276f243143297708d609d757f602842c670155098503e3007404360223004701a20e3602e5088602e5046405e40293002202e504c630f300b5046405e4029300220106010607b7049715f40497073400e30ab8297716e71506053308c6192708c60155815340e4010604440223004701a203210003000311c605a5001200120062023401c300330022122316a30d3400d500121cc50e560ac400330244429700120b7401b300d503564ef70022006100031817181700b5061305a500220e450a660094005300220eb70eb700530e0324270e0300b500941a24005300221b6503e300742233035622280047017261d45ea301063793024422280047024401970172056401b302b4048401b305440197002203210012001201c3002201b3001200c20061385700f428a802040053017209b302b401c3003300220ae703c60ce80de600b50003017200d5002203210140 519 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal142 : ¬ fitsRows (hostAt hosts5 142).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab47b9ac9ca30594831054941cc0,0x9867543210)] hints908 0x3001200b30033001200b30033001200a107c400330022059400331023437301150182061300d5006200620d1401c3025314630115018207c40d140083025405640083018204b10003002202e3001201b300c200a1000300a100030003001200b300a10003001200220d670d6700a100030140 58 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal143 : ¬ fitsRows (hostAt hosts5 143).toFinset :=
  terminal_reject _ (by decide) 0x221 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal144 : ¬ fitsRows (hostAt hosts5 144).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c9ac5aa307b8a41892839820,0x9867543210)] hints908 0xa112c8313200a3313200a3000700a100030003000304b100a103810140 15 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal145 : ¬ fitsRows (hostAt hosts5 145).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda0f73595a4e513148312d4941c20,0x9867543210)] hints908 0x30012003300220033001200330012003300120061000346040693069306934604019725c52c840644635800e353032a231b030bc544b52c840eb7064400e30182288334c60f065038015502c610231dc51c7507a408e513536267061305a501a200626624071402b4051302b402b410a302b420d410a3017274d334c63b670f06015510750c2308e508434ee71b0310231dc5017206c401b30012032100031af300d51af300d50022001200120234003300120012023400330012006100030003001200120012001200a100030094009409d70705017200470012026617440a670403017200470012001203810003000300120012001200a100120012001200a10140 130 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal146 : ¬ fitsRows (hostAt hosts5 146).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda0f73595a4e513148312d4941c20,0x9867543210)] hints908 0x300120da200b300330012003300120033001204a300a10003673605640406056405640d73623606440e3500e305640564056400e376e70834708801e4064400e3018209d402b402b410a306e406e405d702b420d410a30d7301720062108610861086015502c60cf405d71c7507a408e5135305d7018276860803074412f704140f060155312306131dc510750c2308e5084305d7017209c50012006203810003061300d5002200120414010601150172023402540083017200120234003300120321000300030003000301c30012001200a10094009409d709d707050172004705570022026650740a670a67040301720d670d67038100120012001200a100120012001200a10140 133 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal147 : ¬ fitsRows (hostAt hosts5 147).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38ad2f69bdcd9460a4b16820c4731401,0x9876453210)] hints908 0x300030b1600d50022001206b4003300120ac4003303440ac403440083002207540033034406b40344008300120b1602840b1601150b160284023401150022006100031586021446f801973f37276418a549370794838548f701e44818138404030b25072300745e836c3608e51b4304270074024400470022538602141218019706640f5709f53a07692513942f6845a601e41d6701e4040352d50ff4057462c600333e45024403f7002237670766196355a70a168493555709162d570414070505160cd806643587047537380854008326070744110601e413c515f419e8040300940094057400530094055802c609d70155002219745ec301065d03283408e5135303f719c60e0308c627a400d511230e1607442e931d041c4321361a4807050e3602c60155002204c604c608c600b516e802c43fb61eb5053403a700530133002206e40544004724330a73042702660be802b40a6700e302c402b400e3002227c80e3625e41ff3065700b5002202d30061000300030003061300d50022001200620033002200120344003300220061000352b74fb7129300b5113501970022009406c4005300225147325700f4005304c60c8600b500941a2400530022024401973793010602442228004701a20683019704c6211600b50356019700c2077300740356222800470172032100030003009407940053061300d50022009405e40053002204e60fd402440f762663007417b4077303f7001202b60254050500332184062401b3002204c60a1600b500941a240053002202340033002240d6007403561aa517f422c30106244613d50427001200610003001201b3002201b3001200c200120061000319744cf3010653e60074022303f70172097600d50022001202340033001202a60bb300741536730410c3042701a20321125105160516125100a3069300b2069300b20693069300b200b1719645e312710038093420b400687e9276c116d800c5006300070140 360 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal148 : ¬ fitsRows (hostAt hosts5 148).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcd6f37c5ab3a4a117b98d5a54831ca320820,0x9876541032),(0xffbbcc5edbd66b183e93939494358b20c4731401,0x9876453210),(0xffbbca4e5183ddbd6717b54e6290626b16a4a020,0x9867543210)] hints908 0x3000301f7009414980603030706f6011508b408a301061404360602f501630fe7067700f4049700f40053013300220377031601e413f80275012703b40083120323f81666021407730397612754352bd43f951f9639d70b46033409f510570c05085411870204215600830022204601d300741536581402f501630cb75f975b33109633031b141fd702844df349f801f721d401f702840234011504e6007402230998039700220ae703c61fc703c600b5012703d4036703d400530133002202d3006100030003120323f81666021407730397012713f8027503b40377031601e40083612754352bd43f951f9609f510570c05085439d70b4603341187020421560083002203071498060306f601f70094011508b408a301061404360602f501630fe7067700f4049700f40053013300225f975b33109633031b144df349f801f721d41fd7028401f7028402340115204601d300741536581402f501630cb704e6007409980223039700220ae703c61fc703c600b5036703d4012703d400530133002202d3006100030003030703c600b51d661ed51be401630b570133002201270807027503b40377031600f4008301f700941f482ba641b32634065741042bf32738011500220003012700f400530377031601e408070275012703b4008301f7028411230e1609640b07009416370e7325a6011500220537026621c8188639251d8403a702a5402436280083013303770b4600f40e260275074417a6225500f410570c051bb4008301270637027508540377031602040db80377031602040ee7063702750637027504f4053702660083002246e4384323850aa7002202d30061000301270807027503b40377031600f4008301f700941f482ba641b32634065741042bf32738011500220003030703c600b51d661ed51be401630b57013300220377031601e408070275012703b40083012700f4005301f7028411230e1609640b07009416370e7325a6011500220537026621c8188639251d8403a702a5402436280083013303770b4600f40e260275074417a6225500f410570c051bb400830db80377031602040127063702750854037703160204063702750ee70637027504f4053702660083002246e4384323850aa7002202d300610003000331b60d34053303c600b50003001202d331b60d34053303c600b50003001202d302b600f409f500f40053013308130a46021408130fd84b56151407730397000302a515c40956051609f5047503b415b6027504140083013302441d7601d30fd4077303f71ab30012000302b600f409f500f400530133051602a515c4095615b602750414047509f503b40083013308130a46021408130fd84b5615140773039700031d7601d30fd40773024403f71ab300120003035626750ca420050427013326750ca420050356042701330012000300a109850bb3268601d304d404e6007402f501630047204601d3007404e6007402f5016300470106019707230074019701330022204601d3007404e6007402f50163004709850bb3268601d304d404e6007402f501630047010601970723007401970133002203e302a601d304d404e6007407f501630047292408a3010627d6007407f50163004708b408a3010604440b3502a601d300740436078307f50163004730b8009408c608d609d7015559140ec70db814a704f4026600e300030022292408a3010627d6007407f50163004703e302a601d304d404e6007407f50163004702a601d300740436078308b408a3010604440b3507f501630047009430b808c608d609d701550db859140ec714a704f4026600e300030022007401970074019729680266057406640a6700e302662968057406640a6700e3002209a50106019709a501060197532611e70df818570866009401550df8532611e718570866009401550022000300610140 701 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal149 : ¬ fitsRows (hostAt hosts5 149).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38b5eb483dd3945494358b20c4731401,0x9876453210)] hints908 0x300030003000300d500220033064408930022028400d50b1602340115000300121724172400b3034406b400830033001209b300611bd41fb601975568092402b4741701e404030074024400473cb42a444778004701a205e61834019705b71c16500513941b970cd81946502501e404030fc518340047309503e307a42e0413080047018269e80d8602c65567091607050e6781745003212635c713781954502309160705009405580a1609d701550fa40fa40d24005303e307a4176657c6007407f5135303f7009400940574005301a206e4054400470a830223004702660be807940a6700e302c405e400e301a212d612d60c4600b509a712c609a70e3602e5002201066b962a0800475d251ef30a563d061308004718650a561c0404e6007408e5016304270e3607e6015501a206240ff4048401b315472c54154702c402930022032100030003000300d5129305a50022003306440893002205740484005300120344034400330012034401b30012006105f410f3147300b507730197002204970714168707140053002200c21f6600f41085005314b710d63fa710d600b500940ff4005300220c2361c507230074035608e516030047017237933a345fb30106024408e5135300470d44019701a213d5019704c60c4600b51786019700c20321000300031a4808d704140f870d032057213624061e57070500740f335f4804d40cc7009407940053002219e8209706a601e40807047505b715f424941e070403025402340083001207c4062401b30012010603a55f880f060cc713b60c56011505e407940053001200940ff4005307e60a1600b5002204c60a1600b500120061000300d500220da200b300d5001202d3001200b3006106e400470a2311d703560106004702c402b414d3007400740557006280a316780a545dc216e30a540aa625060a540d6707a400470a2311d70444178601060783004705f40a23114602230427309539030074114602230557006221650c771b5316d400470444010606830c7705060c4605a53095403307a42f0315240223344700620244007400471b33055704360d4400740b3500470f3300741135055711460455055711461135004700620e3602c6170519240a2300740047227307a40dc4022303f704640d2401b30dc40843055700620106010605571467127714d381941ef301060dc40223055712f50a236d0530e6022320c70dc406830047006204b100120033002201b3001200c20012006160c561f422c3010601060223042701720e0300d50022001200940033001202a607230074007410c303f7017203210140 477 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal150 : ¬ fitsRows (hostAt hosts5 150).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38b5eb483dd3945494358b20c4731401,0x9876453210)] hints908 0x300030003000300d5002200330644089300220b160c560115028400d500030012034406b400830033013300120344003300d5001202d3006146f81fb6019713063af507442e2710043d6801e45585253601e404030074024400470074024436d80047018212181834019705b739c74d775225139406640f570cd839f75ef8686601e404030fc518340047403307a42e041308004701827f243af315e637071036462809165eb32534091607050e673fd7336779c3212608d60bf7137833d7750879d409160705009405580a1609d701550fa40fa40d240053393503e307a417660d96007407f5135303f7009400940574005301a206e4054400470a830223004702660be807940a6700e302c4236405e400e301a212d612d60c4600b518945af408430bb30074232700220106283417380047707507a43d06130800473d4406931c0404e6007408e5016304270e363ad607e6015501a204c604c608c600b51894777408430723007423270022032100030003000300d5002200330644089300220b160f870603521601f700940115001203440807027535540377031600f400830012006102b3147300b50a830197002204970714168707140053002200c20e351085005314b710d63fa710d600b500940ff40053002270431b6507230074035608e5160300470172379319545fb30106024408e51b4300470d44019701a27103019704c60c4600b51786019700c20321000300031a4808d704140f870d032057212624061e5707050768327715743d9800f4436804032e8707442b170c05157420970b4600f443680403001219e8209706a601e40807047505b7139424941e0704030cb8169714f402340083037706a600f40807047514f40234008300123574056401c300220ab84aa7180608d704142d2807052d2828c721b60c5601150c560ab801f70414011500121123535607444d570e73180608d702842d28070501f704140f870d0321b60c5601150234076805b700f40083001204770e35005300220061000300d5000300120da200b300d5001202d3001200b302d3006106e400471b33055704560a23035600470074007400472c5402b414d300627cf374f80a545dc216e30a54130800b266180a540d6707a400471b330557044404560a230106078300473903007411460223004754273a952c5436c715d534972c2514d300620a65055747080047044404560a2306830557299345f41023018309d717050464143652f5059401b3006205f40a230244004713080557043605f40a2300740b350047043605f40693113505571146045500471146113505570062010607a400472c54154743f414d3227307a40dc4022300472945522510f401850a6714d30dc408430047006212c6102317052b84022355140223055754273a9312c61a0729f334972c231705353502c443b4124601b30dc406830557006204b100120033002201b3001200c20012006106640ec706640f570cd8026611960083017218f400940053002216c60714050500530022009418f40053009406c4005300227b0411e708d60bf71378009404840115017203210140 570 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal151 : ¬ fitsRows (hostAt hosts5 151).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb36ae2f483dd3945494358b20c4731401,0x9876453210)] hints908 0x30003000300030b1600d50022001206b4003300220b1602840b1601150b160284023401150003001203440344034400830334003300030012034403440344008303340033001200030061000346f815860214019718a5493707143f372764481801e415b67dc548f701e404030074024400470b2507230074024407f51b4300470022121853860214019705b739c739c727b5139406640f571fe801e439f75f083c8601e404033e450244004703a503e30074024408e5135300470022196355a710d63767076612f7041460f485235557091607050e673fd73fd74bc3212608d60bf712f7041433d759a87b9409160705009405580a1609d701550fa40fa40d240053098503e30074176604e6007407f5135303f700940094057400530133002206e40544004724330a73004702660be807940a6700e305e40f9405e400e3002212d612d60c4600b50e840e84016309a501062327002219745ec30106035608e501630047334834040106035608e501630047413416f301061c0404e6007408e50163042707e615d607e60155002204c604c608c600b51894778408430723007423270003002202d300610003000300030c5600d5061305a500220012006206b4003300221c750074035602f51603042700122e160fd4024402f51b4303f70012034401b30022006100033df7129319273b8300b508f801970022049700f4168700f40053002200c205b700f405b71e240053030703c6030703c600b500941a24005300220b07028401f74df3154821d402341fd702841a7373a44597011500121187020410570c050127085421564da70b460334794475e43ba7008302440197002208f8019704c6211600b50356019700c20061000300031a4808d704140f870d032057212624061e5707052e1600742fc803e3007404e600742fc803e30074022303f7169707442b170c05083420970b4600f419e800e3009402340053002249232385265300744257002219e8209706a601e40807047505b7139424941e0704032e160fd402440f762663007417b4077303f70377031600f40807027514f40254008300222d4501636b55016324e704c60c4600b527d60c6414f6129300b5002204e60074424824d539e44cd3010604e60074424824d539e41c6301060223042740d6007403561aa517f408a30106244613d504270768561800f4121705b700f400e300221123535607444d570e730ed608d7028413c8015501f700940f87060321b60106011500940d2400530ab80b070094100701f702840155002204c64f7600b502b6071409f507140053002200610003000300d50003001202d30da200b302d3172400b302d30012002200b302d300a106e400470a23004704560a23010600470074007400470074007405570062216500470e840693004704560a230a5600474c0300740106004705f507a47c0307a4055701a207a400470a230047044404560a230106078300473903007401060223004730953903007404360223055700622165004707230e140047044404560a230106078300474c030074010602230047309503e3007404360223055701a205f40a230074004705f40a2307a40047043605f40a2300740b350047043605f40a2300740b35004704360455004704361135055701a2010607a4004719240a2300740047227300740074022300472273007400740223004704440843004701a20106010605571894022355140223055781c41ef3010604440683055784e47f03010604440683055704440683055701a20321001201b3002201b3002200c2001200610a34173729d50f9405b7106702751067027504f46157031602046157031602041196008301720eb7050500530022110600f4050500530022009407140053009404840053002232470204381702040266145504f44fe50f9406641a17008301a203210140 701 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal152 : ¬ fitsRows (hostAt hosts5 152).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f839ab6292831ca410c20,0x9876541032),(0xffbbcdeb38bdab49c9ac5aa307b92418828398a0,0x9867543210),(0xffbbcdeb38bdab49c907314831041183dcd62d49,0x8976543210)] hints908 0x12029300c204a304a1000300a100030003000303810140 12 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal153 : ¬ fitsRows (hostAt hosts5 153).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda0f73595a4e51594831054941cc0,0x9867543210)] hints908 0x300940033001202340af60115175600d5001204c600d50012001202540584008307c40834008300120b64003309640964011500c200a1000300940033001202340af60115175600d5001202540584008307c40834008300120b64003309640964011500c204c600d50012001200a10003094300d50012094300d50012094305a5094305a500c20234023401c32e660475092400e612e50b7415b64415041400e3017205e402c409c300e62e660475092415b64415041412e50b7400e30234023401c3017205e402c409c303210003000300a10024093400240934000300030003001200c200b300a100030012002201c30012427300c20061001200c200b300a10012002201c30012427300c200610140 137 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal154 : ¬ fitsRows (hostAt hosts5 154).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb389460f75ed5a4da6290620b16a4a0e0,0x9867543210)] hints908 0x3000306b40033001201060ad60115277600d5000300120c5600d50022001202540584008307c408340083013300120754003309640284011500120003006100030f331d4413080c770fa40fa40d240053202707340cd80624058400e304f4071400e3420432b7013643680cb82574062400e3002203a53e74130811d704e6007458f80d4408270773473300470464046406c400e3002212d612d60c4600b51c161eb5066403a70bd802c4005300223d9801e417a61ea5138438360475074432770794040336e500743248178607b72fd50ba6021474552a76019700740244099800470022086610d6015513d50244004708130ba602142073021401970b2503e30074024403f700225d86162707442d282d2811b61d040155050605060c860155010603560998004764651ef301060356042700222aa4714306570ce80e3600b50022006100030003009407940053094300d50022030710d60fb710d600b5009405e40053002204c60a1600b507e6094305a5122305a5002216870714049707140053002212f7028411230e1609640b07041428580e7308660155001202b605640505003305e4062401b3092407940d73002214c70b4601e40e262cd5236417a64b4513842bc80c0504f400e304970714434801c3002210e628471a0556b202c41a0508071f5556c2091409c3006200610003000300d500030012001207c400330003001206b4003300120033002202d302d30061000307142db304140ab83af32516070515a80f16082707940293007400740827029301a219c70df80a16070515a823d608270094057400530d8609e601550fa405e4005301a21996036701e407683af5181404031df70768079404030693120333780ba60214309539b302140683068301974f6829b725c5083411870584235700e33e230693043602440f23004701a214e80cf407b714e81d3407b76608297728830ed60b0700f42c6701552dc6007404360223004701a2061302e504c608c600b5046405e40293002201061d3407b70924073400e331e30a7304440356084300472f03007404440223004701a202e512d607e600b5050607e602e5002203210003000300120012006201b3002200120061000318171906094300b5152401970022009406c4005300220eb727b51e2400530e030c8600b509241a24005300224c2503e3007470f30c962228004701723e053cb407730544222800470544019701a2069301970d86211600b50c96019700c20321001200c200b3018200a159e514e649b704f4496629a5237508542375236411960cd800e3017210f302e50924048400530022112368b61116109678a352844dc33de756d706d441c33de7092404841378015501a20484029300224ec605050053002203210140 504 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal155 : ¬ fitsRows (hostAt hosts5 155).toFinset :=
  terminal_reject _ (by decide) 0x3330 4 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal156 : ¬ fitsRows (hostAt hosts5 156).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d3a4a1173d8d52d09394c209060,0x9876542310)] hints908 0x3061300d50012001207c40033034406b403440083002207540033034406b403440083001206b4003300120b1602840b16011502340284023401150022006100035b7713c52c845b78110602540234008301f704140f0633670d0321b60155007402440047001206240594003300124db71c4334c64db828b413b60c5601156bc6253513c5020400532e931d040f061c43213601550e3602c6070500220012208706a601e406444d77047514f400e3110601e4064413c515f400e37ee30214460426065e9302142f155e9302144644019703440344034403440083001206e45684004702c402b40403361543a5083421a600e30012006100030003061300d500220012001206b40033002200330012006100031135039752b74fb7129300b5002200940714005300120244039702c60244045500470182068303970356039704c64f7600b500c2514732570714005304c610d600b5009466440053002206e4035608430047017203210003000300120012001200c200120061000302b502b502230fe701720047002200120047002227e327e310c30cb701a2032100031af300d5002200120012001202340033002200610140 218 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal157 : ¬ fitsRows (hostAt hosts5 157).toFinset :=
  terminal_reject _ (by decide) 0x1473330 7 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal158 : ¬ fitsRows (hostAt hosts5 158).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb388c1ee6b2f6ad2723148312d4941c20,0x9867543210)] hints908 0x30c86129302e5049700f40094049706240053002206c40ff402930022049700f416c600f413a705050053002203b409640155101403340754008300120584058400e3058405842394008300121cf60ad6218401151ba40af607d401150012006100030003000328f802140d554cc31514601502142f750544077303972e5708340564025420f800e300941014003307681ae50b7419960516040300224a970ed6108600f42c9801552f154ca30214267553340b570cf40244042700224c8302140985803302140aa705e4046402930a1605a5001207e6050602e502e5002204c608c600d54ae700f404970464005301330022026605160574031700e30f16035603f7079401b302930022186703c614b7050600b5001202d30061000300030fb70916030710d609c514475a130c64122305a5002231d412b30657080749530c640ce816b30de600b500122285115403a72f682b4404060bd80a05020400532607074400e612e504f4278800e307680234278800830022049701e4049707140d7307d4062401b3002204770e5602541cc501b33574056401c3049707c40ff44338023401c30af60a1600d5002200e602a515c420c615b61ae501e412e50a0503b400e300e60564056412e50b9401c302340234008300120ab8041445b8011502340794003309760976011500120061000300030003010600d5002200c202540033075407c40893009400330022062401b3034403440033001204c600d5147305a5002221840574003300120061000318172db7213600b515a8019700220484029300220eb737d715f400530e0302e500941a240053002202440197386451c711960cd805b705c6375810140083017214e80197031601e4050501b303560197002210380cd80dd713360dd70bf42e27083400e301720321001200c2001201b3002201b3001200c200610003088608c600b5017202d3023401c30033002200d5002204840574005301330172032100d5001202d30012025400330003001206b40033001202d30da200b300610a540a5429480d677f132d44173859240a2307a400b2541235a84fd60d6705570544004702440436004747b305570f331d4405570a230436043600470062294807b735a800470356044400470a230436004707a40436004700625ef304750a54044400b2128612861ca20c460a540d670d861cb503e30e141da307a40047044404440557216504440047472406930444055700620a560a5607b73d4406930a56004706930444044400470a56044400470a23044411d7006204b10140 468 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal159 : ¬ fitsRows (hostAt hosts5 159).toFinset :=
  terminal_reject _ (by decide) 0x123312331313330 15 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal160 : ¬ fitsRows (hostAt hosts5 160).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb328c1ee6e2f6ad266290620b16a4a0e0,0x9867543210)] hints908 0x3275506241f6600f40094005304970624067700f40094005300220e450a66009406c40053002213a70505067700f416c600f4005300221cf60ad6175601151ba40ad607d401150022101403340f4400830f440334033400830022058405840b640083058405840b640083001200610003000300031a8705840cd80564025400e304f402b400e31d440f3323d60cc70fa40fa40d24005349e70b9402b4214800e30094009405740053013300221fe801e45b6654d501e42b75494409564d8716a464460403120333780ba602141a1520730214221303970cf4024404270cf4024404270022086604140155120339a80ba602140d55207302140683039707680574036702040033169707c40574118702040033002221e63e741d340cc70f16035603f705740794079401b3046401b3002212d612d60c4600b50127012703d4036703d4036703d4005300225c97074402c6310801550f16035603f783664b23074408c601f7028400d5050605a5002204c604c608c600b50127012703d4036703d4036703d400530003002202d300610003000319541c631fa661141c6325860998004704e600747d2803e30074399300740827098503e3007485147d933c7828786c8652e803f7055817c30c6400d500220ce816b30de62ee412b3065708070e730c6400b574680d340f6706d400d51c161eb5115403a71c161eb5115403a70bd80bd803d40053013300220bd80a0502042285115403a72f682b4404060053076802542788008312e50754025400e600832607074400e612e504f427880083002202a601d31874224601d32ae452e803f70bd805640677025400330cb807680c372574298800333ac8169707d40c37257429880033002204e60074424824d539e41c63010604e6732407b70ab8041445b8011544280ab8476711b6311800d5317702840ab828c711b6317702841038129300d509760976011500222aa412b3065725e412b306570ce80ce8008600b500222fa41db3010622455d0348d8810872a4099804272ec707440d340d34011514c70b4601e40e26047507441bf61ea513842bc80c0504f400833ec71336076816971ba4036751a40c37257400331c7502144a561c750214081542e339442a763a152fb339442a760683019700220be8047503b4003300e602a515c420c615b61ae501e412e509f503b400e302340234008308130ba6021461930ba60214343583a33ce602143a1583b33ce602140f230197002202d3006100030003000311c605a50022010600d5002200c2025400330094003300220b0702843506122316a306d400d50012118702040a0502041a5505c6003302440683039700220b7401b304c600d50356221303970022006100030e6703c60e67272600b55df30074019700220e450a6600940053002205b700f405b71e2400530e033df70e0300b500941a2400530022055816370e7316b31a3619f602840b0702844de632f306d4011500120be810570c050a05085406a6046403770b46101433e4389505c600830244019700222b842433019704c6129300b50356019700220061000300d5002202d3001202540033000300120ac40033002202d30da200b30061000304841036092417052cc604e6007403f76d8338f408430047046411a3007400740c7701a21a950a730a560c960a56004715a81666007400472ac42f4300740427245600740cf407b7098524b307a4098524b307a4055701a211961004271614d305f4069307a4054407a400470244043605f40693007407730047100402b400e30e350b253b5402b400e3069355b3043604360a83004701a22ac40ba60074042714e8072307a40047035604441a950a730106078300470cf4043607b7098503e3007404360223055701a265d55df3007400472cc6072307a403f7103602c6015504640cd82cd505e411a32415007404360c7701a205061cb503e300740f16082702b3063344e602c601550f1604440827155504643be6447411a301a20106010611d708b416f30a5608b416f30a56055706930693044404440683004726c322d401060444068305574bb40c23044411d701a20321001200c2001201b3002201b3002200c200611a551a555066130629a50204130629a502045895031602040033017209b30033002200d500220012381702042ad805e40574057400330133017203210140 791 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal161 : ¬ fitsRows (hostAt hosts5 161).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdaaf7358ba4e51814831054941cc0,0x9867543210)] hints908 0x3001200330012003300c2003300c20033001200a1000307c4003300220e0300d500220022062400331b0329f3011501820d1401c3025314730115017207540734008306b406240083018203810003061300d50022001200120254003300220ea40ea40033075400330182056407c4003345d309430115018207540033023402340083018203210003000300030012001202e301b300c200a100030012002201b300c201b300c200a100a100030140 88 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal162 : ¬ fitsRows (hostAt hosts5 162).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab47358b54e5183ca41892839820,0x9867543210)] hints908 0x22003300c2003300c2003300c2003300c200a1000306440893003300c200d500c20b940254051301c3017206b406b4008300330182052500d501820381000300120012003300c200b300a100030003000301c300c2001200a10012002201b300c20d6700a1000300a10140 54 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal163 : ¬ fitsRows (hostAt hosts5 163).toFinset :=
  terminal_reject _ (by decide) 0x18887212133330 14 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal164 : ¬ fitsRows (hostAt hosts5 164).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb328c1ee6e2f6ad266290620b16a4a0e0,0x9867543210)] hints908 0x30003110600f4009413c506240053067700f400940497062400530022009416c600f423c5062400530022067700f416c600f413a70505005300220f4403340334008303340334033400830022101403340f440083033403340334008300120ad60ad60234011502340ad60ad601150022006100030003000301f704142d57041408d60bf7111633032d573b7407050664358709f50475085405160cd800832607074413c50b74110601e419e800e30094009405740053009407d408c6059701550022208706a601e41fe8138406640f574c7804755c153bb404031a1520730214120333780ba65334068303970b2503e30074729408e51b43042726b5007402440f230047002205165ac701e406640f57047509f5139404031a152073021412037d782a460214068303975a4707c40574036700f400330f16024403f7002211230e1607441c4311c62e9327a41a4801552845340401066c5608e5016303f724270e0308c608d410f300d50c8605060155002204c604c608c600b5067700f4049703d400530133002202661b860574031700e304e600740356084300470cf40356042706c4046400e300220ae703c614b7008600b5002202d300610003000308d7041403070de60d0335d702e501f702844c97785306d43e13688469b854b6094300d516a30c6446c6094300b5002231d412b3065708070e730c640ce816b30de600b500940ff4005300222285115403a72f682b4404060bd80a05020400531697074400e612e514f425b800832607074400e612e51bb42788008304e60fd402440f762663007417b4077303f70022209706a601e41687020408e550f7029302b602540505003312f7028404c628580e73086600d500220537133683574a4405c6061602546348319411b5003300e60e26047507445b6650d513842cd504f4008314c70b4601e400942bc80c0504f4003333b802142fd50ba602144e134d0839442a760683019745f4182334582a2323e703b41007011500220e5607140a050714005300e602a515c4040615b6047501e412e50a0503b400e322b802140d552693021408130fd83ce602140f2301971697169703b40ac403442de803442de803440083002240d6007403561aa517f422c30106244613d5042705b700f4561806b4202714f41217008328c728c706f604140b163eb802843eb80284011500220061000300030003265300740aa700220fc600f41ea50ff40053002200c20e5602540a0505640033009402340053002202440683039716973554034403442de80344008300220e8401630b5704c6097600b5035602230397002223b8478806b422470b94202704f4008300120061000300030e6727262dd703c600b508f801970022009406c40053002205b71e2405b700f4005304c60c8600b500941a2400530022024401970a0510570c050854215606a6046459c705c64da70b4603340083002208f8019704c6211600b5035601970022749860e8490321d4023419f602847ac706d41fd702840115001200610003001200c2001201b3002201b3002200c20061000300941de810970886145308660115017209b3023400330022097600d50022001202661e3822470484145504f4008301330172032100d50003001202d3001200220ac400330003001202d3172400b302d30da200b302d300a10a540a5432480104562800b20d676dd3173876520a54541235a8562800b20d67374805573748004705f40a230436004705f40a230436055706930436043600470a2304360436004700622948055735a8004704560a230444004700740436004707a4043605570062470805573748055704560a23044405571da3007404360557241500740436055700620a560a56004703e30074010600470a230444044400470106044400470e8406930444055700620a560a560047068406930a56004706930444044400470a56044405576d740a2304440557006204b10140 715 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal165 : ¬ fitsRows (hostAt hosts5 165).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb328c1ee6e2f6ad266290620b16a4a0e0,0x9867543210)] hints908 0x3000304970624067700f40094005304970624067700f40094005300220e4506c4364600940053002213a70505067700f416c600f4005300220af60ad607d4011502340ad61756011500030012058405840b6400830f4408340b64008300030012101403340f44008303340334033400830012000300610003000300034a7707340cd80624058400e304f4071400e30f331d4427f500740c770fa40fa40d240053420432b701362574062419e80cb800e3013300226e6801e417a61ea513841115494409562e57684604032fd50ba602141a1580c31514068303974d150074734407b70b2503e3007402440f2308e51b4305d70022086610d6015508130ba602142f15207302140683039707e5057406a600f400330b2503e30fd4024403f7002203a53e7404560a7362f704e600740f16082705740794079401b304640464046400e3002212d612d60c4600b5067700f410b703d4005300225d8616270744451611b61a483c2801552845340401060356078308e5016305d760350ca403560427050605060506015500220ae703c60c37008600b50003001202d30061000300031a48030703c6459702e512f7009466980ae704c6285806030af600d517c30c6417c30c64122300d500220ce816b30de631d412b3065708070e730d3400b533160c64449700d51c164bf51d8403a71c161eb5115403a70bd80bd803d40053013300220bd80a0502042285115403a75f782b4400e6005304e600740f330074164712f7028411230e1609640b07041428580e7308660115002219e8049700f45157029302b605640b2700330cb8076816971ba42988003351573bc42988029300221a7702666758067700942bc802750584003304e6007403a5010616472d280ab828c711b6311800d512a6028409760d0321b6011504146a3721f612233eb8028400d500222aa412b306572aa412b306570ce80ce8008600b5002214c70b4601e40e262cd5236417a64b4513842bc80c0504f4008306a600f40234047514f400830ba563780a0502c423484d971466023401c300220e5603440e5606241cc50033459763e6311802e507c40c370ac455980ea40033098365c827d6041425687ca7597409760525002202d300610003000300030012010600d5002200c20254003300221f380c560f6706d40115001223b806b4047503b4008302440b57002203560aa70012006100030e6703c647d7272600b503e3152401970022009406c40053002205b700f43ef71e2400530e030c8600b500941a240053002207d4121819f602840b07028426d632f31b14011500121b86103806a60464284705841f0438951f9600830244019700222b840c23019704c6211600b50356019700c20061000300d50003001202d300120ac40033000300120ac40033002202d30da200b302d30061000303a501061308055715a80f16082715a847330047007400740827046411a301a21a950a730a5604560a730a56004715a816660074004715a858e807b724560074245600740047098524b307a42ac411d701a20f3300741308055705f4069307a405f4069307a4004705f40693024405f4069300740773004711e402b400e306930693043604360f2300470eb72b170bf402b400e301a214e80cf407b714e8072307a400471a950a733e841a950a730106078300470d9600740436022300470cf4043611d701a214e80255004714e852c8082744f602c601550905007404360827046405e411a301a201062ac407b703e3007403e3007400470a730a7304440444084300472f03007404440223004728940c23044407b701a205061cb508b426a30a562cc60c773b6716e71ce602c601550f1604440c77050607e61cb501a20321001200c2001200c201b3002200c201b3002200c200a140842bd41c3540842bd47aa51ad6130629a523750854130629a5237508541196375802040be80083017209b3009404840053009404840053002207e50e45005300220eb705050053002202663817020414572ad80c370f94165504f4165504f400830133017203210140 739 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal166 : ¬ fitsRows (hostAt hosts5 166).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdaaf7358ba4e51814831054941cc0,0x9867543210)] hints908 0x30012003300c2003300c2003300c2003300c200a1000307140033002210d600d5002200621b0310230bc50734003301820b940d1405130b940d1405130172073400331b0310230bc50182038100031af300d5002200120012025400330022003300c2003300c20061000300030003001200120012001200a100030012002201b300c201b300c200a1000300a1000300a10140 74 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal167 : ¬ fitsRows (hostAt hosts5 167).toFinset :=
  terminal_reject _ (by decide) 0x3331310 7 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal168 : ¬ fitsRows (hostAt hosts5 168).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca3073dac5a548394c410c20,0x9876325410),(0xffbbcdeb38bdab49ca2b5250783dcd60c4131480,0x9867543210)] hints908 0x300030172017203810003038103810140 9 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal169 : ¬ fitsRows (hostAt hosts5 169).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a465073d8d5a54831c8518440,0x9876543201),(0xffbbcdeb38bdaaf7358ba4e51814831054941cc0,0x9867543210)] hints908 0x30012003300c2003300c2003300c200a1000307140033002210d600d5002200620b940d14051301721b0310230bc5073400330182038100031af300d5002200120012023400330012003300c200610003000300120012001200a100030012001201b300c200a1000300a10140 55 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal170 : ¬ fitsRows (hostAt hosts5 170).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f839ab6254831c8518440,0x9876543201),(0xffbbcdeb38bdab49b9ac5ca30794831054941cc0,0x9867543210)] hints908 0x300a102d400640064000304a200c20644003300c204a10003000300030140 16 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal171 : ¬ fitsRows (hostAt hosts5 171).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49b9ac5ca30794831054941cc0,0x9867543210)] hints908 0x300a13f821751006830d400a344c400a3000700d504a201c300c2091404a3003300c2141304a10003000300030003000300a100a10140 28 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal172 : ¬ fitsRows (hostAt hosts5 172).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda9594e2f835cb62547414c320440,0x9876543201),(0xffbbcdeb38bc60f736d5a4e46290620b16a4a0e0,0x9867543210)] hints908 0x3000300120da200b3003300120033001202d300610003009407d409c525c515740344628700e344b52c84202727640cd80eb70403017209d402b40d7306e40047092402c4051301a20062288318060b162c67015502c600471c7507a408e51353042701a200620cd80266165523c513940eb704031b0310230bc510750c2308e5084303f701a2006203210003061305a5097600d50022001200740356099805d7001217b402440ec805d70012034401b3001202340033001200610003000300030003001200120012006113451d230047017200470012022308430047017200470022032100120012001200610140 120 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal173 : ¬ fitsRows (hostAt hosts5 173).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb388c1ee6b2f6ad2723148312d4941c20,0x9867543210)] hints908 0x30e4506c43146009400530e4506c4031600940053002207d40ed61ba40bc521a6086602340115002206c40094009400530022235615554b0700f41f6600f40053002205940834025405130594083407c4008300220f4404f40ac400831014033407540083001200610003000300032f7505442f75021412030ba602140d5533d31514019700941014003330460964086601551d5613c515f40475074405163f862cd501e40403002204c608c600d50293002207e60e360525186721361fc7050600b500220414075404f400e30e84223315140b570475074406b423b800830022255402c401c317e3021405440aa706b401b3000300122f841c4321360e28075404146ff4061307054ae715f40497046400530f6707540c561f3801150c5605a50133002202e5001200030061000372d834b7094332c30c6400b5002219480c642af606570f6706d400b500122be81fa603a521e60cc7108601060284011507d407940033002211f804062b6403a7161705c60053290818740f331d440cc716970744023425b8008300226f1834770022056402540254008322e30e1607440d3413c801151286043609761715002211b50e56071400530f44062400330ea407c40234089300220061000300030003052500d50003001200030956279608930033002200d5002201c30133239405940083013300120033013306b403440083001209b3006105640254057411a3029300623d44069340a8322437483e6407b71345134500475e3507a40c96004714b709e603070b560d86015501a20094009405740053072307a4072307a4374825d6082702c61036015502c644f601551465044404360436082704840484029301a202230223004702b4100400e31fb605440197024404360843004701a247140a830544004702b411e400e3183405440197183404360683004701a20497073404975084092400e3069304360444044407b703560444045500471fb604441135004701a202e50886088602e50022032100030003010600d5002200c202540033075407c4089300940033002204c600d5094305a5002202c40d7300c2062401b3094309c50012006104c60c4600b5134501971786019700220c370b940be801b30723152422730074019700030022009404f4005337270e03055805a500940d24005311f819960b27752705c600530497009404970094005300220223019704c60c4600b503560197002209a530e65545010601970516168707144914173701b3002202d302c401c301820d44019711f72c745697525400b5024401970e360525018203217b144af306570ce8008600b5001202d3001218867d551d8403a70bd803d400530133001201c300c201c310720182006112f700941de82ba64db32634065741a42bf327380115017209b307d4003300121a7702661e38188640f51d8403a702a51da40ed80083013301720e0300d50022002203210140 532 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal174 : ¬ fitsRows (hostAt hosts5 174).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda0f73595a4e51594831054941cc0,0x9867543210)] hints908 0x307d4003300120c960c9605d71786178605d70022129300d5001200120544054405d7083401c300220d440d4405d70b64003300c200610003009400330012079402930012001207c40834008302540584008300120594073400e30754003300c201060af60115365400d50012001200a10003061300d50022182300d5001204140f5809872d7604140d0311c60155017205161ce8036701e404750b7400e30234023401c3017205e402c409c3094305a50012023400330022032100030003000300850516125100a3006869126531006816d81a050063000700030003001200c200b300a1001200220012006100a1190606a553e6007403f701721ca5002205f41a6377e41a63042701a219b30022002203210140 139 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal175 : ¬ fitsRows (hostAt hosts5 175).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb328c1ee6e2f6ad266290620b16a4a0e0,0x9867543210)] hints908 0x30e4506c40a66009400530e4506c40a6600940053002207d40ad61ba4011521a60ad60ad6011500223b3506c400942ca600f40053002223561555067700f42ca600f4005300220594033403340083059403340334008300220f44033403340083101403340f440083002200610003000300030094009405740053076804f4051600e302c60866015504140af601550f3305f5007404360cc70484048402930133002207340794079411a3029300220ab808660414015550b819c705250df8633708c605250307030709e6030705060307050605a5002202b404f400e305581df701c317e302140544221303970475075406b467d800830133002202b4058400e30db86587057401c317e302140544068303970a6625541f55046401b30003002203a528940c2304440cc7012701270734012704640127046401b30f6707540c561f3801152427129305f4299305a5000300220886088602e502e5002200030061000305580ab80a1600d505f401636906164709050074399300740356082705580456122316a306d400d500220d240094005319480c642af606570f6706d400b5010600d500220be80768079400332be81fa603a521e60cc7108601060284011505583506122316a306d417c306d400d500220c4604c600b53ba82af60657144700b5002211f804062b6403a7161705c60053290818740f331d440cc716970754025425b8008332e7013600e632e7095600e6008300222908187472e416470254003368782b6403a70477005323e702840987369609643a231178096400d50022045608730a660873024407b7056402540254008322e371f607440d3413c80115036701e4012700942fb42ed80956003333b8021441f54e230a46021408131238166602142213019700220be80a0507141a5505c600330be86a041cc51a5505c62a5505c6003300e62ef81ad600e62ef805c6008322b802140d5526930214081312380a4602140f230197002200610003000300030ad6052504360ad6011500030012000307c400330022043600d500220012033401c300030964096401150003001207c403340083013306b40334008300121c930061000305640254057411a30293002226a300741b5526430ca4335401063e6407b70fc50c960047267515240c9600470307030709e6030709e6030709e6015500220094009405740053072307a4072307a40723007425d6082702c61036015502c608660155090500742415007404360436082704840484029300220a830544004702b4100400e37f530214054401970244043607730047002218940a830544004702b404f400e317e302140544019702440436077300470022012701270734012707340127073400e34bb40c2328940c230444044407b70356044413d500470356044413d50047002202e50886088602e500220061000300030f160aa72a960aa7002219480c640f6706d400d5067700f410b700f400530133002202d30bd802540677025400330094003307d4003300220cf40b5704c600d50943256805a500220ae703c6523703c600b50003001202d31384138401c300c228240b571cd600d511b5234801b325262526052500220061000304c60c4600b530e601970356019700221687009413a70e450be800334a2705e418e4036700f400530003002200940d24005311f8040607e5161705c6005300940d24005311f800e60b27161705c600530127009401270094005300221524019704c60c4600b503560197002204970ee703d4036703d4036700f400530516168700f40a341f870033002202d31384138401c300c20244019716270744030704c600b502440197252625260525002200611048104803d4036703d4036703d40053002202d3001210480464036703d418e400530133001201c300c201c300c20182006105581f481916065741a42bf3273801150133017209b307d4003300220be821c80a3403a702a51da4524800830133017209b30e0300d50022001203210140 725 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal176 : ¬ fitsRows (hostAt hosts5 176).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb328c1ee6e2f6ad266290620b16a4a0e0,0x9867543210)] hints908 0x300030e4506c43146009400530e4506c4031600940053002207d40ad60ad6011521a60ad60234011500030012049706c4067700f400940053002223561555067700f41f6600f4005300220594033403340083059403340b640083000300220f4403340334008303340334033400830022000300610003000300030094009405740053076804f4031700e30a160866015502c60866015505f5007405f50fd40436024408270133002205740564025411a3029300220ab808660597015528630fc523d608270df819c70c4605250ae711c614b709e601550022079404f400e318940a831d3407b717e3021436a4068303974a671566101406a602041f55046400e30133002202b4058400e30db81df70d2401c317e30214054406830397062403440ac400e30003002228940c2328940c2304443e8407b706770b740497073400e338c707541cf61936028405f42993015511b60b1611b601550133002202e5002200030061000304c60a1600b52be81fa603a51647122317c30d3417c30d3400d5002205b70204036700f4005319480c642af606570f6706d400b5061300d500220094079400532be81fa603a521e60cc71de80f6702840f6702840f6706d40f6706d4011507d40794003300220e670de60fb703c600b519480c6414470f670d3400b5002211f804062b6403a7161705c60053290818740f331d440cc701f702843a231178096401f702843a231178096401150022290818740f3316470254003311f804060477161700e600533ba70127009400e6003300221e382877025428770254161705c6161705c60083036701e42fb42ed80956036701e42fb42ed80956008322b80214227526930214054422134f0700221cc50e5603440e56062400330f440ac4003300e6012700f42ef800e6003333b8021483e54e230a4602140c960f234e970022006100030003000307d40ad601150ad600d50003001200030ac40033002213b600d500220012025403340083013302540334008301330012033400330003096403b40115001200030061000305640254057411a30293002209a50a5680f80ca408f816660ca407b728630fc50106004728630fc50c960047030709e6030709e615d6015500220094009405740053072307a4072307a408f807230074082702c60af6015502c6086601550905007405f50074043604360827048404840293002205f40a830544004702b4058400e317e30214054401970244043607730047002218940a830544004702b404f400e317e30214054401970244043607730047002201270734012707340f9400e328940c2328940c230444044407b70356044413d500470356044413d50047002202e50886088602e50022006100030003265300740aa700224b660c64449700d5067700f449d703d400530133002202d30e5602540b2700330094023400530022068401630b5704c6097600b5094305a500220ae703c64ab7008600b50003001202d3138401c300c2034401b30943052500220061000304c60c4600b508f80197035601970022009413270b740be80033049705e4036703d40fa400530003002200940d24005311f804060b27242707e5005300940d24005311f804060b27161705c6005332a70094012700940053002208f8019704c60c4600b503560197002204970ee703d4036703d4036700f400530516168700f40a341f870033002202d31384138401c300c20244019716270744030704c600b50244019700942526052500c200610ae703c67817008600b50133001202d3001200c2067700f475b703d400530133001202d301c300c2018201c300c2018200a12ea70e942f3549972f35497705c60d5505b70c3708540e94338549971ad60be8375802041196008301a209b307e50e4500530e450e45005300220be803770316020402661067027516550d5505b704f40c370d5505b708540c370f9400830133017200940484005300220ef50ef50053002203210140 720 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal177 : ¬ fitsRows (hostAt hosts5 177).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcce37abdab28d2707b96a6b1283906628820,0x9876325410),(0xffbb5a4e5183f9bd6717b1cc520c417358b52500,0x9867543210)] hints908 0x30003000302a601d3090504d408b408a3010608b408a309761404148602f5016303f710b704970204067700f4067700f4005301f7009414980603030706f6011501f7009414980603030706f6011501330133002215960684087302a601d3007402a601d3487415360ca402f50163042702a601d302a601d304d404e6007402f50163099802f5016305d701f70284762778d3109679731b1401f70284193602841116109617d301f721d401151fd7028422f3206706d401f70284023416370e7305331a360115000300220c3714b70de60ae703c60ae703c600b50127012703d4036703d4036703d40053000300220377031601e413f80275012703b4008303770b4603344d876b052bd47ae51f961187020406a6020410570c0509f508540083081354680a46021407730397000300220377031601e413f80275012703b4008361070b46033429341c2705c611870204215610570c0509f508540083081323f80a46021407730397002202d3000300610003000300030b07009400940b07009401f700940b071116109617d32bd34b6606d408d6448708d60bf7015501271067027503b414a7063702752cf40377031601e40377031601e400830127105702751d561e6504f40e941c270136053702662015110645a60204008301270637027503b40377031601e40083013300220dd7026602660377031605740377031605740dd71115109517d410954a4405c606643b2706640f5700e304e6007404e6007409980223022305d702a601d300740cf4022304270e26027510482d0426262487057418a51a8704f41315031602040367046400e3204601d300741536487402f5016304270133002203074dd7060306f618570c1706032d1601f7009401f70094011508b44cf301060f16078303f706370275012701270334037703160204012702040127020400330905268601d304d42fe41ee3148602f5016303f7030703071cf603070de60307050605a5000300220dd7026602660dd711244d441c350a9537e705c60a340a340ec70083112326c833261e7807542914280708c619631e97086601f700940fb70506015504560e840873117601d30ca402f5016304270133002203070c17060306f601f70094011508b408a301061404097602f5016303f7012701271014012702040127046401b3000300220003006100030003000301f7009401f700940c170603030706f60c17060303072d1601157e256bf61b2529c718861ec5115403a718861ec5115403a713e70266003301f7009416370603030706f60115012710570c05101418c4461809560537133600330133002202a601d3090504d402a601d3090504d409050f7601d304d409050f7601d304d402f5016303f7012700f4012700f4005301f700940c170603030706f6011501270807027503b40377031600f400830133002200030377031600f40377031600f406370275012703b40637027501272cf4008304561d661ed51be4087304561d665d3538b40873045620a422952a860873045620a422952a86087302f501630427013305371115109517d41095111517d405c6053702660768053702660ee7063702750637027504f40127063702750637027504f40537026605370266008301270637027510570c0504f40dd702660e940a9511670956053713360ee70637027510570c0504f442040a95116709560dd702660537133600830e260275074403770b4600f410570c0504f417a622550204008300221c832264060335d71c83226406572ba641b32264065723e7009400d5030703c6030703c600b50127012704640127012703d40127012703d4036703670464005323e70094030703c6060335d700d5000300220377031600f410570275012703b400830377031601e406370275012703b40083013305370266053711241f041c3527040a95247705c60dd702660e941c2705c6053702660dd7026611241f041c3527040a952477053705c60e945a8705c6008300223ec702660a341b2529c7609746a500e600330377031601e408070275012703b4008311230e16096401f7028416370e7308660b07009401150377031601e4012700f41b2529c70033013300220003006100030003000300031a4801f700940f870603030706f619161e5701150133090502a601d304d408b408a3148602f5016303f709051b6501d304d42a9602f5016303f71936028441e65be30d3405330de600d5000300030003001200030c3705330de60ae703c631b60d3400b50003067700f410b703d400530133001202d319e80377031601e408070275012703b40a341f870083013310b709f50204067700f402b600f40053013309050fd4024426a3148609050fd4077303f701f7009411232d8609640b07009429335a980b0703b4011502a515c40956051609f50475085425b800831ab31ab301330012000304560e84087302a601d30ca402f50163042701331c63281603561c750ca426750ca420050427013301f7028416370e7305331a361936028401f7028422f3206706d4011526750ca42005035604270003000300120ae703c60c37008600b50003001204567b440873282402f50163042701330377031601e4111515c4095617a62255138413f802751ea50854008301331187020410570c0509f5085406a6020403770b46033429341c2705c600832fd50a460214081360080a4615140773039700030003001206a6020410955bf400e609f5020400330003051602a515c405c615b6027501e4047509f503b4008301337ce601d30fd40773024403f708130a46021408130fd82a460214077303971ab300030012000302d30003000300a10003268601d3098501d304d402a601d328d60bb304d404e6007404e6007402f501630843004704e60074010604550223004702a601d300740bb300740b35022300470003204601d300741536007402f5016302f501630047204601d30074153600740b3502f5016300470022204601d3098501d304d402a601d3007404e600743354010602f5016307830047197424c3010601060455078300470bb302a601d304d411760bb300740b3502230047000328d603e3268601d304d404e6007402f5016302f50163004709850bb3268601d304d402a601d300740b3502f501630047002202a601d302a601d304d402a601d33ed603e304d404e6007404e6007402f501630455004702a601d30bb304d4292408a3010604e600740d96007402f501630b3500474c5413781116109617d31e780754009401f700940fb708c608d60bf708d609d701552b242b241b252ce70266076814a7165504f414a7027504f405370266026600e3000308b408a301060d9600740b3502a601d30074043602f5016302f501630047098503e3098501d304d4117601d300740b3502a601d30074043602f5016302f501630047002204e60074007408430223004702a60bb3007400740843022300471b540cd81115109578841d18156602661315031605740367057406640f5706640a6700e30db85758020403670464249412170367057400e30db802660367046477f40a6713e7057400e3002208b424c3010637150106078307830047117601d302a601d304d408b408a30106078302230047368636860603083700940ab818572b33086618570603086601f700940094015500940df8368611e7009414531857086601550c7801f72c13326806d4191611e700941916191611e7015500220003292408a301060d9600741075016307f50163004703e302a601d304d4584600741075016307f50163004702a601d3007433540106078308b408a30106044402f5016307f5016300470df801f700940fb70506240610070fb708c6015502660db82b240ec70266145514a704f400e30003002208b408a3010614040106078302f50163004703e302a601d304d408b41ee30106078302f501630047098501d302a601d304d42fe41ee30106078308b408a30106044402f5016302f5016300470df800940fb705066ad609d7192708c6015512681655012708540a340ec702660a340a340ec700e300030022006101270807027503b40377031600f40083013301f700941f481916065741042bf327380115000300120003030703c600b50e8401630b570133002200030377031601e408070275012703b40083012700f40053013301f7009411232d8609640b07009418c36fb70b0703b40115002200030377031600f421c80a3403a702a540243628008301330377031600f4111515c4095617a622550204063702751ea50854008301331bf806370275085403770316020401270637027508540377031602040e940a9511670e940a952b57053705c60537026600830003001200033cf623850aa70003001202d300a101270637027503b40377031600f400832ea70e940a95116759c705c61bf80637027508540e940a9511671ad6202702660377031602041196008300220003030703c600b584a41d9308f80b3503970003002203070c17060306f601f700940115012700f400532914280703c618b4060315e601f7009419631e9711c60115012700f432a700f400530133002205370266037703160204026606370275145514a704f41067027547f808543548008300032626248700f40e26027507441315031600f418a51a870b7400830db80377031602040127063702750854037703160204063702750ee70637027504f4053702660083002226e41d9308f807830397030703c62dd703c600b526e41d9308f80223039700030022000300610140 1725 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal178 : ¬ fitsRows (hostAt hosts5 178).toFinset :=
  terminal_reject _ (by decide) 0x331111110 9 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal179 : ¬ fitsRows (hostAt hosts5 179).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a46506b1ee52d262a0e320440,0x9876542310),(0xffbbcdeb38bdab49ad4941cc59460f7358418820,0x7698543210)] hints908 0x307d407d40bc5028400d50003001200d500120033064408930012064406440513089310a310720f4400331715001202d300a1006200940a16015512772cd7005300941806052509a70d861ff30657070501a20644079401c3083402b400e30074586403f701a20f440d1418d300220644045401c302b4157400e30624233406240ea402b40d7312a40d44586403f701a2154709241a7403a7040301060dc4042731c617860dc40427018203210003068401630aa70012064400e3001200a1019704c60a1600b56ba6039700621b970eb7005310c32a080c77002200940794005310e5477842f7154707140053006202c40d7301823694039709a710d600b5009409c504a2032100030094025400530012001200a10eb71b9763f7641700e3018204a2170700c2055704a203210140 152 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal180 : ¬ fitsRows (hostAt hosts5 180).toFinset :=
  terminal_reject _ (by decide) 0x111311130 9 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal181 : ¬ fitsRows (hostAt hosts5 181).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c65073d8d52d27414c320801,0x9876543201),(0xffbbcdeb38bdab49ca2941cc520e0f7358b50820,0x7698543210)] hints908 0x7d40bc507d442a5018200d500c20454051301c30b820d1418d305250172003302b408930012038107d40bc507d442a501820454051301c30b820d1418d30525017200d500c2003302b408930012038104b10eb71737005301820182018204a203810eb71737005301820182018204a2038100a10140 59 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal182 : ¬ fitsRows (hostAt hosts5 182).toFinset :=
  terminal_reject _ (by decide) 0x1 1 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal183 : ¬ fitsRows (hostAt hosts5 183).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117b98d52d0931c8510c01,0x9876543201),(0xffbbcdeb38bdab494e3073d6a6b0e64a0a408062,0x9876542310)] hints908 0x3052500c205a5018201c3157401c3001201b3025400e3018203810525001201c300120b9401c30012002200a10003052500c205a5018201b3025400e3018201c3157401c3001203810525001201c3001200220b9401c3001200a1000300a1000300a100121b7500a100121b7500a10140 57 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal184 : ¬ fitsRows (hostAt hosts5 184).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a4a1173d8d5a547414c410c01,0x9876543201),(0xffbbcdeb38bdab49ad4941cc59460f7358418820,0x7698543210)] hints908 0x325860436011507d40525001200d50012045407c40083003300120d1401c300d50012003302b40893001200a10293006207d419d70155009418060525130802c4018503a7005304140ab8180609c501a21b8613a701c302c402b401c3083401e400e3018205940d1418d3048402b3052505e401b3002202e5088605a500225a580e360183065700b507e605a500220516076804540d73096409160155048401b37cd3151426b5021405f408430773039701a2032100030003001200a1150600b22c350d670eb7173702930714092401b3002202c402d309370b82092419b310d60d8605a50eb7005300620321373800f4469503a70053017205a5018200b30381000305b703d405b703d4005301720893018201c30b82018200220381009402b400530012001200a10140 150 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal185 : ¬ fitsRows (hostAt hosts5 185).toFinset :=
  terminal_reject _ (by decide) 0x133111110 9 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal186 : ¬ fitsRows (hostAt hosts5 186).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38b5e958c2726b1ee4a16a290e618801,0x9876542310),(0xffbbcdeb38ad2f67b9ac9ca30398a45a92810c20,0x9876453210),(0xffbbcdeb38bdab45a928398a49ca307b9ac18820,0x7698543210)] hints908 0x30fc500470fc50047001207e506c40a6600940053002207e50a66009406c4005300220a83004705440047000300120a830047054400470003001200030061000300030c960fc504270fc50c9604270022000305440a8303f71ab35fd31514054408430397058402b400e30484029300220a83054403f71ab302b4058400e35fd31514054408430397048402930022088602e50022088602e5002200610003010600d5001205b70464036703d404c40053010600d50022025400330127009400530022025400331627074400b504140525002202c401c3107200610003010600d5001205b7046404c4036703d40053010600d5002202540033012700940053002202c401c31072025400331627074400b50414052500220061179803d4167703d400530133017202d3001201c301820321167703d4179803d400530133017202d301c30182001203210140 166 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal187 : ¬ fitsRows (hostAt hosts5 187).toFinset :=
  terminal_reject _ (by decide) 0x001 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal188 : ¬ fitsRows (hostAt hosts5 188).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1162d4f734c52250710c20,0x9876453210),(0xffbbcdeb38bdab49ca304a0e6291ee6b16a18820,0x7698543210)] hints908 0xa1006800681dd80007107200a100030140 9 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal189 : ¬ fitsRows (hostAt hosts5 189).toFinset :=
  terminal_reject _ (by decide) 0x331111110 9 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal190 : ¬ fitsRows (hostAt hosts5 190).toFinset :=
  terminal_reject _ (by decide) 0x331330 6 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal191 : ¬ fitsRows (hostAt hosts5 191).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f835cb625474188510c01,0x9876542310)] hints908 0x30003142100a303230007000303810003017201720172038103810140 15 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal192 : ¬ fitsRows (hostAt hosts5 192).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a41f28b16e6a5474188510c01,0x9876542310)] hints908 0x3007402c605d70c230c2305d7000300c2129300d50012001207d40033001206e406e405d7059401c3000300120d440d4405d70334003300c2000300a10003056402930012001200330564308405640083001201b3034407540624008300c206240033001210863654108601150b16365411b601150012001200a100030003000305160085142100a302d400680068006300070003001200c200120061001200120022006100030012061300d5001210c30074035616470172001202540033002210e501060244164701720321009400940a1609d7070501820266026607940a67040301a204a2009419b300c20714029304a203210140 124 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal193 : ¬ fitsRows (hostAt hosts5 193).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda307bab49c9ac290620816a4a0e6,0x9867543210)] hints908 0x300030003064408930033001200d50012003306b406b40083001200d503440033001202340c560115058401b3001200a10c86061302e50094009406c4005300220594059400e30074007405d7018203b40964015512a412a405d7018206c404840293002216c600f4009405050053002206e406e405d70a830a8305d7017203810003009407940053001202340234005302340234008301720754025401c33574025401c30012255402340033001200940234005300120976097601150172038100030003000301c30012001200a1001200c2002201b300c2427300c200a1000300120012003300c201b3001200a100120012003300c201b300c200a10140 128 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal194 : ¬ fitsRows (hostAt hosts5 194).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d3a4a1173dac52d0931c8510c01,0x9876542310),(0xffbbcdeb38bc60f736d5a4e4c290620816a4a0e6,0x9867543210)] hints908 0x30003000306b4003300120c8600d50022001204f400330244024403f7001203561d3404270012006100030094009406c4005300120c2300470074004700c2024400470244004700c216c600f4009405050053002206e400470a83004700120061000300940234005300121e480aa7001202440397024417b4022303f7001232380b570356039704c6097600b5002207c402340033009402340053002203562446022304270012006100030003001200c20012001200610003001200c2001201b300c2006100030012001201b300c201b3001200610140 108 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal195 : ¬ fitsRows (hostAt hosts5 195).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bc60f736d5a4e4c290620816a4a0e6,0x9867543210)] hints908 0x30003000300940033001204c600d500220012075404f4008306b403340083001209640964011503340033001202340ad601150ad600d50012006100030094009406c400530094009406c40053001202442df40047024400740047001202440d44004702440d44004700c206c43646009405050053002216c600f4310600f405050053002203560106004703561786004700120061000316a30c6416a30d341596094300b5010600d5001214475a130c64094300b50012056400e612e50234056401c32e660475075400e612e50b7415b64415041400e3023402340083001204770e56025411b5005310860d345cd309761086052516272c741d760d030414451602e5076807c403670ea4003300220e5602540e5602541b4411b5005300e62e660475074415b61a05041412e50b7400e34a5633f5054447a884782bb3319403970768023463d800830022025400332e660475074415b61a05041425740293269302141f784e08713331a4039707680ea42988003300220976097601150ab804143eb8028400d50ab8041445b801150ab81286311800d500120061000300030003001200c2001201b3001201b3001200610003001200c2001201b3001201b300c200610003001200c200120033001201b3001200610012001201b3001201b300c2006100a1002409340024093400030140 249 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal196 : ¬ fitsRows (hostAt hosts5 196).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38b5eb3a4a117b5cc52d0931c8510c01,0x9876542310),(0xffbbcdeb38a4e57b55cd6460f4a16a3986229020,0x9876453210),(0xffbbcdeb388c1ee6b2f6ad272290620816a4a0e6,0x9867543210)] hints908 0x30003009406c40053001216c600f40505005300220b6404f40083033403340083001202340ad601150012006100030003009406c4005300120b6404f40083033403340083001216c600f405050053002202340ad6011500120061000316a30c6446c6094300b5001216a30c6446c6094300b500120e5602540a050714005308130ba60214081348a846b631a403972e660475074400e612e50b7415b61a05041400e3024417b4022303f700220e5602540a050714005300e62e660475074415b61a05041412e50b7400e308130ba60214081348a846b631a4039717b40223024403f70022035624460223042724460223035604270012006100030003001200c2001201b3001200610003001200c2001201b30012006100a10024002400030140 145 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal197 : ¬ fitsRows (hostAt hosts5 197).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e1173d8d52d283988510c01,0x9876542310),(0xffbbcdeb38bdab48c2726b1ee5a8e64a06229020,0x9876453210)] hints908 0xd50012003300c20022003300c200a1000300d5017251940893003300c2003307c404540083018200d500c203810003000300a109341251125100031b7500a10003001200b300a1001204a204a200a10140 41 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal198 : ¬ fitsRows (hostAt hosts5 198).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173d8d52d283988510c01,0x9876542310),(0xffbbcdeb38bdab49c9ee8c16a6b0e64a06229020,0x9876453210)] hints908 0x381000304a112c83003000718d5001200a1000300030140 12 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal199 : ¬ fitsRows (hostAt hosts5 199).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a464f835cc52d274188510c01,0x9876542310),(0xffbbcdeb38bdab28d26e6c1ec41ccb5246229020,0x9876453210)] hints908 0x3001200120012001200a100031ac700221ac700221343146312450d671245146313430d6702b40254051302b4025405130172038100030012001201b300c200a10003001201b300c2001200a1000300120012001200a1000300120012001200a10140 50 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal200 : ¬ fitsRows (hostAt hosts5 200).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f835cb6254831c8510c01,0x9876542310),(0xffbbcdeb38bdab49c907314831041183dcd62d49,0x8976543210)] hints908 0x29300c2029300c204a3001204a304a1000300030003000300030381000300a103810140 18 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal201 : ¬ fitsRows (hostAt hosts5 201).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117b96a6b10931c8510c01,0x9876542310)] hints908 0x300b300d5018200b309c300b30381003300c201c300c2003300c20062003300c204a100030003000300c204a204a10003001200b300b300a10140 30 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal202 : ¬ fitsRows (hostAt hosts5 202).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda958c2726b1ee5a8e64a08510c01,0x9876542310)] hints908 0x323a606b407d40bc509e6028421a601150022061300d5001200120ea4003300120d1402540594051307c401c3002207340ac40f4400830754003300120061000304c608c600d50293002207e60e36052527c80ef625e41ff3065707050022323831640b5709560bf41f55064400e320f8068415d51f5502540083002205e402c401c31e4806e40aa7075401b30003001200940624003309641ce615962d3301552f7505442f75054412030ba602140d5533d3151401971a4515f4051604750744310601e40403001216e809d44bd635b513e403a704031f38113630f313e313b60115176405a57b63213604140e2807543d44061307050133002202e50012000300610003000300030bc60bc600b3000300d5001200b309c300b300c300a1135355230827029300620047004705e63e641f2718171367015501a20047019702b400e311460843004701a200470197157402b400e305e60683004701820dc4135307b71bd41bd41ac702c60155180602c601550dc411461ac704840484029301a20eb7216700e30dc4045500471bd41135004737b40dc41f2701a202e50886088602e50022032100030003001200c200d5001220e400b3001200a1019704c60a1600b502230397002207232ae422730e140397000352d50b94143601b30012019702b402b401b3056401b3006209a52586554513660397168707140be873b4173701b3002202d300940794005365460e03176405a500941814005311f819960b27512603a70053324700940eb70053002202c401c30182022303971af305a508d70c6411e700b50e360525018203210003061300d50022001240b81fa603a521e60cc70172409818740f331d440cc70172001202340033002203210e67008612b3065700b5001205b703d4066403a70053002201c300c201c3107201820012006102a603e302a603e304d4224603e30074022303f70172045605f41a63829581e44cd301060223042701a2061300d50022002207d40033002203210140 367 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal203 : ¬ fitsRows (hostAt hosts5 203).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d28d26e6c1eb628e64a08510c01,0x9876542310)] hints908 0x323a606b407d40bc509e6028421a6011500220e0300d50022001207d4003300120d14025405940513025401c3002207340ac40f4400830754003300120061000325540ff4059411a30293002207d419d7052528630fc521f6004704140ab8103617051fc707e615d609a71506015500221b8613a701c308f806e401970bf401e400e30cd8068415d51f5502540083013300223d340a830d94004708f806e40197079402b400e314363c850ff401b300030022009400940624005305160768100414d31ce6091601550a1602c601550f333c6611460fe706c40484029301330022203705e40f941547059400e31f38113630f313e313b6011517645504061305a503a537b40dc40cb70003002202e50c86088602e500220003006100030003000306b4052509e62776011500030012000300d50022003302b40893002202c402c409c307340754008301330033001209b3006105e410f402b411a3029300221345134500472675152421f6004726a307a413a52643322405e63e6407b709a71dd63ad609a71506015501a2022302230047054406e4019702b400e3054411460773004701a23d340a830d940047183406e40197181402b400e3183404360773004701a2009400940574005307233154072331541bd425d6082702c60155251602c6015503e307a43c661146082704840484029301a21547136423641547059400e301060dc413d500471fb6044413d500476ce40c2337b40dc407b701a202e50886088602e500220321000300030f160aa7061305a50022001200620cf40b5700d5061305a5002200330414089300220012062401b3062401b3002200615723019704c60c4600b5178601970022072300743f5418940693019700030497009437270e450be8003300220a73019704c6031300b503560197002209a501060e840e8401630197168707140be84914173701b3002202d300940d24005311f804060ef537270505005300940d24005311f819960b27512603a70053049700940497009400530022041402c401c301820d4401970244019711f70c64030704c600b530460e36052501820321000305580ab80a1600d50794009400532776097605a50022010600d500220be807680794003340b81fa603a521e60cc707940be82037074400330022409818740f331d440cc70012025400331708036707c401b300220a16096400b5012700940477005300220754023401b30be806240c3707c40033002200610fb700863db7008600b50012036703d44a0703d40053002201c300c201c3107201820012006102a603e302a603e304d40d460074022303f701720456334538b40873813401060223042701a20e0300d50022001207d40033001203210140 497 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal204 : ¬ fitsRows (hostAt hosts5 204).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d28d26e6c1eb628e64a08510c01,0x9876542310)] hints908 0x3000323a606b407d40bc509e6028421a60115000300120e0300d50022001207d4003300120d1402540594051307c401c30003001207340ac40f44008306b4003300120003006100030564025402b411a3029300220fc506a5082728630fc521f6004700940ab81036070527c8150625e41ff30657015500220a832dc307b708f869f401970bf4079400e30244114607730047013300223d340a830d94004708f806e40197079402b400e303440754062400e300030022009400940574005302660768100404031ce60a1601550a1602c6015505f500743c66114603f70133002216e805944bd635b52b0403a700e303560dc413d500470b16176411b601552da40c2337b40dc404270133002202e500120003006100030003000309e607d40115028400d500030012000300d500220033064408930022059423940083013301c3013300121724172400b302d300610564025402b411a30293002213451345004710730fc521f6004709a52c5623e5069308f805e607b709a71dd609a71506015501a20223022300471fb606e401970bf402b400e3024411460773004701a23d340a830d940047183406e40197181402b400e3183405e60773004701a200940094057400530723315407230e1408f81bd408271ce602c60155251602c60155090500743c661146082704840484029301a2154713641547059400e303560dc413d500471fb61bd413d500472da40c2337b40dc407b701a202e50886088602e50022032100030003399300740aa7001200120062068401630b5700d500220033064408930022001200612233019704c60c4600b51786019700227bd4189416030723007401970003009469550b740be8003300220773019704c60c4600b50356019700220e840e84016309a501060197168707140be84914173701b3002202d300940d24005311f804060505190607e5005300940d24005311f804060b2765e603a70053049700940497009400530022041402c401c301820d4401970244019711f70c64030704c600b500940e36052501820321000304c60a1600b50234009400530022061300d5002200940794005340b81fa603a521e60cc70f33090504d4035616470022409818740f331d440cc702340254008300120254003331641647002203a557440a83024416470c5613b60115001206240ea400330d161647002200610ce8008612b3065700b500120bd803d436b503a70053002201c300c201c3107201820012006130b80094055808d611e708d60bf701150172296802660be806640ec706640f57008301a200940714005300220ef50ef50053002207e50e45005315550e450053002203210140 487 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal205 : ¬ fitsRows (hostAt hosts5 205).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcd6f37c5a72ad1ee8c16a6b0e64a08510c01,0x9876542310),(0xffbbcc5edbd66307bab49c928399ac5a86229020,0x9876453210),(0xffbbcdeb38bd9ac5a92839ab49ca307b8a418820,0x7698543210)] hints908 0x3000300030e841596087302a601d30ca402f50163042701f7028401f7028461631c361b1460670e7305331a36015508b424c30106078308f8039700220ae703c63537094300b505e418e400530133002203e302a601d304d408b41ee3148602f5016303f7067700f4049702040053341328b4091618b4060315e601f700942f842b9311c601151f480c863e371bc6015510b70464067700f4005300030133002203770b460334118702042b7517d41f9610670c0509f5085400e32015110601e40e26027507441315031601e41d561e650b74008308132c080a460214081346680a460214068303970db8215606a6020416d845360367033400830003002202a601d30074022308f8039721c806c40f770b9400e30df80234193602843ea845c41fd70284011501330022012703d4036703d400530c3705060ae703c600b50022000302d30061000300030ae703c63537094300b518e405e400530133002201f7028401f7028461631c361b1460670e7305331a3601550e841596087302a601d30ca402f50163042708b424c3010608f8078303970022000303770b460334118702042b7517d41f9610670c0509f5085400e3000308132c080a460214081346680a460214068303970e26027507442015110601e41d561e650b741315031601e4008306a602040db8215616d845360367033400830022067700f404970204005303e302a601d304d408b41ee3148602f5016303f7000318b4060315e6341328b409162f842b9311c601f7009401151f480c863e371bc6015510b70464067700f400530133002202a601d3007408f8022303970133193602840df802343ea845c41fd70284011521c806c40f770b9400e30022036703d4012703d400530c3705060ae703c600b5002202d30061000300034e341d9308f81248039731860d3416b303c600b518680b57013300221268132701270ee703341bf80204012702040033000303a50f3302f50163295702a603e3090504d409050f7603e304d402f5016303f7002200030e5600f40a0500f400530f3303a502f50163295701f7028418c33787096401150022045640661ed51be40873045620a422951596087302f5016304270133036700f40a9532570956008300221f780aa7002200030061000301270ee7132703341bf80204012702041268003300030f3303a502f50163295709050f7603e304d402f5016302a603e3090504d403f7002200034e341d9308f81248039731860d3416b303c600b518680b570133002203a50f3302f5016329570e5600f40a0500f4005301f7028418c33787096401150022045620a422951596087302f50163045640661ed51be4087304270133036700f40a9532570956008300221f780aa7002200030061036703d4012703d40053013313b600d50003001202d3012703d4036703d40053013313b600d50003001202d300840da25b2427961c553297095621025da65d92548817240ac40da200b3000300845da65d92548817241c55329709565b24279621020da20ac40da200b3000300a104e60074019702a60bb30074019728d624b302a601d304d4084304e60074078300471b551da3007402231536007407830047002202a60bb30074019704e6007401971536007407831b551da300740223004704e60074078328d624b302a601d304d408430047002202c601d3117601d304d4045503e3007402230047140401060b3539850bb30074078300470a340a340ec7026626f40a9511671d18156632d7177605740083002239850bb300740783140401060b35004703e30074022302c601d3117601d304d404550047177632d705741d1826f40a951167156602660a340a340ec70083002200610140 675 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal206 : ¬ fitsRows (hostAt hosts5 206).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38b5e72ad1ee8c16a6b0e64a08510c01,0x9876542310),(0xffbbcdeb38bd9ac5a92839ab49ca307b8a418820,0x7698543210)] hints908 0x300030003000309e606b407d4011509e6028421a60115000300120e0300d50022001207d400330022059405943ad40083033401c3051300030012073407340f44008303340033051300120003000300610564025402b411a3029300220fc51465004728630fc521f6004709a513661b5501d30ca409a501065dd30ca407b709a7150615d609a715060155002200030a8355b30047000308f806e401970bf402b400e30244043607730047002209040a830d940047000308f806e401971e1402b400e302440436077300470022009400940574005307230e1407230e140723007407230074082700031ce602c60155214602c6015505f500740f16043608270484048402930022154705940f941547059400e300030356044413d500470356044413d500472da40c230cf4044407b7002202e50886088602e50022006100030003265300741248039700d5061305a5002200120062003300220012034401b3002200612233019704c60c4600b503560197002204970ee703d4036703d4036700f400530003168700f40be80a341f870033002202d300940d24005311f804060b2754e603a70053012700940053002205e401c300c20244019753c7525400b507e6052500c20061000307681038057405740be8003340b81fa603a521e60cc70f3309050074035616470234132707440be80033002203e30074035642570022409818740f331d440cc70234008300223cf60163024424e709873696096400b5162706d400b5002203a557440873024416470976011501270094005300220be8062413270ff4003301270714005300220061036703d418e4382704640053002201c300c201c300c20182001200610a3417370c370f9405b7106702751067027504f40377031602040377031602040be8008301a20ef5005300220ef5005300220e4500530e450053002203210140 343 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal207 : ¬ fitsRows (hostAt hosts5 207).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda72ad1cd6460f59cc55250209060,0x9876453210)] hints908 0x30ef6052502340ed60115001201b3001209d401c30d140d140513001207c408340083025405840083001205a50012001200a100030012088605250012048401c30022097601060115175600d500c202340254008307c400e300120b6400330964015500c20061000300d500120012003300220b9401c3001206b4003300120061000302930062041410360bf709c500940464005319c730c8052507d43bc401b301a2051644340f570d73184402230a730683336539b3021406830197023401b302c606d40ed6015501a204c60e5300b507e605a5002202e5097605a500221df7076801c302b40b94083400e37794077305440b5701a20734073401c305e401b32b84578305440aa700220321000302b400940053010600d5001204c60a1600b5182300d50022061304c600b51293061305a50d86061309c5002200940794005300220254025401b304141bc60525147305a500c20254003305e40b9401c300220234023401c30b8205e402c409c30321000300a100030003385700f428a802040053017209b3789703c62eb80de600b5000301720a641f130033002200d500220381001200c201c30b8200a100120012002200610140 220 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal208 : ¬ fitsRows (hostAt hosts5 208).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca307b5cc52d0931ca320440,0x9876543201),(0xffbbcdeb38bdab49ca1162d4f734e64a0a209060,0x9876453210)] hints908 0x300a102d4125123110003000300c202d300a100030140 12 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal209 : ¬ fitsRows (hostAt hosts5 209).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca3073dab62909394c320440,0x9876543201),(0xffbbcdeb38bdab49c64d62e0f71cc55250209060,0x9876453210),(0xffbbcdeb38bdab49ca2a4a0e62c1ee6b16418820,0x7698543210)] hints908 0x300a102d4006400640003622704a2064400e300c204a100030140 14 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal210 : ¬ fitsRows (hostAt hosts5 210).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda72ad1ee8c18d4a16a3986229020,0x9876453210),(0xffbbcdeb38bda307bab49c9ac290620816a4a0e6,0x9867543210)] hints908 0x3000300330012001200d500120033001200a10003088602e5092406c4029300220d442df405d70584058400e301821ba40af601550172048402930022310600f40505005300220381000316a325d41596683300b50172023401c3003300c200d5094305a500c20e5602540a050714005372240b57017204c401b36c460aa700c203810003001200c2001201b3001201b300c200a1000300a1093400240934000300b300b300a10012001211a300c200a10140 90 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal211 : ¬ fitsRows (hostAt hosts5 211).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda72ad1cd6460f4a16a3986229020,0x9876453210)] hints908 0x3000300d5001200120da209c3052500120033001202d300a10003029302930022009404640053048402c40d7300620ff408340ff400e305840584058400e301820af60af60af60155018202e509241e140403002202e5358600f42c35040300220321000300d500d5001207d4058408930033001200d50012003307c40454008300120033025402340083001200a102c402b401b3092401b3002208860a160525066403a705b702c4005300120484056401c326b5021426b50214054436a4039705640564025400e335f727b50b9402b400e301a2108610860284015528f8021402230b57022302440427018204c404640033285633c3021412a40aa706240b64003300c20d8605a5351719535c66074402c601551345035603f708c6041400d501a2161306570e670e3600b5002203210003001200c200d5001201c300c20033052500c200a10003000300a130573b480ed60bc501720de2093507140293001211a310d602e5092419b3002244a73548073405131f13017202c405e402d30321001200b300a1060306572eb803c600b501721b2503a728a800f4005301720047003300c200d5001203810140 215 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal212 : ¬ fitsRows (hostAt hosts5 212).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca307b9ac5a90931c8510c01,0x9876543201),(0xffbbcdeb38bdab49c9ee8c16a6b0e64a06229020,0x9876453210)] hints908 0x4b1038100a112c8313200a3000700a1000300a100030140 12 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal213 : ¬ fitsRows (hostAt hosts5 213).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38ad2f67b9ac9ca3041ccb524a209060,0x9876453210)] hints908 0x307d40ed62184011515060ed607d40115001210f30c8602e50e4506c40a66009400530022048406c402930022356624e5067700f41f6600f4005300220594083407c4008303b4096401550022059408340ac400830584058400e3002200610003000300030293001204140df82146070519c750b8052500f40a160525067700f410b704640053002205160db80584040339b3151426b502144be539b3021405f408430773019702c6096408660155048401b3013300221df7055801c302b40b9404f400e37804077305440b57013300220734079401c32b84578305440aa7255401b3000300120ae703c60c37050600b507e605a50003002202e5088605a500220003006100030436052504360ed601150012000307c400330012043600d50022001207c401c30003096409640115001207c40834008301330254058400830012006100030293001219c704140df809e605250fc50c9600470fc50c9604270307030709e6030709e6030711c60155002242b705160db8058401c302c61036015504f402b400e30ef50a660b9402b400e304840484029300220a830544004702b4100400e370280544019701f56ec3043607b700220a83054403f702b4058400e366e8054401970be80475255401b300221687012707340127073401270b7400e30a6316d6075402c6015505330b4504440827055830560e0305a5002202e50886088602e500220061000304c6061300b50d1616470106010605a500220d24009400531c1825d42af606570f6706d400b50022009402b40053028400d5097600d500220c4604c600b5010600d50022567820c62b6403a7161705c600531947013600e61947095600e600e30022316407b70254003304770127255401b300220254025401b307c400332328170801c305e409263bf564751f55023401c300220234003300e611f81ad600e611f805c6008310850564056414660b9401c30022006100030003067700f410b703d400530133010600d50022000313b600d500120ae703c65237008600b50003001202d30254003307d407c4089307d40033002205e401c310720ac400331cd600d50414052500220061000330e601970d860c4600b50c960197002205b705e4049703d402930484092401b300221524019704c60c4600b5129305a500220e6707e60fb7008602e506c40516047507440033002209240d24005308860d8605a500940d24005310380b27463505c6005304970094049700940053002202c402c401c30b8205440197056401b311f7074411f7456400b504840714052501a203211798179803d4167703d4167700f4005301a202d317980464167703d40fa4005301330172001201c3018201c30b82018203210ae703c60ce80de600b50133017202d3385700f428a8020400530133017209b3023401c30033002200d5002203210140 519 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal214 : ¬ fitsRows (hostAt hosts5 214).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c9ee8c16a6b1262a0e209060,0x9876453210),(0xffbbcdeb38bdab49c907314831041183dcd62d49,0x8976543210)] hints908 0x4a30012029300c204a3029300c204a100030381000300a1000300030003038100030140 18 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal215 : ¬ fitsRows (hostAt hosts5 215).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb36ae2f07b9b49ca28398ac5a92209060,0x9876453210),(0xffbbcdeb38bdaac5a928398b49ca307b9a418820,0x7698543210)] hints908 0x3000307d40ad61756011521a60ed607d40115002207e506c40a66009400530e4506c40a6600940053002207e50a66009406c40053002223561555067700f42ca600f400530022059403340b6400830594033403340083000300220f4408340b640083058405840b6400830003001200030061000300030293002219c704140df80af6052528630fc50c96078300470fc50c9604270307030709e6030709e6030709e601550022000342b705160db8058401c31ab302c60866015504f402b400e30ef50a660b9402b400e3048404840293002218940a8305440a830047000302b404f400e35fe315140544084303972824043607b700220a83054403f71ab302b4058400e317e3021405440683039706a602040475255401b30022012701270734012707340127073400e300030a6316d6075402c601552a96044408271936028430560e0305a5002202e50886088602e500220061000304c404c404640574005303a521e616470f6702840f6706d4010600d5097600d5002205b70464049704640367036703d400940053194825d42af606570f6706d400b5010600d5002211f820c62b6403a7161705c6005332b7013600e600831947013600e6008300220f331d44164702540033298876f7013600330022287707c4067702540254003300e645080083036701e4450800830414256831770d960fa4171500220234003300e611f805c6008305642348146656a8440502840893002200610003000313b600d5002204970ee703d4036703d4036700f400530003010600d5002202d3025400330127009400530022138401c300c20ac400331627074400b50414052500220061000303e31524019704c60c4600b50356019700220ee7046404c4036700f4005306c40516047507440033002200940d2400530c3700e60b27463505c60053012700940053002202c401c300c2024401971627074400b507140525002200611048104803d4036703d4036703d400530133001202d3001201c300c201c300c2018200610d5505b70d5505b71067027503340d5505b702040d5505b7020403770316020400330133017209b30033002200d50022001203210140 397 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal216 : ¬ fitsRows (hostAt hosts5 216).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcc5edbd66307bab49c9494358b38c4131480,0x9876453210)] hints908 0x300030003068401f5087302a601d3007402a601d34874043602f50163042701f7009401f70094009408d60bf71116109617d301f706d4015501f7028401f7028407d428630bf71116109617d301f721d401151fd7028401f70284048422f3206706d416370e7305331a360115000300220c3714b70de60ae703c60ae703c600b514a705e4036703d418e400530003002202a601d3090504d408b408a3010608b408a30976044402f5016303f710b704970204067700f4067700f400531de81403156801f700940ae703c63e3711c6015510b704970204067700f4067700f4005329143ff83dd7091618b4060315e601f700946174421319631e9711c601151eb7106824a4091614980603030706f601f700944017342738d3030706f601150133000300220377031605741fe80204026606640f57106702750127085400e31e38153527781315031600f4067700f40f770b7400e301f702840df81936028401f702846a880d1630f30115023422e349f81d562b0321d402341fd702842a3706d40115000300220127012703d4036703d4036703d400530c3714b70de60ae703c60ae703c600b5002203770b4605845ac702041b8606640f5710670c0509f508540083262641583f4701e40e26027507441315031601e43346400518a51a870b740083118702040db806a60204036703344a7704750b740083081354680a460214081346880a4602140a8303970003002261070b460334118702041196293459d705c610570c0509f508540083037740c8177601e413f80275012703b40377031601e4418710673665012703b40083215656360c0509f50854215656450b460334049705c60083081323f80a46021408134678166602140f230397002202d300030061000300030003000301f700942d47009475f80603030706f61498060303072d16011504e600740f16022303f7048405740053204601d300742e06007402f5016303f70094057400530133002201f7009401f7009414980603030706f61498060318572d16011508b44cf301060f16078303f7067700f410b7020400530905268601d304d42fe41ee3148602f5016303f7067700f410b702040053013300220377031601e439d7031601e47f680275012703b413f8027501272cf400830377031601e40377031601e413f80275012703b413f8027514a72cf40083120323f81666021412037cc80a460214077308132c080a4602144c1526930214077303976a5805c603770b4603340768215609f510570c054b4504f4202713365a041336008329341c2705c603770b46033484b41c270136201571e6033409f510570c051d567a6504f405371336712845a6033400830133002204e600740cf40223042702a601d300740cf402230427759806d401f702840ab8023411161096773337774d266ae745c41fd7028458360284011518a51a8704f4131503160204036704640e26027510482d0426262487057400e301330022088608c600b50ae703c60c370de600b5012703d4012703d40367036703d400530003002208b408a301060d960ca402f50163042704560e840873117601d30ca402f50163042722f3206706d401f7028422f32067074434137bc40ad6053316370e732f847bf3086601f702847bb87b840de6011519631e97086601f700940fb70506112326c833261e7807542914280708c601550133002204c608c600b50ae703c60c370de600b5012703d4012703d40367036703d40053000300030022000302d300610003000300031a4801f700940f870603030706f619161e570115090502a601d304d40f7601d3090504d402f5016303f709051b6501d304d40774287682f31d6683c37b2471c502f5016303f70c7841e65be30d3405330de600d50003002200030c3716b30de60ae703c631b60d3400b518861ec5115403a70bd803d400530133002219e80377031601e408070275012703b40a341f870083013310b70a050204067700f40e5600f4005309050fd4024426a314860f16077303f701f7028411230e1609640b07009414980e730866011502a515c40956051609f50475085425b800830133002204561d661ed51be40873045620a422952a86087302f501630427013380b3007403561c750ca40cf42005042701f702840df81936028401f7028423e73ea81b1401153c954d6480d32816200503560427000300223d544af306570ce8008600b5002204563e04087313d649e62f257c357064087302f501630427013303770b4601e40e260275074417a62255138413f80c0504f40083118702040db806a60204036703342e8704750b7400832fd50a4602144e134d087c942a760773039700030022126810955bf400e609f502040033000300e602a515c405c615b6027501e412e509f503b400835e6801d30fd40773024403f708130a46021408130fd846b6021407730397002202d3000300610003000301f700942d4700940c170603030706f60c17060303072d16011504e600745e6803e30074022303f7076805740574198701b3204601d300740f7601d3007402f5016303f713273bd40574126801b3000300221b6501d3098501d304d402a601d3007404e60074035602f5016307830047197424c3010601060455078300471d661ed51be4045608738434229510f6045608730223042728d603e3268601d304d404e6007402f5016302f5016300471d661ed51be415960873825422952a860456087302f501630427013300220377031601e439d7031601e406370275012703b40637027501272cf4008302a601d30bb304d4292408a3010604e60074024402f501630b35004701f7028402a61d7617d3096400940b07009401f7028456f4448708d609d70155076804f40f5700e308b408a3010602440b3502a601d300740436077302f5016300470e26027507442015110601e41d561e650b741315031601e400830133002204e6007483d824d539e44ce301060223042702a60bb300740074084302230047053713361115109576a40956026617a6225505740367057447143b2706640a6700e30db85758020403670464249412170367057400e321c85d15115403a77b58147400e3002212681a551a551ad601270204012702040033090502a601d304d45db601d3090504d4022303f70ab808660bf701558113557411e700942ba68123263406570155012702041268012704640a340a340ec7003300223c95414408a3010620a424d52bb3010607f50163042703e302a601d304d4584600741075016307f50163004702a601d300740356078308b408a301060444200507f5016300470df801f700940fb70506240610070fb708c6015579a502860ec702665d661ec5115403a700e30133002232073c0608c60c7805a503e302a601d304d44b1601d3241504d402f5016303f718b4060315e6341328b409162f842b9311c601f7009401151f484a166cb40657723805660155126801270204012704640a340a340ec700330003002200030061000300030003030703c60307272600b5030703c6030703c600b53fc43ae804771b38115403a701b301270624170804770367009401b30133002201270807027503b40a341f870cb84177031600f40083012700f4012700f40053013302a603e3090504d402a601d3090504d409050f7601d304d409050f7603e304d402f5016303f701f7009401f700940c170603030706f60c170603766806f6011500220003012700f401271e24005303070f87060306f619161e573c282ec70094011501f700940ab801f700940c1706030866011501f7009422e32d8606d401f700940c17060316b306f6011500940d2400530022012700f4012700f40053030703c6030703c600b5012700f4012700f4005302b600f409f500f40053013300220003045640661ed51be4087304561d665d3538b40873045620a422952a860873045620a422951596087302f50163042701330377031600f40768036700f40637027504f4008301270637027510570c0504f40dd702664d2518c446180956053713360ee70637027510570c0504f40dd7026642040a952b57095605371336008300223d76015814473d540e73065705a5030703c6030703c600b50fb7091603070976052500220377031601e40377031601e406370275012703b4063702751bf803b4008301330377031600f402a515c405c649c700f4063702750a0503b40083053702660537112433e41c3527040a95247705c60dd702660e94776705c605370266112433e41c3527040a952477053705c60dd702660e945a8705c6008300221da43ae86fa800e604770c17588400e601b304c60c4600b531860d34053303c600b5036701e40127023401c30133002202d30061000300030ae703c60c370de600b50003053300867a460d3400d50003001202d3067700f410b703d4005301337af60d34053303c600d50003001202d3067700f410b7020400530133041422e32d865b8806d401f700940a9682e3206701f706d4011501331f480c560f6706d4011502840b1600d500030003001200030ae703c60c37008600b50003001202d302b606b409f500f40033013305161d560275012703b42015031601e40475012703b40083013322b8021408130a46021408132c080a46021407730d554cc3151407730397000303442704329709560ac471180344133600831ab30012000321c806b4047503b4008301331d762d9501e409564ba5041442345c58095609560083013319634d350214267515140b570003001217240084034456a864250644210209f503d4284730a50284210202b60ac420b21073000302d300a1000304e6007401060223004702a601d300740bb30074022300470b250bb3098501d304d402a601d328d624b304d404e6007404e6007402f50163084300474c2503e300741666007408f80047098503e3007415360074099800470022195424c3010601060783004705f404560c2304e6007402230047098501d300741536007404e600741536007402f501630783004704e6007404e600740998004709850bb3007402a601d3007408f80047002204e6007400740223004702a60bb300740074022300471115590570141d1815661b540cd8026605340f5706640a671315031605741776057400e30074022315360074045500470db829683f370bf413e7057400e30022292424c3010602a60bb3007407830047117603e302a601d304d42456007402230047009401832ee411e70ab801f7009400942b333dc708660603185708660155009408d611e7009408d60bf701555d450bb30074078328d624b324b304d40b350047002203e302a601d304d4117601d302c603e304d404e600742456007402f501630455004708b408a301061404010604e6007427d6007402f501630b3500471116109617d31e7807546053137800943d140bf708d609d701f7009424a408c6015502662b243f740ec707680537026602661655769704f4027514a704f400e351d7137800947867320708666ee708c61e7826c81123332607546b4807e675486a7768c401550a340a340ec70e940a9511671d1815660a860cd801275a761e6504f40266012736650594143600e3002239850bb300740d96007408f8004703e3007457d6007409980047010607831404010608430047026606640ec7026606640f5700e351d70cd802664a87132704f432d70574104816552d04573805e44a872cd50bf400e3002208b416f30106140401060998004708b416f3010608b45fa3010608f800470df830b837671ce6192708c6015508b416f3010602236bb601d3117601d304d40783004719166d5411e7339618c32d671e7807545f241378030781b42b9308660094030738d3150617640155002200610ae703c60ce80de600b50003001202d30e8401630b57013331860d34053303c600b500220003067700f40bd802040053013302a515c40956051609f50475085425b80083013308b45ff3148602f5016302a603e3090504d403f70003001200033cf623850aa70003001202d302b600f409f500f4005301330516111515c405c617a63c3501e404750a0503b4008322b802147d852693021408132c080a46021407730773039703442e870c0503b40ac411870344133600830022000302a603e30ca402f5016304560e840873042701331a662d9500f409564ba500f40a9575a7095630a53b54008301330012000300a101f7009401f700940c170603185708662c13326801f706d43b48015501270637027503b4012718a51a8703b44c46248700f40377031600f4008302a51bd81ad602a56b181ad60a340a340ec7119611962027026600830022000305f422330197030703c6030703c600b507230074019700030022053702660377031602040637027514a704f41067027547f80854354800e300030e26027507443d75110600f455c61e650b741315031600f40083009401f7009401f71096111617d306d401f7009408d60bf70155002238433e550197030703c62dd703c600b50723007401970003002203070c17060306f6030719631e9706f661e4280703c601f700940115012700f4012700f4005318b4060315e65ee328b403c65ed42b9311c601f700940115012700f432a700f400530fb703c60c862a681bc60155012700f432a700f400530133002202660266053702660db835481455145504f400e3000302661fe80204106702750127085403770316057406640f5700e3036700f406c410480b9400e3002209a50106019709a501060197030703c62dd703c600b50022000300610140 2450 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal217 : ¬ fitsRows (hostAt hosts5 217).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda72ad1ee8c1a941d8b50c4131480,0x9876453210)] hints908 0x300030012001200120012001200610003124512450d670a5412450d670a541463124512450d6702b402b410a302b4079402b410a3022310c30d6702b402540513017219d718061dc500621245146313430d670a54146313430d670003032100030012001201b300c201b300c200a10003007400740fe7017207140033001206e456840cb7017210d600d5001200120381000300121af300d500120012001202340033001200610003000300120012001200a100120012001200a10140 95 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal218 : ¬ fitsRows (hostAt hosts5 218).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdead5a671783dd3945a941d8b50c4131480,0x9876453210),(0xffbbcde98b525073148310419c5ed5a4e5183dcd,0x8976543210)] hints908 0x300031a4808d704140f870d030307212624061e57070504e600742fc803e30074022303f71b6503e30074396601d32fc83953024408e5160303f70c7817c30c642206094300d500220ce816b30de631d412b3065708070e730c6400b51c161eb5115403a70bd803d400530133002219e8209706a601e4080704750497139424941e0704030bd80a0502042285115403a72f682b440406005304e60fd402440f762663007417b4077303f712f7028411230e1609640b07041428580e73086601152607074400e612e51bb427880083002204e60074424824d539e41c6301060223042740d6007403561aa517f408a30106244613d504270b0702840df819f602840b07028443c82206314301157d0824d541441c63281602230356042700222aa412b306570ce8008600b500222fa41db3010613d631f82f2522854a341a6308e50163042714c70b4601e40e260475074417a61ea513842bc80c0504f40083118702040db806a6046403670334169704750b7400832fd50ba602144e134d0839442a7606830397002212682a5504060a050204003300e602a515c4040615b6047501e412e509f503b400e3845803e30fd40223024403f708130ba6021408130fd83ce602140f230397002202d3006100030003000304970624067700f400940053002213a70505067700f416c600f4005300220ad60ad6011502340ad60115000300120334033400830b640334008300030012033403340083033403340083001209b3006100030003000312f7041401f7041459480d030e67212608d60bf7070527f5007423d608270fa40d240053098503e30074176608e5160303f7009405740053013300221fe801e4208706a601e44c78047505b7139406640f570403120333780ba602141a15207302140683039726b5007402440f2300470b2503e3007402440f2308e51b4305d7002204560a731d3407b704e600740356084300470464046400e3002212d60c4600b5012703d4036703d40053002208b416f301061c0408e5016304272845340401060356078308e5016305d7050605060155002204c608c600b5012703d4036703d400530003002202d3006100030003000305b700f405b71e240053030703c6030703c600b500941a24005300220e6703c60e67272600b516a30c64122305a50022049700f4168700f40053002200c20b07028426d632f306d40b07028416370e7316b31a3619f602840115001203770b4603341f04389505c61187020410570c050a05085406a604640083024406830397002204c6211600b50e5606241cc501b303560f23039700220061000300030012002200d50003001202d30ac400330003001202d30da200b302d300a1000305f406930074004705f4069307a4004705f40693043605f4069300740b3500470693043604550047069304361135055701a204560a730106004715a804e600740047007400470074055701a204560a730a56004715a8166600740047245600740047098524b307a4055701a204560a73044404560a7301060783004714e80ba60074004714e8072307a400470d960074043602230047098503e3007404360223055701a20a730444084300470106004703e3007400472f03007404440223004701a206930444068305570106055708b416f30a56055726c322d4010604440683055701a20321001200c2001200c201b3002200c200a1009404840053002240842bd41c351ad61196130629a5237508545895031602040083017209b3110600f405050053002202662ad80f9438170204145504f400830133017203210140 653 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal219 : ¬ fitsRows (hostAt hosts5 219).toFinset :=
  sparse_reject _ (by decide) [(0xffbb9c5f9bd4a307dab49a9283b9ac58c4131480,0x9876453210),(0xffbbcdeb38bb9ac5a9283dab49ca30798a418820,0x7698543210)] hints908 0x30003000300030e84159608730e840456087302a601d30ca402a601d30ca402f50163042702a601d302a601d304d408b408a3010602f5016308f802f5016305d701f7028401f7028407d422f320671b1483470e7305331a36011501f7028401f702840c7822f3206706d416370e7305331a360115000300220c3714b70de60ae703c60ae703c600b514a705e4036703d418e400530003002202a601d3090504d402a601d3090504d408b408a3148608b41ee3148602f5016303f710b704970204067700f4067700f40053261501060d96090504d408b408a314860f1602f5016303f710b710b70204067700f4067700f4005329143ff83dd7091618b4060315e601f700946174421319631e9711c601151eb7106824a4091614980603030706f601f700944017342738d3030706f60115000301330003002202a601d302a601d304d402a601d3007402f5016308f802f5016305d726a3007404560e840873204601d30ca40cf402f50163042701f702840df81936028401f7028423e73ea81b14011502344d2618c3544774862b0321d4193602841fd702842a3706d401150003000300220127012703d4036703d4036703d400530c370c370de60ae703c60ae703c600b5002203770b460334118702041b8684d41c271f9610670c0509f508540083262641583f4701e40e26027507441315031601e43346400518a51a870b740083118702040db806a60204036703342e8704750b74008308132c080a460214081346880a4602140773039700030003002203770b46033411870204126829341c2705c610570c0509f508540083037740c8177601e413f80275012703b40377031601e4418710673665012703b40083215656360c0509f5085406a6020456450b460334049705c6008308132c080a460214081346780a4602140773039700030022000302d30003006100030003000301f700942d4700940c170603030706f60c17060303072d16011504e600740f16022303f707680574057413e7020401b3204601d300742e06007402f5016303f710483bd405740367046401b30003002201f7009401f7009401f7009401f72c1376082c13326806d40ab8163706031857086622e31c361b14015508b424c3010608b424c3010609980783078305d70e8404560873117601d30ca402230427009401f700940c170603030703070866339618c32d6701f706d4191611e701550e841596087302a601d30ca402f5016304270133002200030377031601e439d7031601e406370275012703b40637027501272cf4008305370266053702660537026605375e1573385e1553b805c607681057027514a704f402a517d41f9600e3000301f7009402a61d7617d3096400940b07009401f7009456f4448708d60bf70155076804f40f5700e30e941c2705c6053702660e940a9511671d181566201511061f55020409f5063702751d561e6504f453a815660537026657981776020400830e26027507442015110601e41d561e650b741315031601e400830133002204e600740cf40223042702a601d3007402a601d3007409980223022305d70003053702661115109577240956026617a6225505741a662d95057447143b2706640f5700e318a51a8704f4131503160204036704640e26027510482d0426262487057400e321c80f770b9406c400e300226e75031602041a551a551ad601270204012702040033090502a601d304d408b408a31486022303f700030ab808660bf70155529611e700940ae711c601550127020403770316020401270464012706370275012703340033002208b408a301060d960ca402f5016304270266037703160204063702750127012704f41655012708540a340ec700e300030537026622e483141c35095602660a34726435970dd7026602660a9537e726f40a9516970dd705c60a340a340ec7008319631e97086601f700940fb70506112326c833261e7807542914280708c6015537a40ec7026606770b7400e3013300222a683c0608c60fb7050605a503e302a601d304d408b41ee3148602f5016303f7000318b4060315e6341328b409162f842b9311c601f7009401151f483e371bc60c8601550377031602040127020401270464063702750127012704f4003300030022000300610003000300030a341b2529c707680127063702751014012713271014053702660537026600333c282ec700940f870603030706f636861e57011501f7009401f700940ab80c1706030866011584181be4045608732245404348d883f4404373580998042701f7009401f7009422e32d8606d40c17060316b306f6011501270c3710140c1710957714095601270637027510140c1702a574a409560dd70266053713360033013300220cb84177031600f408070275012703b42b241f8700830be801270ee70204012701270204132701270ee7033413270127012703340033000302a603e3090504d402a601d3090504d409050f7601d304d409050f7603e304d402f5016303f7012700f40be80127132703b4003301f700940c170603030706f601f700940c170603205706f6011503a50f3302f5016329570133002200030377031600f4036700f407680637027504f40083045640661ed51be4087304561d661ed51be40873045620a422952a860873045620a422951596087302f501630427013301270637027510570c0504f40dd702660e940a952b5709560537133600830a9537e70956036700f40083002202a601d3265304d426e41d933c787c8646a53c88099803f7030703c605580307320706f600d566c80307030706f6011500220377031600f449c700f402a515c405c6063702750a0503b400830377031601e406370275012703b40377031601e4063702750ee703b400830133053702660537112433e41c3527040a95247705c60dd702660e942e7705c600830022053702663ec70266132701270a0503340e941c2700e638641b2529c7609746a505c600330f3303a502f50163295718c32d57096401f70284011545080127012703b40083013300220003006100030003012701270637027503340127020401270204037703160204003300031c631fa603a509050ca40cc701331f480c560f6706d4011501f7028405330de641e6796306d400d500030003001200030127012703d4036703d4036703d4005300031d780d34053303c60f6706d400b50003001202d3090518740f33090518740cc701335c7800e609f500f4067700f40053013301f70094270311780964011532e709560516008301330133001200036e940cb806b41d762d9501e44f8824d242342ed8095679f6165721020da2047503b40da200b31187020409f502042b755c0405c60033000305162ef805c600830133081339a80a46021407730397000300120003000300a1000304e6007404e6007409980223004702a601d3007402a60bb300740998022300472ea7111559053e947e3553b805c606640f5706640f571b540cd8026603770316057416e52a16057400e30a951a8704f4237510482d041196036704644c252487057400e37d651a8704f4132710482d041268036704641b552487057400e30022292424c3010602a60bb30074099807830047117603e302a601d304d404e600740998022300470b07009436862ee4060308370ab801f700940b0700940c17060318570866495318570866015501f700940df8191611e700940c1706030307086601550484339618c3544721d413e311e700942ee4191611e70155002201f71116109617d38563326806d408d60bf708d60bf74c541378009401f700942f53333408c601550dd702662b242b241b252ce70768053702660dd702660637027514a704f4237514a704f400e301272375795613c504f40dd7026626f40a9511671d181566709627b5177602040083012702755a761e6504f402660e940a9511671d18156632d51106177605740083002222e310685c3621d42a371e78075404840fb705068533280708c601550377031602040db80a340ec7026606370275012704f400e3036732d705741d1826f40a951167156602660a340a340ec70083002284431e970866112326c833261e7807540c780fb705063433280708c6015511960e940a9511671ad60a340ec702660a340a340ec700e316e52a1632d702042ea722e44d441c3526f40a95116705c602660a340a340ec700830022006101270ee70637027503341bf8020401270204037703160204003300030f3303a502f501632957013308b45ff3148602f5016302a603e3090504d403f700030012000326e41d9308f81e480397000331860d34053303c600b518680b5701330022000303a50f3302f50163295702b600f409f500f40053013301f7009418c33787096401150022000302a603e30ca402f5016304560e840873042701331a662d9500f40a953257095600830133001200031f780aa700030012000300a105370e94338511670e940a952b5705c61bf806370275085401270637027508540537026603770316020412680083000301270637027503b4012718a51a8703b44c46248700f40377031600f40083770518c446181ad6012706370275085404970e940a952b572ea705c61196037703160204202702660083002200034e341d9308f812480397030703c6030703c600b50bb300740b3503970003002203070c17060306f6030719631e9706f661e4280703c601f700940115012700f4012700f400530fb703c6140330c80115012700f40053013300220266037703160204053702660db810670275012708541455063702754a2704f400830003036700f41c542598008300223715010607830397030703c600b50022000300610140 1754 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal220 : ¬ fitsRows (hostAt hosts5 220).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e3062d4f734e64a0a408062,0x9876453210)] hints908 0x52500c201c301c3001210e301060155028400d501820234025400e301b301820f44003305a501820381052500d501720b94058408930033001201c3045405130b82003309640bc5018200d500c20381000300943bc4005304a202b400e302b400e3018209241e14040300c202c601550182038134a500c2002234a300c201c30012052500c200a10003001200a10003127728a806c40053018234e72eb80c8600b5017204a204a2038100c200c204a200a10140 90 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal221 : ¬ fitsRows (hostAt hosts5 221).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda959b9ac5ca3079cc55250408062,0x9876453210)] hints908 0x323a606b40bc523a606b40bc5001201b3001205a5001200120d140d14051309d401c300120d140d140513157401c3001200a10003219405251506052500c2048400330012059401c302540594051310a31072059401c3096403b40bc500030012088600d500120012000300a1000300032586052506b405250012000302b408930033001200d50012045401c310a301c3001202c402c409c300a1218421940525150621840525018204840484029304840484029300220594059401c305940594051301a20594059401c314f403b40bc501a2048415f4029300220886088602e50022032104c6061300b5043600d5001200d50012009402b40053043600d50022041401c30b825537632502c436c82c56091409c307c40033001207c4003305b700940477005300220321000300030172018201c30b820172038117980464167703d418e40053000301721798179803d4167703d4167703d4005301a202d3002201c30b8201c30b82032112b306577638172600b5017236b503a737381744005301a2001201c30b8201c30b8203210e6700860fb7172600b5017205b703d405b71744005301a2002201c30b8201c30b8203210140 219 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal222 : ¬ fitsRows (hostAt hosts5 222).toFinset :=
  terminal_reject _ (by decide) 0x1 1 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal223 : ¬ fitsRows (hostAt hosts5 223).toFinset :=
  terminal_reject _ (by decide) 0x11113113310 11 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal224 : ¬ fitsRows (hostAt hosts5 224).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117ad4973588290e608062,0x9876453210)] hints908 0x4852175112c83003313200a3000700a1000300b3141300a10003000300a10140 16 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal225 : ¬ fitsRows (hostAt hosts5 225).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a4a1173d8d52d2831c8510c01,0x9876543201)] hints908 0x10e510e505d714b724e60d8614b709e6015523a602840bc5018210c310c305d70234025400e302c6015501720f4401b3001204973b0409240497073400e310e301060155041405a510e302c6015501a200220d140d14051302b400e3064402b400e3056402c405640d73017203210003171500d5001200d50012089306440644051310a31072003302340254008310a300120033095654c5028408930012000300a10003000304970464049700f400530012000302c601550012049700f4049700f4005310a3001202b400e302b400e3001200a1218421940bc51506150601550182029300220ef506c44f280053001205940594051305940594051301720594059400e30584058400e3018202e50ef515f44f28040300220321000300d5001200d5001201c31072003305250012003307c407c40033001200a1061302e511460c770012019702b305a5114607b7006202c4029302b401b30062019721f603970d860a1600b5006202c401c30b8234f401b30d94039718f4052525d416272c7400b504a20dc411d70dc4082702c605a509240834005320c61a4500940053006203210003017201721b75038128a800f41c1644653f7403a70053013301722eb803c638a45b93065700b5017202d300d500120033004700c2038100d5001205b70484051637270505003301721ce80b27194705c60053017201c30b820033052500c203810140 259 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal226 : ¬ fitsRows (hostAt hosts5 226).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e1173d8d52d0931c8510c01,0x9876543201),(0xffbbcdeb38bd6d47b9ac9ca30398a45a92808062,0x9876453210),(0xffbbcdeb38bdab45a928398a49ca307b9ac18820,0x7698543210)] hints908 0x30003000323a606b40525001201b3001205a5002200120d140d1401c3083401c30003001209b30061219405251506052500c200030484048402930012059401c30003022300470012059401c3000306e4004700120886088602e50022006122a3007422a300740397043600d50022010600d5001202c401c3107202540033041405251627074400b5002207c4003301270094005300220061000301720172017201720321179803d4167703d400530133017202d3001201c30b8203213ef7046405b703d418e4005301a2001201c30b8201c30b8203210140 109 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal227 : ¬ fitsRows (hostAt hosts5 227).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e1173d8d52d0931c8510c01,0x9876543201),(0xffbbcdeb38b5e958c2726b1ee4a16a290e618820,0x9876542310),(0xffbbcdeb38ad2f67b9ac9ca30398a45a92808062,0x9876453210),(0xffbbcdeb38bdab45a928398a49ca307b9ac18820,0x7698543210)] hints908 0x300030ed605250012048402930012088602e50022083401c30b6408340513000300120003006100030ed6052500120003048402930012083401c300030b64083405130012088602e50022006122a300740397010600d5002222a300740397010600d500220254003308134b980a460214039728e52617013600e600e300220254003300e628e52617013600e308134b980a4602140397002200610003179803d4167703d400530133017202d3001201c30b820321179803d4167703d400530133017202d3001201c30b8203210140 104 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal228 : ¬ fitsRows (hostAt hosts5 228).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173dab625483988518801,0x9876543201),(0xffbbcdeb38bdab49b58b5265183dc818820398a4,0x9867543210)] hints908 0x70c1093430d400a30007000300a100d504a200d5018201c30b82091404a300330ea407c40033018204b100030003000300a10140 26 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal229 : ¬ fitsRows (hostAt hosts5 229).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb19b5e9594e1173d8d52d0931c8510c01,0x9876543201),(0xffbbcd6ef6ce272ad1ee8c16a6b0e64a06229020,0x9876542310),(0xffbbcdeab49cb38bda307b9ac5a8a41892839820,0x9854763210),(0xffbbcde9ac5aab49c8a418b38bd92839a307b820,0x5476983210),(0xffbbcdeb38bd9ac5a92839ab49ca307b8a418820,0x7698543210)] hints908 0x3000302a601d3117601d304d40223099803970e8438080873098501d30ca4078304271936028401f702840df832881b14015501330022046404c400532a371d0416a33c5400b5002202c601d3241504d408b408a31486022303f710b70464067700f4005324a40916140329e801150003002206a6020413e703340db80475058400e3177601e41c5436380083081312380a460214084303970003002200030061000304c4046400532a371d0416a33c5400b50022117601d302a601d304d40998022303970133193602840df801f7028432881b140155098501d30ca407830e843808087304270022000306a602040db813e703340475058400e30003081312380a460214084303971c543638177601e40083002210b70464067700f4005308b408a31486022302c601d3241504d403f70003140329e824a40916011500220061000303e3007412480397162706d400b500220127020412681bf802040ee713270127033400330003090500740cc700220003012700f40053090518740cc7002200611bf802040127020401270ee713270334126800330003090500740cc70022000303e3007412480397162706d400b50022090518740cc7012700f40053002200610140 227 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal230 : ¬ fitsRows (hostAt hosts5 230).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173d8d52d2831c8518440,0x9876542310),(0xffbbcdeb38bdab49c9ee8c16a6b1093984101483,0x9876453210)] hints908 0x3810003125100a312c800070003001200b300a1000300030140 13 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal231 : ¬ fitsRows (hostAt hosts5 231).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda9594e117b5cc52d0931c8518440,0x9876542310),(0xffbbcdeb38bda72ad1cd6460f4a16a3984101483,0x9876453210)] hints908 0xd5001200122394003300120033001200a10003043600d5029300620886052522a300744e77001207c4003328f802140683039704140ed6015507c402930182048401c302b4083400e34cb30544054403970094003301a226432ae44e7704c600d5002202e5043602e50012032100030003052500120b9401c30012001201c3001200a10003079402930062048402930012061302e5088602e500223084059400e30234058400e3018209760af601550182032100031af305a500120012122325f325d400d50172023401c300330182025401b300d56b74039701821cc50e56034400330d4442970172032100030012001200c2001200a100a100121f130012001200a10140 131 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal232 : ¬ fitsRows (hostAt hosts5 232).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda9594e117b5cc52d0931c8518440,0x9876542310),(0xffbbcdeb38bda72ad1cd6460f4a16a3984101483,0x9876453210)] hints908 0x300d50003001200120754003300120033001202d300a1000310f30a1600b5006208860a1609c5002207d40794005312030ba602141844022303970a160ed601550693024403f70182048407940d730734083400e34cb3054431940397062406b4062400e301a202230356042711b6147311b60155018203210003000300d50003001207540033001200120033001202d300a10003056402930062009406c400530022061302e5048405640d7300220594059400e3101406b4101400830182023414731cf6011501820321000300220012001201b300c2006100030012001200c2001200a11ae50f941e141996040301724dc33de70924214607140705017204a204a203810140 132 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal233 : ¬ fitsRows (hostAt hosts5 233).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a49cd6460f4a16a3984101483,0x9876453210)] hints908 0x300d5002200120033001200d5001200b300611cd610f300d50293006221f601971a0729f318060705002207d4056400331844022318440223184402230683019766d806d40ed6015513081146022342f70182681805c6083400e3566331640b57001855e40ef5253500e301820d94019712a406e40aa7075401b300c2154709241574040313080dc4134542f7001846d60a6318230155147305a501a202e5006204b10003000300030884050400b300b300d5001209c300b300c300a105e40293006235e405e402930062061302e518f402b302e50022059405132a4408430047018207540bc52e0406830047018228340455004728341135004701820321000300120012001200a10003000300c200c200c200c200a105f41a63007403f701720456022301060427018200c204a204a203810140 155 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal234 : ¬ fitsRows (hostAt hosts5 234).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda72ad1cd6460f4a16a3984101483,0x9876453210)] hints908 0x300d5002200120033001200d5001200330012006100031cd60a1600d50293006207e61af305250d8621460705002207d40794003318440223184402231844022306830197304606d40ed60155076805160f57036701e40403018204140754083400e30e84223315140b571e380475074406b400e3018205e402c401c34cb3054405440aa706b401b3002209241e1404030ab804140bf736c410f307051de80f6706d40c560155147305a501a202e500220321000300030003052500d50003001207c4058408930033001200d5001201c3045401c310a30012003309640525001209b300a105640293006206c40ff402930012061302e50c8602b302e50022059400e33084023407940083018203b401550b6406b4101400830182233409760a16011530140c561cf6011501820321000320e606130525094300d500220012094300d5002202340564005302340254008301723574025401c307c4025401c3001252a41086011510f31473171501826ab209144fd5107303210003000301c3001200a10012001200c2002200a103e30074264300745654135334770172186501061c63010608e5016334b70172143300c219a504a204a203810140 222 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal235 : ¬ fitsRows (hostAt hosts5 235).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38ad2f69bdcd9460c41ccb5244101483,0x9876453210)] hints908 0x30003000301f704140f062f970d0306f6011513c503b4110600f40ac4008327f50fd40244082700220344034400330012208706a601e406443a07047503b4008300e60344034412e501e4034403440d73110601e413c503b4064400830344034403440344008300221c4306f62e9327a413b6011571d600f47a35020400532e9327a41c4306f60f06011505660c860155002200124b850a731d3407b7361543a51bb4279600e3147406c400e30022006100030094009406c400530022067700f4009410b7062400530022110600f4009405050053067700f40094049706c4005300220b640b640f4400830334033403340083002203340f4410140083033403340334008300120ad602340ad60115023402340234011500220061000300030fc600f411b500530022265300740aa7002207c4023400330094023400530022024406830397024417b40f2303f700220e8401630b5704c6097600b50356022303970022035624460223042700120061000300940714005300220e6727262dd703c600b508f80197002204c610d600b505b71e2405b700f4005300941a2400530022024401970244045501060f230047002208f8019704c6211600b503560197002203560843007402230047001200610003000305b700f40ee700f4005300220e670de6144700b532c30c64122300b500220e6703c66e47061300b500941a240053002205b702040477005300220c6412231293171545f4182334582a2323e703b42cb7011500220e5607141cc5005304c6211600b5040607c415550893002203671744560806b42e4714f41a170083001200610003001200c20012001200c200120061000300940094649819d70115017209b3061300d5002200220254003300220266026667f813a70083013301720321142105160516142100a315560e46093407e60086093448e43f0400631cb40068006300070140 348 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal236 : ¬ fitsRows (hostAt hosts5 236).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bc60f736d5a4e4c290620816a4a0e6,0x9867543210)] hints908 0x30003000301b300120ed605253014086601150003001205a500220012083401c30d140d1401c300030012075404f4008306b403340083001209b300610003061302e50fa40fa407340293002205640293002206c40a66009407e5005300220594308400e305840b64023400830012059404f400e310140f4406b4008300c20af607d4097601151cf617560c56011500c20061000307680254051601b3094325f30c6425f30d3400d500220a1604c600b53ba8182300d500220b2702b60094056400531a8710a60254066403a733582d750516029300740074035608270414094300d500220794009400530022056400e6025412e5023401c3056402340083001223b82535003305160768036701e404750b7400e310860d3401065cd3097605250c3707c407c455980ea40033002201060106024407b7108652a401153c35064407d405c601b341f31c750214576869a646444ef7002211b50e5603440e56034400330754023400338023054447a826930214429700220061000300d50022001223940033001206b40033001200330022006100030254056409d411a30293006204140bf71036170519c730c8052515a80c9600473993007440530074004701a209f50094275500940794005305161217443414d302c60af6015504140af601550f33069304360c7709f5048427450484029301a21df7259801c302b4058400e317e30214054401970cd80475074406b4008301a214e80544004702b4058400e317e302140544019710850b250ff401b301a203e3152403e3152400470a730a73044411d71f380f6706d40c56011514733d2410f305a501a202e50533088627d6074402e50022032100030003001200c20012001200610003001200c200120012006100a1186501067de503e30ca408e5016334b7017209b301b3001203e3007403e300745654016334770133017205a50022002203210140 349 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal237 : ¬ fitsRows (hostAt hosts5 237).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bc60f736d5a4e4c290620816a4a0e6,0x9867543210)] hints908 0x30003000306b40033001223340ed60bc5086600d5000300120c8600d5002200120b9408340513083401c30133001204f4003303b405250012000300610003061302e50fa40fa40734029300220564029300221f6600f4009407e5005300220594059400e31014101406b4008300c2059404f400e31014033406b4008300c21cf61cf60c5601151cf602340c560115001200610003009407940053094300d500220e670a166ed710d600b525f30c64312300d5002204c6061300b5041404c66c16094305a5094300d5002205b70794167707140053002203440ac40624257401b33d84182315962a2361433876096406d4015500120e56056464b500330516009404750b7401b3040607c40406155508930022036701e46c65064410480b9405c600e3242702b37fa724640f061715002208071a0556b20914378710e656c20914107300610003000300d500030012001207540033001206b4003300120033002202d3006100030564025410f411a30293006219c70ab80a16070515a823d6082715a80c9600470d8609e6015501a209f5009407e5079400531df70768079404030a160af6015502c60af601555773069304360244082701a214e81d3407b70794058400e317e3021436a40197024404360223004701a214e80544004702b4058400e317e302140544019703440624062400e301a20924073400e30a730a73044458c407b703560444022300470b16147311b6015501a202e50022032100030003001200c20012001200610003001200c200120012006143570714338637f841c33de70924086608660155017243f402931ca500c23b97199649b71ae505e404f404f400e301a2092419b304a219b300c203210140 315 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal238 : ¬ fitsRows (hostAt hosts5 238).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bc60f736d5a4e4c290620816a4a0e6,0x9867543210)] hints908 0x30003000307d4003300120c9658d40427035658d40427000300120e0300d5002200120544054403f7083401c3000300120244024403f7033400330012000300610003061302e50fa40fa405940293013300120564029300221f6600f41f6600f407e5005300220594083400e305840584239400830012059404f400e3101403340754008300c20af60af6365401151cf60ad668e4011500120003006100030e6704c60e6708860a1600b502c40094005300221447182300d5001205b7009405b70484079400530414121809872d7604140d0311c6015510c3007403561647002205161038036701e404750b7400e30564040605640a050b9401c3023402340083001204772535003310860c64108616b31bc605251cd6061300d5002210e501060244164709760976011507d407940033001206240ea400330022006100030003000325223a65000300120033001200d5001200b302d30061068308430d6702930062045606930a5611d71345004721f600474c03007430e6004701a211350455271705f40a2307a40c7702c61ce6015502c6251601551146082711461f2701a20223004702b40bf400e31fb616d40197024411460223004701a20d94004702b4181400e3183406e401971834114602230047018219240a23152400470dc407b703560dc4022300471fb60dc40223004701a202e50dc41ac70022032100030003001200c2001200120061001200c200120012006100a11906146501061d232da40163004701721ca504840293002205f406930074552377a40163004701a219b300220e0302e5002203210140 295 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal239 : ¬ fitsRows (hostAt hosts5 239).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda959bdcd9460c41ccb5244101483,0x9876453210)] hints908 0x30003000306b40525023413b601150003001202b408930033001200d5001202c402c409c307540ac400830033001209b300a105e40293002206c40a6600940e3500530012061302e5048404840d140d73002205940594051305940b9408340513017204f4059400e30b64075404f400830182233467940ed60bc5175667a40866011501820321000300d5002200120033001200d5001200b30061068308430d670293006210e50c7710e50c7721f60047403307a4258605d701a20d440455271710c30c7709160ed6015500740c7711460c7711461f27006210c311d701e4083400e331c616d40397001855e40ef5253500e301820d94004710c311d712a406e4039710850b250ff401b3018236c41b332ae405d70dc411d7001846d60a6318230155147305f410f305a501a202e50dc41ac7006204b1000307680254051601b302c40094005300220b271f6604840564005305e407940053001204140d730b82094309c507c401b3001207e60a1600b5094305a5001206240ea400330012032100030003001201c30b8200a1001200c20012002200a100a1190606a501060427017205f41a63007403f701721433001211a30022001203810140 222 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal240 : ¬ fitsRows (hostAt hosts5 240).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda959bdcd9460c41ccb5244101483,0x9876453210)] hints908 0x30003000307d421460bc5028400d500030012064408930033001200d500120b940254051301c310a30012073400330525001202d300a1056402930022358600f400940e3500530012061302e5048404840d140d7300220594059400e30584239405840083018204f4059400e3033407541014008301820af630140af60115023430141cf60115017203210003000325223a6500120033001200d5001200b302d300a1068308430d67029300621308055710e5082721f600471a0729f31806070501a211350455271713080c7718060ed6015510e50c771146082701a210c307b71574083400e331c6316403970d440106022305d701820d94004710c311d712a406e403970624075464d400e3018215470924157404030dc407b717860074022305d711b6147362e6015501a202e5006204b10003009407940053001204c6061300b50012023402340053023402340083017207c4025401c300120976097601150172038100030003001201c3001200a1001200c20012002200a10456022301061d23016305d7018205f41a6300741b33238505d701721cb504a204a211a304a203810140 211 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal241 : ¬ fitsRows (hostAt hosts5 241).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38b5e72ad2116b1ee52d274188518440,0x9876542310),(0xffbbcdeb388c1ee6b2f6ad272290620816a4a0e6,0x9867543210)] hints908 0x3000305e406c40293001223340ed60bc5301408660115000300120e030c8602e500220b6408340513083401c3000300120b6404f4008303b40525001209b30061000300030003061302e50fa407340293013300120564029300221f6600f407e500530022059404f400e31014033406b4008300121cf60ad60c56011500120003006100030e6704c60a1600b5094325f30c6400d50022066403a705b703d4005333160c641596312300d5002205b700940794005304140ab809872d7604140d0311c601551f380f67028408d606570115274507d407940033002212b306570e67008600b500220e5605640a050234003305160768036701e404750b7400e322b8021408130ba60214081312380a4602140d552bb360767f330214077303973d84182315962a2361433876096406d40155002220f85bd70254066403a70083036701e43c3506441048075405c600e341f333f502140ba646440b57002211b50e56034400330b6403440033285633c30214547602140aa7002200610003000300d5000300120003001206b4003300120da200b302d3006100036cd410f30a1600b502930062045606930a5611d715a80c96004724560074004701a2275500940794005305f4069307a40c7702c60af6015506930436082727450484029301a214e80544004702b4058400e317e3021405440197024404360223004701a203e3152400470a73044407b7035604440223004701a202e55933088602e50022032100030003001200c200120012006100a14357338637f8092408660155017209b30484029300123b972ad80f9404f400e3013301720e0302e5002203210140 303 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal242 : ¬ fitsRows (hostAt hosts5 242).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117b16e6a8e64a04101483,0x9876453210)] hints908 0x3125100a312c8000700030003001200b300b300a10003000303810140 15 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal243 : ¬ fitsRows (hostAt hosts5 243).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcd6ef6ce272ad1ee8c16a6b0e64a08518440,0x9876542310),(0xffbbcdeb38bd9ac5a92839ab49ca307b8a418820,0x7698543210)] hints908 0x30003000301f7009401f700940c170603185708662c13326801f706d40df801550e84380808730e8404560873268601d30ca428d601d30ca402f50163042707d407d401f702840df822f369971b1401150c780c7801f7028416370e7305331a3622f3206706d401150003002214a705e4036703d4029340c73e131d0415f612930ae703c600b50022053702660377031602040637027514a704f410670275012708540db800e326a300740436098501d30ca40cf40b35042707d4193602840af608d60bf70155048448b66657193602841fd702842a3706d40115000300030022185707e60fb7008602e5577643880ae703c60ae703c600b5002203e3090504d4117601d3241504d408b408a3148608b41ee3148602f5016303f782175884302613c500f4067700f4005326150106044408b408a314860f16078303f77e144548067700f4067700f400530fb7091602c62a681bc6015534273ee3091633a438e3030706f62f533334091661371c43030706f601150003000300221b861b8613e70bf40db822e475371f9600831b8606a60204058406640f5700e3036701e402b410480b9400e3081312380a46021405440a8303970003000300221268126803770b4604f410570c0509f50854293459d705c600831196386451c706a6020448380334049705c60083106729d501e427e63675012703b416e52a1601e4416713c5012703b40083081312380a4602140c960f2303970003002200030003006100030003000304c608c600b50ae703c60c370de600b5046405e402930003002208b408a3010602a601d30ca4078304270e8404560873117601d30ca40223042701f7028401f706b457f60284328806d40df816370e7305330866015501f70094009401f7339618c32d6706d4191611e70c170603030703070866015501330022000300940574005302a601d3007460250074022303f7000304840ab8377700942e3325a601150905007402231925007403f7048402930022067700f410b702040053090502a601d304d408b408a31486022303f700030df801f7009408660155529611e700940ae711c6015510b70464067700f40053002203770b46033405376856321413363ca805c60db810570c0509f5058400e3000311960768036701e41ae51bb400830db813e701e404f400e34e085fc302144c1517e30214081312380a4602140683227567430214077303975a04133642240a9524771d18156609f51f5502042e7705c613150b4603341d1815665806033400830133002203770316020402661655012708540a340ec7063702750127012704f400e30003398501d30ca407832f430106042737a40ec7026606770b7400e358360284814618c32d671e780754053313e30de638c706d401f702841e7807545ce40ad6011501330022050607e602e5088602e50c3705060ae703c600b5000300220003006100030003012701271327033401270204012702041268003300031c631fa603a509050ca40cc71f4801f702840f6706d401150c7805330de641e64b2306d400d500030022000301270464036703d404c4005319480d3416b303c60f6706d400b50022090518740f33090518740cc7013311f800e60a0500f4067700f4005301f70284270311780964011532e70956051600830133002221c828770254161705c600830133036701e42fb42ed809560083081312380a4602142213039700030022126809f502042b755c0405c60033000300e62ef805c60083081312380a4602140773039700220003006100030768057405741268003302a601d300743e050074022303f70484377700940ab82e3325a601150905007402231925007403f7057413273bd4126801b3002260d5414408a301064ce3010607830427117603e302a601d304d404e600740998022300470b07009449a806d40df801f700940b0700940c17060316b3086649a84584015501f700940df8191611e700940c1706030307086601554c1510f65bc8087307831d667c251be44c6515960873042700221196036701e407681ae51bb400830dd7026647e805c60db8053702660dd70266063702750a0504f447e864a600e32e7705c60dd7026642240a9524771d18156645751776020400831c542598177601e4008300221c63010607832f43010604270377031602040db80a340ec7026606370275012704f400e30537133626f40a9511670956026637a40a3435970083002208c632073c060c7805a5090503e304d4022302c601d3241504d403f7140330c824a40916011500220061000300031da43ae805e404770367046401b304c60c4600b5030703c6030703c600b5036704640477012706240127048401b300220be801270ee7020401270ee7020413271bf81bf80334132701270127033400330003090500740f33090500740cc7012700f40be80127132703b40033013301f700940c170603030706f601f700940c170603205706f601150022000300940d2400531c63010603a51c6301060cc73cd6009411f706d401150127009400530022012700f4012700f40053030703c605580307320706f600d5012700f40053002200030377031601e406370275012703b40377031601e4063702750ee703b40083013306a600f4194705c60083002203670a05046404771da43ae84f8801b309873696096400b5162706d400b500220061104803d4012703d40367036703d4005300030c370de60ae703c600b50003001202d326e41d9308f81e480397000318680b570133097600d50022000310b70204067700f40053013319470956051600830133001200031f780aa7000300120003023400330133051611f805c60083056423485964520608930022000300a11bf806370275085401270637027508540a340a340ec712681268053702660083000301f7009401f700940df801f72c13755806d40c17060347d7086601550a340ec70127818713c503b4106729d500f4483800f400830022000303e30074019705f457230197030703c64c973e133c5400b50022037703160204053702660db81067027501270854063702754a2704f400e300031c542598177600f40083002203e300740197030703c600b50022191611e703075d271c4306f634273ee303c6767803c60115012700f4012700f40053140330c824a403c60115012700f40053002200610140 1150 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal244 : ¬ fitsRows (hostAt hosts5 244).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49b9ac5ca307a8831040941cc5,0x9867543210)] hints908 0x3006200b3003300c200b3003300c204a10062003300c2003300c2003300c2003300c204a10003006200b3003300c200b3003300c200a1000300a100030003000300a100030140 36 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal245 : ¬ fitsRows (hostAt hosts5 245).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49b9ac5ca307a8831040941cc5,0x9867543210)] hints908 0x30062003300c2003300c200b300b304a10062003300c2003300c2003300c2003300c204a100030062003300c2003300c200b300b300a10003000300030003000300a100a10140 36 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal246 : ¬ fitsRows (hostAt hosts5 246).toFinset :=
  terminal_reject _ (by decide) 0x330 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal247 : ¬ fitsRows (hostAt hosts5 247).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e117b5cb6290931ca320440,0x9876542310),(0xffbbcdeb38bdab47358b54e5183c831040941cc5,0x9867543210),(0xffbbcdeb38bdab49ca307a507315cd62d4418820,0x7698543210),(0xffbbcdeb38bdab420c41039ac5a928398b39460f,0x6789543210),(0xffbbcdeb38bdab44a0e629062082728c1ee6b16a,0x8976543210)] hints908 0x30062003300c2003300c2003300c204a10003000300a10003000300a1000300a10140 18 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal248 : ¬ fitsRows (hostAt hosts5 248).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e2e6c1eb6290931ca320440,0x9876542310)] hints908 0x304840525023425860115017209d401c300d5017207c4045400830033018202b408930033001200d500c203810062006200d500c20254003300c2003300c200610003008524e500a30068006800070003000300a10003517607e507e5005301720e4515740293017200b362d3018203810012001200a1001204a204a200a10140 65 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal249 : ¬ fitsRows (hostAt hosts5 249).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb19ad2f68c27273dab620ea4906628440,0x9876542310),(0xffbbcdeb389ca30bdab47b9ac598a41a92838820,0x9854763210),(0xffbbcde98b525073148310419c5ed5a4e5183dcd,0x8976543210)] hints908 0x3076805740574126800332be81fa603a521e60cc71de80f6702840f6706d4011511d83506122317c306d400d5002204970464036703d40094005319480c642af606570f6706d400b50022290818740f331d440cc711f804062b6403a7161705c6005301f702843a2311780964011532e7013600e6008300221e3828770254161705c60083036701e42fb42ed809560083081312380a46021422130397002264c80a0502042a5505c6003300e62ef805c60083081312380a4602140f230397002200610003000300030e4506c40a6600940053002207d40ad6011517560ad601150003001223561555067700f42ca600f4005300220b64033400830b64033400830003000300120b64033400830334033400830133001200031c9300610003000300940574005307230074072300740827000302c60866015505f500740436082704840293002204c608c600b50293002209a501061b5501d30ca407b728630fc50c9607830047030709e6030709e601550022000302b404f400e318940a8305440a830047000317e302140544068303974a671566101406a602041f55046400e3002228940c23044407b7012707340127073400e3000338c707541cf61936028405f4299301550022088602e502e5002200610003000300940d24005311f804060b27161705c60053012700940053002204c60c4600b526530074124803972568094305a500220516168700f40a341f87003304970ee703d4036703d4036700f400530003002202d3138401c300c21627074400b5234811b501b32526052500220061001200c2104803d4036703d400530133001202d301c300c2018200a10e45005300220d5505b710670275085412680d5505b70c37085403770316020400830133017209b30ef50053002203210140 329 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal250 : ¬ fitsRows (hostAt hosts5 250).toFinset :=
  sparse_reject _ (by decide) [(0xffbbbe62facd276ac1f28b16e6a0ea4906628440,0x9876542310),(0xffbbcddab49eb38bca307b9ac598a41a92838820,0x9854763210),(0xffbbcdb9ac5dab4998a41eb38ba9283ca3078820,0x5476983210),(0xffbbcdeb38bb9ac5a9283dab49ca30798a418820,0x7698543210)] hints908 0x30003000302a601d302a601d304d402a601d31d7601d304d402f50163099802f5016305d70e84380808730e8404560873268601d30ca428d601d30ca402f50163042707d41936028401f702840df822f320671b1401150c781936028401f7028416370e7305331a3622f3206706d4011500030003002201270464036703d404c400537fb73c762a371d040ae703c60ae703c600b500223ed601d3090504d4117601d3241504d408b408a3148608b408a3148602f5016303f710b710b70204067700f4067700f400530fb70916140329e801152f533334091633a438e3030706f601150003013300221b8606a6020413e703340db881a41c271f960083036701e41c5436380083081312380a46021407730397000300030022126806a6020403770b46033410570c0509f5085429341c2705c6008316e52a1601e427e63675012703b40083081312380a46021407730397000300220003000300610003000307680574057403670204003302a601d3007460250074022303f700030484377700940ab82e3325a601150905007402231925007403f705740e2602753bd413150316020401b3002208b408a3010602a601d30ca407830427117601d302a601d304d4117601d302a601d304d409980223022305d7000301f70094595806d40df801f7009401f700940c1706030533086649a81b14015501f7009401f7339618c32d6706d4191611e700940c1706030307030708660155098501d30ca407830e84380808730427002200031196036701e407681ae51bb40083053702663ca805c60db805370266053702660637027509f504f447e81f9600e300032e7705c60537026642240a9524771d18156609f51776020400831c542598177601e400830022398501d30ca407832f43010604270377031602041655012708540a340ec70266063702750127012704f400e300030537026626f40a9511670956026637a40a3435970083002208c618b406033c0601f7009405a508b408a31486022302c601d3241504d403f70003140330c824a4091601150022006100030003012701271327033407680127063702751014012713271014053702660537026600331c63010603a51c6301060cc73cd60094162706d401150127132710140a95758709560dd7026600330022090500740f33090500740cc70127012702040be801270ee702040ee713270127033401271327012703340033000301f700940c170603030706f60115090500740cc70022000306a600f432b705c600830377031601e406370275012703b400830133002205370266132701270a0503345ab705c60033090518740cc7002200611bf802040127020401270ee706370275033403770316020400330003090500740cc701330012000326e41d9308f81e4803970003162706d400b500220003090518740cc7012700f4005301330022000300a11bf806370275085401270637027508540e940a9511670e9433852b57053705c612680377031602040537026600830003012727e6367503b416e52a1600f400830022000303e3007412480397030703c600b50022030733a438e306f62f53333403c60115012700f40053002200610140 580 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal251 : ¬ fitsRows (hostAt hosts5 251).toFinset :=
  terminal_reject _ (by decide) 0x331111110 9 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal252 : ¬ fitsRows (hostAt hosts5 252).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173dab62547414c410c01,0x9876542310),(0xffbbcdeb38bdab49ca2f839ac52d2831ca418440,0x9876325410),(0xffbbcdeb38bdab49c9d07c5a95a9853990400823,0x9876234510),(0xffbbcdeb38bdab49c9ee8c1aa4b1662a0e408062,0x9876453210),(0xffbbcdeb38bdab49c907314831041183dcd62d49,0x8976543210)] hints908 0x23100002231023100002231000020383038303830141 11 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal253 : ¬ fitsRows (hostAt hosts5 253).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a465073dab6290931c8510c01,0x9876542310),(0xffbbcdeb38bdab28d27062d4f734e64a0a408062,0x9876453210)] hints908 0x30613052500220062056401c30022059400330244069303f7018228340223042701820321000300d5000300120754003300c20012003300c202d300a100030613052500220062059400330244069303f70182056401c3002228340223042701820321000300d50003001200120754003300c2003300c202d300a10003001200120012006100030012001200120061222822282ff70182222822282ff7018203210140 82 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal254 : ¬ fitsRows (hostAt hosts5 254).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c9ee8c16a6b10931c8510c01,0x9876542310),(0xffbbcdeb38bdab3a49ac5aa307b8e64a0a408062,0x9876453210)] hints908 0x323a606b40bc5018201b300120d140d14051309d401c3017205a50022002203810003052500c202340033001200120da209c3000300a10003000305250012000300b309c300d5001200a1004700470182048404840293002205e415f402930022004700470172004700470182038100120012001200a100030e7306570e67172600b50172066403a705b71744005301a2001201c30b8201c30b820321046418e4005300030172179803d4167703d40053018209b304a2018203810140 95 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal255 : ¬ fitsRows (hostAt hosts5 255).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda72ad22d62e0f728c52250708062,0x9876453210)] hints908 0x30f060a1605250ed6214605250094057400530d8624e6070501a200620644079401c30624034402b4034403440d73083402b400e30344034403440344008301a20734073401c30714083400e317b40244082701a20d14056401c3002209243b04040310e302840b160b1601150444035607b701820321000300d500030012001207540033001206b4003300120033002202d3006100030a16052500120012079401c30022059400330244007403f700c204f4003302440d4403f700c228340106042728341786042700120061000307d421940bc5150600d50003001206c4003300120c8600d500120012025405940513059401c310a310720594003303b4052500c2000300a100030497079405b702b40053002204c61af300b504c6122300b5002214b70a160fb702c600b5009402c400530022009402540053001200120094025400530ea40254003300220061000300120012001200610003001200120022006104971ae505e41e141e1414571996040301a2199614570c3731f51f661e1408e50eb71ae50f940403018204a204a204a203210140 204 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal256 : ¬ fitsRows (hostAt hosts5 256).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda959c9ac5aa307b8c52250708062,0x9876453210)] hints908 0x323a602840bc50fc50c960047488600740cf405d701820d1404540513056402c405640d7302b400e3064402b400e301720a830544004702c60155062406c400e30172034401b3001226432ae40f1605d710e302c6015510e30c860155041405a501a200220321000300d50022001202340033001206b4003300120da200b3000300610003000305250012000320b220b209c3003306b406c40083001200d50344003300120a630c860115028400d5001200a1218421940bc51ba41506015501a205e406c4029305e415f40293002204840484029300220a63213602e500220594059405130594059401c301a20594059400e314f403b4052501820321000312b3065712b306570e670e67008600b5001204c6061300b500d50022066403a7066403a705b705b703d400533bf6097600d500220ff4023400330012009402540053001202c40d7301820033693309c500120321000300120012001200a100120012001200a1049705e41e141e14145702930003017214574655465520c655f62755020455f6275502040293018209b3003300c200d504a204a203810140 207 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal257 : ¬ fitsRows (hostAt hosts5 257).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d3a49ee8c16a6b109394c410c01,0x9876542310),(0xffbbcdeb38bd276ac9ac5aa307b8c52250708062,0x9876453210)] hints908 0x30fc50a5600470fc50c9607b724560074004701a200620a8307a40827083402b400e317b40693082701a20a830544082702b4058400e317b40244082701a203e31524004704440a7307b70444035607b701a2002203210003000300d500030012001206b4003300120da200b3000302d300610003000321460525002200030012073401c30133001204f400330244024403f70012720403560427001200610003134500470b4500470003001205e406c40293001210f30c8602e5002202230047059401c3000300120c23004703b4052500c209b30061000312b306570e67008600b5002232380b5704c6097600b5094305a50022066403a705b703d400533bf6097600d500221e480aa700120094023400530ff402340033002202c40d7300c2062401b3094309c5001200610003001200120012006104970f9404f4145700e301330172338637f80924086642d70155018209b30484029300c20a6302e500c203210140 179 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal258 : ¬ fitsRows (hostAt hosts5 258).toFinset :=
  terminal_reject _ (by decide) 0x331313310 9 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal259 : ¬ fitsRows (hostAt hosts5 259).toFinset :=
  terminal_reject _ (by decide) 0x131313330 9 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal260 : ¬ fitsRows (hostAt hosts5 260).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f835cb6254831c8510c01,0x9876542310),(0xffbbcdeb38bdab49ca3073dac52d28394c418440,0x9876325410),(0xffbbcdeb38bdab49ca2d7ba095a988218a700823,0x9876234510),(0xffbbcdeb38bdab49ca2e6c1ea4b168290e608062,0x9876453210),(0xffbbcdeb38bdab49ca306394f5b52838ca130880,0x9832547610),(0xffbbcdeb38bdab49ca2b7a5ac829c81180419c25,0x9823546710),(0xffbbcdeb38bdab49ca307b16e6a9283986229020,0x9854763210),(0xffbbcdeb38bdab49ca2a4b9ac5c1e8080a4188e6,0x9845673210),(0xffbbcdeb38bdab49ca2c5a9307b9a818820398a4,0x9867543210)] hints908 0x4b304b304b30141 4 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal261 : ¬ fitsRows (hostAt hosts5 261).toFinset :=
  terminal_reject _ (by decide) 0x113130 6 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal262 : ¬ fitsRows (hostAt hosts5 262).toFinset :=
  terminal_reject _ (by decide) 0x311111333130 12 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal263 : ¬ fitsRows (hostAt hosts5 263).toFinset :=
  terminal_reject _ (by decide) 0x13130 5 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal264 : ¬ fitsRows (hostAt hosts5 264).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f8396a6b109290e608062,0x9876453210)] hints908 0x3810003000300a101720172017203810003038100030140 12 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal265 : ¬ fitsRows (hostAt hosts5 265).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c9ee8c1aa4b16831c8510c01,0x9876542310),(0xffbbcdeb38bdab49b58b5265183dc818820398a4,0x9867543210)] hints908 0x300a118d300c20062003300c204a100030003000300a100030140 14 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal266 : ¬ fitsRows (hostAt hosts5 266).toFinset :=
  terminal_reject _ (by decide) 0x133330 6 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal267 : ¬ fitsRows (hostAt hosts5 267).toFinset :=
  terminal_reject _ (by decide) 0x132221222133130 15 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal268 : ¬ fitsRows (hostAt hosts5 268).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117b9494358b290e608062,0x9876453210)] hints908 0x3810003142100a303230007000301720172017203810003038100030140 15 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal269 : ¬ fitsRows (hostAt hosts5 269).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c64f8398d5a54831c8510c01,0x9876542310),(0xffbbcdeb38bdab49c1f28b9494358b290e608062,0x9876453210)] hints908 0x300a10003001200120012001204a10003003300c20062003300c2003300c204a10003001200120012001200a1000300a1000300a10140 28 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal270 : ¬ fitsRows (hostAt hosts5 270).toFinset :=
  terminal_reject _ (by decide) 0x1 1 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal271 : ¬ fitsRows (hostAt hosts5 271).toFinset :=
  terminal_reject _ (by decide) 0x1373213330 10 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal272 : ¬ fitsRows (hostAt hosts5 272).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e117b5cc4a16a31c8510c01,0x9876542310)] hints908 0x300a100030012001200120012001200a10003102310230bc5059400330182198700620062198700220d14064405130d14064405130b8205940033102310230bc5018204b10003001200120012001200a1000301b300c20012002201b300c200a10003001200120012001200a1000300a10140 58 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal273 : ¬ fitsRows (hostAt hosts5 273).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c6506b1ee4a16a31c8510c01,0x9876542310)] hints908 0x300a100030003142100a300630007000302e300c20012003300c200a101b300c200120022003300c200a1000302e300120012003300c200a100030140 31 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal274 : ¬ fitsRows (hostAt hosts5 274).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a46506b1ee4a16a31c8510c01,0x9876542310),(0xffbbcdeb38bdab494e307b96a6b128394c418440,0x9876325410),(0xffbbcdeb38bdab19ca904a1ac5a9ee218a700823,0x9876234510),(0xffbbcdeb38bdab28d2705a9287b9ac290e608062,0x9876453210)] hints908 0x3000300a10003000300120012001200a1000344d20063124344d200630007000301b300c20012001201b300c200a1000300a10140 27 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal275 : ¬ fitsRows (hostAt hosts5 275).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38b5e959c1f28b16e6a548290e610c01,0x9876542310)] hints908 0x30fc5010607b70fc50c9607b7258604140af60525030709e615d6030709e60155002200220a8305440827058402b400e317b40244082700220a830544082704f402b400e317b402440827002204540d14058401c302b404f400e302b404f400e30ac403440624062400e30022012707340f940127073400e30444035607b70444035607b70a63041411b611b6015500220022006100030003219407d41715175600d50003001213b600d5002200120ac4003300220f44064408930f44064408930133013310720b64003303b409641715051300120003000300610003000309e609e605250fc600f41ea5020400530f060af6052514b709e60ae711c601550022000300120734073401c3013304f4071400e317b40244082700220d14056401c31ab300120644058401c3013302b4058400e3034403440344034402b40d730344034403440344008300220497073406770b7400e301330444035607b710f302840b160b16011500220061000321842194219401151756023421a6011500030012048406c40293002207e506c43528005300223b830c8602e507e506c43528005300220b640b64059400830b64059401c3000300220b640b640f44008303b403b40525002200030061000312b306570ce8008600b50022068401630b5704c6097600b5094305a5002236b503a70bd803d400530436097600d50022265300740aa7002200940234005307c4023400330022041401c300c2034401b3094305250022006100033db700860fb7008600b505b700f413a7050505160033002208f8019704c60c4600b50356019700224a0703d4036703d4005300940be8203702340033002208f8019704c60c4600b5035601970022277803a7161714d6005300940d24005325980b27242707e5005300940d2400530127009420370094005300221384041401c300c20244019702440197030704c61627074400b500943046052500c2006100030e670de60fb7172600b505b700f4012700f40053002200940794005304c60c4600b5094305a5002205b7020403671744005305b700f4051613a705050033002204c61af300b504c60c4600b5002200940d24005325980b2716171f26005300220e6703c62427061300b500940d240053012700f4047700530022041401c300c216e7431502c405f80a56091409c30061001201820012018201c300c2018200a10d5505b70c3708540c370f940d5505b70c3704f41457145700e30133017201f7830341c36f7706d42f3637f809243a133db74767086642d742d7015501a209b30484029300222ae4004700220a6302e52ae40047002203210140 480 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal276 : ¬ fitsRows (hostAt hosts5 276).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d48c2726b1ee4a16a290e610c01,0x9876542310),(0xffbbcdeb38bdab45a928398a49ca307b9ac18820,0x7698543210)] hints908 0x3000300030fc50c9607b723a602840525030709e6030709e60307030709e6015500220a830544082702c601550ac406c400e31ab30022034401b300120d140d1401c302b400e3056402c4056401c3064402b400e305130022012707340127073401270127073400e30a630c860155041405a50a6302c6015500030022001200030061219421940525150621a6015500220003048404840293002207e506c43528005300220886088602e50ef506c43528005300220b64059401c305130b640b6405940083002205940f4400e3051305840b640584008300120061000349870464036703d404840053043600d5002213b600d5002207c400330127009400530022138401c300c20ac400331627074400b5041405250022006122a3007422a30074019707140475074405160033002203e31524019704c60c4600b503560197002225980b27463514d6005300940d240053012700940053002202c401c300c2024401971627074400b5071405250022006100033ef70464498704640367036703d4048400530ee700f413a7050505160033002204c60c4600b5010600d500221ce80b27161714d60053012700940053002200940d240053002202c401c300c20254003311f7074400b50414052500220061001201a20012001201820012006114570d5505b702040d5505b702040c370d5505b70d5505b7033400330133017209b300d5002200220033002203210140 264 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal277 : ¬ fitsRows (hostAt hosts5 277).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb37c56d48c2726b1ee4a16a290e610c01,0x9876542310),(0xffbbcdeb38b5eb49c9ee8c1ac5a8e64a0a418440,0x9876325410),(0xffbbcdeb35bdb146b2307ba72291283996a00823,0x9876234510),(0xffbbcdeb36ae2f47b9ac9ca30398a45a92808062,0x9876453210),(0xffbbcdeb38bdab45a928398a49ca307b9ac18820,0x7698543210)] hints908 0x3000300030fc50c9607b7030709e60155002200120a830544082704f402b400e317b4024408271ab300220127073400e30444035607b701330022001209b300610003219401151756011500030012000307e506c435280053002202c402c409c320e40334210200b31c930061000349870464036703d40484005305b700f413a70505051600330022265300741248039704c60c4600b50943256805a5002225980b27161714d6005300940d2400530127009400530022138401c300c211b5234801b31627074400b52526052500220061250101821421142100a314570c370d5505b7085400830133017209b30ef50053002203210140 124 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal278 : ¬ fitsRows (hostAt hosts5 278).toFinset :=
  terminal_reject _ (by decide) 0x1 1 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal279 : ¬ fitsRows (hostAt hosts5 279).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117b5cc52d274188518801,0x9876543201),(0xffbbcdeb38bdab49ca304a0e6291ee6b16a18820,0x7698543210)] hints908 0x63b2141504a3141300b300b304b112771277005304a212771277040304a202b400e3018202b400e302b400e3018204b100030003127712770053018204a204a204b10140 34 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal280 : ¬ fitsRows (hostAt hosts5 280).toFinset :=
  terminal_reject _ (by decide) 0x111171113710 12 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal281 : ¬ fitsRows (hostAt hosts5 281).toFinset :=
  terminal_reject _ (by decide) 0x3330 4 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal282 : ¬ fitsRows (hostAt hosts5 282).toFinset :=
  terminal_reject _ (by decide) 0x3330 4 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal283 : ¬ fitsRows (hostAt hosts5 283).toFinset :=
  terminal_reject _ (by decide) 0x3333233123310 13 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal284 : ¬ fitsRows (hostAt hosts5 284).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda72ad22d62e0f720ea4984101483,0x9876453210),(0xffbbcdeb38bd94941cc520c41056939460f7358b,0x8976543210)] hints908 0x3061300d5001200120254003300120943182301150754003300c205640254008305640254008300120754003309431823011500c200610003000300030012003300120033001200330012006100030e4507140e45005300221277050512770053002202440047024400470182054400470544004701720244004702440047018203210003000300030012001201b300c201b300c20061000300a1000300a10140 81 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal285 : ¬ fitsRows (hostAt hosts5 285).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e1173d8d5a547418a320801,0x9876543201),(0xffbbcdeb38bdab48c2726b1ee5a0ea4984101483,0x9876453210)] hints908 0x3001200120012001200a10003198700620062198700220d14064405130b82102310230bc505940033018204b1000300120012001200a100030012002201b300c200a1000300120012001200a1000300a10140 42 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal286 : ¬ fitsRows (hostAt hosts5 286).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e2e6c1eb620ea4984101483,0x9876453210)] hints908 0x30033001200b300120033001200b300a1061300d50062006207c4003300220564025400830d1407c4008301821463025301150d1401c3018243731023011505940033018204b1000300030003001200b300a10003001200220d670d6700a100030022001201b300c202e300a1000300a10140 58 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal287 : ¬ fitsRows (hostAt hosts5 287).toFinset :=
  terminal_reject _ (by decide) 0x3333233123310 13 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal288 : ¬ fitsRows (hostAt hosts5 288).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda9594e3073dab62547418a320801,0x9876543201),(0xffbbcdeb38bda72ad22d62e0f720ea4984101483,0x9876453210),(0xffbbcdeb38bd94941cc520c41056939460f7358b,0x8976543210)] hints908 0x3061300d50012001202340033001205640254008300120943182301150754003300c2006100030003001200330012003300120061000307140e45005300220505127700530022054400470172024400470244004701820321000300030012001201b300c20061000300a10140 55 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal289 : ¬ fitsRows (hostAt hosts5 289).toFinset :=
  terminal_reject _ (by decide) 0x333170 6 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal290 : ¬ fitsRows (hostAt hosts5 290).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117b5cc52d2831ca320801,0x9876543201)] hints908 0xd500d501821413141300b300b304b1029304a202e504a22544254400830182254425440083254425440083018204b100030003000300030e350e35005301820254025400530182018204a204b10140 40 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal291 : ¬ fitsRows (hostAt hosts5 291).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117b5cc52d2831ca320801,0x9876543201),(0xffbbcdeb38bdab49bdcd9460c5a92520d0730820,0x9854763210),(0xffbbcdeb38bdab44a0e629062082728c1ee6b16a,0x8976543210)] hints908 0x2540254005304a2064400e30182064400e3064400e3018204b10003000300a102d4006400640003000300030140 23 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal292 : ¬ fitsRows (hostAt hosts5 292).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e2e6c1ec41ccb5244101483,0x9876453210)] hints908 0x300030003142100a300630007000300c20012003300c202e300a100120022003300c201b300c200a1000300120012003300c202e300a1000300a10140 31 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal293 : ¬ fitsRows (hostAt hosts5 293).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a464f835cc5a54831ca320801,0x9876543201),(0xffbbcdeb38bdab28d26e6c1ec41ccb5244101483,0x9876453210),(0xffbbcdeb38bdab49c1f28b9ac5a92520d0730820,0x9854763210),(0xffbbcdeb38bdaae6ca307d26c10408398a41ad49,0x9845673210),(0xffbbcdeb38bdab07b9b49ca2c290620816a4a0e6,0x9867543210)] hints908 0x300030012001200a10003230344d20063000700030012001201b300c200a1000300a10140 19 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal294 : ¬ fitsRows (hostAt hosts5 294).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a4a117b5cc41ccb5244101483,0x9876453210),(0xffbbcdeb38bdab183e93939ac290620816a4a0e6,0x9867543210)] hints908 0x30003000300b300b300d5001200d5001200a1061350c402e50022048435e402930022004700470172004700470182004700470182038100030012001200c200a1000300120012003300c201b300c200a1000300c200c204a200c200a10140 48 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal295 : ¬ fitsRows (hostAt hosts5 295).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38ad2f69bdcd9460c41ccb5244101483,0x9876453210)] hints908 0x30003000312f704140f065b471a3601151075087328244287098503e30fd4024408e51b4303f700220a1602e5001270b801e406445aa7085400830406034403440a0501e4034403440d7311961ae503b4064400830344034403440344008300227ab50a733e7462b70794029304842ec721d40f06011504640464046400e30022001208b416f301061c0408e5016304270b160b160b160b160115050605060506015500220062006100030ff406c40293002204970624067700f40094005300220e030c8602e504970624067700f40094005300220ad623340af6011502343014023401150003001205840b640584008305940f4400e30003001203340f4410140083028403b4015500120003006100030003010600d5002200120254003300221f380c560d0306f60115001223b806b4047503b4008302440b57002203560aa700120061000300940714005300220e6703c647d7272600b503e31524019700220e0310d600b505b700f43ef71e24005300940ff400530022137807d40af608d60bf7011500120cd81b86058406640f5700830244019700222b840c23019704c60c4600b50356019700c200610003000305b700f40ee700f4005300220e6703c6144700b500226e370613205703c600b5002205b700f40477005300940ff4005300226b66028409760d0321b60115001206a617440234047514f400831cc523480053002202b601e4050501c302b60644050501c300220061000300120012001200120012001200120012006100030a5605570a5611d70a560a5600470693069327170a230a23055700620a54108600b20a5416e301040d67128612861ca2294501853a730d67128612861ca2294519043a730d6707a407a40047007405570047055704360436069306932717124550460bf402b414330062069306930d670a230a230d6704440a230d6704440a230d67044404440a230a230d670062069306930c770ef61cb5044406931ac70e4607e61cb521731a0751f3176419a5006204b1001200c201c3002200c200a10094009461b327c7236461b327c72364145315d60155017209b304840293002200940484005300220e0302e500940484005300220266026616550f9416550f9414550f9400e30133017203210140 414 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal296 : ¬ fitsRows (hostAt hosts5 296).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb35a4f17b3dcd9460c41ccb5244101483,0x9876453210),(0xffbbcdeb38bda51856937b9ac5a92520d0730820,0x9854763210),(0xffbbcdeb2f736b49ca30c5ecc10408398a41ad49,0x9845673210),(0xffbbcdeb328c1ee6e2f6ad26c290620816a4a0e6,0x9867543210)] hints908 0x30003000305b72b1704751394066412170cd8208706a601e4040327f50fd402440827098503e30fd4024408e51b4303f700224b850a731d3407b7046400e30022001208b416f301061c0408e5016304270506015500220012006200610003000304970624067700f40094005300220ad6011502340115000300120334210220e400b30334008303340083001209b300610003000305b700f405b700f4005300220e6703c60e67272600b516a30c64122305a50022242706130e6703c600b505b700f405b71e24005300941a240053002219f602840b0702843b480b07028443c8220631430115001206a6046411870204354803670334047516970b74008302440683039700220e5606241cc501b304c6211600b503560f2303970022006100030003051614211421142100a30003549654961ca248441ca248441ca21ca124f2006365b6002401850063000734921421142100a32f3549771ad611960083017209b30094048400530022026614550f9400830133017203210140 190 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal297 : ¬ fitsRows (hostAt hosts5 297).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda959ca117b98d41ccb5244101483,0x9876453210),(0xffbbcdeb38bda307bab49c9ac290620816a4a0e6,0x9867543210)] hints908 0x300030003519408930033001207540ac400830033001200d5001200d5001200a106c40094009400530022050506c4310600940053002202c605d70a8305d7017206e405d70a8305d7017212a405d712a405d7018203810003010600d5001202540033075407c4089300940033001204c600d5094305a500c204140d730b82009401b3094309c5002203810003001200120033001201b300c200a1000300a1093400240934000301c30b8201b3001200a1001200c2002201b300c200a10140 96 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal298 : ¬ fitsRows (hostAt hosts5 298).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c9ee8c18d41ccb5244101483,0x9876453210)] hints908 0x3000300031251125100a354f20b210063756268d112c8000700030003000300b300b300b300a10012002201b300c201b300c200a10003061300d5017202540033017200b300d500d5018200b303810140 41 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal299 : ¬ fitsRows (hostAt hosts5 299).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a49ee8c18d41ccb5244101483,0x9876453210)] hints908 0x3000300030033001200b300120033001200b300a10dc4068319870062044406831987006211461135198704361135198700620d44007400470d442df400470182054406e4004705440d940047018212a412a4004712a412a40047018204b100030003000300120012003300c202e300a100030012002201b300c201b300c200a10003061300d5001202540033001200220234023400830033018218230943011507c40033018200d5102300d501820381000300a10140 92 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal300 : ¬ fitsRows (hostAt hosts5 300).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda959ca117b98d41ccb5244101483,0x9876453210),(0xffbbcdeb38bda307bab49c9ac290620816a4a0e6,0x9867543210)] hints908 0x300030003279609560893003300120754073400830033001200d5001200d5001200a105e406c40293001212930c8602e500120d4405d70a8305d70172054405d708340513017212a405d703b40bc5018203810003182300d5001202540033075407c408930094003300125c152184079401b3017204c600d5147305a500c207540ac40033009401b3017203810003000300120012001200a1000302340033001206b40033001200a169d347916db80934833207e6479119424b716da8093414441f810063000700a1001200c242c300c2002200a10140 108 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal301 : ¬ fitsRows (hostAt hosts5 301).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f8398d5a54831ca320801,0x9876543201),(0xffbbcdeb38bdab49c9cd6460f41ccb5244101483,0x9876453210),(0xffbbcdeb38bdab49c96a4a0e68c1ee6b0a418820,0x7698543210)] hints908 0x30003025402540053018200b300b304b10140 10 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal302 : ¬ fitsRows (hostAt hosts5 302).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e2f8398d5a54831ca320801,0x9876543201),(0xffbbcdeb38bdab49c9cd6460f41ccb5244101483,0x9876453210),(0xffbbcdeb38bdab49c96a4a0e68c1ee6b0a418820,0x7698543210)] hints908 0x3000300d5001200b300b300b300a102930062127712770053006202e512771277040300620564056400e301820564056400e30564056400e3018204b10003000305b70484066403a70053017200b300b303810140 43 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal303 : ¬ fitsRows (hostAt hosts5 303).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e2f8398d5a54831ca320801,0x9876543201),(0xffbbcdeb38bda959c9cd6460f41ccb5244101483,0x9876453210),(0xffbbcdeb38bdab49c96a4a0e68c1ee6b0a418820,0x7698543210)] hints908 0x3000300d50012003306440893001200d500120033062406b40083001200a10714029300621277066403a7005300620e0302e51277066403a7005300222d332d33015501820564056400e30564239405640083018203210003000305b70484066403a70053001205a5018201b3023400e30182038100a100030140 62 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal304 : ¬ fitsRows (hostAt hosts5 304).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda959c9cd6460f41ccb5244101483,0x9876453210),(0xffbbcdeb38bdab49c96a4a0e68c1ee6b0a418820,0x7698543210)] hints908 0x30003000300d500120033064408930012062406b4008300330012062406b400830033001200d500d5001200a10714071402930062066403a7066403a71277005300620e030e0302e5066403a7066403a712770053002205642394056400830564056400e3018205642394056400830564056400e301822d332d3301552d332d33015501820321000300030003066403a7066403a7066403a700530012023400e301b30182023400e301b3018205a505a501820381000300a10140 94 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal305 : ¬ fitsRows (hostAt hosts5 305).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd276ac9cd6460f41ccb5244101483,0x9876453210),(0xffbbcdeb38bdab49c96a4a0e68c1ee6b0a418820,0x7698543210)] hints908 0x300030003010600d50022001202540033002209431b030115062400330012062406b40083062406b4008300120624003309431b0301150012006100030e4507140e4500530022066403a7066403a7066403a700530022444607e50505444607e50053066403a7066403a7066403a700530022062406240624008306240f440624008300c205640b640564008305640b6405640083001206240f4406240083062406240624008300c20061000300030003066403a7066403a7066403a7005300221e481e480aa70022094301150ff4003300c2023400830234008300120ff400330943011500c20061000300a1000300a10140 122 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal306 : ¬ fitsRows (hostAt hosts5 306).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d3a4a2f8398d5a54831ca320801,0x9876543201),(0xffbbcdeb38bd276ac9cd6460f41ccb5244101483,0x9876453210),(0xffbbcdeb38bdab49c96a4a0e68c1ee6b0a418820,0x7698543210)] hints908 0x3000313b600d500220012025400330022062406b40083001209431b0301150624003300120061000307140e450053002205b700f4066403a7005300220505444607e5005305b700f4066403a70053002205640b64056400830012062406240624008306240f440624008300c200610003000305b700f4066403a7005300221e480aa70022023400830012094301150ff4003300c20061000300a10140 79 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal307 : ¬ fitsRows (hostAt hosts5 307).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e2f8398d5a54831ca320801,0x9876543201),(0xffbbcdeb38bdab183e93939ac5a92520d0730820,0x9854763210),(0xffbbcdeb38bdaab5263079483a4e48399cd60820,0x5476983210),(0xffbbcdeb38bdab49c96a4a0e68c1ee6b0a418820,0x7698543210)] hints908 0x3000305b700f4066403a700530012064400e30012064400e3064400e3001200a102540254005302540254005300620e350e350053127712770053006206240ff40083018206240ff4008306240ff40083018204b1000300030140 46 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal308 : ¬ fitsRows (hostAt hosts5 308).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d494e2f8398d5a54831ca320801,0x9876543201),(0xffbbcdeb38a4e57b55cd6460f41ccb5244101483,0x9876453210),(0xffbbcdeb38bdab183e93939ac5a92520d0730820,0x9854763210),(0xffbbcdeb38735949ca307ded510408398a41ad49,0x9845673210),(0xffbbcdeb388c1ee6b2f6ad272290620816a4a0e6,0x9867543210),(0xffbbcdeb38bdaab5263079483a4e48399cd60820,0x5476983210),(0xffbbcdeb3841cd49c841039ac5a937b54a41c60f,0x4576893210),(0xffbbcdeb38bdab49c96a4a0e68c1ee6b0a418820,0x7698543210),(0xffbbcdeb3829062082307b9ac5a92839af6ad272,0x6789543210),(0xffbbcdeb385a928398a418820bdab49ca307b9ac,0x8976543210)] hints908 0x63006359776674761403a762a31c9204b00063006343d4005309b20063032000630063006343d4005343d4005309b200a3032000130013006000630063006304a00063006304a00141 37 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal309 : ¬ fitsRows (hostAt hosts5 309).toFinset :=
  terminal_reject _ (by decide) 0x3330 4 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal310 : ¬ fitsRows (hostAt hosts5 310).toFinset :=
  terminal_reject _ (by decide) 0x333310 6 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal311 : ¬ fitsRows (hostAt hosts5 311).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f8398d52d262a0e408062,0x9876542310),(0xffbbcdeb38bdab49c9cd6460f5a8831040941cc5,0x9867543210)] hints908 0x3125100a312c800070003001200b300a10003000303810140 13 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal312 : ¬ fitsRows (hostAt hosts5 312).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117b5cc5a92831ca418440,0x9876541032),(0xffbbcdeb38bdab49c9cd6460f5a8831040941cc5,0x9867543210)] hints908 0x3142100a3032300070003017201720381000303810140 12 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal313 : ¬ fitsRows (hostAt hosts5 313).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117b98d5a92831ca418440,0x9876541032),(0xffbbcdeb38bdab49b9ac5ca307a8831040941cc5,0x9867543210)] hints908 0x30062003300c200b304a10062003300c2003300c204a100030062003300c200b300a100030003000300a10140 23 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal314 : ¬ fitsRows (hostAt hosts5 314).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c64f835cb62927414c410c01,0x9876543201),(0xffbbcdeb38bdab49ca117b98d5a92831ca418440,0x9876541032),(0xffbbcdeb38bdab49be3092dac729253990400823,0x9876540123),(0xffbbcdeb38bdab49c1f28b16e6a9262a0e408062,0x9876542310),(0xffbbcdeb38bdab49b9ac5ca307a8831040941cc5,0x9867543210)] hints908 0x30012001204a100030062003300c204a100030012001200a1000300a10140 16 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal315 : ¬ fitsRows (hostAt hosts5 315).toFinset :=
  terminal_reject _ (by decide) 0x330 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal316 : ¬ fitsRows (hostAt hosts5 316).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c64f8398d52d27414c410c01,0x9876543201),(0xffbbcdeb38bdab49ca117b9ab6292831ca418440,0x9876541032),(0xffbbcdeb38bdab49be309394c5b5253990400823,0x9876540123),(0xffbbcdeb38bdab49c1f28b96a6b1262a0e408062,0x9876542310),(0xffbbcdeb38bdab47358b54e5183c831040941cc5,0x9867543210),(0xffbbcdeb38bdab49ca307a507315cd62d4418820,0x7698543210),(0xffbbcdeb38bdab420c41039ac5a928398b39460f,0x6789543210),(0xffbbcdeb38bdab44a0e629062082728c1ee6b16a,0x8976543210)] hints908 0x30062003300c204a10003000300a10140 9 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal317 : ¬ fitsRows (hostAt hosts5 317).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca307b5cb625483988510c01,0x9876543201),(0xffbbcdeb38bdab49ca2f839aa4b16831ca408062,0x9876542310),(0xffbbcdeb38bdab49c907314831041183dcd62d49,0x8976543210)] hints908 0x70307030703070304b100030003000300030140 10 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal318 : ¬ fitsRows (hostAt hosts5 318).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca3073d8d52d283988510c01,0x9876543201),(0xffbbcdeb38bdab494e117b96a6b10931ca408062,0x9876542310),(0xffbbcdeb38bdab44a0e629062082728c1ee6b16a,0x8976543210)] hints908 0xd5018200d504a200330644089304a20033023402540083018204b10003000300a1000300a1002409340003000300a100030140 26 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal319 : ¬ fitsRows (hostAt hosts5 319).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda307bab49c9ac290620816a4a0e6,0x9867543210)] hints908 0x3000300030254003300120012001200d5001200330012001200a1000305e406c4029305e406c4029300120c960d4405d717860d4405d7017205440d9405d708340834051301720d442df405d70584058400e301820ff406c40293001230f30c8602e5001203810003331625d41596312300d50172028400d500d5001207c400331bc60525147305a500c200330b9401c300120e5605640a0502340033061309430525017207d401b307d4025401c300c20381000300d50012000300120da200b302340033001206b40033001200a10c9607b705f40a235ae40a2305d70c9600470c96004701a202930062054408270f3372f40c774575071427450714029302c6180607050c7701a2264331542643315405d70dc40dc405570dc41345004705583d2410f305a501a202e55ca310d6190610f302e500620544004702b4157404031146022300470a730683039701823bf627423ab402c40d6704b1000300a1000300030886214600b5017209b318f401c3003300c204841e1400530133017200d50012038101b30012001200a100120012001200a10140 204 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal320 : ¬ fitsRows (hostAt hosts5 320).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e1173d8d52d0931c8510c01,0x9876543201),(0xffbbcdeb38b5e958c2726b1ee5a8e64a0a408062,0x9876542310)] hints908 0x300030af60af6015500120293001204970464049700f40053001202e5049700f4049700f4040310a300120584058400e30584058400e30012000300a1000300030293001204970464049700f4005300120af60af6015500120584058400e30584058400e3001202e5049700f4049700f4040310a30012000300a10003000300d50012000300d5001200330956279608930012003310a3023402540083001200a102c40293092401b3006210e505d719c70df809e6052514b724e60d8614b709e60155017210c305d729770af605f410e301550223043607b701a2061302e5306747433c4400b500221df70db8073401c329b705841905073400e3081312380ba602140544039735f727b50b9402b400e301a20d8605a504973b0409240497073400e31345044408270eb71e053aa6005335174bc31bc602c6015501a20321000300d50012000300d50012003310a302340254008300120033095627960893001200a110e505d714b724e60d8614b709e6015519c70df809e60525017202c40293092401b3006210c305d70436022307b729770af605f410e3015501a2061302e5306747433c4400b5002204973b0409240497073400e30d8605a50444134508270eb71e053aa60053351702c64bc31bc6015501a21df70db8073401c329b705841905073400e335f702b427b50b9400e3081312380ba602140544039701a2032100032eb803c61c8338a4065700b5017202d300d5001228a800f4188640f51d8403a700530133017200330b9401c3001203812eb803c61c8338a4065700b5017202d328a800f4188640f51d8403a700530133017200d5001200330b9401c3001203810140 307 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal321 : ¬ fitsRows (hostAt hosts5 321).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda9594e1173d8d52d0931c8510c01,0x9876543201),(0xffbbcdeb19b5e72ad1ee8c16a6b0e64a0a408062,0x9876542310),(0xffbbcdeb38bd9ac5a92839ab49ca307b8a418820,0x7698543210)] hints908 0x3000300030ad60af601550022048402930022049700f4067700f400530022088602e5049700f4067700f40053013300220334058400e303340b640584008305130022000302d30061000302c40293046401b3002209a501060783019719c70df80af60525030709e6030709e60307030709e6015500220003072300740b350197013330b80af616a3528401550cf4043607b700221af302e5438816a33c4400b500221df70db8058401c30003296805840475058400e3081312380a46021405440197036701e410480b9402b400e30022050605a5012707340127073401270127073400e300030f16044408274548067700f4005305f423032a681bc602c6015500220061000304c40464005313b600d50022012703d4036703d400530133010600d5002202d302540033013308134b980a460214221303971c553297013600e6008300220ac40033051628e5329709560083081339a80a460214221303970022006104e60074019705f44c65159608731865010607830cb730b80b0702840df8328845840155002222a30074019754571d0425f33c5400b5002202c601d3117601d304d403e3007402230fe70bd800f40b255066005324a40916140329e801150022296813e705840db80475058400e3177601e41c5436380083081312380a460214019700220061000303e30074019718680b57097600d50022104803d4012703d40367036703d4005300030ce808861c832634065700b5002202d30bd804845e461ec5115403a7005301331947013600e6008300221f780aa7002202340033051611f805c6008305642348596452060893002200610d551e8702040d551e8702040d551e870d551e8713270334126800330133001209b300d50022001200c20033002200610140 325 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal322 : ¬ fitsRows (hostAt hosts5 322).toFinset :=
  terminal_reject _ (by decide) 0x110 3 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal323 : ¬ fitsRows (hostAt hosts5 323).toFinset :=
  terminal_reject _ (by decide) 0x138733321330 12 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal324 : ¬ fitsRows (hostAt hosts5 324).toFinset :=
  terminal_reject _ (by decide) 0x110 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal325 : ¬ fitsRows (hostAt hosts5 325).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a46506b1ee52d09394c408062,0x9876542310)] hints908 0x30c5601060115028400d50003001200d500120033064408930012023402540083003310a300120f44003300d5001202d300a106e40f24428705e4029307140f06063306f6015502c40f9402c400e30062006202230223428729d80f065b470ed6015500742e04645805d701a251b402e50012199606440b2503b400e3680806445aa7083400e32073054431a42ba57f731bd407733194039706242334062442c4008301820e3615d60e36015501063d06173805d711b607d411b667260115018203210003000300030085008500a300680068000700030012001206440033001200a1134302b300b501970022009418f40053001200740c96045505d7017212c50e3500531293430600b5092402c40053002201060544084305d70d94039701a201970d860e3600b512a4039700c20321000300120012001200a10eb71b971996199600e30182026602660a670a6700e3017204a243e419b300c2092414d304a203210140 179 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal326 : ¬ fitsRows (hostAt hosts5 326).toFinset :=
  terminal_reject _ (by decide) 0x001 3 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal327 : ¬ fitsRows (hostAt hosts5 327).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e117b5cb62927414c408062,0x9876542310)] hints908 0x620062003300c2003300c2003300c200610003048404841dc514f400d50003018205a500c201b30644089300c2091409141dc30f4400330bc5018202d30381000324e5008500a3006800680007000300c209c300a100120012001200a100030012001200a1655434d414d304a2134409d4040304a204b10140 61 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal328 : ¬ fitsRows (hostAt hosts5 328).toFinset :=
  terminal_reject _ (by decide) 0x3733213310 10 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal329 : ¬ fitsRows (hostAt hosts5 329).toFinset :=
  terminal_reject _ (by decide) 0x3733332110 10 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal330 : ¬ fitsRows (hostAt hosts5 330).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c6506b1ee52d27414c408062,0x9876542310)] hints908 0x300a300070003000300030e0300b5018235740053017200b300d5018203810012002201c300c201b300c200a10012001200a104a200c200c200a10140 31 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal331 : ¬ fitsRows (hostAt hosts5 331).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d3a49ee8c18d5a0ea494c408062,0x9876542310),(0xffbbcdeb38bdaad62d4941e939460f718a418820,0x7698543210)] hints908 0x3000300030c5601060115028400d50003001200d500120033064408930012023402540083003310a300120f44003300d5001202d300a106e406e4004705e40293071435170ab8063363c6070502c40f9402c400e30293006210e510e50c7712770eb7005300940ab8180609c509a70d861ff306570705130802c4018503a7005301a202230223004710c310c305571378537406a3378700f42c6708d6100701550074114636d805d701a207e602e534e7306700b5046405e402930022199635f707680b2566f404030266076815740d730cd8639623a53277079423570664121700e34ca305445f18021433652bb3054407730397090507a40d4411460773113505d701a20e3615d60e360155154709241a7403a7040301060dc4173805d7264307a417860dc413d5068305d701a202e55a580e360183065700b5050607e602e500220321000300030094062400530012064400e3064400e300120f060155001200a10f230223022305d772152778053403a71e383f2659871474127700e300740c96045505d70a831786113505d701a21b970eb7029359e81d04061334e700b50022605315683d1406571de8412455d7056634e701556f98302605051277005302c607050497073404970b9400e301a201060544084305d702b404030544039701a20fc50d44068305d7483801e44a870127139404030c9603970182032100030003009407940053001205b708070475092414c706a600f40403017214c706a601e40807047505b715f4040301720381373800f4469503a70053001205a5001200b300a105b7106704751e1406640f5720f814c706a6020400e3017202930012049707140293001200c202e504972c840403002203810140 317 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal332 : ¬ fitsRows (hostAt hosts5 332).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb19bd6d3a49ee8c18d5a0ea494c408062,0x9876542310),(0xffbbcdeb38bdaad62d4941e939460f718a418820,0x7698543210)] hints908 0x30003000318861ec5115403a70bd802040053041401f70414791679335b8806d40a9624d3206701f706d401151de801f7028408d60657011504140b1600d50133000300220e7306570e67008600b50022066403a705b703d400535c460c6415f6182300d500221c83226406570ce80de600b5053300865c460d3400d5000300220516201506a601e41d560475012713940475012703b400830e5606240a0500f4003322b80214081312380a460214077308130ba602140d554cc315140773039715962a2382b3387609643d841b030964011500221e3828770254066403a7008354c5064410480754036701e4095600830ba631a441f333f502140b57000300220b640344003309f503d402b60ac4003354760214149633c302140aa700030022000302d30061000302a60bb30074007410c30fe706770094079400530484377704140ab82e3325a60115153600740074022303f727450484029300221d7603e302a601d304d45db601d3007402230fe71b2503a70bd80204005301f704140df808660155009455041ff311e708d6065701550bd800f41c161eb5115403a700530022195408a30106010606930cb7045605f408731aa582041c63010602230cb70b07028432880c640df801f700f45856028416370e7316b30866015504e6007404e600740998004700220ae704c60a1600b5060306570ce80de600b5046405e4029300221196036701e407681ae51bb4008313e701e40db804f400e303770b4603346fc804060db8053767667874133610570c050a05058400e34e085fc30214081312380a4602142f1517e3021422752bb30214077301972e7705c66e250b4603346f3805c65806062411241f047a7553a815667d440cd819f41336008300221404010601060783042702662cb574340ec7066403a700e303e3007457d600740998004738c706d40b070284496806d45ce411b6111626d614a30e2807545f24137819f60284011500225933088602e50ce803c64dc33d14065700b5050607e602e500220061000300030094062400530fa406240053013300222ca600f407e50053067700f404970344005301330022000303340ff4008303341014008300220ad61cf60115002200610003000305f404560c2304e6007408e5016300471535277879270b741e38131506a600f4067700f400e32334233408c6059705255e350074113503561135004700030022599705e4036703d402936c781d040b761293127710f300b500221403156870e711c61de801f7041408d410f301557b38302623c500f4067700f4005302c60155012709f5073402b601270b7400e3000300224fc64fc60bf4031701c302b400e30544019700030022801301060683024406830047416729d501e4416713c5012703b400830c9601970022000300610003000300940d2400530022049700f4012700f40053002200c201f700940c1706033a13783706f60115001209b30377031601e4063702750d551e8703b4008301330012006110b700f4067700f400530133001202d300d5002200030da2172400b3018200a102a51da44f5806640f5729684d670316057400e30768103804f444a700e3013313080b9406c4049700f400e301a20a2301971af305a56f873c4411e700b50022056401b305e401b300220df83b480866305701550a341737375800f4008301a200032a681bc60c8608d410f3015537d700f40eb70053049700f400530a340ec70e560497073400e301a203210140 633 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal333 : ¬ fitsRows (hostAt hosts5 333).toFinset :=
  terminal_reject _ (by decide) 0x1110 4 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal334 : ¬ fitsRows (hostAt hosts5 334).toFinset :=
  terminal_reject _ (by decide) 0x1110 4 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal335 : ¬ fitsRows (hostAt hosts5 335).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c65073d6a6b1274188508062,0x9876542310),(0xffbbcdeb38bdab44a0e629062082728c1ee6b16a,0x8976543210)] hints908 0xd504a20234025400830033018200330644089304a20234025400830033018200d500d5018204b100030003000300a10934002409340003000300030003000300a100a10140 35 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal336 : ¬ fitsRows (hostAt hosts5 336).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bc60f736d5a4e4c290620816a4a0e6,0x9867543210)] hints908 0x3000300030fa401c301330012001212d60525002207d400e306c406b400830012096401550334003300120c860c5601150ad600d5001200030061000305e406c4029305e406c4029300120c9621f6004703566c26004700220a630c8602e500220e030c8602e5002205440d9400470834083401c3002202442df4004714f403b40525001200610003066403a7066403a705b705b703d40053331625d41596312300d5010600d50022144769641293061300b5010600d50022047705b7009402c400530ab809872d760414451602e50f67028410970106010600d500d5002212b3065712b306570e670e67008600b500220e5605640a05023400335407009412862568010617157a5507540234505600830022025400330768036701e425740293118707d40ea4434802540893169707d40ea42988003300225bd707c422470254025400331336064425980083162707441286311800d504147f8873e336060f8713e336061715002202540033003305e456786575028408071f550284089300220061000300d500220003001202340033001206b4003300120da200b30061000319c704140df81036052515a80c96004732240c960427245600740cf4042701a20293006242b705160768443401c302c60af60155100402b400e30ef50b253b5402b400e309f5048427450484029301a214e80544004702b4058400e35fe31514054401970436282407b701a20a83054403f702b4058400e317e30214054401970cd8047505e401b301a203e315240f1603f70a63063344e602c6015504442a96082713783d2410f305a501a202e50533088619060e0302e50022032100030003001200c20012001200610003001200120012006100a11a551a551f2613063b35020413063b350204375802040293017209b3003300123b972ad805e40574057402930133017200d50022002203210140 345 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal337 : ¬ fitsRows (hostAt hosts5 337).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c65073dac52ce64a08508062,0x9876542310),(0xffbbcdeb38bdab49bdcd9460c290620816a4a0e6,0x9867543210)] hints908 0x30003000300c20062003300c218d304a10003000300a100a10140 14 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal338 : ¬ fitsRows (hostAt hosts5 338).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda307bab49c9ac290620816a4a0e6,0x9867543210)] hints908 0x300030003064408930033001200d50012003306b406b400830012172402e30c560c56011511b600d5001200a105e406c40293048406c4029300220074007405d70a830a8305d701a206130c8602e5002212930c8602e5002206e406e405d70594059401c301a212a412a405d7075407540525018203210003061300d50012108601060284011501720254003300120012056402540254008369430613171501a207d402340893001203210003000300030644089300120012001200c200a12e443f0430331cb4006815560e46093407e6008609340063000700030012001200c200a100120012001200a1009419d721460705018209b30714029300c2026613a71e14040301330182009419b300c204a203810140 139 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal339 : ¬ fitsRows (hostAt hosts5 339).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d3a4a1173dac52ce64a08508062,0x9876542310),(0xffbbcdeb38bc60f736d5a4e4c290620816a4a0e6,0x9867543210)] hints908 0x300030003034400330012056402930022001201b30344034406b4008300120b160b160c560115001200120061000305e406c402930012007400470c2300470003001212930c8602e5002206e40047059401c300030012024400470754052500c209b300610003061300d5001200121f380f67028408d606570115001202540033002220f84b070254066403a7008302440b57002203560aa70012006100030003001200120012001200120012006100030a5611d702c600470693271701a208431ac702930062128612861ca22945190421630d6706e4004702b411e400e306930d940197043606932717018206930d6704440a230d67044402230d6701a202e5190651f302e5006204b100030012001200120061009441c327c7236415d60155018209b30484029300c2026616550f940f9400e301330172009419b300c203210140 162 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal340 : ¬ fitsRows (hostAt hosts5 340).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bc60f736d5a4e4c290620816a4a0e6,0x9867543210)] hints908 0x3000300030094003300120794029300220012075404f4008306b40334008300120594073400e306b4003300120c560ad601150c5600d5001200120061000305e406c4029305e406c4029300120c960d44004703560d44004700220e030c8602e500220e030c8602e500220544054400470834083401c3002202440d44004703b403b4052500c20061000333160c641596312300d5182300d50012094325f30c6400b5002204140ab809872d7604140d0311c6015501060106028401150414094300d500220e5605640a050234003305160768036701e404750b7400e35407074412866568010617155a470744023425b8008300220254003375c707d40ea40fe8025408937a2507d40ea405c600330022025402540254008313360644047507540083036701e410480754057401b30b161cd609761715002211b50e56071400530f4403440033034407d4023408930022006100030003000300d50003001202d3001206b4003300120ac4003300120da200b302d300616e5811d70c9600470c960047390300740074004701a213531ac7029300621286128600b2128612861ca2294519043a7319043a730d670544004702b4100400e31fb6054401970436007400470182054400470a2311d7183405440197043618340047018203e30e1401060047044404440a2307b704440106004704441fb6004701a202e573c4088619062c2302e5006204b100030003001200c20012001200610003001200120012006100a1435710973ad608660155017209b307d4003300123b9778e7236404f400e3013301720e0302e50022002203210140 297 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal341 : ¬ fitsRows (hostAt hosts5 341).toFinset :=
  terminal_reject _ (by decide) 0x331111110 9 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal342 : ¬ fitsRows (hostAt hosts5 342).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c65073d8d52d274188510c01,0x9876543201)] hints908 0x97602340115255401b3017200d500c2023402540083003301820f44003300d5018200330644089300c20381097602340115255401b30172023402540083003301820f44003300d5018200d500c200330644089300c20381000300030003000300c204a200c204a200a100c204a200c204a200a100a10140 60 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal343 : ¬ fitsRows (hostAt hosts5 343).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a4a1173d8d5a5474188510c01,0x9876543201)] hints908 0x3097602340115028400d5001200d50012023402540083003300120f44003300d50012003306440893001200a1054406e405d710f401b302930a6702660be802b400e301a209a734c61ff30657070500620223022305d76d1831c60b57373807541f550644013605b701e400e30182075405a52ca812a40aa7046405e4029300c215472c841a7403a7040308c6182300d5002202e5050607e602e500221996051607680b250b74040320f8025405642e57083400e30624009400334ca30544601502142f750544077303970182032100030003000300d5001200b300b300a143134313006820b4006820b40068000700030003001200a10de2093507140293001210381566083444a700e30172230402d3121807540ed6305701552c47018211a30e0302e543e419b30022032107e5517607e50053017207940e450053017200d5018200b303810003001201c3002201b300c200c2002200a100120012001200a10140 178 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal344 : ¬ fitsRows (hostAt hosts5 344).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a464f835cc5a5474188510c01,0x9876543201)] hints908 0x30012001200120012001200610003124512450d67006220d402b410a320d402b410a30d14025402b405130172124514630d671ac7002210c311d71023102310230bc511d70693069306930047018203210003001200120012001200a10003009400941dc5017209d402b410a3017200470022002200470012038100030003000300120012001200a100120012001200a100120012001200a10140 78 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal345 : ¬ fitsRows (hostAt hosts5 345).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173d8d5a5474188510c01,0x9876543201)] hints908 0x300a30007000300030003055704a2055704a204b100c200b300a100120012002200a10012001200a10140 22 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal346 : ¬ fitsRows (hostAt hosts5 346).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d3a4a1173d8d5a5474188510c01,0x9876543201),(0xffbbcdeb385a928398a418820bdab49ca307b9ac,0x8976543210)] hints908 0x30074007402230fe70c560f6704140f870d0306f60115079430a5009400530f06246804140f870d0306f60155002200120074010602230cb700740356099805d70b1602840b160b16011500120234208706a602540807047514f4008317b402440ec805d712f704140f060f870d0306f601550012059403440033001206441a7806a601e40807047503b400e30344034403440344008314c706a601e406440807047503b400e3034404060344034403440a0501e40d730012006100030003000300120da200b3003300120033001202d3006100030094009409c509d413a7040305f406930f76072315241924135334470714155500531378009430737b73212635c70705013301a209d402b40d7306e4004706e40544004701a20ef619d7070509a509d63a5700620456069347c50dc408e5016320c702c60047158607a408e51353004701a205051b970293072316d42c47013300220cd802663075527513941b97040302c602440047158607a408e50843004715860214019701820003032100030003000300a1093400240024000300030012001201b3001200610003009407140053001200940de619d7015501720266020413a700e301720eb7050500530022032100120012001200610140 232 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal347 : ¬ fitsRows (hostAt hosts5 347).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeaf6ce2b48c2727b9aa4b1683986229020,0x9876325410),(0xffbbcdd2728c1face2f6ab8c520c410358b52507,0x9867543210)] hints908 0x300030003290818740f331d440cc73ca800e62b6403a7161705c6005301f700943a2311780964011532e7013600e60083013300222be81fa603a521e60cc70768057405740367020400330c560f6706d41f48011517c306d401f702846516122300d5002259580d342af606570f6706d400b50127012703d4036703d4036703d40053000300221d762d9501e442342ed80956008306b4047503b421c80083081385480a46021422130397002205162ef805c600832a5505c6118702040a0502040033081339a80a46021407730397002202d3006100033ed601d302a601d304d4117601d3117601d304d40f7601d30074224601d3007402f501630fe70bd80bd800f44a16115403a754e603a700530fb70916140329e801152f533334091633a438e3030706f6011500224c65159605f40873045605f4087341d517f408a3010682344805010602f501630cb704e6007404e600740998022300470b07028426d617c31b1407d419f602840df801150b07028426d617c306d40c7819f6028416370e7316b31a360115002226c8318654571d044843226406572ee4065700b501270464036703d404c400530022036701e41c543638008313e705841f0438851f961b8606a604640db80083081312380a46021407730397002216e52a1601e427e63675012703b4008303770b4610141f04388505c6126806a6046410570c050a0508540083081312380a4602140773039700220061000300030003290800740f3300740cc70bd80bd800f418861ec5115403a75e461ec5115403a7005301f7009414980603030706f6011532b7013600e600830133002202a601d3265304d473880074224601d30074099803f73ca800e60b27161705c6005301f7009414980603030706f6011500222be8010603a501060cc7045605f4087380e80106611408a301060998042707680768053702664a77101414a710140537026600330c562ec706d43cd6028401157a8706d43177028417c306d401f7009453486bd6122300d500220ce80ce803c61c83226406571c832634065700b50516012700f43f741f87003301270ee703d40127012703d40367036703d40367036703d40053000300220377031601e413f80275012703b400830234047503b406a600f4008323480a0505e411876f58440502840893002205165c7805c600830377031601e413f80275012703b400835ab705c6573851a42a5505c60537026607686ac41cc50033256827d600945b577f9873f336061715002202d30061000300030e4506c40a660094005300220497049700f4067700f4067700f40053002202d351360505067700f42ca600f400530497049700f4067700f4067700f40053013300220ad607d40af601150ad617560ad601150003002203340b640584008303340b640584008305130003001203340b64033400830334033403340083051300220003000300610003000305f41a950c23035604e6007426750074200500474d1500740cf407b707230074072300740b3500470003098501d3007404360b3502f5016300470cf4043607b7002202c60866015508c608c608c61cb507230074072300740827000305f50074043608270e26027543b4057413150316020411a30022045605f40c23024404e60074090500740773004702b404f400e3076811961ae51bb4036701e400830db8076804f404f41df71df700e300030e2602751048308409f505744a671566579805742e77501605370266190607e500e310480b9402b4036701e400e3002204e600740f16082705740574057411a30ab804842e3325a62db30094011504640464046400e3046401b3002209a5010609a501060783004709a501061b5501d30ca407b70df80ab80866086619c719c70155030709e6030709e60307030709e60155030709e6030709e60307030709e601550022000308b416f301060444078307f50163004728940c23044407b7026637a45ba43597026678b474c41ad63d24253522e419545c250956479731641dd500e30506050605060155012707340127073401270127073400e3000300220f160444082718b40603155608c601f700941cb52a681bc602c608d423030155050605a5012707340127073401270127073400e300030022006100d5002200c2001200c20033002200c20d551e8702040d551e8702040377031602040d551e870d551e8706370275033400330133001209b300a10e4500530022012700f40053002200c207e50053012700f4005300220d551e870637027508540377031602040d551e870637027508541268111513e810954b3413e8109511154b34053705c60537026600830133001209b300610140 848 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal348 : ¬ fitsRows (hostAt hosts5 348).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdd2728c1face2f6ab8c520c410358b52507,0x9867543210)] hints908 0x300030003000301270807027503b424941f8719e84177031601e400830bd809f500f45d15115403a72f682b4400e6005302a601d30fd402440f762663007417b4077303f701f700940b07009411232d86096484c35a980b0703b401152e87074412e51bb400e625b800830133002203070f87060306f624061e571a482ec70094011504e600740f16022303f71b6501d300742a9602f5016303f717c30d3419f602842206094300d500220ce8053303c61c832264065728470e730d3400b5067700f410b703d400530133002219544ce3281603561aa517f408a3010624462005042704e600740cf4022304270b07028426d617c306d401f7028416370e7316b31a3619f6028401150cf403560223042700220ae703c60c37008600b5000300120377031601e417a622551384111515c4095613f802751ea5085400833a341db30106282402f50163042703770b4603341f04388505c61187020410570c050a05085406a6046400832fd50a460214081360080a461514077303970022051615b6027501e402a515c405c6047509f503b400832a5500e606a604640a05020400330f160244077303f708130a46021408130fd82a46021407730397002202d302d300610003000302a601d302a601d304d402a601d33ed603e304d40f7601d300744b1601d3007402f501630fe70bd80bd800f418867df5115403a71b2503a7005360a3340401060d960d9604d40f7601d300745bc601d3007402f501630fe70bd80bd800f47c561ec5115403a75a361ec5115403a7005329143ff83dd7091601f7009418b4060315e660b4421319631e9711c601151eb7106824a4091601f7009414980603030706f64017342738d3030706f6011501330022159605f40873045605f4087341d517f408a301061aa561a41ee3010602f501630cb704e6007401060455022300471b6501d300740356200502f5016300471b6501d3007403560b3502f50163004700220ce80ce803c63d5412b306570603065700b514a705e4036703d418e400530003002284281db30074045605f408731aa517f408a3010682444805010602f501630cb704e6007400740843022300470b070284220643c8314301f702840df819f6028401151fd702842a3706d40234747860e8742321d419f60284011500220ce80ce803c66043226406571c835574065700b50127012703d4036703d4036703d400530022262641583f4701e41315031601e40e260275074459b6400518a51a870b7400832fa41db301060244077307f501630047036703342e8704750b74118702040db806a604640083081312380a460214081346880a460214077303970022037740c8177601e40377031601e413f80275012703b4418710673665012703b400833a341db301060244077302f5016300474da70b460334049705c6215610570c050a05085406a604640083081312380a46021408134678166602140f230397002202d30061000300030003000301270807027503b406641f870cb84177031600f400830bd80bd800f4188639251d8403a718861ec5115403a7005302a603e302a601d304d402a601d302a601d304d40f7601d300740f7603e3007402f501630fe701f7009401f7009414980603030706f614980603205706f601152e87074412e51bb400e625b800830133002223e7009431d412b3060335d708d6065708d6065700d5030703c6030703c600b53fe4455804778228115403a7005323e70094030703c614980603030706f600d50133002203070f87060306f608d61e573c282ec70094011513e702665a362f2576d41b2529c7066403a7066403a7003301f700940ab801f700945b170af6011501f702841176330306d401f7028416370e7316b306f6011526d617c30d343177028417c30d3429960284534854b6122300d500220ce80ce803c61c83226406571c832634065700b5012700f4012700f40053012700f4036700f4005301330022045605f40873045605f408731aa517f408a301061aa517f422c3010602f501630cb73da800f40768036700f43f17058400830b07028426d6330306d40b0702844de617c306d401f7028448b648b6060335d719f602840115104807543da806b4036700f43f170584008300223dc6439814473d544af3065700b5030703c60fb703c600b500220377031601e40377031601e413f80275012703b413f802750ee703b4008303770b4600f42b7515c405c61187025410570c050a0503b4008303770b4603341f043f9505c603770b46033433e4388505c605371336386438641b2529c719f41336008322b80214081312380a4602140773855826930214077303970022051615b63c3501e402a515c405c6047509f503b400830377031601e4012700f413f80275012703b400332b75736400e603770b460ff42a5500e629941336076831941cc500331f033876096425182a2353f41b035d77536603b4011533b8021408131238166602140f235e084e230a46021407730397002202d302d3006100030003049706c4067700f40094005300220497049700f4067700f4067700f40053002202d313a70505067700f4110600f400530497049700f4067700f4067700f40053013300220ad60ad60ad601150ad602340ad6011500030022033403340334008303340b6403340083000300220334033403340083033403340334008300220003006100030003000305f41a950c2305f404560c2304e60074035602f5016300472ab500742ab5007404550047472406930cf407b7098501d3007404360b3502f501630047098501d30074043602f50163042701330022137801f700944dd7060303074f9608d60bf7011527f500740f16082707230074072300740b350047098501d300741cd602f5016303f71048509405740367046401b300030022045605f40c23045605f40c2304e60074024402f5016300470cd84d67031601e41067027501273b7406640f5700830094009408c608c6305705970155076804f4031700e30e260275104830842015110605740e941c2701362015110605741d561e651d561e6504f405370266144607e500e30e26027507443d75110601e455c61e650b741315031601e400830133002204e6007404e600740843004704560a730cf407b702660266057405743b27031700e304640464046400e3046406c400e30022513614650f16082709a5010609a50106078300470ab808660597015514b709e60ae711c6015503070506030705060307030709e605a5002208b416f301060444078307f50163004708b416f30106582407f50163042702660a347284359702660a345ba40ec70dd7026611247fc45c250a9537e70dd705c61f576d441dd500e305060506050601550497073406770b7400e30133002208b416f30106044407f5016303f716c60127101423c502040127046401b318b4060315e65ee328b409165ed42b9311c601f70094011505060c860155012704640127046401270127073401b300030022000300610003000313b600d50133001202d3001200220ac400330133001202d30ad613b601150ad600d5000300030012000303340ac40083013303340ac4008301330012033400330513096409640115000300121c93000300a100030bb3007405f404560c2304e60074007402f50163004736e500740074004705f406930074004700740436099800470074043608f8004700225f34404308f805f4045647b304e600744886007402f50163004736e500742ab500740047072307a4072307a400470b2503e30074043608f80047098503e30074043609980047002237150106045605f447b304e60074010602f5016300475f34404308f8045605f40c2304e600744886152402f5016300472ab500740ba6007408f86d25007404550047072307a4072307a408f8072300740b3500470b2503e3007404360d96007404360b3502f501630047098503e300740436098501d3007404360b3502f501630047002204e600740106004704560a735cf40a73004704e6007404e6007408f804e600740843004704640464046400e304640f94046400e30022190614650106004709a50a561b550bb30074004709a50a561b5501d3007408f83354010607830047030709e615d6030709e60155030709e6030709e60307030709e60155002201060444099800470bb30074044408f8004703e300740444335401060444078307f5016300470506050605060155012707340f940127073400e300220106044408f8004708b416f30106044409980047816340e4010604442fe41ee301060444078307f501630047050615d605060155012707340127073401270127073400e300220061097600d5002200c2001200c202340033002200c21f4841a42bf3273801f700941916065701150133001209b321c802a51da436280377031600f40a3403a700830133001209b300a10094048400530022012700f4012700f40053002200c2110600f405050053012700f476b700f4005300220d551e87063702750854037703160204111513e810953e941ad61196111513e810954b342f3549772ea705c6202702660083002209b3037703160204106702750d551e87085402662ad80f9405370266063702750d554a07145504f400830133001200610140 1676 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal349 : ¬ fitsRows (hostAt hosts5 349).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d3a464f839ab625474188510c01,0x9876543201),(0xffbbcdeb38bca307dab49b8c520c410358b52507,0x9867543210)] hints908 0x300030003001200120012001200120061000324f20063230324f224f200632502006301850063000700030074007402230fe700120074010602230cb70012061300d50012001202340033001200610003000300030012001201b300120061007400470172009407140053001206e4004701720eb7050500530022032100120012001200610140 68 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal350 : ¬ fitsRows (hostAt hosts5 350).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcde757c56d3a464f839ab625474188510c01,0x9876543201),(0xffbbcde2facdab28d2707b9aa4b1683986229020,0x9876325410),(0xffbbcdd2728c1face2f6ab8c520c410358b52507,0x9867543210)] hints908 0x3000302a626630fd4024402f5016303f701270807027503b40377031601e400830022195408a32816035602f50163042704e600740998022303971c750074035602f501630427002200120377031601e408070275012703b4008304e60fd4024402f5016303f70022006200610003197408a301062dc6007402f501630fe70bd800f418861ec5115403a7005301f7009414980603030706f601150133002202a603e50bb300744074010607f501630cb700740223022303971b650bb300740356084307f50163004700220ce803c66d9412b3065700b5012703d4036703d40053013300220377031601e413f80275012703b400833a341db301060244077302f501630047120323f81666021407730397002202d300610003000302a601d302a603e304d40f7601d3007402f501630fe701270807027503b40377031600f4008300221d661ed51be401630b57030703c600b501330022045605f408731aa517f408a3010602f501630cb72e160074099804e600740998022305d70e260275074403770b4600f410570c05023417a6225500f40083002246e4384323850aa700220377031601e408070275012703b40083012700f4005311230e16096401f7028416370e7309760b0700940115002202d300610003000300030c5600d50133001202d30012006206b400330133001202d30b1602840b1601150003001203440344034400830334003305130003001209b3000300a102a64c350bb3007404e6007407f501630047007401970693019701330b2539130074043607f501630047002205f44a167dd55ae40c2304e6007402f5016300472175019707230e140047013303a501d30074043602f5016300470022195408a3010627d6007407f501630047045605f40c2304e6007407f50163004702c62ab500740455004707230e14072300740b3500470003098501d30074043604e600740b3507f501630047002206e401970a73019706e4153600740843004705e40f9405e400e300221465019709a51366004709a5136609a501060783004709a7150615d609a7150601550022000319741ef30106044407f50163004729241ef30106044407f50163004708b416f30106044404e60074078307f50163004707e615d607e60155154705940f941547059400e3000300220061012700f400530022012700f40053002200c2012700f40053012700f4005300220ee706370275085403770316020410480f940377031602043827063702750637027504f4053702660083002200610140 462 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal351 : ¬ fitsRows (hostAt hosts5 351).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e1173dab625474188510c01,0x9876543201),(0xffbbcdeb38bdab48c2727b9aa4b1683986229020,0x9876325410),(0xffbbcdeb38bdaad62d4941e939460f718a418820,0x7698543210)] hints908 0x3000300a300070d240e450053001205a5001200b300a10f230223022305d70172029300220eb70293002202e5356704030022032107940053017205b704840053017203810140 36 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal352 : ¬ fitsRows (hostAt hosts5 352).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb37c56d494e1173dab625474188510c01,0x9876543201),(0xffbbcdeb38bdaad62d4941e939460f718a418820,0x7698543210)] hints908 0x30003000302a601d302a601d304d40f7601d3007402f516030fe713b612f700944d57060306f601151ea502047245095600530f0612f700942f97060306f60115013300220012045605f408731aa517f408a3010602f501630cb724460356099804270b1602840b160b1601150022025414c7031602542b17027503b4008317b402440ec803f701f700940f062f97060306f6011500220f44034400330022064414c7031601e40807027503b40083034403440344034400830377031601e406440807027503b40083034404060344034403440a0501e40d73002202d30061000300740074022303f70d2413a7005302a603e50bb300740f7601d304d407f501630fe7071430a50094005301f70414569700940c170603030706f614980d0303074fa60115013300222175217502230fe70bd800f41c1644652b0403a7005302a603e501d3098503e304d40f7601d3007408e5016307070bd802041b2503a7005301f7041400942b331fc706f614980d0318574fa601150133002200740106022304270a730a7302230cb70074153604d40998004700740356153604d4035613d50843004700220c4619d700b50ce803c62aa45b93065700b5012703d4012703d40367036703d400530022195408a301067e4581d42f430f0607f501630557045605f408737e7517f45e73010607f50163040701060d960074099800470b2501d30074035604e60074200507f501630047002210d60456129300b50ce80de60603065700b5203700f418e414a705e4005300030022037706a601e439f7031601e406370275012703b413f8047501273bb40083037706a601e402661655203703b413f8047514a73bb40083010602440d960074024407730455004741341db30106024404e60074077307f501630047120323f8166602145f1802142f152693021407730197002202d30061000300030003049700f4067700f400530133001202d30f060115013300120914091400b309b31c9300a10f230a23022300470a830a8302230047007408f80455004707680bf41df700e318a559f725c5059405340a673c1605740be83f2649c705743c16046400e301a20f230a23022300470f230a23022300470094009405970155072307a408f80b350047009401832ee430670ab800942b337983086613e311e7015501a2010608f80843004702660d24121700e3046405e400e301a20df81ce619c701551894022308f807830047030709e603071506015501a2482610963e931e7807543d1409d779e408c605584124321708c608d42303015502662b24492466a7076802661655677504f43f740ec700e3050607e60155049707340497059400e301a2032100030bd800f4469503a7005300220e8401630aa70133001202d3095636150083002203440ac400830ff4003300220061000305f404560c23024604d408e5016305570094233408c6059701550e260475074413c55114110600f4131506a617440083002208f8019707230e140197000331b61d045cc303c600b50022026602660574031700e302b400e3002209a5136601971fc7088600b50022000318b40d0315e61c4367c62e9327a401f70414011516c600f423c500f4005302c601552037048400530133002200610ee700f405b70d24005300220477049700f40053002200c20ee7063702750b740377031617440083002220570c17060311c601f700940115001200610140 622 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal353 : ¬ fitsRows (hostAt hosts5 353).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcde757c56d494e1173dab625474188510c01,0x9876543201),(0xffbbcde2facdab48c2727b9aa4b1683986229020,0x9876325410),(0xffbbca4e5183ddbd6717b54c520c410358b52507,0x9867543210),(0xffbbcdeb38bdaad62d4941e939460f718a418820,0x7698543210),(0xffbbc31483104149ca307b9ac5a9283ef59c5ed5,0x6789543210),(0xffbbc6b16a4a0e6290620837ace2f6ad2728c1ee,0x8976543210)] hints908 0x3000302a601d302a601d304d40f7601d3007402f501630fe70bd800f418861ec5115403a7005301f7009414980603030706f6011501330022045605f408731aa517f408a3010602f501630cb704e600740998022303970b07028426d617c306d401f7028419f6028416370e7316b31a36011500220ce803c61c832264065700b5012703d4036703d40053013300220377031601e413f80275012703b4008303770b4603341f04388505c61187020406a6046410570c050a0508540083081312380a46021407730397002202d30061000300030003049700f4067700f400530133001202d30ad6011500030012033421020334210200b300031c9300a1000305f404560c2304e6007402f5016300472ab5007404550197072300740b3501970133098501d3007404360b3502f501630047002204e6007408430197046400e3002209a5010607830197030709e601550022000308b416f301060444078307f501630047050601550127073400e3013300220061012700f40053002200c20d551e8706370275085403770316020400830133001209b300a10140 205 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal354 : ¬ fitsRows (hostAt hosts5 354).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca2f835cb6254831c8510c01,0x9876543201),(0xffbbcdeb38bdab49ca3073dac52d28394c418440,0x9876541032),(0xffbbcdeb38bdab49ca2d7ba095a988218a700823,0x9876540123),(0xffbbcdeb38bdab49ca2e6c1ea4b168290e608062,0x9876542310),(0xffbbcdeb38bdab49ca306394f5b52838ca130880,0x9876103254),(0xffbbcdeb38bdab49ca2b7a5ac829c81180419c25,0x9876013245),(0xffbbcdeb38bdab49ca307b16e6a9283986229020,0x9876325410),(0xffbbcdeb38bdab49ca2a4b9ac5c1e8080a4188e6,0x9876234510),(0xffbbcdeb38bdab49ca2c5a9307b9a818820398a4,0x9876453210),(0xffbbcdeb38bdab49c907314831041183dcd62d49,0x8976543210)] hints908 0x2310000203830141 4 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal355 : ¬ fitsRows (hostAt hosts5 355).toFinset :=
  terminal_reject _ (by decide) 0x33331323132310 14 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal356 : ¬ fitsRows (hostAt hosts5 356).toFinset :=
  terminal_reject _ (by decide) 0x33310 5 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal357 : ¬ fitsRows (hostAt hosts5 357).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173d8d5a548290e608062,0x9876542310)] hints908 0x300030003000300b300b300b300a1003300c200120022003300c200a1000300b3001200b300a10140 21 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal358 : ¬ fitsRows (hostAt hosts5 358).toFinset :=
  terminal_reject _ (by decide) 0x3333111110 10 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal359 : ¬ fitsRows (hostAt hosts5 359).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda9594e2f835cb62548290e608062,0x9876542310),(0xffbbcdeb38bdab3a4a3073dac52d283986229020,0x9876325410),(0xffbbcdeb38bda549d62d7ba095a988080a4188e6,0x9876234510),(0xffbbcdeb38bda72ad22e6c1ea4b16818820398a4,0x9876453210)] hints908 0x30003051614211421142100a3000372542742716427424fe21ca1230324f224f224f20063018500630007000300030012001200120033001200a1000337670ef40cb8070305e406c40293001202c41dc3059400e30bc5018209b30381000300120012001200a10ef407030ef60705018209b304a203810140 61 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal360 : ¬ fitsRows (hostAt hosts5 360).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49c64f835cb62548290e608062,0x9876542310)] hints908 0x3000300030003142100a3006300070003003300c200c2001202e300a1003300c20012002201b300c200a10003003300c20012001202e300a100a10140 31 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal361 : ¬ fitsRows (hostAt hosts5 361).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca3073d8d52d0931c8510c01,0x9876543201),(0xffbbcdeb38bdab494e117b9ac4a16a290e608062,0x9876542310),(0xffbbcdeb38bdab48c2726b1ee5a92818820398a4,0x9876453210)] hints908 0x3000300a1093409340003000300a10934093400031b7511a300c200a11b7511a300c200a100b300b300a10140 23 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal362 : ¬ fitsRows (hostAt hosts5 362).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca117b98d52d0931c8510c01,0x9876543201),(0xffbbcdeb38bdab494e3073dac4a16a290e608062,0x9876542310)] hints908 0x30003000300a10024002400240024000302340033001202340033001200a14755006300684755006300680007000300a1000300a1001201b300c200a1001201b300c200a10140 36 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal363 : ¬ fitsRows (hostAt hosts5 363).toFinset :=
  terminal_reject _ (by decide) 0x3330 4 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal364 : ¬ fitsRows (hostAt hosts5 364).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda959c65073d8d5a909290e608062,0x9876542310),(0xffbbcdeb38bda51856936b1ee52d2818820398a4,0x9876453210)] hints908 0x30525001200120234003300120da209c3000300a100030fc50fc505d732240c9605d701820a830a8305d70a7306830397157402b404030254029301720a83054405d702b41574040333d3151405440397048402930172088602e50022010602e50022038100030003052500120003433202c409c307d400e30033001200d5001200a110e505d70fc505d7017205e406c4029300120a630c8602e5001210c305d70834051301720a8305d714f40bc5017203810003061300d500220e73065714b7172600b50012066403a7049717440053010600d501a20254003307d407c4089307d400330172025400331cd600d5041405250182041401c30b820321000300120012001200a100a118e40464005300030172167703d4179803d40053017209b302d30b82002203810140 150 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal365 : ¬ fitsRows (hostAt hosts5 365).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e2f8398d52d09290e608062,0x9876542310),(0xffbbcdeb38bdab483dd39456a6b12818820398a4,0x9876453210)] hints908 0x3000300030003000300c20012001200a100c20012001200a100b300b300a10047017200470172009419b30022009419b3002203810140 28 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal366 : ¬ fitsRows (hostAt hosts5 366).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb37c56d494e2f8398d52d09290e608062,0x9876542310),(0xffbbcdeb36ae2f483dd39456a6b12818820398a4,0x9876453210)] hints908 0x300030003061300d5002200120344003300220b640033034403440344008300220b1602840b16011500220062006100034e450bb30074035607f5016300470b2539130074043607f501630cb700740047002206331d041446094300b507230e1401970003002219541db30106024407f50163004712030ba6021412033cc81666021401970e2604750744110601e413c50b74131506a601e4008302c6024404550047002219741ef30106044407f501630fe70ba5302627b50204005318b40d0315e648c327a41c4311c601f70414011502c602c6015516e804843fb635b52b0403a700530133002206e4004706e403560843004702b402b400e3002209a51366019727c8088625e41ff3065700b5002202d3006100030003061300d50022001200620b640033034403440344008300220344003300220b1602840b1601150022006100030b2539130074043607f501630cb74e450bb30074035607f50163004700740047002206331d041446094300b507230e1401970003002219741ef30106044407f501630fe70ba5302627b50204005348c327a418b40d0315e601f704141c4311c6011502c602c6015516e804843fb635b52b0403a700530133002219541db30106024407f501630047110601e40e2604750744131506a601e413c50b74008312030ba6021412033cc816660214019702c6024404550047002206e4004702b402b400e306e4035608430047002209a51366019727c8088625e41ff3065700b5002202d3006100030003061300d50022001200c202a603e302a603e304d40f7603e3007402f5160303f70012023400330022045605f408731aa517f422c3010602f50163042700220061000302a603e302a603e304d40f7603e3007402f5160303f70012061300d50022001200c2023400330022045605f408731aa517f422c3010602f5016304270022006100d50003001202d300d50003001202d300b300c300b300c300a10047004704360843004705e405e4143300620047004705e6078300473067006719a501a20047004705e405e414330436084300470062004700473067006719a505e60783004701a20444045500471bd40b35004707e607e619a50eb7006714330444043607830b35004701a207e607e619a50eb7006714330444045500471bd40b350047043604440b350783004701a203210140 431 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal367 : ¬ fitsRows (hostAt hosts5 367).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb19bd6d494e2f8398d52d09290e608062,0x9876542310),(0xffbbcdead5a671783dd39456a6b12818820398a4,0x9876453210)] hints908 0x300030003009406c400530022067700f40497034400530022110600f405050053067700f4049700f400530133002203340b6403340083033403340334008300220ad602340ad601150022000300610003000305f41a950c23035608e5016300470b2501d30074043608e501630cb72ab500740455004700225cb403c61446094300b507230074019700030022045605f42433024408e50163004712030ba6021412033cc81666021401970e26047507442015110601e41d561e650b74131506a601e400830094233425a605970155002208b416f30106044407f501630fe716c600f423c50204005318b40d0315e6341328b409162f842b9311c601f70414011505660c860155049700f4067700f400530133002204e6007408430047026602661bb4031700e3147406c400e3002209a5010601971fc703c60ae703c600b5002202d30061000300035a230c642206094300b500224b660d34053303c600b50022000302b6025409f500f40053013308130ba60214081348a87ad631a4068303970e260475074400e612e50b7415b650d504140083024417b4077303f700220e5600f40a0502040053051602a515c4040615b604750414047509f50854008308130ba6021408130fd84b561514077303970f160f23024403f700220356244613d504270cf402230356042700220061000305f41596087341d561a45e73010608e501630cb71b6501d30074035608e501630047010600470022060306573537094300b50723007401970003002203e302a601d304d44b1601d3007407f501630fe71b2503a70bd80204005348c327a418b40d0315e601f704141c4311c601151de84628056608d6065701550bd800f45d661eb5115403a70053013300222fa41db30106024407f501630047110601e40e2604750744131506a601e413c50b740083081312380ba602140813466816660214019701060f230244045500470022007400471e383d681474066403a700e300740223035608430047002209a5010601970ce803c660436d34065700b5002202d300610003000305f401630b5731b60c6416b303c600b500221c83226406570ce803c600b5002202d3188639251d8403a70bd800f4005301332607074400e612e51bb42788008302a603e302a601d304d40f7603e3007402f5160303f70022384323850aa700220e5600f40a0500f40053051602a515c4040615b60a0501e404750a0503b4008322b802140d552693021408131238166602140773019753f41b036b882a231f03387609645d77536603b401150022045605f408731aa517f422c3010602f501630427036700f43da806b4104807543f17058400830022006100031de801f7009441a42bf327382ba641b3263406570115001209b3061300d50022001200c20234003300221e380537026602a51da43628188640f51d8403a7008301330012006100d50003001202d300d50003001202d30bc6279621024332107302d3003301330ac40ac40083013300121c9300a101060197022301971586007408f808430047046409d40464143301a213450197072307a4019740a8007408f80783004703070b560ef6030709e619a501a2007401970223019729b72e27447405741433007404360843004701a213450197072307a4019711e700942db7086619a53b151da3007404360783004701a203e3007408f804550047072307a408f80b350047297737074f5608c619a50eb7026637d704f414330b2503e3007404440436043607830b35004701a205060ef6050619a50497508409d404970734143301060444045500475c84022304440b35004703e300740436044404440b350783004701a203210140 669 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal368 : ¬ fitsRows (hostAt hosts5 368).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdead5a671783dd39456a6b12818820398a4,0x9876453210)] hints908 0x300030003048406c4029300220497049700f4067700f4067700f4005300220e030c8602e50497049700f4067700f4067700f40053013300220ad607d40af601150ad621840ad601150003001203340b64058400830334058400e30003002203340b6403340083096403b40155002202d300030061000300030003137856d700f45856028433030c6408d60bf701554d1500740cf407b7189406931d3407b7098501d3007404360b3502f516030047013300220a1602e50ae703c60c370de600b505e404640293000300220cd81187058406a605843f95040606640f5700e328f802144be517e30214120333780a46021422752bb3021407730197076811961ae51bb4036701e400830db804f4031700e30e260c051048059409f505742de805742e77501613150b4603340367062400e30133002204e600740f160827079402930ab804842e3325a62db30414011504640464046400e30293002246d6146523d60827067700f410b7020400530df808660597015514b709e60ae711c6015510b70464067700f40053002208b416f301060444078307f50163004782a382c37a060e286274053308c67ba808c638c751040b0702846e1410f3015505060506050601550497073406770b7400e30133002207e6050602e502e50c3705060ae703c600b5000300220003006100030003000304c608c600b517c30d34122300d500227a960c6405330c5600d5067700f410b703d400530133002202d302b6025409f502340033013322b8021408130ba60214081333780a46021406830d552bb3607680630214077303970768051604750b74036701e4008303444224329701360ac42de803445056008300220094057400530ab804140d0311c609872d76041401151de80c560f6706d4011507d43bc4003300220ae703c60c37008600b5000300121d762d9501e409564ba5041405c642345c58095600831e3806b4047503b4008319634d350214267515140b5700220e5603441cc50033034403440033149633c30214098533c302140aa7002202d30061000305f401f5087305f404561a6382d517f408a3010657e44805010602f501630cb704e600740106022300471b6503e300740c9622280047098503e3007403566ef8004700224c973e131d0469c81293127710f300b5599705e4036703d40293002203e302a601d304d4117601d302c603e304d40f7601d3007457e601d3007402f501630fe713e82b4430264f3815556fe707e5005360a33404010604440f7601d30074224601d3007407830fe73fe44548492403a76c0603a700530fb7091602c62a681bc6015534273ee3091633a438e3030706f62f533334091661371c43030706f60155002204e600740074022300477ec61db30074043641d517f408a301067ff808a301060b350cb707d413780af608d60bf701550074022303561135004700226e0707e60fb7008602e53dc643882d46065738a4065700b500223e053cb4054458a80047036701e402b410480b9400e31b860cd8058406640f5700e3081312380a46021405440197002208b45e830106024472b80047106729d501e427e63675012703b416e52a1601e4416713c5012703b400e301060683024406830047081312380a4602140c960197002200610003000300033fc405580477066403a701b304c60a1600b5144717c30d34122305a500220ce80ce803c61c83226406571c832634065700b5049700f4036700f400530133002202d30bd80bd800f4188639251d8403a718861ec5115403a700530133290800740f3300740cc701f7009414980603030706f601f7009414980603205706f6011500223d760158144712b3065705a5030703c6030703c600b50fb7091603070976052500220094079400532be8010603a501060cc73cd602840c5611f706d4011507d4079400330022030703c60fb703c600b5168700f4012700f4005300220377031601e413f80275012703b40377031601e413f802750ee703b4008306a600f40234047503b4008323480a0505e423481187023401c3002204770e5606241cc501b3036701e40127023401c31cd60a1600d525687743009425685b5709760525002202d3006100030ad601060115175600d500030012000313b600d50022001200220ac4003300220334025400830133033402540083013300120b6400330003096409640115001200030061000304e6007458f80074082706834733004704842db304140ab83ee325a6011504640464046400e30f9401b30022190614650106004709a50a561ef30a5607b709a50a561b5501d3007408f80c9607830047030709e615d6030709e60155030709e6030709e60307030709e60155002236e500743248010607b705f40693007400470bb30074035604e60074007420050047007404360998004701f50c23043611d70022113502550047072307a4072307a4082702c60866015505f500740436082705741268132743b411a300221196036701e4076829d51bb40083072307a4072307a408f805440b35004737150106024404e6007401060773004702b404f400e30905007402440436043607730b350047036701e410480b9402b400e300220506050605060155012707340f940127073400e3010604440998004701f50c23044407b703e3007403560444044413d507830047002215d605a5012707340127073401270127073400e305330b4504440c7708c60c78320715561cb508d402b32a681bc602c60155002200610ce80de60ae703c600b50133001202d300d5002200c20033023401c3002200c20bd80204067700f400530133001209b300a10b0700940b07009401f72c132f36499806d42f3637f809244dd706033a133db70866015501a209b3048402930022049700f4049700f40053002200c20e0302e5049700f4049700f4005300220377031602040dd70266106702750d5505b708542ad80f94106702750d5505b704f400e30133017203210140 1078 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal369 : ¬ fitsRows (hostAt hosts5 369).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda959c9ee8c18d52d09290e608062,0x9876542310)] hints908 0x30003000300030504088400b300d5001200b300b300b300c300a10047004711461b331f2702c402c400e301a205e60a650c770eb766870293006200471bd4019702b402b404032a44084300470182004705e6019701831817136750a401552e040683004701820dc40dc41ac71bd41b3311d702c602c6070501850eb721670d7600e30dc4176606830827670400940094005301a20e360e3601552834045500473d061135004711461c04113507b701a235672167029305e40484650401b3002203210003000300d500220da200b300d50012001200b302d3006106e4004703560106004702c402b4040320d402b4040301a2173801972c361a0729f30705136734e70705006207a400470444178601060683004705f40a230106022300474d773a952c5436c715d534972c25040301a236d801976984640302e5350666b3217400b5006202440074004704360d44007411350047184402231844022318440223068301970768199612171467040307681004504601e4040301820e3602c6070520d4154709240403227307a400740223004744b5048402930ab80714100734f7070500622c361023070521671277040333673a9312c61a0729f334972c230705353502c4124600530ab810362d4436430705006204b10003000300d50012061300d5001200b303440033001200a102b401b30197002204970714168707140053001200c22c9822d365f86a9702841a730bf7015501720e0305a514b710d63fa710d600b5009405640053002220f804e564e820872ce6058406640f5700e30223039701a2019704c650c400b51345039700c2032100031a4808d704140f870d030e672136240668f707050172061300d5001219e8209706a601e40807047505b715f424941e07040301720094003300120012032100120033002201b3001200c2001200a119544cd30106010602230427017202a607230074007410c303f70172061300d50012001200940033001203210140 362 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal370 : ¬ fitsRows (hostAt hosts5 370).toFinset :=
  terminal_reject _ (by decide) 0x221 3 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal371 : ¬ fitsRows (hostAt hosts5 371).toFinset :=
  terminal_reject _ (by decide) 0x333331131130 12 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal372 : ¬ fitsRows (hostAt hosts5 372).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bda9594e1173d8d5a928290e608062,0x9876542310),(0xffbbcdeb38bda72ad2306b1ee4a16a18820398a4,0x9876453210)] hints908 0x300030525001202340033001200120da209c3000300a100030ed61ba40bc501820484029304840293002208340834051305440d9405d70172088602e50022088602e500220381000300030525001200030956279608930033001201c300030b9402540513001200d5001200a10ed60bc51ba40bc5017204840484029300120886088602e500120834051310c305d7017208340513054405d701720381010600d5017200d5001200330b9401c30012025400330d4424e701721786425700120381000338a40e7306572eb8172600b5017202d31c167c651d8403a728a81744005301330172001201c30b8201c30b82038101b300121b7500a1046418e4005300030172179803d4167703d40053017209b300221f130b8203810140 142 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal373 : ¬ fitsRows (hostAt hosts5 373).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bce51b56906b1ee4a16a18820398a4,0x9876453210)] hints908 0x3000300030ed605250ed60525001207c400330012043600d500220012083401c30b940834051301330012083401c3096403b40bc5000300120003006100030ed60ed605250ed61ba40525001204840484029304840484029300120834083401c305440d94004700220834083401c305440544004700220886088602e500220886088602e500220061000300030ed605250ed605250012000307c400330012083401c301330b94083405130012083401c30003096403b40bc50012043600d500220012006100030ed60ed605250ed61ba40525001204840484029304840484029300120886088602e500220886088602e500220834083401c305440d94004700220834083401c305440544004700220061009402b400530106010600d500d50022061304c600b50106010600d5002202b4009400530106010600d500d5002204c6061300b50106010600d5002202540254003322b802140d555f6302140544039728e52617095600e628e52617013600e600830022025402540033003333b8021418c333f502140c9603970127009400e628e5261701360033002202540254003300e628e52617013600e628e5261709560083054422b802140d555f63021403970022003302540254003328e52617013600e60127009400330c9633b8021418c333f50214039700220061000300030ae703c64ab7008600b50133017202d3385700f449d703d400530133017209b3001201c30b8201c30b82032100031798179803d4167703d4167703d4005301a202d317980464167703d418e4005301330172001201c30b8201c30b820321385700f449d703d400530133017209b30ae703c64ab7008600b50133017202d3001201c30b8201c30b82032117980464167703d418e40053013301721798179803d4167703d4167703d4005301a202d3001201c30b8201c30b8203210140 342 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal374 : ¬ fitsRows (hostAt hosts5 374).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a4a3073d8d52d0931c8510c01,0x9876543201)] hints908 0x300030003029300120f060f060115001202e50012064406440083064406440083001200a10af60af6015502341ba4015501720293002204970464049700f40094005300120584058400e30594059400e301820584058400e30584058400e3018202e5049715f4049700f40924040300220321000300030012001206440893001200a15e213033006848e43033006848e47574303300680007000300d5001200d5001220b200b300d5001220e400b300a10293001201974f174f170705002235170af605f410e30155017235f705841905073400e3566303970182019771a503971436050501b300c202e5356735670403009434f4005300220321000300121b7500a1210619d700b5017202d3663413a700530133017200d5001200334e5700c2038105b7048405b704840053017200d50172372706130e67088600b5017220b200b300d500c203810140 166 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal375 : ¬ fitsRows (hostAt hosts5 375).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173d8d52d0931c8510c01,0x9876543201),(0xffbbcdeb38bdab494dee8c16a6b128290e608062,0x9876542310)] hints908 0x3000300030003000300120012003300c200a10012003300c2001200a100c20012001200a100c20012001200a10140 24 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal376 : ¬ fitsRows (hostAt hosts5 376).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494dee8c18d5a548290e608062,0x9876542310)] hints908 0x300030003000300030003001200120033001202e300a106e406e40fe70172022302230cb70182009400330022061300d500220022038100c20012001200a1001200b300a100120012001200a10140 40 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal377 : ¬ fitsRows (hostAt hosts5 377).toFinset :=
  terminal_reject _ (by decide) 0x333331233123310 15 (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal378 : ¬ fitsRows (hostAt hosts5 378).toFinset :=
  terminal_reject _ (by decide) 0x333312221222110 15 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal379 : ¬ fitsRows (hostAt hosts5 379).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab494e2f835cb62909290e608062,0x9876542310)] hints908 0x300d500120033023402540083001220e402e30033064408930012097601060115365400d5001200a10223022305d70223022305d70182061300d50022002207d40033002206e406e405d7059401c301a212a412a405d70b640033018203210003000300030003001200b300a100120012001200a1000300120012001200a110e510e50fe7018210c310c30cb7018204a204a200c203210140 77 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal380 : ¬ fitsRows (hostAt hosts5 380).toFinset :=
  terminal_reject _ (by decide) 0x33332331233110 14 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal381 : ¬ fitsRows (hostAt hosts5 381).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173d8d5a92831c8510c01,0x9876543201),(0xffbbcdeb38bdab49ca306b1ee52d09290e608062,0x9876542310)] hints908 0x300030003000300b300b300a100120022003300c200a1001200b300a10140 16 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal382 : ¬ fitsRows (hostAt hosts5 382).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca1173d8d5a90931c8510c01,0x9876543201)] hints908 0x30012001206440893001200a15e216313006819d5303312c8475519d53033006800070003000300a1006834d434d400631e013a6323081e013a63000700030003100413a7040301330182103619d70705018202d304a204a2038100c202e300a100120012001200a10012001200a10140 57 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal383 : ¬ fitsRows (hostAt hosts5 383).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab183e93939494358b18820398a4,0x9876453210)] hints908 0x3000300030003142100a3006300070003000300031a171a1720f805b700f4040301722cb72cb72c9812f7041407050172061300d5001202340033001200120381001200120033001202e300a10074007405d7017206e406e405d70172009418f40053009418f40053002218f40094005300223aa6050500530022038100c20012001200a100120012001200a10140 72 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal384 : ¬ fitsRows (hostAt hosts5 384).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeaf6ce2b183e93939494358b18820398a4,0x9876453210)] hints908 0x30003000300030f0608d700942f97060306f601152e1600740f16022303f701f700940b160f870603521601150094057400530022001206442097031601e40807027503b400830344040603440a0501e4034403440d730344034403440344008314c7031601e40807027503b406440083002204e600740cf4022304270b1602840b160b1601151c750074035602f50163042700220377031600f40344080702753554008312f700942f97060306f60f0601152e160fd4024402f51b4303f7002203440344003300220062006100030b250bb3007402a639750bb3007440740106043607f501630cb700740074022300471b650bb30074035607f50163004761c50bb30074035607f50163004700220ce80ce80de612b306570183065700b53f541894160307230074019700030022197408a30106197408a301062dc60074044407f501630fe70bd80bd8020436b503a7018503a700531de8140315684124087705667173065708d6065701550bd80bd800f44bd61eb5115403a7751644652b0403a7005381f43ff83dd7091618b40d0315e601f7041460b4421319631e9711c601151eb759a824a4091614980d030307212601f7041440173fd738d3030706f601150133002200740074022300471e38153527783f2678f71474066403a7066403a700e300740356099800470074035658a8004700220e840e84016309a5010601970ce80ce803c625e47183065725e41ff3065700b5002219541db30106024407f501630047775641583f4701e40e2604750744131506a601e459b6400518a51a870b7400830106024409980047120323f80ba6021412033cc816660214019700223a341db30106024408e50163004703775f08177601e413f8047501271394037706a601e4418739c73665012703b400830106024422280047120323f80ba6021412036b38166602140197002202d300610003000300030c5600d500220012006206b4003300220b1602840b1601150b1602840b1601150003002203440344034400830b6400330003001203440344034400830334003300220003006100034e450bb3007402a64c350bb3007404e604d4035607f5016300470074007400470693069311d70b2539130074043607f5016305570b2539130074043607f501630cb701330022137800942b331fc74f9608d60bf7011521752175082707230e1407230e14004703a501d300740f7601d3007408e50163344752f550940574143601b300030022195408a30106195408a301060d960074024407f5016300470cd80266165520373b7406641217008302c602c62ab5007402440455004707680bf4026600e30b2501d30074043604e600740b3507f5016300470e2604750744110601e413c50b74131506a601e400830133002206e406e400470a730a7307b706e406e4153604d403560843004702b40f9405e400e302b402b400e30022146514650c7709a5136609a5136600470ab81ce60094015527c81bc625e41ff3065701551fc7088615d609a7150600d5002219741ef30106044407f50163055703a51ef3010620a424d52f43010607f5016320c7413416f30106044404e60074078307f50163004702c615d607e6015516e80b943fb635b52b0403a700e30133002219741ef30106044407f501630fe73c860d2427b5020418e4003318b40d0315e62e9327a41c4311c601f70414011502c602c60155203704840f9415470594003300030022000300610003000300030ee70807027503b406641e0719e82097031600f4008302a603e302a603e304d402a601d302a603e304d40f7601d300740f7603e3007402f5160303f705b70807047513940ee70807027503b414c7031600f4037706a61744008300221447030703c600b5030703c6144700b5002220570f87060306f608d61e571a4808d70094011501f700940ab801f700945b170af6011501f7009401060f87060306f6011500940794005300220477168700f40053002200c2045605f40873045605f408731aa517f408a301061aa517f422c3010602f5016304273da817440768036700f43f17058400830e260275074403770b46174410570c05058417a6225502040083002214c7031601e4037706a601e40807047504971394080702750ee703b400830377031600f402540807027503b4008311230e16096401f7028416370e730af60b07009401150022012700f40477005304c60a1600b5002200610003000300d50003001202d313b613b60115028400d500030003001200030644210220b220b2107302d303440ac4008305130033013300121724172400b31c9302d300a100740074004702230223004715354f482e270bf40cd8558525360574235714330074043636d80047007404364778004701a213451345004707230e1407230e140047009400944c5441042bf3659808d60597447719a54033007405e636d8004705f5007404366f08004701a206e406e4004702230223004706e406e408f804360843004705e40f9405e4143305e405e4143301a2134513450047189402235c840223004709a51366393501d3007408f805e60783004709a71dd609a7150619a509a71dd615d609a7150619a501a2140350e837071ce613785eb3253408c62c6719a5026602661b5402a540244f38066403171737143302c602c608f804440455004707230e1407230e1408f81bd40b3500470b2503e3007404360d9600740b3507f50163004703e30074043657c600740b3507f50163004701a20106044417380047227307a41bd41738004707e615d607e619a51547136415470594143326430074044404e60074078307f50163004701a2010604442a08004718940f2304442a08004707e607e619a5154713640f9415470594143318650106044404e60074078307f50163004701a20321097600d50022001200c202a603e302a603e304d45876007402f5160303f700120234003300220456334538b408736084010602f501630427002200610094071400530022049700f4012700f40053002200c201f7009401f702a61d7617d306d4009401f7009408d60bf701150012110600f405050053049700f4203700f4005300221fe81744106702750ee70b74026603770316020406640f570083002200610140 1133 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal385 : ¬ fitsRows (hostAt hosts5 385).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab3a464f835cc52d0931c8510c01,0x9876543201),(0xffbbcdeb38bdab494e3073dac5a548394c418440,0x9876541032),(0xffbbcdeb38bdab19ca8d7ba0c4292b218a700823,0x9876540123),(0xffbbcdeb38bdab28d26e6c1ec4a16a290e608062,0x9876542310)] hints908 0x3000314211421142100a3000324f20063230324f224f2006300070003000300030012001200a100941dc5017209d410a3017200470012038100120012001200a10140 34 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal386 : ¬ fitsRows (hostAt hosts5 386).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb37c56d3a464f835cc52d0931c8510c01,0x9876543201),(0xffbbcdeb38b5eb494e3073dac5a548394c418440,0x9876541032),(0xffbbcdeb35bdb119ca8d7ba0c4292b218a700823,0x9876540123),(0xffbbcdeb36ae2f28d26e6c1ec4a16a290e608062,0x9876542310),(0xffbbcdeb349ca38bdab07b9ac398a45a92818820,0x9854763210),(0xffbbcde98b525073148310419c5ed5a4e5183dcd,0x8976543210)] hints908 0x30f570367020400831c750074035608e5016304270022001204e60fd4024408e51b4303f7049708070475139414c706a601e40403002200620061000300030003001200220da200b302d300a100941c9509d414d3013305f40693043637c40163004701a209d41f1306e4004700620ef6170509a51366055701a2000304560a73044407f50163004702c6004707230e1405570133158607a407f50163004701a20321000305b700f40053002210480f94478802042e4704f40367020400e3001205b700f40053002200610140 103 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal387 : ¬ fitsRows (hostAt hosts5 387).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab28d26f8398d4a16a290e608062,0x9876542310)] hints908 0x3000300030003142100a300630007000300030003001200120033001201b300c200a1007402c60cb7018206e406e40fe70172009400330012129300d5001200120381007410c300740cb70172007410e501060fe70172061300d5001200120012023400330012032100c20012001200a100120012001200a10140 62 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
theorem terminal388 : ¬ fitsRows (hostAt hosts5 388).toFinset :=
  terminal_reject _ (by decide) 0x333331110 9 (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal389 : ¬ fitsRows (hostAt hosts5 389).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bd6d3a464f8398d52d0931c8510c01,0x9876543201),(0xffbbcdeb38bdab28d2707b96a6b1283986229020,0x9876325410)] hints908 0x300030003001200120012001200610003250200632502006325022502006323032502250200630007000300030003142100a3006300070074007402230fe700120074010602230cb700120c5600d50022001206b40033002200610074007402230047001200740074022300470012009407140053002205b700f405b700f400530022110600f40505005305b700f405b700f400530022006101f700942cb701150012036717441a170083001205b700f40ee700f40053002205b700f404770053002200610140 100 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal390 : ¬ fitsRows (hostAt hosts5 390).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcde757c56d3a464f8398d52d0931c8510c01,0x9876543201),(0xffbbcddab49eb38bca307b9ac398a45a92818820,0x9854763210)] hints908 0x30003000302a601d302a601d304d4099804e6007402f5016302f5016305d760c561f408a32816035602f50163042760d5414408a32816035602f50163042713b6041401f700940b0700940f8706030f87060306f6011501330022001202a626630fd4024402f5016303f701270807027503b40377031601e40083002202a626630fd4024402f5016303f701270807027503b40377031601e4008300220ac40344037703160344037703160344080702750807027503b400830377031601e408070275012703b400830377031601e408070275012703b400830133002200620003006100030074022300740223022305d70c230c2302230cb702a603e50bb30074153604d407f501630843055702a603e50bb300744074010607f501630cb718a51a8718a52e57058406640a6706640a670dd702660be815b67da532c70574837532c702040083013300220b450b4507830fe701a701270204012702040a340a340ec7003302a603e501d3090504d45dd30f7601d304d402f5016334471fc703c60e461857682600d501f700942b331fc706f600940c17060318572d16011500030022197408a301060d96007402f501630455055704561d661ed51be40873045620a479b52a86087302f5016320c7098501d304d404e6007402f50163019701330022197408a301062dc6007402f501630fe7203700f418e414a76664003301f700940c170603030706f601150133002219631e9719634a970af608d609d708d609d70b070094055860f48503321708c6081332170de601150377031601e41655203703b402660637027514a72cf40083098501d304d404e6007402f5016301970377031601e406370275012703b4008301330022000300610003000300030003000302a601d3090504d408b408a3148602f501630fe713b601f700940f87060306f601151ea502040fc600f400530f0601f700942f97060306f601150003013301330133001200030012006204560e84087302a601d30ca402f501630cb7013308b408a32816035602f5016304270b1602840b160b1601150133000300120ac4037703160ac40807027503b40083013302a626630fd4024402f5016303f701f700940f062f97060306f601151ab301330012034406b400331ab3001206440377031601e43a07027503b400830133034403440344034400830377031601e406443a07027503b40083034404060344034403440a0501e408930513013302d300120003000302d3000300a100740074022300470c230c2302230047000302a603e50bb3007404e6007407f50163004702a639750bb3007404e6007407f5016300470b250bb3007402a639750bb3007404e60074043607f501630843004700223e453e450783004718943f540c230723007402230047000302a64c3501d3098503e304d404e6007402f50163004702a6397501d30bb304d404e6007402f501630047393501d34ff503e304d402a6397501d3007404e60074043602f50163078300470022007400740223004724332433022300470074153600740998004700741536007408f8004718a559f710480bf43d6805740be806640a673f2632c705740367046400e300220b450b45078300470e840e840c2309a501060223004709a501062fe45fa3010608f80047098501d3098501d304d42fe41ee301060998004700942b332dd72dd708660ab800942b33185708660603185709e6015500220003195408a301060d96007407f501630047045605f40c234896007407f50163004701060d96007409980047072300746be601d3007408f800470003098501d3007404e6007404e6007402f5016307f5016300470022197408a3010627d6007402f50163004702a601d30bb304d404e6007402f50163004701060d96007408f8004718943f540c23117601d300740998004700034ff503e3098501d304d404e6007404e6007402f5016302f5016300470022197408a30106197408a301060d960074044407f501630455004702a601d30bb304d4292408a3010648960074044407f501630b350047482610963e931e780754462808c6055808d609d74124321708c60fb7050601550266165532a732a704f407680266165514a704f4027514a7073400e3000308b408a301060d96007404e6007402f5016307f50163004703e3098501d304d44896007404e6007402f5016307f50163004700220061000302a601d302a603e304d45876007402f501630fe701270807027503b40377031600f4008300220e8401630b570133030703c600b5002200030456334538b408736084010602f501630cb702a601d302a603e304d4099804e6007402f5016302f5016305d7111515c409560377031600f41ea5063702750b7417a6225500f4008300223cf623850aa70003001202d30377031601e408070275012703b40083012700f40053013311232d86096401f7009418c32d570b0703b40b070094011500220061000301f70094009401f7009401f702a61d7617d306d408d60bf7011501270637027503b40377031600f40083002284f41d9308f80b3503970133030703c600b500221fe817440266037703160204106702750ee703b406640f5700832e160074099804e600740998022305d70e2602750744262632c700f418a51a8702341315031617440083002226e41d9308f80783039726e41d9308f8022303970003030703c61fc703c600b50022000303070c17060306f601f700940115012700f4005318b4060315e62914321703c619631e97097601f700940115012700f4203700f4005301330022006101f7009401f700940c170603205706f60c17060378470866011501270807027503b40377031600f40083012700f4005300220477012700f400530133030703c600b5012700f40053002200030377031617440377031600f4063702750ee703b406370275382704f4008305371115109517d41095111517d405c6053702667e040c48053702663827063702750637027504f43827063702750637027504f40537026605370266008301270637027503b40377031600f40ee70637027503b4037703161744008300221447030703c600b5030703c6144700b5002202d30377031600f408070275012703b40083012700f40053013303070c17060306f601f7009420570c17060306f601f7009401150022030703c600b5012700f40053012700f4047700530133002200610140 1161 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal391 : ¬ fitsRows (hostAt hosts5 391).toFinset :=
  sparse_reject _ (by decide) [(0xffbbbe6757c56d3a464f8398d52d0931c8510c01,0x9876543201),(0xffbbacf378bdab28d2707b96a6b1283986229020,0x9876325410),(0xffbb6aeb328f3749e2f07b8e65a8626b0a44a020,0x9832547610),(0xffbbcddab49eb38bca307b9ac398a45a92818820,0x9854763210),(0xff9cd62d4941cc520c410779bd6717b56939460f,0x8976543210)] hints908 0x3000302a601d302a601d304d4099804e6007402f5016302f5016305d71d661ed51be40456087320a422952a860456087302f50163042701270637027510570c0504f40e940a95116709560dd702660537133600830133002202a601d3090504d409050f7601d304d402f5016303f7012702041268012702040127132701270334003301f700940c170603030706f6011500030022053702660dd70266053711241f041c3527040a95247705c60e941c2705c600830377031601e406370275012703b40083013300220003006100030003000302a601d3090504d408b408a3148602f5016303f710b70204067700f4005301f7009414980603030706f601150003013301330012000304560e84087302a601d30ca402f501630427013302a601d302a601d304d402f5016302f50163039701f7028422f3206706d401f702841936028416370e7305331a3601150133000300120c370de60ae703c600b50003012703d4036703d40053013300120377031601e413f80275012703b40083013303770b46033429341c2705c61187020406a6020410570c0509f50854008308132c080a46021407730397000300030012000302d3000300a1000301f70094009401f7009401f71116109617d306d408d60bf7015501271067027508540db814a70637027504f40377031602040537026600e300030127063702751d561e6504f40e940a9511671d181566053702662015110617760204008300221fe802040266037703160574106702750127085406640f5700e304e6007409980223039702a601d3007408f80223039701330e26027510482d0426262487057418a51a8704f41315031602040367046400e3002201f72c13326806d40df818570c170603086601f7009401f70094015508b424c3010608f807830397117601d302a601d304d4099802230397013300940c17060303070307086601f70094339618c32d6701f706d4191611e7015500220003053702660266053711244d441c3526f40a95116705c60a340a340ec70083112326c833261e7807542914280708c619631e97086601f700940fb7050601550266063702750127012704f40377031602041655012708540a340ec700e300030022006101f700940c170603030706f60115012700f400530133002200030377031600f406370275012703b40083013305370e940a9511670e940a952b5705c6053702661bf806370275085401270637027508540377031602040377031602040083000300120003030703c600b526e41d9308f81e48039700030022000300a10140 470 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal392 : ¬ fitsRows (hostAt hosts5 392).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38bdab49ca3073d8d52d0931c8510c01,0x9876543201),(0xffbbcdeb38bdab49ca307b5cc5a548394c418440,0x9876541032),(0xffbbcdeb38bdab49ca30639af4292b218a700823,0x9876540123),(0xffbbcdeb38bdab49ca306b1ee4a16a290e608062,0x9876542310),(0xffbbcdeb38bdab49ca307ada97298838ca130880,0x9876103254),(0xffbbcdeb38bdab49ca305390c5bd2d1180419c25,0x9876013245),(0xffbbcdeb38bdab49ca307b96a6b1283986229020,0x9876325410),(0xffbbcdeb38bdab49ca304a1ac5a9ee080a4188e6,0x9876234510),(0xffbbcdeb38bdab49ca305a9287b9ac18820398a4,0x9876453210),(0xffbbcdeb38bdab49ca3079da558d217198450900,0x9810543276),(0xffbbcdeb38bdab49ca303388c128083bcad1ac29,0x9801543267),(0xffbbcdeb38bdab49ca307b8e65a8626b0a44a020,0x9832547610),(0xffbbcdeb38bdab49ca30291ac08128399ee1896a,0x9823546710),(0xffbbcdeb38bdab49ca307b9ac398a45a92818820,0x9854763210),(0xffbbcdeb38bdab49ca30188205a928398a47b9ac,0x9845673210),(0xffbbcdeb38bdab49ca30398a4188207b9ac5a928,0x9867543210)] hints908 0x4b30141 2 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal393 : ¬ fitsRows (hostAt hosts5 393).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcdeb38b5e9594e1173d8d52d0931c8510c01,0x9876543201),(0xffbbcdeb38bd6d49c6507b5cc5a548394c418440,0x9876541032),(0xffbbcdeb38a5ab784a33639af4292b218a700823,0x9876540123),(0xffbbcdeb38ad2f68c2726b1ee4a16a290e608062,0x9876542310),(0xffbbcdeb38bceb1b4a907ada97298838ca130880,0x9876103254),(0xffbbcdeb3895a149de355390c5bd2d1180419c25,0x9876013245),(0xffbbcdeb38bda72ad2307b96a6b1283986229020,0x9876325410),(0xffbbcdeb388c2b49caf64a1ac5a9ee080a4188e6,0x9876234510),(0xffbbcdeb389ca30bdab45a9287b9ac18820398a4,0x9876453210),(0xffbbcdeb387b9ac5a928bdab49ca30398a418820,0x7698543210)] hints908 0x300030003142100a32502006300071a17036702040083001205b700f40053002200610140 19 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal394 : ¬ fitsRows (hostAt hosts5 394).toFinset :=
  sparse_reject _ (by decide) [(0xffbbcd6f19b5e9594e1173d8d52d0931c8510c01,0x9876543201),(0xffbbcde758bd6d49c6507b5cc5a548394c418440,0x9876541032),(0xffbbcc6b3ba5ab784a33639af4292b218a700823,0x9876540123),(0xffbbcce37aad2f68c2726b1ee4a16a290e608062,0x9876542310),(0xffbbcbdab4deb389ca307b9ac398a45a92818820,0x9854763210),(0xffbbc7b9acbdab4398a4deb385a9289ca3018820,0x5476983210),(0xffbbcdeb387b9ac5a928bdab49ca30398a418820,0x7698543210)] hints908 0x3000300030127063702750854037703160204008308b408a32816035602f501630427013301330012001202a626630fd4024402f5016303f701270807027503b40377031601e400831ab30133001209b30062000300a10f570367020400830a6702660083013302a603e50bb300741536007407f50163084300470022119604971ad6008301a70a340ec70083013302a603e501d3098501d304d42fe41ee3010602f501630783004700220003197408a301060d96007402f501630455004702a601d30bb304d4117601d3007402f501630b3500470003098501d304d404e6007402f50163004700220061000302a601d302a603e304d4099804e6007402f5016302f5016305d701270637027503b40377031600f40083002226e41d9308f81e4803970003030703c600b50022000303070c17060306f601f700940115012700f400530133002200610140 166 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal395 : ¬ fitsRows (hostAt hosts5 395).toFinset :=
  sparse_reject _ (by decide) [(0xffb9dd6f19b5e9594e1173d8d52d0931c8510c01,0x9876543201),(0xffb7aef338bda72ad2307b96a6b1283986229020,0x9876325410),(0xffaf6dea72ef2b4ce2307b8e65a8626b0a44a020,0x9832547610),(0xffbbcbdab4deb389ca307b9ac398a45a92818820,0x9854763210),(0xff9eede96abd8e69c862ef1acce128ad0a48c020,0x3276549810),(0xffbbc7b9acbdab4398a4deb385a9289ca3018820,0x5476983210),(0xffbbcdeb387b9ac5a928bdab49ca30398a418820,0x7698543210)] hints908 0x30003000302a601d302a601d304d402f5016302a601d302a601d304d402f5016302f5016305d70e840456087302a601d30ca402f5016304270dd70e940a9516970a9537e705c60e940a95116709560dd70266053702660083000301330133001202a601d3090504d408b408a3148602f5016303f7012702040377031602040127020401270637027501270334003301f700940c170603030706f601150003000301330012053702660537026605370e940a95116727040a95247705c60e941c2705c600830377031601e406370275012703b4008301330133001200030003000300a1000302a601d302a601d304d4099804e6007402f5016302f5016305d702a601d302a601d304d408f802a601d3007402f5016302f5016305d7000301270637027518a51a8704f40e940a9511671d1815660537026626262487036702040083002202a601d302a601d304d408f808b408a3010602f5016302f5016305d702a601d302a601d304d409981d7601d302a601d304d402f5016302f5016305d7000305370e940a95116783940a95116705c6053702660e940a9511670e940a9511672ea705c64c46248716e52a160204008300220003053702660dd702660537112410671c3526f40a95116705c60a340a341b252ce700830537026605370e940a9511670e940a95116705c602660a340a341b252ce7008301330022006105370e940a9511670e940a952b5705c60e940a9511670e940a951167053705c605370266053702660083013301270637027503b40377031600f4008301330012000303070c17060306f601f7009401150a341b2529c7053702660127132701270334003301330022000300a10140 310 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem terminal396 : ¬ fitsRows (hostAt hosts5 396).toFinset :=
  sparse_reject _ (by decide) [(0xf7f9dd6f19b5e9594e1173d8d52d0931c8510c01,0x9876543201),(0xff7dcde758bd6d49c6507b5cc5a548394c418440,0x9876541032),(0xe7bbfc6b3ba5ab784a33639af4292b218a700823,0x9876540123),(0xef3fece37aad2f68c2726b1ee4a16a290e608062,0x9876542310),(0xfefb9f6b98bceb1b4a907ada97298838ca130880,0x9876103254),(0xd7b1cdff3d95a149de355390c5bd2d1180419c25,0x9876013245),(0xffb7aef338bda72ad2307b96a6b1283986229020,0x9876325410),(0xce3bcdebfe8c2b49caf64a1ac5a9ee080a4188e6,0x9876234510),(0xdeb38ffbbc9ca30bdab45a9287b9ac18820398a4,0x9876453210),(0xfdfb5dcf31f5b94d4b1079da558d217198450900,0x9810543276),(0xb7a9c96a18bfebd9ee393388c128083bcad1ac29,0x9801543267),(0xffaf6dea72ef2b4ce2307b8e65a8626b0a44a020,0x9832547610),(0xad3bc8c338bdbfe9cb7a291ac08128399ee1896a,0x9823546710),(0xffbbcbdab4deb389ca307b9ac398a45a92818820,0x9854763210),(0x9ca30deb38bdab4ffbbc188205a928398a47b9ac,0x9845673210),(0xbdab49ca30ffbbcdeb38398a4188207b9ac5a928,0x9867543210),(0xfbfaddaf29b9ea598e21f3b8cd2b08b1a8490a00,0x1076543298),(0x7799c5691835894148107fdbd5ed393dcb51cc31,0x176543289),(0xff9eede96abd8e69c862ef1acce128ad0a48c020,0x3276549810),(0x6b3bc4a338292b4082307bbfe5ab7a39af618a72,0x2376548910),(0xffbbc7b9acbdab4398a4deb385a9289ca3018820,0x5476983210),(0x5a928deb38188209ca307b9acffbbc398a4bdab4,0x4576893210),(0xffbbcdeb387b9ac5a928bdab49ca30398a418820,0x7698543210),(0x398a418820bdab49ca307b9ac5a928ffbbcdeb38,0x6789543210),(0x7b9ac5a928398a418820ffbbcdeb38bdab49ca30,0x8976543210)] hints908 0x30127063702750854037703160204008301330012000300a10140 14 (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem everyTerminal (i : Nat) (hi : i < hosts5.size) : ¬ fitsRows (hostAt hosts5 i).toFinset := by
  change i < 397 at hi
  interval_cases i
  · exact terminal0
  · exact terminal1
  · exact terminal2
  · exact terminal3
  · exact terminal4
  · exact terminal5
  · exact terminal6
  · exact terminal7
  · exact terminal8
  · exact terminal9
  · exact terminal10
  · exact terminal11
  · exact terminal12
  · exact terminal13
  · exact terminal14
  · exact terminal15
  · exact terminal16
  · exact terminal17
  · exact terminal18
  · exact terminal19
  · exact terminal20
  · exact terminal21
  · exact terminal22
  · exact terminal23
  · exact terminal24
  · exact terminal25
  · exact terminal26
  · exact terminal27
  · exact terminal28
  · exact terminal29
  · exact terminal30
  · exact terminal31
  · exact terminal32
  · exact terminal33
  · exact terminal34
  · exact terminal35
  · exact terminal36
  · exact terminal37
  · exact terminal38
  · exact terminal39
  · exact terminal40
  · exact terminal41
  · exact terminal42
  · exact terminal43
  · exact terminal44
  · exact terminal45
  · exact terminal46
  · exact terminal47
  · exact terminal48
  · exact terminal49
  · exact terminal50
  · exact terminal51
  · exact terminal52
  · exact terminal53
  · exact terminal54
  · exact terminal55
  · exact terminal56
  · exact terminal57
  · exact terminal58
  · exact terminal59
  · exact terminal60
  · exact terminal61
  · exact terminal62
  · exact terminal63
  · exact terminal64
  · exact terminal65
  · exact terminal66
  · exact terminal67
  · exact terminal68
  · exact terminal69
  · exact terminal70
  · exact terminal71
  · exact terminal72
  · exact terminal73
  · exact terminal74
  · exact terminal75
  · exact terminal76
  · exact terminal77
  · exact terminal78
  · exact terminal79
  · exact terminal80
  · exact terminal81
  · exact terminal82
  · exact terminal83
  · exact terminal84
  · exact terminal85
  · exact terminal86
  · exact terminal87
  · exact terminal88
  · exact terminal89
  · exact terminal90
  · exact terminal91
  · exact terminal92
  · exact terminal93
  · exact terminal94
  · exact terminal95
  · exact terminal96
  · exact terminal97
  · exact terminal98
  · exact terminal99
  · exact terminal100
  · exact terminal101
  · exact terminal102
  · exact terminal103
  · exact terminal104
  · exact terminal105
  · exact terminal106
  · exact terminal107
  · exact terminal108
  · exact terminal109
  · exact terminal110
  · exact terminal111
  · exact terminal112
  · exact terminal113
  · exact terminal114
  · exact terminal115
  · exact terminal116
  · exact terminal117
  · exact terminal118
  · exact terminal119
  · exact terminal120
  · exact terminal121
  · exact terminal122
  · exact terminal123
  · exact terminal124
  · exact terminal125
  · exact terminal126
  · exact terminal127
  · exact terminal128
  · exact terminal129
  · exact terminal130
  · exact terminal131
  · exact terminal132
  · exact terminal133
  · exact terminal134
  · exact terminal135
  · exact terminal136
  · exact terminal137
  · exact terminal138
  · exact terminal139
  · exact terminal140
  · exact terminal141
  · exact terminal142
  · exact terminal143
  · exact terminal144
  · exact terminal145
  · exact terminal146
  · exact terminal147
  · exact terminal148
  · exact terminal149
  · exact terminal150
  · exact terminal151
  · exact terminal152
  · exact terminal153
  · exact terminal154
  · exact terminal155
  · exact terminal156
  · exact terminal157
  · exact terminal158
  · exact terminal159
  · exact terminal160
  · exact terminal161
  · exact terminal162
  · exact terminal163
  · exact terminal164
  · exact terminal165
  · exact terminal166
  · exact terminal167
  · exact terminal168
  · exact terminal169
  · exact terminal170
  · exact terminal171
  · exact terminal172
  · exact terminal173
  · exact terminal174
  · exact terminal175
  · exact terminal176
  · exact terminal177
  · exact terminal178
  · exact terminal179
  · exact terminal180
  · exact terminal181
  · exact terminal182
  · exact terminal183
  · exact terminal184
  · exact terminal185
  · exact terminal186
  · exact terminal187
  · exact terminal188
  · exact terminal189
  · exact terminal190
  · exact terminal191
  · exact terminal192
  · exact terminal193
  · exact terminal194
  · exact terminal195
  · exact terminal196
  · exact terminal197
  · exact terminal198
  · exact terminal199
  · exact terminal200
  · exact terminal201
  · exact terminal202
  · exact terminal203
  · exact terminal204
  · exact terminal205
  · exact terminal206
  · exact terminal207
  · exact terminal208
  · exact terminal209
  · exact terminal210
  · exact terminal211
  · exact terminal212
  · exact terminal213
  · exact terminal214
  · exact terminal215
  · exact terminal216
  · exact terminal217
  · exact terminal218
  · exact terminal219
  · exact terminal220
  · exact terminal221
  · exact terminal222
  · exact terminal223
  · exact terminal224
  · exact terminal225
  · exact terminal226
  · exact terminal227
  · exact terminal228
  · exact terminal229
  · exact terminal230
  · exact terminal231
  · exact terminal232
  · exact terminal233
  · exact terminal234
  · exact terminal235
  · exact terminal236
  · exact terminal237
  · exact terminal238
  · exact terminal239
  · exact terminal240
  · exact terminal241
  · exact terminal242
  · exact terminal243
  · exact terminal244
  · exact terminal245
  · exact terminal246
  · exact terminal247
  · exact terminal248
  · exact terminal249
  · exact terminal250
  · exact terminal251
  · exact terminal252
  · exact terminal253
  · exact terminal254
  · exact terminal255
  · exact terminal256
  · exact terminal257
  · exact terminal258
  · exact terminal259
  · exact terminal260
  · exact terminal261
  · exact terminal262
  · exact terminal263
  · exact terminal264
  · exact terminal265
  · exact terminal266
  · exact terminal267
  · exact terminal268
  · exact terminal269
  · exact terminal270
  · exact terminal271
  · exact terminal272
  · exact terminal273
  · exact terminal274
  · exact terminal275
  · exact terminal276
  · exact terminal277
  · exact terminal278
  · exact terminal279
  · exact terminal280
  · exact terminal281
  · exact terminal282
  · exact terminal283
  · exact terminal284
  · exact terminal285
  · exact terminal286
  · exact terminal287
  · exact terminal288
  · exact terminal289
  · exact terminal290
  · exact terminal291
  · exact terminal292
  · exact terminal293
  · exact terminal294
  · exact terminal295
  · exact terminal296
  · exact terminal297
  · exact terminal298
  · exact terminal299
  · exact terminal300
  · exact terminal301
  · exact terminal302
  · exact terminal303
  · exact terminal304
  · exact terminal305
  · exact terminal306
  · exact terminal307
  · exact terminal308
  · exact terminal309
  · exact terminal310
  · exact terminal311
  · exact terminal312
  · exact terminal313
  · exact terminal314
  · exact terminal315
  · exact terminal316
  · exact terminal317
  · exact terminal318
  · exact terminal319
  · exact terminal320
  · exact terminal321
  · exact terminal322
  · exact terminal323
  · exact terminal324
  · exact terminal325
  · exact terminal326
  · exact terminal327
  · exact terminal328
  · exact terminal329
  · exact terminal330
  · exact terminal331
  · exact terminal332
  · exact terminal333
  · exact terminal334
  · exact terminal335
  · exact terminal336
  · exact terminal337
  · exact terminal338
  · exact terminal339
  · exact terminal340
  · exact terminal341
  · exact terminal342
  · exact terminal343
  · exact terminal344
  · exact terminal345
  · exact terminal346
  · exact terminal347
  · exact terminal348
  · exact terminal349
  · exact terminal350
  · exact terminal351
  · exact terminal352
  · exact terminal353
  · exact terminal354
  · exact terminal355
  · exact terminal356
  · exact terminal357
  · exact terminal358
  · exact terminal359
  · exact terminal360
  · exact terminal361
  · exact terminal362
  · exact terminal363
  · exact terminal364
  · exact terminal365
  · exact terminal366
  · exact terminal367
  · exact terminal368
  · exact terminal369
  · exact terminal370
  · exact terminal371
  · exact terminal372
  · exact terminal373
  · exact terminal374
  · exact terminal375
  · exact terminal376
  · exact terminal377
  · exact terminal378
  · exact terminal379
  · exact terminal380
  · exact terminal381
  · exact terminal382
  · exact terminal383
  · exact terminal384
  · exact terminal385
  · exact terminal386
  · exact terminal387
  · exact terminal388
  · exact terminal389
  · exact terminal390
  · exact terminal391
  · exact terminal392
  · exact terminal393
  · exact terminal394
  · exact terminal395
  · exact terminal396

end PEqualNP.Outside.L_meta_908_aux

theorem PEqualNP.Outside.L_meta_908 : ∀ G : SimpleGraph (Fin 9), G = SimpleGraph.fromRel (fun a b : Fin 9 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5), (3, 7), (4, 6), (4, 8), (5, 7), (6, 8), (7, 8)] : List (ℕ × ℕ))) →
  ∀ C : PEqualNP.AndCount.AndCountCircuit 9, C.WellFormed →
    (∀ I : Finset (Fin 9), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 9, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 9, w ∉ I → C.eval (insert w I) = true) →
    6 ≤ C.size := by
  intro G hg C _ ok
  subst G
  by_contra low
  have small : C.size ≤ 5 := by omega
  obtain ⟨i,hi,fit⟩ := PEqualNP.Outside.L_meta_908_aux.classified5 (PEqualNP.Outside.L_meta_908_aux.circuit_realizable C small ok)
  exact PEqualNP.Outside.L_meta_908_aux.everyTerminal i hi fit
