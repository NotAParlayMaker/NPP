import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3002_827
    (pairLower : ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin x1), ∃ (x6 : Fin x1), x3.Adj x5 x6) → (∀ (x6 x7 : Fin x1), x6 ≠ x7 → ¬x3.Adj x6 x7 → (2 : ℕ) ≤ (x3.neighborSet x6).ncard → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → ∃ (x12 : Fin x1), ¬(x3.Adj x6 x12 ↔ x3.Adj x7 x12)) → (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → (2 : ℕ) ≤ (x3.neighborSet x7).ncard → (2 : ℕ) ≤ (x3.neighborSet x8).ncard → ∃ (x12 : Fin x1) (x13 : Fin x1), x3.Adj x7 x12 ∧ x12 ≠ x8 ∧ x3.Adj x8 x13 ∧ x13 ≠ x7 ∧ (x12 = x13 ∨ ¬x3.Adj x12 x13)) → (∃ (x8 : Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → (2 : ℕ) ≤ (x3.neighborSet x9).ncard → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → x9 ∈ x8 ∨ x10 ∈ x8) ∧ x8.card = x2) → (∀ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → (2 : ℕ) ≤ (x3.neighborSet x10).ncard → (2 : ℕ) ≤ (x3.neighborSet x11).ncard → x10 ∈ x9 ∨ x11 ∈ x9) → x2 ≤ x9.card) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x11 x12 : Fin x1), x4.eval (List.ofFn fun (x13 : Fin x1) => Decidable.decide (x13 = x11 ∨ x13 = x12)) = Bool.true ↔ x3.Adj x11 x12) → x1 + x2 ≤ x4.size + (1 : ℕ))
    (largeOrder : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : ℕ) (x11 : ℕ → Set (Finset ℕ)), x10 < x2 + x2 + x9 → (∀ x13 < x2 + x2, x11 x13 = {{x13}}) → (∀ x14 < x9, ∃ x16 < x2 + x2 + x14, ∃ x17 < x2 + x2 + x14, x11 (x2 + x2 + x14) = Set.image2 (fun (x18 x19 : Finset ℕ) => x18 ∪ x19) (x11 x16) (x11 x17) ∨ x11 (x2 + x2 + x14) = x11 x16 ∨ x11 (x2 + x2 + x14) = {∅} ∨ x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17) → (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → ↑x17 ∈ x15 ∨ x2 + ↑x18 ∈ x15) → (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, ∀ (x19 : Fin x2), (↑x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ (x2 + ↑x19 ∈ x18 ↔ x19 ∉ x16)) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  let familyAccepts (F : Set (Finset ℕ)) (row : List Bool) : Prop :=
    ∀ A ∈ F, ∃ v ∈ A, row.getD v false = true

  have acceptsProduct (U V : Set (Finset ℕ)) (row : List Bool) :
      familyAccepts (Set.image2 (· ∪ ·) U V) row ↔ familyAccepts U row ∨ familyAccepts V row := by
    classical
    constructor
    · intro product
      by_cases left : familyAccepts U row
      · exact Or.inl left
      right
      simp only [familyAccepts, not_forall] at left
      obtain ⟨A, hA, misses⟩ := left
      intro B hB
      obtain ⟨v, member, bit⟩ := product (A ∪ B) ⟨A, hA, B, hB, rfl⟩
      rcases Finset.mem_union.mp member with inA | inB
      · exact (misses ⟨v, inA, bit⟩).elim
      · exact ⟨v, inB, bit⟩
    · intro which C inC
      obtain ⟨A, hA, B, hB, rfl⟩ := inC
      rcases which with left | right
      · obtain ⟨v,hv,bit⟩ := left A hA
        exact ⟨v, Finset.mem_union_left _ hv, bit⟩
      · obtain ⟨v,hv,bit⟩ := right B hB
        exact ⟨v, Finset.mem_union_right _ hv, bit⟩

  have acceptsChoice (U V : Set (Finset ℕ)) (row : List Bool) :
      familyAccepts (U ∪ V) row ↔ familyAccepts U row ∧ familyAccepts V row := by
    constructor
    · intro h
      exact ⟨fun A hA => h A (Or.inl hA), fun A hA => h A (Or.inr hA)⟩
    · intro both A hA
      exact hA.elim (both.1 A) (both.2 A)

  let step (wires : List Bool) (gate : Gate) : List Bool :=
    wires ++ [gate.op.eval (gate.inputs.map fun v => wires.getD v false)]

  have wireCount (gates : List Gate) (input : List Bool) :
      (gates.foldl step input).length = input.length + gates.length := by
    induction gates generalizing input with
    | nil => simp
    | cons gate gates ih => rw [List.foldl_cons,ih]; simp [step]; omega

  have build (m s : ℕ) (F : ℕ → Set (Finset ℕ))
      (inputs : ∀ v < m, F v = {{v}})
      (steps : ∀ g < s, ∃ a < m + g, ∃ b < m + g,
        F (m + g) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (m + g) = F a ∨
          F (m + g) = {∅} ∨ F (m + g) = F a ∪ F b) :
      ∃ gates : List Gate, gates.length = s ∧ Monotone2 ⟨gates,0⟩ ∧
        ∀ row : List Bool, row.length = m → ∀ w < m + s,
          (gates.foldl step row).getD w false = true ↔ familyAccepts (F w) row := by
    induction s with
    | zero =>
      refine ⟨[], rfl, (fun _ member => (List.not_mem_nil member).elim), ?_⟩
      intro row rowSize w hw
      rw [inputs w (by omega)]
      simp [familyAccepts]
    | succ s ih =>
      obtain ⟨gates, gateCount, monotone, meaning⟩ := ih (fun g hg => steps g (by omega))
      obtain ⟨a, ha, b, hb, law⟩ := steps s (by omega)
      have newGate : ∃ gate : Gate,
          gate.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ gate.inputs.length ≤ 2 ∧
          ∀ row : List Bool, row.length = m →
            (gate.op.eval (gate.inputs.map (fun v => (gates.foldl step row).getD v false)) = true ↔
              familyAccepts (F (m + s)) row) := by
        rcases law with product | copy | constant | choice
        · refine ⟨⟨.or,[a,b]⟩, by simp, by simp, ?_⟩
          intro row rowSize
          change ((gates.foldl step row).getD a false ||
              ((gates.foldl step row).getD b false || false)) = true ↔ _
          rw [Bool.or_false, Bool.or_eq_true, meaning row rowSize a ha, meaning row rowSize b hb,
            product, acceptsProduct]
        · refine ⟨⟨.or,[a]⟩, by simp, by simp, ?_⟩
          intro row rowSize
          change ((gates.foldl step row).getD a false || false) = true ↔ _
          rw [Bool.or_false, meaning row rowSize a ha, copy]
        · refine ⟨⟨.or,[]⟩, by simp, by simp, ?_⟩
          intro row _
          change false = true ↔ _
          rw [constant]
          simp [familyAccepts]
        · refine ⟨⟨.and,[a,b]⟩, by simp, by simp, ?_⟩
          intro row rowSize
          change ((gates.foldl step row).getD a false &&
              ((gates.foldl step row).getD b false && true)) = true ↔ _
          rw [Bool.and_true, Bool.and_eq_true, meaning row rowSize a ha, meaning row rowSize b hb,
            choice, acceptsChoice]
      obtain ⟨gate, op, arity, newMeaning⟩ := newGate
      refine ⟨gates ++ [gate], by simp [gateCount], ?_, ?_⟩
      · intro g member
        change g ∈ gates ++ [gate] at member
        rcases List.mem_append.mp member with old | new
        · exact monotone g old
        · have same := List.mem_singleton.mp new
          exact same.symm ▸ ⟨op, arity⟩
      · intro row rowSize w wBound
        let wires := gates.foldl step row
        let value := gate.op.eval (gate.inputs.map fun v => wires.getD v false)
        have length : wires.length = m + s := by rw [wireCount, rowSize, gateCount]
        change ((gates ++ [gate]).foldl step row).getD w false = true ↔ _
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        change (wires ++ [value]).getD w false = true ↔ _
        by_cases earlier : w < m + s
        · rw [List.getD_append _ _ _ _ (by omega : w < wires.length)]
          exact meaning row rowSize w earlier
        · have atLast : w = m + s := by omega
          rw [atLast, ← length]
          have lastValue : (wires ++ [value]).getD wires.length false = value := by
            rw [List.getD_append_right _ _ _ _ (Nat.le_refl wires.length)]
            simp
          rw [lastValue, length]
          exact newMeaning row rowSize

  have extract (m s o : ℕ) (F : ℕ → Set (Finset ℕ)) :
      o < m + s → (∀ v < m, F v = {{v}}) →
      (∀ j < s, ∃ a < m + j, ∃ b < m + j,
        F (m + j) = Set.image2 (· ∪ ·) (F a) (F b) ∨ F (m + j) = F a ∨
          F (m + j) = {∅} ∨ F (m + j) = F a ∪ F b) →
      ∃ C : Circuit, C.size = s ∧ Monotone2 C ∧
        ∀ x : Fin m → Bool, circuitFun m C x = true ↔
          ∀ A ∈ F o, ∃ v ∈ A, (List.ofFn x).getD v false = true := by
    intro outputBound inputs steps
    obtain ⟨gates, count, monotone, meaning⟩ := build m s F inputs steps
    exact ⟨⟨gates,o⟩, count, monotone, fun x => meaning (List.ofFn x) (by simp) o outputBound⟩
  have circuitBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      200 ≤ q → N = q^2+q+1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r : Fin N, p ≠ r → ∃! l, I p l ∧ I r l) → Monotone2 C →
      (∀ p l, I p l → circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
        (¬∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
          circuitFun (N+N) C x = false) → N*q ≤ 100*C.size := by
    let L {N : ℕ} : Fin N → Fin (N+N) := Fin.castAdd N
    let R {N : ℕ} : Fin N → Fin (N+N) := Fin.natAdd N
    have sides {N : ℕ} (p l : Fin N) : L p ≠ R l := by
      intro equal
      have val := congrArg Fin.val equal
      change p.val = N + l.val at val
      have inRange := p.isLt
      omega
    have leftInjective {N : ℕ} : Function.Injective (@L N) := by
      intro a b eq
      have valuations : (L a).val = (L b).val := congrArg Fin.val eq
      exact Fin.ext valuations
    have rightInjective {N : ℕ} : Function.Injective (@R N) := by
      intro a b eq
      have val := congrArg Fin.val eq
      change N + a.val = N + b.val at val
      exact Fin.ext (by omega)
    let graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) :=
      SimpleGraph.fromRel (fun x y => ∃ p l, x = L p ∧ y = R l ∧ I p l)
    have adjEither {N : ℕ} (I : Fin N → Fin N → Prop) (x y : Fin (N+N)) :
        (graph I).Adj x y ↔
          (∃ p l, x = L p ∧ y = R l ∧ I p l) ∨ (∃ p l, y = L p ∧ x = R l ∧ I p l) := by
      unfold graph
      rw [SimpleGraph.fromRel_adj]
      constructor
      · exact And.right
      · intro ok
        refine ⟨?_,ok⟩
        rintro rfl
        rcases ok with ⟨p,l,atP,atL,_⟩ | ⟨p,l,atP,atL,_⟩
        · exact sides p l (atP.symm.trans atL)
        · exact sides p l (atP.symm.trans atL)
    have leftNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) (y : Fin (N+N)) :
        (graph I).Adj (L p) y ↔ ∃ l, y = R l ∧ I p l := by
      rw [adjEither]
      constructor
      · rintro (⟨p',l,atP,atL,inc⟩ | ⟨p',l,_,invalid,_⟩)
        · exact ⟨l, atL, (leftInjective atP).symm ▸ inc⟩
        · exact (sides p l invalid).elim
      · rintro ⟨l,eq,inc⟩
        exact Or.inl ⟨p,l,rfl,eq,inc⟩
    have rightNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) (y : Fin (N+N)) :
        (graph I).Adj (R l) y ↔ ∃ p, y = L p ∧ I p l := by
      rw [adjEither]
      constructor
      · rintro (⟨p,l',invalid,_,_⟩ | ⟨p,l',atP,atL,inc⟩)
        · exact (sides p l invalid.symm).elim
        · exact ⟨p,atP,(rightInjective atL).symm ▸ inc⟩
      · rintro ⟨p,eq,inc⟩
        exact Or.inr ⟨p,l,eq,rfl,inc⟩
    have leftRight {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
        (graph I).Adj (L p) (R l) ↔ I p l := by
      rw [leftNeighbors]
      constructor
      · rintro ⟨k,eq,inc⟩
        exact (rightInjective eq).symm ▸ inc
      · exact fun inc => ⟨l,rfl,inc⟩
    have noFour {N : ℕ} (I : Fin N → Fin N → Prop)
        (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
        (u v a b : Fin (N+N)) (vertices : u ≠ v) (neighbors : a ≠ b)
        (ua : (graph I).Adj u a) (ub : (graph I).Adj u b)
        (va : (graph I).Adj v a) (vb : (graph I).Adj v b) : False := by
      have crosses (p l : Fin N) (otherP otherL : Fin (N+N))
          (differentP : L p ≠ otherP) (differentL : R l ≠ otherL)
          (pl : I p l) (pOther : (graph I).Adj (L p) otherL)
          (otherL' : (graph I).Adj otherP (R l)) (pair : (graph I).Adj otherP otherL) : False := by
        obtain ⟨k, rfl, pk⟩ := (leftNeighbors I p otherL).mp pOther
        obtain ⟨r, rfl, rl⟩ := (rightNeighbors I l otherP).mp ((graph I).adj_symm otherL')
        have rk := (leftRight I r k).mp pair
        have distinct : p ≠ r := fun eq => differentP (congrArg L eq)
        have same := (unique p r distinct).unique ⟨pl,rl⟩ ⟨pk,rk⟩
        exact differentL (congrArg R same)
      rcases (adjEither I u a).mp ua with ⟨p,l,rfl,rfl,pl⟩ | ⟨p,l,rfl,rfl,pl⟩
      · exact crosses p l v b vertices neighbors pl ub va vb
      · exact crosses p l b v neighbors vertices pl ((graph I).adj_symm va) ((graph I).adj_symm ub) ((graph I).adj_symm vb)
    have enoughNeighbors (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (big : 200 ≤ q) (order : N = q^2+q+1)
        (degree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
        (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
        (v : Fin (N+N)) : ∃ a b, a ≠ b ∧ (graph I).Adj v a ∧ (graph I).Adj v b := by
      classical
      have roomy : q+1 < N := by rw [order]; nlinarith
      have pointsOn (l : Fin N) : (Finset.univ.filter fun p : Fin N => I p l).card = q+1 :=
        (Fintype.card_subtype (fun p => I p l)).symm.trans (degree l)
      have outside (l : Fin N) : ∃ p, ¬ I p l := by
        by_contra! every
        have full : (Finset.univ.filter fun p : Fin N => I p l) = Finset.univ := by ext p; simp [every]
        have count := pointsOn l
        rw [full] at count
        simp at count
        omega
      have twoPoints : ∃ a b : Fin N, a ≠ b := by
        obtain ⟨a,b,_,_,distinct⟩ := Finset.one_lt_card_iff.mp
          (show 1 < (Finset.univ : Finset (Fin N)).card from by simp; omega)
        exact ⟨a,b,distinct⟩
      refine Fin.addCases (fun p => ?_) (fun l => ?_) v
      · obtain ⟨a,b,distinct⟩ := twoPoints
        have other : ∃ r : Fin N, p ≠ r := by by_cases eq : p=a; exact ⟨b,eq ▸ distinct⟩; exact ⟨a,eq⟩
        obtain ⟨r,diff⟩ := other
        obtain ⟨l,onL,_⟩ := unique p r diff
        obtain ⟨z,off⟩ := outside l
        have newPoint : p ≠ z := fun eq => off (eq ▸ onL.1)
        obtain ⟨k,onK,_⟩ := unique p z newPoint
        have otherLine : l ≠ k := fun eq => off (eq ▸ onK.2)
        exact ⟨R l,R k,fun eq => otherLine (rightInjective eq),(leftRight I p l).mpr onL.1,
          (leftRight I p k).mpr onK.1⟩
      · obtain ⟨a,b,memA,memB,distinct⟩ := Finset.one_lt_card_iff.mp
          (show 1 < (Finset.univ.filter fun p : Fin N => I p l).card from by rw [pointsOn]; omega)
        exact ⟨L a,L b,fun eq => distinct (leftInjective eq),
          (graph I).adj_symm ((leftRight I a l).mpr (Finset.mem_filter.mp memA).2),
          (graph I).adj_symm ((leftRight I b l).mpr (Finset.mem_filter.mp memB).2)⟩
    have pointDegree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (positive : 0 < q) (order : N = q^2+q+1)
        (degrees : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
        (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
        (p : Fin N) : (Finset.univ.filter fun l : Fin N => I p l).card = q+1 := by
      classical
      let through := Finset.univ.filter (fun l : Fin N => I p l)
      let rest (l : Fin N) := Finset.univ.filter (fun r : Fin N => I r l ∧ r ≠ p)
      have count (l : Fin N) (hl : l ∈ through) : (rest l).card = q := by
        let full := Finset.univ.filter (fun r : Fin N => I r l)
        have same : rest l = full.erase p := by ext r; simp [rest,full,and_comm]
        have inFull : p ∈ full := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
        have cardFull : full.card = q+1 := (Fintype.card_subtype (fun r => I r l)).symm.trans (degrees l)
        rw [same,Finset.card_erase_of_mem inFull,cardFull]
        omega
      have disjoint : (↑through : Set (Fin N)).PairwiseDisjoint rest := by
        intro l other k more different
        refine Finset.disjoint_left.mpr ?_
        intro r here there
        have throughL : I p l := (Finset.mem_filter.mp other).2
        have throughK : I p k := (Finset.mem_filter.mp more).2
        obtain ⟨rl,diff⟩ := (Finset.mem_filter.mp here).2
        have rk := (Finset.mem_filter.mp there).2.1
        exact different ((unique p r (Ne.symm diff)).unique ⟨throughL,rl⟩ ⟨throughK,rk⟩)
      have together : through.biUnion rest = Finset.univ.erase p := by
        ext r
        constructor
        · intro seen
          obtain ⟨l,_,rl⟩ := Finset.mem_biUnion.mp seen
          exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp rl).2.2,Finset.mem_univ _⟩
        · intro seen
          have diff := (Finset.mem_erase.mp seen).1
          obtain ⟨l,⟨pl,rl⟩,_⟩ := unique p r (Ne.symm diff)
          exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,pl⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _,rl,diff⟩⟩
      have rightSize : (Finset.univ.erase p).card = (q+1)*q := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin,order]
        rw [Nat.add_sub_cancel]
        ring
      have scale : through.card*q = (q+1)*q := by
        calc
          through.card*q = ∑ l ∈ through, q := by simp
          _ = ∑ l ∈ through, (rest l).card := Finset.sum_congr rfl (fun l hl => (count l hl).symm)
          _ = (through.biUnion rest).card := (Finset.card_biUnion disjoint).symm
          _ = (q+1)*q := by rw [together,rightSize]
      exact Nat.eq_of_mul_eq_mul_right positive scale
    have coverBudget (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (rowDegree : ∀ p : Fin N, (Finset.univ.filter fun l : Fin N => I p l).card = q+1)
        (columnDegree : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1)
        (S : Finset (Fin (N+N))) (covers : ∀ p l, I p l → L p ∈ S ∨ R l ∈ S) : N ≤ S.card := by
      classical
      let edges := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
      let rows (p : Fin N) := (Finset.univ.filter fun l : Fin N => I p l).image fun l => (p,l)
      let columns (l : Fin N) := (Finset.univ.filter fun p : Fin N => I p l).image fun p => (p,l)
      let star (v : Fin (N+N)) : Finset (Fin N × Fin N) := Fin.addCases rows columns v
      have rowSize (p : Fin N) : (rows p).card = q+1 := by
        dsimp only [rows]
        rw [Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.snd eq),rowDegree]
      have columnSize (l : Fin N) : (columns l).card = q+1 := by
        dsimp only [columns]
        rw [Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq),
          ← Fintype.card_subtype (fun p => I p l),columnDegree]
      have starSize (v : Fin (N+N)) : (star v).card = q+1 := by
        refine Fin.addCases (fun p => ?_) (fun l => ?_) v
        · simpa [star] using rowSize p
        · simpa only [star,Fin.addCases_right] using columnSize l
      have distinct : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint columns := by
        intro l _ k _ different
        refine Finset.disjoint_left.mpr ?_
        intro e inL inK
        obtain ⟨p,_,left⟩ := Finset.mem_image.mp inL
        obtain ⟨r,_,right⟩ := Finset.mem_image.mp inK
        exact different (congrArg Prod.snd (left.trans right.symm))
      have edgeSize : edges.card = N*(q+1) := by
        have same : edges = Finset.univ.biUnion columns := by
          ext e
          rcases e with ⟨p,l⟩
          simp [edges,columns,Prod.mk.injEq]
        rw [same,Finset.card_biUnion distinct]
        simp [columnSize]
      have capture : edges ⊆ S.biUnion star := by
        rintro ⟨p,l⟩ good
        have relation := (Finset.mem_filter.mp good).2
        rcases covers p l relation with atP | atL
        · apply Finset.mem_biUnion.mpr
          refine ⟨L p,atP,?_⟩
          have inRow : (p,l) ∈ rows p := Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,relation⟩,rfl⟩
          simpa [star,L] using inRow
        · apply Finset.mem_biUnion.mpr
          refine ⟨R l,atL,?_⟩
          have inCol : (p,l) ∈ columns l := Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,relation⟩,rfl⟩
          simpa only [star,R,Fin.addCases_right] using inCol
      have budget : edges.card ≤ S.card*(q+1) :=
        (Finset.card_le_card capture).trans (Finset.card_biUnion_le.trans (by simp [starSize]))
      rw [edgeSize] at budget
      exact Nat.le_of_mul_le_mul_right budget (by omega)
    have pairTests (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (big : 200 ≤ q) (C : Circuit)
        (positive : ∀ p l : Fin N, I p l →
          circuitFun (N+N) C (fun i => decide (i = L p ∨ i = R l)) = true)
        (negative : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (R l) = true} ≤ q →
          (¬∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true) → circuitFun (N+N) C x = false) :
        ∀ u v : Fin (N+N), C.eval (List.ofFn fun i : Fin (N+N) => decide (i = u ∨ i = v)) = true ↔
          (graph I).Adj u v := by
      intro u v
      let x : Fin (N+N) → Bool := fun i => decide (i=u ∨ i=v)
      change circuitFun (N+N) C x = true ↔ (graph I).Adj u v
      constructor
      · intro recognized
        by_contra missing
        let toPair (a : {l : Fin N // x (R l) = true}) : {v' : Fin (N+N) // v' ∈ ({u,v} : Finset _)} := by
          refine ⟨R a.val,?_⟩
          have sits : R a.val = u ∨ R a.val = v := of_decide_eq_true a.property
          simpa only [Finset.mem_insert,Finset.mem_singleton] using sits
        have injective : Function.Injective toPair := by
          intro a b equal
          apply Subtype.ext
          have same := congrArg (fun z : {j : Fin (N+N) // j ∈ ({u,v} : Finset _)} => z.val) equal
          change R a.val = R b.val at same
          exact rightInjective same
        have small : Fintype.card {l : Fin N // x (R l) = true} ≤ q := by
          apply (Fintype.card_le_of_injective toPair injective).trans
          rw [Fintype.card_of_subtype ({u,v} : Finset (Fin (N+N))) (fun _ => Iff.rfl)]
          have bound := Finset.card_insert_le (a := u) (s := ({v} : Finset (Fin (N+N))))
          simp only [Finset.card_singleton] at bound
          omega
        have cannot : ¬∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true := by
          rintro ⟨p,l,inc,onP,onL⟩
          have hereP : L p = u ∨ L p = v := of_decide_eq_true onP
          have hereL : R l = u ∨ R l = v := of_decide_eq_true onL
          rcases hereP with left | right <;> rcases hereL with first | second
          · exact sides p l (left.trans first.symm)
          · apply missing
            exact (adjEither I u v).mpr (Or.inl ⟨p,l,left.symm,second.symm,inc⟩)
          · apply missing
            exact (adjEither I u v).mpr (Or.inr ⟨p,l,right.symm,first.symm,inc⟩)
          · exact sides p l (right.trans second.symm)
        rw [negative x small cannot] at recognized
        contradiction
      · intro inc
        rcases (adjEither I u v).mp inc with ⟨p,l,rfl,rfl,hit⟩ | ⟨p,l,rfl,rfl,hit⟩
        · exact positive p l hit
        · have eq : x = (fun i => decide (i=L p ∨ i=R l)) := by funext i; simp [x,or_comm]
          rw [eq]
          exact positive p l hit
    intro q N I _ C big order degrees unique mono positive negative
    by_cases high : 300 ≤ q
    · exact largeOrder q N I C high order degrees unique mono positive negative
    classical
    let G := graph I
    have neighbors (v : Fin (N+N)) : ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b :=
      enoughNeighbors q N I big order degrees unique v
    have atLeastTwo (v : Fin (N+N)) : 2 ≤ (G.neighborSet v).ncard := by
      obtain ⟨a,b,diff,va,vb⟩ := neighbors v
      have finite : (G.neighborSet v).Finite := Set.toFinite _
      rw [Set.ncard_eq_toFinset_card _ finite]
      exact Finset.one_lt_card_iff.mpr ⟨a,b,finite.mem_toFinset.mpr va,finite.mem_toFinset.mpr vb,diff⟩
    have noTwins (v w : Fin (N+N)) (different : v ≠ w) : ∃ a, ¬(G.Adj v a ↔ G.Adj w a) := by
      by_contra! same
      obtain ⟨a,b,distinct,va,vb⟩ := neighbors v
      exact noFour I unique v w a b different distinct va vb ((same a).mp va) ((same b).mp vb)
    have other (v w : Fin (N+N)) : ∃ a, G.Adj v a ∧ a ≠ w := by
      obtain ⟨a,b,different,va,vb⟩ := neighbors v
      by_cases first : a = w
      · exact ⟨b,vb,fun second => different (first.trans second.symm)⟩
      · exact ⟨a,va,first⟩
    have adjacent (v w : Fin (N+N)) (edge : G.Adj v w) :
        ∃ a b : Fin (N+N), G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬G.Adj a b) := by
      obtain ⟨a,va,notW⟩ := other v w
      obtain ⟨b,wb,notV⟩ := other w v
      refine ⟨a,b,va,notW,wb,notV,Or.inr ?_⟩
      intro ab
      exact noFour I unique w a v b (Ne.symm notW) (Ne.symm notV) (G.adj_symm edge) wb (G.adj_symm va) ab
    let cover (S : Finset (Fin (N+N))) : Prop :=
      ∀ u v, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S
    let coverSize (k : ℕ) : Prop := ∃ S : Finset (Fin (N+N)), cover S ∧ S.card = k
    have some : ∃ k, coverSize k :=
      ⟨_,Finset.univ,fun _ _ _ _ _ => Or.inl (Finset.mem_univ _),rfl⟩
    let t := Nat.find some
    have minimum : ∀ S : Finset (Fin (N+N)), cover S → t ≤ S.card := fun S ok =>
      Nat.find_min' some ⟨S,ok,rfl⟩
    obtain ⟨S,coverS,count⟩ := Nat.find_spec some
    have rows := pointDegree q N I (by omega) order degrees unique
    have tBig : N ≤ t := by
      change N ≤ Nat.find some
      rw [← count]
      apply coverBudget q N I rows degrees S
      intro p l inc
      exact coverS (L p) (R l) ((leftRight I p l).mpr inc) (atLeastTwo _) (atLeastTwo _)
    have floor := pairLower (N+N) t G C
      (fun v => by obtain ⟨a,_,_,adj,_⟩ := neighbors v; exact ⟨a,adj⟩)
      (fun v w distinct _ _ _ => noTwins v w distinct)
      (fun v w edge _ _ => adjacent v w edge)
      ⟨S,coverS,count⟩ minimum mono (pairTests q N I big C positive negative)
    have planeSize : 100 ≤ N := by rw [order]; omega
    have factor : N*q ≤ N*299 := Nat.mul_le_mul_left _ (by omega)
    omega
  intro q N incidence _decidable large order lineSize unique steps output families
    valid inputs gates cover witnesses
  obtain ⟨candidate, size, monotone, evaluate⟩ :=
    extract (N + N) steps output families valid inputs gates
  have readAt (x : Fin (N + N) → Bool) (index : Fin (N + N)) :
      (List.ofFn x).getD index.val false = x index := by
    rw [List.getD_eq_getElem _ _ (by simpa using index.isLt), List.getElem_ofFn]
  have accepts (point line : Fin N) (edge : incidence point line) :
      circuitFun (N + N) candidate
        (fun index => decide (index = Fin.castAdd N point ∨ index = Fin.natAdd N line)) = true := by
    let row : Fin (N + N) → Bool :=
      fun index => decide (index = Fin.castAdd N point ∨ index = Fin.natAdd N line)
    change circuitFun (N + N) candidate row = true
    apply (evaluate row).mpr
    intro certificate present
    rcases cover certificate present point line edge with atPoint | atLine
    · exact ⟨point.val, atPoint, (readAt row (Fin.castAdd N point)).trans (by simp [row])⟩
    · exact ⟨N + line.val, atLine, (readAt row (Fin.natAdd N line)).trans (by simp [row])⟩
  have rejects (x : Fin (N + N) → Bool)
      (sparse : Fintype.card {line : Fin N // x (Fin.natAdd N line) = true} ≤ q)
      (independent : ¬ ∃ point line, incidence point line ∧
        x (Fin.castAdd N point) = true ∧ x (Fin.natAdd N line) = true) :
      circuitFun (N + N) candidate x = false := by
    cases result : circuitFun (N + N) candidate x with
    | false => rfl
    | true =>
      exfalso
      let selected := Finset.univ.filter fun line : Fin N => x (Fin.natAdd N line) = true
      have sparseSelected : selected.card ≤ q := by
        simpa [selected, Fintype.card_subtype] using sparse
      obtain ⟨certificate, present, exactCertificate⟩ := witnesses selected sparseSelected
      obtain ⟨wire, inCertificate, active⟩ := (evaluate x).mp result certificate present
      have range : wire < N+N := by
        by_contra! outOfRange
        rw [List.getD_eq_default _ _ (by simpa using outOfRange)] at active
        contradiction
      let vertex : Fin (N+N) := ⟨wire, range⟩
      change vertex.val ∈ certificate at inCertificate
      have activeVertex : x vertex = true := by simpa only [← readAt x vertex] using active
      revert inCertificate activeVertex
      refine Fin.addCases (fun point => ?_) (fun line => ?_) vertex
      · intro included on
        obtain ⟨line, chosen, edge⟩ := (exactCertificate point).1.mp included
        have lineOn : x (Fin.natAdd N line) = true := (Finset.mem_filter.mp chosen).2
        exact independent ⟨point, line, edge, on, lineOn⟩
      · intro included on
        exact (exactCertificate line).2.mp included (Finset.mem_filter.mpr ⟨Finset.mem_univ _, on⟩)
  have lower := circuitBound q N incidence candidate large order lineSize unique monotone accepts rejects
  simpa only [size] using lower
