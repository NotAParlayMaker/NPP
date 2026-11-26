import PEqualNP.Defs

-- Submitted via OpenAI Codex by gpt-6.2-astra.
-- Bitwise gate evaluation adapts R_meta_1342_642. The negative row cover
-- adapts R_meta_7692_481 to the two different incidence requirements.
-- The monotonicity premise is shared with R_meta_6670_317.

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 50000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_6670_836
    (packed : ∃ (p : Fin 22 → Bool × Fin 36 × Fin 36) (o : Fin 22),
      (∀ j : Fin 22, (p j).2.1.val < 14+j.val ∧ (p j).2.2.val < 14+j.val ∧
        (p j).2.1 ≠ (p j).2.2) ∧
      let w := (List.ofFn p).foldl (fun (w : List ℕ) (t : Bool × Fin 36 × Fin 36) =>
        w ++ [if t.1 = true then w.getD t.2.1.val 0 &&& w.getD t.2.2.val 0
              else w.getD t.2.1.val 0 ||| w.getD t.2.2.val 0]) ([2096402563585, 1908774503976962, 7268796792840, 11868302994571348, 6852534434792576, 483785355044896, 16676438272, 22821541807390727, 27339504955162624, 23715654360105016, 19568575878529472, 28717078517124608, 33785758938591232, 36020000926171136] : List ℕ)
      w.getD (14+o.val) 0 = 262143)
    (mono : ∀ (C : Circuit), TopForm.IsAO2 14 C → ∀ x y : Fin 14 → Bool,
      (∀ i, x i = true → y i = true) → C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (22 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ (14 : ℕ) ≤ x1.output ∧ x1.output < (14 : ℕ) + x1.size ∧ ∀ (x2 : Fin (14 : ℕ) → Bool), (x1.eval (List.ofFn x2) = Bool.true → ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x5) = Bool.true) ∧ ((∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), x4 ≠ (1 : Fin (7 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true) → x1.eval (List.ofFn x2) = Bool.true) := by
  obtain ⟨p,o,ports,hout⟩ := packed
  let mk : Bool × Fin 36 × Fin 36 → Gate := fun t =>
    ⟨if t.1 = true then .and else .or, [t.2.1.val,t.2.2.val]⟩
  let ns : List ℕ → (Bool × Fin 36 × Fin 36) → List ℕ := fun w t =>
    w ++ [if t.1 = true then w.getD t.2.1.val 0 &&& w.getD t.2.2.val 0
          else w.getD t.2.1.val 0 ||| w.getD t.2.2.val 0]
  let bs : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let C : Circuit := ⟨(List.ofFn p).map mk,14+o.val⟩
  let cols : List ℕ := [2096402563585, 1908774503976962, 7268796792840, 11868302994571348, 6852534434792576, 483785355044896, 16676438272, 22821541807390727, 27339504955162624, 23715654360105016, 19568575878529472, 28717078517124608, 33785758938591232, 36020000926171136]
  have sz : C.size = 22 := by change ((List.ofFn p).map mk).length = 22; simp
  have gate (i : Fin 22) : gateAt C i.val = mk (p i) := by
    change (((List.ofFn p).map mk).getD i.val _) = _
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_ofFn, dite_eq_left i.isLt, Option.map_some, Option.getD_some]
  have listed (g : Gate) (hg : g ∈ C.gates) : ∃ i : Fin 22, g = mk (p i) := by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨i,rfl⟩
  have ao : TopForm.IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨i,rfl⟩ := listed g hg
      by_cases h : (p i).1 = true <;> simp [mk,h]
    · intro j hj a ha
      have h : j < 22 := by change j < C.size at hj; omega
      let i : Fin 22 := ⟨j,h⟩
      rw [show gateAt C j = mk (p i) from gate i] at ha
      change a ∈ [(p i).2.1.val, (p i).2.2.val] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact (ports i).1
      · exact (ports i).2.1
    · intro g hg
      obtain ⟨i,rfl⟩ := listed g hg
      rfl
  have nd : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨i,rfl⟩ := listed g hg
    change ([(p i).2.1.val, (p i).2.2.val] : List ℕ).Nodup
    have distinct : (p i).2.1.val ≠ (p i).2.2.val := fun h => (ports i).2.2 (Fin.ext h)
    simp [distinct]
  have encode (k : ℕ) :
      (((List.ofFn p).foldl ns cols).getD (14+o.val) 0).testBit k =
        C.eval (cols.map (fun z => z.testBit k)) := by
    let bit : ℕ → Bool := fun z => z.testBit k
    have getBit (w : List ℕ) (i : ℕ) :
        (w.map bit).getD i false = bit (w.getD i 0) := by
      simp only [bit,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases w[i]? <;> simp
    have stepBit (w : List ℕ) (t : Bool × Fin 36 × Fin 36) :
        (ns w t).map bit = bs (w.map bit) (mk t) := by
      by_cases h : t.1 = true
      · simp only [ns,bs,mk,h,ite_true,List.map_append,List.map_cons,List.map_nil]
        change w.map bit ++ [bit (w.getD t.2.1.val 0 &&& w.getD t.2.2.val 0)] =
          w.map bit ++ [(w.map bit).getD t.2.1.val false && ((w.map bit).getD t.2.2.val false && true)]
        rw [getBit,getBit]
        simp only [bit,Nat.testBit_and,Bool.and_true]
      · simp only [ns,bs,mk,h,List.map_append,List.map_cons,List.map_nil]
        change w.map bit ++ [bit (w.getD t.2.1.val 0 ||| w.getD t.2.2.val 0)] =
          w.map bit ++ [(w.map bit).getD t.2.1.val false || ((w.map bit).getD t.2.2.val false || false)]
        rw [getBit,getBit]
        simp only [bit,Nat.testBit_or,Bool.or_false]
    have foldBits : ∀ (ts : List (Bool × Fin 36 × Fin 36)) (w : List ℕ),
        (ts.foldl ns w).map bit = (ts.map mk).foldl bs (w.map bit) := by
      intro ts
      induction ts with
      | nil => intro w; rfl
      | cons t ts ih =>
        intro w
        simp only [List.foldl_cons,List.map_cons]
        rw [ih,stepBit]
    change bit (((List.ofFn p).foldl ns cols).getD (14+o.val) 0) =
      (((List.ofFn p).map mk).foldl bs (cols.map bit)).getD (14+o.val) false
    rw [← foldBits,getBit]
  let row (k : ℕ) (i : Fin 14) := (cols.getD i.val 0).testBit k
  let E := fun a b : Fin 7 => a = b ∨ a = b+1 ∨ a = b+3
  have test (k : ℕ) : C.eval (List.ofFn (row k)) = (262143 : ℕ).testBit k := by
    change ((List.ofFn p).foldl ns cols).getD (14+o.val) 0 = 262143 at hout
    have h := encode k
    rw [hout] at h
    exact h.symm
  have pos : ∀ a b : Fin 7, b ≠ 1 → E a b → ∃ k : Fin 18,
      ∀ i : Fin 14, row k.val i = true → i = Fin.castAdd 7 a ∨ i = Fin.natAdd 7 b := by
    decide +kernel
  have neg : ∀ a : Fin 7 → Bool, ∃ k : Fin 37,
      (∀ i : Fin 7, a i = true → row (18+k.val) (Fin.castAdd 7 i) = true) ∧
      (∀ j : Fin 7, (∀ i : Fin 7, E i j → a i = false) → row (18+k.val) (Fin.natAdd 7 j) = true) := by
    decide +kernel
  have yes : ∀ k : Fin 18, (262143 : ℕ).testBit k.val = true := by decide +kernel
  have no : ∀ k : Fin 37, (262143 : ℕ).testBit (18+k.val) = false := by decide +kernel
  refine ⟨C, by omega, ao, nd, by change 14 ≤ 14+o.val; omega, ?_, ?_⟩
  · change 14+o.val < 14+C.size
    have := o.isLt
    omega
  · intro x
    constructor
    · intro hx
      by_contra none
      obtain ⟨k,hp,hl⟩ := neg (fun i => x (Fin.castAdd 7 i))
      have sub : ∀ i : Fin 14, x i = true → row (18+k.val) i = true := by
        intro i hi
        by_cases h : i.val < 7
        · let p : Fin 7 := ⟨i.val,h⟩
          have eq : Fin.castAdd 7 p = i := Fin.ext rfl
          rw [← eq] at hi ⊢
          exact hp p hi
        · let j : Fin 7 := ⟨i.val-7, by omega⟩
          have eq : Fin.natAdd 7 j = i := Fin.ext (by simp [j]; omega)
          rw [← eq] at hi ⊢
          apply hl j
          intro p he
          cases hx' : x (Fin.castAdd 7 p)
          · rfl
          · exact False.elim (none ⟨p,j,he,hx',hi⟩)
      exact Bool.false_ne_true (((test (18+k.val)).trans (no k)).symm.trans
        (mono C ao x (row (18+k.val)) sub hx))
    · rintro ⟨a,b,hb,he,ha,hb'⟩
      obtain ⟨k,hk⟩ := pos a b hb he
      refine mono C ao (row k.val) x ?_ ((test k.val).trans (yes k))
      intro i hi
      rcases hk i hi with rfl | rfl
      · exact ha
      · exact hb'
