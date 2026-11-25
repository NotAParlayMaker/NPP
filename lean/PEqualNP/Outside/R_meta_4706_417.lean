import PEqualNP.Defs

-- Submitted via OpenAI Codex by gpt-6.2-astra.
-- Fix the free wire to the union of points zero and one.
-- Four gates restore the line-zero star and join it to the residual output.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_4706_417
    (geometry : let D : Finset (Fin 13) := {0,1,3,9}
      let reps : List (ℕ × ℕ) := [(7,904),(13,2848),(19,708),(21,2720),(25,2656),(37,2440),(41,2370),(133,808)]
      ∀ z ∈ reps, ∀ m ∈ ([1,3,9] : List (Fin 13)), ∀ t : Fin 13, ∀ b : Bool,
      let bit := fun (a c : ℕ) (i : Fin 13) =>
        if b then c.testBit (-(m*i+t)).val else a.testBit (m*i+t).val
      let x := Fin.append (bit z.1 z.2) (bit z.2 z.1)
      (∀ p w : Fin 13, p-w ∈ D →
        ¬ (x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)) ∧
      ((List.ofFn (fun i : Fin 13 => x (Fin.castAdd 13 i))).count true,
        (List.ofFn (fun i : Fin 13 => x (Fin.natAdd 13 i))).count true) ∈
        ([(3,4),(4,3)] : List (ℕ × ℕ)))
    (core : let D : Finset (Fin 13) := {0,1,3,9}
      let aug : (Fin 26 → Bool) → Fin 27 → Bool := fun (x : Fin 26 → Bool) => Fin.lastCases (x 0 || x 1) x
      ∃ C : Circuit, Monotone2 C ∧ NestedCover.ReadsBack 27 C ∧ C.size ≤ 58 ∧
        C.output < 27+C.size ∧
        (∀ p w : Fin 13, w ≠ 0 → p-w ∈ D →
          circuitFun 27 C (aug (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 w))) = true) ∧
        (∀ x : Fin 26 → Bool, (∀ p w : Fin 13, p-w ∈ D →
          ¬ (x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)) →
          ((List.ofFn (fun i : Fin 13 => x (Fin.castAdd 13 i))).count true,
        (List.ofFn (fun i : Fin 13 => x (Fin.natAdd 13 i))).count true) ∈
        ([(3,4),(4,3)] : List (ℕ × ℕ)) → circuitFun 27 C (aug x) = false)) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x3 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x3 : ℕ × ℕ) (x4 x5 : Fin (13 : ℕ)) (x6 : Bool) =>   have x7 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x7 x8 : ℕ) (x9 : Fin (13 : ℕ)) => if x6 = Bool.true then x8.testBit ↑(-(x4 * x9 + x5)) else x7.testBit ↑(x4 * x9 + x5);   Fin.append (x7 x3.1 x3.2) (x7 x3.2 x3.1); ∃ (x4 : Fin (4 : ℕ)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x5 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x5 ∧       x5.size ≤ (62 : ℕ) ∧         have x6 : Fin (26 : ℕ) := if ↑x4 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x4 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x7 : Bool := Decidable.decide (↑x4 = (0 : ℕ));         have x8 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x8 : Fin (26 : ℕ) → Bool) (x9 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x7 = Bool.true then x8 (0 : Fin (26 : ℕ)) && x8 x6 else x8 (0 : Fin (26 : ℕ)) || x8 x6) x8 x9;         (∀ (x9 x10 : Fin (13 : ℕ)), (∃ x11 ∈ x1, x9 = x10 + x11) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x5 (x8 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) ∧ ∀ x9 ∈ x2, ∀ x11 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∀ (x13 : Fin (13 : ℕ)) (x14 : Bool), PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x5 (x8 (x3 x9 x11 x13 x14)) = Bool.false := by
  obtain ⟨C, hm, hb, hs, ho, hp, hn⟩ := core
  have sz (Q : Circuit) : Q.size = Q.gates.length := rfl
  have lookup (Q : Circuit) (j : ℕ) : NestedCover.gateAt Q j = Q.gates.getD j ⟨.or,[]⟩ := rfl
  let k := 27 + C.size
  let tail : List Gate := [⟨.or,[3,9]⟩, ⟨.or,[26,k]⟩,
    ⟨.and,[13,k+1]⟩, ⟨.or,[C.output,k+2]⟩]
  let E : Circuit := ⟨C.gates ++ tail, k+3⟩
  have em : Monotone2 E := by
    intro g hg
    rcases List.mem_append.mp hg with old | new
    · exact hm g old
    · simp only [tail, List.mem_cons, List.not_mem_nil, or_false] at new
      rcases new with rfl | rfl | rfl | rfl <;> simp
  have eb : NestedCover.ReadsBack 27 E := by
    intro j hj i hi
    by_cases h : j < C.gates.length
    · apply hb j h i
      simpa [lookup, E, List.getD_eq_getElem?_getD,
        List.getElem?_append, h] using hi
    · have hj' : j < C.gates.length + 4 := by simpa [E,tail] using hj
      have cases : j = C.gates.length ∨ j = C.gates.length+1 ∨
          j = C.gates.length+2 ∨ j = C.gates.length+3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;>
        simp [lookup, E, tail, List.getD_eq_getElem?_getD] at hi <;>
        change C.output < 27 + C.gates.length at ho <;>
        (try simp only [k,sz] at hi ⊢) <;> omega
  have es : E.size ≤ 62 := by simpa [E,tail,sz] using (show C.gates.length + 4 ≤ 62 by change C.gates.length ≤ 58 at hs; omega)
  let aug : (Fin 26 → Bool) → Fin 27 → Bool := fun (x : Fin 26 → Bool) => Fin.lastCases (x 0 || x 1) x
  have run (x : Fin 26 → Bool) :
      circuitFun 27 E (aug x) =
        (circuitFun 27 C (aug x) || (x 13 && ((x 0 || x 1) || (x 3 || x 9)))) := by
    let step := fun (w : List Bool) (g : Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have wireExtension (gs : List Gate) (w : List Bool) :
        ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
      induction gs generalizing w with
      | nil => exact ⟨[], by simp⟩
      | cons g gs ih =>
        obtain ⟨t, ht, hl⟩ := ih (step w g)
        exact ⟨_ :: t, by simpa [step, List.append_assoc] using ht, by simp [hl]⟩
    let w := C.wires (List.ofFn (aug x))
    obtain ⟨t, ht, hl⟩ := wireExtension C.gates (List.ofFn (aug x))
    change w = _ at ht
    have len : w.length = k := by simp only [ht,List.length_append,List.length_ofFn,hl,k,sz]
    have raw (i : Fin 27) : w.getD i.val false = aug x i := by
      rw [ht,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa only [List.length_ofFn] using i.isLt)]
      simp only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]
    have prev (v t : List Bool) (i : Nat) (h : i < v.length) :
        (v ++ t).getD i false = v.getD i false := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_append,h]
    have atEnd (v : List Bool) (a : Bool) : (v ++ [a]).getD v.length false = a := by
      simp [List.getD_eq_getElem?_getD]
    change (((C.gates ++ tail).foldl step (List.ofFn (aug x))).getD (k+3) false) = _
    rw [List.foldl_append]
    change (tail.foldl step w).getD (k+3) false = _
    have h3 := raw (3 : Fin 27)
    have h9 := raw (9 : Fin 27)
    have h13 := raw (13 : Fin 27)
    have h26 := raw (26 : Fin 27)
    change w.getD 3 false = x 3 at h3
    change w.getD 9 false = x 9 at h9
    change w.getD 13 false = x 13 at h13
    change w.getD 26 false = (x 0 || x 1) at h26
    have lower : 27 ≤ k := by simp [k]
    change C.output < k at ho
    change _ = (w.getD C.output false || _)
    let a := x 3 || x 9
    let b := (x 0 || x 1) || a
    let c := x 13 && b
    have orValue (v : List Bool) : GateOp.or.eval v = v.any id := rfl
    have andValue (v : List Bool) : GateOp.and.eval v = v.all id := rfl
    have sor (v : List Bool) (i j : ℕ) : step v ⟨.or,[i,j]⟩ =
        v ++ [v.getD i false || v.getD j false] := by
      simp only [step,orValue,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]
    have sand (v : List Bool) (i j : ℕ) : step v ⟨.and,[i,j]⟩ =
        v ++ [v.getD i false && v.getD j false] := by
      simp only [step,andValue,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true]
    have s1 : step w ⟨.or,[3,9]⟩ = w ++ [a] := by rw [sor,h3,h9]
    have s2 : step (w ++ [a]) ⟨.or,[26,k]⟩ = w ++ [a] ++ [b] := by
      rw [sor,prev w [a] 26 (by omega), ← len, atEnd, h26]
    have s3 : step (w ++ [a] ++ [b]) ⟨.and,[13,k+1]⟩ = w ++ [a] ++ [b] ++ [c] := by
      have l : (w ++ [a]).length = k+1 := by simp [len]
      rw [← l]
      rw [sand,atEnd,prev (w++[a]) [b] 13 (by omega),prev w [a] 13 (by omega),h13]
    have s4 : step (w ++ [a] ++ [b] ++ [c]) ⟨.or,[C.output,k+2]⟩ =
        w ++ [a] ++ [b] ++ [c] ++ [w.getD C.output false || c] := by
      have l : (w ++ [a] ++ [b]).length = k+2 := by simp [len]
      have l' : (w ++ [a]).length = k+1 := by simp [len]
      rw [← l]
      rw [sor,atEnd,prev (w++[a]++[b]) [c] C.output (by omega),
        prev (w++[a]) [b] C.output (by omega),prev w [a] C.output (by omega)]
    simp only [tail,List.foldl_cons,List.foldl_nil,s1,s2,s3,s4]
    have l : (w ++ [a] ++ [b] ++ [c]).length = k+3 := by simp [len]
    rw [← l,atEnd]
  refine ⟨1, E, em, eb, es, ?_, ?_⟩
  · intro p w inc
    obtain ⟨d,hd,rfl⟩ := inc
    change circuitFun 27 E (aug _) = true
    apply (run (fun i => decide (i = Fin.castAdd 13 (w+d) ∨ i = Fin.natAdd 13 w))).trans
    by_cases hw : w = 0
    · subst w
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> exact Bool.or_true _
    · have pos := hp (w+d) w hw (by simpa using hd)
      change circuitFun 27 C (aug _) = true at pos
      exact (congrArg (fun z : Bool => z || _) pos).trans (by rfl)
  · intro z hz m hm' t b
    obtain ⟨disjoint, count⟩ := geometry z hz m hm' t b
    change circuitFun 27 E (aug _) = false
    rw [run, hn _ disjoint count]
    have safe (x : Fin 26 → Bool)
        (hd : ∀ p w : Fin 13, p-w ∈ ({0,1,3,9} : Finset (Fin 13)) →
          ¬ (x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)) :
        (false || (x 13 && ((x 0 || x 1) || (x 3 || x 9)))) = false := by
      have a := hd 0 0 (by decide)
      have b := hd 1 0 (by decide)
      have c := hd 3 0 (by decide)
      have d := hd 9 0 (by decide)
      change ¬ (x 0 = true ∧ x 13 = true) at a
      change ¬ (x 1 = true ∧ x 13 = true) at b
      change ¬ (x 3 = true ∧ x 13 = true) at c
      change ¬ (x 9 = true ∧ x 13 = true) at d
      cases e : x 13 <;> simp [e] at a b c d ⊢ ; tauto
    exact safe _ disjoint
