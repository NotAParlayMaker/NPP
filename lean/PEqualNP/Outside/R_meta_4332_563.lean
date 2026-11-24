import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Pin input 9 to false by redirecting its reads to a wire beyond the circuit.
-- L-meta-2012 and L-meta-3438 supply the two bounds for the nine-input function.
theorem PEqualNP.Outside.R_meta_4332_563
    (floor : ¬ HasCircuitSize 9 (fun x =>
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
        x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) 14)
    (binary : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 9 → Bool, D.eval (List.ofFn x) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
      13 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op))
    (remaining : ∀ (D : Circuit) (phase : Bool), FanInTwo D → D.size ≤ 15 →
        15 ≤ D.size + cond phase 1 0 →
        13 ≤ D.gates.countP (fun g => GateOp.rec true true false (fun _ => true) true g.op) →
        ∃ x : Fin 9 → Bool,
          (if phase = true then !(D.eval (List.ofFn x)) else D.eval (List.ofFn x)) ≠
            ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
              x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) :
    (have target : (Fin 10 → Bool) → Bool := fun x =>
      x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
      x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
      x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 ||
      x 9 && x 6 || x 6 && x 8 || x 8 && x 5
     ∀ (C : Circuit) (out : ℕ) (phase : Bool), FanInTwo C → C.size ≤ 15 →
       have value : (Fin 10 → Bool) → Bool :=
         fun x => (C.wires (List.ofFn x)).getD out false
       ∃ x : Fin 10 → Bool,
         x 9 = false ∧ (if phase = true then !(value x) else value x) ≠ target x) := by
  intro F10 C out phase fan small v
  have pin :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
      ∀ x : Fin 9 → Bool,
        D.eval (List.ofFn x) = (C.wires (List.ofFn x ++ [false])).getD out false := by
    let stop := 9 + C.size
    let shift (i : ℕ) := if i < 9 then i else if i = 9 then stop else i - 1
    let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map shift⟩
    let value (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
    let run (s : List Gate) (w : List Bool) := s.foldl (fun a g => a ++ [value a g]) w
    have read (p q : List Bool) (i : ℕ) (hp : p.length = 9) (hq : 9 + q.length ≤ stop) :
        (p ++ q).getD (shift i) false = (p ++ false :: q).getD i false := by
      by_cases hlt : i < 9
      · simp only [shift, ite_eq_left hlt]
        have hi : i < p.length := by omega
        rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]
      by_cases heq : i = 9
      · subst i
        simp only [shift, lt_self_iff_false, ite_false, ite_true]
        rw [List.getD_eq_default _ _ (by simpa only [List.length_append, hp] using hq),
          List.getD_append_right _ _ _ _ (by omega)]
        simp [hp]
      · simp only [shift, ite_eq_right hlt, ite_eq_right heq]
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        have hdiff : i - p.length = (i - 1 - p.length) + 1 := by omega
        rw [hdiff, List.getD_cons_succ]
    have compare (p : List Bool) (hp : p.length = 9) (s : List Gate) (q : List Bool)
        (bound : 9 + q.length + s.length ≤ stop) :
        ∃ Q, run (s.map rename) (p ++ q) = p ++ Q ∧
          run s (p ++ false :: q) = p ++ false :: Q ∧ Q.length = q.length + s.length := by
      induction s generalizing q with
      | nil => exact ⟨q, rfl, rfl, by simp⟩
      | cons g s ih =>
        have same : value (p ++ q) (rename g) = value (p ++ false :: q) g := by
          simp only [value, rename, List.map_map]
          congr 1
          exact List.map_congr_left (fun i _ => read p q i hp (by omega))
        let q' := q ++ [value (p ++ false :: q) g]
        have len : q'.length = q.length + 1 := by simp [q']
        obtain ⟨Q, hQ, hQ', hLen⟩ := ih q' (by
          rw [len]
          simp only [List.length_cons] at bound
          omega)
        refine ⟨Q, ?_, ?_, ?_⟩
        · simpa only [run, List.map_cons, List.foldl_cons, same, q', List.append_assoc] using hQ
        · simpa only [run, List.foldl_cons, q', List.append_assoc, List.cons_append] using hQ'
        · simp only [List.length_cons]
          omega
    let D : Circuit := ⟨C.gates.map rename, shift out⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ C.gates.map rename at hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      simpa only [rename, List.length_map] using fan g' hg'
    · change (C.gates.map rename).length = C.gates.length
      simp only [List.length_map]
    · intro x
      let p := List.ofFn x
      have hp : p.length = 9 := by simp [p]
      obtain ⟨Q, hQ, hQ', hLen⟩ := compare p hp C.gates [] (by
        change 9 + ([] : List Bool).length + C.gates.length ≤ 9 + C.gates.length
        simp)
      rw [List.append_nil] at hQ
      change (run (C.gates.map rename) p).getD (shift out) false =
        (run C.gates (p ++ [false])).getD out false
      rw [hQ, hQ']
      exact read p Q out hp (by
        change 9 + Q.length ≤ 9 + C.gates.length
        simp [hLen])
  let F9 := fun x : Fin 9 → Bool =>
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any fun e =>
      x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  have edgeForm (x : Fin 9 → Bool) : F9 x =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
        x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
        x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
    simp only [F9, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  let lift (x : Fin 9 → Bool) : Fin 10 → Bool := Fin.snoc x false
  have slice (x : Fin 9 → Bool) : F10 (lift x) = F9 x := by
    rw [edgeForm]
    dsimp only [F10]
    have read (i : Fin 9) : lift x i.castSucc = x i := by simp [lift]
    have last : lift x (9 : Fin 10) = false := rfl
    change (lift x (0 : Fin 9).castSucc && lift x (1 : Fin 9).castSucc ||
      lift x (1 : Fin 9).castSucc && lift x (2 : Fin 9).castSucc ||
      lift x (2 : Fin 9).castSucc && lift x (3 : Fin 9).castSucc ||
      lift x (3 : Fin 9).castSucc && lift x (4 : Fin 9).castSucc ||
      lift x (4 : Fin 9).castSucc && lift x (0 : Fin 9).castSucc ||
      lift x (0 : Fin 9).castSucc && lift x (5 : Fin 9).castSucc ||
      lift x (1 : Fin 9).castSucc && lift x (6 : Fin 9).castSucc ||
      lift x (2 : Fin 9).castSucc && lift x (7 : Fin 9).castSucc ||
      lift x (3 : Fin 9).castSucc && lift x (8 : Fin 9).castSucc ||
      lift x (4 : Fin 9).castSucc && lift x (9 : Fin 10) ||
      lift x (5 : Fin 9).castSucc && lift x (7 : Fin 9).castSucc ||
      lift x (7 : Fin 9).castSucc && lift x (9 : Fin 10) ||
      lift x (9 : Fin 10) && lift x (6 : Fin 9).castSucc ||
      lift x (6 : Fin 9).castSucc && lift x (8 : Fin 9).castSucc ||
      lift x (8 : Fin 9).castSucc && lift x (5 : Fin 9).castSucc) = _
    simp only [read, last, Bool.and_false, Bool.false_and, Bool.or_false]
  let counted : Gate → Bool := fun g => GateOp.rec true true false (fun _ => true) true g.op
  have complement (D : Circuit) (hD : FanInTwo D) :
      ∃ E : Circuit, FanInTwo E ∧ E.size = D.size + 1 ∧
        E.gates.countP counted = D.gates.countP counted ∧
        ∀ x : Fin 9 → Bool, E.eval (List.ofFn x) = !(D.eval (List.ofFn x)) := by
    let gate : Gate := ⟨.not, [D.output]⟩
    let E : Circuit := ⟨D.gates ++ [gate], 9 + D.size⟩
    refine ⟨E, ?_, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ D.gates ++ [gate] at hg
      rcases List.mem_append.mp hg with hd | hn
      · exact hD g hd
      · have eq : g = gate := List.mem_singleton.mp hn
        subst g
        simp [gate]
    · change (D.gates ++ [gate]).length = D.gates.length + 1
      simp
    · change (D.gates ++ [gate]).countP counted = _
      have hz : [gate].countP counted = 0 := rfl
      rw [List.countP_append, hz, Nat.add_zero]
    · intro x
      let step := fun (w : List Bool) (g : Gate) =>
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      have len (gs : List Gate) (w : List Bool) :
          (gs.foldl step w).length = w.length + gs.length := by
        induction gs generalizing w with
        | nil => simp
        | cons g gs ih =>
          simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
          omega
      have lengthW : (D.wires (List.ofFn x)).length = 9 + D.size := by
        change (D.gates.foldl step (List.ofFn x)).length = 9 + D.gates.length
        simp only [len, List.length_ofFn]
      change ((D.gates ++ [gate]).foldl step (List.ofFn x)).getD (9 + D.size) false = _
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change ((D.wires (List.ofFn x)) ++ [!(D.eval (List.ofFn x))]).getD
        (9 + D.size) false = _
      rw [← lengthW, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      rfl
  obtain ⟨D, fanD, sizeD, pinD⟩ := pin
  have smallD : D.size ≤ 15 := sizeD ▸ small
  by_contra failed
  have correct (x : Fin 9 → Bool) :
      (if phase = true then !(D.eval (List.ofFn x)) else D.eval (List.ofFn x)) = F9 x := by
    have last : lift x (9 : Fin 10) = false := rfl
    have ofFn : List.ofFn (lift x) = List.ofFn x ++ [false] := by
      change List.ofFn ((Fin.snoc x false) : Fin 10 → Bool) = _
      rw [List.ofFn_succ']
      simp <;> rfl
    by_contra wrong
    apply failed
    refine ⟨lift x, last, ?_⟩
    change (if phase = true then !((C.wires (List.ofFn (lift x))).getD out false)
      else (C.wires (List.ofFn (lift x))).getD out false) ≠ F10 (lift x)
    rwa [ofFn, ← pinD, slice]
  have positive : ∃ E : Circuit, FanInTwo E ∧ E.size = D.size + cond phase 1 0 ∧
      E.gates.countP counted = D.gates.countP counted ∧
      ∀ x : Fin 9 → Bool, E.eval (List.ofFn x) = F9 x := by
    cases phase
    · exact ⟨D, fanD, by simp, rfl, fun x => by simpa using correct x⟩
    · obtain ⟨E, efan, esize, ecount, eeval⟩ := complement D fanD
      exact ⟨E, efan, esize, ecount, fun x => (eeval x).trans (by simpa using correct x)⟩
  obtain ⟨E, efan, esize, ecount, eeval⟩ := positive
  have needed : 15 ≤ D.size + cond phase 1 0 := by
    by_contra h
    have esmall : E.size ≤ 14 := by omega
    exact floor ⟨E, efan, esmall, eeval⟩
  have many : 13 ≤ D.gates.countP counted := by
    rw [← ecount]
    exact binary E efan (fun x => (eeval x).trans (edgeForm x))
  obtain ⟨x, bad⟩ := remaining D phase fanD smallD needed many
  exact bad (correct x)
