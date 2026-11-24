import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.EdgeOwnership

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_2247_1
  (normalize :
    ∀ (n : ℕ) (rows : List Bool → Prop) (C : Circuit),
    Monotone2 C → ReadsBack n C → (∀ w, rows w → w.length = n) →
    (∃ w, rows w ∧ C.eval w = true) → (∃ w, rows w ∧ C.eval w = false) →
    (¬ ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧
      (∀ w, rows w → D.eval w = C.eval w) ∧ D.size < C.size) →
    (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧
    (∀ j < C.gates.length, C.output ≠ n + j →
      ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs) ∧
    (∀ j < C.gates.length, ∃ a b, a ≠ b ∧ (gateAt C j).inputs = [a,b]) ∧
    (∀ j < C.gates.length, ∀ t : Bool, ∃ w, rows w ∧
      (C.wires w).getD (n + j) false ≠ t) ∧
    (∀ j < C.gates.length, ∀ a < n + j, ∃ w, rows w ∧
      (C.wires w).getD (n + j) false ≠ (C.wires w).getD a false))
  (count :
    let S := singerLines3
    let examples := fun t w => if t = true then
      ∃ p l : Fin 13, p ∈ S l ∧ w = incidenceInput {p} {l}
      else ∃ Q, IsQuadrangle S Q ∧ w = incidenceInput Q (missLines S Q)
    let rows := fun w => examples true w ∨ examples false w
    let valid := fun C : Circuit => Monotone2 C ∧ ReadsBack 26 C ∧
      ∀ t w, examples t w → C.eval w = t
    ∀ C, valid C →
      let gate := gateAt C
      let bit := fun (w : List Bool) (i : ℕ) => (C.wires w).getD i false
      (∀ j < C.size, ∀ i ∈ (gate j).inputs,
        let t := !(gate j).op.eval []
        ∃ w, examples t w ∧ bit w i = !t ∧ bit w (26 + j) = t) →
      (¬ ∃ D, valid D ∧ D.size < C.size) →
      C.output + 1 = 26 + C.size →
      (∀ j < C.size,
        let i := 26 + j
        i ∈ C.output :: C.gates.flatMap Gate.inputs ∧
        (∃ a b, a ≠ b ∧ (gate j).inputs = [a,b]) ∧
        (∀ t : Bool, ∃ w, rows w ∧ bit w i ≠ t) ∧
        ∀ a < i, ∃ w, rows w ∧ bit w i ≠ bit w a) →
      (∃ i j, (gate i).op = (gate j).op ∧ (gate j).op = .and ∧ InCone 26 C i j) →
      64 ≤ C.size) :
  have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 ∧ x5.size < x4.size; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ x6 < x5.gates.length,     have x8 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6;     have x9 : Bool := !x8.op.eval [];     ∀ x10 ∈ x8.inputs, ∃ (x12 : List Bool), x2 x9 x12 ∧ (x5.wires x12).getD x10 Bool.false = !x9 ∧ (x5.wires x12).getD ((26 : ℕ) + x6) Bool.false = x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x5 x6 → x6.size < (64 : ℕ) → (∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x6 x10 x11) → x4 x6 := by
  intro offsets data fits smaller essential C hfits hessential hsmall hnested
  let S := singerLines3
  let row := fun Q => incidenceInput Q (missLines S Q)
  let examples := fun t w => if t = true then
    ∃ p l : Fin 13, p ∈ S l ∧ w = incidenceInput {p} {l}
    else ∃ Q, IsQuadrangle S Q ∧ w = row Q
  let rows := fun w => examples true w ∨ examples false w
  let valid := fun D : Circuit => Monotone2 D ∧ ReadsBack 26 D ∧
    ∀ t w, examples t w → D.eval w = t
  have geom : ∀ p l : Fin 13, p ∈ S l ↔ p - l ∈ offsets := by
    change ∀ p l : Fin 13, p ∈ singerLines3 l ↔ p - l ∈ ({0,1,3,9} : Finset (Fin 13))
    decide +kernel
  have quad (Q : Finset (Fin 13)) : IsQuadrangle S Q ↔ Q.card = 4 ∧
      ∀ l : Fin 13, (Q.filter fun p => p - l ∈ offsets).card ≤ 2 := by
    have hinter (l : Fin 13) : Q ∩ S l = Q.filter fun p => p - l ∈ offsets := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_filter, geom]
    change (Q.card = 4 ∧ ∀ l : Fin 13, (Q ∩ S l).card ≤ 2) ↔ _
    simp only [hinter]
  have row_eq (Q : Finset (Fin 13)) : row Q =
      (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
        List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ offsets) := by
    change List.ofFn _ ++ List.ofFn _ = List.ofFn _ ++ List.ofFn _
    apply congrArg (List.append (List.ofFn fun p : Fin 13 => decide (p ∈ Q)))
    apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    change (l ∈ (Finset.univ.filter fun w : Fin 13 => Disjoint (S w) Q)) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_right]
    exact forall₂_congr fun p _ => not_congr (geom p l)
  have pos_eq (p l : Fin 13) : incidenceInput {p} {l} =
      (List.ofFn fun q : Fin 13 => decide (q = p)) ++
        List.ofFn fun q : Fin 13 => decide (q = l) := by
    change (List.ofFn fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) ++
      (List.ofFn fun q : Fin 13 => decide (q ∈ ({l} : Finset (Fin 13)))) = _
    simp only [Finset.mem_singleton]
  have match_data (t : Bool) (w : List Bool) : data t w ↔ examples t w := by
    cases t with
    | false =>
      change (∃ Q : Finset (Fin 13), Q.card = 4 ∧
        (∀ l : Fin 13, (Q.filter fun p => p - l ∈ offsets).card ≤ 2) ∧
        w = (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
          List.ofFn fun l : Fin 13 => decide (∀ p ∈ Q, p - l ∉ offsets)) ↔
        (∃ Q, IsQuadrangle S Q ∧ w = row Q)
      simp only [quad, row_eq, and_assoc]
    | true =>
      change (∃ p l : Fin 13, p - l ∈ offsets ∧
        w = (List.ofFn fun q : Fin 13 => decide (q = p)) ++
          List.ofFn fun q : Fin 13 => decide (q = l)) ↔
        (∃ p l : Fin 13, p ∈ S l ∧ w = incidenceInput {p} {l})
      simp only [geom, pos_eq]
  have match_fits (D : Circuit) : fits D ↔ valid D := by
    constructor
    · rintro ⟨hm, hb, hf⟩
      exact ⟨hm, hb, fun t w hw => hf t w ((match_data t w).mpr hw)⟩
    · rintro ⟨hm, hb, hf⟩
      exact ⟨hm, hb, fun t w hw => hf t w ((match_data t w).mp hw)⟩
  have hvalid := (match_fits C).mp hfits
  by_contra hno
  have hmin : ¬ ∃ D, valid D ∧ D.size < C.size := by
    rintro ⟨D, hv, hs⟩
    exact hno ⟨D, (match_fits D).mpr hv, hs⟩
  have hrows_len (w : List Bool) (hw : rows w) : w.length = 26 := by
    rcases hw with hp | hq
    · obtain ⟨p, l, _, rfl⟩ := hp
      change ((List.ofFn fun q : Fin 13 => decide (q ∈ ({p} : Finset (Fin 13)))) ++
        (List.ofFn fun q : Fin 13 => decide (q ∈ ({l} : Finset (Fin 13))))).length = 26
      simp only [List.length_append, List.length_ofFn]
    · obtain ⟨Q, _, rfl⟩ := hq
      change ((List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
        (List.ofFn fun l : Fin 13 => decide (l ∈ missLines S Q))).length = 26
      simp only [List.length_append, List.length_ofFn]
  have htrue : ∃ w, rows w ∧ C.eval w = true := by
    have hi : (0 : Fin 13) ∈ S 0 := by
      change (0 : Fin 13) ∈ singerLines3 0
      decide +kernel
    exact ⟨incidenceInput {(0 : Fin 13)} {(0 : Fin 13)},
      Or.inl ⟨0, 0, hi, rfl⟩, hvalid.2.2 true _ ⟨0, 0, hi, rfl⟩⟩
  have hfalse : ∃ w, rows w ∧ C.eval w = false := by
    let Q : Finset (Fin 13) := {0,1,2,5}
    have hq : IsQuadrangle S Q := by
      change IsQuadrangle singerLines3 ({0,1,2,5} : Finset (Fin 13))
      decide +kernel
    exact ⟨row Q, Or.inr ⟨Q, hq, rfl⟩, hvalid.2.2 false _ ⟨Q, hq, rfl⟩⟩
  have hrow_of_example (t : Bool) (w : List Bool) : examples t w → rows w := by
    cases t
    · exact Or.inr
    · exact Or.inl
  have hrowmin : ¬ ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧
      (∀ w, rows w → D.eval w = C.eval w) ∧ D.size < C.size := by
    rintro ⟨D, hm, hb, hd, hs⟩
    apply hmin
    refine ⟨D, ⟨hm, hb, ?_⟩, hs⟩
    intro t w hw
    exact (hd _ (hrow_of_example t w hw)).trans (hvalid.2.2 t w hw)
  obtain ⟨hlast, hread, htwo, hvaries, hdistinct⟩ :=
    normalize 26 rows C hvalid.1 hvalid.2.1 hrows_len htrue hfalse hrowmin
  have hnonempty : C.gates ≠ [] := by
    obtain ⟨i, j, hi, hj, hc⟩ := hnested
    intro he
    change (C.gates.getD i ⟨.or, []⟩).op = .and at hi
    rw [he] at hi
    change GateOp.or = GateOp.and at hi
    cases hi
  have hessential' : ∀ j < C.size, ∀ i ∈ (gateAt C j).inputs,
      let t := !(gateAt C j).op.eval []
      ∃ w, examples t w ∧ (C.wires w).getD i false = !t ∧
        (C.wires w).getD (26 + j) false = t := by
    intro j hj i hi
    obtain ⟨w, hd, harg, hgate⟩ := hessential j hj i hi
    exact ⟨w, (match_data _ _).mp hd, harg, hgate⟩
  have hnormal : ∀ j < C.size,
      let i := 26 + j
      i ∈ C.output :: C.gates.flatMap Gate.inputs ∧
      (∃ a b, a ≠ b ∧ (gateAt C j).inputs = [a,b]) ∧
      (∀ t : Bool, ∃ w, rows w ∧ (C.wires w).getD i false ≠ t) ∧
      ∀ a < i, ∃ w, rows w ∧ (C.wires w).getD i false ≠ (C.wires w).getD a false := by
    intro j hj
    refine ⟨?_, htwo j hj, hvaries j hj, hdistinct j hj⟩
    by_cases hout : C.output = 26 + j
    · exact List.mem_cons.mpr (Or.inl hout.symm)
    · obtain ⟨k, _, hk, hm⟩ := hread j hj hout
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨gateAt C k, ?_, hm⟩
      change C.gates.getD k ⟨.or, []⟩ ∈ C.gates
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
  have hnested' : ∃ i j, (gateAt C i).op = (gateAt C j).op ∧
      (gateAt C j).op = .and ∧ InCone 26 C i j := by
    obtain ⟨i, j, hi, hj, hcone⟩ := hnested
    exact ⟨i, j, hi.trans hj.symm, hj, hcone⟩
  exact (Nat.not_le_of_lt hsmall)
    (count C hvalid hessential' hmin (hlast hnonempty) hnormal hnested')
