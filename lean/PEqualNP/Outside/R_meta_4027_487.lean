import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 15000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4027_487
    (witness :
      let tab : List ℕ := [17264083201, 5726601218, 8593281040, 17466196004, 17432510976, 17230398528, 17196589056, 17180870656, 17185472520, 18038849664, 20043137039, 20615790832, 21222133504, 21458120704, 17701995044, 21474779684, 22940156994, 25769747522, 17467131940, 18043338888, 21474804360, 17235936328, 17280475393, 21474779521, 22907144194, 25769756802, 25857298705]
      ∃ (D : Circuit) (u : ℕ), IsAO2 27 D ∧ D.size ≤ 19 ∧
        27 ≤ D.output ∧ D.output < 27 + D.size ∧ 27 ≤ u ∧ u < 27 + D.size ∧
        (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        ∀ k : Fin 35, let row := List.ofFn (fun i : Fin 27 => (tab.getD i.val 0).testBit k.val)
          D.eval row = decide (k.val < 16 ∨ k.val = 34) ∧
            (32 ≤ k.val → (D.wires row).getD u false = decide (k.val < 34)))
    (certifyMain :
      let tab : List ℕ := [17264083201, 5726601218, 8593281040, 17466196004, 17432510976, 17230398528, 17196589056, 17180870656, 17185472520, 18038849664, 20043137039, 20615790832, 21222133504, 21458120704, 17701995044, 21474779684, 22940156994, 25769747522, 17467131940, 18043338888, 21474804360, 17235936328, 17280475393, 21474779521, 22907144194, 25769756802, 25857298705]
      let masks : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 512, 2048, 8192, 32768, 131072, 524288, 24, 4184, 34, 354, 136, 2560, 2832, 544, 65, 3137, 130, 6274, 5]
      let input := fun (x : Fin 26 → Bool) (i : Fin 27) => (List.range 26).any fun j =>
        (masks.getD i.val 0).testBit j && x (Fin.ofNat 26 j)
      ∀ D : Circuit, Monotone2 D →
        (∀ k : Fin 35, D.eval (List.ofFn fun i : Fin 27 => (tab.getD i.val 0).testBit k.val) =
          decide (k.val < 16 ∨ k.val = 34)) →
        ∀ x : Fin 26 → Bool, D.eval (List.ofFn (input x)) =
          ([(0,523),(2,2092),(4,177),(6,708)] : List (ℕ × ℕ)).any (fun r =>
            x (Fin.ofNat 26 (13 + r.1)) && (List.range 13).any fun j => r.2.testBit j && x (Fin.ofNat 26 j)))
    (certifyAux :
      let tab : List ℕ := [17264083201, 5726601218, 8593281040, 17466196004, 17432510976, 17230398528, 17196589056, 17180870656, 17185472520, 18038849664, 20043137039, 20615790832, 21222133504, 21458120704, 17701995044, 21474779684, 22940156994, 25769747522, 17467131940, 18043338888, 21474804360, 17235936328, 17280475393, 21474779521, 22907144194, 25769756802, 25857298705]
      let masks : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 512, 2048, 8192, 32768, 131072, 524288, 24, 4184, 34, 354, 136, 2560, 2832, 544, 65, 3137, 130, 6274, 5]
      let input := fun (x : Fin 26 → Bool) (i : Fin 27) => (List.range 26).any fun j =>
        (masks.getD i.val 0).testBit j && x (Fin.ofNat 26 j)
      ∀ (D : Circuit) (u : ℕ), Monotone2 D →
        (∀ k : Fin 35, 32 ≤ k.val →
          (D.wires (List.ofFn fun i : Fin 27 => (tab.getD i.val 0).testBit k.val)).getD u false = decide (k.val < 34)) →
        ∀ x : Fin 26 → Bool, (D.wires (List.ofFn (input x))).getD u false = (x 1 || x 2))
    (assemble :
      let masks : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 512, 2048, 8192, 32768, 131072, 524288, 24, 4184, 34, 354, 136, 2560, 2832, 544, 65, 3137, 130, 6274, 5]
      let input := fun (x : Fin 26 → Bool) (i : Fin 27) => (List.range 26).any fun j =>
        (masks.getD i.val 0).testBit j && x (Fin.ofNat 26 j)
      let good := fun (n : ℕ) (C : Circuit) (v : ℕ) => IsAO2 n C ∧
        n ≤ C.output ∧ C.output < n + C.size ∧ n ≤ v ∧ v < n + C.size ∧ ∀ g ∈ C.gates, g.inputs.Nodup
      ∀ (D : Circuit) (u : ℕ), good 27 D u → ∃ (C : Circuit) (v : ℕ),
        good 26 C v ∧ C.size ≤ D.size + 40 ∧
        ∀ x : Fin 26 → Bool, let row := List.ofFn (input x)
          C.eval (List.ofFn x) = (([(3,4184),(5,354),(7,1416),(8,2832),(9,5664),(10,3137),(11,6274),(12,4357)] : List (ℕ × ℕ)).any
            (fun r => x (Fin.ofNat 26 (13 + r.1)) && (List.range 13).any fun j => r.2.testBit j && x (Fin.ofNat 26 j)) || D.eval row) ∧
          (C.wires (List.ofFn x)).getD v false = (D.wires row).getD u false) :
  ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), x1.size ≤ (59 : ℕ) ∧ (26 : ℕ) ≤ x1.output ∧ x1.output < (26 : ℕ) + x1.size ∧ (26 : ℕ) ≤ x2 ∧ x2 < (26 : ℕ) + x1.size ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) ∧ (∀ (x3 : Fin (26 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (1 : Fin (26 : ℕ)) || x3 (2 : Fin (26 : ℕ)))) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x5 ≠ (1 : Fin (13 : ℕ)) ∧ (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true := by
  obtain ⟨D, u, ao, small, dlo, dhi, ulo, uhi, distinct, rows⟩ := witness
  have mono : Monotone2 D := fun g hg => ⟨ao.1 g hg, le_of_eq (ao.2.2 g hg)⟩
  obtain ⟨C, v, ⟨cAO, clo, chi, vlo, vhi, different⟩, cost, joined⟩ :=
    assemble D u ⟨ao, dlo, dhi, ulo, uhi, distinct⟩
  refine ⟨C, v, by omega, clo, chi, vlo, vhi, ?_, ?_, ?_⟩
  · intro j g hg
    have mem := List.mem_iff_getElem?.mpr ⟨j,hg⟩
    obtain ⟨a,b,inputs⟩ := List.length_eq_two.mp (cAO.2.2 g mem)
    have hlen := (List.getElem?_eq_some_iff.mp hg).1
    have atGate : gateAt C j = g := by
      change C.gates.getD j ⟨.or,[]⟩ = g
      simp only [List.getD_eq_getElem?_getD,hg,Option.getD_some]
    have back := cAO.2.1 j hlen
    rw [atGate,inputs] at back
    exact ⟨cAO.1 g mem, a, b, inputs, by simpa [inputs] using different g mem,
      back a (by simp), back b (by simp)⟩
  · intro x
    exact (joined x).2.trans (certifyAux D u mono (fun k => (rows k).2) x)
  · intro x
    rw [(joined x).1, certifyMain D mono (fun k => (rows k).1) x, ← List.any_append]
    let data : List (ℕ × ℕ) := [(3,4184),(5,354),(7,1416),(8,2832),(9,5664),(10,3137),(11,6274),(12,4357),
      (0,523),(2,2092),(4,177),(6,708)]
    let edge (p l : Fin 13) := l ≠ 1 ∧ (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)
    have geometry : ∀ p l : Fin 13, edge p l ↔
        ∃ r ∈ data, r.1 = l.val ∧ r.2.testBit p.val = true := by decide
    have lineIdx : ∀ r ∈ data, r.1 < 13 := by decide
    have pointPlace (p : Fin 13) : Fin.ofNat 26 p.val = Fin.castAdd 13 p := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by have h := p.isLt; omega)
    have linePlace (l : Fin 13) : Fin.ofNat 26 (13 + l.val) = Fin.natAdd 13 l := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (by have h := l.isLt; omega)
    suffices result : data.any (fun r => x (Fin.ofNat 26 (13 + r.1)) &&
      (List.range 13).any fun j => r.2.testBit j && x (Fin.ofNat 26 j)) = true ↔
      ∃ p l, edge p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true by
      simpa only [data,edge,and_assoc,List.cons_append,List.nil_append] using result
    constructor
    · intro path
      obtain ⟨r, hr, gate⟩ := List.any_eq_true.mp path
      simp only [Bool.and_eq_true] at gate
      obtain ⟨k, hk, on⟩ := List.any_eq_true.mp gate.2
      simp only [Bool.and_eq_true] at on
      let p : Fin 13 := ⟨k,List.mem_range.mp hk⟩
      let l : Fin 13 := ⟨r.1,lineIdx r hr⟩
      refine ⟨p, l, (geometry p l).mpr ⟨r,hr,rfl,on.1⟩, ?_, ?_⟩
      · rw [← pointPlace]
        exact on.2
      · rw [← linePlace]
        exact gate.1
    · rintro ⟨p,l,edgeYes,pOn,lOn⟩
      obtain ⟨r,hr,index,hit⟩ := (geometry p l).mp edgeYes
      apply List.any_eq_true.mpr
      refine ⟨r,hr,?_⟩
      simp only [Bool.and_eq_true]
      refine ⟨by rwa [index,linePlace], List.any_eq_true.mpr ⟨p.val,List.mem_range.mpr p.isLt,?_⟩⟩
      simp only [Bool.and_eq_true,pointPlace]
      exact ⟨hit,pOn⟩
