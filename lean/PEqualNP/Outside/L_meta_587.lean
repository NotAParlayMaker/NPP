import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def net : Circuit := { gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩], output := 29 }
private def edges : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (6, 8), (7, 9), (8, 5), (9, 6)]

private def sample (t : Fin 1024) (i : Fin 10) : Bool := t.val.testBit i.val
private def pack (x : Fin 10 → Bool) : Fin 1024 := ⟨(Finset.univ : Finset (Fin 10)).sum (fun i => if x i then 2^i.val else 0) % 1024, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma sample_surj : ∀ x : Fin 10 → Bool, ∃ t, sample t = x := by
  intro x
  refine ⟨pack x,?_⟩
  revert x
  decide +kernel

private def edgeTest (x : Fin 10 → Bool) : Bool := edges.any (fun e => x (Fin.ofNat 10 e.1) && x (Fin.ofNat 10 e.2))

private lemma edge_spec (x : Fin 10 → Bool) : edgeTest x = true ↔ ∃ u v : Fin 10, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true := by
  simp only [edgeTest,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨i,j⟩,h,hi,hj⟩
    have bounds : ∀ e ∈ edges, e.1 < 10 ∧ e.2 < 10 := by decide
    obtain ⟨h1,h2⟩ := bounds _ h
    exact ⟨⟨i,h1⟩,⟨j,h2⟩,h,by simpa [Fin.ofNat,Nat.mod_eq_of_lt h1] using hi,by simpa [Fin.ofNat,Nat.mod_eq_of_lt h2] using hj⟩
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨(u.val,v.val),h,by simpa using hu,by simpa using hv⟩

private def ok (t : Fin 1024) : Bool := net.eval (List.ofFn (sample t)) == edgeTest (sample t)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row0 : ∀ i : Fin 64, ok ⟨0+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row1 : ∀ i : Fin 64, ok ⟨64+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row2 : ∀ i : Fin 64, ok ⟨128+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row3 : ∀ i : Fin 64, ok ⟨192+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row4 : ∀ i : Fin 64, ok ⟨256+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row5 : ∀ i : Fin 64, ok ⟨320+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row6 : ∀ i : Fin 64, ok ⟨384+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row7 : ∀ i : Fin 64, ok ⟨448+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row8 : ∀ i : Fin 64, ok ⟨512+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row9 : ∀ i : Fin 64, ok ⟨576+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row10 : ∀ i : Fin 64, ok ⟨640+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row11 : ∀ i : Fin 64, ok ⟨704+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row12 : ∀ i : Fin 64, ok ⟨768+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row13 : ∀ i : Fin 64, ok ⟨832+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row14 : ∀ i : Fin 64, ok ⟨896+i.val,by omega⟩ = true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private lemma row15 : ∀ i : Fin 64, ok ⟨960+i.val,by omega⟩ = true := by decide +kernel

private lemma correct (x : Fin 10 → Bool) : net.eval (List.ofFn x) = edgeTest x := by
  obtain ⟨t,rfl⟩ := sample_surj x
  suffices h : ok t = true by simpa [ok] using h
  let i : Fin 64 := ⟨t.val % 64,Nat.mod_lt _ (by decide)⟩
  have h : t.val / 64 ≤ 15 := by omega
  interval_cases hh : t.val / 64
  · have e : t = ⟨0+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row0 i
  · have e : t = ⟨64+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row1 i
  · have e : t = ⟨128+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row2 i
  · have e : t = ⟨192+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row3 i
  · have e : t = ⟨256+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row4 i
  · have e : t = ⟨320+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row5 i
  · have e : t = ⟨384+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row6 i
  · have e : t = ⟨448+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row7 i
  · have e : t = ⟨512+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row8 i
  · have e : t = ⟨576+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row9 i
  · have e : t = ⟨640+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row10 i
  · have e : t = ⟨704+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row11 i
  · have e : t = ⟨768+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row12 i
  · have e : t = ⟨832+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row13 i
  · have e : t = ⟨896+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row14 i
  · have e : t = ⟨960+i.val,by omega⟩ := Fin.ext (by dsimp [i]; omega)
    exact e ▸ row15 i

theorem PEqualNP.Outside.L_meta_587 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩], output := 29 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 20 ∧ (∃ A : Finset ℕ, A.card = 14 ∧ ∀ j : ℕ, j ∈ A ↔ ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (6, 8), (7, 9), (8, 5), (9, 6)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro C rfl
  change Monotone2 net ∧ net.size = 20 ∧ _
  refine ⟨?_,rfl,?_,?_⟩
  · intro g hg
    simp [net] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · refine ⟨{0,1,2,3,4,5,6,8,9,14,16,17,18,19},by decide,?_⟩
    intro j
    change _ ↔ ∃ g : Gate, net.gates[j]? = some g ∧ g.op = GateOp.or
    by_cases hj : j < 20
    · interval_cases j <;> simp [net]
    · have hnil : net.gates[j]? = none := List.getElem?_eq_none (by change 20 ≤ j; omega)
      simp only [hnil,reduceCtorEq,false_and,exists_false,iff_false]
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
  · intro x
    change net.eval (List.ofFn x) = true ↔ _
    rw [correct]
    exact edge_spec x
