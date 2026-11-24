import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem PEqualNP.Outside.R_meta_2830_317
    (switches : let r (D : Circuit) (m : ℕ) (b : Bool) := D.eval (List.ofFn (fun j : Fin 9 => m.testBit j.val) ++ [b])
      ∀ D : Circuit, Monotone2 D → D.size ≤ 14 →
        (∀ m ∈ ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ), r D m (m.testBit 0 || m.testBit 1)=true) →
        (∀ m ∈ ([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ), r D m (m.testBit 0 || m.testBit 1)=false) →
        (∃ a ∈ ([6,66] : List ℕ), r D a false=false) ∧ (∃ b ∈ ([17,33] : List ℕ), r D b false=false) ∧ (∃ c ∈ ([104,116,208,276] : List ℕ), r D c true=true))
    (compile : ∀ (col : Fin 10 → BitVec 27) (t : BitVec 27) (C : Circuit), Monotone2 C → t ≠ 0 → t ≠ -1 →
      (∀ i : Fin 27, C.eval (List.ofFn fun u => (col u).getLsbD i.val) = t.getLsbD i.val) →
      let p := List.ofFn col
      ∃ fs : List (BitVec 27), fs.length ≤ C.size ∧ t ∈ p ++ fs ∧
        ∀ j : Fin fs.length, let old := p ++ fs.take j.val
          fs.get j ∉ old ∧ fs.get j ≠ 0 ∧ fs.get j ≠ -1 ∧ ∃ a ∈ old, ∃ b ∈ old, fs.get j = a &&& b ∨ fs.get j = a ||| b)
    (finite : ∀ a ∈ ([6,66] : List ℕ), ∀ b ∈ ([17,33] : List ℕ), ∀ c ∈ ([104,116,208,276] : List ℕ),
      let masks : List ℕ := [554,562,581,104,116,650,713,208,773,276,897,914,515,518,12,529,24,545,578,132,160,264,288,320,a,b,c+512]
      let col (j : Fin 10) : BitVec 27 := BitVec.ofBoolListLE (masks.map fun m => m.testBit j.val)
      let p := List.ofFn col
      ∀ fs : List (BitVec 27), BitVec.ofNat 27 83881984 ∈ p ++ fs →
        (∀ j : Fin fs.length, let old := p ++ fs.take j.val
          fs.get j ∉ old ∧ fs.get j ≠ 0 ∧ fs.get j ≠ -1 ∧ ∃ u ∈ old, ∃ v ∈ old, fs.get j = u &&& v ∨ fs.get j = u ||| v) → 15 ≤ fs.length) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)], x1.eval ((List.ofFn fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5) ++ [x3.testBit (0 : ℕ) || x3.testBit (1 : ℕ)]) = Bool.true) → (∀ x4 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x6 : Fin (9 : ℕ)) => x4.testBit ↑x6) ++ [x4.testBit (0 : ℕ) || x4.testBit (1 : ℕ)]) = Bool.false) → (15 : ℕ) ≤ x1.size := by
  intro D hm hp hn
  by_contra! small
  have hs : D.size ≤ 14 := by omega
  obtain ⟨⟨a,ha,da⟩,⟨b,hb,db⟩,⟨c,hc,dc⟩⟩ := switches D hm hs hp hn
  let masks : List ℕ := [554,562,581,104,116,650,713,208,773,276,897,914,515,518,12,529,24,545,578,132,160,264,288,320,a,b,c+512]
  let col (j : Fin 10) : BitVec 27 := BitVec.ofBoolListLE (masks.map fun m => m.testBit j.val)
  let t := BitVec.ofNat 27 83881984
  have packed (i : Fin 27) : (List.ofFn fun j => (col j).getLsbD i.val) =
      List.ofFn (fun j : Fin 10 => (masks.getD i.val 0).testBit j.val) := by
    congr 1
    funext j
    change (BitVec.ofBoolListLE (masks.map fun m => m.testBit j.val)).getLsbD i.val = _
    rw [BitVec.getLsbD_ofBoolListLE]
    have hj : i.val < masks.length := i.isLt
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj, List.getElem_map]
  let raw (m : ℕ) (h : Bool) := List.ofFn (fun j : Fin 9 => m.testBit j.val) ++ [h]
  let nominal (m : ℕ) := raw m (m.testBit 0 || m.testBit 1)
  let samples (a b c : ℕ) : List (List Bool × Bool) :=
    (([42,50,69,104,116,138,201,208,261,276,385,402] : List ℕ).map fun m => (nominal m,false)) ++
    ((([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ).map fun m => (nominal m,true)) ++
      [(raw a false,false),(raw b false,false),(raw c true,true)])
  have correct (p : List Bool × Bool) (hp' : p ∈ samples a b c) : D.eval p.1 = p.2 := by
    rcases List.mem_append.mp hp' with h | h
    · obtain ⟨m,hm,rfl⟩ := List.mem_map.mp h
      exact hn m hm
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨m,hm,rfl⟩ := List.mem_map.mp h
        exact hp m hm
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl | rfl | rfl
        · exact da
        · exact db
        · exact dc
  have table : ∀ i : Fin 27, (List.ofFn (fun j : Fin 10 => (masks.getD i.val 0).testBit j.val), t.getLsbD i.val) ∈ samples a b c := by
    dsimp only [masks,t,samples,nominal,raw]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb hc
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> rcases hc with rfl|rfl|rfl|rfl <;> decide +kernel
  have semantic (i : Fin 27) : D.eval (List.ofFn fun j => (col j).getLsbD i.val) = t.getLsbD i.val := by
    rw [packed]
    exact correct _ (table i)
  obtain ⟨fs,len,out,legal⟩ := compile col t D hm (by decide) (by decide) semantic
  have floor := finite a ha b hb c hc fs out legal
  omega
