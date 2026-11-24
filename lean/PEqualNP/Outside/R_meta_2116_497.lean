import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2116_497
    (rename : ∀ (n : ℕ) (C : Circuit) (σ : Equiv.Perm (Fin n)),
      ∃ D : Circuit, D.size = C.size ∧
        (IsMinimalCircuit n C → IsMinimalCircuit n D) ∧
        (∀ x : Fin n → Bool, circuitFun n D x = circuitFun n C (fun i => x (σ i))) ∧
        ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          D.gates[j]? = some
            ⟨g.op, g.inputs.map (fun k => if h : k < n then (σ ⟨k,h⟩).val else k)⟩)
    (ordered : ∀ (C : Circuit) (r4 r6 r7 : ℕ), IsMinimalCircuit 9 C → C.size ≤ 15 →
      circuitFun 9 C = (fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (∀ w ∈ g.inputs, w < 9 + j) ∧ g.inputs.Nodup ∧
        (g.op = .not ∧ g.inputs.length = 1 ∨ g.op ≠ .not ∧ g.inputs.length = 2)) →
      r4 ≤ r6 → r6 ≤ r7 → r7 < C.size →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (4 ∈ g.inputs ↔ j = r4) ∧ (6 ∈ g.inputs ↔ j = r6) ∧ (7 ∈ g.inputs ↔ j = r7) ∧
        ((4 ∈ g.inputs ∨ 6 ∈ g.inputs ∨ 7 ∈ g.inputs) → g.op = .or)) →
      False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  classical
  dsimp only
  intro C hg unique
  obtain ⟨hMin, hSize, hF, shape, _⟩ := hg
  let F (x : Fin 9 → Bool) :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
    x 6 && x 8 || x 8 && x 5
  let reads (u : Fin 9) : Finset (Fin C.size) :=
    Finset.univ.filter fun j => u.val ∈ (C.gates.get j).inputs
  have one (u : Fin 9) (hu : u ∈ ([4, 6, 7] : List (Fin 9))) :
      ∃ j : Fin C.size, (C.gates.get j).op = .or ∧
        ∀ k : Fin C.size, u.val ∈ (C.gates.get k).inputs ↔ k = j := by
    have hc : (reads u).card = 1 := (unique u hu).1
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
    have hm : j ∈ reads u := by rw [hj]; simp
    refine ⟨j, (unique u hu).2 j hm, fun k => ?_⟩
    have hmem : k ∈ reads u ↔ u.val ∈ (C.gates.get k).inputs := by simp [reads]
    rw [← hmem, hj, Finset.mem_singleton]
  obtain ⟨j4, rule4⟩ := one 4 (by decide)
  obtain ⟨j6, rule6⟩ := one 6 (by decide)
  obtain ⟨j7, rule7⟩ := one 7 (by decide)
  let reader (u : Fin 9) := if u = 4 then j4 else if u = 6 then j6 else j7
  let spec : Fin 3 → Fin 9 := ![4, 6, 7]
  let pre : Fin 6 → Fin 3 → Fin 9 :=
    ![![4,6,7], ![7,4,6], ![6,7,4], ![4,7,6], ![6,4,7], ![7,6,4]]
  let tab : Fin 6 → Fin 9 → Fin 9 :=
    ![![0,1,2,3,4,5,6,7,8], ![1,2,3,8,6,0,7,4,5],
      ![2,3,8,5,7,1,4,6,0], ![0,5,8,3,4,1,7,6,2],
      ![1,0,5,8,6,2,4,7,3], ![2,1,0,5,7,3,6,4,8]]
  have bij (i : Fin 6) : Function.Bijective (tab i) := by
    unfold Function.Bijective Function.Injective Function.Surjective
    fin_cases i <;> decide
  have aut (i : Fin 6) : ∀ x : Fin 9 → Bool, F (fun t => x (tab i t)) = F x := by
    fin_cases i <;> decide +kernel
  have preMap (i : Fin 6) (v : Fin 3) : tab i (pre i v) = spec v := by
    fin_cases i <;> fin_cases v <;> decide
  have preReader (i : Fin 6) (v : Fin 3) :
      (C.gates.get (reader (pre i v))).op = .or ∧
      ∀ k : Fin C.size, (pre i v).val ∈ (C.gates.get k).inputs ↔
        k = reader (pre i v) := by
    fin_cases i <;> fin_cases v <;> first | exact rule4 | exact rule6 | exact rule7
  have order : ∃ i : Fin 6, reader (pre i 0) ≤ reader (pre i 1) ∧
      reader (pre i 1) ≤ reader (pre i 2) := by
    by_cases h46 : j4 ≤ j6
    · by_cases h67 : j6 ≤ j7
      · exact ⟨0, by change j4 ≤ j6 ∧ j6 ≤ j7; omega⟩
      · by_cases h47 : j4 ≤ j7
        · exact ⟨3, by change j4 ≤ j7 ∧ j7 ≤ j6; omega⟩
        · exact ⟨1, by change j7 ≤ j4 ∧ j4 ≤ j6; omega⟩
    · by_cases h47 : j4 ≤ j7
      · exact ⟨4, by change j6 ≤ j4 ∧ j4 ≤ j7; omega⟩
      · by_cases h67 : j6 ≤ j7
        · exact ⟨2, by change j6 ≤ j7 ∧ j7 ≤ j4; omega⟩
        · exact ⟨5, by change j7 ≤ j6 ∧ j6 ≤ j4; omega⟩
  obtain ⟨i, il, ir⟩ := order
  let σ := Equiv.ofBijective (tab i) (bij i)
  obtain ⟨D, hs, hMin', run, gate⟩ := rename 9 C σ
  let up (j : Fin C.size) : Fin D.size := ⟨j.val, hs.symm ▸ j.isLt⟩
  let key (k : ℕ) := if h : k < 9 then (σ ⟨k,h⟩).val else k
  have gateEq (j : Fin C.size) :
      D.gates.get (up j) = ⟨(C.gates.get j).op, (C.gates.get j).inputs.map key⟩ := by
    have hj : C.gates[j.val]? = some (C.gates.get j) := by
      rw [List.getElem?_eq_getElem j.isLt] <;> rfl
    have hd := gate j.val (C.gates.get j) hj
    rw [List.getElem?_eq_getElem (up j).isLt] at hd
    exact Option.some.inj hd
  have keyIn (u : Fin 9) : key u.val = (σ u).val := by simp [key, u.isLt]
  have inj : Function.Injective key := by
    intro a b hab
    by_cases ha : a < 9 <;> by_cases hb : b < 9
    · have ht : (σ ⟨a,ha⟩).val = (σ ⟨b,hb⟩).val := by simpa [key, ha, hb] using hab
      exact congrArg Fin.val (σ.injective (Fin.val_injective ht))
    · have ht : (σ ⟨a,ha⟩).val = b := by simpa [key, ha, hb] using hab
      have hp := (σ ⟨a,ha⟩).isLt
      omega
    · have ht : a = (σ ⟨b,hb⟩).val := by simpa [key, ha, hb] using hab
      have hp := (σ ⟨b,hb⟩).isLt
      omega
    · simpa [key, ha, hb] using hab
  have onto (k : Fin D.size) : ∃ j, up j = k :=
    ⟨⟨k.val, hs ▸ k.isLt⟩, Fin.val_injective rfl⟩
  have shape' (k : Fin D.size) :
      let g := D.gates.get k
      (∀ w ∈ g.inputs, w < 9 + k.val) ∧ g.inputs.Nodup ∧
      (g.op = .not ∧ g.inputs.length = 1 ∨ g.op ≠ .not ∧ g.inputs.length = 2) := by
    obtain ⟨j, rfl⟩ := onto k
    obtain ⟨back, nd, lens⟩ := shape j
    dsimp only
    rw [gateEq]
    refine ⟨?_, nd.map inj, by simpa using lens⟩
    intro w hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    by_cases h : v < 9
    · have hp := (σ ⟨v,h⟩).isLt
      rw [show key v = (σ ⟨v,h⟩).val by simp [key, h]]
      omega
    · rw [show key v = v by simp [key, h]]
      exact back v hv
  let r (v : Fin 3) := up (reader (pre i v))
  have exactReaders (v : Fin 3) :
      (D.gates.get (r v)).op = .or ∧ ∀ k : Fin D.size,
        (spec v).val ∈ (D.gates.get k).inputs ↔ k = r v := by
    obtain ⟨op, all⟩ := preReader i v
    constructor
    · change (D.gates.get (up (reader (pre i v)))).op = _
      rw [gateEq]
      exact op
    · intro k
      obtain ⟨j, rfl⟩ := onto k
      have hp : key (pre i v).val = (spec v).val := by
        rw [keyIn]
        exact congrArg Fin.val (preMap i v)
      rw [gateEq, ← hp]
      change key (pre i v).val ∈ (C.gates.get j).inputs.map key ↔ up j = _
      rw [List.mem_map]
      constructor
      · rintro ⟨w, hw, he⟩
        rw [inj he] at hw
        exact congrArg up ((all j).mp hw)
      · intro he
        have hval : (up j).val = (r v).val := congrArg (fun k : Fin D.size => k.val) he
        have heq : j = reader (pre i v) := Fin.val_injective hval
        exact ⟨(pre i v).val, (all j).mpr heq, rfl⟩
  have fD : circuitFun 9 D = F := by
    funext x
    rw [run, hF]
    exact aut i x
  have getOf (j : ℕ) (g : Gate) (hg : D.gates[j]? = some g) :
      ∃ k : Fin D.size, k.val = j ∧ D.gates.get k = g := by
    by_cases h : j < D.size
    · rw [List.getElem?_eq_getElem h] at hg
      exact ⟨⟨j,h⟩, rfl, Option.some.inj hg⟩
    · rw [List.getElem?_eq_none (by exact Nat.le_of_not_lt h)] at hg
      cases hg
  have rule (v : Fin 3) (k : Fin D.size) :
      (spec v).val ∈ (D.gates.get k).inputs ↔ k.val = (r v).val :=
    Iff.trans ((exactReaders v).2 k)
      ⟨fun h => congrArg Fin.val h, fun h => Fin.val_injective h⟩
  refine ordered D (r 0).val (r 1).val (r 2).val (hMin' hMin) (hs.symm ▸ hSize)
    fD ?_ il ir (r 2).isLt ?_
  · intro j g hg
    obtain ⟨k, rfl, rfl⟩ := getOf j g hg
    exact shape' k
  · intro j g hg
    obtain ⟨k, rfl, rfl⟩ := getOf j g hg
    refine ⟨rule 0 k, rule 1 k, rule 2 k, ?_⟩
    rintro (h | h | h)
    · rw [Fin.val_injective ((rule 0 k).mp h)]
      exact (exactReaders 0).1
    · rw [Fin.val_injective ((rule 1 k).mp h)]
      exact (exactReaders 1).1
    · rw [Fin.val_injective ((rule 2 k).mp h)]
      exact (exactReaders 2).1
