import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.GenericRejection PEqualNP.TopForm

set_option maxHeartbeats 2200000 in
theorem PEqualNP.Outside.R_meta_3471_582
  (andCase :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x4.gates[x4.output - (x2 + x2)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size)
  (orCase :
    ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
    200 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
    (∀ a b, a ≠ b → ∃! l, a ∈ S l ∧ b ∈ S l) →
    IsAO2 (n+n) C → C.output+1 = n+n+C.size →
    RightOnIncidentPairs S C →
    (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
    ∀ a b, n+n ≤ a → n+n ≤ b →
      C.gates[C.output-(n+n)]? = some ⟨.or,[a,b]⟩ →
      (∃ l, ∃ p ∈ S l, (C.wires (incidenceInput {p} {l})).getD a false = false) →
      (∃ l, ∃ p ∈ S l, (C.wires (incidenceInput {p} {l})).getD b false = false) →
      n*q ≤ 100*C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C large dim line pair ao outLow outHigh _ correct reject
  classical
  let m := n+n
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let correctFor (D : Circuit) := RightOnIncidentPairs S D
  let rejectFor (D : Circuit) := ∀ X Y, Y.card ≤ q → IsFalseInput S X Y →
    D.eval (incidenceInput X Y) = false
  have rowLength (X Y : Finset (Fin n)) : (incidenceInput X Y).length = m := by
    change (List.ofFn (fun p : Fin n => decide (p ∈ X)) ++
      List.ofFn (fun l : Fin n => decide (l ∈ Y))).length = n+n
    rw [List.length_append,List.length_ofFn,List.length_ofFn]
  have stepLength (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length+gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp [step,Nat.add_comm,Nat.add_left_comm]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih (step w g)]
      · exact List.getD_append _ _ _ _ hi
      · simp [step]
        omega
  have seesInput (D : Circuit) (v : ℕ) (raw : v < m) :
      ∃ X Y, Y.card ≤ q ∧ IsFalseInput S X Y ∧ (D.wires (incidenceInput X Y)).getD v false = true := by
    have read (X Y : Finset (Fin n)) :
        (D.wires (incidenceInput X Y)).getD v false = (incidenceInput X Y).getD v false :=
      keep D.gates _ v (by rw [rowLength]; exact raw)
    by_cases point : v < n
    · let p : Fin n := ⟨v,point⟩
      refine ⟨{p},∅,by simp,?_,?_⟩
      · intro l hl
        simp at hl
      · rw [read]
        change (List.ofFn (fun i : Fin n => decide (i ∈ ({p} : Finset (Fin n)))) ++
          List.ofFn (fun i : Fin n => decide (i ∈ (∅ : Finset (Fin n))))).getD v false = true
        rw [List.getD_append _ _ _ _ (by simpa using point)]
        rw [List.getD_eq_getElem _ _ (by simpa using point),List.getElem_ofFn]
        exact decide_eq_true (Finset.mem_singleton_self p)
    · have lineIndex : v-n < n := by unfold m at raw; omega
      let l : Fin n := ⟨v-n,lineIndex⟩
      refine ⟨∅,{l},by simp; omega,?_,?_⟩
      · intro a _
        exact Finset.disjoint_empty_right _
      · rw [read]
        change (List.ofFn (fun i : Fin n => decide (i ∈ (∅ : Finset (Fin n)))) ++
          List.ofFn (fun i : Fin n => decide (i ∈ ({l} : Finset (Fin n))))).getD v false = true
        rw [List.getD_append_right _ _ _ _ (by simp; omega),List.length_ofFn]
        rw [List.getD_eq_getElem _ _ (by simpa using lineIndex),List.getElem_ofFn]
        exact decide_eq_true (Finset.mem_singleton_self l)
  have value (D : Circuit) (shape : IsAO2 m D) (k : ℕ) (g : Gate) (found : D.gates[k]? = some g)
      (w : List Bool) (length : w.length = m) :
      (D.wires w).getD (m+k) false = g.op.eval (g.inputs.map fun i => (D.wires w).getD i false) := by
    have klt : k < D.gates.length := by
      by_contra! h
      rw [List.getElem?_eq_none h] at found
      cases found
    have name : D.gates[k] = g := by rwa [getElem?_pos _ k klt,Option.some.injEq] at found
    have gateName : gateAt D k = g := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ klt,name]
    have back (i : ℕ) (hi : i ∈ g.inputs) : i < m+k := shape.2.1 k klt i (by rwa [gateName])
    let pref := (D.gates.take k).foldl step w
    have plen : pref.length = m+k := by
      change ((D.gates.take k).foldl step w).length = _
      rw [stepLength,length,List.length_take,Nat.min_eq_left (by omega)]
    have split : D.gates = D.gates.take k ++ g :: D.gates.drop (k+1) := by
      have eq := List.take_concat_get klt
      rw [name] at eq
      calc
        D.gates = D.gates.take (k+1) ++ D.gates.drop (k+1) := (List.take_append_drop _ _).symm
        _ = D.gates.take k ++ g :: D.gates.drop (k+1) := by rw [← eq,List.concat_eq_append,List.append_assoc]; rfl
    have fold : D.wires w = (D.gates.drop (k+1)).foldl step (step pref g) := by
      change D.gates.foldl step w = _
      conv_lhs => rw [split]
      rw [List.foldl_append,List.foldl_cons]
    rw [fold]
    rw [keep _ _ _ (by simp [step,plen]),← plen]
    change (pref ++ [_]).getD pref.length false = _
    rw [List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self]
    change g.op.eval (g.inputs.map fun i => pref.getD i false) = _
    apply congrArg g.op.eval
    apply List.map_congr_left
    intro i hi
    have bound : i < pref.length := by rw [plen]; exact back i hi
    rw [keep (D.gates.drop (k+1)) (step pref g) i (by simp [step]; omega)]
    exact (List.getD_append _ _ _ _ bound).symm
  have equalGate (g h : Gate) (ops : g.op = h.op) (pins : g.inputs = h.inputs) : g = h := by
    cases g
    cases h
    simpa using And.intro ops pins
  let trim (D : Circuit) (v : ℕ) : Circuit := ⟨D.gates.take (v-m+1),v⟩
  have trimSize (D : Circuit) (v : ℕ) (valid : m ≤ v ∧ v < m+D.size) :
      (trim D v).size = v-m+1 := by
    change (D.gates.take (v-m+1)).length = v-m+1
    rw [List.length_take,Nat.min_eq_left]
    change v-m+1 ≤ D.size
    omega
  have trimAO (D : Circuit) (v : ℕ) (shape : IsAO2 m D) : IsAO2 m (trim D v) := by
    refine ⟨fun g h => shape.1 g (List.mem_of_mem_take h),?_,
      fun g h => shape.2.2 g (List.mem_of_mem_take h)⟩
    intro j hj i hi
    have old : j < D.gates.length := by
      change j < (D.gates.take (v-m+1)).length at hj
      rw [List.length_take] at hj
      omega
    have e : gateAt (trim D v) j = gateAt D j := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hj,List.getD_eq_getElem _ _ old]
      exact List.getElem_take
    exact shape.2.1 j old i (by rwa [e] at hi)
  have trimVal (D : Circuit) (v : ℕ) (valid : m ≤ v ∧ v < m+D.size) (w : List Bool)
      (len : w.length = m) : (trim D v).eval w = (D.wires w).getD v false := by
    let z := (D.gates.take (v-m+1)).foldl step w
    have long : v < z.length := by
      change v < ((D.gates.take (v-m+1)).foldl step w).length
      rw [stepLength,len]
      change v < m+(trim D v).size
      rw [trimSize D v valid]
      omega
    have cut : D.wires w = (D.gates.drop (v-m+1)).foldl step z := by
      change D.gates.foldl step w = _
      conv_lhs => rw [← List.take_append_drop (v-m+1) D.gates]
      rw [List.foldl_append]
    rw [cut,keep _ _ _ long]
    rfl
  have main (k : ℕ) : ∀ D : Circuit, D.size = k → IsAO2 m D →
      D.output < m+D.size → correctFor D → rejectFor D → n*q ≤ 100*D.size := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro D size shape output good sound
      have forbidRaw (v : ℕ) (quiet : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y →
          (D.wires (incidenceInput X Y)).getD v false = false) : m ≤ v := by
        by_contra! raw
        obtain ⟨X,Y,card,no,read⟩ := seesInput D v raw
        rw [quiet X Y card no] at read
        exact Bool.noConfusion read
      have baseOutput : m ≤ D.output := forbidRaw _ sound
      have jump (v : ℕ) (back : v < D.output)
          (accept : ∀ l, ∀ p ∈ S l, (D.wires (incidenceInput {p} {l})).getD v false = true)
          (quiet : ∀ X Y, Y.card ≤ q → IsFalseInput S X Y →
            (D.wires (incidenceInput X Y)).getD v false = false) : n*q ≤ 100*D.size := by
        have valid : m ≤ v ∧ v < m + D.size := ⟨forbidRaw _ quiet,by omega⟩
        have sz := trimSize D v valid
        have small : (trim D v).size < k := by omega
        have bound := ih (trim D v).size small (trim D v) rfl (trimAO D v shape)
          (by change v < m+(trim D v).size; omega)
          (fun l p hp => (trimVal D v valid _ (rowLength _ _)).trans (accept l p hp))
          (fun X Y card no => (trimVal D v valid _ (rowLength _ _)).trans (quiet X Y card no))
        omega
      by_cases last : D.output+1 = m+D.size
      · let j := D.output-m
        have idx : j < D.gates.length := by change D.output-m < D.size; omega
        let g := D.gates[j]
        have eq : D.gates[j]? = some g := getElem?_pos _ j idx
        have mem : g ∈ D.gates := List.getElem_mem idx
        rcases shape.1 g mem with op | op
        · exact andCase q n S D large dim line pair shape baseOutput output ⟨g,eq,op⟩ good sound
        · have how : g.inputs.length = 2 := shape.2.2 g mem
          obtain ⟨a,b,ins⟩ : ∃ a b : ℕ, g.inputs = [a,b] := by
            cases list : g.inputs with
            | nil => simp [list] at how
            | cons a xs =>
              cases xs with
              | nil => simp [list] at how
              | cons b ys =>
                cases ys with
                | nil => exact ⟨a,b,rfl⟩
                | cons y zs => simp [list] at how
          have actual : gateAt D j = g := by
            unfold gateAt
            rw [List.getD_eq_getElem _ _ idx]
          have readBack (i : ℕ) (mem : i ∈ g.inputs) : i < D.output := by
            have lt := shape.2.1 j idx i (by rwa [actual])
            dsimp [j] at lt
            omega
          have aPrior : a < D.output := readBack a (by simp [ins])
          have bPrior : b < D.output := readBack b (by simp [ins])
          have combine (X Y : Finset (Fin n)) :
              D.eval (incidenceInput X Y) =
                ((D.wires (incidenceInput X Y)).getD a false ||
                  (D.wires (incidenceInput X Y)).getD b false) := by
            have eval := value D shape j g eq _ (rowLength X Y)
            rw [op,ins] at eval
            have wire : m+j = D.output := by dsimp [j]; omega
            rw [wire] at eval
            change D.eval (incidenceInput X Y) =
              ((D.wires (incidenceInput X Y)).getD a false ||
                ((D.wires (incidenceInput X Y)).getD b false || false)) at eval
            simpa only [Bool.or_false] using eval
          have soundA (X Y : Finset (Fin n)) (card : Y.card ≤ q) (no : IsFalseInput S X Y) :
              (D.wires (incidenceInput X Y)).getD a false = false :=
            (Bool.or_eq_false_iff.mp ((combine X Y).symm.trans (sound X Y card no))).1
          have soundB (X Y : Finset (Fin n)) (card : Y.card ≤ q) (no : IsFalseInput S X Y) :
              (D.wires (incidenceInput X Y)).getD b false = false :=
            (Bool.or_eq_false_iff.mp ((combine X Y).symm.trans (sound X Y card no))).2
          by_cases allA : ∀ l, ∀ p ∈ S l, (D.wires (incidenceInput {p} {l})).getD a false = true
          · exact jump a aPrior allA soundA
          · by_cases allB : ∀ l, ∀ p ∈ S l, (D.wires (incidenceInput {p} {l})).getD b false = true
            · exact jump b bPrior allB soundB
            · push Not at allA allB
              obtain ⟨la,pa,hia,notA⟩ := allA
              obtain ⟨lb,pb,hib,notB⟩ := allB
              have packed : g = ⟨.or,[a,b]⟩ := equalGate _ _ op ins
              have atOutput : D.gates[j]? = some ⟨.or,[a,b]⟩ := eq.trans (congrArg some packed)
              exact orCase q n S D large dim line pair shape last good sound a b
                (forbidRaw a soundA) (forbidRaw b soundB) atOutput
                ⟨la,pa,hia,Bool.eq_false_iff.mpr notA⟩ ⟨lb,pb,hib,Bool.eq_false_iff.mpr notB⟩
      · have valid : m ≤ D.output ∧ D.output < m+D.size := ⟨baseOutput,output⟩
        have sz := trimSize D D.output valid
        have small : (trim D D.output).size < k := by omega
        have bound := ih (trim D D.output).size small (trim D D.output) rfl (trimAO D D.output shape)
          (by change D.output < m+(trim D D.output).size; omega)
          (fun l p hp => (trimVal D D.output valid _ (rowLength _ _)).trans (good l p hp))
          (fun X Y card no => (trimVal D D.output valid _ (rowLength _ _)).trans (sound X Y card no))
        omega
  exact main C.size C rfl ao outHigh correct reject
