import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A least circuit admits no shortcut from a gate to one of its operands.
-- The wire renumbering follows Wang He in L_meta_1975. A least AND has a maximal false
-- input on which the shortcut changes the output, and a least OR has a minimal
-- true input with the dual property.
theorem PEqualNP.Outside.R_meta_4061_704
    (upper : ∃ D : Circuit, IsAO2 26 D ∧ D.size ≤ 64 ∧ circuitFun 26 D = fun (x : Fin 26 → Bool) => decide (∃ (p l : Fin 13), (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true))
    (finite : let F := fun (x : Fin 26 → Bool) => decide (∃ (p l : Fin 13), (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  ∀ C : Circuit, IsAO2 26 C → C.size ≤ 64 →
    (∀ x, Minimal (fun x => F x = true) x → circuitFun 26 C x = true) →
    (∀ x, Maximal (fun x => F x = false) x → circuitFun 26 C x = false) →
    (∀ k < C.size, ∀ a ∈ (gateAt C k).inputs,
      let on := (gateAt C k).op.eval [true,false] == false
      ∃ x, (if on then Maximal (fun z => F z = false) x else Minimal (fun z => F z = true) x) ∧
        (C.wires (List.ofFn x)).getD a false = on ∧
        ({gates := C.gates.drop (k+1), output := C.output} : Circuit).eval
          (({gates := C.gates.take k, output := 0} : Circuit).wires (List.ofFn x) ++ [on]) = on) →
    ∀ j < C.size, (gateAt C j).op = .and → ∀ v : Fin 26, v = 0 ∨ v = 1 ∨ v = 14 →
      gateVal 26 C j (pairInput 0 v) = false) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [_x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → ∀ x6 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x9 : Fin (26 : ℕ)), x9 = (0 : Fin (26 : ℕ)) ∨ x9 = (1 : Fin (26 : ℕ)) ∨ x9 = (14 : Fin (26 : ℕ)) → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) x9) = Bool.false := by
  intro G inst hadj C hLeast j hj hand v hv
  have gateDef (K : Circuit) (k : Nat) : gateAt K k = K.gates.getD k ⟨.or, []⟩ := rfl
  have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  let run (gs : List Gate) (w : List Bool) :=
    gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) w

  let OK (n : Nat) (gs : List Gate) := ∀ (i : Nat) (hi : i < gs.length),
    let g := gs[i]
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ ∀ a ∈ g.inputs, a < n+i

  have ao_iff {n : Nat} {C : Circuit} : IsAO2 n C ↔ OK n C.gates := by
    constructor
    · intro ao i hi
      exact ⟨ao.1 _ (List.getElem_mem _), ao.2.2 _ (List.getElem_mem _), fun a ha =>
        ao.2.1 _ hi a (by rw [gateDef, List.getD_eq_getElem _ _ hi]; exact ha)⟩
    · intro ok
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
        exact (ok i hi).1
      · intro i hi
        simpa only [gateDef, List.getD_eq_getElem _ _ hi] using (ok i hi).2.2
      · intro g hg
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
        exact (ok i hi).2.1

  have ok_append (n : Nat) (p s : List Gate) :
      OK n (p ++ s) ↔ OK n p ∧ OK (n+p.length) s := by
    constructor
    · intro ok
      constructor
      · intro i hi
        have hh := ok i (by simp; omega)
        dsimp only at hh
        rw [List.getElem_append_left hi] at hh
        exact hh
      · intro i hi
        have hk := ok (p.length+i) (by simp; omega)
        simpa only [List.getElem_append_right (Nat.le_add_right ..),
          Nat.add_sub_cancel_left, Nat.add_assoc] using hk
    · rintro ⟨hp, hs⟩ i hi
      by_cases h : i < p.length
      · simpa only [List.getElem_append_left h] using hp i h
      · have hl : i-p.length < s.length := by simp only [List.length_append] at hi; omega
        have eqn : n + p.length + (i-p.length) = n+i := by omega
        simpa only [List.getElem_append_right (Nat.le_of_not_gt h), eqn] using hs _ hl

  have run_len (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp [run]
    | cons g gs ih =>
      change (run gs (_ ++ [_])).length = _
      rw [ih]; simp; omega

  have run_append (p s : List Gate) (w : List Bool) :
      run (p++s) w = run s (run p w) := by simp [run, List.foldl_append]

  -- Delete the gate at index j and redirect its output to an earlier operand.
  -- This renumbering is also used in L_meta_1975.
  let idx (k a i : Nat) := if i < k then i else if i = k then a else i-1
  let ren (k a : Nat) (g : Gate) : Gate := ⟨g.op, g.inputs.map (idx k a)⟩

  have remap_ok {k a : Nat} (ha : a < k) {s : List Gate} (hs : OK (k+1) s) :
      OK k (s.map (ren k a)) := by
    intro i hi
    have old := hs i (by simpa using hi)
    simp only [List.getElem_map, ren, List.length_map]
    refine ⟨old.1, old.2.1, ?_⟩
    intro z hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
    have := old.2.2 t ht
    unfold idx
    split <;> (try split) <;> omega

  have ok_cons (n : Nat) (g : Gate) (s : List Gate) :
      OK n (g::s) ↔ OK n [g] ∧ OK (n+1) s := ok_append n [g] s

  have short_ok {n a : Nat} {p s : List Gate} {g : Gate} (ha : a < n+p.length)
      (ok : OK n (p ++ g::s)) : OK n (p ++ s.map (ren (n+p.length) a)) := by
    obtain ⟨hp,hs⟩ := (ok_append ..).mp ok
    exact (ok_append ..).mpr ⟨hp, remap_ok ha ((ok_cons ..).mp hs).2⟩

  have read_shift (p s : List Bool) (a i : Nat) (ha : a < p.length) :
      ((p ++ [p.getD a false]) ++ s).getD i false = (p++s).getD (idx p.length a i) false := by
    by_cases small : i < p.length
    · simp only [idx, small, ite_true]
      rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ small,
        List.getD_append _ _ _ _ small]
    · by_cases eqn : i = p.length
      · subst i
        simp only [idx, Nat.lt_irrefl, ite_false, ite_true]
        rw [List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (Nat.le_refl _),
          Nat.sub_self, List.getD_append _ _ _ _ ha]
        rfl
      · have t : p.length < i := by omega
        simp only [idx, small, eqn, ite_false]
        rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by omega)]
        simp only [List.length_append, List.length_singleton]
        congr 1; omega

  have run_shift (p s : List Bool) (gs : List Gate) (a i : Nat) (ha : a < p.length) :
      (run gs ((p ++ [p.getD a false]) ++ s)).getD i false =
        (run (gs.map (ren p.length a)) (p ++ s)).getD (idx p.length a i) false := by
    induction gs generalizing s with
    | nil => exact read_shift p s a i ha
    | cons g gs ih =>
      have eqn : g.op.eval (g.inputs.map fun j => ((p ++ [p.getD a false]) ++ s).getD j false) =
          (ren p.length a g).op.eval ((ren p.length a g).inputs.map fun j => (p++s).getD j false) := by
        simp only [ren, List.map_map]
        congr 1
        apply List.map_congr_left
        exact fun j _ => read_shift p s a j ha
      simpa only [run, List.foldl_cons, List.map_cons, ← eqn, List.append_assoc] using
        ih (s ++ [g.op.eval (g.inputs.map fun j => ((p ++ [p.getD a false]) ++ s).getD j false)])

  let dominates (p q : List Bool) := p.length = q.length ∧
    ∀ i : Nat, p.getD i false = true → q.getD i false = true

  have true_append {p q : List Bool} (h : dominates p q) {a b : Bool}
      (hb : a = true → b = true) : dominates (p ++ [a]) (q ++ [b]) := by
    refine ⟨by simp [h.1], ?_⟩
    intro i
    by_cases hs : i < p.length
    · rw [List.getD_append _ _ _ _ hs, List.getD_append _ _ _ _ (h.1 ▸ hs)]
      exact h.2 i
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by have := h.1; omega), ← h.1]
      cases i-p.length with
      | zero => exact hb
      | succ k => simp [List.getD]

  have run_mono (gs : List Gate)
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) {p q : List Bool}
      (h : dominates p q) : dominates (run gs p) (run gs q) := by
    induction gs generalizing p q with
    | nil => exact h
    | cons g gs ih =>
      apply ih (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))
      apply true_append h
      rcases ops g List.mem_cons_self with hop | hop
      · simp only [hop, andEval, List.all_eq_true, List.mem_map, id_eq]
        intro yes v hv
        obtain ⟨i, hi, rfl⟩ := hv
        exact h.2 i (yes _ ⟨i, hi, rfl⟩)
      · simp only [hop, orEval, List.any_eq_true, List.mem_map, id_eq]
        rintro ⟨v, ⟨i, hi, rfl⟩, hv⟩
        exact ⟨_, ⟨i, hi, rfl⟩, h.2 i hv⟩

  have run_read (gs : List Gate) (w : List Bool) {i : Nat} (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (run gs (_ ++ [_])).getD i false = _
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

  have bits_dom {n : Nat} {x y : Fin n → Bool}
      (h : ∀ i, x i = true → y i = true) : dominates (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using hi : i < (List.ofFn x).length),
          List.getD_eq_getElem _ _ (by simpa using hi : i < (List.ofFn y).length), List.getElem_ofFn, List.getElem_ofFn]
      exact h _
    · simp [hi]

  have pivot {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (minimum : IsLeastAO G C) (j : Nat) (hj : j < C.size)
      (on : Bool) (hop : (gateAt C j).op = if on then .and else .or)
      (a : Nat) (ha : a ∈ (gateAt C j).inputs) :
      ∃ y, (if on then Maximal (fun z => graphFun G ∅ z = false) y
             else Minimal (fun z => graphFun G ∅ z = true) y) ∧
        (C.wires (List.ofFn y)).getD a false = on ∧
        ({gates := C.gates.drop (j+1), output := C.output} : Circuit).eval
          (({gates := C.gates.take j, output := 0} : Circuit).wires (List.ofFn y) ++ [on]) = on := by
    change j < C.gates.length at hj
    let p := C.gates.take j
    let g := gateAt C j
    let s := C.gates.drop (j+1)
    have plen : p.length = j := by simp [p, Nat.min_eq_left hj.le]
    have split : C.gates = p ++ g :: s := by
      rw [show g = C.gates[j] from List.getD_eq_getElem _ _ hj]
      simp only [p, s, ← List.drop_eq_getElem_cons hj, List.take_append_drop]
    have before := minimum.1.2.1 j hj a ha
    let rough := p ++ s.map (ren (n+j) a)
    let D : Circuit := ⟨rough, idx (n+j) a C.output⟩
    have dao : IsAO2 n D := by
      apply ao_iff.mpr
      have good := ao_iff.mp minimum.1
      rw [split] at good
      change OK n rough
      simpa only [rough, plen] using short_ok (show a < n+p.length by omega) good
    have smaller : D.size < C.size := by
      change (p ++ s.map _).length < C.gates.length
      rw [split]; simp
    have ops : ∀ g ∈ s, g.op = .and ∨ g.op = .or := by
      intro g hg
      apply minimum.1.1
      rw [split]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hg))
    let front (x : Fin n → Bool) := run p (List.ofFn x)
    have frontLen x : (front x).length = n+j := by simp [front, run_len, plen]
    let old (x : Fin n → Bool) := g.op.eval (g.inputs.map fun i => (front x).getD i false)
    let bypass (x : Fin n → Bool) := (front x).getD a false
    have cv (x : Fin n → Bool) : C.wires (List.ofFn x) = run s (front x ++ [old x]) := by
      change run C.gates _ = _
      rw [split, run_append]
      rfl
    have dv (x) : circuitFun n D x = (run s (front x ++ [bypass x])).getD C.output false := by
      change (run rough _).getD _ false = _
      rw [show rough = p ++ _ from rfl, run_append]
      have h := run_shift (front x) [] s a C.output (by rw [frontLen]; exact before)
      simpa only [List.append_nil, frontLen] using h.symm

    let F := graphFun G ∅
    have real (x : Fin n → Bool) : (run s (front x ++ [old x])).getD C.output false = F x := by
      change (run s (front x ++ [old x])).getD C.output false = graphFun G ∅ x
      rw [← cv]
      exact congrFun minimum.2.1 x
    have edom (x y : Fin n → Bool) (le : x ≤ y) : circuitFun n D x = true → circuitFun n D y = true :=
      (run_mono D.gates dao.1 (bits_dom (fun i h => Bool.eq_true_of_true_le (h ▸ le i)))).2 D.output
    have diff : ∃ x, circuitFun n D x ≠ F x := by
      by_contra! all
      exact (Nat.not_le_of_gt smaller) (minimum.2.2 D dao (funext all))
    have sep (x) (e : circuitFun n D x ≠ F x) : old x ≠ bypass x := by
      intro same
      apply e
      rw [dv, ← real, same]
    have operand (x) : (C.wires (List.ofFn x)).getD a false = bypass x := by
      rw [cv, run_read _ _ (by simp; rw [frontLen]; omega), List.getD_append _ _ _ _ (by rw [frontLen]; omega)]
    have orient : ∀ a b : Bool, a ≠ b → (a = true → b = true) → a = false ∧ b = true := by decide
    obtain ⟨x, hx⟩ := diff
    cases on
    · have low (z) : bypass z = true → old z = true := by
        intro yes
        have h : g.op = .or := hop
        simp only [old, h, orEval, List.any_eq_true, List.mem_map, id_eq]
        exact ⟨_, ⟨a,ha,rfl⟩, yes⟩
      have le (z) : circuitFun n D z = true → F z = true := by
        rw [dv, ← real]
        exact (run_mono s ops (true_append ⟨rfl, fun _ h => h⟩ (low z))).2 C.output
      have dx := orient _ _ hx (le x)
      obtain ⟨y, ey, hy⟩ := Set.Finite.exists_le_minimal (s := {z | F z = true})
        (Set.toFinite _) (show x ∈ {z | F z = true} from dx.2)
      have dy : circuitFun n D y = false := by
        cases d : circuitFun n D y
        · rfl
        · exact Bool.noConfusion (dx.1.symm.trans (edom y x ey d))
      have different : circuitFun n D y ≠ F y := by rw [dy, show F y = true from hy.1]; decide
      have p := (orient _ _ (sep y different).symm (low y)).1
      refine ⟨y, hy, (operand y).trans p, ?_⟩
      change (run s (front y ++ [false])).getD C.output false = false
      rw [dv, p] at dy
      exact dy
    · have low (z) : old z = true → bypass z = true := by
        have h : g.op = .and := hop
        simp only [old, h, andEval, List.all_eq_true, List.mem_map, id_eq]
        intro yes
        exact yes _ ⟨a, ha, rfl⟩
      have le (z) : F z = true → circuitFun n D z = true := by
        rw [dv, ← real]
        exact (run_mono s ops (true_append ⟨rfl, fun _ h => h⟩ (low z))).2 C.output
      have dx := (orient _ _ hx.symm (le x)).symm
      obtain ⟨y, ey, hy⟩ := Set.Finite.exists_le_maximal (s := {z | F z = false})
        (Set.toFinite _) (show x ∈ {z | F z = false} from dx.2)
      have dy := edom x y ey dx.1
      have different : circuitFun n D y ≠ F y := by rw [dy, show F y = false from hy.1]; decide
      have p := (orient _ _ (sep y different) (low y)).2
      refine ⟨y, hy, (operand y).trans p, ?_⟩
      change (run s (front y ++ [true])).getD C.output false = true
      rw [dv, p] at dy
      exact dy

  let F := fun (x : Fin 26 → Bool) => decide (∃ (p l : Fin 13), (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true)
  have same : graphFun G ∅ = F := by
    funext z
    apply Bool.eq_iff_iff.mpr
    change ((decide (∃ a ∈ (∅ : Finset (Fin 26)), z a = true) ||
      decide (∃ a b, G.Adj a b ∧ z a = true ∧ z b = true)) = true) ↔ _
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq, F]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨p, l, inc, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (hadj u v).mp huv
      · exact ⟨p,l,inc,hu,hv⟩
      · exact ⟨p,l,inc,hv,hu⟩
    · rintro ⟨p,l,inc,hp,hl⟩
      exact ⟨_,_,(hadj _ _).mpr ⟨p,l,inc,Or.inl ⟨rfl,rfl⟩⟩,hp,hl⟩
  have computes := hLeast.2.1.trans same
  obtain ⟨E, aoE, eSize, works⟩ := upper
  have hCsize := (hLeast.2.2 E aoE (works.trans same.symm)).trans eSize
  apply finite C hLeast.1 hCsize (fun x h => (congrFun computes x).trans h.1)
    (fun x h => (congrFun computes x).trans h.1) _ j hj hand v hv
  intro k hk a ha
  have member : gateAt C k ∈ C.gates := by rw [gateDef, List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
  rcases hLeast.1.1 _ member with andOp | orOp
  · have witness := pivot G C hLeast k hk true andOp a ha
    rw [andOp]
    rw [same] at witness
    exact witness
  · have witness := pivot G C hLeast k hk false orOp a ha
    rw [orOp]
    rw [same] at witness
    exact witness
