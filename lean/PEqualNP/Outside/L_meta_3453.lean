import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3453

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.FactorSubst

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

def wirePrefix (C : Circuit) (xs : List Bool) (r : Nat) : List Bool :=
  (C.gates.take r).foldl step xs

theorem fold_length (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem fold_extends (gs : List Gate) (xs : List Bool) :
    ∃ ys, gs.foldl step xs = xs ++ ys := by
  induction gs generalizing xs with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨ys, eq⟩ := ih (step xs g)
    exact ⟨_ :: ys, by simpa [step, List.append_assoc] using eq⟩

theorem prefix_length (C : Circuit) (xs : List Bool) (r : Nat) (hr : r ≤ C.gates.length) :
    (wirePrefix C xs r).length = xs.length + r := by
  simp [wirePrefix, fold_length, Nat.min_eq_left hr]

theorem prefix_read (C : Circuit) (xs : List Bool) (r i : Nat)
    (hr : r ≤ C.gates.length) (hi : i < xs.length + r) :
    (wirePrefix C xs r).getD i false = (C.wires xs).getD i false := by
  obtain ⟨tail, h⟩ := fold_extends (C.gates.drop r) (wirePrefix C xs r)
  have full : C.wires xs = wirePrefix C xs r ++ tail := by
    change C.gates.foldl step xs = _
    rw [← List.take_append_drop r C.gates, List.foldl_append]
    exact h
  rw [full]
  have hp : i < (wirePrefix C xs r).length := by rwa [prefix_length _ _ _ hr]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hp]

theorem gateAt_eq (C : Circuit) (r : Nat) (hr : r < C.gates.length) :
    gateAt C r = C.gates[r] := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hr]

theorem prefix_succ (C : Circuit) (xs : List Bool) (r : Nat) (hr : r < C.gates.length) :
    wirePrefix C xs (r+1) = step (wirePrefix C xs r) (gateAt C r) := by
  unfold wirePrefix
  rw [List.take_succ_eq_append_getElem hr, List.foldl_append, gateAt_eq C r hr]
  rfl

theorem snoc_read (xs : List Bool) (v : Bool) (i : Nat) :
    (xs ++ [v]).getD i false =
      if i < xs.length then xs.getD i false else if i = xs.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h e
  · rw [List.getElem?_append_left h]
  · subst e; simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem combine (R : Bool → Bool → Prop) (refl : ∀ p, R p p)
    (andRel : ∀ {p q t s}, R p q → R t s → R (p && t) (q && s))
    (orRel : ∀ {p q t s}, R p q → R t s → R (p || t) (q || s))
    (op : GateOp) (basis : op = .and ∨ op = .or)
    (args : List Nat) (f h : Nat → Bool) (rel : ∀ i ∈ args, R (f i) (h i)) :
    R (op.eval (args.map f)) (op.eval (args.map h)) := by
  induction args with
  | nil => exact refl _
  | cons a args ih =>
    have ha := rel a (by simp)
    have ht := ih (fun i hi => rel i (by simp [hi]))
    rcases basis with rfl | rfl
    · simpa [GateOp.eval] using andRel ha ht
    · simpa [GateOp.eval] using orRel ha ht

theorem transport (R : Bool → Bool → Prop) (refl : ∀ p, R p p)
    (trans : ∀ {p q t}, R p q → R q t → R p t)
    (andRel : ∀ {p q t s}, R p q → R t s → R (p && t) (q && s))
    (orRel : ∀ {p q t s}, R p q → R t s → R (p || t) (q || s))
    (n : Nat) (C : Circuit) (u : Nat) (sigma : Nat → Nat) (xs : List Bool)
    (hlen : xs.length = n) (ao : IsAO2 n C) (earlier : ∀ r, sigma r < n + u)
    (hrd : ∀ r < C.gates.length, n+u ∈ (gateAt C r).inputs →
      R ((C.wires xs).getD (sigma r) false) ((C.wires xs).getD (n+u) false)) :
    ∀ i, R (((substReads C n u sigma).wires xs).getD i false) ((C.wires xs).getD i false) := by
  let D := substReads C n u sigma
  have glen : D.gates.length = C.gates.length := by simp [D, substReads]
  have inductionResult (r : Nat) (hr : r ≤ C.gates.length) :
      ∀ i, R ((wirePrefix D xs r).getD i false) ((wirePrefix C xs r).getD i false) := by
    induction r with
    | zero => intro i; exact refl _
    | succ r ih =>
      have hlt : r < C.gates.length := by omega
      have hd : r < D.gates.length := by omega
      intro i
      rw [prefix_succ D xs r hd, prefix_succ C xs r hlt]
      let g := gateAt C r
      let rep := fun i : Nat => if i = n+u then sigma r else i
      have mapped : gateAt D r = ⟨g.op, g.inputs.map rep⟩ := by
        change gateAt D r = ⟨(gateAt C r).op, (gateAt C r).inputs.map rep⟩
        rw [gateAt_eq D r hd, gateAt_eq C r hlt]
        change (C.gates.mapIdx _)[r] = _
        exact List.getElem_mapIdx (l := C.gates) (i := r)
          (f := fun j (v : Gate) => (⟨v.op, v.inputs.map fun a => if a = n+u then sigma j else a⟩ : Gate))
      have basis : g.op = .and ∨ g.op = .or := by
        apply ao.1 g
        change gateAt C r ∈ C.gates
        rw [gateAt_eq C r hlt]
        exact List.getElem_mem hlt
      have point (a : Nat) (ha : a ∈ g.inputs) :
          R ((wirePrefix D xs r).getD (rep a) false) ((wirePrefix C xs r).getD a false) := by
        by_cases hit : a = n+u
        · subst a
          have prev := ao.2.1 r hlt (n+u) ha
          have before : sigma r < xs.length + r := by rw [hlen]; have := earlier r; omega
          have within : n+u < xs.length + r := by rwa [hlen]
          have localRead := hrd r hlt ha
          rw [← prefix_read C xs r _ (by omega) before, ← prefix_read C xs r _ (by omega) within] at localRead
          simpa [rep] using trans (ih (by omega) (sigma r)) localRead
        · simpa [rep, hit] using ih (by omega) a
      have val := combine R refl andRel orRel g.op basis g.inputs
        (fun a => (wirePrefix D xs r).getD (rep a) false)
        (fun a => (wirePrefix C xs r).getD a false) point
      rw [mapped]
      simp only [step, List.map_map, Function.comp_def, snoc_read,
        prefix_length D xs r (by omega), prefix_length C xs r (by omega)]
      split_ifs <;> first | exact ih (by omega) i | exact val | exact refl _
  have fin := inductionResult C.gates.length (by omega)
  have doneW (K : Circuit) : wirePrefix K xs K.gates.length = K.wires xs := by
    unfold wirePrefix
    rw [List.take_length]
    rfl
  have dDone : wirePrefix D xs C.gates.length = D.wires xs := by
    rw [← glen, doneW]
  rw [dDone, doneW C] at fin
  exact fin

end PEqualNP.Outside.L_meta_3453

theorem PEqualNP.Outside.L_meta_3453 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (sigma : ℕ → ℕ) (x : Fin n → Bool), PEqualNP.TopForm.IsAO2 n C → u < C.gates.length → (∀ r : ℕ, sigma r < n + u) → ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = true → (C.wires (List.ofFn x)).getD (n + u) false = true) → ∀ i : ℕ, ((PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x)).getD i false = true → (C.wires (List.ofFn x)).getD i false = true) ∧ ((∀ r < C.gates.length, n + u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs → (C.wires (List.ofFn x)).getD (sigma r) false = (C.wires (List.ofFn x)).getD (n + u) false) → (PEqualNP.FactorSubst.substReads C n u sigma).wires (List.ofFn x) = C.wires (List.ofFn x)) := by
  intro n C u sigma x ao _ earlier
  let xs := List.ofFn x
  let D := PEqualNP.FactorSubst.substReads C n u sigma
  have lengthD : (D.wires xs).length = (C.wires xs).length := by
    change (D.gates.foldl PEqualNP.Outside.L_meta_3453.step xs).length =
      (C.gates.foldl PEqualNP.Outside.L_meta_3453.step xs).length
    simp [PEqualNP.Outside.L_meta_3453.fold_length, D, PEqualNP.FactorSubst.substReads]
  constructor
  · intro h
    apply PEqualNP.Outside.L_meta_3453.transport (fun p q => p = true → q = true)
      (fun _ hp => hp) (fun pq qt hp => qt (pq hp)) _ _ n C u sigma xs (by simp [xs]) ao earlier h
    · intro p q t s pq ts hpt
      exact Bool.and_eq_true_iff.mpr ⟨pq (Bool.and_eq_true_iff.mp hpt).1, ts (Bool.and_eq_true_iff.mp hpt).2⟩
    · intro p q t s pq ts hpt
      rcases Bool.or_eq_true_iff.mp hpt with h | h
      · simp [pq h]
      · simp [ts h]
  · intro h
    have eq := PEqualNP.Outside.L_meta_3453.transport Eq (fun _ => rfl)
      (fun h1 h2 => h1.trans h2) (fun h1 h2 => by rw [h1, h2])
      (fun h1 h2 => by rw [h1, h2]) n C u sigma xs (by simp [xs]) ao earlier h
    apply List.ext_getElem lengthD
    intro i hi hj
    have qi : (D.wires xs).getD i false = (C.wires xs).getD i false := eq i
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at qi
    exact qi
