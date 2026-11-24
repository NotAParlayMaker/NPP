import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3070_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atom := Bool ⊕ Nat
abbrev Result := Atom ⊕ Gate

def evalAtom (w : List Bool) : Atom → Bool
  | .inl b => b
  | .inr i => w.getD i false

def evalResult (w : List Bool) : Result → Bool
  | .inl a => evalAtom w a
  | .inr g => g.op.eval (g.inputs.map fun i => w.getD i false)

def andAtom : Atom → Atom → Result
  | .inl false, _ => .inl (.inl false)
  | _, .inl false => .inl (.inl false)
  | .inl true, a => .inl a
  | a, .inl true => .inl a
  | .inr i, .inr j => .inr ⟨.and, [i, j]⟩

def orAtom : Atom → Atom → Result
  | .inl true, _ => .inl (.inl true)
  | _, .inl true => .inl (.inl true)
  | .inl false, a => .inl a
  | a, .inl false => .inl a
  | .inr i, .inr j => .inr ⟨.or, [i, j]⟩

def simplify : GateOp → List Atom → Result
  | .and, [] => .inl (.inl true)
  | .or, [] => .inl (.inl false)
  | .and, [a] => .inl a
  | .or, [a] => .inl a
  | .and, [a, b] => andAtom a b
  | .or, [a, b] => orAtom a b
  | .not, xs =>
    match xs.headD (.inl false) with
    | .inl b => .inl (.inl (!b))
    | .inr i => .inr ⟨.not, [i]⟩
  | _, _ => .inl (.inl false)

def basis (op : GateOp) : Prop := op = .and ∨ op = .or ∨ op = .not

def cost : Result → Nat
  | .inl _ => 0
  | .inr _ => 1

def effective {α : Type} (op : GateOp) (xs : List α) : List α :=
  if op.eval [false] then xs.take 1 else xs

def zeroRead (op : GateOp) (xs : List Atom) : Bool :=
  (effective op xs).contains (.inl false)

def Bound (n : Nat) : Atom → Prop
  | .inl _ => True
  | .inr i => i < n

def Safe (n : Nat) : Result → Prop
  | .inl a => Bound n a
  | .inr g => basis g.op ∧ g.inputs.length ≤ 2 ∧ ∀ i ∈ g.inputs, i < n

lemma short_cases {α : Type} (xs : List α) (h : xs.length ≤ 2) :
    xs = [] ∨ (∃ a, xs = [a]) ∨ ∃ a b, xs = [a, b] := by
  cases xs with
  | nil => exact Or.inl rfl
  | cons a xs =>
    cases xs with
    | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
    | cons b xs =>
      cases xs with
      | nil => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
      | cons c xs => simp at h

lemma simplify_semantics (op : GateOp) (xs : List Atom)
    (ho : basis op) (hl : xs.length ≤ 2) (w : List Bool) :
    evalResult w (simplify op xs) = op.eval (xs.map (evalAtom w)) := by
  rcases ho with rfl | rfl | rfl <;>
    rcases short_cases xs hl with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  all_goals try casesm* Atom, Bool
  all_goals simp [simplify, andAtom, orAtom, evalResult, evalAtom, GateOp.eval]

lemma simplify_cost (op : GateOp) (xs : List Atom)
    (ho : basis op) (hl : xs.length ≤ 2) :
    cost (simplify op xs) + (if zeroRead op xs then 1 else 0) ≤ 1 := by
  rcases ho with rfl | rfl | rfl <;>
    rcases short_cases xs hl with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  all_goals try casesm* Atom, Bool
  all_goals simp [simplify, andAtom, orAtom, cost, zeroRead, effective, GateOp.eval]

lemma simplify_safe (n : Nat) (op : GateOp) (xs : List Atom)
    (ho : basis op) (hl : xs.length ≤ 2)
    (hb : ∀ a ∈ xs, Bound n a) : Safe n (simplify op xs) := by
  rcases ho with rfl | rfl | rfl <;>
    rcases short_cases xs hl with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
  all_goals try casesm* Atom, Bool
  all_goals simp_all [simplify, andAtom, orAtom, Safe, Bound, basis]

def valStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl valStep w

def emit (gs : List Gate) : Result → List Gate
  | .inl _ => gs
  | .inr g => gs ++ [g]

def resultAtom (n : Nat) (gs : List Gate) : Result → Atom
  | .inl a => a
  | .inr _ => .inr (n + gs.length)

def normalStep (n : Nat) (s : List Gate × List Atom) (g : Gate) :
    List Gate × List Atom :=
  let r := simplify g.op (g.inputs.map fun i => s.2.getD i (.inl false))
  (emit s.1 r, s.2 ++ [resultAtom n s.1 r])

def initial {n : Nat} (xs : List (Option (Fin n))) : List Atom :=
  xs.map fun a => a.elim (.inl false) (fun i => .inr i.val)

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (valStep w g)).length = _
    rw [ih]
    simp [valStep]
    omega

lemma run_keeps (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (valStep w g)).getD i false = _
    rw [ih _ (by simp [valStep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma emit_length (gs : List Gate) (r : Result) :
    (emit gs r).length = gs.length + cost r := by
  cases r <;> simp [emit, cost]

lemma bound_mono {n m : Nat} (h : n ≤ m) (a : Atom) :
    Bound n a → Bound m a := by
  cases a <;> simp_all [Bound]
  omega

lemma lookup_bound (n : Nat) (xs : List Atom)
    (h : ∀ a ∈ xs, Bound n a) (i : Nat) :
    Bound n (xs.getD i (.inl false)) := by
  simp only [List.getD_eq_getElem?_getD]
  cases he : xs[i]? with
  | none => trivial
  | some a => exact h a (List.mem_of_getElem? he)

lemma eval_lookup (xs : List Atom) (w : List Bool) (i : Nat) :
    (xs.map (evalAtom w)).getD i false = evalAtom w (xs.getD i (.inl false)) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases xs[i]? <;> simp [evalAtom]

lemma run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w = valStep (run gs w) g := by
  simp [run, List.foldl_append]

lemma evalAtom_emit (n : Nat) (gs : List Gate) (r : Result) (w : List Bool)
    (hw : w.length = n) (a : Atom) (ha : Bound (n + gs.length) a) :
    evalAtom (run (emit gs r) w) a = evalAtom (run gs w) a := by
  cases r with
  | inl _ => rfl
  | inr g =>
    cases a with
    | inl _ => rfl
    | inr i =>
      change (run (gs ++ [g]) w).getD i false = _
      rw [run_snoc]
      have hi : i < (run gs w).length := by
        simpa [run_length, hw, Bound] using ha
      exact List.getD_append _ _ _ _ hi

lemma eval_resultAtom (n : Nat) (gs : List Gate) (r : Result) (w : List Bool)
    (hw : w.length = n) :
    evalAtom (run (emit gs r) w) (resultAtom n gs r) =
      evalResult (run gs w) r := by
  cases r with
  | inl _ => rfl
  | inr g =>
    change (run (gs ++ [g]) w).getD (n + gs.length) false = _
    rw [run_snoc]
    have hl : (run gs w).length = n + gs.length := by rw [run_length, hw]
    change ((run gs w) ++ [_]).getD (n + gs.length) false = _
    rw [← hl, List.getD_append_right _ _ _ _ (le_refl _)]
    simp [evalResult]

lemma resultAtom_bound (n : Nat) (gs : List Gate) (r : Result)
    (hs : Safe (n + gs.length) r) :
    Bound (n + (emit gs r).length) (resultAtom n gs r) := by
  cases r with
  | inl a => exact hs
  | inr g => simp [Bound, resultAtom, emit]

lemma normalStep_bound (n : Nat) (gs : List Gate) (xs : List Atom) (g : Gate)
    (hg : basis g.op ∧ g.inputs.length ≤ 2)
    (hb : ∀ a ∈ xs, Bound (n + gs.length) a) :
    ∀ a ∈ (normalStep n (gs, xs) g).2,
      Bound (n + (normalStep n (gs, xs) g).1.length) a := by
  let r := simplify g.op (g.inputs.map fun i => xs.getD i (.inl false))
  have hs : Safe (n + gs.length) r := simplify_safe _ _ _ hg.1
    (by simpa using hg.2) (by
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 ha
      exact lookup_bound _ _ hb i)
  intro a ha
  change a ∈ xs ++ [resultAtom n gs r] at ha
  change Bound (n + (emit gs r).length) a
  rcases List.mem_append.1 ha with ha | ha
  · exact bound_mono (by rw [emit_length]; omega) a (hb a ha)
  · have he : a = resultAtom n gs r := by simpa using ha
    rw [he]
    exact resultAtom_bound _ _ _ hs

lemma normalStep_sound (n : Nat) (gs : List Gate) (xs : List Atom) (g : Gate)
    (hg : basis g.op ∧ g.inputs.length ≤ 2)
    (hb : ∀ a ∈ xs, Bound (n + gs.length) a)
    (w : List Bool) (hw : w.length = n) :
    (normalStep n (gs, xs) g).2.map
        (evalAtom (run (normalStep n (gs, xs) g).1 w)) =
      valStep (xs.map (evalAtom (run gs w))) g := by
  let r := simplify g.op (g.inputs.map fun i => xs.getD i (.inl false))
  have hm : xs.map (evalAtom (run (emit gs r) w)) =
      xs.map (evalAtom (run gs w)) := by
    apply List.map_congr_left
    intro a ha
    exact evalAtom_emit n gs r w hw a (hb a ha)
  change (xs ++ [resultAtom n gs r]).map (evalAtom (run (emit gs r) w)) = _
  rw [List.map_append, List.map_singleton, hm, eval_resultAtom _ _ _ _ hw]
  unfold valStep
  congr 1
  rw [simplify_semantics _ _ hg.1 (by simpa using hg.2)]
  simp only [List.map_map]
  congr 1
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro i _
  exact (eval_lookup xs (run gs w) i).symm

lemma effective_map {α β : Type} (op : GateOp) (f : α → β) (xs : List α) :
    effective op (xs.map f) = (effective op xs).map f := by
  unfold effective
  split <;> simp [List.map_take]

def charged (K : List Nat) (g : Gate) : Bool :=
  K.any fun i => (effective g.op g.inputs).contains i

lemma charged_zeroRead (K : List Nat) (xs : List Atom) (g : Gate)
    (hp : ∀ i ∈ K, xs.getD i (.inl false) = .inl false)
    (hc : charged K g = true) :
    zeroRead g.op (g.inputs.map fun i => xs.getD i (.inl false)) = true := by
  obtain ⟨i, hi, hgi⟩ := List.any_eq_true.1 hc
  unfold zeroRead
  rw [effective_map]
  apply List.contains_iff_mem.2
  exact List.mem_map.2 ⟨i, List.contains_iff_mem.1 hgi, hp i hi⟩

lemma normalStep_cost (n : Nat) (gs : List Gate) (xs : List Atom) (g : Gate)
    (K : List Nat) (hg : basis g.op ∧ g.inputs.length ≤ 2)
    (hp : ∀ i ∈ K, xs.getD i (.inl false) = .inl false) :
    (normalStep n (gs, xs) g).1.length + (if charged K g then 1 else 0) ≤
      gs.length + 1 := by
  have hs := simplify_cost g.op (g.inputs.map fun i => xs.getD i (.inl false))
    hg.1 (by simpa using hg.2)
  have hz := charged_zeroRead K xs g hp
  change (emit gs _).length + _ ≤ _
  rw [emit_length]
  cases hc : charged K g <;>
    cases he : zeroRead g.op (g.inputs.map fun i => xs.getD i (.inl false)) <;>
    simp_all
lemma normalStep_protected (n : Nat) (gs : List Gate) (xs : List Atom) (g : Gate)
    (K : List Nat)
    (hp : ∀ i ∈ K, i < xs.length ∧ xs.getD i (.inl false) = .inl false) :
    ∀ i ∈ K, i < (normalStep n (gs, xs) g).2.length ∧
      (normalStep n (gs, xs) g).2.getD i (.inl false) = .inl false := by
  intro i hi
  obtain ⟨hb, he⟩ := hp i hi
  constructor
  · change i < (xs ++ [_]).length
    simp
    omega
  · change (xs ++ [_]).getD i (.inl false) = _
    rw [List.getD_append _ _ _ _ hb, he]

def Good (gs : List Gate) : Prop :=
  ∀ g ∈ gs, basis g.op ∧ g.inputs.length ≤ 2

def normalize (n : Nat) (gs ds : List Gate) (xs : List Atom) :
    List Gate × List Atom :=
  gs.foldl (normalStep n) (ds, xs)

lemma normalStep_good (n : Nat) (ds : List Gate) (xs : List Atom) (g : Gate)
    (hd : Good ds) (hg : basis g.op ∧ g.inputs.length ≤ 2)
    (hb : ∀ a ∈ xs, Bound (n + ds.length) a) :
    Good (normalStep n (ds, xs) g).1 := by
  let r := simplify g.op (g.inputs.map fun i => xs.getD i (.inl false))
  have hs : Safe (n + ds.length) r := simplify_safe _ _ _ hg.1
    (by simpa using hg.2) (by
      intro a ha
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 ha
      exact lookup_bound _ _ hb i)
  change Good (emit ds r)
  cases he : r with
  | inl a => exact hd
  | inr g' =>
    rw [he] at hs
    intro h hh
    rcases List.mem_append.1 hh with hh | hh
    · exact hd h hh
    · have eq : h = g' := by simpa using hh
      subst h
      exact ⟨hs.1, hs.2.1⟩

lemma normalize_invariants (n : Nat) (gs ds : List Gate) (xs : List Atom)
    (K : List Nat) (hg : Good gs) (hd : Good ds)
    (hb : ∀ a ∈ xs, Bound (n + ds.length) a)
    (hp : ∀ i ∈ K, i < xs.length ∧ xs.getD i (.inl false) = .inl false) :
    Good (normalize n gs ds xs).1 ∧
      (∀ a ∈ (normalize n gs ds xs).2,
        Bound (n + (normalize n gs ds xs).1.length) a) ∧
      (∀ i ∈ K, i < (normalize n gs ds xs).2.length ∧
        (normalize n gs ds xs).2.getD i (.inl false) = .inl false) ∧
      (normalize n gs ds xs).1.length + (gs.filter (charged K)).length ≤
        ds.length + gs.length := by
  induction gs generalizing ds xs with
  | nil => exact ⟨hd, hb, hp, by simp [normalize]⟩
  | cons g gs ih =>
    have hhead := hg g (by simp)
    have htail : Good gs := fun h hh => hg h (List.mem_cons_of_mem g hh)
    let s := normalStep n (ds, xs) g
    have hsGood : Good s.1 := normalStep_good n ds xs g hd hhead hb
    have hsBound : ∀ a ∈ s.2, Bound (n + s.1.length) a :=
      normalStep_bound n ds xs g hhead hb
    have hsProtected : ∀ i ∈ K,
        i < s.2.length ∧ s.2.getD i (.inl false) = .inl false :=
      normalStep_protected n ds xs g K hp
    obtain ⟨hf, hbf, hpf, hcost⟩ := ih s.1 s.2 htail hsGood hsBound hsProtected
    refine ⟨hf, hbf, hpf, ?_⟩
    have hc := normalStep_cost n ds xs g K hhead (fun i hi => (hp i hi).2)
    change s.1.length + (if charged K g then 1 else 0) ≤ ds.length + 1 at hc
    change (normalize n gs s.1 s.2).1.length +
      ((g :: gs).filter (charged K)).length ≤ ds.length + (g :: gs).length
    cases he : charged K g <;> simp [he] at hc ⊢ <;> omega

lemma normalize_sound (n : Nat) (gs ds : List Gate) (xs : List Atom)
    (hg : Good gs) (hb : ∀ a ∈ xs, Bound (n + ds.length) a)
    (w : List Bool) (hw : w.length = n) :
    (normalize n gs ds xs).2.map
        (evalAtom (run (normalize n gs ds xs).1 w)) =
      run gs (xs.map (evalAtom (run ds w))) := by
  induction gs generalizing ds xs with
  | nil => rfl
  | cons g gs ih =>
    have hhead := hg g (by simp)
    have htail : Good gs := fun h hh => hg h (List.mem_cons_of_mem g hh)
    let s := normalStep n (ds, xs) g
    have hsBound : ∀ a ∈ s.2, Bound (n + s.1.length) a :=
      normalStep_bound n ds xs g hhead hb
    have hi := ih s.1 s.2 htail hsBound
    have hs := normalStep_sound n ds xs g hhead hb w hw
    exact hi.trans (congrArg (run gs) hs)

lemma initial_bound {n : Nat} (xs : List (Option (Fin n))) :
    ∀ a ∈ initial xs, Bound n a := by
  intro a ha
  obtain ⟨q, _, rfl⟩ := List.mem_map.1 ha
  cases q with
  | none => trivial
  | some i => exact i.isLt

lemma initial_sound {n : Nat} (xs : List (Option (Fin n))) (x : Fin n → Bool) :
    (initial xs).map (evalAtom (List.ofFn x)) = xs.map (fun q => q.elim false x) := by
  simp only [initial, List.map_map]
  apply List.map_congr_left
  intro q _
  cases q with
  | none => rfl
  | some i => simp [evalAtom, List.getD_eq_getElem?_getD]

lemma initial_protected {n : Nat} (xs : List (Option (Fin n))) (K : List Nat)
    (h : ∀ i ∈ K, xs[i]? = some none) :
    ∀ i ∈ K, i < (initial xs).length ∧
      (initial xs).getD i (.inl false) = .inl false := by
  intro i hi
  have he := h i hi
  have hb : i < xs.length := by
    by_contra! hn
    have hnone : xs[i]? = none := List.getElem?_eq_none_iff.2 hn
    rw [hnone] at he
    contradiction
  constructor
  · simpa [initial] using hb
  · simp only [initial, List.getD_eq_getElem?_getD, List.getElem?_map, he]
    rfl

lemma main (n : Nat) (C : Circuit) (xs : List (Option (Fin n))) (K : List Nat)
    (hf : FanInTwo C) (hk : ∀ i ∈ K, xs[i]? = some none)
    (hn : ∃ x y : Fin n → Bool,
      C.eval (xs.map fun q => q.elim false x) ≠
        C.eval (xs.map fun q => q.elim false y)) :
    ∃ D : Circuit, FanInTwo D ∧
      D.size + (C.gates.filter (charged K)).length ≤ C.size ∧
      ∀ x : Fin n → Bool,
        D.eval (List.ofFn x) = C.eval (xs.map fun q => q.elim false x) := by
  have hg : Good C.gates := by
    intro g h
    exact ⟨by simpa [basis] using (hf g h).1, (hf g h).2⟩
  have hb : ∀ a ∈ initial xs, Bound (n + ([] : List Gate).length) a := by
    simpa using initial_bound xs
  let s := normalize n C.gates [] (initial xs)
  obtain ⟨hgood, _, _, hcost⟩ := normalize_invariants n C.gates [] (initial xs) K
    hg (by simp [Good]) hb (initial_protected xs K hk)
  have hv (x : Fin n → Bool) :
      evalAtom (run s.1 (List.ofFn x)) (s.2.getD C.output (.inl false)) =
        C.eval (xs.map fun q => q.elim false x) := by
    have hsem := normalize_sound n C.gates [] (initial xs) hg hb (List.ofFn x)
      (by simp)
    change s.2.map (evalAtom (run s.1 (List.ofFn x))) =
      run C.gates ((initial xs).map (evalAtom (List.ofFn x))) at hsem
    rw [initial_sound] at hsem
    rw [← eval_lookup, hsem]
    rfl
  cases he : s.2.getD C.output (.inl false) with
  | inl b =>
    obtain ⟨x, y, hxy⟩ := hn
    have hx := hv x
    have hy := hv y
    rw [he] at hx hy
    exact False.elim (hxy (hx.symm.trans hy))
  | inr i =>
    refine ⟨⟨s.1, i⟩, ?_, ?_, ?_⟩
    · intro g h
      have h' := hgood g h
      exact ⟨by simpa [basis] using h'.1, h'.2⟩
    · simpa [Circuit.size] using hcost
    · intro x
      have h := hv x
      rw [he] at h
      exact h

end PEqualNP.Outside.L_meta_3070_aux

theorem PEqualNP.Outside.L_meta_3070 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Option (Fin x1))) (x4 : List ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ x6 ∈ x4, x3[x6]? = Option.some Option.none) → (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x2.eval (List.map (fun (x9 : Option (Fin x1)) => x9.elim Bool.false x7) x3) ≠ x2.eval (List.map (fun (x9 : Option (Fin x1)) => x9.elim Bool.false x8) x3)) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x8 ∧ x8.size + (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => x4.any fun (x10 : ℕ) => (if x9.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x9.inputs else x9.inputs).contains x10) x2.gates).length ≤ x2.size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x2.eval (List.map (fun (x10 : Option (Fin x1)) => x10.elim Bool.false x9) x3) := by
  intro n C xs K hf hk hn
  exact PEqualNP.Outside.L_meta_3070_aux.main n C xs K hf hk hn
