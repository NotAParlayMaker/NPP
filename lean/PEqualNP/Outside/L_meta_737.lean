import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_737_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def petFun (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

private def adjB : Fin 10 → Fin 10 → Bool
  | ⟨0, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨0, _⟩ => true
  | ⟨1, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨1, _⟩ => true
  | ⟨2, _⟩, ⟨3, _⟩ | ⟨3, _⟩, ⟨2, _⟩ => true
  | ⟨3, _⟩, ⟨4, _⟩ | ⟨4, _⟩, ⟨3, _⟩ => true
  | ⟨4, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨4, _⟩ => true
  | ⟨0, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨0, _⟩ => true
  | ⟨1, _⟩, ⟨6, _⟩ | ⟨6, _⟩, ⟨1, _⟩ => true
  | ⟨2, _⟩, ⟨7, _⟩ | ⟨7, _⟩, ⟨2, _⟩ => true
  | ⟨3, _⟩, ⟨8, _⟩ | ⟨8, _⟩, ⟨3, _⟩ => true
  | ⟨4, _⟩, ⟨9, _⟩ | ⟨9, _⟩, ⟨4, _⟩ => true
  | ⟨5, _⟩, ⟨7, _⟩ | ⟨7, _⟩, ⟨5, _⟩ => true
  | ⟨7, _⟩, ⟨9, _⟩ | ⟨9, _⟩, ⟨7, _⟩ => true
  | ⟨9, _⟩, ⟨6, _⟩ | ⟨6, _⟩, ⟨9, _⟩ => true
  | ⟨6, _⟩, ⟨8, _⟩ | ⟨8, _⟩, ⟨6, _⟩ => true
  | ⟨8, _⟩, ⟨5, _⟩ | ⟨5, _⟩, ⟨8, _⟩ => true
  | _, _ => false

private def b2n (b : Bool) : Nat := if b then 1 else 0

private def n1 : Fin 10 → Fin 10
  | ⟨0, _⟩ => ⟨1, by decide⟩ | ⟨1, _⟩ => ⟨0, by decide⟩ | ⟨2, _⟩ => ⟨1, by decide⟩
  | ⟨3, _⟩ => ⟨2, by decide⟩ | ⟨4, _⟩ => ⟨0, by decide⟩ | ⟨5, _⟩ => ⟨0, by decide⟩
  | ⟨6, _⟩ => ⟨1, by decide⟩ | ⟨7, _⟩ => ⟨2, by decide⟩ | ⟨8, _⟩ => ⟨3, by decide⟩
  | ⟨9, _⟩ => ⟨4, by decide⟩

private def n2 : Fin 10 → Fin 10
  | ⟨0, _⟩ => ⟨4, by decide⟩ | ⟨1, _⟩ => ⟨2, by decide⟩ | ⟨2, _⟩ => ⟨3, by decide⟩
  | ⟨3, _⟩ => ⟨4, by decide⟩ | ⟨4, _⟩ => ⟨3, by decide⟩ | ⟨5, _⟩ => ⟨7, by decide⟩
  | ⟨6, _⟩ => ⟨8, by decide⟩ | ⟨7, _⟩ => ⟨5, by decide⟩ | ⟨8, _⟩ => ⟨5, by decide⟩
  | ⟨9, _⟩ => ⟨6, by decide⟩

private def n3 : Fin 10 → Fin 10
  | ⟨0, _⟩ => ⟨5, by decide⟩ | ⟨1, _⟩ => ⟨6, by decide⟩ | ⟨2, _⟩ => ⟨7, by decide⟩
  | ⟨3, _⟩ => ⟨8, by decide⟩ | ⟨4, _⟩ => ⟨9, by decide⟩ | ⟨5, _⟩ => ⟨8, by decide⟩
  | ⟨6, _⟩ => ⟨9, by decide⟩ | ⟨7, _⟩ => ⟨9, by decide⟩ | ⟨8, _⟩ => ⟨6, by decide⟩
  | ⟨9, _⟩ => ⟨7, by decide⟩

private lemma adjB_irrefl (u : Fin 10) : adjB u u = false := by revert u; decide
private lemma adjB_symm (u v : Fin 10) : adjB u v = adjB v u := by revert u v; decide
private lemma adjB_iff_n (u v : Fin 10) : adjB u v = true ↔ v = n1 u ∨ v = n2 u ∨ v = n3 u := by
  revert u v; decide

private def get10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Fin 10 → Bool
  | ⟨0, _⟩ => b0 | ⟨1, _⟩ => b1 | ⟨2, _⟩ => b2 | ⟨3, _⟩ => b3 | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5 | ⟨6, _⟩ => b6 | ⟨7, _⟩ => b7 | ⟨8, _⟩ => b8 | ⟨9, _⟩ => b9

private def isAct (alive : Fin 10 → Bool) (v : Fin 10) : Bool :=
  alive v && (alive (n1 v) || alive (n2 v) || alive (n3 v))

private def actCnt (alive : Fin 10 → Bool) : Nat :=
  b2n (isAct alive ⟨0, by decide⟩) + b2n (isAct alive ⟨1, by decide⟩) +
  b2n (isAct alive ⟨2, by decide⟩) + b2n (isAct alive ⟨3, by decide⟩) +
  b2n (isAct alive ⟨4, by decide⟩) + b2n (isAct alive ⟨5, by decide⟩) +
  b2n (isAct alive ⟨6, by decide⟩) + b2n (isAct alive ⟨7, by decide⟩) +
  b2n (isAct alive ⟨8, by decide⟩) + b2n (isAct alive ⟨9, by decide⟩)

private def isActR1 (alive : Fin 10 → Bool) (u v : Fin 10) : Bool :=
  alive v && (v != u) &&
  (adjB u v ||
    (let w := n1 v; alive w && (w != u) && !(adjB u w)) ||
    (let w := n2 v; alive w && (w != u) && !(adjB u w)) ||
    (let w := n3 v; alive w && (w != u) && !(adjB u w)))

private def actR1Cnt (alive : Fin 10 → Bool) (u : Fin 10) : Nat :=
  b2n (isActR1 alive u ⟨0, by decide⟩) + b2n (isActR1 alive u ⟨1, by decide⟩) +
  b2n (isActR1 alive u ⟨2, by decide⟩) + b2n (isActR1 alive u ⟨3, by decide⟩) +
  b2n (isActR1 alive u ⟨4, by decide⟩) + b2n (isActR1 alive u ⟨5, by decide⟩) +
  b2n (isActR1 alive u ⟨6, by decide⟩) + b2n (isActR1 alive u ⟨7, by decide⟩) +
  b2n (isActR1 alive u ⟨8, by decide⟩) + b2n (isActR1 alive u ⟨9, by decide⟩)

private def noBad (alive : Fin 10 → Bool) : Bool :=
  (List.finRange 10).all fun u =>
    if isAct alive u then
      (List.finRange 10).all fun v =>
        if u.val < v.val && isAct alive v then
          ((alive (n1 v) && (n1 v != u)) || (alive (n2 v) && (n2 v != u)) || (alive (n3 v) && (n3 v != u)) ||
           (alive (n1 u) && (n1 u != v)) || (alive (n2 u) && (n2 u != v)) || (alive (n3 u) && (n3 u != v))) &&
          (isActR1 alive u v || isActR1 alive v u)
        else true
    else true

private def check10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Bool :=
  let dead := b2n (!b0) + b2n (!b1) + b2n (!b2) + b2n (!b3) + b2n (!b4) +
              b2n (!b5) + b2n (!b6) + b2n (!b7) + b2n (!b8) + b2n (!b9)
  if dead ≤ 3 then
    let alive := get10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
    decide (6 ≤ actCnt alive) && noBad alive
  else if dead == 4 then
    let alive := get10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
    let ac := actCnt alive
    if decide (6 ≤ ac) then true
    else
      decide (5 ≤ ac) && noBad alive &&
      (List.finRange 10).all fun u =>
        if isAct alive u then
          let alive0 := fun w => if w == u then false else alive w
          let a0 := actCnt alive0
          let a1 := actR1Cnt alive u
          decide (1 ≤ a0) && decide (1 ≤ a1) && (decide (4 ≤ a0) || decide (4 ≤ a1))
        else true
  else true

private lemma h_check10 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
      check10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 = true := by
  decide

private def petSub (D : Finset (Fin 10)) (x : Fin 10 → Bool) : Bool :=
  (List.finRange 10).any fun u =>
    (List.finRange 10).any fun v =>
      decide (u ∉ D ∧ v ∉ D) && adjB u v && x u && x v

private lemma petSub_eq_true (D : Finset (Fin 10)) (x : Fin 10 → Bool) :
    petSub D x = true ↔ ∃ u v : Fin 10, u ∉ D ∧ v ∉ D ∧ adjB u v = true ∧ x u = true ∧ x v = true := by
  simp only [petSub, List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨u, v, ⟨⟨⟨hu, hv⟩, hadj⟩, hxu⟩, hxv⟩
    exact ⟨u, v, hu, hv, hadj, hxu, hxv⟩
  · rintro ⟨u, v, hu, hv, hadj, hxu, hxv⟩
    exact ⟨u, v, ⟨⟨⟨hu, hv⟩, hadj⟩, hxu⟩, hxv⟩

private lemma petSub_empty (x : Fin 10 → Bool) : petSub ∅ x = petFun x := by
  apply Bool.eq_iff_iff.mpr
  rw [petSub_eq_true]
  simp only [Finset.notMem_empty, not_false_eq_true, true_and]
  have hpet : ∀ u v : Fin 10, adjB u v = true →
      (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨
      (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
      (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) ∨
      (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 3) ∨
      (u = 4 ∧ v = 0) ∨ (u = 0 ∧ v = 4) ∨
      (u = 0 ∧ v = 5) ∨ (u = 5 ∧ v = 0) ∨
      (u = 1 ∧ v = 6) ∨ (u = 6 ∧ v = 1) ∨
      (u = 2 ∧ v = 7) ∨ (u = 7 ∧ v = 2) ∨
      (u = 3 ∧ v = 8) ∨ (u = 8 ∧ v = 3) ∨
      (u = 4 ∧ v = 9) ∨ (u = 9 ∧ v = 4) ∨
      (u = 5 ∧ v = 7) ∨ (u = 7 ∧ v = 5) ∨
      (u = 7 ∧ v = 9) ∨ (u = 9 ∧ v = 7) ∨
      (u = 9 ∧ v = 6) ∨ (u = 6 ∧ v = 9) ∨
      (u = 6 ∧ v = 8) ∨ (u = 8 ∧ v = 6) ∨
      (u = 8 ∧ v = 5) ∨ (u = 5 ∧ v = 8) := by
    intro u v
    fin_cases u <;> fin_cases v <;> decide
  simp only [petFun, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨u, v, hadj, hxu, hxv⟩
    rcases hpet u v hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp_all
  · intro h
    rcases h with ((((((((((((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) |
      ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact ⟨0, 1, by decide, h1, h2⟩
    · exact ⟨1, 2, by decide, h1, h2⟩
    · exact ⟨2, 3, by decide, h1, h2⟩
    · exact ⟨3, 4, by decide, h1, h2⟩
    · exact ⟨4, 0, by decide, h1, h2⟩
    · exact ⟨0, 5, by decide, h1, h2⟩
    · exact ⟨1, 6, by decide, h1, h2⟩
    · exact ⟨2, 7, by decide, h1, h2⟩
    · exact ⟨3, 8, by decide, h1, h2⟩
    · exact ⟨4, 9, by decide, h1, h2⟩
    · exact ⟨5, 7, by decide, h1, h2⟩
    · exact ⟨7, 9, by decide, h1, h2⟩
    · exact ⟨9, 6, by decide, h1, h2⟩
    · exact ⟨6, 8, by decide, h1, h2⟩
    · exact ⟨8, 5, by decide, h1, h2⟩

private def restrict (f : (Fin 10 → Bool) → Bool) (v : Fin 10) (b : Bool) : (Fin 10 → Bool) → Bool :=
  fun x => f (Function.update x v b)

private lemma restrict_petSub_false (D : Finset (Fin 10)) (w : Fin 10) :
    restrict (petSub D) w false = petSub (insert w D) := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [restrict, petSub_eq_true, Finset.mem_insert, not_or]
  constructor
  · rintro ⟨u, v, hu, hv, hadj, hxu, hxv⟩
    have huw : u ≠ w := by rintro rfl; simp at hxu
    have hvw : v ≠ w := by rintro rfl; simp at hxv
    simp [Function.update, huw, hvw] at hxu hxv
    exact ⟨u, v, ⟨huw, hu⟩, ⟨hvw, hv⟩, hadj, hxu, hxv⟩
  · rintro ⟨u, v, ⟨huw, hu⟩, ⟨hvw, hv⟩, hadj, hxu, hxv⟩
    exact ⟨u, v, hu, hv, hadj, by simp [Function.update, huw, hxu], by simp [Function.update, hvw, hxv]⟩

private def DependsOn (f : (Fin 10 → Bool) → Bool) (v : Fin 10) : Prop :=
  ∃ x : Fin 10 → Bool, f (Function.update x v false) ≠ f (Function.update x v true)

private def NonConst (f : (Fin 10 → Bool) → Bool) : Prop :=
  ∃ x y : Fin 10 → Bool, f x ≠ f y

private lemma dependsOn_nonConst {f : (Fin 10 → Bool) → Bool} {v : Fin 10}
    (h : DependsOn f v) : NonConst f := by
  obtain ⟨x, hx⟩ := h
  exact ⟨Function.update x v false, Function.update x v true, hx⟩

private lemma not_dependsOn_eq {f : (Fin 10 → Bool) → Bool} {v : Fin 10}
    (h : ¬ DependsOn f v) (x : Fin 10 → Bool) :
    f (Function.update x v false) = f x := by
  have hall : ∀ y : Fin 10 → Bool, f (Function.update y v false) = f (Function.update y v true) := by
    intro y; by_contra hne; exact h ⟨y, hne⟩
  cases hxv : x v
  · rw [show Function.update x v false = x by ext i; by_cases hi : i = v <;> simp [Function.update, hi, hxv]]
  · rw [hall x, show Function.update x v true = x by ext i; by_cases hi : i = v <;> simp [Function.update, hi, hxv]]

private def readList (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

private def reads (g : Gate) (w : ℕ) : Prop :=
  w ∈ readList g

private lemma readList_length_le (g : Gate) (h : g.inputs.length ≤ 2) :
    (readList g).length ≤ 2 := by
  cases ho : g.op <;> simp [readList, ho] <;> omega

private lemma gateOp_eval_readList (g : Gate) (val : ℕ → Bool) :
    g.op.eval (g.inputs.map val) = g.op.eval ((readList g).map val) := by
  cases ho : g.op with
  | not =>
    cases hi : g.inputs with
    | nil => simp [readList, ho, hi]
    | cons a as => simp [readList, ho, hi, GateOp.eval]
  | and => simp [readList, ho]
  | or => simp [readList, ho]
  | mod m => simp [readList, ho]
  | maj => simp [readList, ho]

private lemma gateOp_eval_congr (g : Gate) (v1 v2 : ℕ → Bool)
    (h : ∀ w, reads g w → v1 w = v2 w) :
    g.op.eval (g.inputs.map v1) = g.op.eval (g.inputs.map v2) := by
  rw [gateOp_eval_readList, gateOp_eval_readList]
  congr 1
  apply List.map_congr_left
  intro w hw
  exact h w hw

private lemma getD_append_singleton (l : List Bool) (v : Bool) (k : ℕ) :
    (l ++ [v]).getD k false = if k = l.length then v else l.getD k false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with heq
  · subst heq; simp
  · by_cases hlt : k < l.length
    · rw [List.getElem?_append_left hlt]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

private lemma getD_of_ge (l : List Bool) (k : ℕ) (hk : l.length ≤ k) :
    l.getD k false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

private lemma getD_ofFn (x : Fin 10 → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < 10 then x ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact h), Option.getD_some, List.getElem_ofFn]
  · rw [List.getElem?_eq_none (by rw [List.length_ofFn]; omega)]; rfl

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWire, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    rw [stepWire, getD_append_singleton]
    have hne : i ≠ w.length := Nat.ne_of_lt hi
    simp [hne]

private lemma list_split_at {α : Type*} (l : List α) (j : ℕ) (hj : j < l.length) :
    l = l.take j ++ l[j] :: l.drop (j + 1) := by
  have h1 := (List.take_append_drop j l).symm
  have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
  rw [h2] at h1
  exact h1

private def shiftIdx (k w : ℕ) : ℕ :=
  if w < k then w else w - 1

private def remapGate (f : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map f }

private lemma fanInTwo_remapGate (f : ℕ → ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (remapGate f g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (remapGate f g).inputs.length ≤ 2 := by
  simpa [remapGate] using hg

private def substConstGate (w : ℕ) (b : Bool) (g : Gate) : Gate :=
  match g.op with
  | .and =>
    if w ∈ g.inputs then
      if b then { op := .and, inputs := g.inputs.filter (fun i => decide (i ≠ w)) }
      else { op := .or, inputs := [] }
    else g
  | .or =>
    if w ∈ g.inputs then
      if b then { op := .and, inputs := [] }
      else { op := .or, inputs := g.inputs.filter (fun i => decide (i ≠ w)) }
    else g
  | .not =>
    match g.inputs with
    | a :: _ => if a = w then { op := if b then .or else .and, inputs := [] } else g
    | [] => g
  | _ => g

private def TrivialGate (g : Gate) : Prop :=
  g.inputs = [] ∨ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 1)

private lemma fanInTwo_substConstGate (w : ℕ) (b : Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (substConstGate w b g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (substConstGate w b g).inputs.length ≤ 2 := by
  rcases hg with ⟨hop, hlen⟩
  cases ho : g.op
  · simp only [substConstGate, ho]
    split_ifs
    · exact ⟨by simp, (List.length_filter_le _ _).trans hlen⟩
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simpa [ho] using hop, hlen⟩
  · simp only [substConstGate, ho]
    split_ifs
    · exact ⟨by simp, by simp⟩
    · exact ⟨by simp, (List.length_filter_le _ _).trans hlen⟩
    · exact ⟨by simpa [ho] using hop, hlen⟩
  · simp only [substConstGate, ho]
    cases hi : g.inputs with
    | nil => exact ⟨by simpa [ho] using hop, by simp [hi]⟩
    | cons a as =>
      by_cases haw : a = w
      · simp only [haw, ↓reduceIte]
        cases b <;> simp
      · simp only [haw, ↓reduceIte]
        exact ⟨by simpa [ho] using hop, by simpa [hi] using hlen⟩
  · simp [ho] at hop
  · simp [ho] at hop

private lemma substConstGate_not_reads (w : ℕ) (b : Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    ¬ reads (substConstGate w b g) w := by
  cases ho : g.op
  · simp only [substConstGate, ho]
    split_ifs with h1 h2
    · simp [reads, readList]
    · simp [reads, readList]
    · simpa [reads, readList, ho] using h1
  · simp only [substConstGate, ho]
    split_ifs with h1 h2
    · simp [reads, readList]
    · simp [reads, readList]
    · simpa [reads, readList, ho] using h1
  · simp only [substConstGate, ho]
    cases hi : g.inputs with
    | nil => simp [reads, readList, ho, hi]
    | cons a as =>
      by_cases haw : a = w
      · simp only [haw, ↓reduceIte]
        cases b <;> simp [reads, readList]
      · simp only [haw, ↓reduceIte]
        simp [reads, readList, ho, hi, Ne.symm haw]
  · simp [ho] at hg
  · simp [ho] at hg

private lemma substConstGate_trivial_of_reads (w : ℕ) (b : Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hr : reads g w) :
    TrivialGate (substConstGate w b g) := by
  rcases hg with ⟨hop, hlen⟩
  cases ho : g.op
  · have hw : w ∈ g.inputs := by simpa [reads, readList, ho] using hr
    simp only [substConstGate, ho, hw, ↓reduceIte]
    split_ifs
    · have hlt : (g.inputs.filter (fun i => decide (i ≠ w))).length < g.inputs.length := by
        apply List.length_filter_lt_length_iff_exists.mpr
        exact ⟨w, hw, by simp⟩
      have hle1 : (g.inputs.filter (fun i => decide (i ≠ w))).length ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
      · exact Or.inl (List.eq_nil_of_length_eq_zero h0)
      · exact Or.inr ⟨Or.inl rfl, h1⟩
    · exact Or.inl rfl
  · have hw : w ∈ g.inputs := by simpa [reads, readList, ho] using hr
    simp only [substConstGate, ho, hw, ↓reduceIte]
    split_ifs
    · exact Or.inl rfl
    · have hlt : (g.inputs.filter (fun i => decide (i ≠ w))).length < g.inputs.length := by
        apply List.length_filter_lt_length_iff_exists.mpr
        exact ⟨w, hw, by simp⟩
      have hle1 : (g.inputs.filter (fun i => decide (i ≠ w))).length ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
      · exact Or.inl (List.eq_nil_of_length_eq_zero h0)
      · exact Or.inr ⟨Or.inr rfl, h1⟩
  · cases hi : g.inputs with
    | nil => simp [reads, readList, ho, hi] at hr
    | cons a as =>
      have haw : a = w := by simp [reads, readList, ho, hi] at hr; exact hr.symm
      simp [substConstGate, ho, hi, haw, TrivialGate]
  · simp [ho] at hop
  · simp [ho] at hop

private lemma substConstGate_preserves_trivial (w : ℕ) (b : Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (ht : TrivialGate g) :
    TrivialGate (substConstGate w b g) := by
  by_cases hr : reads g w
  · exact substConstGate_trivial_of_reads w b g hg hr
  · rcases hg with ⟨hop, _⟩
    cases ho : g.op
    · have hw : w ∉ g.inputs := by simpa [reads, readList, ho] using hr
      simpa [substConstGate, ho, hw] using ht
    · have hw : w ∉ g.inputs := by simpa [reads, readList, ho] using hr
      simpa [substConstGate, ho, hw] using ht
    · cases hi : g.inputs with
      | nil => simpa [substConstGate, ho, hi] using ht
      | cons a as =>
        have hne : a ≠ w := fun h => hr (by simp [reads, readList, ho, hi, h])
        simpa [substConstGate, ho, hi, hne] using ht
    · simp [ho] at hop
    · simp [ho] at hop

private lemma remapGate_preserves_trivial (f : ℕ → ℕ) (g : Gate) (ht : TrivialGate g) :
    TrivialGate (remapGate f g) := by
  rcases ht with hnil | ⟨hop, hlen⟩
  · exact Or.inl (by simp [remapGate, hnil])
  · exact Or.inr ⟨hop, by simp [remapGate, hlen]⟩

private lemma substConstGate_eval (w : ℕ) (b : Bool) (g : Gate)
    (val : ℕ → Bool) (hval : val w = b)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (substConstGate w b g).op.eval ((substConstGate w b g).inputs.map val)
      = g.op.eval (g.inputs.map val) := by
  cases ho : g.op
  · simp only [substConstGate, ho]
    split_ifs with h1 h2
    · subst h2
      simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.mem_filter, decide_eq_true_eq]
      constructor
      · intro h i hi
        by_cases hiw : i = w
        · subst hiw; exact hval
        · exact h i ⟨hi, hiw⟩
      · intro h i hi; exact h i hi.1
    · have hbf : b = false := Bool.eq_false_iff.mpr h2
      subst hbf
      simp only [GateOp.eval, List.map_nil, List.any_nil]
      symm
      rw [Bool.eq_false_iff]
      intro hall
      rw [List.all_eq_true] at hall
      have := hall (val w) (List.mem_map_of_mem h1)
      simp [hval] at this
    · simp [ho]
  · simp only [substConstGate, ho]
    split_ifs with h1 h2
    · subst h2
      simp only [GateOp.eval, List.map_nil, List.all_nil]
      symm
      rw [List.any_eq_true]
      exact ⟨val w, List.mem_map_of_mem h1, by simp [hval]⟩
    · have hbf : b = false := Bool.eq_false_iff.mpr h2
      subst hbf
      simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨i, ⟨hi, _⟩, hvi⟩; exact ⟨i, hi, hvi⟩
      · rintro ⟨i, hi, hvi⟩
        by_cases hiw : i = w
        · subst hiw; simp [hval] at hvi
        · exact ⟨i, ⟨hi, hiw⟩, hvi⟩
    · simp [ho]
  · simp only [substConstGate, ho]
    cases hi : g.inputs with
    | nil => simp [ho, hi]
    | cons a as =>
      by_cases haw : a = w
      · subst haw
        simp only [↓reduceIte]
        cases b <;> simp [GateOp.eval, hval]
      · simp [ho, hi, haw]
  · simp [ho] at hop
  · simp [ho] at hop

private lemma foldl_shift_after (k : ℕ) (gs : List Gate) (hno : ∀ g ∈ gs, ¬ reads g k)
    (w_old w_new : List Bool) (t : ℕ)
    (hl_old : w_old.length = k + 1 + t) (hl_new : w_new.length = k + t)
    (hinv : ∀ i, i ≠ k → w_new.getD (shiftIdx k i) false = w_old.getD i false) :
    ∀ i, i ≠ k →
      ((gs.map (remapGate (shiftIdx k))).foldl stepWire w_new).getD (shiftIdx k i) false
        = (gs.foldl stepWire w_old).getD i false := by
  induction gs generalizing t w_old w_new with
  | nil => exact hinv
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg_no : ¬ reads g k := hno g (List.mem_cons_self ..)
    have hval :
        (remapGate (shiftIdx k) g).op.eval ((remapGate (shiftIdx k) g).inputs.map (fun i => w_new.getD i false))
          = g.op.eval (g.inputs.map (fun i => w_old.getD i false)) := by
      simp only [remapGate, List.map_map]
      apply gateOp_eval_congr g
      intro i hi
      exact hinv i (fun heq => hg_no (heq ▸ hi))
    have hstep : stepWire w_new (remapGate (shiftIdx k) g) =
        w_new ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)] := by
      simp only [stepWire, hval]
    rw [hstep]
    set v := g.op.eval (g.inputs.map fun i => w_old.getD i false)
    have hstep_old : stepWire w_old g = w_old ++ [v] := rfl
    rw [hstep_old]
    apply ih (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
      (w_old ++ [v]) (w_new ++ [v]) (t + 1)
      (by simp [List.length_append, hl_old]; omega)
      (by simp [List.length_append, hl_new]; omega)
    intro i hne
    rw [getD_append_singleton, getD_append_singleton, hl_old, hl_new]
    by_cases hlt : i < k
    · have hsh : shiftIdx k i = i := by simp [shiftIdx, hlt]
      have hne1 : i ≠ k + 1 + t := by omega
      have hne2 : shiftIdx k i ≠ k + t := by rw [hsh]; omega
      simp only [hne1, hne2, ↓reduceIte, hinv i hne]
    · have hgt : k < i := by omega
      have hsh : shiftIdx k i = i - 1 := by simp [shiftIdx, hlt]
      by_cases heq : i = k + 1 + t
      · subst heq
        have hsh' : shiftIdx k (k + 1 + t) = k + t := by simp [shiftIdx]; omega
        simp only [hsh', ↓reduceIte]
      · have hne2 : shiftIdx k i ≠ k + t := by rw [hsh]; omega
        simp only [heq, hne2, ↓reduceIte, hinv i hne]

private def remapIdx (k u w : ℕ) : ℕ :=
  if w = k then u else shiftIdx k w

private lemma foldl_remap_after (k u : ℕ) (hu : u < k) (gs : List Gate)
    (w_old w_new : List Bool) (t : ℕ)
    (hl_old : w_old.length = k + 1 + t) (hl_new : w_new.length = k + t)
    (hinv : ∀ i, w_new.getD (remapIdx k u i) false = w_old.getD i false) :
    ∀ i,
      ((gs.map (remapGate (remapIdx k u))).foldl stepWire w_new).getD (remapIdx k u i) false
        = (gs.foldl stepWire w_old).getD i false := by
  induction gs generalizing t w_old w_new with
  | nil => exact hinv
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hval :
        (remapGate (remapIdx k u) g).op.eval ((remapGate (remapIdx k u) g).inputs.map (fun i => w_new.getD i false))
          = g.op.eval (g.inputs.map (fun i => w_old.getD i false)) := by
      simp only [remapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _; exact hinv i
    have hstep : stepWire w_new (remapGate (remapIdx k u) g) =
        w_new ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)] := by
      simp only [stepWire, hval]
    rw [hstep]
    set v := g.op.eval (g.inputs.map fun i => w_old.getD i false)
    have hstep_old : stepWire w_old g = w_old ++ [v] := rfl
    rw [hstep_old]
    apply ih (w_old ++ [v]) (w_new ++ [v]) (t + 1)
      (by simp [List.length_append, hl_old]; omega)
      (by simp [List.length_append, hl_new]; omega)
    intro i
    rw [getD_append_singleton, getD_append_singleton, hl_old, hl_new]
    by_cases hik : i = k
    · rw [hik]
      have hne1 : k ≠ k + 1 + t := by omega
      have hrm : remapIdx k u k = u := by simp [remapIdx]
      have hne2 : remapIdx k u k ≠ k + t := by rw [hrm]; omega
      simp only [hne1, hne2, ↓reduceIte, hinv k]
    · by_cases hlt : i < k
      · have hrm : remapIdx k u i = i := by simp [remapIdx, hik, shiftIdx, hlt]
        have hne1 : i ≠ k + 1 + t := by omega
        have hne2 : remapIdx k u i ≠ k + t := by rw [hrm]; omega
        simp only [hne1, hne2, ↓reduceIte, hinv i]
      · have hgt : k < i := by omega
        have hrm : remapIdx k u i = i - 1 := by simp [remapIdx, hik, shiftIdx, hlt]
        by_cases heq : i = k + 1 + t
        · subst heq
          have hrm' : remapIdx k u (k + 1 + t) = k + t := by rw [hrm]; omega
          simp only [hrm', ↓reduceIte]
        · have hne2 : remapIdx k u i ≠ k + t := by rw [hrm]; omega
          simp only [heq, hne2, ↓reduceIte, hinv i]

private lemma elimDead (C : Circuit) (hF : FanInTwo C) (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output ≠ 10 + j)
    (hdead : ∀ k, j < k → (hk : k < C.gates.length) → ¬ reads C.gates[k] (10 + j)) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size - 1 ∧
      ∀ x : Fin 10 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let gs1 := C.gates.take j
  let gs2 := C.gates.drop (j + 1)
  let C' : Circuit := {
    gates := gs1 ++ gs2.map (remapGate (shiftIdx (10 + j)))
    output := shiftIdx (10 + j) C.output
  }
  refine ⟨C', ?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg1 | hg2
    · exact hF g (List.mem_of_mem_take hg1)
    · rw [List.mem_map] at hg2
      obtain ⟨g0, hg0, rfl⟩ := hg2
      exact fanInTwo_remapGate _ g0 (hF g0 (List.mem_of_mem_drop hg0))
  · simp [C', Circuit.size, gs1, gs2, List.length_take, List.length_drop]; omega
  · intro x
    simp only [Circuit.eval, wires_eq_foldl, C']
    have hsplit : C.gates = gs1 ++ C.gates[j] :: gs2 := list_split_at C.gates j hj
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons]
    set w0 := gs1.foldl stepWire (List.ofFn x)
    have hw0 : w0.length = 10 + j := by
      simp [w0, foldl_stepWire_length, gs1, List.length_take]; omega
    have hno : ∀ g ∈ gs2, ¬ reads g (10 + j) := by
      intro g hg
      rw [List.mem_iff_getElem] at hg
      obtain ⟨m, hm, rfl⟩ := hg
      have hlt : j + 1 + m < C.gates.length := by simp [gs2] at hm; omega
      have hget : gs2[m] = C.gates[j + 1 + m] := List.getElem_drop
      rw [hget]
      exact hdead (j + 1 + m) (by omega) hlt
    exact foldl_shift_after (10 + j) gs2 hno (stepWire w0 C.gates[j]) w0 0
      (by simp [stepWire, List.length_append, hw0]) (by omega)
      (fun i hi => by
        rw [stepWire, getD_append_singleton, hw0]
        by_cases hlt : i < 10 + j
        · simp [shiftIdx, hlt, hi]
        · have hsh : shiftIdx (10 + j) i = i - 1 := by simp [shiftIdx, hlt]
          rw [hsh, getD_of_ge w0 (i - 1) (by omega), getD_of_ge w0 i (by omega)]
          simp [hi])
      C.output hout

private lemma elimAlias (C : Circuit) (hF : FanInTwo C) (j : ℕ) (hj : j < C.gates.length)
    (u : ℕ) (hu : u < 10 + j)
    (halias : ∀ x : Fin 10 → Bool,
      let w0 := (C.gates.take j).foldl stepWire (List.ofFn x)
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => w0.getD i false) = w0.getD u false) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size - 1 ∧
      (∀ x : Fin 10 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ m, (hm : m < C'.gates.length) →
        j ≤ m → (hm' : m + 1 < C.gates.length) → TrivialGate C.gates[m + 1] → TrivialGate C'.gates[m]) := by
  let gs1 := C.gates.take j
  let gs2 := C.gates.drop (j + 1)
  let C' : Circuit := {
    gates := gs1 ++ gs2.map (remapGate (remapIdx (10 + j) u))
    output := remapIdx (10 + j) u C.output
  }
  have hlen' : C'.gates.length = C.gates.length - 1 := by
    simp [C', gs1, gs2, List.length_take, List.length_drop]; omega
  refine ⟨C', ?_, hlen', ?_, ?_⟩
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg1 | hg2
    · exact hF g (List.mem_of_mem_take hg1)
    · rw [List.mem_map] at hg2
      obtain ⟨g0, hg0, rfl⟩ := hg2
      exact fanInTwo_remapGate _ g0 (hF g0 (List.mem_of_mem_drop hg0))
  · intro x
    simp only [Circuit.eval, wires_eq_foldl, C']
    have hsplit : C.gates = gs1 ++ C.gates[j] :: gs2 := list_split_at C.gates j hj
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons]
    set w0 := gs1.foldl stepWire (List.ofFn x)
    have hw0 : w0.length = 10 + j := by
      simp [w0, foldl_stepWire_length, gs1, List.length_take]; omega
    exact foldl_remap_after (10 + j) u hu gs2 (stepWire w0 C.gates[j]) w0 0
      (by simp [stepWire, List.length_append, hw0]) (by omega)
      (fun i => by
        rw [stepWire, getD_append_singleton, hw0]
        by_cases hik : i = 10 + j
        · subst hik
          simp only [remapIdx, ↓reduceIte]
          exact (halias x).symm
        · by_cases hlt : i < 10 + j
          · simp only [remapIdx, hik, shiftIdx, hlt, ↓reduceIte]
          · simp only [remapIdx, hik, ↓reduceIte, shiftIdx, hlt]
            rw [getD_of_ge w0 (i - 1) (by omega), getD_of_ge w0 i (by omega)])
      C.output
  · intro m hm hge hm' htriv
    have hgs1_len : gs1.length = j := by simp [gs1, List.length_take]; omega
    have h1 : C'.gates[m] = (gs2.map (remapGate (remapIdx (10 + j) u)))[m - j]'(by simp [gs2, List.length_drop]; omega) := by
      have := List.getElem_append_right (as := gs1) (bs := gs2.map (remapGate (remapIdx (10 + j) u))) (i := m) (h₂ := hm) (by omega)
      simpa [C', hgs1_len] using this
    rw [h1, List.getElem_map]
    have h2 : gs2[m - j]'(by simp [gs2, List.length_drop]; omega) = C.gates[m + 1] := by
      simp only [gs2, List.getElem_drop]; congr 1; omega
    rw [h2]
    exact remapGate_preserves_trivial _ _ htriv

private lemma elimConst (C : Circuit) (hF : FanInTwo C) (j : ℕ) (hj : j < C.gates.length)
    (b : Bool) (hout : C.output ≠ 10 + j)
    (hconst : ∀ x : Fin 10 → Bool,
      let w0 := (C.gates.take j).foldl stepWire (List.ofFn x)
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => w0.getD i false) = b) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size - 1 ∧
      (∀ x : Fin 10 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ m, (hm : m < C'.gates.length) →
        (j ≤ m → (hm' : m + 1 < C.gates.length) → TrivialGate C.gates[m + 1] → TrivialGate C'.gates[m]) ∧
        (j ≤ m → (hm' : m + 1 < C.gates.length) → reads C.gates[m + 1] (10 + j) → TrivialGate C'.gates[m])) := by
  let gs1 := C.gates.take j
  let gs2 := C.gates.drop (j + 1)
  let gs2s := gs2.map (substConstGate (10 + j) b)
  let C' : Circuit := {
    gates := gs1 ++ gs2s.map (remapGate (shiftIdx (10 + j)))
    output := shiftIdx (10 + j) C.output
  }
  have hlen' : C'.gates.length = C.gates.length - 1 := by
    simp [C', gs1, gs2s, gs2, List.length_take, List.length_drop]; omega
  refine ⟨C', ?_, hlen', ?_, ?_⟩
  · intro g hg
    rw [List.mem_append] at hg
    rcases hg with hg1 | hg2
    · exact hF g (List.mem_of_mem_take hg1)
    · rw [List.mem_map] at hg2
      obtain ⟨g1, hg1, rfl⟩ := hg2
      rw [List.mem_map] at hg1
      obtain ⟨g0, hg0, rfl⟩ := hg1
      exact fanInTwo_remapGate _ _ (fanInTwo_substConstGate _ _ g0 (hF g0 (List.mem_of_mem_drop hg0)))
  · intro x
    simp only [Circuit.eval, wires_eq_foldl, C']
    have hsplit : C.gates = gs1 ++ C.gates[j] :: gs2 := list_split_at C.gates j hj
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons]
    set w0 := gs1.foldl stepWire (List.ofFn x)
    have hw0 : w0.length = 10 + j := by
      simp [w0, foldl_stepWire_length, gs1, List.length_take]; omega
    have hstep_b : stepWire w0 C.gates[j] = w0 ++ [b] := by
      simp only [stepWire]
      exact congrArg (fun v => w0 ++ [v]) (hconst x)
    have hsub_eq : gs2s.foldl stepWire (w0 ++ [b]) = gs2.foldl stepWire (w0 ++ [b]) := by
      have hgen : ∀ (l : List Gate) (hl : ∀ g ∈ l, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
          (w : List Bool) (hw_len : 10 + j < w.length) (hw_b : w.getD (10 + j) false = b),
          (l.map (substConstGate (10 + j) b)).foldl stepWire w = l.foldl stepWire w := by
        intro l
        induction l with
        | nil => intros; rfl
        | cons g l ih =>
          intro hl w hw_len hw_b
          simp only [List.map_cons, List.foldl_cons]
          have hg_op := hl g (List.mem_cons_self ..)
          have hev : stepWire w (substConstGate (10 + j) b g) = stepWire w g := by
            simp only [stepWire]
            rw [substConstGate_eval (10 + j) b g (fun i => w.getD i false) hw_b hg_op]
          rw [hev]
          apply ih (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) (stepWire w g)
            (by simp only [stepWire, List.length_append, List.length_singleton]; omega)
          rw [stepWire, getD_append_singleton]
          have hne : 10 + j ≠ w.length := Nat.ne_of_lt hw_len
          simp only [hne, ↓reduceIte, hw_b]
      apply hgen gs2 (fun g hg => (hF g (List.mem_of_mem_drop hg)).1) (w0 ++ [b])
        (by simp [List.length_append, hw0]) (by rw [getD_append_singleton, hw0]; simp)
    rw [hstep_b, ← hsub_eq]
    have hno : ∀ g ∈ gs2s, ¬ reads g (10 + j) := by
      intro g hg
      rw [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact substConstGate_not_reads (10 + j) b g0 (hF g0 (List.mem_of_mem_drop hg0)).1
    exact foldl_shift_after (10 + j) gs2s hno (w0 ++ [b]) w0 0
      (by simp [List.length_append, hw0]) (by omega)
      (fun i hi => by
        rw [getD_append_singleton, hw0]
        by_cases hlt : i < 10 + j
        · simp only [shiftIdx, hlt, hi, ↓reduceIte]
        · have hsh : shiftIdx (10 + j) i = i - 1 := by simp [shiftIdx, hlt]
          rw [hsh, getD_of_ge w0 (i - 1) (by omega), getD_of_ge w0 i (by omega)]
          simp [hi])
      C.output hout
  · intro m hm
    have hgs1_len : gs1.length = j := by simp [gs1, List.length_take]; omega
    refine ⟨?_, ?_⟩
    · intro hge hm' htriv
      have h1 : C'.gates[m] = (gs2s.map (remapGate (shiftIdx (10 + j))))[m - j]'(by simp [gs2s, gs2, List.length_drop]; omega) := by
        have := List.getElem_append_right (as := gs1) (bs := gs2s.map (remapGate (shiftIdx (10 + j)))) (i := m) (h₂ := hm) (by omega)
        simpa [C', hgs1_len] using this
      rw [h1, List.getElem_map, List.getElem_map]
      have h2 : gs2[m - j]'(by simp [gs2, List.length_drop]; omega) = C.gates[m + 1] := by
        simp only [gs2, List.getElem_drop]; congr 1; omega
      rw [h2]
      exact remapGate_preserves_trivial _ _
        (substConstGate_preserves_trivial _ _ _ (hF _ (List.getElem_mem hm')) htriv)
    · intro hge hm' hreads
      have h1 : C'.gates[m] = (gs2s.map (remapGate (shiftIdx (10 + j))))[m - j]'(by simp [gs2s, gs2, List.length_drop]; omega) := by
        have := List.getElem_append_right (as := gs1) (bs := gs2s.map (remapGate (shiftIdx (10 + j)))) (i := m) (h₂ := hm) (by omega)
        simpa [C', hgs1_len] using this
      rw [h1, List.getElem_map, List.getElem_map]
      have h2 : gs2[m - j]'(by simp [gs2, List.length_drop]; omega) = C.gates[m + 1] := by
        simp only [gs2, List.getElem_drop]; congr 1; omega
      rw [h2]
      exact remapGate_preserves_trivial _ _
        (substConstGate_trivial_of_reads _ _ _ (hF _ (List.getElem_mem hm')) hreads)

private lemma output_ne_of_const_gate (C : Circuit) (f : (Fin 10 → Bool) → Bool)
    (heval : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f x)
    (hnc : NonConst f) (j : ℕ) (hj : j < C.gates.length) (b : Bool)
    (hconst : ∀ x : Fin 10 → Bool,
      let w0 := (C.gates.take j).foldl stepWire (List.ofFn x)
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => w0.getD i false) = b) :
    C.output ≠ 10 + j := by
  intro hout
  obtain ⟨x, y, hxy⟩ := hnc
  have hval (z : Fin 10 → Bool) : f z = b := by
    rw [← heval z, Circuit.eval, wires_eq_foldl, hout]
    have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := list_split_at C.gates j hj
    rw [hsplit, List.foldl_append, List.foldl_cons]
    set w0 := (C.gates.take j).foldl stepWire (List.ofFn z)
    have hw0 : w0.length = 10 + j := by
      simp [w0, foldl_stepWire_length, List.length_take]; omega
    rw [foldl_stepWire_getD_lt _ (stepWire w0 C.gates[j]) (10 + j)
      (by simp only [stepWire, List.length_append, List.length_singleton, hw0]; omega)]
    rw [stepWire, getD_append_singleton, hw0]
    simp only [↓reduceIte]
    exact hconst z
  exact hxy ((hval x).trans (hval y).symm)

private lemma elimTrivial (C : Circuit) (hF : FanInTwo C) (f : (Fin 10 → Bool) → Bool)
    (heval : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f x)
    (hnc : NonConst f) (j : ℕ) (hj : j < C.gates.length) (ht : TrivialGate C.gates[j]) :
    ∃ C' : Circuit, FanInTwo C' ∧ C'.size = C.size - 1 ∧
      (∀ x : Fin 10 → Bool, C'.eval (List.ofFn x) = f x) ∧
      (∀ m, (hm : m < C'.gates.length) →
        j ≤ m → (hm' : m + 1 < C.gates.length) → TrivialGate C.gates[m + 1] → TrivialGate C'.gates[m]) := by
  rcases ht with hnil | ⟨hop, hlen1⟩
  · set b := C.gates[j].op.eval []
    have hconst : ∀ x : Fin 10 → Bool,
        let w0 := (C.gates.take j).foldl stepWire (List.ofFn x)
        C.gates[j].op.eval (C.gates[j].inputs.map fun i => w0.getD i false) = b := by
      intro x; simp [b, hnil]
    have hout := output_ne_of_const_gate C f heval hnc j hj b hconst
    obtain ⟨C', hF', hsz', hev', htr⟩ := elimConst C hF j hj b hout hconst
    exact ⟨C', hF', hsz', fun x => (hev' x).trans (heval x), fun m hm => (htr m hm).1⟩
  · cases hgi : C.gates[j].inputs with
    | nil => simp [hgi] at hlen1
    | cons u us =>
      simp [hgi] at hlen1
      subst hlen1
      have hev_u : ∀ x : Fin 10 → Bool,
          let w0 := (C.gates.take j).foldl stepWire (List.ofFn x)
          C.gates[j].op.eval (C.gates[j].inputs.map fun i => w0.getD i false) = w0.getD u false := by
        intro x
        simp only [hgi, List.map_cons, List.map_nil]
        rcases hop with h | h <;> simp [h, GateOp.eval]
      by_cases hu : u < 10 + j
      · obtain ⟨C', hF', hsz', hev', htr⟩ := elimAlias C hF j hj u hu hev_u
        exact ⟨C', hF', hsz', fun x => (hev' x).trans (heval x), htr⟩
      · have hconst : ∀ x : Fin 10 → Bool,
            let w0 := (C.gates.take j).foldl stepWire (List.ofFn x)
            C.gates[j].op.eval (C.gates[j].inputs.map fun i => w0.getD i false) = false := by
          intro x
          have h1 := hev_u x
          dsimp only at h1 ⊢
          rw [h1]
          apply getD_of_ge
          simp [foldl_stepWire_length, List.length_take]; omega
        have hout := output_ne_of_const_gate C f heval hnc j hj false hconst
        obtain ⟨C', hF', hsz', hev', htr⟩ := elimConst C hF j hj false hout hconst
        exact ⟨C', hF', hsz', fun x => (hev' x).trans (heval x), fun m hm => (htr m hm).1⟩

private lemma plugInput (C : Circuit) (hF : FanInTwo C) (v : Fin 10) (b : Bool)
    (hout : C.output ≠ v.val) :
    let C1 : Circuit := { gates := C.gates.map (substConstGate v.val b), output := C.output }
    FanInTwo C1 ∧ C1.size = C.size ∧
      ∀ x : Fin 10 → Bool, C1.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b)) := by
  intro C1
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact fanInTwo_substConstGate _ _ g0 (hF g0 hg0)
  · simp [C1, Circuit.size]
  · intro x
    simp only [Circuit.eval, wires_eq_foldl, C1]
    have hgen : ∀ (gs : List Gate) (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
        (w1 w2 : List Bool) (hl1 : w1.length = w2.length) (hge : 10 ≤ w1.length)
        (hv2 : w2.getD v.val false = b)
        (hagree : ∀ i, i ≠ v.val → w1.getD i false = w2.getD i false),
        ∀ i, i ≠ v.val →
          ((gs.map (substConstGate v.val b)).foldl stepWire w1).getD i false
            = (gs.foldl stepWire w2).getD i false := by
      intro gs
      induction gs with
      | nil => intro _ w1 w2 _ _ _ hagree i hi; exact hagree i hi
      | cons g gs ih =>
        intro hgs w1 w2 hl1 hge hv2 hagree i hi
        simp only [List.map_cons, List.foldl_cons]
        have hg_op := hgs g (List.mem_cons_self ..)
        have hnot := substConstGate_not_reads v.val b g hg_op
        have hev1 :
            (substConstGate v.val b g).op.eval ((substConstGate v.val b g).inputs.map fun k => w1.getD k false)
              = (substConstGate v.val b g).op.eval ((substConstGate v.val b g).inputs.map fun k => w2.getD k false) := by
          apply gateOp_eval_congr
          intro k hk
          exact hagree k (fun h => hnot (h ▸ hk))
        have hev2 := substConstGate_eval v.val b g (fun k => w2.getD k false) hv2 hg_op
        have hval_eq := hev1.trans hev2
        apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
          (stepWire w1 (substConstGate v.val b g)) (stepWire w2 g)
          (by simp [stepWire, List.length_append, hl1])
          (by simp [stepWire, List.length_append]; omega)
          (by
            rw [stepWire, getD_append_singleton]
            have hne : v.val ≠ w2.length := by omega
            simp only [hne, ↓reduceIte, hv2])
          (by
            intro k hk
            rw [stepWire, stepWire, getD_append_singleton, getD_append_singleton, hl1, hval_eq]
            split_ifs
            · rfl
            · exact hagree k hk)
          i hi
    apply hgen C.gates (fun g hg => (hF g hg).1) (List.ofFn x) (List.ofFn (Function.update x v b))
      (by simp) (by simp)
      (by rw [getD_ofFn]; simp [v.isLt])
      (by
        intro i hi
        rw [getD_ofFn, getD_ofFn]
        split_ifs with hlt
        · have hne : (⟨i, hlt⟩ : Fin 10) ≠ v := fun h => hi (congrArg Fin.val h)
          simp [Function.update, hne]
        · rfl)
      C.output hout

private lemma eval_indep_of_not_read (C : Circuit) (v : Fin 10)
    (hout : C.output ≠ v.val) (hno : ∀ g ∈ C.gates, ¬ reads g v.val) :
    ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (Function.update x v false)) = C.eval (List.ofFn (Function.update x v true)) := by
  intro x
  simp only [Circuit.eval, wires_eq_foldl]
  have hgen : ∀ (gs : List Gate) (hgs : ∀ g ∈ gs, ¬ reads g v.val)
      (w1 w2 : List Bool) (hl : w1.length = w2.length)
      (hagree : ∀ i, i ≠ v.val → w1.getD i false = w2.getD i false),
      ∀ i, i ≠ v.val → (gs.foldl stepWire w1).getD i false = (gs.foldl stepWire w2).getD i false := by
    intro gs
    induction gs with
    | nil => intro _ w1 w2 _ hagree i hi; exact hagree i hi
    | cons g gs ih =>
      intro hgs w1 w2 hl hagree i hi
      simp only [List.foldl_cons]
      have hg := hgs g (List.mem_cons_self ..)
      have hev : g.op.eval (g.inputs.map fun k => w1.getD k false) =
          g.op.eval (g.inputs.map fun k => w2.getD k false) := by
        apply gateOp_eval_congr
        intro k hk
        exact hagree k (fun h => hg (h ▸ hk))
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (stepWire w1 g) (stepWire w2 g)
        (by simp [stepWire, List.length_append, hl])
        (by
          intro k hk
          rw [stepWire, stepWire, getD_append_singleton, getD_append_singleton, hl, hev]
          split_ifs
          · rfl
          · exact hagree k hk)
        i hi
  apply hgen C.gates hno (List.ofFn (Function.update x v false)) (List.ofFn (Function.update x v true))
    (by simp)
    (by
      intro i hi
      rw [getD_ofFn, getD_ofFn]
      split_ifs with hlt
      · have hne : (⟨i, hlt⟩ : Fin 10) ≠ v := fun h => hi (congrArg Fin.val h)
        simp [Function.update, hne]
      · rfl)
    C.output hout

private lemma eval_gate0_indep (C : Circuit) (u v : Fin 10) (b : Bool)
    (hout : C.output ≠ v.val)
    (h0 : 0 < C.gates.length)
    (hg0 : ∀ x : Fin 10 → Bool,
      C.gates[0].op.eval (C.gates[0].inputs.map fun i => (List.ofFn (Function.update x u b)).getD i false) =
        C.gates[0].op.eval (C.gates[0].inputs.map fun i => (List.ofFn (Function.update (Function.update x v false) u b)).getD i false))
    (hrest : ∀ k, 0 < k → (hk : k < C.gates.length) → ¬ reads C.gates[k] v.val) :
    ¬ DependsOn (restrict (fun x => C.eval (List.ofFn x)) u b) v := by
  rintro ⟨x, hx⟩
  apply hx
  simp only [restrict, Circuit.eval, wires_eq_foldl]
  have hsplit : C.gates = C.gates[0] :: C.gates.drop 1 := by
    simpa using list_split_at C.gates 0 h0
  rw [hsplit, List.foldl_cons, List.foldl_cons]
  have hgen : ∀ (gs : List Gate) (hgs : ∀ g ∈ gs, ¬ reads g v.val)
      (w1 w2 : List Bool) (hl : w1.length = w2.length)
      (hagree : ∀ i, i ≠ v.val → w1.getD i false = w2.getD i false),
      ∀ i, i ≠ v.val → (gs.foldl stepWire w1).getD i false = (gs.foldl stepWire w2).getD i false := by
    intro gs
    induction gs with
    | nil => intro _ w1 w2 _ hagree i hi; exact hagree i hi
    | cons g gs ih =>
      intro hgs w1 w2 hl hagree i hi
      simp only [List.foldl_cons]
      have hg := hgs g (List.mem_cons_self ..)
      have hev : g.op.eval (g.inputs.map fun k => w1.getD k false) =
          g.op.eval (g.inputs.map fun k => w2.getD k false) := by
        apply gateOp_eval_congr
        intro k hk
        exact hagree k (fun h => hg (h ▸ hk))
      apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (stepWire w1 g) (stepWire w2 g)
        (by simp [stepWire, List.length_append, hl])
        (by
          intro k hk
          rw [stepWire, stepWire, getD_append_singleton, getD_append_singleton, hl, hev]
          split_ifs
          · rfl
          · exact hagree k hk)
        i hi
  have hno_drop : ∀ g ∈ C.gates.drop 1, ¬ reads g v.val := by
    intro g hg
    rw [List.mem_iff_getElem] at hg
    obtain ⟨m, hm, rfl⟩ := hg
    have hlt : 1 + m < C.gates.length := by simp at hm; omega
    have hget : (C.gates.drop 1)[m] = C.gates[1 + m] := List.getElem_drop
    rw [hget]
    exact hrest (1 + m) (by omega) hlt
  have hval0 :
      C.gates[0].op.eval (C.gates[0].inputs.map fun i => (List.ofFn (Function.update (Function.update x v false) u b)).getD i false)
        = C.gates[0].op.eval (C.gates[0].inputs.map fun i => (List.ofFn (Function.update (Function.update x v true) u b)).getD i false) := by
    have h1 := hg0 (Function.update x v true)
    have h2 : Function.update (Function.update (Function.update x v true) v false) u b
        = Function.update (Function.update x v false) u b := by
      ext i
      by_cases hiu : i = u
      · subst hiu; simp [Function.update]
      · by_cases hiv : i = v
        · subst hiv; simp [Function.update, hiu]
        · simp [Function.update, hiu, hiv]
    rw [h2] at h1
    exact h1.symm
  apply hgen (C.gates.drop 1) hno_drop
    (stepWire (List.ofFn (Function.update (Function.update x v false) u b)) C.gates[0])
    (stepWire (List.ofFn (Function.update (Function.update x v true) u b)) C.gates[0])
    (by simp [stepWire, List.length_append])
    (by
      intro i hi
      rw [stepWire, stepWire, getD_append_singleton, getD_append_singleton]
      simp only [List.length_ofFn]
      split_ifs
      · exact hval0
      · rw [getD_ofFn, getD_ofFn]
        split_ifs with hlt
        · have hne : (⟨i, hlt⟩ : Fin 10) ≠ v := fun h => hi (congrArg Fin.val h)
          by_cases hiu : (⟨i, hlt⟩ : Fin 10) = u
          · simp [Function.update, hiu]
          · simp [Function.update, hiu, hne]
        · rfl)
    C.output hout

private def MinSize (f : (Fin 10 → Bool) → Bool) (s : ℕ) : Prop :=
  HasCircuitSize 10 f s ∧ ∀ s' < s, ¬ HasCircuitSize 10 f s'

private lemma exists_minSize {f : (Fin 10 → Bool) → Bool} {s : ℕ} (h : HasCircuitSize 10 f s) :
    ∃ s' ≤ s, MinSize f s' := by
  classical
  refine ⟨Nat.find (⟨s, h⟩ : ∃ k, HasCircuitSize 10 f k), Nat.find_min' _ h,
    Nat.find_spec (⟨s, h⟩ : ∃ k, HasCircuitSize 10 f k), fun k hk => Nat.find_min _ hk⟩

private lemma active_card_le_size_add_one {f : (Fin 10 → Bool) → Bool} {s : ℕ}
    (hmin : MinSize f s) (S : Finset (Fin 10)) (hS : ∀ v ∈ S, DependsOn f v) (hS2 : 2 ≤ S.card) :
    S.card ≤ s + 1 := by
  classical
  obtain ⟨C, hF, hsz, hev⟩ := hmin.1
  have hCsz : C.size = s := by
    by_contra hne
    exact hmin.2 C.size (by omega) ⟨C, hF, Nat.le_refl _, hev⟩
  have hout_ge : 10 ≤ C.output := by
    by_contra hlt
    push_neg at hlt
    let v0 : Fin 10 := ⟨C.output, hlt⟩
    have hex : ∃ v ∈ S, v ≠ v0 := by
      have : (S.erase v0).Nonempty := by
        rw [← Finset.card_pos]
        have := Finset.pred_card_le_card_erase (s := S) (a := v0)
        omega
      obtain ⟨v, hv⟩ := this
      exact ⟨v, Finset.mem_of_mem_erase hv, Finset.ne_of_mem_erase hv⟩
    obtain ⟨v, hvS, hvv0⟩ := hex
    obtain ⟨x, hx⟩ := hS v hvS
    apply hx
    rw [← hev, ← hev, Circuit.eval, Circuit.eval, wires_eq_foldl, wires_eq_foldl]
    rw [foldl_stepWire_getD_lt C.gates (List.ofFn _) C.output (by rw [List.length_ofFn]; exact hlt)]
    rw [foldl_stepWire_getD_lt C.gates (List.ofFn _) C.output (by rw [List.length_ofFn]; exact hlt)]
    rw [getD_ofFn, getD_ofFn]
    have hne : (⟨C.output, hlt⟩ : Fin 10) ≠ v := hvv0.symm
    simp [hlt, Function.update, hne]
  have hout_lt : C.output < 10 + C.gates.length := by
    by_contra hge
    push_neg at hge
    obtain ⟨v, hvS⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    obtain ⟨x, hx⟩ := hS v hvS
    apply hx
    rw [← hev, ← hev, Circuit.eval, Circuit.eval, wires_eq_foldl, wires_eq_foldl]
    rw [getD_of_ge _ C.output (by rw [foldl_stepWire_length]; simp; omega)]
    rw [getD_of_ge _ C.output (by rw [foldl_stepWire_length]; simp; omega)]
  let U : Finset ℕ := (C.gates.flatMap readList).toFinset
  have hU_card : U.card ≤ 2 * C.gates.length := by
    have hsum_le : (C.gates.map (fun g => (readList g).length)).sum ≤ (C.gates.map (fun _ => 2)).sum := by
      have hgen : ∀ (l : List Gate), (∀ g ∈ l, (readList g).length ≤ 2) →
          (l.map (fun g => (readList g).length)).sum ≤ (l.map (fun _ => 2)).sum := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons g l ih =>
          intro hl
          simp only [List.map_cons, List.sum_cons]
          have h1 := hl g (List.mem_cons_self ..)
          have h2 := ih (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))
          omega
      exact hgen C.gates (fun g hg => readList_length_le g (hF g hg).2)
    have hsum2 : (C.gates.map (fun _ => 2)).sum = 2 * C.gates.length := by
      have hgen : ∀ (l : List Gate), (l.map (fun _ => 2)).sum = 2 * l.length := by
        intro l; induction l with
        | nil => simp
        | cons _ l ih => simp [ih]; omega
      exact hgen C.gates
    calc U.card ≤ (C.gates.flatMap readList).length := List.toFinset_card_le _
      _ = (C.gates.map (fun g => (readList g).length)).sum := List.length_flatMap
      _ ≤ (C.gates.map (fun _ => 2)).sum := hsum_le
      _ = 2 * C.gates.length := hsum2
  let W1 : Finset ℕ := S.image Fin.val
  let W2 : Finset ℕ := ((Finset.range C.gates.length).image (fun j => 10 + j)).erase C.output
  have hdisj : Disjoint W1 W2 := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    simp only [W1, Finset.mem_image] at ha1
    simp only [W2, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at ha2
    obtain ⟨v, _, rfl⟩ := ha1
    obtain ⟨_, j, _, hj⟩ := ha2
    omega
  have hW1_sub : W1 ⊆ U := by
    intro a ha
    simp only [W1, Finset.mem_image] at ha
    obtain ⟨v, hvS, rfl⟩ := ha
    by_contra hnot
    have hno : ∀ g ∈ C.gates, ¬ reads g v.val := by
      intro g hg hr
      apply hnot
      simp only [U, List.mem_toFinset, List.mem_flatMap]
      exact ⟨g, hg, hr⟩
    obtain ⟨x, hx⟩ := hS v hvS
    apply hx
    rw [← hev, ← hev]
    exact eval_indep_of_not_read C v (by omega) hno x
  have hW2_sub : W2 ⊆ U := by
    intro a ha
    simp only [W2, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at ha
    obtain ⟨hne, j, hj, rfl⟩ := ha
    by_contra hnot
    have hdead : ∀ k, j < k → (hk : k < C.gates.length) → ¬ reads C.gates[k] (10 + j) := by
      intro k _ hk hr
      apply hnot
      simp only [U, List.mem_toFinset, List.mem_flatMap]
      exact ⟨C.gates[k], List.getElem_mem hk, hr⟩
    obtain ⟨C', hF', hsz', hev'⟩ := elimDead C hF j hj hne.symm hdead
    have hlt : C'.size < s := by simp [Circuit.size] at hCsz hsz' ⊢; omega
    exact hmin.2 C'.size hlt ⟨C', hF', Nat.le_refl _, fun x => (hev' x).trans (hev x)⟩
  have hsub : W1 ∪ W2 ⊆ U := Finset.union_subset hW1_sub hW2_sub
  have hW1_card : W1.card = S.card := Finset.card_image_of_injective S Fin.val_injective
  have hmem_out : C.output ∈ (Finset.range C.gates.length).image (fun j => 10 + j) := by
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨C.output - 10, by omega, by omega⟩
  have hW2_card : W2.card = C.gates.length - 1 := by
    rw [Finset.card_erase_of_mem hmem_out,
      Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hW1_card, hW2_card] at hle
  have hpos : 1 ≤ C.gates.length := by omega
  simp only [Circuit.size] at hCsz
  omega

private lemma two_gate_elim {f : (Fin 10 → Bool) → Bool} {s : ℕ}
    (hmin : MinSize f s) (S : Finset (Fin 10))
    (hS : ∀ v : Fin 10, v ∈ S ↔ DependsOn f v)
    (hS3 : 3 ≤ S.card)
    (hno3 : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      DependsOn (restrict f u false) v ∨ DependsOn (restrict f v false) u)
    (hno4 : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      DependsOn (restrict f u true) v ∨ DependsOn (restrict f v true) u) :
    ∃ v ∈ S,
      (NonConst (restrict f v false) → HasCircuitSize 10 (restrict f v false) (s - 2)) ∧
      (NonConst (restrict f v true) → HasCircuitSize 10 (restrict f v true) (s - 2)) := by
  classical
  obtain ⟨C, hF, hsz, hev⟩ := hmin.1
  have hCsz : C.size = s := by
    by_contra hne
    exact hmin.2 C.size (by omega) ⟨C, hF, Nat.le_refl _, hev⟩
  have hs2 : 2 ≤ s := by
    have := active_card_le_size_add_one hmin S (fun v hv => (hS v).mp hv) (by omega)
    omega
  have h0 : 0 < C.gates.length := by simp [Circuit.size] at hCsz; omega
  have hnc_f : NonConst f := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    exact dependsOn_nonConst ((hS v).mp hv)
  have hout_ge10 : 10 ≤ C.output := by
    by_contra hlt
    push_neg at hlt
    let v0 : Fin 10 := ⟨C.output, hlt⟩
    have : (S.erase v0).Nonempty := by
      rw [← Finset.card_pos]
      have := Finset.pred_card_le_card_erase (s := S) (a := v0)
      omega
    obtain ⟨v, hv⟩ := this
    obtain ⟨x, hx⟩ := (hS v).mp (Finset.mem_of_mem_erase hv)
    apply hx
    rw [← hev, ← hev, Circuit.eval, Circuit.eval, wires_eq_foldl, wires_eq_foldl]
    rw [foldl_stepWire_getD_lt C.gates (List.ofFn _) C.output (by rw [List.length_ofFn]; exact hlt)]
    rw [foldl_stepWire_getD_lt C.gates (List.ofFn _) C.output (by rw [List.length_ofFn]; exact hlt)]
    rw [getD_ofFn, getD_ofFn]
    have hne : (⟨C.output, hlt⟩ : Fin 10) ≠ v := Ne.symm (Finset.ne_of_mem_erase hv)
    simp [hlt, Function.update, hne]
  have hnot_triv0 : ¬ TrivialGate C.gates[0] := by
    intro ht
    obtain ⟨C', hF', hsz', hev', _⟩ := elimTrivial C hF f hev hnc_f 0 h0 ht
    exact hmin.2 C'.size (by omega) ⟨C', hF', Nat.le_refl _, hev'⟩
  have hread0_lt10 : ∀ w, reads C.gates[0] w → w < 10 := by
    intro w hr
    by_contra hge
    push_neg at hge
    let g0' := substConstGate w false C.gates[0]
    let C1 : Circuit := { gates := g0' :: C.gates.drop 1, output := C.output }
    have hF1 : FanInTwo C1 := by
      intro g hg
      rw [List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact fanInTwo_substConstGate _ _ _ (hF _ (List.getElem_mem h0))
      · exact hF g (List.mem_of_mem_drop hg)
    have hev1 : ∀ x : Fin 10 → Bool, C1.eval (List.ofFn x) = f x := by
      intro x
      rw [← hev x]
      simp only [Circuit.eval, wires_eq_foldl, C1]
      have hsplit : C.gates = C.gates[0] :: C.gates.drop 1 := by
        simpa using list_split_at C.gates 0 h0
      conv_rhs => rw [hsplit]
      simp only [List.foldl_cons]
      have hstep : stepWire (List.ofFn x) g0' = stepWire (List.ofFn x) C.gates[0] := by
        simp only [stepWire, g0']
        rw [substConstGate_eval w false C.gates[0] (fun i => (List.ofFn x).getD i false)
          (getD_of_ge _ w (by simp; omega)) (hF _ (List.getElem_mem h0)).1]
      rw [hstep]
    have hC1_0 : 0 < C1.gates.length := by simp [C1]
    have htr1 : TrivialGate C1.gates[0] :=
      substConstGate_trivial_of_reads w false C.gates[0] (hF _ (List.getElem_mem h0)) hr
    obtain ⟨C', hF', hsz', hev', _⟩ := elimTrivial C1 hF1 f hev1 hnc_f 0 hC1_0 htr1
    have hsz1 : C1.size = C.size := by simp [C1, Circuit.size]; omega
    exact hmin.2 C'.size (by omega) ⟨C', hF', Nat.le_refl _, hev'⟩
  have hread0_inS : ∀ w, (hw : w < 10) → reads C.gates[0] w → (⟨w, hw⟩ : Fin 10) ∈ S := by
    intro w hw hr
    by_contra hnot
    have hnd : ¬ DependsOn f ⟨w, hw⟩ := fun hd => hnot ((hS _).mpr hd)
    obtain ⟨hF1, hsz1, hev1⟩ := plugInput C hF ⟨w, hw⟩ false (by omega)
    let C1 : Circuit := { gates := C.gates.map (substConstGate w false), output := C.output }
    have hsz1' : C1.size = C.size := hsz1
    have hev1' : ∀ x : Fin 10 → Bool, C1.eval (List.ofFn x) = f x := by
      intro x; rw [hev1 x, hev, not_dependsOn_eq hnd x]
    have hC1_0 : 0 < C1.gates.length := by simp [C1]; omega
    have htr1 : TrivialGate C1.gates[0] := by
      simp only [C1, List.getElem_map]
      exact substConstGate_trivial_of_reads w false C.gates[0] (hF _ (List.getElem_mem h0)) hr
    obtain ⟨C', hF', hsz', hev', _⟩ := elimTrivial C1 hF1 f hev1' hnc_f 0 hC1_0 htr1
    exact hmin.2 C'.size (by omega) ⟨C', hF', Nat.le_refl _, hev'⟩
  have hout_ne10 : C.output ≠ 10 := by
    intro hout10
    let S0 : Finset (Fin 10) := (readList C.gates[0]).attach.toFinset.image
      (fun p => ⟨p.1, hread0_lt10 p.1 p.2⟩)
    have hS0_card : S0.card ≤ 2 := by
      calc S0.card ≤ (readList C.gates[0]).attach.toFinset.card := Finset.card_image_le
        _ ≤ (readList C.gates[0]).attach.length := List.toFinset_card_le _
        _ = (readList C.gates[0]).length := List.length_attach
        _ ≤ 2 := readList_length_le _ (hF _ (List.getElem_mem h0)).2
    have hdiff : (S \ S0).Nonempty := by
      rw [← Finset.card_pos]
      have := Finset.card_sdiff_add_card_inter S S0
      have := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := S0))
      omega
    obtain ⟨v, hv⟩ := hdiff
    rw [Finset.mem_sdiff] at hv
    obtain ⟨hvS, hvS0⟩ := hv
    have hv_nread : ¬ reads C.gates[0] v.val := by
      intro hr
      apply hvS0
      simp only [S0, Finset.mem_image, List.mem_toFinset, List.mem_attach, true_and]
      exact ⟨⟨v.val, hr⟩, rfl⟩
    obtain ⟨x, hx⟩ := (hS v).mp hvS
    apply hx
    rw [← hev, ← hev, Circuit.eval, Circuit.eval, wires_eq_foldl, wires_eq_foldl, hout10]
    have hsplit : C.gates = C.gates[0] :: C.gates.drop 1 := by
      simpa using list_split_at C.gates 0 h0
    rw [hsplit, List.foldl_cons, List.foldl_cons]
    rw [foldl_stepWire_getD_lt _ (stepWire _ _) 10 (by simp [stepWire, List.length_append])]
    rw [foldl_stepWire_getD_lt _ (stepWire _ _) 10 (by simp [stepWire, List.length_append])]
    rw [stepWire, stepWire, getD_append_singleton, getD_append_singleton]
    simp only [List.length_ofFn, ↓reduceIte]
    apply gateOp_eval_congr
    intro w hr
    have hne : w ≠ v.val := fun h => hv_nread (h ▸ hr)
    rw [getD_ofFn, getD_ofFn]
    split_ifs with hlt
    · have hne' : (⟨w, hlt⟩ : Fin 10) ≠ v := fun h => hne (congrArg Fin.val h)
      simp [Function.update, hne']
    · rfl
  have hex_cons0 : ∃ k, 0 < k ∧ ∃ hk : k < C.gates.length, reads C.gates[k] 10 := by
    by_contra hno
    push_neg at hno
    obtain ⟨C', hF', hsz', hev'⟩ := elimDead C hF 0 h0 hout_ne10 hno
    exact hmin.2 C'.size (by omega) ⟨C', hF', Nat.le_refl _, fun x => (hev' x).trans (hev x)⟩
  have hfan2_step : ∀ v ∈ S, (∃ k, 0 < k ∧ ∃ hk : k < C.gates.length, reads C.gates[k] v.val) →
      reads C.gates[0] v.val →
      (NonConst (restrict f v false) → HasCircuitSize 10 (restrict f v false) (s - 2)) ∧
      (NonConst (restrict f v true) → HasCircuitSize 10 (restrict f v true) (s - 2)) := by
    intro v _ ⟨k, hk0, hk, hreadk⟩ hread0
    have hbranch : ∀ b : Bool, NonConst (restrict f v b) →
        HasCircuitSize 10 (restrict f v b) (s - 2) := by
      intro b hnc_b
      obtain ⟨hF1, hsz1, hev1⟩ := plugInput C hF v b (by omega)
      let C1 : Circuit := { gates := C.gates.map (substConstGate v.val b), output := C.output }
      have hsz1' : C1.size = C.size := hsz1
      have hev1' : ∀ x : Fin 10 → Bool, C1.eval (List.ofFn x) = restrict f v b x := by
        intro x; rw [hev1 x, hev]; rfl
      have hC1_0 : 0 < C1.gates.length := by simp [C1]; omega
      have hC1_k : k < C1.gates.length := by simp [C1]; omega
      have htr0 : TrivialGate C1.gates[0] := by
        simp only [C1, List.getElem_map]
        exact substConstGate_trivial_of_reads v.val b C.gates[0] (hF _ (List.getElem_mem h0)) hread0
      have htrk : TrivialGate C1.gates[k] := by
        simp only [C1, List.getElem_map]
        exact substConstGate_trivial_of_reads v.val b C.gates[k] (hF _ (List.getElem_mem hk)) hreadk
      obtain ⟨C2, hF2, hsz2, hev2, htr2⟩ := elimTrivial C1 hF1 (restrict f v b) hev1' hnc_b 0 hC1_0 htr0
      have hk1 : k - 1 < C2.gates.length := by simp [Circuit.size, C1] at hsz2 ⊢; omega
      have hk1' : k - 1 + 1 < C1.gates.length := by omega
      have htrk2 : TrivialGate C2.gates[k - 1] := by
        have hkeq : k - 1 + 1 = k := by omega
        exact htr2 (k - 1) hk1 (by omega) hk1' (by simpa [hkeq] using htrk)
      obtain ⟨C3, hF3, hsz3, hev3, _⟩ := elimTrivial C2 hF2 (restrict f v b) hev2 hnc_b (k - 1) hk1 htrk2
      exact ⟨C3, hF3, by omega, hev3⟩
    exact ⟨hbranch false, hbranch true⟩
  have hconst0_step : ∀ (v : Fin 10) (b : Bool),
      (substConstGate v.val b C.gates[0]).inputs = [] →
      NonConst (restrict f v b) → HasCircuitSize 10 (restrict f v b) (s - 2) := by
    intro v b hnil hnc_b
    obtain ⟨k, hk0, hk, hreadk⟩ := hex_cons0
    obtain ⟨hF1, hsz1, hev1⟩ := plugInput C hF v b (by omega)
    let C1 : Circuit := { gates := C.gates.map (substConstGate v.val b), output := C.output }
    have hsz1' : C1.size = C.size := hsz1
    have hev1' : ∀ x : Fin 10 → Bool, C1.eval (List.ofFn x) = restrict f v b x := by
      intro x; rw [hev1 x, hev]; rfl
    have hC1_0 : 0 < C1.gates.length := by simp [C1]; omega
    have hC1_k : k < C1.gates.length := by simp [C1]; omega
    have hnil1 : C1.gates[0].inputs = [] := by simp [C1, hnil]
    set bc := C1.gates[0].op.eval []
    have hconst1 : ∀ x : Fin 10 → Bool,
        let w0 := (C1.gates.take 0).foldl stepWire (List.ofFn x)
        C1.gates[0].op.eval (C1.gates[0].inputs.map fun i => w0.getD i false) = bc := by
      intro x; simp [bc, hnil1]
    have hout1 := output_ne_of_const_gate C1 (restrict f v b) hev1' hnc_b 0 hC1_0 bc hconst1
    obtain ⟨C2, hF2, hsz2, hev2, htr2⟩ := elimConst C1 hF1 0 hC1_0 bc hout1 hconst1
    have hk1 : k - 1 < C2.gates.length := by simp [Circuit.size, C1] at hsz2 ⊢; omega
    have hk1' : k - 1 + 1 < C1.gates.length := by omega
    have htr_or_reads : TrivialGate C1.gates[k] ∨ reads C1.gates[k] 10 := by
      by_cases hkv : reads C.gates[k] v.val
      · left
        simp only [C1, List.getElem_map]
        exact substConstGate_trivial_of_reads v.val b C.gates[k] (hF _ (List.getElem_mem hk)) hkv
      · right
        simp only [C1, List.getElem_map]
        have hgop := (hF _ (List.getElem_mem hk)).1
        cases ho : C.gates[k].op
        · have hw : v.val ∉ C.gates[k].inputs := by simpa [reads, readList, ho] using hkv
          simpa [substConstGate, ho, hw] using hreadk
        · have hw : v.val ∉ C.gates[k].inputs := by simpa [reads, readList, ho] using hkv
          simpa [substConstGate, ho, hw] using hreadk
        · cases hi : C.gates[k].inputs with
          | nil => simp [reads, readList, ho, hi] at hreadk
          | cons a as =>
            have hne : a ≠ v.val := fun h => hkv (by simp [reads, readList, ho, hi, h])
            simpa [substConstGate, ho, hi, hne] using hreadk
        · simp [ho] at hgop
        · simp [ho] at hgop
    have htrk2 : TrivialGate C2.gates[k - 1] := by
      have hkeq : k - 1 + 1 = k := by omega
      rcases htr_or_reads with htr | hrd
      · exact (htr2 (k - 1) hk1).1 (by omega) hk1' (by simpa [hkeq] using htr)
      · exact (htr2 (k - 1) hk1).2 (by omega) hk1' (by simpa [hkeq] using hrd)
    obtain ⟨C3, hF3, hsz3, hev3, _⟩ := elimTrivial C2 hF2 (restrict f v b)
      (fun x => (hev2 x).trans (hev1' x)) hnc_b (k - 1) hk1 htrk2
    exact ⟨C3, hF3, by omega, hev3⟩
  have hg0_F := hF C.gates[0] (List.getElem_mem h0)
  cases ho : C.gates[0].op
  · cases hi : C.gates[0].inputs with
    | nil => exact absurd (Or.inl hi) hnot_triv0
    | cons a as =>
      cases as with
      | nil => exact absurd (Or.inr ⟨Or.inl ho, by simp [hi]⟩) hnot_triv0
      | cons b bs =>
        cases bs with
        | nil =>
          have hra : reads C.gates[0] a := by simp [reads, readList, ho, hi]
          have hrb : reads C.gates[0] b := by simp [reads, readList, ho, hi]
          have ha10 := hread0_lt10 a hra
          have hb10 := hread0_lt10 b hrb
          let u : Fin 10 := ⟨a, ha10⟩
          let v : Fin 10 := ⟨b, hb10⟩
          have huS : u ∈ S := hread0_inS a ha10 hra
          have hvS : v ∈ S := hread0_inS b hb10 hrb
          have huv : u ≠ v := by
            intro heq
            have hab : a = b := congrArg Fin.val heq
            subst hab
            have halias : ∀ x : Fin 10 → Bool,
                let w0 := (C.gates.take 0).foldl stepWire (List.ofFn x)
                C.gates[0].op.eval (C.gates[0].inputs.map fun i => w0.getD i false) = w0.getD a false := by
              intro x; simp [ho, hi, GateOp.eval]
            obtain ⟨C', hF', hsz', hev', _⟩ := elimAlias C hF 0 h0 a ha10 halias
            exact hmin.2 C'.size (by omega) ⟨C', hF', Nat.le_refl _, fun x => (hev' x).trans (hev x)⟩
          by_cases hu2 : ∃ k, 0 < k ∧ ∃ hk : k < C.gates.length, reads C.gates[k] u.val
          · exact ⟨u, huS, hfan2_step u huS hu2 hra⟩
          · by_cases hv2 : ∃ k, 0 < k ∧ ∃ hk : k < C.gates.length, reads C.gates[k] v.val
            · exact ⟨v, hvS, hfan2_step v hvS hv2 hrb⟩
            · exfalso
              push_neg at hu2 hv2
              have hind_v : ¬ DependsOn (restrict f u false) v := by
                have hreq : restrict f u false = restrict (fun x => C.eval (List.ofFn x)) u false := by
                  funext x; exact (hev (Function.update x u false)).symm
                rw [hreq]
                apply eval_gate0_indep C u v false (by omega) h0
                · intro x
                  simp only [ho, hi, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
                    List.all_nil, id_eq, Bool.and_true, getD_ofFn, ha10, ↓reduceDIte]
                  have hu_eq : (⟨a, ha10⟩ : Fin 10) = u := rfl
                  simp [hu_eq, Function.update]
                · exact hv2
              have hind_u : ¬ DependsOn (restrict f v false) u := by
                have hreq : restrict f v false = restrict (fun x => C.eval (List.ofFn x)) v false := by
                  funext x; exact (hev (Function.update x v false)).symm
                rw [hreq]
                apply eval_gate0_indep C v u false (by omega) h0
                · intro x
                  simp only [ho, hi, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
                    List.all_nil, id_eq, Bool.and_true, getD_ofFn, hb10, ↓reduceDIte]
                  have hv_eq : (⟨b, hb10⟩ : Fin 10) = v := rfl
                  simp [hv_eq, Function.update]
                · exact hu2
              rcases hno3 u huS v hvS huv with h1 | h2
              · exact hind_v h1
              · exact hind_u h2
        | cons c cs => have := hg0_F.2; simp [hi] at this
  · cases hi : C.gates[0].inputs with
    | nil => exact absurd (Or.inl hi) hnot_triv0
    | cons a as =>
      cases as with
      | nil => exact absurd (Or.inr ⟨Or.inr ho, by simp [hi]⟩) hnot_triv0
      | cons b bs =>
        cases bs with
        | nil =>
          have hra : reads C.gates[0] a := by simp [reads, readList, ho, hi]
          have hrb : reads C.gates[0] b := by simp [reads, readList, ho, hi]
          have ha10 := hread0_lt10 a hra
          have hb10 := hread0_lt10 b hrb
          let u : Fin 10 := ⟨a, ha10⟩
          let v : Fin 10 := ⟨b, hb10⟩
          have huS : u ∈ S := hread0_inS a ha10 hra
          have hvS : v ∈ S := hread0_inS b hb10 hrb
          have huv : u ≠ v := by
            intro heq
            have hab : a = b := congrArg Fin.val heq
            subst hab
            have halias : ∀ x : Fin 10 → Bool,
                let w0 := (C.gates.take 0).foldl stepWire (List.ofFn x)
                C.gates[0].op.eval (C.gates[0].inputs.map fun i => w0.getD i false) = w0.getD a false := by
              intro x; simp [ho, hi, GateOp.eval]
            obtain ⟨C', hF', hsz', hev', _⟩ := elimAlias C hF 0 h0 a ha10 halias
            exact hmin.2 C'.size (by omega) ⟨C', hF', Nat.le_refl _, fun x => (hev' x).trans (hev x)⟩
          by_cases hu2 : ∃ k, 0 < k ∧ ∃ hk : k < C.gates.length, reads C.gates[k] u.val
          · exact ⟨u, huS, hfan2_step u huS hu2 hra⟩
          · by_cases hv2 : ∃ k, 0 < k ∧ ∃ hk : k < C.gates.length, reads C.gates[k] v.val
            · exact ⟨v, hvS, hfan2_step v hvS hv2 hrb⟩
            · exfalso
              push_neg at hu2 hv2
              have hind_v : ¬ DependsOn (restrict f u true) v := by
                have hreq : restrict f u true = restrict (fun x => C.eval (List.ofFn x)) u true := by
                  funext x; exact (hev (Function.update x u true)).symm
                rw [hreq]
                apply eval_gate0_indep C u v true (by omega) h0
                · intro x
                  simp only [ho, hi, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
                    List.any_nil, id_eq, Bool.or_false, getD_ofFn, ha10, ↓reduceDIte]
                  have hu_eq : (⟨a, ha10⟩ : Fin 10) = u := rfl
                  simp [hu_eq, Function.update]
                · exact hv2
              have hind_u : ¬ DependsOn (restrict f v true) u := by
                have hreq : restrict f v true = restrict (fun x => C.eval (List.ofFn x)) v true := by
                  funext x; exact (hev (Function.update x v true)).symm
                rw [hreq]
                apply eval_gate0_indep C v u true (by omega) h0
                · intro x
                  simp only [ho, hi, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
                    List.any_nil, id_eq, Bool.or_false, getD_ofFn, hb10, ↓reduceDIte]
                  have hv_eq : (⟨b, hb10⟩ : Fin 10) = v := rfl
                  simp [hv_eq, Function.update]
                · exact hu2
              rcases hno4 u huS v hvS huv with h1 | h2
              · exact hind_v h1
              · exact hind_u h2
        | cons c cs => have := hg0_F.2; simp [hi] at this
  · cases hi : C.gates[0].inputs with
    | nil => exact absurd (Or.inl hi) hnot_triv0
    | cons a as =>
      have hra : reads C.gates[0] a := by simp [reads, readList, ho, hi]
      have ha10 := hread0_lt10 a hra
      let u : Fin 10 := ⟨a, ha10⟩
      have huS : u ∈ S := hread0_inS a ha10 hra
      refine ⟨u, huS, ?_, ?_⟩
      · exact hconst0_step u false (by simp [substConstGate, ho, hi, u])
      · exact hconst0_step u true (by simp [substConstGate, ho, hi, u])
  · have := hg0_F.1; simp [ho] at this
  · have := hg0_F.1; simp [ho] at this

private lemma sum_b2n_eq_card (p : Fin 10 → Bool) :
    b2n (p ⟨0, by decide⟩) + b2n (p ⟨1, by decide⟩) + b2n (p ⟨2, by decide⟩) +
    b2n (p ⟨3, by decide⟩) + b2n (p ⟨4, by decide⟩) + b2n (p ⟨5, by decide⟩) +
    b2n (p ⟨6, by decide⟩) + b2n (p ⟨7, by decide⟩) + b2n (p ⟨8, by decide⟩) +
    b2n (p ⟨9, by decide⟩) = (Finset.univ.filter (fun v : Fin 10 => p v = true)).card := by
  have huniv : (Finset.univ : Finset (Fin 10)) =
      {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩,
       ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩} := by
    decide
  rw [Finset.card_filter, huniv]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    Fin.mk.injEq, Nat.reduceEqDiff, or_self, not_false_eq_true, b2n]
  omega

private def aliveOf (D : Finset (Fin 10)) : Fin 10 → Bool :=
  fun v => decide (v ∉ D)

private lemma get10_aliveOf (D : Finset (Fin 10)) :
    get10 (aliveOf D 0) (aliveOf D 1) (aliveOf D 2) (aliveOf D 3) (aliveOf D 4)
          (aliveOf D 5) (aliveOf D 6) (aliveOf D 7) (aliveOf D 8) (aliveOf D 9) = aliveOf D := by
  funext v
  fin_cases v <;> rfl

private lemma dead_aliveOf (D : Finset (Fin 10)) :
    b2n (!(aliveOf D 0)) + b2n (!(aliveOf D 1)) + b2n (!(aliveOf D 2)) +
    b2n (!(aliveOf D 3)) + b2n (!(aliveOf D 4)) + b2n (!(aliveOf D 5)) +
    b2n (!(aliveOf D 6)) + b2n (!(aliveOf D 7)) + b2n (!(aliveOf D 8)) +
    b2n (!(aliveOf D 9)) = D.card := by
  have h := sum_b2n_eq_card (fun v => !(aliveOf D v))
  exact h.trans (by congr 1; ext v; simp [aliveOf])

private lemma dependsOn_petSub_iff (D : Finset (Fin 10)) (v : Fin 10) :
    DependsOn (petSub D) v ↔ isAct (aliveOf D) v = true := by
  have hnbr : (aliveOf D (n1 v) || aliveOf D (n2 v) || aliveOf D (n3 v)) = true ↔
      ∃ w : Fin 10, w ∉ D ∧ adjB v w = true := by
    simp only [Bool.or_eq_true, aliveOf, decide_eq_true_eq]
    constructor
    · rintro ((h | h) | h)
      · exact ⟨n1 v, h, (adjB_iff_n v (n1 v)).mpr (Or.inl rfl)⟩
      · exact ⟨n2 v, h, (adjB_iff_n v (n2 v)).mpr (Or.inr (Or.inl rfl))⟩
      · exact ⟨n3 v, h, (adjB_iff_n v (n3 v)).mpr (Or.inr (Or.inr rfl))⟩
    · rintro ⟨w, hwD, hadj⟩
      rcases (adjB_iff_n v w).mp hadj with rfl | rfl | rfl
      · exact Or.inl (Or.inl hwD)
      · exact Or.inl (Or.inr hwD)
      · exact Or.inr hwD
  rw [isAct, Bool.and_eq_true, hnbr]
  simp only [aliveOf, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx⟩
    by_contra hno
    apply hx
    apply Bool.eq_iff_iff.mpr
    rw [petSub_eq_true, petSub_eq_true]
    have hterm : ∀ b a c, a ∉ D → c ∉ D → adjB a c = true →
        Function.update x v b a = true → Function.update x v b c = true → a ≠ v ∧ c ≠ v := by
      intro b a c ha hc hadj _ _
      constructor
      · rintro rfl; exact hno ⟨ha, c, hc, hadj⟩
      · rintro rfl; exact hno ⟨hc, a, ha, by rwa [adjB_symm]⟩
    constructor
    · rintro ⟨a, c, ha, hc, hadj, h1, h2⟩
      obtain ⟨hav, hcv⟩ := hterm false a c ha hc hadj h1 h2
      refine ⟨a, c, ha, hc, hadj, ?_, ?_⟩ <;> simp [Function.update, hav, hcv] at h1 h2 ⊢ <;> assumption
    · rintro ⟨a, c, ha, hc, hadj, h1, h2⟩
      obtain ⟨hav, hcv⟩ := hterm true a c ha hc hadj h1 h2
      refine ⟨a, c, ha, hc, hadj, ?_, ?_⟩ <;> simp [Function.update, hav, hcv] at h1 h2 ⊢ <;> assumption
  · rintro ⟨hvD, w, hwD, hadj⟩
    have hvw : v ≠ w := by
      rintro rfl; rw [adjB_irrefl] at hadj; exact Bool.noConfusion hadj
    let x : Fin 10 → Bool := fun i => decide (i = w)
    refine ⟨x, ?_⟩
    have h0 : petSub D (Function.update x v false) = false := by
      rw [Bool.eq_false_iff]
      intro htr
      rw [petSub_eq_true] at htr
      obtain ⟨a, c, _, _, hac, ha, hc⟩ := htr
      have haw : a = w := by
        by_cases hav : a = v
        · subst hav; simp at ha
        · simp [x, Function.update, hav] at ha; exact ha
      have hcw : c = w := by
        by_cases hcv : c = v
        · subst hcv; simp at hc
        · simp [x, Function.update, hcv] at hc; exact hc
      subst haw; subst hcw
      rw [adjB_irrefl] at hac; exact Bool.noConfusion hac
    have h1 : petSub D (Function.update x v true) = true := by
      rw [petSub_eq_true]
      exact ⟨v, w, hvD, hwD, hadj, by simp [Function.update], by simp [x, Function.update, hvw.symm]⟩
    rw [h0, h1]; decide

private lemma dependsOn_r1_of_isActR1 (D : Finset (Fin 10)) (u v : Fin 10)
    (huD : u ∉ D) (h : isActR1 (aliveOf D) u v = true) :
    DependsOn (restrict (petSub D) u true) v := by
  simp only [isActR1, aliveOf, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    bne_iff_ne, Bool.not_eq_true'] at h
  have hcase : v ∉ D ∧ v ≠ u ∧ (adjB u v = true ∨ ∃ w : Fin 10, w ∉ D ∧ w ≠ u ∧ adjB v w = true ∧ adjB u w = false) := by
    rcases h with ⟨⟨hvD, hvu⟩, (((hadj | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩)⟩
    · exact ⟨hvD, hvu, Or.inl hadj⟩
    · exact ⟨hvD, hvu, Or.inr ⟨n1 v, h1, h2, (adjB_iff_n v (n1 v)).mpr (Or.inl rfl), h3⟩⟩
    · exact ⟨hvD, hvu, Or.inr ⟨n2 v, h1, h2, (adjB_iff_n v (n2 v)).mpr (Or.inr (Or.inl rfl)), h3⟩⟩
    · exact ⟨hvD, hvu, Or.inr ⟨n3 v, h1, h2, (adjB_iff_n v (n3 v)).mpr (Or.inr (Or.inr rfl)), h3⟩⟩
  rcases hcase with ⟨hvD, hvu, hadj_uv | ⟨w, hwD, hwu, hvw, hnot_uw⟩⟩
  · let x : Fin 10 → Bool := fun _ => false
    refine ⟨x, ?_⟩
    have h0 : restrict (petSub D) u true (Function.update x v false) = false := by
      rw [Bool.eq_false_iff]
      intro htr
      rw [restrict, petSub_eq_true] at htr
      obtain ⟨a, c, _, _, hac, ha, hc⟩ := htr
      have hau : a = u := by
        by_cases h1 : a = u
        · exact h1
        · by_cases h2 : a = v
          · subst h2; simp [Function.update, hvu] at ha
          · simp [x, Function.update, h1, h2] at ha
      have hcu : c = u := by
        by_cases h1 : c = u
        · exact h1
        · by_cases h2 : c = v
          · subst h2; simp [Function.update, hvu] at hc
          · simp [x, Function.update, h1, h2] at hc
      subst hau; subst hcu; rw [adjB_irrefl] at hac; exact Bool.noConfusion hac
    have h1 : restrict (petSub D) u true (Function.update x v true) = true := by
      rw [restrict, petSub_eq_true]
      exact ⟨u, v, huD, hvD, hadj_uv, by simp [Function.update], by simp [Function.update, hvu]⟩
    rw [h0, h1]; decide
  · have hwv : w ≠ v := by
      rintro rfl; rw [adjB_irrefl] at hvw; exact Bool.noConfusion hvw
    let x : Fin 10 → Bool := fun i => decide (i = w)
    refine ⟨x, ?_⟩
    have h0 : restrict (petSub D) u true (Function.update x v false) = false := by
      rw [Bool.eq_false_iff]
      intro htr
      rw [restrict, petSub_eq_true] at htr
      obtain ⟨a, c, _, _, hac, ha, hc⟩ := htr
      have ha_cases : a = u ∨ a = w := by
        by_cases h1 : a = u
        · exact Or.inl h1
        · by_cases h2 : a = v
          · subst h2; simp [Function.update, hvu] at ha
          · simp [x, Function.update, h1, h2] at ha; exact Or.inr ha
      have hc_cases : c = u ∨ c = w := by
        by_cases h1 : c = u
        · exact Or.inl h1
        · by_cases h2 : c = v
          · subst h2; simp [Function.update, hvu] at hc
          · simp [x, Function.update, h1, h2] at hc; exact Or.inr hc
      rcases ha_cases with rfl | rfl <;> rcases hc_cases with rfl | rfl
      · rw [adjB_irrefl] at hac; exact Bool.noConfusion hac
      · rw [hnot_uw] at hac; exact Bool.noConfusion hac
      · rw [adjB_symm, hnot_uw] at hac; exact Bool.noConfusion hac
      · rw [adjB_irrefl] at hac; exact Bool.noConfusion hac
    have h1 : restrict (petSub D) u true (Function.update x v true) = true := by
      rw [restrict, petSub_eq_true]
      exact ⟨v, w, hvD, hwD, hvw, by simp [Function.update, hvu], by simp [x, Function.update, hwu, hwv]⟩
    rw [h0, h1]; decide

private lemma noBad_implies (D : Finset (Fin 10)) (hnb : noBad (aliveOf D) = true) :
    (∀ u v : Fin 10, isAct (aliveOf D) u = true → isAct (aliveOf D) v = true → u ≠ v →
      DependsOn (restrict (petSub D) u false) v ∨ DependsOn (restrict (petSub D) v false) u) ∧
    (∀ u v : Fin 10, isAct (aliveOf D) u = true → isAct (aliveOf D) v = true → u ≠ v →
      DependsOn (restrict (petSub D) u true) v ∨ DependsOn (restrict (petSub D) v true) u) := by
  have hpair : ∀ u v : Fin 10, u.val < v.val → isAct (aliveOf D) u = true → isAct (aliveOf D) v = true →
      ((aliveOf D (n1 v) && (n1 v != u)) || (aliveOf D (n2 v) && (n2 v != u)) || (aliveOf D (n3 v) && (n3 v != u)) ||
       (aliveOf D (n1 u) && (n1 u != v)) || (aliveOf D (n2 u) && (n2 u != v)) || (aliveOf D (n3 u) && (n3 u != v))) = true ∧
      (isActR1 (aliveOf D) u v || isActR1 (aliveOf D) v u) = true := by
    intro u v hlt hu hv
    have h1 := List.all_eq_true.mp hnb u (List.mem_finRange u)
    simp only [hu, ↓reduceIte] at h1
    have h2 := List.all_eq_true.mp h1 v (List.mem_finRange v)
    simp only [hlt, hv, Bool.and_true, decide_true, ↓reduceIte, Bool.and_eq_true] at h2
    exact h2
  have hsym : ∀ u v : Fin 10, u ≠ v → isAct (aliveOf D) u = true → isAct (aliveOf D) v = true →
      (DependsOn (restrict (petSub D) u false) v ∨ DependsOn (restrict (petSub D) v false) u) ∧
      (DependsOn (restrict (petSub D) u true) v ∨ DependsOn (restrict (petSub D) v true) u) := by
    have hlt_case : ∀ u v : Fin 10, u.val < v.val → isAct (aliveOf D) u = true → isAct (aliveOf D) v = true →
        (DependsOn (restrict (petSub D) u false) v ∨ DependsOn (restrict (petSub D) v false) u) ∧
        (DependsOn (restrict (petSub D) u true) v ∨ DependsOn (restrict (petSub D) v true) u) := by
      intro u v hlt hu hv
      have huv : u ≠ v := fun h => by omega
      have huD : u ∉ D := by simp [isAct, aliveOf] at hu; exact hu.1
      have hvD : v ∉ D := by simp [isAct, aliveOf] at hv; exact hv.1
      obtain ⟨h3, h4⟩ := hpair u v hlt hu hv
      constructor
      · simp only [Bool.or_eq_true, Bool.and_eq_true, aliveOf, decide_eq_true_eq, bne_iff_ne] at h3
        rcases h3 with (((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
        · left; rw [restrict_petSub_false, dependsOn_petSub_iff]
          simp [isAct, aliveOf, huv.symm, hvD, h1, h2]
        · left; rw [restrict_petSub_false, dependsOn_petSub_iff]
          simp [isAct, aliveOf, huv.symm, hvD, h1, h2]
        · left; rw [restrict_petSub_false, dependsOn_petSub_iff]
          simp [isAct, aliveOf, huv.symm, hvD, h1, h2]
        · right; rw [restrict_petSub_false, dependsOn_petSub_iff]
          simp [isAct, aliveOf, huv, huD, h1, h2]
        · right; rw [restrict_petSub_false, dependsOn_petSub_iff]
          simp [isAct, aliveOf, huv, huD, h1, h2]
        · right; rw [restrict_petSub_false, dependsOn_petSub_iff]
          simp [isAct, aliveOf, huv, huD, h1, h2]
      · rw [Bool.or_eq_true] at h4
        rcases h4 with h4a | h4b
        · exact Or.inl (dependsOn_r1_of_isActR1 D u v huD h4a)
        · exact Or.inr (dependsOn_r1_of_isActR1 D v u hvD h4b)
    intro u v huv hu hv
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne huv) with hlt | hgt
    · exact hlt_case u v hlt hu hv
    · obtain ⟨h1, h2⟩ := hlt_case v u hgt hv hu
      exact ⟨h1.symm, h2.symm⟩
  exact ⟨fun u v hu hv huv => (hsym u v huv hu hv).1, fun u v hu hv huv => (hsym u v huv hu hv).2⟩

private lemma petSub_lb_card4 (D : Finset (Fin 10)) (hD : D.card = 4) (s : ℕ)
    (hs : HasCircuitSize 10 (petSub D) s) : 5 ≤ s := by
  classical
  obtain ⟨s', hs'le, hmin⟩ := exists_minSize hs
  suffices 5 ≤ s' by omega
  have hchk := h_check10 (aliveOf D 0) (aliveOf D 1) (aliveOf D 2) (aliveOf D 3) (aliveOf D 4)
    (aliveOf D 5) (aliveOf D 6) (aliveOf D 7) (aliveOf D 8) (aliveOf D 9)
  simp only [check10, dead_aliveOf, get10_aliveOf, hD, Nat.reduceLeDiff, ↓reduceIte,
    beq_self_eq_true] at hchk
  let S : Finset (Fin 10) := Finset.univ.filter (fun v => isAct (aliveOf D) v = true)
  have hS_iff : ∀ v, v ∈ S ↔ DependsOn (petSub D) v := by
    intro v; rw [dependsOn_petSub_iff]; simp [S]
  have hS_card : S.card = actCnt (aliveOf D) := (sum_b2n_eq_card (isAct (aliveOf D))).symm
  by_cases h6 : 6 ≤ actCnt (aliveOf D)
  · have := active_card_le_size_add_one hmin S (fun v hv => (hS_iff v).mp hv) (by omega)
    omega
  · simp only [decide_eq_true_eq, h6, ↓reduceIte, Bool.and_eq_true, List.all_eq_true,
      List.mem_finRange, forall_true_left] at hchk
    obtain ⟨⟨h5, hnb⟩, hall_u⟩ := hchk
    obtain ⟨hno3', hno4'⟩ := noBad_implies D hnb
    have hno3 : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
        DependsOn (restrict (petSub D) u false) v ∨ DependsOn (restrict (petSub D) v false) u :=
      fun u hu v hv huv => hno3' u v (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 huv
    have hno4 : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
        DependsOn (restrict (petSub D) u true) v ∨ DependsOn (restrict (petSub D) v true) u :=
      fun u hu v hv huv => hno4' u v (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 huv
    obtain ⟨u, huS, hr0, hr1⟩ := two_gate_elim hmin S hS_iff (by omega) hno3 hno4
    have hu_act : isAct (aliveOf D) u = true := (Finset.mem_filter.mp huS).2
    have huD : u ∉ D := by simp [isAct, aliveOf] at hu_act; exact hu_act.1
    have hcu := hall_u u
    simp only [hu_act, ↓reduceIte, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcu
    obtain ⟨⟨h0pos, h1pos⟩, h4_0 | h4_1⟩ := hcu
    · have halive0 : (fun w => if w == u then false else aliveOf D w) = aliveOf (insert u D) := by
        funext w
        by_cases hwu : w = u
        · subst hwu; simp [aliveOf]
        · simp [aliveOf, hwu]
      rw [halive0] at h0pos h4_0
      let S0 : Finset (Fin 10) := Finset.univ.filter (fun v => isAct (aliveOf (insert u D)) v = true)
      have hS0_card : S0.card = actCnt (aliveOf (insert u D)) := (sum_b2n_eq_card _).symm
      have hS0_dep : ∀ v ∈ S0, DependsOn (restrict (petSub D) u false) v := by
        intro v hv
        rw [restrict_petSub_false, dependsOn_petSub_iff]
        exact (Finset.mem_filter.mp hv).2
      have hnc0 : NonConst (restrict (petSub D) u false) := by
        obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S0.card)
        exact dependsOn_nonConst (hS0_dep v hv)
      obtain ⟨s0, hs0_le, hmin0⟩ := exists_minSize (hr0 hnc0)
      have hlb0 := active_card_le_size_add_one hmin0 S0 hS0_dep (by omega)
      have hs'2 : 2 ≤ s' := by
        have := active_card_le_size_add_one hmin S (fun v hv => (hS_iff v).mp hv) (by omega)
        omega
      omega
    · let S1 : Finset (Fin 10) := Finset.univ.filter (fun v => isActR1 (aliveOf D) u v = true)
      have hS1_card : S1.card = actR1Cnt (aliveOf D) u := (sum_b2n_eq_card _).symm
      have hS1_dep : ∀ v ∈ S1, DependsOn (restrict (petSub D) u true) v := by
        intro v hv
        exact dependsOn_r1_of_isActR1 D u v huD (Finset.mem_filter.mp hv).2
      have hnc1 : NonConst (restrict (petSub D) u true) := by
        obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S1.card)
        exact dependsOn_nonConst (hS1_dep v hv)
      obtain ⟨s1, hs1_le, hmin1⟩ := exists_minSize (hr1 hnc1)
      have hlb1 := active_card_le_size_add_one hmin1 S1 hS1_dep (by omega)
      have hs'2 : 2 ≤ s' := by
        have := active_card_le_size_add_one hmin S (fun v hv => (hS_iff v).mp hv) (by omega)
        omega
      omega

private lemma petSub_step_le3 (D : Finset (Fin 10)) (hD : D.card ≤ 3) (s : ℕ)
    (hs : HasCircuitSize 10 (petSub D) s) :
    2 ≤ s ∧ ∃ u : Fin 10, u ∉ D ∧ HasCircuitSize 10 (petSub (insert u D)) (s - 2) := by
  classical
  obtain ⟨s', hs'le, hmin⟩ := exists_minSize hs
  have hchk := h_check10 (aliveOf D 0) (aliveOf D 1) (aliveOf D 2) (aliveOf D 3) (aliveOf D 4)
    (aliveOf D 5) (aliveOf D 6) (aliveOf D 7) (aliveOf D 8) (aliveOf D 9)
  simp only [check10, dead_aliveOf, get10_aliveOf, hD, ↓reduceIte, Bool.and_eq_true,
    decide_eq_true_eq] at hchk
  obtain ⟨h6, hnb⟩ := hchk
  let S : Finset (Fin 10) := Finset.univ.filter (fun v => isAct (aliveOf D) v = true)
  have hS_iff : ∀ v, v ∈ S ↔ DependsOn (petSub D) v := by
    intro v; rw [dependsOn_petSub_iff]; simp [S]
  have hS_card : S.card = actCnt (aliveOf D) := (sum_b2n_eq_card _).symm
  have hs'2 : 2 ≤ s' := by
    have := active_card_le_size_add_one hmin S (fun v hv => (hS_iff v).mp hv) (by omega)
    omega
  obtain ⟨hno3', hno4'⟩ := noBad_implies D hnb
  have hno3 : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      DependsOn (restrict (petSub D) u false) v ∨ DependsOn (restrict (petSub D) v false) u :=
    fun u hu v hv huv => hno3' u v (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 huv
  have hno4 : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      DependsOn (restrict (petSub D) u true) v ∨ DependsOn (restrict (petSub D) v true) u :=
    fun u hu v hv huv => hno4' u v (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 huv
  obtain ⟨u, huS, hr0, _⟩ := two_gate_elim hmin S hS_iff (by omega) hno3 hno4
  have huD : u ∉ D := by
    have := (Finset.mem_filter.mp huS).2
    simp [isAct, aliveOf] at this; exact this.1
  let D' := insert u D
  have hD'_card : D'.card = D.card + 1 := Finset.card_insert_of_notMem huD
  have hnc0 : NonConst (restrict (petSub D) u false) := by
    rw [restrict_petSub_false]
    have hchk' := h_check10 (aliveOf D' 0) (aliveOf D' 1) (aliveOf D' 2) (aliveOf D' 3) (aliveOf D' 4)
      (aliveOf D' 5) (aliveOf D' 6) (aliveOf D' 7) (aliveOf D' 8) (aliveOf D' 9)
    simp only [check10, dead_aliveOf, get10_aliveOf, hD'_card] at hchk'
    have hact_pos : 1 ≤ actCnt (aliveOf D') := by
      by_cases hle3 : D.card + 1 ≤ 3
      · simp only [hle3, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hchk'
        omega
      · have heq4 : D.card + 1 = 4 := by omega
        have hnot3 : ¬ (D.card + 1 ≤ 3) := hle3
        rw [ite_eq_right hnot3] at hchk'
        simp only [heq4, beq_self_eq_true, ↓reduceIte] at hchk'
        by_cases h6' : 6 ≤ actCnt (aliveOf D')
        · omega
        · simp only [decide_eq_true_eq, h6', ↓reduceIte, Bool.and_eq_true] at hchk'
          omega
    let S' : Finset (Fin 10) := Finset.univ.filter (fun v => isAct (aliveOf D') v = true)
    have hS'_card : S'.card = actCnt (aliveOf D') := (sum_b2n_eq_card _).symm
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S'.card)
    exact dependsOn_nonConst ((dependsOn_petSub_iff D' v).mpr (Finset.mem_filter.mp hv).2)
  have hcs := hr0 hnc0
  rw [restrict_petSub_false] at hcs
  obtain ⟨C', hF', hsz', hev'⟩ := hcs
  exact ⟨by omega, u, huD, ⟨C', hF', by omega, hev'⟩⟩

private lemma main_proof :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 12 := by
  intro h12
  have h0 : HasCircuitSize 10 (petSub ∅) 12 := by
    obtain ⟨C, hF, hsz, hev⟩ := h12
    exact ⟨C, hF, hsz, fun x => (hev x).trans (petSub_empty x).symm⟩
  obtain ⟨_, u1, hu1, h1⟩ := petSub_step_le3 ∅ (by simp) 12 h0
  have hc1 : (insert u1 ∅ : Finset (Fin 10)).card = 1 := by simp
  obtain ⟨_, u2, hu2, h2⟩ := petSub_step_le3 (insert u1 ∅) (by omega) 10 h1
  have hc2 : (insert u2 (insert u1 ∅) : Finset (Fin 10)).card = 2 := by
    rw [Finset.card_insert_of_notMem hu2, hc1]
  obtain ⟨_, u3, hu3, h3⟩ := petSub_step_le3 (insert u2 (insert u1 ∅)) (by omega) 8 h2
  have hc3 : (insert u3 (insert u2 (insert u1 ∅)) : Finset (Fin 10)).card = 3 := by
    rw [Finset.card_insert_of_notMem hu3, hc2]
  obtain ⟨_, u4, hu4, h4⟩ := petSub_step_le3 (insert u3 (insert u2 (insert u1 ∅))) (by omega) 6 h3
  have hc4 : (insert u4 (insert u3 (insert u2 (insert u1 ∅))) : Finset (Fin 10)).card = 4 := by
    rw [Finset.card_insert_of_notMem hu4, hc3]
  have h5 := petSub_lb_card4 (insert u4 (insert u3 (insert u2 (insert u1 ∅)))) hc4 4 h4
  omega

end PEqualNP.Outside.L_meta_737_aux

theorem PEqualNP.Outside.L_meta_737 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) 12 :=
  PEqualNP.Outside.L_meta_737_aux.main_proof
