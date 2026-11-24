import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4356

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Wire semantics helpers adapted from PEqualNP/Outside/L_meta_1388.lean (Apache-2.0).

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

-- The seven input wires: the six variables, with a constant false in position two.
def emb (x : Fin 6 → Bool) : List Bool := [x 0, x 1, false, x 2, x 3, x 4, x 5]

lemma emb_length (x : Fin 6 → Bool) : (emb x).length = 7 := rfl

-- The function computed at gate k.
def V (C : Circuit) (k : Fin 11) (x : Fin 6 → Bool) : Bool :=
  (C.wires (emb x)).getD (7 + k.val) false

-- Trivial functions: the two constants and the six variables.
def trivB (F : (Fin 6 → Bool) → Bool) : Bool :=
  decide (F = fun _ => false) || decide (F = fun _ => true) || decide (∃ j : Fin 6, F = fun x => x j)

-- Gate i computes a nontrivial function that no earlier gate computes.
def isFirst (C : Circuit) (i : Fin 11) : Bool :=
  !trivB (V C i) && (List.finRange 11).all (fun j => !(decide (j < i) && decide (V C j = V C i)))

def firsts (C : Circuit) : List (Fin 11) := (List.finRange 11).filter (isFirst C)

-- The first gate computing the same function as gate k.
def fo (C : Circuit) (k : Fin 11) : Fin 11 :=
  (Finset.univ.filter (fun j => V C j = V C k)).min' ⟨k, by simp⟩

def pos (C : Circuit) (a : Fin 11) : ℕ := (firsts C).idxOf a

lemma fo_eq (C : Circuit) (k : Fin 11) : V C (fo C k) = V C k := by
  unfold fo
  exact (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter (fun j => V C j = V C k)) _)).2

lemma fo_le (C : Circuit) (k : Fin 11) : fo C k ≤ k :=
  Finset.min'_le _ _ (by simp)

lemma fo_min (C : Circuit) (k j : Fin 11) (hj : j < fo C k) : V C j ≠ V C k := by
  intro h
  have := Finset.min'_le (Finset.univ.filter (fun j => V C j = V C k)) j (by simp [h])
  exact absurd hj (not_lt.mpr this)

lemma isFirst_iff (C : Circuit) (i : Fin 11) :
    isFirst C i = true ↔ trivB (V C i) = false ∧ ∀ j : Fin 11, j < i → V C j ≠ V C i := by
  unfold isFirst
  rw [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1, fun j hj hv => ?_⟩
    have := h2 j (List.mem_finRange j)
    simp [hj, hv] at this
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1, fun j _ => ?_⟩
    by_cases hj : j < i
    · simp [hj, h2 j hj]
    · simp [hj]

lemma mem_firsts (C : Circuit) (i : Fin 11) : i ∈ firsts C ↔ isFirst C i = true := by
  simp [firsts, List.mem_filter, List.mem_finRange]

lemma fo_first (C : Circuit) (k : Fin 11) (hk : trivB (V C k) = false) : fo C k ∈ firsts C := by
  rw [mem_firsts, isFirst_iff, fo_eq]
  exact ⟨hk, fun j hj => fo_min C k j hj⟩

lemma firsts_sorted (C : Circuit) : (firsts C).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange 11).filter _

lemma pos_lt (C : Circuit) (a : Fin 11) (ha : a ∈ firsts C) : pos C a < (firsts C).length :=
  List.idxOf_lt_length_of_mem ha

lemma get_pos (C : Circuit) (a : Fin 11) (ha : a ∈ firsts C) :
    (firsts C)[pos C a]'(pos_lt C a ha) = a :=
  List.getElem_idxOf (pos_lt C a ha)

lemma pos_mono (C : Circuit) (a b : Fin 11) (ha : a ∈ firsts C) (hb : b ∈ firsts C) (hab : a < b) :
    pos C a < pos C b := by
  by_contra hne
  rcases Nat.lt_or_eq_of_le (not_lt.mp hne) with h | h
  · have hs := List.pairwise_iff_getElem.mp (firsts_sorted C) (pos C b) (pos C a)
      (pos_lt C b hb) (pos_lt C a ha) h
    rw [get_pos C a ha, get_pos C b hb] at hs
    exact absurd (lt_trans hs hab) (lt_irrefl _)
  · have e1 := get_pos C a ha
    have e2 := get_pos C b hb
    have : a = b := by
      rw [← e1, ← e2]
      simp only [h]
    exact absurd (this ▸ hab) (lt_irrefl _)


lemma nodup_firsts (C : Circuit) : (firsts C).Nodup :=
  (firsts_sorted C).imp (fun h => ne_of_lt h)

lemma triv_false (F : (Fin 6 → Bool) → Bool) (h : ∀ x, F x = false) : trivB F = true := by
  unfold trivB
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl (Or.inl (funext h))

lemma triv_true (F : (Fin 6 → Bool) → Bool) (h : ∀ x, F x = true) : trivB F = true := by
  unfold trivB
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl (Or.inr (funext h))

lemma triv_coord (F : (Fin 6 → Bool) → Bool) (j : Fin 6) (h : ∀ x, F x = x j) : trivB F = true := by
  unfold trivB
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨j, funext h⟩

lemma triv_cases (F : (Fin 6 → Bool) → Bool) (h : trivB F = true) :
    F = (fun _ => false) ∨ F = (fun _ => true) ∨ ∃ j : Fin 6, F = fun x => x j := by
  unfold trivB at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

def BIG : ℕ := 1000

def inMap (w : ℕ) : ℕ := [0, 1, BIG, 2, 3, 4, 5].getD w BIG

-- The variable a coordinate function reads, if it is one.
def coord (F : (Fin 6 → Bool) → Bool) : Option (Fin 6) :=
  (List.finRange 6).find? (fun j => decide (F = fun x => x j))

lemma coord_some (F : (Fin 6 → Bool) → Bool) (j : Fin 6) (h : coord F = some j) :
    F = fun x => x j := by
  have := List.find?_some h
  simpa using this

lemma coord_none (F : (Fin 6 → Bool) → Bool) (h : coord F = none) (j : Fin 6) :
    F ≠ fun x => x j := by
  intro hF
  have := List.find?_eq_none.mp h j (List.mem_finRange j)
  simp [hF] at this

def rho (C : Circuit) (i : Fin 11) (w : ℕ) : ℕ :=
  if w < 7 then inMap w
  else if h : w < 7 + i.val then
    if trivB (V C ⟨w - 7, by have := i.isLt; omega⟩) = false then
      6 + pos C (fo C ⟨w - 7, by have := i.isLt; omega⟩)
    else
      match coord (V C ⟨w - 7, by have := i.isLt; omega⟩) with
      | some j => j.val
      | none => BIG
  else BIG

def sel (g : Gate) : List ℕ :=
  match g.op with
  | GateOp.not => g.inputs.take 1
  | _ => g.inputs

def dflt : Gate := ⟨GateOp.and, []⟩

def mkGate (C : Circuit) (i : Fin 11) : Gate :=
  ⟨(C.gates.getD i.val dflt).op, (sel (C.gates.getD i.val dflt)).map (rho C i)⟩

def Dg (C : Circuit) : List Gate := (firsts C).map (mkGate C)

-- The value of wire w as read by gate i of C.
def opv (C : Circuit) (i : Fin 11) (w : ℕ) (x : Fin 6 → Bool) : Bool :=
  if w < 7 + i.val then (C.wires (emb x)).getD w false else false

lemma C_gate (C : Circuit) (hs : C.gates.length = 11) (i : Fin 11) (x : Fin 6 → Bool) :
    V C i x = (C.gates[i.val]'(by have := i.isLt; omega)).op.eval
      ((C.gates[i.val]'(by have := i.isLt; omega)).inputs.map fun w => opv C i w x) := by
  have h := foldl_step_gate C.gates (emb x) i.val (C.gates[i.val]'(by have := i.isLt; omega))
    (List.getElem?_eq_getElem _)
  unfold V opv
  rw [wires_eq_foldl]
  simp only [emb_length] at h
  exact h

lemma D_gate (C : Circuit) (o : ℕ) (m : ℕ) (hm : m < (firsts C).length) (x : Fin 6 → Bool) :
    ((⟨Dg C, o⟩ : Circuit).wires (List.ofFn x)).getD (6 + m) false =
      (mkGate C ((firsts C)[m])).op.eval ((mkGate C ((firsts C)[m])).inputs.map fun w =>
        if w < 6 + m then ((⟨Dg C, o⟩ : Circuit).wires (List.ofFn x)).getD w false else false) := by
  have hj : (Dg C)[m]? = some (mkGate C ((firsts C)[m])) := by
    simp [Dg, hm]
  have h := foldl_step_gate (Dg C) (List.ofFn x) m _ hj
  rw [wires_eq_foldl]
  simpa only [List.length_ofFn] using h

lemma D_input (C : Circuit) (o : ℕ) (x : Fin 6 → Bool) (j : ℕ) (hj : j < 6) :
    ((⟨Dg C, o⟩ : Circuit).wires (List.ofFn x)).getD j false = x ⟨j, hj⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt _ _ j (by simp [hj])]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]

lemma opv_cases (C : Circuit) (i : Fin 11) (b : ℕ) :
    trivB (fun x => opv C i b x) = true ∨ ∃ j : Fin 11, j < i ∧ V C j = fun x => opv C i b x := by
  by_cases hb : b < 7
  · left
    have hv : ∀ x, opv C i b x = (emb x).getD b false := by
      intro x
      unfold opv
      rw [wires_eq_foldl, foldl_step_getD_lt _ _ b (by simp only [emb_length]; omega)]
      simp only [show b < 7 + i.val by omega, ↓reduceIte]
    interval_cases b
    · exact triv_coord _ 0 (fun x => by simp [hv, emb])
    · exact triv_coord _ 1 (fun x => by simp [hv, emb])
    · exact triv_false _ (fun x => by simp [hv, emb])
    · exact triv_coord _ 2 (fun x => by simp [hv, emb])
    · exact triv_coord _ 3 (fun x => by simp [hv, emb])
    · exact triv_coord _ 4 (fun x => by simp [hv, emb])
    · exact triv_coord _ 5 (fun x => by simp [hv, emb])
  · by_cases hb2 : b < 7 + i.val
    · right
      refine ⟨⟨b - 7, by have := i.isLt; omega⟩, ?_, ?_⟩
      · show b - 7 < i.val
        omega
      · funext x
        unfold V opv
        simp only [hb2, ↓reduceIte]
        congr 1
        show 7 + (b - 7) = b
        omega
    · left
      exact triv_false _ (fun x => by unfold opv; simp only [hb2, ↓reduceIte])


lemma firsts_len (C : Circuit) : (firsts C).length ≤ 11 := by
  have := List.length_filter_le (isFirst C) (List.finRange 11)
  simpa [firsts] using this

lemma opnd (C : Circuit) (o : ℕ) (m : ℕ) (hm : m < (firsts C).length)
    (ih : ∀ m' < m, ∀ (hm' : m' < (firsts C).length) (x : Fin 6 → Bool),
      ((⟨Dg C, o⟩ : Circuit).wires (List.ofFn x)).getD (6 + m') false = V C ((firsts C)[m']) x)
    (w : ℕ) (hw : (fun x => opv C ((firsts C)[m]) w x) ≠ (fun _ => true)) (x : Fin 6 → Bool) :
    (if rho C ((firsts C)[m]) w < 6 + m then
        ((⟨Dg C, o⟩ : Circuit).wires (List.ofFn x)).getD (rho C ((firsts C)[m]) w) false
      else false) = opv C ((firsts C)[m]) w x := by
  have hlen := firsts_len C
  have hi : (firsts C)[m] ∈ firsts C := List.getElem_mem hm
  have hpos : pos C ((firsts C)[m]) = m := (nodup_firsts C).idxOf_getElem m hm
  have hbig : ¬ BIG < 6 + m := by unfold BIG; omega
  by_cases hw7 : w < 7
  · have hv : opv C ((firsts C)[m]) w x = (emb x).getD w false := by
      unfold opv
      rw [wires_eq_foldl, foldl_step_getD_lt _ _ w (by simp only [emb_length]; omega)]
      simp only [show w < 7 + ((firsts C)[m]).val by omega, ↓reduceIte]
    rw [hv]
    have hr : rho C ((firsts C)[m]) w = inMap w := by
      unfold rho
      simp only [hw7, ↓reduceIte]
    rw [hr]
    interval_cases w
    · simp only [inMap, List.getD_cons_zero, show (0 : ℕ) < 6 + m by omega, ↓reduceIte,
        D_input C o x 0 (by decide)]
      rfl
    · simp only [inMap, List.getD_cons_succ, List.getD_cons_zero, show (1 : ℕ) < 6 + m by omega,
        ↓reduceIte, D_input C o x 1 (by decide)]
      rfl
    · simp only [inMap, List.getD_cons_succ, List.getD_cons_zero, hbig, ↓reduceIte]
      rfl
    · simp only [inMap, List.getD_cons_succ, List.getD_cons_zero, show (2 : ℕ) < 6 + m by omega,
        ↓reduceIte, D_input C o x 2 (by decide)]
      rfl
    · simp only [inMap, List.getD_cons_succ, List.getD_cons_zero, show (3 : ℕ) < 6 + m by omega,
        ↓reduceIte, D_input C o x 3 (by decide)]
      rfl
    · simp only [inMap, List.getD_cons_succ, List.getD_cons_zero, show (4 : ℕ) < 6 + m by omega,
        ↓reduceIte, D_input C o x 4 (by decide)]
      rfl
    · simp only [inMap, List.getD_cons_succ, List.getD_cons_zero, show (5 : ℕ) < 6 + m by omega,
        ↓reduceIte, D_input C o x 5 (by decide)]
      rfl
  · by_cases hwi : w < 7 + ((firsts C)[m]).val
    · have hk : w - 7 < 11 := by have := ((firsts C)[m]).isLt; omega
      have hvk : ∀ y, opv C ((firsts C)[m]) w y = V C ⟨w - 7, hk⟩ y := by
        intro y
        unfold opv V
        simp only [hwi, ↓reduceIte]
        congr 1
        show w = 7 + (w - 7)
        omega
      rw [hvk x]
      have hfun : (fun y => opv C ((firsts C)[m]) w y) = V C ⟨w - 7, hk⟩ := funext hvk
      rw [hfun] at hw
      have hr : rho C ((firsts C)[m]) w =
          (if trivB (V C ⟨w - 7, hk⟩) = false then 6 + pos C (fo C ⟨w - 7, hk⟩)
           else match coord (V C ⟨w - 7, hk⟩) with
             | some j => j.val
             | none => BIG) := by
        unfold rho
        simp only [hw7, ↓reduceIte, hwi, ↓reduceDIte]
      rw [hr]
      by_cases ht : trivB (V C ⟨w - 7, hk⟩) = false
      · simp only [ht, ↓reduceIte]
        have hfo := fo_first C ⟨w - 7, hk⟩ ht
        have hlt : fo C ⟨w - 7, hk⟩ < (firsts C)[m] := by
          have h1 := fo_le C ⟨w - 7, hk⟩
          have h2 : (⟨w - 7, hk⟩ : Fin 11) < (firsts C)[m] := by
            show w - 7 < ((firsts C)[m]).val
            omega
          exact lt_of_le_of_lt h1 h2
        have hp : pos C (fo C ⟨w - 7, hk⟩) < m := by
          have := pos_mono C _ _ hfo hi hlt
          omega
        simp only [show 6 + pos C (fo C ⟨w - 7, hk⟩) < 6 + m by omega, ↓reduceIte]
        rw [ih _ hp (pos_lt C _ hfo) x]
        simp only [get_pos C _ hfo]
        rw [fo_eq]
      · have ht' : trivB (V C ⟨w - 7, hk⟩) = true := by simpa using ht
        simp only [ht', Bool.true_eq_false, ↓reduceIte]
        cases hc : coord (V C ⟨w - 7, hk⟩) with
        | some j =>
          simp only [show (j.val : ℕ) < 6 + m by have := j.isLt; omega, ↓reduceIte,
            D_input C o x j.val j.isLt]
          rw [coord_some _ j hc]
        | none =>
          simp only [hbig, ↓reduceIte]
          rcases triv_cases _ ht' with h0 | h1 | ⟨j, hj⟩
          · rw [h0]
          · exact absurd h1 hw
          · exact absurd hj (coord_none _ hc j)
    · have hr : rho C ((firsts C)[m]) w = BIG := by
        unfold rho
        simp only [hw7, ↓reduceIte, hwi, ↓reduceDIte]
      rw [hr]
      simp only [hbig, ↓reduceIte]
      unfold opv
      simp only [hwi, ↓reduceIte]


lemma op_cases (C : Circuit) (hfan : FanInTwo C) (g : Gate) (hg : g ∈ C.gates) :
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨hop, hlen⟩ := hfan g hg
  refine ⟨?_, hlen⟩
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hop

lemma no_true (C : Circuit) (hs : C.gates.length = 11) (hfan : FanInTwo C) (i : Fin 11)
    (hi : i ∈ firsts C) (w : ℕ)
    (hw : w ∈ sel (C.gates[i.val]'(by have := i.isLt; omega))) :
    (fun x => opv C i w x) ≠ (fun _ => true) := by
  intro htrue
  have hf := (isFirst_iff C i).mp ((mem_firsts C i).mp hi)
  have hmem : C.gates[i.val]'(by have := i.isLt; omega) ∈ C.gates := List.getElem_mem _
  obtain ⟨hop, hlen⟩ := op_cases C hfan _ hmem
  have hval := C_gate C hs i
  have htx : ∀ x, opv C i w x = true := fun x => congrFun htrue x
  generalize C.gates[i.val]'(by have := i.isLt; omega) = g at hw hop hlen hval
  rcases hop with hop | hop | hop
  · have hsel : sel g = g.inputs := by unfold sel; rw [hop]
    rw [hsel] at hw
    rw [hop] at hval
    generalize g.inputs = l at hw hlen hval
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp at hw
    · simp only [List.mem_singleton] at hw
      subst hw
      have : V C i = fun _ => true := by
        funext x
        rw [hval x]
        simp [GateOp.eval, htx x]
      exact absurd (triv_true _ (fun x => congrFun this x)) (by simp [hf.1])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      have key : ∀ c, (V C i = fun x => opv C i c x) → False := by
        intro c hc
        rcases opv_cases C i c with h | ⟨j, hj, hj2⟩
        · rw [← hc] at h
          simp [hf.1] at h
        · exact hf.2 j hj (hj2.trans hc.symm)
      rcases hw with rfl | rfl
      · apply key b
        funext x
        rw [hval x]
        simp [GateOp.eval, htx x]
      · apply key a
        funext x
        rw [hval x]
        simp [GateOp.eval, htx x]
    · simp at hlen
  · have hsel : sel g = g.inputs := by unfold sel; rw [hop]
    rw [hsel] at hw
    rw [hop] at hval
    have : V C i = fun _ => true := by
      funext x
      rw [hval x]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      exact ⟨true, ⟨w, hw, htx x⟩, rfl⟩
    exact absurd (triv_true _ (fun x => congrFun this x)) (by simp [hf.1])
  · have hsel : sel g = g.inputs.take 1 := by unfold sel; rw [hop]
    rw [hsel] at hw
    rw [hop] at hval
    generalize g.inputs = l at hw hlen hval
    rcases l with _ | ⟨a, rest⟩
    · simp at hw
    · simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hw
      subst hw
      have : V C i = fun _ => false := by
        funext x
        rw [hval x]
        simp [GateOp.eval, htx x]
      exact absurd (triv_false _ (fun x => congrFun this x)) (by simp [hf.1])

lemma getD_gate (C : Circuit) (hs : C.gates.length = 11) (i : Fin 11) :
    C.gates.getD i.val dflt = C.gates[i.val]'(by have := i.isLt; omega) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i.val < C.gates.length by have := i.isLt; omega)]

lemma D_correct (C : Circuit) (hs : C.gates.length = 11) (hfan : FanInTwo C) (o : ℕ) :
    ∀ m (hm : m < (firsts C).length) (x : Fin 6 → Bool),
      ((⟨Dg C, o⟩ : Circuit).wires (List.ofFn x)).getD (6 + m) false = V C ((firsts C)[m]) x := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm x
  have hi : (firsts C)[m] ∈ firsts C := List.getElem_mem hm
  rw [D_gate C o m hm x, C_gate C hs _ x]
  have hmk : mkGate C ((firsts C)[m]) =
      ⟨(C.gates[((firsts C)[m]).val]'(by have := ((firsts C)[m]).isLt; omega)).op,
       (sel (C.gates[((firsts C)[m]).val]'(by have := ((firsts C)[m]).isLt; omega))).map
         (rho C ((firsts C)[m]))⟩ := by
    unfold mkGate
    rw [getD_gate C hs]
  rw [hmk]
  simp only [List.map_map]
  have hmem : C.gates[((firsts C)[m]).val]'(by have := ((firsts C)[m]).isLt; omega) ∈ C.gates :=
    List.getElem_mem _
  have hop := (op_cases C hfan _ hmem).1
  have hnt := no_true C hs hfan ((firsts C)[m]) hi
  have hop' := opnd C o m hm (fun m' hm' => ih m' hm')
  generalize C.gates[((firsts C)[m]).val]'(by have := ((firsts C)[m]).isLt; omega) = g at hop hnt
  rcases hop with hop | hop | hop
  · have hsel : sel g = g.inputs := by unfold sel; rw [hop]
    rw [hsel]
    congr 1
    apply List.map_congr_left
    intro w hw
    exact hop' w (hnt w (by rw [hsel]; exact hw)) x
  · have hsel : sel g = g.inputs := by unfold sel; rw [hop]
    rw [hsel]
    congr 1
    apply List.map_congr_left
    intro w hw
    exact hop' w (hnt w (by rw [hsel]; exact hw)) x
  · have hsel : sel g = g.inputs.take 1 := by unfold sel; rw [hop]
    rw [hsel, hop]
    have hnt' := hnt
    rw [hsel] at hnt'
    generalize g.inputs = l at hnt'
    rcases l with _ | ⟨a, rest⟩
    · simp [GateOp.eval]
    · have ha := hop' a (hnt' a (by simp)) x
      simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, GateOp.eval,
        List.headD_cons, Function.comp_apply]
      rw [ha]


lemma tb_triv (b : Fin 8) :
    trivB (fun x : Fin 6 → Bool => (false :: true :: List.ofFn x).getD b.val false) = true := by
  fin_cases b
  · exact triv_false _ (fun x => by simp)
  · exact triv_true _ (fun x => by simp)
  · exact triv_coord _ 0 (fun x => by simp [List.getD_eq_getElem?_getD])
  · exact triv_coord _ 1 (fun x => by simp [List.getD_eq_getElem?_getD])
  · exact triv_coord _ 2 (fun x => by simp [List.getD_eq_getElem?_getD])
  · exact triv_coord _ 3 (fun x => by simp [List.getD_eq_getElem?_getD])
  · exact triv_coord _ 4 (fun x => by simp [List.getD_eq_getElem?_getD])
  · exact triv_coord _ 5 (fun x => by simp [List.getD_eq_getElem?_getD])

-- The distinct nontrivial functions computed by the gates of C.
def S (C : Circuit) : Finset ((Fin 6 → Bool) → Bool) :=
  (Finset.univ.filter (fun k : Fin 11 => trivB (V C k) = false)).image (V C)

lemma firsts_le (C : Circuit) : (firsts C).length ≤ (S C).card := by
  have hnd : ((firsts C).map (V C)).Nodup := by
    apply List.Nodup.map_on _ (nodup_firsts C)
    intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (((isFirst_iff C b).mp ((mem_firsts C b).mp hb)).2 a h)
    · exact h
    · exact absurd hab.symm (((isFirst_iff C a).mp ((mem_firsts C a).mp ha)).2 b h)
  have hsub : ((firsts C).map (V C)).toFinset ⊆ S C := by
    intro F hF
    rw [List.mem_toFinset, List.mem_map] at hF
    obtain ⟨a, ha, rfl⟩ := hF
    unfold S
    rw [Finset.mem_image]
    exact ⟨a, by simp [((isFirst_iff C a).mp ((mem_firsts C a).mp ha)).1], rfl⟩
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map] at this
  exact this

lemma sel_len (g : Gate) : (sel g).length ≤ g.inputs.length := by
  unfold sel
  split
  · simp only [List.length_take]
    omega
  · exact le_refl _

lemma D_fan (C : Circuit) (hs : C.gates.length = 11) (hfan : FanInTwo C) (o : ℕ) :
    FanInTwo ⟨Dg C, o⟩ := by
  intro g hg
  simp only [Dg, List.mem_map] at hg
  obtain ⟨i, _, rfl⟩ := hg
  have hmem : C.gates.getD i.val dflt ∈ C.gates := by
    rw [getD_gate C hs]
    exact List.getElem_mem _
  obtain ⟨hop, hlen⟩ := hfan _ hmem
  refine ⟨hop, ?_⟩
  show ((sel (C.gates.getD i.val dflt)).map (rho C i)).length ≤ 2
  rw [List.length_map]
  exact le_trans (sel_len _) hlen

lemma D_big (C : Circuit) (o : ℕ) (x : Fin 6 → Bool) :
    ((⟨Dg C, o⟩ : Circuit).wires (List.ofFn x)).getD BIG false = false := by
  rw [wires_eq_foldl]
  apply foldl_step_getD_ge
  have := firsts_len C
  simp only [List.length_ofFn, Dg, List.length_map]
  unfold BIG
  omega

def outIdx (C : Circuit) : ℕ :=
  if C.output < 7 then inMap C.output
  else if h : C.output < 18 then
    if trivB (V C ⟨C.output - 7, by omega⟩) = false then 6 + pos C (fo C ⟨C.output - 7, by omega⟩)
    else
      match coord (V C ⟨C.output - 7, by omega⟩) with
      | some j => j.val
      | none => BIG
  else BIG

lemma out_correct (C : Circuit) (hs : C.gates.length = 11) (hfan : FanInTwo C)
    (hG : (fun x => C.eval (emb x)) ≠ (fun _ => true)) (x : Fin 6 → Bool) :
    (⟨Dg C, outIdx C⟩ : Circuit).eval (List.ofFn x) = C.eval (emb x) := by
  unfold Circuit.eval
  show ((⟨Dg C, outIdx C⟩ : Circuit).wires (List.ofFn x)).getD (outIdx C) false =
    (C.wires (emb x)).getD C.output false
  by_cases h7 : C.output < 7
  · have hv : (C.wires (emb x)).getD C.output false = (emb x).getD C.output false := by
      rw [wires_eq_foldl, foldl_step_getD_lt _ _ _ (by simp only [emb_length]; omega)]
    rw [hv]
    have hr : outIdx C = inMap C.output := by
      unfold outIdx
      simp only [h7, ↓reduceIte]
    rw [hr]
    generalize C.output = o at h7
    interval_cases o
    · rw [show inMap 0 = 0 from rfl, D_input C _ x 0 (by decide)]; rfl
    · rw [show inMap 1 = 1 from rfl, D_input C _ x 1 (by decide)]; rfl
    · rw [show inMap 2 = BIG from rfl, D_big]; rfl
    · rw [show inMap 3 = 2 from rfl, D_input C _ x 2 (by decide)]; rfl
    · rw [show inMap 4 = 3 from rfl, D_input C _ x 3 (by decide)]; rfl
    · rw [show inMap 5 = 4 from rfl, D_input C _ x 4 (by decide)]; rfl
    · rw [show inMap 6 = 5 from rfl, D_input C _ x 5 (by decide)]; rfl
  · by_cases h18 : C.output < 18
    · have hk : C.output - 7 < 11 := by omega
      have hvk : ∀ y, (C.wires (emb y)).getD C.output false = V C ⟨C.output - 7, hk⟩ y := by
        intro y
        unfold V
        congr 1
        show C.output = 7 + (C.output - 7)
        omega
      rw [hvk x]
      have hr : outIdx C =
          (if trivB (V C ⟨C.output - 7, hk⟩) = false then 6 + pos C (fo C ⟨C.output - 7, hk⟩)
           else match coord (V C ⟨C.output - 7, hk⟩) with
             | some j => j.val
             | none => BIG) := by
        unfold outIdx
        simp only [h7, ↓reduceIte, h18, ↓reduceDIte]
      rw [hr]
      by_cases ht : trivB (V C ⟨C.output - 7, hk⟩) = false
      · simp only [ht, ↓reduceIte]
        have hfo := fo_first C ⟨C.output - 7, hk⟩ ht
        rw [D_correct C hs hfan _ _ (pos_lt C _ hfo) x]
        simp only [get_pos C _ hfo]
        rw [fo_eq]
      · have ht' : trivB (V C ⟨C.output - 7, hk⟩) = true := by simpa using ht
        simp only [ht', Bool.true_eq_false, ↓reduceIte]
        cases hc : coord (V C ⟨C.output - 7, hk⟩) with
        | some j =>
          simp only
          rw [D_input C _ x j.val j.isLt, coord_some _ j hc]
        | none =>
          simp only
          rw [D_big]
          rcases triv_cases _ ht' with h0 | h1 | ⟨j, hj⟩
          · rw [h0]
          · exact absurd (by funext y; rw [Circuit.eval, hvk y, h1]) hG
          · exact absurd hj (coord_none _ hc j)
    · have hr : outIdx C = BIG := by
        unfold outIdx
        simp only [h7, ↓reduceIte, h18, ↓reduceDIte]
      rw [hr, D_big, wires_eq_foldl, foldl_step_getD_ge]
      simp only [emb_length, hs]
      omega

end PEqualNP.Outside.L_meta_4356

theorem PEqualNP.Outside.L_meta_4356 : have x1 : (Fin (6 : ℕ) → Bool) → List Bool := fun (x1 : Fin (6 : ℕ) → Bool) => [x1 (0 : Fin (6 : ℕ)), x1 (1 : Fin (6 : ℕ)), Bool.false, x1 (2 : Fin (6 : ℕ)), x1 (3 : Fin (6 : ℕ)), x1 (4 : Fin (6 : ℕ)), x1 (5 : Fin (6 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size = (11 : ℕ) →       PEqualNP.MetaComplexity.HasCircuitSize (6 : ℕ) (fun (x5 : Fin (6 : ℕ) → Bool) => x2.eval (x1 x5)) (7 : ℕ) ∨         have x5 : Fin (11 : ℕ) → (Fin (6 : ℕ) → Bool) → Bool := fun (x5 : Fin (11 : ℕ)) (x6 : Fin (6 : ℕ) → Bool) => (x2.wires (x1 x6)).getD ((7 : ℕ) + ↑x5) Bool.false;         ∃ (x6 : Fin (8 : ℕ) → Fin (11 : ℕ)), (∀ (x7 x8 : Fin (8 : ℕ)), x7 ≠ x8 → ∃ (x10 : Fin (6 : ℕ) → Bool), x5 (x6 x7) x10 ≠ x5 (x6 x8) x10) ∧ ∀ (x7 x8 : Fin (8 : ℕ)), ∃ (x9 : Fin (6 : ℕ) → Bool), x5 (x6 x7) x9 ≠ (Bool.false :: Bool.true :: List.ofFn x9).getD (↑x8) Bool.false := by
  intro x1 C hfan hsize
  have hs : C.gates.length = 11 := hsize
  by_cases hcard : 8 ≤ (PEqualNP.Outside.L_meta_4356.S C).card
  · right
    intro x5
    obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hcard
    let e : Fin 8 ≃ T := (T.equivFinOfCardEq hT).symm
    have hpre : ∀ a : Fin 8, ∃ k : Fin 11,
        PEqualNP.Outside.L_meta_4356.trivB (PEqualNP.Outside.L_meta_4356.V C k) = false ∧
        PEqualNP.Outside.L_meta_4356.V C k = (e a).val := by
      intro a
      have := hTS (e a).property
      unfold PEqualNP.Outside.L_meta_4356.S at this
      rw [Finset.mem_image] at this
      obtain ⟨k, hk, hkv⟩ := this
      exact ⟨k, (Finset.mem_filter.mp hk).2, hkv⟩
    choose σ hσ using hpre
    refine ⟨σ, ?_, ?_⟩
    · intro a b hab
      have hne : PEqualNP.Outside.L_meta_4356.V C (σ a) ≠ PEqualNP.Outside.L_meta_4356.V C (σ b) := by
        rw [(hσ a).2, (hσ b).2]
        intro h
        exact hab (e.injective (Subtype.ext h))
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    · intro a b
      by_contra hall
      push Not at hall
      have heq : PEqualNP.Outside.L_meta_4356.V C (σ a) =
          fun x : Fin 6 → Bool => (false :: true :: List.ofFn x).getD b.val false := funext hall
      have := PEqualNP.Outside.L_meta_4356.tb_triv b
      rw [← heq, (hσ a).1] at this
      exact Bool.false_ne_true this
  · left
    have hle : (PEqualNP.Outside.L_meta_4356.firsts C).length ≤ 7 := by
      have := PEqualNP.Outside.L_meta_4356.firsts_le C
      omega
    by_cases hG : (fun x => C.eval (PEqualNP.Outside.L_meta_4356.emb x)) = (fun _ => true)
    · refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩], 6⟩, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_singleton] at hg
        subst hg
        exact ⟨by simp, by simp⟩
      · show 1 ≤ 7
        omega
      · intro x
        have h1 := congrFun hG x
        show _ = C.eval (PEqualNP.Outside.L_meta_4356.emb x)
        rw [h1]
        rfl
    · refine ⟨⟨PEqualNP.Outside.L_meta_4356.Dg C, PEqualNP.Outside.L_meta_4356.outIdx C⟩,
        PEqualNP.Outside.L_meta_4356.D_fan C hs hfan _, ?_, ?_⟩
      · show (PEqualNP.Outside.L_meta_4356.Dg C).length ≤ 7
        simp only [PEqualNP.Outside.L_meta_4356.Dg, List.length_map]
        exact hle
      · intro x
        exact PEqualNP.Outside.L_meta_4356.out_correct C hs hfan hG x
