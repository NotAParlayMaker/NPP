import Mathlib
import PEqualNP.Defs

namespace LMeta590

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

private theorem ite_pos {α : Type} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by
  split_ifs
  rfl

private theorem ite_neg {α : Type} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by
  split_ifs
  rfl

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private theorem foldl_stepWire_length (gs : List Gate) (x : List Bool) :
    (gs.foldl stepWire x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, stepWire, ih]
    omega

private theorem foldl_stepWire_getD_of_lt (gs : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length) :
    (gs.foldl stepWire x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (stepWire x g).length := by
      simp [stepWire]
      omega
    rw [ih (stepWire x g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_left {α : Type} (l1 l2 : List α) (d : α) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_append_right_self {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

private theorem getD_of_ge {α : Type} (l : List α) (d : α) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

private def snocB {n : ℕ} (y : Fin n → Bool) (b : Bool) : Fin (n + 1) → Bool :=
  Fin.snoc (α := fun _ => Bool) y b

private theorem snocB_castSucc {n : ℕ} (y : Fin n → Bool) (b : Bool) (i : Fin n) :
    snocB y b i.castSucc = y i := by
  simp [snocB]

private theorem snocB_last {n : ℕ} (y : Fin n → Bool) (b : Bool) :
    snocB y b (Fin.last n) = b := by
  simp [snocB]

private theorem snocB_mk_n {n : ℕ} (y : Fin n → Bool) (b : Bool) (h : n < n + 1) :
    snocB y b ⟨n, h⟩ = b :=
  snocB_last y b

private def shift (n i : ℕ) : ℕ :=
  if i < n then i else i + 1

private def shiftGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shift n)⟩

private theorem shift_foldl_inv (n : ℕ) (gs : List Gate) (w w' : List Bool)
    (hlen : w'.length = w.length + 1)
    (hn : n ≤ w.length)
    (hinv : ∀ i, w'.getD (shift n i) false = w.getD i false) :
    ∀ i, ((gs.map (shiftGate n)).foldl stepWire w').getD (shift n i) false =
      (gs.foldl stepWire w).getD i false := by
  induction gs generalizing w w' with
  | nil => exact hinv
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have heval : (shiftGate n g).op.eval ((shiftGate n g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [shiftGate, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro a _
      exact hinv a
    apply ih (stepWire w g) (stepWire w' (shiftGate n g))
    · simp [stepWire, hlen]
    · simp [stepWire]; omega
    · intro i
      by_cases hi : i < w.length
      · by_cases hin : i < n
        · have h1 : shift n i = i := ite_pos hin
          rw [h1, stepWire, stepWire, getD_append_left w' _ _ i (by omega),
            getD_append_left w _ _ i hi]
          simpa [h1] using hinv i
        · have h1 : shift n i = i + 1 := ite_neg hin
          rw [h1, stepWire, stepWire, getD_append_left w' _ _ (i + 1) (by omega),
            getD_append_left w _ _ i hi]
          simpa [h1] using hinv i
      · by_cases heq : i = w.length
        · subst heq
          have h1 : shift n w.length = w.length + 1 := ite_neg (by omega)
          rw [h1, ← hlen, stepWire, stepWire, getD_append_right_self, getD_append_right_self, heval]
        · have h1 : shift n i = i + 1 := ite_neg (by omega)
          rw [h1, stepWire, stepWire,
            getD_of_ge (w' ++ _) _ (i + 1) (by simp [hlen]; omega),
            getD_of_ge (w ++ _) _ i (by simp; omega)]

private theorem forward_dir (n s : ℕ) (f : (Fin n → Bool) → Bool)
    (hf : HasCircuitSize n f s) :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s + 1 ∧ ∃ o1 o2 : ℕ,
      ∀ x : Fin (n + 1) → Bool,
        (C.wires (List.ofFn x)).getD o1 false = f (fun i : Fin n => x i.castSucc) ∧
        (C.wires (List.ofFn x)).getD o2 false = (x (Fin.last n) || f (fun i : Fin n => x i.castSucc)) := by
  rcases hf with ⟨C, hfan, hsize, heval⟩
  let o1 : ℕ := if C.output < n + C.gates.length then shift n C.output else (n + 1) + C.gates.length + 1
  let o2 : ℕ := (n + 1) + C.gates.length
  let C' : Circuit := ⟨C.gates.map (shiftGate n) ++ [⟨GateOp.or, [n, o1]⟩], o2⟩
  refine ⟨C', ?_, ?_, o1, o2, ?_⟩
  · intro g hg
    simp only [C', List.mem_append, List.mem_map, List.mem_singleton] at hg
    rcases hg with ⟨g0, hg0, rfl⟩ | rfl
    · obtain ⟨hop, hlen⟩ := hfan g0 hg0
      exact ⟨hop, by simpa [shiftGate] using hlen⟩
    · exact ⟨Or.inr (Or.inl rfl), by simp⟩
  · simp [C', Circuit.size] at hsize ⊢
    omega
  · intro x
    let y : Fin n → Bool := fun i => x i.castSucc
    have hbase : ∀ i, (List.ofFn x).getD (shift n i) false = (List.ofFn y).getD i false := by
      intro i
      by_cases hi : i < n
      · have h1 : shift n i = i := ite_pos hi
        rw [h1, getD_ofFn x i (by omega), getD_ofFn y i hi]
        rfl
      · have h1 : shift n i = i + 1 := ite_neg hi
        rw [h1, getD_of_ge (List.ofFn x) _ (i + 1) (by simp; omega),
          getD_of_ge (List.ofFn y) _ i (by simp; omega)]
    have hmain := shift_foldl_inv n C.gates (List.ofFn y) (List.ofFn x) (by simp) (by simp) hbase
    let w' := (C.gates.map (shiftGate n)).foldl stepWire (List.ofFn x)
    have hw'len : w'.length = (n + 1) + C.gates.length := by
      simp [w', foldl_stepWire_length]
    have ho1w' : w'.getD o1 false = f y := by
      have hev := heval y
      simp only [Circuit.eval, wires_eq_foldl] at hev
      rw [← hev]
      by_cases hlt : C.output < n + C.gates.length
      · have ho1eq : o1 = shift n C.output := ite_pos hlt
        rw [ho1eq]
        exact hmain C.output
      · have ho1eq : o1 = (n + 1) + C.gates.length + 1 := ite_neg hlt
        rw [ho1eq, getD_of_ge w' _ _ (by omega),
          getD_of_ge (C.gates.foldl stepWire (List.ofFn y)) _ _ (by rw [foldl_stepWire_length]; simp; omega)]
    have hnw' : w'.getD n false = x (Fin.last n) := by
      have h1 := foldl_stepWire_getD_of_lt (C.gates.map (shiftGate n)) (List.ofFn x) n (by simp)
      rw [h1, getD_ofFn x n (by omega)]
      rfl
    have hCwires : C'.wires (List.ofFn x) = stepWire w' ⟨GateOp.or, [n, o1]⟩ := by
      simp [C', wires_eq_foldl, List.foldl_append, w']
    rw [hCwires]
    constructor
    · by_cases hlt : C.output < n + C.gates.length
      · have ho1lt : o1 < w'.length := by
          have ho1eq : o1 = shift n C.output := ite_pos hlt
          rw [ho1eq, hw'len]
          unfold shift
          split_ifs <;> omega
        rw [stepWire, getD_append_left w' _ _ o1 ho1lt, ho1w']
      · have ho1eq : o1 = (n + 1) + C.gates.length + 1 := ite_neg hlt
        have ho1ge : (stepWire w' ⟨GateOp.or, [n, o1]⟩).length ≤ o1 := by
          simp [stepWire, hw'len, ho1eq]
        rw [getD_of_ge _ _ o1 ho1ge]
        have hev := heval y
        simp only [Circuit.eval, wires_eq_foldl] at hev
        rw [← hev, getD_of_ge _ _ C.output (by rw [foldl_stepWire_length]; simp; omega)]
    · have ho2eq : o2 = w'.length := by omega
      rw [ho2eq, stepWire, getD_append_right_self]
      simp only [GateOp.eval, List.map_cons, List.map_nil, hnw', ho1w', y]
      cases x (Fin.last n) <;> cases f (fun i => x i.castSucc) <;> rfl

private def effReads (n : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∧ n ∈ g.inputs) ∨
  (g.op = GateOp.or ∧ n ∈ g.inputs) ∨
  (g.op = GateOp.not ∧ g.inputs.head? = some n)

private theorem eval_eq_of_not_effReads (n : ℕ) (g : Gate) (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hno : ¬ effReads n g) (w1 w2 : List Bool)
    (heq : ∀ i, i ≠ n → w1.getD i false = w2.getD i false) :
    g.op.eval (g.inputs.map fun i => w1.getD i false) =
      g.op.eval (g.inputs.map fun i => w2.getD i false) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfan
  rcases hfan with hop | hop | hop
  · rw [hop]
    congr 1
    apply List.map_congr_left
    intro i hi
    apply heq i
    intro hin
    subst hin
    exact hno (Or.inl ⟨hop, hi⟩)
  · rw [hop]
    congr 1
    apply List.map_congr_left
    intro i hi
    apply heq i
    intro hin
    subst hin
    exact hno (Or.inr (Or.inl ⟨hop, hi⟩))
  · rw [hop]
    cases h : g.inputs with
    | nil => simp [GateOp.eval]
    | cons a tl =>
      simp only [List.map_cons, GateOp.eval, List.headD_cons]
      have ha : a ≠ n := by
        intro han
        subst han
        exact hno (Or.inr (Or.inr ⟨hop, by simp [h]⟩))
      rw [heq a ha]

private theorem wires_eq_of_no_effReads (n : ℕ) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hno : ∀ g ∈ gs, ¬ effReads n g)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length) (hn : n < w1.length)
    (heq : ∀ i, i ≠ n → w1.getD i false = w2.getD i false) :
    ∀ i, i ≠ n → (gs.foldl stepWire w1).getD i false = (gs.foldl stepWire w2).getD i false := by
  induction gs generalizing w1 w2 with
  | nil => exact heq
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hgfan := hfan g (List.mem_cons_self ..)
    have hgno := hno g (List.mem_cons_self ..)
    have hev := eval_eq_of_not_effReads n g hgfan hgno w1 w2 heq
    apply ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
      (stepWire w1 g) (stepWire w2 g)
    · simp [stepWire, hlen]
    · simp [stepWire]; omega
    · intro i hin
      by_cases hi : i < w1.length
      · rw [stepWire, stepWire, getD_append_left w1 _ _ i hi,
          getD_append_left w2 _ _ i (by omega)]
        exact heq i hin
      · by_cases heqi : i = w1.length
        · subst heqi
          rw [stepWire, stepWire, getD_append_right_self, hlen, getD_append_right_self, hev]
        · rw [stepWire, stepWire,
            getD_of_ge (w1 ++ _) _ i (by simp; omega),
            getD_of_ge (w2 ++ _) _ i (by simp [hlen]; omega)]

private def remap (n m j_del repl j i : ℕ) : ℕ :=
  if n + 1 + j ≤ i then n + m
  else if i < n then i
  else if i = n then n + m
  else if i < n + 1 + j_del then i - 1
  else if i = n + 1 + j_del then repl
  else i - 2

private def remapGate (n m j_del repl j : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap n m j_del repl j)⟩

private def delGatesFrom (n m j_del repl : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs =>
    if j = j_del then delGatesFrom n m j_del repl (j + 1) gs
    else remapGate n m j_del repl j g :: delGatesFrom n m j_del repl (j + 1) gs

private def delGates (n m j_del repl : ℕ) (gs : List Gate) : List Gate :=
  delGatesFrom n m j_del repl 0 gs

private def delGatesPrefix (n m j_del repl : ℕ) (gs : List Gate) (k : ℕ) : List Gate :=
  delGatesFrom n m j_del repl 0 (gs.take k)

private theorem delGatesFrom_append (n m j_del repl : ℕ) (j : ℕ) (gs1 gs2 : List Gate) :
    delGatesFrom n m j_del repl j (gs1 ++ gs2) =
      delGatesFrom n m j_del repl j gs1 ++ delGatesFrom n m j_del repl (j + gs1.length) gs2 := by
  induction gs1 generalizing j with
  | nil => simp [delGatesFrom]
  | cons g gs1 ih =>
    simp only [List.cons_append, delGatesFrom, List.length_cons]
    split_ifs
    · rw [ih (j + 1)]; congr 2; omega
    · rw [List.cons_append, ih (j + 1)]; congr 3; omega

private theorem delGatesFrom_length (n m j_del repl : ℕ) (j : ℕ) (gs : List Gate) :
    (delGatesFrom n m j_del repl j gs).length =
      if j ≤ j_del ∧ j_del < j + gs.length then gs.length - 1 else gs.length := by
  induction gs generalizing j with
  | nil => simp [delGatesFrom]
  | cons g gs ih =>
    simp only [delGatesFrom, List.length_cons]
    by_cases hj : j = j_del
    · rw [ite_pos hj, ih (j + 1)]
      split_ifs <;> omega
    · rw [ite_neg hj, List.length_cons, ih (j + 1)]
      split_ifs <;> omega

private theorem delGates_length (n m j_del repl : ℕ) (gs : List Gate) (hj : j_del < gs.length) :
    (delGates n m j_del repl gs).length = gs.length - 1 := by
  unfold delGates
  rw [delGatesFrom_length]
  split_ifs <;> omega

private theorem delGatesFrom_fanInTwo (n m j_del repl : ℕ) (j : ℕ) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ delGatesFrom n m j_del repl j gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing j with
  | nil => intro g hg; cases hg
  | cons g0 gs ih =>
    intro g hg
    simp only [delGatesFrom] at hg
    have ih' := ih (j + 1) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    split_ifs at hg
    · exact ih' g hg
    · simp only [List.mem_cons] at hg
      rcases hg with rfl | hg
      · obtain ⟨hop, hlen⟩ := hfan g0 (List.mem_cons_self ..)
        exact ⟨hop, by simpa [remapGate] using hlen⟩
      · exact ih' g hg

private theorem delGates_fanInTwo (n m j_del repl : ℕ) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ delGates n m j_del repl gs,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
  delGatesFrom_fanInTwo n m j_del repl 0 gs hfan

private theorem delGatesPrefix_eq_delGates (n m j_del repl : ℕ) (gs : List Gate) :
    delGatesPrefix n m j_del repl gs gs.length = delGates n m j_del repl gs := by
  simp [delGatesPrefix, delGates]

private theorem delGatesPrefix_succ (n m j_del repl : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    delGatesPrefix n m j_del repl gs (k + 1) =
      if k = j_del then delGatesPrefix n m j_del repl gs k
      else delGatesPrefix n m j_del repl gs k ++ [remapGate n m j_del repl k gs[k]] := by
  unfold delGatesPrefix
  rw [List.take_succ_eq_append_getElem hk, delGatesFrom_append]
  have hlen : (gs.take k).length = k := List.length_take_of_le (by omega)
  simp only [hlen, Nat.zero_add, delGatesFrom]
  split_ifs <;> simp

private theorem delGatesPrefix_length (n m j_del repl : ℕ) (gs : List Gate) (k : ℕ) (hk : k ≤ gs.length) :
    (delGatesPrefix n m j_del repl gs k).length = if k ≤ j_del then k else k - 1 := by
  unfold delGatesPrefix
  rw [delGatesFrom_length, List.length_take_of_le hk]
  split_ifs <;> omega

private theorem delete_gate_correct (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (b : Bool) (j_del : ℕ) (hj : j_del < C.gates.length) (repl : ℕ)
    (hrepl_bound : repl < n + j_del ∨ repl = n + C.gates.length)
    (hno_other : b = true → ∀ j (hj' : j < C.gates.length), j ≠ j_del → ¬ effReads n C.gates[j])
    (hrepl_val : ∀ y : Fin n → Bool,
      let w0 := ((C.gates.take j_del).foldl stepWire (List.ofFn (snocB y b)))
      let w0' := ((delGatesPrefix n C.gates.length j_del repl C.gates j_del).foldl stepWire (List.ofFn y))
      w0'.getD repl false = C.gates[j_del].op.eval (C.gates[j_del].inputs.map fun i => w0.getD i false))
    (y : Fin n → Bool) :
    let m := C.gates.length
    let w := C.wires (List.ofFn (snocB y b))
    let w' := (delGates n m j_del repl C.gates).foldl stepWire (List.ofFn y)
    ∀ i, i ≠ n → w'.getD (remap n m j_del repl m i) false = w.getD i false := by
  intro m
  have hinv : ∀ k (hk : k ≤ m),
      let wk := (C.gates.take k).foldl stepWire (List.ofFn (snocB y b))
      let wk' := (delGatesPrefix n m j_del repl C.gates k).foldl stepWire (List.ofFn y)
      (∀ i < n, wk'.getD i false = wk.getD i false) ∧
      (∀ t < k, t < j_del → wk'.getD (n + t) false = wk.getD (n + 1 + t) false) ∧
      (∀ t < k, j_del < t → wk'.getD (n + t - 1) false = wk.getD (n + 1 + t) false) ∧
      (j_del < k → wk'.getD repl false = wk.getD (n + 1 + j_del) false) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i hi
        simp only [List.take_zero, List.foldl_nil, delGatesPrefix, delGatesFrom]
        rw [getD_ofFn y i hi, getD_ofFn (snocB y b) i (by omega)]
        exact (snocB_castSucc y b ⟨i, hi⟩).symm
      · intro t ht; omega
      · intro t ht; omega
      · intro h; omega
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2, ih3, ih4⟩ := ih (by omega)
      set wk := (C.gates.take k).foldl stepWire (List.ofFn (snocB y b))
      set wk' := (delGatesPrefix n m j_del repl C.gates k).foldl stepWire (List.ofFn y)
      have hwk_len : wk.length = n + 1 + k := by
        simp [wk, foldl_stepWire_length, List.length_take_of_le (show k ≤ C.gates.length by omega)]
      have hwk'_len : wk'.length = n + (if k ≤ j_del then k else k - 1) := by
        simp [wk', foldl_stepWire_length, delGatesPrefix_length n m j_del repl C.gates k (by omega)]
      have hwk_succ : (C.gates.take (k + 1)).foldl stepWire (List.ofFn (snocB y b)) =
          stepWire wk C.gates[k] := by
        rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append]
        rfl
      have hwk'_succ : (delGatesPrefix n m j_del repl C.gates (k + 1)).foldl stepWire (List.ofFn y) =
          if k = j_del then wk' else stepWire wk' (remapGate n m j_del repl k C.gates[k]) := by
        rw [delGatesPrefix_succ n m j_del repl C.gates k (by omega)]
        split_ifs <;> simp [wk', List.foldl_append]
      rw [hwk_succ, hwk'_succ]
      by_cases hkj : k = j_del
      · subst hkj
        rw [ite_pos rfl]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i hi
          rw [stepWire, getD_append_left wk _ _ i (by omega)]
          exact ih1 i hi
        · intro t ht htj
          rw [stepWire, getD_append_left wk _ _ (n + 1 + t) (by omega)]
          exact ih2 t htj htj
        · intro t ht htj; omega
        · intro _
          rw [stepWire, ← hwk_len, getD_append_right_self]
          exact hrepl_val y
      · rw [ite_neg hkj]
        have hwire_match : ∀ i, i ≠ n → wk'.getD (remap n m j_del repl k i) false = wk.getD i false := by
          intro i hin
          unfold remap
          by_cases hge : n + 1 + k ≤ i
          · rw [ite_pos hge,
              getD_of_ge wk' _ _ (by rw [hwk'_len]; split_ifs <;> omega),
              getD_of_ge wk _ _ (by rw [hwk_len]; omega)]
          · rw [ite_neg hge]
            by_cases hlt : i < n
            · rw [ite_pos hlt]
              exact ih1 i hlt
            · rw [ite_neg hlt, ite_neg hin]
              by_cases hltj : i < n + 1 + j_del
              · rw [ite_pos hltj]
                have := ih2 (i - (n + 1)) (by omega) (by omega)
                have he1 : n + (i - (n + 1)) = i - 1 := by omega
                have he2 : n + 1 + (i - (n + 1)) = i := by omega
                rw [he1, he2] at this
                exact this
              · rw [ite_neg hltj]
                by_cases heqj : i = n + 1 + j_del
                · rw [ite_pos heqj, heqj]
                  exact ih4 (by omega)
                · rw [ite_neg heqj]
                  have := ih3 (i - (n + 1)) (by omega) (by omega)
                  have he1 : n + (i - (n + 1)) - 1 = i - 2 := by omega
                  have he2 : n + 1 + (i - (n + 1)) = i := by omega
                  rw [he1, he2] at this
                  exact this
        have heval_k : (remapGate n m j_del repl k C.gates[k]).op.eval
            ((remapGate n m j_del repl k C.gates[k]).inputs.map fun i => wk'.getD i false) =
            C.gates[k].op.eval (C.gates[k].inputs.map fun i => wk.getD i false) := by
          cases hb : b
          · simp only [remapGate, List.map_map, Function.comp_def]
            congr 1
            apply List.map_congr_left
            intro i _
            by_cases hin : i = n
            · rw [hin]
              have hrem : remap n m j_del repl k n = n + m := by
                unfold remap
                rw [ite_neg (by omega), ite_neg (by omega), ite_pos rfl]
              rw [hrem, getD_of_ge wk' _ _ (by rw [hwk'_len]; split_ifs <;> omega)]
              have hwn : wk.getD n false = false := by
                rw [foldl_stepWire_getD_of_lt _ _ n (by simp), getD_ofFn (snocB y b) n (by omega),
                  snocB_mk_n, hb]
              rw [hwn]
            · exact hwire_match i hin
          · have hno := hno_other hb k (by omega) hkj
            have hgf := (hfan C.gates[k] (List.getElem_mem ..)).1
            simp only [remapGate, List.map_map, Function.comp_def]
            let w_alt : List Bool := List.ofFn (fun idx : Fin wk.length => wk'.getD (remap n m j_del repl k idx.val) false)
            have hmap : (C.gates[k].inputs.map (fun x => wk'.getD (remap n m j_del repl k x) false)) =
                (C.gates[k].inputs.map (fun x => w_alt.getD x false)) := by
              apply List.map_congr_left
              intro i _
              by_cases hilt : i < wk.length
              · rw [getD_ofFn _ i hilt]
              · have hrem : remap n m j_del repl k i = n + m := by
                  unfold remap; rw [ite_pos (by omega)]
                rw [hrem, getD_of_ge wk' _ _ (by rw [hwk'_len]; split_ifs <;> omega),
                  getD_of_ge w_alt _ _ (by simp [w_alt]; omega)]
            rw [hmap]
            apply eval_eq_of_not_effReads n C.gates[k] hgf hno w_alt wk
            intro i hin
            by_cases hilt : i < wk.length
            · rw [getD_ofFn _ i hilt]
              exact hwire_match i hin
            · rw [getD_of_ge w_alt _ _ (by simp [w_alt]; omega), getD_of_ge wk _ _ (by omega)]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro i hi
          rw [stepWire, stepWire, getD_append_left wk' _ _ i (by omega),
            getD_append_left wk _ _ i (by omega)]
          exact ih1 i hi
        · intro t ht htj
          by_cases htk : t < k
          · rw [stepWire, stepWire, getD_append_left wk' _ _ (n + t) (by rw [hwk'_len]; split_ifs <;> omega),
              getD_append_left wk _ _ (n + 1 + t) (by omega)]
            exact ih2 t htk htj
          · have hteq : t = k := by omega
            subst hteq
            have hwk'_eq : n + t = wk'.length := by rw [hwk'_len, ite_pos (by omega)]
            rw [stepWire, stepWire, hwk'_eq, getD_append_right_self, ← hwk_len, getD_append_right_self, heval_k]
        · intro t ht htj
          by_cases htk : t < k
          · rw [stepWire, stepWire, getD_append_left wk' _ _ (n + t - 1) (by rw [hwk'_len]; split_ifs <;> omega),
              getD_append_left wk _ _ (n + 1 + t) (by omega)]
            exact ih3 t htk htj
          · have hteq : t = k := by omega
            subst hteq
            have hwk'_eq : n + t - 1 = wk'.length := by rw [hwk'_len, ite_neg (by omega)]; omega
            rw [stepWire, stepWire, hwk'_eq, getD_append_right_self, ← hwk_len, getD_append_right_self, heval_k]
        · intro hjlt
          have hjk : j_del < k := by omega
          have hrepl_lt_or : repl < wk'.length ∨ repl = n + m := by
            rcases hrepl_bound with h1 | h2
            · left; rw [hwk'_len, ite_neg (by omega)]; omega
            · right; exact h2
          rcases hrepl_lt_or with hlt | heq
          · rw [stepWire, stepWire, getD_append_left wk' _ _ repl hlt,
              getD_append_left wk _ _ (n + 1 + j_del) (by omega)]
            exact ih4 hjk
          · rw [heq, stepWire, stepWire, getD_of_ge (wk' ++ _) _ (n + m) (by simp [hwk'_len]; split_ifs <;> omega),
              getD_append_left wk _ _ (n + 1 + j_del) (by omega)]
            have h4 := ih4 hjk
            rw [heq, getD_of_ge wk' _ (n + m) (by rw [hwk'_len]; split_ifs <;> omega)] at h4
            exact h4
  obtain ⟨h1, h2, h3, h4⟩ := hinv m le_rfl
  intro w w' i hin
  have hw_eq : w = (C.gates.take m).foldl stepWire (List.ofFn (snocB y b)) := by
    simp [w, wires_eq_foldl, m]
  have hw'_eq : w' = (delGatesPrefix n m j_del repl C.gates m).foldl stepWire (List.ofFn y) := by
    simp [w', delGatesPrefix_eq_delGates, m]
  rw [hw_eq, hw'_eq]
  unfold remap
  by_cases hge : n + 1 + m ≤ i
  · rw [ite_pos hge,
      getD_of_ge _ _ (n + m) (by rw [foldl_stepWire_length, delGatesPrefix_length _ _ _ _ _ _ le_rfl]; simp; split_ifs <;> omega),
      getD_of_ge _ _ i (by rw [foldl_stepWire_length]; simp [m]; omega)]
  · rw [ite_neg hge]
    by_cases hlt : i < n
    · rw [ite_pos hlt]; exact h1 i hlt
    · rw [ite_neg hlt, ite_neg hin]
      by_cases hltj : i < n + 1 + j_del
      · rw [ite_pos hltj]
        have := h2 (i - (n + 1)) (by omega) (by omega)
        have he1 : n + (i - (n + 1)) = i - 1 := by omega
        have he2 : n + 1 + (i - (n + 1)) = i := by omega
        rw [he1, he2] at this
        exact this
      · rw [ite_neg hltj]
        by_cases heqj : i = n + 1 + j_del
        · rw [ite_pos heqj, heqj]; exact h4 hj
        · rw [ite_neg heqj]
          have := h3 (i - (n + 1)) (by omega) (by omega)
          have he1 : n + (i - (n + 1)) - 1 = i - 2 := by omega
          have he2 : n + 1 + (i - (n + 1)) = i := by omega
          rw [he1, he2] at this
          exact this

private theorem backward_dir (n s : ℕ) (f : (Fin n → Bool) → Bool)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y')
    (hC : ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s + 1 ∧ ∃ o1 o2 : ℕ,
      ∀ x : Fin (n + 1) → Bool,
        (C.wires (List.ofFn x)).getD o1 false = f (fun i : Fin n => x i.castSucc) ∧
        (C.wires (List.ofFn x)).getD o2 false = (x (Fin.last n) || f (fun i : Fin n => x i.castSucc))) :
    HasCircuitSize n f s := by
  rcases hC with ⟨C, hfan, hsize, o1, o2, houts⟩
  rcases hnc with ⟨y0, y1, hne⟩
  have hfalse : ∃ y : Fin n → Bool, f y = false := by
    cases h0 : f y0
    · exact ⟨y0, h0⟩
    · cases h1 : f y1
      · exact ⟨y1, h1⟩
      · exact absurd (h0.trans h1.symm) hne
  have htrue : ∃ y : Fin n → Bool, f y = true := by
    cases h0 : f y0
    · cases h1 : f y1
      · exact absurd (h0.trans h1.symm) hne
      · exact ⟨y1, h1⟩
    · exact ⟨y0, h0⟩
  rcases hfalse with ⟨yf, hyf⟩
  rcases htrue with ⟨yt, hyt⟩
  have hcast : ∀ (y : Fin n → Bool) (b : Bool), (fun i : Fin n => snocB y b i.castSucc) = y := by
    intro y b; funext i; exact snocB_castSucc y b i
  have ho1_ne_n : o1 ≠ n := by
    intro h
    have h1 := (houts (snocB yf true)).1
    rw [h, hcast, hyf, wires_eq_foldl, foldl_stepWire_getD_of_lt _ _ n (by simp),
      getD_ofFn _ n (by omega), snocB_mk_n] at h1
    exact absurd h1 (by decide)
  have ho2_ne_n : o2 ≠ n := by
    intro h
    have h0 := (houts (snocB yt false)).2
    rw [h, hcast, hyt, wires_eq_foldl, foldl_stepWire_getD_of_lt _ _ n (by simp),
      getD_ofFn _ n (by omega), snocB_mk_n, snocB_last] at h0
    exact absurd h0 (by decide)
  have hex_eff : ∃ j : ℕ, ∃ hj : j < C.gates.length, effReads n C.gates[j] := by
    by_contra hno
    push Not at hno
    have hno' : ∀ g ∈ C.gates, ¬ effReads n g := by
      intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
      exact hno j hj
    have heq_in : ∀ i, i ≠ n → (List.ofFn (snocB yf false)).getD i false =
        (List.ofFn (snocB yf true)).getD i false := by
      intro i hin
      by_cases hi : i < n
      · rw [getD_ofFn _ i (by omega), getD_ofFn _ i (by omega)]
        exact (snocB_castSucc yf false ⟨i, hi⟩).trans (snocB_castSucc yf true ⟨i, hi⟩).symm
      · rw [getD_of_ge _ _ i (by simp; omega), getD_of_ge _ _ i (by simp; omega)]
    have hsame := wires_eq_of_no_effReads n C.gates (fun g hg => (hfan g hg).1) hno'
      (List.ofFn (snocB yf false)) (List.ofFn (snocB yf true)) (by simp) (by simp) heq_in o2 ho2_ne_n
    have h0 := (houts (snocB yf false)).2
    have h1 := (houts (snocB yf true)).2
    rw [hcast, hyf, snocB_last] at h0 h1
    simp only [Bool.false_or, Bool.true_or, wires_eq_foldl] at h0 h1
    rw [h0, h1] at hsame
    exact absurd hsame (by decide)
  let m := C.gates.length
  have finish : ∀ (b : Bool) (j_del : ℕ) (hj : j_del < m) (repl : ℕ),
      (repl < n + j_del ∨ repl = n + m) →
      (b = true → ∀ j (hj' : j < m), j ≠ j_del → ¬ effReads n C.gates[j]) →
      (∀ y : Fin n → Bool,
        let w0 := ((C.gates.take j_del).foldl stepWire (List.ofFn (snocB y b)))
        let w0' := ((delGatesPrefix n m j_del repl C.gates j_del).foldl stepWire (List.ofFn y))
        w0'.getD repl false = C.gates[j_del].op.eval (C.gates[j_del].inputs.map fun i => w0.getD i false)) →
      HasCircuitSize n f s := by
    intro b j_del hj repl hrb hno hrv
    refine ⟨⟨delGates n m j_del repl C.gates, remap n m j_del repl m o1⟩, ?_, ?_, ?_⟩
    · exact delGates_fanInTwo n m j_del repl C.gates hfan
    · simp only [Circuit.size, delGates_length n m j_del repl C.gates hj]
      simp only [Circuit.size] at hsize
      omega
    · intro y
      simp only [Circuit.eval, wires_eq_foldl]
      rw [delete_gate_correct n C hfan b j_del hj repl hrb hno hrv y o1 ho1_ne_n]
      have h0 := (houts (snocB y b)).1
      rw [hcast] at h0
      exact h0
  by_cases handor : ∃ j : ℕ, ∃ hj : j < m, (C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) ∧ n ∈ C.gates[j].inputs
  · rcases handor with ⟨j_del, hj, hop, hnin⟩
    rcases hop with hand | hor
    · apply finish false j_del hj (n + m) (Or.inr rfl) (by intro h; cases h)
      intro y
      simp only
      have hlen' : ((delGatesPrefix n m j_del (n + m) C.gates j_del).foldl stepWire (List.ofFn y)).length = n + j_del := by
        rw [foldl_stepWire_length, delGatesPrefix_length n m j_del (n + m) C.gates j_del (by omega)]
        simp
      rw [getD_of_ge _ _ (n + m) (by omega), hand, GateOp.eval]
      symm
      rw [List.all_eq_false]
      refine ⟨false, ?_, by decide⟩
      rw [List.mem_map]
      refine ⟨n, hnin, ?_⟩
      rw [foldl_stepWire_getD_of_lt _ _ n (by simp), getD_ofFn _ n (by omega), snocB_mk_n]
    · have hlen_in : C.gates[j_del].inputs.length ≤ 2 := (hfan C.gates[j_del] (List.getElem_mem ..)).2
      have hother_or : (∀ a ∈ C.gates[j_del].inputs, a = n) ∨
          ∃ a, a ≠ n ∧ (C.gates[j_del].inputs = [n, a] ∨ C.gates[j_del].inputs = [a, n]) := by
        cases hin : C.gates[j_del].inputs with
        | nil => rw [hin] at hnin; cases hnin
        | cons a tl =>
          cases tl with
          | nil =>
            left; intro x hx; rw [hin] at hnin; simp at hnin hx; omega
          | cons b tl2 =>
            cases tl2 with
            | nil =>
              rw [hin] at hnin; simp at hnin
              rcases hnin with rfl | rfl
              · by_cases hbn : b = n
                · left; intro x hx; simp at hx; rcases hx with rfl | rfl <;> omega
                · right; exact ⟨b, hbn, Or.inl rfl⟩
              · by_cases han : a = n
                · left; intro x hx; simp at hx; rcases hx with rfl | rfl <;> omega
                · right; exact ⟨a, han, Or.inr rfl⟩
            | cons _ _ => rw [hin] at hlen_in; simp at hlen_in
      rcases hother_or with halln | ⟨a, han, hin_eq⟩
      · apply finish false j_del hj (n + m) (Or.inr rfl) (by intro h; cases h)
        intro y
        simp only
        have hlen' : ((delGatesPrefix n m j_del (n + m) C.gates j_del).foldl stepWire (List.ofFn y)).length = n + j_del := by
          rw [foldl_stepWire_length, delGatesPrefix_length n m j_del (n + m) C.gates j_del (by omega)]
          simp
        rw [getD_of_ge _ _ (n + m) (by omega), hor, GateOp.eval]
        symm
        rw [List.any_eq_false]
        intro x hx
        rw [List.mem_map] at hx
        rcases hx with ⟨u, hu, rfl⟩
        have hun := halln u hu
        rw [hun, foldl_stepWire_getD_of_lt _ _ n (by simp), getD_ofFn _ n (by omega), snocB_mk_n]
        decide
      · let repl : ℕ := if n + 1 + j_del ≤ a then n + m else if a < n then a else a - 1
        have hrb : repl < n + j_del ∨ repl = n + m := by
          simp only [repl]
          split_ifs <;> omega
        apply finish false j_del hj repl hrb (by intro h; cases h)
        intro y
        simp only
        have hwn : ((C.gates.take j_del).foldl stepWire (List.ofFn (snocB y false))).getD n false = false := by
          rw [foldl_stepWire_getD_of_lt _ _ n (by simp), getD_ofFn _ n (by omega), snocB_mk_n]
        have hev_a : C.gates[j_del].op.eval (C.gates[j_del].inputs.map fun i =>
            ((C.gates.take j_del).foldl stepWire (List.ofFn (snocB y false))).getD i false) =
            ((C.gates.take j_del).foldl stepWire (List.ofFn (snocB y false))).getD a false := by
          rw [hor]
          rcases hin_eq with heq | heq
          · rw [heq]; simp only [GateOp.eval, List.map_cons, List.map_nil, hwn]
            cases ((C.gates.take j_del).foldl stepWire (List.ofFn (snocB y false))).getD a false <;> rfl
          · rw [heq]; simp only [GateOp.eval, List.map_cons, List.map_nil, hwn]
            cases ((C.gates.take j_del).foldl stepWire (List.ofFn (snocB y false))).getD a false <;> rfl
        rw [hev_a]
        have hprefix_eq : ∀ k (hk : k ≤ j_del),
            let wk := (C.gates.take k).foldl stepWire (List.ofFn (snocB y false))
            let wk' := (delGatesPrefix n m j_del repl C.gates k).foldl stepWire (List.ofFn y)
            (∀ i < n, wk'.getD i false = wk.getD i false) ∧
            (∀ t < k, wk'.getD (n + t) false = wk.getD (n + 1 + t) false) := by
          intro k
          induction k with
          | zero =>
            intro _
            refine ⟨?_, fun t ht => by omega⟩
            intro i hi
            simp only [List.take_zero, List.foldl_nil, delGatesPrefix, delGatesFrom]
            rw [getD_ofFn y i hi, getD_ofFn (snocB y false) i (by omega)]
            exact (snocB_castSucc y false ⟨i, hi⟩).symm
          | succ k ih =>
            intro hk
            obtain ⟨ih1, ih2⟩ := ih (by omega)
            set wk := (C.gates.take k).foldl stepWire (List.ofFn (snocB y false))
            set wk' := (delGatesPrefix n m j_del repl C.gates k).foldl stepWire (List.ofFn y)
            have hwk_len : wk.length = n + 1 + k := by
              simp [wk, foldl_stepWire_length, List.length_take_of_le (show k ≤ C.gates.length by omega)]
            have hwk'_len : wk'.length = n + k := by
              simp [wk', foldl_stepWire_length, delGatesPrefix_length n m j_del repl C.gates k (by omega),
                ite_pos (show k ≤ j_del by omega)]
            rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append,
              delGatesPrefix_succ n m j_del repl C.gates k (by omega),
              ite_neg (by omega), List.foldl_append]
            change (∀ i < n, (stepWire wk' (remapGate n m j_del repl k C.gates[k])).getD i false =
                (stepWire wk C.gates[k]).getD i false) ∧
              (∀ t < k + 1, (stepWire wk' (remapGate n m j_del repl k C.gates[k])).getD (n + t) false =
                (stepWire wk C.gates[k]).getD (n + 1 + t) false)
            have hevk : (remapGate n m j_del repl k C.gates[k]).op.eval
                ((remapGate n m j_del repl k C.gates[k]).inputs.map fun i => wk'.getD i false) =
                C.gates[k].op.eval (C.gates[k].inputs.map fun i => wk.getD i false) := by
              simp only [remapGate, List.map_map, Function.comp_def]
              congr 1
              apply List.map_congr_left
              intro i _
              unfold remap
              by_cases hge : n + 1 + k ≤ i
              · rw [ite_pos hge,
                  getD_of_ge wk' _ _ (by rw [hwk'_len]; omega),
                  getD_of_ge wk _ _ (by rw [hwk_len]; omega)]
              · rw [ite_neg hge]
                by_cases hlt : i < n
                · rw [ite_pos hlt]; exact ih1 i hlt
                · rw [ite_neg hlt]
                  by_cases hin : i = n
                  · rw [ite_pos hin, hin,
                      getD_of_ge wk' _ _ (by rw [hwk'_len]; omega),
                      foldl_stepWire_getD_of_lt _ _ n (by simp), getD_ofFn _ n (by omega), snocB_mk_n]
                  · rw [ite_neg hin, ite_pos (by omega)]
                    have := ih2 (i - (n + 1)) (by omega)
                    have he1 : n + (i - (n + 1)) = i - 1 := by omega
                    have he2 : n + 1 + (i - (n + 1)) = i := by omega
                    rw [he1, he2] at this
                    exact this
            refine ⟨?_, ?_⟩
            · intro i hi
              rw [stepWire, stepWire, getD_append_left wk' _ _ i (by omega),
                getD_append_left wk _ _ i (by omega)]
              exact ih1 i hi
            · intro t ht
              by_cases htk : t < k
              · rw [stepWire, stepWire, getD_append_left wk' _ _ (n + t) (by omega),
                  getD_append_left wk _ _ (n + 1 + t) (by omega)]
                exact ih2 t htk
              · have hteq : t = k := by omega
                subst hteq
                rw [stepWire, stepWire, ← hwk'_len, getD_append_right_self, ← hwk_len, getD_append_right_self, hevk]
        obtain ⟨hp1, hp2⟩ := hprefix_eq j_del le_rfl
        by_cases hge : n + 1 + j_del ≤ a
        · have hrepl_eq : repl = n + m := ite_pos hge
          rw [hrepl_eq,
            getD_of_ge _ _ (n + m) (by rw [foldl_stepWire_length, delGatesPrefix_length _ _ _ _ _ _ (by omega)]; simp; omega),
            getD_of_ge _ _ a (by rw [foldl_stepWire_length, List.length_take_of_le (by omega)]; simp; omega)]
        · by_cases hlt : a < n
          · have hrepl_eq : repl = a := by simp only [repl, ite_neg hge, ite_pos hlt]
            conv_lhs => arg 2; rw [hrepl_eq]
            exact hp1 a hlt
          · have hrepl_eq : repl = a - 1 := by simp only [repl, ite_neg hge, ite_neg hlt]
            conv_lhs => arg 2; rw [hrepl_eq]
            have := hp2 (a - (n + 1)) (by omega)
            have he1 : n + (a - (n + 1)) = a - 1 := by omega
            have he2 : n + 1 + (a - (n + 1)) = a := by omega
            rw [he1, he2] at this
            exact this
  · push Not at handor
    rcases hex_eff with ⟨j0, hj0, heff0⟩
    have hnot_only : ∀ j (hj : j < m), effReads n C.gates[j] →
        C.gates[j].op = GateOp.not ∧ C.gates[j].inputs.head? = some n := by
      intro j hj heff
      rcases heff with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
      · exact absurd h2 (handor j hj (Or.inl h1))
      · exact absurd h2 (handor j hj (Or.inr h1))
      · exact h3
    obtain ⟨hnot0, hhead0⟩ := hnot_only j0 hj0 heff0
    by_cases hsecond : ∃ j1 : ℕ, ∃ hj1 : j1 < m, j1 ≠ j0 ∧ effReads n C.gates[j1]
    · rcases hsecond with ⟨j1, hj1, hne01, heff1⟩
      obtain ⟨hnot1, hhead1⟩ := hnot_only j1 hj1 heff1
      have hpair : ∃ ja jb : ℕ, ∃ (hja : ja < m) (hjb : jb < m), ja < jb ∧
          C.gates[ja].op = GateOp.not ∧ C.gates[ja].inputs.head? = some n ∧
          C.gates[jb].op = GateOp.not ∧ C.gates[jb].inputs.head? = some n := by
        by_cases hlt : j0 < j1
        · exact ⟨j0, j1, hj0, hj1, hlt, hnot0, hhead0, hnot1, hhead1⟩
        · exact ⟨j1, j0, hj1, hj0, by omega, hnot1, hhead1, hnot0, hhead0⟩
      rcases hpair with ⟨ja, jb, hja, hjb, hjab, hnota, hheada, hnotb, hheadb⟩
      apply finish false jb hjb (n + ja) (Or.inl (by omega)) (by intro h; cases h)
      intro y
      simp only
      have hrb_eval : C.gates[jb].op.eval (C.gates[jb].inputs.map fun i =>
          ((C.gates.take jb).foldl stepWire (List.ofFn (snocB y false))).getD i false) = true := by
        rw [hnotb]
        cases h : C.gates[jb].inputs with
        | nil => rw [h] at hheadb; cases hheadb
        | cons a tl =>
          rw [h] at hheadb
          simp only [List.head?_cons, Option.some.injEq] at hheadb
          rw [hheadb]
          simp only [List.map_cons, GateOp.eval, List.headD_cons]
          rw [foldl_stepWire_getD_of_lt _ _ n (by simp), getD_ofFn _ n (by omega), snocB_mk_n]
          rfl
      rw [hrb_eval]
      have hja_in : ((delGatesPrefix n m jb (n + ja) C.gates jb).foldl stepWire (List.ofFn y)).getD (n + ja) false =
          ((delGatesPrefix n m jb (n + ja) C.gates (ja + 1)).foldl stepWire (List.ofFn y)).getD (n + ja) false := by
        have hsplit : delGatesPrefix n m jb (n + ja) C.gates jb =
            delGatesPrefix n m jb (n + ja) C.gates (ja + 1) ++
              delGatesFrom n m jb (n + ja) (ja + 1) ((C.gates.take jb).drop (ja + 1)) := by
          unfold delGatesPrefix
          have htake_eq : C.gates.take jb = C.gates.take (ja + 1) ++ (C.gates.take jb).drop (ja + 1) := by
            have h1 : (C.gates.take jb).take (ja + 1) = C.gates.take (ja + 1) := by
              rw [List.take_take, Nat.min_eq_left (by omega)]
            rw [← h1, List.take_append_drop]
          conv_lhs => rw [htake_eq]
          rw [delGatesFrom_append]
          simp [List.length_take_of_le (show ja + 1 ≤ C.gates.length by omega)]
        rw [hsplit, List.foldl_append, foldl_stepWire_getD_of_lt]
        rw [foldl_stepWire_length, delGatesPrefix_length _ _ _ _ _ _ (by omega),
          ite_pos (by omega)]
        simp
      rw [hja_in, delGatesPrefix_succ n m jb (n + ja) C.gates ja (by omega),
        ite_neg (by omega), List.foldl_append]
      set wa := (delGatesPrefix n m jb (n + ja) C.gates ja).foldl stepWire (List.ofFn y)
      have hwa_len : wa.length = n + ja := by
        rw [foldl_stepWire_length, delGatesPrefix_length _ _ _ _ _ _ (by omega),
          ite_pos (by omega)]
        simp
      change (stepWire wa (remapGate n m jb (n + ja) ja C.gates[ja])).getD (n + ja) false = true
      conv_lhs => arg 2; rw [← hwa_len]
      rw [stepWire, getD_append_right_self]
      simp only [remapGate, hnota]
      cases h : C.gates[ja].inputs with
      | nil => rw [h] at hheada; cases hheada
      | cons a tl =>
        rw [h] at hheada
        simp only [List.head?_cons, Option.some.injEq] at hheada
        rw [hheada]
        simp only [List.map_cons, GateOp.eval, List.headD_cons]
        have hrem : remap n m jb (n + ja) ja n = n + m := by
          unfold remap
          rw [ite_neg (by omega), ite_neg (by omega), ite_pos rfl]
        rw [hrem, getD_of_ge wa _ (n + m) (by omega)]
        rfl
    · push Not at hsecond
      apply finish true j0 hj0 (n + m) (Or.inr rfl)
      · intro _ j hj hne
        exact hsecond j hj hne
      · intro y
        simp only
        have hlen' : ((delGatesPrefix n m j0 (n + m) C.gates j0).foldl stepWire (List.ofFn y)).length = n + j0 := by
          rw [foldl_stepWire_length, delGatesPrefix_length n m j0 (n + m) C.gates j0 (by omega)]
          simp
        rw [getD_of_ge _ _ (n + m) (by omega), hnot0]
        cases h : C.gates[j0].inputs with
        | nil => rw [h] at hhead0; cases hhead0
        | cons a tl =>
          rw [h] at hhead0
          simp only [List.head?_cons, Option.some.injEq] at hhead0
          rw [hhead0]
          simp only [List.map_cons, GateOp.eval, List.headD_cons]
          rw [foldl_stepWire_getD_of_lt _ _ n (by simp), getD_ofFn _ n (by omega), snocB_mk_n]
          rfl

end LMeta590

theorem PEqualNP.Outside.L_meta_590 : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), (∃ y y' : Fin n → Bool, f y ≠ f y') → ((∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s + 1 ∧ ∃ o1 o2 : ℕ, ∀ x : Fin (n + 1) → Bool, (C.wires (List.ofFn x)).getD o1 false = f (fun i : Fin n => x i.castSucc) ∧ (C.wires (List.ofFn x)).getD o2 false = (x (Fin.last n) || f (fun i : Fin n => x i.castSucc))) ↔ PEqualNP.MetaComplexity.HasCircuitSize n f s) := by
  intro n s f hnc
  exact ⟨LMeta590.backward_dir n s f hnc, LMeta590.forward_dir n s f⟩
