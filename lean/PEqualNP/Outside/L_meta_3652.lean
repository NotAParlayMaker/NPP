import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3652

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK PEqualNP.Core PEqualNP.ReadTwo

def fd {α : Type} (st : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) w

theorem fd_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    fd st (gs ++ [g]) w = fd st gs w ++ [st (fd st gs w) g] := by
  simp [fd, List.foldl_append]

theorem fd_len {α : Type} (st : List α → Gate → α) (gs : List Gate) :
    ∀ w : List α, (fd st gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [fd]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [st w g])
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem fd_keep {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) :
    ∀ (w : List α) (i : ℕ), i < w.length → (fd st gs w).getD i d = w.getD i d := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [st w g]) i (by simp; omega)
    simp only [fd, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem fd_take {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k i : ℕ) (hi : i < X.length + k) (hk : k ≤ gs.length) :
    (fd st gs X).getD i d = (fd st (gs.take k) X).getD i d := by
  have h1 : fd st gs X = fd st (gs.drop k) (fd st (gs.take k) X) := by
    unfold fd
    rw [← List.foldl_append, List.take_append_drop]
  rw [h1]
  exact fd_keep st d _ _ i (by rw [fd_len, List.length_take, Nat.min_eq_left hk]; exact hi)

theorem fd_gate {α : Type} (st : List α → Gate → α) (d : α) (gs : List Gate) (X : List α)
    (k : ℕ) (hk : k < gs.length) :
    (fd st gs X).getD (X.length + k) d = st (fd st (gs.take k) X) gs[k] := by
  rw [fd_take st d gs X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, fd_snoc]
  have hl : (fd st (gs.take k) X).length = X.length + k := by
    rw [fd_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

def wireSt (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wires_eq_fd (C : Circuit) (x : List Bool) : C.wires x = fd wireSt C.gates x := rfl

theorem wire_lt_gate {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (x : Fin n → Bool) :
    gateVal n C k x = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => wval C x i) := by
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  rw [gateVal, wires_eq_fd, show n + k = (List.ofFn x).length + k from by rw [hlen],
    fd_gate wireSt false C.gates (List.ofFn x) k hk]
  have hgk : gateAt C k = C.gates[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hk]
  rw [hgk]
  simp only [wireSt, wval, wires_eq_fd]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hirb : i < n + k := hAO.2.1 k hk i (by simpa [hgk] using hi)
  rw [fd_take wireSt false C.gates (List.ofFn x) k i (by rw [hlen]; exact hirb) (le_of_lt hk)]

theorem allTrue_wval {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) :
    ∀ k ≤ C.gates.length, ∀ w < n + k, wval (n := n) C (fun _ => true) w = true := by
  intro k hk
  induction k with
  | zero =>
    intro w hw
    simp only [Nat.add_zero] at hw
    rw [wval, wires_eq_fd, fd_keep wireSt false C.gates _ w (by simp [hw])]
    simp [List.getD_eq_getElem?_getD, hw]
  | succ k ih =>
    intro w hw
    by_cases hwk : w < n + k
    · exact ih (Nat.le_of_lt hk) w hwk
    · have hweq : w = n + k := by omega
      subst w
      have hkl : k < C.gates.length := by omega
      have hgv : wval (n := n) C (fun _ => true) (n + k) = gateVal n C k (fun _ => true) := rfl
      rw [hgv, wire_lt_gate C hAO k hkl]
      have hgk : C.gates[k] ∈ C.gates := List.getElem_mem hkl
      have hgk' : gateAt C k = C.gates[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hkl]
      have hlen2 : (gateAt C k).inputs.length = 2 := by rw [hgk']; exact hAO.2.2 _ hgk
      rcases (hAO.1 _ hgk) with hop | hop
      · rw [← hgk'] at hop
        rw [hop]
        simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
        intro i hi
        exact ih (Nat.le_of_lt hk) i (hAO.2.1 k hkl i hi)
      · rw [← hgk'] at hop
        rw [hop]
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
        obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt C k).inputs = [a, b] := by
          match heq : (gateAt C k).inputs with
          | [a, b] => exact ⟨a, b, rfl⟩
          | [] => simp [heq] at hlen2
          | [_] => simp [heq] at hlen2
          | _ :: _ :: _ :: _ => simp [heq] at hlen2
        have ha : a ∈ (gateAt C k).inputs := by rw [hab]; simp
        exact ⟨a, ha, ih (Nat.le_of_lt hk) a (hAO.2.1 k hkl a ha)⟩

def BelowW {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true

theorem belowW_not_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (w : ℕ) (hw : BelowW G C w) (hlt : w < n) : False := by
  let x : Fin n → Bool := pairInput ⟨w, hlt⟩ ⟨w, hlt⟩
  have h1 : wval C x w = true := by
    rw [wval, wires_eq_fd, fd_keep wireSt false C.gates _ w (by simp [hlt])]
    simp [List.getD_eq_getElem?_getD, hlt, x, pairInput]
  have h2 := hw x h1
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_true_eq] at h2
  obtain ⟨u, v, huv, hu, hv⟩ := h2
  simp only [x, pairInput, decide_eq_true_eq, or_self] at hu hv
  subst u; subst v
  exact G.ne_of_adj huv rfl

theorem isImpWire_of_belowW {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (w : ℕ) (hw : w < n + C.gates.length) (hb : BelowW G C w) :
    IsImpWire G C w :=
  ⟨hb, fun _ => true, allTrue_wval C hAO C.gates.length le_rfl w hw⟩

theorem isImpOperand_of_belowW {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (w : ℕ) (hw : w < n + C.gates.length) (hb : BelowW G C w) :
    IsImpOperand G C w := by
  have hge : n ≤ w := by
    by_contra! hlt
    exact belowW_not_input G C w hb hlt
  refine ⟨hge, ?_, ?_⟩
  · intro x hx
    apply hb x
    simpa [wval, gateVal, Nat.add_sub_of_le hge] using hx
  · refine ⟨fun _ => true, ?_⟩
    simpa [gateVal, wval, Nat.add_sub_of_le hge] using
      allTrue_wval C hAO C.gates.length le_rfl w hw

theorem belowW_inputs_of_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hb : BelowF G C k) :
    ∀ t ∈ (gateAt C k).inputs, BelowW G C t := by
  intro t ht x hxt
  apply hb x
  rw [wire_lt_gate C hAO k hk, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  exact ⟨t, ht, hxt⟩

theorem belowW_of_belowF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (k : ℕ) (hb : BelowF G C k) : BelowW G C (n + k) :=
  fun x hx => hb x hx

def coneSt (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => (w - n) :: cs.getD (w - n) [])

theorem cones_eq_fd (n : ℕ) (C : Circuit) : cones n C = fd (coneSt n) C.gates [] := rfl

theorem inCone_elim {n : ℕ} (C : Circuit) (a b : ℕ) (h : InCone n C a b) :
    b < C.gates.length ∧ ∃ w ∈ (gateAt C b).inputs,
      n ≤ w ∧ w < n + b ∧ (w - n = a ∨ InCone n C a (w - n)) := by
  by_cases hb : b < C.gates.length
  · refine ⟨hb, ?_⟩
    have hmem : a ∈ (fd (coneSt n) C.gates []).getD b [] := h
    have hb0 : b = ([] : List (List ℕ)).length + b := (Nat.zero_add b).symm
    rw [hb0, fd_gate (coneSt n) [] C.gates [] b hb] at hmem
    have hlen_take : (fd (coneSt n) (C.gates.take b) []).length = b := by
      rw [fd_len, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (le_of_lt hb)]
    have hgk : gateAt C b = C.gates[b] := by simp [gateAt, List.getD_eq_getElem?_getD, hb]
    simp only [coneSt, hlen_take, ← hgk, List.mem_flatMap, List.mem_filter,
      decide_eq_true_eq, List.mem_cons] at hmem
    obtain ⟨w, ⟨hw_in, hw_ge, hw_lt⟩, hcases⟩ := hmem
    refine ⟨w, hw_in, hw_ge, hw_lt, ?_⟩
    rcases hcases with rfl | hrest
    · exact Or.inl rfl
    · right
      unfold InCone
      rw [cones_eq_fd]
      have hwb : w - n < b := by omega
      have htk := fd_take (coneSt n) [] C.gates [] b (w - n) (by simp [hwb]) (le_of_lt hb)
      rw [htk]
      exact hrest
  · have hlen_c : (cones n C).length = C.gates.length := by
      rw [cones_eq_fd, fd_len, List.length_nil, Nat.zero_add]
    have hnone : (cones n C).getD b [] = [] := by
      rw [List.getD_eq_default _ _ (by omega)]
    unfold InCone at h
    rw [hnone] at h
    simp at h

theorem gate_inputs_pair {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) :
    (gateAt C k).inputs = [opnd C k 0, opnd C k 1] := by
  have hgk : gateAt C k = C.gates[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hk]
  have hlen : (gateAt C k).inputs.length = 2 := by rw [hgk]; exact hAO.2.2 _ (List.getElem_mem hk)
  match heq : (gateAt C k).inputs with
  | [a, b] => simp [opnd, heq]
  | [] => simp [heq] at hlen
  | [_] => simp [heq] at hlen
  | _ :: _ :: _ :: _ => simp [heq] at hlen

theorem opnd_lt {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (b : Fin 2) : opnd C k b < n + k := by
  have hp := gate_inputs_pair C hAO k hk
  have hin : opnd C k b ∈ (gateAt C k).inputs := by
    rw [hp]
    fin_cases b <;> simp
  exact hAO.2.1 k hk _ hin

theorem no_core_above_belowF {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hLFP : IsLiftFixedPoint G C)
    (hCone : ∀ k < C.gates.length, InOutputCone n C k)
    (hNoAndBelow : ∀ k2 < C.gates.length, (gateAt C k2).op = GateOp.and →
      ∀ t ∈ (gateAt C k2).inputs, ¬ (∀ x : Fin n → Bool,
        Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → graphFun G ∅ x = true)) :
    ∀ b < C.gates.length, (∃ a, BelowF G C a ∧ InCone n C a b) →
      BelowF G C b ∧ (gateAt C b).op = GateOp.or ∧ ¬ IsCore G C b := by
  intro b
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    intro hb ⟨a, ha, hab⟩
    obtain ⟨_, w, hwin, hwge, hwlt, hwa⟩ := inCone_elim C a b hab
    have hw_below : BelowW G C w := by
      rcases hwa with rfl | hwc
      · simpa [Nat.add_sub_of_le hwge] using belowW_of_belowF G C (w - n) ha
      · have ihw := ih (w - n) (by omega) (by omega) ⟨a, ha, hwc⟩
        simpa [Nat.add_sub_of_le hwge] using belowW_of_belowF G C (w - n) ihw.1
    have hnot_and : (gateAt C b).op ≠ GateOp.and := by
      intro hand
      exact hNoAndBelow b hb hand w hwin (fun x hx => hw_below x hx)
    have hor : (gateAt C b).op = GateOp.or := by
      have hgk : gateAt C b = C.gates[b] := by simp [gateAt, List.getD_eq_getElem?_getD, hb]
      rcases hAO.1 _ (List.getElem_mem hb) with h | h
      · exact absurd (by simpa [hgk] using h) hnot_and
      · simpa [hgk] using h
    have hpair := gate_inputs_pair C hAO b hb
    have hpos : ∃ p : Fin 2, opnd C b p = w := by
      rw [hpair] at hwin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hwin
      rcases hwin with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    obtain ⟨pos, rfl⟩ := hpos
    have hbelow_b : BelowF G C b := by
      by_contra hnb
      apply hLFP
      refine ⟨b, hb, pos, hCone b hb, hor, hnb, ?_⟩
      exact isImpWire_of_belowW G C hAO _ (by omega) hw_below
    refine ⟨hbelow_b, hor, ?_⟩
    intro hcore
    apply hcore.2.2.1
    have hbi := belowW_inputs_of_or G C hAO b hb hor hbelow_b
    constructor
    · apply isImpOperand_of_belowW G C hAO _ (by have := opnd_lt C hAO b hb 0; omega)
      exact hbi _ (by rw [hpair]; simp)
    · apply isImpOperand_of_belowW G C hAO _ (by have := opnd_lt C hAO b hb 1; omega)
      exact hbi _ (by rw [hpair]; simp)

theorem mem_foldl_insertNew (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (hv : v ∈ L.foldl insertNew acc) : v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => exact Or.inl hv
  | cons x xs ih =>
    simp only [List.foldl_cons] at hv
    rcases ih _ hv with h | h
    · unfold insertNew at h
      split_ifs at h
      · exact Or.inl h
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | rfl
        · exact Or.inl h
        · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_foldl_orStep (A B : List (List ℕ)) (v : List ℕ)
    (hv : v ∈ ([A, B] : List (List (List ℕ))).foldl (fun acc C => C.foldl insertNew acc) []) :
    v ∈ A ∨ v ∈ B := by
  simp only [List.foldl_cons, List.foldl_nil] at hv
  rcases mem_foldl_insertNew B (A.foldl insertNew []) v hv with h | h
  · rcases mem_foldl_insertNew A [] v h with h0 | h0
    · simp at h0
    · exact Or.inl h0
  · exact Or.inr h

theorem capAdd_zero_left (a : List ℕ) (hla : a.length = 2) (hba : ∀ x ∈ a, x ≤ 2) :
    capAdd 1 [0, 0] a = a := by
  match a with
  | [x, y] =>
    have hx : x ≤ 2 := hba x (by simp)
    have hy : y ≤ 2 := hba y (by simp)
    simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil_left, Nat.zero_add,
      List.cons.injEq, and_true]
    omega
  | [] => simp at hla
  | [_] => simp at hla
  | _ :: _ :: _ :: _ => simp at hla

theorem mem_foldl_andStep_two (S : List ℕ) (hS : S.length = 2) (A B : List (List ℕ))
    (hA : ∀ a ∈ A, a.length = 2 ∧ ∀ x ∈ a, x ≤ 2) (v : List ℕ)
    (hv : v ∈ ([A, B] : List (List (List ℕ))).foldl (andStep 1) [S.map fun _ => 0]) :
    ∃ a ∈ A, ∃ b ∈ B, v = capAdd 1 a b := by
  have hS0 : (S.map fun _ : ℕ => (0 : ℕ)) = [0, 0] := by
    match S with
    | [_, _] => rfl
    | [] => simp at hS
    | [_] => simp at hS
    | _ :: _ :: _ :: _ => simp at hS
  rw [hS0] at hv
  simp only [List.foldl_cons, List.foldl_nil] at hv
  unfold andStep at hv
  rcases mem_foldl_insertNew _ [] v hv with h | h
  · simp at h
  · simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨u, hu, b, hb, rfl⟩ := h
    rcases mem_foldl_insertNew _ [] u hu with hu0 | hu0
    · simp at hu0
    · simp only [List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hu0
      obtain ⟨z, rfl, a, ha, rfl⟩ := hu0
      have ⟨hla, hba⟩ := hA a ha
      rw [capAdd_zero_left a hla hba]
      exact ⟨a, ha, b, hb, rfl⟩

def lpSt (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

theorem linearParts_eq_fd (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x = fd lpSt C.gates
      ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

def rvSt (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  let ins := g.inputs.map fun i => R.getD i []
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

theorem readVectors_eq_fd (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = fd (rvSt S k) C.gates ((List.range n).map (leafVectors S k)) := rfl

def VecOk (rv : List (List (List ℕ))) (lp : List (Bool × Bool)) (w wp : List Bool) : Prop :=
  rv.length = lp.length ∧ lp.length = w.length ∧ w.length = wp.length ∧
  (∀ i : ℕ, (lp.getD i (false, false)).1 = wp.getD i false) ∧
  (∀ i : ℕ, ∀ vec ∈ rv.getD i [], vec.length = 2 ∧ (∀ c ∈ vec, c ≤ 2) ∧
    1 ≤ vec.getD 0 0 + vec.getD 1 0 ∧ w.getD i false = true ∧
    (vec.getD 1 0 = 0 → (lp.getD i (false, false)).1 = true) ∧
    (vec.getD 1 0 = 1 → (lp.getD i (false, false)).2 = true))

theorem getD_append_self_gen {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_append_left_gen {α : Type} (l r : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem vecOk_step {S : List ℕ} (hS : S.length = 2)
    (rv : List (List (List ℕ))) (lp : List (Bool × Bool)) (w wp : List Bool)
    (hok : VecOk rv lp w wp) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen2 : g.inputs.length = 2) :
    VecOk (rv ++ [rvSt S 1 rv g]) (lp ++ [lpSt lp g]) (w ++ [wireSt w g]) (wp ++ [wireSt wp g]) := by
  rcases hok with ⟨h12, h23, h34, hwp, hrv⟩
  obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
    match heq : g.inputs with
    | [a, b] => exact ⟨a, b, rfl⟩
    | [] => simp [heq] at hlen2
    | [_] => simp [heq] at hlen2
    | _ :: _ :: _ :: _ => simp [heq] at hlen2
  refine ⟨by simp [h12], by simp [h23], by simp [h34], ?_, ?_⟩
  · intro i
    by_cases hi : i < lp.length
    · rw [getD_append_left_gen _ _ i _ hi, getD_append_left_gen _ _ i _ (by omega)]
      exact hwp i
    · by_cases heq : i = lp.length
      · subst heq
        have hlp : lp.length = wp.length := h23.trans h34
        rw [getD_append_self_gen, hlp, getD_append_self_gen]
        have ha := hwp a; have hb := hwp b
        simp only [List.getD_eq_getElem?_getD] at ha hb
        rcases hop with h | h
        · simp [lpSt, wireSt, GateOp.eval, h, hab, ha, hb]
        · rw [Set.mem_singleton_iff] at h
          simp [lpSt, wireSt, GateOp.eval, h, hab, ha, hb]
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  · intro i vec hvec
    by_cases hi : i < rv.length
    · rw [getD_append_left_gen _ _ i _ hi] at hvec
      rw [getD_append_left_gen _ _ i _ (by omega), getD_append_left_gen _ _ i _ (by omega)]
      exact hrv i vec hvec
    · by_cases heq : i = rv.length
      · subst heq
        rw [getD_append_self_gen] at hvec
        have hrl : rv.length = lp.length := h12
        have hrw : rv.length = w.length := h12.trans h23
        rw [hrl, getD_append_self_gen, ← hrl, hrw, getD_append_self_gen]
        rcases hop with h | h
        · simp only [rvSt, h, hab, List.map_cons, List.map_nil] at hvec
          obtain ⟨va, hva, vb, hvb, rfl⟩ := mem_foldl_andStep_two S hS _ _
            (fun x hx => ⟨(hrv a x hx).1, (hrv a x hx).2.1⟩) vec hvec
          have ⟨ha_len, ha_bd, ha_pos, ha_w, ha_0, ha_1⟩ := hrv a va hva
          have ⟨hb_len, hb_bd, hb_pos, hb_w, hb_0, hb_1⟩ := hrv b vb hvb
          match va, vb, ha_len, hb_len with
          | [a0, a1], [b0, b1], _, _ =>
            have ha0 : a0 ≤ 2 := ha_bd a0 (by simp)
            have ha1 : a1 ≤ 2 := ha_bd a1 (by simp)
            have hb0 : b0 ≤ 2 := hb_bd b0 (by simp)
            have hb1 : b1 ≤ 2 := hb_bd b1 (by simp)
            simp only [List.getD_cons_zero, List.getD_cons_succ] at ha_pos hb_pos ha_0 ha_1 hb_0 hb_1
            simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil_left, List.length_cons,
              List.length_nil, List.mem_cons, List.not_mem_nil, or_false,
              List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
              Option.getD_some, wireSt, h, hab, lpSt, GateOp.eval,
              List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.foldl_cons,
              List.foldl_nil, id, Bool.true_and, Bool.and_true, Bool.false_and, Bool.or_false]
            simp only [List.getD_eq_getElem?_getD] at ha_w hb_w ha_0 ha_1 hb_0 hb_1
            refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
            · rintro c (rfl | rfl) <;> omega
            · omega
            · simp [ha_w, hb_w]
            · intro hz
              have ha1z : a1 = 0 := by omega
              have hb1z : b1 = 0 := by omega
              simp [ha_0 ha1z, hb_0 hb1z]
            · intro ho
              rcases (by omega : (a1 = 0 ∧ b1 = 1) ∨ (a1 = 1 ∧ b1 = 0)) with ⟨ha1z, hb1o⟩ | ⟨ha1o, hb1z⟩
              · simp [ha_0 ha1z, hb_1 hb1o]
              · simp [ha_1 ha1o, hb_0 hb1z]
        · rw [Set.mem_singleton_iff] at h
          simp only [rvSt, h, hab, List.map_cons, List.map_nil] at hvec
          rcases mem_foldl_orStep _ _ vec hvec with hva | hvb
          · have ⟨hlen, hbd, hpos, hw, h0, h1⟩ := hrv a vec hva
            simp only [List.getD_eq_getElem?_getD] at hw h0 h1
            simp only [wireSt, h, hab, lpSt, GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id, Bool.or_false, List.getD_eq_getElem?_getD]
            refine ⟨hlen, hbd, hpos, by simp [hw], ?_, ?_⟩
            · intro hz; simp [h0 hz]
            · intro ho; simp [h1 ho]
          · have ⟨hlen, hbd, hpos, hw, h0, h1⟩ := hrv b vec hvb
            simp only [List.getD_eq_getElem?_getD] at hw h0 h1
            simp only [wireSt, h, hab, lpSt, GateOp.eval, List.map_cons, List.map_nil,
              List.any_cons, List.any_nil, id, Bool.or_false, List.getD_eq_getElem?_getD]
            refine ⟨hlen, hbd, hpos, by simp [hw], ?_, ?_⟩
            · intro hz; simp [h0 hz]
            · intro ho; simp [h1 ho]
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hvec
        simp at hvec

theorem vecOk_foldl {S : List ℕ} (hS : S.length = 2) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length = 2)
    (rv : List (List (List ℕ))) (lp : List (Bool × Bool)) (w wp : List Bool)
    (hok : VecOk rv lp w wp) :
    VecOk (fd (rvSt S 1) gs rv) (fd lpSt gs lp)
      (fd wireSt gs w) (fd wireSt gs wp) := by
  induction gs generalizing rv lp w wp with
  | nil => exact hok
  | cons g gs ih =>
    have hg := hgs g List.mem_cons_self
    exact ih (fun x hx => hgs x (List.mem_cons_of_mem _ hx)) _ _ _ _
      (vecOk_step hS rv lp w wp hok g hg.1 hg.2)

theorem lp0_getD (x : List Bool) (isLine : ℕ → Bool) (i : ℕ) :
    (((x.zipIdx).map fun (b, j) => if isLine j then (false, b) else (b, false)).getD i (false, false)) =
      if isLine i then (false, x.getD i false) else (x.getD i false, false) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_zipIdx]
  cases hx : x[i]? with
  | none => simp [List.getD_eq_getElem?_getD, hx]
  | some b => simp [List.getD_eq_getElem?_getD, hx]

theorem lp_or_gate {N : ℕ} (C : Circuit) (hAO : IsAO2 (N + N) C) (isLine : ℕ → Bool) (x : List Bool)
    (hx : x.length = N + N) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) :
    ((linearParts C isLine x).getD (N + N + k) (false, false)).2 =
      (((linearParts C isLine x).getD (opnd C k 0) (false, false)).2 ||
       ((linearParts C isLine x).getD (opnd C k 1) (false, false)).2) := by
  have hlen0 : ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)).length = N + N := by
    simp [hx]
  rw [linearParts_eq_fd, ← hlen0, fd_gate lpSt (false, false) C.gates _ k hk]
  have hgk : gateAt C k = C.gates[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hk]
  have hp := gate_inputs_pair C hAO k hk
  have ha_lt := opnd_lt C hAO k hk 0
  have hb_lt := opnd_lt C hAO k hk 1
  rw [← hgk]
  simp only [lpSt, hop, hp, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false]
  rw [← fd_take lpSt (false, false) C.gates _ k (opnd C k 0)
    (by rw [hlen0]; exact ha_lt) (le_of_lt hk)]
  rw [← fd_take lpSt (false, false) C.gates _ k (opnd C k 1)
    (by rw [hlen0]; exact hb_lt) (le_of_lt hk)]

theorem desc_or_to_and (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 (N + N) C) (u v : Fin (N + N)) (isLine : ℕ → Bool)
    (xList : List Bool) (hxlen : xList.length = N + N)
    (k : ℕ) (hk : k < C.gates.length) (hb : BelowF G C k)
    (hv : gateVal (N + N) C k (pairInput u v) = true)
    (hlp : ((linearParts C isLine xList).getD (N + N + k) (false, false)).2 = false) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ BelowF G C j ∧
      gateVal (N + N) C j (pairInput u v) = true ∧
      ((linearParts C isLine xList).getD (N + N + j) (false, false)).2 = false := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hgk : gateAt C k = C.gates[k] := by simp [gateAt, List.getD_eq_getElem?_getD, hk]
    rcases hAO.1 _ (List.getElem_mem hk) with hop | hop
    · exact ⟨k, hk, by simpa [hgk] using hop, hb, hv, hlp⟩
    · rw [← hgk] at hop
      have hpair := gate_inputs_pair C hAO k hk
      rw [wire_lt_gate C hAO k hk, hop, hpair] at hv
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false, Bool.or_eq_true] at hv
      have hlp_eq := lp_or_gate C hAO isLine xList hxlen k hk hop
      rw [hlp_eq, Bool.or_eq_false_iff] at hlp
      have hbin := belowW_inputs_of_or G C hAO k hk hop hb
      rcases hv with hva | hvb
      · have hw : BelowW G C (opnd C k 0) := hbin _ (by rw [hpair]; simp)
        have hge : N + N ≤ opnd C k 0 := by
          by_contra! hlt
          exact belowW_not_input G C _ hw hlt
        have hlt_k := opnd_lt C hAO k hk 0
        have hk' : opnd C k 0 - (N + N) < k := by omega
        obtain ⟨j, hj1, hj2, hj3, hj4, hj5⟩ := ih (opnd C k 0 - (N + N)) hk' (by omega)
          (fun x hx => hw x (by simpa [wval, gateVal, Nat.add_sub_of_le hge] using hx))
          (by simpa [gateVal, wval, Nat.add_sub_of_le hge] using hva)
          (by simpa [Nat.add_sub_of_le hge] using hlp.1)
        exact ⟨j, hj1, hj2, hj3, hj4, hj5⟩
      · have hw : BelowW G C (opnd C k 1) := hbin _ (by rw [hpair]; simp)
        have hge : N + N ≤ opnd C k 1 := by
          by_contra! hlt
          exact belowW_not_input G C _ hw hlt
        have hlt_k := opnd_lt C hAO k hk 1
        have hk' : opnd C k 1 - (N + N) < k := by omega
        obtain ⟨j, hj1, hj2, hj3, hj4, hj5⟩ := ih (opnd C k 1 - (N + N)) hk' (by omega)
          (fun x hx => hw x (by simpa [wval, gateVal, Nat.add_sub_of_le hge] using hx))
          (by simpa [gateVal, wval, Nat.add_sub_of_le hge] using hvb)
          (by simpa [Nat.add_sub_of_le hge] using hlp.2)
        exact ⟨j, hj1, hj2, hj3, hj4, hj5⟩

lemma main_proof (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj] (C : Circuit)
    (hG : ∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧
      ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p)))
    (hC4 : NoFourCycle G) (hAO : IsAO2 (N + N) C)
    (hFun : circuitFun (N + N) C = graphFun G ∅)
    (hLFP : IsLiftFixedPoint G C)
    (hCone : ∀ k < C.gates.length, InOutputCone (N + N) C k)
    (hNoAndBelow : ∀ k2 < C.gates.length, (gateAt C k2).op = GateOp.and →
      ∀ t ∈ (gateAt C k2).inputs, ¬ (∀ x : Fin (N + N) → Bool,
        Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → graphFun G ∅ x = true))
    (p1 l1 : Fin N)
    (hDR : (p1.val, N + l1.val) ∈ doubleReread C (N + N) (fun w => decide (N ≤ w))
      ((List.finRange N).flatMap fun p5 => ((List.finRange N).filter
        fun l5 => decide (I p5 l5)).map fun l6 => (p5.val, N + l6.val))) :
    ∃ j ∈ maximalCores G C, s(Fin.castAdd N p1, Fin.natAdd N l1) ∈ gammaE G C j := by
  let _ := hC4
  unfold doubleReread at hDR
  rw [List.mem_filter] at hDR
  obtain ⟨hmem_E, hsingle_pair⟩ := hDR
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, Prod.mk.injEq] at hmem_E
  obtain ⟨p5, l5, hI5, hp5, hl5⟩ := hmem_E
  have hI1 : I p1 l1 := by
    have hp_eq : p1 = p5 := Fin.ext hp5.symm
    have hl_eq : l1 = l5 := Fin.ext (by omega)
    rw [hp_eq, hl_eq]
    exact hI5
  have hsingle0 : lineSingle C (N + N) (fun w => decide (N ≤ w)) p1.val (N + l1.val) = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hsingle_pair
    exact hsingle_pair.1
  let u : Fin (N + N) := Fin.castAdd N p1
  let v : Fin (N + N) := Fin.natAdd N l1
  have huv_adj : G.Adj u v := (hG u v).mpr ⟨p1, l1, hI1, Or.inl ⟨rfl, rfl⟩⟩
  have hne_uv : u.val ≠ v.val := by
    have hp := p1.isLt
    change p1.val ≠ N + l1.val
    omega
  have hF_uv : graphFun G ∅ (pairInput u v) = true := by
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq]
    exact ⟨u, v, huv_adj, by simp [pairInput], by simp [pairInput]⟩
  have hC_uv : circuitFun (N + N) C (pairInput u v) = true := by rw [hFun]; exact hF_uv
  have hout_ge : N + N ≤ C.output := by
    by_contra! hlt
    let w0 : Fin (N + N) := ⟨C.output, hlt⟩
    have hC_w0 : circuitFun (N + N) C (pairInput w0 w0) = true := by
      change (C.wires (List.ofFn (pairInput w0 w0))).getD C.output false = true
      rw [wires_eq_fd, fd_keep wireSt false C.gates _ C.output (by simp [hlt])]
      simp [List.getD_eq_getElem?_getD, hlt, w0, pairInput]
    have hF_w0 : graphFun G ∅ (pairInput w0 w0) = true := by rw [← hFun]; exact hC_w0
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq] at hF_w0
    obtain ⟨a, b, hab, ha, hb⟩ := hF_w0
    simp only [pairInput, decide_eq_true_eq, or_self] at ha hb
    subst a; subst b
    exact G.ne_of_adj hab rfl
  have hout_lt : C.output < N + N + C.gates.length := by
    by_contra! hle
    have hC_false : circuitFun (N + N) C (pairInput u v) = false := by
      change (C.wires (List.ofFn (pairInput u v))).getD C.output false = false
      rw [wires_eq_fd, List.getD_eq_default _ _ (by rw [fd_len]; simp; exact hle)]
    rw [hC_uv] at hC_false
    cases hC_false
  let j_out := C.output - (N + N)
  have hj_out_lt : j_out < C.gates.length := by omega
  have hj_out_eq : N + N + j_out = C.output := by omega
  have hj_out_below : BelowF G C j_out := by
    intro x hx
    rw [← hFun]
    simpa [circuitFun, Circuit.eval, gateVal, hj_out_eq] using hx
  have hj_out_val : gateVal (N + N) C j_out (pairInput u v) = true := by
    simpa [gateVal, hj_out_eq, circuitFun, Circuit.eval] using hC_uv
  let isLine : ℕ → Bool := fun w => decide (N ≤ w)
  let xList : List Bool := (List.range (N + N)).map fun i => i == u.val || i == v.val
  have hxList_len : xList.length = N + N := by simp [xList]
  have hxList_eq : xList = List.ofFn (pairInput u v) := by
    apply List.ext_getElem (by simp [xList])
    intro i hi1 hi2
    simp only [xList, List.getElem_map, List.getElem_range, List.getElem_ofFn, pairInput]
    apply Bool.eq_iff_iff.mpr
    simp [Fin.ext_iff]
  have hsingle_xList : ((linearParts C isLine xList).getD (N + N + j_out) (false, false)).2 = false := by
    rw [hj_out_eq]
    have hvu : v.val = N + l1.val := Fin.val_natAdd N l1
    have huu : u.val = p1.val := rfl
    simpa [lineSingle, isLine, xList, huu, hvu] using hsingle0
  obtain ⟨j, hj_lt, hj_and, hj_below, hj_val, hj_lp2⟩ :=
    desc_or_to_and N I G C hAO u v isLine xList hxList_len j_out hj_out_lt hj_out_below hj_out_val hsingle_xList
  have hVecOk0 : VecOk ((List.range (N + N)).map (leafVectors [u.val, v.val] 1))
      ((xList.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false))
      (List.ofFn (pairInput u v)) (List.ofFn (pairInput u u)) := by
    refine ⟨by simp [xList], by simp [xList], by simp, ?_, ?_⟩
    · intro i
      rw [lp0_getD]
      by_cases hi : i < N + N
      · rw [hxList_eq]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
          Option.getD_some, pairInput]
        by_cases hil : isLine i = true
        · simp only [hil, ↓reduceIte]
          have hNu : i ≠ u.val := by
            simp only [isLine, decide_eq_true_eq] at hil
            have := p1.isLt
            change i ≠ p1.val
            omega
          simp [hNu, Fin.ext_iff]
        · have hnil : isLine i = false := Bool.eq_false_iff.mpr hil
          simp only [hnil, Bool.false_eq_true, ↓reduceIte]
          have hNv : i ≠ v.val := by
            simp only [isLine, decide_eq_true_eq] at hil
            change i ≠ N + l1.val
            omega
          simp [hNv, Fin.ext_iff]
      · have hxn : xList[i]? = none := List.getElem?_eq_none (by simp [hxList_len]; omega)
        simp [List.getD_eq_getElem?_getD, hxn, hi]
    · intro i vec hvec
      by_cases hi : i < N + N
      · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi] at hvec
        simp only [Option.map_some, Option.getD_some, leafVectors] at hvec
        have hmem_uv : i ∈ [u.val, v.val] ↔ i = u.val ∨ i = v.val := by simp
        split_ifs at hvec with hin
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hvec
          subst vec
          simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil,
            List.mem_cons, List.not_mem_nil, or_false, List.getD_cons_zero, List.getD_cons_succ]
          have h_if_u : (if u.val = i then 1 else 0) + (if v.val = i then 1 else 0) ≥ 1 := by
            rcases hmem_uv.mp hin with rfl | rfl <;> simp
          refine ⟨trivial, ?_, h_if_u, ?_, ?_, ?_⟩
          · rintro c (rfl | rfl) <;> split_ifs <;> omega
          · simp [List.getD_eq_getElem?_getD, hi, pairInput, Fin.ext_iff]
            rcases hmem_uv.mp hin with rfl | rfl <;> simp
          · intro hz
            have hnv : i ≠ v.val := by intro h; subst h; simp at hz
            have hiu : i = u.val := by
              rcases hmem_uv.mp hin with h | h
              · exact h
              · exact absurd h hnv
            subst hiu
            rw [lp0_getD, hxList_eq]
            have hnotline : isLine u.val = false := by
              simp only [isLine, decide_eq_false_iff_not, not_le]
              exact p1.isLt
            simp [hnotline, List.getD_eq_getElem?_getD, hi, pairInput]
          · intro ho
            have hiv : i = v.val := by
              by_contra hnv
              have hnv' : v.val ≠ i := Ne.symm hnv
              simp [hnv'] at ho
            subst hiv
            rw [lp0_getD, hxList_eq]
            have hline : isLine v.val = true := by
              simp only [isLine, decide_eq_true_eq]
              change N ≤ N + l1.val
              omega
            simp [hline, List.getD_eq_getElem?_getD, hi, pairInput]
        · simp at hvec
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hvec
        simp at hvec
  have hVecOkF := vecOk_foldl (S := [u.val, v.val]) rfl C.gates (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩)
    ((List.range (N + N)).map (leafVectors [u.val, v.val] 1))
    ((xList.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false))
    (List.ofFn (pairInput u v)) (List.ofFn (pairInput u u)) hVecOk0
  rw [← readVectors_eq_fd, ← linearParts_eq_fd, ← wires_eq_fd, ← wires_eq_fd] at hVecOkF
  have hj_pt_false : (C.wires (List.ofFn (pairInput u u))).getD (N + N + j) false = false := by
    by_contra hnt
    have ht := Bool.eq_true_of_not_eq_false hnt
    have hf := hj_below (pairInput u u) ht
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq] at hf
    obtain ⟨a, b, hab, ha, hb⟩ := hf
    simp only [pairInput, decide_eq_true_eq, or_self] at ha hb
    subst a; subst b
    exact G.ne_of_adj hab rfl
  have hj_lp1 : ((linearParts C isLine xList).getD (N + N + j) (false, false)).1 = false := by
    rw [hVecOkF.2.2.2.1 (N + N + j), hj_pt_false]
  have hj_read2 : ReadTwiceAt (N + N) C j u v := by
    unfold ReadTwiceAt readsAtMost
    change ((readVectors C (N + N) [u.val, v.val] 1).getD (N + N + j) []).any
      (fun vec => vec.all fun a => decide (a ≤ 1)) = false
    rw [Bool.eq_false_iff]
    intro hany
    rw [List.any_eq_true] at hany
    obtain ⟨vec, hmem, hall⟩ := hany
    have ⟨hlen, hbd, hpos, _, h0, h1⟩ := hVecOkF.2.2.2.2 (N + N + j) vec hmem
    match vec, hlen with
    | [c0, c1], _ =>
      simp only [List.all_cons, List.all_nil, decide_eq_true_eq, Bool.and_true, Bool.and_eq_true] at hall
      rcases hall with ⟨_, hc1⟩
      have hcases : c1 = 0 ∨ c1 = 1 := by omega
      rcases hcases with rfl | rfl
      · have htrue := h0 rfl
        rw [htrue] at hj_lp1
        cases hj_lp1
      · have htrue := h1 rfl
        rw [htrue] at hj_lp2
        cases hj_lp2
  have hj_imp : IsImpGate G C j := ⟨hj_below, pairInput u v, hj_val⟩
  have hj_not_both : ¬ (IsImpOperand G C (opnd C j 0) ∧ IsImpOperand G C (opnd C j 1)) := by
    rintro ⟨hop0, _⟩
    have hin : opnd C j 0 ∈ (gateAt C j).inputs := by
      rw [gate_inputs_pair C hAO j hj_lt]
      simp
    apply hNoAndBelow j hj_lt hj_and (opnd C j 0) hin
    intro x hx
    have hxg : gateVal (N + N) C (opnd C j 0 - (N + N)) x = true := by
      have hw_eq : C.wires (List.ofFn x) = ({ gates := C.gates, output := opnd C j 0 } : Circuit).wires (List.ofFn x) := rfl
      simpa [gateVal, Circuit.eval, Nat.add_sub_of_le hop0.1, hw_eq] using hx
    exact hop0.2.1 x hxg
  have hj_core : IsCore G C j :=
    ⟨hj_lt, hj_imp, hj_not_both, u, v, huv_adj, hj_val, hj_read2⟩
  have hj_max : IsMaximalCore G C j := by
    refine ⟨hj_core, fun i hi hci hinc => ?_⟩
    exact (no_core_above_belowF G C hAO hLFP hCone hNoAndBelow i hi ⟨j, hj_below, hinc⟩).2.2 hci
  refine ⟨j, ?_, ?_⟩
  · unfold maximalCores gatesWhere
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hj_lt, hj_max⟩
  · unfold gammaE
    rw [Finset.mem_filter]
    exact ⟨SimpleGraph.mem_edgeFinset.mpr huv_adj, u, v, rfl, hj_val⟩

end PEqualNP.Outside.L_meta_3652

theorem PEqualNP.Outside.L_meta_3652 :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone (N + N) C k) → (∀ k2 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → ∀ p1 l1 : Fin N, (p1.val, N + l1.val) ∈ (PEqualNP.ReadK.doubleReread C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))) → ∃ j ∈ PEqualNP.Core.maximalCores G C, s(Fin.castAdd N p1, Fin.natAdd N l1) ∈ PEqualNP.TopForm.gammaE G C j := PEqualNP.Outside.L_meta_3652.main_proof
