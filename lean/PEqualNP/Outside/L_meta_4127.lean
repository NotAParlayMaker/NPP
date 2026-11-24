import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4127_aux

open PEqualNP.CircuitLowerBounds

theorem fold_prefix {α β : Type} (F : List α → β → α) :
    ∀ (gs : List β) (init : List α),
      ∃ t, gs.foldl (fun w g => w ++ [F w g]) init = init ++ t := by
  intro gs
  induction gs with
  | nil => intro init; exact ⟨[], by simp⟩
  | cons g gs ih =>
    intro init
    obtain ⟨t, ht⟩ := ih (init ++ [F init g])
    exact ⟨[F init g] ++ t, by rw [List.foldl_cons, ht, List.append_assoc]⟩

theorem fold_length {α β : Type} (F : List α → β → α) :
    ∀ (gs : List β) (init : List α),
      (gs.foldl (fun w g => w ++ [F w g]) init).length = init.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro init; simp
  | cons g gs ih =>
    intro init
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def lpGate (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or  => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

theorem lp_eq (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    PEqualNP.ReadK.linearParts C isLine x =
      C.gates.foldl (fun w g => w ++ [lpGate w g])
        ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

theorem and_fst (l : List (Bool × Bool)) : ∀ acc : Bool × Bool,
    (l.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) acc).1 =
      (acc.1 && l.all (·.1)) := by
  induction l with
  | nil => intro acc; simp
  | cons p l ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp [Bool.and_assoc]

theorem getD_fst (lp : List (Bool × Bool)) (i : ℕ) :
    (lp.map Prod.fst).getD i false = (lp.getD i (false, false)).1 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases lp[i]? <;> rfl

theorem fst_rel : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (lp : List (Bool × Bool)),
      (gs.foldl (fun w g => w ++ [lpGate w g]) lp).map Prod.fst =
        gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (lp.map Prod.fst) := by
  intro gs
  induction gs with
  | nil => intro _ lp; rfl
  | cons g gs ih =>
    intro hg lp
    rw [List.foldl_cons, List.foldl_cons, ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))]
    rw [List.map_append]
    congr 2
    simp only [getD_fst]
    rcases hg g List.mem_cons_self with h | h
    · simp [lpGate, h, GateOp.eval, and_fst, List.all_map, Function.comp_def]
    · simp [lpGate, h, GateOp.eval, List.any_map, Function.comp_def]

theorem getD_app_left {α : Type} (l l' : List α) (d : α) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_at {α : Type} (l l' : List α) (v d : α) :
    (l ++ v :: l').getD l.length d = v := by
  simp [List.getD_eq_getElem?_getD]

theorem fold_split {α β : Type} (F : List α → β → α) (gs : List β) (init : List α) (k : ℕ)
    (g : β) (h : gs[k]? = some g) :
    ∃ t, gs.foldl (fun w g => w ++ [F w g]) init =
      (gs.take k).foldl (fun w g => w ++ [F w g]) init ++
        F ((gs.take k).foldl (fun w g => w ++ [F w g]) init) g :: t := by
  obtain ⟨hlt, hgx⟩ := List.getElem?_eq_some_iff.mp h
  have hs : gs = gs.take k ++ g :: gs.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k gs]
    rw [List.drop_eq_getElem_cons hlt, hgx]
  obtain ⟨t, ht⟩ := fold_prefix F (gs.drop (k + 1))
    ((gs.take k).foldl (fun w g => w ++ [F w g]) init ++
      [F ((gs.take k).foldl (fun w g => w ++ [F w g]) init) g])
  refine ⟨t, ?_⟩
  conv_lhs => rw [hs]
  rw [List.foldl_append, List.foldl_cons, ht, List.append_assoc]
  rfl

def X14 : List Bool := List.ofFn fun (x4 : Fin 14) => decide (↑x4 = (0 : ℕ) ∨ ↑x4 = (7 : ℕ))

def isL (b : Bool) : ℕ → Bool := fun x4 => decide (x4 = if b = true then (7 : ℕ) else (0 : ℕ))

def LP0 (b : Bool) : List (Bool × Bool) :=
  (X14.zipIdx).map fun (c, i) => if isL b i then (false, c) else (c, false)

theorem init_len (b : Bool) : (LP0 b).length = 14 := by
  cases b <;> decide

theorem init_fst (b : Bool) : (LP0 b).map Prod.fst =
    List.ofFn fun (x12 : Fin 14) => decide (x12 = if b = true then Fin.castAdd 7 (0 : Fin 7)
      else Fin.natAdd 7 (0 : Fin 7)) := by
  cases b <;> decide

theorem init_snd (b : Bool) : ∀ x6 : Fin 7,
    ((LP0 b).getD x6 (false, false)).2 = (if b = true then false else decide (x6 = 0)) ∧
    ((LP0 b).getD (7 + x6) (false, false)).2 = (if b = true then decide (x6 = 0) else false) := by
  cases b <;> decide

end PEqualNP.Outside.L_meta_4127_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4127_aux in
theorem PEqualNP.Outside.L_meta_4127 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) →     ∀ (x3 : Bool),       ((PEqualNP.ReadK.linearParts x1 (fun (x4 : ℕ) => Decidable.decide (x4 = if x3 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.ofFn fun (x4 : Fin (14 : ℕ)) => Decidable.decide (↑x4 = (0 : ℕ) ∨ ↑x4 = (7 : ℕ)))).getD x1.output (Bool.false, Bool.false)).2 = Bool.false →         ∃ (x5 : ℕ → Bool),           (∀ (x6 : Fin (7 : ℕ)), (x5 ↑x6 = if x3 = Bool.true then Bool.false else Decidable.decide (x6 = (0 : Fin (7 : ℕ)))) ∧ x5 ((7 : ℕ) + ↑x6) = if x3 = Bool.true then Decidable.decide (x6 = (0 : Fin (7 : ℕ))) else Bool.false) ∧             (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                 x1.gates[x6]? = Option.some x7 →                   x7.inputs = [x8, x9] →                     have x12 : List Bool := x1.wires (List.ofFn fun (x12 : Fin (14 : ℕ)) => Decidable.decide (x12 = if x3 = Bool.true then Fin.castAdd (7 : ℕ) (0 : Fin (7 : ℕ)) else Fin.natAdd (7 : ℕ) (0 : Fin (7 : ℕ))));                     (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((14 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((14 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧               x5 x1.output = Bool.false := by
  intro C hC b hout
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
    exact (hC i g (List.getElem?_eq_some_iff.mpr ⟨hi, hgi⟩)).1
  set LP := C.gates.foldl (fun w g => w ++ [lpGate w g]) (LP0 b) with hLPd
  have hfst : LP.map Prod.fst = C.wires (List.ofFn fun (x12 : Fin 14) =>
      decide (x12 = if b = true then Fin.castAdd 7 (0 : Fin 7) else Fin.natAdd 7 (0 : Fin 7))) := by
    rw [hLPd, fst_rel C.gates hops (LP0 b), init_fst b]
    rfl
  obtain ⟨t0, ht0⟩ := fold_prefix lpGate C.gates (LP0 b)
  refine ⟨fun w => (LP.getD w (false, false)).2, ?_, ?_, ?_⟩
  · intro x6
    beta_reduce
    rw [hLPd, ht0, getD_app_left _ _ _ _ (by rw [init_len]; omega),
      getD_app_left _ _ _ _ (by rw [init_len]; omega)]
    exact init_snd b x6
  · intro x6 x7 x8 x9 hg hin
    obtain ⟨hop, a, c, hac, hne, ha, hc⟩ := hC x6 x7 hg
    rw [hin] at hac
    simp only [List.cons.injEq, and_true] at hac
    obtain ⟨rfl, rfl⟩ := hac
    intro x12
    have hx12 : x12 = LP.map Prod.fst := hfst.symm
    obtain ⟨t, ht⟩ := fold_split lpGate C.gates (LP0 b) x6 x7 hg
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hg
    have hlen : ((C.gates.take x6).foldl (fun w g => w ++ [lpGate w g]) (LP0 b)).length
        = 14 + x6 := by
      rw [fold_length, init_len, List.length_take]
      omega
    have e14 : LP.getD (14 + x6) (false, false) =
        lpGate ((C.gates.take x6).foldl (fun w g => w ++ [lpGate w g]) (LP0 b)) x7 := by
      rw [hLPd, ht, ← hlen, getD_app_at]
    have eA : ∀ i, i < 14 + x6 → LP.getD i (false, false) =
        ((C.gates.take x6).foldl (fun w g => w ++ [lpGate w g]) (LP0 b)).getD i (false, false) := by
      intro i hi
      rw [hLPd, ht, getD_app_left _ _ _ _ (by rw [hlen]; exact hi)]
    beta_reduce
    rw [hx12, getD_fst, getD_fst, e14, eA x8 ha, eA x9 hc]
    refine ⟨fun hand => ?_, fun hor => ?_⟩
    · simp [lpGate, hand, hin]
    · simp [lpGate, hor, hin]
  · exact hout

