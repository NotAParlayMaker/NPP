import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1747_aux

open PEqualNP.CircuitLowerBounds

def chk (n : ℕ) : List Gate → Bool
  | [] => true
  | g :: gs => g.inputs.all (fun i => decide (i < n)) && chk (n + 1) gs

theorem chk_spec : ∀ (gs : List Gate) (n : ℕ), chk n gs = true →
    ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j
  | [], _, _, _, hj, _, _ => absurd hj (by simp)
  | g :: gs, n, h, 0, _, i, hi => by
    simp only [chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    simpa using h.1 i (by simpa using hi)
  | g :: gs, n, h, j + 1, hj, i, hi => by
    simp only [chk, Bool.and_eq_true] at h
    have := chk_spec gs (n + 1) h.2 j (by simpa using hj) i (by simpa using hi)
    omega

def Inv (w : List Bool) (m : ℕ) : Prop :=
  (∀ i, w.getD i false = m.testBit i) ∧ (∀ i, w.length ≤ i → m.testBit i = false)

theorem step_inv (w : List Bool) (m : ℕ) (b : Bool) (h : Inv w m) :
    Inv (w ++ [b]) (if b then m ||| 2 ^ w.length else m) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro i
    rcases lt_trichotomy i w.length with hi | rfl | hi
    · rw [List.getD_append _ _ _ _ hi, h1]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow] <;> omega
    · rw [List.getD_append_right _ _ _ _ le_rfl]
      cases b <;> simp [Nat.testBit_or, Nat.testBit_two_pow, h2]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      cases b <;> simp [Nat.testBit_or, h2 i hi.le, Nat.testBit_two_pow] <;> omega
  · intro i hi
    simp at hi
    cases b <;> simp [Nat.testBit_or, h2 i (by omega), Nat.testBit_two_pow] <;> omega

def mk : ℕ → ℕ → List Bool → ℕ
  | _, m, [] => m
  | k, m, b :: bs => mk (k + 1) (if b then m ||| 2 ^ k else m) bs

theorem mk_spec : ∀ (bs w : List Bool) (m : ℕ), Inv w m → Inv (w ++ bs) (mk w.length m bs)
  | [], w, m, h => by simpa [mk] using h
  | b :: bs, w, m, h => by
    have := mk_spec bs (w ++ [b]) _ (step_inv w m b h)
    simpa [mk] using this

def run : ℕ → ℕ → List Gate → ℕ
  | _, m, [] => m
  | k, m, g :: gs => run (k + 1) (if g.op.eval (g.inputs.map fun i => m.testBit i) then m ||| 2 ^ k else m) gs

theorem run_spec : ∀ (gs : List Gate) (w : List Bool) (m : ℕ), Inv w m →
    Inv (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) (run w.length m gs)
  | [], w, m, h => by simpa [run] using h
  | g :: gs, w, m, h => by
    have hmap : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => m.testBit i) :=
      List.map_congr_left (fun i _ => h.1 i)
    have := run_spec gs _ _ (step_inv w m (g.op.eval (g.inputs.map fun i => w.getD i false)) h)
    simp only [List.foldl_cons, run]
    rw [hmap] at this ⊢
    simpa using this

theorem eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (run x.length (mk 0 0 x) C.gates).testBit C.output := by
  have h0 : Inv [] 0 := ⟨by simp, by simp⟩
  have hx := mk_spec x [] 0 h0
  simp only [List.nil_append, List.length_nil] at hx
  exact (run_spec C.gates x _ hx).1 C.output

def mchk (gs : List Gate) : Bool :=
  gs.all (fun g => (match g.op with
    | GateOp.and => true
    | GateOp.or => true
    | _ => false) && decide (g.inputs.length ≤ 2))

theorem mchk_spec (C : Circuit) (h : mchk C.gates = true) : PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  simp only [mchk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨?_, h2⟩
  cases hop : g.op <;> simp_all


theorem enc_spec (Q : Finset (Fin 13)) :
    Q = Finset.univ.filter (fun u : Fin 13 => (mk 0 0 (List.ofFn fun u : Fin 13 => decide (u ∈ Q))).testBit u.val) ∧
    mk 0 0 (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) < 8192 := by
  have h0 : Inv [] 0 := ⟨by simp, by simp⟩
  have hx := mk_spec (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) [] 0 h0
  simp only [List.nil_append, List.length_nil] at hx
  constructor
  · ext u
    have := hx.1 u.val
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← this]
    fin_cases u <;> simp
  · have := Nat.lt_pow_two_of_testBit (mk 0 0 (List.ofFn fun u : Fin 13 => decide (u ∈ Q))) (n := 13)
      (fun i hi => hx.2 i (by simpa using hi))
    simpa using this


def mchk2 (gs : List Gate) : Bool :=
  gs.all (fun g => (match g.op with
    | GateOp.and => true
    | GateOp.or => true
    | _ => false) && decide (g.inputs.length = 2))

theorem mchk2_spec (gs : List Gate) (h : mchk2 gs = true) :
    ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  simp only [mchk2, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨?_, h2⟩
  cases hop : g.op <;> simp_all

def circ : Circuit := { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 43] }], output := 48 }

def S (d : Fin 13) : Bool := d = 0 || d = 1 || d = 3 || d = 9

theorem memS (d : Fin 13) : d ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔ S d = true := by
  revert d
  decide

def cnt (f : Fin 13 → Bool) : ℕ := ((List.finRange 13).filter f).length

theorem cnt_eq (f : Fin 13 → Bool) : (Finset.univ.filter (fun u => f u = true)).card = cnt f := by
  rfl

def ok (m : ℕ) : Bool :=
  !(cnt (fun u : Fin 13 => m.testBit u.val) == 4 &&
    (List.finRange 13).all (fun k => decide (cnt (fun u : Fin 13 => m.testBit u.val && S (u - k)) ≤ 2))) ||
  !(run 26 (mk 0 0 (List.ofFn (fun u : Fin 13 => m.testBit u.val) ++
    List.ofFn (fun v : Fin 13 => (List.finRange 13).all (fun r => !(m.testBit r.val && S (r - v)))))) circ.gates).testBit 48

set_option maxRecDepth 100000 in
theorem all_ok : ∀ m < 8192, ok m = true := by
  decide +kernel

theorem lines_eq (m : ℕ) (v : Fin 13) : decide (∀ r ∈ Finset.univ.filter (fun u : Fin 13 => m.testBit u.val = true), r - v ∉ ({0, 1, 3, 9} : Finset (Fin 13))) = (List.finRange 13).all (fun r => !(m.testBit r.val && S (r - v))) := by
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_const, Finset.mem_filter, Finset.mem_univ, true_and, memS]
  refine forall_congr' fun r => ?_
  cases m.testBit r.val <;> simp

theorem fin_ok (m : ℕ) (hm : m < 8192) (hc : cnt (fun u : Fin 13 => m.testBit u.val) = 4)
    (hk : ∀ k : Fin 13, cnt (fun u : Fin 13 => m.testBit u.val && S (u - k)) ≤ 2) :
    (run 26 (mk 0 0 (List.ofFn (fun u : Fin 13 => m.testBit u.val) ++
      List.ofFn (fun v : Fin 13 => (List.finRange 13).all (fun r => !(m.testBit r.val && S (r - v)))))) circ.gates).testBit 48 = false := by
  have h := all_ok m hm
  have e : (cnt (fun u : Fin 13 => m.testBit u.val) == 4 &&
    (List.finRange 13).all (fun k => decide (cnt (fun u : Fin 13 => m.testBit u.val && S (u - k)) ≤ 2))) = true := by
    simp [hc, List.all_eq_true, hk]
  unfold ok at h
  rw [e] at h
  revert h
  generalize (run 26 (mk 0 0 (List.ofFn (fun u : Fin 13 => m.testBit u.val) ++
      List.ofFn (fun v : Fin 13 => (List.finRange 13).all (fun r => !(m.testBit r.val && S (r - v)))))) circ.gates).testBit 48 = b
  cases b <;> simp

end PEqualNP.Outside.L_meta_1747_aux

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1747 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [27, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [29, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [30, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [32, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [33, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [35, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [36, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [38, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [39, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [41, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [42, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [28, 31] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [44, 34] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [45, 37] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [46, 40] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [47, 43] }], output := 48 } : PEqualNP.CircuitLowerBounds.Circuit) →
  C.gates.length = 23 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (13 + 13) C ∧
  (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ p l : Fin 13, p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
     C.eval (List.ofFn (fun u : Fin 13 => decide (u = p)) ++ List.ofFn (fun v : Fin 13 => decide (v = l)))
       = decide (((p : ℕ), (l : ℕ)) ∈ ([(0, 0), (1, 1), (2, 2), (5, 4)] : List (ℕ × ℕ)))) ∧
  (∀ Q : Finset (Fin 13), Q.card = 4 →
     (∀ k : Fin 13, (Q.filter (fun u0 : Fin 13 => u0 - k ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2) →
     C.eval (List.ofFn (fun u2 : Fin 13 => decide (u2 ∈ Q))
             ++ List.ofFn (fun v2 : Fin 13 => decide (∀ r ∈ Q, r - v2 ∉ ({0, 1, 3, 9} : Finset (Fin 13))))) = false) := by
  intro C hC
  subst hC
  refine ⟨rfl, fun j hj i hi => PEqualNP.Outside.L_meta_1747_aux.chk_spec _ 26 (by decide +kernel) j hj i hi, PEqualNP.Outside.L_meta_1747_aux.mchk2_spec _ (by decide +kernel), ?_, ?_⟩
  · simp only [PEqualNP.Outside.L_meta_1747_aux.eval_eq, PEqualNP.Outside.L_meta_1747_aux.memS]
    set_option maxRecDepth 100000 in decide +kernel
  · intro Q hc hk
    obtain ⟨hQ, hm⟩ := PEqualNP.Outside.L_meta_1747_aux.enc_spec Q
    generalize PEqualNP.Outside.L_meta_1747_aux.mk 0 0 (List.ofFn fun u : Fin 13 => decide (u ∈ Q)) = m at hQ hm
    subst hQ
    simp only [PEqualNP.Outside.L_meta_1747_aux.cnt_eq, Finset.filter_filter, PEqualNP.Outside.L_meta_1747_aux.memS] at hc hk
    simp only [← Bool.and_eq_true, PEqualNP.Outside.L_meta_1747_aux.cnt_eq] at hc hk
    rw [PEqualNP.Outside.L_meta_1747_aux.eval_eq]
    simp only [PEqualNP.Outside.L_meta_1747_aux.lines_eq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.decide_eq_true]
    rw [List.length_append, List.length_ofFn, List.length_ofFn]
    exact PEqualNP.Outside.L_meta_1747_aux.fin_ok m hm hc hk
