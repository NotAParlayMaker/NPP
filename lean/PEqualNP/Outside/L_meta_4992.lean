import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4992

open PEqualNP.CircuitLowerBounds

def flag (o : GateOp) : Bool :=
  match o with
  | GateOp.or => true
  | _ => false

def enc (g : Gate) : Bool × ℕ × ℕ :=
  match g.inputs with
  | [] => (false, if flag g.op = true then 0 else 1, if flag g.op = true then 0 else 1)
  | [a] => (flag g.op, a + 2, a + 2)
  | a :: b :: _ => (flag g.op, a + 2, b + 2)

def st (x6 : List (BitVec 24)) (x7 : Bool × ℕ × ℕ) : List (BitVec 24) :=
  x6 ++ [if x7.1 = Bool.true then x6.getD x7.2.1 (0 : BitVec 24) ||| x6.getD x7.2.2 0
    else x6.getD x7.2.1 0 &&& x6.getD x7.2.2 0]

theorem bitD (W : List (BitVec 24)) (k i : ℕ) :
    (W.getD i 0).getLsbD k = (W.map fun v => v.getLsbD k).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> simp

theorem gate_bit (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (k : ℕ) (hk : k < 24) (W : List (BitVec 24)) (wb : List Bool)
    (hW : W.map (fun v => v.getLsbD k) = false :: true :: wb) :
    (if (enc g).1 = Bool.true then W.getD (enc g).2.1 (0 : BitVec 24) ||| W.getD (enc g).2.2 0
      else W.getD (enc g).2.1 0 &&& W.getD (enc g).2.2 0).getLsbD k
      = g.op.eval (g.inputs.map fun i => wb.getD i false) := by
  have hb : ∀ i, (W.getD i 0).getLsbD k = (false :: true :: wb).getD i false := by
    intro i; rw [bitD, hW]
  have hb2 : ∀ i, (W.getD i (BitVec.ofNat 24 0)).getLsbD k = (false :: true :: wb).getD i false := hb
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl <;>
      simp [-List.getD_eq_getElem?_getD, enc, flag, GateOp.eval, BitVec.getLsbD_and] <;> simp only [hb2] <;> rfl
  | [a], _ =>
    rcases hop with rfl | rfl <;>
      simp [-List.getD_eq_getElem?_getD, enc, flag, GateOp.eval, BitVec.getLsbD_and,
        BitVec.getLsbD_or] <;> simp only [hb2] <;> rfl
  | [a, b], _ =>
    rcases hop with rfl | rfl <;>
      simp [-List.getD_eq_getElem?_getD, enc, flag, GateOp.eval, BitVec.getLsbD_and,
        BitVec.getLsbD_or] <;> simp only [hb2] <;> rfl
  | _ :: _ :: _ :: _, h => simp at h

theorem fold_bit (k : ℕ) (hk : k < 24) : ∀ (gs : List Gate),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    ∀ (W : List (BitVec 24)) (wb : List Bool),
    W.map (fun v => v.getLsbD k) = false :: true :: wb →
    ((gs.map enc).foldl st W).map (fun v => v.getLsbD k) = false :: true ::
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wb := by
  intro gs
  induction gs with
  | nil => intro _ W wb hW; simpa using hW
  | cons g gs ih =>
    intro hm W wb hW
    have hg := hm g (by simp)
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    apply ih (fun g1 hg1 => hm g1 (by simp [hg1]))
    have e := gate_bit g hg.1 hg.2 k hk W wb hW
    simp only [st, List.map_append, List.map_cons, List.map_nil, hW, e, List.cons_append]

end PEqualNP.Outside.L_meta_4992

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4992 in
theorem PEqualNP.Outside.L_meta_4992 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (BitVec (24 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x4 : List (Bool × ℕ × ℕ)), x4.length = x1.size ∧ ∀ (x5 : Fin (24 : ℕ)), ((List.foldl (fun (x6 : List (BitVec (24 : ℕ))) (x7 : Bool × ℕ × ℕ) => x6 ++ [if x7.1 = Bool.true then x6.getD x7.2.1 (0 : BitVec (24 : ℕ)) ||| x6.getD x7.2.2 (0 : BitVec (24 : ℕ)) else x6.getD x7.2.1 (0 : BitVec (24 : ℕ)) &&& x6.getD x7.2.2 (0 : BitVec (24 : ℕ))]) ((0 : BitVec (24 : ℕ)) :: BitVec.allOnes (24 : ℕ) :: x2) x4).getD (x1.output + (2 : ℕ)) (0 : BitVec (24 : ℕ))).getLsbD ↑x5 = x1.eval (List.map (fun (x6 : BitVec (24 : ℕ)) => x6.getLsbD ↑x5) x2) := by
  intro x1 x2 hmono
  refine ⟨x1.gates.map enc, by simp [Circuit.size], ?_⟩
  intro x5
  have hW : ((0 : BitVec 24) :: BitVec.allOnes 24 :: x2).map (fun v => v.getLsbD x5)
      = false :: true :: x2.map (fun v => v.getLsbD x5) := by
    simp only [List.map_cons, BitVec.getLsbD_zero, BitVec.getLsbD_allOnes, x5.2, decide_true]
    simp
  have h := fold_bit x5 x5.2 x1.gates hmono _ _ hW
  change ((List.foldl st _ (x1.gates.map enc)).getD (x1.output + 2) 0).getLsbD x5 = _
  rw [bitD, h]
  simp only [Circuit.eval, Circuit.wires, List.getD_cons_succ]
