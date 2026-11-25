import PEqualNP.Defs
import PEqualNP.Library.LRAT.LinkN2

namespace PEqualNP.Outside.V_meta_9624__k2
open PEqualNP.Library.LRAT PEqualNP.Library.LRAT.LinkN

-- The frame of this file (the encoding enc2, the packed certificate and the theorem lower) follows the proof of
-- L-meta-9507 by Stasana. The circuit and the certificate are new: the certificate was found by a clause learning
-- search and holds, for every learned clause, the clauses that make it follow by unit propagation.

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩], 5⟩

def rows : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

def gg (r : ℕ) : Bool := (43176 : ℕ).testBit r

def F : List (List ℕ) := enc2 4 1 gg rows

def kw : List Nat := [
0x42d0440e0000000000000000b02b0a40009c260002508c22030000000002c00000000000000000000000000000000000000000000000000000001c0000000000000000000006c000001a0000a03c090201801c0001805010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a800000000000000000000000000000000000000000000000000000000000000000000000007800000000000007400000000000000000000000000004000000000000006400000000000000000000000000000000000030080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000a0000000009000000000842000000000000001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160541404c120040d]

noncomputable def kk : List Nat := unpack 10 kw

def pw : List Nat := [
0x10006104c5f03572008080300307405060650a863099d909dd2078bc0b8bb0586702e8702807005200691b05d170123200e35026310222f01e2d01a2b014000c002020225cc12178001942818c251842419c0ba1c0a01c0145c048c8038d4098c4088bc078b4068ac05000bb0580018c141841017c0d5c8020200c0141c00c0f1942b758237541f2f82d19c0ba1c0a01c0147c194700e45c048c8038d4098c4088bc078b4068ac05000bc2e82e00065054630b0610405f0357200808030050a40303dde0bdd5080c0044c30846702e87028070052706d1c039170123200e35026310222f01e2d01a2b014002f0ba2f82d]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem refuted : ¬ FormulaSat F :=
  checkW_sound F kk 10 pw (by decide +kernel)

theorem tab : ∀ r < 16, PEqualNP.MetaComplexity.tableIndex (fun i : Fin 4 => r.testBit i) = r := by decide +kernel

theorem lower (t : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (43176 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t) : 2 ≤ t := by
  by_contra hlt
  obtain ⟨D, hD, hs, hr⟩ := h
  have hv := valid_ofCirc 4 1 gg (· ∈ rows) D hD (by have h0 : D.gates.length ≤ t := hs; omega) (fun r hm => by
    have h16 : r < 16 := by clear hD hs hr hlt; revert r; decide
    show D.eval (List.ofFn fun i : Fin 4 => r.testBit i) = _
    refine (hr _).trans ?_
    show (43176 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex fun i : Fin 4 => r.testBit i) = (43176 : ℕ).testBit r
    rw [tab r h16])
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact refuted ⟨val 4 1 M, enc2_sat (by decide) hM hnf hlx⟩

end PEqualNP.Outside.V_meta_9624__k2

theorem PEqualNP.Outside.V_meta_9624__k2 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (43176 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 2 ∧
  ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (43176 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 2 ≤ t :=
  ⟨⟨PEqualNP.Outside.V_meta_9624__k2.C, by simp [PEqualNP.Outside.V_meta_9624__k2.C, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩, PEqualNP.Outside.V_meta_9624__k2.lower⟩
