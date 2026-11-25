import PEqualNP.Defs
import PEqualNP.Library.LRAT.LinkN2

namespace PEqualNP.Outside.V_meta_9587__k2
open PEqualNP.Library.LRAT PEqualNP.Library.LRAT.LinkN

-- The frame of this file (the encoding enc2, the packed certificate and the theorem lower) follows the proof of
-- L-meta-9507 by Stasana. The circuit and the certificate are new: the certificate was found by a clause learning
-- search and holds, for every learned clause, the clauses that make it follow by unit propagation.

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩], 5⟩

def rows : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

def gg (r : ℕ) : Bool := (32896 : ℕ).testBit r

def F : List (List ℕ) := enc2 4 1 gg rows

def kw : List Nat := [
0x43a0480e0000000000000000e0110dc34040330c8300bc2e02c000000002400000000a80000000000000000000000000000000000000000000000000026000080940700000000240000008806084000001f0140001003008000000000000000000000000000000000000007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000d80000000000000000000000000000b40000000000000000000000000000000000000000290000000000000000a0000000000000000000000000023000000000000000080000000000000000000000000000000000000d0040000000000000000000000000000000007000000000000000000000000000000000000000000000000000000000000000000000003e00000000000ec0000000000000e400000000003500000000000c40000000000000b000000000002b00000000000000000000000000000000000000000000000027000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001d000000000000000000000001b00000000000000000000000000001805c16054140280c]

noncomputable def kk : List Nat := unpack 10 kw

def pw : List Nat := [
0x10685e02579088610c40202c090600507c650406303dd40add20a8bc048bb0386702a87020070011d0811b0791700a320063501e3101a2f0162d0122b00c000f8091841517c0d5c80c1941018c0f2f0122ec0e19c0aa1c0801c0045c028c8018d4078c4068bc058b4048ac03000090600c0202e5cc14178091943618c321842f19c0aa1c0801c0045c028c8018d4078c4068bc058b4048ac03000bb0380b00c280240d5f01c1781901427194377683876034758302f83ba1c0801c004842347c2145c028c8018d4078c4068bc058b4048ac03000bc2e812098600258f0740202c630cdea06c090f06702a8702007001330a51700a320063501e3101a2f0162d0122b00c002f0042fddb1905e0641618809184115c80c19c0aa1c0801c0045c028c8018d4078c4068bc058b4048ac03000bc1905e0243c0246505c630e4610445f035720300802c050d4030b1de0f5dd0e8c004cc30b46702a870200700127095240911700a320063501e3101a2f0162d0122b00c002f0ba2f83b]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem refuted : ¬ FormulaSat F :=
  checkW_sound F kk 10 pw (by decide +kernel)

theorem tab : ∀ r < 16, PEqualNP.MetaComplexity.tableIndex (fun i : Fin 4 => r.testBit i) = r := by decide +kernel

theorem lower (t : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (32896 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t) : 2 ≤ t := by
  by_contra hlt
  obtain ⟨D, hD, hs, hr⟩ := h
  have hv := valid_ofCirc 4 1 gg (· ∈ rows) D hD (by have h0 : D.gates.length ≤ t := hs; omega) (fun r hm => by
    have h16 : r < 16 := by clear hD hs hr hlt; revert r; decide
    show D.eval (List.ofFn fun i : Fin 4 => r.testBit i) = _
    refine (hr _).trans ?_
    show (32896 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex fun i : Fin 4 => r.testBit i) = (32896 : ℕ).testBit r
    rw [tab r h16])
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact refuted ⟨val 4 1 M, enc2_sat (by decide) hM hnf hlx⟩

end PEqualNP.Outside.V_meta_9587__k2

theorem PEqualNP.Outside.V_meta_9587__k2 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (32896 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 2 ∧
  ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (32896 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 2 ≤ t :=
  ⟨⟨PEqualNP.Outside.V_meta_9587__k2.C, by simp [PEqualNP.Outside.V_meta_9587__k2.C, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩, PEqualNP.Outside.V_meta_9587__k2.lower⟩
