import PEqualNP.Defs
import PEqualNP.Library.LRAT.LinkN2

namespace PEqualNP.Outside.V_meta_9533__k2
open PEqualNP.Library.LRAT PEqualNP.Library.LRAT.LinkN

-- The frame of this file (the encoding enc2, the packed certificate and the theorem lower) follows the proof of
-- L-meta-9507 by Stasana. The circuit and the certificate are new: the certificate was found by a clause learning
-- search and holds, for every learned clause, the clauses that make it follow by unit propagation.

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩], 5⟩

def rows : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

def gg (r : ℕ) : Bool := (170 : ℕ).testBit r

def F : List (List ℕ) := enc2 4 1 gg rows

def kw : List Nat := [
0x41b058130000000000000000b02b0a8000a4280002709815030000000002400048000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000001c1101805010030080000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003c000000b00400000000000000000088210801f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000942408c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a0641805c140280d]

noncomputable def kk : List Nat := unpack 10 kw

def pw : List Nat := [
0x10246105c5f049720280803003038650a8630a1d1088bc070bb0740503dec0346702e870200700135045180411700a320062b01e3501a310162f0122d00c000b00a020255cc16178091942918c271842619c0ba1c0801c0045c028c8018ac078d4068c4058bc048b403000bb0740918c181841517c125c80a0200c00c0e1942b744232f81b0140f7b00d19c0ba1c0801c004d4114601045c028c8018ac078d4068c4058bc048b403000bc2e81c0246506463068610545f049720280803003039d1090c004c0503dec034c30506702e870200700135045180411700a320062b01e3501a310162f0122d00c002f0ba2f81b04cc1084bf080bd07cbb078c305287020070011700a320062b01e3501a310162f0122d00c007b00d]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem refuted : ¬ FormulaSat F :=
  checkW_sound F kk 10 pw (by decide +kernel)

theorem tab : ∀ r < 16, PEqualNP.MetaComplexity.tableIndex (fun i : Fin 4 => r.testBit i) = r := by decide +kernel

theorem lower (t : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (170 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t) : 2 ≤ t := by
  by_contra hlt
  obtain ⟨D, hD, hs, hr⟩ := h
  have hv := valid_ofCirc 4 1 gg (· ∈ rows) D hD (by have h0 : D.gates.length ≤ t := hs; omega) (fun r hm => by
    have h16 : r < 16 := by clear hD hs hr hlt; revert r; decide
    show D.eval (List.ofFn fun i : Fin 4 => r.testBit i) = _
    refine (hr _).trans ?_
    show (170 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex fun i : Fin 4 => r.testBit i) = (170 : ℕ).testBit r
    rw [tab r h16])
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact refuted ⟨val 4 1 M, enc2_sat (by decide) hM hnf hlx⟩

end PEqualNP.Outside.V_meta_9533__k2

theorem PEqualNP.Outside.V_meta_9533__k2 : PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (170 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 2 ∧
  ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (170 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) t → 2 ≤ t :=
  ⟨⟨PEqualNP.Outside.V_meta_9533__k2.C, by simp [PEqualNP.Outside.V_meta_9533__k2.C, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩, PEqualNP.Outside.V_meta_9533__k2.lower⟩
