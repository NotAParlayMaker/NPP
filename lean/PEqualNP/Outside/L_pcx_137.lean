import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_137_aux
open PEqualNP.ProofComplexity

private abbrev V := Fin 5 × Fin 2
private abbrev F := (fun C => linOfClause C) '' BPHP 5 2
private def collision (i j : Fin 5) (a : Fin 2 → Bool) : Clause V :=
  Finset.univ.image (fun b => ((i,b), !a b)) ∪ Finset.univ.image (fun b => ((j,b), !a b))
private theorem axiomLine (i j : Fin 5) (a : Fin 2 → Bool) (h : i ≠ j) :
    linOfClause (collision i j a) ∈ F := ⟨_, ⟨i,j,a,h,rfl⟩,rfl⟩
private def s0 : List (LinClause V) := []
private theorem d0 : IsLinDerivation F s0 := .nil

private def c1 : LinClause V := linOfClause (collision 1 4 ![true, false])
private def s1 := c1 :: s0
private theorem d1 : IsLinDerivation F s1 :=
  .ax d0 (axiomLine 1 4 ![true, false] (by decide))

private def c2 : LinClause V := linOfClause (collision 1 4 ![true, true])
private def s2 := c2 :: s1
private theorem d2 : IsLinDerivation F s2 :=
  .ax d1 (axiomLine 1 4 ![true, true] (by decide))

private def c3 : LinClause V := linOfClause (collision 0 4 ![false, false])
private def s3 := c3 :: s2
private theorem d3 : IsLinDerivation F s3 :=
  .ax d2 (axiomLine 0 4 ![false, false] (by decide))

private def c4 : LinClause V := linOfClause (collision 1 2 ![false, true])
private def s4 := c4 :: s3
private theorem d4 : IsLinDerivation F s4 :=
  .ax d3 (axiomLine 1 2 ![false, true] (by decide))

private def c5 : LinClause V := linOfClause (collision 0 2 ![true, true])
private def s5 := c5 :: s4
private theorem d5 : IsLinDerivation F s5 :=
  .ax d4 (axiomLine 0 2 ![true, true] (by decide))

private def c6 : LinClause V := linOfClause (collision 3 4 ![true, true])
private def s6 := c6 :: s5
private theorem d6 : IsLinDerivation F s6 :=
  .ax d5 (axiomLine 3 4 ![true, true] (by decide))

private def c7 : LinClause V := linOfClause (collision 2 4 ![true, true])
private def s7 := c7 :: s6
private theorem d7 : IsLinDerivation F s7 :=
  .ax d6 (axiomLine 2 4 ![true, true] (by decide))

private def c8 : LinClause V := linOfClause (collision 0 3 ![true, true])
private def s8 := c8 :: s7
private theorem d8 : IsLinDerivation F s8 :=
  .ax d7 (axiomLine 0 3 ![true, true] (by decide))

private def c9 : LinClause V := linOfClause (collision 0 4 ![false, true])
private def s9 := c9 :: s8
private theorem d9 : IsLinDerivation F s9 :=
  .ax d8 (axiomLine 0 4 ![false, true] (by decide))

private def c10 : LinClause V := linOfClause (collision 3 4 ![false, true])
private def s10 := c10 :: s9
private theorem d10 : IsLinDerivation F s10 :=
  .ax d9 (axiomLine 3 4 ![false, true] (by decide))

private def c11 : LinClause V := linOfClause (collision 0 2 ![false, false])
private def s11 := c11 :: s10
private theorem d11 : IsLinDerivation F s11 :=
  .ax d10 (axiomLine 0 2 ![false, false] (by decide))

private def c12 : LinClause V := linOfClause (collision 1 2 ![true, false])
private def s12 := c12 :: s11
private theorem d12 : IsLinDerivation F s12 :=
  .ax d11 (axiomLine 1 2 ![true, false] (by decide))

private def c13 : LinClause V := linOfClause (collision 1 3 ![false, true])
private def s13 := c13 :: s12
private theorem d13 : IsLinDerivation F s13 :=
  .ax d12 (axiomLine 1 3 ![false, true] (by decide))

private def c14 : LinClause V := linOfClause (collision 0 1 ![false, false])
private def s14 := c14 :: s13
private theorem d14 : IsLinDerivation F s14 :=
  .ax d13 (axiomLine 0 1 ![false, false] (by decide))

private def c15 : LinClause V := linOfClause (collision 2 4 ![true, false])
private def s15 := c15 :: s14
private theorem d15 : IsLinDerivation F s15 :=
  .ax d14 (axiomLine 2 4 ![true, false] (by decide))

private def c16 : LinClause V := linOfClause (collision 0 3 ![true, false])
private def s16 := c16 :: s15
private theorem d16 : IsLinDerivation F s16 :=
  .ax d15 (axiomLine 0 3 ![true, false] (by decide))

private def c17 : LinClause V := linOfClause (collision 0 1 ![true, false])
private def s17 := c17 :: s16
private theorem d17 : IsLinDerivation F s17 :=
  .ax d16 (axiomLine 0 1 ![true, false] (by decide))

private def c18 : LinClause V := linOfClause (collision 1 3 ![true, true])
private def s18 := c18 :: s17
private theorem d18 : IsLinDerivation F s18 :=
  .ax d17 (axiomLine 1 3 ![true, true] (by decide))

private def c19 : LinClause V := linOfClause (collision 0 3 ![false, false])
private def s19 := c19 :: s18
private theorem d19 : IsLinDerivation F s19 :=
  .ax d18 (axiomLine 0 3 ![false, false] (by decide))

private def c20 : LinClause V := linOfClause (collision 1 4 ![false, true])
private def s20 := c20 :: s19
private theorem d20 : IsLinDerivation F s20 :=
  .ax d19 (axiomLine 1 4 ![false, true] (by decide))

private def c21 : LinClause V := linOfClause (collision 0 3 ![false, true])
private def s21 := c21 :: s20
private theorem d21 : IsLinDerivation F s21 :=
  .ax d20 (axiomLine 0 3 ![false, true] (by decide))

private def c22 : LinClause V := linOfClause (collision 2 4 ![false, false])
private def s22 := c22 :: s21
private theorem d22 : IsLinDerivation F s22 :=
  .ax d21 (axiomLine 2 4 ![false, false] (by decide))

private def c23 : LinClause V := linOfClause (collision 0 4 ![true, false])
private def s23 := c23 :: s22
private theorem d23 : IsLinDerivation F s23 :=
  .ax d22 (axiomLine 0 4 ![true, false] (by decide))

private def c24 : LinClause V := linOfClause (collision 2 3 ![false, false])
private def s24 := c24 :: s23
private theorem d24 : IsLinDerivation F s24 :=
  .ax d23 (axiomLine 2 3 ![false, false] (by decide))

private def c25 : LinClause V := linOfClause (collision 2 4 ![false, true])
private def s25 := c25 :: s24
private theorem d25 : IsLinDerivation F s25 :=
  .ax d24 (axiomLine 2 4 ![false, true] (by decide))

private def c26 : LinClause V := linOfClause (collision 2 3 ![true, true])
private def s26 := c26 :: s25
private theorem d26 : IsLinDerivation F s26 :=
  .ax d25 (axiomLine 2 3 ![true, true] (by decide))

private def c27 : LinClause V := linOfClause (collision 3 4 ![true, false])
private def s27 := c27 :: s26
private theorem d27 : IsLinDerivation F s27 :=
  .ax d26 (axiomLine 3 4 ![true, false] (by decide))

private def c28 : LinClause V := linOfClause (collision 3 4 ![false, false])
private def s28 := c28 :: s27
private theorem d28 : IsLinDerivation F s28 :=
  .ax d27 (axiomLine 3 4 ![false, false] (by decide))

private def c29 : LinClause V := linOfClause (collision 0 2 ![true, false])
private def s29 := c29 :: s28
private theorem d29 : IsLinDerivation F s29 :=
  .ax d28 (axiomLine 0 2 ![true, false] (by decide))

private def c30 : LinClause V := linOfClause (collision 0 2 ![false, true])
private def s30 := c30 :: s29
private theorem d30 : IsLinDerivation F s30 :=
  .ax d29 (axiomLine 0 2 ![false, true] (by decide))

private def c31 : LinClause V := linOfClause (collision 1 3 ![false, false])
private def s31 := c31 :: s30
private theorem d31 : IsLinDerivation F s31 :=
  .ax d30 (axiomLine 1 3 ![false, false] (by decide))

private def c32 : LinClause V := linOfClause (collision 2 3 ![false, true])
private def s32 := c32 :: s31
private theorem d32 : IsLinDerivation F s32 :=
  .ax d31 (axiomLine 2 3 ![false, true] (by decide))

private def c33 : LinClause V := linOfClause (collision 0 1 ![true, true])
private def s33 := c33 :: s32
private theorem d33 : IsLinDerivation F s33 :=
  .ax d32 (axiomLine 0 1 ![true, true] (by decide))

private def c34 : LinClause V := linOfClause (collision 1 2 ![true, true])
private def s34 := c34 :: s33
private theorem d34 : IsLinDerivation F s34 :=
  .ax d33 (axiomLine 1 2 ![true, true] (by decide))

private def c35 : LinClause V := linOfClause (collision 1 3 ![true, false])
private def s35 := c35 :: s34
private theorem d35 : IsLinDerivation F s35 :=
  .ax d34 (axiomLine 1 3 ![true, false] (by decide))

private def c36 : LinClause V := linOfClause (collision 0 4 ![true, true])
private def s36 := c36 :: s35
private theorem d36 : IsLinDerivation F s36 :=
  .ax d35 (axiomLine 0 4 ![true, true] (by decide))

private def c37 : LinClause V := linOfClause (collision 0 1 ![false, true])
private def s37 := c37 :: s36
private theorem d37 : IsLinDerivation F s37 :=
  .ax d36 (axiomLine 0 1 ![false, true] (by decide))

private def c38 : LinClause V := linOfClause (collision 1 4 ![false, false])
private def s38 := c38 :: s37
private theorem d38 : IsLinDerivation F s38 :=
  .ax d37 (axiomLine 1 4 ![false, false] (by decide))

private def c39 : LinClause V := linOfClause (collision 2 3 ![true, false])
private def s39 := c39 :: s38
private theorem d39 : IsLinDerivation F s39 :=
  .ax d38 (axiomLine 2 3 ![true, false] (by decide))

private def c40 : LinClause V := linOfClause (collision 1 2 ![false, false])
private def s40 := c40 :: s39
private theorem d40 : IsLinDerivation F s40 :=
  .ax d39 (axiomLine 1 2 ![false, false] (by decide))

private def c41 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, false), ({(1, 1)}, true), ({(4, 0)}, false), ({(4, 1)}, false)}
private def s41 := c41 :: s40
private theorem d41 : IsLinDerivation F s41 :=
  .res (C := c36) (D := c17) d40
    (List.mem_of_getElem? (i := 4) rfl)
    (List.mem_of_getElem? (i := 23) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c42 : LinClause V := {({(1, 0)}, false), ({(1, 1)}, true), ({(3, 0)}, false), ({(4, 0)}, false), ({(4, 1)}, false)}
private def s42 := c42 :: s41
private theorem d42 : IsLinDerivation F s42 :=
  .res (C := c6) (D := c35) d41
    (List.mem_of_getElem? (i := 35) rfl)
    (List.mem_of_getElem? (i := 6) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c43 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, true), ({(2, 0)}, true), ({(3, 0)}, true), ({(3, 1)}, false)}
private def s43 := c43 :: s42
private theorem d43 : IsLinDerivation F s43 :=
  .res (C := c32) (D := c11) d42
    (List.mem_of_getElem? (i := 10) rfl)
    (List.mem_of_getElem? (i := 31) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c44 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, true), ({(2, 0)}, true), ({(3, 0)}, true)}
private def s44 := c44 :: s43
private theorem d44 : IsLinDerivation F s44 :=
  .res (C := c43) (D := c19) d43
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 24) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c45 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, false), ({(2, 0)}, true), ({(2, 1)}, true), ({(3, 0)}, true)}
private def s45 := c45 :: s44
private theorem d45 : IsLinDerivation F s45 :=
  .res (C := c21) (D := c24) d44
    (List.mem_of_getElem? (i := 23) rfl)
    (List.mem_of_getElem? (i := 20) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c46 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, false), ({(2, 0)}, true), ({(3, 0)}, true)}
private def s46 := c46 :: s45
private theorem d46 : IsLinDerivation F s46 :=
  .res (C := c30) (D := c45) d45
    (List.mem_of_getElem? (i := 15) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c47 : LinClause V := {({(0, 0)}, true), ({(2, 0)}, true), ({(3, 0)}, true)}
private def s47 := c47 :: s46
private theorem d47 : IsLinDerivation F s47 :=
  .res (C := c46) (D := c44) d46
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 2) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c48 : LinClause V := {({(0, 0)}, true), ({(1, 0)}, false), ({(1, 1)}, true), ({(2, 0)}, true), ({(4, 0)}, false), ({(4, 1)}, false)}
private def s48 := c48 :: s47
private theorem d48 : IsLinDerivation F s48 :=
  .res (C := c42) (D := c47) d47
    (List.mem_of_getElem? (i := 5) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(3, 0)}, by decide, by decide, by decide⟩

private def c49 : LinClause V := {({(1, 0)}, false), ({(1, 1)}, true), ({(2, 0)}, true), ({(4, 0)}, false), ({(4, 1)}, false)}
private def s49 := c49 :: s48
private theorem d49 : IsLinDerivation F s49 :=
  .res (C := c41) (D := c48) d48
    (List.mem_of_getElem? (i := 7) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(0, 0)}, by decide, by decide, by decide⟩

private def c50 : LinClause V := {({(1, 0)}, false), ({(1, 1)}, true), ({(2, 0)}, false), ({(4, 0)}, false), ({(4, 1)}, false)}
private def s50 := c50 :: s49
private theorem d50 : IsLinDerivation F s50 :=
  .res (C := c7) (D := c12) d49
    (List.mem_of_getElem? (i := 42) rfl)
    (List.mem_of_getElem? (i := 37) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c51 : LinClause V := {({(1, 0)}, false), ({(1, 1)}, true), ({(4, 0)}, false), ({(4, 1)}, false)}
private def s51 := c51 :: s50
private theorem d51 : IsLinDerivation F s51 :=
  .res (C := c50) (D := c49) d50
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 1) rfl)
    ⟨{(2, 0)}, by decide, by decide, by decide⟩

private def c52 : LinClause V := {({(1, 0)}, false), ({(4, 0)}, false), ({(4, 1)}, false)}
private def s52 := c52 :: s51
private theorem d52 : IsLinDerivation F s52 :=
  .res (C := c2) (D := c51) d51
    (List.mem_of_getElem? (i := 49) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c53 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, false), ({(1, 1)}, false), ({(4, 0)}, false), ({(4, 1)}, true)}
private def s53 := c53 :: s52
private theorem d53 : IsLinDerivation F s53 :=
  .res (C := c33) (D := c23) d52
    (List.mem_of_getElem? (i := 19) rfl)
    (List.mem_of_getElem? (i := 29) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c54 : LinClause V := {({(1, 0)}, false), ({(1, 1)}, false), ({(2, 0)}, false), ({(4, 0)}, false), ({(4, 1)}, true)}
private def s54 := c54 :: s53
private theorem d54 : IsLinDerivation F s54 :=
  .res (C := c34) (D := c15) d53
    (List.mem_of_getElem? (i := 19) rfl)
    (List.mem_of_getElem? (i := 38) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c55 : LinClause V := {({(0, 0)}, true), ({(1, 0)}, false), ({(1, 1)}, false), ({(3, 0)}, true), ({(4, 0)}, false), ({(4, 1)}, true)}
private def s55 := c55 :: s54
private theorem d55 : IsLinDerivation F s55 :=
  .res (C := c54) (D := c47) d54
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 7) rfl)
    ⟨{(2, 0)}, by decide, by decide, by decide⟩

private def c56 : LinClause V := {({(1, 0)}, false), ({(1, 1)}, false), ({(3, 0)}, false), ({(4, 0)}, false), ({(4, 1)}, true)}
private def s56 := c56 :: s55
private theorem d56 : IsLinDerivation F s56 :=
  .res (C := c18) (D := c27) d55
    (List.mem_of_getElem? (i := 37) rfl)
    (List.mem_of_getElem? (i := 28) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c57 : LinClause V := {({(0, 0)}, true), ({(1, 0)}, false), ({(1, 1)}, false), ({(4, 0)}, false), ({(4, 1)}, true)}
private def s57 := c57 :: s56
private theorem d57 : IsLinDerivation F s57 :=
  .res (C := c56) (D := c55) d56
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 1) rfl)
    ⟨{(3, 0)}, by decide, by decide, by decide⟩

private def c58 : LinClause V := {({(1, 0)}, false), ({(1, 1)}, false), ({(4, 0)}, false), ({(4, 1)}, true)}
private def s58 := c58 :: s57
private theorem d58 : IsLinDerivation F s58 :=
  .res (C := c53) (D := c57) d57
    (List.mem_of_getElem? (i := 4) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(0, 0)}, by decide, by decide, by decide⟩

private def c59 : LinClause V := {({(1, 0)}, false), ({(4, 0)}, false), ({(4, 1)}, true)}
private def s59 := c59 :: s58
private theorem d59 : IsLinDerivation F s59 :=
  .res (C := c58) (D := c1) d58
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 57) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c60 : LinClause V := {({(1, 0)}, false), ({(4, 0)}, false)}
private def s60 := c60 :: s59
private theorem d60 : IsLinDerivation F s60 :=
  .res (C := c52) (D := c59) d59
    (List.mem_of_getElem? (i := 7) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c61 : LinClause V := {({(1, 0)}, false), ({(2, 0)}, false), ({(2, 1)}, false), ({(3, 0)}, false), ({(3, 1)}, true)}
private def s61 := c61 :: s60
private theorem d61 : IsLinDerivation F s61 :=
  .res (C := c34) (D := c35) d60
    (List.mem_of_getElem? (i := 26) rfl)
    (List.mem_of_getElem? (i := 25) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c62 : LinClause V := {({(1, 0)}, false), ({(2, 0)}, false), ({(2, 1)}, false), ({(3, 0)}, false)}
private def s62 := c62 :: s61
private theorem d62 : IsLinDerivation F s62 :=
  .res (C := c26) (D := c61) d61
    (List.mem_of_getElem? (i := 35) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c63 : LinClause V := {({(1, 0)}, false), ({(1, 1)}, false), ({(2, 0)}, false), ({(2, 1)}, true), ({(3, 0)}, false)}
private def s63 := c63 :: s62
private theorem d63 : IsLinDerivation F s63 :=
  .res (C := c18) (D := c39) d62
    (List.mem_of_getElem? (i := 44) rfl)
    (List.mem_of_getElem? (i := 23) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c64 : LinClause V := {({(1, 0)}, false), ({(2, 0)}, false), ({(2, 1)}, true), ({(3, 0)}, false)}
private def s64 := c64 :: s63
private theorem d64 : IsLinDerivation F s64 :=
  .res (C := c63) (D := c12) d63
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 51) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c65 : LinClause V := {({(1, 0)}, false), ({(2, 0)}, false), ({(3, 0)}, false)}
private def s65 := c65 :: s64
private theorem d65 : IsLinDerivation F s65 :=
  .res (C := c62) (D := c64) d64
    (List.mem_of_getElem? (i := 2) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c66 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, true), ({(2, 0)}, true), ({(2, 1)}, false), ({(4, 0)}, true)}
private def s66 := c66 :: s65
private theorem d66 : IsLinDerivation F s66 :=
  .res (C := c25) (D := c3) d65
    (List.mem_of_getElem? (i := 40) rfl)
    (List.mem_of_getElem? (i := 62) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c67 : LinClause V := {({(0, 0)}, true), ({(2, 0)}, true), ({(2, 1)}, false), ({(4, 0)}, true)}
private def s67 := c67 :: s66
private theorem d67 : IsLinDerivation F s67 :=
  .res (C := c30) (D := c66) d66
    (List.mem_of_getElem? (i := 36) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c68 : LinClause V := {({(0, 0)}, true), ({(2, 0)}, true), ({(2, 1)}, true), ({(4, 0)}, true), ({(4, 1)}, false)}
private def s68 := c68 :: s67
private theorem d68 : IsLinDerivation F s68 :=
  .res (C := c9) (D := c11) d67
    (List.mem_of_getElem? (i := 58) rfl)
    (List.mem_of_getElem? (i := 56) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c69 : LinClause V := {({(0, 0)}, true), ({(2, 0)}, true), ({(2, 1)}, true), ({(4, 0)}, true)}
private def s69 := c69 :: s68
private theorem d69 : IsLinDerivation F s69 :=
  .res (C := c68) (D := c22) d68
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 46) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c70 : LinClause V := {({(0, 0)}, true), ({(2, 0)}, true), ({(4, 0)}, true)}
private def s70 := c70 :: s69
private theorem d70 : IsLinDerivation F s70 :=
  .res (C := c67) (D := c69) d69
    (List.mem_of_getElem? (i := 2) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c71 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, false), ({(1, 0)}, false), ({(3, 0)}, false), ({(3, 1)}, true)}
private def s71 := c71 :: s70
private theorem d71 : IsLinDerivation F s71 :=
  .res (C := c33) (D := c35) d70
    (List.mem_of_getElem? (i := 37) rfl)
    (List.mem_of_getElem? (i := 35) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c72 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, false), ({(3, 0)}, false), ({(3, 1)}, true)}
private def s72 := c72 :: s71
private theorem d72 : IsLinDerivation F s72 :=
  .res (C := c71) (D := c16) d71
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 55) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c73 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, false), ({(1, 1)}, true), ({(3, 0)}, false), ({(3, 1)}, false)}
private def s73 := c73 :: s72
private theorem d73 : IsLinDerivation F s73 :=
  .res (C := c8) (D := c17) d72
    (List.mem_of_getElem? (i := 64) rfl)
    (List.mem_of_getElem? (i := 55) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c74 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, false), ({(3, 0)}, false), ({(3, 1)}, false)}
private def s74 := c74 :: s73
private theorem d74 : IsLinDerivation F s74 :=
  .res (C := c18) (D := c73) d73
    (List.mem_of_getElem? (i := 55) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c75 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, false), ({(3, 0)}, false)}
private def s75 := c75 :: s74
private theorem d75 : IsLinDerivation F s75 :=
  .res (C := c74) (D := c72) d74
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 2) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c76 : LinClause V := {({(1, 0)}, false), ({(2, 0)}, true), ({(3, 0)}, false), ({(4, 0)}, true)}
private def s76 := c76 :: s75
private theorem d76 : IsLinDerivation F s76 :=
  .res (C := c75) (D := c70) d75
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 5) rfl)
    ⟨{(0, 0)}, by decide, by decide, by decide⟩

private def c77 : LinClause V := {({(1, 0)}, false), ({(3, 0)}, false), ({(4, 0)}, true)}
private def s77 := c77 :: s76
private theorem d77 : IsLinDerivation F s77 :=
  .res (C := c65) (D := c76) d76
    (List.mem_of_getElem? (i := 11) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(2, 0)}, by decide, by decide, by decide⟩

private def c78 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, true), ({(1, 0)}, false), ({(1, 1)}, false), ({(2, 0)}, false)}
private def s78 := c78 :: s77
private theorem d78 : IsLinDerivation F s78 :=
  .res (C := c34) (D := c29) d77
    (List.mem_of_getElem? (i := 43) rfl)
    (List.mem_of_getElem? (i := 48) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c79 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, true), ({(1, 0)}, false), ({(2, 0)}, false)}
private def s79 := c79 :: s78
private theorem d79 : IsLinDerivation F s79 :=
  .res (C := c78) (D := c17) d78
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 61) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c80 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, true), ({(3, 0)}, true), ({(3, 1)}, false), ({(4, 0)}, true)}
private def s80 := c80 :: s79
private theorem d80 : IsLinDerivation F s80 :=
  .res (C := c10) (D := c3) d79
    (List.mem_of_getElem? (i := 69) rfl)
    (List.mem_of_getElem? (i := 76) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c81 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, true), ({(3, 0)}, true), ({(4, 0)}, true)}
private def s81 := c81 :: s80
private theorem d81 : IsLinDerivation F s81 :=
  .res (C := c80) (D := c19) d80
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 61) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c82 : LinClause V := {({(0, 1)}, true), ({(1, 0)}, false), ({(2, 0)}, false), ({(3, 0)}, true), ({(4, 0)}, true)}
private def s82 := c82 :: s81
private theorem d82 : IsLinDerivation F s82 :=
  .res (C := c79) (D := c81) d81
    (List.mem_of_getElem? (i := 2) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(0, 0)}, by decide, by decide, by decide⟩

private def c83 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, false), ({(1, 0)}, false), ({(1, 1)}, true), ({(2, 0)}, false)}
private def s83 := c83 :: s82
private theorem d83 : IsLinDerivation F s83 :=
  .res (C := c5) (D := c12) d82
    (List.mem_of_getElem? (i := 77) rfl)
    (List.mem_of_getElem? (i := 70) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c84 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, false), ({(1, 0)}, false), ({(2, 0)}, false)}
private def s84 := c84 :: s83
private theorem d84 : IsLinDerivation F s84 :=
  .res (C := c33) (D := c83) d83
    (List.mem_of_getElem? (i := 50) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c85 : LinClause V := {({(0, 1)}, false), ({(1, 0)}, false), ({(2, 0)}, false), ({(4, 0)}, true), ({(4, 1)}, false)}
private def s85 := c85 :: s84
private theorem d85 : IsLinDerivation F s85 :=
  .res (C := c84) (D := c9) d84
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 75) rfl)
    ⟨{(0, 0)}, by decide, by decide, by decide⟩

private def c86 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, false), ({(3, 0)}, true), ({(4, 0)}, true), ({(4, 1)}, true)}
private def s86 := c86 :: s85
private theorem d86 : IsLinDerivation F s86 :=
  .res (C := c21) (D := c28) d85
    (List.mem_of_getElem? (i := 64) rfl)
    (List.mem_of_getElem? (i := 57) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c87 : LinClause V := {({(0, 1)}, false), ({(1, 0)}, false), ({(2, 0)}, false), ({(3, 0)}, true), ({(4, 0)}, true), ({(4, 1)}, true)}
private def s87 := c87 :: s86
private theorem d87 : IsLinDerivation F s87 :=
  .res (C := c84) (D := c86) d86
    (List.mem_of_getElem? (i := 2) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(0, 0)}, by decide, by decide, by decide⟩

private def c88 : LinClause V := {({(0, 1)}, false), ({(1, 0)}, false), ({(2, 0)}, false), ({(3, 0)}, true), ({(4, 0)}, true)}
private def s88 := c88 :: s87
private theorem d88 : IsLinDerivation F s88 :=
  .res (C := c85) (D := c87) d87
    (List.mem_of_getElem? (i := 2) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c89 : LinClause V := {({(1, 0)}, false), ({(2, 0)}, false), ({(3, 0)}, true), ({(4, 0)}, true)}
private def s89 := c89 :: s88
private theorem d89 : IsLinDerivation F s89 :=
  .res (C := c88) (D := c82) d88
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 6) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c90 : LinClause V := {({(2, 0)}, true), ({(2, 1)}, true), ({(3, 0)}, true), ({(4, 0)}, true), ({(4, 1)}, false)}
private def s90 := c90 :: s89
private theorem d90 : IsLinDerivation F s90 :=
  .res (C := c10) (D := c24) d89
    (List.mem_of_getElem? (i := 79) rfl)
    (List.mem_of_getElem? (i := 65) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c91 : LinClause V := {({(2, 0)}, true), ({(3, 0)}, true), ({(4, 0)}, true), ({(4, 1)}, false)}
private def s91 := c91 :: s90
private theorem d91 : IsLinDerivation F s91 :=
  .res (C := c25) (D := c90) d90
    (List.mem_of_getElem? (i := 65) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c92 : LinClause V := {({(2, 0)}, true), ({(3, 0)}, true), ({(3, 1)}, false), ({(4, 0)}, true), ({(4, 1)}, true)}
private def s92 := c92 :: s91
private theorem d92 : IsLinDerivation F s92 :=
  .res (C := c32) (D := c22) d91
    (List.mem_of_getElem? (i := 59) rfl)
    (List.mem_of_getElem? (i := 69) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c93 : LinClause V := {({(2, 0)}, true), ({(3, 0)}, true), ({(4, 0)}, true), ({(4, 1)}, true)}
private def s93 := c93 :: s92
private theorem d93 : IsLinDerivation F s93 :=
  .res (C := c92) (D := c28) d92
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 64) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c94 : LinClause V := {({(2, 0)}, true), ({(3, 0)}, true), ({(4, 0)}, true)}
private def s94 := c94 :: s93
private theorem d94 : IsLinDerivation F s94 :=
  .res (C := c91) (D := c93) d93
    (List.mem_of_getElem? (i := 2) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c95 : LinClause V := {({(1, 0)}, false), ({(3, 0)}, true), ({(4, 0)}, true)}
private def s95 := c95 :: s94
private theorem d95 : IsLinDerivation F s95 :=
  .res (C := c89) (D := c94) d94
    (List.mem_of_getElem? (i := 5) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(2, 0)}, by decide, by decide, by decide⟩

private def c96 : LinClause V := {({(1, 0)}, false), ({(4, 0)}, true)}
private def s96 := c96 :: s95
private theorem d96 : IsLinDerivation F s96 :=
  .res (C := c77) (D := c95) d95
    (List.mem_of_getElem? (i := 18) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(3, 0)}, by decide, by decide, by decide⟩

private def c97 : LinClause V := {({(1, 0)}, false)}
private def s97 := c97 :: s96
private theorem d97 : IsLinDerivation F s97 :=
  .res (C := c60) (D := c96) d96
    (List.mem_of_getElem? (i := 36) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(4, 0)}, by decide, by decide, by decide⟩

private def c98 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, true), ({(3, 0)}, false), ({(3, 1)}, false), ({(4, 0)}, false)}
private def s98 := c98 :: s97
private theorem d98 : IsLinDerivation F s98 :=
  .res (C := c6) (D := c23) d97
    (List.mem_of_getElem? (i := 91) rfl)
    (List.mem_of_getElem? (i := 74) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c99 : LinClause V := {({(0, 0)}, false), ({(3, 0)}, false), ({(3, 1)}, false), ({(4, 0)}, false)}
private def s99 := c99 :: s98
private theorem d99 : IsLinDerivation F s99 :=
  .res (C := c8) (D := c98) d98
    (List.mem_of_getElem? (i := 90) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c100 : LinClause V := {({(0, 0)}, false), ({(3, 0)}, false), ({(3, 1)}, true), ({(4, 0)}, false), ({(4, 1)}, false)}
private def s100 := c100 :: s99
private theorem d100 : IsLinDerivation F s100 :=
  .res (C := c36) (D := c16) d99
    (List.mem_of_getElem? (i := 63) rfl)
    (List.mem_of_getElem? (i := 83) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c101 : LinClause V := {({(0, 0)}, false), ({(3, 0)}, false), ({(3, 1)}, true), ({(4, 0)}, false)}
private def s101 := c101 :: s100
private theorem d101 : IsLinDerivation F s101 :=
  .res (C := c100) (D := c27) d100
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 73) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c102 : LinClause V := {({(0, 0)}, false), ({(3, 0)}, false), ({(4, 0)}, false)}
private def s102 := c102 :: s101
private theorem d102 : IsLinDerivation F s102 :=
  .res (C := c99) (D := c101) d101
    (List.mem_of_getElem? (i := 2) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c103 : LinClause V := {({(1, 0)}, true), ({(1, 1)}, false), ({(2, 0)}, true), ({(2, 1)}, true), ({(4, 0)}, true)}
private def s103 := c103 :: s102
private theorem d103 : IsLinDerivation F s103 :=
  .res (C := c20) (D := c22) d102
    (List.mem_of_getElem? (i := 82) rfl)
    (List.mem_of_getElem? (i := 80) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c104 : LinClause V := {({(1, 0)}, true), ({(2, 0)}, true), ({(2, 1)}, true), ({(4, 0)}, true)}
private def s104 := c104 :: s103
private theorem d104 : IsLinDerivation F s104 :=
  .res (C := c103) (D := c40) d103
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 63) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c105 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, false), ({(2, 0)}, false), ({(2, 1)}, true), ({(3, 0)}, false)}
private def s105 := c105 :: s104
private theorem d105 : IsLinDerivation F s105 :=
  .res (C := c8) (D := c39) d104
    (List.mem_of_getElem? (i := 96) rfl)
    (List.mem_of_getElem? (i := 65) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c106 : LinClause V := {({(0, 0)}, false), ({(2, 0)}, false), ({(2, 1)}, true), ({(3, 0)}, false)}
private def s106 := c106 :: s105
private theorem d106 : IsLinDerivation F s106 :=
  .res (C := c105) (D := c29) d105
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 76) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c107 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, true), ({(2, 1)}, true), ({(3, 0)}, false), ({(4, 0)}, true)}
private def s107 := c107 :: s106
private theorem d107 : IsLinDerivation F s107 :=
  .res (C := c106) (D := c104) d106
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 2) rfl)
    ⟨{(2, 0)}, by decide, by decide, by decide⟩

private def c108 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, true), ({(2, 0)}, false), ({(2, 1)}, false), ({(3, 0)}, false)}
private def s108 := c108 :: s107
private theorem d108 : IsLinDerivation F s108 :=
  .res (C := c26) (D := c16) d107
    (List.mem_of_getElem? (i := 81) rfl)
    (List.mem_of_getElem? (i := 91) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c109 : LinClause V := {({(0, 0)}, false), ({(2, 0)}, false), ({(2, 1)}, false), ({(3, 0)}, false)}
private def s109 := c109 :: s108
private theorem d109 : IsLinDerivation F s109 :=
  .res (C := c5) (D := c108) d108
    (List.mem_of_getElem? (i := 103) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c110 : LinClause V := {({(1, 0)}, true), ({(2, 0)}, true), ({(2, 1)}, false), ({(4, 0)}, true), ({(4, 1)}, true)}
private def s110 := c110 :: s109
private theorem d110 : IsLinDerivation F s110 :=
  .res (C := c4) (D := c38) d109
    (List.mem_of_getElem? (i := 105) rfl)
    (List.mem_of_getElem? (i := 71) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c111 : LinClause V := {({(1, 0)}, true), ({(2, 0)}, true), ({(2, 1)}, false), ({(4, 0)}, true)}
private def s111 := c111 :: s110
private theorem d111 : IsLinDerivation F s111 :=
  .res (C := c25) (D := c110) d110
    (List.mem_of_getElem? (i := 85) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c112 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, true), ({(2, 1)}, false), ({(3, 0)}, false), ({(4, 0)}, true)}
private def s112 := c112 :: s111
private theorem d112 : IsLinDerivation F s112 :=
  .res (C := c109) (D := c111) d111
    (List.mem_of_getElem? (i := 2) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(2, 0)}, by decide, by decide, by decide⟩

private def c113 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, true), ({(3, 0)}, false), ({(4, 0)}, true)}
private def s113 := c113 :: s112
private theorem d113 : IsLinDerivation F s113 :=
  .res (C := c112) (D := c107) d112
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 5) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c114 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, true), ({(3, 0)}, false)}
private def s114 := c114 :: s113
private theorem d114 : IsLinDerivation F s114 :=
  .res (C := c102) (D := c113) d113
    (List.mem_of_getElem? (i := 11) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(4, 0)}, by decide, by decide, by decide⟩

private def c115 : LinClause V := {({(1, 0)}, true), ({(1, 1)}, false), ({(2, 0)}, true), ({(3, 0)}, true), ({(3, 1)}, true)}
private def s115 := c115 :: s114
private theorem d115 : IsLinDerivation F s115 :=
  .res (C := c4) (D := c24) d114
    (List.mem_of_getElem? (i := 110) rfl)
    (List.mem_of_getElem? (i := 90) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c116 : LinClause V := {({(1, 0)}, true), ({(1, 1)}, false), ({(2, 0)}, true), ({(3, 0)}, true)}
private def s116 := c116 :: s115
private theorem d116 : IsLinDerivation F s116 :=
  .res (C := c13) (D := c115) d115
    (List.mem_of_getElem? (i := 102) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c117 : LinClause V := {({(1, 0)}, true), ({(1, 1)}, true), ({(2, 0)}, true), ({(3, 0)}, true), ({(3, 1)}, false)}
private def s117 := c117 :: s116
private theorem d117 : IsLinDerivation F s117 :=
  .res (C := c32) (D := c40) d116
    (List.mem_of_getElem? (i := 84) rfl)
    (List.mem_of_getElem? (i := 76) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c118 : LinClause V := {({(1, 0)}, true), ({(1, 1)}, true), ({(2, 0)}, true), ({(3, 0)}, true)}
private def s118 := c118 :: s117
private theorem d118 : IsLinDerivation F s118 :=
  .res (C := c117) (D := c31) d117
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 86) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c119 : LinClause V := {({(1, 0)}, true), ({(2, 0)}, true), ({(3, 0)}, true)}
private def s119 := c119 :: s118
private theorem d119 : IsLinDerivation F s119 :=
  .res (C := c116) (D := c118) d118
    (List.mem_of_getElem? (i := 2) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c120 : LinClause V := {({(1, 0)}, true), ({(3, 0)}, true), ({(3, 1)}, false), ({(4, 0)}, true), ({(4, 1)}, true)}
private def s120 := c120 :: s119
private theorem d120 : IsLinDerivation F s120 :=
  .res (C := c13) (D := c38) d119
    (List.mem_of_getElem? (i := 106) rfl)
    (List.mem_of_getElem? (i := 81) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c121 : LinClause V := {({(1, 0)}, true), ({(3, 0)}, true), ({(4, 0)}, true), ({(4, 1)}, true)}
private def s121 := c121 :: s120
private theorem d121 : IsLinDerivation F s121 :=
  .res (C := c120) (D := c28) d120
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 92) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c122 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, true), ({(1, 0)}, true), ({(3, 0)}, true), ({(4, 1)}, true)}
private def s122 := c122 :: s121
private theorem d122 : IsLinDerivation F s122 :=
  .res (C := c23) (D := c121) d121
    (List.mem_of_getElem? (i := 98) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(4, 0)}, by decide, by decide, by decide⟩

private def c123 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, false), ({(2, 0)}, false), ({(4, 0)}, false), ({(4, 1)}, true)}
private def s123 := c123 :: s122
private theorem d123 : IsLinDerivation F s123 :=
  .res (C := c5) (D := c15) d122
    (List.mem_of_getElem? (i := 117) rfl)
    (List.mem_of_getElem? (i := 107) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c124 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, false), ({(1, 0)}, true), ({(2, 0)}, false), ({(3, 0)}, true), ({(4, 1)}, true)}
private def s124 := c124 :: s123
private theorem d124 : IsLinDerivation F s124 :=
  .res (C := c123) (D := c121) d123
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 2) rfl)
    ⟨{(4, 0)}, by decide, by decide, by decide⟩

private def c125 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, true), ({(2, 0)}, false), ({(3, 0)}, true), ({(4, 1)}, true)}
private def s125 := c125 :: s124
private theorem d125 : IsLinDerivation F s125 :=
  .res (C := c124) (D := c122) d124
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 2) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c126 : LinClause V := {({(1, 0)}, true), ({(3, 0)}, true), ({(3, 1)}, true), ({(4, 0)}, true), ({(4, 1)}, false)}
private def s126 := c126 :: s125
private theorem d126 : IsLinDerivation F s126 :=
  .res (C := c20) (D := c31) d125
    (List.mem_of_getElem? (i := 105) rfl)
    (List.mem_of_getElem? (i := 94) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c127 : LinClause V := {({(1, 0)}, true), ({(3, 0)}, true), ({(4, 0)}, true), ({(4, 1)}, false)}
private def s127 := c127 :: s126
private theorem d127 : IsLinDerivation F s127 :=
  .res (C := c10) (D := c126) d126
    (List.mem_of_getElem? (i := 116) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c128 : LinClause V := {({(0, 0)}, false), ({(0, 1)}, true), ({(2, 0)}, false), ({(4, 0)}, false), ({(4, 1)}, false)}
private def s128 := c128 :: s127
private theorem d128 : IsLinDerivation F s128 :=
  .res (C := c7) (D := c29) d127
    (List.mem_of_getElem? (i := 120) rfl)
    (List.mem_of_getElem? (i := 98) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c129 : LinClause V := {({(0, 0)}, false), ({(2, 0)}, false), ({(4, 0)}, false), ({(4, 1)}, false)}
private def s129 := c129 :: s128
private theorem d129 : IsLinDerivation F s129 :=
  .res (C := c36) (D := c128) d128
    (List.mem_of_getElem? (i := 92) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c130 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, true), ({(2, 0)}, false), ({(3, 0)}, true), ({(4, 1)}, false)}
private def s130 := c130 :: s129
private theorem d130 : IsLinDerivation F s130 :=
  .res (C := c129) (D := c127) d129
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 2) rfl)
    ⟨{(4, 0)}, by decide, by decide, by decide⟩

private def c131 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, true), ({(2, 0)}, false), ({(3, 0)}, true)}
private def s131 := c131 :: s130
private theorem d131 : IsLinDerivation F s131 :=
  .res (C := c130) (D := c125) d130
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 5) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c132 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, true), ({(3, 0)}, true)}
private def s132 := c132 :: s131
private theorem d132 : IsLinDerivation F s132 :=
  .res (C := c131) (D := c119) d131
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 12) rfl)
    ⟨{(2, 0)}, by decide, by decide, by decide⟩

private def c133 : LinClause V := {({(0, 0)}, false), ({(1, 0)}, true)}
private def s133 := c133 :: s132
private theorem d133 : IsLinDerivation F s133 :=
  .res (C := c114) (D := c132) d132
    (List.mem_of_getElem? (i := 18) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(3, 0)}, by decide, by decide, by decide⟩

private def c134 : LinClause V := {({(2, 0)}, false), ({(3, 0)}, false), ({(3, 1)}, false), ({(4, 0)}, false), ({(4, 1)}, true)}
private def s134 := c134 :: s133
private theorem d134 : IsLinDerivation F s134 :=
  .res (C := c26) (D := c15) d133
    (List.mem_of_getElem? (i := 107) rfl)
    (List.mem_of_getElem? (i := 118) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c135 : LinClause V := {({(2, 0)}, false), ({(3, 0)}, false), ({(3, 1)}, false), ({(4, 0)}, false)}
private def s135 := c135 :: s134
private theorem d135 : IsLinDerivation F s135 :=
  .res (C := c6) (D := c134) d134
    (List.mem_of_getElem? (i := 128) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c136 : LinClause V := {({(2, 0)}, false), ({(2, 1)}, false), ({(3, 0)}, false), ({(3, 1)}, true), ({(4, 0)}, false)}
private def s136 := c136 :: s135
private theorem d136 : IsLinDerivation F s136 :=
  .res (C := c7) (D := c27) d135
    (List.mem_of_getElem? (i := 128) rfl)
    (List.mem_of_getElem? (i := 108) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c137 : LinClause V := {({(2, 0)}, false), ({(3, 0)}, false), ({(3, 1)}, true), ({(4, 0)}, false)}
private def s137 := c137 :: s136
private theorem d137 : IsLinDerivation F s137 :=
  .res (C := c136) (D := c39) d136
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 97) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c138 : LinClause V := {({(2, 0)}, false), ({(3, 0)}, false), ({(4, 0)}, false)}
private def s138 := c138 :: s137
private theorem d138 : IsLinDerivation F s138 :=
  .res (C := c135) (D := c137) d137
    (List.mem_of_getElem? (i := 2) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c139 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, false), ({(1, 0)}, true), ({(2, 0)}, true), ({(2, 1)}, true)}
private def s139 := c139 :: s138
private theorem d139 : IsLinDerivation F s139 :=
  .res (C := c37) (D := c40) d138
    (List.mem_of_getElem? (i := 101) rfl)
    (List.mem_of_getElem? (i := 98) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c140 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, false), ({(1, 0)}, true), ({(2, 0)}, true)}
private def s140 := c140 :: s139
private theorem d140 : IsLinDerivation F s140 :=
  .res (C := c30) (D := c139) d139
    (List.mem_of_getElem? (i := 109) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c141 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, true), ({(1, 0)}, true), ({(1, 1)}, false), ({(2, 0)}, true)}
private def s141 := c141 :: s140
private theorem d141 : IsLinDerivation F s141 :=
  .res (C := c4) (D := c11) d140
    (List.mem_of_getElem? (i := 136) rfl)
    (List.mem_of_getElem? (i := 129) rfl)
    ⟨{(2, 1)}, by decide, by decide, by decide⟩

private def c142 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, true), ({(1, 0)}, true), ({(2, 0)}, true)}
private def s142 := c142 :: s141
private theorem d142 : IsLinDerivation F s142 :=
  .res (C := c141) (D := c14) d141
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 127) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c143 : LinClause V := {({(0, 0)}, true), ({(1, 0)}, true), ({(2, 0)}, true)}
private def s143 := c143 :: s142
private theorem d143 : IsLinDerivation F s143 :=
  .res (C := c140) (D := c142) d142
    (List.mem_of_getElem? (i := 2) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c144 : LinClause V := {({(0, 0)}, true), ({(1, 0)}, true), ({(3, 0)}, false), ({(4, 0)}, false)}
private def s144 := c144 :: s143
private theorem d144 : IsLinDerivation F s144 :=
  .res (C := c138) (D := c143) d143
    (List.mem_of_getElem? (i := 5) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(2, 0)}, by decide, by decide, by decide⟩

private def c145 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, true), ({(1, 0)}, true), ({(4, 0)}, true), ({(4, 1)}, false)}
private def s145 := c145 :: s144
private theorem d145 : IsLinDerivation F s145 :=
  .res (C := c20) (D := c14) d144
    (List.mem_of_getElem? (i := 124) rfl)
    (List.mem_of_getElem? (i := 130) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c146 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, true), ({(1, 0)}, true), ({(4, 0)}, true)}
private def s146 := c146 :: s145
private theorem d146 : IsLinDerivation F s146 :=
  .res (C := c145) (D := c3) d145
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 142) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c147 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, false), ({(1, 0)}, true), ({(1, 1)}, true), ({(4, 0)}, true)}
private def s147 := c147 :: s146
private theorem d147 : IsLinDerivation F s147 :=
  .res (C := c9) (D := c38) d146
    (List.mem_of_getElem? (i := 137) rfl)
    (List.mem_of_getElem? (i := 108) rfl)
    ⟨{(4, 1)}, by decide, by decide, by decide⟩

private def c148 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, false), ({(1, 0)}, true), ({(4, 0)}, true)}
private def s148 := c148 :: s147
private theorem d148 : IsLinDerivation F s148 :=
  .res (C := c37) (D := c147) d147
    (List.mem_of_getElem? (i := 110) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c149 : LinClause V := {({(0, 0)}, true), ({(1, 0)}, true), ({(4, 0)}, true)}
private def s149 := c149 :: s148
private theorem d149 : IsLinDerivation F s149 :=
  .res (C := c148) (D := c146) d148
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 2) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c150 : LinClause V := {({(0, 0)}, true), ({(1, 0)}, true), ({(3, 0)}, false)}
private def s150 := c150 :: s149
private theorem d150 : IsLinDerivation F s150 :=
  .res (C := c144) (D := c149) d149
    (List.mem_of_getElem? (i := 5) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(4, 0)}, by decide, by decide, by decide⟩

private def c151 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, true), ({(1, 0)}, true), ({(1, 1)}, false), ({(3, 0)}, true)}
private def s151 := c151 :: s150
private theorem d151 : IsLinDerivation F s151 :=
  .res (C := c13) (D := c19) d150
    (List.mem_of_getElem? (i := 137) rfl)
    (List.mem_of_getElem? (i := 131) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c152 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, true), ({(1, 0)}, true), ({(3, 0)}, true)}
private def s152 := c152 :: s151
private theorem d152 : IsLinDerivation F s152 :=
  .res (C := c151) (D := c14) d151
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 137) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c153 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, false), ({(1, 0)}, true), ({(3, 0)}, true), ({(3, 1)}, true)}
private def s153 := c153 :: s152
private theorem d153 : IsLinDerivation F s153 :=
  .res (C := c37) (D := c31) d152
    (List.mem_of_getElem? (i := 115) rfl)
    (List.mem_of_getElem? (i := 121) rfl)
    ⟨{(1, 1)}, by decide, by decide, by decide⟩

private def c154 : LinClause V := {({(0, 0)}, true), ({(0, 1)}, false), ({(1, 0)}, true), ({(3, 0)}, true)}
private def s154 := c154 :: s153
private theorem d154 : IsLinDerivation F s154 :=
  .res (C := c21) (D := c153) d153
    (List.mem_of_getElem? (i := 132) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(3, 1)}, by decide, by decide, by decide⟩

private def c155 : LinClause V := {({(0, 0)}, true), ({(1, 0)}, true), ({(3, 0)}, true)}
private def s155 := c155 :: s154
private theorem d155 : IsLinDerivation F s155 :=
  .res (C := c154) (D := c152) d154
    (List.mem_of_getElem? (i := 0) rfl)
    (List.mem_of_getElem? (i := 2) rfl)
    ⟨{(0, 1)}, by decide, by decide, by decide⟩

private def c156 : LinClause V := {({(0, 0)}, true), ({(1, 0)}, true)}
private def s156 := c156 :: s155
private theorem d156 : IsLinDerivation F s156 :=
  .res (C := c150) (D := c155) d155
    (List.mem_of_getElem? (i := 5) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(3, 0)}, by decide, by decide, by decide⟩

private def c157 : LinClause V := {({(1, 0)}, true)}
private def s157 := c157 :: s156
private theorem d157 : IsLinDerivation F s157 :=
  .res (C := c133) (D := c156) d156
    (List.mem_of_getElem? (i := 23) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(0, 0)}, by decide, by decide, by decide⟩

private def c158 : LinClause V := ∅
private def s158 := c158 :: s157
private theorem d158 : IsLinDerivation F s158 :=
  .res (C := c97) (D := c157) d157
    (List.mem_of_getElem? (i := 60) rfl)
    (List.mem_of_getElem? (i := 0) rfl)
    ⟨{(1, 0)}, by decide, by decide, by decide⟩

end PEqualNP.Outside.L_pcx_137_aux
open PEqualNP.Outside.L_pcx_137_aux
set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_pcx_137 : ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 2)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP 5 2) π ∧ π.length ≤ 158 := by
  exact ⟨s158, ⟨d158, List.mem_cons_self⟩, by decide⟩
