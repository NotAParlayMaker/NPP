import PEqualNP.Defs

open PEqualNP.ProofComplexity

namespace PEqualNP.Outside.L_pcx_125

def l1 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  (∅ : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l2 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l3 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((2 : Fin 4), (2 : Fin 3))), false), ((((3 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l4 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l5 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((1 : Fin 4), (2 : Fin 3))), false), ((((3 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l6 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l7 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((0 : Fin 4), (2 : Fin 3))), false), ((((3 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l8 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l9 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l10 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l11 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l12 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l13 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l14 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l15 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((1 : Fin 4), (2 : Fin 3))), false), ((((2 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l16 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l17 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((0 : Fin 4), (2 : Fin 3))), false), ((((2 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l18 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l19 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l20 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l21 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l22 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l23 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((0 : Fin 4), (1 : Fin 3))), false), ((((1 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l24 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l25 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l26 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((0 : Fin 4), (0 : Fin 3))), false), ((((1 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l27 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l28 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l29 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((0 : Fin 4), (2 : Fin 3))), false), ((((1 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l30 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l31 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l32 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((0 : Fin 4), (0 : Fin 3))), false), ((((3 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l33 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l34 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l35 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((0 : Fin 4), (1 : Fin 3))), false), ((((2 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l36 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l37 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l38 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l39 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((0 : Fin 4), (0 : Fin 3))), false), ((((2 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l40 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l41 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((0 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l42 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((0 : Fin 4), (1 : Fin 3))), false), ((((3 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l43 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((0 : Fin 4), (0 : Fin 3))), true), ((((0 : Fin 4), (1 : Fin 3))), true), ((((0 : Fin 4), (2 : Fin 3))), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l44 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l45 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l46 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((1 : Fin 4), (0 : Fin 3))), false), ((((3 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l47 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l48 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l49 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((1 : Fin 4), (1 : Fin 3))), false), ((((2 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l50 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l51 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((2 : Fin 4), (0 : Fin 3))), false), ((((3 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l52 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l53 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l54 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l55 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((2 : Fin 4), (1 : Fin 3))), false), ((((3 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l56 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l57 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((1 : Fin 4), (0 : Fin 3))), false), ((((2 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l58 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((2 : Fin 4), (0 : Fin 3))), true), ((((2 : Fin 4), (1 : Fin 3))), true), ((((2 : Fin 4), (2 : Fin 3))), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l59 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l60 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  ({((({((1 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), false)), ((({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), true)), ((({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), true))} : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3))

def l61 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((1 : Fin 4), (1 : Fin 3))), false), ((((3 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l62 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((3 : Fin 4), (0 : Fin 3))), true), ((((3 : Fin 4), (1 : Fin 3))), true), ((((3 : Fin 4), (2 : Fin 3))), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

def l63 : PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3) :=
  linOfClause ({((((1 : Fin 4), (0 : Fin 3))), true), ((((1 : Fin 4), (1 : Fin 3))), true), ((((1 : Fin 4), (2 : Fin 3))), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3))

end PEqualNP.Outside.L_pcx_125

theorem PEqualNP.Outside.L_pcx_125 :
    ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 4 × Fin 3)),
      PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 63 := by
  refine ⟨[PEqualNP.Outside.L_pcx_125.l1, PEqualNP.Outside.L_pcx_125.l2, PEqualNP.Outside.L_pcx_125.l3, PEqualNP.Outside.L_pcx_125.l4, PEqualNP.Outside.L_pcx_125.l5, PEqualNP.Outside.L_pcx_125.l6, PEqualNP.Outside.L_pcx_125.l7, PEqualNP.Outside.L_pcx_125.l8, PEqualNP.Outside.L_pcx_125.l9, PEqualNP.Outside.L_pcx_125.l10, PEqualNP.Outside.L_pcx_125.l11, PEqualNP.Outside.L_pcx_125.l12, PEqualNP.Outside.L_pcx_125.l13, PEqualNP.Outside.L_pcx_125.l14, PEqualNP.Outside.L_pcx_125.l15, PEqualNP.Outside.L_pcx_125.l16, PEqualNP.Outside.L_pcx_125.l17, PEqualNP.Outside.L_pcx_125.l18, PEqualNP.Outside.L_pcx_125.l19, PEqualNP.Outside.L_pcx_125.l20, PEqualNP.Outside.L_pcx_125.l21, PEqualNP.Outside.L_pcx_125.l22, PEqualNP.Outside.L_pcx_125.l23, PEqualNP.Outside.L_pcx_125.l24, PEqualNP.Outside.L_pcx_125.l25, PEqualNP.Outside.L_pcx_125.l26, PEqualNP.Outside.L_pcx_125.l27, PEqualNP.Outside.L_pcx_125.l28, PEqualNP.Outside.L_pcx_125.l29, PEqualNP.Outside.L_pcx_125.l30, PEqualNP.Outside.L_pcx_125.l31, PEqualNP.Outside.L_pcx_125.l32, PEqualNP.Outside.L_pcx_125.l33, PEqualNP.Outside.L_pcx_125.l34, PEqualNP.Outside.L_pcx_125.l35, PEqualNP.Outside.L_pcx_125.l36, PEqualNP.Outside.L_pcx_125.l37, PEqualNP.Outside.L_pcx_125.l38, PEqualNP.Outside.L_pcx_125.l39, PEqualNP.Outside.L_pcx_125.l40, PEqualNP.Outside.L_pcx_125.l41, PEqualNP.Outside.L_pcx_125.l42, PEqualNP.Outside.L_pcx_125.l43, PEqualNP.Outside.L_pcx_125.l44, PEqualNP.Outside.L_pcx_125.l45, PEqualNP.Outside.L_pcx_125.l46, PEqualNP.Outside.L_pcx_125.l47, PEqualNP.Outside.L_pcx_125.l48, PEqualNP.Outside.L_pcx_125.l49, PEqualNP.Outside.L_pcx_125.l50, PEqualNP.Outside.L_pcx_125.l51, PEqualNP.Outside.L_pcx_125.l52, PEqualNP.Outside.L_pcx_125.l53, PEqualNP.Outside.L_pcx_125.l54, PEqualNP.Outside.L_pcx_125.l55, PEqualNP.Outside.L_pcx_125.l56, PEqualNP.Outside.L_pcx_125.l57, PEqualNP.Outside.L_pcx_125.l58, PEqualNP.Outside.L_pcx_125.l59, PEqualNP.Outside.L_pcx_125.l60, PEqualNP.Outside.L_pcx_125.l61, PEqualNP.Outside.L_pcx_125.l62, PEqualNP.Outside.L_pcx_125.l63], ⟨?_, by decide⟩, by decide⟩
  exact (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l2) (D := PEqualNP.Outside.L_pcx_125.l13) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l3) (D := PEqualNP.Outside.L_pcx_125.l4) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l3) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l5) (D := PEqualNP.Outside.L_pcx_125.l6) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l5) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l7) (D := PEqualNP.Outside.L_pcx_125.l8) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l7) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l9) (D := PEqualNP.Outside.L_pcx_125.l11) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l26) (D := PEqualNP.Outside.L_pcx_125.l10) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l48) (D := PEqualNP.Outside.L_pcx_125.l38) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l12) (D := PEqualNP.Outside.L_pcx_125.l21) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l34) (D := PEqualNP.Outside.L_pcx_125.l56) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l14) (D := PEqualNP.Outside.L_pcx_125.l27) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l15) (D := PEqualNP.Outside.L_pcx_125.l16) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l15) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l17) (D := PEqualNP.Outside.L_pcx_125.l18) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l17) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l19) (D := PEqualNP.Outside.L_pcx_125.l24) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l32) (D := PEqualNP.Outside.L_pcx_125.l20) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l46) (D := PEqualNP.Outside.L_pcx_125.l21) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l22) (D := PEqualNP.Outside.L_pcx_125.l43) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l23) (D := PEqualNP.Outside.L_pcx_125.l63) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l23) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l25) (D := PEqualNP.Outside.L_pcx_125.l40) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l26) (D := PEqualNP.Outside.L_pcx_125.l59) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l26) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l28) (D := PEqualNP.Outside.L_pcx_125.l44) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l29) (D := PEqualNP.Outside.L_pcx_125.l30) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l29) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l31) (D := PEqualNP.Outside.L_pcx_125.l36) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l32) (D := PEqualNP.Outside.L_pcx_125.l33) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l32) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l34) (D := PEqualNP.Outside.L_pcx_125.l50) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l35) (D := PEqualNP.Outside.L_pcx_125.l43) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l35) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l37) (D := PEqualNP.Outside.L_pcx_125.l40) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l54) (D := PEqualNP.Outside.L_pcx_125.l38) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l39) (D := PEqualNP.Outside.L_pcx_125.l58) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l39) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l41) (D := PEqualNP.Outside.L_pcx_125.l43) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l42) (D := PEqualNP.Outside.L_pcx_125.l62) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l42) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l43) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l45) (D := PEqualNP.Outside.L_pcx_125.l52) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l46) (D := PEqualNP.Outside.L_pcx_125.l47) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l46) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l48) (D := PEqualNP.Outside.L_pcx_125.l50) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l49) (D := PEqualNP.Outside.L_pcx_125.l63) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l49) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l51) (D := PEqualNP.Outside.L_pcx_125.l58) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l51) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l53) (D := PEqualNP.Outside.L_pcx_125.l59) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l54) (D := PEqualNP.Outside.L_pcx_125.l56) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l55) (D := PEqualNP.Outside.L_pcx_125.l62) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l55) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l57) (D := PEqualNP.Outside.L_pcx_125.l58) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l57) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l58) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l60) (D := PEqualNP.Outside.L_pcx_125.l63) (PEqualNP.ProofComplexity.IsLinDerivation.res (C := PEqualNP.Outside.L_pcx_125.l61) (D := PEqualNP.Outside.L_pcx_125.l62) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l61) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l62) (PEqualNP.ProofComplexity.IsLinDerivation.ax (C := PEqualNP.Outside.L_pcx_125.l63) PEqualNP.ProofComplexity.IsLinDerivation.nil
      ⟨({((((1 : Fin 4), (0 : Fin 3))), true), ((((1 : Fin 4), (1 : Fin 3))), true), ((((1 : Fin 4), (2 : Fin 3))), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inl ⟨(1 : Fin 4), rfl⟩, rfl⟩⟩)
      ⟨({((((3 : Fin 4), (0 : Fin 3))), true), ((((3 : Fin 4), (1 : Fin 3))), true), ((((3 : Fin 4), (2 : Fin 3))), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inl ⟨(3 : Fin 4), rfl⟩, rfl⟩⟩)
      ⟨({((((1 : Fin 4), (1 : Fin 3))), false), ((((3 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(1 : Fin 4), (3 : Fin 4), (1 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((3 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((2 : Fin 4), (0 : Fin 3))), true), ((((2 : Fin 4), (1 : Fin 3))), true), ((((2 : Fin 4), (2 : Fin 3))), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inl ⟨(2 : Fin 4), rfl⟩, rfl⟩⟩)
      ⟨({((((1 : Fin 4), (0 : Fin 3))), false), ((((2 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(1 : Fin 4), (2 : Fin 4), (0 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((2 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((2 : Fin 4), (1 : Fin 3))), false), ((((3 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(2 : Fin 4), (3 : Fin 4), (1 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((3 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((2 : Fin 4), (0 : Fin 3))), false), ((((3 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(2 : Fin 4), (3 : Fin 4), (0 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((2 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((1 : Fin 4), (1 : Fin 3))), false), ((((2 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(1 : Fin 4), (2 : Fin 4), (1 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((1 : Fin 4), (0 : Fin 3))), false), ((((3 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(1 : Fin 4), (3 : Fin 4), (0 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((0 : Fin 4), (0 : Fin 3))), true), ((((0 : Fin 4), (1 : Fin 3))), true), ((((0 : Fin 4), (2 : Fin 3))), true)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inl ⟨(0 : Fin 4), rfl⟩, rfl⟩⟩)
      ⟨({((((0 : Fin 4), (1 : Fin 3))), false), ((((3 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(0 : Fin 4), (3 : Fin 4), (1 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((3 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((0 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((0 : Fin 4), (0 : Fin 3))), false), ((((2 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(0 : Fin 4), (2 : Fin 4), (0 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((2 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((0 : Fin 4), (1 : Fin 3))), false), ((((2 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(0 : Fin 4), (2 : Fin 4), (1 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((0 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((0 : Fin 4), (0 : Fin 3))), false), ((((3 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(0 : Fin 4), (3 : Fin 4), (0 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((0 : Fin 4), (2 : Fin 3))), false), ((((1 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(0 : Fin 4), (1 : Fin 4), (2 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((0 : Fin 4), (0 : Fin 3))), false), ((((1 : Fin 4), (0 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(0 : Fin 4), (1 : Fin 4), (0 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((0 : Fin 4), (1 : Fin 3))), false), ((((1 : Fin 4), (1 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(0 : Fin 4), (1 : Fin 4), (1 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((0 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((3 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((0 : Fin 4), (2 : Fin 3))), false), ((((2 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(0 : Fin 4), (2 : Fin 4), (2 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((1 : Fin 4), (2 : Fin 3))), false), ((((2 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(1 : Fin 4), (2 : Fin 4), (2 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((2 : Fin 4), (1 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((0 : Fin 4), (0 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((0 : Fin 4), (2 : Fin 3))), false), ((((3 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(0 : Fin 4), (3 : Fin 4), (2 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((0 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((1 : Fin 4), (2 : Fin 3))), false), ((((3 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(1 : Fin 4), (3 : Fin 4), (2 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((1 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      ⟨({((((2 : Fin 4), (2 : Fin 3))), false), ((((3 : Fin 4), (2 : Fin 3))), false)} : PEqualNP.ProofComplexity.Clause (Fin 4 × Fin 3)), ⟨Or.inr ⟨(2 : Fin 4), (3 : Fin 4), (2 : Fin 3), by decide, rfl⟩, rfl⟩⟩)
      (by decide) (by decide)
      ⟨({((2 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
      (by decide) (by decide)
      ⟨({((3 : Fin 4), (2 : Fin 3))} : Finset (Fin 4 × Fin 3)), by decide, by decide, by decide⟩)
