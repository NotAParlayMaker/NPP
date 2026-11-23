import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_926_aux

open PEqualNP.CircuitLowerBounds

def C0 : Circuit :=
  { gates := [
      { op := GateOp.and, inputs := [0, 1] },
    ], output := 2 }

def C1 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 3] },
    ], output := 4 }

def C2 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 3] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [4, 5] },
    ], output := 6 }

def C3 : Circuit :=
  { gates := [
      { op := GateOp.and, inputs := [0, 1] },
      { op := GateOp.and, inputs := [2, 3] },
      { op := GateOp.or, inputs := [4, 5] },
    ], output := 6 }

def C4 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [4, 3] },
      { op := GateOp.and, inputs := [0, 5] },
    ], output := 6 }

def C5 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 4] },
      { op := GateOp.and, inputs := [1, 3] },
      { op := GateOp.or, inputs := [5, 6] },
    ], output := 7 }

def C6 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [4, 3] },
      { op := GateOp.and, inputs := [0, 5] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 7] },
    ], output := 8 }

def C7 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 5] },
      { op := GateOp.and, inputs := [3, 4] },
      { op := GateOp.or, inputs := [6, 7] },
    ], output := 8 }

def C8 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [5, 3] },
      { op := GateOp.or, inputs := [6, 4] },
      { op := GateOp.and, inputs := [0, 7] },
    ], output := 8 }

def C9 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [5, 3] },
      { op := GateOp.and, inputs := [0, 6] },
      { op := GateOp.and, inputs := [1, 4] },
      { op := GateOp.or, inputs := [7, 8] },
    ], output := 9 }

def C10 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 5] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.and, inputs := [3, 4] },
      { op := GateOp.or, inputs := [6, 7] },
      { op := GateOp.or, inputs := [9, 8] },
    ], output := 10 }

def C11 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [0, 3] },
      { op := GateOp.and, inputs := [1, 5] },
      { op := GateOp.or, inputs := [0, 4] },
      { op := GateOp.and, inputs := [2, 7] },
      { op := GateOp.or, inputs := [6, 8] },
    ], output := 9 }

def C12 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [5, 3] },
      { op := GateOp.or, inputs := [6, 4] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [8, 9] },
    ], output := 10 }

def C13 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [5, 3] },
      { op := GateOp.and, inputs := [0, 6] },
      { op := GateOp.or, inputs := [2, 4] },
      { op := GateOp.and, inputs := [1, 8] },
      { op := GateOp.or, inputs := [7, 9] },
    ], output := 10 }

def C14 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [5, 3] },
      { op := GateOp.and, inputs := [0, 6] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.and, inputs := [3, 4] },
      { op := GateOp.or, inputs := [7, 8] },
      { op := GateOp.or, inputs := [10, 9] },
    ], output := 11 }

def C15 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 5] },
      { op := GateOp.and, inputs := [2, 4] },
      { op := GateOp.or, inputs := [1, 4] },
      { op := GateOp.and, inputs := [3, 8] },
      { op := GateOp.or, inputs := [6, 7] },
      { op := GateOp.or, inputs := [10, 9] },
    ], output := 11 }

def C16 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [5, 3] },
      { op := GateOp.or, inputs := [6, 4] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.and, inputs := [3, 4] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.or, inputs := [11, 10] },
    ], output := 12 }

def C17 : Circuit :=
  { gates := [
      { op := GateOp.and, inputs := [0, 1] },
      { op := GateOp.and, inputs := [2, 3] },
      { op := GateOp.and, inputs := [4, 5] },
      { op := GateOp.or, inputs := [6, 7] },
      { op := GateOp.or, inputs := [9, 8] },
    ], output := 10 }

def C18 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [4, 5] },
      { op := GateOp.or, inputs := [8, 9] },
    ], output := 10 }

def C19 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 6] },
      { op := GateOp.and, inputs := [1, 3] },
      { op := GateOp.and, inputs := [4, 5] },
      { op := GateOp.or, inputs := [7, 8] },
      { op := GateOp.or, inputs := [10, 9] },
    ], output := 11 }

def C20 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 6] },
      { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [3, 8] },
      { op := GateOp.or, inputs := [7, 9] },
    ], output := 10 }

def C21 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.or, inputs := [7, 4] },
      { op := GateOp.or, inputs := [8, 5] },
      { op := GateOp.and, inputs := [0, 9] },
    ], output := 10 }

def C22 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.or, inputs := [7, 4] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.and, inputs := [1, 5] },
      { op := GateOp.or, inputs := [9, 10] },
    ], output := 11 }

def C23 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.and, inputs := [4, 5] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.or, inputs := [11, 10] },
    ], output := 12 }

def C24 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [1, 9] },
      { op := GateOp.or, inputs := [8, 10] },
    ], output := 11 }

def C25 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [1, 4] },
      { op := GateOp.and, inputs := [2, 5] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.or, inputs := [11, 10] },
    ], output := 12 }

def C26 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.or, inputs := [1, 5] },
      { op := GateOp.and, inputs := [4, 9] },
      { op := GateOp.or, inputs := [8, 10] },
    ], output := 11 }

def C27 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 6] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [3, 9] },
      { op := GateOp.or, inputs := [7, 8] },
      { op := GateOp.or, inputs := [11, 10] },
    ], output := 12 }

def C28 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 6] },
      { op := GateOp.and, inputs := [2, 4] },
      { op := GateOp.or, inputs := [1, 5] },
      { op := GateOp.and, inputs := [3, 9] },
      { op := GateOp.or, inputs := [7, 8] },
      { op := GateOp.or, inputs := [11, 10] },
    ], output := 12 }

def C29 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.or, inputs := [7, 4] },
      { op := GateOp.or, inputs := [8, 5] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [10, 11] },
    ], output := 12 }

def C30 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.or, inputs := [7, 4] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [2, 5] },
      { op := GateOp.and, inputs := [1, 10] },
      { op := GateOp.or, inputs := [9, 11] },
    ], output := 12 }

def C31 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.or, inputs := [7, 4] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.and, inputs := [3, 5] },
      { op := GateOp.or, inputs := [9, 10] },
      { op := GateOp.or, inputs := [12, 11] },
    ], output := 13 }

def C32 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.or, inputs := [2, 4] },
      { op := GateOp.and, inputs := [1, 9] },
      { op := GateOp.and, inputs := [2, 5] },
      { op := GateOp.or, inputs := [8, 10] },
      { op := GateOp.or, inputs := [12, 11] },
    ], output := 13 }

def C33 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.or, inputs := [2, 4] },
      { op := GateOp.and, inputs := [1, 9] },
      { op := GateOp.and, inputs := [3, 5] },
      { op := GateOp.or, inputs := [8, 10] },
      { op := GateOp.or, inputs := [12, 11] },
    ], output := 13 }

def C34 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [3, 10] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.or, inputs := [12, 11] },
    ], output := 13 }

def C35 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [3, 5] },
      { op := GateOp.and, inputs := [4, 10] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.or, inputs := [12, 11] },
    ], output := 13 }

def C36 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [2, 5] },
      { op := GateOp.or, inputs := [1, 5] },
      { op := GateOp.and, inputs := [4, 10] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.or, inputs := [12, 11] },
    ], output := 13 }

def C37 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 6] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [3, 9] },
      { op := GateOp.and, inputs := [4, 5] },
      { op := GateOp.or, inputs := [7, 8] },
      { op := GateOp.or, inputs := [12, 10] },
      { op := GateOp.or, inputs := [13, 11] },
    ], output := 14 }

def C38 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 6] },
      { op := GateOp.or, inputs := [1, 5] },
      { op := GateOp.and, inputs := [3, 8] },
      { op := GateOp.or, inputs := [2, 5] },
      { op := GateOp.and, inputs := [4, 10] },
      { op := GateOp.or, inputs := [7, 9] },
      { op := GateOp.or, inputs := [12, 11] },
    ], output := 13 }

def C39 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.or, inputs := [7, 4] },
      { op := GateOp.or, inputs := [8, 5] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.and, inputs := [3, 4] },
      { op := GateOp.or, inputs := [10, 11] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C40 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.or, inputs := [7, 4] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [2, 5] },
      { op := GateOp.and, inputs := [1, 10] },
      { op := GateOp.and, inputs := [3, 4] },
      { op := GateOp.or, inputs := [9, 11] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C41 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.or, inputs := [2, 4] },
      { op := GateOp.and, inputs := [1, 9] },
      { op := GateOp.or, inputs := [3, 4] },
      { op := GateOp.and, inputs := [5, 11] },
      { op := GateOp.or, inputs := [8, 10] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C42 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [3, 4] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.or, inputs := [11, 10] },
    ], output := 12 }

def C43 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [10, 11] },
    ], output := 12 }

def C44 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.and, inputs := [1, 4] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [9, 10] },
      { op := GateOp.or, inputs := [12, 11] },
    ], output := 13 }

def C45 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.and, inputs := [4, 10] },
      { op := GateOp.or, inputs := [9, 11] },
    ], output := 12 }

def C46 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.and, inputs := [3, 4] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.or, inputs := [12, 10] },
      { op := GateOp.or, inputs := [13, 11] },
    ], output := 14 }

def C47 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [0, 3] },
      { op := GateOp.and, inputs := [1, 7] },
      { op := GateOp.or, inputs := [0, 4] },
      { op := GateOp.and, inputs := [2, 9] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [8, 10] },
      { op := GateOp.or, inputs := [12, 11] },
    ], output := 13 }

def C48 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [1, 3] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.and, inputs := [4, 10] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.or, inputs := [12, 11] },
    ], output := 13 }

def C49 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.or, inputs := [9, 5] },
      { op := GateOp.or, inputs := [10, 6] },
      { op := GateOp.and, inputs := [0, 11] },
    ], output := 12 }

def C50 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.or, inputs := [9, 5] },
      { op := GateOp.and, inputs := [0, 10] },
      { op := GateOp.and, inputs := [1, 6] },
      { op := GateOp.or, inputs := [11, 12] },
    ], output := 13 }

def C51 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [10, 11] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C52 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.and, inputs := [1, 11] },
      { op := GateOp.or, inputs := [10, 12] },
    ], output := 13 }

def C53 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.and, inputs := [1, 5] },
      { op := GateOp.and, inputs := [2, 6] },
      { op := GateOp.or, inputs := [10, 11] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C54 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.or, inputs := [1, 6] },
      { op := GateOp.and, inputs := [5, 11] },
      { op := GateOp.or, inputs := [10, 12] },
    ], output := 13 }

def C55 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [2, 4] },
      { op := GateOp.and, inputs := [1, 10] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [9, 11] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C56 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.and, inputs := [3, 4] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [9, 10] },
      { op := GateOp.or, inputs := [13, 11] },
      { op := GateOp.or, inputs := [14, 12] },
    ], output := 15 }

def C57 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.and, inputs := [4, 11] },
      { op := GateOp.or, inputs := [9, 10] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C58 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [1, 10] },
      { op := GateOp.and, inputs := [2, 6] },
      { op := GateOp.or, inputs := [9, 11] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C59 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [0, 4] },
      { op := GateOp.and, inputs := [1, 7] },
      { op := GateOp.or, inputs := [0, 5] },
      { op := GateOp.and, inputs := [2, 9] },
      { op := GateOp.or, inputs := [0, 6] },
      { op := GateOp.and, inputs := [3, 11] },
      { op := GateOp.or, inputs := [8, 10] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C60 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.and, inputs := [2, 5] },
      { op := GateOp.or, inputs := [1, 6] },
      { op := GateOp.and, inputs := [4, 11] },
      { op := GateOp.or, inputs := [9, 10] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C61 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [1, 5] },
      { op := GateOp.or, inputs := [10, 6] },
      { op := GateOp.and, inputs := [4, 11] },
      { op := GateOp.or, inputs := [9, 12] },
    ], output := 13 }

def C62 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.and, inputs := [1, 4] },
      { op := GateOp.or, inputs := [4, 6] },
      { op := GateOp.and, inputs := [5, 11] },
      { op := GateOp.or, inputs := [9, 10] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C63 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.and, inputs := [4, 10] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [9, 11] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C64 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [3, 10] },
      { op := GateOp.and, inputs := [4, 6] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.or, inputs := [13, 11] },
      { op := GateOp.or, inputs := [14, 12] },
    ], output := 15 }

def C65 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [2, 4] },
      { op := GateOp.or, inputs := [1, 4] },
      { op := GateOp.and, inputs := [3, 10] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.or, inputs := [13, 11] },
      { op := GateOp.or, inputs := [14, 12] },
    ], output := 15 }

def C66 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.or, inputs := [1, 5] },
      { op := GateOp.and, inputs := [3, 9] },
      { op := GateOp.or, inputs := [2, 6] },
      { op := GateOp.and, inputs := [4, 11] },
      { op := GateOp.or, inputs := [8, 10] },
      { op := GateOp.or, inputs := [13, 12] },
    ], output := 14 }

def C67 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.or, inputs := [9, 5] },
      { op := GateOp.or, inputs := [10, 6] },
      { op := GateOp.and, inputs := [0, 11] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [12, 13] },
    ], output := 14 }

def C68 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.or, inputs := [9, 5] },
      { op := GateOp.and, inputs := [0, 10] },
      { op := GateOp.or, inputs := [2, 6] },
      { op := GateOp.and, inputs := [1, 12] },
      { op := GateOp.or, inputs := [11, 13] },
    ], output := 14 }

def C69 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.or, inputs := [9, 5] },
      { op := GateOp.and, inputs := [0, 10] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.and, inputs := [3, 6] },
      { op := GateOp.or, inputs := [11, 12] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C70 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.or, inputs := [2, 5] },
      { op := GateOp.or, inputs := [11, 6] },
      { op := GateOp.and, inputs := [1, 12] },
      { op := GateOp.or, inputs := [10, 13] },
    ], output := 14 }

def C71 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.or, inputs := [2, 5] },
      { op := GateOp.and, inputs := [1, 11] },
      { op := GateOp.and, inputs := [2, 6] },
      { op := GateOp.or, inputs := [10, 12] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C72 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.or, inputs := [2, 5] },
      { op := GateOp.and, inputs := [1, 11] },
      { op := GateOp.and, inputs := [3, 6] },
      { op := GateOp.or, inputs := [10, 12] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C73 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.or, inputs := [2, 5] },
      { op := GateOp.and, inputs := [1, 11] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [10, 12] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C74 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.and, inputs := [3, 12] },
      { op := GateOp.or, inputs := [10, 11] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C75 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [3, 6] },
      { op := GateOp.and, inputs := [5, 12] },
      { op := GateOp.or, inputs := [10, 11] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C76 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.and, inputs := [1, 11] },
      { op := GateOp.and, inputs := [5, 6] },
      { op := GateOp.or, inputs := [10, 12] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C77 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.or, inputs := [8, 4] },
      { op := GateOp.and, inputs := [0, 9] },
      { op := GateOp.and, inputs := [2, 6] },
      { op := GateOp.or, inputs := [1, 6] },
      { op := GateOp.and, inputs := [5, 12] },
      { op := GateOp.or, inputs := [10, 11] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C78 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [0, 2] },
      { op := GateOp.or, inputs := [7, 4] },
      { op := GateOp.and, inputs := [1, 8] },
      { op := GateOp.or, inputs := [0, 5] },
      { op := GateOp.and, inputs := [2, 10] },
      { op := GateOp.or, inputs := [0, 6] },
      { op := GateOp.and, inputs := [3, 12] },
      { op := GateOp.or, inputs := [9, 11] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C79 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [2, 4] },
      { op := GateOp.and, inputs := [1, 10] },
      { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.and, inputs := [3, 12] },
      { op := GateOp.or, inputs := [9, 11] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C80 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [2, 4] },
      { op := GateOp.and, inputs := [1, 10] },
      { op := GateOp.or, inputs := [3, 6] },
      { op := GateOp.and, inputs := [5, 12] },
      { op := GateOp.or, inputs := [9, 11] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C81 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [3, 5] },
      { op := GateOp.or, inputs := [11, 6] },
      { op := GateOp.and, inputs := [4, 12] },
      { op := GateOp.or, inputs := [9, 10] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C82 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [4, 5] },
      { op := GateOp.and, inputs := [1, 10] },
      { op := GateOp.or, inputs := [2, 4] },
      { op := GateOp.and, inputs := [6, 12] },
      { op := GateOp.or, inputs := [9, 11] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C83 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.and, inputs := [2, 5] },
      { op := GateOp.or, inputs := [1, 5] },
      { op := GateOp.or, inputs := [11, 6] },
      { op := GateOp.and, inputs := [4, 12] },
      { op := GateOp.or, inputs := [9, 10] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

def C84 : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [7, 3] },
      { op := GateOp.and, inputs := [0, 8] },
      { op := GateOp.or, inputs := [1, 6] },
      { op := GateOp.and, inputs := [4, 10] },
      { op := GateOp.or, inputs := [2, 6] },
      { op := GateOp.and, inputs := [5, 12] },
      { op := GateOp.or, inputs := [9, 11] },
      { op := GateOp.or, inputs := [14, 13] },
    ], output := 15 }

end PEqualNP.Outside.L_meta_926_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_926 :
    (PEqualNP.MetaComplexity.HasCircuitSize 2 (fun x : Fin 2 → Bool => (x 0 && x 1)) 1) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2)) 2) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 3 (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) 3) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) 4) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) 5) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6)) 6) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 7) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6)) 8) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 5 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 4 && x 6)) 9) ∧ (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 5 && x 6)) 9) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C0,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C0],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C1,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C1],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C2,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C2],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C3,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C3],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C4,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C4],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C5,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C5],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C6,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C6],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C7,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C7],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C8,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C8],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C9,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C9],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C10,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C10],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C11,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C11],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C12,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C12],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C13,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C13],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C14,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C14],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C15,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C15],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C16,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C16],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C17,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C17],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C18,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C18],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C19,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C19],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C20,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C20],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C21,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C21],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C22,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C22],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C23,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C23],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C24,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C24],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C25,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C25],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C26,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C26],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C27,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C27],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C28,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C28],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C29,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C29],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C30,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C30],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C31,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C31],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C32,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C32],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C33,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C33],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C34,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C34],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C35,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C35],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C36,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C36],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C37,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C37],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C38,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C38],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C39,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C39],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C40,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C40],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C41,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C41],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C42,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C42],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C43,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C43],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C44,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C44],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C45,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C45],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C46,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C46],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C47,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C47],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C48,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C48],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C49,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C49],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C50,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C50],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C51,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C51],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C52,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C52],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C53,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C53],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C54,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C54],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C55,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C55],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C56,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C56],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C57,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C57],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C58,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C58],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C59,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C59],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C60,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C60],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C61,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C61],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C62,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C62],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C63,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C63],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C64,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C64],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C65,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C65],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C66,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C66],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C67,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C67],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C68,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C68],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C69,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C69],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C70,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C70],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C71,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C71],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C72,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C72],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C73,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C73],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C74,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C74],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C75,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C75],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C76,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C76],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C77,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C77],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C78,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C78],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C79,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C79],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C80,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C80],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C81,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C81],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C82,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C82],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C83,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C83],
      by decide,
      by decide⟩
  · exact ⟨PEqualNP.Outside.L_meta_926_aux.C84,
      by simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_926_aux.C84],
      by decide,
      by decide⟩
