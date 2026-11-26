import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_18042

abbrev Word := BitVec 32768

def inputAt (r : Fin 32768) (i : Fin 15) : Bool := r.val.testBit i.val


def joinHalves {n : Nat} (hi lo : BitVec (2^n)) : BitVec (2^(n+1)) :=
  (hi ++ lo).cast (by rw [Nat.pow_succ, Nat.mul_two])

theorem joinBit {n : Nat} (hi lo : BitVec (2^n)) (r : Nat) :
    (joinHalves hi lo).getLsbD r =
      if r < 2^n then lo.getLsbD r else hi.getLsbD (r - 2^n) := by
  simp only [joinHalves, BitVec.getLsbD_cast, BitVec.getLsbD_append]

def binaryColumn : (n i : Nat) → BitVec (2^n)
  | 0, _ => 0
  | n+1, i =>
      if i < n then
        let old := binaryColumn n i
        joinHalves old old
      else
        joinHalves (BitVec.allOnes (2^n)) 0

theorem binaryColumnBit {n i r : Nat} (hi : i < n) (hr : r < 2^n) :
    (binaryColumn n i).getLsbD r = r.testBit i := by
  induction n generalizing i r with
  | zero => omega
  | succ n ih =>
    have half : r - 2^n < 2^n := by rw [Nat.pow_succ, Nat.mul_two] at hr; omega
    by_cases lower : i < n
    · rw [binaryColumn, if_pos lower, joinBit]
      by_cases head : r < 2^n
      · exact (if_pos head).trans (ih lower head)
      · rw [if_neg head, ih lower half]
        have split : 2^n+(r-2^n)=r := by omega
        exact ((congrArg (fun t : Nat => t.testBit i) split).symm.trans
          (Nat.testBit_two_pow_add_gt lower (r-2^n))).symm
    · have eq : i=n := by omega
      subst i
      rw [binaryColumn, if_neg (by omega), joinBit]
      by_cases head : r < 2^n
      · rw [if_pos head, Nat.testBit_lt_two_pow head]
        simp [BitVec.getLsbD]
      · rw [if_neg head, BitVec.getLsbD_allOnes,
          Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (Nat.le_of_not_gt head) hr]
        exact decide_eq_true half

def source (i : Fin 15) : Word := binaryColumn 15 i.val

theorem sourceBit (r : Fin 32768) (i : Fin 15) :
    (source i).getLsbD r.val = inputAt r i :=
  binaryColumnBit i.isLt r.isLt


def inputRow (x : Fin 15 → Bool) : Fin 32768 :=
  let bits := BitVec.ofBoolListLE (List.ofFn x)
  ⟨bits.toNat, by simpa using bits.isLt⟩

theorem rowCorrect (x : Fin 15 → Bool) : inputAt (inputRow x) = x := by
  funext i
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    i.isLt, dif_pos, Option.getD_some]

def observe (r : Fin 32768) (w : Word) : Bool := w.getLsbD r.val

def allBits (xs : List Word) : Word := xs.foldr (· &&& ·) (BitVec.allOnes 32768)
def anyBits (xs : List Word) : Word := xs.foldr (· ||| ·) 0

theorem allBitsCorrect (r : Fin 32768) (xs : List Word) :
    observe r (allBits xs) = (xs.map (observe r)).all id := by
  induction xs with
  | nil =>
    change (BitVec.allOnes 32768).getLsbD r.val = true
    rw [BitVec.getLsbD_allOnes]
    exact decide_eq_true r.isLt
  | cons x xs ih =>
    change observe r (x &&& allBits xs) = (observe r x && (xs.map (observe r)).all id)
    exact (BitVec.getLsbD_and).trans (congrArg (fun b => observe r x && b) ih)

theorem anyBitsCorrect (r : Fin 32768) (xs : List Word) :
    observe r (anyBits xs) = (xs.map (observe r)).any id := by
  induction xs with
  | nil => simp [anyBits, observe]
  | cons x xs ih =>
    change observe r (x ||| anyBits xs) = (observe r x || (xs.map (observe r)).any id)
    exact (BitVec.getLsbD_or).trans (congrArg (fun b => observe r x || b) ih)

theorem observedRead (r : Fin 32768) (xs : List Word) (i : ℕ) :
    observe r (xs.getD i 0) = (xs.map (observe r)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : xs[i]? <;> simp [observe, h]

def packedGate (op : GateOp) (xs : List Word) : Word :=
  match op with
  | .and => allBits xs
  | .or => anyBits xs
  | .not => ~~~(xs.headD 0)
  | _ => 0

theorem gateMatches (r : Fin 32768) (g : Gate) (ws : List Word)
    (ops : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    observe r (packedGate g.op (g.inputs.map (fun i => ws.getD i 0))) =
      g.op.eval (g.inputs.map (fun i => (ws.map (observe r)).getD i false)) := by
  have reads : (g.inputs.map (fun i => ws.getD i 0)).map (observe r) =
      g.inputs.map (fun i => (ws.map (observe r)).getD i false) := by
    rw [List.map_map]
    congr 1
    funext i
    exact observedRead r ws i
  rcases ops with h | h | h
  · rw [h]
    change observe r (allBits _) = _
    rw [allBitsCorrect, reads]
    rfl
  · rw [h]
    change observe r (anyBits _) = _
    rw [anyBitsCorrect, reads]
    rfl
  · rw [h]
    change observe r (~~~((g.inputs.map fun i => ws.getD i 0).headD 0)) = !_
    rw [← reads]
    simp only [List.headD_eq_getD, ← observedRead]
    simp [observe, BitVec.getLsbD_not, r.isLt]

def packedRun : List Gate → List Word → List Word
  | [], ws => ws
  | g :: gs, ws => packedRun gs (ws ++ [packedGate g.op (g.inputs.map (fun i => ws.getD i 0))])

theorem runMatches (r : Fin 32768) (gs : List Gate) (ws : List Word)
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    (packedRun gs ws).map (observe r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) (ws.map (observe r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [packedRun, List.foldl_cons]
    rw [ih _ (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))]
    simp only [List.map_append, List.map_singleton]
    rw [gateMatches r g ws (ops g (by simp))]



-- A fixed matching shares the common-neighbour wires with all six universal-vertex tests.
def witness : Circuit :=
  ⟨[⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [4, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [10, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [27, 9]⟩, ⟨.and, [15, 17]⟩, ⟨.and, [29, 10]⟩, ⟨.and, [15, 18]⟩, ⟨.and, [31, 11]⟩, ⟨.and, [16, 17]⟩, ⟨.and, [33, 12]⟩, ⟨.and, [16, 18]⟩, ⟨.and, [35, 13]⟩, ⟨.and, [17, 18]⟩, ⟨.and, [37, 14]⟩, ⟨.and, [19, 21]⟩, ⟨.and, [39, 3]⟩, ⟨.and, [19, 22]⟩, ⟨.and, [41, 4]⟩, ⟨.and, [23, 25]⟩, ⟨.and, [43, 1]⟩, ⟨.and, [23, 26]⟩, ⟨.and, [45, 2]⟩, ⟨.and, [20, 21]⟩, ⟨.and, [47, 7]⟩, ⟨.and, [20, 22]⟩, ⟨.and, [49, 8]⟩, ⟨.and, [24, 25]⟩, ⟨.and, [51, 5]⟩, ⟨.and, [24, 26]⟩, ⟨.and, [53, 6]⟩, ⟨.and, [21, 22]⟩, ⟨.and, [55, 14]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [57, 14]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [59, 14]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [61, 13]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [63, 12]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [65, 14]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [67, 13]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [69, 12]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [71, 11]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [73, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [75, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [77, 14]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [79, 13]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [81, 12]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [83, 11]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [85, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [87, 9]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [89, 8]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [91, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [93, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [95, 5]⟩, ⟨.and, [58, 60]⟩, ⟨.and, [97, 62]⟩, ⟨.and, [98, 64]⟩, ⟨.and, [66, 68]⟩, ⟨.and, [100, 70]⟩, ⟨.and, [72, 84]⟩, ⟨.and, [102, 90]⟩, ⟨.and, [103, 96]⟩, ⟨.and, [74, 86]⟩, ⟨.and, [105, 92]⟩, ⟨.and, [76, 88]⟩, ⟨.and, [107, 94]⟩, ⟨.and, [78, 80]⟩, ⟨.and, [109, 82]⟩, ⟨.and, [19, 23]⟩, ⟨.and, [72, 74]⟩, ⟨.and, [112, 76]⟩, ⟨.and, [113, 99]⟩, ⟨.and, [114, 101]⟩, ⟨.and, [111, 115]⟩, ⟨.and, [20, 24]⟩, ⟨.and, [84, 86]⟩, ⟨.and, [118, 88]⟩, ⟨.and, [119, 99]⟩, ⟨.and, [120, 110]⟩, ⟨.and, [117, 121]⟩, ⟨.and, [15, 25]⟩, ⟨.and, [58, 90]⟩, ⟨.and, [124, 92]⟩, ⟨.and, [125, 94]⟩, ⟨.and, [126, 101]⟩, ⟨.and, [127, 110]⟩, ⟨.and, [123, 128]⟩, ⟨.and, [16, 26]⟩, ⟨.and, [60, 66]⟩, ⟨.and, [131, 78]⟩, ⟨.and, [132, 104]⟩, ⟨.and, [133, 106]⟩, ⟨.and, [130, 134]⟩, ⟨.and, [17, 21]⟩, ⟨.and, [62, 68]⟩, ⟨.and, [137, 80]⟩, ⟨.and, [138, 104]⟩, ⟨.and, [139, 108]⟩, ⟨.and, [136, 140]⟩, ⟨.and, [18, 22]⟩, ⟨.and, [64, 70]⟩, ⟨.and, [143, 82]⟩, ⟨.and, [144, 96]⟩, ⟨.and, [145, 106]⟩, ⟨.and, [146, 108]⟩, ⟨.and, [142, 147]⟩, ⟨.or, [28, 30]⟩, ⟨.or, [149, 32]⟩, ⟨.or, [150, 34]⟩, ⟨.or, [151, 36]⟩, ⟨.or, [152, 38]⟩, ⟨.or, [153, 116]⟩, ⟨.or, [154, 122]⟩, ⟨.and, [0, 155]⟩, ⟨.or, [40, 42]⟩, ⟨.or, [157, 48]⟩, ⟨.or, [158, 50]⟩, ⟨.or, [159, 56]⟩, ⟨.or, [160, 129]⟩, ⟨.or, [161, 135]⟩, ⟨.and, [9, 162]⟩, ⟨.or, [44, 46]⟩, ⟨.or, [164, 52]⟩, ⟨.or, [165, 54]⟩, ⟨.or, [166, 141]⟩, ⟨.or, [167, 148]⟩, ⟨.and, [14, 168]⟩, ⟨.or, [156, 163]⟩, ⟨.or, [170, 169]⟩, ⟨.not, [171]⟩], 172⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

theorem witnessOps : ∀ g ∈ witness.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  intro g hg
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (witnessFit g hg).1


def packedWitness : Word := (packedRun witness.gates (List.ofFn source)).getD witness.output 0

theorem packedCorrect (r : Fin 32768) :
    observe r packedWitness = witness.eval (List.ofFn (inputAt r)) := by
  have inputs : (List.ofFn source).map (observe r) = List.ofFn (inputAt r) := by
    rw [List.map_ofFn]
    exact congrArg (fun f : Fin 15 → Bool => List.ofFn f) (funext (fun i => sourceBit r i))
  unfold packedWitness Circuit.eval Circuit.wires
  rw [observedRead, runMatches r witness.gates _ witnessOps, inputs]

def expected : Word := ~~~((source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 7 &&& source 9 &&& source 13 &&& source 14) ||| (source 0 &&& source 2 &&& source 4 &&& source 6 &&& source 8 &&& source 13) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 9 &&& source 11 &&& source 12 &&& source 13) ||| (source 0 &&& source 3 &&& source 4 &&& source 5 &&& source 7 &&& source 9 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 6 &&& source 7 &&& source 9 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 13) ||| (source 0 &&& source 3 &&& source 4 &&& source 6 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 5 &&& source 6 &&& source 9 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 4 &&& source 5 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 13) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 13) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 4 &&& source 6 &&& source 8 &&& source 10 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 2 &&& source 3 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 1 &&& source 2 &&& source 3 &&& source 5 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 13) ||| (source 0 &&& source 1 &&& source 3 &&& source 6 &&& source 7 &&& source 10 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 4 &&& source 5 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12) ||| (source 0 &&& source 1 &&& source 2 &&& source 5 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 2 &&& source 4 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 5 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 2 &&& source 4 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 13) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 14) ||| (source 0 &&& source 2 &&& source 3 &&& source 5 &&& source 6 &&& source 9 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 6 &&& source 7 &&& source 9 &&& source 11 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 5 &&& source 7 &&& source 10) ||| (source 0 &&& source 3 &&& source 4 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 6 &&& source 7 &&& source 10 &&& source 11 &&& source 13) ||| (source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 5 &&& source 6 &&& source 9) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 3 &&& source 5 &&& source 7 &&& source 8 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 8 &&& source 9 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 13) ||| (source 0 &&& source 1 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 12 &&& source 13) ||| (source 0 &&& source 2 &&& source 4 &&& source 6 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 4 &&& source 5 &&& source 7 &&& source 8 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 3 &&& source 4 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 2 &&& source 4 &&& source 5 &&& source 8 &&& source 10 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12) ||| (source 0 &&& source 3 &&& source 4 &&& source 7 &&& source 8 &&& source 14) ||| (source 1 &&& source 2 &&& source 3 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 8 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 12) ||| (source 0 &&& source 2 &&& source 3 &&& source 6 &&& source 7 &&& source 12) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 8 &&& source 10 &&& source 12 &&& source 13) ||| (source 1 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 8 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 3 &&& source 4 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 14) ||| (source 0 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 13) ||| (source 0 &&& source 2 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 11 &&& source 12) ||| (source 0 &&& source 2 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 10 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 4 &&& source 5 &&& source 6 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 7 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 2 &&& source 3 &&& source 5 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 14) ||| (source 0 &&& source 1 &&& source 4 &&& source 5 &&& source 8 &&& source 11) ||| (source 1 &&& source 2 &&& source 3 &&& source 9 &&& source 10 &&& source 12) ||| (source 0 &&& source 1 &&& source 4 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 6 &&& source 8 &&& source 10 &&& source 11 &&& source 12) ||| (source 0 &&& source 2 &&& source 3 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 11 &&& source 13) ||| (source 0 &&& source 1 &&& source 2 &&& source 5 &&& source 7 &&& source 9 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 5 &&& source 7 &&& source 8 &&& source 10 &&& source 11 &&& source 14) ||| (source 0 &&& source 1 &&& source 3 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 13 &&& source 14) ||| (source 2 &&& source 3 &&& source 4 &&& source 12 &&& source 13 &&& source 14) ||| (source 6 &&& source 7 &&& source 8 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 4 &&& source 6 &&& source 7 &&& source 8 &&& source 10 &&& source 11 &&& source 13 &&& source 14) ||| (source 0 &&& source 2 &&& source 3 &&& source 5 &&& source 7 &&& source 10 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 5 &&& source 6 &&& source 8 &&& source 9 &&& source 11 &&& source 13) ||| (source 0 &&& source 2 &&& source 3 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 14) ||| (source 0 &&& source 1 &&& source 2 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 10 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 3 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 3 &&& source 4 &&& source 10 &&& source 11 &&& source 14) ||| (source 0 &&& source 2 &&& source 3 &&& source 6 &&& source 8 &&& source 9 &&& source 10 &&& source 11 &&& source 12 &&& source 13) ||| (source 1 &&& source 2 &&& source 4 &&& source 9 &&& source 11 &&& source 13) ||| (source 5 &&& source 6 &&& source 7 &&& source 9 &&& source 10 &&& source 12) ||| (source 0 &&& source 3 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 11 &&& source 12) ||| (source 1 &&& source 2 &&& source 3 &&& source 5 &&& source 6 &&& source 8 &&& source 9 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 1 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 8 &&& source 9 &&& source 12 &&& source 14) ||| (source 0 &&& source 3 &&& source 4 &&& source 5 &&& source 8 &&& source 9 &&& source 11 &&& source 12 &&& source 13 &&& source 14) ||| (source 0 &&& source 2 &&& source 4 &&& source 5 &&& source 6 &&& source 9 &&& source 10 &&& source 12 &&& source 13 &&& source 14) ||| (source 1 &&& source 2 &&& source 4 &&& source 5 &&& source 6 &&& source 7 &&& source 9 &&& source 12 &&& source 13 &&& source 14))
def target (x : Fin 15 → Bool) : Bool := !((x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14))

set_option maxRecDepth 16000 in
theorem expectedCorrect (r : Fin 32768) :
    observe r expected = target (inputAt r) := by
  simp only [expected, target, observe, BitVec.getLsbD_not, r.isLt, decide_true,
    Bool.true_and, BitVec.getLsbD_and, BitVec.getLsbD_or, sourceBit]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 60000000 in
theorem wordsMatch : packedWitness = expected := by
  decide +kernel

end PEqualNP.Outside.L_meta_18042

open PEqualNP.Outside.L_meta_18042 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_18042 : PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => !((x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14))) 170 := by
  change PEqualNP.MetaComplexity.HasCircuitSize 15 target 170
  refine ⟨witness, witnessFit, by decide, ?_⟩
  intro x
  have h := packedCorrect (inputRow x)
  rw [wordsMatch, expectedCorrect, rowCorrect] at h
  exact h.symm
