import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_18043

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



-- A universal vertex cannot belong to an independent triple.
-- A fixed matching shares the common-neighbour wires between obstructions.
def witness : Circuit :=
  ⟨[⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [4, 8]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [10, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [27, 28]⟩, ⟨.and, [29, 47]⟩, ⟨.and, [30, 48]⟩, ⟨.or, [0, 49]⟩, ⟨.and, [31, 32]⟩, ⟨.and, [33, 51]⟩, ⟨.or, [1, 52]⟩, ⟨.and, [34, 40]⟩, ⟨.and, [43, 54]⟩, ⟨.and, [46, 55]⟩, ⟨.or, [12, 56]⟩, ⟨.and, [35, 41]⟩, ⟨.and, [44, 58]⟩, ⟨.or, [13, 59]⟩, ⟨.and, [36, 42]⟩, ⟨.and, [45, 61]⟩, ⟨.or, [14, 62]⟩, ⟨.and, [37, 38]⟩, ⟨.and, [39, 64]⟩, ⟨.or, [5, 65]⟩, ⟨.and, [50, 53]⟩, ⟨.and, [57, 67]⟩, ⟨.and, [60, 68]⟩, ⟨.and, [63, 69]⟩, ⟨.and, [66, 70]⟩, ⟨.and, [9, 16]⟩, ⟨.and, [10, 17]⟩, ⟨.and, [11, 18]⟩, ⟨.and, [12, 17]⟩, ⟨.and, [13, 18]⟩, ⟨.and, [14, 18]⟩, ⟨.or, [72, 73]⟩, ⟨.or, [74, 78]⟩, ⟨.and, [15, 79]⟩, ⟨.or, [75, 76]⟩, ⟨.and, [16, 81]⟩, ⟨.and, [17, 77]⟩, ⟨.and, [19, 23]⟩, ⟨.and, [20, 24]⟩, ⟨.or, [84, 85]⟩, ⟨.and, [71, 86]⟩, ⟨.or, [80, 82]⟩, ⟨.or, [83, 88]⟩, ⟨.or, [87, 89]⟩, ⟨.and, [0, 90]⟩, ⟨.and, [3, 19]⟩, ⟨.and, [4, 19]⟩, ⟨.and, [7, 20]⟩, ⟨.and, [8, 20]⟩, ⟨.and, [14, 22]⟩, ⟨.or, [92, 94]⟩, ⟨.or, [96, 97]⟩, ⟨.and, [21, 98]⟩, ⟨.or, [93, 95]⟩, ⟨.and, [22, 100]⟩, ⟨.and, [15, 25]⟩, ⟨.and, [16, 26]⟩, ⟨.or, [102, 103]⟩, ⟨.and, [71, 104]⟩, ⟨.or, [99, 101]⟩, ⟨.or, [105, 106]⟩, ⟨.and, [9, 107]⟩, ⟨.and, [1, 25]⟩, ⟨.and, [2, 26]⟩, ⟨.and, [5, 25]⟩, ⟨.and, [6, 26]⟩, ⟨.or, [109, 110]⟩, ⟨.and, [23, 113]⟩, ⟨.or, [111, 112]⟩, ⟨.and, [24, 115]⟩, ⟨.and, [17, 21]⟩, ⟨.and, [18, 22]⟩, ⟨.or, [117, 118]⟩, ⟨.and, [71, 119]⟩, ⟨.or, [114, 116]⟩, ⟨.or, [120, 121]⟩, ⟨.and, [14, 122]⟩, ⟨.or, [91, 108]⟩, ⟨.or, [123, 124]⟩, ⟨.not, [125]⟩], 126⟩

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

end PEqualNP.Outside.L_meta_18043

open PEqualNP.Outside.L_meta_18043 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_18043 : PEqualNP.MetaComplexity.HasCircuitSize 15 (fun x : Fin 15 → Bool => !((x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 9 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 6 && x 8 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13) || (x 0 && x 3 && x 4 && x 5 && x 7 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 7 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 3 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 3 && x 6 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 1 && x 2 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 2 && x 4 && x 7 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 13) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 7 && x 8 && x 10 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 7 && x 10) || (x 0 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 7 && x 10 && x 11 && x 13) || (x 9 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 5 && x 6 && x 9) || (x 2 && x 3 && x 4 && x 5 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 5 && x 7 && x 8 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 12 && x 13) || (x 0 && x 2 && x 4 && x 6 && x 7 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 7 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 7 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 8 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12) || (x 0 && x 3 && x 4 && x 7 && x 8 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12 && x 14) || (x 2 && x 3 && x 4 && x 5 && x 6 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 6 && x 7 && x 12) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 8 && x 10 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 5 && x 6 && x 8 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 6 && x 7 && x 8 && x 9 && x 10 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 13) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 6 && x 8 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 9 && x 10 && x 11 && x 12 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 7 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 8 && x 11) || (x 1 && x 2 && x 3 && x 9 && x 10 && x 12) || (x 0 && x 1 && x 4 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 9 && x 10 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 6 && x 8 && x 10 && x 11 && x 12) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13) || (x 0 && x 1 && x 2 && x 5 && x 7 && x 9 && x 10 && x 11 && x 13 && x 14) || (x 5 && x 7 && x 8 && x 10 && x 11 && x 14) || (x 0 && x 1 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 13 && x 14) || (x 2 && x 3 && x 4 && x 12 && x 13 && x 14) || (x 6 && x 7 && x 8 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 6 && x 7 && x 8 && x 10 && x 11 && x 13 && x 14) || (x 0 && x 2 && x 3 && x 5 && x 7 && x 10 && x 11 && x 12 && x 13 && x 14) || (x 5 && x 6 && x 8 && x 9 && x 11 && x 13) || (x 0 && x 2 && x 3 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 14) || (x 0 && x 1 && x 2 && x 3 && x 4 && x 5 && x 6 && x 10 && x 13 && x 14) || (x 1 && x 2 && x 3 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12 && x 13) || (x 1 && x 3 && x 4 && x 10 && x 11 && x 14) || (x 0 && x 2 && x 3 && x 6 && x 8 && x 9 && x 10 && x 11 && x 12 && x 13) || (x 1 && x 2 && x 4 && x 9 && x 11 && x 13) || (x 5 && x 6 && x 7 && x 9 && x 10 && x 12) || (x 0 && x 3 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 11 && x 12) || (x 1 && x 2 && x 3 && x 5 && x 6 && x 8 && x 9 && x 12 && x 13 && x 14) || (x 0 && x 1 && x 4 && x 5 && x 6 && x 7 && x 8 && x 9 && x 12 && x 14) || (x 0 && x 3 && x 4 && x 5 && x 8 && x 9 && x 11 && x 12 && x 13 && x 14) || (x 0 && x 2 && x 4 && x 5 && x 6 && x 9 && x 10 && x 12 && x 13 && x 14) || (x 1 && x 2 && x 4 && x 5 && x 6 && x 7 && x 9 && x 12 && x 13 && x 14))) 140 := by
  change PEqualNP.MetaComplexity.HasCircuitSize 15 target 140
  refine ⟨witness, witnessFit, by decide, ?_⟩
  intro x
  have h := packedCorrect (inputRow x)
  rw [wordsMatch, expectedCorrect, rowCorrect] at h
  exact h.symm
