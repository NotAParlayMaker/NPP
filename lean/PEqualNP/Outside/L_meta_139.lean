import Mathlib
import PEqualNP.Defs

namespace Bull139

/- Each natural number stores a Boolean column of the 32-row truth table, least
   significant bit first. A search state is a pool of available columns. Giving
   both constants for free makes the lower bound valid even for empty gates and
   missing wires. -/

private abbrev T := Nat
private def U : T := 0xffffffff
private def tgt : T := 0xeeeceae8
private def inp : List T := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
private def start : List T := 0 :: U :: inp
private def pairs (x : T) : List T → List T
  | [] => []
  | y::ys => (x &&& y) :: (x ||| y) :: pairs x ys
private def choices : List T → List T
  | [] => []
  | x::xs => (x ^^^ U) :: (pairs x xs ++ choices xs)

private def GateValue (w : List T) (z : T) : Prop :=
  z ∈ w ∨ (∃ x ∈ w, z = x ^^^ U) ∨
  (∃ x y, x ∈ w ∧ y ∈ w ∧ z = x &&& y) ∨
  (∃ x y, x ∈ w ∧ y ∈ w ∧ z = x ||| y)

private theorem GateValue.copy {w : List T} {x : T} (h : x ∈ w) : GateValue w x :=
  Or.inl h
private theorem GateValue.neg {w : List T} {x : T} (h : x ∈ w) : GateValue w (x ^^^ U) :=
  Or.inr (Or.inl ⟨x,h,rfl⟩)
private theorem GateValue.both {w : List T} {x y : T} (h : x ∈ w) (k : y ∈ w) :
    GateValue w (x &&& y) := Or.inr (Or.inr (Or.inl ⟨x,y,h,k,rfl⟩))
private theorem GateValue.either {w : List T} {x y : T} (h : x ∈ w) (k : y ∈ w) :
    GateValue w (x ||| y) := Or.inr (Or.inr (Or.inr ⟨x,y,h,k,rfl⟩))

private theorem pairMem (x : T) {y : T} {w : List T} (h : y ∈ w) :
    (x &&& y) ∈ pairs x w ∧ (x ||| y) ∈ pairs x w := by
  induction w with
  | nil => simp at h
  | cons z zs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp [pairs]
    · obtain ⟨ha,ho⟩ := ih h
      simp [pairs, ha, ho]

private theorem gateMem {w : List T} {z : T} (h : GateValue w z) :
    z ∈ w ∨ z ∈ choices w := by
  induction w with
  | nil => simp [GateValue] at h
  | cons x xs ih =>
    have liftTail {a} (hh : a ∈ xs ∨ a ∈ choices xs) :
        a ∈ x::xs ∨ a ∈ choices (x::xs) := by
      rcases hh with hh | hh <;> simp [choices, hh]
    rcases h with ha | ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, rfl⟩ | ⟨a, b, ha, hb, rfl⟩
    · exact Or.inl ha
    ·
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [choices]
      · exact liftTail (ih (.neg ha))
    ·
      rcases List.mem_cons.mp ha with e | ha <;> rcases List.mem_cons.mp hb with f | hb
      · simp [e, f]
      · subst a; exact Or.inr (by simp [choices, (pairMem x hb).1])
      · subst b; rw [Nat.and_comm]; exact Or.inr (by simp [choices, (pairMem x ha).1])
      · exact liftTail (ih (.both ha hb))
    ·
      rcases List.mem_cons.mp ha with e | ha <;> rcases List.mem_cons.mp hb with f | hb
      · simp [e, f]
      · subst a; exact Or.inr (by simp [choices, (pairMem x hb).2])
      · subst b; rw [Nat.or_comm]; exact Or.inr (by simp [choices, (pairMem x ha).2])
      · exact liftTail (ih (.either ha hb))

-- All shorter executions may spend their remaining gates copying an existing wire.
private def Safe : Nat → List T → Prop
  | 0, w => tgt ∉ w
  | k+1, w => ∀ z, GateValue w z → Safe k (z::w)

private theorem safeSub {k : Nat} {u v : List T} (h : ∀ x ∈ u, x ∈ v)
    (s : Safe k v) : Safe k u := by
  induction k generalizing u v with
  | zero => exact fun hz => s (h _ hz)
  | succ k ih =>
    intro z hz
    have hv : GateValue v z := by
      rcases hz with a | ⟨_,a,rfl⟩ | ⟨_,_,a,b,rfl⟩ | ⟨_,_,a,b,rfl⟩
      · exact .copy (h _ a)
      · exact .neg (h _ a)
      · exact .both (h _ a) (h _ b)
      · exact .either (h _ a) (h _ b)
    apply ih (v := z::v) _ (s z hv)
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simp
    · exact List.mem_cons_of_mem _ (h _ ha)

-- With two gates left, a binary last gate has an old operand, unless it reads
-- the new wire twice. In the latter case it simply copies that wire. For AND an
-- old operand must contain every target 1, and for OR it must avoid every target 0.
private def two (w : List T) : Bool :=
  let cs := choices w
  w.contains tgt || cs.contains tgt || cs.contains (tgt ^^^ U) ||
  w.any fun x =>
    ((x &&& tgt == tgt) && cs.any (fun y => x &&& y == tgt)) ||
    ((x ||| tgt == tgt) && cs.any (fun y => x ||| y == tgt))

private theorem twoSound {w : List T} (h : two w = false) : Safe 2 w := by
  intro y hy z hz
  change tgt ∉ z::y::w
  have fail : ¬ two w = true := by simp [h]
  have direct (g : GateValue w tgt) : False := by
    rcases gateMem g with a | a <;> apply fail <;> simp [two, a]
  have old : tgt ∉ w := fun a => direct (.copy a)
  have hy' : y ≠ tgt := fun e => direct (e ▸ hy)
  have andHit {x} (hx : x ∈ w) (eq : x &&& y = tgt) : False := by
    rcases gateMem hy with yy | yy
    · exact direct (eq ▸ GateValue.both hx yy)
    · have he : x &&& tgt = tgt := by rw [← eq, ← Nat.and_assoc, Nat.and_self]
      have hit : w.any (fun a =>
          ((a &&& tgt == tgt) && (choices w).any (fun b => a &&& b == tgt)) ||
          ((a ||| tgt == tgt) && (choices w).any (fun b => a ||| b == tgt))) = true := by
        apply List.any_eq_true.mpr
        exact ⟨x,hx, Bool.or_eq_true_iff.mpr (.inl (Bool.and_eq_true_iff.mpr
          ⟨by simp [he], List.any_eq_true.mpr ⟨y, yy, by simp [eq]⟩⟩))⟩
      exact fail (by unfold two; simp [hit])
  have orHit {x} (hx : x ∈ w) (eq : x ||| y = tgt) : False := by
    rcases gateMem hy with yy | yy
    · exact direct (eq ▸ GateValue.either hx yy)
    · have he : x ||| tgt = tgt := by rw [← eq, ← Nat.or_assoc, Nat.or_self]
      have hit : w.any (fun a =>
          ((a &&& tgt == tgt) && (choices w).any (fun b => a &&& b == tgt)) ||
          ((a ||| tgt == tgt) && (choices w).any (fun b => a ||| b == tgt))) = true := by
        apply List.any_eq_true.mpr
        exact ⟨x,hx, Bool.or_eq_true_iff.mpr (.inr (Bool.and_eq_true_iff.mpr
          ⟨by simp [he], List.any_eq_true.mpr ⟨y, yy, by simp [eq]⟩⟩))⟩
      exact fail (by unfold two; simp [hit])
  have lastGate {v} (e : GateValue (y::w) v) (eq : v = tgt) : False := by
    rcases e with a | ⟨v,a,rfl⟩ | ⟨v,b,ha,hb,rfl⟩ | ⟨v,b,ha,hb,rfl⟩
    ·
      rw [eq] at a
      rcases List.mem_cons.mp a with a | a
      · exact hy' a.symm
      · exact old a
    ·
      rcases List.mem_cons.mp a with rfl | a
      · rcases gateMem hy with yy | yy
        · exact direct (eq ▸ GateValue.neg yy)
        · have he : tgt ^^^ U = v := by rw [← eq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          exact fail (by simp [two, he, yy])
      · exact direct (eq ▸ GateValue.neg a)
    ·
      rcases List.mem_cons.mp ha with ea | aa <;> rcases List.mem_cons.mp hb with eb | bb
      · exact hy' (by simpa [ea, eb] using eq)
      · exact andHit bb (by simpa [ea, Nat.and_comm] using eq)
      · exact andHit aa (by simpa [eb] using eq)
      · exact direct (eq ▸ GateValue.both aa bb)
    ·
      rcases List.mem_cons.mp ha with ea | aa <;> rcases List.mem_cons.mp hb with eb | bb
      · exact hy' (by simpa [ea, eb] using eq)
      · exact orHit bb (by simpa [ea, Nat.or_comm] using eq)
      · exact orHit aa (by simpa [eb] using eq)
      · exact direct (eq ▸ GateValue.either aa bb)
  intro mem
  rcases List.mem_cons.mp mem with rfl | mem
  · exact lastGate hz rfl
  · rcases List.mem_cons.mp mem with eq | eq
    · exact hy' eq.symm
    · exact old eq

private def search : Nat → List T → Bool
  | 0, w => two w
  | k+1, w => search k w || (choices w).any fun z => !(w.contains z) && search k (z::w)

private theorem searchSound {k : Nat} {w : List T} (h : search k w = false) :
    Safe (k+2) w := by
  induction k generalizing w with
  | zero => exact twoSound h
  | succ k ih =>
    intro z hz
    have h' : search k w = false := (Bool.or_eq_false_iff.mp h).1
    by_cases hm : z ∈ w
    · apply safeSub (v := w) _ (ih h')
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha <;> assumption
    · have hc := (gateMem hz).resolve_left hm
      have nh := (Bool.or_eq_false_iff.mp h).2
      have hf : search k (z::w) = false := by
        cases eq : search k (z::w) with
        | false => rfl
        | true =>
          have hh : (choices w).any (fun v => !(w.contains v) && search k (v::w)) = true :=
            List.any_eq_true.mpr ⟨_, hc, by simp [hm, eq]⟩
          exact Bool.noConfusion (hh.symm.trans nh)
      exact ih hf

-- The kernel checks the finite exclusions individually to bound peak memory.
private theorem initialFour : search 2 start = false := by decide +kernel
private theorem first0 : search 2 (0x0000ffff :: start) = false := by decide +kernel
private theorem first1 : search 2 (0x00ff00ff :: start) = false := by decide +kernel
private theorem first2 : search 2 (0x0f0f0f0f :: start) = false := by decide +kernel
private theorem first3 : search 2 (0x33333333 :: start) = false := by decide +kernel
private theorem first4 : search 2 (0x55555555 :: start) = false := by decide +kernel
private theorem first5 : search 2 (0x88888888 :: start) = false := by decide +kernel
private theorem first6 : search 2 (0xa0a0a0a0 :: start) = false := by decide +kernel
private theorem first7 : search 2 (0xaa00aa00 :: start) = false := by decide +kernel
private theorem first8 : search 2 (0xaaaa0000 :: start) = false := by decide +kernel
private theorem first9 : search 2 (0xc0c0c0c0 :: start) = false := by decide +kernel
private theorem first10 : search 2 (0xcc00cc00 :: start) = false := by decide +kernel
private theorem first11 : search 2 (0xcccc0000 :: start) = false := by decide +kernel
private theorem first12 : search 2 (0xeeeeeeee :: start) = false := by decide +kernel
private theorem first13 : search 2 (0xf000f000 :: start) = false := by decide +kernel
private theorem first14 : search 2 (0xf0f00000 :: start) = false := by decide +kernel
private theorem first15 : search 2 (0xfafafafa :: start) = false := by decide +kernel
private theorem first16 : search 2 (0xfcfcfcfc :: start) = false := by decide +kernel
private theorem first17 : search 2 (0xff000000 :: start) = false := by decide +kernel
private theorem first18 : search 2 (0xffaaffaa :: start) = false := by decide +kernel
private theorem first19 : search 2 (0xffccffcc :: start) = false := by decide +kernel
private theorem first20 : search 2 (0xfff0fff0 :: start) = false := by decide +kernel
private theorem first21 : search 2 (0xffffaaaa :: start) = false := by decide +kernel
private theorem first22 : search 2 (0xffffcccc :: start) = false := by decide +kernel
private theorem first23 : search 2 (0xfffff0f0 :: start) = false := by decide +kernel
private theorem first24 : search 2 (0xffffff00 :: start) = false := by decide +kernel

private def firsts : List T := [0x0000ffff, 0x00ff00ff, 0x0f0f0f0f, 0x33333333, 0x55555555, 0x88888888, 0xa0a0a0a0, 0xaa00aa00, 0xaaaa0000, 0xc0c0c0c0, 0xcc00cc00, 0xcccc0000, 0xeeeeeeee, 0xf000f000, 0xf0f00000, 0xfafafafa, 0xfcfcfcfc, 0xff000000, 0xffaaffaa, 0xffccffcc, 0xfff0fff0, 0xffffaaaa, 0xffffcccc, 0xfffff0f0, 0xffffff00]
private theorem initialSafe : Safe 5 start := by
  intro z hz
  rcases gateMem hz with hm | hc
  · apply safeSub (v := start) _ (searchSound initialFour)
    intro x h
    rcases List.mem_cons.mp h with rfl | h <;> assumption
  · have cover : (choices start).all (fun a => start.contains a || firsts.contains a) = true := by decide
    have hh := List.all_eq_true.mp cover _ hc
    rcases Bool.or_eq_true_iff.mp hh with hm | hm
    · have hz' : z ∈ start := by simpa using hm
      apply safeSub (v := start) _ (searchSound initialFour)
      intro x h
      rcases List.mem_cons.mp h with rfl | h <;> assumption
    · have hmem : z ∈ firsts := by simpa using hm
      simp only [firsts, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact searchSound first0
      · exact searchSound first1
      · exact searchSound first2
      · exact searchSound first3
      · exact searchSound first4
      · exact searchSound first5
      · exact searchSound first6
      · exact searchSound first7
      · exact searchSound first8
      · exact searchSound first9
      · exact searchSound first10
      · exact searchSound first11
      · exact searchSound first12
      · exact searchSound first13
      · exact searchSound first14
      · exact searchSound first15
      · exact searchSound first16
      · exact searchSound first17
      · exact searchSound first18
      · exact searchSound first19
      · exact searchSound first20
      · exact searchSound first21
      · exact searchSound first22
      · exact searchSound first23
      · exact searchSound first24

open PEqualNP.CircuitLowerBounds

private abbrev Row := Fin 32
private def pack (f : Row → Bool) : T := (BitVec.ofBoolListLE (List.ofFn f)).toNat

private theorem bitPack (f : Row → Bool) (i : Nat) :
    (pack f).testBit i = if h : i < 32 then f ⟨i,h⟩ else false := by
  change (BitVec.ofBoolListLE _).getLsbD i = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp_all

private theorem packAnd (a b : Row → Bool) :
    pack (fun j => a j && b j) = pack a &&& pack b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, bitPack]
  split <;> simp

private theorem packOr (a b : Row → Bool) :
    pack (fun j => a j || b j) = pack a ||| pack b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, bitPack]
  split <;> simp

private theorem packNeg (a : Row → Bool) :
    pack (fun j => !(a j)) = pack a ^^^ U := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hu : U.testBit i = decide (i < 32) := Nat.testBit_two_pow_sub_one 32 i
  simp only [Nat.testBit_xor, hu, bitPack]
  split <;> simp_all

-- Read the same physical wire on every input row and pack its column. This
-- connects the list-based circuit evaluator, including its default-false reads,
-- to the finite search above.
private def scalar (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)
private def pushGate (w : List Bool) (g : Gate) := w ++ [scalar w g]
private def col (p : Row → List Bool) (i : Nat) := pack (fun j => (p j).getD i false)

private theorem packZero : pack (fun _ => false) = 0 := by decide
private theorem packOnes : pack (fun _ => true) = U := by decide

private theorem validGate (p : Row → List Bool) (w : List T) (g : Gate)
    (op : g.op = .and ∨ g.op = .or ∨ g.op = .not) (sz : g.inputs.length ≤ 2)
    (cols : ∀ i, col p i ∈ w) (zero : 0 ∈ w) (ones : U ∈ w) :
    GateValue w (pack (fun j => scalar (p j) g)) := by
  obtain ⟨op', ins⟩ := g
  change op' = .and ∨ op' = .or ∨ op' = .not at op
  change ins.length ≤ 2 at sz
  rcases op with rfl | rfl | rfl <;> cases ins with
  | nil =>
    simp only [scalar, GateOp.eval, List.map_nil, List.all_nil, List.any_nil, List.headD, Bool.not_false, packZero, packOnes]
    first | exact .copy zero | exact .copy ones
  | cons i rest =>
    cases rest with
    | nil =>
      first
      | simpa [scalar, GateOp.eval, packNeg, col, Function.comp_def] using GateValue.neg (cols i)
      | simpa [col, scalar, GateOp.eval, Function.comp_def] using GateValue.copy (cols i)
    | cons k rest =>
      cases rest with
      | nil =>
        first
        | simpa [scalar, GateOp.eval, packAnd, col, Function.comp_def] using GateValue.both (cols i) (cols k)
        | simpa [scalar, GateOp.eval, packOr, col, Function.comp_def] using GateValue.either (cols i) (cols k)
        | simpa [scalar, GateOp.eval, packNeg, col, Function.comp_def] using GateValue.neg (cols i)
      | cons l ls => simp at sz

private theorem noCurrent {k : Nat} {w : List T} (h : Safe k w) : tgt ∉ w := by
  induction k generalizing w with
  | zero => exact h
  | succ k ih =>
    intro hm
    exact ih (h tgt (.copy hm)) (by simp)

private theorem excludeRun {k n : Nat} (gs : List Gate) (w : List T) (p : Row → List Bool)
    (s : Safe k w) (len : gs.length ≤ k) (pl : ∀ j, (p j).length = n)
    (cols : ∀ i, col p i ∈ w) (zero : 0 ∈ w) (ones : U ∈ w)
    (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (out : Nat) : col (fun j => gs.foldl pushGate (p j)) out ≠ tgt := by
  induction gs generalizing k n w p with
  | nil =>
    intro eq
    exact noCurrent s (eq ▸ cols out)
  | cons g gs ih =>
    cases k with
    | zero => simp at len
    | succ k =>
      let z := pack (fun j => scalar (p j) g)
      have hg := ok g (by simp)
      have gv : GateValue w z := validGate p w g hg.1 hg.2 cols zero ones
      let p' := fun j => pushGate (p j) g
      apply ih (k := k) (n := n+1) (w := z :: w) (p := p') (s z gv) (by simpa using len)
      · intro j
        simp [p', pushGate, pl]
      · intro i
        by_cases small : i < n
        · have he : col p' i = col p i := by
            apply congrArg pack
            funext j
            simp [p', pushGate, List.getD_eq_getElem?_getD, List.getElem?_append_left (pl j ▸ small : i < (p j).length)]
          exact List.mem_cons_of_mem _ (he ▸ cols i)
        · by_cases last : i = n
          · subst i
            have he : col p' n = z := by
              apply congrArg pack
              funext j
              simp [p', pushGate, List.getD_eq_getElem?_getD, pl j]
            simp [he]
          · have he : col p' i = 0 := by
              change pack _ = pack (fun _ => false)
              apply congrArg pack
              funext j
              have large : (p' j).length ≤ i := by simp [p', pushGate, pl]; omega
              simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none large]
            exact List.mem_cons_of_mem _ (he ▸ zero)
      · exact List.mem_cons_of_mem _ zero
      · exact List.mem_cons_of_mem _ ones
      · intro gg hgg
        exact ok gg (List.mem_cons_of_mem _ hgg)

private def row (r : Row) (i : Fin 5) := r.val.testBit i.val
private def bull (x : Fin 5 → Bool) :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 1 && x 4)

private theorem lower {s : Nat} (h : PEqualNP.MetaComplexity.HasCircuitSize 5 bull s) : 6 ≤ s := by
  obtain ⟨C, fan, size, val⟩ := h
  apply Nat.le_of_not_gt
  intro small
  have cols : ∀ i, col (fun j => List.ofFn (row j)) i ∈ start := by
    intro i
    by_cases hi : i < 5
    · have hfin : ∀ i : Fin 5, col (fun j => List.ofFn (row j)) i.val ∈ start := by decide
      exact hfin ⟨i,hi⟩
    · have he : col (fun j => List.ofFn (row j)) i = 0 := by
        change pack _ = pack (fun _ => false)
        apply congrArg pack
        funext j
        simp [List.getD_eq_getElem?_getD, hi]
      rw [he]
      exact List.Mem.head _
  have bound : C.gates.length ≤ 5 := by change C.gates.length ≤ s at size; omega
  have hn := excludeRun C.gates start (fun j => List.ofFn (row j)) initialSafe bound
    (n := 5) (by simp) cols (by decide) (by decide) (fun g hg => fan g hg) C.output
  apply hn
  change pack (fun r => C.eval (List.ofFn (row r))) = tgt
  simp only [val]
  decide

private def six : Circuit :=
  ⟨[⟨.or, [1,2]⟩, ⟨.or, [5,3]⟩, ⟨.and, [0,6]⟩, ⟨.or, [2,4]⟩,
    ⟨.and, [1,8]⟩, ⟨.or, [7,9]⟩], 10⟩

private theorem upper {s : Nat} (h : 6 ≤ s) : PEqualNP.MetaComplexity.HasCircuitSize 5 bull s := by
  refine ⟨six, ?_, h, ?_⟩
  · intro g hg
    simp only [six, List.mem_cons, List.not_mem_nil, or_false] at hg
    change (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor
    all_goals first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | decide
  · intro x
    have table : ∀ a b c d e : Bool,
        ((a && ((b || c) || d)) || (b && (c || e))) =
        ((a && b) || (a && c) || (b && c) || (a && d) || (b && e)) := by decide
    simpa [six, Circuit.eval, Circuit.wires, GateOp.eval, List.getD, bull,
      Bool.or_assoc, Bool.and_assoc] using table (x 0) (x 1) (x 2) (x 3) (x 4)

end Bull139

theorem PEqualNP.Outside.L_meta_139 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 6 ≤ s := by
  intro s
  exact ⟨Bull139.lower, Bull139.upper⟩
