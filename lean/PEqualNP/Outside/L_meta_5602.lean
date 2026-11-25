import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5602

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def graph (u v : Fin 4) : Bool := (55 : ℕ).testBit (4 * u.val + v.val)

def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 9]⟩,
    ⟨.and, [0, 6]⟩, ⟨.or, [10, 11]⟩], 12⟩

theorem upper : RepSizeAtMost graph 5 := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · unfold Monotone2
    simp [circuit]
  · unfold Represents
    decide +kernel

-- The seven selected promise rows already rule out size four.
abbrev Word := Nat

def pairs : List (Fin 4 × Fin 4) := [(0,0), (0,1), (0,2), (0,3), (1,0), (1,2), (2,0)]

def pairAt (i : Fin 7) : Fin 4 × Fin 4 := pairs.getD i.val (0,0)

def inputs : List Word := [15, 48, 64, 0, 81, 2, 36, 8]
def available : List Word := inputs ++ [127]
def target : Word := 23

def bit (i : Fin 7) (w : Word) : Bool := w.testBit i.val

theorem inputRows : ∀ i : Fin 7,
    inputs.map (bit i) = oneEach (pairAt i).1 (pairAt i).2 := by decide +kernel

theorem outputRows : ∀ i : Fin 7,
    bit i target = graph (pairAt i).1 (pairAt i).2 := by decide +kernel

def wordGate (w : List Word) (g : Gate) : Word :=
  match g.op, g.inputs with
  | .and, [] => 127
  | .and, [a] | .or, [a] => w.getD a 0
  | .and, [a,b] => w.getD a 0 &&& w.getD b 0
  | .or, [a,b] => w.getD a 0 ||| w.getD b 0
  | _, _ => 0

def wordStep (w : List Word) (g : Gate) : List Word := w ++ [wordGate w g]

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

theorem bitRead (i : Fin 7) (w : List Word) (j : ℕ) :
    bit i (w.getD j 0) = (w.map (bit i)).getD j false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? <;> simp [bit]

theorem wordSound (i : Fin 7) (w : List Word) (g : Gate)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    bit i (wordGate w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨opName, ins⟩ := g
  change opName = .and ∨ opName = .or at op
  change ins.length ≤ 2 at arity
  have hone : bit i (127 : Word) = true := by
    change (2 ^ 7 - 1 : ℕ).testBit i.val = true
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact i.isLt
  have hand (a b : Word) : bit i (a &&& b) = (bit i a && bit i b) := Nat.testBit_and _ _ _
  have hor (a b : Word) : bit i (a ||| b) = (bit i a || bit i b) := Nat.testBit_or _ _ _
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
  · rcases op with rfl | rfl
    · exact hone
    · simp [wordGate,GateOp.eval,bit]
  · rcases op with rfl | rfl <;>
      simp only [wordGate,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.any_cons,
        List.all_nil,List.any_nil,id_eq,Bool.and_true,Bool.or_false,bitRead]
  · rcases op with rfl | rfl <;>
      simp only [wordGate,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.any_cons,
        List.all_nil,List.any_nil,id_eq,Bool.and_true,Bool.or_false,hand,hor,bitRead]
  · simp at arity

theorem simulate (i : Fin 7) (gs : List Gate) (w : List Word)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    (gs.foldl wordStep w).map (bit i) = gs.foldl boolStep (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hx := hg g (by simp)
    rw [List.foldl_cons,List.foldl_cons,ih _ (fun h hh => hg h (List.mem_cons_of_mem _ hh))]
    simp [wordStep,boolStep,wordSound i w g hx.1 hx.2]

def candidates (s : List Word) : List Word :=
  s.flatMap fun a => s.flatMap fun b => [a &&& b, a ||| b]

def wordBits (s : List Word) : Nat := s.foldr (fun w acc => (1 <<< w) ||| acc) 0

theorem wordBitsMem (s : List Word) (t : Word) : (wordBits s).testBit t = true ↔ t ∈ s := by
  induction s with
  | nil => simp [wordBits]
  | cons w s ih =>
    change ((1 <<< w) ||| wordBits s).testBit t = true ↔ t ∈ w :: s
    rw [Nat.testBit_or,Nat.one_shiftLeft,Nat.testBit_two_pow,Bool.or_eq_true,
      decide_eq_true_eq,ih,List.mem_cons]
    exact or_congr eq_comm Iff.rfl

def fresh (s : List Word) : List Word :=
  let produced := wordBits (candidates s)
  let present := wordBits s
  (List.range 128).filter fun t => produced.testBit t && !present.testBit t

theorem freshMem (s : List Word) (t : Word) : t ∈ fresh s ↔
    t < 128 ∧ t ∈ candidates s ∧ t ∉ s := by
  cases h : (wordBits s).testBit t with
  | false =>
    have hn : t ∉ s := fun ht => by
      have ht' := (wordBitsMem s t).mpr ht
      rw [h] at ht'
      cases ht'
    simp [fresh, h, hn, wordBitsMem]
  | true =>
    have hm := (wordBitsMem s t).mp h
    simp [fresh, h, hm]

theorem candidateBound {s : List Word} (h : ∀ t ∈ s, t < 128)
    {t : Word} (ht : t ∈ candidates s) : t < 128 := by
  simp only [candidates,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at ht
  obtain ⟨a,ha,b,hb,he⟩ := ht
  rcases he with rfl | rfl
  · exact Nat.and_lt_two_pow (n := 7) _ (h b hb)
  · exact Nat.or_lt_two_pow (n := 7) (h a ha) (h b hb)

def combines (p : Word) (s : List Word) : Bool :=
  s.any fun a =>
    (((a &&& p) == p) && s.any (fun b => (a &&& b) == p)) ||
    (((a ||| p) == p) && s.any (fun b => (a ||| b) == p))

theorem combinesTrue {p : Word} {s : List Word} (h : p ∈ candidates s) : combines p s = true := by
  simp only [candidates,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at h
  obtain ⟨a,ha,b,hb,h⟩ := h
  refine List.any_eq_true.mpr ⟨a,ha,Bool.or_eq_true_iff.mpr ?_⟩
  rcases h with rfl | rfl
  · left
    exact Bool.and_eq_true_iff.mpr
      ⟨by rw [← Nat.and_assoc,Nat.and_self]; simp,
        List.any_eq_true.mpr ⟨b,hb,by simp⟩⟩
  · right
    exact Bool.and_eq_true_iff.mpr
      ⟨by rw [← Nat.or_assoc,Nat.or_self]; simp,
        List.any_eq_true.mpr ⟨b,hb,by simp⟩⟩

def search (p : Word) : ℕ → List Word → Bool
  | 0, s => s.contains p
  | k+1, s => search p k s ||
      (if k = 0 then combines p s else (fresh s).any (fun t => search p k (t::s)))

theorem branchFalse (p t : Word) (s : List Word) (k : ℕ) (ht : t ∈ fresh s)
    (no : search p (k+1) s = false) : search p k (t::s) = false := by
  have h := Bool.or_eq_false_iff.mp no
  cases k with
  | zero =>
    have hs : s.contains p = false := h.1
    have hns : p ∉ s := by simpa using hs
    have hc : combines p s = false := by simpa only [ite_true] using h.2
    have hm : t ∈ candidates s := ((freshMem s t).mp ht).2.1
    have hne : p ≠ t := by
      intro he
      subst p
      have hcomb := combinesTrue hm
      rw [hc] at hcomb
      cases hcomb
    simp [search, hne, hns]
  | succ k =>
    have hc : (fresh s).any (fun v => search p (k+1) (v::s)) = false := by
      simpa only [Nat.succ_ne_zero, ite_false] using h.2
    exact Bool.eq_false_iff.mpr (List.any_eq_false.mp hc t ht)

theorem readAvailable {a s : List Word} (h : ∀ t ∈ a, t ∈ s) (zero : (0 : Word) ∈ s)
    (j : ℕ) : a.getD j 0 ∈ s := by
  by_cases hj : j < a.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem (h := hj))
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
    exact zero

theorem gateAvailable {a s : List Word} (h : ∀ t ∈ a, t ∈ s) (hcap : ∀ t ∈ s, t < 128)
    (zero : (0 : Word) ∈ s) (ones : (127 : Word) ∈ s) (g : Gate)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    wordGate a g ∈ s ∨ wordGate a g ∈ fresh s := by
  obtain ⟨name, ins⟩ := g
  change name = .and ∨ name = .or at op
  change ins.length ≤ 2 at arity
  have add (w : Word) (hw : w ∈ candidates s) : w ∈ s ∨ w ∈ fresh s := by
    by_cases hmem : w ∈ s
    · exact Or.inl hmem
    · exact Or.inr ((freshMem s w).mpr ⟨candidateBound hcap hw,hw,hmem⟩)
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k,ks⟩⟩⟩
  · rcases op with rfl | rfl
    · exact Or.inl ones
    · exact Or.inl zero
  · rcases op with rfl | rfl <;> exact Or.inl (readAvailable h zero i)
  · have hi := readAvailable h zero i
    have hj := readAvailable h zero j
    rcases op with rfl | rfl
    · apply add
      exact List.mem_flatMap.mpr ⟨_,hi,List.mem_flatMap.mpr ⟨_,hj,by simp [wordGate]⟩⟩
    · apply add
      exact List.mem_flatMap.mpr ⟨_,hi,List.mem_flatMap.mpr ⟨_,hj,by simp [wordGate]⟩⟩
  · simp at arity

theorem boundedRead (w : List Word) (h : ∀ t ∈ w, t < 2^7) (j : ℕ) :
    w.getD j 0 < 2^7 := by
  by_cases hj : j < w.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact h _ (List.getElem_mem (h := hj))
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hj)]
    decide

theorem boundedGate (w : List Word) (h : ∀ t ∈ w, t < 2^7) (g : Gate)
    (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    wordGate w g < 2^7 := by
  obtain ⟨name,ins⟩ := g
  change name = .and ∨ name = .or at op
  change ins.length ≤ 2 at arity
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k,ks⟩⟩⟩
  · rcases op with rfl | rfl <;> simp [wordGate]
  · rcases op with rfl | rfl <;> exact boundedRead w h i
  · rcases op with rfl | rfl
    · exact Nat.and_lt_two_pow _ (boundedRead w h j)
    · exact Nat.or_lt_two_pow (boundedRead w h i) (boundedRead w h j)
  · simp at arity

theorem boundedFold (gs : List Gate) (w : List Word) (h : ∀ t ∈ w, t < 2^7)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    ∀ t ∈ gs.foldl wordStep w, t < 2^7 := by
  induction gs generalizing w with
  | nil => exact h
  | cons g gs ih =>
    rw [List.foldl_cons]
    apply ih _ _ (fun a ha => hg a (List.mem_cons_of_mem _ ha))
    intro t ht
    have hc := hg g (by simp)
    rcases List.mem_append.mp ht with ht | ht
    · exact h _ ht
    · have ht' := List.mem_singleton.mp ht
      rw [ht']
      exact boundedGate w h g hc.1 hc.2

theorem searchContains (k : ℕ) (p : Word) (s : List Word) (h : p ∈ s) : search p k s = true := by
  induction k with
  | zero => simp [search,h]
  | succ k ih => simp [search,ih]

theorem excludes (k : ℕ) (p : Word) (gs : List Gate) (a s : List Word)
    (ha : ∀ t ∈ a, t ∈ s) (hcap : ∀ t ∈ s, t < 128) (zero : (0 : Word) ∈ s) (ones : (127 : Word) ∈ s)
    (hlen : gs.length ≤ k)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (no : search p k s = false) (j : ℕ) : (gs.foldl wordStep a).getD j 0 ≠ p := by
  induction k generalizing gs a s with
  | zero =>
    have he : gs = [] := List.length_eq_zero_iff.mp (by omega)
    subst gs
    intro h
    have hm := readAvailable ha zero j
    change a.getD j 0 = p at h
    have hp := searchContains 0 p s (h ▸ hm)
    rw [no] at hp
    cases hp
  | succ k ih =>
    cases gs with
    | nil =>
      intro h
      have hm := readAvailable ha zero j
      change a.getD j 0 = p at h
      have hp := searchContains (k+1) p s (h ▸ hm)
      rw [no] at hp
      cases hp
    | cons g gs =>
      let b := wordGate a g
      have ht : gs.length ≤ k := by simpa using hlen
      have hrest : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 :=
        fun _ hp => hg _ (List.mem_cons_of_mem _ hp)
      have hvalid := hg g (by simp)
      have no' := Bool.or_eq_false_iff.mp no
      have hnext : ∀ x ∈ wordStep a g, x ∈ a ∨ x = b := by
        intro x hx
        simpa [wordStep,b] using hx
      change (gs.foldl wordStep (wordStep a g)).getD j 0 ≠ p
      rcases gateAvailable ha hcap zero ones g hvalid.1 hvalid.2 with h | h
      · exact ih gs _ s (fun x hx => (hnext x hx).elim (ha x) (fun he => he ▸ h))
          hcap zero ones ht hrest no'.1
      · have hbranch := branchFalse p b s k h no
        refine ih gs _ (b::s) ?_ ?_ (List.mem_cons_of_mem _ zero) (List.mem_cons_of_mem _ ones)
          ht hrest hbranch
        · intro x hx
          rcases hnext x hx with hx | rfl
          · exact List.mem_cons_of_mem _ (ha x hx)
          · exact List.mem_cons_self
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ((freshMem s b).mp h).1
          · exact hcap _ hx

-- Split the last three gates by the first new word, so each kernel replay is small.
def firstA : List Word := [1, 4, 10, 16, 32]
def firstB : List Word := [38, 44, 47, 50, 52]
def firstC : List Word := [56, 63, 66, 72, 79]
def firstD : List Word := [83, 89, 95, 100, 112]
def firstE : List Word := [113, 117]

def rejectsTail (t : Word) : Bool := !(search target 3 (t::available))

theorem firstChoices : fresh available = firstA ++ firstB ++ firstC ++ firstD ++ firstE := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem checkA : firstA.all rejectsTail = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem checkB : firstB.all rejectsTail = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem checkC : firstC.all rejectsTail = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem checkD : firstD.all rejectsTail = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem checkE : firstE.all rejectsTail = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem noThree : search target 3 available = false := by decide +kernel

theorem noFour : search target 4 available = false := by
  have ha : (fresh available).all rejectsTail = true := by
    simp only [firstChoices,List.all_append,checkA,checkB,checkC,checkD,checkE,Bool.true_and]
  have hb : (fresh available).any (fun t => search target 3 (t::available)) = false := by
    apply List.any_eq_false.mpr
    intro t ht
    have h := List.all_eq_true.mp ha t ht
    simpa [rejectsTail] using h
  change (search target 3 available ||
    (if 3 = 0 then combines target available else
      (fresh available).any (fun t => search target 3 (t::available)))) = false
  rw [if_neg (by decide : (3 : Nat) ≠ 0), noThree, Bool.false_or]
  exact hb

theorem lower : ¬ RepSizeAtMost graph 4 := by
  rintro ⟨C, hC, hs, hr⟩
  have hmask : (C.gates.foldl wordStep inputs).getD C.output 0 = target := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 7
    · let i : Fin 7 := ⟨j,hj⟩
      change bit i ((C.gates.foldl wordStep inputs).getD C.output 0) = bit i target
      rw [bitRead, simulate i _ inputs (fun g hg => hC g hg), inputRows, outputRows]
      exact hr (pairAt i).1 (pairAt i).2
    · have h7 : 2^7 ≤ 2^j := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hj)
      have hfold := boundedFold C.gates inputs (by simp [inputs]) (fun g hg => hC g hg)
      rw [Nat.testBit_lt_two_pow ((boundedRead _ hfold C.output).trans_le h7),
        Nat.testBit_lt_two_pow ((show target < 2^7 by decide).trans_le h7)]
  have ht := excludes 4 target C.gates inputs available
    (fun t ht => List.mem_append_left _ ht) (by simp [available,inputs]) (by decide) (by decide) hs (fun g hg => hC g hg) noFour C.output
  exact ht hmask

end PEqualNP.Outside.L_meta_5602

theorem PEqualNP.Outside.L_meta_5602 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (55 : ℕ).testBit (4 * u.val + v.val)) 5 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (55 : ℕ).testBit (4 * u.val + v.val)) 4 := by
  exact ⟨PEqualNP.Outside.L_meta_5602.upper, PEqualNP.Outside.L_meta_5602.lower⟩
