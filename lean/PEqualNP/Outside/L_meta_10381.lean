import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.Represents
namespace PEqualNP.Outside.L_meta_10381

-- The truth-table engine and projection lemmas are adapted from L_meta_9358.
namespace WordEngine
abbrev Word := Nat
def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask
def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words
def availableB (mask : Nat) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w
def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank
def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))
theorem restrictWord (mask : Nat) (word : Word) : word &&& mask &&& mask = word &&& mask := by
  simp
theorem projectGate {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots : List Word} {out : Word} (gate : GateWord mask roots out) :
    GateWord cut (roots.map (· &&& cut)) (out &&& cut) := by
  have av {word : Word} (ha : AvailableWord mask roots word) :
      AvailableWord cut (roots.map (· &&& cut)) (word &&& cut) := by
    rcases ha with rfl | rfl | hm
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl submask)
    · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · refine Or.inl ⟨a &&& cut, av ha, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have cutAt := congrArg (fun n : Nat => n.testBit i) submask
    simp only [Nat.testBit_and, Nat.testBit_xor] at cutAt ⊢
    cases h : cut.testBit i
    · simp
    · simp [h] at cutAt
      simp [cutAt]
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases cut.testBit i <;> simp
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases cut.testBit i <;> simp
theorem availableWeaken {mask : Nat} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h
def properWord (mask word : Word) : Prop := word ≠ 0 ∧ word ≠ mask
def binWord (isOr : Bool) (a b : Word) : Word :=
  if isOr then a ||| b else a &&& b
theorem binWord_comm (d : Bool) (a b : Word) : binWord d a b = binWord d b a := by
  cases d <;> simp [binWord, Nat.land_comm, Nat.lor_comm]
variable {mask : Nat} {target : Word}
def LiveWord (mask : Nat) (target : Word) : Nat → Nat → Finset (Word) → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ properWord mask target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Word)) (a : Word), t=u+1 ∧ S=insert a U ∧ properWord mask a ∧
      (mask ^^^ a) ∉ insert a U ∧ LiveWord mask target k u (insert ((mask ^^^ a)) U)) ∨
    (∃ (U : Finset (Word)) (a b : Word) (d : Bool), S=insert a (insert b U) ∧ properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      binWord d a b ∉ insert a (insert b U) ∧ LiveWord mask target k t (insert (binWord d a b) U))
theorem LiveWord.stop {target : Word} (hp : properWord mask target) : LiveWord mask target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem LiveWord.unary {target : Word} {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
    (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)) :
    LiveWord mask target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem LiveWord.binary {target : Word} {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
    (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)) :
    LiveWord mask target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveWord.ind {target : Word} {motive : ∀ (k t : Nat) (S : Finset (Word)), LiveWord mask target k t S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 0 {target} (LiveWord.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
      (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)),
      motive k t (insert ((mask ^^^ a)) U) tail → motive (k+1) (t+1) (insert a U) (LiveWord.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
      (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)),
      motive k t (insert (binWord d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (LiveWord.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset (Word)} (h : LiveWord mask target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)
theorem liveWordProper {k t S} (h : LiveWord mask target k t S) : ∀ a ∈ S, properWord mask a := by
  induction h using LiveWord.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
def wordRep (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  w ∈ ws ∨ ¬properWord mask w
def Masked (mask word : Nat) : Prop := word &&& mask = word
theorem maskedAvailable {bank : List Word} {word : Word}
    (all : ∀ w ∈ bank, Masked mask w) (aw : AvailableWord mask bank word) :
    Masked mask word := by
  rcases aw with rfl | rfl | hw
  · simp [Masked]
  · simp [Masked]
  · exact all _ hw
theorem maskedGate {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateWord mask bank out) :
    Masked mask out := by
  rcases g with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, ea | ea⟩
  · have h := projectGate (mask := mask) (cut := mask) (by simp)
      (roots := bank) (out := mask ^^^ a) (Or.inl ⟨a, ha, rfl⟩)
    have ma := maskedAvailable all ha
    unfold Masked at ma ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bit := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
    cases hm : mask.testBit i <;> simp_all
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    simp only [Masked] at ma mb ⊢
    rw [Nat.land_assoc, mb]
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    unfold Masked at ma mb ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bitA := congrArg (fun n : Nat => n.testBit i) ma
    have bitB := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at bitA bitB ⊢
    cases hm : mask.testBit i <;> simp_all
def binaryWitness (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  ∃ d a b, a ∈ bank ∧ b ∈ bank ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ out = binWord d a b
theorem classifyBinary {bank : List Word}
    (all : ∀ w ∈ bank, Masked mask w) (d : Bool) {a b : Word}
    (ha : AvailableWord mask bank a) (hb : AvailableWord mask bank b) :
    wordRep mask bank (binWord d a b) ∨ binaryWitness mask bank (binWord d a b) := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Word} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  have ma : a &&& mask = a := maskedAvailable all ha
  have mb : b &&& mask = b := maskedAvailable all hb
  have absorbA : a ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  have absorbB : b ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  rcases classify ha with rfl | hma | ⟨ha', pa⟩
  · rw [binWord_comm]
    cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, wordRep] using
          (Or.inl hv : wordRep mask bank b))
  · rw [hma, binWord_comm]
    cases d
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, mb, wordRep] using
          (Or.inl hv : wordRep mask bank b))
    · exact Or.inl (by simpa [binWord, absorbB] using cm)
  rcases classify hb with rfl | hmb | ⟨hb', pb⟩
  · cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · exact Or.inl (by simpa [binWord, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
  · rw [hmb]
    cases d
    · exact Or.inl (by simpa [binWord, ma, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
    · exact Or.inl (by simpa [binWord, absorbA] using cm)
  by_cases eq : a = b
  · subst b
    cases d <;> exact Or.inl (by simpa [binWord, wordRep] using
      (Or.inl ha' : wordRep mask bank a))
  exact Or.inr ⟨d, a, b, ha', hb', pa, pb, eq, rfl⟩
variable {rows : Nat}
def fullMask (rows : Nat) : Nat := 2 ^ rows - 1
theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))
abbrev maskedFlat (m a : Word) : Prop := a &&& m = 0 ∨ a &&& m = m
def flatSet (m : Word) (s : Finset (Word)) := s.filter (maskedFlat m)
def visibleWords (m : Word) (s : Finset (Word)) := s.image fun w => w &&& m
theorem flIns {m a : Word} {s : Finset (Word)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]
theorem flLe (m a : Word) (s : Finset (Word)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]
theorem prIns (m a : Word) (s : Finset (Word)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..
theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp
theorem flBoth {m a b : Word} {d : Bool} (ha : maskedFlat m a) (hb : maskedFlat m b) :
    maskedFlat m (binWord d a b) := by
  unfold maskedFlat at *
  rw [cofBinary]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> cases d <;>
    simp [binWord, ha, hb]
theorem simpleBin {m a b : Word} {d : Bool} (h : maskedFlat m a ∨ maskedFlat m b) :
    binWord d a b &&& m = 0 ∨ binWord d a b &&& m = m ∨
      binWord d a b &&& m = a &&& m ∨ binWord d a b &&& m = b &&& m := by
  rw [cofBinary]
  have top1 (x : Word) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]
    simp
  have top2 (x : Word) : m ||| (x &&& m) = m := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and]
    cases x.testBit i <;> cases m.testBit i <;> rfl
  have right1 (x : Word) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Word) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  rcases h with (ha|ha)|(hb|hb) <;> cases d <;>
    simp [binWord, *, top1, top2, right1, right2]
def projectedStock (m : Word) (s : Finset (Word)) := insert 0 (insert m (visibleWords m s))
theorem availableB_spec {mask : Nat} {bank : List Word} {v : Word} :
    availableB mask bank v = true ↔ AvailableWord mask bank v := by
  simp [availableB, AvailableWord, or_assoc]
theorem flatCountCard (mask : Nat) {words : List Word} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]
theorem and_cu (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (_h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem and_cv (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cu (u v e i : ℕ) (_h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cv (u v e i : ℕ) (h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem liveDirected {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) {p n : Nat}
    (hp : goal.testBit p = true) (hn : goal.testBit n = false) :
    ∃ w ∈ S, w.testBit p = true ∧ w.testBit n = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩ := live
    exact ⟨goal, by simp, hp, hn⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, ueq, _⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    obtain ⟨w, hw, wp, wn⟩ := ih tail
    rcases Finset.mem_insert.mp hw with eq | hU
    · subst w
      cases op
      · by_cases ha : a.testBit n = false
        · exact ⟨a, Finset.mem_insert_self .., and_cu a b p n wp wn (by simp [ha])⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            and_cv a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
      · by_cases ha : a.testBit p = true
        · exact ⟨a, Finset.mem_insert_self .., or_cu a b p n wp wn ha⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            or_cv a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩
theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)
def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0
def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]
theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp
theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]
theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]
theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]
theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]
end WordEngine
open WordEngine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Plane
abbrev AO (m : Nat) (stock : List Word) (out : Word) :=
  ∃ a b, AvailableWord m stock a ∧ AvailableWord m stock b ∧ (out = a &&& b ∨ out = a ||| b)
def AOBuild (m : Nat) (stock : List Word) : List Word → Prop
  | [] => True
  | w::ws => AO m stock w ∧ AOBuild m (w::stock) ws
def AOLower (m : Nat) (stock : List Word) (target : Word) (bound : Nat) : Prop :=
  ∀ vs, AOBuild m stock vs → AvailableWord m (vs++stock) target → bound ≤ vs.length
theorem aoOfAvailable {m stock w} (av : AvailableWord m stock w) : AO m stock w :=
  ⟨w,0,av,Or.inl rfl,Or.inr (by simp)⟩
theorem aoWeaken {m small big vs} (sub : ∀ w ∈ small, AvailableWord m big w)
    (h : AOBuild m small vs) : AOBuild m big vs := by
  induction vs generalizing small big with
  | nil => trivial
  | cons w ws ih =>
    obtain ⟨⟨a,b,ha,hb,ev⟩,tail⟩ := h
    refine ⟨⟨a,b,availableWeaken sub ha,availableWeaken sub hb,ev⟩,ih ?_ tail⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun v hv => Or.inr (Or.inr (List.mem_cons_of_mem _ hv))) (sub _ ha)
variable {mask target : Word}
theorem pullAO {w : List (Word)} {z : Word} {k S} (h : LiveWord mask target k 0 S)
    (hz : wordRep mask w z ∨ binaryWitness mask w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ LiveWord mask target k' 0 S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveWordProper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (binWord d a b)
        have ht : LiveWord mask target k 0 (insert (binWord d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : binWord d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
theorem extractAO {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : AOBuild mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k S, k ≤ values.length ∧ LiveWord mask target k 0 S ∧ ∀ w ∈ S, w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0, {target}, Nat.zero_le _, LiveWord.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all (Or.inr builds.1)
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm))
    obtain ⟨k, S, hk, live, sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S, v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    have gate : wordRep mask roots w ∨ binaryWitness mask roots w := by
      obtain ⟨a,b,ha,hb,eq|eq⟩ := builds.1
      · subst w; exact classifyBinary all false ha hb
      · subst w; exact classifyBinary all true ha hb
    obtain ⟨k', S', hk', hl, hsub⟩ := pullAO live gate available
    exact ⟨k', S', by simp only [List.length_cons]; omega, hl, hsub⟩
theorem aoGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    AO (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl
  · cases ins with
    | nil => exact aoOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact aoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact aoOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact aoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
theorem aoBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ AOBuild (fullMask rows) (bank.map BitVec.toNat) vs ∧
      ∀ v ∈ gs.foldl hcsStep bank, v.toNat ∈ vs ++ bank.map BitVec.toNat := by
  induction gs generalizing bank with
  | nil => exact ⟨[], rfl, trivial, fun _ h => List.mem_map_of_mem h⟩
  | cons g gs ih =>
    let v := hcsGateVal bank g
    have hg := hfan g List.mem_cons_self
    obtain ⟨xs, len, build, sub⟩ := ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have eq : (hcsStep bank g).map BitVec.toNat = bank.map BitVec.toNat ++ [v.toNat] := by
      simp [hcsStep, v]
    rw [eq] at build
    refine ⟨v.toNat :: xs, by simp [len], ⟨aoGateWord bank g hg.1 hg.2, aoWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m
theorem monoFan {C : Circuit} (legal : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨op,sz⟩ := legal g hg
  refine ⟨?_,sz⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
  tauto
end Plane
open WordEngine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace Plane
set_option maxHeartbeats 0 in
def posted (u v : Fin 5) : Bool := (16269948 : Nat).testBit (5*u.val+v.val)
set_option maxHeartbeats 0 in
def raw : List (BitVec 25) := [0x1f, 0x3e0, 0x7c00, 0xf8000, 0x1f00000, 0x108421, 0x210842, 0x421084, 0x842108, 0x1084210]
set_option maxHeartbeats 0 in
def stock : List Word := raw.map BitVec.toNat
set_option maxHeartbeats 0 in
def target25 : BitVec 25 := 16269948
set_option maxHeartbeats 0 in
abbrev T : Word := target25.toNat
set_option maxHeartbeats 0 in
def point (r : Fin 25) := oneEach (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 (r.val % 5))
set_option maxHeartbeats 0 in
theorem representation_live (C : Circuit) (legal : Monotone2 C) (right : Represents posted C) :
    ∃ k ≤ C.size, LiveWord (fullMask 25) T k 0 stock.toFinset := by
  have rawBits : ∀ r : Fin 25, (raw.map fun w => w.getLsbD r.val) = point r := by decide +kernel
  have goalBits : ∀ r : Fin 25, target25.getLsbD r.val =
      posted (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 (r.val % 5)) := by decide +kernel
  let eb := C.gates.foldl hcsStep raw
  have eq : eb.getD C.output 0 = target25 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Fin 25 := ⟨j,hj⟩
    have bits := hcsFoldBits raw r C.gates (monoFan legal)
    have ack := right (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 (r.val % 5))
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (point r)).getD C.output false = _ at ack
    rw [← rawBits r,← bits] at ack
    exact (hcsGetDBit eb j C.output).trans (ack.trans (goalBits r).symm)
  obtain ⟨ws,len,built,sub⟩ := aoBuilds raw C.gates legal
  have hit : AvailableWord (fullMask 25) (ws++stock) T := by
    change AvailableWord _ _ target25.toNat
    rw [←eq,List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some w => exact Or.inr (Or.inr (sub w (List.mem_of_getElem? h)))
  obtain ⟨k,S,budget,run,subset⟩ := extractAO (stockMaskedOfCheck (by decide +kernel : stock.all (fun w => w &&& fullMask 25 == w) = true)) built hit
      (by unfold properWord; decide +kernel)
  have witnesses : ∀ w ∈ stock, ∃ p n : Fin 25, T.testBit p.val = true ∧ T.testBit n.val = false ∧
      ∀ u ∈ stock, u.testBit p.val = true → u.testBit n.val = false → u = w := by decide +kernel
  have same : S = stock.toFinset := by
    ext w; constructor
    · exact fun h => List.mem_toFinset.mpr (subset w h)
    · intro h
      obtain ⟨p,n,yes,no,unique⟩ := witnesses w (List.mem_toFinset.mp h)
      obtain ⟨u,mem,a,b⟩ := liveDirected run yes no
      exact (unique u (subset u mem) a b) ▸ mem
  exact ⟨k,budget.trans (Nat.le_of_eq len),same ▸ run⟩
end Plane
namespace Plane.Project
def Pool (g : Word) : Nat → Finset Word → Prop
  | 0, s => g ∈ s
  | n+1, s => Pool g n s ∨ ∃ a ∈ s, ∃ b ∈ s, ∃ d, Pool g n (insert (binWord d a b) s)
theorem weakenPool {g : Word} {n s q} (sub : s ⊆ q) (h : Pool g n s) : Pool g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,b,hb,d,run⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) run⟩
theorem maskedAO {mask goal : Word} {k s} (run : LiveWord mask goal k 0 s) (m : Word) (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n+(flatSet m s).card ≤ k ∧ Pool (goal &&& m) n (projectedStock m s) := by
  induction k generalizing s with
  | zero =>
    have es := run.2.1
    subst s
    refine ⟨0,?_,?_⟩
    · simp only [flatSet, Finset.filter_singleton, properGoal, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · change goal &&& m ∈ projectedStock m {goal}
      simp [projectedStock,visibleWords]
  | succ k ih =>
    rcases run with ⟨v,u,a,impossible,_⟩ | ⟨u,a,b,d,eq,pa,pb,ab,fresh,tail⟩
    · omega
    subst s
    let v := binWord d a b
    obtain ⟨n,cap,built⟩ := ih tail
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n+(flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k+1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa,fb,ite_true,ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBoth fa fb; simp only [vf,ite_true] at cap; omega | omega | tauto
      refine ⟨n,budget,weakenPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with e|e|e|e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · subst w
        have cases := simpleBin (d := d) simple
        tauto
      · tauto
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa,fb,ite_false] at ca cb
      refine ⟨n+1,by omega,Or.inr ⟨a &&& m,?_,b &&& m,?_,d,weakenPool ?_ built⟩⟩
      · simp [projectedStock,prIns]
      · simp [projectedStock,prIns]
      · intro w hw
        simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
        rw [cofBinary] at hw
        tauto
theorem toBuild {m g : Word} {n s} {stock : List Word}
    (sources : ∀ x ∈ s, AvailableWord m stock x) (h : Pool g n s) :
    ∃ vs, vs.length ≤ n ∧ AOBuild m stock vs ∧ AvailableWord m (vs ++ stock) g := by
  induction n generalizing s stock with
  | zero => exact ⟨[],by simp,True.intro,sources g h⟩
  | succ n ih =>
    rcases h with h | ⟨a,ha,b,hb,d,h⟩
    · obtain ⟨vs,len,built,hit⟩ := ih sources h; exact ⟨vs,by omega,built,hit⟩
    · let z := binWord d a b
      have sub : ∀ x ∈ insert z s, AvailableWord m (z::stock) x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun v hv => Or.inr (Or.inr (List.mem_cons_of_mem _ hv))) (sources _ hx)
      obtain ⟨vs,len,built,hit⟩ := ih sub h
      refine ⟨z::vs,by simp; omega,⟨⟨a,b,sources _ ha,sources _ hb,?_⟩,built⟩,?_⟩
      · cases d <;> simp [z,binWord]
      · rcases hit with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_left_comm,or_assoc] using h))
theorem appendAO {mask : Word} {stock xs ys : List Word} (left : AOBuild mask stock xs)
    (right : AOBuild mask (xs ++ stock) ys) : AOBuild mask stock (xs ++ ys) := by
  induction xs generalizing stock with
  | nil => exact right
  | cons x xs ih =>
    refine ⟨left.1, ih left.2 (aoWeaken ?_ right)⟩
    intro w hw
    exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hw))
theorem cut {mask goal m k S stock prep floor} (run : LiveWord mask goal k 0 S)
    (proper : ¬ maskedFlat m goal) (built : AOBuild m stock prep)
    (supply : ∀ x ∈ projectedStock m S, AvailableWord m (prep ++ stock) x)
    (lower : AOLower m stock (goal &&& m) floor) :
    floor + (flatSet m S).card ≤ prep.length + k := by
  obtain ⟨n,len,red⟩ := maskedAO run m proper
  obtain ⟨vs,cap,prog,hit⟩ := toBuild supply red
  have total := appendAO built prog
  have hit' : AvailableWord m ((prep++vs)++stock) (goal &&& m) := by
    rcases hit with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by simpa [List.mem_append,or_left_comm,or_comm,or_assoc] using h))
  have bound := lower _ total hit'
  simp only [List.length_append] at bound
  omega
end Plane.Project
namespace Plane.Project
def oneAO (stock : List Word) (w : Word) : Bool :=
  stock.any fun a => stock.any fun b => (a &&& b == w) || (a ||| b == w)
theorem oneAO_spec {m : Word} {stock w} (h : oneAO stock w) : AO m stock w := by
  obtain ⟨a,ha,ok⟩ := List.any_eq_true.mp h
  obtain ⟨b,hb,ok⟩ := List.any_eq_true.mp ok
  have eq := Bool.or_eq_true_iff.mp ok
  exact ⟨a,b,Or.inr (Or.inr ha),Or.inr (Or.inr hb),eq.elim (fun e => Or.inl (eq_of_beq e).symm)
    (fun e => Or.inr (eq_of_beq e).symm)⟩
def cheapPrep (m : Word) (stock : List Word) : List Word → Option (List Word)
  | [] => some []
  | w::ws =>
    if availableB m stock w then cheapPrep m stock ws
    else if oneAO stock w then (cheapPrep m (w::stock) ws).map (w::·)
    else none
theorem inLarger {m w : Word} {xs raw : List Word} (h : AvailableWord m raw w) :
    AvailableWord m (xs ++ raw) w :=
  availableWeaken (fun _ hw => Or.inr (Or.inr (List.mem_append_right _ hw))) h
theorem cheapPrep_spec {m : Word} {stock needed vs}
    (h : cheapPrep m stock needed = some vs) :
    AOBuild m stock vs ∧ ∀ w ∈ needed, AvailableWord m (vs++stock) w := by
  induction needed generalizing stock vs with
  | nil =>
    obtain rfl := Option.some.inj h
    exact ⟨True.intro,by simp⟩
  | cons w ws ih =>
    simp only [cheapPrep] at h
    split at h
    · rename_i present
      obtain ⟨built,covered⟩ := ih h
      refine ⟨built,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact inLarger (availableB_spec.mp present)
      · exact covered _ hv
    · split at h
      · rename_i step
        cases he : cheapPrep m (w::stock) ws with
        | none => simp [he] at h
        | some more =>
          simp [he] at h
          subst vs
          obtain ⟨built,covered⟩ := ih he
          refine ⟨⟨oneAO_spec step,built⟩,?_⟩
          intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact Or.inr (Or.inr (by simp))
          · apply availableWeaken (small := more++w::stock) (big := (w::more)++stock) _ (covered v hv)
            intro x hx
            exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hx))
      · contradiction
def cheapCut (m : Word) (low fuel : Nat) (stock ws : List Word) : Bool :=
  let needed := ws.map (· &&& m)
  match cheapPrep m stock needed with
  | none => false
  | some vs => decide (vs.length + fuel < low + flatCount m ws)
theorem cheapCut_sound {m mask goal low fuel stock ws k}
    (lower : AOLower m stock (goal &&& m) low) (proper : ¬ maskedFlat m goal)
    (nd : ws.Nodup) (hk : k ≤ fuel) (close : cheapCut m low fuel stock ws = true) :
    ¬ LiveWord mask goal k 0 ws.toFinset := by
  intro run
  unfold cheapCut at close
  cases he : cheapPrep m stock (ws.map (· &&& m)) with
  | none => simp [he] at close
  | some vs =>
    simp [he] at close
    obtain ⟨built,covered⟩ := cheapPrep_spec he
    have source : ∀ w ∈ projectedStock m ws.toFinset, AvailableWord m (vs++stock) w := by
      intro w hw
      simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image,List.mem_toFinset] at hw
      rcases hw with rfl | rfl | ⟨v,hv,rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact covered _ (List.mem_map_of_mem hv)
    have bound := cut run proper built source lower
    rw [flatCountCard m nd] at close
    omega
end Plane.Project

open WordEngine Plane Plane.Project PEqualNP.Represents

-- Keep rows 0, 1, 2, 4 and columns 0, 2, 4. Three input wires become constant.
def minorMask : Nat := 22042293
def minorStock : List Nat := [21, 672, 21504, 1049633, 4198532, 16794128, 22020096]
def minorGoal : Nat := 5259828

private def readSlot : List (BitVec 25) → BitVec 4 → BitVec 4 → BitVec 25
  | [], _, _ => 0
  | a :: rest, i, k => if i == k then a else readSlot rest i (k+1)

private theorem readSlot_get (bank : List (BitVec 25)) (j : Nat) (k : BitVec 4)
    (hj : j < bank.length) (fit : k.toNat + j < 16) :
    readSlot bank (BitVec.ofNat 4 (k.toNat + j)) k = bank[j] := by
  induction bank generalizing j k with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero => simp [readSlot]
    | succ j =>
      have kfit : k.toNat + 1 < 16 := by omega
      have ksucc : (k + 1).toNat = k.toNat + 1 := by
        rw [BitVec.toNat_add]
        exact Nat.mod_eq_of_lt kfit
      have ne : BitVec.ofNat 4 (k.toNat + (j+1)) ≠ k := by
        intro h
        have eq := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit] at eq
        omega
      simp only [readSlot, ne, beq_iff_eq, ite_false, List.getElem_cons_succ]
      have ht : j < xs.length := by simpa using hj
      have hs : (k+1).toNat + j < 16 := by omega
      have idx : k.toNat + (j+1) = (k+1).toNat + j := by omega
      rw [idx]
      exact ih j (k+1) ht hs

private def gateSlot (bank : List (BitVec 25)) (a b : BitVec 4) (op : Bool) : BitVec 25 :=
  if op then readSlot bank a 0 ||| readSlot bank b 0
  else readSlot bank a 0 &&& readSlot bank b 0

-- Include both constants and all seven surviving input wires.
private def coreBank : List (BitVec 25) :=
  [0, 22042293, 21, 672, 21504, 1049633, 4198532, 16794128, 22020096]

-- Every gate selects two earlier wires and applies conjunction or disjunction.
set_option maxHeartbeats 8000000 in
private theorem checkCore
    (v0 v1 v2 v3 v4 v5 v6 : BitVec 25)
    (a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 out : BitVec 4)
    (d0 d1 d2 d3 d4 d5 d6 : Bool)
    (h0 : v0 = gateSlot (coreBank) a0 b0 d0)
    (h1 : v1 = gateSlot (v0 :: coreBank) a1 b1 d1)
    (h2 : v2 = gateSlot (v1 :: v0 :: coreBank) a2 b2 d2)
    (h3 : v3 = gateSlot (v2 :: v1 :: v0 :: coreBank) a3 b3 d3)
    (h4 : v4 = gateSlot (v3 :: v2 :: v1 :: v0 :: coreBank) a4 b4 d4)
    (h5 : v5 = gateSlot (v4 :: v3 :: v2 :: v1 :: v0 :: coreBank) a5 b5 d5)
    (h6 : v6 = gateSlot (v5 :: v4 :: v3 :: v2 :: v1 :: v0 :: coreBank) a6 b6 d6)
    : readSlot (v6 :: v5 :: v4 :: v3 :: v2 :: v1 :: v0 :: coreBank) out 0 ≠ 5259828 := by
  simp only [gateSlot, readSlot, coreBank, BitVec.reduceAdd] at *
  bv_decide (config := { timeout := 260 })

private theorem availableSlot {xs : List Word} {w : Word} (fit : xs.length ≤ 7)
    (h : AvailableWord minorMask (xs ++ minorStock) w) :
    ∃ s, readSlot (xs.map (BitVec.ofNat 25) ++ coreBank) s 0 = BitVec.ofNat 25 w := by
  let bank := xs.map (BitVec.ofNat 25) ++ coreBank
  have bankCap : bank.length ≤ 16 := by
    simp [bank, coreBank]
    omega
  have mem : BitVec.ofNat 25 w ∈ bank := by
    rcases h with rfl | rfl | h
    · simp [bank, coreBank]
    · simp [bank, coreBank, minorMask]
    · rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (List.mem_map_of_mem h)
      · apply List.mem_append_right
        have embed : minorStock.map (BitVec.ofNat 25) ⊆ coreBank := by decide
        exact embed (List.mem_map_of_mem h)
  obtain ⟨j, hj, atJ⟩ := List.mem_iff_getElem.mp mem
  refine ⟨BitVec.ofNat 4 j, ?_⟩
  simpa [atJ] using readSlot_get bank j 0 hj (by simp; omega)

private theorem gateWitness {xs : List Word} {w : Word} (fit : xs.length ≤ 7)
    (h : AO minorMask (xs ++ minorStock) w) :
    ∃ a b op, BitVec.ofNat 25 w = gateSlot
      (xs.map (BitVec.ofNat 25) ++ coreBank) a b op := by
  obtain ⟨x, y, hx, hy, h⟩ := h
  obtain ⟨a, ha⟩ := availableSlot fit hx
  obtain ⟨b, hb⟩ := availableSlot fit hy
  rcases h with rfl | rfl
  · exact ⟨a, b, false, by rw [gateSlot]; simp only [Bool.false_eq_true, ite_false, Bool.true_eq, ite_true, ha, hb, BitVec.ofNat_and, BitVec.ofNat_or]⟩
  · exact ⟨a, b, true, by rw [gateSlot]; simp only [Bool.false_eq_true, ite_false, Bool.true_eq, ite_true, ha, hb, BitVec.ofNat_and, BitVec.ofNat_or]⟩

private theorem buildPad {n : Nat} {xs stock : List Word} (h : AOBuild minorMask stock xs) :
    AOBuild minorMask stock (xs ++ List.replicate n 0) := by
  have zeroes (bank : List Word) : AOBuild minorMask bank (List.replicate n 0) := by
    induction n generalizing bank with
    | zero => trivial
    | succ n ih =>
      rw [List.replicate_succ]
      exact ⟨aoOfAvailable (Or.inl rfl), ih _⟩
  exact appendAO h (zeroes _)

private theorem exactLength (xs : List Word) (h : xs.length = 7) :
    ∃ w0 w1 w2 w3 w4 w5 w6, xs = [w0,w1,w2,w3,w4,w5,w6] := by
  obtain ⟨w0, xs, rfl⟩ := List.exists_cons_of_ne_nil (l := xs) (by rintro rfl; simp at h)
  obtain ⟨w1, xs, rfl⟩ := List.exists_cons_of_ne_nil (l := xs) (by rintro rfl; simp at h)
  obtain ⟨w2, xs, rfl⟩ := List.exists_cons_of_ne_nil (l := xs) (by rintro rfl; simp at h)
  obtain ⟨w3, xs, rfl⟩ := List.exists_cons_of_ne_nil (l := xs) (by rintro rfl; simp at h)
  obtain ⟨w4, xs, rfl⟩ := List.exists_cons_of_ne_nil (l := xs) (by rintro rfl; simp at h)
  obtain ⟨w5, xs, rfl⟩ := List.exists_cons_of_ne_nil (l := xs) (by rintro rfl; simp at h)
  obtain ⟨w6, xs, rfl⟩ := List.exists_cons_of_ne_nil (l := xs) (by rintro rfl; simp at h)
  have e : xs = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at h; omega)
  exact ⟨w0,w1,w2,w3,w4,w5,w6,by rw [e]⟩

private theorem minorLower : AOLower minorMask minorStock minorGoal 8 := by
  intro xs built output
  by_contra! below
  let padding := List.replicate (7-xs.length) (0 : Word)
  have len : (xs ++ padding).length = 7 := by simp [padding]; omega
  have hb : AOBuild minorMask minorStock (xs ++ padding) := buildPad built
  have ho : AvailableWord minorMask ((xs ++ padding) ++ minorStock) minorGoal := by
    refine availableWeaken ?_ output
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_append_left _ hw)))
    · exact Or.inr (Or.inr (List.mem_append_right _ hw))
  obtain ⟨w0,w1,w2,w3,w4,w5,w6, ws⟩ := exactLength _ len
  rw [ws] at hb ho
  obtain ⟨a0, b0, d0, h0⟩ := gateWitness (xs := []) (by simp) hb.1
  obtain ⟨a1, b1, d1, h1⟩ := gateWitness (xs := [w0]) (by simp) hb.2.1
  obtain ⟨a2, b2, d2, h2⟩ := gateWitness (xs := [w1,w0]) (by simp) hb.2.2.1
  obtain ⟨a3, b3, d3, h3⟩ := gateWitness (xs := [w2,w1,w0]) (by simp) hb.2.2.2.1
  obtain ⟨a4, b4, d4, h4⟩ := gateWitness (xs := [w3,w2,w1,w0]) (by simp) hb.2.2.2.2.1
  obtain ⟨a5, b5, d5, h5⟩ := gateWitness (xs := [w4,w3,w2,w1,w0]) (by simp) hb.2.2.2.2.2.1
  obtain ⟨a6, b6, d6, h6⟩ := gateWitness (xs := [w5,w4,w3,w2,w1,w0]) (by simp) hb.2.2.2.2.2.2.1
  have outMem : AvailableWord minorMask ([w6,w5,w4,w3,w2,w1,w0] ++ minorStock) minorGoal := by
    simpa only [AvailableWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc, or_left_comm, or_comm] using ho
  obtain ⟨out, hOut⟩ := availableSlot (by simp) outMem
  exact checkCore (BitVec.ofNat 25 w0) (BitVec.ofNat 25 w1) (BitVec.ofNat 25 w2) (BitVec.ofNat 25 w3) (BitVec.ofNat 25 w4) (BitVec.ofNat 25 w5) (BitVec.ofNat 25 w6) a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 out d0 d1 d2 d3 d4 d5 d6 h0 h1 h2 h3 h4 h5 h6 hOut

private theorem lower : ¬ RepSizeAtMost posted 10 := by
  rintro ⟨c,legal,cap,right⟩
  obtain ⟨k,fit,live⟩ := representation_live c legal right
  exact cheapCut_sound (m := minorMask) (goal := T) (low := 8) (fuel := 10)
    (stock := minorStock) (ws := stock) minorLower (by unfold maskedFlat; decide +kernel)
    (by decide +kernel) (fit.trans cap) (by decide +kernel) live

end PEqualNP.Outside.L_meta_10381

theorem PEqualNP.Outside.L_meta_10381 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16269948 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact PEqualNP.Outside.L_meta_10381.lower
