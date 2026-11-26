import PEqualNP.Defs
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum
namespace PEqualNP.Outside.L_meta_18163_aux.Five

namespace WordEngine
def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)
def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start
theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)
theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩
abbrev Word := Nat
abbrev RowState := Nat × List Word × List (Word × Word × Word)
def insertWord (w : Word) (ws : List Word) : List Word :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws
def childState (mask token : Nat) (state : RowState) : Option RowState :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 3
  let a := token / (4 * 3 * 64)
  let b := (token / (4 * 3)) % 64
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if op == 2 || keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)
def gateToken (a b op keep : Nat) : Nat := ((a * 64 + b) * 3 + op) * 4 + keep
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
theorem liveWordSize {k t S} (h : LiveWord mask target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using LiveWord.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : (mask ^^^ a) ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : binWord d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩
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
theorem insertWordMem {x w : Word} {ws : List Word} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]
theorem insertWordNodup {w : Word} {ws : List Word} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩
theorem insertWordSet (w : Word) (ws : List Word) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]
theorem eraseWordSet {ws : List Word} (nd : ws.Nodup) (w : Word) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]
theorem gateTokenFields {a b op keep : Nat} (hb : b < 64) (ho : op < 3) (hk : keep < 4) :
    gateToken a b op keep % 4 = keep ∧
    gateToken a b op keep / 4 % 3 = op ∧
    gateToken a b op keep / (4 * 3 * 64) = a ∧
    gateToken a b op keep / (4 * 3) % 64 = b := by
  unfold gateToken
  omega
def keepWord (save : Bool) (w : Word) (ws : List Word) : List Word :=
  if save then ws else ws.erase w
theorem keepNodup {ws : List Word} (nd : ws.Nodup) (save : Bool) (w : Word) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd
theorem keepSubset (save : Bool) (w : Word) (ws : List Word) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h
theorem keepSet {ws : List Word} (nd : ws.Nodup) {w : Word} {U : Finset Word}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]
theorem keepPairSet {ws : List Word} (nd : ws.Nodup) {a b : Word} {U : Finset Word}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h
theorem getWord {ws : List Word} {x : Word} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb
theorem binaryChild {mask fuel a b : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x y : Word} {keep : Nat}
    (d : Bool) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (binWord d x y)) (fresh : binWord d x y ∉ ws) :
    childState mask (gateToken a b (if d then 1 else 0) keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (binWord d x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (binWord d x y, x, y) :: history) := by
  have oh : (if d then 1 else 0) < 3 := by cases d <;> decide
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) hb64 oh hk
  simp only [childState, ke, op, aa, bb, hx, hy]
  cases d <;>
    simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, binWord, properWord]
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
abbrev PointWire (rows : Nat) := Fin rows → Bool
def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]
theorem encodeAnd (a b : PointWire rows) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
theorem encodeOr (a b : PointWire rows) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
def pointWord (f : PointWire rows) : Word := (encodePoint f).toNat
def relabel (sourceIndex : Fin rows → Fin rows) (word : Word) : Word :=
  pointWord fun i => word.testBit (sourceIndex i).val
theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]
theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))
theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]
theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]
theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq
theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i
theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Word) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)
theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Word} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]
theorem kw_step (goal : Word) (D D' : Finset Word) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, goal.testBit e = true → goal.testBit i = false →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, goal.testBit e = true → goal.testBit i = false → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_eq_left (h)]
    cases c e i
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2, h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx, hcc⟩ | ⟨hx, hcc⟩
      · rw [hx]; exact ⟨hu, hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv, hcv e i h2 h3 hcc⟩
    · rw [ite_eq_right (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
          · rw [hx', hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx', hy']
        rw [ite_eq_left (h3), ite_eq_left (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_eq_right (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_eq_right (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_eq_right h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_eq_right h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_eq_right (h3n)]
        exact h3
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
def KWPartition (goal : Word) (ws : Finset Word) : Prop :=
  ∃ f : Nat → Nat → Word,
    (∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ ws ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
    (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true →
      goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
theorem kwFromLive {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) (tight : S.card = k + 1) : KWPartition goal S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    subst S
    exact ⟨fun _ _ => goal, fun _ _ hp hn => ⟨by simp, hp, hn⟩, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, eq, _⟩ | ⟨U, a, b, op, rfl, pa, pb, ab, fresh, tail⟩
    · omega
    let w := binWord op a b
    have wU : w ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have wA : w ≠ a := fun eq => fresh (Finset.mem_insert.mpr (Or.inl eq))
    have wB : w ≠ b := fun eq => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq)))
    have tailSize := (liveWordSize tail).2
    change (insert w U).card + 0 ≤ k + 1 at tailSize
    rw [Finset.card_insert_of_notMem wU] at tailSize
    have paCard := Finset.card_insert_le a (insert b U)
    have pbCard := Finset.card_insert_le b U
    have aU : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      omega
    have bU : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have := Finset.card_insert_le a U
      omega
    obtain ⟨f, hf, hr⟩ := ih tail (by
      change (insert w U).card = k + 1
      rw [Finset.card_insert_of_notMem wU]
      omega)
    have keepA : a ∉ insert w U := by simp [wA.symm, aU]
    have keepB : b ∉ insert w U := by simp [wB.symm, bU]
    have other : ∀ x ∈ insert w U, x ≠ w → x ∈ insert a (insert b U) := by
      intro x hx hn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left hn))
    have ha : a ∈ insert a (insert b U) := Finset.mem_insert_self ..
    have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    cases op
    · exact kw_step goal _ _ a b w (fun _ i => !(a.testBit i)) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => and_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv a b e i h1 h2 h3)
        (fun _ _ _ _ h => h.symm)
    · exact kw_step goal _ _ a b w (fun e _ => a.testBit e) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => or_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv a b e i h1 h2 h3)
        (fun _ _ _ _ _ => rfl)
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
namespace PackedRect
end PackedRect
def DagAuto (mask goal : Word) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal
abbrev WordMoveStep := List (Word × Nat) × List (Word × Nat)
abbrev WordMove := List WordMoveStep
def mixStep (m : WordMoveStep) (w : Word) : Word :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right
def BitLinear (f : Word → Word) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true
theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]
theorem bitLinearOr {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩
theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩
theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩
theorem mixStepLinear (move : WordMoveStep) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih
def mixMove (move : WordMove) (w : Word) : Word :=
  (List.rec (motive := fun _ => Word → Word) id
    (fun step _ next w => next (mixStep step w)) move) w
theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]
theorem bitLinearComp {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩
theorem mixMoveLinear (move : WordMove) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)
theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Word} {move : WordMove}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Word} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩
theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]
theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Word} {move : WordMove}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Word} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩
theorem maskedBelow {mask w : Word} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]
theorem liveMaskedImage {mask goal : Word} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k t : Nat} {S : Finset Word} (live : LiveWord mask goal k t S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveWord mask goal k t (S.image (relabel select)) := by
  let f := relabel select
  have hmask : f mask = mask := auto.2.1
  have inj {a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
      f a = f b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have proper {a : Word} (ma : Masked mask a) (ha : properWord mask a) :
      properWord mask (f a) := by
    exact ⟨fun eq => ha.1 (inj ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (inj ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {S : Finset Word} {v : Word} (hv : v ∉ S) (mv : Masked mask v)
      (ms : ∀ w ∈ S, Masked mask w) : f v ∉ S.image f := by
    intro hw
    obtain ⟨w,hs,eq⟩ := Finset.mem_image.mp hw
    exact hv (inj (ms w hs) mv eq ▸ hs)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton, auto.2.2]
    exact LiveWord.stop hp
  | @unary k t U a ha fresh tail ih =>
    let v := mask ^^^ a
    have ma := masked a (Finset.mem_insert_self ..)
    have mv : Masked mask v := by
      apply maskedGate (bank := [a]) (by simpa using ma)
      exact Or.inl ⟨a, Or.inr (Or.inr (by simp)), rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem hU)
    have fve : f v = mask ^^^ f a := by
      change relabel select (mask ^^^ a) = _
      rw [relabelXor, auto.2.1]
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) (t+1) ((insert a U).image f)
    rw [Finset.image_insert] at ht hf
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht hf
    rw [Finset.image_insert]
    exact LiveWord.unary (proper ma ha) hf ht
  | @binary k t U a b op pa pb ab fresh tail ih =>
    let v := binWord op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply maskedGate (bank := [a,b]) (by simpa using And.intro ma mb)
      exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
        cases op <;> simp [v, binWord]⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have fve : f v = binWord op (f a) (f b) := by
      cases op
      · exact relabelAnd ..
      · exact relabelOr ..
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) t ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveWord.binary (proper ma pa) (proper mb pb) (fun h => ab (inj ma mb h)) hf ht
def dagMoveWords (m : WordMove) (ws : List Word) : List Word :=
  List.rec [] (fun w _ next => insertWord (mixMove m w) next) ws
theorem dagMoveSet {m : WordMove} {ws : List Word} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWords m ws).toFinset = ws.toFinset.image (relabel select) := by
  induction ws with
  | nil => simp [dagMoveWords]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (dagMoveWords m ws)).toFinset = _
    rw [insertWordSet, ih (fun w hw => agree _ (List.mem_cons_of_mem _ hw)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]
abbrev DagLink := Nat × Nat
abbrev DagLinks := Nat → Nat → Option DagLink
def dagRef (count : Nat) (states : Nat → Option RowState)
    (moves : Array WordMove) (links : DagLinks) (parent token : Nat) (state : RowState) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto-1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWords m state.2.1
def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)
theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩
theorem childStateData {mask token : Nat} {state child : RowState}
    (eval : childState mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let a := token / (4 * 3 * 64)
  let b := token / (4 * 3) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let rest := keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega,?_⟩
  have read (i : Nat) : AvailableWord mask ws (ws.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : ws[i]? with
    | none => exact Or.inl rfl
    | some a => exact Or.inr (Or.inr (List.mem_of_getElem? h))
  have hm : Masked mask z := by
    apply maskedGate masked
    unfold z
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inl rfl⟩
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inr rfl⟩
    · exact Or.inl ⟨x,read _,rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (op == 2 || keep.testBit 1) y _ w other
def DagMovesOK (mask goal : Word) (width : Nat) (moves : Array WordMove) : Prop :=
  ∀ (i : Nat) (m : WordMove), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w
abbrev DagMoveRecord (width : Nat) := WordMove × (Fin width → Fin width) × (Fin width → Fin width)
def dagMoves (cert : List (DagMoveRecord width)) : Array WordMove := (cert.map Prod.fst).toArray
def dagMoveRecordProps {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal
def dagMoveRecordOK {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)
theorem dagMoveRecordSpec {width : Nat} {mask goal : Word} {entry : DagMoveRecord width}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok
theorem dagMovesOfCheck {width : Nat} {mask goal : Word} {cert : List (DagMoveRecord width)}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩
theorem dagLinked {mask goal : Word} {width count : Nat} {states : Nat → Option RowState}
    {moves : Array WordMove} {links : DagLinks} {parent token : Nat} {state : RowState}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRef count states moves links parent token state = true)
    {k t : Nat} (live : LiveWord mask goal k t state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveWord mask goal k t saved.2.1.toFinset := by
  unfold dagRef at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination,saved,hd,eq,finish.1,?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select,auto,agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWords m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSet (fun w hw => agree w (masked w hw))]
          exact liveMaskedImage auto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))
def dagLookupLinks (index data indexWidth sizeBits tokenBits destinationBits autoBits trials : Nat) :
    DagLinks := fun parent token =>
  let entry := unpack index indexWidth parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  let width := tokenBits + destinationBits + autoBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option DagLink) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := unpack data width mid
        let key := code &&& ((1 <<< tokenBits) - 1)
        if Nat.beq token key then
          some ((code >>> tokenBits) &&& ((1 <<< destinationBits) - 1),
            code >>> (tokenBits + destinationBits))
        else if Nat.blt token key then next lo mid else next (mid+1) hi
      else none) trials) offset (offset+size)
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
theorem suppliesOfCheck {oldMask : Word} {old new : List Word} {rename : Word → Word}
    (h : new.all (fun w => availableB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvailableWord oldMask old (rename w) := by
  intro w hw
  exact availableB_spec.mp (List.all_eq_true.mp h w hw)
end WordEngine

open WordEngine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Rep9102
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
end Rep9102

open WordEngine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace Rep9102
set_option maxHeartbeats 0 in
def posted (u v : Fin 5) : Bool := decide (u ≠ v)
set_option maxHeartbeats 0 in
def raw : List (BitVec 25) := [0x1f, 0x3e0, 0x7c00, 0xf8000, 0x1f00000, 0x210842, 0x421084, 0x842108, 0x1084210, 0x108421]
set_option maxHeartbeats 0 in
def stock : List Word := raw.map BitVec.toNat
set_option maxHeartbeats 0 in
def target25 : BitVec 25 := 0xfbefbe
set_option maxHeartbeats 0 in
abbrev T : Word := target25.toNat
set_option maxHeartbeats 0 in
def point (r : Fin 25) := oneEach (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 (r.val % 5))
set_option maxHeartbeats 0 in
theorem representation_live (C : Circuit) (legal : Monotone2 C) (right : Represents posted C) :
    ∃ k ≤ C.size, LiveWord (fullMask 25) T k 0 stock.toFinset := by
  let raw : List (BitVec 25) := [0x1f, 0x3e0, 0x7c00, 0xf8000, 0x1f00000, 0x108421, 0x210842, 0x421084, 0x842108, 0x1084210]
  let stock := raw.map BitVec.toNat
  rw [show Rep9102.stock.toFinset = stock.toFinset by decide +kernel]
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
end Rep9102

open WordEngine PEqualNP.Represents
namespace Rep9102.Orbit
set_option maxHeartbeats 0 in
def MonoViable (mask goal : Word) (s : RowState) : Prop :=
  s.2.1.Nodup ∧ ∃ k ≤ s.1, LiveWord mask goal k 0 s.2.1.toFinset
set_option maxHeartbeats 0 in
def AOChild (mask : Word) (s c : RowState) : Prop :=
  ∃ a b op keep, a < s.2.1.length ∧ a < b ∧ b < s.2.1.length ∧ op < 2 ∧ keep < 4 ∧
    childState mask (gateToken a b op keep) s = some c
set_option maxHeartbeats 0 in
theorem binaryMonoProgress {mask fuel k : Nat} {x y target : Word} {d : Bool} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k 0 (insert (binWord d x y) U)) :
    ∃ child, AOChild mask (fuel, ws, history) child ∧ MonoViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := binWord d x y
  have p := liveWordProper tail v (Finset.mem_insert_self _ _)
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep
    cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : RowState := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, if d then 1 else 0, keep, ha, hab, hb, ?_, keepLt, ?_⟩, ?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k 0 (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail
set_option maxHeartbeats 0 in
theorem monoProgress {mask : Nat} {target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : MonoViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child, AOChild mask state child ∧ MonoViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset, eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,impossible,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · omega
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm, same, getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryMonoProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x, Finset.insert_comm]; exact fresh
      have tail' : LiveWord mask target k 0 (insert (binWord d y x) U) := by
        rw [binWord_comm d y x]; exact tail
      exact binaryMonoProgress nd width cap eq' xy.symm (by omega) fresh' tail'
set_option maxHeartbeats 0 in
def coverAt (n : Nat) (ws : List Word) : Word :=
  List.rec 0 (fun w _ acc => if w.testBit n then acc else w ||| acc) ws
set_option maxHeartbeats 0 in
theorem coverAt_bit {w : Word} {ws : List Word} {p n : Nat}
    (member : w ∈ ws) (pos : w.testBit p = true) (neg : w.testBit n = false) :
    (coverAt n ws).testBit p = true := by
  induction ws with
  | nil => simp at member
  | cons x xs ih =>
    change (if x.testBit n then coverAt n xs else x ||| coverAt n xs).testBit p = true
    rcases List.mem_cons.mp member with rfl | tail
    · simp [neg, Nat.testBit_or, pos]
    · cases x.testBit n <;> simp [Nat.testBit_or, ih tail]
set_option maxHeartbeats 0 in
theorem coverAt_live {mask goal : Word} {ws : List Word} {k n : Nat}
    (live : LiveWord mask goal k 0 ws.toFinset) (neg : goal.testBit n = false) :
    goal &&& coverAt n ws = goal := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and]
  cases h : goal.testBit p with
  | false => rfl
  | true =>
    obtain ⟨w,mem,one,zero⟩ := liveDirected live h neg
    simp [coverAt_bit (List.mem_toFinset.mp mem) one zero]
set_option maxHeartbeats 0 in
def basicCut (goal : Word) (neg : List Nat) (s : RowState) : Bool :=
  decide (s.1+1 < s.2.1.length) ||
    neg.any (fun n => (goal &&& coverAt n s.2.1) != goal)
set_option maxHeartbeats 0 in
theorem basicOpen {mask goal : Word} {neg : List Nat} {s : RowState}
    (negative : ∀ n ∈ neg, goal.testBit n = false) (v : MonoViable mask goal s) :
    basicCut goal neg s = false := by
  obtain ⟨nd,k,cap,live⟩ := v
  have size := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at size
  simp only [basicCut, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    List.any_eq_false, bne_iff_ne, ne_eq]
  constructor
  · omega
  · intro n mem
    simp [coverAt_live live (negative n mem)]
set_option maxHeartbeats 0 in
abbrev Table := Nat → Option RowState
set_option maxHeartbeats 0 in
abbrev EdgeCut := Nat → Nat → RowState → Bool
set_option maxHeartbeats 0 in
def pass (m g : Word) (neg : List Nat) (states : Table) (count : Nat)
    (moves : Array WordMove) (links : DagLinks) (cut : EdgeCut) (i : Nat)
    (s : RowState) (a b op keep : Nat) : Bool :=
  let tok := gateToken a b op keep
  match childState m tok s with
  | none => true
  | some c => basicCut g neg c || cut i tok c || dagRef count states moves links i tok c
set_option maxHeartbeats 0 in
def scan (m g : Word) (neg : List Nat) (states : Table) (count : Nat)
    (moves : Array WordMove) (links : DagLinks) (cut : EdgeCut) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some s =>
    let n := s.2.1.length
    dagStateOK m s.2.1 && decide (n ≤ 64) && !(s.2.1.contains g) &&
    treeBlock 0 n (fun a => treeBlock (a+1) (n-(a+1)) (fun b =>
      treeBlock 0 2 (fun op => treeBlock 0 4 (pass m g neg states count moves links cut i s a b op))))
set_option maxHeartbeats 0 in
theorem tableSound {m g : Word} {width count : Nat} {neg : List Nat} {states : Table}
    {moves : Array WordMove} {links : DagLinks} {cut : EdgeCut}
    (mb : Masked (fullMask width) m) (autos : DagMovesOK m g width moves)
    (negative : ∀ n ∈ neg, g.testBit n = false)
    (cutOpen : ∀ i tok s, MonoViable m g s → cut i tok s = false)
    (checked : ∀ i < count, scan m g neg states count moves links cut i = true) :
    ∀ fuel i s, i < count → states i = some s → s.1 = fuel →
      ∀ k ≤ fuel, ¬ LiveWord m g k 0 s.2.1.toFinset := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | ind fuel ih =>
    intro i s hi row cap k fit live
    have h := checked i hi
    simp only [scan, row, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨nd,masked⟩ := dagStateOKSpec h.1.1.1
    rcases monoProgress h.1.1.2 ⟨nd,k,cap ▸ fit,live⟩ with hit | ⟨c,edge,v⟩
    · simpa [hit] using h.1.2
    obtain ⟨a,b,op,keep,ha,hab,hb,hop,hkeep,ev⟩ := edge
    have aa := treeBlock_at h.2 (i := a) (Nat.zero_le _) (by simpa using ha)
    have bb := treeBlock_at aa (i := b) (by omega) (by omega)
    have oo := treeBlock_at bb (i := op) (Nat.zero_le _) (by simpa using hop)
    have kk := treeBlock_at oo (i := keep) (Nat.zero_le _) (by simpa using hkeep)
    simp only [pass, ev, basicOpen negative v, cutOpen _ _ _ v, Bool.false_or] at kk
    obtain ⟨less,cm⟩ := childStateData ev masked
    obtain ⟨_,j,fit',plan⟩ := v
    obtain ⟨dest,saved,inRange,lookup,eq,tail⟩ := dagLinked mb autos cm kk plan
    exact ih c.1 (cap ▸ less) dest saved inRange lookup eq j fit' tail
set_option maxHeartbeats 0 in
def diagonal : List Nat := [0,6,12,18,24]
set_option maxHeartbeats 0 in
theorem lowerFromTable {fuel count root : Nat} {states : Table} {s : RowState}
    {moves : Array WordMove} {links : DagLinks} {cut : EdgeCut}
    (autos : DagMovesOK (fullMask 25) T 25 moves)
    (cuts : ∀ i tok c, MonoViable (fullMask 25) T c → cut i tok c = false)
    (checked : ∀ i < count, scan (fullMask 25) T diagonal states count moves links cut i = true)
    (bound : root < count) (lookup : states root = some s) (budget : s.1 = fuel)
    (bank : s.2.1.toFinset = stock.toFinset) : ¬ RepSizeAtMost posted fuel := by
  rintro ⟨C,legal,size,right⟩
  obtain ⟨k,fit,run⟩ := representation_live C legal right
  rw [←bank] at run
  exact tableSound (m := fullMask 25) (by unfold Masked; decide +kernel) autos
    (by decide +kernel : ∀ n ∈ diagonal, T.testBit n = false) cuts checked fuel root s bound
    lookup budget k (fit.trans size) run
end Rep9102.Orbit

open WordEngine
namespace Rep9102.Geometry
open Rep9102.Orbit
set_option maxHeartbeats 0 in
def forcesAt (goal : Word) (ws : List Word) (w : Word) (p n : Nat) : Bool :=
  goal.testBit p && !goal.testBit n &&
    ws.all (fun v => v == w || !v.testBit p || v.testBit n)
set_option maxHeartbeats 0 in
theorem forcedAnswer {g : Word} {ws : List Word} {w : Word} {p n : Nat}
    {f : Nat → Nat → Word}
    (legal : ∀ p n, g.testBit p = true → g.testBit n = false →
      f p n ∈ ws.toFinset ∧ (f p n).testBit p = true ∧ (f p n).testBit n = false)
    (h : forcesAt g ws w p n = true) :
    g.testBit p = true ∧ g.testBit n = false ∧ f p n = w := by
  simp only [forcesAt, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨mem,on,off⟩ := legal _ _ h.1.1 h.1.2
  have v := List.all_eq_true.mp h.2 _ (List.mem_toFinset.mp mem)
  exact ⟨h.1.1,h.1.2,by simpa [on,off] using v⟩
set_option maxHeartbeats 0 in
def overlap (g : Word) (ws : List Word) (x y : Word) (p n px nx py ny : Nat) : Bool :=
  x != y && forcesAt g ws x p nx && forcesAt g ws x px n &&
  forcesAt g ws y p ny && forcesAt g ws y py n
set_option maxHeartbeats 0 in
theorem overlapImpossible {g : Word} {ws : List Word} {x y p n px nx py ny : Nat}
    (kw : KWPartition g ws.toFinset) : overlap g ws x y p n px nx py ny = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨f,legal,box⟩ := kw
  simp only [overlap, Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨ne,a⟩,b⟩,c⟩,d⟩ := h
  obtain ⟨pos,nnx,xa⟩ := forcedAnswer legal a
  obtain ⟨ppx,neg,xb⟩ := forcedAnswer legal b
  obtain ⟨_,nny,ya⟩ := forcedAnswer legal c
  obtain ⟨ppy,_,yb⟩ := forcedAnswer legal d
  have X := box p nx px n pos ppx nnx neg (xa.trans xb.symm)
  have Y := box p ny py n pos ppy nny neg (ya.trans yb.symm)
  exact ne ((X.trans xa).symm.trans (Y.trans ya))
set_option maxHeartbeats 0 in
theorem tightPartition {m g : Word} {s : RowState} (live : MonoViable m g s)
    (tight : s.2.1.length = s.1+1) : KWPartition g s.2.1.toFinset := by
  obtain ⟨nd,k,fit,run⟩ := live
  have sz := (liveWordSize run).2
  have card := List.toFinset_card_of_nodup nd
  apply kwFromLive run
  omega
set_option maxHeartbeats 0 in
def rectangleReject (g : Word) (s : RowState) (code : Nat) : Bool :=
  let field := unpack code 5
  (s.2.1.length == s.1+1) &&
  overlap g s.2.1 (s.2.1.getD (field 0) 0) (s.2.1.getD (field 1) 0)
    (field 2) (field 3) (field 4) (field 5) (field 6) (field 7)
set_option maxHeartbeats 0 in
theorem rectangleOpen {m g : Word} {s : RowState} (code : Nat)
    (live : MonoViable m g s) : rectangleReject g s code = false := by
  unfold rectangleReject
  by_cases t : s.2.1.length = s.1+1
  · simp [t,overlapImpossible (tightPartition live t)]
  · simp [t]
end Rep9102.Geometry

open WordEngine
namespace Rep9102.Project
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
end Rep9102.Project

open WordEngine
namespace Rep9102.Project
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
end Rep9102.Project

open WordEngine
namespace Rep9102.Project
abbrev Minor := Word × Nat × List Word
def Minor.mask (x : Minor) : Word := x.1
def Minor.low (x : Minor) : Nat := x.2.1
def Minor.raw (x : Minor) : List Word := x.2.2
def Minor.Valid (goal : Word) (q : Minor) : Prop :=
  ¬ maskedFlat q.mask goal ∧ AOLower q.mask q.raw (goal &&& q.mask) q.low
def bankCut (minors : Array Minor) (hint : Nat → Nat → Nat) : Orbit.EdgeCut :=
  fun i tok s =>
    match minors[hint i tok]? with
    | none => false
    | some q => cheapCut q.mask q.low s.1 q.raw s.2.1
theorem bankCut_open {goal mask : Word} {minors : Array Minor} {hint : Nat → Nat → Nat}
    (valid : ∀ q ∈ minors, Minor.Valid goal q) (i tok s) (v : Orbit.MonoViable mask goal s) :
    bankCut minors hint i tok s = false := by
  obtain ⟨nd,k,fit,run⟩ := v
  unfold bankCut
  cases h : minors[hint i tok]? with
  | none => rfl
  | some q =>
    have proof := valid q (Array.mem_of_getElem? h)
    exact Bool.eq_false_iff.mpr (fun pos => cheapCut_sound proof.2 proof.1 nd fit pos run)
end Rep9102.Project

open WordEngine
namespace Rep9102.Project
def geometryOrMinor (minors : Array Minor) (hint : Nat → Nat → Nat) : Orbit.EdgeCut :=
  fun i tok s =>
    let code := hint i tok
    if code < 16 then bankCut minors hint i tok s else Geometry.rectangleReject T s (code - 16)
theorem geometryOrMinor_open {mask} {minors : Array Minor} {hint : Nat → Nat → Nat}
    (valid : ∀ q ∈ minors, Minor.Valid T q) (i tok s) (v : Orbit.MonoViable mask T s) :
    geometryOrMinor minors hint i tok s = false := by
  simp only [geometryOrMinor]
  split
  · exact bankCut_open valid i tok s v
  · exact Geometry.rectangleOpen _ v
end Rep9102.Project

open WordEngine
namespace Rep9102.Orbit
abbrev requiredTests (width : Nat) (goal : Word) (ws : List Word) : Prop :=
  ∀ w ∈ ws, ∃ p n : Fin width, goal.testBit p.val = true ∧ goal.testBit n.val = false ∧
    ∀ v ∈ ws, v.testBit p.val = true → v.testBit n.val = false → v = w

theorem lowerStock {m goal width fuel root count raw} {states : Table} {row : RowState}
    {neg : List Nat} {moves : Array WordMove} {links : DagLinks} {cut : EdgeCut}
    (all : ∀ w ∈ raw, Masked m w) (proper : properWord m goal) (needs : requiredTests width goal raw)
    (mb : Masked (fullMask width) m) (autos : DagMovesOK m goal width moves)
    (negative : ∀ n ∈ neg, goal.testBit n = false)
    (cutOpen : ∀ i tok s, MonoViable m goal s → cut i tok s = false)
    (checked : ∀ i < count, scan m goal neg states count moves links cut i = true)
    (index : root < count) (look : states root = some row) (rFuel : row.1 = fuel)
    (exactStock : row.2.1.toFinset = raw.toFinset) : AOLower m raw goal (fuel+1) := by
  intro vs builds hit
  by_contra! h
  obtain ⟨k,S,budget,live,sub⟩ := extractAO all builds hit proper
  have eq : S = raw.toFinset := by
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub _ hw)
    · intro hw
      obtain ⟨p,n,yes,no,only⟩ := needs _ (List.mem_toFinset.mp hw)
      obtain ⟨v,hv,a,b⟩ := liveDirected live yes no
      exact (only v (sub v hv) a b) ▸ hv
  rw [eq,←exactStock] at live
  exact tableSound mb autos negative cutOpen checked fuel root row index look rFuel k (by omega) live
end Rep9102.Orbit

open WordEngine
namespace Rep9102.CompactMoves
abbrev RawMove := WordMove × Nat × Nat
def rawMove (code : Nat) : RawMove := Id.run do
  let mut left := Array.replicate 25 0
  let mut right := Array.replicate 25 0
  let mut select := 0
  let mut inverse := 0
  for s in [:25] do
    let r := unpack code 3 (s/5)
    let c := unpack code 3 (s % 5)
    let d := if code.testBit 15 then 5*c+r else 5*r+c
    if s ≤ d then left := left.modify (d-s) (· ||| (1 <<< s))
    else right := right.modify (s-d) (· ||| (1 <<< s))
    select := select ||| (s <<< (5*d))
    inverse := inverse ||| (d <<< (5*s))
  let parts := fun (a : Array Nat) => (List.range 25).filterMap (fun n =>
    if a[n]! == 0 then none else some (a[n]!,n))
  return ([(parts left,parts right)],select,inverse)
def rawList (count packed : Nat) : List RawMove :=
  (List.range count).map (fun i => rawMove (unpack packed 16 i))
def record (r : RawMove) : DagMoveRecord 25 :=
  (r.1,fun i => Fin.ofNat 25 (unpack r.2.1 5 i.val),fun i => Fin.ofNat 25 (unpack r.2.2 5 i.val))
end Rep9102.CompactMoves

open WordEngine

namespace Rep9102.SmallCrown

open Orbit

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def records : List (DagMoveRecord 25) := (CompactMoves.rawList 29 0x440bc443405ac21a421ac0ca460ac2c242c2c6424642c0d140d1c6114611c4c144c1c6814681c298c4584458c2d042d0c6504650c4c844c8c688).map CompactMoves.record
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def mask : Word := 0x7bdef

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def goal : Word := 0x3adae

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def raw : List Word := [15,480,15360,33825,67650,135300,270600,491520]

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def neg : List Nat := [0,6,12,18]

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem autos : DagMovesOK mask goal 25 (dagMoves records) := dagMovesOfCheck (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def hullCode (i : Nat) := unpack 0x640cd92c8263e42044c463e42044c363e42044a363e42044a263c0d9286263c0d92841620cd92c61620cd92c406140b328836140b328626140b328416140b32820614013284160e4a034e160e4a034c160e4a034c060e4a034a460e4a034a060e4a0348060e42034a460e42034a360e420348360e420346260ccd9286160ccd9284160ccd9284060ccd9282060ccd9042060c0d9286260c0d9284160c0d9282060c089146260c0891441604cd92820604ca02ca2604ca02c81604ca02c61604ca02c60604ca02c40604c502c606040b328626040b328616040b328416040b328406040b3282060407328413458891cc23458891cc13458891ca13458891ca03458891c8034583908c234583908a13458390862345839084133e41040e433e41040c333e41040c233e41040a133c089148233c089148133647620c133647620c033647620a03364160c603358891ca23358891c823358891c813358891c803358891c623358891c613358891c603358891c41335839286133583908a23358390862335839086133583908413358390440335839042033581908203298501c203298102ca33298102c82328076148232807614813280761461328076146032807614413280761440328076142030e45020e130e45020e030e45020c030e41040a230e410408130e41020a230d889044130d889042030c089146130c089144130c089144030c08914203098501cc13098501cc03098501ca13098501ca03098501c813098501c803098102ca43098102c833098102c623098102c413098101c833098101c623098101c413080761461308076146030807614413080761440308076142004583908c104583908c004583908a0045839088204583908610424533d040424533ce30424533ce20424133ca0040c3904a1040c3904a0040c390480040c390462040c3904600364260ce10364260ce00364260cc00364260c800358f92861035839288103583928600358390861035839084002d85328c302d85328a202d81328a102cca6048302cca6046202cca6044102cca6042002cc2604a102cc2604a002cc26048302cc26048102cc26048002cc26046202cc26046002cc26044102cc2604200224533cc20224130cc00224130ca10224130ca00218390420020c390462020c390441020c39042001d85328a301d85328a201d853288201d85308a301d813288101d813286101d813286001d813284001d81308c101d81308c001d81308a201d81308a001d813088101d813088001d813086101d813086001d813084001cca6148201cca6146201cca6146101cca6046201cca6046101cca6044101cca6044001cc26148201cc26048101cc26048001cc26046201cc26046101cc26046001cc26044101cc26044001cc260420 40 i

def smallBank (header entries i : Nat) : Option RowState :=
  let h := unpack header 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack entries 20 (h/256+j)), [])

def state0 := smallBank 0x3b9932992999209917990f890879008a 0x780004210821084108420842103c00001e00000f00001780004210821084108420842103c00001e00000f00002780004210821084108420842103c00001ef001e00000f780004210821084108420842f0842103c00001e00000f7800042108210841084f108420842103c00001e00000f780004210821084108420842f03c00001e00000f780004210821084108420842f03c00001e0780004210821084108420842103c00001e00000f

def edge0 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x9a1288a378a063aa522332bf1c2d0038 0x3101566310156506335642e0094e310094d043294c1800642310064100326406100336740033500303342d000662d0005a2d0004e1700042300002a300001e4f015664f0156511215644f00c41410094e4f0094d0f2094c4f006424f006410b2264072003427400341002e340610033674003350122334950031e4d000664f0006502280644d0005a4f000590e28058400004e4f0004d0c2804c4e000364f000350c260344e0002a4f000290028028170001e4f0001d002601cc001566c001565022d564380094e4a0094d002c94c4400666440065a30006562d0064e450064abf00642170063ea6006363000632300062abf00366bf0035abf0034ebf00342c0003410b1e3409a003324a0032abf00066bf0005abf0004e950003ea600036c000035001e0344a0002a6101566610156511195645f00c663000c625f00c5a3100c566d00c4e4600c4a6100c424f00c3e5f0096673009625f0095a6d0094e61009426d0064e610064d0f1864c6100635300063161006298c00625bb00342a6003410b18340a6003353000331a6003299a003255e000665e0005a61000566c0004e990004a6000042610003e610002674000250030024600001ea6000127201566720156511175644400f663000f624400f5a3100f562d00f4e4600f4a7200c667200c5a7200c4e6100941310093d700064e720064d0f1664c2d00641450063d7200635bf00341300033dbe00336bf003350c1a3346f000666f0005a6f0004e72000327400031002e030600002a7200029001a028710001e720125b062b25a0625259111525872012577200f5b7200f577200f4f7200c5b7200c577200c4f7200c435f0095b73009575f0094f740094b6d00943740093f61009377400933720065b720064f730064b72006430424642042a6410f14640730063f72006377300633610062b8c00627bf0035bbf0034f740034bbf003438d0033fbf003370024336002a3350b143347400333a60032b9a003274a0031f720005b061e05a720004f061a04e740004b072204a7200043041a042740003f052203e7200037001a03674000330122032730001f041e01ec000013001e0120618f4f0614f4e0714f4d0612f4c1132f4b0916c4f0920c4b1a2cc43031694f032094b162c943142c937061c64f062264b071c643072263f051c6370522633011c62b0122627192c34f0816343082033f04183370514336041433504123340f32333011632b0120327041c31f042231b152c04f0216043022003f00160370020033001802b011402a001402900120280b32027001c01f002201b132c013110b25b110725a1207259110525811112571a08f5b1a0ef571a0cf4f1608c5b160ec57160cc4f140cc43070895b070e957070c94f050c943010c937190c65b190864f190e64b0f0a64310066420f066410f046400f1063f1408637140e633050862b050e627150c35b150834f150e34b1308343130e33f0b0a3370c063360b063350b043340b10333010832b010e327130c31f060c05b060804f060e04b0408043040e03f0008037000e033000a02b010602a000602900040280010027040c01f000c013 16 7 13 7 8 8 (i % 8) tok

def state1 := smallBank 0x35882d8825881d8815880d8806780068 0x780004210821084108420842f03c00001e000080780004210821084108420842f03c00001ef001e078000421082108410842085ef0842f03c00001e07800042108210841084f108420842f03c00001e0780004210821084109e2108420842f03c00001e07800042108211e421084108420842f03c00001e0780004210821084109e20842f03c00001e0780004210821084109e20842f03c00

def edge1 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x709d6498569c499a38232a1c11320022 0x650125a650125906452586500c416400642650064117646409e00342a000341005e3409e00336a0003351464334a90031e630005a6500059055a058630004e650004d005a04c63000366500035054c0346b0002a65000290052028530001e650001d004c01ca00125aa001259025d25834006423500641005c640630035a630034e540034a5100342650033e9e003365400332a50032a5f00326530031e9e0005a9e0004e9e000429e00036a00003500460349800026350001ea50125aa501259024b258630095a5300956630094e540094a5100942650093eba009365400932a40065aa40064ea40064276003429100341004a34051003295300325910031da30005aa30004ea300042b900036a5000350042034a50001a91000126f0125a6f01259113d2586f00c5a5100c566f00c4e5400c4a5100c427200c3e6f0095a6f0094e6f009425e00635720063172006256e003426f003410f3c340510033553003316f003299e0003554000319c0002a9e0002900400289e0125a9e01259063b2589e00c5a5100c569e00c4e5400c4a9e00c426500c3e9e0095a9e009569e0094e9e00942ba006359800631ba00629bf0062536003421600341043a340160033553003311600329ac003259c0005a9c0004e9e0004a9c000429e0003e9e00026a0000250b6a024b90001e9e0001a16000129e0125a9e0125906392589600f5a5100f569600f4e5400f4a9e00c5a9e00c4e9e00941540093d5100641980063da4006352c00341530033d2a003362c00335053c3349c0005a9c0004e9e00032a000031005e0309c0002a9e00029003c028a30001e9e00f4f0254f4e0248f4d0636f4c9e00f4b9e00c4f9e00c4b9e00c439e0094f9e0094b9e00943a00093f9e00937a000933a40064f9f0064ba400643a00063fa400637a000633ba0062bac006272c0034f2c00343a00033f2c00337004833600543350436334a000333160032bac00327910031fc90031b9e0004f155c04e9e00043023c042a00003f166403e9e00037003c036a0000331464032a50001f004201ea00001b006201a2f00013135c012023ac430236c420336c410234c40116cc3f0138943014493f1a68937154a643156463f164a6371664633144a62b1464627064a343066433f074a3370764333054a32b0564327003e31f006031b196804300380370044033003a02b013602a003602900340280f6c027134a01f136401b044a013046400f 16 7 13 7 8 8 (i % 8) tok

def state2 := smallBank 0x38883088288820881888108808880088 0x780004210821084108420842f03c00001e0000017800042108210841084f0842103c00001e000002780004210823c841084208421001ef001e00000f780004210821084109e20842f03c00001e00000f780004210821084108420842103c02001e00000f780004210821084108420842103c00001e20000f780004210821084109e2108420842f03c000000f780004210821084108420842f03c00001e000020

def edge2 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x4e8f4396369a2a1921911a8e0c9c0019 0x540125a5401259066b25852006425400641046a6409e00336a000335006a334510005a510004e51000425100036530001ea000012720125a7201259115f2585f00935700064272006410f5e640bf003356f0005a720005902500586f0004e720004d0e5004c6f0004272000410c500407200029710001e720001d005001c7200011200125a20012590069258420065a420064e2d0064a2b00642440063e1f0063615006325b0062a2d006261e0035a1e0034e48003421f0033620003350b5c33487003261e0005a1e0004e48000427e000325b0002a2000029005c028bf0125abf012591155258370064249006410f54640be0035abe0034ebf0034abe00342bf0033ea50032ac400326490031ebe0005abe0004ea00004abe00042a00003e9e00036bf000321d0001ea000012bf0001100460104d0125a4d01259185b2584d009353f006424d006410f526404d003364d003350b4e3346f00036720003500500345e0002a720002901580289400012150125a1501259114d2580000935270064215006410f4c64015003361500335006633472000355e0002a72000290156028be0125abe012591149258be0095abe00956be0094ebe00942ba00629bf006250d003420f003410f483400e00329c400325bd0005abd0004e9e0004abd000429e0003e9c00036be000329c0002abe000290040028be00026bf0002501620240800012980125a980125902652588b00642980064100646409e00336a0003350062334a50032a960005a9800059024e058960004e980004d025804c8a0004298000410058040970003698000350056034970001e980001d004e01c 16 7 13 7 8 8 (i % 8) tok

def state3 := smallBank 0x2f77287721771a7713770d6708570088 0x780004210821084109e21084f0842f03c0078000421082108418def109e20842f03c007800042108211e421084109e20842f03c00780004210823c8421084109e20842f03c007800043d084210821084109e20842f03c00780004210823c84109e20842f03c00780004210823c84109e20842f780004210821084109e20842103c000000f00001

def edge3 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x541247993d942f9c251512a50717000e 0x9c00f4e9c00f4d1176f4c9c0064e9c0064a9c006429e0063e9c006369e006329c0062a9c00626b70031dbe0031909000360b000350f760349c0001dab00019b900f4ec800f4d0278f4cb60094e9c0094a22009429e0093e9c009369e00932b60064ec700642b700636b60034ec700342b700336b10031ac20031900a0318b800036c80003500780349c000290500025c80001dc8000119c00f4e9c00f4d0674f4c9c00c4e9c00c4a9c00c429e00c3e9c0094e9c009429c006359e006319e006259c003359e00331a20032902000359e00031000002a020002900760280200f4e0200f4d0272f4c0200c4e9c00c4a0200c429e00c3e020094e020094a02009422600635ab0063126006292c006256800335c20033168003290c00325000004e0000042020003e020002605000250fa6024250001e020001a6800012020000e0200f4e9c00f4a0200c4e0200c4d0374c4c02009419e0093dc100641ab0063d1200635aa00341c20033d560033502000320500031008e030000002a02000290074028110001e56000120200c430084c420086c410370c400200c3f0200943020093f020093705009331200643040063f12006370500633260062b23006275600343050033f56003370500333680032b2300327c80031f4c0031b0200043199c0420200037007403605000331aa4032140001f137a01e050001b13a201a5700013047a012050000f04a200e007293701709360070935006e93411a8933199663719a46331a9662b1aa4627159633715a4333169632b16a4327137831f139e31b069603706a4033079602b07a4027047801f049e01b0078013009e00f070125a0701259026d25804006420700641006c640a50032abf00329006a328030005a030004e03000421500036060001e 16 7 13 7 8 8 (i % 8) tok

def state4 := smallBank 0x31772a7723771c7715770e7707770077 0x7800042108210841084f0842103c02001e0780004210821084108420842f03c20001e0780004210821084108420842f03c80001e0780004210823c8410842085ef0842f001e0780004210823c8421084109e20842f001e0780004210821084109e20842f03c00001ef780004210821084109e20842f03c0002000780004210821084109e2085ef0842f03c00

def edge4 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x3e88398a340b29951e1716100a970015 0x6f00f4e6f00f4d188cf4c5c006296e003366f003350f82334bc000299600f4e9600f4d0098f4c8900336960033500943349c0002a9e00029007e028a10001e5100f4e5100f4d0a88f4c770093550003365100335048a3349b000359c0002a9e0002914920285a00f4e5a00f4d0096f4c620064e510064a6200642520063e50006366300632b50062a5200626590034e59003428f00336590004e59000428f00036b50002a5a00029007a028860000e2a00f4e2a00f4d0686f4c2a0094e2a0094a2a009421b006292c0062559003293400325290004e2900042020003e00000362a00032000002a2a0002900760282a000262c0002514a20247500012020000e9e00f4e9e00f4d0290f4c3300336340033500903349c0004e9c000429e0003e9c000369e000329c0002a9e00026a30001ec30001a9d000129e00f4e9e00f4d1ba4f4c9e00c41020034e02003420500341008e340020033605003351aa43349c0004e9e0004d038804c9c000369e0003500880349c0002a9e000290b80028a30001e9e0001d008001ca300f4ea300f4d027af4ca20064e9d0064aa2006429e0063e9c006369e00632b70062a9e00626a20034ea200342a200336b00032675000369000035007a0349c0001dc2000199000011 16 7 13 7 8 8 (i % 8) tok

def state5 := smallBank 0x31772a7723771c7715770e7707770077 0x780004210821084109e20842f03c00000227800042108211e4108420842f03c0000080780004210823c84108420842f001ef001e0780004218821084108420842f03c00001e07800042108210a4108420842f03c00001e0780004210821084108620842f03c00001e0780004210823c84109e20842f03c00001e078000421082108410842084af03c00001e0

def edge5 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x33952b9022131b0e160a110a0714000e 0xab00f4eab00f4d029ef4cb10062ac20062900a06283c003364c00335009e334aa0004eab0004d027c04caa00042ab00041037c040aa00036ab00035017c0344c00012ab00011007c0109e00f4e9e00f4d068ef4c9e009352c003359c0004e9e0004d058c04c9c000429e00041008c0409e00029a30001e9e0001d008201c9e000113400f4e3400f4d009cf4c620034e6200342520033e500033664003321c0032a52003265a0031e5d0031a330004e330004233000361c0002a34000290090028850001a6300f4e6300f4d1180f4c6300935620033663003351d9a3349c000369e00035008c0349c0002a9e000291c98028a8000129600f4e9600f4d009af4c8900336960033500943349c0002a9e000290c7e028a30001e9600f4e9600f4d0292f4c8900336960033500923349c0002a9e00029008a028a30001e2c00f4e2c00f4d0684f4c2a0034e2a003422c0033e140032a4300326900031e2c0031a2a0004e2a00042050003e02000362c00032900001e050001a05000122c0001113900106300f4e6300f4d0680f4c63009356200336630033517943349c000369e0003500820349c0002a9e000291494028a800012 16 7 13 7 8 8 (i % 8) tok

def state6 := smallBank 0x2e562a4623771c7715770e7707770077 0x7a1084210823c84109e20842f7a10823c84109e20842f780004210823c84109e2084210000f00001780004210821084109e20842f03c00000017a10823c841084208421001ef001e00000f780004210821084109e20842103c000000f780004210823c84108420842f001e000020780004210821084109e20842f03c0000020

def edge6 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x31982b8c268a210b1714128909130012 0x6370000633000062b1aba62902006271aca62510003370100333100032b16ba329020032716ca325470031f220031b55000370200033550002b07ba029020002707ca0258e0001f220001bc6000133a0000f19b862b19c862715b832b15c832713b831f13c831b06b802b06c802704b801f04c801b00b801300c800f0400f4e0400f4d00a8f4c050031e0e0031d00a631c010004e01000420100036130002a9e00f4e9e00f4d02a6f4c0200336050033500a63349c0004e9c000429c000369c0002a0500012420064e2d0064a2b00642440063e1f0063615006325b0062a2d006261e0034e28003421f0033620003350b9c33487003261e0004e28000427e000325b0002a2000029009c0280300f4e0300f4d158af4c01003360300335138a334a30001ebe0001d008a01c8500f4e8500f4d00a4f4c140032a2c0032900a2328860031e810004e850004d029804c81000428500041029a040890003685000350094034840002a850002900920289e00f4e9e00f4d02a2f4c0200336050033500a23349c0004e9e0004d027e04c9c000429e000410e7e0409c000369e000350c7e03405000129e00011007e010 16 7 13 7 8 8 (i % 8) tok

def state7 := smallBank 0x2a6624661e66186612660c6606660066 0x780004210821084109e20a42f03c00780004210821084109e20842f03c20780004210821084109e20842f03c22780004210823c84109e2085ef0842f780004210823c8418def109e20842f780004210823c84211e4109e20842f7800043d084210823c84109e20842f7a108780004210823c84109e20842f

def edge7 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x300b2d062889210f1812118d0a8e0015 0x9c00c429c00c411bc4c409c0093500000420000036020003500ac034000002a02000291ac40289c00c429c00c4100bec40000002a020002900b0028aa00c42aa00c4103b4c40af0031ec10031d00bc31c3b0002a4b0002900ae0285900c425900c4100bac402100342020033e21003360200332000032a2200326b30031e120031a580004258000368e0002a7c0001ab400c42c600c4100b8c402100642000063e21006360200632000062a2200626b200342c5003360baa32ab200042c50003600aa02a7d0000e830000d00c600c0000c420000c4106b2c400000642000063e00006360200632000062a0000626190031d2a00319000001d0a000190000c420000c3e0000942000094100b29400000635020063102006251000335020033110003293900035020003155000290000932000093111cc9300000641000063d00006350000631000062902006251000341010033d10003350100331100032902003255500041020003d5500035020003155000290200025 16 7 13 7 8 8 (i % 8) tok

def state8 := smallBank 0x2a6624661e66186612660c6606660066 0x780004210823c84109e20842f001ef7800043d0821084109e20842f020007800042188211e4108420842f03c00780004210821084109e20842f03c00780004210823084109e20842f03c007a1084210823c84109e20842f03c007a1087800023c84109e20842f03c007800042108211e410842084af03c00

def edge8 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x218c1c8a1a05170613080a12028f0005 0x3300c423300c4100c0c40320004232000360200032000002a33000261a0001e120001a59000123d0000e0200c42020093502000410200029110001e020001d0bac01c5600012020001100ac0109c00c429c00c4111acc409c006292a000299c00c429c00c4102b6c40000002a020002900b60289c00c429c00c411bc2c4000000420000036000002a020002900b60280200935050093112006350500631560033505003310000042020003e0000036020003500b2034020003205000311aca030110001e020001a5600012020000e0200935020093112006350400631560033505003310000042020003e0000036020003519c0034110001e020001a5600012020000e9c00c429c00c4106acc409c006292a00029 16 7 13 7 8 8 (i % 8) tok

def state9 := smallBank 0x2a6624661e66186612660c6606660066 0x78000421082108418def03c0000022780004210823c84109e20842f000227a10823c84108420842f001ef001e07a108210a4108420842f03c00001e07a10821084108420842f03c20001e07a10823c8410842085ef0842f001e0780004210823ca4108420842f001e0780004210823c84108620842f001e0

def edge9 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x23921c0f150e11870e07070e03870007 0xb000c42b000c4102c6c407f0032a930032900c6328a700042b00004102bc040a700036b00003503bc034ae0002ab00002901bc0289300012b00001100bc0103a00c423a00c4100c8c407d0031e830031d00c631c39000423a0004101b404039000363a0003500b40343e0002a3a0002900ae0286200342520033e500033664003321c0032a52003265a0031e5d0031a330004233000361c0002a340002900c0028850001a8900336960033500c43349c0002a9e000290cbe028a30001e8900336960033500c43349c0002a9e0002900be028a10001e6200642510063e50006366300632b50062a520062659003426a0033659000426a00036b50002a5a0002900ba028860000e8100c428100c4100c4c40110001e2a0001d00b001c82000128100c428100c4100c2c40110001e2a0001d00b601c8200012 16 7 13 7 8 8 (i % 8) tok

def state10 := smallBank 0x285523551e55186512660c6606660066 0x780004210823ca4109e20842f780004210823ca6109e20842f7800043d0821084109e20a42f78000421082bcaf23c8418def109e27a10823c84109e2084210000f00001780004210823c84109e20842f000017a10823c84108420842f001e000020780004210823c84109e20842f00020

def edge10 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x198316861582130510060c87060d000c 0x936000093500d89343900936390093500d69347b00012800001100d00100000936000062900d4c40210032467003187b0002400ce01c050031e0e0031d00cc31c01000420100036130002a0200c420200c4100ccc4000000420000036000002a110001e140032a2c0032900ca328860031e8100042850004102c40408900036850003500c4034840002a850002900c20280200c420200c4100cac400000042020004102be040000003602000350ebe034000002a020002900b0028 16 7 13 7 8 8 (i % 8) tok

def state11 := smallBank 0x23551e55195514550f550a5505550055 0x7a10823c84109e20842f001ef7a10821084109e20842f03c2078000421082108418def03c227a10823c84109e2085ef0842f7a10823c8418def109e20842f780004210823c84109e20842f780004212a23c84109e20842f7a10843d0823c84109e20842f

def edge11 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x1708158312860e09088b070304060008 0x32000360200032000002a33000261a0001e120001a59000123d0000e000002a020002900d8028ad00936ad0093503d29347a0001e920001d00d001c21003360200332000032a2200326b30031e120031a5800036690002a7c0001a21006360000632000062a22006260dd43360bd432a02d403600d402a7d0000e830000d00dc00c0000936000093500da9343900936390093502d69347b00012800001100d201000009360000932000062902006251000329020032539000290200025 16 7 13 7 8 8 (i % 8) tok

def state12 := smallBank 0x23441e54195514550f550a5505550055 0x780004210823ca618def780004210833de62bcaf18def7a10823c84109e20842f000017a10823c84109e20842f000207a10823c84109e20842f00022780004210823c8418def000227a10823ca4108420842f001e07a10823c84108620842f001e0

def edge12 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x1503130411830e860a09040c02040004 0x790062a790062900e062800de93479003186600018240000c0000036000002a110001e0000036020003502d8034000002a020002900d80287d0031e830031d00dc31c39000363a0003502d60343e0002a3a0002900d60287b009367b0093500dc93478000367b0003501d2034780002a7b0002900d2028880001e7b0001d00d001c110001e2a0001d00d801c8200012110001e2a0001d00da01c8200012 16 7 13 7 8 8 (i % 8) tok

def state13 := smallBank 0x1d331943154411440d44094404540044 0x7a10823ca618def7a10833de62bcaf18def7a10823c8418def000227a10823c84109e20842f7a10823ca4109e20842f7a10823ca6109e20842f7a1082bcaf23c8418def109e2780004212a23c8418def

def edge13 (i tok : Nat) : Option DagLink :=
  dagLookupLinks 0x9800803050605000500038301840003 0x79003186600018240000c780002a7b0002902e0028880001e7b0001d00e001c7b00012800001100e0010210032467003187b0002400de01c780062a780062902e0628 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def states (i : Nat) : Option RowState := (if i < 56 then (if i < 24 then (if i < 8 then state0 i else (if i < 16 then state1 i else state2 i)) else (if i < 40 then (if i < 32 then state3 i else state4 i) else (if i < 48 then state5 i else state6 i))) else (if i < 80 then (if i < 64 then state7 i else (if i < 72 then state8 i else state9 i)) else (if i < 96 then (if i < 88 then state10 i else state11 i) else (if i < 104 then state12 i else state13 i))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge (i tok : Nat) : Option DagLink := (if i < 56 then (if i < 24 then (if i < 8 then edge0 i tok else (if i < 16 then edge1 i tok else edge2 i tok)) else (if i < 40 then (if i < 32 then edge3 i tok else edge4 i tok) else (if i < 48 then edge5 i tok else edge6 i tok))) else (if i < 80 then (if i < 64 then edge7 i tok else (if i < 72 then edge8 i tok else edge9 i tok)) else (if i < 96 then (if i < 88 then edge10 i tok else edge11 i tok) else (if i < 104 then edge12 i tok else edge13 i tok))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def links (i tok : Nat) : Option DagLink := do
  let (d,a) ← edge i tok
  if d == 0 then none else some (d-1,a)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def cut (i tok : Nat) (s : RowState) : Bool :=
  match edge i tok with
  | some (0,code) => Geometry.rectangleReject goal s (hullCode code)
  | _ => false
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem cutOpen (i tok s) (h : MonoViable mask goal s) : cut i tok s = false := by
  unfold cut
  split
  · exact Geometry.rectangleOpen _ h
  · rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def check := scan mask goal neg states 112 (dagMoves records) links cut

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b0to28 : treeBlock 0 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b28to56 : treeBlock 28 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b0to56 : treeBlock 0 56 check = true := treeBlock_merge (left := 28) (right := 28) b0to28 b28to56

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b56to84 : treeBlock 56 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b84to112 : treeBlock 84 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b56to112 : treeBlock 56 56 check = true := treeBlock_merge (left := 28) (right := 28) b56to84 b84to112

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b0to112 : treeBlock 0 112 check = true := treeBlock_merge (left := 56) (right := 56) b0to56 b56to112

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem lower : AOLower mask raw goal 11 := by
  apply lowerStock (width := 25) (root := 0) (fuel := 10) (row := (10,raw,[]))
    (stockMaskedOfCheck (by decide +kernel)) (by unfold properWord; decide +kernel)
    (by decide +kernel) (by unfold Masked; decide +kernel) autos
    (by decide +kernel : ∀ n ∈ neg, goal.testBit n = false) cutOpen
    (fun i hi => treeBlock_at b0to112 (Nat.zero_le i) (by simpa using hi))
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
end Rep9102.SmallCrown

open WordEngine
namespace Rep9102.Subfloor
open SmallCrown

def rawOn (m : Word) := Rep9102.stock.map (· &&& m)
def dropMask (v : Fin 5) : Word :=
  (![0x1ef7bc0,0x1def41d,0x1bd837b,0x1705ef7,0x7bdef] : Fin 5 → Nat) v
def omitRowMask (v : Fin 5) : Word :=
  (![0x1ffffe0,0x1fffc1f,0x1ff83ff,0x1f07fff,0xfffff] : Fin 5 → Nat) v
def omitColMask (v : Fin 5) : Word :=
  (![0x1ef7bde,0x1def7bd,0x1bdef7b,0x17bdef7,0xf7bdef] : Fin 5 → Nat) v

private theorem mapLower {m n target low roots bank} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (andG : ∀ a b, f (a &&& b) = f a &&& f b) (orG : ∀ a b, f (a ||| b) = f a ||| f b)
    (supply : ∀ a ∈ roots, AvailableWord n bank (f a)) (lower : AOLower n bank (f target) low) :
    AOLower m roots target low := by
  have av {roots bank} (src : ∀ a ∈ roots, AvailableWord n bank (f a)) {a}
      (h : AvailableWord m roots a) : AvailableWord n bank (f a) := by
    rcases h with rfl | rfl | h
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ h
  intro vs built hit
  have mapBuilt {ws roots bank} (src : ∀ a ∈ roots, AvailableWord n bank (f a))
      (b : AOBuild m roots ws) : AOBuild n bank (ws.map f) := by
    induction ws generalizing roots bank with
    | nil => trivial
    | cons w ws ih =>
      obtain ⟨⟨a,b,ha,hb,op⟩,tail⟩ := b
      refine ⟨⟨f a,f b,av src ha,av src hb,?_⟩,ih ?_ tail⟩
      · rcases op with rfl | rfl
        · exact Or.inl (andG _ _)
        · exact Or.inr (orG _ _)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun _ h => Or.inr (Or.inr (List.mem_cons_of_mem _ h))) (src _ hx)
  rw [← List.length_map (f := f) (as := vs)]
  apply lower (vs.map f) (mapBuilt supply built)
  apply av _ hit
  intro w hw
  rcases List.mem_append.mp hw with hv | hr
  · exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_map_of_mem hv)))
  · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_append_right _ hx))) (supply _ hr)

private def gather : List Nat → Word → Word
  | [], _ => 0
  | j::js, w => Nat.bit (w.testBit j) (gather js w)

private theorem gatherGates (js : List Nat) (x y : Word) :
    gather js (x &&& y) = gather js x &&& gather js y ∧
    gather js (x ||| y) = gather js x ||| gather js y := by
  induction js with
  | nil => simp [gather]
  | cons j js ih => exact ⟨by simp [gather,Nat.land_bit,ih.1], by simp [gather,Nat.lor_bit,ih.2]⟩

private def slots (v : Fin 5) : List Nat :=
  (List.range 19).map fun j =>
    let skip := fun a => if a < v.val then a else a+1
    if j % 5 = 4 then 25 else 5*skip (j/5) + skip (j % 5)

theorem allFour (v : Fin 5) : AOLower (dropMask v) (rawOn (dropMask v)) (T &&& dropMask v) 11 := by
  have ok := (by decide +kernel : ∀ i : Fin 5,
    let f := gather (slots i)
    f 0 = 0 ∧ f (dropMask i) = SmallCrown.mask ∧ f (T &&& dropMask i) = SmallCrown.goal ∧
    (rawOn (dropMask i)).all (fun w => availableB SmallCrown.mask SmallCrown.raw (f w)) = true) v
  obtain ⟨zero,ones,goalEq,cover⟩ := ok
  exact mapLower _ zero ones (fun a b => (gatherGates _ a b).1) (fun a b => (gatherGates _ a b).2)
    (suppliesOfCheck cover) (goalEq ▸ SmallCrown.lower)

private abbrev removesPort (m s : Word) : Prop :=
  ∃ p n : Fin 25, (T &&& m).testBit p.val = true ∧ (T &&& m).testBit n.val = false ∧
    ∀ w ∈ rawOn m, w.testBit p.val = true → w.testBit n.val = false → maskedFlat s w

private def lineMask (row : Bool) (i : Fin 5) := if row then omitRowMask i else omitColMask i

theorem line12 (row : Bool) (i : Fin 5) :
    AOLower (lineMask row i) (rawOn (lineMask row i)) (T &&& lineMask row i) 12 := by
  let m := lineMask row i
  let s := dropMask i
  have properties := (by decide +kernel : ∀ r : Bool, ∀ v : Fin 5,
    let m := lineMask r v
    let s := dropMask v
    (rawOn m).all (fun w => w &&& m == w) = true ∧
    (T &&& m ≠ 0 ∧ T &&& m ≠ m) ∧
    ¬ maskedFlat s (T &&& m) ∧ (T &&& m) &&& s = T &&& s ∧
    (rawOn m).all (fun w => availableB s (rawOn s) (w &&& s)) = true ∧ removesPort m s) row i
  obtain ⟨masked,proper,nonflat,restrict,sources,p,n,pos,neg,sep⟩ := properties
  intro vs built hit
  obtain ⟨k,S,budget,live,sub⟩ := extractAO (stockMaskedOfCheck masked) built hit proper
  obtain ⟨w,hw,yes,no⟩ := liveDirected live pos neg
  have flat : w ∈ flatSet s S := Finset.mem_filter.mpr ⟨hw,sep w (sub w hw) yes no⟩
  have posCard := Finset.card_pos.mpr ⟨w,flat⟩
  have supply : ∀ x ∈ projectedStock s S, AvailableWord s ([] ++ rawOn s) x := by
    intro x hx
    simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image] at hx
    rcases hx with rfl | rfl | ⟨a,ha,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact suppliesOfCheck sources a (sub a ha)
  have cut := Project.cut live nonflat (show AOBuild s (rawOn s) [] from trivial) supply (restrict ▸ allFour i)
  simp only [List.length_nil,Nat.zero_add] at cut
  change 11 + (flatSet s S).card ≤ k at cut
  omega

theorem row12 (v : Fin 5) : AOLower (omitRowMask v) (rawOn (omitRowMask v)) (T &&& omitRowMask v) 12 :=
  line12 true v
theorem col12 (v : Fin 5) : AOLower (omitColMask v) (rawOn (omitColMask v)) (T &&& omitColMask v) 12 :=
  line12 false v
def minorFacts : List (Word × Nat) :=
  (List.finRange 5).map (fun v => (dropMask v, 11)) ++
  (List.finRange 5).map (fun v => (omitRowMask v, 12)) ++
  (List.finRange 5).map (fun v => (omitColMask v, 12))


theorem minorLower {m n} (h : (m,n) ∈ minorFacts) : AOLower m (rawOn m) (T &&& m) n := by
  simp only [minorFacts, List.mem_append, List.mem_map, or_assoc] at h
  rcases h with ⟨v, _, e⟩ | ⟨v, _, e⟩ | ⟨v, _, e⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact allFour v
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact row12 v
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact col12 v


end Rep9102.Subfloor
open WordEngine
namespace Rep9102.Project

theorem validCuts (pairs : Array (Word × Nat))
    (known : ∀ q ∈ pairs, q ∈ Subfloor.minorFacts)
    (proper : ∀ q ∈ pairs, ¬ maskedFlat q.1 T) :
    ∀ q ∈ pairs.map (fun x => (⟨x.1,x.2,stock.map (· &&& x.1)⟩ : Minor)), Minor.Valid T q := by
  intro q h
  obtain ⟨x,mem,rfl⟩ := Array.mem_map.mp h
  exact ⟨proper _ mem,Subfloor.minorLower (known _ mem)⟩
end Rep9102.Project

open WordEngine PEqualNP.Represents

namespace Rep9102.Final9102

open Orbit Project

def actions0 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x28c8c4c844c8b8883888c688).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions0 : actions0.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions6 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x4650a7082708b5083508a8c8).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions6 : actions6.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions12 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x18d0c2d042d0b8503850c650).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions12 : actions12.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions18 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x445897101710b310331098d0).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions18 : actions18.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions24 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x1898c2984298a8582858c458).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions24 : actions24.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions30 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x346095181518a31823189898).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions30 : actions30.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions36 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x14e0a2e096a0b2a02660b460).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions36 : actions36.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions42 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0xc4c144c13881c681468194e0).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions42 : actions42.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions48 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0xc611461127013501a8c128c1).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions48 : actions48.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions54 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x311188d108d1c0d140d13811).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions54 : actions54.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions60 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x51921190899409928194419).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions60 : actions60.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions66 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x18c2c2c242c23842c6424642).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions66 : actions66.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions72 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x460a97021702b302330298c2).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions72 : actions72.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions78 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x88ca08cac0ca40ca380ac60a).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions78 : actions78.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions84 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0xc05a405a981a181ac21a421a).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions84 : actions84.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions90 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x9622b222911a111a885a085a).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions90 : actions90.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions96 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0xc443444382e290e28662b062).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions96 : actions96.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions102 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x230398831883c28342832843).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions102 : actions102.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions108 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0xa80b280bc40b440b95031503).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions108 : actions108.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions114 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x4213050b210b088bc08b408b).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions114 : actions114.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions120 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x8853c053405398131813c213).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions120 : actions120.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions126 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x94231423a223222383139113).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions126 : actions126.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions132 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x2644344482a390a310a32063).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions132 : actions132.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions138 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x14c422c496841684b2843284).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions138 : actions138.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions144 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x90d48654b0549614b21420cc).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions144 : actions144.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
def actions150 : List (DagMoveRecord 25) := (CompactMoves.rawList 6 0x29c909c109c845c941c82d4).map CompactMoves.record
set_option maxHeartbeats 0 in
theorem verifiedActions150 : actions150.all (dagMoveRecordOK (fullMask 25) T) = true := by decide +kernel
theorem allActions {a b : List (DagMoveRecord 25)} (ha : a.all (dagMoveRecordOK (fullMask 25) T) = true) (hb : b.all (dagMoveRecordOK (fullMask 25) T) = true) : (a++b).all (dagMoveRecordOK (fullMask 25) T) = true := by simp [ha,hb]
def records : List (DagMoveRecord 25) := ((((actions0++(actions6++actions12))++(actions18++(actions24++actions30)))++((actions36++(actions42++actions48))++((actions54++actions60)++(actions66++actions72))))++(((actions78++(actions84++actions90))++(actions96++(actions102++actions108)))++((actions114++(actions120++actions126))++((actions132++actions138)++(actions144++actions150)))))
theorem autos : DagMovesOK (fullMask 25) T 25 (dagMoves records) := dagMovesOfCheck (allActions (allActions (allActions (allActions verifiedActions0 (allActions verifiedActions6 verifiedActions12)) (allActions verifiedActions18 (allActions verifiedActions24 verifiedActions30))) (allActions (allActions verifiedActions36 (allActions verifiedActions42 verifiedActions48)) (allActions (allActions verifiedActions54 verifiedActions60) (allActions verifiedActions66 verifiedActions72)))) (allActions (allActions (allActions verifiedActions78 (allActions verifiedActions84 verifiedActions90)) (allActions verifiedActions96 (allActions verifiedActions102 verifiedActions108))) (allActions (allActions verifiedActions114 (allActions verifiedActions120 verifiedActions126)) (allActions (allActions verifiedActions132 verifiedActions138) (allActions verifiedActions144 verifiedActions150)))))
def masks : Array (Word × Nat) := #[(1048575,12),(32538623,12),(33522687,12),(33553439,12),(33554400,12),(16236015,12),(24895223,12),(29224827,12),(31389629,12),(32472030,12),(507375,11),(24141559,11),(29197179,11),(31388701,11),(32472000,11)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def minors : Array Minor := masks.map (fun x => ⟨x.1,x.2,stock.map (· &&& x.1)⟩)

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def words (j : Nat) : Nat := unpack 0xfff18c7ff0843ff4211ff8000fd755d7e9fa53f39f39f94bf2fc63ce7e318fff18739f843f0fc21ce7e108cbf0843ff84210fa3e847d08423e4f909f21084f8c1087c21633e01a11f00694f802c67c01213e00529f00210f800c67c00423e000018c7f18c6318c56bfffeb5fd7f4a7e94a529ffd294fd294a53f4a52949ce7ffca52fca3f8c7f18fe3f8c63ffc6318fe1ffc210fc21085755d4273e72118f3908c39c843f084213c62109d2908479c84234a4210e7210863108423284210837ff6fdadfffed6fdbf67fff633ff6b99ffb3ecffd8c67d9ffb3ecfb19f633ecfb18c633ec6318cffd8c67d8c6319f6318c62febffd731ffeafabea57d4a52a42f893ffa7e9fa7ff4fd29fa53f4fd294ffe94a53f47fe8fa3ff4211f5b188fa79c47d2c623e8ffd1f47d08fa39c47d09523e847d1f421088000042d18c211fffd08ffd0847d1f423e8421096310847fe8423e84210c62108420e7fffe637fe631be6318c637cbf297e52ffff297e5f94a5ffca5297e4ffc8427c9f213e421087fd28427fff213ff2109fe7084fd28427d8c213e53109f27c84f9084213ff2109f2108427c8421083f8fff18ffff8c63ffc5f1084218dce10be2f885f108421dac210cc61085ff8842f884216b4210ad610852908427384212942108c610842f88421083f087e10ffff087e1f8421ffc21087e10842107fe0f83ff0001f1a100f8c8407c2c603e12101f07fe0f83e007c18c03e06301f02100f808407c00000aa2a8031b180182100042c6002063000fffe007fe0003ec6001f21000f83e007c000006840003210000d2800058c00026300012100007fe0003e000018c0000a5000042000018c000084000021000004400001f 25 j

def hull0 (i : Nat) : Nat := unpack 0x20cf914a2020cf91481020cf91480020cf91461020cf91460020cf91440020c590420020c391461020c391440020c390841020c3904a1020c390482020c390481020c390480020c390462020c390461020c390460020c390441020c390440020c390420020c29042001f013110001f013108001d85328e501d85328e401d85328e301d85328c401d85328c301d85328a301d85328a201d853288201d853288101d853286001d853284001d85308a301d813348301d81308e001d81308c001d81308a001d813088201d813088101d813088001d813086101d813086001d813084101d813084001d813082001cca614c201cca614c101cca614a101cca6048201cca6046201cca6046101cca6044101cca6044001cca6042001cc56042001cc39144001cc26146101cc26144001cc26046201cc26046101cc26044101cc260420 40 (i % 64)

def hull1 (i : Nat) : Nat := unpack 0x2705350c0027053110302705310e3027013510302701350e202701350c10270131120027013110002701310c002701310a202701310a102701310a0027013108102644c048102644c046002584c046102584c0440024d4c14a0024d4c1481024d4c1460024c4c1461024c4c1440024c4c0862024c4c0841024c4c0481024c4c0462024c4c0461024c4c0460024c4c0441024c4c0440024c4c0420024c2c04400230533cc1023013110002301310800224533d050224533d040224533ce40224533ce30224533ce20224533cc30224533cc20224533cc10224533ca20224533ca10224533ca00224533c810224533c800224533c600224530cc30224133c6002241334820224130c810224130c800224130c610224130c600224130c410224130c2002185328c302185328c202185328a202185328a102185328800218390420 40 (i % 64)

def hull2 (i : Nat) : Nat := unpack 0x34cf91481034cf91460034cf91440034ca614c3034ca614c2034ca614a2034ca614a1034ca61482034ca61481034ca61480034ca6146002e4760c8002d853290402d85328e402d85328c402d85328c302d85328a302d85328a202d853288202d853288102d853288002d853286002d853284002d839082002d813286102d813284002d813084002cd1604c302cd16048202cd16046202cd16044102cca614c502cca614a402cca6148302cca6146202cca6144102cca6142002cca604c502cca604a402cca6048302cca6046202cca6044102cca6042002cc56046202cc56044102cc56042002cc2604e002cc2604c002cc2604a102cc2604a002cc26048002cc26046202cc26046002cc26044102cc26044002cc2604200270535145027053512402705351230270535103027053510202705350e202705350e102705350c1 40 (i % 64)

def hull3 (i : Nat) : Nat := unpack 0x364a63ca10364a614810364760ce20364760ce10364760cc10364760cc00364760ca003644c0c8103644c0c6103644c0c400364263c6003642620e003642620c003642620a003642620600364260d010364260ce20364260ce10364260cc10364260ca10364260ca00364260c810364260c800364260c610364260c600364260c4003642604200358f928810358f9286103588928a2035889284003588908a00358890880035889086003584c088103584c086103584c0840035839288203583928810358392861035839286003583928400358391c4003583908c103583908a103583908a0035839088203583908810358390880035839086203583908610358390860035839084103583908400358390820035839046103583904410358390440035839042003581908410358190820034cf914a3034cf914a2034cf91482 40 (i % 64)

def hull4 (i : Nat) : Nat := unpack 0x40cd90462040cd90461040cd90460040cd90441040cd90440040cd90420040c590441040c590420040c3904c1040c3904c0040c3904a1040c3904a0040c390481040c390480040c390462040c390461040c390460040c390441040c390440040c39042003b07610e103b07610e003b07610c103b07610c003b07610a003b02650c003b02610a003a54c3ca203a49c0c8103a49c0c6003a44c3c4003994c286103989c284003989c08a003989c088003984c288103984c286003984c284003984c1c4003984c08c103984c08a103984c088203984c088103984c088003984c086203984c086103984c086003984c084103984c084003984c082003984c044103984c042003981c0820038d4c1460038ca614e3038ca614c20370f951240370f951230370f951030370f951020370f950e20364a63ce40364a63cc30364a63cc2 40 (i % 64)

def hull5 (i : Nat) : Nat := unpack 0x4ccec04410470a651240470a651020464763ca004590908c504590908a4045909088304588908e004588908c504588908c304588908c004588908a204588908a0045889088304588908810458890880045889086204588908600458890840045839090104583908e104583908c104583908c004583908a104583908a0045839088204583908800458390861045839086004583908400424533d040424533ce40424533ce30424533ce20424533cc30424533cc20424533cc10424533cc00424533ca30424533ca20424533ca10424533c810424130c400418f928c30418f928a30418f9288204188908a00418890881041889088004188908610418890860041889084004185328c304185328c2040cf90462040cf90441040cf90420040cd904c2040cd904a4040cd904a2040cd90483040cd90482040cd90481040cd90480 40 (i % 64)

def hull6 (i : Nat) : Nat := unpack 0x570535166057053516505705351450570535144057053514305705351240570535123057053512205705351030570535102057053510105705350e205705350e105705350e00570135123057013510205701350e105594c288205589c088005589c086105589c086005589c0840054cec04a2054cec0483054cec0482054cec0481054cec0462054cec0461054cec0441054c4c04c1054c4c04c0054c4c04a1054c4c04a0054c4c0481054c4c0480054c4c0462054c4c0461054c4c0460054c4c0441054c4c042004f03910c104e49c3c8004e44c3ca104e44c3c8104e44c3c8004e44c3c6004e44c148004e44c0ca104e44c0c8104e44c0c8004e44c0c6104e44c0c6004e41c0c4004d94c28a204d8f928c204d89c08a004d89c088004d89c086104d89c084004d889086004cd4c14a104ccf914e204ccf914c104ccec0462 40 (i % 64)

def hull7 (i : Nat) : Nat := unpack 0x308089144030808914203080890482308089046130808904413080890440308089042030807614a130807614a0308076148130807614803080761461308076146030807614413080761440308076142030807604803080760461308076046005f089510105f08950e105f08950e005f08950c005f08910c005e44c0ce105e44c0cc105e44c0cc005e44c0ca205e44c0ca105e44c0c8205e44c0c8105e44c0c8005e44c046105d8f928e205d89c08c005b076510105b076510005b07650e105b07650e005b07650c005b07610c005b026510105b02650e005995c088305989c08c005989c08a205989c08a005989c088305989c088105989c088005984c08e105984c08c105984c08c005984c08a105984c08a005984c088305984c088205984c088005984c086105984c086005984c084005984c0462058ca61503058ca614e2 40 (i % 64)

def hull8 (i : Nat) : Nat := unpack 0x30a450206030a450204030a450202030a41040a330a410408330a410408230a410406230a41020403099092c413099090441309909042030989c146030989c144130989c144030989c04413098891481309889148030988914623098891461309889146030988914413098891440309889142030988904623098890441309889044030988904203098501ce03098501cc13098501cc03098501ca13098501ca03098501c813098501c803098501c613098501c603098501c4030981034833098102cc53098102cc33098102ca43098102ca23098102c833098102c823098102c623098102c613098102c413098102c203098101ca43098101c823098101c813098101c623098101c603098101c413098101c203081090441308109042030809c144030809c044030809c042030808914a0308089148030808914603080891441 40 (i % 64)

def hull9 (i : Nat) : Nat := unpack 0x30e41040a130e410408230e410408130e410406130e410406030e410404030e41020c430e410208130e410206130e410206030e410204030e410202030d9092c6230d9092c4130d909046230d909044130d909042030d88914a130d889148130d889148030d889146230d889146130d889146030d889144130d889144030d889142030d889046230d889046130d889044130d889044030d889042030d8102ca230c109048230c109046130c109046030c109044030c109042030c09c148030c08914c130c08914c030c08914a130c08914a030c089148030c089146130c089146030c089144130c089144030c089142030c089084030c089048230c089048130c089046130c089046030c089044130c089044030c089042030c079142030b05024e030b05024c030b05024a030b010248130a45020c030a45020a030a4502080 40 (i % 64)

def hull10 (i : Nat) : Nat := unpack 0x31301024a231255c046131249c14a031249c148031249c048231249c048131249c046031189c14a131189c14a031189c148131189c148031189c146231189c146131189c146031189c144131189c144031189c046231189c046131189c044131189c044031015c048031015c046131015c046031015c044031009c14c031009c14a131009c14a031009c148131009c148031009c146131009c146031009c144131009c144031009c142031009c048231009c048131009c046131009c046031009c044131009c044031009c042030f05024e030f05024c030f05024a030f0104c8330f01040e430f01040c330f01040c230f01040a230f01040a130f010248130e45020c130e45020a130e45020a030e450208130e450208030e450206030e41040e530e41040e430e41040c430e41040c330e41040c230e41040a330e41040a2 40 (i % 64)

def hull11 (i : Nat) : Nat := unpack 0x33410904613341090441334109044033410904203340b604c33340b604c23340b604a33340b604a23340b604823340b604813340b604623340b604613340b604413340b604403298501c203298102ce43298102cc43298102cc33298102ca43298102ca33298102c833298102c823298102c813298102c623298102c613298102c413298102c403298101c823298101c6132811614a33281161462328089144032807614a0328076148232807614813280761480328076146132807614603280761441328076144032807614203164b604823164b6046131590904413159090420315889042031305025213130502501313050250031305024e131305024e031305024c031305024a03130105546313010552531301055243130105504313010550331301054e331301054e231301054c231301054c1313010250431301024e4 40 (i % 64)

def hull12 (i : Nat) : Nat := unpack 0x336426208033642620403364260c4033641620603359092ca43359092c833359092c623359092c4133590904623359090441335909042033589c1c8133589c1c613358892c623358892c4133588928203358891cc03358891ca13358891ca03358891c813358891c803358891c613358891c603358891c413358891c4033588914a1335889144033588908a03358890881335889088033588908613358890860335889084133588908403358890820335889044133588904203358391ca33358391ca13358391c813358391c803358391c613358391c603358391c403358390841335839082033583904203358192c413358192c203358191c413358191c2033581908203358102c623358102c413341091462334109144133410904c433410904c333410904a433410904a333410904a2334109048333410904823341090462 40 (i % 64)

def hull13 (i : Nat) : Nat := unpack 0x33989c1c4033989c144033989c088033989c086133989c086033989c084033989c044133989c042033984c1c8133984c1c6033984c1c4033984c086233984c084133984c042033981c1c2033981c08203398102c623398102c4133815c146233815c144133815c04a433815c048333815c046233815c046133815c04413380b604c33380b604a23380b6048133710954c23370264c833370164c623364b640e53364b640c43364b640c33364b640a33364b640a23364b6408133649c208133649c2061336476210133647620e233647620e133647620e033647620c133647620c033647620a133647620a0336476208133647620803364762061336476206033647620403364760c803364760c40336426210033642620e333642620e233642620e033642620c333642620c233642620c033642620a233642620a13364262081 40 (i % 64)

def hull14 (i : Nat) : Nat := unpack 0x3440b604a23440b6048133e450202033e41040e533e41040e433e41040e333e41040e233e41040c433e41040c333e41040c233e41040c133e41040a333e41040a233e41040a133e410408233e410408133e410406233e410406133d9092ca333d9092c6133d909046133d909044033d8102ca333c10904a333c109048233c109046133c0d914a233c08914a033c089148133c089148033c089146133c089146033c089144133c089144033c089142033b07610a033b026250033b02624e133b02624e033b02624c133b02624c033b02624a133b02624a033a55c408233a44c086233a44c086133a44c084133a44c044133a44c042033a41c084133a41c084033a41c082033995c2c8333995c2c6233995c2c4133994c1c8133993c1c8033989c1ca133989c1ca033989c1c8233989c1c8133989c1c8033989c1c6133989c1c60 40 (i % 64)

def hull15 (i : Nat) : Nat := unpack 0x35301054e135301054c235301054c135195c2c6135015c046135009c14a235009c14a135009c148135009c148035009c146135009c146035009c144135009c144035009c142034f08924c134f08924a134f08924a034f03924c134f03924c034f03924a134e55c40c334e55c40a234e49c20c034e49c20a134e49c20a034e49c208234e49c208134e49c208034e49c206134e49c206034e49c204034e49c148034e44c206134e44c206034e41c204034d95c2c8234d9092ca234d8391c8034c15c048134c10904c234c10904c134c10904a13464b640e53464b640c43464b640a33464763c203459092c623458891d013458891ce13458891ce03458891cc13458891cc03458891ca03458891c813458891c803458891c6034588908a0345889088034588908613458391c6134410904c434410904a334410904833441090462 40 (i % 64)

def hull16 (i : Nat) : Nat := unpack 0x6040b328816040b328806040b328626040b328616040b328606040b328416040b328406040b32820604083286160408328406040732861604073284060407308816040730880604073086260407308616040730860604073084035f03954e135e49c20e035e49c20c135e49c20a235e49c20a135e49c20a035e49c208235e49c0c8135e49c046135e44c20e035e44c20c035e44c20a235e44c20a135d9092cc235b026550235b02654e135b02654c035989c1cc135989c1cc035989c1ca035989c1c8135989c1c8035989c1c6035989c08a035989c088035989c086135989c046235984c1cc035984c1ca035815c048335815c04623580b604c2353020550435302054e335302054c235301055463530105545353010552535301055243530105523353010550435301055033530105502353010550135301054e335301054e2 40 (i % 64)

def hull17 (i : Nat) : Nat := unpack 0x60e4a034c060e4a034a060e4a0348060e4a0346060e45034c460e45034a360e420450760e42044e660e42044c560e42044a460e42040a460e420408360e420350760e42034e660e42034c560e42034c160e42034c060e42034a460e42034a060e420348360e420346260e420344160e410342060c0d928a160c0d9288160c0d9286160c0d9286060c0d9284160c0d9284060c0d9282060a4a034c160a4a034c060a4a034a06064ec08416064ec08206064b334806064b328806064b3286060647334a4604ca02cc2604ca02cc1604ca02cc0604ca02ca2604ca02ca1604ca02ca0604ca02c82604ca02c81604ca02c80604ca02c61604ca02c60604ca02c41604ca02c40604ca02c20604c302c60604c202c81604c202c61604c202c60604c202c406040b328a46040b328a36040b328a26040b328a16040b328836040b32882 40 (i % 64)

def hull18 (i : Nat) : Nat := unpack 0x620cd92c816200d928816200d928616200d928606200d928406200d928206200d908606200d908406140b328c56140b328c46140b328c36140b328c26140b328a36140b328a26140b328836140b328826140b328816140b328806140b328626140b328616140b328606140b328416140b328406140b328206130a038e06130a038c061305038e461305038c461305038c261305038a2613020594761302058e461302058c361302058c261302039266130203906613020390561302038e561302038e461302038e361302038c461302038c361302038c261302038a361302038a2613020388161301038826124ec08626124ec08416124ec04416124ec04206100ec28a06100ec28816100ec28806100ec28616100ec28416100ec28406100ec282061009c148261009c146160f0204c8360f0104c6260e4a034e060e4a034c1 40 (i % 64)

def hull19 (i : Nat) : Nat := unpack 0x64f08938c064f03938c064e4ec34c564e4ec34a464e4ec348364e4ec348064e4ec346264e4ec208064e44c346264e44c344164e44c0c6264e44c0c4164e44c084164e44c044164e44c042064e41c344164e41c0c4164e41c082064241344a36424134482640cd92ca2640cd92c81640cd92c61640cd92c4063e42044e563e42044c463e42044a463e42044a363e42034a463e42034a363e420348363e420348263c0d9286063c0d9284063c0d9282063c089146263c089146163c089144162701338c362701338c162701338a362701338a26270133882627013388162644c046262644c04416240ec28616240ec28406240ec28206240ec08406230134c836230134c6262242c042062241334e362241334c562241334c262241334a46224133483622413346262241334416224130c826224130c626224130c416224130841 40 (i % 64)

def hull20 (i : Nat) : Nat := unpack 0x904cf04061904cf04060904cf04041904cf04040904cf04020904ca04060904c404040904c304061904c304040904c304020904c204082904c204061904c204041904c204040904c2040209041163c419041163c209041033ca49041033ca39041033c839041033c829041033c809041033c629041033c619041033c609041033c419041033c409041033c209040b33c209040933c419040933c209040833c419040833c209040830c819040733c4165e4ec350365e4ec34e265e4ec34e165e4ec34c165e4ec34c065e4ec34a065e44c34c0657013590465701358e365701358c265701358c165701338a16530205926653020592565302059056530205904653020590365302058e365302058e265302058c265302058c165302058a06500ec28606500ec28406500ec282065009c148265009c146164f0d938e164f0d938c0 40 (i % 64)

def hull21 (i : Nat) : Nat := unpack 0x9130104c8391193c448291193c446191189c148291013c3c6291013c3c4191013c3c2091009c146291009c1441909930448190993044609098f044e29098f044c29098f044c19098f044a29098f044a19098f044a09098f044819098f044809098f044609098f044409098f040a29098f0408190989c1461909830448190983044809098304460908d1640a3908d164082908d164041908cf04081908cf040609081163c629081163c619081163c419081163c409081163c209080761462908076144190590344a290590344a1905903448190590344809059034461905903446090590344409059033c819059033c619059033c609059033c4090590308609058830840904d164061904d164041904d164020904cf040c3904cf040c2904cf040a3904cf040a2904cf040a1904cf04082904cf04081904cf04080904cf04062 40 (i % 64)

def hull22 (i : Nat) : Nat := unpack 0x9281163c629281163c419281163c209271034ce19271034cc19270834cc59270834ca4924d3c4062924d3c404192413c3c4192413c3c2092413c0c2091d933448191d933446091cd16406191cd16404191cd16404091c1163c6291c1163c4191c1163c2091c1160c20914cf04061914cf04041914cf04040914cf040209141033cc59141033cc49141033ca49141033ca39141033c839141033c829141033c629141033c619141033c419141033c409141033c209130f04d029130f04d019130f04d009130f04ce69130f04ce19130f04ce09130f04cc59130f04cc19130f04cc09130f04ca19130f04ca09130305d289130305d079130305ce69130305cc59130305cc49130305ca49130305ca39130304d079130304ce69130304ce59130304cc59130304cc49130304ca49130304ca39130304c839130204ca49130104ca4 40 (i % 64)

def hull23 (i : Nat) : Nat := unpack 0x95993c44a195984c44a1954d3c4082954d3c40619530305d279530305d069530305d059530305ce59530305ce49530305cc49530305cc39530305ca39530304cc59530304cc49530304ca49530105cc39530104ca393b1164ce193b1164cc193b1164cc093b0d64cc593b0d64ca493b0264ca493b0164c8393993c44c393993c44a293993c44a193993c448293993c448193993c448093993c446193993c446092cd1640c392cd16408292cd16408192cd16406192cd16406092cd16404092ccf0408292ccf0406292ccf0404192cc2040419281163cc49281163ca39281163c82 40 (i % 64)

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def hull (i : Nat) : Nat := (if Nat.blt i 768 then (if Nat.blt i 384 then (if Nat.blt i 192 then (if Nat.blt i 64 then hull0 i else (if Nat.blt i 128 then hull1 i else hull2 i)) else (if Nat.blt i 256 then hull3 i else (if Nat.blt i 320 then hull4 i else hull5 i))) else (if Nat.blt i 576 then (if Nat.blt i 448 then hull6 i else (if Nat.blt i 512 then hull7 i else hull8 i)) else (if Nat.blt i 640 then hull9 i else (if Nat.blt i 704 then hull10 i else hull11 i)))) else (if Nat.blt i 1152 then (if Nat.blt i 960 then (if Nat.blt i 832 then hull12 i else (if Nat.blt i 896 then hull13 i else hull14 i)) else (if Nat.blt i 1024 then hull15 i else (if Nat.blt i 1088 then hull16 i else hull17 i))) else (if Nat.blt i 1344 then (if Nat.blt i 1216 then hull18 i else (if Nat.blt i 1280 then hull19 i else hull20 i)) else (if Nat.blt i 1408 then hull21 i else (if Nat.blt i 1472 then hull22 i else hull23 i)))))

end Rep9102.Final9102

open WordEngine PEqualNP.Represents

namespace Rep9102.Final9102

open Orbit Project

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def hashToken (v : Nat) : Nat :=
  let a := ((v ^^^ (v >>> 16))*2246822507) % 4294967296
  let b := ((a ^^^ (a >>> 13))*3266489909) % 4294967296
  b ^^^ (b >>> 16)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def getLocal (data bits byteOff span salt tok : Nat) : Nat :=
  let h := hashToken (tok+40503*salt)
  let page := data >>> (8*byteOff)
  (unpack page bits ((h % 1024) % span)) ^^^
    (unpack page bits (span+(h/1024 % 1024) % span)) ^^^
    (unpack page bits (2*span+(h/1048576 % 1024) % span))

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def bankPage (fuel symbols flags width i : Nat) : Option RowState :=
  let present := unpack flags width (i % 16)
  let ws := (List.range width).filterMap fun j =>
    if present.testBit j then some (words (unpack symbols 8 j)) else none
  some (unpack fuel 4 (i % 16), ws, [])
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def actionPage (header data tiny hulls deps i tok : Nat) : Nat :=
  let m := unpack header 65 (i % 16)
  let mCount := (m>>>26) % 16
  let hCount := (m>>>30) % 32
  let x := getLocal data (m / 4611686018427387904 + 1) (m % 4096) ((m>>>12) % 128) ((m>>>19) % 128) tok
  if x < mCount then 2*unpack tiny 4 ((m>>>35) % 256+x)
  else if x < mCount+hCount then 2*(16+unpack hulls 11 ((m>>>43) % 512+x-mCount))
  else 1+2*unpack deps 19 ((m>>>52) % 1024+x-mCount-hCount)

def as0 := bankPage 0xcccccccccccdddde 0xa98b5a434241362f2e2a29281b1110090800 0xe62af9aa9e49fbb26ee4abbb66ae4eab96aaf4aab98aae62a3926fe59af92abe4aab926b 18
def ac0 := actionPage 0xb2081ebc14019356587c0f480b00d18dec0a0396270078b615ec00c38bc03e524ae2005e41c018a5ad6ac00da1c0101096afa005f07006a75b555002a02c034338a98801241601a960543c00800900989aa9da00370480384574be001403c0ba1a8a47800741601f08e518c00260a00b42da86e000a0480440d38000000028028000 0x37c001b02c00f88a00002631c3c003f6c36c27421c002b7da0005cc14002e4554500044fb3d9b0f6402c33006d700d30035805f02413538c000f40d83498c5c0291cb01101621e2c0ba4092000d006fac9a1803c858b00001a01470fa8b4c0dc055a00829800993e249000f27000023bc00c00002d78823782ca011f0924e01d02400015410208c012002a00245bc02ed5c03dd000340acc27be0e669025009000700240000046315e4002234da053003a530e6d400bb870000001df240a4c4440c0746dc00006404d9280000f416a2380b0e0289886c04001403dc22664e0006c0006a60a40002ac0000b4702476b00a6c66c902fd005d15c27c2c40030037f8618030000024d00d3a634d1021c084c2e2bef3f202dd1d0122000792c0025ba80006446fc2d3dc40002c078600db440009c532d000be90e9a80000d80029e305800052c030101d00c2c51e6ad6be4d0001eaa551a008ec93c124238000bd835a6100180780016015ec100a0b40b430c0ba4a54012002fa5344ae900b58000090500184402a2c10c000d0daa400c094a88c0e40cd0043000090004c30a5309280000b43440641b000003c30003493c0de50369c038f01e8f600e58ee800240120ab30084628fa80e43038000bed30413f0c3000000a406a0a03a009a0c05000748b759408400400c00ca00930024f3001406c64c510028a0001d3110a8000f1850007b501e002fcf60000f195a8003f28084038ec40527b4d00400002a01bf13f2fec4f8b033d0080e94701bf2aa0000016aa8000093f01fb801290191c0005039849006c8001cea1832ae400062588124400ce04a4094d30201a9e57e180d000d5850c94fc0400cc7250a24008021500000072c1c014000024000f14c00015474702a000a952512008882e644d9ca1c08800050150000cc5636c050000928e0c04c039618048068b2c035da801f15cbc004400001003075d40c80322e500648524101b02040c0155b402348381f70500600da966550000473007f53443403000050061d005098078131a0c060db4558015f2ca00f00002202500002b000005c801d52032570001c0000880240065000001cf67001c000c237e40e00fe12c07c2fbccc02fdad1eaab8700003e0e400328301d040000eb800c00009862d84054003fd363430400002a29e280000dd49ebe4c07389730046f005310d403842a8094ce553c05c013c00e08c382080032083fed00500000fa966cfd40d5400020100b0c0d4024233000000000000e1eb5ae380640004132178009f2fa21d2bf0020084b4050000809baec0c2191502c92c4214033f1018e93000a680bb000de20000008c0c213b4d650002b838e025f01aac1f602b173180780000e808f3811039dc4741a2f00d000d8a38000a50000058318c940a43ec0756e320000004aaeb72830a7020006272380d5864004001032bb0000117400ee409f20000044451c29332410003fb008e400000c00370860050233820003c019537eb0188d2553c7400ee1689000000000c4f6c47550409ffe42c00ae34b64e2380fc358224101c00306da6406d5c40fd3000003fd3f80000f409807ea4cc2e100000bfd602f3cd1000140095cea900282003bd4de1bc00360979f01e000dd333d28000a84001e616bc78404f70562d63c01009fd140565fc080da0ab40612916500b2c000fe72403400130161c0156127e57c800006345cf4801e7710035387280d414dabc814000702348000845000301db0d588cc002f71f03c000353d00002bf740046c01e1100380e0e4ca00190000008ada71809400009250eb0005c90c00431c0af4168e4e2a5b9103934448ef003ac01a09d449c801b0100a808c000a766340030c2948090004015b00703e35c8d4780b0003a02d400ab9700040ae4d4d019e4007a03747c15ecbc380000003018ed27ef00a018e84380537013075f015eaca054a500500112a6c0000ac9c470195a300204100002b000f80a22004000cc5fea726154bc0ccc02d540689dc80bfa4f55de0000082f2400223c801e37dc800a3101d0004000000000108001e02df40a8f6cd0cd180b11b1e03538000cdc0b133eb034089ab09c0d8f34932201fec4031000b44b5601e4c04c30271c0080c16018039d8090022d000033f7b4ae00a78003105bb4000600000080002fda7dc0bdf86b03413df8009fb3500b000bc074389c005017027e0069cdc52eb029e80147360037e84bfe01a030000040a80de361de49cd52a3000b49112b81b80cc00ed7ca000d110233809a915e98386b07cb581df863302297b000726754083d80012c0c01183a4faba9080c7f00002196606d643006d8000c86830001b011680a15000dc0749e13840e03f00cbf3000176265800014c79808c0780003000002976f4e8036006be00d80407a19b806a00e28780c0002c001c5622af8000401a307b0200023c000629c8007e092877201bfa0178d0040c400000fc038124c0927201e775800f917df983a4a007806851d000c0085753d880056d80008001c3300e007500cc5a2 0xedcba43210edcba843210edcba987653210edcba9876543210edcba876543210edcba8743210edcba876543210edcba843210edcba743210dcba43210dcba43210edcba9876543210edcba843210edcba43210dcba43210edcba43210 0x170ad2da437d2ca582da 0xba1fd5c3faa87f5e0e4b01c9583905067080ce0c19c103381067000ce0c198103300066060c2081840030a4051460a2861444828880510c0a2900f5181ea183d1207a200f4301e9d034380686a0d00013bf87d7b0faf21f5743eab87d550fa921851c30a2061120c220184303085060080c00c180103001060000c0921311c262204c120982013030262482f4705e880bc48178802f0c05e740b8e0171a82e0004400178082e8005d020b800170082d8005b0e0941812808250004a0e092181240824800490e05a180b408168002d0e058180b008160002c0c056000ac001301058000b00415c002b81056000ac04154002a81050000a00413c00278004e12092201240823800470208c00118c4161782c02054000a8001496028060b408168002d04059020b200164182a02054000a81414c202983053040a60414c002984052020a400148182882051000a20c13010260004c060960812c0025830480409000120181c0203800070620acbc159602b06050080a0001400027580d2ac1a52434a3869540d0a41a0e82f9c05f580acac159242b238561e08c381184823080460e08a181140822800453606c5a0d910149d02338046ba1e15c3c2a8785e0ecb01d9583b24062460c4861892026a304d4309a0c110102200044060860810c002185042080840c108102101042000840c1041020800410606e080dc001b8303304066000cc181902032000640c0c410188003106060080c00018030250404a0009400122f079580f2ac1e5743bab877550ee9218d1c31a20634909c8e1391027030400408000100181f8203f0007e140f8201f0303e0407c040f8001f0303d0407a000f4481c080380c0700c0d8101b000360605e080bc0017800223a04070080d410318755d0eaf6191e43235064680c8f613de427b504f6809e3e108742109042100841e0ec341d8103b00076000e8081c800390006e3e0d4741a890351006a1a0940012878230d0460408c001186820000402407c400fae873570e6aa1cd7838ac071560e29012d1825a184b12082201043020850350806a0c0d4101a810350006a0c0d0101a0003413062220c434188302e0405c000b80012030200404000080480f0801e0c03cbc1c174382c070570e0ac1c1543824830480608e0c118182203043060260c0481808830100601a0c03018000210903e1007c0c0f8101f0103e0007c1c0f0301e0503c08078040f0001e0603a08074000e8301c0403800070200d8101b000360c068100d0001a0a03210064180c820190203200064200c01018000300c05c100b800170602c08058000b030150402a00054180a02014000280c0441008800113101a5e034b0068300d0401a00034c4061780c2c0180c03010060000c2c0160002dfc0cbd81979032ba0655c0caa819320266004cb40983013040260004c2809040120602408048080900012490228e04510088901110022180455008290104f02074040e0081a810490188e03110060900c1001818030c8051800a2d0140c02810050000a2d01000020e8039c0073500eba05d5c0baa8174802e8c05d0c0baf0165802cac059240b238164402c4404080080f0101c020340406008090101002018040180802010000202403c40078600f0001e2403840070600e0001c2402c40058600b00016240204004060080001074018e0031a8062c00cbc055740aac0155702aac055540aa48154802a8e055180aa20154302a26024480488809100121a024300480809000124201c80038d8071a00e3201c6003838070600e0a01c1003808070000e260184803088061000c1a0183003008060000c240144002860050000abc01174022c00457008ac011540224804480088e0111802220044300826010480208804100081a01030020080400008bc00d7401ac00357006ac00d5401a4803480068e00d1801a2003430062600c480188803100061a00c3001808030000676008e8011c802380046c008d401168022c0040200800011d001380026a004b00080001
def as1 := bankPage 0xbbbccccccccccccc 0xa98b7b5f5a454443413b362f2e2928261b1510090800 0xd8a4a330928cc2483222bfc88bbf2a2afd88abfa22afcc0abf322a7cc0a9f222bbc8daaf626abca8aaf2632b 22
def ac1 := actionPage 0xa938dac4160162e3d4386d5009007d6069ea369f04802ca9f0f017c91f401b51ca6f09e111c014261436444f659007522e9961a6d4700568554bc0a2f9b80293cda4f845407e02099d520c1c823f010ca8e8be0e3307006446544806130b40b91b1821820749200f0bc40d406245b00b448e838010b13807613d400000006c046000 0x39b22223f03c0a1d590010c3000001358000fc004c000057f000215000e9e400a12151000360392dd9440240f882b102bc4700b68000801030a80d015540034ac07c07c041e6c0c1197f687abb62289d0197440007eb4000140d8280f7607032f0171e2474df6801ce30001c0025c068001701f59f6c07821d500678070400003655f1002d901e4d264051b0026f56de0830008890c34ca65a00000003408111c01344201648001e008915600000e01e4b001c20000060002c3c7349e194ab45101b0000543c0000498280c812c07c06591c724031a11d41e0120c40007189a00436a01c1a98016b980b04502a081e0280106820a1aa66fe16002ae064076029abcb60034b9028c0c0009dbc100001750d8480f4028d68064b2d003b20001409a01b280021f0001faea01da1500e02586100d6c06da70500d0336800014f60007800717003ca840dc001c7400168df10901e0247907dcfc06c62d7f001a430b02800004e00070e0014038009401800280d0000b4b40c008087800a528000038773c6860c0d02d6b039c11180a0018a47de0201a0311ae59fec01d2439de01d01e3800070173030a70c00160003190050400060199c03db65102299cf800bd00b0243053bf80e40001238002054095400041f36a7d103c00708149402c50b0df39d00001e000000f1d6f06088ff5d8fcc340105c9344074be545f1285000100027006d80400180100bc53e943390400000000e9c000aa3c15758f84144de8d001e0e44010001a4dd0071800005e100002d590016dc001c50028201e540299a554c0200d3cfc1d404e45485870061f001ecdc1007401c316a6c051fe4001c3800444472c01cb73903f03dac30003bb94001500308a01568925f18103c044948dc008402bccd0072f564000000048000210c0c908000afc00000141c236910a0000094265806f000001f03d08457c0af3854c8a009e70030000006dc2434b80060104965af540d32024002b604ca7801408890000ca2658d60401000ab37a50a01210b100ac10991cd080d003c020400d161d20351c31c3840dd162c1c000c01e31100000010001785501e0001e2000a0074db1938de0010003102602a53301e57f032f9664309f40003300af1f1005440726f600011d1e17bef07983a8f040e610070490001c002202f8c02f1b2d65701bf03ac002510668000500f1c0ac00245189d21d40001df4af240000016965451344f7601c00002c03a1c001b72c76201e0af11233d032014e5c8000800004ac000002de92df2310b0c03654015a2e88eeb845d67779540c0dc10094849405110150001cf00ef8b98e00f0385de58fc0900002c0230199400005809a5abded6d5029ff00100000216b51dc0003588080037d075f604d240d72290003019a097ceb22000000ae1025038d820140120800010260104fdb0e01db4002a800880db138866724b03828001ae4b0c20c30fd1c000101e00001801142828e8ae36780c64b000d0078136b0001845c0bc31280087d221409efd10804c003600010e9c819e76501501a000ac00c05183d63802a548064c01a00000974003500a4014b14d20d84003d800b00080b00048b00062c0800191028370100c630a2b020002000200064014c040bb119530248ec80001940321eef00d2d10dee00100e81001059d1378003949001f0dc086c1ba01006407e9e0000f080c04200029c892a409001232b6006000b2bc4a038c00004039c001100099dc0718004034ec2b400017c41d6b21808382004ac8228180024205104b01fa00004e4bf45140001ba7557cd0ae5c15db12b40000801a00c5402a200369600452410320005d5ce03a50000e021080000900240284780013000411f8900015328003d0141c01400197c0000000a6630088b1406fb5400110870001c00141a00950073093450143233c66a1e3bd00118016aa5f420000f9004582c000c05018401db21f1010f2b8304501200ca00002500040007601502d41f30d02f4a20005e554000528a004000a0002b18e60b34000c02201c5e2e401ac4442400035490397c0b460216970e330014044628a47222b28a500026600a02100000dc06079804406c0c4083d4c364200071800b7a202400310a1001003d30283030610000040390002403417199be00003288320a1dd1d90ca1fb8402009803223c3a400f70001592c000e04d503004 0xedcba643210dcba43210dcba43210edc9876543210edcb9876543210edc743210edcb9876543210edcb9876543210edcba9876543210edcba9876543210edba9876543210edc9876543210edc843210edcb8643210edc7430edcba743210 0x2d24b796b2d259cb212369a8e4b77a06fcdf1a12d92ce594b1960242d25a2a392cde699f2d423a5b4b3960684cf88eb4b690df5a3b442c8488905bab716dada5bab6d6d19f11c240474b0 0x43975832eb0e5560caaa6900482002e4004880218f70c1ee002a8b050000a00513e0027c2c4e8309d69126ca24c74498c09305112002241443800870610cbc60574c02b9355526a903fd187f890ff101fe923b11c76098ec111d8002a4084e8009d0213800270084880091431161822c0843800870610a0821578bfae97f581d6ae3ad5875aa8eb491d6903ad1c75a30eb131d6243ac4475880eb43114182280045008860010c062140842808850010a0421000420108200104001f0b02d0005a0010200202142f4085e310bc0c179642caa8592c0b2001650c251f84a3d094181291816a182d1005a180b4083f0007e000f658150002a02079000ee0c1d40035820692f0ac08158b029800534309218124f423a182c0c0580020c183a0006a5a0aeac15cb02b800572f0aa58154102a800555a0a4ac148b0290005208102041fc003f8107d000fa001f0083b80077060e6081cc18378206f060d8081b0c42e9785d060ba081755c2caa859310b05e160182c020582c0a200144d4242182b0c0560c1f4103e8007b020f2001e4083900072060e2081c418370206e060ca0819400319885c2f0b80c170102e2c052560a462140bc2803050040a05813800271604c000980c208104104080060fc081f8003d01078000f0041d8003b01075000ea001d0083980073020e2001c4083800070060da081b4183202064000c46216cbc2d8305b040b66213cbc278304f0409e5813400269604b00096041bc00378106e000dc041b400368106b000d67c128f4251884a2f0940c12810251a8482c09000120f8239e8473108e5e11c182382047000805a0fcd41e1d03b38076181a9d023238463d08c181191022880457d07caa0f8c01f0003e3a0728e0a830150106c000d80c1ac10358106a000d4041a4003481065000ca04190003200063580aeac15cc424978490609208124c423178460608c08118b01c000386a0d8d01b0083400068120ce2019dec32bc865120c020180082f8005f6a0b0d01604829880537b0a0f2140481f0803e4307a000f0001c060363a06a700d53c1780028
def as2 := bankPage 0xbbbbbbbbbbbbbbbb 0xa98b5c5a454342413e362f2e2a2928201b1411100908 0xd9348765121d113bbc44aed142bbcc4a6d6129b54526d1449b444bad51c9345324f5149345924d1c49355124 22
def ac2 := actionPage 0xaab076cc3801dab7d4f43b520a00b143226e1aa01c802c9c51310bcb8e40164b8a8f04e209e019223c4601b00680059076a0c0b721700667554f304b20b8033337a690255c1a01416ed2fc08945d00bc9ce94a023c17016e3ef47e011783402c1948360008c5805b896512c00300b00ac32e83c000b06805c0c7400000002c02c000 0x7940010009d80f8001e0008c0000000752200b00b964d25bc02265820888078c01d5e4cdfc8a0004c0d05b8004062b640140016b005492c0dceedb7468520c04f2032a007c000b096017000e85000ac0c46dc00480004b318060b010bef805bcf0000b8b612711556ef2805af6db1002400004ac88d10c81247a02d286c9d00014030001824a7c490460e74000031b00001400e0106460051c015900000500015001b65684000301600034f40a70500018010280938a0155d2000340e1d8cc00021b0070df9c000824700d1060016d906558060901a01101da4045703c3c660994f0190805cc49802aa6800c0018a200600480c20007f80003142b0040078001098058a00502320799a40014d1300e2ac6601da5e800003f0002c00e81503de0ee00702fa0183c504d7d06833503396a006003610ec496a41c00120003f0180005ba080a400000e68d741b37318e3965fe1ab00c9a1cc35543430cd53503a01f9f54008969d50001dce4539e0090220cc15d7d449d000000004182000031580fad3943805025bb640030d40a54008e004c00180000309c7514edaa40d0028400001b20ae0b0000100270d900001a7040040300352160000800b40802ee7549a0a01e0024007b98d2001219a1630400280e9002c4694e10059ed43a00000000fe70310001c000800508053b31ff00004029344bc028300056eacc1041c20941f803700000000330168001f14930902403e1c100e007e8e78010000035a0db380285cc32cd00913d00e10a41a28a29500c5433400403b5580400331300301140b09280d6c0247a7003e4400d1d0c03350002c000b24f0002c000800108060760c00000d00e72a1006812c00c0440100097e4d0d101e1c00000163013400091492415170004977c000003a0b40000803f800038001239f00cd0d2d30051c871329260154c73534e44438046e740018100156dc07401401004c835601d2770000137e4020b809c003c02a4c799c0872c0b510000000330eb86a3c095726c231003bc0ac5000a405a708002548c000c43038bec80f01c3400d683902dbf57c703f07d00112eac001c494031100893e00bc0bc3521c08300ce400dc000000001a00074060617d00c00000092f01e1cb0006c947000a20d34c1c088003f34a34000000065414e8c01c98f261f5c360332a00a0868540f279d08004050e9cb38070d0324906c0ec20150055cc14b006e0001b40000300208003a03d60b10b326f8007e5bc000003ce48800d1809c05c093a8c0033088b1d0005d60000096806401e38c50004180000006049c000b28000000253d4b501404700b099d2304b2e42b893043a08601ca46a0b00032a0180190003002ae00100c39b5806a86106690120046401f902d00c300880a450333631e600e00f75058014e563585c960fc980583cc7b0b3450009f9a3202f000f80c7e1c0000540c770005c06c02ff00000378354400903f1d56da2c0140e4005e9cadb6335c4bc800cd63924700900d022327a00ceed4902003b000680e6b0000032cc5e13b6000291180680100040ec7340ad8206000007e000004402f82806a808690e44040007e34e706380681f840044e16a008cc003be00000000322103d62ed40055758478000002030201900a183add6bad00000b87c060160400157000303940367ecbf3c70040168d224c7d61286c4b43e0211f006edadf0005d40d020002f3940000002d3f4b44c051f00ae0073e53d0057400380070000005a00555f582f2790806c0386008940f3ef40400bd73001000040007c0c25015034f742c043a00578002260d5c9c15305b37644100358039c1a0003ba4c12801e10000a40a804220000154b101d002fef00000904248091ccd34cd5f74dc4c07f68fd019455000000039825f9695603d98b31a000840aeb9002ffc409c06d0000008cc0700b5eb0d016c761c3a82500280000ab6a8ccd2f508000009c0807fb6e0278b1a1c68d000341ec543ecc8091c05bcb1a3c803f00000c940027b4914000000db8014002f00858c044f150007c9a0f90e00034000edcc63e3e8000000bcb01b3c0020028b80029100258e4e00300f9805ae8500087fe99eba9b6f00018794c031000033165226200764 0xedcba8743210dcba743210edcb98210edcb86420edcba9876543210edcb7643edcba986543210edcba876543210edcba76543210edcba98765210edcba876543210edcba76543210edcba7643210edcba843210edcba76543210edcba743210 0x16c1a02f05d4cf1752e7706d1da213f2b254c2c78e7247a4af9590fe1e5ccb8368ed11bc8a714227439 0x492da8e5b524a5a394b58286ac50c188882111122202044018870210e021fa003f4007e278fa021d4003a93c60968ac3a124702498cc72e98e5826cac4d9209b231361f2243a4484889081121b21a3243418868210d021e8003d06c490c89206124082484848880910d118002300044000e92f1900032000622189010120003a00073000de0018e183190c47810e7001ce043900072010e3001c6043800070010da001b41c3203064010c60018c00314085e800bd02178002f0006f800dc2c1b60836cbc61800c3311bc5e378186f020de021ba00374b86d960db021b60036c0868000d00219e0033c085d000ba02170002e0c46d178da021b200364086c000d8021ae0035c086b000d60219c003380866800cd00182042e4005c810b1001620c3881071000e2081c2043840070830d5041aa00354286a040d4061a808350086a000d4081a60434c0069830d2041a400348185f820bf0017e0c2f8105f000be06176082ec005d830a3041460028c0066010cb00196043280065010c9001928a2410c48070900c1200424000482288f4311e1c23c30478108f0011ef65c1e4b83d951792a2d4459a08b351156822a042d8005b010b50016a042c000580009b0213200264004c010970012e00258084a00094021260024c00472e98957312aa62578c32c1865630c903e5187ca18f90616e082dc005b830b404168002d02859840b306166082cc0859800b306164082c80059030a20414400288184d0209a001340c254104a80095061180823000460308b041160022e58bcc9979962b3265664095c692b1f242243cde467888b50d16a082c00058020af0015e22278344f090897f30ef661de4c3ae9875730eaa61d247d238fa441f4243e8407d060fa3215c602b8b457030ae0415c002b82856840ad0615a082b40856800ad32158602b0b456030ac04158002b0e8441c08835110bc61574c2ac1855730aac61554c2898f8121f0223e0407c068f80c1f0923bd2077a38ef461de883bd0c77898ef121de223bc4077868ef0c1de0e2ac1855828ab04156022ac0055848aa08154062a80855008aa001540e2a41854828a904152022a400548308a041140022974c22f1827b2d0f25a1ec9d3c93a6a21ed043c4c8388907122062040c0854000a80014e042980053010a50014a042900052000a20213c002780849000920d11c00220484388087
def as3 := bankPage 0xbbbbbbbbbbbbbbbb 0xa9988b5f5a5652514f454443413a362f2e2b2a291b1008 0xac099f70133ea1067d41c4fa8989f54313fa0627d4144faa089f501a3ee0287d4210fa808ef52115ea122ed4205d 23
def ac3 := actionPage 0x6928ce305200cacac46c61023b0291546a0a2f760d8076998d0115b71200194a687e89594d200ca3bc3e440ba58006911a1d819523d80507f70d80b258dc03339ba6004d0c7001999442b424701b00d4b129300f2d1d807847b47f079202402a1dea2f8247cca01b0b2510006366400d83aa846000d1f00780c7400000003402c000 0x64006fe008a003087fee00de03a0704274ad00e04a0a207e4230000c300b0040eb64a0c44003180e0016eea80f82d502cef023ec500040180050060e3040858d800017001801834849c0d119e06118403c0e70171548000338a2b4020d4c6088edd38049b64060ef4080002407c728f50001721e60040d58ab8008b08004a08031302805808b74029704824200020701f280000009080240600000609243b407de2480116c53c02d400201700001238268b45e00b00000045a40001e08924098424a00ebc068208f00054244e14f2000096c000811030020a0800002c60d548700000401e75426d68068e79e6dc0e1b03004220b090d055a00855a00020356feb7268450f50006459000a60013b045e60080f3600930230cca54050135c824758180d0180000e0585e002018f672604e34701c606b9d079002746cec0314009f2380e0c70341e60d405896003a2518080414480100f7010602003888061ac0800008d900501c0b580a000160001c0419c05f56fba4fa08000101490001b07d82477a04ed46620007d40b52800b76a70258cb8400700051facc02800018003af2ee001e013fc05c62027a12f03e00018c9800f7c1d7ebd85824199c0fe806c00a004403400c00083e0003001a42c88618520000200e57580f500000997e03c426a0010200a003800000160140faac06e7b9a0001a5a3a00008c59460700e5c0f73e3800405e920cc4800a8d24ce20316194f9000f0467e017449daaab2988900bc005921b0001de01f24000008000300014500401800000f0000f92001810004405c05002802db2c003e0180000140006000440063936080172515880361eb1cd0000003fb2da0c0380503751a0361c0071353461440000c66224860c614084c00400700004061e4803d27dc50e41a18a402003c0701084840006c425d99c000c0001c0a00a058040309ac0000e0380075022c8166080a043db507c0803da0001e00001a30800a84a9000826ee8c000224f800680403dc13d0b80612ae5199d03c45d805552384201530000963c436800b7f581e580420e0000c001e00308a31f39e5c0701b0f6125cd00020068728100900200008b080080392000200b4c0191c0200483100354f910401c07092c009428060071cd1c24364eec80200000063c01c03c92d43c00c370d4000d56400110000184030170000160c02845000445cf0050214882d528500020300000001f5c350b300000121000491f4f00108400191c04c00636da0177006c014009d6de48001f5406001470000006db0005400520033a59940c300008879901a3c054d000798f4048d0900980080cf75a0ee6549236c03025d96076c025f7007695c16c00015493820147004820002d80a12009780680bc000f08ea23000f5694224046d0006609009e900c0390002d8080749ae300200501160a56934a8dc8393c43ef01e032845b1b10000066f0006e00030ed36d8ea0003c0113f8070102f68001e00727f12202468234003f0072250012803809476010ee400023e1b009002a360000c6000282009003364023e4c01c6f213b78058000000200000239003a30401cc1410050039cb1c0bc228d028b400c23672098ce6c00260c8a0b0120007c028b94000c35e01c87600f0200a0dc50001804800000052050289c71498d080302100508001f00000681d0062c2b43d000030000002653cd68002d796f080e80000c60000041a658038003aac003732834f00370001001100077c0160aa023040383f40343b00a581c401701300080f7aa2ff01002d61200002310035fa80c4096a000100580dc00040060160009f411502c500018000489ed9d8002b64d4ed7d2b5c2c0ba4083b54c0f31b44b803000ec91d000002d0eb50c32731ddc3d991cd08034000074cb60ff88b5e33ff33c0dc055934300088048095d3000016c092a00b9bb40002f00200e32a704f580001c001c1401c00c02183213c70133dd24014d200b8003500ed80000f8001f4b08af037200fce0001801ee18742038f00bd1503bbda74098098c0482a470d 0xdc8743210edcb8643210edcba843210edc73210edcb73210edc73210edcba753210edc7430edc73210edcba843210edcba643210dcba43210d9320d943edcba876543210edcba86543210 0x2da5b0b696c1f35b50f21dc3a8731462843c8750e5e6c4f8790ee1d4398a31421e43a872f2cf99f63ea7ccfb1f53e6b6aafd43a535d2a4547a8b02a04d439d71562a451813512a12ef 0xfc2d15c74298e053061267422e8e424107e800fb001ec8e30c6058800ad3a14a925a51cb4ab94155282924ed1c9d8112900252244a040940312204244044440088800fe021f6003ec007a800ac3a148702903051a18fe4f1f874284e050800a80d14c202847c4f868a70014e2428040503417299257264ae4495c592b931bf1637c6457830af2b14a402943c52800a502250004a01893821270224c0049808928012502248004900888001100221e0043c007d188bc2f1780c2c41058800a37b2e6f25cda8b9b41737b2a8f2551a8aa341541b2463248c1891821231b23032460188c02118061ee083dc6c580c8b006160082c03451000a27a2e2f05c5e8a93c1521224a204940891001226b22ed245c08870010e492128e424087b000f6001ea74278e04f43977832ed0e55e0cab2413e0c2460048418903290f061e8003cd94668c0b6001660c2946052000a10413c24274744a0e8925d31abc6215c9e2a93c482788c4f048950812a0224000480088f8011f0221a004344c76888ed4317c182c800590d0a4181480c29010520909c10138ba6315cb5aa96b482d68c5ad0ca4ab948552909052118a40111e0023c00474308c801190e23018460088c00118022180043008858010b001e486308004d8609a0013434264604c8309904132b05a958b52416a462d4005910ca3ac1465628c9051918a30011c1b23432468188d0211a0c2323e460748c0911810230003c41877020ee001303625c644b830970412e00258344a80095482ce8c59d609fab13f482728c4e47c918e9231f2343a46818890211206218084300883801070020a003c40078010ed001da0c3b01076068a20d12a0c250104a0008e00118ba63d8cc1a4166462cc904e1189c03113042260c42c1085811060020c004100881001020220200404088000100021fe003fc007c010f7001ee003bc0877000ee021d8003b00875800eb061260824c00468008b
def as4 := bankPage 0xbbbbbbbbbbbbbbbb 0xa98b655f5d5a52464542413d3b2f2e2c2a2928211b1511100908 0xe06221f1308a3c58228f128923c48248f1088edcc222b7108935c4623973188a5c474297108f25c622c97508b25c482c9710b925 26
def ac4 := actionPage 0xa648f6703e01aa2952d8731a4f00ccf7e936357f27006a6cf48519388f80392e6a338c98c1c015143c1845cb64808509858b62a5523002848744914240b40311d482188d04ae00a8d630f43c7855005463186e1c3414012c2d70330a949ec01a13a81783c84d000d883d0880a2aac00a02b680802081e807804cc0000000a0019000 0xa400001cd0056c01801c0000114040341380c812c0000107f0c2c531520001100030068004000000330014044318d01e2870800190c318060307000f3c038f6882405860d30000001c50001ce0000007030c68000c878038c3cd54c4cb3010c81b128600250974a30f3402416800014580c03c06c100b006005826c0dc00004c00cc01d800b807ce20c258b226800085e010d7c0f2c50003f0d2d4080f0591c000000036c0162efaff101b0545500301153287b00008c00064000071546e1c00104b27ce24a4684d301700fffcf3102ea2c50ff62f4500e6c05810009cc0c074d240cc013d340010004000300000121001800ab3700300c586005803c0782340000900f9c20f13a0000060f64000040c0000023000380f965c9007fc4000b18000a36ec068090fdc04825c9440307b0eac00001072331830000001680c15c06eb76c4823ce3ec74bd090cb100f028f704a10058c0c0f82b83017a410c03c1881005005105ac1ee4beb01f4af00024030015700bf023c6f0018740044c7380ec387bc70e500002306b35d18400f01d28e143cc003e81a10002c5800009e800602b009000000ecba4080004003b44c000b8000b8c07c0000b2401e13b1bf0002c08a46c00a80c42801dde06c44d002000040006e28a82ca280f809470cf640d5702554000c045e500680000899019380680d40149d1d6dc00108002794f10001df80000f000155ec12900061e01e0cb7e400f0c00c00003a50136c91cff0a5c05e801621dc9c682180dd624c44a1c030008300703f30775400a3860304806d89c04a7050b394249c6940c1a8006380a60004009ed3059151c08044c0000002b4002c40506c0cb344080008003ed09e0020277e009070d0b755455070ad09050cdd53908ef026000d21640e00000934928072000700a6807000031c03506c348a0d810000048200000900564355d18028e4800064494ca1400ad00000e2802c06c01c070048b01664000f5181402c800168200004d01000f78e2930003406061c00006cb4406d1ad000734f30f2827d3700c80009380015206800111666f020000087688000028f21c073a50103689024c03e800000427b93f508801800100ee3f03a89005070abb707b00da0d350b0e0e00e605d19e08ac06600ab040d890579109f0061150600300f00f180070d0ce000986ba9fd508000185128fd94dca23200220102c06c40600cc8fc32003c102c10216a2000122a812e7f8a005c00d95dd7f74000168f8c0d9e80203ea0783d300001c90000300800524c001d08301c548248d28620240ff800c50121301c834508700070706c00807700c0670820132c5b1a00000381080dc00400041b60d01801c025ce901bf722b76de74b0001a44007c02d22c0980c4018d57dac800f03654001a1c000045f1806d11db0063d36400081c00183173ca62441c24d1890004d98c6e4002324051324501a4800ea01a0c20067400000004273830c0bd44b307392c78065e24b02900000000775e89395160538804003dd8000240d00c0024c80166030000820a50004400040007d1703cc200100f03d0400001eb91eeef289009bd3136080740516cc04af5ad0004df24f8ac0005b90030341d399c2d224015f30046f00b01f7002e380001e0003c0a6138000709a44084cbfcd0c00004e06076e0103a594700009c000efd4000bb9b0d409849f80030dc4e20 0xedcba9876543210edcba9876543210edcba987653210edcba876543210edcba876543210edb73210edb632edc9876543210edb7321edb63edcb7410edc87653210edc73210edcb87653210edcba86543210dc843210 0x256dbfb43680585bfb43680ddd2ba52261d23a226e4d5d13a026a4ccfb9f5956e91d1ba27412a5d1ba1740e796d2d8a891622bc568a914cfb5458a914e28c503ed57ea2d44a8750a8d454812a84f9d47a8b0256d2d8 0x456400ab80156002aa0055000a980151002a0004e848998112c0225600458c474010df001a20033cb0668114b00296044ec009d8113a00274244c840992c12456248044280085011090021262398bc73010c3001865830420ad83154042a80452800a500149022900052000a3811460028c044e4009c8113800270244c440988312f0425e0c454108a988e52f1ca62344bc68800c22c1800c53810a700145022860050c08a0001400226e004dc189b021360625c084b8188802110001f462390bc72030ce0419c00304005f8315c042b81056818a78214f002880450800a10113f0027e044f8009f0013d02278004f0089b001360226a004d418968212d0621e0843c007c988e32f1c60c3341066800c00017c004d030700e0bd0017a382400048001330026418378306d000bc0011e044c000980112e0025c044b40096811270024e7c2f4f45e988bd2f17a182ec005d8d0b9181720c2e4105c8012c00214382e8005d1f8b92c172004ac008b801095a1b6002e0b05880114511ec6c3d9105c080b83a15e0444c0089801080016e0041418810210200168ca5cc308c379166522a0841c0081831006f1a2082d400598e8b0181323a25d74c82416c462d89052918a52b94255284044a8009501123002460c478108f0011d0023604468008d011120022400420088180103061fe083fd387ca70c00616c082d800590609a001fc002b8e8541c0a8
def as5 := bankPage 0xbbbbbbbbbbbbbbbb 0xc4a98b7c7b655f5c5a4e45444342412e2928261b151110090800 0x618b927820d5e6403579920d1e6403479820e6e6083b39901d4e708353983154e6885539824e4e6283939a20e4e60a1939921d0e 26
def ac5 := actionPage 0x842182507200e9b0320ca922c30024d4a0f44c8745003863b07222be9e809c2e8a2f909c07a01a139c16c76ca7b00589260a434583e804041b04a172899c09c1d88220a128ce00a0d940f8428478005862206e1a3a3c002c2bd0330a9916001813181483894fa051877c07810306d02842c6810050a1f016e06b000000016809c000 0x3e20699806354002f5140004011006f4003e58d46a8888000d0280f804301803780102ad620284e0c3c2c034b480000305b5752c030050052021b200eda4002c905b1c80006c04000d3918000c8c0a7800c0182c91c00d814c1b868ca46cdb40005c4b165e0410000800040008920a5280007dec4e5d223101e003006eac0522ff69541c701dc7800b0780f0000b383c08836000040fe8c06f40c0240051662291ed4010b61cfe600864cc0e576c001800050874078a0232c000000002c5d95cba801180227db01ff0ff402dfe1900000002701dc1f75d0d15e065b01401602b4cd5cd0002ca98008000f30064068c6806de01e000054800b845db1563cd01b02302cb5d0008d502970340c4de2407ca006000e1800003645d330e0038414340014ad950000c01e30329e77c003dc049d14091c1801c17002fdd00750601ae83ada2c070a72024860a0b082b945bd8050001bc000a9d40e8677b6c8170d40000000a6c1507a0c02c8013e9a8aab97831d300000007802822cbbcd03b8094000048000bd3c0202f2e3d50b0143b72e23c41fc808a7017c524001000a00116806e0d1d24200e8fc010004170740660ea60680228080992245001a0016a94940038cc0000c006412790002014f45400e838011498528090282703a6b4a4032a0060b9cd029ce00002801a008b750010d03cb7940518000008026554611f8de1007c19b6035d4d008200560074e3403f602cf0001101c17d0002ed0e029920b856bf02c0245419a216080805018575800300034fc1e1c40d002c04882073c0b0288e4826002818124005c4037b80c4a00d00c12023d948120f300ad8def78882100ae6802058003032ae6e000005e63a000204ab481e0a04624e48be0010000528b0582fd02cd928cd800cbf5c236000b000d85022053a00681aef738cb72263800203418006e003c000404c3f9b550050000049a88183e003c515f8fec8c007c9800026e38000187807081c0727b00011584c0d818097540202c367439603cc032336d6bf0092511000d00507000275e40d990178420373aa00000090e1c05444b5b14324dc8e733e4000761013c1501720bb8200144d02303435e58f54001d0000035c028e0151e301d028f0c1ba0001b602c0065cb10b5809c0940bc0024ac8e555426d500002ec806830bc680016c00a0b940c470255c0a6700515b40b7e16a101500800906802070ef03cc4c04400026aa5c470142141011080405c4856a74002810039c00588051c0c0000d21980790e5c82c0a81cf 0xedcb76430320edcb873210edcb876320edca987653210dc987653210edcb987653210edcb731ecb7630edcb7310edcb6432dc743210edcb876543210edcb876543210edcba876543210edcb764320 0x12b254c39b21625fbba23a6730d49752d45104f825b12fdce99cc37a6f0d485c7ea744e51a72c25802d9bc20416a9644588710a2043f3f14ba8dc4579ca8c4d0999612b6563f5736732563f52d45a4b38ed9612b6563f5736d24e64b39612b1fc3f57367362043f87b0f0fb52ca5346e203cb5427ce22440878a91509f3a5b4b04ccad954fcdcd9ca 0x7421ce0438407b060f63a1e6f23401058800b1001980058408af060e7001ce0032cf464178c81c17a202f408af8613200264183980073060e4001c80032800b00015f002bc00574389a011340e266044cc3098801310e1d2043a43874010e80c1ca003943071800e3001920457000ae0014d001c40056810a60014c001c2583811864218c83f17a7a2f408ab001520029600374b06ca30c6101787e2e408a9ad124562480836c006d960d8002b200548bc6f160d72f18e382e800b181150001b8b436cb06dad0d62c1ac0453c00a780145001aa0850c00a08313e0024e08494b06d020d7001a858318605c801620428000500189e801260424800490006c020d6001ac0034c08ac001580229c0053800a68114c002980450400a08313c042780c4c0109803128042506239cbc73830d9041b200348b062860bb022ae004ed6892001175a1ac00340b067178c3
def as6 := bankPage 0xbbbbbbbbbbbbbbbb 0xa98b7e65625f5a4e4c45444341362e29281b15100800 0xd00aff482afd00abf40ab7ca0adf882b7c322df0c4d7c60d5f09157d22a9f40aa7c262cf0b0b3c24d4f183d5 22
def ac6 := actionPage 0x85d8ce189a08ca2642cc5ef24d006d0661462d6c16806277b09b14b212001b38a84b08d78cc0089b532443ab4640044d42116195323802a6510830a2596001d2f183c8450474052156d18c1e6e2a00e08be0b60b2f2400363f904904938a00b11a081a81c804e0198a0507c0a2a2b00cc336814030a15807609100000000e8026000 0x4cd08bdcfcb5a020000008600180002400001401134e0001e0b1aa32c0db00d612c0d08cc1000096301721435879cd006e71c83401d3a0d63bcd0020001800c0000818007e6559000383bbb749d90040f003e0d0002be2f991da08206dea8bd03b603a9e444950364600000063e80d4050580c0340ea80d0e904068320e33400396d2d6323e54029589b1800d9c00c00c05a520eb80005000014031bd949f80df3000100057200a000c01401f0646918200690604e1f830000aee3203cd600038214016f5000f3a0021040068920db0013948a0322d1240949c0f119fe400475a90e00c004901f78100fa4000010b42c0001cc0200019000424fe535480340100380130a6000e0219070000d40000e1dc506ca006016060c3b09200d0400dc006200300483060f0ae08573002070801a300112801702df1012083800a995e6ce5fd7a08d00007054e050022004101fb40a1dc00407406c04abd02c3403046ee03880a020707ff301183a0001ca40058200600a05000118085018e400c12000009220059c22778fb9812d0e85c00800c804000000787d61050100000001564001e700120d55460308c02ec5500088cc51680ed1c8016bc9f02ee03a0d65896270202013c4031dc010027a20051c161c02c00dc6003c341865900a68f0c01c0017502000d4040a00a60000832600000001801344301b45a6c0216544446f0f65c7c600c742405000a8060020e1de04a03f4002046f700070000005531c18041600000024441e0026c045c59c3930c901a3c01000157a008001b49900d1c05866540040575805048401c008200b15c0100051c0ebc14080000348006d1a01ef8db16700802001f404868055c31c80d1700005d14026a19c4095cc10a1a7f2244c488a011203900821c00145c0000007801a63e2200073d2d000049eaa560094153b2a10828180129048222815278120c80a02158e60c003757d440008d40d02800138a7d00a03c020001ff504d545f0f67406e6412804008bc050024f000540a000000034028800d8060a00e06d6a02000628813b037c003b327b601888b394005808007c60118d5380a75ec1b09c4806f1000e0158297958002801ae1640e81c3164170f38d30808c0bc23580030386700c848324bcb0119cfa31cee0064c3924c60004402c32400000802401c70c00486500800084d814068010e2002416412c04890940c80221c00000000006c00801c14590090022d84c000314500c1406405120a90004980007803c871544060801508a20f1800000190091408414e90802952de09b4007c228020a6da012200054831c051d79b0000002d8580a433da10064e01b00401c3432d31690006005c000c00400e0130270003c05d70c04cbec610a6c00c50044df54059200a00f14761e0001805157db8450001c03400000005c06d11c100b6406c011b0c97d66851c070655d0002d32c0a803439412400103c00c70040c37404ca00301d0d44803dba9b6ce003000006f003d22303de00186620d74a2cc07b500700dc02803054132e01c180000498d63b570588533c0410610d149170c1c9141559010700050180038180737008a4c0a817203be0 0xedc9876543210edc9876543210edc9876543210edc764309875103210edc7430edcb4310edcb643210edcba43210edc76430edc76430edc7430edc98654310edcba743210edcb864210 0xb7d6e09011cb684808e11a240472dc5b423846add5b48884708d034b756d22211c2340d2dc5b423846cb095b2b21e41cb456828dda2378b604708d1162384688e11a23846da0161682cf51a 0x8be9a9302c260004c15470230e0101c0045f800ba1a92e2c25c004b8f4851790a04214005f800be8017c022f67c4d0c49a031343525e584bc00979a92d2c25a004b4f8961892c06258045d800b88016d2c250004a0e093a30da101b4005ec00ba1a9272c24e0049c08b92d1265624c58498009300179002e2584940092a30de101bc384940092be1226524474485a06e8e0d7001aeaa4a594940c1286824438488e8902d0ea651b230364006a2e993022f0005e008b78016f572b0aa56120ac23158122b0205615c94aa929482528c4a44894881293a23e7047d0c69060d2001a4045dc00b4ad1262c22000440bc84821095a1b00c5ec08bc80177002ec005d400b980172002e0005a180a99893306266624ac1895961150022a5843c008783174042e8045b400b681169002d2045a000b4189322f2640c4c810992c1265624c6245cbc8b831170422e583e8007d03173042e6045b000b60116b002d6045a800b501167002ce0459800b3189312f2620c4c41098989162f22c0c458108b160f9001f20c5bc10b781165002ca9053918a70914e1029cb04dd589ba4111462222444440889d10d3821ab03a95875000bf43158182b1f488aa911692203044198870e10e3a1e8d23386067000ad
def as7 := bankPage 0xbbbbbbbbbbbbbbbb 0xa9a7988b7f655f5a504e4c4544412e281b1510090800 0x9413be503cf95133e444f7911b9e44ce791539e464e793139e644e7b1139f444e794139e545c795131e504c7 22
def ac7 := actionPage 0xa5b946fcfa010a3532cc9d6c39006511215248a93680468050a5214e9b00173d68508f254d004c1d4c2746b147b0060df21262d7d46804667548212382740262e483c07988dc0d195151a830a86e04989328ba0f464f004c3ed44f049c1b80a51a2a1c81ca85c01c09240bc04385e008c38a834000e1700740bf400000003802a000 0x190001df40004019500030800008631741900f00060b0025cb7cb011b50e804400030006906cb6c071738c000ac06b030ab8000065400000059b1893c203c018590040b1c30805b3407400030f1a0680160000ab466000440051668b8d20477c30cb40f17280000c0aa440900f40602c114b036139da2002e03dbb0a00605e800004650021701283980e0482e0bd12c00fa805016024b879c89281400bc0001cc271ae0b31140081d3a400748a0f803a7a0d00003bb7805000002a6049f2100606bc0543419c0800000ca2000e01004e54005e30f7a7e041a5513098bdc2f6d13f00000880062e80207cc460060ea2c05d9600008ec42472180ca817e7981e22a80736200187bd00062fea0c8780d00008b933ca40b3806eb35a05d2ad10c1306c19b7fa028002ef1e00716903ef217b60a89a0b0220a800200061aa14c09832c040180181c00384b873a6003c203cf7efbf4681a68b800001fb0301d3c4610440618000002af8b17f582c0001c3b09026806050d20702ca801800e00002cc000001945960001294800806a00903701e300a2d4c9c8000084003302f1802b1951016ac270d0025b702d01300484060003cc854c8e48d1a000480013006c8099ddc2700eba81b008570c7f10f5d1140c15113814005fc07b7d09bc00de380c2d710c01e930007281688000000117370841dd3772ef7a189693e06cef150005001603f0030012060007900000281e7f2404ad6801d2fcd35329138c9c000039205c6002183cab5501b4c01c00007c10124c00082807006672985de0007ca3d200f00d0000000130056ce59b4000c77020135bf0011c00c07c084e68f7c044045a09b78070b6402c8780000044302a70e0004198d3379003a8f302e0024000018059e1c001410502801f1405524400152db6954014c0a4044038000005c01c54d280217d4001d01800041300040229f1c0d8b54a2d024c61850005b6c40140060002c00001400d84cc006b855c035b48063c45f30000002abd0674427141600911015039ba63c035740800000500b15d00028801b02197e9c001038029b7472d7211b4000008c50b0000c434052c1800d10049963400000002bb08a30028e5cfd004c028e34c01300000065e480000641219c00021a54bae8150255c000004000f02d05b70014011a61353e3001400320291a98033dc1c99488620c0d9934054409b9005110b46802c02867e30483dd1070068802de6af92d3efa4a08002990b30a7c0b4045800401100030700046d02cc05000000d64e6d35c008d800800c88f357e94860027e00c0e700e72008d914071809118008e581c019ea0d9a08a400d83880007980f33a000bf32601d4a80180179c160b0600c64531001d00d7b20990008adb0b01c3e6000fc04440e500b0ca3731001c0f2800902978082a77c140e9100054072b74db41be200d34001001c00014c9001403800143a6000033006fe4400e72000edc682c40a8c3400de00b00002a000023380941004a0e44dc13e04dc7b8020478a0983430de3b268ebc4005000580015f000102f76b80d43300b47351a800f700189b00100402e8401420800c001000068034000002fb0c28000f9b960001900ba7a76e036000acf2cc0001f756d27d0fe83be1f34234000050ff8b22332bdef6b6783b400014469372fd00000c01b00c 0xedcb987654321edcb74320edcb987654320edc987654310edc74310edc98654310edcb987654310edcb987654310edcb9876543210edcb9876543210edcba987654310edba9876543210edba9876543210edcb9876543210edba9876543210edba9876543210 0xb13270de9bc33e170144b195a238ce9612c057c2d825b4968ed1090050096d15a1b4023813824b45686d008e04e09411dd4b44d60ce8f01622bc46dd4812d60de1bb33a58078027b456819719d1a6236d25a2b4067cce88dba968a159e63786ec9908d04b692d15a0264238469bc04a668580af15c090af823 0x3260c634c4b0831612c2b000560e0981a930461ce8639c4073860e7551c20064800c59614f0029e0c63800c38216d2c29c00538bca58214b3525c86390307201191003225853400a68118b003165851400a28118a003145851000a20218706304085d0b0a18014346264204c8fc85230e6101cc0064000c78018c00312005acc4b0031605d2b65852000a416142002848c4c440989c12f461ca2039400c383184042e25e54810a916141002826a49d0c5e060bc0030c0460c10b982170002d4ac588bcaa021542f2a208544b0a3001462c27e004fc00c201182082f6145e4d0ac851592c27c004f928998a13341258943a0507400195042e4c854d8ca997953042a662540bca803150042a1104f61c9e9613d0027a0864408c80018e0031a0062400c201180062fa0c5d800b61895e062bcba568c4ab031562c29400528b09e0013c3825a8c38c407183188042d2005a4bc9d9613b04276004ecb09b80137561a60463810c5801880030c0060808c08317e062ee085a000b39895f062be6255c18abc393d2f274084e8b09c801392c26c004d818ca031920831e0463c10c50018a0030a0860c00c18018100300005fc18be03175042cc00598c4ae8315d312aa0c554bc9c1613804270004e0b09a80135
def as8 := bankPage 0xaaaaaaaaaaaabbbb 0xb8a998938b655f5d5a4b4543413e362e2a2928261b1514111009080400 0x49892b02458e4012387200915590048a2c80245324016a2920091649004aa24803451240130892009844800488928ba60492770224e3b011271d 29
def ac8 := actionPage 0x6888de786a005a0e53f867204e00b0ee69c82f8426005a6a74cd163b8f40322e2a580b1ac18012148d23858be0c00948f6106285326005a3d146b142402c02319982b0a0f4160118abc11450640b008c45606828290481301d102314100241900ca80a07871480508464040301e6d005c182020060e90811209f40000001b8023000 0x53b09040100c0615260053040091b7fcb40850cb51c0280007fc0004f1200001b00000b5800400007197c03c500a00060000e33ed4a1003413800001d501a1c650a94201dbc03b17124000050150300f550b10b034f071003c44817c024030058f70b18100001b461000a886515803803193c40007055003437644c0fc637f01700f011000000008cf60242c8242267d7f6bb0358e8000000900600989d9d0232846000104839fb00aa8031f0031757a10250217c0b91aeb20bd60a0000a03c25e00941d1aa0000c026d00d240c8035327e01202f019f0325d01ed51c000f5602124c01600400f0191801c04df30908868000d72100000029c24000200d0253630037641f9404026287c40002813801015380000580940654bc4003305bc901d10d18a3238003da00b2ee039a40a4705500000138e840200a0074060b3407467000c0380a5b14418c38b016d3d006039d002f2a00dea54d01400160000374ac0094001e8c000007701d02600170303601c70002114000a74b0001b27382400ff2f14805c0e812bde0b8e6adc03c015abf9c2580d8028505d0267c10272800080151892950d1000ac5112ac9024dc0bc07e6000a5c24bcc00010000002c0297bf70009a2a400003e9ac5750d0480603424008000069bb2dfce1ee55e2806c884058a623fc0000e40007020d94800ad3015bf5370004c0307c1c2500d700084800612aba040a0c83206ac1c9009404488815ac0360788000094d5039e1b000813c16d641705f60000059c406802e0eb0a00ad06cecc000945121e0d81e3b7e20030b0d273500040e50000880c0303105a02cf8f3f31530002c00006c10273aa04c00d904e04fa47ab39c004a375df55db00040d00000e03d020291e2b94080dc038303703825c003d940004dfec4001c13a805400a01c1f000ac288ae37f1b044890f5a00204098016f91de0400235400d88fdb2416b3880281b1900004b4245e04e91300f80724026096800d00003992007fac5e0a90006f60b0325339a0b981661e80001696200645408000a000c007c80078ca00542b1de9f481d570020ca05105e8f00412283d097305e58030b4000036054d07f17c000000068fd011aa4a76000000f82f8008cbe86dc020a0b400463c0cbd8150000004d50a1c2d85d205014eaa2ad5700e0000023dab00034081db0054807b2000de06508ff0364b1be00a512200c612e0f29020004e389e078400401425154b009a65b1ab000460000ab000064d3f1304003e340242a02900234e00000005a0ce0000bde6b025a801da2000e1fef2835ebd48000000dc800e40b07ec7aebe4000375cec1858016052607836a4bde064011a2ae007cad022007418183c01044a9bd72c83a32101b0864c00210528b2a16002dd21b30054f04f400bc014c280e0d0053412000040031d818900b51e2c6010000ccc0802003eb2308800000146401877800140090003c00aea8e0c01003c095d78085e000 0xedb63edcba876543210edcba8654210edcba76543210edcba6543210edcba6543210edcba6543210edcba743210edcba643210edcba543210dcba43210dcba432107643edc98765432100edcb9876543210 0x1cf13225f722a0d3e5d9722a0d3e80d5069f2ecadb56e9e5247f4fe5fc2d1344684cf9361201e659cb19602cc4805ab2147250c798e6f3dd2ae2594684b594626c2905009a12021ed351c96ef40d096c 0x7a800f43dadf795bed4ae1a15c352b76856e0477800ef011d1003a2046bc00d7801ac02356006ac08d0801a1023400068175a8352b66856c90ad9195b38a086f4100c8201104389f36f3e60c7cc10f9811dd003ba9c77000ee281aa4e354046a800d5001a90233e0067c08cf0019e58616acc2d2153232a60640a0881418f9021f2023b60076c00ec811c8003900070400d4001a70234c0069800d28119d0033a0c67010ce2eb4e6369490a9519528320c044180c7c410f8811da003b40076008eb001d6023aa0075408ea001d4023a60074c00e0011b9003720069008d1801a3023380067008cd8019b5e698bad3161582bab056560aaac04d51892a31154620a8d254ea429d4753a8ca744d4e8929d1153a20a740ce6811cd0139a0073400e6009ca003940672408e4809c900392006fcb0d1001a2023340066a1d43472348c468508d09d1a33a0165402348046100839b60536cc6d2d75a58fab21d56424ac841593daa77954ed4a9da153879c70d38e0471c00e3801c60238a007143ce2069c4023880071000e089199103330ecfa1d8ec1ae44855e24abd255609aac00396586f800df001bd00378006ec00dd219b90c372006d9a4d00e9a0003320c6615551232a210545088260504b72096c412468248104a19ca0c39400728d4db961b70036e0666000cc2eb035855692aac4d55abaaa4855424aa90ce4861c900392006d400da2a99b463362066c00cc019975e552baaa56154abaa94955290aa44d54892a9553348c6690ccd0819a0c3340066804cb801970032c0c65558bd0017a792dcac5b810b70016e2f2c65858c10b1801635a2c4ac588b0b1001620032800644b0ae0015c592b6aa56cb0ad8015b592b4aa568b0ad0015a432687e4d0f49a06134461d2863a44074860e9
def as9 := bankPage 0xaaaaaaaaaaaaaaaa 0xa9a8988b70655f5a514e454341362e2d2b2a2928211b141110 0xd30c24c8aa126c49093284849911ac4c886626446d13233489991a44c8c92264631132a34c1941a60ca8e10654908322143e 25
def ac9 := actionPage 0x85f911c4d400a9edc2c882cc3b02b0e221483e5b1d80646550931f290240232e88470c9358a00a96051dc58906500b09760e225433a812846ec6e0da028c01321a634054f0c800a0fe41501e6e6500b06a687a093332005828d03603148e8019117a11814703a016858c04c06202c00c41560040306050148022c0000000d800b000 0x900107840c048e50009d0810019174000809e0ba7050b027818814d381805450fd0040fe85f07a8e0071a09c5471020f076c0d0057069c05caa70140af823d88800028072b282b29c0332cd083c0f4c01ab82b60012180140200008130575d80400504008478081bc00509200000e08c8039c20b025e036f60de02d200003a60c1f8801d17e2e0098008773063c0b5503400e6fae0e07c00404011c00066c140733a00085a5c0a1a0009000df001801846ecc040201abdfa05dc820028608631fc800003dfe63e0b82b700000093d9f39c0b01c0174f20005c0e000c03ad712a80200b8200fc0910d96000703f90480303080968167f8010f5240180871cc0007a8c00009bcb8007c19510c668000658008d83631fc50af0d008ab635ba010660300b0001600000c38005381d58000000ca1800d5954d70a816a0100180c7a50b6cb6c93808c71408c301fd0001c14097110007126c0df00399000b10603be4004000a17c00c0c1019400b800008151d603601688000010c0bca8012a025000004a808421c001201c60c7e00750001045048471a00000d0016600743040dc7a1860004d04ac493482241c00620001031800060f0118528017a99539d4a00047581e501400b34040341009f70480a701144c00aa04020c400077002acab0011e04600ef0e300406f02805053dde0602f233000760d678f09440008090603c7c100c90d02510d0111cd9f65000deef0a1a80002cc0002e02800305b0031403202e0bbc1f000c04c7a0201f504ce0561da04c002fb0d8393802e79009201bc776491238223b74c028065aa2a200010ba40071eca1a4e763c014803043c02057802c16ce01f01b00000e14000b20044000300600014001f6c345e0421560001486d12c01804d734b00064011d00000001c78e45900200a00301f5400056071550000003ce5192c01910c614d7d90007d5e8601004550e0c0180410583601800d2105c0c581201374600408298075ffa224ce138100204640001a72849001ccac60002e5e6001f001988cc0000013dc3d12000fd800510160000000130009000170dee9b44aff053405b98001f20402000090075974054e00c0a100103700b02b0000006260296b0c48000013759c5571c61b02a2c028b272fc06a20cf21995380670003e0269d937601400a02e34cf641803fa7038c06140b0000005c06313a001540d000d6800b3b8025330e7800003c19a98004d1c047527040e0917db7dc00c35a0e2864480a0801009abc001c6a0e9cafc40a269a60568003e2d000196a40d05028045e37c3c7020c504a1f0123a006400b94110035b014403030793a000d8000015e498a0915190030831c1200019203ab00006500caa4c1de97da16920574800035a4015b385e3020c95ea4200a3f006a00e060064fb00007dd0550e0fe0d5a 0xedcba65210edcba743210edcba543210dcba43210ed940d9320ed940d43ed43ed943d943edcb764320edcba87543210edcba7643210dcba643210edb721 0x2aed3fa7d49a925198c713a1cd0f3c8062e559aa8b50a9fd3ea4d21e31c0777450eb9545a8950a0440790318e2a45089c3f47e53fa793425dc878c71462844e8996b6d64638a313a2653f9d51462844e80f4fe754518a113a03c4e898eea2744c870e809a132 0xde829bc0b37134d166994c6af5985d926b441114002270044c3881c00fb001f50d3a2246da0572232c61058d029f9b90591a0b6c414408290cea061d40b376106e800dc011b65d608aec112166092cc4956626acd55218022e004440088518e9a19d3103a61874c20dd011ba063680087008fa001f4433c0006cd75a4abb3955672aec55558aa42c54658a0488001100021f0043204860010c0121300426047c800f9011f1003e2006c808d8801b10036000878010db420f003e0206c400d7811ef003de006b5e574beae87950a3a85c08f6801ab7b5d2f2ba5a974b42e97b5d0f2ba1a974342e8435a01e874350e8121d0043a008703d0d86a1b024360086c08f6001ec58670acce0019aac3135662690b111962002190643008860190b822170042c0c850110a0121100422006a018d3021a60034a0c68c10d1beadf7d4f23a8a0350e8ea170241600685eda23db286a5d6d4ba8091a0121e00416008280104802080040c008080100801f4003de007b800f6801ec00340f6cfded8f2f3066a5ccfaa9df5240122d0244e007f000fd801f90d3bc2276c10e4069c412376bcc155d82a6acd4859a2eb34496684a2202444007f824dd811bb0636a8e6710cce0899c0c3380066400f5801e9
def as10 := bankPage 0xaaaaaaaaaaaaaaaa 0xb4a9988b7d7265615f5c5a524f454443413f3e3b362f2e291b10 0xd06103d40827750a08dd4090375020e9d4282a7502429d40a627503189d608627702189d480627502289d40c22751a089d528227 26
def ac10 := actionPage 0x648116186e0499c4b2348300460050dae10e3d7625003866d0771db58ac0302dc83a0c18d7000c157d19c48b2ca069097a894214d1e00683d2c470ea29200151c9622068f86e00a8d4b1042e6a390054626070142a1d803e29d028090f8ac0310f280c83c606e015850c01818203800ac142006060834002a05100000001a0015000 0x400f901c200f90740040ec011002b2d0c10cd0004894875307000041fe0c0733a07a00331a909eb200f0a8064080d60d9e240700b84207004a906396000260880034b81971400200005cc00033c911ccb28e4000028100c701cc05000100d82480020854b00da6114617c8a02382000180b6410a000000046e6cd6100c468400fb4009b400e480097bc0c132904d2ab15f004c1b071722001b0040333e0b00b25e023a8898138a04300a087012ea4fe8837140333ce06c029780740207980601406f3e0f0267401208900098018020168832067200a8284c121e02c001894932ad0000e207c00fc1dc6ff79037529d4001140cf78020182fa01602a9c0551562e13f6b034e887b55c0200307d8025d6831914d0076000f40011b400130009004c502602d000017b1a42c44e080550d00f7c011012219e11c005c20360235b9b6c100e95613033017000b783806183c019700048044002854a033b4a3da2c0a8000016c0dc60000f0001902806006e8a8b41a00bc402566a1e00113080dc000054b5132dc78000054068802150f5e3004309033000934a9754d8d828e74058e30180a00a00e02b45f59b6d70803c0e0fb40340a5a00c0132406f901f0ba009aba700d10400231003a11e00010053c501400993d0562741532e0080100010f10008080ed38a4090f3b849060915452000f50053000f2b498dc89b480302606003e80501135505131e0c0040500757085306b9b60a5cf5009094c0040001a002206815b501cf03ac082957580000000028c000436702c0ebe84e5a01b0280701410b7285118c378c050004480b9104d80899540e92d7e9a56d40901200580c7800068405e8f28017eb0016e32c010688e700402aa800000978aa3009dc02deca8140903725f00001c00435eb30880014000cc7df0c752c8c07000e5cc00072b620019058f2298e80b92e480042f6320480b01c281c45c1470003b80140608904080907aa383074480a0001c5787507c0008ca6042682c0fd25762b814054c19cecbfa800f702e3eb8003a7a03c400f43230134e6b405069290000e16c0005f2000e8a071551d1a414d000418000054b001800d1ed868066aa0117a01788406250058cccb001668bd1491f627020088c008fc7d2001a00164b90000cb633cae08836300b598f014bce000000825400fb038024782422d0000c6b14002dea0340a01c0b100c06800b62c00000c36cd4b0256a0006f480ad388ad000c3491e9000a123d8e008ec010483a0c970804000007b560680e300c0753120001f45a98c281e80010f03060 0xdcba630c84210edcb864210edcba843210dc765210edcb765210edcba6543210ecb73210ec73210ecb763210edcba753210edcba743210edc7430edc73210edcb6210edcb6210 0x90f13a1cd248750e61c526a494621cd2601b66ab9570adf44273ca78ff0f21dc39b6366ab856fadd5b6af529a4d46a8c47fae144287c4e8790e61c44c8730e22743c87313a1cc3889d0e61e43b8730f21dc39abb4fe9f526a492feaf55dab74f693466 0x492358d46a008c478fb089f6003a07471ce0e3862c86940830810c0e7801cf3a38aaec315586092cb1059692aa11d540122f0045e047fc00ff801d00239e0073ce8e21c1c40c3860073818e6821cd0c58e86ae8315d002421d40430809a4f7329ee1d3dc307b814e5801cb06394bad355d852ab0a1259220b252161232c21258420b084d5208aa44953c8ea784d4f08a9e0245c008b8b10900212023fc007f800e7011cb003960c72410e4861c0433481869000fe801c7123780071848df081be003f61a71c48deccaec685c326b464d31c7a32003f4047e400fb001c57b680f6c7d7584b52e50045a008b0091302223003fa007e9a0fb801f5103ae0071048dd069a102456008ac19150222a02452008a4091280225024480089008fc001f8023ee007dc00e1bdb3a79674f6c61e58c352e2685c40c8a0111403223044460c84c110983211044220c72010e4001c106372086e460fe8e9fb123700a6f800df031b7
def as11 := bankPage 0xaaaaaaaaaaaaaaaa 0xa98b71655f5d5a524e45434241362e2c2a2928211b15111009 0xc24c48e1222470830ed8c1856c20c4d61191cb08a9658c6452c20dc9681564b0a8b25861992ca0cc9612264b18a925c45492 25
def ac11 := actionPage 0x8388f9fc7a01714451647ce40d00848f58aa396b2b802044ac511ab211c09020d8220c95c7a0148e031085aa25602386ad87c274b330320326c3c12a289800e17e81c880e8b600a8ab40c83a6637026849605a192b240026202c2a0a919200960e08108305d38010052502412163c00c80cd80a0505230020036c000000154012000 0x4c4a5e07a9f78f00d74c1d5ac03dbe87003a1001e303c0edb3381800acc41f080066bc82069392f8000014000f00d9fe0521d1d00157018200307d017ca145b064e0717f67d16ae9da000c001e5e07ec0873000cf6c000001564a71500002e697c800005bab80ed102a140027240e4f89b01b0045750c0b30023f84000bc002f029031c8055a34503e00c7208c0020038124b7d5c33ae016de2a7000b1c101c0ed090c29044886000006f2e2003000400e291500f360180709506603400e3de0d005010a0000949c7600008fcc9008d3806c020640001404410020000ed6de069c11fa995b000bc28b8ce98094dedf2487000011801b281cdc86f774fa005807000201680f8c000d89e0d20ca63e140000a00196f0204c396aac417052420d022b030005df0a5a00c200f7d5b003e0338009ab3dc07840000023f6803a0ee720d35d029dc0400090789b000c40010500614a000003000066506671c0706d4301026bf020192d1a0069c0780470780d0304a5381457580065e00032acf349018d84a4d978126e026a040001076180801c0a5318000ba520000020ae038011b881031e0070ae1800002d033814f23808481ee4000f0818308a0d03509e9380e55018d9954fa8000d70ef50000025280382b1300d814000300f4c4032804e9906c56b945870047a0cead06ac9059e000030c00900f90f0066a0d40dfc0440065fc8050cd1d2c0901c0004800c026000000025605f114c8000464040000f60799076b82a8007817d6a6328a9e2f6811a5c064ace053b79d80f66b47501c0000e00000395f00b8056e03b00d0006cde4c3c202d000882fc08358806b702b9d103d0007c99c1bdb5c003900602708a1800c705e016f15000d6ecacb8001b7c90022c101b081280182000f3b3000073c5586002203000ca5a5fc002e644003e0000131c0a48bd180d9606002912d74a057e3000600030a00000a87cc9879bdc008068a65f640d6130f20d0536306000f20d300d18fc601009095b0c550071060ca6 0xedcba76543210edcba76543210edb7210edb6432edc9876543210edb721edb721edb643edc87653210edcb741edcb7410edc73210edcb76543210edcba6543210edb643edb63 0x528a4c25ecfd0606a0cc1959ea0a0cc17c3f87d0eed059f95d2ae54d29a514961f43b87367a54d418a914e2843c8a113a03c638a113a03d428a113a1e55da855069fd3ea4d46228407a8950a03d26a490f21cd26a491462744c 0x3276044ec00960092b00256024a60094c0922802450648808910191c82239063f0087e000e1832940452810a48193b82277004ae04954012a81252004a4049440128802500249e0093c092200244024860090c191c02238063ee087dc00e1002410047e387a400f3002400047c0079400f21f23f3d47e048f0011e0123900472048e0011c0122a004540478c00f1801e20046e7e840011b00210103c600784011a8020e024180083000ef8021d024140081dcd01b9a00003bc206c4011a0021b6841a0081c00f8001d9063ac08759957100228004300085d9501821db003ae0c75000d8aeb4f5761caac392165232ca02466008cc0911802230644008880010f802150242800850090280205003be0475c00eb831d3043a68670800d800232004600081000e93ea841d4501a86c0900801d1
def as12 := bankPage 0xaaaaaaaaaaaaaaaa 0xc4a98b655f5c5a4b4645434241362e292826201b14111009 0x703283722b03702b03e20a9d700a9d720a8d700a8d6242b56c0a956a0c95624495620ae5665291638291626311634311 24
def ac12 := actionPage 0x83c0fa203c01516e41cc76fc3a0058aca0cc3a700f00564c2c661936a0c0062588308ad94f004991a41744ab869064c8420a022501e005038ac4d0fa40e000f1ae42607110680848d1b124327639003c632876152c27805225e83a09140d028912461b83c846e007886d08410387500a42c2026040e2700540c3400000013802b000 0x36002de10c90015e17e800002a60082a00180082c0e0540b28392581d705b23720006f0a0a007987c0b2aa6cb0d31a7c0b0619c291c00bd80c800c80010d6a4ee80001d566e01a0e378883e0803be402ab100005382412c0003871531052b14b615e333c0098128000045018019c0e019800340602480020030ebe80c5800c6cc0600275139802e8d401dba379577e80f04960316212000605439169c0bada8058009e800c92401ac09f01e0bdc00d7a56f00008b4af02fc7381c021e3902400300000100089163916e0030743f060240004f005090e001cc73bc002a00007801382111814008132009b73a90791c804b0e000000018081a00c006012d281e0681e703565000e500146900074014203527410c010ccf0f411035a04838c00016054ea07804dfecb15429016e90050e0801a3f40b02040dd0603880054055a82710001a22c005b41014a20e000a3b02884d07c99200000904fc1004010b803ad400001808f0000903dc000a0ec4c8ab80709fcc01d1a80e0b84ea00de700006316d87920a0f4020a20b6d035030b050ca06005aa00008f0c0eab765cbf025cb00c68000000000301708001000f67652f0007242d14c000dc0001b34b1069009c000601b75b34e28000e00015f0045d045a6401c014c51c0045741403cb01259901009200028f24001647801b34019148501b3235892164110043804dc0000647dc0a7dcb8f80160030280c23e08c0850a0da3f000281d0c89f0658a400b800005c05c57c003b5c25970080354c00166c0380100ea40260000060380e701d0395be004440782e801113402201006c01c6a110574807470171d8ce179954c0770006406ef140ed31803130270397c77907023805ced1a01905011c0041001cb794a8004330bc8139000370000606860a139103005980050014530066504006f5804c820880170536e4081eca41898da7c01265ada0002f00000a9380be83bfc34a01aa5dee000b0000000e40be9e0026402c0d91024000c045407405c8c324d3b7a33e00b08803803501f1058001890030316a4d7a1005863881003c0ff3b00ee9b890c0033040dc0a690000f434088080b0361e300e257e0fe095fa035000c2bb87000b80dc0ff03fb005000 0xedcba986543210edcb764320edcba876543210432edcb9871edcb98760edca98765210edcb9810edcbedcb76420edcba9876543210edcbedcb643ec743edcba876543210edcba876543210 0x12aa1d4388310eac7d883a2724ce9732ce4cac41d13926e8dc99d0b4738e319a2be5742c9b920215cce9752e65ccb813d38c5049edc0b436804f1752e6502ce0e01bf726dfdbeb4167ecf1b8b934a293097b934a293097 0x315200ca400144002870050c58a1001421628300506048dc091a8020d02500009e8112e002490040862a38094680280004fe009f8013e8027c004f2009e0012401236024640080c013a81272433d2187a400f481273433d0187a000f400274004e6009c80138a29eb0e3d6047ad14f5071ea023d48679c30f3801e7004e0009ac40f48026f004dc009a400f28126d004da0499c013381266004cc1c79830f3011e6003cc1c79030f2011e4003c8009b001318024e7946010a4cc54517a8a0651408a28c54497a890651208a240931002622c4c20098409258024b0249400928191d8223b0641e0883c00f018a822f50404978012f0125c004b804924012481248004900478400f0811d2003a462a04bd408327d044fa04974012e8125b004b600968092c802590248e0091c09230024606474088e8190002200
def as13 := bankPage 0xaaaaaaaaaaaaaaaa 0xb8a98b7d7c7b6965605f5c5a4e4544434241362e29281b1009 0x8030d7b0502bd84065ec8412f681117b04833d84056ee020b760191bb2088dd8049aec0a0d764106bb00a15d8c0356c2232b 25
def ac13 := actionPage 0x8228f1e4d00090f6b10c72e636003076d87e346c2b802a376c3d17b415008b1aa61d8b18c6a0060cc30e052b837003860d866255523802c2c4c3011270dc08e14d616879149200809ab0a4347a48004047584c16362380281ff020091513001a0ce80c83c787800c84fc02418223d00b013200804094401260510000000124015000 0x3896093c00681c1c040f01562a38432994407580300c059000419c702ce0086601402c0000c4850578b0668570670f37c020300bc3a5048dde956f00000001070c5d3d00600f84005500cc2f0305a9df1d190080004c0000ad2ab00a50bf90417750000274650b4000006857010475f3400103c0a00000bc30f00070a000eddf00120e7880d1065439ad4e013020a066e04a00d0060a009b060024d02e6d8a5b0719a03007ff60004e80c100b0000a780f0a33019008700082f0b880c2f8003250300ef26be0f0000880050d10d80d0096c9787420b0b78ab0e0090f210070dd0480b0b0d1da20ba0b4000121785601b90c0ce0f6000f741062a07ea00354d9b000b107cf7005aa4c0bd0400303c000b0101a024681ada63232868124000ab0456475405c255503c0403c00009d4890021806fa83a200c0f0001831cc40018d746001800e06673e80574001c3589235201000017cb50216d0674e58350003675814a071a0040fdf80179c8a08801309c720ee000003c7ae04230000ed4c0048008f700283c05a80e30000f001a084339733800000140043278114b00024e2700c0900ac109450319a0281c957d0002a05f1cd008a0003ba011d3004c26801bbe5441391a7805000fbc006000178a4068380000159900580001672d0c9f94001ed0195185c0f018cd631e7100ea4b009508001a42700c6300000018820200e508000000e19b402208d0080401409 0xedcb7643ecb632edcb431edcbecb63ecb8632edcb741dcb7643edcb74310edcb6432c743210edcb76543210edcb76543210edcba76543210edcb9743edcb64320 0x2564a9858f1ce48f49bc59cb2cac9552a60b1c99612b2549dd3972a4b38eb9bc59cb2c3c8750e60d439796d461e43a87306a2043c87306e1e43b8750e694d26a330f22043c8734ae948989552a227be978c718798bb9552a20a9c6 0x14797283085065e98c0131802900c3ca04a1cfd08231e5103ca00cc80147812837d46000a380141061e4024fe009ec012f231e4103c6049f0112e0025c0051a009ec010800331004f4049e0011801277004ee00960112b00254064a2008a81112801e3006600894c012983250004520889001120128c00518049d8013b00265024c800990092a002540649e0893c191e0223c06456088ac00f10028b0051200a14b1420024d02510fa8c169180020e
def as14 := bankPage 0xaaaaaaaaaaaaaaaa 0xb8a98b7069655c5a534541362f2e2a29282726201b1511100908 0x61c6085c518216567005951c01644700595b40181249ba0c922e64308b998920e6c2483994c20e643083984c436613129984c326 26
def ac14 := actionPage 0xa458d270a801798dd1cc5d306400b4ad60d4288b3681404f3454133f0b4032208a1d899c8180118dcc0d04acc1c027460a05e225d1c80242c102a0faa0e401213e8128692cb204a88b30882e8638003c3fe03a133a2480261b701807981280150b3805838843e0150324020102c6b104810a00603082f003002ac0000000e000e000 0xf582d0000184b703600fec01808e7099003000e43000000849180ba27871da90000005c8cb3e0c4683d0001c0c0003d5610001c0d769c50001801d30ee800d85026140cbd0350081451e10001f602c4011c8027141e6301688511a000d358516f1583a80007de30010052c22d05400cb38030000059938914a80d000000c9e3c041b01e4db70079600b1800000000000c90042c07037403370144d50035db1002762050c801018001b00001259000010e0405006c303625000f75d0400022000090ab48045a0021c4000013375640e005a38000db3cdea01a63415e8009000170201506006880f38c5002d4e800c602813e072607481eca0a0002c004020334000682dff1ee896b40480300004d500031eaed02c00020e00400e01e18b00b00938d6402c0180b2801784d00030900d00b20000278d01d2d80c02530100c33143860d62c3a0010e3c36f402d00d0c32400006c00153403808c00047c33023c0008195a230d42484c000a54000e08a02705f0023ee28e1d0000000280003020154c02c0f40ce10040059204800cb41a01403b0000100ad6d69e2d80dc0030b2908802cdc0740030cc000cc5e000451d40ec6f78b402f9032c786cf79e00b001bdd000f764c00eb028a40018000003b0c071df562f4103043024152b013105a40184200009800e6a9405e30c00780a1000d006e058078198a172966682c506800301a8160115c000003291250140779c003a4ac310e600163584007018dc81a7610002b426386638e0002e0680c06824003400ae6b503380f82dc154b80566c9d0e006007463b60354b5800011d803000330049606c86a98f02c00003083000022fce000446801e01ce48a8a01800e089b3a4f9010a0199900832c4a00e0090017014500a00d00384065984a13807043e03840ee94a08f81061407000c04016400009da800020a75794e000ac02d20008c07ad8000121880c009172298055200302986594ce1800f018001b46b4ac07009aa3a05640042400408404809c0026077410001a0015c9ba0146020078000a95b35800000266cc4077024d000046d5f59301e66c0da234c1132600009507ba541bc385ca825f601ee0001e8000000448c34007c8000c032a80bf00c0018892854179722dac0d24009f314fb800603800d840c402c00600d1d40ab1c1c03419a4d016f81102c0c4880f07bf2cc768019a005408da31707b43000b487860a9819a000216400d0000ee0800aa69c0ed00da0011b0671 0xdc93d943edcb876543210edcba86543210edcba8543210edcb87643210edcb98210edcb86420edcb87210edcb8420edcb98420edcb876320edcba9876543210c9876543210edcb9876543210ecb83210 0x5eaa8750a9fc06b9750ea153f80c855dcaec5d6ba94f21576e8556b9a02f05d4cf1752e6724d309f13c19ccd9732e066cb9970178718d209e0ca27a94c4187f0fa1e43ba594662089913137cb4967 0xbad4d219ba3337486248cc480181092d6105ac04b080161012c10058204af4015e802bc0257600aec095d002ba0253c00a78094e8029d063dc087b938ee001a900348c6cd9219b0033446628c6c452188882d72b5aa24b547560802c1005804eaf8095f0029c02534087bca4f6831ed043d83a6a800d50e9a3003460cacd59290ea23194463a850650a021a10034200675219ea431b636100cb6c0966942c62857c00acc0158802ac0255600a90014f0029c005360c82d58ea8e9b91d3460868000cf8019c4867690c641973832d90859c04b38115a002b40056000ab81156802ad0055600aa80154822a30054600a88114e8029d005340c82410cf0019e00336a4b2d3d65a925e4f4bcac958b5179d1fc2f4e0009c00136219eb103d600a6401480026f0c4dc867a8094b0026d0c4d6008fc40f3002990c4d2867a0014c0028a004d4189a10cf38129700504009a401338023e0052e00a58014a812910251c00a0439380126e004d0009980920812400047a04a50014a00265005240899001321fa3f3d47e00a4440f3061e6
def as15 := bankPage 0xaaaaaaaaaaaaaaaa 0xa998938b71655f5a565453514e4c4544413b3a362f2e2b2a291b08 0x940205f220499e442833c8c106793020cf220609e441813c8a1027990204f260151e4408a3e881487b30090f22050ee444a15c89142b 27
def ac15 := actionPage 0xa44905ec580191a632187ee6280254cb20fe3c691d00385eec7c1d308a01152d783a8e1585600e15141986a9e3700ac9460aa3344158056401040189d8a402b1af8178b8cc700150b030b05a5618004052203c2c200d80561ef015138a96c0220b780708c309200d04340242e0cc6006c14e00a0c0359802805b000000030c018000 0x2800358c007926201520500100c7945c000c00a10204800d03bc4088228f2c304124000101174b00f7ec0001860007406ac15f00004d3c02f57000100c0000c2361f2e40002230c03490931ef64000302d0004089c022370335d1be01a7400001800000081892441612486c06914d201e0d0cc09602b2a40000f0003965970020089071490300540926c00008a7203480060c00030204f4060288b0058a2000000ce96816a000045a009080020356fd80e602f690000e685b261808000052141402dcf59c18094140d0ed012f107c83c708108c57000900001785d0fc0819690c680000090f00004791480254207301f4910502c400008003260055ce35ce00008800040c1400c29e26240e0302a917cc5b00c400004881601460056601b002a90800a058274be8010411a3bc5ecc207b805cc0abb50020180c0907d200008a0874000048000bc0114381300270069e023a6040100d0c0006df31ac008a8ad0006184c11318a0a000005ce0090f41930240f800406c4e4a1e04039bdc5600481440400bdddbb441533880031610201dfffc8180004550fe49507a016d036098000501e0180000a80802b931080403127003299541969a6007049367e0134fc1080249a8000064403dc00b833caec009701638800d486abf4100ace00414b03c18d822af0060114a0f493073c14d034062800201bb7000042e86067d04a4033600c0033c3681b963e504f442efe004813d32678404454d101c0ee44003c060002901140014834b5560000a0138a0800107c169dc4e59a2eb000e036c205529e60120090b25466a803402400003c001d7e3f6710824c00fc0003c100300903880800040c1868f0ba830a1004f1b300edab08009029003623a0e0255170000039c6dc80d7c04603a304800000186d9a900ea902782b83750b43a42809e02e04038082fc627816183044f00020ba0a818003900075500534979c59783521801b8f42d86c1300d55014ba0a04a1e0c656103c03060020481200040f837181407349910116000530af020004000540ae2b438e4c0f9bc00206503841404408016001d2b00378c01783e027007b5fe05808e05831002a00380000000b189d19922383c5bb820019d3583c410180f830c628110023428ea02f466090414e0000490c6f0004002d7100060700000302735b2a7ed8c1860703d40028111f0045ec000300f90000eb96dd2c803822005b004001b802da900240528e080161b194902c0f00080835870198bcb000d4142003c710018101802800ca102063d200441f02800035fc533600020e78da0c008b480002a4c0102000141f380cbf5c44803d7 0xedcba8543210dc843210edcb874310dc843210edcb8643210edc7430edc98654310edc865310edcb6310edcb6420edcba843210edcba754310dcba65320edc430d73dc3 0x101d0bad85aeb616b9f15b0b5d6c1f13e87ccf89f33e27ccf8a544a69456c2d8af4bb10a88c1155769fd3ea4966aaed45a854fe9f407774d1d4fa51287576a1d3fa78bb175aea54a9612b0e2b35576a1d3fa79019dcb4760ca952c256 0x48678bac89218d032da045b004b3c0166802cc0059200b180161002bf0057c08ad40157812aa5154aa29181905081f1003baaa76800e99d1fd383fa007407164022a13a3f29e74870e92c9cf2d39e747ece0fd969d0745728eae51d27062293a3f4aa73c00e7832e3045c604b2c0165812c80059004aa00154012a70054e628f8bd1f03204044080070c1971022e20259400b280962802c50258800b100953002a60254a00a94c51e97a3d064060880c00e1243174662ee2b59bd6b032d6045ac04b240164812c70058eb0b0559608fac11d58204a900152012a3005460c8081101001c07f68cdad19fd9536b2a295aa0cb54016393ac60258c00ae809513ca086f4105280419008e9b90037200a85a5071d1f67a5c0f0b804970082e00258600b0dad5cb4ab9495728eae40950002a03a3ea707d61173362e684500d8a00ad169022d2544e1489c00e2c3a888a465128c8a11393a27063ec087d8094f8029f433c0006cc00d90329c04538006b400d40329b04536006b800d6001a7
def as16 := bankPage 0xaaaaaaaaaaaaaaaa 0xa9988b7f71655f5d5a5452504e454442413a362f2e2c2b2a2928211b1008 0xa402888e9203423a484208e92022c3a4008b0e821421da18508568210365a08c09968250265a0a409968310265a2840996a210265b08409978210265 30
def ac16 := actionPage 0x84118e047001519eb1f4c2f0290258c720dc606e0d006457d066283541001a28da2692994ca016913b1288cbc47003884988e445813001c3fb0441f271a80151d581d8d50d3600f8cd50ac58729a048c52d850263233802a25702510149a401510380e06478f600f8644064262c68005827a8180a0b4d804609f40000002ac023000 0x16100e03e88689000202e005e403d26003c16870c708418c050ea8010295000000f0226774c553840311efb050e0af23f0240629d66d20a0003a2b541b4ed46000002fac19e40001e030032005a2460020790001047705038086021567ac1095000cd810aa1966500500c34d0f0071b1801b0004fbf207019b00041006d7cc6b0014002670025c25528c524510000b32da004edcd0011449877014041c6948bc060d28040db06a2f000048ac0d23820000e0c9d65f80a0683c76b200b1e695004400c11e1f48001c42a00310000060f9c1770bbb301bb01ded994000000800903001a09bc4995ba034803b80604bc0c055d2e800024ccb0035ec835c41ac0007384106b270320003473ef01600680b54008000074b0f7c0004000fec04b7240400305780006000175a3e0001401080140560158d7500340a4600403035a7c6004715100404140000d80005200000f4f1c0244b0832a14dc1f0b62004c9e0000b1d66c2042c0030903f0c5100f05740fc47660b00800602a87100962370160012a360210700076000002c0063f32200300d0340c72000004085032003d870280092808039ca0024002c894c588207a0ac32178006eb9c3000c940002fc958000d036f03c14c000d02920178c0c800a12b834bb16a828e2824a1081ed142300c368537701000b02f83f41f0210008176b24e00e9f48dfb00000c80039000b805c0b5338fed4590a55000000d4d050cca4e03587bb41a5051c0c1c007cc0600029c7d21d88a01400079f00000600e1c10154bd762ab5030639e310246c00247000000a903c600d0017920c9930d630a7b00b94080abb5da08006ee8900000800785a000223b8c001405629ed02d6f02804500151800003409038ad4a98e4a800021c0201c641c00208ac01698080183f3913e0d827ed086ac001fd8e00858009000000bb8d1920d84f31df600013336e800540005f87077e82a41628000781270028a0000903c90000c03404024c030120001ef1b46d3340b4880270d6a689a00012c0800101d6310147005200000c005fb59a39779d2c001bb9b0181040c000024534e4c5bc01c60005806c12950006ce00b5cf00400f0400120020220070000a834000a5c030600368058002700c6c00041533d77db72150024d0095840020dd4ee4034028b6a11cb60000614a14300b01e1c1000580020420001e4600e08029974300000d09a00a00300094724004218000a3426de00100900020200700375c2ef2c800200e65e38020b040 0xedc76430edcb64320dcba643210d930d9320edb7321edb763edc8765310edcb8765310edcb865310edc3210edc865310edcb8653210edcb6310edcb8653210edcba865310 0xfa1f33e2b616bbb79cf222323bc776ee9dc29f50ca154225139e694b893f80ef55b028650aa12ceba2740e7ace39ea8950aa0a1942e7d2e954280cd5d76aeb53e7c46d5e8ba501e033b86aea7d0b8efa854fe9f21742a7d2a153fa7c85d0a9f4abb50a9fd3e80ea7cf8d42a7f4f92a25342f576a2d42a7f4fa03aa153e7c6e954285501e0325142e854f89e4 0x65f004bd40173002e5005c800b880170802df005bc00a9cc5200323200400007dc0150802a03a44ee881148e92bb2148642bcc340979802dd43488348b41916892220c40a0081484fe0c1c40438822674096da1a4b1d4222284430f9001f21835e086bd5da1243425764690c8d0d8b002dc005b600b68016c802d80c5ae00b5c316b002d60c5aa00b54014fa1a4a1a43c0c87800fa061f3003e6187c400f8802d23f3c2587840168802b92c3a404ad4015a801df68674e6ae1a15b822b206558e69343508801db1c35f0cc71218e40adc065b8deb58416b002cf0059c00af5cd5b232b646498de7cc40f9aa9da003b40cac41158801d90256800ad000ec37ae2005640cabc3109822076f4000075c74e88e9ab0056204ab800eb003010058eacb040160802bb0255af2820110402206563aa0075538d50e9aa6c68cecbadb175082d50055e04ab1d945852342043c56804acf6801d4
def as17 := bankPage 0xaaaaaaaaaaaaaaaa 0xa98b71706a66655d5a53514e454442413e3d362f2e2c2b2a29281b1008 0xc20820be100859f02202cf8150127c0c8093e844049f020628fc102147c303085e501842f18142178124a0bc2010d9e14404cf0a20627850a113 29
def ac17 := actionPage 0x8291ed643201792cc124d8aaf406688a208a62505280284050402ba5ad401b1cf81d9291da800c0d140cc7888e300685c605c2a4191802c28ec28119f9c801312a612078eca8008089307c326a5600483dd834152e2380221ba8190a1405808c0cf80b03474f600a853c0340a248b028819e00c030815003e05900000000e0017000 0x40607c0106aa0cc7e5982642e05006c17000401dce6b828008100e1403b4a830008038000c80162d4179dab8a80a8ce8f43830000c0dd901ff3c00ae85e1dc8ae8300acb7a1b2c000080e8806d44008f001000608e006000181400eec038012a45f3063c096213802603b420fbb0e4341ec036bdde80103530440a07449031ca0480e0000602c500083c56108d980000b140fd09aa80c4dbc1d48000402400117f2e1cf03da0280810350a0039d003b8007a01906000030ba0023b701cd0740025c0603007d5c0064a2346dc018b957640003360d820163b405aa6078120009ac06c000080b42c0c81b600746ecc006450006c20003ecd603a081815017605881601ac005fe0e800d5403589c800405003ed000e6a15f4490212e88a03600314290000f378807492002e8001402800810016a940200010500b38481a08011024f024000081f0240ca1c0677500ac876664073ec1b02080901000492e2d8ff580146801f076390750a0010d737e4342c60b02800ca0a0b092407500002370670bb0000049533c7005c90d0404000212078560000f8690c20b000677c024147cf042e0007003d5a113baa0b09060e4407048632c1ad900070500c05df0040000a0071807006b0c37020f004c5094005717708150000194620a107409dbb58bc081302200021e940a20002003004062a80e441165413024510021700b2d601d50f5e040c40f45f0e00271405300f0741c2c677000e0f001983c0587da9003d1bcc4c0001090f56029800019bd82024c540cf12ef450005c0e376001d18d062e0f032002ac10340791d6000e7098f4b402780006800a0a8800006150000000000000a0034231423014c32b503081b102c0052c0e0ed8f0010200560024e651996209616146000401800281391286920182000a007d40003ce02800ce4c529d8929d6180c00429ce7e400010e626c0054c44 0xdcba43210d930dc930ed973dc93d93e8262edb3edb732edcb763edcb41edcb8753210edcb8654320edcb864320edc76430 0x80f622884898cd02203aa150c94ce91a82ec5d0a2943ae757ea2d43a85021ddaa14a65daafd43a854fe03bc3774d2152a584ad66eafd46a8750a9fc07786ee9a42a54b095adb5aeb5b5eeafd46a8750a9fc0776ea9d1021eb3766ab9d72ae35c2b2563a2139e6548b8d119d50a532f65de94d265149592a2534a32a1d0b9f73ce76543a073ee79cecaa950b696c2d88a9146282f05087d0f9c06776ee9dc3b753ea110bad85af0e0fa1f1 0x175902bb204864024be40179802f25549e8c93d0d27882330c466008cc81160d22c06458248840178812da5958aa2b150d312ca5b514b6188800110012d8005b086980010fa1ad00658008b010d2f802160657e08afd392d0021a0042a9cb10195f272590443a0085031098e9ab1d34c04b5c016ba1a610c43818864096ab2a89184361886001098ea11005d800ae4010716204005d600ba4015c0020d2c40600ba80174002b70041e58800e918802e70056a008301966802b24e54c9c91c0102861f2043bc3a72074d3292a800540a4924e916801ff0c3f0aa73c0973022c800550b497000fc021d2
def as18 := bankPage 0xaaaaaaaaaaaaaaaa 0xb8b6a9988b7e7b716665625f5d5a4e454442413a362f2e2a2928211b151008 0x28c0224e5088451ca1008a3c002313b800c62565082072ca1041a59420514b282422965808452ca01a0a59502414b290502965080692da040a259c02844b 31
def ac18 := actionPage 0x8308f9e0ae008931c16c74d64d00588e609e385e1680523d904a19ab95c0911cc6228b948aa0088d940e44e907a00805da064253f14803a27f02c109c11c017113614074c88c04707f3090325c4404383a584015282301201a2c1c08911180100b980a82864f20cc046304010222800581ae012030a2b803207900000000e8020000 0xd0180e00c03740ec00c680350f0206020004500694294400007035c028d6b00609a80716c60009c0331e0659d50022500010ba80c78e08a5c0210d80423190181e115553e48003801161112820000af05803780070680000017710024800b3e40b52c60a00003a925701fd5808e148408801018d206a002064006e80c40dad38074480cf6801905a7b01ba200831a340c76c0242dcf34822a1e0001c318c05418606000004d2e200000000c5800a0186d7108e5ac0c0c001400684b00005f0c2b00e070d953800a8f6970606700dab982af3031a0082c0a9c0001de0450007f1006f6ce24c000000ad82920458001c152823558c20061608cba0100bff4f4001d206868002aa78035d4af3a04d8007b002a8003ebc10827231c2006f4ed835032f404801ba0247001606c80053da003b2067c021011a02c1cd6e3c022eab2fe7b6c19009002a008000100450040f594a00bc2b0086602140005290cd09780c096c0408ca04000e306c9001e1022806d65060a09b003000d73b7d0b310571adf0ca07b08f096200300004490003f6050356a330534855005300e00f091e80100f0290331950003908040f95126fb0080a406a00160482304001719930a740000530581b10792000800ec4e07c08007e87752c71000010d457016e401b600289c83205029f88c00419e010000603409d8405d4092819459090000322200000e2300d1700800000f59beb1d03a610370d890ec0261e4329444000800a279a905410ecc0060d93e8a6000051ef50009f1e500084301d0480f3808a183e001a790f43603c1fc401788168040990000f3c01401c603d8cc4006b42400ab403e0160d8862000e6000000d4045206022732881e384409044207ed7f000cd09c6a68dc600039 0xedc6321edc9876543210edc9876543210edb7321edb63edcb853210edcb84210edc76309875103210edc730edc630edcb63210edcb4210dcba320edcba53210 0x12b254adc5b4b621c9f53e67c4fa9f3956e91d1ba27412a5d1ba1740e7ac449a81101d50a86432b696c43b8727ccf8c3c8727ccf8c3c8727ccf8c3b8727ccf8c3b8727ccf8d265149592a2534a27cd6d2d8af750ea15268cd5ee0388c 0x17f0623b004766a8e8b11d012fd005c6188e4011c8c1e1043c200bf4017e002fb025f07c904c5208623a00474188e0011c0d2360646c00b48711b802373f46c588d80176002d161506008d4b11924324005f20cbc4196628aca4e594a2975392eaaa5500466208803110022c300586aa95001179d22c10456188ac0972802e000596008ac4115179e4005f000b8c31150022a025c208b20016400229005ea00b800112979e5025bcb49701118002246f5c40cb19bd3e802230c4303a74474e43e2e000586f89ece91308225905eb12bd64146c4a8d8350e54898911340ae56c5cb029fdb13fa1a51204584c8982913119fc
def as19 := bankPage 0xaaaaaaaaaaaaaaaa 0xb8a9a7988b7f6a655d5a464542412e2928211b1511100908 0x4c5323585323685323491323495a83491a834972834932834957034953034913038046ed80c6ad49868d4b068d490735 24
def ac19 := actionPage 0x84a0daa0da00f1a3c22c5f367d0078c3a102298e36803a5af071144007802f27e836091d89400a92b417c46ce1f00ac8160b01b5d4500323ad4440c278f802c17381e855087a04e89e40b428681e00c43828301426070046123013080f120010073607030608c0c802db028102446004010d80a040c2300240510000000130015000 0x16597a6e99f4078340a03402f4d40010ed9e51c494011c1b5f40062f55b3ac319a2058f6d5800b1a00002c0059a2904280c80f9669e500000002cf3fe029834eea4e5cb40a01a00011885e8400000b2816cad60e142003818b51e0500034cdc0f801f100061bca29801d04aa0ab4a770237064e000f111dca088059b817ab70059800519c6001a6005086054000012de824059a16881b401402042458ad402e6aded81f07254c5e2000000f4b6a0c3060600280fc032b018824e80b001060801098040000000080000d320040068040c6c164800412006e30d175bbd20820117b0e0f2d770000f188f034760cfba340d14580036db0100053be465a4c0006508661039c8001000244b6bc000012250ca3101c22018000440520044340f0684d312612404a624c001140179a006c027ea8c1f06f40017209f05b04c150013ddd00d029820601e7961ff06b5f36400700d500002b9602b1d13440d482cf2681800905d83c06135803a0fefee5df40000289b480db70a03bae07e000001eb02000832e9000500c1a00d436800561ca73563c5f2866b80b080d5a026059007003c07d489681db0082450060947259e5005e000873ff4000c8000001c180022094c8d7807570002f10300c093670208f0001830142c7f4054012ca4023c2550350000e4a8024002601576000a26f1cfe13c800078dbac0369f8034004d0300170000235e632610353a4464a55008c2002b43886008bbf18800fae4028460d240a01ee420004002877800093c0224d8ca5d221a8003810088ae000000b8121380aa703cee000d0b406bd490016fe800000000ea46003cc0780cc401151a0253ac0003900050cc8b160f105a51c01680600004e068c8304c0049566040000c1654da00000b059a08800f4180e05825378878800b3241931d69f812011815006206a15f0064fb0300001936c03123500b9d62020dafc001c00eec001103b1403140002d700065bb4b0030042400350805c037700077e58c0186ef3c000101c31a18005c000001e100001797c035939d6ad9b902ceccf9d34016cf00a16ac0802800501eca800a18080908ee204080018671000630ea20250420009007805d6c6d985fa084500b9202000c009302b00005b00f1b090808ad7001c20991a4c52ac0f41c50a4210096900a0675900890930000dc00ed6f1f07019420d801040028e7001cbf15e00000022c09c2c6b029c01918703840038094e02c002913c9924900248000 0xedcb876543210edcba87654310edba876543210edcba876543210edcb764320edcba9876543210edcb876320edcba987653210edcb876543210edcba876543210edcba876543210edb73210edb632edb632edb732edc987653210 0xa594a6932a253e7c6e9d29850944f889812f4b294d264a27d0f88987e44748a8ae15cfc9cc9b82bc570ad9150b06e08005653c25c4b097748e889b935744e809a933740e7899930740e789993087d0ecfa9f3 0x1998030b0261008b88116f802c4044fa089e4012c802520061204c18217c052f53351c14a34cd37002512046c00cb8098380307045c20cb78116f0227c064f0089e00128023260864a00c8401900030e0061204c10197e032e50059462a58193f97a66004ba0093c411c0131f0057200938b124ab2240063e00c78018e8031812600c0b780969012d10057062a6409318024d2c49004c6c118c003130456e5e9340125962470665404c8c018e0031b0063400c64018b803160062800c480188892ff065fc0cba8015b18a9831516009300125162460661a08aa001542b25304492009240122813210462000c340185803070060c04c14197e832e60454e00a98c54b83280044900091c01220332b0664e10c8809910230f0061e00c281184003080060a00c100181832fb065c808a94015298a95064fc089180123002430c5223890401208e1eb003d600c0031480628e00480007a80180062820047c007a0017f8628a0c502008f400f3812fc0c478008f0f4f3179e6
def as20 := bankPage 0xaaaaaaaaaaaaaaaa 0xa98b7f7b655f5a57504e4c4b46454442412e2928261b15100908 0xc802e1f281187c20466f0811b3c80554f203153c21854f0a2153c30854f882153c20664f089193c24464f0a1193c60464f481193 26
def ac20 := actionPage 0x62a9d5fc7008a9464138e4e63c02749560966c69350126463045332e9b009920282018558ae00a8ed40e0b09c9800646ad86a4f4a4a002631d02f2023bcc0941688150c1120600a8a040904a82b300504698421f3b3300281f901e0c989a80940d680b84894f804e050c03c16347b00781a2010060d2e803806700000001b401b000 0x76e006020010bd27201008a8001dc2db01c965b04020885e7001aada505e000048d800080000e125e92a2000000040190f85a06a465074276001307800cb1a569517036e06528d4100f381606e1806009c021805814e0d010087a10268c007087a60007030000010c0017817400b240d7ac6d4800d58c0975800003e0739251800472aa391defdf6900007c74000202905080008158806a93a4005905184007f44b054de00c0207d000342001c273ac0d030072380c2000e02cb568da0038010008101c000800d1aca7015c860460198a00c1400056895b5a801200000400e69000ca3d2b2035008c0100c00682a1333c60c593003c304005a001e001c701ac00b9000b417d5dd70e00ca50e2000296000ae900069b0f47040c90610f50c8340030008f02c010e00824025a801870658273003080008066407d2020c7890037d63802f06d80001003b64a70504b8007021c807a13a0206c5c0603da0a2402681a80218154be047000b01f8004c0002c00790080240801c081a02000140480a05b064711d6085631018c018a363d22041e19308020d040d5e15c20960bea004000300f99d02f00629e86a2f07b5005001034f03c0c6fb400b00030c005ac006b1fa080006b1bf014e05a5467a80071920801a169c800c81c0ae816800c0b20000018201880403a00540d0a40906ea06b00cb75451f1200034e8e1fa47c00b007b33000b58420780d458af000ec598cbc1e0003403100a8f018994b54880661700482c000255da86005d7e797e702ca01000c0134005ae447854001406d6c08830052c09000240074043befd6018090242b8002ab02f00010084cce2400a836c5d818010a0e5e6c2240f0020088802002242d810683c66af0000ce8004806400c0988120d0c0d8022868180d67100108683f7802dd900015fca74881d3f7c00a63a002860769c004c082bc03 0xdcb74320edcb87654320dc98765310edcb98765310edcb731edcb8731e740e70e74e74dc7310dc98654310edcb87654310edcb8765310edcb876543210edcb876543210 0x87b0e8fa29f13025e9652ba527d84c898ba74b197aa1132261f991e22e2c0575887e6e65b59b937045c2c858b97682cfd9ea866e4af1171a774ee5bf3740e79ccb4660ec14dc9b831452ca5117b9768ad059e7e6e85d039e732d18dc95e2a845c6a0d3b45682cf3f67e6e81cf3993725708c529a51498fa09812f4a6945263e82604bdd3a52d554f9f113025ee9c076aaa7cd889812f4a69332b53e7c696529a4ca894f9f1 0x64e00c40013b833210061808b2c013b16267044bc188e4099300326004ca00c951935aaa64004c886798fcf30131e464d258978411f1f9e10064804c68018aa3268004c458974411e9c23a0262c00c580130003230062a5ea28bd351625b1047604c50018a002d02c4c20097c018981311045d05ea24bd42962590262000c40012c0130f0061e0095c118603306045c65ea08bd34802561c3c200c880187002c52f5025e9a0012d802551047400c301984822e0044f6009503115219e4006660cc1c01640227a564b800971592980253
def as21 := bankPage 0xaaaaaaaaaaaaaaaa 0xb9b8a9a1a08b8180655a4e4542412e2928261b1511100908 0x44868f60868f40868f248717c046e7404767406aa7249327448e87608e87408e8726868734868724aa87258a872c8a87 24
def ac21 := actionPage 0x82f14614d604c144c15898f85902609720944a6f16805641704722b216c0131e76230e189a40040edc0f864aa6d007069a0722c4d34022630503214a10ec01a151815894e09400c891409042624702643ce03220220f81581410140d0e19809207e80784c54ee00803030301a1c67024012200c06083b002604900000001a0013000 0x5aa240084001000e81a011eb607949ada207800729220b81a04d81cf0168f8140001cc42f270762d196170148220c4000000f2400b81802b80ce8ca0078a10001a29c00a81806cc0c080fbf9c000012c8602e88020288747d40003d3a8f274600000000ec08aa268e68900401624562a01902fd600052f030079dbb5ad20d3921024000000064ad3db01800000f60008032b383c0000393392a1d95f2d1014a978f80009d90a04cae602bb00c001cdac40c00061ec11fdb3b62530682e01006a5d802e20c04e260e581be81a003dc41c8380be4e4900a200b0a30e000040054e84000b102380492d3a7aa21817000ae3bec50001b0241100c71680a051400cc10336c00070c94810bebd027102f1380e01012b6103d34b805c82c002429decb0003603cc00040e02404002c181d400e00225881816001c42018111f0890700b0690a46c1d0450c0061a4492e0600028140009a30006e6a625e840d003600800052d9002c631c0a00fce161206012c6197f7aa2a00003501a2d348773c0828eeb509fc001881b8690256000000a80050393100000000000540184080d4650040a005c7028192956e60809024a4000087bfc10000e31c0a681e42b406181ca0182953800004020012613564d1f6db0494600020958000595f0562d011d920800d0e330146500a9e38ee016dc027800e81bc003d5002323ba0001c14000004d2df04801ec41c458d97d1c00a412a0016db9c088066144180e1f48005500d000005802a0242b0200002cc8f94e0f404900844001212cc045052002467099e04200400001318c0d2380025c0333eb300603e840f81be73811a7290ccb400fa0480d0f809831c050eb2fb0f00f0f022004080840f04c60827a0fe92070066065d95b36c308000080500207080200798082ac00670d17026c028083e83a109944908008e66e03ac0c1a000000d00ec01aecd18980053600649a 0xedca8753210edca87320edca987653210dc98765321030edcb987653210edcb7310edcb8765321edca754321edca730edcba9876543210ecb731eca7530edcb730edcb43edca5432 0xe80dd1732d05082d3a02e65a0a105a20416a2043d8787d84c51b8f11ca12412798e896e1e73985f88389fa5d46e22bce546266584ad958fd5a49cc5422644c4ad954e78b44ad954e78b44ad954fccb41672ca3b25539e398728e49c62d12b6553f3732d18e54b195b2a9fb3f373273258cad954e85cf0ec 0x7300026001ca64094c862970052e009cc0196862960052c009c8f93818a701e482249040196072ff0c5fe04bfc017f872980c53004a60014c062950052a009c40195803260052800a4c1192803250052458a45193821a703f4827a904019497a902c51a5e9bc711b83320005185e9b4b136aaa6410478188f0018f812ec625bc00a20b14031278314c604ca4018f002872c4fe909b84920202360265400ca80994003280063a04bac01758128b0051600a18b13f0032a0063000a2401421627d625bcc0b782941802832c4f800ca4b13da31e55a66200ca00174802852c508589e401978128f6250658a0d893c16278
def as22 := bankPage 0xaaaaaaaaaaaaaaaa 0xc5b8a98b7f655a51504c45444241362e2a29281b1311100908040200 0x362242932053893431309346130932c13093a4130936312093431209366120934612093626409330192a320932c320552c6405378b405278 28
def ac22 := actionPage 0x837185647204f93c31a0b2b081003898e0c4555024002e46f05c28a292c09820a82b12904e80098f33140847e82004c7260943e3823812e33b03c1e180a002a14e81a8e0949600c090c0986c342b00a834a03e330f1d804212901614052d401506c80707c2124009824400c2a08a4046805d8040a0358810e018c00000028c208000 0x1600150500b1bd203372c76ffcb20c0000000389998220fb1e80140400125058e002374a81c0abe804940720cc10425a06cb5d941802b56389a03030000d05030e40d02697817b040000e517bc9b0b0000000004fe349380b8040246800000503220f000000d0044c005f1d0024230bce6304c6e2407a28003a75a0388600326780030000104bc60000012957024000000762d009da60680516196804c0007ccb8152053dd57802b00e012001183020a07b9e7381203bdcb7a400d9c00001c91816c61bc64ac260000000049000567009000033970e130aa34200f42000400a04de1047500460b3747003720050150000c002000003c0e03e680200f324272184e4000d184850680202ce9dac24000c04380e418821e7480002204940120e80ee000010bf0000700000c4618c1b0040002336020c080004448073804308e0861003538e01c070282e181a01100006cc22000138f2b01dbd30822084c70140b3480600de049170408ae01ce06498017400901e2d780b029854880d16800f0000001406080e7940903b932100bb818e0022000c0541214523008091816a0402005c003d0d6a816a00c19c432500000008e04007a00040a006050f2a6dea000830004fd00548c21005ad4153bd258006901ba0000048500e04189a920500c2000640000c14e05eda3013a339280524e08b809208645b060000003f066a2a070394b22800e1de778000001c00000a06c080001cf818b9a9612b523ba120900070660000d660480143d805e001f5000b30037010202c08c540377402da5601800100c4c02fa0582c0037812f0012600107346600000a034c4500dbeb80903aa90b405432203bdef40d80001f41c0029c83806038c00a183b00007b8020bba6900150b48c619fc40009303c1ef01a7583cf0078cdad0bb000050915302f308f0cc070a00a00dce0f8279090c070b306e20032ac792 0xedcb643206edc76430edc98654310c310b6edc6430edc76430edc98654310edc98654310edcb7643210ed7437476430320 0x2be574ae2dd5b8b69678a511c2343c2da5b023445ada5b023445adb5b4b611108d1160696dada5b08904708d11606d6b88d1162244688b5ae2344588911a22c570ad15951a68cbe97b1562a4528a2a992ca57a072c257cac7f0fd9faba25a12162043f878b41522a2542954fad897eee88e99cc3525d4b514413e095faba03a2728d39732d05084f023 0x1d2f3434ec189d8013b2aa2f4645e208bc19a0ad2f42f5da08bb4b169802d30267e70b8cb165802cb4650420a08099e003392c59400b291940882810068400ce4b162802c54651420a28019c013362f5d208ba4b162002c4026805eae4115c962a800550ac8a419a3803400067e00cf8019d18b000660062bb01976302e12c56e00adcb153802a70267a08ce8019c17ab80457058a980153033460268400cf4019e0033b0066e00cd8c57f832ff315d60cbacbd5b022b62c54a00a94e96eab2450048a8c7fd0cff881ff0c3fe00cd4199a02334025e000bc00177812ee005dc00b5001992d3312c66204cbd597d002fa565da00bb41199803330466200cc401980332e005ee00bd8017a022d3005a6009d4019680274
def as23 := bankPage 0xaaaaaaaaaaaaaaaa 0xb8a9a38e8b838065625a4e454441362e29281b1510090800 0x81114789055bc1055b81055b80c56b50456b80696b4912ab890d4bc10d4b810d4b49854b4d054b69054b49294b4b094b 24
def ac23 := actionPage 0x82e90dcc1c01191841587ecc4d005c8120a03c591e812a3b90471d260b40281916218d118cc0068bec0e8568c90024457586a273f23812228702d109b9a001b110813074b89200b872407c344a39005c2e2028181c1480500dac10090b19800e05860603044ca007021b0200c1a6402340bd80a03061b801c034c0000000d8011000 0x82b50001c03000006c1fec16e2a58d019250000023876af8235001101c3d00de0b80400001e4a020a8e4229861e0a6b05d0101aa8f640ab4c004b00020ded3bcc0006d00820000066aa626412403a051d200181cc14207a520023843801f569726252a6800a00000399de06cad03c150036e0154ea024bfa197d0810c015205000603585000506400103f6f82808b088a7fa0a640d0010e22cd70440003c04481dfc89e03880000221002aa52e806dfa0e00e02996007fad580d16cf9bc0c00018b3001634354a7a1200d4f90000c1942c63788e01e0c8017044004f89e626b0001000aa0b03e524005923b8a00238100000af5b03c304c8c034001d49d41d73f0d20101403800f20020c82e014927183600201d0240f01d050b0050049d02d2800082a10100a285113c4f0740000028066b849e003b87802ee4c1c002af171ac924090401e7000c07008714000001f5841c4c40a9017d383a0c16e0001642800501fd9b400018d0806767921010e70007002964001c038080010a06816d31f38008007180d2bc00500126b16f0082980403d8b501058ac0c0508d0254000001000600ac8043ce078131294c05000a2800f01d405000e21142c832078de1980dc002a803d00043c40800c0c480902a90741e501402fa5b5fc60519204977e11c115c18556c0702f60e02a04035a7c0187bac3e5681501e5bd5c0080010000907061000038cc0f3cde00a0d0067c0505ee9230805b0757109880953027d010019100516d20bf00c7702004c70a314062a300ac00000e0be40f76690aa000186002206060e087901200000e40a930d0c47860110078520670302a000e2020b0025df500ae05f20100b00950af00371777b0d 0xedba9876543210edc9876543210edc9876543210edc9876543210987510edc7430edcb4321edc765430edc765430edc76543098751098520b320edc6430edc643 0xb684808e11ab684708d1202396eada4442384681a7f0fddfaacf33e6743c05e054b716d08e11b6224d2c03746e43ead811c23445ad811a22c4708d5b6b611008d1160656dad8440234458195b6b611008d1160656c08d116b604688b 0x19a882351006a210d3009a60034c0667608cec019d98b192f63258c64198c823190063258c0c018181347355fa58bf4017e9f2d2315a40cb48d57e162fc005f8aea45214889291375fc6abf8b97f162fe025fc00bf8d57d962fb005f600d1cd57c162f8005f00cd0cbd7d162fa045f400be9697bab2f72c5ec00bd801a2962f5005ea8ca404148003483a5e4aaa31194621a8c1051818a300146003402c5cc00b99897098ad1065a2c49f009a28033f3a5f058b940172a428e1251c04d1801a3013440068800cf8b975162ea025d400ba8b172002e40068e6ab8cb171802e30068c00ce8b171002e2625c2c0b84b170802e10068a58b800170003442c5d000ba0b16f802df
def as24 := bankPage 0xaaaaaaaaaaaaaaaa 0xb8b6b5a9a4988b847f655f5a504c45442e281b090800 0x801afe090bf9042fcc863f1243dc491b7124ade094b71262dc4b0b71342dc590b71a42dd490b78242de410b7 22
def ac24 := actionPage 0xa4896ad91c0511be4220ad524d0080d020f6549c16803a613078244d3080092f863a912489000a16d41c87f0e5b0050ad28cc377a46813e4dd05d19361780a023282b8a97d1a00d8ffc13444a28e007c7128781a454600462eb033099b9f801e13ca13028a53c011077c07406387d00782da01e010e1700620b50000000078030000 0x2c05cf50c21800001718afc008878a00c4c00090004d748629d511d8cf8501f011d8f0d8f0a00000f00064a74000f00000b10f29d15944038b01f0107c01007002800092003824dc442389fc0abf06db81df8b9f0000404300b80400000204c0061dca2809a2000001008a8c00080141e4a71280001c20630003278ebc2a00038a559806940477ceb0001f0a629980d0c9900d019d005600641aa001b2d4202597e002fb0700000a201214188007618a00812d055809827a00040c00e3e811200207b7202000019c6c594a001005036aa7a0e0e58650315b6f0e1a0860a9970002d60dd4780002fb43e000060000a00600b7b52a3a816637081824080020038002000000140482441282500002db941028060258910200397450008007010340000a8064070f4d030074b2db3c804024034400044068008330e69f5c01c421c08061971200338010c44040f00c54004230000001900019b65100a06cd7803f001409365e059c00e5810000106000004c039a99b19340c156990152003600200036480d45624b1e7f0e20012c1039803409f19400bb6ed002f9c90001603c05f0008a3b59000c007c2000007bc743070c1b48ca000080360e04265a55a0050123141303f71b08f1635f500db5819002860035205050e82604d6d83100022c0a006e00290767a7500220964c062c03f1ce00081d5458b05de0070007c513048780030476c191548008066121f75344038d00c4800042445cb98630b01101d00807c6000021401c400064000001a0000192d119c2db22b7fc1dd0402c400155804c54360e54000101901206400f54b5c06dc0100c0000a2dc844200105e64501dd02123683cd0732000000b3812069fdf8380332f247440e7c0b17a05a80d00010071ca2600002280300814f25610c0200035a00426900071335d27d03e5c011a44200001b36394e956304356017f554ae90f24200017400e03d00330001112402b74003e26200016f34002d5c0540a203c00c0000035188009f13006000e8011960af00f6801c000200034840989021405f8184e5801000c60001eacc70018001dad025b800000421485a6c108706e0800a035c008c0199f0280a480310114004000002e9f0c051890118390a080066500301e5204a06661f0054001fb0c917d00012db8c2000602282002c0dea80000d0054443500fa01c04000ad6b3c3018390001c055832d8135a00dd0280401c005d4c4001901c00055a00148405829a05c09902820300a000dd8379c800d003040000a52c006901a20006814a01947f6d553e80131c3a007e840484dfc0e758060c8000e00ead8006009c01800b003320026d03bc012a1fc0400 0xedcba987654310edba987654321edba98765431010edcb7430edcb9854310edcb987654320edba9876543210edcb987654320edcb9876543210edcb98765430edcba987654310edcba987654320edcba98765430edba9876543210edba9876543210 0x2ea358592674b00f010c09cdd1b911a0944682570cd51709c133a4c88b9061da28c4f09811a0901182211a15c130230433f603b563726e0cd0ee04857caf15d11608d9619a2be574ae0d011608cce99a2ba564ac0b111608e7e9b9370674cd0b10b2099f41b93706409788b0466e4dc13225e2c4458570a808df89972ba5709788b0466e411823 0x6a600d4001a7003422c64600c8cb19100322316380cc71197f882ff385fc8ca60414c0034b0667e58c84019098b1e0663c70bf5194b882970269e00d3cb192003242c64000c80e97e1c2fc4852c8ca58494b082965d52404d2401a4aea93006a458c400188003512c61e00c3c01a78034e0069200ce4c5968332d2c62a00c54b1870030e4647a208f419a0023403163e5ec7c198f8231f2c61a00c361d280334b2c61800c30d571a1a3e0c47c04d28119d00338566605ec60118c163130062658c2c018584353026a600d3401a6023370066eaccc0c5960332c2c62e00c5cbd89163120462400c48b1850030a0069614d14d194853292c61200c24f17c252401448000d2819a3033440066d08cb8c5950332a316500cca0b188803112c61000c2009a5853472c60c00c1931800b300425a498a64594c833520469400d28199f0233d0067a62c74198e97b1b2c63608c6c018d963050060a0cd5021a70134e0069a08cf0019e17b1a2c63408c68018d163040060874bed214a89295
def as25 := bankPage 0x9999999999aaaaaa 0xb8a9988b655f5a504b4544413e362e2a29281b151009080700 0x5ac3802c61c01695600b48b005845802c26401711200f08900984480442240149098f1024bdc8426ec41927561095b8684cd 25
def ac25 := actionPage 0x84f8ea117000a94dd2306ef23b029092a10c316d36013443307517b08b00291cc8308bd581600e0cbd1245e960b00705620722f4005803624b02c179a82c01b0f28110bcb01200886930605e5004002830e016272442013c115008118b9340140646040545dc000382cb014241c3900540e60040f021e002802700000003c810a000 0xc1d0781ef82610000a008e0003087417c05e14f832c7ce234ba1e00838e998c00555070a0016270001d83430003c00009c06c000046920028002210402a4c0380581ec101b25b52400830c4ec0187815cf2401434077810102081c1c8039b6c00004ac1411d75c0bc939d00045fb00ac00006c03854d6a00107a1fccd22d0500d6a00d30694b7116090d0000017e28180000002dc568260ce0000440a4e40905400300682f4d91016574060000006d0f2f002283cb07c6006800823adf81806ec0feba800193707d56002fa30078b63600000c95d4056934508d84801c0480a502f8064205bec03e600654408ecd6047cd3280c41040088000641a027400dae00681a001800044090280684809c0c05a8100b2407d32b35ec3a029324a58a00de00400b04329183794e2408401ca01439a34504a00024000003d44054014000c01b8cd30c65915e440300000ac48210007492c268902610314019767e3db0070801c90073c02081dc01800aa40ead967702e071c02288e0a808e028003800000ce810340053e05ea20b826003cd531cb3001b0500a90422be1c407ee1f1aa1c1906b4c89101c1440006ffffea002d7a9741b66000d802cb01aa03140380000012688406001107035c046e0e832501d9d380fb80005800801da5281290593c010e8282aa010a7011a0c81e0500022340cd435b000520750b000ae3e0f040b02030f32819c032503170480c674403301051900070000803a00440d0029a03f40001f907cbc480c600c003e7fa2409950180318b6000a0f814c0468091144e49e094001d05403303fd8a98002e2030393f5c0000000048737dc40cfd8801600000900e00500732a064a5009101210a0c0098d0335035e0603eb0073b60c9081c0809c40c60600189007300001c0184e029dc403c00620ad0044d5000000200305040009d51965cbda90a9a958180014090cf9c5a000c0008009c1c000008f0383d308ac 0xedcb6420edcba854210edcb76543210edcba6543210edcba543210edcba543210edcba643210edcba543210dcba54321dcba6543edc9876543210edcba7432edc98765431030 0x403804ed9dabb3702a00ed9982f84a201b5c500ed5752e85ce84c30bb3426b796eadb44623c4708d0352c0598900b56264ec72592a190c99f26827c4c88e10c16812cb195a23847025047752c7b2e60ab856419d26434c610a313c26046885 0x2b3c81d790aced875db0139f006bcd52e9225d38c260684ce30381a07003a00073e00e7801cea739c007389ce1c01c3a7361006c29cd8001b00035d568a63b04066080ebfa197f40ce658e71244ae0681804f7401cc803970072c00e4409c800377006e800dc001ae0035a006b200d6001aba44ac0684e0d02821ef013de0473400e6801ca803930472400e4801c80038f0071c08dd801bb0036e046b600d6c01ab2f4b45d968b12d15e5a09ca91295293279224f09c9e1293c08e1001c2003820170000e0005bf8037f006fc08dd401ba97b552c6aa08d5401aaa6cb3489662f2cc4a59c3caf8395e00e0cb1b980373056e400dc815b880371436e018dc019b6c23a16e74246e850dc086381007026adbcb1b78036f556dc8cdb841b70036d5e71cb0e3925c709b8e556fe8cdfd0dbf8837f0c6fe00dfd75bf2bb7e556fc90df919bf21b7e126fc20df831bf0037e0068736d061da0813410068262cbcbd978332f0465f10cba1d971632e0065c00d50b1958032b006a458c9c0193803542c64c00c9801a781349
def as26 := bankPage 0x9999999999999999 0xa98b70655a53514b4543413e362e2d2a291b 0xc8c773495cac573315e8c57a615cd0572aa5cca97a2a5ca8973225e88973261d8c5b4316 18
def ac26 := actionPage 0x847189152c007148b230b4828400409e5914543e31811a4cac88259da4c01024d642910dce800711c32007a6873004487a0d836303a00483b4c6a17969cc00f1c363409ca9060090d4318c3e4e83005062a0aa19213300462910400a0e95002510281783864c801186050440e2e7200a019a01a010d35012608500000000740a3000 0x1a06806ac7260ce000052da031c0000fc039e00045a0451eea5ae50778d7500e07199204300860e7c00670605cd0000a041600a020670700bc0f08605d2b65bba0ad105abb00005005e03000c419b009000440e070007014508b7037747d00b0d45f00370c1f45300c40802d0d00f80178d8780002c1269772b133000cc05e00603407005906e0c003004970057001e11824dc2ac123801101c1003c115b6ee00160c85991824a06b860272004600000129814d9872077c442b2202ed0c9880028f759000f0038007fdea01200121e039c00610e039090bc30006c30777037b0704090000e30753e40400a8e009704502007df2051000000207490730038f305774776520c0f20600e09cfd00007500f028b056605ff78506ed001550103024007d13001c3001c441aa529002029804ec201550b270040398b0000044c10240a2055051df4bd015117440615eb00400e3b80100de51c086b4000400001c20269403340705120f80121006a7aa60f8160447e0728000200005c000286300000382398500051738f801789abd5d5f1ff40a1038a7e018103b07a923b28d2b9a88002d2e024e064da403f11a0501538003c10da000060025446560a540200800c0c7a002c695c00c80a49be1db09e2a000d058005037d00b401adc0d02f10fd6003008afc0007c40501e236c1c4506cb8400c03004c000000c08301401978000114408060384058210000019e7070110231190037842010187000004a07c098700d0047d303b01f02304ea034805000c00804410c04a1c1c78510014401d41900000030b78051a16001002bc0410004581775c01a20fab101605cd176a960c9d6001c00b94000110d005d700000000582003e226ce00000e06280cd2440345a00249ff294b505cef0008fb0c204800050e96400105c82000040105d002a81d1e05f01a3818900964fd80378c13 0xed9430edc3d43d43ed43ed3edc3d73dc3d43ed9743dc93d943dcedcb764320edcba87543210 0x15e6adbd2634c658c3173323eae3d96ab74fe9e53b806ed6e3d5ba794ed752e7b8f65aadd3fa794ee01bb560771ed6dacab74ed8c315b8f6b6d655ba7700cbe5e9b9371e9fd3ea7900eadd3fa794ed752e85cf65aadd3fa794ee01bb56075e6add3fa794ed752e85cf7a69fd3ea7900d09de9a7f4fa9e403b934fe9f53c80684ef3de6bb76f2cbd96b26ed5c0b7662aba8cc2ea 0x3c36874c20da419af8235f026ca00d9409b2003647983c3aee809b1023ff0078000efc75db013605da02d52e5a25ca44b9469720d0141202b8c046f8080d0101202013c10078204f0001e0003be026bc00d7809ae8035d066b408d6819ac8235956948ad17075fd0cbf9066b0b12915a52244a44694836ff465fe833fd047fa36fe865fd033fa047f40cd5c11abaecff489468d28c0225033fc047f804ef401de813bc0077804ed401da803b30276400ec809d5803ab026b800d7009ad8035b639f4013e58e74244a2047fc0cfec01de013bb0077204edc01db003aa0075200d6809ac00357026acbd3f9767f2c4965792cad259564b24c964892c8f2591a4b0fc941e9283b250724a09c941292823250424a004480275e00ebc0dd7013ae0175c00eb831d6003ac0075004d5401aabcc121d7963aee809d1bdcd66a978d52ed69e4013c30074600e8801d08038b0071400d9001b180362
def as27 := bankPage 0x9999999999999999 0xb8b7b6a9a89d99988b7271655f5a59454341362e2b2a291b 0x10872310cd23188d23508d23808d23900d2310a52313852315852330892380912390112310859d10856d108c6d10852d 24
def ac27 := actionPage 0x82e109e4ae01194631687ae45704449c98b039692481204b4c561ab09200902428260c954780140fbc1085e943b02a06b206a2d421400442d8c33139d1a0011152818880c8f000809a40a8384e4b008c3ca0401c1e04803817ac160e0c01801b09460a04c4d2a08703fc048161887005415d81e050732801c085000000015c123000 0x1b30015500001f698003603a6a9400400441d30012060145946a003612596d0500783580700616d40000f472301e598000001a34cb12a40403c006f640445a0186b000202ca000011bf003033a5001a53400900075b130009100733f92bf0000280fa08aa0db7a7b100e8060da4ea6cb6700800e700504809353abc4b604c60460cb07000a004b4d3304501f18010988205a5c79828f9300756cd034c00189e3604a2fb56adb45e4bc80001607ece77035b00380c806e0300011d6430009731310000d780187001f078012015b065e00000004c1b231c83c40d002800007402c023280020000002eb4f5e0ac400d24c0db6a502e2040f51000c0880ce021d300816f016d0056a5a162b880a25d00e000502f00f826552811064050012ba440e8d8150d307760b9aa0980da3541b1800003f60a8068964753140e36880540eb9800000147722ab00c0f102e2ee460a049306c040ec7508003005410000060002666110d02ba0006e402a060104f030080004002bc1e100b20442325f3004c04280a7686860002700001a12a51c00021e0689047000d030662ac6d00078c000001f880000a8582cab1ece068882024070014702ba4b5c0072845001b2189355b40008040328c21004700252000f30000651004a0c00e80400756610b6d002c194922705884514c0001602a7e000cc50000e7a6c01800019880002e1401ad3844559402280a00000403920283400200d0380000c47e02870000e300a826e1f73f200b000b00e07fe5400f50bae096abf007006bb80c0f0045e0008107c97ed5050f4a0bfa0dd73002e00653b30035700b0245003888000ac60460024e2020034000a580800ac040300659c00180070240c58c09399a08148c0904000f0400be09677fd0100e17778280a90e0147008241f0641e001b51380b02700cfcd4526e0b381f296e002a27be486ac600400da0029e0240a883d8c01a00040ac80000778c0397f4b240e881a85e6c2841353620 0xedc6510edb6210edba65210edba6210edcba6543210edcba643210edcb6310edcba510edcba510edcba643210dcba54321dcba10ed430edc4320ed420edc9320 0x165ecb593006006aed5cab74ee9255ba7949a9255ba7949a9256dab7492b6d5ba4949a925d0418784668150295e93c1e23c27806682eaf35b6add24b9165aadd3ea79492023b627f56ea153ea79492023b627f50a9f53ca484fc9e56fa855069f404 0x1624eabc9d5693aab275264ea449d4793a8d2744e4e8949d1193a212740de9013d2017a400f4809ba80375006e60cdbc01e880372007a00adca2257c4465007a2d2e8875d124b91137228add039ba003718383600f4001e522bc90e792d2e8c75d1a4394127280adc5fe7ebfcee6d9b00cfdc01e6813cc0279200f2001d5813a9026e800dc009b705bd1087a006dbc01b7c84252a84a8af3039e6003ca697143ae290dec863d9007b2b0e4155c824b904672026e4041c80036d5d89686f6031ec003d85771eaae3d21c7a338f1271e20e3c09b58036b026d400da801e2803b1006d2bb4015e52aaca54894a8d29409e2003c40e76018ec009d8003b0026ce00d9c09b300366
def as28 := bankPage 0x9999999999999999 0xa9988b71655f5a5954524f4c45444341403f3e362f291b 0xa6081f4410ee8822dd1841ba60837c4106ea020dd9048ba22a1744942f88285d4050ba20c1744302e89205d1440b 23
def ac28 := actionPage 0x63f141fc3400a988b1f092f077004cbd20f442703c002859d0781d34a1c0142a88378c9811200e139d18c4caec9007c8b689a234c1d805439cc4810220e00141b062306cf8ac0080cc31102a706600445fa07e102e2d002e2a503407118ac02710881502c706e011863407810223b008c21202004092400460850000000124023000 0x3180c2c0d0c800d6840000555010010404620c800a0005000ead7500a46b04050057c0f9030001f79005f650040b7e9d70168759009803c0ca18e00a07080d4a4000240d000000380e018c06001759429015e9724a00010749408318e871de1020c007fdc06a0e402927000003b00801d2f1008b700a4530a12940e420400102700407001000340b0e80940000123c08044000002a4a9200b400d2171283c0c81ca00a2061f8ea40c52c25d35c34e800928100035a9a8008d9945ec9001901e2d004018744f0080009532530253800023cf04014718059803b49300300f6fd1817811de15e00a51474036900715700001300d70000ac5ef0b0403806000130077805c00000e070130370405d765804020300759100a01500085a07829329d00001d7c14800035c768004000640a00060979d01600d0007cb71500b0140072812690394410074175806d2fc145250d8f97003d60000145d851000d0f900f8c0b40e0000307e230960239e000675310d4008ca4c014030b91500eacbcf20e50f06b00019540c17a00560010705037a0a4c49b6090262158084044689a00aac0080b0600000a1903bf30850900b207181b164a3001082802e6404300980004fe0e0039410016006b4a80353711a0b81f260c80007e248ddbbe400000510026f0004c000003f905c024018d08337e03c009d60938372fe20002d5c82931a00c07c20827e02640f8a000013ef001e67c4002a13ec1c00383f55f8172843eda1e0bede00615901ee08f80300281ff0004000419ac000bbf524e00040000880137aa7803c2225db2aacf4009d0a6c1880120d0000ab30401066e8f20001b00300618809ab800f428a00f7830380186001f00000f9b23c02f79c4c8affda1000000019b13e002c0eb03d6dee1c05c3efa767f81a7303e0580e06cea0a4c20014eb6f884730174f800b3002000050a9a8070024b000132f8807000f07dc653c160008004014300608d40d1a8d91991b025e0477649832e61420018004955fa8ae001d82530695c40036400068200006001c4515b001400000f31a9b07298d048deb9a0012008000bb2a0f1c03c83e898eb00381db4a80a017c602e000c60289809f800034695f0422001833000ba860001c27a0e7 0xedcb864210dc76510dcb65210edc6510edcb65210edcba6510edcba543210edcb6310eb7310e73210edcba75310edcba743210edc7430edc98654310edc73210edc865310 0x524bd965ab856fadb43a735e7b2749a924998e31baf3de6bb7666cc597b2d64ed7d96ae15b6b655ca4d492f35d2b9f64e8646e8d909cf102e006006f3de68dd4ee93524b636c2d7d240016be9e53ba48004005afaf2b90008005c80069352400349a92001bd34fe9e001bd34fe9e001 0x31e734b8d0070c74df019c2823850070a06e0009c2003840088e18f350dd5863ab1d71600e0c19c0b4b631d6c6212991a49884932384241085ba03364062380c4101801f101b8100702bb3915e5a89cab12954932804e502449f1293e00f6401ec003d22c75c00eb8b1d6803ad5572a00e1401c081b7f106ec8cd6c41adbcca8798c23b04065fe83374006fa3edc849b9883736894f3108e3e1187b7c006f8bb38dee58b54b00482000f5c01eb08398006fa00df1a1bd0fb71068340906809ea803d50279c00f3809bd8037b026f400de81a0c82419027a800f5009e3803c70278c00f1809bc80379026f000de1ee543cca86a950d12a06e080cc1006820090406dfc8cbf9067f208fe419b802370717f0defe019fc023f8027a600f4c09e6803cd507549cea809d5003aa026ee00ddc09bb00376
def as29 := bankPage 0x9999999999999999 0xa9988b7f71655f5d5a545352504e4b45433b362f2e2c2a291b 0xa08127d200c5e900c2f414417a08523d04491e82448f418247a28123d44091ec2048fc10247a40123d0c0c4ea206274102e3 25
def ac29 := actionPage 0x82995de4b408891d413c9ee487044c85a090446d5a812c3d8c461db524c0131cf8200cd7d1600c8d040d456ac89026c5b5866264f2b80222a6c3110a3164092138815870ecb600c884b0a430664802483ba04011283d8136177018040ea6c09b088803018485601481db0100a1816022c0a98040306130018030c0000000d8190000 0x1c064212619c07000000bc1623440181ad001e2018065014d3ada15000f000a00f020010180e4ec40081200296008d2500800c0407500ab7240209744a0c003e4292800a01184c0156cc06f0c08f83dd0440006da07008719419ef0009c405048519100200172000105810e8aa600b101c0063d240a507b21576d0b19010b00604a0e0628210c001d01d00100063ff24e8341a40037406002e207dc03d40a03f5a850092800af8120f728105425fa4d40281c8781d4a83d0001407d840050015e007cfc580002c5281b214977500db480009301fc42800444088012e8000059f806a8e597208bcd845c101a84b0288030930b2d00a505483e02030081000f090200539d30a203a00001008001fc0054dcb66f7c0b0300180cd4947bb0e8dc4300b990007303a020ca1002c40000803e242bdac4b8c2781884b40b000150680d6b440025af2b93e0240c5940a183625804fb0070c070bbe7c002000b7c006f02206600cde530b3a269e0110660080320003eb7000f9f800cb4c0b8c0044680c0000482a0b040f49352702c0ec41598c05ddcf071dd6b02a0343f1880e27b40a00d1c000e09c5834f000000680021fed40080e2c07c1b7333008b3805780107012cc840c30360304a6000269b6240022f870c07800b80000000007c01595d8d838013f9d02114b000905f2ae5f3c12660a2c80780bc300a0ae12f78000e7f248780f08000202062e9f802817656233cdc00013d06f20f800045be37e0c1eb7e804670000d0073020631157407501140001042e6410095500c0068003006010766e0c00805e9b965303003ad0403f2600280e8001003edb930100d1 0xedc8765310edcb741edcb1dc3edcb7654310edcb65410edc3210edc865310edcb6543210edcb6310edcb6543210edcba654310edcba543210db7643edcb63c84210 0xa855069f21742b00dc2377632c61762ea33361a52404806e1141a823b8664948fbb93722cb56da7f4fa9e40476d73e9f4035d6ba06c06300379ee7c04806ed10a8ed0c74fe9f53c42a84e9fd3ea7885509d5ba7d4f292404a7d4f293215ab750a9f53ca4d492025cfa7d01201a15426784170018088569253ba4949005809 0x13a40074804e89cdc639b89106d200f8001e08139e73710a2e21e1b4083680273800e71a254023fd047300ce45a1c602369869e00d03411fe37bf8007be00f7801ed803b500736d0e2011b4033970472e04e6801cd32c190079600ee831d8003980672800e5c09c9804490079a00f2001de003b6007649cea801cb013926c9b0d908811fd803cc0878a00eec01ca013915d9ca912b41a0582409027be00f7401ee003d30079200ef401dc003b70474800e6c01ca0138f466f008d9801ed0038d1d79604e28e9be9c37d
def as30 := bankPage 0x9999999999999999 0xb8a99a8b736a655f5d5a514b4645434137362e2a2928211b15141110 0x52233015a0330172033015222301804127680c12565201266528124656012465044472518145250c44525141498504449850462b05058a50 28
def ac30 := actionPage 0x61810945460080abc0ac729c9300444dd84c334a32002023f01816229d40230dd60b8a8fc4c004068b0584e7435002031582a24351a821017281410990cc0880b0409878b868184852b044365036042c2510201923128112112c0e0b8e09c00b07860604058ec006033401018124d00840a180407042a801602ec0000001d008f000 0x40053d6200b06807001a36930de2055060b4090600d2d3ba08845a1a52812711de7380e43b8000286b4344043c00080000020200140001c3060883000c00f2960fb1b70b030c963ade0d35ef0157040004001b8001e0416c9181331a2f018340180000000500c32108091830007cc00731ad6881000169ed20666490622003340d0007073f00a4001bc00de981512003b83a0024a240d260d066840c0a7057007030732040012265380313607003726405003201050b681a508c0d34190025001a04571837516011c6010de2a3050a00b09c00053300770bb023a600060c24203000054c4a2e00000f0006a39140cf8110dd900476659a420cbc0090e0a722020905b00d09317022f800086e85f0000f50ee0000e0f830301600021a01bde8005c00f30077df18cc00580030180b403fa1a00f0315a3800e00d60b40ed5c41996993036500186200d0009f80c5359070010d9620ac1015e00c39430000410588d500e59a000871501880088d6e060d 0xd43d43ed43ed943edb721edb63ed732ed3ed72eb7210eb642eb76432edc621edc9876543210db721edc4 0x99f2ea4346289f13a2644b5d2a0a53c6289f13a2644b806be974c8689f132259dc3b73a627c4e89900d412807404c9cf13225ee789912f73a4bc96b9d25e4b6ce83205f67017d9c05f4a693524a2f0ec01801a534a293003a4b491c3a5312d6f6cf59cb2d554da95a 0x203803650080c01010020006bf6006c6f7371fa6dbdc8f2b77600d89ee6e354dc7b9b6d536d0e5c07c31028621b00c0201804020080200ffc35fb003f6007ea00fd001fa803f4007e600fc801f7803f1007e000fb401f4803e6027d000fa009f2003e4027c600f8c09e7803cf107cc00f8409d3803a7
def as31 := bankPage 0x9999999999999999 0xb8b6a9988b7d69655a4f4e454443413e362f2e2d2b2a2910 0x2990c32991832946838986832d0683390683690683298a83290a8338a48329248329062d2b022d29828d29028d28a435 24
def ac31 := actionPage 0x62b935d07200c131413c8cd47a007c89d89a43621c002241b04720aa8b401a1dc6228f934700088e140fc78842b00606560723a381500302d0c351c180a019314b8158d4a070011884b0a464403800343d60402f151d804616701c108839411109380b85c3148088839c048140ed5005013600204023281460168000000108109000 0xf081a2070e06d2f06300200d0d01d09620911005d6705b00e05b00adb042c09b01c04fe001d5e40f2b1d01800001c08d5c2d0001918017aece053004c301dd280570001e00831beb673838029007bc1d05de11c402001b4183a028003830070b00304435a03040800d3cb9b580000f890160eb10270e99c690002a0281fb6220030bb800a0018f0301d00c608001c003ea002624e44c98000dc37a25000301513f904ca02001c02909a903000b644f0063e0b00439330e8510c00952e615a00f4b0079b0003800280de818103c1c5e1916e8075a8003757c525e001ba4300c082c09f800b3940a06368829f47014003d90e000040058b18004a5405e43ab980693d5c58c443000c18000000005002000c01100e09201800847470a193f430a6aa0300ae008024030a0fb6310e885000a0021c0000080d40b0a01c30690389000112381ca99815747d790b9058003001a2f640060075019a2247900aa00591ea0307a0080b0c0958ea09336000de5061c10a000008009e40f600001bb220036305a37017007600000520051902fd00d03661000142001b69880a05daacf4752b0fcb000db8004064000626768325db807010881554030069b800000261c3cf2ba8000016a0151c49407680009c427b8adaf001c2c1d31c001800b682c2004a099dc9710832a000483402806b280205bc0d9d96179cde1140000e2d0000056a93a4a61c8d9381a0002db02800615000368023c99011e1e038a08a00768008538060038d000ac201c818c6f2826a5d014411807540023c05003a6002a80007800b6fbf900000581e90e80046a0019a018284d700a884b1a037ab67338aa2029300a800d01dee03780808c607e9c00abd9f400c249904cf3b0c000ac000028770858034027010a5e 0xedcb64320edcb654320ecb73210edcba76543210ecb73210edcba753210edcba76320edc76430edc76430dcba5310edcba743210ed940ed90d9320d9320ed 0x1602804d98a1939a72ce48ec18e2643a8711321c44c8750e2264388990e21d4388750e61c4628990e23144c87162243462833011e5284506a09409a33324f0974868c501201bca660664b91712dd21a313b876eed9da284506a04d193c0c60ba023d46bea1141a818ff13a260fb 0x74f5c01c323b7b0c6f60cf6401c188b770c6ee8ed710dae08b5c0c6b824f4001bebf4b07d960fd199f6332f44e0d7ac24f4435becccbd9397b271d5a20c1037c006f8db29c0a0bca3da907b444df035be0141d0082608f3801bd834370286601074020e0041b0083201060020900411006f5310a4020bcd4d78d9af312f64e5e804160082a20f2c11e5893ca0081e010050dd38036b0081c010150dd28036c0c6d00503001fe803f9006d200d9d5e7e2bceb4899a0103402060040b008140102401ff003fc007f600fe001fb813c5006d400da001b300408
def as32 := bankPage 0x9999999999999999 0xb8a99b8b8280746a6966655d5a4e4544434241362e2c2a292810 0x50c128d40c3235120c8d4080dd9020ab70082ad8020ab56080ad50248b550822d502a13540c2a55120a954882a57020a954284a5 26
def ac32 := actionPage 0x41e9059c840050d820f07cc634002c68d8763a5f2200183230391a2a1ac1111718198c5287400a8a4b0b45c863700584a20422d370e00481c8c1d141995008e0cf60d890ac9000685dc0583c4a660240276020161b4500380d0c0e090b11408c056605838408c007020b01c12165500400a580604062a801c028c00000011800d000 0x81c404928b0723134706e03636dc0e28f400830006c00400052007204006554020001602036760318022806006937a80a054082809d3b41a202030006c0280f4afa5014a2080084d760066c05323e981d007b505528000802b800051c14886e041ac07d800039b53400091d6080ae3dda5607ce0d004dd000b5806000bc67b65084044009f142071b5c0c640701bf000e08300004800740f790a7080acb541401d7f22c00308edb810006e4505e05280a05a54df00000800001c00282bb27efa4e9c7434005011e901dc000000015fc42a0e5c0a0255af000870746b20859b001007dfeb0eaa09f00350379000399b081002201007030e0e0309af933890b76024462818e300b055000601207c40dfb8207afa94e40053c1718000c98090b80000640e3807200000046234b39301931486e340380e04005c5c00512604014789a1802750841a15c2c053a703520c7200b001a460000000f6af983d0f07970406520f00ea76205050000150000088000358295be47b10c0820000d88070f00832f0660bc07eae560000e608500008a3e7016000a76d0142ee0356ae54200202400dc80b9000180045a10c03110150200067602b00261f09642060e 0xebed43ed72edcb8753210edca754321edca740edcba8743210edc7edcb7430edcb43edcb654320edb43edb732edb72eda53dcb763 0x4a88982ac07ca807c0f254ca807c0f22844e8750e57728189d13141c4e898a0e274ba89d1321cbca8c513a264048c51422744c87301201bb776ced1d9a8142a18e1d43812c2561cc3812c2562744c8964b89644f89912ccc9988990e61c08a 0x10a801d300429008500109c01d23f4d67e9120100cade615bbb0074605095d6113ac200d80624f1401d1014260084c05090021201421008420103c0203814060080c0100801d0804260080800ffd69e40042510762010f8021200400737ec1afd80208003fa067ba00e610dbc803670084600e3402110041f0071801085cdfb003f600716fd2383e1895bcc0071401080020f00389
def as33 := bankPage 0x9999999999999999 0xb8a98b727170655f5a5553514e4b4543413e362e2d2b2a29211b10 0x6082267010334d884449b05089360c1126c14824d828289b8405136500a26c12444d828889b2411136880a46c144c0da24281b04488d 27
def ac33 := actionPage 0x6169f0dcec0078c6c0a0ea647500405bd8486e2e3a00262a4c223195acc01013a610178a0a60460943078aa4894044843603849206200201dec19220e15000d0db60b0f460e800706330506a268502542998242b0f52022411700d110624c01406560487024c60070284014140f220258099802040531001c022c00000011400b000 0x790d27dd00d9090991c030a0a001043d0080c22a1a0469d205b4a0001666b4003ac0f000807a00a51c080bca649940d006d401a00000406bf00603fb005620b203b0032a900e01a000a870045b5acd5f06ca20700fa10400f90050442f050619b004606003cb00369d007f79093404071e0202050c456050d07d30f201670090459e06e200c900cc3007099e0090f20fef0d0899040763ca8f000c05c0700183001e0083c0001649b12c0057d602281c1e765585070520bf002105057104220e505000d8502720da0d04a016000b00c0e1040465008298d0ca0009b7200b09d08b0080fe005cf4990019983040f0004707d7a0f008e036f61bfff583007d0d7500b006ac071300da0053040b04ac00a0c707f3e5084100050600075832400c00795e0500002a880409076a20811ded5c8000028658cc40010463cc00001a078c6f0e00160000fa01087d0e0f8080008b1785f603a2b800507c19700060501706ec0001002a5000c66f08414e817b91567b2c114022e781c003707d68139088870000040310b1b8003ab30505450309b0080000800b1608b0870000994099a807a30572 0xdc9320ed940d943e73e73edc3ed73ed63ed93ed973dc93d93e62dce3db721 0x1576a153fa7d49a02bb790318e2a45089c3f47e4d097721e31c4e899012e4d97b2d4fe9ed3c90f18e023b660957632c638c5132e4d97abb4fe9f53da79011db597b2d50e9fd3da7921e31c04784ed98255dab71f631c62af54fe9f53da7945d7dd5da7f4fa9ed3c808f09db597abb50e9fd3ea7b4f2023c276d5eaaed43a7f4fa9ed3c808ece9ed26a492301882ebcf79acd598b2f65aca593ac557aac556a7b4560fb4553a7229ed3b94f13e2644b8770e61c097 0x5024020480431688540102041e2803c37383ee70783e01883b102802010040218883b10678408f0809ff003fe007fa04fec31d832c1f0677600ee819dc823b90677008ee001fd21bc6007740cedc31d8003f9027ee00ec401d80042f437660ceb411d6bec71197fa3afe419d48042c
def as34 := bankPage 0x9999999999999999 0xb8a98b7e7b7165625f5a4e454443413e362f2b2a291b10 0x6210cec4231e881a3e10347620a8ec2851dc10a3b24147a0648f80c91d81a23b4244764508f44211f08423b1015b 23
def ac34 := actionPage 0x6270d1c06e04b91dc10c5cd068007880a07a2b5c1e003639f03714298e409a19e6198992c500498c0b0c0448a4602305bd85a1e412201182bac2a0d1e11400e14881305cc8740098923088285637004c41d84012241381181eac1e080e89c00c0e380c834507204a05ec04018161900a81ba00c0c0403804c04d0000000310014000 0x61064a0e20ff1d020bd00000dfa00a11250e90183ac0008500f030367d1808dce800a0001fa0ab580000d8c6580321a8323000af0800699e32000068e934301600c8300086d88000540001de4540022028cf007e3824c17400487a00b0780d0e8146801b380016e4200d44f79a44d2780022d13d44a4800000d06100ae02caca03f30000903808c294600180195821c63a800054e151b650032d41d0a0180054cc0000406e8e0055a800d170200001415699ec00e4003511068cd53803388060d031a40e0c8002014a90048eb9002b08d3680098a82003b008d106f0e000007872038000fba30eed07007890f07f0b030555504500006f60620605400c40065c0b06330a0f00020a00c700c2407060050a16147a70e002a8a20406043807018490002b001ea6800b2080e210f74016723000001a1080c71f140000cb380a64c00049000010a5c106e0e08b66d505b0a0106a0fe50650c54900d0d8f000c2d24044830006c0d709405300606000af0f80808e8098c006079a8af020eb81f0010070dcf584090700a23c73008070026b380003016008120003057a401214061ac2a0e02b4662100600380000ad398a900000000eaa86010000307400c00210250001aa60108550061a8764903401a880a560278417000e1000030038eb00150008501420ec5b4087800b8d190140310b2000003421401cd1000002d60020000012079c001056b3196070429094e0328440106b4a7001288e684005b4000050f280960086f3000b120a001d6048000008083140c0086000167060200028002ba400680438338000d90123d010f7380c400000734f4100c78c96b400fc2ada8 0xedcb210edcb5210edcba7543210edcba7310edc764309875103210edb62dcba543210dcba310edc7430edc6430edcb63210dcba54321dcba210d920 0x340600bbcf61a8750d92e19a2743987113a1cc388730e2935248730e2935248730e29ed26a4945e31c4e87318e274398730e21cc38a7b49a9250eb0d21e31c05808a10d294327e1981a031 0x1562a9d3d6107aa18f552265094ca558a4010e019ec083d30c7a68cef50dde883bd0c77afd2c5fa33b441d0082c00f5c81be2ec516a838d10700a0a80415007ac05070020a003d50479e010dc020d003cf0283008f3801e7033cc0079600ec66611804170082d2af6a726bce48a8d866010540219804140082605045960c80410007960cf2401d82ac4d467ba86f7441ee863dd4973226e642db883b715d898af131562600438487b88cf710dee093dc107b818f716652acc5e008640502d19e3803c4
def as35 := bankPage 0x9999999999999999 0xb8b6b4a98b7b6a6966655d5c5a4e45434241362e2a2928211b151110 0x184063318606231a40623184064d1980525194054518486451840645800993980095598029929800d1c918422c9802954968111491c21149 28
def ac35 := actionPage 0x617109b4b00460b9b0b07ccc4704305858523a6023001c2990261b2a92c01112c6120bd48e604508eb084509a75023442603a24402681241cf01510998f40220a760a070b4ac0c504c30442c4e66023421182014211302140eac0c080c92000f05e80202440f200d016b0040a1446023406580202041b00120168000000090009000 0x90f0d62e080c0f0003000347bc27f16954ca0110606f0b4080c06107000085660acb4815206030076a7b0700f0643001092d5d9006d070b04000f6000d5a920601011140b02a6003dc0180002a585639cb62d0c03502d01600a9e0070f78b7640e008ff23c06180092000b0b03db009410550440220b6b0087100a500f700147400f7bc60079cf49b001801c57d46000002140500a60128407a2a4400ed11a81007e80180810f40016001a00588058323d59b33053677baa61df1a7920243bae00070280f40152b2c0089c0f1019b181de0341904040003d0510055d00f0021920000e3d2930c0da063b060b007707a08570000061500a03b0200e009707384e17100063f760020001037190805140400000e9024e00071609e0dfa0a00590c201f3e4e9018b800e04d60004c00301da102b8b1353994101c805fa0392d5d0680068108aad877b18048011c3e135000031c0d600ef0000508295e030a04007000780c703fb96b05a01078be0800400120010060500040272a6300ff11d820d30f400c0027 0xedb73210edb6432edb742edc98765210e61dc621edc9876543210edc9876543210edb721edb721edb643edcb7410edcb54210edb643dcba30db73 0x14144e8330600be8209c0600b68209c0600b61ec3b87200e7f4a99511385601001d3fe274398707cc4608a8790e61c0018790ee1cda0b3f2ba55ca9a534a292c3e8770e6cf4a98c7142272c7b0d25e02c0450885c33526a490f21cc8789d0e693439 0x88c00fbc0222803ed0088800fb801f6014403d7de00fa002219abe70088400f9c31f2814410083400f9801f21f4460088201100021f81437027d200f9401f19fc2c0085820fa401f08042900862d10a0021280408558ae010f01a19033dc467a886f5011e2003c4008720108c01ed00439
def as36 := bankPage 0x9999999999999999 0xb8a98b69655d5c5a4b4645434241362e2928211b11100f09 0x6822916a294178294178614169c14168c14169318168318169a18168a18169268169228168228161069681067c85065c 24
def ac36 := actionPage 0x832906183a012126b1907d003602288f98c43a7923801a45505d1838aa000f20d82c889b9c60088f6c12438d26500846bd88c195f1d002032f03d0c2887802215781c8511c94049899c0b026721e008c3c6050112d16002c18f01d081007402607f8068404c1a00d0274018121c7500500a180604072b801a028c00000011c00d000 0x7325b84e0321b914f47d83da699a250068005c7337e05880d6a98029001d484a2001596c17582e7000090221e003807d40660007b001c0583201d801a4e00300203c05f1040849300040244a6010010c607000c0c49000c0e009500a07e8a9e400bf03d0008800b01720a8017022d3a900046c0703160d75ae982c0604c03d9a0d0d200009ac85e00ce788180503c0a5800eb4a07802111400eabb298231d000363a0c000d00327000b5000a004c2658155d8582038009004065bc596d206cec56910d4001b9bc0eda186f1011005a64000048208046fa78c80605a0c376c010a9c80b3c060c7a8ece00017002072a05692500003564a0b0b2180a0e410080003cd265c001004c03e007d014068131b04b7ac018849f7780e082ba0501102c14f3fe67d2ce300fb0877a3a1c918000b8ac0000009800edaf2a004002f400e92852060160800dd1f00462500010203f5e05312a98c000032b03eecb81001502c0e003f75a4450a010079a072c007000000018d696016c00200ef5290c0338c7c942182c170140c82e03cc000ab6c0584e568133280023c007e4003cc52b49e3008650e0113c0748016f801049ac084a44580a068cad010c1a8da0000003f8001800800cec4841902400000000c090a40a2fce0000049496a801cd4be806ac007f160536808b80f600ae1300d627ac68146b800c50080c3400071fe0388002943027a603000001cb0010c500a1cb8860001e00f1f00a5c408882a9a980005ca0424090490007f2f8a70d0000066000f0008741d6b2577263200092350053d03e05b4040881a0c80c80001061c005826b01e67618000590d400602217a4a1d8002c06b0faa2245067200e7bc0013280608a15100c0df000d0005740b00803900e0a0e050e00a0360c0030864b861800e52b 0xedcba76543210edcb43edcb943edcb9843e74ec743edcb764320edcba876543210edcb764320edcba876543210edcb76543210edcba76543210edcba76543210ed632edb7210edb6432 0x4b8df1bc2a86f8de1722aa01be76d2c80da9832223c85c86e76cded9015c2b6568ab9111981b02b0550a60ecda95c1fe1582a8537002584a89676ce004b09512c2584a896a854a693519a3145e80d9fa0c0d419832b3d4141982f 0x48fa111f0023c00477008ae011440a26034400683808f8c01ea00475008e8011c4023980472008d8591a8123517c71048e2051bc11d318c9106922632401a4800470008de011b802369646b008d6591a80235034430685400e9c01d2814677982600e34c64680467008cc0119402308045f027c204f6801c601464048c20117011c498c8c06916051e8023200463008c401180022e8045b008b40d1081a1000388068ac0115011bd8037b028f009164022b004530089e011380a26834410683a08de801bc834920690e111e40a3c82458008b0011481228004500089a0113002258343f0683608de001bc02c470088e0b0d0021a02c2b008560cf8802230e3f5007e40111401f8803f0
def as37 := bankPage 0x9999999999999999 0xa9a7988b7f7d7b655f5a5753504e4c4b46454443362e29281b09 0x906089e44015b910146e51011b904906e41441b984106e4101ab90424ae41112b90484ae43012b92404ae61012bb0404af41012b 26
def ac37 := actionPage 0x81b929f9860078edb0d08eee37004070d860437023812634cc2e20b589400b1956158e99ce80070c040a45ac8d3004058984c246149851c29ac240fad95800f13661106948b200808f40782a8e5b00543da034103c2d802c19901607180b00950a480882c907804a03f402c10303c005815200c030c2e002c05500000000f0016000 0x5a44d3b4042322a501664002d501800000802c4e002c0039266012ec0771810900260aac9220107f00acf3890a0b0800410af50038d90000030415940a7ae5005b008832030007750a6050210d000050c00000863050026153200065960606535070c0090010e00942101071c4b47c52e60ab41e075a000c0f1000b22c000016118009629e100120488604206f30001575c822c08a04400003080a7a24256060b058083eae0b10f009000a300899850000081a0000901f09c082202aa220a322292053a000b08d000507c0d8a0c6260cc10a50d08e5ab1ded019e02afe06b9ad1810a0003f02000000f05c1405016000000701821340c1a8027fc42501890186b03ab200090380b00014581240b4ce013a0500fb7b40571140001880644188180000a78821c0765429daa0024370427f806002a2602c00001ad30405cb40060d600998620000230056800438e881100f6e48f00001704d8ef94000256075c0c8801fe062f2814b00c054cdde62e60601ed1887340c05019a00000000170016363d26501e0780825a740e100b003420d6c4f300002941000356b8cc029400685230b6202ef034ed06960381b502800789826806008003000e4880606ad225d86f00c1dbc505e0100180e62c413020608c6703400481800000009982291000000f109a1d8000bb8404052f580361800d029220750fc4139 0xe74edcb741edcb741db643d730d73d73c74310c98654310edcb7654310edcb7654310edcb76543210edcb76543210edcb76543210edcba7654310edba76543210 0x2e4d9eb3b670d695129e450690cf13a271c109712d011c109712d49195dd0b7cea5c10c112e25adf597a814fe9f53da79011db3ad704cb595dbea7f4a693525a48e144b896a4d4969209712d49a92d2412e25ae852612e25800dd08086c04b896a4d49294d26a494a693524ba14984b8960034a693524 0x1468008d00519919f6883e6028c60117919f6083e5028bef304c023d0045e047ce05174022e8045c028b4090780a2c80459028b001160122a8344e0483408f98023c80457047ca00f1c022a834510482800f3c027b004540689e0904c01e7004f6008a605140120c824120078c011440a27044370a86610fa402790144f0089e090601a0882411
def as38 := bankPage 0x9999999999999999 0xb8a98b6e69655f5c5a534b46454241362e292826201b151109 0x8302a5c14192d9024970105736408a9bc0150d980c86e80643648921b20490d82251ac112a9818ca4b218525838292c16249 25
def ac38 := actionPage 0x413139c4680030b2309096d0390030549842476024012027482122ae0900861336101094c72045092207c78a461042046d83c394a1c0014218c1c1aa092408d0f860c8c8dc74008070404062501f008828201c2c1e2d011c10b00b1408934093061604894286e006027c010300ed308440be004090479811e024c00000025000c000 0x2d00f501840a7daf003000ee0ff00803c2609a0330e098b7a4018c0f0100d300097b10140470e0304007e081801ec38bb080017829e02900a702801004b90b1009705100acc10084e2c2b8e36e186404267980005d0ac11b085c0d70eb00100970c30cd00b0030050c60ac0c7b8980c00d40c9e07e67908004b630607c007020e197f4ed000b515605e041dd8803a69003070027440935c80022004022506c00a39215a00af800f2500c282e0010a30240000a73dce4061b8c62a7e901403025400e00000b3818096a048038004502010a0010133bc6a0000a484060304b381206ae2c114100d6a407504005d4024b2a00580f6001d07bcc06d40f8160b781b004cd0d8fba04840d400082f10d000035bb504060205dd58405a54351c0a0256002746c4c1228131441fb8381364040501cd0005000017d00841041e000001bd044864d77208c1c082a97801c6380c072e0001e0028a0032c4700407201b212d50f0c00010a09bb9000660 0xedcbedcb76420edcb8710edcbedcb98210dedcb7420edcb97420edcb876320edcba9876543210c987654310edcb987654310edcb643e74c93e740 0x1732e04f4e314127a4504f09d0c85cca019a2e65c0b816e27c4f49d8b93884f89d9c427c4ec2191113a1884ed29a514984c097ba14a44c097b383806fd86808df5911b636a4506786d0ac1541f83eb2f65aa053fa7d4f69e40476cea1beb2464445067dc9b3d676ce53f36c56c8a0cf 0x241003f1028fe18fbc01f78048400906012080240803ee0290018fb401f680480008fe011f839f9013f20e7e004fc031f6003ec028fa011f4023e004763f7de011d5e61c8047b028dc8cfb841f71c3e7028d6011ac0a3480469
def as39 := bankPage 0x9999999999999999 0xc5b8a9a2a08b82807b655a4e45444341362e2928201b14111009 0x604360d010d83264160cd10583245260c930983254260cb109832445a0c91a283604157691054d444153581054d404153500a175 26
def ac39 := actionPage 0x6158ddc86e0498bf40906cc81e028c4f1844335e1b0018254c2017ab91c08a11b60f8b138720058853074509046002c3e5834244223001a1cac17101d12000d0d160a878cc4e00805cc04438502b005823d0221528380208114c10079298c10508280682870b2107832b0240c2848043c13a00403081e0140024c0000000e000c000 0xd60e00e9299010706b000080aa0d6917d9c7000236bb900050bc0900b00d000a6b4a0710ee90480022608fda00037a00080002b20d6fe13066003e0b8001280200398b680080280f1bdcd0200904de604aa7710deca520263e400240855405500750ab0a05801fd609204d3002601000601151000430de8a0b0e50009d7f0dd0fe00000f890e6b39020a507206881d0030a770020f1b8b0b0300000598400a0c354020a10eb0b1d000010000820887a9538c80368cb0c2402bbeaaf000783480000900410c7ad4012605404bf400b048000cb89002a0005fc208a6c40003508a8080005034040004d2940b000870152b08646281077340c01c4c2996000ce0001e07b4077a4c84002601c2500200d8a7b0e0500070643c708001901050a5402b5c622000001e203c0051da1604004081b02582014a00ce84d040a00d61b005a3fdd0a200f0e175af09093896085f3f0709db035ea0003b0c65a0be002400c8160a0000ba7cfb1c0f00110c000c6a28f723a8d031e709b8644800393a0006006d204d01a6dfbb901fd02100165044d00018ac1c80007206cbd85f0 0xedca740edcba876543210edc743dca7543edcb74310edcb43edcb43edca5432cb74320edcb7654320432edca98751edca9870edca98765210edcb9810 0x21d4387930ea1c3c969f0e20d4187930ea1c41887b0ea1c41a87b0ea1c41a87b0ea1c34f8750e04b896b10744e499d2e659c991ce38c668b816525e6dcb816525e15cb816525e15c808840ae674ba973 0x52280233243f0127d20522c02458148900912011940a110042200916011842a2f8045f00914013dc0a44004f7009120107c027980488028720121c022c83478008aa00f9011ea80486457e81cfd009fa00486457ea1cfd409fa80485457e686fcc39f9863f3027e600fcc0242083f5
def as40 := bankPage 0x9999999999999999 0xb8a9a18b81807b6f6965605c5a4e45434241362e29281b1009 0x821097c01433e00346ea0845780c0d5a8c02ad62015720832bc04195c020cad520256b0822b704115a83032d4501972082b3 25
def ac40 := actionPage 0x6138ed88a80438b2309470b6370228555846345224811a28301f19238ac01411b80d8a8fd1000787f30644a7a5204283bd02e203d2801141c6c140e1a1240110c9608860b48e008857c02c2e3e1e02881bd814101e3881120c2809068d8cc08a055604024588a004823b0180c2036002c0d9808030a1b011804900000000e8093000 0xf95d0000b740d3294805f9270780d06860000b4330e0310c4610007b7c000f8ef002e0d12f100d9f90c07001b0c00000b219a40280d604090000f001410b1a001000381a3b04015840c690072404462dac200040084801f00167003603500693cd80cec94801a4a00330366578022340001000645002073500068043230406501e4044024a2080405c00c06094080a00b82f00001c08c9102300002700c3762c70d48e059c2038000a007a20050002ef06d040020a650f02ab4055609e642aa2df0641393bc07781e05c001c4e00640db0ba03e40aeed80582e07d8001801d80ddc0d19d524e05f40390e6012626ac0000880ee3a76283f100c006e400e019006700031425020403c050363021203503552360c94789880082300047403000003c503427d66407000ba10004679705005019006023e5f601b1008e707040b0085d0007670047005850f7002621603898028006589a62840028c084830e121c200ba42802700c0d000076e4ec08000 0xedcbecb8632edcb74310edcb7654321edcb9743b3edca54321edca430edcba986543210dec3eca53ec8632ecb832edca754321 0x9612b2549dd397378b39658790ea1cc1a13025e554a889efa5e31c61e62ee6ec7e2ca58c75ca889c594758e99552a1e31659552a1e31659552aa5444f89c724c40ba95059474ca867e718b2cdd2ca58e6e9652c70ea1c3c9 0x9f00123431f80048a008580d1dc023b023e8007d00124002479648e008e80124431f700490008e2fd0e5721c814294085890fc449f89748e2c91c05238024701428008500123c02473f4390091a18fb40246063ec009100119c2a2f81423
def as41 := bankPage 0x9999999999999999 0xbcb9b8a99a8b73706965605c5a534541362e2b2a292827261b1511100908 0x144370045139401144650045529401164a5004710940120514438830510e24418438c10610e204184385106216c009459880262662009869880c5126 30
def ac41 := actionPage 0x829169b9ec00b908412c90d723006078e06c426732004c336c331c3228c0111818178b1858604a0adc0784cba64009045d83823551c021820b0180fa612400f0e880a06d049604906330402e724802482ae012162a0f80440d7007090f92c08f04e6038287106003022c00c0c1c4e005407580203061c011401cc0000000d8089000 0x1ed8380f44b97c00080016a86c098011002229000e7829b0340546c0090020402636fc24c7404a6c1521fb84b406ab33506c030000001a515fcc0c80086032f030066e3f1649c095014009408003d06f62d0000d2c0442ba002e0000034001554e7c018a094ce0d838807993c1c0f04800f8000d8008200648b113493c0c74dcba4000367c00000d809bc00c50ade004be902272010034e62002960801200608300a0000d0f2b29df10003a006c10901c500e8a030a050f04c69e0640008e9040000d321e0fdc0021926ef82062c00304f410013124166802627400013000404f0fb51f0038000a249c8667a800011d05bc80e80091a9863c8e52be8d038000107a60003703008000000398009802324418018c240c9000000800ab0666801b4140901300030b5537200811b6a07e390a57e0020002500015ccb000165700010c9738680059b5e001600540c700b3f980b001c314a9026d68001324c069c0a00014e306006400b80147b51c8200f29c04798407281159909d908200900407002404700b00600770634200518600e359030169000bef400000551d0062edc001fc0c800d0480093e6bae0e0e8049c89fa18003bdc690351d04ac0001206889b60251683ec0036049080021d358001f492f0000304b0b8030402b31405015a018000010e003c2f01d0658000698ee0060160048301c090500807003a30000a1610000011a2d8000276481c400067095e22d480009ea00060601f5d01025aca09c5048170c780000f777e07003120404006c1e00002d35010051c50065 0xedc430dc3dc93d63db3d943edcb8420edcb98420edca8753210edca8720edcba9876543210c9876543210430edcb9876543210ecb83210ecb632 0x58880900dcba9e508a0d41281500940d293f238366cc40276eed9dabb3764e5db4b02600a8541a8250094c890cd806fadaf283504a01d8aa543685509a1132c654be0cd93100e013ed77ea950da15426844ca8cd806ce93f21542884ccd9732e066cb99701785949f09e0605949f09e06027a1e43a87225ef5d168ef1c611c113ca726965198822626f9692cf378b3965 0x250a1ba7006d600da80a502b3b21d7563aea811b18035e006b8913ed2274804e1129a41132c0a63004a00093e01278024e8049b0092e01258024a80494009260d01939ce02361006ba00d6c0a4e02365006b40526811b20035f006b2013d52275094d3009385726ca24d8249b00936012641a03834022b6c050d8011b000360286ac00d58324121bf4009220120c3240a1bf30291a052080240014450e908011fc0a23093f202918012300a4080481008fc05110022200492008fa091f0023e1fc463d88c20fc831f9063f1
def as42 := bankPage 0x9999999999999999 0xb8b6a9a49b988b655f5a544c4544413a2f2e2a2908 0x2708795843ccc21ec610f83087d0843e0421e4698b230c591ac2c8c61646d0b2328595842c8e0e646933 21
def ac42 := actionPage 0x8428c2351400d975320c570c570244b428ee207c5d013a51d06f0c3922801b25b830059985801410841402ab61b00a07160801550058234328c3c09248dc09317781903d047001189ac0b4186c3b005043e0440a2b15804419f01c03109280150a78070106052011033c01004202800800ad80601090b8016034c000000064011000 0x1f224490027f40010301a0df0c0a36f500111003c0d03c0caf9e0403dc83be039e800588d88600022303cf2001e80365ab813e070c91ef500c0e0002f75573f100000f009ac6e2390604c4021702203fb10e7f040023f034896409ce1a900002940f0008fb2ca107d806d62c0f80b0d00bf8064003f000830013f40f4388567c8fca8084022603383660c5406403cf1d000a0066a09080054c008828048014001ba0434093c2003cba03ffc002e7783290bc685c0b60701e05049c96e306262aae166031664c08e440030007d6402fafb95b406c881303e18180cc20000000894034068c0368188f801704ccfdc0000024f8a680c3c012825fd7a1ae68053a001814164812000f440020058f6458314c2c2a0001480003bb0030100032c055800968c202825fad000001f5480605b80f881d12800f100a5344000012045b24aff2128783030496081130400e241e303c005de9000a388c091c0a70a400000d0017e500ab8000eb80b53800012a4900000d440400002b01d2824003c001210598d471487b500e630ccf00e700005056050f07070d6000050bee060940b4a001100a788070108900002a00010ff000501c1b0156f89b60502800001a98180ce56c9f192a8b4102553b40bb300c0180004026e35807504082655d5bd3a55c1d48000a1fb0444a0587cf0030002a6936f6000012001a190056c003c85000cc0000583cd84ac30006c95161024172842c1204228a70ca03800049c060810009c8006803107274006632429aa07069404081e08081802401848c815009e012e0980a500075800202220640099004a580aa01c080384800101d000f0396000108e710b06d6802508e8d4902c002256d3992001da006c2000c010f25b7e8113b0031063800e681a0277e004d3d20340301e628384fedeb7001170360a380400009820007e40ccac0a50809202cc500e002e2007546001eb4b44f0180002f0d000070022706803689c00741c0040be0020680685806d30426818b5c02231b607018e04140a39f616800248013602c9180400102b01ccb000042005000538700207140097054056000c00a01099ed5000e0700a99998e5b30d9f000310f15e800990 0xedcba85310dcba530edcba85320edcba86530edcba8543210edcba843210edcba843210edc6430edc76430edc98654310edc98654310edcb865310edcb85310edcba530edcb420edcb64320 0x80900df2a5042a84cf818f53ea054021542701201b3b502a013f2514a0854f81d67e0ed1d9a5042a84cf81948088550a9f23e0220f91f13e07c4f80883e27c10d9f13e0220f89f053ea796bad7 0x3b4d80096615095da10083f70072856e28adb1004b2007260137802533049b0093601255ee130342606848c0e4801c927360286c0db3f5de5e36cbb02966ef1d089e18eba900722012c81255804ab0494001280024e0049a0674208e7c01cfb1b926072400e40a1b714356069a80d2dc025aa9cac04954012a8124f8049f00930a71884a052ebde577bc08e7801cf0038f0696c092d8025b044b402968012d01a54824a9009520d278124f0049e0673a08e7401ce8038e02962acf3811c68037b069b2012c40258004af009500129cc622834230071200de80a57024a80094808e3001bc834d80299a012b80256804ac0094601288c622034220471000de00a558ebcd567783aef011c580377489dae33481a69004ab00954012a402533049b28936df250124a034210470e00dd81253004a6049260124dfe133dc267684ce3098a1b70036e3a82e75059d1c6a938d
def as43 := bankPage 0x9999999999999999 0xb8a99a8b847f73716a66655f5d5a57545350464544422e2c2a29281b08 0x5220129b810094d40130a6a00d0535404829a882490d40a058aa1402c550601a2a850191540804f2a042259902412ca818096544804b2b040259 29
def ac43 := actionPage 0x8269f5656800a0fc4118e0acd3005873a080625272002835103a26a8548014182819905398400a0ae30b8709a91044450985835491a0016262c2a18a211410c11f6138b4fc8a006885b08c50725600383da042232f2d02221ad01f0e931a40110b680b85c64da04e040c0481a1eaa025c15582008082b8022077000000022001f000 0x1001a2b2ed1780f06a3500006061aa03516900000efcd2c8010ac1025d65003d4280000012002345a70e04236d001502417a57dab6a6bf001b00000060208dc00caab200320d8277082dd2606d020170f897a8a40d580046038504025663c0000005ac1e076260381601c00d91e307a3553600084c0039000003c40081890365003210b816d58a1070000541a5f4007e64002e70afe0fafee22222e0c4f0a025c0000003a0800018044e47005220153a400092a4d6c1026001c50002b5ceafa82a001007e0c0e00c510b8d00108005040d0224f00025408301bc50200200010500f17011072627710085011207926d000000d077402b95600f01500871e740dcf016f030400077000095303a2032330e0a772f70bc0c00600e9bd4a00000aca00369999a31d059c140f600052140802c02181b31800f1a1a003c405a403400007246c380027818f000958176581804cb360017f0830f000e02644503e209000b48d0004ce79c80f0b81a200818252086800000380008453ad2b04800a18652001304da70006900029fce29038d4c141e6007005c0601c0c91406b2d530000241302a9b04779103000001f047c8a09839b6e4199776804020c0b280606bda18800a1006aa5c0e012db010f6070020072b200001bf84f4087800e00003ef6003450f85900578004001d201fc05d402280ce9a031b80000481d02a04050003800c629e0020afefbd0abf6e1e2c9012a504780d809178123e81070507f1fc19 0xdb93d93ec977474ced73ed732edb63edc732edcb875310edcb85310edcba86543210edcb865320edcb310edcb8530 0x93300df72f954a8710ba1542679068c22806d994528843885d0aa133d8790ee116ba172664b98688c9982302602a8d1da0340445af3de6b9371acd598b2f65aca593ad5586aec0d716d1150a6c4aa94c8b5c9aad556a1d3fa78c09802b554280900d3da774a9442554a69450120173a2a81eb9e73a2a81ead85ae0800fb9e73a14c2803d50685d0a9f23e2a050c2154267c8f8bb776ced10aa133e100ddbbb6768ecd9529e42a7c066a804a49450aa139f901201b3b53ea7941a18 0x1498518ba00f0801dc28ca2518b42700c41fb803b72b6c450d60026339cb9469728d1b155da803b5009c00525c024ba7bbe0077c00ed0026f81495798080901012002b3b2007640524de60237c041d75600eac025e9638d0097858e30025d803a62c712012e8025c803a52c710012dc01d2004b600734c7140a1e493bc92876e4eedc19d1823a3007320d2cdbe54063f900730dee240a5900397489de0d3540268aeccb57996012d4025a0049d0492c01259ce4a37c940072a9ce1d45b0a7361
def as44 := bankPage 0x9999999999999999 0xb8a99b8b89887f7e70655a5453504c45443a2f2e2a291b08 0xc0251f80251f90411fc0411f50419750431750511751211758211770411750261752221750416750491b54211b50c11b 24
def ac44 := actionPage 0x82b97d8d6408510b5124acb29a0074752082514e2d803a33b03527228e401c168618928f88e0098a5c0b48c684a0250496050412b2c822a1fac251e9391018c0eb6110e08ca80c606cc07060348900502cd83029163a041c13cc1411099cc18e0896088802c50048038c024200f04026011180809053900200590000000254117000 0x300820e9cc478d200200041d80691809026001108a833780fc064c7c04910e702d005608d0071509a10044901d000b800115cd1007501bc0411f3000010c800000c62df6801083eb0004e880400c40fa0000066f00b070022d90015371787800258c02b0c5620098038a4d99805467a0001711d21f600007693f540430040001400317107c19b0120c3d9509804000007580603c560d44a69bea73487fcdaa1036323a265a0148007f4002c0000621880fc03a006817400000dcc000180102000c0f04100100016c25550c52ae900c923008f0d0500c5b990100ce12af0e543bd001b021e00000705c061001700e5d0308e607a000660064144d48d45f7a1dfe001c8103cad00180df0e9680004dda003f435adac0b50003c103a4a6000d1380000094d5b806681ef4852d6c50000930005008400033a3065050ee4f6002c500f0d0c2c00000d045c0e7c755782a000000541c81800300b009c028409dc050600e23818035f448000998f5b839398820e18f37100e60a2902e00d8bd54080580086f7c0a5080900b507e00040804400cd2f090d89307040af08056025f9d0d0011841a0a90f88e000102c0897028070900f73099ef9200203e0803e041016d00007c7b70614a010004014a06315308129f000cea40a00126c0a03fcb105b41042b41ab502b000022a39300e0008050540390e08490026f573814d07900000340044eb5840f2ac020240005ec703c2318c00001407e843008000a01b180037e8401dce41a843015a0 0xc0edcba86310edcba854321edcba8310edc7630edc9865310edcb8531032108510edcba5310c310cb6edcb4210dc93d3ed963 0x2e95c8b1d5763db0458ca7d281f114574ac7bb86aeb1d6329f42e3be02c0442e854f8a1742a7c4f91f13e0228f91f13e02290e1f23e27c045526a487c4f8526a48870f89f054aa8d5029f53c944f89994407c8f89f011822802d26a48888f99f23e27c16c2d7bcf61a02403730da9a2305608c0951a834ac9548b0d1abd576adacd54a34466c037dcbe552a1c42a84cf20d1 0x468e7070344a06aabdf007bedf34842692accb0099601319ce5d234ba468e4df03842072abde007bd02e8019d0004b35195ca31904206003dd0674450dd0a1ac004ca5395aa32b5763ca9c63518c62502c4205803e0577beaaf7c01ee014b0108345efb401ea814ad0094a5efb001ea014aa518c0f0ff041fe003d30294eacf3801e7014a61d79a00f35da6c3b48b107f600f24adc5143740099a01294bdf7003c70094805288120f803c63a82af1050420a004ca519460527d462d883f80078200ef555da8149b117ec00f0001de0ebaa46970052651a34003b9
def as45 := bankPage 0x9999999999999999 0xc5b8a9a09b8b8074655d5a575146454442413e37362e2b2a2928211b13121008 0x268104833481048344a20883a48047034480470360804703408047032482070324806603258046032c8046032428051524204499402284714062845124341051 32
def ac45 := actionPage 0x6261e1084a0068dd3124ec7826003469a086743115803a2dec3f361720c00816381c17ca9a800b09cc0c0a64cc4005843e03c4d2132804819701b210e2d40110ab80b8cc65e6049843b048562e8200401bd81a221549001e0b0c0a0b89ac800b047603038492208501c301014164702280a58040805130114034c000000214011000 0xd063b65033000003005c0016785f09055592b0a0e700750220001050008010060272619a10176600480030ade00140af54230000330e368805100830800207843524000009a28105804c000045628633000030548509c0003a03a163208a0cd460f070b0870027329200c0067ac6270000ac80080000002a26fdc1c510a30011a7000b883631e5901682604006c96bf02f200100603c0683a002400801d30000000c053f1a212eab781c31801f5a96003de050d62c8145c0ea06e2800110000788739de70744040383898540004102be17900d15c240581b047fa41c1a07800a81c0f800057830d8805180000d40030006c798005d12060746647e21b200340f02ade011c0006007b690004021c100581e448e5024005008c658201018b0043d0240000012b100011c2d00028a090000ca01db701e0e8c0203c9002c60552864fa700c020544e6c0e5d93c94003c03e09a90d05000c0f500e2e6479055c050a05060c0b3080c50bd5c4037030690206f0026a75070b07000e5085b205d720b07e30640380669090940000a0280e0617b00050355a0f4000f04000d0500ee54a0d9fb6086260f0729000360605000f5000b586400600030ca0b4fb9a867c0b000b22b0b001057bb100e708009300 0xedc63edc530dcba6543210320d930d930d9320dc930e82b252e76edb7321edb763edc74 0x21c1f18707c5dba819111914fa5139e694b893f9111de3240553ea19422834a273cd297127f2223bc6453ea15422834a273cd297127ef55b02c750ca1542477808a7d42283502944e79c72e259ac450d9b132244c778ed1994fa513a8740bd1792e4a212aa524a29409892e070a9551aa053ea792899c3321aea1cce9732e23846f89312151a564ab0f21dc3986f0d578acd3e67c6ceba2740e7ace39eb7d67ace54b7e6e78db15b 0x1358020f00412628be0d0e40208af456438ac34f5c61eb833d7047ae871c032068040d5d7b6871bc32060040c1a7860cf0cadd491ba95b99aa73356e3d29c7a438dc1902c0205aebdb439d801354026a064d3009a61d3483269014d2009a4012850e368040f0e81c190380a070040e0c81401028026a21c69008120134d0e35864010c7fc013490e35064050c7f800fe19e480d4310c7f600fdcadd4834c20498400fac1260834c00485a00fa8fdf0963e10097a58f680a5c004b8
def as46 := bankPage 0x9999999999999999 0xb8a9a38b83806a6665625d5a514e444241302e2c2a29281e1c1b1008 0x5018487501828b501123380a1a238281a238182a23560122355022238080bc39082a43c082a438082a4350c0a435880a437080a435086243 28
def ac46 := actionPage 0x61990d45460058ad30c0709eb2002c52585c324e30810e27cc2b16a515008d12a6138a110ac00708ab08c487a4704344058421e3b3100181de81f0d9c0cc08a0e380e858b8b4048062c060244a49024c285826101d14012610900b070a0a4021046604028388c00601a30140c124500300898040205220016022c00000009400b000 0xf0007603767079c60b08b40bc0c20ba5007000e5085b205d720b07e3064038066900020126b0552106b05306f010909e40580905401d0c000c5009055b0f005846046003f00c100606c4e250b70e9c30cb9507f0c07007f03ca2ba000fb07c05d7ba600070070944cd8633530037006040400520907005030009931006e00b812c18c3390d826250013d794000253200000704e30ad560240748f0d1baab01c05d00089c4620c030e0863600241c3040600001002a50bc6a3201c5836691419000097a4a779d0020353030960f0b0880d0185800000d13fdc010150e0bb04d018004603907aaa000a31460001080018504405380c509c6a049a02228b500053800051507294006816a582420002e724010380b6c400004032bda0338063040b495004bc1077f80a880c0082070f21f6fb0000088b3687360e0001009346b6b16006790006290d80f709047040fc0d120170f20f605389000a0f0350502275000096020146010833040503 0xd74e77edb3edb732edcb763c7eb6dcba873210edc765430edc76530edc76543098751098520b320dc630 0x5439a12f25dc7f8a313d51a564ab4d6684bc9772023fc5189ea8d01a029b72b254ba059a8fa543a173ee79ceca8740e7dcf39d9552a16d2d89552a1d039f73c90a554a85b1146282f05087ce1c1f43e67c61c1f13e67c61d4383e27c21d4383e27c21d4383e27c21c1f1 0x34c4049880d32412638042e5f9b4590b4025e804292c84601370025e004282c8440136c025d8042a2c84001370b20f804db2c83c012dc0213804b10a94ec517c020e833da029ae012c04a1b8041c317e005360026c014d6009ac012bc0a10004200083601364320d0041a009b0012a0020c854a70094e01060026b80414
def as47 := bankPage 0x9999999999999999 0xb8aba98e8b6a6665625b5a514e4544424136322e2b2a29281b15111008 0x8500913c18048ae2402497420124b8100925981088ce84105a7014125348209299810494e00a84a650414538904429d082214e840272650a0293 29
def ac47 := actionPage 0x6231453c8c0470c3b10898905700345ce07a483b26802629f03922978f009212d81990c885a010877b0bc784470042438585633214880101aac28178d91800b0c46110a06ce0006059307040368000302818321c1523001a118c160b0a18408907e8080502c5200e024c01828060804600718060b0248800e022c0000002c800b000 0x909e0b0700c80001c5c305b01ab0b30275d8000a5700000687068b0db2410700002ec58af90a00f7b61f5cafa0010dd59114480f182c09d41f0036f0001000082901ac18ae533d0082a20490101e07028183caf6bc007382200000000c0c014290001035682800038184019641808e022aa3024100e07214b019ff6800107060056605000200151f09606a9a57d40e0782d000012a9c35940d0000e5169ac3c6001c2023a0831c0c0340900de002d10a3009c005b7042700a30a07b7010209b0008379df000c7a020e017017016700738189732000080e2420721a039700ca68028000350b000922e0a100153b0491008f0a07d000630f000e7210d302100130d050610061069940010281070496d0070030009d008a042e26000475fa030081c04000e7b80000020501c7181b018445114861208910000001c70286077c0b0a86a000005a807b0ccf4800340047380046810c008a0597c078478700e400003101a011c601816000028380011800003402781a1000a03118328c17133200992805000a304c00dd0c06a5ff07000e5085b205d720b07e306403806690 0xedb732edc6321edc9876543210edc987653210edc98765432100987510edc7304dcba54321dcba32100e7 0x3a073c4cc984ac952b716d2d88727d4f99f18727ccf89f53e740a564ab952fd5f9a46b1126e38ac7542a1128a173e30f21c9f33e32121e43b872b3550a9f9090f21dc39542a7d4b2468770e4f99f19090ee1cacd542a7e02ac7b11226322a14a2748d417428750e684bc9771863045189ea8d01a02 0x32488648c0088800fcc32218044335884591080a6c864410088234f8419f086440008807cfc8c5f9074420c8840510802210643f0087e05374021ead43b2c874010f04a19084320c86401364321b804375a9a0ad3401a670243b00876010d81268004d00699c090e8021d00435009ae010ccbdf8834cc5a982ad305563c23478438f040f5869eb033d65d8eeaf1dd563ba4477468ee871dc4a1e0843c0c878010f10e3d86432008640d320126380430
def as48 := bankPage 0x9999999999999999 0xb8b6a9a7a4988b847f655f5d5a53504c45412e2a29281b11100c0a0908 0x2241a819121540e0922a0644c150322c0a8191a0540c9902a0654815033240a81b120540e0902a0740815038040a81910619148822a9300a0cb1 29
def ac48 := actionPage 0x637926a074008165c1a887386c0260a7a0c8408f1e81344db0601dc197009524582c8d5d8da04c10c414460d85a007078e0962b5f2e823036d04212a91b401a18581d87d14da00b8acc0d434725c02604b2056192b0f01501c30210c0e87812609980a0603c1c00d83340301a18b306540fa00604064b002c028c00000011808d000 0x20cb905e0038300b0c60706010c29ffa995003e67751d20823d03740034cab280000027f7346f001aa014c97d8103f263582800bc7b88071074005761680016004015a64014650009b3c05caa7f880005a06500080020650686d67006539660352329c200016d01e83080020280000dc86d400507e000406050ce05c0f02c0d5b40a001e05280a8ab60012206a4007f060700d1a08c40ba89c02e074d8f1dc11070ed50141a00001033f7cc57f8020b3405fc409060c03100d466a001c0020818ffee3f14080008bdc8b000ed236007d010a0a8017001ae28aa02800bd001f41e466b0c00036e0a000009241040070c069810a380cd038e62e5ebcad20dfc00004e8645a0001f1598020080c0075b55060e900d78298bcc0001bfd0280000814e8141e800dbe2bc01cca011e2014f0295e74623984ba11865b8009b680023a4fe00004f600000e34c09502500654e600200234202d03bd8e80017d0399f012001a34fc0010180224000441186d6034ea110392f4ae0109ac00007cd1d1600212b340022616490002afc0740c9dfe07040d00000381c9ff0080281ebd000a0ed9b1c131800d78080b0000de22dd556079c12701f20ab90481401001dbf46002b0019402a81800001a62a001dc01f5b136240e094db000a93094898379882648dc13bd40900cbe065ed6001db15ab400ee079a040406bb17103226000b7a804210900028306ea10340c9e00e0818651120014043002001460481a8080a016f80b018053d40490002b8a2018a6019232010d180400242019987002e0100111dd2228006100c900ca06bc1f00dd5813458c003e402090048eb00140680031138000c1c0c5166480e038e07a1a602400034000b1e80086a05d80694002000603c018c4a90552081c18600d400720e200005515a814800000a210e3ce6a00c130021b7012a52c4c006af031f01c08060cfb03e001960402a8718007cc09025a50340a21f40000004200830f67061bf037cf0f7488590000c0400100655dcf990500433f0010 0xdcb9854310edcb87653210edba876543210edcb87654320edcb876543210edcb876530edcba87654310edcba87654320edba876543210edcba8765430edcba876543210edcba876543210edcba876543210ec7ec7643edb632 0x3e425c4b4046a6a78d809712c7c04b896652a78f809712ca814f1f013025c4b2a053c2604b8967c8940f809712c949281f013025c4b2503e47c04c09712cfbd281f012e2584b897ab155ea1d3f60ac095c2a34dc9592ad78a5349966ab7544a854fa53740e7899930 0x4e6008b00139402528045e008ae8cfb01a58824b1068ce0919c022b43c4f069c601154320d21bed569ec053881254004a4048c2011700229ab4f6009c80928c025180460048b60116c0229004e30a9ae1522802288a4374a7e0013d00271034d8069ac012881a4583489008b401140127a024a706910c717c122fc3c4f0089e0538c2a6c9a48d349040113889f0834e7049c4013881a57824ae0095c0d1941232004640089a0d3c42272814e50495a012b4c63f02463008c6011304a1f834e6049cc013982272014e4009c80d2b01256004ac068c40918802310044b029c2013840a62804c500986052fc025f8044a009be053795a67804cf5697c012f95a24804490487c192340222803f4
def as49 := bankPage 0x9999999999999999 0xc5b8a9a48b8584817f6557504b464544422e29280908 0x4842dd810b74042dea119748465d8119740465ca50972c425ca131728545ca191728c45ca911738445ca10db 22
def ac49 := actionPage 0x8239b574940490f0310cd2ac47024871607868470f8046306c3a2ea2ac800817781a15cecd400a8a7c0b0a46658005449e03e50251700461cac1c258f95820e0d060c11468ca00785cb058762ca4003c28982632124a001c11b00f1187bcc01206b606064314600702b401c1c12b302440da0040306598020030c0000000d8090000 0x1cf06cc0001516a00000010029a02684f6b0007100d8004f0445c6a90e3980000012901d106ed0781a020d0c510eccc5004000002b0c1d7a57e4d051ee08d9b940013063400ac8023c38f635005b418a800c02e1f8cc07d800061df071817d805f300000cc403a383301480a00e1601b07d6459800e2c00c8c6d9a80001480fa20050f90ab00157b93700404b3e6300dc828037f1528c0004e3400473dd9ba49b2b500ce0400020100680009de9a00fa08a8120011c50400b0240300b819a4000c49071602440f3ef2408080740003b5e090000865c90038b828120080160500107ec0003c00c5d5a6d9e03d40e62403005ad35060f680003d23830ab081c000011310e443f6ed430253abef42374ae20000003800044d499cd74881aec20042406b02e887e1200d0c405530c6000d0032090b9012207102f7e568562225b6005100026f00520087400d00f4e07f00782c2f10009cac90ce80e1aaed316700d00c27090a004900f03250b353594ca0b2000006b01000c400bf581404c400d32251040f0001c0002d00000543994801b958a33bcb11199d0319030e137020e75e0b92600a00a60e0502000b481ae003c40625c5200015bc0902dc0002c20846c8a160011a0484ad5810701c0d01102c8da918008f400908015001e0055455180033c0ddb4a909f6e300a000095003833765077067132351705f78e008648000970000 0xedca754321edca730edcba987654321032edca875321edca8730edcba987653210ecb431ecb83e740e740e74e74e74e74dcb730 0x39d1be3405739d1be340570ae7e4f9dceb97604778c518322a3404e39d36c6d4680560a8e75810d00ac150800567e4340678cc158fc8750e41a033c6628336c6d4ae1151a01582a8540a6fc9ceb97686c11811b636a455f939f73ae5cdb1b535c54ca91151a01582a8540a6fd1f939d72e6d4ac1572ac45c2a3f47e4e75cbb0236c6d4c511708a111f939f73a6d8da9891d415c2a0530a27c84b896 0x52f40a3a964676082291208b23309445407c2053b80277014bc00978051d0023a16465009e0011c01a77004e806976631d0023796464009e0053ad224080473008dc5918c4a221d442009de053b40276804ec009d4053a40274814ba00974051c802390046d2c8c4013b8023896461009da091a8023516460009d8011a402759645e467dc013a8025c1646b008d0053a0be389645c009d2012e402361646a2c8b6013a01a6d98c903191e59168027380459
def as50 := bankPage 0x9999999999999999 0xc7c5b8a98b8180655a504e46454442412e2928261b15111009080706 0x1902a151888c866101a3ca101a3c2101c5c2501a1c2122a1c2302a1c2105c1c1908c4c2088d8c3118a8c20d0a8c20c8c8c2908c8c3108c8c 28
def ac50 := actionPage 0x61d171b8c40c80d840c4a8d484005c6118604e6731800c2f6c2f2231a9018816f61690560760480abb0a476a466003850984e364b2b801a25d022182299800f1116100b4f47000887bb07854663a044037e03225272e002c16ac180d932840060ac8098348dc604804740300c2e7c026817600c030b1e003405900000000ec017000 0x6001924090621004d0a10c040004361400f9a0502447708009c1cfe61c007c1000801357b4d380e378d20e9cc0300050128e003820880f39c03381e00640902403038e08b700c010f08072210e55000fbe05400c95019dd0ea05002c74780e034006d73e0ec00a600bdd9c96f0a40b9005ee008a0000b0d7060edcfc009300d03007698c7bd0ed0060c100000b055570ab072f060e014af33b4003684070000b01fc56088f01fcb504007044050cee781400a004781480d5100000b10a2d7ea02212e00012b08a0a80833c004960667b00bcb337a09b00007893d680004009c9005200800221faa05016045020102d0118199800768100151ec50400401e250440012ca02d98006631800903da64000b23c0000b9510800728a42f05280e002c7f8220181c32c804799200024d419050198908089025c30ac013a07026004083c0000daa490000950a00f017279c0e8f3590728bb2e4f380002a443034d40000a7a00741c1dd9470a9e5d0600026e04b6fa801410249ea84202e000010e8cde0200a007bdd04147ea8869307b4001003e20083e70740089da38a01500f05000024000b0a0e920e5058b021a30391c2882138080060022380000000182c07800f014c8030686162f 0x746543320a320dc987653210ecb731edcb730edcb43dcba7432dc98765310edcb987653103e70edcba8765310edba87654321edba8765310 0x26e4ad954e85cf28cab54a6932213e87ccf91f17405ccb414213c08dfaba03a2728d39732d05084f0238787d84c4aa7e65a0b39651d92b6553f368c72a58cad954fd9f99cc87b0e8fa1f413025ee9d2c65ea844c5887e6e79cdb6b686c088b8d013b74ee5bf3740e79a3307604628a594a22e21041dd36aab1d4f89812e1f0f889812e7c44c097 0x29f0c53ccb279804dd609b4013681a7a024f4069e6093cc0279004ce00998053000260004860090a013c40249004ee0092001238b2459648a467e2c33cc026e0048f2c91c59224027380487009e2011f51a422ac7c008f886fc8fdf90047b009d65f244be419647a1088601394026697c8c2f902011e8023c88442009c60d2c0be4000478068cc21104c63f97c7f5d8f8011dc4a2008440
def as51 := bankPage 0x9999999999999999 0xb8a9a48b84837f70655c5a51504c4544434241362e2a29281b100804030200 0xc0830923010612464218248e043049180860922a90412454230248a942049158840922e108124540c05312881065450220ab0a08093a140822b428101968 31
def ac51 := actionPage 0x82994138720098ee412c9c8c28008467a08a4a3b2580282f104023980ec01415281c114945605008b30d47e40650230411864391b32811a1e0c2f198c18c00d0dc6150b058e404886130944a2872003c2ae03c200f2a801e11d0170c851d401106e807844190804a82320301a0c4002240ed80e070431001c04d00000001d0014000 0x2866000a301baa5b72d0010300c400014d3b00e628ef621b6021137092000c0003150056a01cc1029a4a440001e65047ab1004205c00002c000086282c0181b4200001c0800101a2c4c85280f031014a35f0800b6446b620a627d9b00cc103580005c5d01c1a04046d000c625ae0700d4495657c14654029e9b1f08800600800037000a1032dd004a186581c0700378020203cd004000004a46005ec019247a552c000304006e270229d058d09008a5014a202450000379469030600398000140351e858004482a00052200400000037a8a0499ca4bc001394002ca2005aa382c90080662546205e8a0090d1db0d603ca090510fa009b3066fda0000000eec0b08e170506d9e5d0cb97400ba800000553005553000c00570357040999f30910e0030309b043c020974a20090300a98ad4703880001073090c05fd008100060d222200c00700022863886003664a021496f0f0800060000069cca0360a500a8281ae595e8630000982005400228037384013ae49bc045ae6079c2181680782806ca0f881204a0201400b00c90380ca500000b60811c0160a04adc9001851bc1158000db04002140a800000487b8137f1c09011c2056600180a0140b6149014098779044070010005070f0c0c80d0025302fa7077e0bc058d85040020e81607800070800523600334e22c000601f68140400718809a8b9c023c5d80ec605607 0xedc765430edc65430edc98654310edc98654310edc9865431098520cb310cb6b6a5ed743ed6437643737643 0xb5c4588911a22d6b88d1162256b88b11223445ad95ae8784588902cb656ba201162240cad95ae88845889034b656ba2211a22c4481a5b2b5d1208d1162240dd438a314227c4eb6d6b6a1d3f54c87d0bd78a53499672a2540a7d29da09592a628d298a30f21dc3a8734a6934518790ee1d439 0x3a9b2592c002582448d1291a053f4027e974bb2c976052ec025d964af0095e0d3f4027d18cbc06978592b80257014fc2c95a012b522460948c029f6013ecc65d17cba06974092e8b256004ac009fa592a00254004fc2c94a012940a7d164a400948013ecbe5c824b92c9460128c027d18cdc069b8592880251034f9049f2050c002180142e0085c00fac027c814f500992013200263804c400984093dd5a7b004f6029e8ad34002682b4c100982013e15a1e8043d009ee053cc021d8043a0085a093d8027b034f20086c010d411f5003ea
def as52 := bankPage 0x9999999999999999 0xb8b5a9a4988b84838065625a504e4c4a454441362e29281f1b10090800 0xa0488a3c024451e890228f048114788408a3c820451d912028f408129b80602a5c0a0152e0111297018094b24110a9c00d054c90422c70881943 29
def ac52 := actionPage 0x6269ad81640c38d3c10cc8a47e026c5d208255507902142c343227219f401f11b81691cd4fc00b877c0907c4e9e006c2f1846352549000e162c231592a800050a96100947ccc00584c30743e346502282258361c131b81140f4c170c868d800d06660784834e0007827b028161274003c0e180a040838801a0490000000120013000 0x79b8b00101da0010830bf005000a00eac55f0fb46e00030226819a800026d2400003580021b5df000c0e7008089692004061ea0280008899d7bd3170c0001b9450059400080012f000d1920648162194000e6c02b00066f0206cae6c769000513b40033dc0c800120292c00352fc8e158802f0192c0c45f80010a6802105d02cd29c3c0a003208002c5403801cf80fac04001e95627c0010001ee800203816b23c00a60810104000520078e330379e80701880d88120899d3051f36800e44259780000cac3d9049b17381e00020000104808360c14002e935eb300d11466a0036030092001f862000d02c06b5f20b02a00012b675da000b304000441360630ab0020a412d7010902000d0001c070d6040078537d80af308a50400a00f0003030d04bc6d77b2d7708523130000700770950b18fb7605112000a80b0c57030a32098470b010460007e009d6600ba960003d0208caf000c24c03e00a0be41a14060096ff00090040d3500600804002c37666316b9c00d202a40da0010600260a090b0351a7007009e020102080226c00061c0200686b007780e00182b008005016f4140c402086b54e3340e129a0530820008c 0x30edcba987654320b0edcba98765430edcba987654310edcba98765432010987510a9820edc6430edc643c3105edc65430 0x27eb2c604b18cd0d01802744b88b1073f5ab2c73343b8420249facb1812f958c674cd12f1a03005d09d12e22c41cfd33a668588830b2099f41b736c6409788b0466dcdb13225e2c4458570a808dc1b523806688a9041d82744bd889371c560a7941e2603f04e03ab6d6c22011a22c0cadb5b08804688b032b604688b5b023445adb5b4b611008d1160656dada5b08884688b034b6d6c2202aa234458195ae23445889 0x280004ff009f8633c01a78164eb009d6593940272a344410888113fc0a7f824fe009fc093ec027dc14f2319de0d3bcb276804ed2f9d2593a41274804e92c9c801390b271804e33c9b2951145222834fd009f5093c8c677034ee2c9d0013a0b271004e200a006b364b26c804d9009fa59360026c164d7009ae5936c026d964d6009ac63374be6e834dd049bb1133a1e67164ce0099c013f0b266804cd46922212465e6d324da8899859300026018cbd0697a592c40258b0418
def as53 := bankPage 0x8888888888899999 0xc6c2b8a99a8b737069655a53504c4b45443e362e2a281b15090800 0x16a118028e43005148600a3894014512802ac25005984a00e309401541280388250051458010208af602816e408329c811453d0148a7 27
def ac53 := actionPage 0x6309d52128006901c174d088d4044478e09e61403a003835d04b299eb8c09218c81e134e4c800e8aab0ec8c6c73003050d8743d3349821c25cc361a9820c0901168168b8a8ec00e070c088504e63006c2ba812212539003e0d0c070f8c8b001005060284c5d84084821300c201c3900400aa0020c03258020018c00000030c008000 0x1005cd0a07a14000b0d107e1e1fd00690b0799700ec338b8501ad035ebf188d0806cf81040236000373000050140d00183b00100f801fb92a103060000a030000eae16af804959d0907d4a2a8000220f48150152012a9604fd04540690a32680777eb92900000019201acc0068a4dd036000600f001785830e00000f016ba8212048205187703c1146ded035be19cba014cfc400904360010a9ff00000423580c07340b024000700807d6abd5fc000a60616076bbffddc00297f3001f26f80027d3ed020000000d0e0bec46c6f9b0c479c7c8b00d92fb40050b04db0746233037e000014d02187024008a00594a000cce701700b99774385b0256e05d00ff00870059207db6b59000c82206002630d80003bd400008340871066b006c181154241622380005945741ee28000bc0e019002140000140053dc051a0ec24802008e03086016092a010b994005c0000000cf00e6000902800001094404000000551e25011d250d92900ad1a00030000049d87e00001f11b6406801018800005007821003ca540295002329e800027407d0358008c810001e95400039874d055f01400000001d01178171133500570b018bc20024c35094006a05fcca009004801286fe0100000519a020a0a0d5a0b00f0670a06fbbb10d000700232050040e07d9e0a00012b4503c95e030db2c62c03c093bf591960003aeb0000010aec0008003aaf022e987008045c5011217fc80e0e0b0e094f090730de 0xedb3edc3edc3dc3dc93d63db3d43ed9643d93dcedc987654310a1edcba7430edcba984310a20 0x24abff7c0c5109a1142064465595766ec9d837a63caa14027f4fa970878ca7fefa9ae35b5009fd3ed95766ec9d8367600bf94c2804fe9f52490f194ffdf535c5009fd3ebae4268450820932632a4abff77c84d08a1041264c653b075c84d08a1041264c87bff7a2ce53e213424845ffb394f884d09211bcb792ec5bab0d616c208e046e19aa2e133a4c88b90920a3b45189e1302341182211a15c13021856cb0f319a314608be8d01802744b88b 0xa9a2b5891db123b6200a98b560748c0e0d6edc6dd035ba00a64014c402980052f00a5c014b402952751200a24054a402930051900a10917f802e9835b508b280563802948052800a4e0149402918051a00a300145c02838050502a48054898efeb1ddb29b64516498efea45fd29b680d6d09ec9015921da4c014980a8f0061006b6c0149012918052304a4001480028f8051e04a08014117b02aee0558be8af7d126fa245f41fbd83d7b04ef6095ec00b9c1944002880050f00a1c0343402868050c0ca12014243283005060ca060140c0281164f1009e201404027f964e7009ce59398027300501
def as54 := bankPage 0x8888888888888888 0xb8a99d9b9a988b736e69655f5a53514b454341362e2b2a29 0x66209152209184209142c02e4220ce4220b642303642a0364228964220964222ca4224ca4320ca4a20ca43218a4a218a 24
def ac54 := actionPage 0x6199c114ce0068bbc0b0dc7a2800645220466e35040026248822341a98000711c610978c14a005885c080a852a700443ad83e4f232b01121bac1d248f99000b0cc80d0fc694a007857c04072266700701e981e33103181140d6c0e1406acc18d05760608428e6086022b028320c84042c0d20080c0369801c033000000030c00d000 0xb00000510e123c3f204b270089c0300005760200000000e0300b2b8000814018084000007896f1958c70d4042cc4121a70000b5bc6a3812d316e1789aa0250f41c0900310457112f2400000118b8020401cc050ad0018e074050341b4040b8a8ae001e80008c3c9fc0001d810f4701309582bac6106006000d0d0715f05ff01540741e6e840870960001027ac8bb880a00c00003e80380f000ce100182302d09003bf18500d0733bb30983000602062c3f2045d000b0a00f50024034c8650003c04c5309702c00718146a9c5080097012f6096c0000eab800081c00c8100438c05bc00302602018e01d000270169c1542c090806038060a08634801d59620030b75c813480e0020453b64e4016060c015407001600c0d00e20234327002046060500b4009058c00690407a02404000020be2730e73e20ae80f2000af0d640072dea4800054010c00f90170d60038e8b10d0a104da00d0000e18190b72b03b710596af0f7528c00a0000401202811c0399600007029e032c005b4016100f664001828851a4d0186080981 0xedca510edcba530edcba510ed430edc4320ed4320ed20dc320edc9320d43d43d43ed43ed3ed3 0x13b18f31a6306502c0c61857f96f2dc5b49e13ab0d05de437662aa00d19982784b2002815009f8d193c23635c3082c5fe70c9e13a05942d7f9c32784e8163b4766ec540a804fc43c65061059001e9b5d502a013f2e75ca47c8d8e11af619cab6867ec057faa94fe9748d8d762cc558a2f65d4b946bb886ecdd593b155ca7648dca27fef65c0b7f696c517c2f6556638748d5738dd5953274fa9f13d9da3b263892919 0xa960953402a68254a00a940152412828050543ac61958c02b19ad4b2ca960152d56a4a354910a920151002a18054200a8201500028b0153e0ca2a014555effa45ff00a7e014f8029e8053c0ca280145032898051300a74014e56ac4805387bb8857484029b8053600a6a014b80295a8d1206b6e014b4029614520
def as55 := bankPage 0x8888888888888888 0xb8a9a89b988b7271655f5a59544f4c4544433e3629 0x84813c0409d121569902b44a19a240cd128c68906344a91a2448d12446a942346c11b2608e130468b023 21
def ac55 := actionPage 0x82a0a1fc54010108411450f405044c7b1888267413011a3b0c4111b50e80921bd61f8858c4e0c70d430e43eb628006c5fd86c1d501580202cf02f0da28ac01b134815860ec7400888a40842c6429006838e02a142a14003416501107111a009009460802470ac006840303c0a284800341b201202081e003c06700000000a001b000 0x45d72000070029d0009a283a0210221003405cd230016180283e41797a346c6007c6fbf2800c01d32df40a800228005102c42cf23d8d2005cb6130b4000341978180700490354304e6d0c800000179340c0032e01e85545e00001dc840a0055f100b00043000664b0320057240227d65e089a0003004a00ed70b02b22009a004001e9e01d1e02f575070377f00741000f15992613304000030206805627850f271006018f884d9125760030fb0f0603f01d039d0c80d0ca0007f060db0a930d00005d450815c0d028065dd3580a00067b808cb0b91003630e90060d0056f0000b1b03000300358cb2081a0be00aa18c0da9b81a6e07816cd017d801c04a34001c402276e0730bf80000692a1a800003801002069981300201c000281301cec28140001e131ce07814f0390052cd543165508007114a35c73c01580184a88a000c904c0010c0b0000050147ab018203c0798007c80004ca645269800096abc63ba3e5018b3481f24e20000000181d1d45980215400004030001d880178b038681206012058c0005763403ee32f489254501fa9880a96541e8a90b000027ac440009002b09000c1db80009800571a802d7d700a90016607107a200077050b00022004731bc529201a0201009f030056053f0000f00911808202d6b5000707001f01d2700140e91641954712000126fc3026001c450380008149238c3503e0d8207481541000e014171a0f300001cc06bdec075a0a0720a91dafdcdd2f87003cd04860800c00001240327004034ac0e0ef292001700040002c05da4c01409050c56fcb304400c9800f1819 0xedcba54321edcbaeb7310edcba75310edc6430edc76430edc98654310edc98654310edcb865310edcb85310edcb6510edcba530ed6210eda65210edcba6543210edcb6310 0x2f2d0b0140017198e0000040000100000400001000824008000020000080053084031861058001048cd1963280020a19404800ce21940481702c 0x2f57158ae20159402b109d5704aaa01555269389d272fa1a5943412868050d2ca160142cb2850050a06acc0959802b30456402ac8015901aaa0255400aa863430be861650c06a180943002860fd5398ada01581a2a70155f00aa20d70c02af8055e00aba0154002a70155c04aa00151c1ae10159800ab80156c02ad0054600a8a0556402a7ab5261da4ce36cc1ad98055900ab00155c02a6b7d0704a0e9d41002822c5f857bf0937e122fc09df812bf00355402aa805543da0c5f41812833fe047fbc0536d0a2cd0354b00aa69766856cd26d7017ae10f57402a9bfe046dc08536c81ad913d9a02b340153c0aa480508
def as56 := bankPage 0x8888888888888888 0xb8a99f9b988b84746a69655f5d594b454443403e362f2e2a29 0xc02109c01084d10a50a894285452142aa10a1511860a894605452302a2188651084e2884a31443118a3108c5308462c84231 25
def ac56 := actionPage 0x824115702e00f8bb40f08aac06004c54907644520a021029283a212709008913e61c8f9248a005097b0e0748646002048d06e373f1a0012230c351a1d0d408b1076190bcdca608607ab0c0585c39024037585e262733801c19102a100f9a000f0ab8128505d9000a841d024202246007011200205095c003002ec00000016400f000 0x76e3c82002e82a06cda2c65f0036588000a03600794064aa036e003dc010001d003e01c5625f8827800515d72d004c420070f334004101381d00218000000e1900ba110602025bb12505c00200a7079e257d65804213042058000001fc31c037e011500081060030030722053d0dc071e8100c550955d91d570005527a0040009d0c7002200c200dfbc30e020008139845b400a08e8a0700220535f501000500017087e068060071110000a00021000a5006f080232963155333a891af80100b000b00940f70a90090440109c0501d0a0a20b00ac00ed54008403cc160708b03703000adb215d800e00387914ec7400043c0036b20ba40430069308002d30285c064800e041d30028b08100780e9b9400882a000ca0758030033f4d8c02c99c2821139a9c78000c1d6013831a0e0058cd03b00f00b000011f404c04400111247803c074002a29350018059046701e09bf2c840065a00b405002230dc6df4040002b080500c3ec8c0a2a10099c007228d8a1d1f062e8ac0a501e01889f0a0a0000ee127cc0001203cc0f000e0e03e7996344c00003d701c00004130db31620d00a030830bdb0077ca06085900070078 0xedcba40edcba4d743d732dc732edca53db63dc732dc2edcb86420dcb6520edcb6510edcb6520edcb50edcba510edcba7650 0x1098954a025572a5d4a04b172aa93304b1091f01109f5280954fa9ed2ea5025802404000bcb25a3746c05c0b2f2de4b0f61000800b2b42a71ce29c338236328196184008009f93ec31861bc942a7dc6e8d91adf198d058004005e4a1742a35863 0x6b780d5e422ba0157400ae49156812ac0055806a78094a002940051d06ae6095cc02b98457102ae2015c41aab8255700aae0d49c12938052700ada015b002b595d4c00ad4015a402b38056873a2401448eab00655103ac40159802b0805562fa200944002e6835630ca9e87420328443df986bf3097e60efca4df948bf2277e44afc805a401aca0159402b23c56155ac20958402b097d0f2ca1e0943c0287a1d063fa0c7b41832832350343a062140c3281805a523ad60158c42a6b753823a708d414428280562
def as57 := bankPage 0x8888888888888888 0xb8b6a9a49b988b847f71655f5a5453504b45362e2a29 0x8220de808378020dc888a722216c8891b82286c88c1b22606c8a81b23206c9881b2a206cc881b62206e0881b 22
def ac57 := actionPage 0x82a9920d30009114c134bafc75044881e0825b741500363a8c402938a4c00f1bd81c92d9cf400a8cab0e08cbc590038602066405236002c2ad0301ba42680921346178cd048e00708fc0a4506cbb00543de03c202f4380301950190c929e80150a260c05078ae007046c0401228ba005818e016020a3d002a07700000000a801f000 0x47684f5000062b40b05cb9a1b200480050019531809920b1b81839508680a0a0013380107640000c88072718b494e450c48a02c0060000da620b3e1eb8007603e0cb9c0050094e38037003f0011f8001650152c8452070ac0027005032d3a80a000e091c86bd400434106d63c1192e0456005e406340004590000d1900000301100520008361c790093a7e4000805e6001a80a925d68000024a018037f01dc3a3000016100000180fc0ddd54a400695a0022ca6300e705d0800030022e00070d700271aa079b02798cac00192068000440e78280e4e23030880c8c2000155c8045981d06166da5a44441c048e5603cdf8c40300dd1047b4085000904ac05037b02404f0000d7732e4dfe401b30204e480405b81b57c00001000e52099254791328002a002009fb0008400b6057ad4834706660ead00ec4046cc1b000c0fb3202cd4e2f00000001a7c75a696ecbb40000192a6401d8a04a400981ee03479a9860a3004d80056492005408001562001255312b8988b0060e9c15b030d6bbe2881400038a02000058191a40007d200451c03cde78006000138198c415e0277c3b4400009480002f48ce8bf0400bd00d1070302300080cd040631bb100d678d0398a18040240528000f8373099805bd608bc085a00000003481c0b8306469034353a92fe69ac18064070380c0301404d000034000df41dfe50000868cb263805582c323ba032402b03ec080c00240a6802000205fc6e02409a5f602cce437f200284a8000c83c003d006c0603596093c030000f0036037da122cfd1800cd741bd00a16dc010d37d33814da00e 0xedca5421edca0edcba84210dc3edcb543210edcb85310edcba6543210edcb654320edcb310edcb6543210edcb540edcba54310dcba530edcba54320edcba65430edcba54321 0x4007feca94027f4fc9f4ec92c654a013fa7e4fa4b09535c50161a003ff702d71952804fc9f6f2cfb800ffd098eb0c29f90b213422005d9bb276284d088007feecdd93b176084c650610009f509a1105cffdd8bb075eeb99d2132903d4308009f7001ffb3a50085831861800ffd09a113180b00027e4fa84d08863800ffd9d27e4fa9f1099d505c0b0003b176084d0899205800200213 0x182a51454a00a62c1480a2902ed7675ad2a75a5eaa0095404ea6e014dc0298005784eaee015dd42b42756802ad0015a1429b2753602a6c014d802978057781b7c0d6f802ba8057400a38df450428a0057363baa516689ecd1459227b240d5c196a80651502ade017400ab70054f56a4c01498028c835bd00b4c1168c0ad18057200ae201494128c0051873a0edf41db2e10057000a980148442898056f00b9e015b802a68054a00a4601480028ba75046dc080d6d00ab836d6c0aa82015bc12b70056e04ab20156402a48252900a520149002910051e
def as58 := bankPage 0x8888888888888888 0xc5b8a99b8b7371706a6966655a5854534b464544433e37362e2c2a29281b 0x28192504a0449412c102504a0341412a092104a42884139082104a0341012810c288a180c222890c088a04085c481028b18040a2c401028b2a04282c 30
def ac58 := actionPage 0x8219bd14e40048c5c0e8c086f20058586068524171012427f032221f38c09211d6178f4f0e4006884b0b06e726304303dd85232372902161cd013159a1cc0a00aa609088c1280c604c20443e5a33002023d0201b2a21801010cc0f0b9012800e07180604458d400782a3024161e6702400f20040a030e0034016c00000028c087000 0xd2780074010068c00114042018e79410002d0000d002c5010009897e080402b0ce8880001f30002c5f8260000d92d006002ada92288023205c080df5380cb80007440300405c00001800505bd5086480b1c4300038acc6689b0002a500001a0b1000c580e93040de81a4000001b00813c004c44c69100000800b0ce5000d0a01070c00000f07727a0b9060f00d092010070250a7720022050f06c000662a0a307505077200a002f576011020226c00477440022004028004007c0025e002d0460002a2c093c0507c00b801da9497301a3015d63cb6c5c077e0038080a02e680074000534007fc01d0ed03034682649058899397b6e9040d0000a0d680017f2050b21bf8701ae0408e1028cc540307fd9883ea4d00700a700cb9300c0090a3cd089640f2000d67b0b81b0005917a5683203001a0b50fa014c000063101c058005156130398e0940d0000004f4c50010a00b5513080f5756a2000000100e0f562406940c55f358816e0787088000e952202000f15c86a40f02d6010c0000000027a60240bedeac38c0aca9e823cbb568030088700e38009356c7020c 0xdcdcdbedceceb6e3edcedc4eb4ec2edcb875310edca754321edca740edcba8743210c42 0x2c355ca76931258ce197796f2586b094526bcc783ce59a129b49a930898cea1742a4c49692b25249c5985afb14e20a3c433af2de4b2d656ca593b23572a9d27a4b35c89876a7b4ee92d24498924fe593a7b4f29da0a4135ae9ed3b422842f2de4bb56eeca593b23618d910a17c1b0298520a00ed0901f03c9782783b074a010aa13004dd9953155d49fc96376654c557527f258baa7dc207b8f65c0b2a33063896127 0xab7b51af68058556a76ab4ed1e9da353b02a1c0162c32c38058700b08ab4611a8c01d0d1ca0e2141c02c51658700b0c8d468028881d0a02a120142402c48050802a0a0162076930150480bd0536d0aed92f6135dc26937ad22f5a3deb46bd63f7ac7af58edeb1cbd6277ac4af588deb10bd60561402c281d8402b080361002c20150200a04015f002bd8057a00af2f7700aea615d2175ad8eb5a84aa08156b00ad6c552986a50053902a70014e176bb00532
def as59 := bankPage 0x8888888888888888 0xa99a988b887f737170655f5a585753504b4541362e2b2a1b 0x94808b901a0b904253981053e0105390a05390c053924053d04053948053901313901613901a13941213912035911055 24
def ac59 := actionPage 0x411a04d4620c38a4c084e464f300404ae038642e720124212c1a301590c08b0f860c1689cc8045074b05cac4644022436d82c4f1e3a8122182c15230d25010e0ac6088f85d0600804a303c7228530c2c20e0182f1052011c0d10090e86c8c00e04d80383c29c6008017b00c0e0e830038069004040419801201ec00000011008a000 0x120308b6014cd480d0173864e648000100008e142010084d000781b88a0000028a98144c81201d30008d103ed0386018b6e39c008081bfae1606ff328160024008246354414001ee07110106117600077f5077202004001005105ce06205476307007a3e001d10210277c05040340600097020223e0006990a010f2028000001931f930940500044060afb0208013090709360f20000064000880e08a01c083e03f56536805000ff06a0b60c7e070fe052c04108008a20c98b810b100d0047409010540141007071590060041031000a001cb600258300401fe5350064e1020014848da7020007801c007552ffba2c00a82c050126000b500253dd6fa90215a3c6d38006d0112784e65000010008840220080b0d4007019882400002a190126c89c03f600227308004010032000c03b486f05e0e705570000a0309070208000f8101001000b63c07e27f00661292020060 0xdedcdc93ed3ed93ed93ed963db93d93ed3ec97e74ed7e74e62ec62 0xb594ed7bde5b8f65acad91ad3582add50a4f4960637c2241a6f2d84800ffdb4b02602c014da8049c930890cdab74ec668cab9af5d09a1141444abcd3ca76be1ffaf7426845051e119b259ffaf742a84d08a0a3c2335ffb6542a84d08a0a3c244abcd3fa794ed7bdcdb8f31d80b005fe8e4fe9fc225796e3daab5165acad91ad3582add50a4f495b6aa0358540895e5b8f65acad91ad3582add27a4b031c51120ed71ea9d3fa7b4f29db005fd4ee9202ea774901702c 0x2a58054a802950059346a8c054a0028e0851400a4c0548db2e28052106a420547c0a8e8059246a8a0148442898058802a4001639a2b38051c00ba40546c028d8151a00a340174402c48051902a2e01630028a81513
def as60 := bankPage 0x8888888888888888 0xb8b6a99b988b89887f7e73716965625f5a53504c4b454341362e2d2b2a291b 0x240284864881090c98021219c004243241104878002090cd010121924802432400b0864901210e00060669202024d8000866a48500894901121292804425 31
def ac60 := actionPage 0x6129652c6c04509eb08cac8e3402284b9842524322001423ec1f261f19400b10e60f128e04c04488040688c5e49006833e02c4026348020162c141f1089408b0a06090e474a8045048b040683453002820981c2e153280140e700a1207a9808f05680406c252c085820b01c260a8410380b20040501720022018800000014410a000 0x390800000280ac00b01e171010fa096826006001607b004062e5e060c70907706036005902300006013200f36100c08c80a7d0c039a007a4207f0b30c90b050580b0600200d00e061037085c00743800010091b120001a0000e00114a000005000468c0023908381c0101a0085cc3200f000a32a1a9514af4dc865040b03007a9402002d74b4037140060001ae9646a00020006fd07979a713100000015505054016000006016040a0104654694504f5000bf06a30310360e4045d0000a09700d9000944c509acf37c12800a393000cc080b9306780d9ba10301d003c090001011ac075c06805dfac183b20bd8c79062c09800366688090150498c0901c89034ed02980200600026f384043080b030700755700e2d60400820009bc26707e9806f4b03805270070007429d20780006826a00272480196b4011ae80cb8af9fdea02860442420113813b60512c 0x98751032108510eda51ecb632edcba6210edcba5310edcb6c310cb6ed420dc9320ed9430edb3edc3d 0xa48004005240020029dd24002002e6a9b42218c30801a77492bcd6dab74914da110c618417001a77492e6a0e02c0040053ca4d49000800a854fa9e52427e4f2c2401800a04890d019a18c1802eaf356de931a632c618b9991f525a133ff62c84d089e119b796c24007fedf191b21554a013fa5f4bc44866d5cab74ec668ca 0x168802a90055102a9c0153c0aa68458c00a980d53122a622d4c12a981d531b2e10059a00a980944c02c48154a00b300152002a38154500b180150402cb2ad4846a90054f5a2bd8854102a6601655ceb3a8d6702a602145876c40152d
def as61 := bankPage 0x8888888888888888 0xb8b7b5a9a88b655f5d5a5954504c4544433e362e2a291b 0x904a2f00945e1808bc9011734482f01852e18099c901338602a724054c580c98b03131612262c444e25089e0a113 23
def ac61 := actionPage 0x61f8e5e5040038e4c0d862e089025867e0622c662d01302e502914af0e001614861308d70c408309fa09444ac1600204da03c1d4c2d01362070130ca291c01a0d2808058e87600a85530342666370450231816112b14001c0eec0907900ac01005f6030306070048822b008102048004c0a1802040824001a028c00000012000d000 0x3042043a65093f71c0a0001029b687a11879c15003e806a5125814944eec0240f2413a6c0705b80030002d53b0001dcf613b001b9001f11c6190007d00008806b12800f822f9c807b80007800a15d8939be20b6c201043a9c00a000800000921c0015699808014a66812d019c0be807e8000348000000603ae179aa0210067b0c511bc2082e933c0b01d6c00072070a248bd3ca01c8170420e37468030040300800000680002e4b209e406944228c004806049800738c0c9c020000102900591a601e2324a0054c062800f615e01aaa7095004002e41500369a80600556287c0002ad7500f518005643c0fd800f008b06ab75d5400544d78858352006f9d518008074004b300060bbb9800011800041f05d2002f5c9812200001a6008019160001d2cb8233cdd568361009f091308180e090ab5107098e130b080000d04000000988ad1027107005490010b600b5a088a1bc9010223970b9f37590001c00060bc0c00ea00e0e10792c000005a39400ecac5d80600020041802210d0900d8b0900b3ccbd377804902312ec34800900500700356a095ac09e007c030661ac00001ba30e33200000cbc16309b000042a90427ba8405047b0fa1030090300c17850000428904279a840504790fa1032090300c1785 0xc0edcba6410edcba54321edcba41010db7643edcba54321edcba10edcba543210edcba10edc76430edc98654310edcb8510edcb6510edba6210edba6210 0x5cfb1b56d808a10c60b400dcfb1ced162ac442a3b431c018008550980142a84c00d5b81c4485086305b492f2d0b8dd1b000c988dd1b000ae400200172001000004000010008280080041404c00800ab74f293524ab74f293524 0x20edf0057506a7e096d5bed9805a300b280163802bb0057468ad20950002cd0059200ae08d570129f2edd800b26055d402baa455b46ab60d4f4129ec35e783b7d036f802b68056313ab2215652694a352913a52214a576eb9658b00b16af5c956b90955810ab0914a11a940952810a5001581eeafb455f5dbacd5579a2af0155e04aa40556c02a4015586fa28094500eaaaad2546a4a2149402a982d53
def as62 := bankPage 0x8888888888888888 0xb8a98b6e6a69655f5d5a514b454341362e2a2928211b1815131211 0x6209182f0062058a2440b5048816061444c086492050c9431049287402a10c606421c80c8431249086209210c0924c20132b0610c720 27
def ac62 := actionPage 0x60c9114c6c00407f206082a232101c3d982e3f4b1300101d4c161ea28980890dc40a0e5108208386a3048648671001c3258222c3d330012176c1015188b008d0a7607894b4a800404db038425244002023d81a1b2532011210300b0c0c0f408e0668038582c5a00d01ac0081a0c9506440558020901228010012c000000244006000 0xee70010000008682045080f131d0b3004057a0110617600506700004055172860300f00608b006905600bfd4fe6b34a061f0216080c100423788a00102040030070210d200a904000a070db24a4013000a10d300afd010109700406d0ad00629d02080626000013720009604030498625010010740010500050595000010f01c2080acc4c5347f0aeb01e6000b5038ce8000f1d57f939d600000681a018040789c0d950c0034b80671417930ecaac00de56059c1f0010000dc05a6c400000034005000c29401234a12ef250094338031501605980322200001222d41f00e0040405f000289600107606d40040ab4381900000ca8080088a1010e0a30a0cb48014a0000400a4f80aacbb6 0xe73210b2e76432eb743276edc621edc987653210d631c621c621edc9876543210edc9876543210ed531db721c 0x4441782d1360b81689b05a26c16d3f8db11e2352689511e1cc3886d0d294d26a2f0ec018010060067c3e41142200acfa872004004fa8728300a80100000c00800006006ecdd1ba1736d9d7602e00c00d2570e94c4b58694b1e9c232a3324b4958f9 0x2d8005af00b5c016b41ac18258304b040d60402d5815a800b58016ac02d5015a900aa4016a402d4005a702b440769402d281d9b00b360165c42d580595
def as63 := bankPage 0x8888888888888888 0xb8a99c9b8b8275747271706a655f5d5a5351454341362e2b2a28211b141110 0x4c084282901119052220320a504064168080c82905049052120340a484068158080d029210a406002029b4005052680180a4d000248ea00183154001922a 31
def ac63 := actionPage 0x40a928f48400406630507e72b400342e18243935320014152c10199899000b0986070b0b4e8004845302c485284003c1cd8121f262980140c8c060d1194c00c0526018488106045820a0081c3c4200280d50040c1912800c05c802048b0cc086027401018486804301030040818260620051002020712800e018c00000009c008000 0x630288042a1b83ff380000ca700a8d49000605200f4992b00d5db450c2f83358278068e200000b90030fba00009f201f00055060d080ab0d0e064850d30999cb099080abbf04000a0e60d50a85000d158cd017ed0006b190500119900a03000b981060904400065005644002a7e20332003d7c0040520c0029c10800f5f07005d60f6604024c70b0c40085f20810b358ed9a0004007118e2bc1f8c51832000310008301e16bc6f1e2c000705213020610e0e8200490f0b08700e80d2c045e089222c2da130381a803164980353000400a00065e570 0xeded73ed63edb3ed53d963e62eb2e52c7ed732ed3ed72eb7210eb642eb76432 0x2744ba896f16c34868c503de0bc06d0bfd4da804991f2311642c435c6b47c8c4590b10d71ad22a4346238a70c8d91a7fe9f93e213418828c79649149302502e0592292604a05c0b23e29b2784e83a0630c20ba5344c896979cf12f73a4bc96b9d25e4b6ce82fb380bece02f 0x2db805b602b681945402da8651400b681944c1ac921d470ca2a056c8028a805b300a2c0145002d90158c00a26016c402d8005ae
def as64 := bankPage 0x8888888888888888 0xc5b8a98b8280757369655a53514e454341362e2d2b2a10 0x4041ae81815ec1033a820676040ce80819cc1093a0129b4049a682834cca0299c805350492680924cc14499a8093 23
def ac64 := actionPage 0x8191ccc9ca0068ad40b8d25ca40034505858632b31800c2710282c9329409011a811940892804807e4060943a65006c32582e43173b001816e8171f8a9081060b060b0d4494608684e3048581e93003821d820250c3982140f0c0e0f8598408a0696058582126007829400c1e0675006c07d804050051811a0168000000140009000 0x1c25a800ce00e9a400865e0651430000002828550467b9590006c3824a074f11f01bb74ae48340d8012050dac50960001f060f97702057a200e6c01a002d4503c008800f4800b92a08938c00ad89481d21000b0680118062b0282011e0014c74800f600e0baee04286013551700b1018050600ff1c6000006a70717180000db81e01414b0e75009443a9001f8c0945f700005052e0202c6a15e6d0004000a0f42a1009d405400901e00a0b2f4930010500a0f70d00b020f8079936203a018802574804e09e080400bc0bc0f58e1f300d07c9003806b070360a0000a606409f3d0004420090d1778d3d007c869a00c00521030d0d8f277a20700c40690a3243c0003504e540103010800e2932b07030033130e1ab06b00003400b570f3700780600003c642d8418360d6c05020bbb804005b39f82000a6003836f00c0ec0060681c944c0d060004aec05840004220a99932001b00005be2a0aa0e03600e059a0f05f0100099360700b843910f64315602a080 0xed940ed90320d9320d920d9320dc9320edd43d43eb3ed43ed943e73 0x58890d18a0cbca58aa1141a8250268ccc93c25d21a313ca660b15621992e45c4b74868c468c9e06305d21a31401508a05401a327818c174868c4a0d40a803464f03182e7a8d7d62a84506a06002814fc714b206305d1fe2744c1f733e5d4868c513e2744c896ba5414a78c513e2744c896be974ac48f918e311642c435c6b4e88b913225bc469733e5d4868c513e2744c896a0274c4f89d1316228250161a43462828f15b42ff554a012f45c89d13225af7 0x5b943af80150c02dda1d7a00a881950002df0053f00b68016c80aa08053e5bbfeb777802df2459800a7a016f402de005b602b6a016d40ad9805b300a840550002a00053c00b78014e802dd005b80db62014e002dd8651600b74b5625fae2bf5c41fb188781802dc815b700b6e1f6c436d8815b100b62016e402e5805b8
def as65 := bankPage 0x8888888888888888 0xb8a9a3a0988b83807b716a6965625a4e45444341362e2910 0x45202745104784085bc0085b80085b440c1b46081b64081b88032b84092bc0092b44094b44884b45084b54084b44488b 24
def ac65 := actionPage 0x40e88d9466004884a07042c22400204018321e581c801e1d2c160ea786400f0d260886d185200d055b03c308036022827181a153b1a811411ac0b091b8d010907f60583cc06e044039b024184c3a023817980e091f1b811c092806040d05400804040281c582800401ba0100c201600240b180605090b821203d0000000164090000 0x6304e6c219800009260aba803e81ac410005000c47c000080e939605d6c0e07d090c0ef600f7f08080000c37a0905b01929093a6b0e08200d3010000c1f09080ee037c03080900d259e0d00b2e04200842300db5f07ca002000e16b180609c1042fab6b0e1da788006a079a0200705020330d4e2280104c5960007e00000041f333037c0050041060740309464060026f20c0000049f02000970677311951000d0051077800b0f075e0005113040d61fe4f03d37004000203260100902570001000320b30a009004270ad17a02d82844080b0209c544200b63b16c0002638c08230c430451a500006000e54c062736234e7104b0381600140068042480e101000581a7281a01a80070140003a7499601354a 0xcb7db63edc765430edc765430edc76543098751098520b320dcba310dcba543210dcba310c6430c643edc643edc5430edcb63210 0x21cc3812d0e04543a8730e21c4398710e000800870004004380020023144c87118a264388c51321c4388710e21c2774980b816001 0x2e2805c400b7e0157c2aa7015c106b44015780ae1005c202b800170002ae805c300aa40170802a80554e00a9d335b656b6cd5c18db82017040adf805c000b7e0d66996a800515
def as66 := bankPage 0x8888888888888888 0xb8a98b8280746a6966655d5a5853514e444342413e362e2c2a292825211e1c1b10 0x601c0801b00902415804109130022849160101450c0c049106018188830480c441804015c0c8200960601050b031080858180605240c120292061101490302812481 33
def ac66 := actionPage 0x80b8f911e600885fa054748641041c2dd028374218830a1628141a1e8d40080a84090bcf0a20038502044567442001c26102228361a011011e8111219110088086608080a0940468393034364854002c185818171c2400140a4c08088b19808c040603834448a0448193014121646022c08580404062a811801ec00000011800a000 0x15e003c6035c0820180d82100718003d480266050ec268000d39a763e6c8800134a061f0216080c100a0440c944304f02d28020400676f0405d4320b138a00416d0401c5188f41c0013ca26083130cb4424fc0d9d0064028eb000c06000c2a3375ddf005e3d010d2a5380d040f07007d1d0a6a80802b9000ff080540002630e3ddc5736009d006781c000030a0c02000de00f0d1f034b980cd98d55b86000e0205423070e000020055c6c0241000d008023080ccf690807020057781963108b200b04de60f126800313bf0790098005c07308e007c4070a000f1c54b004404 0xedc77db7212ebed43ed72dcba873210edc7edcb7430edcb43edb43edb732edb72dcb763 0x5e5bc965ecad94b2764ac8d4aa614a29341338419a9a47e89d1328ec4e8730ee1c897a7549a92523a2f2a2260ab01f2a01f03c9532a01f03c89d0e57728197513a2643979518a2744c58b18a2844e8990e562c3a8702584ac398702584ac4e89912c9712c8990e61c08a 0x358604b0c0d64412c7815c90bb36015f402bd8057900b74016dd86a50858c00b98016e1ced886db100ada0171402b639db100b62015ac02e20056a
def as67 := bankPage 0x8888888888888888 0xb8aba9928e8b7b65625d5c5b5a55514e45444342413e362e2b2a29281b161510 0x81000a232500212528201119a1008269440821292808212982402129a100862980880a2944080a2928080a2930080a2980094229a1000ac9800c214924120249 32
def ac67 := actionPage 0x811110745a00d04730787c366200301f083a3b1b1800080f2c1a1a8d18408607040c0c468800c283520585a3440061419102c2b1612000e0b8c101289190008050607084308c044821202c381850001c0e9010170c28000e064805090614000702a602040144e0c480e300c120871041405180404012980100108000000104107000 0x1400081f0001d6b84a02464780000192d07c0659ca001d280824b3a3a06800000402a7c003000d02c0c22947402858a10557b444408060060002333000500a0007c01f6c059040c0c080f5b01107c000a1010c944300a1010c9443092a04023806ce00d50403c4f00079080004183e000d9120a0037c37a000439006400874bcd182100a070874bcd182100a070a02dfc60a040400020290189050d018e5800f1800df00381500600702402600a4046f7053606470700034a061f0216080c1 0xedc9876543210730db73d210987510edc74300e737 0x21e43989d1321d439870252cf4a989d61a4cc6e0cc0c00152689d0e61c52689d0e61c52687361a4cc6e0cc0b800d26a490e61c526a4913a1cc38a4d492274398714fa93524a2f4021cc38b0d21e311a527e1981855d8cb18e3144ca7f17e2744c 0x15aa00b540169c02e6005cb7db8e0171c02e50359604b2c01659f6e4015c600b900571922c9a359343b262564c42c98659300b860168812d0805a106b320967802cf0359905b3e016701acb805c100b2c216301ac80258f
def as68 := bankPage 0x8888888888888888 0xb8b6a9a78b6a6966655d5a5345413e362e2a2928211b1511100f0e0c0a09 0x38892005a22480188892006822480180892004a0c510228292410a0cc10828292442021466080c511821214460830492820a128a08885228282148a0 30
def ac68 := actionPage 0x81d8f9c4b80488ccc0e076cc3b00445e60643a5a0e003c28102c1ca786c01c10b8118e51414009873b074668463004033e02e2c3c3b012215f011119d24819108f606078d4aa00803bb02c345a4802241a581416262381120b6c08091011808a04c60383074c6003820b0140e305502280ca004020b2e801e02ac0000000ac00e000 0x7e8003dc004280a0c170055603c0c6f4e8991e003e4040000ab960bf98500c1239a006d8000001000613bd49224da6a80d70096001c5734a006fe5081ad04c2e01a014c20000c31000d02d40b80070086c100a0e01002000003de04812a480876ac223801c4d18c00fd219024034a02194003d0231100cac6c0029813b96900aad600a0000a018000300082980d7b400695c074080715227200d40001100815a840580000240321c200040b03c000d4cd8ef0000003a818406001d04ac0d03d25701e02201300c6d3c7c9114a00201101c0e400a000af539040039e0bfd25e000e1794dd440240f0cf0003600358c001cc03cc46a8cf128c03c0920180020000000077145ae28a8008a001e1059360b906f3ba03f07c048d600d3bf00fc7a4c006bc645800080e00006080400c0848018b00b90600f85b810507dc00838970002f1b01084602f0c80008383066f7200f0307600740707708266002c090b200d901780019871b90a4bebb0ff0500694e0000701418609060600425aa0c07001c0000db48c5e898300b7174afe4020000003400b7825934066ffe0300070740e7b803f3bcc0b0108d0a9920503ee58d08d00bbd20044b0a07d08 0xedba76543210edcba765430edcba7654321edcba765430edcba76543ec7ec7643eced632edb73210edb6432edb742e61dc621edc9876543210edc98765210 0x25c4b0950020004b0950002584b540a7f4f69e3026014fe9ed26a48524a4031b715faab554aa75029eced98f4fe935240060068289d0660be8209c0600b68209c0600b654ca889c2b00800e89d0e4f988c1150f21dc398700061c801 0x983c02ea035bf04a9c057582ae1855ab06bb40975402ea8355d04ab8015701af5045d802bb00d69c12ad8055b06bb20976402ec845d702bae0175c1aad0255a00ab40574c02e98158d00b1a0560002c0005d100ba00573c02d00059d00afe0573802e701d7e02afc035f802bf005cd06b4a0167c02ce0057d00b60016b802d7805ad35b58016b032d5015c302b56016a4fad8005a8
def as69 := bankPage 0x8888888888888888 0xb8a9a4a2988b847f7b655f5a53504c4b4544362e2909 0x54409d1114744491d1504746411d910474440ed110ab4444ae1142b4460ad1302b4540ad1902b4c40ad9102b 22
def ac69 := actionPage 0x61190df06a0440c2b0887cf05402245dd842347551831a2c6c2017b914c08915560f0a1bce60460a1b07042d873022c4c98361e661b001a23cc1a0dae8e408d10a80c05d449804907440542a8a2c0450309826123a1d821e157010071713000f08e806028889800903640200e303a005411200a040c1e01220490000000130013000 0x8700642602f0075a090f7320306c000083080b527150d09e92302a0d93db0000a8304960b1006ba20ed292d1008029600a0003105fc025011c50d0000d0d6071042102a076b47a506f0800c8f000700004a300aa401bd0b6a2f0900f1004c0970e3e080a50100f8a210512c090200bd4f01010909b60be1035006000b0e0070d80b13000a2b5f1f05b80400009034c0019a2001441000700002d802e502c60288653c040b000496ca03000b682200008003e00010209d00e008832d722188cd029dba104080522b1400605408b40004d0e77a1700909000a40e1004a1020558980009d2fcd90006000003ad5053c6c6cf3fdb0004c80c800052240880327e1c1b01de006634001bc002a804435abc3c0ee80f20000c0381ae3800e591a000c04a4282341e035a613401120a0400600800b0010bc800c02000481405a92602d4301000028090200f420cd2094b7280038c8048409dc04018010381e20c47879c003b60903607d020264a30041000000931a12800f400380089c054a80e28c00ee8073b42303801d380a039e0438002b307 0xda543d730d73d73d73d73cb7430cb9854310edcb76543210edba76543210edcb7654320edcb76543210edcb76543210edcb765430edcba7654310edcba7654320 0x1c032912ae00718bf12c256c33fc758e9dc03295009f4900e370438c4b095126e09300e312e2584a89369a9f89009712c2544989612a0044b095003000d789612a2580009612a0004b89612a0004b89612a0004b89612a2584a80012e2584a800 0x93b7e0177802ee815db00bb80159c02ed835c400bb40176402ec0054800ba80d57c12af835d600aa4018441aea0055100c220575412a80054700c220175c12a30054600bac1570422d10060f00baa0d7081ae000545
def as70 := bankPage 0x8888888888888888 0xb8a98b87858482696557534b464543362e292809 0xa098bc098b8098b6508b60b0b6890b6099360c93a086dc086d8086da094dc094d8094d6284d7084d 20
def ac70 := actionPage 0x81512565660070b2c0987eaca3023852a038395132803223681b19289c000811260d09d39660060802064449a5100203dd8301b493a03121d2c170aa318c00c0d760a848f074047061304c1e6a3702382b601e0e270f00340f900c050e92800f05f604818588e00782440080a101e006805d002030412011201880000000d000a000 0x2dcb6802a0298e018002015e4040003406634ac414a90041000c00252c0180148000280212f40800d480140660004608422805c000878144d00001b34970c000140073825380c2113a5295c101380380c50098b12279109e60a10c0100d8801c000044f0d86f400020879bad090d08c008b02c0603d0190c04def650d082f0e040d03460e891a0ce0018e5c0600d20eb6c0dba507407666005207440738040e0200780002200070081000096e07f00200b908d080034c2dd91da403000814510be0053605a00403b400b03240a02a0b003001300038799615a76340f0010031708001a0800ab2192f0012070c40e8000634001954783c8362861020837816074c0a00f3900203849380033b90840008a880000c02510e20294b68004001ec0919008c70d005b8d0d0202d12000f4ac86070b0020031320230056240d025cd00574500003161e02dad0340031bad5819c71880e24005a80118024f006302921609b738000448000140c20ff0010a058de780018c290a0a334051280c83c8 0xe74e74ec743c933e740e74edca754321edca740edcba876543210edca754321edca740edcba876543210ed43ed43 0x6f6c81401b3222330360560a61481db7b640a00888cc0d8154298520765707f8810ac15429b0030e4507f0b716c2d6c33fb74ee99bdb20554a012f11119839c668cc17c2f5401b3222330298510a06aca69111982704db2912c2559489612a25994a8012c25594a8012c2544b32912ad3594895 0x18de806bd00d5ec02f3a45af12b5e756b002f3165e400bc85d78cb2f1815e300bc6015f00abd0057a00bca0179002f1805e200bc3276fc0ab6a45ae12b560578002f00156c00ad80d78002ed8356a02bbc916b44ad5015df00bbe017740aee005dc02ad2015a402f0005df
def as71 := bankPage 0x8888888888888888 0xc5b8a98b8169655c5a504b464542362e2928261b151109 0x620a4684148cc82a2a0455962315281c325032a4a90549620a926415450c350a306a16619428c3284f0250d918a1 23
def ac71 := actionPage 0x60c915cc6e0068a0c05488c81f0068441828415a1d02181fd0121f268f40100e04090dd34e004206db040609274002c32a01a2b3d2e012614d00a14190ec0940808038949c76008830401846322e023811580c20131b030e074c050e0611c10902c4028503100002013c0081408a80030041002060320800e010c00000018c005000 0x3000510000003261107007b4d67b171190487000001d81d35811d84600341cab04c4968202410005055a80000cc0001c00019c78c0382416dd8ef4118e08106602206180d0000dfadde00211049050907604e6e6342040b4ec000064000b0400a689e051361480204814261da0080005a8810180c0000189ad00486a63e005e300b0009050e9000508a74119fa405a83b01c3a0000088054fab1efe56c754000022ad026004400f21e0d479171c0000008a28000481a600d00a9801010053ec00000cbf00004008068c81565c0049add9122107af01400070a600eb035c3640080c540581ad8580d001e02360b6b00d000cb6ae0001c0001a0024077804b000c2003606956c489ac41107230601a5a00660610020020565e600170fb5095204e370000050308706020142ff0dc301880c20227b86a8000040bc00ba9400690b01808004a05aad06003b1983a90805406380c600f7 0xedca870edcba9876543210c987654310edcb987654310d730edcba7654310edba7654321edba7654310edcb9876543210edcb43edcb943edcb9843b432 0x1982741689d12e25801dd0a5225ec337d6404506606d07d742df3a97043044b896ba0b144b8960f625c4b00112e2580089712c37c6f0aa1be3785c8aa7ceda5901832223305b86e7ceda5902c4306444790b91021b8668cc1542a5bdb202223303603b 0x1d6c00ad8075ad0cb5a056b402d6805ea00bd27f6c002ef025ac00bb0096a802cc005d604b520d57822f4835a804b50017a402f4005e52cbc60978c02f4005e7
def as72 := bankPage 0x8888888888888888 0xc7c5b8a08b8281806f6e6965605f4e4544434241362e29282014111009 0x21202519108228c8060646412032324101619009230c844118660208c320109a1b0080ab6804055a40220b52060152900a0c94814064a5022125 29
def ac72 := actionPage 0x4050d178e2043059202862b633001c2a98122e551b001013cc0815a78d82080926038a1246c004043301c4a803902201e980a213a2300140d6c040e9a11800805f60186cb44e086825a00c305433060c11d806122632010a07ec03080e8a400703440182870c2002817300c0e2838001c08d804030b24801202ac0000000ec00e000 0x212301c00191c76601145b2060428270066010020e2560c0351003f410cd7c4407d0066009070c4058371810230bd00c2020a000394030600275b0020901b208440e0081600d090400548256000947f2085763090c060060ff400f0004c1f5c7a9046020b0080a9b04c800f780a3016840c000200f80a090e70c0102400608389c02042d960f5c0b00005a00b000bff99060f812a50c000453056006e0f70083b6b03ed95c464063fd00a00e4f0ba0a00f00960ec300000b0f 0xdec3ec8632ecb832edc743edcb74310edcb43edca43cba7432432a432edcb98210dedcb7420edcb97420edca8753210 0x12aa5444f89c724c40ba95059474cdd2ca58e6e9652c70e1e4b4f8750e20c43d8750e20d43d8750e1a7c3a8705c0b292f39c718cd1702ca4bccd1702e05b89f13d2762e4e213e2767109f13b0863304e82d 0x32d7065ad00bc00184802e28161200bb4016bc3ad7015ae
def as73 := bankPage 0x8888888888888888 0xbeb8a9a5a49b9a8b8a8481746f696557534541362e2a292815100908 0x6002cc14002cc121824c143024c131024c1c1024c162024c1e0024c121038c121428c129028c12112c812502c81400232e400c2964024296 28
def ac73 := actionPage 0x821220ada804a0bb40d104506300744fd8607a2641001c254c2e3811a8c08e1156151a08504046880b09cbc3ca302403a604855194a802618b021250aad00900a780d0e44e24008044c0445a22c200441a6016200f690020096c070b8724400e0366018343542006811300814043b0030041002050029020e0108000000140007000 0x2001f8000000000b25d501a7f26074d1816f99b70d76b00017af5e4b3851073e123d92180000068100ce5f80756c982049032734061c06a8000000e028410382e59836702000b0049d90122e8000dec0b82e63d80a00c1407420037aea23006004f10c70c040043007500006400f0d51c1800073d0008050e2762a8806fdd06001e6555000160000c0049401d0e0e41db2600090740d15600d0f4a06306f7700000f0220077355c00b0445444d3806700f05d007200f61e60000163ed40801ee5960fc1c0170000b30030000c02b61000662748009cfdf016c19aa502000000002800380dc456980785eb7904b03d60b0002c85a007ca00298a882c09d800a7e4052e54028084800001900792940e4db048b900b6a61c003de04800077f00cdd1d39871e80df0000eb1c00316a05ac02c54016f4195001770000634e0b8012f3d4b00011059e0d96b35000c744d2970977ca100442d80053d8000f2c13c200020a4507b82c706ef2060532e0000c01805d0edc36ad15b500000140407000993037c61d194d0f9bd0f000a0a2c58038580aa042160c20c20c80ea603 0xdc93dc3d3d53d3da3ed953da9374e774ccc9876543210b3 0x587732da581300542a094027f4fa94c890cd7d6d7962283504a01662a31d23a0670cd19832943a7e43685509a113d4764c7912510a1c929152264488890f8d8a1d3f27d43685509a1131e44943a7e4fa86d0a21342263c8946c50e9f93ea1b42a85109a1131e44af2de4b0f61ac2475818e55c5341674ce54fa694a244866b9872ace592b02600bf95929f4787fc8ad14820e29bf3696ced01813004d2945030e850e9792ea5c4a894d28a503feaa954aa8546a8950a9f53c94d0343c87225e6ec7e2ca58c75ca889c594758e9 0x14eff29ddc12b66bb68d5ec70253700a60014a00307005f902bf0017e002fa815f400be8057b002f62757706a6c094d802978052700bf0094b802970052506a74014904ed88052d00a46514101a9c8053400a449181922f08051f53bba014cc028e8060d00beae14d4129aa7d2a00a540146c0305005f400be0017b402f58053b04a56014613a890060c7bb740d6e81adc3051700a2e017b002f58051200a0ef76e9c6dd1450500a0a017a832d7805e8
def as74 := bankPage 0x8888888888888888 0xb8a9a6a4a38b84837f655453504c4544412e2b2a2908 0x80434e11193c0464e0119384624f0189380624d150934c424d91093444c4d1311346444d511138042f611495 22
def ac74 := actionPage 0x61a935845000d0c140c494ac3b044059185c484c15022029902923208ac01911d812108dc9400887eb0807e5c39004438e0323d2514803016cc171c9011400a0a760a8d4708808484cb04c602e5502202358222c122280140fcc0f140790c00a06f60608830c604682db024381263022c12a00c0e0373012604d000000038c094000 0xfdf960f9055d0f3e08e0b007400000a0beff0e3630810001a097078c21f0ce0f00f00ab5696e020036a500d401c0c101ab18d0028080000e81003f5946040880615116ac08000760830a04e0ccd010b0600678005dc8a04c3f101b2a070006900223246aab8c9100154580c18001b9d001a094e820402c0b006620192778c5404c6042fa30002c7000008000035c40a200481d0141000bcb0311e502ac00ef80034000edc034890036a0496e00061010f31e000107fa6276605c3fc900e04a1271360090009e010002b44d000f43e3448820a6f1aa01d1302809ae3c000c82170000740001d1a2d5c01b01ca200620008481a05100c08a871a8ca10807700b040a000000070550305373870117240c0008567000a780500710475b0b51c070130606a00e880084104f0109d60000056048305006e4684e620305039056065d0690c088b60000e00006e3f00c7d2101f1037e7e000d0d0e06e0a9800c51a0400334e80000005b4003a140d2de60780390005e800002883085a04fc162812001c174a3e50580190000002c0010006bb3aa4801bef22da01e7399ed001367bfc903698079d4b25b62140c 0xedc65430edc98654310edc9865310edc98654310edcba85310edcba8310edcba831098520b320b8610cb310cb6cb6ca5edc430dc3 0x7c4f81f13e0220f80883e27c10d9f13e02210d9f01107c4f81f0114220021f01142200221b3e0228440043e0228440043e0228440044407c4f808a110011111f13e022844004b10b156229e508a0d41281500940d293f238366f2c007feda581300542a0d4027f4fa94c890cd 0xb020060402ad4015a802ae8360400bfa0d5b002ae015ff31b5a0156c0aff005fe06ad2095a402ad0356b00ab25153582919452353bbef56d44ada8055871bd8df7b01af6025ec06ad0095a002ab8060400aa0c153802a71454d00a9a017fc02a4015fd00a8e017f812b38054600bfa0d71402a2a1d7c00a86015081a9c0053100a52c145ca28294504
def as75 := bankPage 0x8888888888888888 0xb8a99b988b846a66655d5a57545346454442372e2c2a2928232208 0x48241469042256030544c140a8981819130506225380844a44910980811e301122c7120458c2408b1908116341022c6220648e040c91 27
def ac75 := actionPage 0x6171455d6400689ab0ac94ac7100204a505447521a0010240c2921a69140881146138fd208a045082b090748456002c3d184434403100141cac21151da9418e0d061009cc87200685e307c46544802302aa032192851011412f00b09101e001a066803828591400982130180c204600340b9806020824011e02ec0000000a008f000 0x2a00e01a9e896001d00c00d80dec0e995af0003d01100000b080909ca9b0f0f304dc01471b8220300b749000510a0304c06903987e781005703f010b07023d0030e142b07c000b004d36300088413e890000836d300b000600573f01666d701012cf017c080070f0000f062086067d509f0ebf4791600d03008d051f3b029020a2988500f3b800fc0023b00f00c00ccd0d0835030bb93a0028aa8462504e014d01c001136a2000f040604940e401eb501690000740bfb41b08000201e23f40a4040400020fbf41660ce06e3f880a00989400866066e0382c00a3c661cd4042318000116002008ce9103fa0f5c00078c008800883e60000a5801a9c81c029400267d38fd24410509d00f505a000a3c000321c0c0bdc0d20160600c0a0a1081010990007cb010a17001a620f60c00a9063f2b070e608b064e807000690704f011a690f0010f000b821f 0xecced73ed732edb63edc732c7edc74dcba87310dcba8310b0edcba830edcba85310dcba30edc65430edc76530 0xaad5569a532604c015b2a146080900d26a49481deacc4d8945ce8aa07ae79ce8aa07ab616b82003ee79ce8530a00f5ceae04821082083a7e4e74d99b224038c298520a214141a153e2a050c2133e33f1953005eeb114fa9e4a07c066cfc676b114fa9e50686200c007ca9410aa133e063d4fa8042a84cf91f13e0220f8088 0x15f300be20160003042fdfb00afe595b4b2b60057b2cad40181c02bd1656900c0e5959c03030057900ae6256f576ca2bd9400ae4a34dd3a9b8060b04c0a018141afc805f804be8017d1cef637dec06af0015c53ab428d364ea6ced81042d90057076ad4015bc1ab68055f60a9c2570cc6d70055e
def as76 := bankPage 0x8888888888888888 0xbeb8aaa9908d8b70655e5a53504c4a48453835312e2a291f1e1d1b08 0x18208a312220a3402c0a31220a23c0288c350908c323008c315008c313010c340380c312500c31300943123044313008c512208a912208b1 28
def ac76 := actionPage 0x6139f875000048723088f03a60022835583e71193a001618881d360c1440070bc60d18859440440583060b22892001c29582c511241011212ec1424882080890896091003d2204483dc0346616d40040175814280959001a092c0910831cc08903b6038541184006813b0141a04820224065806070130800e01cc0000001c4009000 0x300c4b3012b00a502070116a0bba683a0f661b204c03005197b080300052f332b440000d060d2ba0375050031c828d01a614404a438402000200e00770b9367004d00020006b9765adcd0590009a0a060040010207e05cd011bb009a0a060040010207e05cd011bb00aa0c02704c030205f043d004bf00680f6dc0805811b94077343d664145b000c618031816301cc57df00640002a00e01a9e896001d00c00d80dec0e995af00030f00f027035010305a06ba027af00c100e06baa3e6007800c001909e60d8a6d9000009a0a060040010207e05cd011bb00022608205001700530606000630a7920054420817162e0006 0xc3104a3c3e6e66ec97ecd64ece675 0x2bbd26a48ad54fa9e52a916acd26a48878f89f04407c8f89f011822802d59a48878f89f0ba171e3d4217b0d994521c32845ac339a6d4d0580aa34aa45866db5b595bab6d3f4b48710adb5b595bab6d3f4b48710adb5b5b6b2b756da7ea8d0e215ba172664b4464cc11813015468ed01a0222d55aaad3fa78c09802b55428c101201b6b6b2b6d3f5468710ad56aab4fe9e302600ad950a6d4d895529db4b5759eb35385468710ad26a49481deacc4a349a92522a40ef50f1f1 0xc120580012e3ab5a000b3a0d8041300835c604b8c0166402ff97daf00b300d7f012fe2ada300b280d4c802ca8059306bec016441afb0059002bec0163dcf03a360746bcaab63802c7015f200be2016340af7815ee00bdc057dc02c1afdfc00b04c97f01ae480581
def as77 := bankPage 0x8888888888888888 0xc7b8a98e8b8380746a686665625a534e454442413e342e2b2a29281b17100d0c08 0x28060211940841214a10088928500444942204224940812125006049128820248940114244a1082122700404e128021070940101b04a08809824a0420922600904a1 33
def ac77 := actionPage 0x815984d124048081c090b05c960250375042532e28000e1aac2026961880080c940f928a4660c3860a0788c504100182e98384222230012158c1a1f0e9140080a040c8f0604a00404bb05c742625042822182831104980100f90121305ad400e06180786021c6047822302c200c8200340c20080600530126018c000000180008000 0xc818d00120090406000a6a2656144b334600adc803d007800940062150c00174809801b2ada0698c0454006ec40023258f60002416702e4000037941df00000033975c191e581a30882c41760020030055520309603615051a00603707c770682ca895302001a80c08e0f02004c07e0a8d0679009640a00030002234e14060845a60089800b02fc871b205d000472543570565250440330070ad0000b04607400443c9200101003b40a031f366406c8019035201a2f60001b06c9b62700e39c00008490b0720ca8120033be80280b1020a9c0014a2001c00c87606918000000e060f614092039a0065d045620c069a08600003c20070ab3db00565e004400d64005b86f000a0001830516459f40c82417fd89081ca074200030b03218056014084 0xecec7543c7eb64987510a9820dc630edc63320dc930e82b2ecb763 0x2be551a814f55b2b55648d117a8a4d894928a502624b8498389b52aa5439e4832aa543a073ee79214aa950b626d4a873ca2a1d4383e27c21d4383e27c21c1f18707c64446453ea49289cf34a5c49fc7758aa7d42283502944e79c72e259ac44c89412263bc768cca7d289d43a05e8bc972510955292514a04c497038598af55aaa053ea78ce1391261aebbd26a48a7d4f295 0x58315b048060956c10018215ae8805d104b96018300300305fb00bf6c173c02e7835cc02b94c5718b2e3165c52cb88c572432e1805c300c080170802e0805c400b808779832de805bd43bc4016f10ef2065b90cb6c8778c32dd865b500b660182c13050060a00c060180802fd005a602c02097215ad08059e
def as78 := bankPage 0x8888888888888888 0xc7b8a9a4988b858481655a5753504c4b4645442e2a29281b0b0a0908 0xc040d2340c052342405234041923404492340509234140923504092340407434042543404454341405434840543504054324481852428119 28
def ac78 := actionPage 0x6181a991660440bbb0b8cabc5600285a18565f593280182acc2a2aaaa9000c144614131452808509ac0947c9ce3003846a042334b59801c1fec1f152424c18a0f060f09d046e00686e3074486e3a00343220321e2a36802a1410120c8f96c01807380785048ba009028c0241c0a6d00540a5806070239822201ec0000001c808a000 0x712009b10e020082e0050564099c750d916170e409f0209511000000210b00d70207975200060076260d00b38b500e000025040399cf10055202e99022e464900d0372fc0d070d49bd2a009480a00011015e0034096bc0a001203028d500c36700c40c062bc041854000000596000147382a03d000b9f800010447c0604005109c501a900357306cd046190f0d6267e10b050000109010e9c500090b054782cb31e8001f47c600071010000b750340b900cb1c0df50200ab5d799003b31d18dd0359e594c0034a500145001165817e6a7608640000020a032a7a4c078020044d99081222c1c01c60fb9a880b58632e063000900023b40d00000a8180800195b200b294c700fe7b4fde0800000a0eb2e03a04e0bf000009000003c4324220a8074001772a41200040f11b35c819fafad04f4402c0178000001947181332da0010e035005b8c89980b5001a5639205c804107800020e02d2b00dc30952a8080e0000244ad733f1ba0d680d008670007f010500c0d87440c000019878e290007530069600 0xa32ecb431ecb83e740e740e74e74e74dcba730dcba984310edcba87653210edcba876530edcba87654310edcba87654320ec7ec 0x3f27cee758118a31260cc09151a0271f90d019e330563f21d4390680cf198a0cae1151a0208408560aa15029bf273ad0d82302600454410817e4e7dce9ae2a65488a8d01042042b0550a814dfa3f273ac098018a22e20840845088fc9cfb9d3686cc750540a6144f909712c7c84b8966a6b154f09712c1ed5029e13025c4b3e44a07c04b8964a4940f809812e25a63b02600ad550a6d4a7716a8a6d4d89a517a2c 0x5e600bd05978012f1805e32cbbe01788b2ef235af00c0c5979002f08060700bca5978cb2ee18de82cbb60176802ec805ff00bbc017611ad6afe0f04bfc017f802ef825dc00bb80175c02eb0a5c34ab5cc183c1b02005fd06bc00176c02ea8060e00be6017c802f8805ee00ba6058340306805d2
def as79 := bankPage 0x8888888888888888 0xc5c2b8a9a49a8b848370655c5a504c46454342362e2a29281b15100908070605040300 0x602409182c240123048282242090130484121220908250441210449025201100814d0412204a2082411250105082302409104505012204a220241125080808229605010c48c0 35
def ac79 := actionPage 0x617154dd24003886b0b4926ac204243fd85643303281101e6c291e959940890e56128d8a4e4046868b08c604c63022430d83c2c2122801816281d14109000070a940d0947c6400504eb054403654004021602019163a801c0d500a09091d0012048603838408410581bb0081218540244075802070215011a012c0000001c8006000 0x900500002b831000f9a0070030c002140b1b0d570d019b30a62f0e009e74d000b06ac30a060050b3483023c000078125053e030006020c000317ba04c7d501745980e18257000408009b530010b05009d10e040a00843b0c099300d40b9005bc5fa08900da31362a600180a0fe4600319c018138923f0819ce9870e00e04180daa00a7060107d873040e3c007d84600022d400007184d00006681cd001001a9a468006038811b8a007981031cd00f5010720d05000091b52f023000008400003701801002053154608296b1260240f00015f3000484002003a02c0b8747208520000058600600a1c670a07702d9e3603255000b1e13057d507200a840b090a20000ba00c20b60020353baa08702a0d0000092f050d6c15 0xa1baa9820cb310b6ca5ed643737643ed5437543736543dc9876531032 0x1c1b52334454841031d82744bb866a06689792422e420818ea1702744bad95ae8784588902cb656ba201162240cad95ae8884688b1120696cad744422c4481aa7f4f69e215b412b254c518750e04a53fa4d4904b896512a010ea154267aced28b4a49404b8961260e227c3a8702529fd26a4800c009f412ef9dceb0231460c6809c 0x3099660400c08597fc02ff97e0704c0e597f802ff165fd00bfa0584002c88059000b1e0160c02e5006127db900172003088160f00b420167802c10061000bee097d802fb005ef06c24c183c03078060160bf8017f00b09005c900b8c0d83c13078059902b020160402f5005e7
def as80 := bankPage 0x7777777777777788 0xc6c2beb8b5a99b9a8b847a787471655a58545350453e362e28090800 0x4c22e014822e010822e010022e011820e030820e00482a6004862a0048a2a004a22a006822a005824a004922c00482a40c00111f180211f 28
def ac80 := actionPage 0x62a9e0888604309fb138ea403202204ce088691e610224223030330e0c80160e7617970654608606ac09caa2e7200382e984a4a1459801c14ac2421891c81090976110f040e40c5843307c661e9104301d183a2b0d4100140cac1b12051cc00905780905421e400701e40001c0a73006003d800060241800c00c8000000188085000 0x807200950003090663000842300500906ab56012061ad003200016948132059e002220467b65b419225bf0000ba1bccf0000b06e04601101eeb00800000006a80c74002001c60d807a9781c812003e00d0840319ec8795208600b813b480548801890d0b90aa00860dcb30008100eb2902550a03606f03c290108307b0001879805e8140ac640ba7d1e4320001baeb803083c00b90d0b2a600b7aa1800b0aba0025d05008f0006f01850509020d005f1400073740008c0a8562706037000c025460801700550bcb3700cc6d03c0e6802a0091f0074f0146b0610000029006000fd80160573050001c0e40910101726400002607b75000068d8000b03263c81f85ce938c0040c1e04ffbd34001033201855000e000150001f104b405c8e004cee85d00000bc3237e0481a019b77c4c9015ca8644000e453c00100c73720f0103230061f00034081a8 0xedcdcdcdcda3daedcececcecea5ededcca110 0xb02cf157249b0aa60885e3bc1636c6586a2731a0ea9849244065dd8b7561af15098d91a93aa093d2760c69108d91ae35275412634885e3bc5616c25829ab314880cb0e61253aa4a492920fc8490589d5252494907e42482c4ea92924a483f21242382e058bf97e29a530925020730c30cd3da7a41682904800bbb602bfd129ad351f2be26e6cf18e90e1e230c32de3bc575edcd84b0760a14b836a478c8a8ec13a25dc1b5222a3b04e897 0xc5c01874330d2be8348d06b19355f26a4e4d48c9a018617b33ac63d49c7a3f89c4f138662000c4019878030f0061700cee018c03b178662f02c5e018bc0b170062e00c5a198a80315076260cc4c0589803130761f0cc3e0587c030f8061600c36938f813160062c04c56018acbf0f1661e00c38018a8030d0162500c4e0188c03130e61400c280189403121464200c44019b807100062000c3e5f874030e8061543c28218517b44aee8949cfe919fc7f3f8f67f13cfe259fd0f0c8661900c3201860070b8061700c2c87850330a00614
def as81 := bankPage 0x7777777777777777 0xbeb8a9a49b9a8b847f7a7473716e65585753504b45413e362e2b2a 0x6402092880412780082491013092202c1244068248a09049181209320241244480a8882825111104a2a020944444a108848ac1121258 27
def ac81 := actionPage 0x60e170bcea0470653060ac566400502b18304d274a0016136c1723119d008908d80a8e481a610583c304c5c3ab30034191822271a3981120acc0d0f8c20808b045605054554604501b20242424330a1c0b9010100e12010e04c807070509000801d40302c186800380aa0140c0a510220031004040211810a00c8000000108005000 0x11500680f9b080f20a04020b002210219009022930c701b4060340008c27f30eb4020707002076d010c0072701060680300f0d0085885040630b80c00f0d6d0430d1ba0500900a70010cf57b120817550c60070034709f80000170040060d6cb28a0c01813941005500001116a09a00075e902ae7600011808500a00105001060380230052266430190af73903262207e30000210ca05350d7900307913008002ff07443a040aee60b67400450010dc3804f4000501983583084211d730180e068070036443f6902fc089440c0d528c4218e40098943e006200012960440c0 0xed953ed53da93ec97e74ed7e74e7e74eb2ec62ecb2ec52cedbdc 0x9f109211420824c610f672b093e21342484635a7c42684908a1041263087cc6670bfd7f2fd3f443ef1d856d8c258429e4d0940d514e29843c655e3b0b60a3a40b712ce0878ca0e61259c336600bf97e1f9222ce19b3005fcbf11d1f922344e07b896cec017f263490810732754920b13a82c4ea0b14d0610589e92e25b49e0d986a09bad35d2504c 0x2bc845190813210064200c80019ec031f8063e00c6c019e80b1d0067100c7a018e003118067800c7401890031a8163300c68018cc0318bc63803c5601884031780619
def as82 := bankPage 0x7777777777777777 0xbeb8a9a5a49a988b8a8884736558534b45362e2a 0x400b321893310932c09321313210e3410ad600ad400ad2148d2188d4508d3108dc108d2608d2c08d 20
def ac82 := actionPage 0x80d9749ce800a875a068b24a420620389032552420820e1b481928119440040d560b1288cc004386540507c40c300342c6022331d59801e12900d148ca9000f07780208c58c600a827a00c40263302201190041d10198112076c020b069cc00902d40084c2866043812b004160e83002c05180206032a000c016c00000018c007000 0x4731003b30102000280a2c0030c00483c10080048e2332f40d93a0f801b00a40ebc9ebb40ebc16e41101202000480016e001010a698fc3013013848120105211201015090500402310174000008084cb02440000e570c02524e6001280a0082800a0090008371800014e35100562d960000913d2022000101e42ac050340500f400e513c0002fecb8c0b295290000e7258022400181853300b02805038e801c430000a380002a800280802806489c80718203a10000004000002960572c03020045000f0000007585c085bd6900d8c2200005d001150c180720050706050ab000a270108d2901850d828b44520a00848720b0a20880a00a036303d0d2590400b00175040647002d0070fd4103a02daa92005c 0xedc3d3ddedcdc3dc93dc3ed3ed3d53ed3da3ed93ed3 0x7d4d71adac25009fd3eaa91cc32c6533e4f444087b4c4f89e8ec18c5e8bc96a98c24648af1d85b0530e3a40b6f4c78878ca0d00daf1bfd6cec017f2985009f52490f195615b3b005fca613fa7d49243c653ea6b8b094027f4fa9e8730ca5343986527c4268450820931843d3a91121f1ad3e2134228410498c21ed9108a1041243db7b644f89ed3a98c 0x192c0b248064900c8ea18c53b188163100c6201924a311006484ec64018c803238063700c84018e80312a465308c8c059004b1a0067c00c8a0591003220063e02c7a018f40b138062702c8401910032100622
def as83 := bankPage 0x7777777777777777 0xc5bebcb8a98b8477736553514b4543362e2b2a 0x8c456288ac61158822b0e61a20ad4419a8863518cca219943632b22256844b18d1451a28c345 19
def ac83 := actionPage 0x40e1c4c486002076b068d45875003036d82e64263300181930122f101980140a34081687c8200204f2040aa3853021c2598204b1951801410ec0f220b1cc10807b4078f0590010203b40286026c3002818d0102d131800060bec081207a5000a0506040682d4800581fb01c28106300180da0080a0452001c037000000029008e000 0x605a2004418182b0009b59ad061081cf090e0008b20903cc304000fdfdbe07709297010e001b020f0031d14015a0035400148d400c800de03300002005011a01080050007340e532c0d6348f0180d01c21a10867a050c2838cf34e80300ac00480050b930000a300380288fea09506000094d91c00a620e801b95200060004b79a120140f4040803e2c509401890000023218c81000080168ca8298904fdb003008000d008030972074f00b040100776f012fe29400039005015a0f004003b240340038dc3694027ba01020000180001dce1940a41d13026041cc70282000abf002e0001fe6b0050000e4a1d1b3480034b9 0x320dc320dc9320edc320ed43d43d43ed3eda3eda3ec3edc3edc3 0x10f194184163fe5029f8878ca0c20b14027e21e3283082c7a6d7561a815009f98f3085688017291f2363846bd8672ada19fb015feaa52e91b1aec598ab145ecba9728d7946f65bfb145e8aacc70ca7b2e05bfb4b628be17b2c2556638748d56283285a46b7bcdd53e213422840c610f8d6f79baa7c42684908a1031843dbd31e550970878cabc6ff5bd31e550a013ea5c21e32ac2b7a63caa14027f4fa970878ca 0x64f0cc66018cd5f2a2465400c9e019383b1a0663402c68018d00326a8e3261c480193003250064900c90a38c40326296375dcd0c1890a312146225dcd0eb9994f3309635
def as84 := bankPage 0x7777777777777777 0xb8a9a6a4a39d9b988b89847f6e69655f504c454341362e2b2a29 0x40c224522089160822450c089185022454808918202245020b114092445028911508244600302e800233a0008b680030da002836 26
def ac84 := actionPage 0x4061051848043857a02c808414021c29d0143e3d12800c140c0a1d1b9180060976050d0c4cc004844b024605845021c1f980a2e241402240c6804168f85400705b4018b07026003829a0085032430224121002241621840e0808010f0b18048403b600854452a044017c0041614a7003805180206042b000c016c000000190087000 0x4988114000832a210e1804c12862cc0600e80bc802b1100cd9079350011bba00000941f1f130500d07a3107530a7027b9b0655d00113300086e0500d00b07876055030530c462ddc3fd30306b00061820446a00c7c221826200c4a0730dc42160004001b00851c8102ae324320043e3180728638639e1b001a20880dc5020b407400b07d094d9a0003d00228702b0000036001c3001f4d244c05a80abc2f031902a400b00200a30bd23e5a0f0060006102069130161594 0x8510b320b8610eba531edc510edca5edcba530cb310cb6cb6ca5ed430edc4320ed4320ed20 0x824000004120014c2100c20013b18f31a6306502c534a603082c0c61840000041a058008004f8134008005fe5bcb716d2784eac3417790dd98a9a33304f0962c3502a013f1a327846c6b861058bfce193c2740b24faff3864f09d02c 0x165700cb00195c03120265700cae0989403128065402ca40194c032900635
def as85 := bankPage 0x7777777777777777 0xb8a9a88b837e7a65625f59544c45443629 0x9107e083e041f221bc10dc086e4457822b8115a992e4497024ba145a8c2d5416b20b 17
def ac85 := actionPage 0x61006dd850006087b07c34da1900303f583a18651400261c0c1b0b2d0ac00d0cc60d0553c3600685c306026882b024827582a103a1d001c110c1307190a000e073607830a45204882ca030184c030010151812081d24801c07ec03030b09c19002760180c3c6e04500c2008041216021c04100201050a010e0108000000054087000 0x9b0108dd48000c81913000f8d00091380080d10009c0d90004808730005960009fa90000d501a10dd07c0ed06360450887b6d01a4610d973709010100e10001600800d990305c0080542b0a0c08800ab7de7830900800d520a04800e0a31b05020b60f2d9cd8840a01838008b3092098102f0c8cba0005000007005a8b88b050b403960060520c6e9a000007bd07101700507d9030eca07800123c071980008007ef0510310030ea00a0b9807e00770f60aa60d0f5c0020e060b69890b60996b00008ca0bfe7010fa2003f40003ab4073442964009fa0f10000000cd002ffa905d050000ea401dc82202ca0d43020de700eb995043adf270b860621e2001400e002c10260b30229631006790a01e00be396612fbc00388a02244101327ac24c0 0xedc65430edc765430edc65430edc98654310edc98654310edc98654310edcba85310edcba810edcba8310cb0edcba6510edcba10eda6210987510321098520 0x100000000800002000000010008240080041200000800412044008000020006501200200000000 0x65806cc60598803310366200ca4059500b298065300caec1908a32138e3406c68e389dbf138362704c4e01a3403320065058c88939104f221f6263dc4c63898bf130362604c4c0198c0b2c00662
def as86 := bankPage 0x7777777777777777 0xb8a9a49f9b988b84746a69655d594b4544433e362e2a29 0x88111740222e00652c028a580914b006316014c2c0498543420b002a660c44cc088998411332022650c50cc208a9 23
def ac86 := actionPage 0x61b1093c8c00507ec0c46e8cb9024437506236420a000c1ac8311a1f0900060cf6188c0e48a00386220c45a6a34021c2f18602a301a810e162c2e129694c0880a5416884ac8408404e40943e4827002c21e03a18203a00140e90080a0d118017048802024497004881430100a16470028065002020a188308028c0000000a800d000 0xf40077220000525785e60004d006e5100900df591fbd1806c0601b55d48b800000cebd800703400386a0014029317c380980c20c03000760e0407e80280750007050824010505010440201c000c38d9a0ca577930800000c501f060800026e30a10080239126340131ce04063861013915c30bc0174007b7e0000b03c000345021d54026c30008740c48586d801d883ed02c0bd0c01002400007d97d070010572538d4331800000952025a0656e0560068188c8010d01a506c00b912701c2068ec020040500002d2df837e194160280d91403003e0a200c1558d22a2001fa005be93024e9067393d0000fb0f0d940003ca706005410606800ab01f020001d4040a91000b3b04278000506d20 0xdcba30edcba5430d743d732dc732db63dc732dc2c7edcba10db50edcba0edcba510dcba760bedcba75310 0x13ea1342218dff3fd6749f93ea7c4264981702c000255280955ca9752812c4247c04427d4a02553ea7b4ba94096247258254030010013ed940cb0c6184160009f93ec31861bbf4267dc6e8d91adf198d0580040058c93d1ac31cfb434070c7000 0x33c8065760c8401908031d0066673c62018c403330166500cca05990033218e2f2fc5e0d8bc1317c3e4584c8a939144f22a362043c402188033100066f78ccaab9941332806652fc5c598b813170062e85c5b038b4c7168362d43c4c7f898f7130662646c3e8787c430f8661f00ce02195d1b128862500d1c01994032834658
def as87 := bankPage 0x7777777777777777 0xc7c6b8a9988b846a6966655a5453504b4645443e37362e2c2a2928252423 0x14104444505050214104450808628820c062208486088202045c280850b0202502c18049130302244c08089130202844c0c881130222044c0a081130 30
def ac87 := actionPage 0x60d17918c20430723060ac8a81002835502e52442080081a0c1724a02501090c240b918f46600285e205c84744300142d982e3f311c811414ec161a96a9008709c60b0b0a926005845b0544c4e63001420d826212529020c0f500e0d0d9e801105a6070584c90044826302c1c2282081c106004070a3b802803700000001e800e000 0x203ec033002d00580000010413c0138020025660250025030043828047003740d90652108c00100950b0f30e002d7c462710b180444e504198105ac00e300c0030b643150b70002a03910406d0001860e0000073c11fbf128d10703001290000ba0400f7006b3b6e00c4000013008154ea0c5034120006168140e806907c0a805fe02c0a480000320ca89644b4a0003004b80f00f900e00df00d0324008429577c020f000dc49b07e0040bae0dc80078c0c9032e402ec016a051d906ac2300243f99902df9e00100601e09eae4064000741a00d904c0c4a40b6018020163e80086800700d6f120a9000e6399a9 0xcc2edc4eb4ec2dcba87310ca42dc3a20c0edcba43210dcba8310b0edcba40edcba54310 0xa774de99524a3e0badbd7daa754a99d319d931a9bd24a3e006c310a17c1fc360530a41401da1203e0792f04f0760e9402130053edee3db7b2f59c0b2a33063896586702d71952c3584a013f27d7acbfcc90ca0c20027daff1941840058d9f6b0d612131d61853f2164220067dafe5e8328318610580027db3a584a010b0630c2ff9fea1342263016000 0xcd2059800f148062806cbc0192c033440e4f06c9eab9180323006406fc68218d01b272ee4657c8c019c813338066706c8a01910131e8063d73c4edf89db33108633
def as88 := bankPage 0x7777777777777777 0xb8a98b847f78737170655f5e5a585453504845413e362b2a29221f1e1d1b 0x608045060026141601105060480581c0412c05c800b0169010405a208101644128059800a01604d08058114201608025098020924600824a18024150 30
def ac88 := actionPage 0x40d17864820028543060a82aa4022826582c4d1438831211681625088cc00608460a9043d2400383ca0487c1e30000c1d50223c0d1101100d88101c061040870644068d0308000202fb02c5412a30238129814210749020e07f0050a8230c01101f4020440c8200280ca00c1a04410010051004070130850a01cc0000001c4189000 0xd820aa0400cfa90509c0f1660a2400844f140c7000050a806006c0710985040108392055ee807a30820002039d3080a5a090f900304a50c047c00c00f87e30200622043001e20412218019819000f9000103b94399d8057bdb008000069001009d6010c082390382000d9020400044a200222a004000488e6b82bb9000703205832ba800050084003e5bed80a08180d820aa0400c00438280470061c310cd100050a806006c0710985040108392 0x6ec97ce62dcecbedbdcedc675c 0x2b653ca7684ee6dc798ec05802ff4727f4fe112b8954e9ed3ca76c017f53ba480bac24d998ce61a029b49644c65b0e5767ba9d9fbb234f29d9ee6e8c70620c3a134224ac939250c212b0e3be312c2549a5f4918e31b18e318175e3bc5612c1379638434640c70c60c417565a6f4d909d37a4947c4b539a6f49290d1f00370ea9d33a654c5802fe 0x5905a3330064002c76018e403359666a46c6c078b00b120162200cd4ab8e00f0f0062103c38058600335a36231cc462188c0f0b8164302cc20d9840b1e00639
def as89 := bankPage 0x7777777777777777 0xbeb8b1aaa99b9a92908e8d8b7065635a53504d4c4b4a45362e2b2a291b 0x20110318420818c22040c612020630812031a202018c20441468002a230811211a40201b5201222b80028654804832a102019440600ca1050065 29
def ac89 := actionPage 0x40a1446880002040a0489a344000101f101e481a28010c0ea80d220d1000040704060f864c20c283540287020690234145010341020050a096c0717861501870406028a030e00c281c2014461651000c0d100a1c0a38800805ec040a841c808602660203818e408280f30081004640230031002040120800a00c8000000104005000 0x42620a010042620a0110818e80880fc00042620a011830001314c00368100100a81c02e820724082086002940abc0f7e420f3c0010300608a8980000a80195d806102e81000802006005602de10177802702c5e38088b1a0384000b7090cf2020103004e202074129405e00204450e3000702f030538d812800d820aa0400c0d820aa0400c 0x5edcba5310c3100ca3c3d95366 0x53ca480040053ca482584ad3ca77490a4147a7949000800b9d736d95750280014da110c618417001a7949000800b9a8380b00100173ae6db2aea05000800b084486606305b611be320554978890cab9af59d7365414648895846d2bfd4da4c22432961213422828f0912ad94f29da13ad94f29da13 0x172d8365100cba0595803360065c02caa0196c1b2881e5e6ccc4098cc1b2b0265600ca80794403288064646ca4218cc1b2083641
def as90 := bankPage 0x7777777777777777 0xc2b8afaba98b6e6a6965625f5d5a504541362e2a29281b1918171511 0x4300c41404944141414414280a824050c824240c824441482484148240414820c414840c414880c41490c0065a040254a014054a024054a0 28
def ac90 := actionPage 0x40c0e9506400286f2060709c26001835d030364813000c1a0c1818a21500050c840c0bd0048003060b060547854021c2da02e272f1e811813ec17131187010a09060b8905c58009839c0483c2266063c15981e1a0c22801a085008090421001202060303018c400300bb014120036001c031006050020000800e8000000140086000 0xc3215e088c000802fa8e60a0000a10500a600940301057730520d02180405834470830902500301310c2030004505f80019040501c10800a0210100000628e052d2b300c57c12c17b39b300000f00a629010e2002bb254000007c9a94000be3060fb150b0dc070ed92cc94ac00a06095700021c819816a004c92800130009014c9009ec200151a982001a90808700c00f030600ea00b60801471e26ae0e80b449ad016050139c850c8000390ebfd8a22bc1604410b440009c000de5001ea6008ff0021b003000905163498410030f000f71f50e000083780042620a0110818e80880fc0 0xb2e76432eb7432d631c621c621edc9876543210edc987653210edc987653210ecb763ed531edcba1987510 0x9b05c0b44d82d1360b67c3e41142200acfa8733ea1ca0c02a0040180100000401801672c4185aae0c6185060150020015faba55c1d4390700c6186adb652242843182da480040053ca482584ad3ca77490a4147 0x2cc6019c813388067100cbe0196803380065e00ca2019bd1b3721e6e10cdc199b8072c8065900cd0ab9180331ab65d02cac019b55b2e01655
def as91 := bankPage 0x7777777777777777 0xc7c5b8a09c9b82807574736965535145444341362e2b2a2928211110 0x30089116008361a008361200916120902a122202a1200c4a121204a1220a0a1200c3212088321280832120483412408341204a481200910e 28
def ac91 := actionPage 0x405164bc2800304c2024ac5833001024d8104f2939830c114c0824119d808907c60390480e6043838a018763e61021c1a580c321c4980140b4805168e1400060534028a46884042826b0143e2ca400280f9808191232010e066c0309071d00870286008342ca600480d30000a1083021c03d000010621000e00e8000000058006000 0x17201c00060110a0048319e000100237f107100ba02020b30e00b0e8c08085a17000e000405108220a5700037100770600ea09831d800a425cba00009008f20000d0d90cb30078858b680280c0029a7534500a806f8c2000b503b00000e0fd008000502a43450a0a00f4286000602e00450b4030e45020700020370e0d43a2004090d87430422ef37034300d59077000e28078e809000d0250002c1e43104 0xc543320320dc9320eb3ee73eded73edb3ed53eb2e52c7e73210 0x21c4622780ba4346252268c9e06305cb0d40a7e38a5903182e8f918e311642c435c6b4e88b913225bc469761a43462828f15b42ff55497a2e44e89912d7bce897512de2d8690d18a07bc1780da17fa9b4991f2311642c435c6b48a90d188e29c323646a4524c0940b81647c5364f09d0770c6184174a689912d2f111 0x3278064e0cc6ac3890033b066340cc66018d4031a00633
def as92 := bankPage 0x7777777777777777 0xbbb8ada9948e8b8380736a696865625c534e45444342413e362e29281b16100f0e0d 0x120420a0448120602120420a110010219812400846200041168220408620501021881804086204820218840a00862102404188400602a2104100a88400450a2102104288 34
def ac92 := actionPage 0x6090c89ccc08703f3038524a9202341a981627201281180b0c09108f18800904a40307078a00438211018323c30000810080c161d18800807a4050a0e88000303a401840748004201a90081a3a3000100c90040a1a19810c056802040b090005025600814406c04380d3000041635001c03d00001060a800c0108000000058087000 0x86030cf600003c2e050e00d455600519709e080c9e00913290480950d9008007b91b097665ba007080c2a705000684764135039e804b005505c0060020f000520200114b00fd17bfb60fd83c3882200f480062e80d0001510c01c468807554181000800ae150008c0250000fa798008028070a4690008207c606b106507103000000607701500630b00828500a1d84000c00f1 0xec7543eced632737cb7db63987510a9820c6430edc643 0x6decc93204b05c0b26b4c698af9957a994ca9912500100113a2643a8730e04a45b89b13225ad6b3d2a62744c87024e1c09389912e1c0938990e049c3987025a1c08a870004004380020021c438 0x33c8067800cc001954033b80e2900c52018a01b3802e5b00cb6019d8033a006767dce6019cc033a8067400ce6059d4033180662
def as93 := bankPage 0x7777777777777777 0xb8a9a7a4988b8784655a53504c4b4544362e2a291b0c0b0a09 0x828250c04a2860291430308a1908450c041c86022a43012521818290c441486420a4341052144a0a12230451118230890528 25
def ac93 := actionPage 0x40d11d9068043886306884c054041840d834395d4980141e8c19192d1cc0080e840c8b55ca6043070b06454a037082834983227471c8212189018119d13420e0a980a880bc76048844b0503a463c02341d6022191825801c0b500f0a0617008d04160583c24a6006017a024141051021c09d808040631001802ac00000011810e000 0x560142e42c3821600f200124645046009507000b040e5ca05420000c0597baba306feb08e006b10045902081dc1c0180900c88c1040400280029c30100a720b100007a058000c09930253530134606701bc5a1605bc11701e004b4d0000d603c06006b0800e7116815ba12800e000920d480240d0180b000a5000c0080e019d40618e00b5c91300c508670b0600632ce0a6d0105209400c3021e00d5001c0017d00160058013be40101496b00551400b85c3521003b36c3d80005006000e71b1e05384050083028a0030c081de0058c200980600857f0220001a8540503b02709005d5044200508e0079f002150f69162c80c0860090008300c700b2097460041700ca000506005c66082774a057f0c14ab0470 0xed43d730d73d73d73cba7430cba984310edcba76543210edcba765430edcba7654310edcba765430edba76543210ec7cecec7643 0x1a6b2912ae00718bf12c256c33fc758e9dc03294fa48071b824c038c4b89612a24da692012c2544989612a0044b095002b0c4b0950f425c4b09512c2540009712c2540009712c2540080066ec017f2654956a6d3a6b4d08baa853da76cdd9b228756ce4a4147 0x3330065400d180994c03298466302d180d98803290468c04cb0019f0031e0063b00c72059ec033d8067a02cf0019b403360066900cf4059e55b2e0065c
def as94 := bankPage 0x7777777777777777 0xc7c5b8a99a8b8584828174696557534b46453e3836332e2a292826150908 0x180845045028441150a220480a9081152202048021226200848a881410926009824a802609221108248802c092220902488026212200c884882210a2 30
def ac94 := actionPage 0x604944cce604384f3020926282022823d00a4530208008114c021e17a4408b0796000d8b8c2085035300068482a042816d80033160f0016094800178a9040050444000b0486608182030004a1e7302140e10001e0f38000a064c0009862cc1090244000382ca200280f3000100e64021c04d800020431811000e8000000090006000 0x950901d08070b6000ad5450050060b00bd015030d3a721103d06280e8c480060004530200ae240c1f0f0a0db70cab02304250904516150000e42807000e415900c0b100a0f64264f3f097020d000c50e8ee007200fd9fca047e0db1230020c0405101ac3032ae03800b69e0f9001a60d044b4880009600b8609070005304ab20c07d3e7c09dec00040c80080510205183300701d070a03c600086c00070024c85204038e3c54e4a8 0xd54ececcc987654310edcb9876543210b432432c933e740e74ed43 0x8d8a1d0da134227a4ec4c6600bf95929f4d49a528b3663eac8ffa874bc9752e2544a6945281ff47e82103a003fe7f84b00312c334660aa152c806603b6f6c80888cc0d817c1db0030e4507f0b716c2d6c33fb74ee99bdb20554a012f11119839c668cc17c2f54011119820028850356534888cc13826d94895 0x68400d060b8c813190067f00c620189c033f80623
def as95 := bankPage 0x7777777777777777 0xc7b8aeaca9a49a8f8b8a84776b655753504c49453c39342e2a2908 0x4004c16804882d10110584420930884146110830f001446a02208d120411a1408435001c06a01280d208501a120a034222406845880d 27
def ac95 := actionPage 0x6159a8608a0c3863b0a4c82a6300282e1050601221800e1608272d889440850aa61295440c208384fb0889c1e71001c25183c460d410010110c1b1f0620400a07960d0dc28e404383730645e1281021c18e022240759001a0950090c82ac810d0316038480ce40450113014140282022804d80602004081140088000000080003000 0xea0016906706b90791040f3007a0100fad01010c60d4c7807040e90a9e186d860000b05921c061800040637022520070d30230e527032e40050a713060008b00bbd222a0b6c500c10a102003802b108be003100851b28200100879d075080f09500009400859e014080c0f400069301c1f0a680080e01034b001c000000026eb218a820016319f301cc0581ea04a4a03ae7d98ef00009080150687af010b006c9d20020070b003101205051a6b7105a320020060a001f01d060a1b7881066d30030020d003307402057a5b6702f0002101f 0xcb310cb6ca54eec33e5574e7ececc 0xf808a110011101f13e0228440043e0228440045109404a83700ea2134a502580dc03acb578ac94f06a07201df2369600a8548253224335662a31d23a0670cd19832a3628743684d089e83af1b19528743684d089e93b161a3ab8a682ce99ca9f4d2944890cd730ce592b02600bf95929f4787fc8acc6600bf93525146881a633005fc9a934a5146881a633e5600bf95929f45a7fd841ff 0xca80999803298065260cc2019f983300068704cfa019f403258364a04c940191413248064900c880190c03208068b72c98e19301b260264c4fc8e0191c031f8068a00d0a01a0c033f8064d04c90018f53b188168600c7805a18031d8068600c7201a15471902e32
def as96 := bankPage 0x7777777777777777 0xc2b8b2a995908b84836c6a68655a5753464537362e2a2928231b170d0b0a0806 0x1208520140090c061209080a1209081240084a2212090822140508421205088241208902400aa102c1080e0240884a0222084a0218084a0212104a0212404a02 32
def ac96 := actionPage 0x6179ac788800686ab0acc6368300343058525d1931001016ac232b0b9c808e0a080f130454c04804130648c1e620a301c182a400f30000e0ca8131e0710418605e6090d830c4143829b0485a0e9504281118202305510110070c0f0f8011400702d60585c0100003811301c1c0090001c05d808080030010e018c000000200008000 0x3c0010c5d00ba00c50a0f263c35db0390076479070000300b0ac000365be000218be9b9001a930d00700373609034b063024120ae454000840008cdf4fd087001e10f00518900ae30881a0199cf10389e80bc5bc082b9514a120007285d800f032006c3f0000003c8b040810301244060700030321921028100260072a12107000591340474403e00084c000578b2c034f5000603a00368904200031db0000000a290506331e6010ff9bf100d000820f90a1c0044c1108100030a400dd27002f40050371306000f22400ea600b0c41308000025400064042310006b11201036f032a0250290010078 0x7543ec7ecececb763eccc7edc74baa9820 0xba05389612b31d8130056aa8536a6c4a69cd35a6a4d299d152714e09ad352694ce8a9662bd56aa814fa9e3384e44986b66eb515a2b35648cab454fa7b4ed1a232a9b4cd1ea2c73ab81208420820e9f939d24038c4007f0a414428394706d95b1b4e5eaa79281151d07c045088008b2d5e2b253c6649c0920d4af15929e528910cc9381241a94425012c254490375109a52824025c4b049037 0xb460066100cac05a1803430068400cf801a2c033d8068060cfc019f9833c0067806cec09a2803450068800d0e019c803450068200d02019f403388168004ce6ad9b403362fe7e00cd25999803448066700cc401a2013410068200cbe01a2013408068100cb40d9d5832b0065600d000d9d1832a80655
def as97 := bankPage 0x6666666666667777 0xc7c2c0beb8a99e9a8b847a7865585345433e362e2a2928100908050400 0x81b4001445a000134d00061128000b09400024f200012b9000191c800088e400040720001349000095c000c04012c84044a8812249040a12504 29
def ac97 := actionPage 0x813124856400505aa0908c4230020c2c4846432118090415ec211d8f20c18a0a06108d46cc600384aa080643232001024103e2f1719000811681f158a90800708380d880496600703440343a1e330244121810150f40021007880708871041080336038242d0608381420180c1232021c081806040512011801cc000000114009000 0xdf050080000462e5dd54500a03a441bec0f0200241e0614801a0d00380259bb00079d83a004a40001378222007016024200000800212a0c0004201a4201004a02940cc1000cf0c1960000004008010d0f4c02d40c01e633e55900000780e818b12ad00001247909208000039070a5c00782c078a0030800a44050060d381e6805ee4d0a0760c0810770583501c81462a020122101999000b9073700d800c0051042f920190c1b0286040005676575040483704700440160050440e0a00cab3f1e0d008a300810 0xededad43dceddcedcedcccba737643ed543 0xb01359f2be26e6cf18e90e1e230c32b7862442e69bdf18747a35c6a864f75b898b21741e17bdd6e262c85b1b1920b2eacd592360dbc10c0c3786ef58bb15611bc31b2183143082cbaf6e6c24d2724618c29802fe43c30a744901181635a668cb87c0dd1a62744bc3a8702504b0954fa84d08a0a 0x35b97ea000d405fa64034c8069543d1e21a3d63570069800d4009a78034f0069c00d36bdad927510fea213d4401a75174da1e9b0ed3619a6c0b4d8069b00d348ba3d0f478768f0cd1e05a3c0347866b800d7003a58034b0069500d1e019d403462b65d00cba0190c132080641
def as98 := bankPage 0x6666666666666666 0xc7c2beb8a9a49b9a918b847a7874736d6558545350453e36 0x1010971020979000976040873400871000d30880930841131004951010951200950e00910864110d00a1084a0e104896 24
def ac98 := actionPage 0x40b15860840420433050a42a4300141f981c4c133100100e480c24898c008306e40511c40460028343020801a73002816580e370c48810e09cc061705a4408704360289c24e400381c300c3c109104200b1806170639000e042803098210800501b4010400c62044009200816045100100350020800190208010c000000200005000 0x6201612e80051040b020302008a06053d0202bf00308000f104000213068e25e06000100e00701a019e280043302e007010010b108705721000593010010e00870377400028501000310000800076f5464060020b0b054d00076134810fc0000b74000c040060f123500400286c000c0407c00980c36126100032020a0c0a02a20c0400060c6a55070d00 0xdcedcdcedaedccceccececcadb 0x2eb4d7494132c0b3c55c9267cbe2530924880cb6e29d8f7b714176126acc522032c398499a9316623e34c69892423140935262cc47c6ab54ba2744c7e53aa4a492920fc8490589d5252494907e42484705c0b17f2fc534925020750c2bf1242054088e0fc82b4f482d049ed0010b9868c3bb9445f137363643861865 0x1a6c03500669c00d5401a68fb4c9ee9931d325fa652756166987bd5c01a780b4e0069c02d5201aa403510e68f00d1e01a880f4f00696
def as99 := bankPage 0x6666666666666666 0xb8aea9a49b8f8b84787774736e6b65645857534b45413e362e2b2a 0x80026130005426040884a1011092402213200442488108491c01092242a02450540600a015401104a880209446202520088c24001958 27
def ac99 := actionPage 0x60a9045d66004035b04c742873002417582032124100100a2c0f15889c408704660709040e204381db0343a1a7300180c9818160c38810e04e40a0a060802820252048483040001011902020182000080850100d09198208038808058289000501640402404480028081018100210000803900c030028810a010c0000000c0005000 0x80c59d3030d2f40a0200cb0a000086bb2bd9002ef0009e55730008000b900a3900d58703f0cf0bf053890101801000e0cd0bf053890101801000e0cd00079ff0070b9f4d050bf053890101801000e0cd02c100810081060600d8d8198000883f07182218e00b5000831802140000c00000271f04d90820 0xe74ed7e7cce74ceb2ecb2ec52c 0x6d8c258429e4d0940d514e29843c65474712ce0878ca0e61259c336600bf97e23a3f244662b365fcbf1392634913159b2fe5f89c931a48712c017f263490810734c566cbf97e23744e7e5c91f91500b05402c4ea92416275058a68162be4f49712da4f06cc4d3182c 0x35e016ac00d5801ae40357006a202d5e05abc035d806af00d5c01a5c0356806ac00d5609a5c0355066a800d5019a8403508069d
def as100 := bankPage 0x6666666666666666 0xc7c5c2beb8aca9a59a8a847773655853504b4945362e2b2a 0x48041b88041b08250d081855880545280c45084445082845080705180499880519084419048419090419028429080589 24
def ac100 := actionPage 0x403120704600182f2018863253041016500a3f182080080a84041e0c0c00020526020d454e6003024a010602851020c1150082c1320800a07e802130998008403a60007841060048162000361c32021009d800140c39000c03c80008848cc0060174000342082041809a000140a3304140350000604208106012c000000190006000 0x400812a05a040e2200203228130038090015601a00801037a009c05651c061a28034505c30036060000863b2ca9002e9000ee5573000002a0840980014402f02802094f026403d0602004000c76c8003e6a4c0980000c76c80b0a02356032008f57 0x320320eec333edca3c3ed35ed35ec97 0x6502c51e43c65061058c79842b4400c50650b46f4c795428e4b843c653da694bd15498c552398658ca5e8bc96a98c24648a61c746f4c78878ca0d00d9b220921ed9d7f29851c924878ca5343986546b42284104a7522243e35a11420826633385fcbf4fd10f 0x14755a96ad4ed5601aac0b56806ad
def as101 := bankPage 0x6666666666666666 0xb8b3b2a9a6a4a3969592908e8b847a6c686559504d4c453629 0x200843a00421c40410e204087104043884021c44010f040087880043880441c40240f0000ab800445c20022c402126201c43 25
def ac101 := actionPage 0x4090a85ca000282290484e2c31020c108022261608010408280f118b0c000303d007088582004101e202c3a2c5000140d980c141648030e0568060989050005025403044344a04201010141c1a30020c075006090d28000803080304040540050124018101486003805100c060413001401880400021801060064000000008003000 0x980148056800022d004040b300004098014805680030d5090690004ae225f2003c04010582301064d608500d14001194001440b14008019840208c0f027004ea030120e1900d140008230 0x1b320b8610cb310cb6ca5cb 0xce187b0a55818505012000255d533828e0019c30f614ab030ab9558a35218710de1842e829000824002e614c255b73314c41201600041a0580080000082809000 0x6b404d4c01a98035a816b200d4a0dac4035a026a400d4801acd1b4fa1e9f10d3e19a7c0b5a806b200d4601ac4035f806b0
def as102 := bankPage 0x6666666666666666 0xc6c2b8b0afada9908b84837a786a65625a595853504b453e362e2a29231b1a19 0x200202910282030208809084030090842202310402c8110402809088c00088b0604200b020440450204241902012429020030290202202900482029010820290 32
def ac102 := actionPage 0x8080cc750800782cb0305c365206281290142a1b20000808a808130d90000404060407c64e404281c101c3a322002080d900c1a181880080628060b8a8cc00402c6028444cc4003011a0141a224204140750060a10188008030801050680c4030144008241c2c00280720041004150014020802050118810600a8000000144004000 0x300959009404000282ff280508088280005292032003608077008591a4203306024007503027e04500a00545c001c40545c001c40790200040052032008104006001c10d08025c00bc007b0a3300bf000201204014fc3002b2e0004800403a091ae00259ae2803d00004d0000022d00149600287 0xedcbeddccca1bac7bcb0987510a98207c 0xafd5d2ae0ea1c8380630c2f7dc93736e0c7ea753b66ccd6a753b66ccd6c13796364346306305d34dc9d4ca6289c9090f1ced91799111cc18416247258254034fb434070000005cc2984ab6e6629882402c 0x236b743d6e21adc335b806b30cd7001adc074f8069f56d4a05a8c0352816a303d3005a9c035b006c100d6001b000358006a7
def as103 := bankPage 0x6666666666666666 0xbdbbb8a9948b847473655345433e3c39362e2a29181716100e0d0c0b0a08 0x2320400451840011462000481828021460801051820082050904051820102064808082210c0404851020121440188841008142500146084008142600 30
def ac103 := actionPage 0x40c8e07cc204384320606a3c31041020502e321d1880080f8c15168d14c08807040a0a864620028352044502e22002018581e24112302160a0c0c1007908089042605060350400481a2024261a5000140b8012110d10000405a808068690000302920382834600018133010080e66003005100202051100100168000000094009000 0x6c02110a084724a8041f0386a2001b600308a48000003800d23487012e1e09b0c08004580a4352006500a82857055032ea00a050070b76970f000e02e2a00bc00e7e0044300c550f0fa70f700000163005c0130042d0585000a102a10045ea02080010801f000914b66c60003b7e0f0a610b095000d0007581e00a431a006740a8385701eddc1d43030a35037581 0xceeec7cecec7543ecececb763eced531 0x11fa0840e800ff9fe4de9a133ad2562ac19bb005fc995252684cc8a59b3356649901702c98498d30a259ad31a62be655ea653224a8b71362644b5ad0e049c4c8970e049c5a896b559cb10616ab83186166ccd400800 0x351306a700d7a05abc0357806bc02d76ada940352806bb00d6401aec0353806a302d5201aa4035d006ba00d7409ae4035c806b400d7201a980352006b1
def as104 := bankPage 0x5666666666666666 0xc7c2bfb8b2a9958b847a776c6b65595853453e3c38362e2a29170b080401 0x104580001618801054640044011122100482304012094c080039080110a41004509040220c410a0831040122441084a2102412084060482101442084 30
def ac104 := actionPage 0x411924408210283d30748c203000141c982e431018020a0d4816208609000905f60a8ec28c410302b30486a106200241218222f0531820e07ac0e1382a0000603460608410c2003015b02c300691041c080812160310000403c80908009881070164038300082002008a0141000400010031006040020000800e8000000100006000 0x1830033054d00f001805093008600046003700134b00002da75a80028415019f7005000500135617036e00b59403438000c53000607d08500eb703010a06000e8900006b5000605740a907017070004065608706000ca010a0c939060d0900f20c833828212dc614703706000e8c4801094001800109400180018c00c6005103 0xc7643ececcbaecece 0x274490118164f7726dce7ac906e62584aa734d69a934a67454cdd6a2b4566ac919359666cb07b8dc1a0af1592944886649c0920d4b2d5e2b20d40e403cc67cac017f2b253e8b5161ff6107fe632fe564a7d34a5166cc7d591ff66cb4d19a3266cb4d19a3246c8d515a2a 0x1b04035f80e9400d2801a4c0349006c000d7e03a4403488269000d2001ad4035e006be00d7a01ae4035b026be00d7c01ad0135e806bd00d5ea3aac175582eab04d5601af80353006be00d480dae98351806a3
def as105 := bankPage 0x5555555555555555 0xc7c2c0beb8a9a4978c8b86847a7867656459585347453e 0x5010664020c2006c84029908093310026520144b0208904541210a824205048248a104614208a484122510224a4 23
def ac105 := actionPage 0x4088e02860041820a0446a1032000c0f501a320818000807080d17830c82030344068b0106400181830304c0263001c095018210028810604200c0f80080002020205874004000100f202c2e0060000c0698120f0040010a02480706000c000300e402824006000180510100c00300008021004030018000600880000000c0003000 0x304008700e0440d00000531ad04645183010862000e00010313720d05177001001a8440080604075701040006db5090db7608003069000030690001160030690000306900 0xdadcededce 0xf75c6b70862dc485b114c21018d8c90597566ac916f0c6c860c50c20b1f09842fe394304c167b349c8cd2722614bf90f0c3349c918630a600bf90f0c33c1c73709ece41b94f2722c3277c5e6e13d247372 0x1b343362006cc43d8a19b140362806cc00d9619b400368006ca00d8601b240361006c800d8e01b0c0363006c2
def as106 := bankPage 0x5555555555555555 0xc7b8b2b0a995908b847978777674736d6c6b656458534b453e362e2a 0x400044540a004540102c140202c1408202a800015c400104c4040254110024421002440a002440c0024409008444084044400825840a0058 28
def ac106 := actionPage 0x40489c14c204201210204a0a20000808801023051000040420081082880002020003880142000100fa018320a70041006900c120438800a0284050801884083011202838084204100780101a041002080380060c0208010401a002058104008200c200824084004100510040c02310014019000030018830600440000000c0002000 0x404ca003800420101010d45a2201c0002a83700d001086002c304040409430a932d08006480450024 0xcccccd 0x4c566cbf11ba273f2e48fc8a80582a0162be99b20db131352698c164d4988f8d56a9744c7e6353629829859ab3566b30112a383f20ae60a9319334def8c3 0x6cb04d9601b300362806cf02d9c01b3c036721ec5
def as107 := bankPage 0x5555555555555555 0xc7c2c1bfbdbbb8a98b847a78736c6559534d45433e3c362e2a291a1917100d0b0801 0x1e100004400a0402020284008080a0804020282020202044100202820800642004002022820301000b00040222400400889002002224000810890002024240009840900 34
def ac107 := actionPage 0x4080983460002020903c461a3006080fc81e210c10830407a40f0f058c400303a4070702444043019803834122000080c901a180711010c05680a0b0388000602460404414a404380ca0201c0433041404c0100e02000002024806050110000300e60100809000030029004000420020800c00200020000020044000000008182000 0x370508440213040200db34064007182c800802054186da228018051081403c04000a050090300de108e8c07207500002078000018c00094801140405030e50270083000408 0xecececedcbacb 0x4f391ee459b2d3466b4958a684cc8a531a258b4b559b3359a532defb926e6dc18f8f61b63319c30f614ab15caac51a90c3886f0ba0a598a62 0xda203b0c0361806c200d9e01b380367806d001d8801b103368006cd04d9e01b3d1b66a1ecd10d9a19b340367006d1
def as108 := bankPage 0x4444444444444455 0xc7c3bfbab8a9968c8b86847a79786c67656459585347453e3601 0x2000888200822400083200016408240904082840840a102084841010a20204290080898018102005302001340800820a14204289 26
def ac108 := actionPage 0x80a004000008118040500200000408881e260110000404080f100098018301c007878044000100d9038360230000806481a180118000402e40d0a808c00020152060480460001009902c1e023000080448160d0010800401e00a060004000200e204824006004100610200c00300208029008030018020800a80000000c0004000 0x480070508060101160116004301160116013c090c010c01020720401f0f70006430 0xc 0x7bae36664826c2c45308409a4e467838e6e13d9c83729e4e45864ef8bcdc27a48e6e51a5b0ccb9dd175c64f191ae3e7bb936e73d648373 0xcda801b4c0369006d300da401b500369806d200da201b280364806c800da201b1c1363006c6
def as109 := bankPage 0x33344 0xc1bab886847a7859531901 0x4144d06a0b4916 11
def ac109 := actionPage 0x3058000000100b2018200060001004900c0a0030000801d00202001800060064000000080003000 0x8100810000234e0004320 0x0 0x13ba2eb8c9e3235c7cf391ee46694cb 0x1b4c0369006d4
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactStates (i : Nat) := (if Nat.blt i 880 then (if Nat.blt i 432 then (if Nat.blt i 208 then (if Nat.blt i 96 then (if Nat.blt i 48 then (if Nat.blt i 16 then as0 i else (if Nat.blt i 32 then as1 i else as2 i)) else (if Nat.blt i 64 then as3 i else (if Nat.blt i 80 then as4 i else as5 i))) else (if Nat.blt i 144 then (if Nat.blt i 112 then as6 i else (if Nat.blt i 128 then as7 i else as8 i)) else (if Nat.blt i 176 then (if Nat.blt i 160 then as9 i else as10 i) else (if Nat.blt i 192 then as11 i else as12 i)))) else (if Nat.blt i 320 then (if Nat.blt i 256 then (if Nat.blt i 224 then as13 i else (if Nat.blt i 240 then as14 i else as15 i)) else (if Nat.blt i 288 then (if Nat.blt i 272 then as16 i else as17 i) else (if Nat.blt i 304 then as18 i else as19 i))) else (if Nat.blt i 368 then (if Nat.blt i 336 then as20 i else (if Nat.blt i 352 then as21 i else as22 i)) else (if Nat.blt i 400 then (if Nat.blt i 384 then as23 i else as24 i) else (if Nat.blt i 416 then as25 i else as26 i))))) else (if Nat.blt i 656 then (if Nat.blt i 544 then (if Nat.blt i 480 then (if Nat.blt i 448 then as27 i else (if Nat.blt i 464 then as28 i else as29 i)) else (if Nat.blt i 512 then (if Nat.blt i 496 then as30 i else as31 i) else (if Nat.blt i 528 then as32 i else as33 i))) else (if Nat.blt i 592 then (if Nat.blt i 560 then as34 i else (if Nat.blt i 576 then as35 i else as36 i)) else (if Nat.blt i 624 then (if Nat.blt i 608 then as37 i else as38 i) else (if Nat.blt i 640 then as39 i else as40 i)))) else (if Nat.blt i 768 then (if Nat.blt i 704 then (if Nat.blt i 672 then as41 i else (if Nat.blt i 688 then as42 i else as43 i)) else (if Nat.blt i 736 then (if Nat.blt i 720 then as44 i else as45 i) else (if Nat.blt i 752 then as46 i else as47 i))) else (if Nat.blt i 816 then (if Nat.blt i 784 then as48 i else (if Nat.blt i 800 then as49 i else as50 i)) else (if Nat.blt i 848 then (if Nat.blt i 832 then as51 i else as52 i) else (if Nat.blt i 864 then as53 i else as54 i)))))) else (if Nat.blt i 1312 then (if Nat.blt i 1088 then (if Nat.blt i 976 then (if Nat.blt i 928 then (if Nat.blt i 896 then as55 i else (if Nat.blt i 912 then as56 i else as57 i)) else (if Nat.blt i 944 then as58 i else (if Nat.blt i 960 then as59 i else as60 i))) else (if Nat.blt i 1024 then (if Nat.blt i 992 then as61 i else (if Nat.blt i 1008 then as62 i else as63 i)) else (if Nat.blt i 1056 then (if Nat.blt i 1040 then as64 i else as65 i) else (if Nat.blt i 1072 then as66 i else as67 i)))) else (if Nat.blt i 1200 then (if Nat.blt i 1136 then (if Nat.blt i 1104 then as68 i else (if Nat.blt i 1120 then as69 i else as70 i)) else (if Nat.blt i 1168 then (if Nat.blt i 1152 then as71 i else as72 i) else (if Nat.blt i 1184 then as73 i else as74 i))) else (if Nat.blt i 1248 then (if Nat.blt i 1216 then as75 i else (if Nat.blt i 1232 then as76 i else as77 i)) else (if Nat.blt i 1280 then (if Nat.blt i 1264 then as78 i else as79 i) else (if Nat.blt i 1296 then as80 i else as81 i))))) else (if Nat.blt i 1536 then (if Nat.blt i 1424 then (if Nat.blt i 1360 then (if Nat.blt i 1328 then as82 i else (if Nat.blt i 1344 then as83 i else as84 i)) else (if Nat.blt i 1392 then (if Nat.blt i 1376 then as85 i else as86 i) else (if Nat.blt i 1408 then as87 i else as88 i))) else (if Nat.blt i 1472 then (if Nat.blt i 1440 then as89 i else (if Nat.blt i 1456 then as90 i else as91 i)) else (if Nat.blt i 1504 then (if Nat.blt i 1488 then as92 i else as93 i) else (if Nat.blt i 1520 then as94 i else as95 i)))) else (if Nat.blt i 1648 then (if Nat.blt i 1584 then (if Nat.blt i 1552 then as96 i else (if Nat.blt i 1568 then as97 i else as98 i)) else (if Nat.blt i 1616 then (if Nat.blt i 1600 then as99 i else as100 i) else (if Nat.blt i 1632 then as101 i else as102 i))) else (if Nat.blt i 1696 then (if Nat.blt i 1664 then as103 i else (if Nat.blt i 1680 then as104 i else as105 i)) else (if Nat.blt i 1728 then (if Nat.blt i 1712 then as106 i else as107 i) else (if Nat.blt i 1744 then as108 i else as109 i)))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactAdvice (i tok : Nat) := (if Nat.blt i 880 then (if Nat.blt i 432 then (if Nat.blt i 208 then (if Nat.blt i 96 then (if Nat.blt i 48 then (if Nat.blt i 16 then ac0 i tok else (if Nat.blt i 32 then ac1 i tok else ac2 i tok)) else (if Nat.blt i 64 then ac3 i tok else (if Nat.blt i 80 then ac4 i tok else ac5 i tok))) else (if Nat.blt i 144 then (if Nat.blt i 112 then ac6 i tok else (if Nat.blt i 128 then ac7 i tok else ac8 i tok)) else (if Nat.blt i 176 then (if Nat.blt i 160 then ac9 i tok else ac10 i tok) else (if Nat.blt i 192 then ac11 i tok else ac12 i tok)))) else (if Nat.blt i 320 then (if Nat.blt i 256 then (if Nat.blt i 224 then ac13 i tok else (if Nat.blt i 240 then ac14 i tok else ac15 i tok)) else (if Nat.blt i 288 then (if Nat.blt i 272 then ac16 i tok else ac17 i tok) else (if Nat.blt i 304 then ac18 i tok else ac19 i tok))) else (if Nat.blt i 368 then (if Nat.blt i 336 then ac20 i tok else (if Nat.blt i 352 then ac21 i tok else ac22 i tok)) else (if Nat.blt i 400 then (if Nat.blt i 384 then ac23 i tok else ac24 i tok) else (if Nat.blt i 416 then ac25 i tok else ac26 i tok))))) else (if Nat.blt i 656 then (if Nat.blt i 544 then (if Nat.blt i 480 then (if Nat.blt i 448 then ac27 i tok else (if Nat.blt i 464 then ac28 i tok else ac29 i tok)) else (if Nat.blt i 512 then (if Nat.blt i 496 then ac30 i tok else ac31 i tok) else (if Nat.blt i 528 then ac32 i tok else ac33 i tok))) else (if Nat.blt i 592 then (if Nat.blt i 560 then ac34 i tok else (if Nat.blt i 576 then ac35 i tok else ac36 i tok)) else (if Nat.blt i 624 then (if Nat.blt i 608 then ac37 i tok else ac38 i tok) else (if Nat.blt i 640 then ac39 i tok else ac40 i tok)))) else (if Nat.blt i 768 then (if Nat.blt i 704 then (if Nat.blt i 672 then ac41 i tok else (if Nat.blt i 688 then ac42 i tok else ac43 i tok)) else (if Nat.blt i 736 then (if Nat.blt i 720 then ac44 i tok else ac45 i tok) else (if Nat.blt i 752 then ac46 i tok else ac47 i tok))) else (if Nat.blt i 816 then (if Nat.blt i 784 then ac48 i tok else (if Nat.blt i 800 then ac49 i tok else ac50 i tok)) else (if Nat.blt i 848 then (if Nat.blt i 832 then ac51 i tok else ac52 i tok) else (if Nat.blt i 864 then ac53 i tok else ac54 i tok)))))) else (if Nat.blt i 1312 then (if Nat.blt i 1088 then (if Nat.blt i 976 then (if Nat.blt i 928 then (if Nat.blt i 896 then ac55 i tok else (if Nat.blt i 912 then ac56 i tok else ac57 i tok)) else (if Nat.blt i 944 then ac58 i tok else (if Nat.blt i 960 then ac59 i tok else ac60 i tok))) else (if Nat.blt i 1024 then (if Nat.blt i 992 then ac61 i tok else (if Nat.blt i 1008 then ac62 i tok else ac63 i tok)) else (if Nat.blt i 1056 then (if Nat.blt i 1040 then ac64 i tok else ac65 i tok) else (if Nat.blt i 1072 then ac66 i tok else ac67 i tok)))) else (if Nat.blt i 1200 then (if Nat.blt i 1136 then (if Nat.blt i 1104 then ac68 i tok else (if Nat.blt i 1120 then ac69 i tok else ac70 i tok)) else (if Nat.blt i 1168 then (if Nat.blt i 1152 then ac71 i tok else ac72 i tok) else (if Nat.blt i 1184 then ac73 i tok else ac74 i tok))) else (if Nat.blt i 1248 then (if Nat.blt i 1216 then ac75 i tok else (if Nat.blt i 1232 then ac76 i tok else ac77 i tok)) else (if Nat.blt i 1280 then (if Nat.blt i 1264 then ac78 i tok else ac79 i tok) else (if Nat.blt i 1296 then ac80 i tok else ac81 i tok))))) else (if Nat.blt i 1536 then (if Nat.blt i 1424 then (if Nat.blt i 1360 then (if Nat.blt i 1328 then ac82 i tok else (if Nat.blt i 1344 then ac83 i tok else ac84 i tok)) else (if Nat.blt i 1392 then (if Nat.blt i 1376 then ac85 i tok else ac86 i tok) else (if Nat.blt i 1408 then ac87 i tok else ac88 i tok))) else (if Nat.blt i 1472 then (if Nat.blt i 1440 then ac89 i tok else (if Nat.blt i 1456 then ac90 i tok else ac91 i tok)) else (if Nat.blt i 1504 then (if Nat.blt i 1488 then ac92 i tok else ac93 i tok) else (if Nat.blt i 1520 then ac94 i tok else ac95 i tok)))) else (if Nat.blt i 1648 then (if Nat.blt i 1584 then (if Nat.blt i 1552 then ac96 i tok else (if Nat.blt i 1568 then ac97 i tok else ac98 i tok)) else (if Nat.blt i 1616 then (if Nat.blt i 1600 then ac99 i tok else ac100 i tok) else (if Nat.blt i 1632 then ac101 i tok else ac102 i tok))) else (if Nat.blt i 1696 then (if Nat.blt i 1664 then ac103 i tok else (if Nat.blt i 1680 then ac104 i tok else ac105 i tok)) else (if Nat.blt i 1728 then (if Nat.blt i 1712 then ac106 i tok else ac107 i tok) else (if Nat.blt i 1744 then ac108 i tok else ac109 i tok)))))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactLinks (i tok : Nat) : Option DagLink :=
  let c := compactAdvice i tok
  if c % 2=1 then some ((c/2) % 2048, c/4096) else none
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactHint (i tok : Nat) : Nat :=
  let c := compactAdvice i tok
  if c % 2=1 then 15 else if c/2<16 then c/2 else 16+hull (c/2-16)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactCut := geometryOrMinor minors compactHint
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
def compactCheck := scan (fullMask 25) T diagonal compactStates 1749 (dagMoves records) compactLinks compactCut

end Rep9102.Final9102
open WordEngine
namespace Rep9102.Fast
open Orbit Project Final9102

def forceN {α : Type} (w : Nat) (k : Nat → α) : α := Nat.rec (k 0) (fun v _ => k (v+1)) w
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
@[simp] theorem forceN_eq {α : Type} (w : Nat) (k : Nat → α) : forceN w k = k w := by cases w <;> rfl

def forceList (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun f => f [])
    (fun w _ rest f => forceN w (fun x => rest (fun tail => f (x::tail)))) ws) k
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
@[simp] theorem forceList_eq (ws : List Nat) (k : List Nat → Bool) : forceList ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceN w (fun x => forceList ws (fun tail => k (x::tail))) = _
    rw [forceN_eq,ih]

def tag (g : Nat) : List Nat → Nat → Nat
  | [],_ => 0
  | n::ns,w => (if w.testBit n then 0 else g &&& w) ||| (tag g ns w <<< 25)
def wanted (g : Nat) : List Nat → Nat
  | [] => 0
  | _::ns => g ||| (wanted g ns <<< 25)
def unionTags (t : Nat → Nat) : List Nat → Nat
  | [] => 0
  | w::ws => t w ||| unionTags t ws

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem pack_cons (g n : Nat) (ns ws : List Nat) :
    unionTags (tag g (n::ns)) ws = (g &&& coverAt n ws) ||| (unionTags (tag g ns) ws <<< 25) := by
  induction ws with
  | nil => simp [unionTags,coverAt]
  | cons w ws ih =>
    change tag g (n::ns) w ||| unionTags (tag g (n::ns)) ws =
      (g &&& (if w.testBit n then coverAt n ws else w ||| coverAt n ws)) ||| ((tag g ns w ||| unionTags (tag g ns) ws) <<< 25)
    rw [ih,Nat.shiftLeft_or_distrib,tag]
    cases w.testBit n <;> simp [Nat.and_or_distrib_left,Nat.or_comm,Nat.or_left_comm,Nat.or_assoc]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem pack_good (g : Nat) (ns ws : List Nat)
    (h : ∀ n ∈ ns, g &&& coverAt n ws = g) : unionTags (tag g ns) ws = wanted g ns := by
  induction ns with
  | nil => induction ws <;> simp_all [tag,unionTags,wanted]
  | cons n ns ih => rw [pack_cons,h n (by simp),ih (fun j hj => h j (by simp [hj])),wanted]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem unionBits (t : Nat → Nat) (ws : List Nat) (b : Nat) :
    (unionTags t ws).testBit b = true ↔ ∃ w ∈ ws, (t w).testBit b = true := by
  induction ws with
  | nil => simp [unionTags]
  | cons w ws ih => simp [unionTags,Nat.testBit_or,ih]

def without (x y : Nat) : List Nat → List Nat → Nat
  | w::ws,t::ts =>
    if w == x || w == y then without x y ws ts else t ||| without x y ws ts
  | _,_ => 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem without_eq (x y : Nat) (t : Nat → Nat) (ws : List Nat) :
    without x y ws (ws.map t) = unionTags t (ws.filter (fun w => w != x && w != y)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    by_cases a : w=x <;> by_cases b : w=y <;> simp [without,unionTags,a,b,ih]

def kept (ws : List Nat) (x y k : Nat) := keepWord (k.testBit 1) y (keepWord (k.testBit 0) x ws)
def combined (base tx ty tz k : Nat) :=
  base ||| (if k.testBit 0 then tx else 0) ||| (if k.testBit 1 then ty else 0) ||| tz

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem childTags (t : Nat → Nat) (ws : List Nat) (x y z k : Nat)
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (ne : x ≠ y) :
    unionTags t (insertWord z (kept ws x y k)) =
      combined (without x y ws (ws.map t)) (t x) (t y) (t z) k := by
  rw [without_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  simp only [combined,Nat.testBit_or,Bool.or_eq_true,unionBits,List.mem_filter,Bool.and_eq_true,
    bne_iff_ne,insertWordMem,kept,keepWord]
  cases k.testBit 0 <;> cases k.testBit 1 <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.zero_testBit,
    nd.mem_erase_iff,(nd.erase x).mem_erase_iff] <;> grind

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem insertLength (z : Nat) (ws : List Nat) : (insertWord z ws).length = ws.length+1 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change (if z ≤ w then z::w::ws else w::insertWord z ws).length = _
    split <;> simp [ih]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem block_of {lo n : Nat} {f : Nat → Bool}
    (all : ∀ j, lo ≤ j → j < lo+n → f j = true) : treeBlock lo n f = true := by
  induction n generalizing lo with
  | zero => rfl
  | succ n ih =>
    change (f lo && treeBlock (lo+1) n f) = true
    exact Bool.and_eq_true_iff.mpr ⟨all _ le_rfl (by omega),ih (fun j a b => all j (by omega) (by omega))⟩

def direct (m g : Nat) (ns : List Nat) (i : Nat) (s : RowState)
    (finish : Nat → RowState → Bool) : Bool :=
  let fuel := s.1
  forceList s.2.1 fun ws =>
    let n := ws.length
    dagStateOK m ws && decide (n ≤ 64) && !(ws.contains g) &&
    (fuel == 0 || forceN (wanted g ns) (fun full =>
      forceList (ws.map (tag g ns)) fun tags =>
      treeBlock 0 n fun a =>
      forceN (ws.getD a 0) fun x =>
      forceN (tags.getD a 0) fun tx =>
      treeBlock (a+1) (n-(a+1)) fun b =>
      forceN (ws.getD b 0) fun y =>
      forceN (tags.getD b 0) fun ty =>
      forceN (without x y ws tags) fun base =>
      treeBlock 0 2 fun op =>
      forceN (if op == 0 then x &&& y else x ||| y) fun z =>
      z == 0 || z == m || ws.contains z ||
      forceN (tag g ns z) (fun tz =>
      treeBlock 0 4 fun k =>
        let rest := kept ws x y k
        decide (fuel-1+1 < rest.length+1) ||
        (combined base tx ty tz k != full) ||
        forceList (insertWord z rest) (fun bank => finish (gateToken a b op k) (fuel-1,bank,(z,x,y)::s.2.2)))))

end Rep9102.Fast

namespace Rep9102.Fast
open Orbit Project Final9102

def linkCode (c : Nat) : Option DagLink := if c % 2=1 then some ((c/2) % 2048,c/4096) else none
def hintCode (hullAt : Nat → Nat) (c : Nat) := if c % 2=1 then 15 else if c/2<16 then c/2 else 16+hullAt (c/2-16)

def dispatch (bank : Table) (count : Nat) (moves : Array WordMove) (ms : Array Minor)
    (hullAt : Nat → Nat) (ad : Nat → Nat → Nat) (i tok : Nat) (s : RowState) :=
  forceN (ad i tok) fun c =>
    if c % 2=1 then dagRef count bank moves (fun _ _ => linkCode c) i tok s
    else geometryOrMinor ms (fun _ _ => hintCode hullAt c) i tok s

def fastCheckWith (bank : Table) (count : Nat) (moves : Array WordMove) (ms : Array Minor)
    (hullAt : Nat → Nat) (ad : Nat → Nat → Nat) (i : Nat) :=
  match bank i with
  | none => false
  | some s => direct (fullMask 25) T diagonal i s (dispatch bank count moves ms hullAt ad i)


end Rep9102.Fast
open WordEngine
namespace Rep9102.Fast
open Orbit Project Final9102

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem getTag (f : Nat → Nat) (ws : List Nat) (a : Nat) (ha : a < ws.length) :
    (ws.map f).getD a 0 = f (ws.getD a 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using ha),List.getD_eq_getElem _ _ ha,List.getElem_map]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem direct_pass {m g i : Nat} {ns : List Nat} {s : RowState} {finish : Nat → RowState → Bool}
    (ok : direct m g ns i s finish = true)
    {bank : Table} {count : Nat} {moves : Array WordMove} {lk : DagLinks} {cut : EdgeCut}
    (sound : ∀ tok c, finish tok c = true →
      (cut i tok c || dagRef count bank moves lk i tok c) = true)
    {a b op k : Nat} (hab : a<b) (hb : b<s.2.1.length) (ho : op<2) (hk : k<4) :
    pass m g ns bank count moves lk cut i s a b op k = true := by
  obtain ⟨fuel,ws,history⟩ := s
  change b < ws.length at hb
  simp only [direct,forceList_eq,forceN_eq,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨stateOK,width⟩,_⟩,all⟩ := ok
  change ws.length ≤ 64 at width
  have nd := (dagStateOKSpec stateOK).1
  have ha := hab.trans hb
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := if op == 0 then x &&& y else x ||| y
  let rest := kept ws x y k
  have fields := gateTokenFields (a:=a) (b:=b) (op:=op) (keep:=k) (by omega) (by omega) hk
  obtain ⟨kE,oE,aE,bE⟩ := fields
  have nop : op ≠ 2 := by omega
  have output : (if op == 0 then x &&& y else if op == 1 then x ||| y else m ^^^ x) = z := by
    rcases (show op=0 ∨ op=1 by omega) with rfl|rfl <;> rfl
  have cell : childState m (gateToken a b op k) (fuel,ws,history) =
      (if fuel == 0 then none else if z == 0 || z == m || ws.contains z then none else
        some (fuel-1,insertWord z rest,(z,x,y)::history)) := by
    simp only [childState,kE,oE,aE,bE,show ¬ b≥ws.length by omega,decide_false,
      show ¬ a≥b by omega,nop,beq_eq_false_iff_ne.mpr nop,Bool.false_eq_true,
      ↓reduceIte,Bool.or_false,Bool.false_or]
    change (if fuel == 0 then none else
      if _ then none else some _) = _
    simp only [← output,z,x,y,rest,kept,keepWord,nop, Bool.false_or,beq_eq_false_iff_ne.mpr nop]
  rw [pass,cell]
  by_cases dead : fuel = 0
  · simp [dead]
  rw [if_neg (show ¬ (fuel == 0) = true by simpa using dead)]
  by_cases stale : (z == 0 || z == m || ws.contains z) = true
  · rw [if_pos stale]
  rw [if_neg stale]
  have all' := (Bool.or_eq_true_iff.mp all).resolve_left (by simpa using dead)
  have A := treeBlock_at all' (i:=a) (by omega) (by simpa using ha)
  have B := treeBlock_at A (i:=b) (by omega) (by omega)
  have O := treeBlock_at B (i:=op) (by omega) (by simpa using ho)
  change ((z == 0 || z == m || ws.contains z) || treeBlock 0 4 _) = true at O
  have K := treeBlock_at ((Bool.or_eq_true_iff.mp O).resolve_left stale) (i:=k) (by omega) (by simpa using hk)
  rw [getTag _ _ _ ha,getTag _ _ _ hb] at K
  change (decide (fuel-1+1 < rest.length+1) ||
    (combined (without x y ws (ws.map (tag g ns))) (tag g ns x) (tag g ns y) (tag g ns z) k != wanted g ns)
    || finish (gateToken a b op k) (fuel-1,insertWord z rest,(z,x,y)::history)) = true at K
  let c : RowState := (fuel-1,insertWord z rest,(z,x,y)::history)
  change (basicCut g ns c || cut i _ c || dagRef count bank moves lk i _ c) = true
  by_cases closed : basicCut g ns c = true
  · simp [closed]
  have openC : basicCut g ns c = false := Bool.eq_false_iff.mpr closed
  simp only [basicCut,Bool.or_eq_false_iff,decide_eq_false_iff_not,List.any_eq_false,bne_iff_ne,
    Bool.not_eq_true',bne_eq_false_iff_eq] at openC
  have len : ¬fuel-1+1 < rest.length+1 := by
    have l := openC.1
    change ¬fuel-1+1 < (insertWord z rest).length at l
    rwa [insertLength] at l
  have pack := pack_good g ns c.2.1 (by intro n hn; simpa using openC.2 n hn)
  have memx : x ∈ ws := by dsimp [x]; rw [List.getD_eq_getElem _ _ ha];exact List.getElem_mem _
  have memy : y ∈ ws := by dsimp [y]; rw [List.getD_eq_getElem _ _ hb];exact List.getElem_mem _
  have ne : x ≠ y := by
    unfold x y
    rw [List.getD_eq_getElem _ _ ha,List.getD_eq_getElem _ _ hb]
    intro eq
    have eqidx := nd.getElem_inj.mp eq
    omega
  change unionTags (tag g ns) (insertWord z (kept ws x y k)) = _ at pack
  rw [childTags _ ws x y z k nd memx memy ne] at pack
  have good := sound _ c (by simpa [len,pack] using K)
  simpa [Bool.eq_false_iff.mpr closed] using good

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem fastCheck_sound {bank : Table} {count : Nat} {moves : Array WordMove} {ms : Array Minor}
    {hullAt : Nat → Nat} {ad : Nat → Nat → Nat} {i : Nat}
    (ok : fastCheckWith bank count moves ms hullAt ad i = true) :
    scan (fullMask 25) T diagonal bank count moves (fun j t => linkCode (ad j t))
      (geometryOrMinor ms (fun j t => hintCode hullAt (ad j t))) i = true := by
  cases hr : bank i with
  | none => simp [fastCheckWith,hr] at ok
  | some s =>
    simp only [fastCheckWith,hr] at ok
    have top := ok
    simp only [direct,forceList_eq,forceN_eq,Bool.and_eq_true] at top
    simp only [scan,hr,Bool.and_eq_true]
    refine ⟨top.1,block_of fun a _ ha => block_of fun b hb hb' => block_of fun op _ hop => block_of fun k _ hk => ?_⟩
    apply direct_pass ok _ (by omega) (by omega) (by omega) (by omega)
    intro tok c hit
    simp only [dispatch,forceN_eq] at hit
    split at hit
    · apply Bool.or_eq_true_iff.mpr (Or.inr ?_)
      exact hit
    · apply Bool.or_eq_true_iff.mpr (Or.inl ?_)
      exact hit

end Rep9102.Fast
open WordEngine
namespace Rep9102.Fast.Packed
open Orbit Project Final9102
abbrev SlotTable := Nat × Nat × Nat

def entry (q : Minor) (t : SlotTable) (j : Nat) : Nat :=
  forceN (unpack t.2.2 7 j) fun code =>
    if code = 0 then 0 else
      4 * ((unpack 0x3ff0001f84210fa10847c84213e21085f08421f83e007c00f83e0003f8c6318a5294a4a5294a318c630fc210843f084210fc210843f0000006318c6294a529294a528fa108423e842108fa108423e800000318c6314a52949f2108427c842109f2108427c800000318c6317c421085f1084217c421085f10000007e108421f8421087e108421f84000001ff8000f83e007c00f8200000080000020000008000002000000ffc0007c1f00200000080000020000008000002000000ffc00040000010000004000001000000400000100000040000010000004000001084210c2108410842104210841084217c000001f0000007c000001f0000007ffffffe000000 25 (code-1)) &&& q.mask) + (if code ≤ 12 then 1 else 2)

def index (t : SlotTable) (v : Nat) := (v ^^^ (v >>> t.2.1)) % t.1

def validSlot (q : Minor) (e : Nat) :=
  let v := e/4
  if e % 4=1 then availableB q.mask q.raw v
  else if e % 4=2 then !(availableB q.mask q.raw v) && oneAO q.raw v else true

def validSlots (q : Minor) (t : SlotTable) :=
  t.1 != 0 && treeBlock 0 t.1 (fun j => validSlot q (entry q t j))

def tagLookup (q : Minor) (t : SlotTable) (v : Nat) := forceN (entry q t (index t v)) fun e =>
  if e/4 == v then e % 4 else 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem tagSpec (q : Minor) (t : SlotTable) (valid : validSlots q t = true) (v : Word) :
    (tagLookup q t v = 1 → availableB q.mask q.raw v = true) ∧
    (tagLookup q t v = 2 → availableB q.mask q.raw v = false ∧ oneAO q.raw v = true) := by
  obtain ⟨pos,cells⟩ := Bool.and_eq_true_iff.mp valid
  have ne : t.1 ≠ 0 := by simpa using pos
  have cell := treeBlock_at cells (i:=index t v) (Nat.zero_le _) (by simpa [index] using Nat.mod_lt (v ^^^ (v >>> t.2.1)) (Nat.pos_of_ne_zero ne))
  let e := entry q t (index t v)
  change validSlot q e = true at cell
  simp only [tagLookup,forceN_eq]
  change ((if e/4 == v then e % 4 else 0) = 1 → _) ∧ ((if e/4 == v then e % 4 else 0) = 2 → _)
  by_cases hv : e/4=v
  · simp only [hv,beq_self_eq_true,↓reduceIte]
    constructor
    · intro h; simpa [validSlot,h,hv] using cell
    · intro h; simpa [validSlot,h,hv] using cell
  · simp [hv]

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem oneWeaken (base extra : List Word) (v : Word) (h : oneAO base v = true) :
    oneAO (extra++base) v = true := by
  obtain ⟨a,ha,y⟩ := List.any_eq_true.mp h
  obtain ⟨b,hb,test⟩ := List.any_eq_true.mp y
  exact List.any_eq_true.mpr ⟨a,List.mem_append_right _ ha,List.any_eq_true.mpr
    ⟨b,List.mem_append_right _ hb,test⟩⟩

def fastPrep (q : Minor) (t : SlotTable) (extra : List Word) : List Word → Option (List Word)
  | [] => some []
  | w::ws => forceN (tagLookup q t w) fun kind =>
    if (kind == 1) || extra.contains w || ((kind != 2) && availableB q.mask q.raw w) then fastPrep q t extra ws
    else if kind == 2 || oneAO (extra++q.raw) w then (fastPrep q t (w::extra) ws).map (w::·)
    else none

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem fastPrep_eq (q : Minor) (t : SlotTable) (valid : validSlots q t = true) (extra ws : List Word) :
    fastPrep q t extra ws = cheapPrep q.mask (extra++q.raw) ws := by
  induction ws generalizing extra with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨free,one⟩ := tagSpec q t valid w
    let k := tagLookup q t w
    have avail : ((k == 1) || extra.contains w || ((k != 2) && availableB q.mask q.raw w)) =
        availableB q.mask (extra++q.raw) w := by
      have ext : availableB q.mask (extra++q.raw) w = (extra.contains w || availableB q.mask q.raw w) := by
        simp [availableB,List.contains_append,Bool.or_comm,Bool.or_left_comm,Bool.or_assoc]
      rw [ext]
      by_cases h : k=1
      · simp [h,free h]
      by_cases h' : k=2
      · simp [h,h',(one h').1]
      · simp [beq_eq_false_iff_ne.mpr h,show (k != 2) = true by simpa using h']
    have gate : ((k == 2) || oneAO (extra++q.raw) w) = oneAO (extra++q.raw) w := by
      by_cases h : k=2
      · simp [h,oneWeaken _ _ _ (one h).2]
      · simp [h]
    simp only [fastPrep,cheapPrep,forceN_eq]
    change (if _ then _ else if _ then _ else _) = _
    rw [show tagLookup q t w = k from rfl,avail,gate,ih extra,ih (w::extra)]
    rfl

def usingCache (q : Minor) (t : SlotTable) (fuel : Nat) (ws : List Word) : Bool :=
  match fastPrep q t [] (ws.map (· &&& q.mask)) with
  | none => false
  | some adds => decide (adds.length+fuel < q.low+flatCount q.mask ws)

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem usingCache_eq (q : Minor) (t : SlotTable) (h : validSlots q t = true) (fuel : Nat) (ws : List Word) :
    usingCache q t fuel ws = cheapCut q.mask q.low fuel q.raw ws := by
  simp [usingCache,cheapCut,fastPrep_eq q t h]

end Rep9102.Fast.Packed
open WordEngine

namespace Rep9102.Fast.Packed

open Orbit Project Final9102



def cache0 : SlotTable := (281,5,0x74080000000000000031500000000001a80000000a00000002c000000000000010800062000000000000000000016f400000000000000c000000000000000000a0000000000001240000001c00000003000000048a0170000d000c3a0003b00000250000000000004300019800000b800000ca07c980050000000000001400000000024000000000000000000118000000000000000006c0000054020000001e2d0000000000002b00000000000000000001f0000048004c000100000000bc000000000000000000110000000000000a401c00fc900060002300000000078000006db9148880000000d10420238f0038681)
def cache1 : SlotTable := (319,18,0x37000000000000000001f800000000000000000000005e000000000000900004f9c0001a5a0000000000000000015002000000000400002347000000000000009a000000000000000170054000000000db900000000000000000000000000000e780000074b0000004800000033000000200024800128051000000001100000a00000000000000000008601400000000000000000000000006610000a4014180003800f8000002c000380208000000320000000000000000000340001d800000000000003500e8000000000000000000000000305c01300c4000140000000b000000000000000000992c0000000000080001206000004f4000000000000000011000000000000100001e0f0038681)
def cache2 : SlotTable := (305,15,0xdc041000004a000000000000007e0000000000205a940000000000000001501143805c0218000024000000000002000000000004200000000000000000000000000000000000000402c00000000000000cc0000002300000030000000000000000000004b00ac000120000000000297600000609113e00000000139400014003900000000002900007c0000001b140000000000003418000000000000920001700000380000000000000000000000002100000000000000000000200002c0320001e800000013000003a0000000000003100026809e000000000000a20052c0000012060010000000000000000009c011000000000011908e0000f0038681)
def cache3 : SlotTable := (333,5,0x33000060000026000080400000000000018800001780420048000900000001bba00000000001c0000000000000000000110000005510cc1b007a01f008a000000001f80012803c0070000000000000020000000000000001a000000000000420e00000000118000000000000580000000000023000000000000238000b0000000000000000006a024000148000000000000000003e0004100000004c0004f0000000000248000000000000e800000000000000036000000134000006400000000000000000001402b0000000000138000000000000100000000000e680000000000000000000000000022000000c000000000000000000000000000000640150000000000600000000000000a0000000271100016800000010000000f0038681)
def cache4 : SlotTable := (307,8,0x100011000000000000000000000000000000000000027000004c00000000e0000000000000000ad1000000000000290a01600006c0000000000000000000003000000000000000000000000065a8000000002c0000000000000000000000000000000219e0000064023000000e00000000000000000001300000000000c40341800000000000000000000000000008c000000000056f4f1400000000000d4779040005c000000000050300000000bc00000d8000008000000000000000000000000000000000011dc300011000000013000293e7200000000000000000003e9400001380009200000012d8128a00000002c0000001500800000000005000121c000025f8010de681)
def cache5 : SlotTable := (350,8,0x7c0000080000000188000840000000018000003800000000088035780000096000000065200a0000008000000000000000180000000000000000000000000000000000000000d800000680000000a80000000000000000000000760000000bc000500000000006006601580009c0006800009000003e000000000000000000000000000095380000000032000000000000070000000006c0000000000000000000000000001e800000000000000000000170000000000000000000000800014000004c000000000000000000000000000800016800002680000000000b0000000003a3c0000014000007e00000000000000a4000013d5130000000000003000000000000000000000000000006e000000148012000000000e40000000005000800006017263a00010000000f4a38681)
def cache6 : SlotTable := (344,19,0xb80000000018000000000000190091b0000000000000000000001a00000000000300013000000000000000034000000000000000000000000000000021800000000000003200000000000002000000000000000000000013c00000000000000000a20000001180000000035000001c0000000000001e6e000000000000000140052000009abd88000000003a00000180002000000000000016000000000000050000000000250000000000000000601e4000000000000002c00000148f2c00000013000108000000058000000000000000a40000000000000000000000001f00000000000000000000000000002e00000009c01300000000002200000000000ac00466000000002280000000000e119200000095a00041060004e0000011002000000012a1000000f5438681)
def cache7 : SlotTable := (339,17,0xec000000000050f0000011c000000060000000000090000a20000000000001000000000002d00000000c000000001880000000000000000000000000000000000000000000000001500000490000000a00004e0002580000000001040000000000000001f0000000000001d0000bba000000000000000000000008c5000000000000028000100000e0000000000000000b000000000000002a7d28000000000000000000000045000000000c13005e94029a4000440000000000000000000000001c8000b001c000104d0000000000000044000000000000000000000b8000000000000000000000000000004301080130000000000139b160000000f558000000000000000000231e00026120001f800600000000000000080110064000000001030000000038681)
def cache8 : SlotTable := (347,9,0x973d48000000240000018000000000c802200000000000000011a20000000000c01c8000011800000000000003c0000000340000000000000000000000000000000005600000825c0000a000154e013000000000000003d000001d000000008000000002280360000000cc0007c00000007c48000000000000000000288000000000000000000000000001000000000000000000000000108028005804300840001600000694000000000000000000013000c000250000000000000014000000000000000000000a40000000d40073800000000000000000000000000000000000000003c0000014000007602480000003a000000000000000000000000000000000004a00000000004d00000400000012000018000024000000000000001100000006c0001000dc00f5400681)
def cache9 : SlotTable := (187,9,0x640410000d00000000090bc034360000000000000144002011c000840000038027004c01e002c785804a000000001b1400000007600000000002c00000050000022a00000000000000001700000000000e40529475f80973c000000000000000000110a8a0000013000120000e839700840000114000980193300024bd00016800025a800c0d180401004300018400000411000000000e0010000000f0038001)
def cache10 : SlotTable := (166,13,0x2e00000000000000000000001b8400000004c0002000954000001f801801794000003600e000000f8000008401a00000000000000007400000000080001680005428000000007801480800000000000003c7c0000000013008988036e80190018500560800076d12000000000000198000000120001e98002402a0000000000000006b800000c0010000000f6a38681)
def cache11 : SlotTable := (241,10,0x530400000000000000000000002e0000000000220000000003c000000000000000004f001400000d000000000000000000000003200000003a0000000000000000000000004c000000000a8000000800000000000000000000000000000000000014000000000640000000000000000000bc000000288000e00009000000012800000b00006601bcb0000000000000000000000e0000900023930000c0000000005a00000620004600013809a00000510801700200121658000000000006d400000006119d0c21c0000000000000f3438681)
def cache12 : SlotTable := (191,8,0xe40000002080000000000a0000a400000000010000f9100000000000000000001e8c00ac00000b00000000000011639646b40000000017000000000024809c00000012c000000040008000000000000a200000000002000021000000000002c03b00000004e01200005401300c6680600003a0000000a002180000001f001800014000008d28012000000006a4000000000000000114afc00000b80100e000000038681)
def cache13 : SlotTable := (213,7,0xa8009010800014000000101b80000058000d8000000000092000187a0000000e558001300000000000006c0000000045000000000024000000023000002600000008201e00000010000000000000e800000000000000038000050000035a20000000000000000044a13400064000000000d0000012004f280220000000000002800000000000000000000c000000600003807c00000000002100000460000180000000000000330000011000004f7400f90a40000f0000681)
def cache14 : SlotTable := (197,2,0x193400d800000e006c0000098000000000000000000000027800001045000001400b000000000000001300000003c0002200008c0004aed080000000000d40002b38000640000000b805100000050cfc00096000000000f490000000000000000000000105a1300000000e0000004f5100014000b0000000000000000000005e00b4000000008601cd20000000000000a00000040000038011c00000000099000000000000800018000000001)
def cacheOf : Nat → SlotTable
  | 0 => cache0
  | 1 => cache1
  | 2 => cache2
  | 3 => cache3
  | 4 => cache4
  | 5 => cache5
  | 6 => cache6
  | 7 => cache7
  | 8 => cache8
  | 9 => cache9
  | 10 => cache10
  | 11 => cache11
  | 12 => cache12
  | 13 => cache13
  | 14 => cache14
  | _ => (1,0,0)

def cachedMinor (idx : Nat) (s : RowState) :=
  match minors[idx]? with
  | none => false
  | some q => usingCache q (cacheOf idx) s.1 s.2.1

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cachesValid : treeBlock 0 minors.size (fun i => (minors[i]?).all fun q => validSlots q (cacheOf i)) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cachedMinor_eq (idx : Nat) (s : RowState) : cachedMinor idx s =
    (match minors[idx]? with | none => false | some q => cheapCut q.mask q.low s.1 q.raw s.2.1) := by
  unfold cachedMinor
  cases h : minors[idx]? with
  | none => rfl
  | some q =>
    have lt : idx < minors.size := (Array.getElem?_eq_some_iff.mp h).1
    have ok := treeBlock_at cachesValid (i:=idx) (Nat.zero_le idx) (by simpa using lt)
    simp [h] at ok
    exact usingCache_eq q _ ok _ _


end Rep9102.Fast.Packed
open WordEngine
namespace Rep9102.Fast.Packed
open Orbit Project Final9102

def cachedDispatch (bank : Table) (ad : Nat → Nat → Nat) (i tok : Nat) (s : RowState) :=
  forceN (ad i tok) fun c =>
    if c % 2=1 then dagRef 1749 bank (dagMoves records) (fun _ _ => linkCode c) i tok s
    else if c/2 < 16 then cachedMinor (c/2) s
    else Geometry.rectangleReject T s (hull (c/2-16))

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cachedDispatch_eq (bank : Table) (ad : Nat → Nat → Nat) (i tok : Nat) (s : RowState) :
    cachedDispatch bank ad i tok s = dispatch bank 1749 (dagMoves records) minors hull ad i tok s := by
  simp only [cachedDispatch,dispatch,forceN_eq]
  split
  · rfl
  · rename_i even
    split
    · rename_i small
      simp [geometryOrMinor,hintCode,even,small,cachedMinor_eq,bankCut]
    · rename_i big
      simp [geometryOrMinor,hintCode,even,big]

def cachedScan (bank : Table) (ad : Nat → Nat → Nat) (i : Nat) :=
  match bank i with
  | none => false
  | some s => direct (fullMask 25) T diagonal i s (cachedDispatch bank ad i)

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem cachedScan_eq (bank : Table) (ad : Nat → Nat → Nat) (i : Nat) :
    cachedScan bank ad i = fastCheckWith bank 1749 (dagMoves records) minors hull ad i := by
  simp only [cachedScan,fastCheckWith]
  cases bank i with
  | none => rfl
  | some s => exact congrArg (direct (fullMask 25) T diagonal i s) (funext fun tok => funext fun c => cachedDispatch_eq bank ad i tok c)

def cachedCompact := cachedScan compactStates compactAdvice

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem compact_from_cached {start count} (h : treeBlock start count cachedCompact = true) :
    treeBlock start count compactCheck = true := by
  apply block_of
  intro i lo hi
  have v := treeBlock_at h lo hi
  rw [cachedCompact,cachedScan_eq] at v
  exact fastCheck_sound v

end Rep9102.Fast.Packed
namespace Rep9102.Final9102
open Orbit Project
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem valid : ∀ q ∈ minors, Minor.Valid T q := validCuts masks (by decide +kernel) (by decide +kernel)
private theorem halves {s n : Nat} {p : Nat → Bool}
    (left : treeBlock s (n / 2) p = true)
    (right : treeBlock (s + n / 2) (n - n / 2) p = true) :
    treeBlock s n p = true := by
  have h := treeBlock_merge left right
  simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using h

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem scanned : treeBlock 0 1749 Fast.Packed.cachedCompact = true := by
  iterate 7 all_goals apply halves
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem completed : ¬ RepSizeAtMost posted 14 := by
  apply lowerFromTable (root := 0) (s := (14,[31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[])) autos (geometryOrMinor_open valid)
    (fun i hi => treeBlock_at (Fast.Packed.compact_from_cached scanned) (Nat.zero_le i) (by simpa using hi))
  · decide +kernel
  · decide +kernel
  · rfl
  · decide +kernel
end Rep9102.Final9102
theorem baseFive : ∀ s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide (u ≠ v)) s → 15 ≤ s := by
  rintro s ⟨C, hmono, hs, hrep⟩
  by_contra small
  exact PEqualNP.Outside.L_meta_18163_aux.Five.Rep9102.Final9102.completed ⟨C, hmono, by omega, hrep⟩

end PEqualNP.Outside.L_meta_18163_aux.Five

namespace PEqualNP.Outside.L_meta_18163_aux.Reduction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)

def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false

def fok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_prefix _ _ _ _ (h t rfl)

theorem emit (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, fok g → (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · simp at hl

theorem engine3 {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + F.card ≤ C.size ∧ ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega

      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, h2, fun x => ?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have := hev x
      rw [hm] at this
      exact this.symm

def rd (A B : ℕ → ℕ) (k w : ℕ) : Prop := A k = w ∨ B k = w

def pt (n u v : ℕ) : ℕ → Bool := fun k => decide (k = u ∨ k = n + v)

def Tg (n m : ℕ) (A B : ℕ → ℕ) (An : ℕ → Bool) (i j : ℕ) : Prop :=
  i < n ∧ j < m ∧ An j = false ∧ ((A j = i ∧ B j = n + i) ∨ (A j = n + i ∧ B j = i)) ∧
    ∀ k < m, (rd A B k i ∨ rd A B k (n + i)) → k = j

def Kill (n : ℕ) (V : (ℕ → Bool) → ℕ → Bool) (i j : ℕ) : Prop :=
  (∃ b, ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) (n + n + j) = b) ∨
    ∃ w < n + n + j, ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) (n + n + j) = V (pt n u v) w

theorem core (n : ℕ) (hn : 3 ≤ n) (m : ℕ) (A B : ℕ → ℕ) (An : ℕ → Bool) (V : (ℕ → Bool) → ℕ → Bool) (o : ℕ)
    (hA : ∀ j < m, A j < n + n + j) (hB : ∀ j < m, B j < n + n + j) (hAB : ∀ j < m, A j ≠ B j)
    (v0 : ∀ P k, k < n + n → V P k = P k)
    (v1 : ∀ P j, j < m → V P (n + n + j) = if An j = true then V P (A j) && V P (B j) else V P (A j) || V P (B j))
    (ho : o < n + n + m)
    (hf : ∀ u v, u < n → v < n → V (pt n u v) o = decide (u ≠ v))
    (irr : ∀ j < m, ∀ w < n + n + j, ¬∀ u v, u < n → v < n → V (pt n u v) (n + n + j) = V (pt n u v) w) :
    ∃ i < n, ∃ a b c, a < m ∧ b < m ∧ c < m ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Kill n V i a ∧ Kill n V i b ∧ Kill n V i c := by
  classical

  have mono : ∀ (P Q : ℕ → Bool), (∀ k, P k = true → Q k = true) → ∀ w < n + n + m, V P w = true → V Q w = true := by
    intro P Q hPQ w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw h
      by_cases hwn : w < n + n
      · rw [v0 _ _ hwn] at h ⊢; exact hPQ _ h
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + n + j := ⟨w - (n + n), by omega⟩
        have hj : j < m := by omega
        have a1 := hA j hj
        have b1 := hB j hj
        rw [v1 _ _ hj] at h ⊢
        split_ifs at h ⊢ with hAn
        · rw [Bool.and_eq_true] at h ⊢
          exact ⟨ih _ a1 (by omega) h.1, ih _ b1 (by omega) h.2⟩
        · rw [Bool.or_eq_true] at h ⊢
          exact h.imp (ih _ a1 (by omega)) (ih _ b1 (by omega))

  have rep : ∀ (Hd : ℕ → Prop) (P Q : ℕ → Bool), (∀ k < n + n, ¬Hd k → P k = Q k) →
      (∀ j < m, ¬Hd (n + n + j) → (Hd (A j) ∨ Hd (B j)) → V P (n + n + j) = V Q (n + n + j)) →
      ∀ w < n + n + m, ¬Hd w → V P w = V Q w := by
    intro Hd P Q h1 h2 w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hH
      by_cases hwn : w < n + n
      · rw [v0 _ _ hwn, v0 _ _ hwn]; exact h1 _ hwn hH
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + n + j := ⟨w - (n + n), by omega⟩
        have hj : j < m := by omega
        have a1 := hA j hj
        have b1 := hB j hj
        by_cases hr : Hd (A j) ∨ Hd (B j)
        · exact h2 j hj hH hr
        · rw [not_or] at hr
          rw [v1 _ _ hj, v1 _ _ hj, ih _ a1 (by omega) hr.1, ih _ b1 (by omega) hr.2]

  have row1 : ∀ u < n, V (fun k => decide (k = u)) o = false := by
    intro u hu
    by_contra h
    have h1 := mono (fun k => decide (k = u)) (pt n u u) (by
      intro k hk
      have : k = u := by simpa using hk
      simp [pt, this]) o ho (by simpa using h)
    rw [hf u u hu hu] at h1
    simp at h1
  have col1 : ∀ v < n, V (fun k => decide (k = n + v)) o = false := by
    intro v hv
    by_contra h
    have h1 := mono (fun k => decide (k = n + v)) (pt n v v) (by
      intro k hk
      have : k = n + v := by simpa using hk
      simp [pt, this]) o ho (by simpa using h)
    rw [hf v v hv hv] at h1
    simp at h1

  obtain ⟨jo, hjo, rfl⟩ : ∃ jo, jo < m ∧ o = n + n + jo := by
    by_cases h : o < n + n
    · exfalso
      by_cases h2 : o < n
      · have := hf o o h2 h2
        rw [v0 _ _ h] at this
        simp [pt] at this
      · have := hf (o - n) (o - n) (by omega) (by omega)
        rw [v0 _ _ h] at this
        have e : o = n + (o - n) := by omega
        simp only [pt, ← e] at this
        simp at this
    · exact ⟨o - (n + n), by omega, by omega⟩

  let Z : ℕ → ℕ → Prop := fun i w => ∀ u v, u < n → v < n → u ≠ i → v ≠ i → V (pt n u v) w = false
  have zr : ∀ i < n, Z i i := by
    intro i hi u v hu hv hui hvi
    rw [v0 _ _ (by omega)]
    simp only [pt, decide_eq_false_iff_not, not_or]
    omega
  have zc : ∀ i < n, Z i (n + i) := by
    intro i hi u v hu hv hui hvi
    rw [v0 _ _ (by omega)]
    simp only [pt, decide_eq_false_iff_not, not_or]
    omega
  have kr : ∀ i j w, j < m → rd A B j w → Z i w → Kill n V i j := by
    intro i j w hj hr hz
    have a1 := hA j hj
    have b1 := hB j hj
    by_cases hAn : An j = true
    · left
      refine ⟨false, fun u v hu hv hui hvi => ?_⟩
      rw [v1 _ _ hj, if_pos hAn]
      rcases hr with rfl | rfl
      · rw [hz u v hu hv hui hvi]; rfl
      · rw [hz u v hu hv hui hvi, Bool.and_false]
    · right
      rcases hr with rfl | rfl
      · refine ⟨B j, b1, fun u v hu hv hui hvi => ?_⟩
        rw [v1 _ _ hj, if_neg hAn, hz u v hu hv hui hvi, Bool.false_or]
      · refine ⟨A j, a1, fun u v hu hv hui hvi => ?_⟩
        rw [v1 _ _ hj, if_neg hAn, hz u v hu hv hui hvi, Bool.or_false]
  have zor : ∀ i j, j < m → An j = false → Z i (A j) → Z i (B j) → Z i (n + n + j) := by
    intro i j hj hAn h1 h2 u v hu hv hui hvi
    rw [v1 _ _ hj, if_neg (by simp [hAn]), h1 u v hu hv hui hvi, h2 u v hu hv hui hvi]; rfl

  have orii : ∀ i j, i < n → j < m → An j = false → (rd A B j i ∨ rd A B j (n + i)) → V (pt n i i) (n + n + j) = true := by
    intro i j hi hj hAn hr
    have p1 : V (pt n i i) i = true := by rw [v0 _ _ (by omega)]; simp [pt]
    have p2 : V (pt n i i) (n + i) = true := by rw [v0 _ _ (by omega)]; simp [pt]
    rw [v1 _ _ hj, if_neg (by simp [hAn]), Bool.or_eq_true]
    rcases hr with (h | h) | (h | h)
    · exact Or.inl (by rw [h]; exact p1)
    · exact Or.inr (by rw [h]; exact p1)
    · exact Or.inl (by rw [h]; exact p2)
    · exact Or.inr (by rw [h]; exact p2)
  have notout : ∀ i j, i < n → j < m → An j = false → (rd A B j i ∨ rd A B j (n + i)) → j ≠ jo := by
    rintro i j hi hj hAn hr rfl
    have h1 := orii i j hi hj hAn hr
    rw [hf i i hi hi] at h1
    simp at h1

  have seesC : ∀ i < n, ∃ P Q : ℕ → Bool, (∀ k, k ≠ n + i → P k = Q k) ∧ P i = false ∧ Q i = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo) := by
    intro i hi
    obtain ⟨u, hu, hui⟩ : ∃ u < n, u ≠ i := by
      by_cases h : i = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    refine ⟨pt n u i, fun k => decide (k = u), ?_, ?_, ?_, ?_⟩
    · intro k hk; simp [pt, hk]
    · simp only [pt, decide_eq_false_iff_not, not_or]; omega
    · simp only [decide_eq_false_iff_not]; omega
    · rw [hf u i hu hi, row1 u hu]; simp [hui]
  have seesR : ∀ i < n, ∃ P Q : ℕ → Bool, (∀ k, k ≠ i → P k = Q k) ∧ P (n + i) = false ∧ Q (n + i) = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo) := by
    intro i hi
    obtain ⟨v, hv, hvi⟩ : ∃ v < n, v ≠ i := by
      by_cases h : i = 0
      · exact ⟨1, by omega, by omega⟩
      · exact ⟨0, by omega, by omega⟩
    refine ⟨pt n i v, fun k => decide (k = n + v), ?_, ?_, ?_, ?_⟩
    · intro k hk; simp [pt, hk]
    · simp only [pt, decide_eq_false_iff_not, not_or]; omega
    · simp only [decide_eq_false_iff_not]; omega
    · rw [hf i v hi hv, col1 v hv]; simp [Ne.symm hvi]

  have raw : ∀ (i x y h g : ℕ), i < n → ((x = i ∧ y = n + i) ∨ (x = n + i ∧ y = i)) → h < m → g < m → h ≠ g → rd A B h x → rd A B g x →
      (∀ a, rd A B h a → a < n + n ∨ ∃ i' j, a = n + n + j ∧ Tg n m A B An i' j) →
      (∃ P Q : ℕ → Bool, (∀ k, k ≠ y → P k = Q k) ∧ P x = false ∧ Q x = false ∧ V P (n + n + jo) ≠ V Q (n + n + jo)) →
      ∃ i < n, ∃ a b c, a < m ∧ b < m ∧ c < m ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ Kill n V i a ∧ Kill n V i b ∧ Kill n V i c := by
    intro i x y h g hi hxy hh hg hhg rhx rgx hat hsee
    have zx : Z i x := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> [exact zr _ hi; exact zc _ hi]
    have zy : Z i y := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> [exact zc _ hi; exact zr _ hi]
    have hxN : x < n + n := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    have hyN : y < n + n := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
    have hne : x ≠ y := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    by_cases h3 : ∃ k < m, (rd A B k x ∨ rd A B k y) ∧ k ≠ h ∧ k ≠ g
    · obtain ⟨k, hk, hr, k1, k2⟩ := h3
      refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, Ne.symm k1, Ne.symm k2, kr i h x hh rhx zx, kr i g x hg rgx zx, ?_⟩
      exact hr.elim (fun r => kr i k x hk r zx) (fun r => kr i k y hk r zy)
    push Not at h3
    have only : ∀ k < m, (rd A B k x ∨ rd A B k y) → k = h ∨ k = g := by
      intro k hk hr
      by_contra hc
      rw [not_or] at hc
      exact hc.2 (h3 k hk hr hc.1)
    obtain ⟨P, Q, pq, px, qx, hdiff⟩ := hsee

    have both : ∀ k < m, rd A B k x → rd A B k y → (A k = x ∧ B k = y) ∨ (A k = y ∧ B k = x) := by
      intro k _ h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact absurd (h1.symm.trans h2) hne
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact absurd (h1.symm.trans h2) hne
    have andv : ∀ k < m, An k = true → rd A B k x → ∀ W : ℕ → Bool, W x = false → V W (n + n + k) = false := by
      intro k hk hAn hr W hW
      rw [v1 _ _ hk, if_pos hAn]
      rcases hr with hr | hr
      · rw [hr, v0 _ _ hxN, hW]; rfl
      · rw [hr, v0 _ _ hxN, hW, Bool.and_false]
    have orxy : ∀ k < m, An k = false → (rd A B k x ∧ rd A B k y) → k ≠ jo := by
      intro k hk hAn hr
      refine notout i k hi hk hAn ?_
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hr.1
      · exact Or.inl hr.2
    have zgate : ∀ k < m, An k = false → rd A B k x → rd A B k y → Z i (n + n + k) := by
      intro k hk hAn r1 r2
      rcases both k hk r1 r2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact zor i k hk hAn (by rw [e1]; exact zx) (by rw [e2]; exact zy)
      · exact zor i k hk hAn (by rw [e1]; exact zy) (by rw [e2]; exact zx)
    by_cases rhy : rd A B h y
    · by_cases rgy : rd A B g y
      ·
        have hops : An h ≠ An g := by
          intro e
          have same : ∀ W, V W (n + n + h) = V W (n + n + g) := by
            intro W
            rw [v1 _ _ hh, v1 _ _ hg, e]
            rcases both h hh rhx rhy with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases both g hg rgx rgy with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;> rw [e1, e2, e3, e4] <;>
              cases V W x <;> cases V W y <;> cases An g <;> rfl
          rcases Nat.lt_or_gt_of_ne hhg with hlt | hlt
          · exact irr g hg (n + n + h) (by omega) fun u v _ _ => (same _).symm
          · exact irr h hh (n + n + g) (by omega) fun u v _ _ => same _
        obtain ⟨p, q, hp, hq, hpq, pAn, qAn, rpx, rpy, rqx, rqy, hset⟩ : ∃ p q, p < m ∧ q < m ∧ p ≠ q ∧ An p = false ∧ An q = true ∧ rd A B p x ∧ rd A B p y ∧ rd A B q x ∧ rd A B q y ∧ (∀ k, k = h ∨ k = g → k = p ∨ k = q) := by
          cases e1 : An h with
          | false =>
            have e2 : An g = true := by
              cases e2 : An g with
              | true => rfl
              | false => exact absurd (e1.trans e2.symm) hops
            exact ⟨h, g, hh, hg, hhg, e1, e2, rhx, rhy, rgx, rgy, fun k hk => hk⟩
          | true =>
            have e2 : An g = false := by
              cases e2 : An g with
              | false => rfl
              | true => exact absurd (e1.trans e2.symm) hops
            exact ⟨g, h, hg, hh, Ne.symm hhg, e2, e1, rgx, rgy, rhx, rhy, fun k hk => hk.symm⟩
        have hrd : ∃ k < m, rd A B k (n + n + p) := by
          by_contra hno
          push Not at hno
          refine hdiff (rep (fun w => w = y ∨ w = n + n + p) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
          · intro j hj hjH hr
            have hjp : j ≠ p := fun e => hjH (Or.inr (by rw [e]))
            have : rd A B j y := by
              rcases hr with (e | e) | (e | e)
              · exact Or.inl e
              · exact absurd (Or.inl e) (hno j hj)
              · exact Or.inr e
              · exact absurd (Or.inr e) (hno j hj)
            have hjq : j = q := by
              rcases hset j (only j hj (Or.inr this)) with e | e
              · exact absurd e hjp
              · exact e
            subst hjq
            rw [andv j hj qAn rqx P px, andv j hj qAn rqx Q qx]
          · rintro (e | e)
            · omega
            · exact orxy p hp pAn ⟨rpx, rpy⟩ (by omega)
        obtain ⟨k, hk, hr⟩ := hrd
        have ar : ∀ c < m, rd A B c x → rd A B c y → ¬rd A B c (n + n + p) := by
          intro c hc c1 c2 c3
          rcases both c hc c1 c2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases c3 with e3 | e3 <;> omega
        refine ⟨i, hi, p, q, k, hp, hq, hk, hpq, ?_, ?_, kr i p x hp rpx zx, kr i q x hq rqx zx, kr i k _ hk hr (zgate p hp pAn rpx rpy)⟩
        · rintro rfl; exact ar _ hp rpx rpy hr
        · rintro rfl; exact ar _ hq rqx rqy hr
      ·
        have oy : ∀ k < m, rd A B k y → k = h := by
          intro k hk r
          rcases only k hk (Or.inr r) with e | e
          · exact e
          · subst e; exact absurd r rgy
        cases hAn : An h with
        | true =>
          exfalso
          refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
          intro j hj _ hr
          have : j = h := oy j hj hr
          subst this
          rw [andv j hj hAn rhx P px, andv j hj hAn rhx Q qx]
        | false =>
          have hrd : ∃ k < m, rd A B k (n + n + h) := by
            by_contra hno
            push Not at hno
            refine hdiff (rep (fun w => w = y ∨ w = n + n + h) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
            · intro j hj hjH hr
              exfalso
              have : rd A B j y := by
                rcases hr with (e | e) | (e | e)
                · exact Or.inl e
                · exact absurd (Or.inl e) (hno j hj)
                · exact Or.inr e
                · exact absurd (Or.inr e) (hno j hj)
              exact hjH (Or.inr (by rw [oy j hj this]))
            · rintro (e | e)
              · omega
              · exact orxy h hh hAn ⟨rhx, rhy⟩ (by omega)
          by_cases hother : ∃ k < m, rd A B k (n + n + h) ∧ k ≠ g
          · obtain ⟨k, hk, hr, hkg⟩ := hother
            refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, ?_, Ne.symm hkg, kr i h x hh rhx zx, kr i g x hg rgx zx, kr i k _ hk hr (zgate h hh hAn rhx rhy)⟩
            rintro rfl
            have a1 := hA h hh
            have b1 := hB h hh
            rcases hr with e | e <;> omega
          · exfalso
            push Not at hother
            obtain ⟨k, hk, hr⟩ := hrd
            have hkg := hother k hk hr
            subst hkg
            have hhk : h < k := by
              have a1 := hA k hk
              have b1 := hB k hk
              rcases hr with e | e <;> omega
            have ops : (A k = x ∧ B k = n + n + h) ∨ (A k = n + n + h ∧ B k = x) := by
              rcases rgx with e1 | e1 <;> rcases hr with e2 | e2
              · omega
              · exact Or.inl ⟨e1, e2⟩
              · exact Or.inr ⟨e2, e1⟩
              · omega
            have hhv : ∀ W, V W (n + n + h) = (V W x || V W y) := by
              intro W
              rw [v1 _ _ hh, if_neg (by simp [hAn])]
              rcases both h hh rhx rhy with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · rw [e1, e2]
              · rw [e1, e2, Bool.or_comm]
            cases hAk : An k with
            | true =>
              refine irr k hk x (by omega) fun u v _ _ => ?_
              rw [v1 _ _ hk, if_pos hAk]
              rcases ops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, hhv] <;> cases V (pt n u v) x <;> cases V (pt n u v) y <;> rfl
            | false =>
              refine irr k hk (n + n + h) (by omega) fun u v _ _ => ?_
              rw [v1 _ _ hk, if_neg (by simp [hAk])]
              rcases ops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2, hhv] <;> cases V (pt n u v) x <;> cases V (pt n u v) y <;> rfl
    ·
      have oy : ∀ k < m, rd A B k y → k = g := by
        intro k hk r
        rcases only k hk (Or.inr r) with e | e
        · subst e; exact absurd r rhy
        · exact e
      have rgy : rd A B g y := by
        by_contra hno
        refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
        intro j hj _ hr
        exfalso
        have := oy j hj hr
        subst this
        exact hno hr
      cases hAn : An g with
      | true =>
        exfalso
        refine hdiff (rep (fun w => w = y) P Q (fun k _ hk => pq k hk) ?_ _ (by omega) (by omega))
        intro j hj _ hr
        have : j = g := oy j hj hr
        subst this
        rw [andv j hj hAn rgx P px, andv j hj hAn rgx Q qx]
      | false =>
        have hrd : ∃ k < m, rd A B k (n + n + g) := by
          by_contra hno
          push Not at hno
          refine hdiff (rep (fun w => w = y ∨ w = n + n + g) P Q (fun k _ hk => pq k fun e => hk (Or.inl e)) ?_ _ (by omega) ?_)
          · intro j hj hjH hr
            exfalso
            have : rd A B j y := by
              rcases hr with (e | e) | (e | e)
              · exact Or.inl e
              · exact absurd (Or.inl e) (hno j hj)
              · exact Or.inr e
              · exact absurd (Or.inr e) (hno j hj)
            exact hjH (Or.inr (by rw [oy j hj this]))
          · rintro (e | e)
            · omega
            · exact orxy g hg hAn ⟨rgx, rgy⟩ (by omega)
        obtain ⟨k, hk, hr⟩ := hrd
        refine ⟨i, hi, h, g, k, hh, hg, hk, hhg, ?_, ?_, kr i h x hh rhx zx, kr i g x hg rgx zx, kr i k _ hk hr (zgate g hg hAn rgx rgy)⟩
        · rintro rfl
          rcases hat _ hr with e | ⟨i', j, e, hT⟩
          · omega
          · have hjg : j = g := by omega
            subst hjg
            obtain ⟨_, _, _, hops, hex⟩ := hT
            have hx' : x = i' ∨ x = n + i' := by
              rcases hops with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases rgx with e3 | e3 <;> omega
            have : h = j := by
              refine hex h hh ?_
              rcases hx' with rfl | rfl
              · exact Or.inl rhx
              · exact Or.inr rhx
            exact hhg this
        · rintro rfl
          have a1 := hA g hg
          have b1 := hB g hg
          rcases hr with e | e <;> omega
  by_contra hG
  have hexT : ∃ j, j < m ∧ ¬∃ i, Tg n m A B An i j := by
    refine ⟨jo, hjo, ?_⟩
    rintro ⟨i, hi, hj, hAn, hops, _⟩
    refine notout i jo hi hj hAn ?_ rfl
    rcases hops with ⟨e, _⟩ | ⟨_, e⟩
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr e)
  obtain ⟨hh, hhT⟩ := Nat.find_spec hexT
  have hmin : ∀ j, j < Nat.find hexT → ∃ i, Tg n m A B An i j := by
    intro j hj
    by_contra hc
    exact Nat.find_min hexT hj ⟨by omega, hc⟩
  generalize Nat.find hexT = h at hh hhT hmin
  clear hexT
  have hAh := hA h hh
  have hBh := hB h hh
  have hat : ∀ a, rd A B h a → a < n + n ∨ ∃ i' j, a = n + n + j ∧ Tg n m A B An i' j := by
    intro a ha
    by_cases h1 : a < n + n
    · exact Or.inl h1
    · right
      have : a < n + n + h := by rcases ha with e | e <;> omega
      obtain ⟨i, hi⟩ := hmin (a - (n + n)) (by omega)
      exact ⟨i, a - (n + n), by omega, hi⟩
  have Tne : ∀ i j, Tg n m A B An i j → j ≠ h := by
    rintro i j hT rfl
    exact hhT ⟨i, hT⟩
  have Tno : ∀ i j, Tg n m A B An i j → j ≠ jo := by
    rintro i j ⟨hi, hj, hAn, hops, _⟩
    refine notout i j hi hj hAn ?_
    rcases hops with ⟨e, _⟩ | ⟨_, e⟩
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr e)
  have VT : ∀ i j, Tg n m A B An i j → ∀ W : ℕ → Bool, V W (n + n + j) = (W i || W (n + i)) := by
    rintro i j ⟨hi, hj, hAn, hops, _⟩ W
    rw [v1 _ _ hj, if_neg (by simp [hAn])]
    rcases hops with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2, v0 _ _ (by omega), v0 _ _ (by omega)]
    · rw [e1, e2, v0 _ _ (by omega), v0 _ _ (by omega), Bool.or_comm]
  have sole : ∀ a, rd A B h a → ∀ k < m, rd A B k a → k = h := by
    intro a ha k hk hr
    by_contra hkh
    apply hG
    rcases hat a ha with h1 | ⟨i, j, rfl, hT⟩
    · by_cases h2 : a < n
      · exact raw a a (n + a) h k h2 (Or.inl ⟨rfl, rfl⟩) hh hk (Ne.symm hkh) ha hr hat (seesC a h2)
      · have e : a = n + (a - n) := by omega
        exact raw (a - n) a (a - n) h k (by omega) (Or.inr ⟨e, rfl⟩) hh hk (Ne.symm hkh) ha hr hat (by
          have := seesR (a - n) (by omega)
          rwa [← e] at this)
    · obtain ⟨hi, hj, hAn, hops, hex⟩ := hT
      have zA : Z i (A j) := by rcases hops with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> [exact zr i hi; exact zc i hi]
      have zB : Z i (B j) := by rcases hops with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> [exact zc i hi; exact zr i hi]
      have zj := zor i j hj hAn zA zB
      refine ⟨i, hi, j, h, k, hj, hh, hk, Tne i j ⟨hi, hj, hAn, hops, hex⟩, ?_, Ne.symm hkh, kr i j _ hj (Or.inl rfl) zA, kr i h _ hh ha zj, kr i k _ hk hr zj⟩
      rintro rfl
      have a1 := hA j hj
      have b1 := hB j hj
      rcases hr with e | e <;> omega
  have fin : ∀ (Hd : ℕ → Prop) (P Q : ℕ → Bool), (∀ k < n + n, ¬Hd k → P k = Q k) →
      (∀ j < m, ¬Hd (n + n + j) → (Hd (A j) ∨ Hd (B j)) → j = h) → V P (n + n + h) = V Q (n + n + h) → ¬Hd (n + n + jo) →
      V P (n + n + jo) = V Q (n + n + jo) := by
    intro Hd P Q h1 h2 h3 h4
    refine rep Hd P Q h1 (fun j hj hjH hr => ?_) _ (by omega) h4
    rw [h2 j hj hjH hr]; exact h3
  have hVh : ∀ W, V W (n + n + h) = if An h = true then V W (A h) && V W (B h) else V W (A h) || V W (B h) := fun W => v1 W h hh
  have ra : rd A B h (A h) := Or.inl rfl
  have rb : rd A B h (B h) := Or.inr rfl
  have sa := sole _ ra
  have sb := sole _ rb
  have hab := hAB h hh
  have atom : ∀ a, rd A B h a → (∃ i < n, a = i) ∨ (∃ i < n, a = n + i) ∨ ∃ i j, a = n + n + j ∧ Tg n m A B An i j := by
    intro a ha
    rcases hat a ha with h1 | h1
    · by_cases h2 : a < n
      · exact Or.inl ⟨a, h2, rfl⟩
      · exact Or.inr (Or.inl ⟨a - n, by omega, by omega⟩)
    · exact Or.inr (Or.inr h1)
  have third : ∀ i j, i < n → j < n → ∃ v < n, v ≠ i ∧ v ≠ j := by
    intro i j _ _
    by_cases h0 : 0 ≠ i ∧ 0 ≠ j
    · exact ⟨0, by omega, h0.1, h0.2⟩
    · by_cases h1 : 1 ≠ i ∧ 1 ≠ j
      · exact ⟨1, by omega, h1.1, h1.2⟩
      · refine ⟨2, by omega, ?_, ?_⟩ <;> omega
  rcases atom _ ra with ⟨i, hi, ea⟩ | ⟨i, hi, ea⟩ | ⟨i, ja, ea, hTa⟩
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · by_cases hij : i = j
      · subst hij
        exact hab (ea.trans eb.symm)
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have hfin := fin (fun w => w = i ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = false := (hf i i hi hi).trans (by simp)
            have f2 : V Q (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + i) = decide (k = j ∨ k = n + i)
            have hH2 : ¬(k = i ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ n + n + jo = j := hH
            omega
    · by_cases hij : i = j
      · subst hij
        cases hAn : An h with
        | false =>
          refine hhT ⟨i, hi, hh, hAn, Or.inl ⟨ea, eb⟩, fun k hk hr => ?_⟩
          rcases hr with hr | hr
          · exact sa k hk (by rw [ea]; exact hr)
          · exact sb k hk (by rw [eb]; exact hr)
        | true =>
          obtain ⟨P, Q, pq, px, qx, hdiff⟩ := seesC i hi
          refine hdiff (fin (fun w => w = n + i) P Q (fun k _ hk => pq k hk) ?_ ?_ (by omega))
          · intro k hk _ hr
            exact sb k hk (by rw [eb]; exact hr)
          · rw [hVh, hVh, if_pos hAn, if_pos hAn, ea, eb, v0 _ i (by omega), v0 _ i (by omega), px, qx]
            simp
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (n + j) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have ua : V Q (i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have hfin := fin (fun w => w = i ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬(k = i ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ n + n + jo = n + j := hH
            omega
    · have hj := hTb.1
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i jb hTb (xb h hh (Or.inl (by rw [← ea]; exact ra))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false by apply decide_eq_false; omega), (show P (n + j) = false by apply decide_eq_false; omega)]; rfl
          have ua : V Q (i) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false by apply decide_eq_false; omega), (show Q (n + j) = false by apply decide_eq_false; omega)]; rfl
          have hfin := fin (fun w => w = i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬(k = i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = false by apply decide_eq_false; omega), (show P (n + j) = true by apply decide_eq_true; omega)]; rfl
          have ua : V Q (i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false by apply decide_eq_false; omega), (show Q (n + j) = false by apply decide_eq_false; omega)]; rfl
          have hfin := fin (fun w => w = i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬(k = i ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = i ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | (rfl | rfl | rfl)
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = i ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno j jb hTb
            omega
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · by_cases hij : i = j
      · subst hij
        cases hAn : An h with
        | false =>
          refine hhT ⟨i, hi, hh, hAn, Or.inr ⟨ea, eb⟩, fun k hk hr => ?_⟩
          rcases hr with hr | hr
          · exact sb k hk (by rw [eb]; exact hr)
          · exact sa k hk (by rw [ea]; exact hr)
        | true =>
          obtain ⟨P, Q, pq, px, qx, hdiff⟩ := seesC i hi
          refine hdiff (fin (fun w => w = n + i) P Q (fun k _ hk => pq k hk) ?_ ?_ (by omega))
          · intro k hk _ hr
            exact sa k hk (by rw [ea]; exact hr)
          · rw [hVh, hVh, if_pos hAn, if_pos hAn, ea, eb, v0 _ i (by omega), v0 _ i (by omega), px, qx]
            simp
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (j) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have hfin := fin (fun w => w = n + i ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = j)
            have hH2 : ¬(k = n + i ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ n + n + jo = j := hH
            omega
    · by_cases hij : i = j
      · subst hij
        exact hab (ea.trans eb.symm)
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ub : V Q (n + j) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have hfin := fin (fun w => w = n + i ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = false := (hf i i hi hi).trans (by simp)
            have f2 : V Q (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + i) = decide (k = i ∨ k = n + j)
            have hH2 : ¬(k = n + i ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | rfl
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ n + n + jo = n + j := hH
            omega
    · have hj := hTb.1
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i jb hTb (xb h hh (Or.inr (by rw [← ea]; exact ra))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = v ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = v)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false by apply decide_eq_false; omega), (show P (n + j) = false by apply decide_eq_false; omega)]; rfl
          have ua : V Q (n + i) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false by apply decide_eq_false; omega), (show Q (n + j) = false by apply decide_eq_false; omega)]; rfl
          have hfin := fin (fun w => w = n + i) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf v i hv hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = v ∨ k = n + i) = decide (k = v)
            have hH2 : ¬(k = n + i) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i := hH
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = n + i)
          have va : V P (n + i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = true by apply decide_eq_true; omega), (show P (n + j) = false by apply decide_eq_false; omega)]; rfl
          have ua : V Q (n + i) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false by apply decide_eq_false; omega), (show Q (n + j) = false by apply decide_eq_false; omega)]; rfl
          have hfin := fin (fun w => w = n + i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = n + i)
            have hH2 : ¬(k = n + i ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬(n + n + k = n + i ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ (w = n + i ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with rfl | (rfl | rfl | rfl)
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : n + n + jo = n + i ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno j jb hTb
            omega
  · rcases atom _ rb with ⟨j, hj, eb⟩ | ⟨j, hj, eb⟩ | ⟨j, jb, eb, hTb⟩
    · have hi := hTa.1
      have xa := hTa.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i ja hTa (xa h hh (Or.inl (by rw [← eb]; exact rb))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true by apply decide_eq_true; omega), (show P (n + i) = false by apply decide_eq_false; omega)]; rfl
          have vb : V P (j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false by apply decide_eq_false; omega), (show Q (n + i) = false by apply decide_eq_false; omega)]; rfl
          have ub : V Q (j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = j ∨ k = n + i)
          let Q : ℕ → Bool := fun k => decide (k = j)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = false by apply decide_eq_false; omega), (show P (n + i) = true by apply decide_eq_true; omega)]; rfl
          have vb : V P (j) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false by apply decide_eq_false; omega), (show Q (n + i) = false by apply decide_eq_false; omega)]; rfl
          have ub : V Q (j) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf j i hj hi).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = j ∨ k = n + i) = decide (k = j)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ k = j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ n + n + k = j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | rfl
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ n + n + jo = j := hH
            have := Tno i ja hTa
            omega
    · have hi := hTa.1
      have xa := hTa.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exact Tne i ja hTa (xa h hh (Or.inr (by rw [← eb]; exact rb))).symm
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true by apply decide_eq_true; omega), (show P (n + i) = false by apply decide_eq_false; omega)]; rfl
          have vb : V P (n + j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false by apply decide_eq_false; omega), (show Q (n + i) = false by apply decide_eq_false; omega)]; rfl
          have ub : V Q (n + j) = false := by rw [v0 _ _ (by omega)]; apply decide_eq_false; omega
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = n + j)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true by apply decide_eq_true; omega), (show P (n + i) = false by apply decide_eq_false; omega)]; rfl
          have vb : V P (n + j) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false by apply decide_eq_false; omega), (show Q (n + i) = false by apply decide_eq_false; omega)]; rfl
          have ub : V Q (n + j) = true := by rw [v0 _ _ (by omega)]; apply decide_eq_true; omega
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = n + j) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 j hj
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = n + j)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ k = n + j) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ n + n + k = n + j) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ w = n + j) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | rfl
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ n + n + jo = n + j := hH
            have := Tno i ja hTa
            omega
    · have hi := hTa.1
      have hj := hTb.1
      have xa := hTa.2.2.2.2
      have xb := hTb.2.2.2.2
      by_cases hij : i = j
      · subst hij
        exfalso
        have e1 : ja = jb := by
          refine xb ja hTa.2.1 ?_
          rcases hTa.2.2.2.1 with ⟨e, _⟩ | ⟨_, e⟩
          · exact Or.inl (Or.inl e)
          · exact Or.inl (Or.inr e)
        exact hab (by rw [ea, eb, e1])
      · obtain ⟨v, hv, hvi, hvj⟩ := third i j hi hj
        cases hAn : An h with
        | true =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + v)
          let Q : ℕ → Bool := fun k => decide (k = n + v)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true by apply decide_eq_true; omega), (show P (n + i) = false by apply decide_eq_false; omega)]; rfl
          have vb : V P (n + n + jb) = false := by rw [VT j jb hTb P, (show P (j) = false by apply decide_eq_false; omega), (show P (n + j) = false by apply decide_eq_false; omega)]; rfl
          have ua : V Q (n + n + ja) = false := by rw [VT i ja hTa Q, (show Q (i) = false by apply decide_eq_false; omega), (show Q (n + i) = false by apply decide_eq_false; omega)]; rfl
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false by apply decide_eq_false; omega), (show Q (n + j) = false by apply decide_eq_false; omega)]; rfl
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i v hi hv).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := col1 v hv
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + v) = decide (k = n + v)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) := hH
            have := Tno i ja hTa
            omega
        | false =>
          let P : ℕ → Bool := fun k => decide (k = i ∨ k = n + j)
          let Q : ℕ → Bool := fun k => decide (k = i)
          have va : V P (n + n + ja) = true := by rw [VT i ja hTa P, (show P (i) = true by apply decide_eq_true; omega), (show P (n + i) = false by apply decide_eq_false; omega)]; rfl
          have vb : V P (n + n + jb) = true := by rw [VT j jb hTb P, (show P (j) = false by apply decide_eq_false; omega), (show P (n + j) = true by apply decide_eq_true; omega)]; rfl
          have ua : V Q (n + n + ja) = true := by rw [VT i ja hTa Q, (show Q (i) = true by apply decide_eq_true; omega), (show Q (n + i) = false by apply decide_eq_false; omega)]; rfl
          have ub : V Q (n + n + jb) = false := by rw [VT j jb hTb Q, (show Q (j) = false by apply decide_eq_false; omega), (show Q (n + j) = false by apply decide_eq_false; omega)]; rfl
          have hfin := fin (fun w => (w = i ∨ w = n + i ∨ w = n + n + ja) ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) P Q ?_ ?_ ?_ ?_
          · have f1 : V P (n + n + jo) = true := (hf i j hi hj).trans (by simp <;> omega)
            have f2 : V Q (n + n + jo) = false := row1 i hi
            rw [f1, f2] at hfin
            cases hfin
          · intro k hk hH
            show decide (k = i ∨ k = n + j) = decide (k = i)
            have hH2 : ¬((k = i ∨ k = n + i ∨ k = n + n + ja) ∨ (k = j ∨ k = n + j ∨ k = n + n + jb)) := hH
            rw [decide_eq_decide]
            omega
          · intro k hk hkH hr
            have hkH2 : ¬((n + n + k = i ∨ n + n + k = n + i ∨ n + n + k = n + n + ja) ∨ (n + n + k = j ∨ n + n + k = n + j ∨ n + n + k = n + n + jb)) := hkH
            have hr2 : ∃ w, rd A B k w ∧ ((w = i ∨ w = n + i ∨ w = n + n + ja) ∨ (w = j ∨ w = n + j ∨ w = n + n + jb)) := hr.elim (fun e => ⟨_, Or.inl rfl, e⟩) (fun e => ⟨_, Or.inr rfl, e⟩)
            obtain ⟨w, hw, hw2⟩ := hr2
            rcases hw2 with (rfl | rfl | rfl) | (rfl | rfl | rfl)
            · exfalso; have := xa k hk (Or.inl hw); omega
            · exfalso; have := xa k hk (Or.inr hw); omega
            · exact sa k hk (by rw [ea]; exact hw)
            · exfalso; have := xb k hk (Or.inl hw); omega
            · exfalso; have := xb k hk (Or.inr hw); omega
            · exact sb k hk (by rw [eb]; exact hw)
          · rw [hVh, hVh, ea, eb, va, vb, ua, ub]
            simp [hAn]
          · intro hH
            have hH2 : (n + n + jo = i ∨ n + n + jo = n + i ∨ n + n + jo = n + n + ja) ∨ (n + n + jo = j ∨ n + n + jo = n + j ∨ n + n + jo = n + n + jb) := hH
            have := Tno i ja hTa
            have := Tno j jb hTb
            omega

def onl (n : ℕ) (Q : ℕ → Bool) : List Bool := (List.range (n + n)).map Q

theorem onl_len (n : ℕ) (Q : ℕ → Bool) : (onl n Q).length = n + n := by simp [onl]

theorem onl_get (n : ℕ) (Q : ℕ → Bool) (k : ℕ) (hk : k < n + n) : (onl n Q).getD k false = Q k := by
  simp [onl, List.getD_eq_getElem?_getD, List.getElem?_range hk]

theorem one_onl (n : ℕ) (u v : Fin n) : PEqualNP.Represents.oneEach u v = onl n (pt n u v) := by
  refine List.ext_getElem (by simp [PEqualNP.Represents.oneEach, onl]) fun k h1 h2 => ?_
  have hk : k < n + n := by simpa [onl] using h2
  simp only [PEqualNP.Represents.oneEach, onl, List.getElem_map, List.getElem_range, pt]
  by_cases h : k < n
  · rw [List.getElem_append_left (by simpa using h)]
    simp only [List.getElem_ofFn, Fin.ext_iff]
    rw [decide_eq_decide]
    have := v.isLt
    omega
  · rw [List.getElem_append_right (by simpa using h)]
    simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff]
    rw [decide_eq_decide]
    have := u.isLt
    omega

end PEqualNP.Outside.L_meta_18163_aux.Reduction

open PEqualNP.Outside.L_meta_18163_aux.Reduction PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_18163_aux.Reduction

theorem removeThree : ∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (n + 1) => decide (u ≠ v)) (s + 3) → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s := by
  rintro k s ⟨C0, hC0, hsize, hf0⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · exact ⟨⟨[], 0⟩, by simp [Monotone2], Nat.zero_le _, fun u _ => Fin.elim0 u⟩
    · refine ⟨⟨[], 2⟩, by simp [Monotone2], Nat.zero_le _, ?_⟩
      intro u v
      fin_cases u
      fin_cases v
      decide
  classical

  have hex : ∃ s, ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = s ∧ ∀ u v : Fin (k + 1), C.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v) := ⟨_, C0, hC0, rfl, hf0⟩
  obtain ⟨C, hC, hCs, hf⟩ := Nat.find_spec hex
  have hmin : ∀ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D → (∀ u v : Fin (k + 1), D.eval (PEqualNP.Represents.oneEach u v) = decide (u ≠ v)) → C.size ≤ D.size := by
    intro D h1 h2
    rw [hCs]
    exact Nat.find_min' hex ⟨D, h1, rfl, h2⟩
  have hle : C.size ≤ C0.size := hmin C0 hC0 hf0
  set n := k + 1 with hn
  have hn3 : 3 ≤ n := by omega
  let V : (ℕ → Bool) → ℕ → Bool := fun Q w => (run C.gates (onl n Q)).getD w false
  have hm : C.size = C.gates.length := rfl
  have hV : ∀ u v : Fin n, ∀ w, V (pt n u v) w = (run C.gates (PEqualNP.Represents.oneEach u v)).getD w false := by
    intro u v w
    rw [one_onl]
  have hlen1 : ∀ u v : Fin n, (PEqualNP.Represents.oneEach u v).length = n + n := fun u v => by
    simp only [PEqualNP.Represents.oneEach, List.length_append, List.length_ofFn]
  have nonc : ¬∃ b, ∀ p : Fin n × Fin n, C.eval (PEqualNP.Represents.oneEach p.1 p.2) = b := by
    rintro ⟨b, hb⟩
    have h1 := hb (⟨0, by omega⟩, ⟨0, by omega⟩)
    have h2 := hb (⟨0, by omega⟩, ⟨1, by omega⟩)
    rw [hf] at h1 h2
    rw [← h1] at h2
    simp at h2

  have irr0 : ∀ j < C.gates.length, ¬((∃ b, ∀ p : Fin n × Fin n, (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD (n + n + j) false = b) ∨
      ∃ w < n + n + j, ∀ p : Fin n × Fin n, (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD (n + n + j) false = (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD w false) := by
    intro j hj hbad
    obtain ⟨D, d1, d2, d3⟩ := engine3 (n + n) (n + n) C (fun p : Fin n × Fin n => PEqualNP.Represents.oneEach p.1 p.2) (fun p => PEqualNP.Represents.oneEach p.1 p.2)
      (fun p => hlen1 _ _) (fun p => hlen1 _ _) {j} hC (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩) nonc (by
        intro i hi
        have : i = j := by simpa using hi
        subst this
        exact ⟨hj, hbad⟩)
    have := hmin D d1 fun u v => (d3 (u, v)).trans (hf u v)
    rw [Finset.card_singleton] at d2
    omega
  have shape : ∀ j, j < C.gates.length → ∃ a b : ℕ, ∃ c : Bool, a < n + n + j ∧ b < n + n + j ∧ a ≠ b ∧
      ∀ Q, V Q (n + n + j) = if c = true then V Q a && V Q b else V Q a || V Q b := by
    intro j hj
    obtain ⟨hop, hl⟩ := hC _ (List.getElem_mem hj)
    have hop' : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := by simpa using hop
    have rg0 : ∀ l : List Bool, l.length = n + n → (run C.gates l).getD (n + n + j) false = C.gates[j].op.eval (C.gates[j].inputs.map fun i => if i < n + n + j then (run C.gates l).getD i false else false) := by
      intro l hll
      have := run_gate C.gates l j hj
      rw [hll] at this
      exact this
    have bad := irr0 j hj
    generalize hin : C.gates[j].inputs = l at hl rg0
    rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact absurd (Or.inl ⟨C.gates[j].op.eval [], fun p => by rw [rg0 _ (hlen1 _ _)]; rfl⟩) bad
    · by_cases ha : a < n + n + j
      · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
        rw [rg0 _ (hlen1 _ _)]
        rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
      · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
        rw [rg0 _ (hlen1 _ _)]
        rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
    · by_cases ha : a < n + n + j
      · by_cases hb : b < n + n + j
        · by_cases hab : a = b
          · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _), ← hab]
            rcases hop' with e | e <;> simp [e, GateOp.eval, ha]
          · rcases hop' with e | e
            · refine ⟨a, b, true, ha, hb, hab, fun Q => ?_⟩
              have := rg0 (onl n Q) (onl_len n Q)
              rw [e] at this
              simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true] at this
              simpa [V] using this
            · refine ⟨a, b, false, ha, hb, hab, fun Q => ?_⟩
              have := rg0 (onl n Q) (onl_len n Q)
              rw [e] at this
              simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb, GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false] at this
              simpa [V] using this
        · rcases hop' with e | e
          · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, hb]
          · refine absurd (Or.inr ⟨a, ha, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, ha, hb]
      · rcases hop' with e | e
        · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
          rw [rg0 _ (hlen1 _ _)]
          simp [e, GateOp.eval, ha]
        · by_cases hb : b < n + n + j
          · refine absurd (Or.inr ⟨b, hb, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, ha, hb]
          · refine absurd (Or.inl ⟨false, fun p => ?_⟩) bad
            rw [rg0 _ (hlen1 _ _)]
            simp [e, GateOp.eval, ha, hb]
    · simp at hl
  choose! A B An hA hB hAB hv1 using shape
  have hout : C.output < n + n + C.gates.length := by
    by_contra h
    refine nonc ⟨false, fun p => ?_⟩
    change (run C.gates (PEqualNP.Represents.oneEach p.1 p.2)).getD C.output false = false
    exact List.getD_eq_default _ _ (by rw [run_length, hlen1]; omega)
  obtain ⟨i, hi, a, b, c, ha, hb, hc, hab, hac, hbc, ka, kb, kc⟩ := core n hn3 C.gates.length A B An V C.output hA hB hAB
    (fun Q w hw => by
      simp only [V]
      rw [run_input _ _ _ (by rw [onl_len]; exact hw), onl_get n Q w hw])
    (fun Q j hj => hv1 j hj Q) hout
    (fun u v hu hv => by
      have := hf ⟨u, hu⟩ ⟨v, hv⟩
      rw [one_onl] at this
      change (run C.gates (onl n (pt n u v))).getD C.output false = _ at this
      simp only [V]
      rw [this]
      simp [Fin.ext_iff])
    (fun j hj w hw hall => irr0 j hj (Or.inr ⟨w, hw, fun p => by rw [← hV, ← hV]; exact hall _ _ p.1.isLt p.2.isLt⟩))

  let ii : Fin (k + 1) := ⟨i, hi⟩
  have hsa : ∀ u : Fin k, ((ii.succAbove u : Fin (k + 1)) : ℕ) ≠ i := fun u h => Fin.succAbove_ne ii u (Fin.ext h)
  have hlen2 : ∀ u v : Fin k, (PEqualNP.Represents.oneEach u v).length = k + k := by intro u v; simp [PEqualNP.Represents.oneEach]
  have kf : ∀ j, Kill n V i j → (∃ b, ∀ p : Fin k × Fin k, (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD (n + n + j) false = b) ∨
      ∃ w < n + n + j, ∀ p : Fin k × Fin k, (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD (n + n + j) false = (run C.gates (PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2))).getD w false := by
    rintro j (⟨b, h⟩ | ⟨w, hw, h⟩)
    · exact Or.inl ⟨b, fun p => by rw [← hV]; exact h _ _ (Fin.isLt _) (Fin.isLt _) (hsa _) (hsa _)⟩
    · exact Or.inr ⟨w, hw, fun p => by rw [← hV, ← hV]; exact h _ _ (Fin.isLt _) (Fin.isLt _) (hsa _) (hsa _)⟩
  obtain ⟨D, d1, d2, d3⟩ := engine3 (n + n) (k + k) C (fun p : Fin k × Fin k => PEqualNP.Represents.oneEach (ii.succAbove p.1) (ii.succAbove p.2)) (fun p => PEqualNP.Represents.oneEach p.1 p.2)
    (fun p => hlen1 _ _) (fun p => hlen2 _ _) {a, b, c} hC (by
      intro w hw
      by_cases h : w < n
      · by_cases hwi : w = i
        · left
          refine ⟨false, fun p => ?_⟩
          rw [one_onl, onl_get n _ w hw, pt, decide_eq_false_iff_not]
          have := hsa p.1
          omega
        · right
          obtain ⟨u', hu'⟩ := Fin.exists_succAbove_eq (x := (⟨w, h⟩ : Fin (k + 1))) (y := ii) (fun e => hwi (congrArg Fin.val e))
          refine ⟨u', by have := u'.isLt; omega, fun p => ?_⟩
          rw [one_onl, one_onl, onl_get n _ w hw, onl_get k _ _ (by have := u'.isLt; omega)]
          simp only [pt]
          rw [decide_eq_decide]
          have e1 : w = ((ii.succAbove p.1 : Fin (k + 1)) : ℕ) ↔ (u' : ℕ) = p.1 := by
            rw [← show ((ii.succAbove u' : Fin (k + 1)) : ℕ) = w from congrArg Fin.val hu', ← Fin.ext_iff, ← Fin.ext_iff, (Fin.succAbove_right_injective).eq_iff]
          have := u'.isLt
          constructor
          · rintro (e | e)
            · exact Or.inl (e1.1 e)
            · omega
          · rintro (e | e)
            · exact Or.inl (e1.2 e)
            · omega
      · by_cases hwi : w = n + i
        · left
          refine ⟨false, fun p => ?_⟩
          rw [one_onl, onl_get n _ w hw, pt, decide_eq_false_iff_not]
          have := hsa p.2
          have := (ii.succAbove p.1).isLt
          omega
        · right
          obtain ⟨u', hu'⟩ := Fin.exists_succAbove_eq (x := (⟨w - n, by omega⟩ : Fin (k + 1))) (y := ii) (fun e => hwi (by have := congrArg Fin.val e; simp only [ii] at this; omega))
          refine ⟨k + u', by have := u'.isLt; omega, fun p => ?_⟩
          rw [one_onl, one_onl, onl_get n _ w hw, onl_get k _ _ (by have := u'.isLt; omega)]
          simp only [pt]
          rw [decide_eq_decide]
          have e0 : ((ii.succAbove u' : Fin (k + 1)) : ℕ) = w - n := congrArg Fin.val hu'
          have e1 : w - n = ((ii.succAbove p.2 : Fin (k + 1)) : ℕ) ↔ (u' : ℕ) = p.2 := by
            rw [← e0, ← Fin.ext_iff, ← Fin.ext_iff, (Fin.succAbove_right_injective).eq_iff]
          have h1 := u'.isLt
          have h2 := p.1.isLt
          have h3 := (ii.succAbove p.1).isLt
          constructor
          · rintro (e | e)
            · omega
            · have := e1.1 (by omega); omega
          · rintro (e | e)
            · omega
            · have := e1.2 (by omega); omega)
    (by
      rintro ⟨b, hb⟩
      have h1 := hb (⟨0, by omega⟩, ⟨0, by omega⟩)
      have h2 := hb (⟨0, by omega⟩, ⟨1, by omega⟩)
      simp only [hf] at h1 h2
      rw [← h1] at h2
      simp [(Fin.succAbove_right_injective).eq_iff] at h2)
    (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl
      · exact ⟨ha, kf _ ka⟩
      · exact ⟨hb, kf _ kb⟩
      · exact ⟨hc, kf _ kc⟩)
  have hcard : ({a, b, c} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  rw [hcard] at d2
  refine ⟨D, d1, by omega, ?_⟩
  intro u v
  rw [d3 (u, v), hf]
  simp only [ne_eq, (Fin.succAbove_right_injective).eq_iff]

end PEqualNP.Outside.L_meta_18163_aux.Reduction

theorem PEqualNP.Outside.L_meta_18163 : ∀ n s : ℕ, 5 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → 3 * n ≤ s := by
  intro n
  induction n with
  | zero => intro s hn; omega
  | succ n ih =>
    intro s hn represented
    by_cases base : n = 4
    · subst n
      exact PEqualNP.Outside.L_meta_18163_aux.Five.baseFive s represented
    obtain ⟨C, hC, hs, hrep⟩ := represented
    have smaller := PEqualNP.Outside.L_meta_18163_aux.Reduction.removeThree n (s - 3) ⟨C, hC, by omega, hrep⟩
    have prior := ih (s - 3) (by omega) smaller
    omega
