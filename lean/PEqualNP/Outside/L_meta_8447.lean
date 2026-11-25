import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8447

abbrev Forest := Nat → Nat × Nat

def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)

def decodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
  let entry := unpack packed width index
  (entry &&& ((1 <<< parentWidth) - 1), entry >>> parentWidth)

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
abbrev CutCheck := RowState → Bool

def rootWords (base : List Word) (token : Nat) : List Word :=
  List.rec (motive := fun _ => Nat → List Word) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token

def rootState (base : List Word) (fuel token : Nat) : RowState :=
  (fuel, rootWords base token, [])

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

abbrev Bound := Nat × List Word × Nat × Word

def stockWord (mask : Nat) (stock : List Word) (needed : List Word) (word : Word) : List Word :=
  let v := word &&& mask
  if v == 0 || v == mask || stock.contains v || needed.contains v then needed
  else v :: needed

def recipeStart (mask : Nat) (stock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWord mask stock seen word)) words) []

def recipeClosure (mask : Nat) (stock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (if seen.contains (out &&& mask) then stockWord mask stock (stockWord mask stock seen a) b else seen))
    history start

def recipeNeeded (mask : Nat) (stock words : List Word) (history : List (Word × Word × Word)) :
    List Word :=
  recipeClosure mask stock history (recipeStart mask stock words)

def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask

def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words

def availableB (mask : Nat) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w

def recipeGate (mask : Nat) (bank : List Word) (w a b : Word) : Bool :=
  availableB mask bank a &&
    ((w == mask ^^^ a) || (availableB mask bank b && (w == a &&& b || w == a ||| b)))

def replayRecipes (mask : Nat) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := w &&& mask
      if needed.contains v && !availableB mask bank v &&
          recipeGate mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank

def boundCloses (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    (let remaining := fuel - flatCount mask ws
     if remaining < lower then
       let start := recipeStart mask stock ws
       if start.length + remaining < lower then
         let needed := recipeClosure mask stock history start
         if needed.length + remaining < lower then
           let replay := replayRecipes mask needed history.reverse stock
           (replay.length + remaining < lower) &&
             ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask))
         else false
       else false
     else false)

def knownCloses (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => boundCloses target state bound || later) bounds

def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank

def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))

def WordBuilds (mask : Nat) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateWord mask roots w ∧ WordBuilds mask (w :: roots) ws

def Lower (mask : Nat) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuilds mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length

def Known (bounds : List Bound) : Prop :=
  ∀ bound ∈ bounds, Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1

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

theorem projectBuilds {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots values : List Word} (builds : WordBuilds mask roots values) :
    WordBuilds cut (roots.map (· &&& cut)) (values.map (· &&& cut)) := by
  induction values generalizing roots with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨projectGate submask builds.1, ih builds.2⟩

theorem availableWeaken {mask : Nat} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h

theorem gateWeaken {mask : Nat} {small big : List Word} {out : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (gate : GateWord mask small out) : GateWord mask big out := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq⟩
  · exact Or.inl ⟨a, availableWeaken sub ha, rfl⟩
  · exact Or.inr ⟨a, b, availableWeaken sub ha, availableWeaken sub hb, eq⟩

theorem extendKnown {bound : Bound} {bounds : List Bound}
    (old : Known bounds)
    (new : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    Known (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h

def AgreesAt (i j : Nat) (word : Word) : Prop :=
  word.testBit i = word.testBit j

theorem agreesAvailable {i j mask : Nat} {bank : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (av : AvailableWord mask bank word) : AgreesAt i j word := by
  rcases av with rfl | rfl | h
  · simp [AgreesAt]
  · exact m
  · exact all _ h

theorem agreesGate {i j mask : Nat} {bank : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (gate : GateWord mask bank word) : AgreesAt i j word := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · simp only [AgreesAt, Nat.testBit_xor] at m ⊢
    rw [m, show a.testBit i = a.testBit j from agreesAvailable m all ha]
  · subst word
    simp only [AgreesAt, Nat.testBit_and]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]
  · subst word
    simp only [AgreesAt, Nat.testBit_or]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]

theorem agreesBuilds {i j mask : Nat} {roots values : List Word} {word : Word}
    (m : AgreesAt i j mask) (all : ∀ w ∈ roots, AgreesAt i j w)
    (builds : WordBuilds mask roots values)
    (av : AvailableWord mask (values ++ roots) word) : AgreesAt i j word := by
  induction values generalizing roots with
  | nil => exact agreesAvailable m all av
  | cons v vs ih =>
    have vg := agreesGate m all builds.1
    have hc : ∀ w ∈ v :: roots, AgreesAt i j w := by
      intro w h
      rcases List.mem_cons.mp h with rfl | mem
      · exact vg
      · exact all _ mem
    apply ih hc builds.2
    rcases av with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by
        simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using h))

theorem buildsMap {m n : Nat} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots : List Word} {bank : List Word}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    {values : List Word} (h : WordBuilds m roots values) :
    WordBuilds n bank (values.map f) := by
  have av {bank roots : List Word} {v : Word}
      (src : ∀ v ∈ roots, AvailableWord n bank (f v))
      (h : AvailableWord m roots v) : AvailableWord n bank (f v) := by
    rcases h with rfl | rfl | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ih ?_ h.2⟩
    · rcases h.1 with ⟨a, ha, eq⟩ | ⟨a, b, ha, hb, eq | eq⟩
      · exact Or.inl ⟨f a, av supply ha, eq ▸ invert a⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inl (eq ▸ meet a b)⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem lowerMap {m n : Nat} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word} {goal : Word} {minimum : Nat}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    (bound : Lower n bank (f goal) minimum) :
    Lower m roots goal minimum := by
  intro values build hit
  suffices AvailableWord n (values.map f ++ bank) (f goal) by
    simpa using bound (values.map f) (buildsMap f zero ones invert meet join supply build) this
  rcases hit with rfl | rfl | mem
  · exact Or.inl zero
  · exact Or.inr (Or.inl ones)
  · rcases List.mem_append.mp mem with hv | hr
    · exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_map_of_mem hv)))
    · exact availableWeaken (fun w hw => Or.inr (Or.inr (List.mem_append_right _ hw))) (supply _ hr)

theorem buildsWeaken {mask : Nat} {small big values : List Word}
    (supply : ∀ w ∈ small, AvailableWord mask big w) (build : WordBuilds mask small values) :
    WordBuilds mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateWeaken supply build.1, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem gateBuildsIndex {mask : Nat} (bank values : List Word)
    (legal : ∀ i, i < values.length →
      GateWord mask (bank ++ values.take i) (values.getD i 0)) :
    WordBuilds mask bank values := by
  induction values generalizing bank with
  | nil => trivial
  | cons v vs ih =>
    have first := legal 0 (by simp)
    have tail : ∀ i, i < vs.length →
        GateWord mask ((bank ++ [v]) ++ vs.take i) (vs.getD i 0) := by
      intro i hi
      simpa [List.take_succ_cons, List.append_assoc] using
        legal (i + 1) (by simpa using hi)
    refine ⟨by simpa using first, buildsWeaken ?_ (ih (bank ++ [v]) tail)⟩
    intro w mem
    exact Or.inr (Or.inr (by simpa [or_comm] using mem))

theorem lowerWeaken {mask goal minimum : Nat} {old new : List Word}
    (lower : Lower mask old goal minimum) (supply : ∀ w ∈ new, AvailableWord mask old w) :
    Lower mask new goal minimum := by
  apply lowerMap id rfl rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) supply
  exact lower

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

def wordWitness (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  (∃ a ∈ ws, properWord mask a ∧ w = mask ^^^ a) ∨
  ∃ d a b, a ∈ ws ∧ b ∈ ws ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ w = binWord d a b

theorem pullWord {w : List (Word)} {z : Word} {k t S} (h : LiveWord mask target k t S)
    (hz : wordRep mask w z ∨ wordWitness mask w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ LiveWord mask target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveWordProper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase ((mask ^^^ a))
        have ht : LiveWord mask target k t (insert ((mask ^^^ a)) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : (mask ^^^ a) ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (binWord d a b)
        have ht : LiveWord mask target k t (insert (binWord d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha



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

theorem classifyWord {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (gate : GateWord mask bank out) :
    wordRep mask bank out ∨ wordWitness mask bank out := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Word} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, h | h⟩
  · rcases classify ha with rfl | hma | ⟨hm, hp⟩
    · exact Or.inl (by simpa using cm)
    · exact Or.inl (by simpa [hma] using c0)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  · subst out; exact (classifyBinary all false ha hb).imp id Or.inr
  · subst out; exact (classifyBinary all true ha hb).imp id Or.inr

theorem extractWordLive {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : WordBuilds mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k t S, k ≤ values.length ∧ LiveWord mask target k t S ∧ ∀ w ∈ S, w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0, 0, {target}, Nat.zero_le _, LiveWord.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all builds.1
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm))
    obtain ⟨k, t, S, hk, live, sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S, v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    obtain ⟨k', t', S', hk', hl, hsub⟩ := pullWord live (classifyWord all builds.1) available
    exact ⟨k', t', S', by simp only [List.length_cons]; omega, hl, hsub⟩

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

theorem unaryChild {mask fuel a : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x : Word} {keep : Nat}
    (ha : a < ws.length) (ha64 : a < 64) (hf : fuel ≠ 0) (hk : keep < 2)
    (hx : ws.getD a 0 = x) (p : properWord mask (mask ^^^ x)) (fresh : mask ^^^ x ∉ ws) :
    childState mask (gateToken a a 2 keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (mask ^^^ x) (keepWord (keep.testBit 0) x ws),
        (mask ^^^ x, x, x) :: history) := by
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) ha64 (by decide : 2 < 3) (by omega : keep < 4)
  simp only [childState, ke, op, aa, bb, hx]
  simp [hf, Nat.not_le_of_lt ha, Nat.not_le_of_lt hk, p.1, p.2, fresh, keepWord]

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

def WordViable (mask : Nat) (target : Word) (state : RowState) : Prop :=
  state.2.1.Nodup ∧ ∃ k t, k ≤ state.1 ∧ LiveWord mask target k t state.2.1.toFinset

def HasChild (mask : Nat) (state child : RowState) : Prop :=
  ∃ a b op keep, a < state.2.1.length ∧
    ((a = b ∧ op = 2 ∧ keep < 2) ∨
      (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4)) ∧
    childState mask (gateToken a b op keep) state = some child

theorem unaryProgress {mask fuel k t : Nat} {x target : Word} {U : Finset Word} {ws : List Word}
    {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x U) (fresh : mask ^^^ x ∉ insert x U)
    (tail : LiveWord mask target k t (insert (mask ^^^ x) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  have xm : x ∈ ws := by
    rw [← List.mem_toFinset, he]
    simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hx : ws.getD a 0 = x := getWord xm
  have p := liveWordProper tail (mask ^^^ x) (Finset.mem_insert_self _ _)
  let save := decide (x ∈ U)
  let keep := if save then 1 else 0
  have keepLt : keep < 2 := by dsimp [keep]; split <;> decide
  have keepBit : keep.testBit 0 = save := by
    unfold keep
    cases save <;> decide
  have fn : mask ^^^ x ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord save x ws
  let child : RowState := (fuel - 1, insertWord (mask ^^^ x) rest, (mask ^^^ x, x, x) :: history)
  refine ⟨child, ⟨a, a, 2, keep, ha, Or.inl ⟨rfl, rfl, keepLt⟩, ?_⟩, ?_⟩
  · have eq := unaryChild (fuel := fuel) (history := history) ha (by omega) (by omega) keepLt hx p fn
    rw [keepBit] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup nd save x) (fun h => fn (keepSubset save x ws _ h)),
      k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord (mask ^^^ x) rest).toFinset
    rw [insertWordSet, keepSet nd he]
    exact tail

theorem binaryProgress {mask fuel k t : Nat} {x y target : Word} {d : Bool} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k t (insert (binWord d x y) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
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
  refine ⟨child, ⟨a, b, if d then 1 else 0, keep, ha, Or.inr ⟨hab, hb, ?_, keepLt⟩, ?_⟩, ?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail

theorem wordProgress {mask : Nat} {target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : WordViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child, HasChild mask state child ∧ WordViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, t, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset, eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,_,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · exact unaryProgress nd width cap eq fresh tail
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm, same, getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x, Finset.insert_comm]; exact fresh
      have tail' : LiveWord mask target k t (insert (binWord d y x) U) := by
        rw [binWord_comm d y x]; exact tail
      exact binaryProgress nd width cap eq' xy.symm (by omega) fresh' tail'

theorem rootWordSublist (base : List Word) (token : Nat) : (rootWords base token).Sublist base := by
  induction base generalizing token with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token &&& 1 == 0 then rootWords ws (token >>> 1)
      else w :: rootWords ws (token >>> 1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _

theorem rootToken (base : List Word) (S : Finset Word) :
    ∃ token < 2 ^ base.length, (rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0, by simp, by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token, htoken, ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low, high]
      by_cases hw : w ∈ S
      · simp [bit, hw, ih]
      · simp [bit, hw, ih]

theorem liveAgrees {i j k t : Nat} {S : Finset Word}
    (h : LiveWord mask target k t S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S, AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveWord.ind with
  | stop => exact all _ (Finset.mem_singleton_self _)
  | @unary k t U a pa fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp only [AgreesAt, Nat.testBit_xor]
      rw [show mask.testBit i = mask.testBit j from m,
        show a.testBit i = a.testBit j from all a (Finset.mem_insert_self _ _)]
    · exact all _ (Finset.mem_insert_of_mem hw)
  | @binary k t U a b d pa pb ab fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp [AgreesAt, binWord, Nat.testBit_and, Nat.testBit_or, aa, bb]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and, ht] using h

variable {rows : Nat}

def fullMask (rows : Nat) : Nat := 2 ^ rows - 1

theorem toNatMasked (v : BitVec rows) : Masked (fullMask rows) v.toNat := by
  unfold Masked fullMask
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt v.isLt]

theorem notNat (v : BitVec rows) : (~~~v).toNat = fullMask rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, Nat.xor_comm, BitVec.toNat_allOnes]
  rfl

theorem gateOfAvailable {bank : List Word} {w : Word}
    (av : AvailableWord mask bank w) : GateWord mask bank w :=
  Or.inr ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩

theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))

def buildable (m g : Word) : Nat → Finset (Word) → Prop
  | 0, s => g ∈ s
  | n+1, s => buildable m g n s ∨
    (∃ a ∈ s, buildable m g n (insert (m ^^^ a) s)) ∨
    (∃ a ∈ s, ∃ b ∈ s, ∃ d, buildable m g n (insert (binWord d a b) s))

theorem supplyPool {m g : Word} {n s q} (sub : s ⊆ q) (h : buildable m g n s) : buildable m g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,h⟩ | ⟨a,ha,b,hb,d,h⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr (Or.inl ⟨a,sub ha,ih (Finset.insert_subset_insert _ sub) h⟩)
    · exact Or.inr (Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) h⟩)

theorem supplyMore {m g : Word} {n l s} (le : n ≤ l) (h : buildable m g n s) : buildable m g l s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

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

theorem cofNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    (mask ^^^ a) &&& m = m ^^^ (a &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun w : Nat => w.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]

theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp

theorem flNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (mask ^^^ a) ↔ maskedFlat m a := by
  unfold maskedFlat
  rw [cofNot sub]
  constructor <;> intro h
  · rcases h with h | h
    · right
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
    · left
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
  · rcases h with h | h <;> simp [h]

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

theorem maskedBuild {goal : Word} {k t s} (run : LiveWord mask goal k t s) (m : Word) (submask : mask &&& m = m) (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n+(flatSet m s).card ≤ k ∧ buildable m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveWord.ind with
  | stop =>
    refine ⟨0,?_,?_⟩
    · simp only [flatSet, Finset.filter_singleton, properGoal, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · change goal &&& m ∈ projectedStock m {goal}
      simp [projectedStock,visibleWords]
  | @unary k t u a pa fresh tail ih =>
    obtain ⟨n,cap,built⟩ := ih
    have nn : (mask ^^^ a) ∉ u := fun h => fresh (Finset.mem_insert_of_mem h)
    rw [flIns nn] at cap
    have card := flLe m a u
    have old : a &&& m ∈ projectedStock m (insert a u) := by simp [projectedStock,prIns]
    have sub : projectedStock m u ⊆ projectedStock m (insert a u) := by
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.subset_insert ..)))
    by_cases f : maskedFlat m a
    · have ff := (flNot submask a).mpr f
      simp only [f,ff,ite_true] at cap card
      refine ⟨n,by omega,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with rfl|rfl|rfl|h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rcases ff with e|e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inr h))
    · have nf := mt (flNot submask a).mp f
      simp only [f,nf,ite_false] at cap card
      refine ⟨n+1,by omega,Or.inr (Or.inl ⟨_,old,supplyPool ?_ built⟩)⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rw [cofNot submask] at hw
      tauto
  | @binary k t u a b d pa pb ab fresh tail ih =>
    let v := binWord d a b
    obtain ⟨n,cap,built⟩ := ih
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
      refine ⟨n,budget,supplyPool ?_ built⟩
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
      refine ⟨n+1,by omega,Or.inr (Or.inr ⟨a &&& m,?_,b &&& m,?_,d,supplyPool ?_ built⟩)⟩
      · simp [projectedStock,prIns]
      · simp [projectedStock,prIns]
      · intro w hw
        simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
        rw [cofBinary] at hw
        tauto

theorem availableB_spec {mask : Nat} {bank : List Word} {v : Word} :
    availableB mask bank v = true ↔ AvailableWord mask bank v := by
  simp [availableB, AvailableWord, or_assoc]

theorem recipeGate_spec {mask : Nat} {bank : List Word} {v a b : Word}
    (h : recipeGate mask bank v a b = true) : GateWord mask bank v := by
  simp only [recipeGate, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, availableB_spec] at h
  rcases h with ⟨ha, first | ⟨hb, second⟩⟩
  · exact Or.inl ⟨a, ha, first⟩
  · exact Or.inr ⟨a, b, ha, hb, second⟩

theorem replayRecipesBuilds (mask : Nat) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : WordBuilds mask bank (replayRecipes mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuilds mask bank
      (if needed.contains (w &&& mask) && !availableB mask bank (w &&& mask) &&
          recipeGate mask bank (w &&& mask) (a &&& mask) (b &&& mask) then
        (w &&& mask) :: replayRecipes mask needed recipes ((w &&& mask) :: bank)
      else replayRecipes mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGate_spec (Bool.and_eq_true_iff.mp yes).2, ih _⟩
    · exact ih _

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

theorem buildsAppend {mask : Nat} {roots first second : List Word}
    (left : WordBuilds mask roots first)
    (right : WordBuilds mask (first ++ roots) second) :
    WordBuilds mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1, ih left.2 ?_⟩
    have same (bank other vals : List Word) (perm : bank.Perm other)
        (h : WordBuilds mask bank vals) : WordBuilds mask other vals := by
      induction vals generalizing bank other with
      | nil => trivial
      | cons v vs ih =>
        exact ⟨gateWeaken (fun x hx => Or.inr (Or.inr (perm.mem_iff.mp hx))) h.1,
          ih _ _ (perm.cons v) h.2⟩
    exact same _ _ _ (List.perm_middle (a := w) (l₁ := ws) (l₂ := roots)).symm right

theorem buildableWords {mask goal n : Nat} {pool : Finset Word} {bank : List Word}
    (h : buildable mask goal n pool) (supply : ∀ w ∈ pool, AvailableWord mask bank w) :
    ∃ values, values.length ≤ n ∧ WordBuilds mask bank values ∧
      AvailableWord mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero => exact ⟨[], Nat.le_refl _, trivial, supply _ h⟩
  | succ n ih =>
    have add {w : Word} (g : GateWord mask bank w)
        (tail : buildable mask goal n (insert w pool)) :
        ∃ values, values.length ≤ n+1 ∧ WordBuilds mask bank values ∧
          AvailableWord mask (values ++ bank) goal := by
      have growing : ∀ v ∈ insert w pool, AvailableWord mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun _ hh => Or.inr (Or.inr (List.mem_cons_of_mem _ hh))) (supply _ hv)
      obtain ⟨values, budget, build, hit⟩ := ih tail growing
      refine ⟨w :: values, by simp only [List.length_cons]; omega, ⟨g, build⟩, ?_⟩
      rcases hit with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by simp only [List.mem_append, List.mem_cons] at *; tauto))
    rcases h with h | ⟨a, ha, h⟩ | ⟨a, ha, b, hb, d, h⟩
    · obtain ⟨values, cap, build, hit⟩ := ih h supply
      exact ⟨values, by omega, build, hit⟩
    · exact add (Or.inl ⟨a, supply a ha, rfl⟩) h
    · apply add (w := binWord d a b) ?_ h
      exact Or.inr ⟨a, b, supply a ha, supply b hb, by cases d <;> simp [binWord]⟩

theorem boundClosesSound {state : RowState} {bound : Bound}
    (known : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : WordViable mask target state) :
    boundCloses target state bound = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, t, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveWord mask target k t ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let replay := replayRecipes cut (recipeNeeded cut stock ws history) history.reverse stock
  change ((target &&& cut) == goal && goal != 0 && goal != cut &&
    (if fuel - flatCount cut ws < minimum then
      if (recipeStart cut stock ws).length + (fuel - flatCount cut ws) < minimum then
        if (recipeNeeded cut stock ws history).length + (fuel - flatCount cut ws) < minimum then
          (replay.length + (fuel - flatCount cut ws) < minimum) &&
            ws.all (fun w => availableB cut (replay ++ stock) (w &&& cut))
        else false
      else false
    else false)) = true at hc
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  simp only [decide_eq_true_eq] at length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuild live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvailableWord cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableWords build supply
  have both := buildsAppend (replayRecipesBuilds cut _ history.reverse stock) built
  have hit : AvailableWord cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact availableWeaken (fun v hv => Or.inr (Or.inr (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesSound {bounds : List Bound} {state : RowState}
    (known : Known bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (viable : WordViable mask target state) :
    knownCloses target bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (boundCloses target state bound || knownCloses target bounds state) = false
    rw [boundClosesSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))

abbrev PointWire (rows : Nat) := Fin rows → Bool

def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem encodeNot (f : PointWire rows) : encodePoint (fun j => !f j) = ~~~encodePoint f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_not, encodeBit f ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
  simp [hi]

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

theorem maskBit {i : Nat} (hi : i < rows) : (fullMask rows).testBit i = true := by
  simp [fullMask, Nat.testBit_two_pow_sub_one, hi]

theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]

theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))

theorem relabelMask (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex (fullMask rows) = fullMask rows := by
  have all : (fun i => (fullMask rows).testBit (sourceIndex i).val) = fun _ => true := by
    funext i
    exact maskBit (sourceIndex i).isLt
  have bits : encodePoint (fun _ : Fin rows => true) = BitVec.allOnes rows := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp [hi]
  simp [relabel, all, pointWord, bits, fullMask]

theorem relabelNot (sourceIndex : Fin rows → Fin rows) (a : Word) :
    relabel sourceIndex (fullMask rows ^^^ a) = fullMask rows ^^^ relabel sourceIndex a := by
  have eq : (fun i => (fullMask rows ^^^ a).testBit (sourceIndex i).val) =
      fun i => !a.testBit (sourceIndex i).val := by
    funext i
    simp [Nat.testBit_xor, maskBit (sourceIndex i).isLt]
  simp only [relabel, eq, pointWord, encodeNot, notNat]

theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]

theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]

theorem lowerRelabel (sourceIndex : Fin rows → Fin rows) {bank roots : List Word}
    {src dst : Word} {minimum : Nat}
    (old : Lower (fullMask rows) bank src minimum)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord (fullMask rows) bank (relabel sourceIndex w)) :
    Lower (fullMask rows) roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) (relabelMask sourceIndex)
    (relabelNot sourceIndex) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rw [goal]
  exact old

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

theorem lowerRelabelMasked (sourceIndex : Fin rows → Fin rows)
    {oldMask newMask : Nat} {bank roots : List Word} {src dst : Word} {minimum : Nat}
    (old : Lower oldMask bank src minimum)
    (masks : relabel sourceIndex newMask = oldMask)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord oldMask bank (relabel sourceIndex w)) :
    Lower newMask roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) masks
    (fun w => by rw [relabelXor, masks]) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rwa [goal]

theorem extendKnownRelabel (sourceIndex : Fin rows → Fin rows) {bounds : List Bound}
    {source destination : Bound} (old : Known bounds) (mem : source ∈ bounds)
    (budget : destination.2.2.1 = source.2.2.1)
    (masks : relabel sourceIndex destination.1 = source.1)
    (goal : relabel sourceIndex destination.2.2.2 = source.2.2.2)
    (supply : ∀ w ∈ destination.2.1,
      AvailableWord source.1 source.2.1 (relabel sourceIndex w)) :
    Known (destination :: bounds) := by
  apply extendKnown old
  rw [budget]
  exact lowerRelabelMasked sourceIndex (old _ mem) masks goal supply

theorem relabelToNatBound (sourceIndex : Fin rows → Fin rows) (word : Word) :
    Masked (fullMask rows) (relabel sourceIndex word) := toNatMasked _

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

theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i = decide (i < 12) := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
  rw [e, Nat.testBit_two_pow_sub_one]

def tb (w e : ℕ) : Bool := !(Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb_eq (w e : ℕ) : tb w e = w.testBit e := by
  have h : Nat.land (Nat.shiftRight w e) 1 = 1 &&& (w >>> e) := Nat.and_comm _ _
  unfold tb Nat.testBit
  rw [h]
  generalize (1 &&& w >>> e) = X
  cases X <;> rfl

def rect (x J : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)

def rectW (x : ℕ) : ℕ := rect x (Nat.xor (Nat.shiftRight x 12) 4095) 12

theorem rect_tb (x J i : ℕ) (hJ : J.testBit i = true) : ∀ n e : ℕ, e < n → x.testBit e = true →
    (rect x J n).testBit (12 * e + i) = true := by
  intro n
  induction n with
  | zero => intro e he; omega
  | succ n ih =>
    intro e he hx
    show ((cond (tb x n) (J <<< (12 * n)) 0) ||| rect x J n).testBit (12 * e + i) = true
    rw [Nat.testBit_or]
    by_cases hen : e = n
    · subst hen
      rw [tb_eq, hx]
      simp [Nat.testBit_shiftLeft, hJ]
    · rw [ih e (by omega) hx]
      simp

theorem rectW_tb (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e = true)
    (h2 : x.testBit (12 + i) = false) : (rectW x).testBit (12 * e + i) = true := by
  apply rect_tb _ _ _ _ 12 e he h1
  show ((x >>> 12) ^^^ 4095).testBit i = true
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, h2, tb4095]
  simp [hi]

def full : ℕ := 22300745198530623141535718272648361505980415

theorem full_eq : full = 2 ^ 144 - 1 := by norm_num [full]

theorem tb_land (a b q : ℕ) : (Nat.land a b).testBit q = (a.testBit q && b.testBit q) :=
  Nat.testBit_and a b q

theorem tb_lor (a b q : ℕ) : (Nat.lor a b).testBit q = (a.testBit q || b.testBit q) :=
  Nat.testBit_or a b q

theorem tb_xor (a b q : ℕ) : (Nat.xor a b).testBit q = Bool.xor (a.testBit q) (b.testBit q) :=
  Nat.testBit_xor a b q

theorem full_tb (q : ℕ) : full.testBit q = decide (q < 144) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem land_sub (h a : ℕ) (H : ∀ q, h.testBit q = true → a.testBit q = true) :
    Nat.land h a = h := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land]
  cases hh : h.testBit q
  · rfl
  · rw [H q hh]; rfl

theorem land_disj (a h : ℕ) (H : ∀ q, a.testBit q = true → h.testBit q = true → False) :
    Nat.land a h = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land, Nat.zero_testBit]
  cases ha : a.testBit q
  · rfl
  · cases hh : h.testBit q
    · rfl
    · exact (H q ha hh).elim

def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)

def orSL (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)

theorem orS_tb (x s q : ℕ) : (orS x s).testBit q = (x.testBit q || x.testBit (s + q)) := by
  show (x ||| x >>> s).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_shiftRight]

theorem orSL_tb (x s q : ℕ) :
    (orSL x s).testBit q = (x.testBit q || (decide (s ≤ q) && x.testBit (q - s))) := by
  show (x ||| x <<< s).testBit q = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]

theorem orS_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ p.testBit (k * j + q) = true) (q : ℕ)
    (h : (orS x (k * s)).testBit q = true) : ∃ j, j < n + s ∧ p.testBit (k * j + q) = true := by
  rw [orS_tb, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨j, hj, hp⟩ := hx q h
    exact ⟨j, by omega, hp⟩
  · obtain ⟨j, hj, hp⟩ := hx _ h
    refine ⟨j + s, by omega, ?_⟩
    rw [Nat.mul_add, Nat.add_assoc]; exact hp

theorem orSL_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true)
    (q : ℕ) (h : (orSL x (k * s)).testBit q = true) :
    ∃ j, j < n + s ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true := by
  rw [orSL_tb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hs, h⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx q h
    exact ⟨j, by omega, hq, hp⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx _ h
    have e : q - k * (j + s) = q - k * s - k * j := by rw [Nat.mul_add]; omega
    refine ⟨j + s, by omega, ?_, ?_⟩
    · rw [Nat.mul_add]; omega
    · rw [e]; exact hp

def rowM : ℕ := 5445847423328601499764522166702896582657

theorem rowM_tb (q : ℕ) (h : rowM.testBit q = true) : q < 144 ∧ q % 12 = 0 := by
  have hlt : q < 144 := by
    by_contra hq
    have h0 : rowM.testBit q = false := by
      apply Nat.testBit_lt_two_pow
      have h1 : rowM < 2 ^ 144 := by norm_num [rowM]
      have h2 : (2 : ℕ) ^ 144 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [h0] at h
    exact Bool.noConfusion h
  have hall : ∀ q : ℕ, q < 144 → rowM.testBit q = true → q % 12 = 0 := by decide +kernel
  exact ⟨hlt, hall q hlt h⟩

def rowsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) rowM

def colsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095

def hullC (p : ℕ) : ℕ :=
  Nat.land (orSL (orSL (orSL (orSL (rowsOf p) 6) 3) 1) 1)
    (orSL (orSL (orSL (orSL (colsOf p) 96) 48) 24) 12)

def hull (p : ℕ) : ℕ := hullC (Nat.land p full)

theorem rowsOf_tb (p q : ℕ) (h : (rowsOf p).testBit q = true) :
    (q < 144 ∧ q % 12 = 0) ∧ ∃ j, j < 12 ∧ p.testBit (j + q) = true := by
  unfold rowsOf at h
  rw [tb_land, Bool.and_eq_true] at h
  refine ⟨rowM_tb q h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (1 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 1 p _ 1 6 h0
  have h2 := orS_ex 1 p _ _ 3 h1
  have h3 := orS_ex 1 p _ _ 1 h2
  have h4 := orS_ex 1 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, by simpa using hp⟩

theorem colsOf_tb (p q : ℕ) (h : (colsOf p).testBit q = true) :
    q < 12 ∧ ∃ j, j < 16 ∧ p.testBit (12 * j + q) = true := by
  unfold colsOf at h
  rw [tb_land, Bool.and_eq_true, tb4095, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (12 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 12 p _ 1 8 h0
  have h2 := orS_ex 12 p _ _ 4 h1
  have h3 := orS_ex 12 p _ _ 2 h2
  have h4 := orS_ex 12 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, hp⟩

theorem hullC_spec (p : ℕ) (hp : ∀ q, p.testBit q = true → q < 144) (q : ℕ)
    (h : (hullC p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  unfold hullC at h
  rw [tb_land, Bool.and_eq_true] at h
  obtain ⟨hR, hC⟩ := h
  have r0 : ∀ q, (rowsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 1 * j ≤ q ∧ (rowsOf p).testBit (q - 1 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have r1 := orSL_ex 1 (rowsOf p) _ 1 6 r0
  have r2 := orSL_ex 1 (rowsOf p) _ _ 3 r1
  have r3 := orSL_ex 1 (rowsOf p) _ _ 1 r2
  have r4 := orSL_ex 1 (rowsOf p) _ _ 1 r3
  obtain ⟨j, hj, hjq, hr⟩ := r4 q hR
  obtain ⟨⟨hb, hm⟩, i, hi, hpi⟩ := rowsOf_tb p _ hr
  have c0 : ∀ q, (colsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 12 * j ≤ q ∧ (colsOf p).testBit (q - 12 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have c1 := orSL_ex 12 (colsOf p) _ 1 8 c0
  have c2 := orSL_ex 12 (colsOf p) _ _ 4 c1
  have c3 := orSL_ex 12 (colsOf p) _ _ 2 c2
  have c4 := orSL_ex 12 (colsOf p) _ _ 1 c3
  obtain ⟨j', hj', hjq', hc⟩ := c4 q hC
  obtain ⟨hlt, e', he', hpe⟩ := colsOf_tb p _ hc
  have e1 : i + (q - 1 * j) = 12 * (q / 12) + i := by omega
  have e2 : q - 12 * j' = q % 12 := by omega
  rw [e1] at hpi
  rw [e2] at hpe
  have hb' := hp _ hpe
  exact ⟨by omega, i, e', hi, by omega, hpi, hpe⟩

theorem hull_spec (p q : ℕ) (h : (hull p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  have hp : ∀ q, (Nat.land p full).testBit q = true → q < 144 := by
    intro q hq
    rw [tb_land, full_tb, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  obtain ⟨h1, i, e', hi, he, ha, hb⟩ := hullC_spec _ hp q h
  rw [tb_land, Bool.and_eq_true] at ha hb
  exact ⟨h1, i, e', hi, he, ha.1, hb.1⟩

def tw : List ℕ → ℕ → ℕ → ℕ
  | [], _, t => t
  | a :: l, o, t => tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))

def priv (t a : ℕ) : ℕ := hull (Nat.land a (Nat.xor t full))

def hullsOK (t : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, acc => Nat.beq (Nat.land (priv t a) a) (priv t a) &&
      (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a)))

def avOK1 (as : List ℕ) : Bool := hullsOK (tw as 0 0) as 0

def orL : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.lor a (orL l)

def rectOK1 (l : List ℕ) : Bool := avOK1 (l.map rectW)

def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')

def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs, IsRect z.1) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)) ∧
  (∀ q, q < 144 → ∃ z ∈ zs, z.1 q) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true)

theorem Part.rect {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, IsRect z.1 := h.1

theorem Part.bnd {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → q < 144 := h.2.1

theorem Part.disj {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) := h.2.2.1

theorem Part.cov {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ q, q < 144 → ∃ z ∈ zs, z.1 q := h.2.2.2.1

theorem Part.sub {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true := h.2.2.2.2


theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ l : List α, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro h a ha b hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact h.1 b hb'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']; exact hs _ _ (h.1 a ha')
      · exact ih h.2 a ha' b hb' hab

theorem tw_spec (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ), (tw as o t).testBit q = false →
    t.testBit q = false ∧ (o.testBit q = true → ∀ a ∈ as, a.testBit q = false) ∧
    as.Pairwise (fun a b => ¬ (a.testBit q = true ∧ b.testBit q = true)) := by
  intro as
  induction as with
  | nil => intro o t h; exact ⟨h, fun _ a ha => by simp at ha, List.Pairwise.nil⟩
  | cons a l ih =>
    intro o t h
    obtain ⟨h1, h2, h3⟩ := ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
    rw [tb_lor, Bool.or_eq_false_iff, tb_land] at h1
    refine ⟨h1.1, ?_, ?_⟩
    · intro ho b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h4 := h1.2
        rw [ho] at h4
        simpa using h4
      · exact h2 (by rw [tb_lor, ho]; rfl) b hb
    · refine List.pairwise_cons.mpr ⟨?_, h3⟩
      intro b hb hab
      have h4 := h2 (by rw [tb_lor, hab.1]; simp) b hb
      rw [h4] at hab
      exact Bool.noConfusion hab.2

theorem priv_in {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) : ∀ z ∈ zs, ∀ q,
    (priv (tw (zs.map Prod.snd) 0 0) z.2).testBit q = true → z.1 q := by
  intro z hz q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) full)).testBit x = true → z.1 x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (zs.map Prod.snd) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z', hz', hzq⟩ := hP.cov x hx
    by_cases hzz : z' = z
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) zs hpw z' hz' z hz hzz
        ⟨hP.sub z' hz' x hzq, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

theorem hullsOK_sound (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
    (∀ z ∈ zs, ∀ q, (priv t z.2).testBit q = true → z.1 q) →
    (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true) →
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) →
    (∀ q, acc.testBit q = true → ∀ z ∈ zs, ¬ z.1 q) →
    hullsOK t (zs.map Prod.snd) acc = true := by
  intro zs
  induction zs with
  | nil => intros; rfl
  | cons z zs ih =>
    intro acc hh hs hd ha
    rw [List.pairwise_cons] at hd
    have hz := hh z List.mem_cons_self
    have e1 := land_sub _ _ (fun q hq => hs z List.mem_cons_self q (hz q hq))
    have e2 := land_disj acc (priv t z.2) (fun q h1 h2 => ha q h1 z List.mem_cons_self (hz q h2))
    have e3 := ih (Nat.lor acc (priv t z.2)) (fun z' hz' => hh z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' => hs z' (List.mem_cons_of_mem _ hz')) hd.2 (fun q hq z' hz' hz'q => by
        rw [tb_lor, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
        · exact hd.1 z' hz' q (hz q hq) hz'q)
    show (Nat.beq (Nat.land (priv t z.2) z.2) (priv t z.2) &&
      (Nat.beq (Nat.land acc (priv t z.2)) 0 &&
        hullsOK t (zs.map Prod.snd) (Nat.lor acc (priv t z.2)))) = true
    rw [e1, e2, e3, Nat.beq_refl]
    rfl

theorem avOK1_sound {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    avOK1 (zs.map Prod.snd) = true :=
  hullsOK_sound _ zs 0 (priv_in hP) hP.sub hP.disj (fun q hq => by simp at hq)

end PackedRect

abbrev Witness := Word × Nat × Nat

def witnessWord (w : Witness) : Word := w.1

def essentialB (mask target : Word) (stock : List Word) (entry : Witness) : Bool :=
  let (w,p,n) := entry
  mask.testBit p && mask.testBit n && target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x => x == w || x.testBit p == x.testBit n)

theorem essentialRequired {stock : List Word} {entry : Witness} {S : Finset Word} {k t : Nat}
    (ok : essentialB mask target stock entry = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    witnessWord entry ∈ S := by
  obtain ⟨w,p,n⟩ := entry
  simp only [essentialB, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp,mn⟩,tp⟩,tn⟩,unequal⟩,rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S, AgreesAt p n x := by
    intro x hx
    have h := List.all_eq_true.mp rest x (sub x hx)
    have hw : x ≠ w := fun e => no (by simpa [witnessWord, e] using hx)
    simpa [hw, AgreesAt] using h
  have agree := liveAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt, tp, falseBit] at agree

theorem essentialWordsIn {stock : List Word} {witnesses : List Witness} {S : Finset Word} {k t : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    (witnesses.map witnessWord).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequired (List.all_eq_true.mp ok entry mem) sub live

theorem essentialLower {stock : List Word} {witnesses : List Witness} {minimum : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (bound : minimum ≤ (witnesses.map witnessWord).toFinset.card - 1) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have card := Finset.card_le_card (essentialWordsIn ok sub live)
  have size := (liveWordSize live).2
  omega

theorem essentialLift {stock cutStock : List Word} {witnesses : List Witness} {minimum cut prior : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : properWord cut (target &&& cut))
    (supplies : ∀ w ∈ stock, AvailableWord cut cutStock (w &&& cut))
    (known : Lower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map witnessWord).toFinset).card) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have subW := essentialWordsIn ok sub live
  have subFlat : flatSet cut (witnesses.map witnessWord).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat, properWord] using cutProper
  obtain ⟨n, budget, built⟩ := maskedBuild live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S, AvailableWord cut cutStock w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x,hx,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact supplies _ (sub _ hx)
  obtain ⟨ys,len,built',out⟩ := buildableWords built starts
  have lower := known ys built' out
  omega

def unpackWitnesses (stock : List Word) (codes : List Nat) : List Witness :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0, (code >>> 9) &&& 511, code &&& 511) :: rest) codes

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

def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset ^^^ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun j _ next i => (if row.testBit i then 1 <<< j else 0) ||| next (i + 1)) axes) 0

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

theorem maskedTransfer {mask w : Word} {select : Fin rows → Fin rows}
    (same : relabel select mask = mask) (hw : Masked mask w) :
    Masked mask (relabel select w) := by
  unfold Masked at *
  rw [← same, ← relabelAnd, hw]

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

abbrev RowChart := { rows : List Nat // rows.length = 24 }

def chartRow (chart : RowChart) (i : Nat) : Nat :=
  chart.val.getD i 0

def chartBits (w : Word) (rows : List Nat) : Word :=
  List.rec 0 (fun r _ packed => ((w >>> r) &&& 1) ||| (packed <<< 1)) rows

theorem chartBitsBit (w : Word) (rows : List Nat) (i : Nat) (hi : i < rows.length) :
    (chartBits w rows).testBit i = w.testBit (rows.getD i 0) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    change (((w >>> row) &&& 1) ||| (chartBits w rows <<< 1)).testBit i = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have lt : i < rows.length := by simpa using hi
      simp [ih i lt, Nat.testBit_succ]

def chartWord (chart : RowChart) (w : Word) : Word := chartBits w chart.val

def ChartOK (goal : Word) (chart : RowChart) : Prop :=
  (∀ i : Fin 12, goal.testBit (chartRow chart i.val) = true) ∧
  (∀ i : Fin 12, goal.testBit (chartRow chart (12+i.val)) = false)

def chartCheck (goal : Word) (chart : Option RowChart) : Bool :=
  chart.all fun c => @decide (ChartOK goal c) (by unfold ChartOK; infer_instance)

theorem chartOfCheck {goal : Word} {chart : Option RowChart}
    (ok : chartCheck goal chart = true) (c : RowChart) (eq : chart = some c) :
    ChartOK goal c := by
  subst chart
  unfold ChartOK
  exact of_decide_eq_true ok

theorem chartWordBit (chart : RowChart) (w : Word) {i : Nat} (hi : i < 24) :
    (chartWord chart w).testBit i = w.testBit (chartRow chart i) := by
  exact chartBitsBit w chart.val i (by rw [chart.property]; exact hi)

theorem chartPos {goal : Word} {chart : RowChart} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart i) = true := ok.1 ⟨i,hi⟩

theorem chartNeg {goal : Word} {chart : RowChart} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart (12+i)) = false := ok.2 ⟨i,hi⟩

theorem chartRectangles {goal : Word} {chart : RowChart} {ws : List Word}
    (ok : ChartOK goal chart) (nd : ws.Nodup) (kw : KWPartition goal ws.toFinset) :
    PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨f, good, rectangle⟩ := kw
  let label := fun p n => f (chartRow chart p) (chartRow chart (12+n))
  let part := fun w => ((fun q : Nat => q < 144 ∧ label (q/12) (q % 12) = w),
    PackedRect.rectW (chartWord chart w))
  have partition : PackedRect.Part (ws.map part) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro z hz
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      intro p n p' n' hp hn hp' hn' h h'
      have divmod (a b : Nat) (lt : b < 12) :
          (12*a+b)/12 = a ∧ (12*a+b)%12 = b := by omega
      have h1 := h.2
      have h2 := h'.2
      rw [(divmod p n hn).1, (divmod p n hn).2] at h1
      rw [(divmod p' n' hn').1, (divmod p' n' hn').2] at h2
      refine ⟨by omega,?_⟩
      rw [(divmod p n' hn').1, (divmod p n' hn').2]
      exact (rectangle _ _ _ _ (chartPos ok hp) (chartPos ok hp') (chartNeg ok hn)
        (chartNeg ok hn') (h1.trans h2.symm)).trans h1
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      exact hq.1
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne q h1 h2 => hne (h1.2.symm.trans h2.2)) nd
    · intro q hq
      have member := (good _ _ (chartPos ok (show q/12 < 12 by omega))
        (chartNeg ok (Nat.mod_lt q (by decide : 0 < 12)))).1
      exact ⟨_, List.mem_map.mpr ⟨_,List.mem_toFinset.mp member,rfl⟩,hq,rfl⟩
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      obtain ⟨bound, same⟩ := hq
      have hp : q/12 < 12 := by omega
      have hn : q % 12 < 12 := Nat.mod_lt _ (by decide)
      have h := (good _ _ (chartPos ok hp) (chartNeg ok hn)).2
      change (label (q/12) (q % 12)).testBit (chartRow chart (q/12)) = true ∧
        (label (q/12) (q % 12)).testBit (chartRow chart (12+q % 12)) = false at h
      rw [same] at h
      have bit := PackedRect.rectW_tb (chartWord chart w) (q/12) (q % 12) hp hn
        ((chartWordBit chart w (by omega)).trans h.1)
        ((chartWordBit chart w (by omega)).trans h.2)
      rwa [Nat.div_add_mod] at bit
  have hw := PackedRect.avOK1_sound partition
  simpa only [PackedRect.rectOK1, List.map_map, Function.comp_def, part] using hw

theorem tightChart {goal mask : Word} {chart : RowChart} {ws : List Word} {fuel : Nat}
    (ok : ChartOK goal chart) (tight : ws.length = fuel + 1)
    (viable : WordViable mask goal (fuel,ws,[])) : PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change (ws : List Word).length + t ≤ k + 1 at card
  have ht : t = 0 := by omega
  have hk : ws.toFinset.card = k + 1 := by
    have q : ws.toFinset.card = ws.length := List.toFinset_card_of_nodup nd
    omega
  subst t
  exact chartRectangles ok nd (kwFromLive live hk)

def dagForceWord {α : Type} (word : Word) (cont : Word → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem dagForceWordEq {α : Type} (word : Word) (cont : Word → α) :
    dagForceWord word cont = cont word := by cases word <;> rfl

def dagForceWords (words : List Word) (cont : List Word → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Word → Bool) → Bool) (fun k => k [])
    (fun w _ next k => dagForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem dagForceWordsEq (words : List Word) (cont : List Word → Bool) :
    dagForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change dagForceWord w (fun v => dagForceWords ws (fun rest => cont (v :: rest))) = _
    rw [dagForceWordEq, ih]

def dagBoundCloses (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStart mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosure mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipes mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)

theorem dagBoundClosesEq (target : Word) (state : RowState) (bound : Bound) :
    dagBoundCloses target state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨mask, stock, lower, goal⟩ := bound
  simp [dagBoundCloses, boundCloses, dagForceWordsEq, dagForceWordEq, Nat.blt_eq]

def dagKnownCloses (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundCloses target state bound || later) bounds

theorem dagKnownClosesEq (target : Word) (bounds : List Bound) (state : RowState) :
    dagKnownCloses target bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundCloses target state bound || dagKnownCloses target bounds state) =
      (boundCloses target state bound || knownCloses target bounds state)
    rw [dagBoundClosesEq, ih]

abbrev DagLink := Nat × Nat
abbrev DagLinks := Nat → Nat → Option DagLink

def dagAllowedRoot (witnesses : List Witness) (ws : List Word) : Bool :=
  witnesses.all (fun entry => ws.contains (witnessWord entry))

def dagTrace (mask : Word) (stock : List Word) (fuel : Nat) (forest : Forest)
    (i : Nat) : Option RowState :=
  (Nat.rec (motive := fun _ => Nat → Option RowState) (fun _ => none)
    (fun _ previous j =>
      let (parent, token) := forest j
      if parent == 0 then
        if token < 2 ^ stock.length then some (rootState stock fuel token) else none
      else (previous (parent - 1)).bind (childState mask token)) (fuel + 1)) i

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

def dagPartition (directed : Bool) (ws : List Word) : Word → Word → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      dagForceWord (p &&& w) (fun up =>
        dagForceWord (n &&& w) (fun down =>
          rest up down &&
            dagForceWord (p ^^^ up) (fun offP =>
              dagForceWord (if directed then n else n ^^^ down) (rest offP))))) ws

theorem dagOffBits {v w : Word} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at bit ⊢

theorem dagPartitionSound {directed : Bool} {ws : List Word} {positive negative : Word}
    (fail : dagPartition directed ws positive negative = false) :
    ∃ p n, positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws, if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Word} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all
    apply hn
    apply Nat.eq_of_testBit_eq
    intro i
    simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0 || Nat.beq negative 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩ := nonempty (w := positive) (fun eq => by simp [eq] at fail)
    obtain ⟨n,hn⟩ := nonempty (w := negative) (fun eq => by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0 || Nat.beq negative 0 ||
      dagForceWord (positive &&& w) (fun up =>
        dagForceWord (negative &&& w) (fun down =>
          dagPartition directed ws up down &&
            dagForceWord (positive ^^^ up) (fun offP =>
              dagForceWord (if directed then negative else negative ^^^ down)
                (dagPartition directed ws offP))))) = false at fail
    simp only [dagForceWordEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2, hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := dagOffBits hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply dagOffBits
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2, hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail

theorem dagPartitionLive {mask goal : Word} {ws : List Word} {k t : Nat} {directed : Bool}
    (goalMask : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) :
    dagPartition directed ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : dagPartition directed ws goal (mask ^^^ goal) = false := by
    cases h : dagPartition directed ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p,n,hp,hn,agree⟩ := dagPartitionSound openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  cases mode : directed with
  | false =>
    have same := liveAgrees live (pm.trans nm.1.symm) (fun w hw => by
      simpa [mode,AgreesAt] using agree w (List.mem_toFinset.mp hw))
    simp [AgreesAt, hp, nm.2] at same
  | true =>
    have ht := noNot mode
    subst t
    obtain ⟨w,hw,a,b⟩ := liveDirected live hp nm.2
    have same := agree w (List.mem_toFinset.mp hw)
    simp [mode, a, b] at same

abbrev DagSample := Nat × Nat
abbrev DagSignals := Word × Word
abbrev DagCounts := Word × Word × Word

def dagForceCache (tags : List DagSignals) (use : List DagSignals → Bool) : Bool :=
  (List.rec (motive := fun _ => (List DagSignals → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      dagForceWord tag.1 (fun up => dagForceWord tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use

theorem dagForceCacheEq (tags : List DagSignals) (use : List DagSignals → Bool) :
    dagForceCache tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change dagForceWord a (fun up => dagForceWord b (fun down =>
      dagForceCache rest (fun tail => use ((up,down)::tail)))) = _
    simp only [dagForceWordEq, ih]

def dagSignalContrast (directed : Bool) (full : Word) (tag : DagSignals) : Word :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2

def dagCountStep (acc : DagCounts) (column : Word) : DagCounts :=
  (acc.1 ||| column, acc.2.1 ||| (acc.1 &&& column), acc.2.2 ||| (acc.2.1 &&& column))

def dagCountSigns (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : Bool :=
  (List.rec (motive := fun _ => (DagCounts → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      dagForceWord (dagSignalContrast directed full tag) (fun column =>
        more (fun acc =>
          dagForceWord (acc.1 ||| column) (fun once =>
            dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use

theorem dagCountSignsEq (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : dagCountSigns directed full tags use =
    use (tags.foldr (fun tag acc => dagCountStep acc (dagSignalContrast directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change dagForceWord (dagSignalContrast directed full tag) (fun column =>
      dagCountSigns directed full tags (fun acc =>
        dagForceWord (acc.1 ||| column) (fun once =>
          dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [dagForceWordEq, ih]
    rfl

def dagHighest (value : Word) : Nat :=
  (Nat.rec (motive := fun _ => Word → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      dagForceWord (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset+shift))) 8) value 0

def dagSampleMiss (sample : DagSample) (full : Word) (normal tight : DagCounts)
    (x y out : DagSignals) (directed : Bool) (op keep : Nat) : List Nat :=
  let counts := if directed then tight else normal
  let dx := if keep.testBit 0 then 0 else dagSignalContrast directed full x
  let dy := if op == 2 || keep.testBit 1 then 0 else dagSignalContrast directed full y
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| dagSignalContrast directed full out) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then [] else [unpack sample.1 18 (dagHighest missing)])

def dagPairReject (mask goal : Word) (directed : Bool) (ws : List Word) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)

theorem dagPairsOpen {mask goal : Word} {ws : List Word} {pairs : List Nat} {k t : Nat} {directed : Bool}
    (masked : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) : dagPairReject mask goal directed ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code,_,check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true, Bool.not_eq_true, List.all_eq_true] at check
  obtain ⟨⟨⟨hp, mn⟩, hn⟩, bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  cases mode : directed
  · have h := liveAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
      have pair := bank _ (List.mem_toFinset.mp hw)
      simpa [mode, AgreesAt] using pair)
    simp [AgreesAt, hp, neg] at h
  · have ht := noNot mode
    subst t
    obtain ⟨word,mem,on,off⟩ := liveDirected live hp neg
    have pair := bank _ (List.mem_toFinset.mp mem)
    simp [mode,on,off] at pair

def dagLocal (mask goal : Word) (chart : Option RowChart)
    (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel,ws,_) := state
  ws.length > fuel + 1 ||
    (!ws.contains goal &&
      (fuel == 0 ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) ||
        cut state ||
        (if ws.length == fuel + 1 then !dagPartition true ws goal (mask ^^^ goal)
         else !dagPartition false ws goal (mask ^^^ goal))))

def dagSizeFloor (n op keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) -
    (if op == 2 || keep.testBit 1 then 0 else 1)) + 1

def dagTooWide (n fuel token : Nat) : Bool :=
  dagSizeFloor n (token / 4 % 3) (token % 4) > (fuel-1) + 1

def dagKept (ws : List Word) (op keep x y : Nat) : List Word :=
  keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)

def dagGateWord (mask op x y : Word) : Word :=
  if Nat.beq op 0 then x &&& y else if Nat.beq op 1 then x ||| y else mask ^^^ x

def dagDirectChild (mask : Word) (state : RowState) (a b op keep x y out : Nat) : Option RowState :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    some (fuel-1, insertWord out (dagKept ws op keep x y), (out,x,y) :: history)

theorem dagDirectChildEq {mask a b op keep : Nat} {state : RowState}
    (hb : b < 64) (hop : op < 3) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    dagDirectChild mask state a b op keep x y (dagGateWord mask op x y) =
      childState mask (gateToken a b op keep) state := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨keepEq,opEq,aEq,bEq⟩ := gateTokenFields (a := a) hb hop hk
  simp only [childState, keepEq, opEq, aEq, bEq]
  rfl

abbrev DagTagged := Word × DagSignals

def dagTagBases (stock : List Word) (positive negative width : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun w _ next i => (w, unpack positive width i, unpack negative width i) :: next (i+1)) stock) 0

def dagTagRoot (bank : List DagTagged) (token : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token

def dagTagKeep (keep : Bool) (w : Word) (bank : List DagTagged) : List DagTagged :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank

def dagTagInsert (tag : DagTagged) (bank : List DagTagged) : List DagTagged :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank

def dagTagStep (mask full token : Word) (bank : List DagTagged) : List DagTagged :=
  let keep := token % 4
  let op := token / 4 % 3
  let x := bank.getD (token / (4*3*64)) (0,0,0)
  let y := bank.getD (token / (4*3) % 64) (0,0,0)
  let tag := (dagGateWord mask op x.1 y.1, dagGateWord full op x.2.1 y.2.1, dagGateWord full op x.2.2 y.2.2)
  dagTagInsert tag (dagTagKeep (op == 2 || keep.testBit 1) y.1 (dagTagKeep (keep.testBit 0) x.1 bank))

def dagTraceTags (mask width : Word) (root : List DagTagged) (fuel : Nat) (forest : Forest)
    (i : Nat) : List DagSignals :=
  let tags := (Nat.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun _ previous j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then dagTagRoot root token
      else dagTagStep mask (fullMask width) token (previous (parent-1))) (fuel+1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags

def dagPackWords (ws : List Word) : Word :=
  List.rec 0 (fun w _ tail => (w &&& fullMask 512) ||| (tail <<< 512)) ws

def dagLaneMarks (n : Nat) : Word :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 512)) n

def dagOmitted (a b : Nat) (left right : Bool) : Word :=
  (if left then 0 else 1 <<< (512*a)) ||| (if right then 0 else 1 <<< (512*b))

def dagPackedPair (mask goal packed marks erased out : Word) (directed : Bool) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    dagForceWord code (fun code =>
      dagForceWord (code &&& 511) (fun p =>
        dagForceWord (code >>> 9) (fun n =>
          let up := (packed >>> p) &&& marks
          let down := (packed >>> n) &&& marks
          let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
          let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
          goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 512 && Nat.blt n 512 &&
            gateOK && Nat.beq (contrast &&& (marks ^^^ erased)) 0)))

theorem dagPackBits {ws : List Word} {i row : Nat} (inside : i < ws.length) (width : row < 512) :
    (dagPackWords ws).testBit (512*i+row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 512) ||| (dagPackWords ws <<< 512)).testBit (512*i+row) = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp [fullMask, Nat.testBit_two_pow_sub_one, width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 512 ≤ 512*i.succ+row := by omega
      have offset : 512*i.succ+row-512 = 512*i+row := by omega
      have past : ¬ 512*i.succ+row < 512 := by omega
      simp [crossed, offset, fullMask, Nat.testBit_two_pow_sub_one, past, ih hi]

theorem dagMarkBits {length i : Nat} (inside : i < length) :
    (dagLaneMarks length).testBit (512*i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks length <<< 512)).testBit (512*i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 512 ≤ 512*i.succ := by omega
      have offset : 512*i.succ-512 = 512*i := by omega
      simp [crossed, offset, ih hi]

def dagCheckChildren (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (reference : Nat → RowState → Bool) (state : RowState) (sample : DagSample) (tags : List DagSignals) : Bool :=
  let n := state.2.1.length
  (n ≤ 64) && !state.2.1.contains goal &&
  dagForceWord (dagPackWords state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        dagCountSigns true full tags (fun tight =>
          let visit := fun a b op retains =>
            dagForceWord (state.2.1.getD a 0) (fun x =>
              dagForceWord (state.2.1.getD b 0) (fun y =>
                dagForceWord (dagGateWord mask op x y) (fun out =>
                  let xs := tags.getD a (0,0)
                  let ys := tags.getD b (0,0)
                  dagForceWord (dagGateWord full op xs.1 ys.1) (fun up =>
                    dagForceWord (dagGateWord full op xs.2 ys.2) (fun down =>
                      treeBlock 0 retains (fun keep =>
                        let token := gateToken a b op keep
                        if dagTooWide n state.1 token then true else
                          let directed := dagSizeFloor n op keep == (state.1-1)+1
                          let pairs := dagSampleMiss sample full normal tight xs ys (up,down) directed op keep
                          let erased := dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)
                          if dagPackedPair mask goal packed marks erased out directed pairs then true
                          else match dagDirectChild mask state a b op keep x y out with
                          | none => true
                          | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                            let child := (fuel, forced, history)
                            reference token child || dagLocal mask goal chart cut child)))))))
          treeBlock 0 n (fun a =>
            visit a a 2 2 && treeBlock (a+1) (n-(a+1)) (fun b =>
              treeBlock 0 2 (fun op => visit a b op 4)))))))))

def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)

theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩

def dagCheckNode (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (count : Nat) (states : Nat → Option RowState) (moves : Array WordMove) (links : DagLinks)
    (sample : DagSample) (tags : Nat → List DagSignals) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) => dagForceWords ws (fun forced =>
      dagStateOK mask forced && dagCheckChildren mask goal chart cut
        (dagRef count states moves links (i+1)) (fuel, forced, history) sample (tags i))

def dagCheckRoots (mask goal : Word) (chart : Option RowChart) (cut : CutCheck)
    (witnesses : List Witness) (reference : Nat → RowState → Bool) (stock : List Word)
    (fuel : Nat) : Bool :=
  treeBlock 0 (2^stock.length) fun token =>
    let state := rootState stock fuel token
    !dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart cut state || reference token state

theorem dagLocalOpen {mask goal : Word} {chart : Option RowChart}
    {cut : CutCheck} {state : RowState}
    (masked : Masked mask goal) (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (viable : WordViable mask goal state) (noCut : cut state = false) :
    dagLocal mask goal chart cut state = false := by
  obtain ⟨fuel,ws,history⟩ := state
  have ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length + t ≤ k + 1 at card
  have fit : ¬ ws.length > fuel + 1 := by omega
  by_cases hz : fuel = 0
  · have kz : k = 0 := by omega
    subst k
    obtain ⟨_,eq,_⟩ := live
    have hm : goal ∈ ws := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [dagLocal, fit, hm]
  by_cases tight : ws.length = fuel + 1
  · have ht : t = 0 := by omega
    subst t
    have dir := dagPartitionLive (directed := true) masked live (fun _ => rfl)
    have noChart : chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c))) = false := by
      cases opt : chart with
      | none => rfl
      | some c =>
        have vt : WordViable mask goal (fuel,ws,[]) := viable
        have ok := tightChart (chartOK c opt) tight vt
        simp [ok]
    simp [dagLocal, fit, hz, tight, dir, noCut, noChart]
  · have sep := dagPartitionLive (directed := false) masked live (by simp)
    simp [dagLocal, fit, hz, tight, sep, noCut]

theorem dagInsertLength (w : Word) (ws : List Word) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]

theorem dagKeepLength (keep : Bool) (w : Word) (ws : List Word) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]

theorem dagWideChild {mask token : Nat} {state child : RowState}
    (eval : childState mask token state = some child)
    (wide : dagTooWide state.2.1.length state.1 token = true) :
    child.2.1.length > child.1 + 1 := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let i := token / (4 * 3 * 64)
  let j := token / (4 * 3) % 64
  let x := ws.getD i 0
  let y := ws.getD j 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let a := keep.testBit 0
  let b := op == 2 || keep.testBit 1
  let rest := keepWord b y (keepWord a x ws)
  let bad : Bool := fuel == 0 || j ≥ ws.length || (if op == 2 then i != j || keep ≥ 2 else i ≥ j)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [dagInsertLength]
  have h1 := dagKeepLength a x ws
  have h2 := dagKeepLength b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega

theorem dagKeepMem {ws : List Word} {x w : Word} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord, nd.mem_erase_iff, and_comm] using h
  · simpa [keepWord] using h

theorem dagKeepNodup {ws : List Word} (nd : ws.Nodup) (keep : Bool) (x : Word) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd

theorem dagPackedPairSound {mask goal out : Word} {ws : List Word} {directed : Bool}
    {pairs : List Nat} {a b : Nat} {left right : Bool}
    (nd : ws.Nodup)
    (checked : dagPackedPair mask goal (dagPackWords ws) (dagLaneMarks ws.length)
      (dagOmitted a b left right) out directed pairs = true) :
    dagPairReject mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) pairs = true := by
  obtain ⟨code,mem,verdict⟩ := List.any_eq_true.mp checked
  apply List.any_eq_true.mpr
  refine ⟨code,mem,?_⟩
  simp only [dagForceWordEq, Bool.and_eq_true, Nat.blt_eq] at verdict
  obtain ⟨⟨⟨⟨⟨⟨hp, hn⟩, neg⟩, wp⟩, wn⟩, output⟩, closure⟩ := verdict
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp,hn⟩,neg⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := dagKeepMem (dagKeepNodup nd left (ws.getD a 0)) later
  have leftMem := dagKeepMem nd rightMem.1
  obtain ⟨i,inside,eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside] using eq
  have omitted : (dagOmitted a b left right).testBit (512*i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (512*j)).testBit (512*i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 512*j ≠ 512*i by omega]
    simp [dagOmitted, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks ws.length
  let signal := dagPackWords ws
  have mark : marks.testBit (512*i) = true := dagMarkBits inside
  have test {j : Nat} (within : j < 512) :
      ((signal >>> j) &&& marks).testBit (512*i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (512*i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted a b left right)).testBit (512*i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px,nx,pt,nt,Nat.testBit_and,Nat.testBit_xor,mark,omitted,p,n] at h ⊢

theorem dagEarlyOpen {mask goal a b op keep out : Nat} {state child : RowState}
    (masked : Masked mask goal) (viable : WordViable mask goal child)
    (parent : state.2.1.Nodup) (eval : dagDirectChild mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) (pairs : List Nat) :
    dagPackedPair mask goal (dagPackWords state.2.1) (dagLaneMarks state.2.1.length)
      (dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)) out
      (dagSizeFloor state.2.1.length op keep == (state.1-1)+1) pairs = false := by
  obtain ⟨fuel,ws,history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  have closed := dagPackedPairSound parent closed
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := out == 0 || out == mask || ws.contains out
  let bank := dagKept ws op keep x y
  change (if bad then none else if stale then none else
    some (fuel-1, insertWord out bank, (out,x,y)::history)) = some child at eval
  by_cases h : bad = true
  · simp [h] at eval
  by_cases h' : stale = true
  · simp [h,h'] at eval
  have eq : (fuel-1,insertWord out bank,(out,x,y)::history) = child := by simpa [h,h'] using eval
  subst child
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel-1 at cap
  have size := (liveWordSize live).2
  change (insertWord out bank : List Word).toFinset.card + t ≤ k+1 at size
  rw [List.toFinset_card_of_nodup nd, dagInsertLength] at size
  have same : (out::bank).toFinset = (insertWord out bank).toFinset := by
    ext w
    simp only [List.mem_toFinset, List.mem_cons, insertWordMem]
  have openBank := dagPairsOpen (pairs := pairs)
    (directed := dagSizeFloor ws.length op keep == (fuel-1)+1) masked (show LiveWord mask goal k t (out::bank).toFinset by rwa [same])
  have available : (dagSizeFloor ws.length op keep == (fuel-1)+1) = true → t = 0 := by
    intro directed
    have exactBudget := beq_iff_eq.mp directed
    have first := dagKeepLength (keep.testBit 0) x ws
    have second := dagKeepLength (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    change dagSizeFloor ws.length op keep = (fuel-1)+1 at exactBudget
    unfold dagSizeFloor at exactBudget
    dsimp only [bank, dagKept] at size
    omega
  have refuses := openBank available
  exact Bool.noConfusion (closed.symm.trans refuses)

theorem dagChildAt {mask goal : Word} {chart : Option RowChart}
    {cut : CutCheck} {ref : Nat → RowState → Bool} {state child : RowState} {sample : DagSample} {tags : List DagSignals} {a b op keep : Nat}
    (checked : dagCheckChildren mask goal chart cut ref state sample tags = true)
    (ha : a < state.2.1.length)
    (legal : (a = b ∧ op = 2 ∧ keep < 2) ∨ (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4))
    (eval : childState mask (gateToken a b op keep) state = some child)
    (masked : Masked mask goal) (viable : WordViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : dagLocal mask goal chart cut child = false) :
    ref (gateToken a b op keep) child = true := by
  have narrow : dagTooWide state.2.1.length state.1 (gateToken a b op keep) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have tooMany := dagWideChild eval h
    obtain ⟨f,w,path⟩ := child
    simp [dagLocal, tooMany] at openChild
  simp only [dagCheckChildren, dagForceCacheEq, dagForceWordEq, dagCountSignsEq,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  rcases Bool.and_eq_true_iff.mp atA with ⟨unary,binary⟩
  rcases legal with ⟨rfl,rfl,hk⟩ | ⟨ab,hb,hop,hk⟩
  · have atKeep := treeBlock_at unary (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := a) (op := 2)
      (keep := keep) (by omega) (by decide) (by omega)
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep
  · have atB := treeBlock_at binary (i := b) (by omega) (by omega)
    have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
    have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := b) (op := op)
      (keep := keep) (by omega) (by omega) hk
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep

theorem readWordMasked {mask : Word} {ws : List Word}
    (all : ∀ w ∈ ws, Masked mask w) (i : Nat) : Masked mask (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp [Masked]
  | some w => exact all w (List.mem_of_getElem? h)

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

theorem dagAllNodes {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {chart : Option RowChart}
    {cut : CutCheck} {forest : Forest} {moves : Array WordMove} {links : DagLinks} {sample : DagSample}
    {tags : Nat → List DagSignals}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (cutSound : ∀ s, WordViable mask goal s → cut s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNode mask goal chart cut count
      (dagTrace mask stock fuel forest) moves links sample tags) = true):
    ∀ cap i saved, i < count → dagTrace mask stock fuel forest i = some saved →
      saved.1 = cap → ∀ k t, k ≤ cap → ¬LiveWord mask goal k t saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k t kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : RowState := (remaining, words, history)
    let states := dagTrace mask stock fuel forest
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change dagCheckNode mask goal chart cut count states moves links sample tags i = true at checked
    simp only [dagCheckNode, stateEq, dagForceWordsEq, Bool.and_eq_true] at checked
    obtain ⟨nd,masked⟩ := dagStateOKSpec checked.1
    have ok := checked.2
    have viable : WordViable mask goal s := ⟨nd,k,t,sFuel ▸ kBound,live⟩
    have scanned := ok
    simp only [dagCheckChildren, Bool.and_eq_true, decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgress wide viable with hit | ⟨child, possible, cv⟩
    · simpa [hit] using absent
    obtain ⟨a,b,op,keep,ha,legal,eval⟩ := possible
    have r := dagChildAt ok ha legal eval goalMask cv nd (dagLocalOpen goalMask chartOK cv (cutSound _ cv))
    have ⟨less,cm⟩ := childStateData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_,k',t',fits,clive⟩ := cv
    obtain ⟨j,dest,bound,restore,fuelEq,tail⟩ :=
      dagLinked maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' t' fits tail

theorem lowerDag {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {chart : Option RowChart}
    {forest : Forest} {moves : Array WordMove} {links : DagLinks} {sample : DagSample}
    {tags : Nat → List DagSignals}
    {bounds : List Bound} {witnesses : List Witness}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w) (stockNd : stock.Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : Known bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (rootCheck : dagCheckRoots mask goal chart (dagKnownCloses goal bounds) witnesses
      (dagRef count (dagTrace mask stock fuel forest) moves links 0)
      stock fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNode mask goal chart (dagKnownCloses goal bounds)
      count (dagTrace mask stock fuel forest) moves links sample tags) = true) :
    Lower mask stock goal (fuel+1) := by
  intro values build hit
  by_contra! small
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive stockMasked build hit proper
  have included : S ⊆ stock.toFinset := fun w hw => List.mem_toFinset.mpr (sub w hw)
  obtain ⟨token,tokenBound,eq⟩ := rootToken stock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState stock fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : WordViable mask goal state := by
    refine ⟨(rootWordSublist stock token).nodup stockNd,k,t,?_,?_⟩
    · change k ≤ fuel
      omega
    · rwa [eq']
  have cutOpen (s : RowState) (h : WordViable mask goal s) : dagKnownCloses goal bounds s = false := by
    rw [dagKnownClosesEq]
    exact knownClosesSound known submasks h
  have openRoot := dagLocalOpen goalMask chartOK v (cutOpen _ v)
  have allowed : dagAllowedRoot witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset, eq']
    exact essentialRequired (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart (dagKnownCloses goal bounds) state ||
    dagRef count (dagTrace mask stock fuel forest) moves links 0 token state) = true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have finish := dagAllNodes maskBounds goalMask chartOK cutOpen autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveWord mask goal k t state.2.1.toFinset := by rwa [eq']
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact stockMasked _ ((rootWordSublist stock token).subset hw)
  obtain ⟨i,s,hi,restore,cap,plan⟩ := dagLinked maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k t fits plan

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

def projectDAGStock (mask : Word) (source : List Word) (indices : List Nat) : List Word :=
  List.rec [] (fun i _ rest => (mask &&& source.getD i 0) :: rest) indices

theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)

theorem suppliesOfCheck {oldMask : Word} {old new : List Word} {rename : Word → Word}
    (h : new.all (fun w => availableB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvailableWord oldMask old (rename w) := by
  intro w hw
  exact availableB_spec.mp (List.all_eq_true.mp h w hw)

def dagShift (mask : Word) (move : WordMove) (word : Word) : Word :=
  mixMove move (word &&& mask)

def dagShiftUnique (mask : Word) (move : WordMove) : Nat → Word → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      dagForceWord (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && dagForceWord (occupied ||| col) next)
    else next occupied)

theorem dagShiftLinear (mask : Word) (move : WordMove) : BitLinear (dagShift mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0

theorem dagShiftBasis (mask : Word) (move : WordMove) (i : Nat) :
    dagShift mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and, Nat.testBit_two_pow, same, h]
  rw [dagShift, select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp

theorem dagShiftUniqueSpec {mask : Word} {move : WordMove} {n : Nat} {occupied : Word}
    (ok : dagShiftUnique mask move n occupied = true) :
    (∀ j < n, ∀ b, (dagShift mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n, ∀ k < n, ∀ b, (dagShift mask move (2^j)).testBit b = true →
      (dagShift mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then dagForceWord col (fun w =>
      Nat.beq (w &&& occupied) 0 && dagForceWord (occupied ||| w) (dagShiftUnique mask move n))
      else dagShiftUnique mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,dagForceWordEq] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : dagShift mask move (2^n) = 0 := by simp [dagShiftBasis,active]
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · simp [same,dead] at h
        · exact existing j (by omega) b h
      · intro j hj k hk b a c
        by_cases e : j = n
        · simp [e,dead] at a
        by_cases e' : k = n
        · simp [e',dead] at c
        exact unique j (by omega) k (by omega) b a c
    · simp only [active,ite_true,dagForceWordEq,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : dagShift mask move (2^n) = col := by simp [dagShiftBasis,active,col]
      have old {j b : Nat} (hj : j < n) (h : (dagShift mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or, Bool.or_eq_false_iff] using existing j hj b h
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · rw [same,colEq] at h
          have bit := congrArg (fun w => Nat.testBit w b) disjoint
          simpa [Nat.testBit_and,h] using bit
        · exact (old (by omega) h).1
      · intro j hj k hk b a c
        by_cases e : j = n
        · by_cases e' : k = n
          · exact e.trans e'.symm
          · rw [e,colEq,(old (by omega) c).2] at a
            contradiction
        by_cases e' : k = n
        · rw [e',colEq,(old (by omega) a).2] at c
          contradiction
        exact unique j (by omega) k (by omega) b a c

theorem dagShiftGates {mask : Word} {move : WordMove} {width : Nat}
    (bounded : Masked (fullMask width) mask) (checked : dagShiftUnique mask move width 0 = true) :
    (∀ a b, dagShift mask move (a &&& b) = dagShift mask move a &&& dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ||| b) = dagShift mask move a ||| dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ^^^ b) = dagShift mask move a ^^^ dagShift mask move b) := by
  let f := dagShift mask move
  have lin := dagShiftLinear mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,dagShiftBasis,zero] at a
    exact (dagShiftUniqueSpec checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and, Bool.and_eq_true, lin, lin, lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and, Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i, Nat.testBit_or, Bool.or_eq_true, lin a i, lin b i]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨j,(left | right),same⟩
      · exact Or.inl ⟨j,left,same⟩
      · exact Or.inr ⟨j,right,same⟩
    · rintro (⟨j,left,same⟩ | ⟨j,right,same⟩)
      · exact ⟨j,Or.inl left,same⟩
      · exact ⟨j,Or.inr right,same⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have l := lin a i
    have r := lin b i
    have v := lin (a ^^^ b) i
    cases pa : (f a).testBit i <;> cases pb : (f b).testBit i
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      have disj : a.testBit j = true ∨ b.testBit j = true := by
        rw [Nat.testBit_xor] at hj
        cases aj : a.testBit j <;> cases bj : b.testBit j <;> simp [aj,bj] at hj ⊢
      rcases disj with da | db
      · have := l.mpr ⟨j,da,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this
      · have := r.mpr ⟨j,db,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := r.mp pb
      have notA : a.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := l.mpr ⟨j,yes,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this)
      exact ⟨j,by simp [Nat.testBit_xor,notA,hj],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := l.mp pa
      have notB : b.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := r.mpr ⟨j,yes,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this)
      exact ⟨j,by simp [Nat.testBit_xor,hj,notB],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      obtain ⟨a',ha,q⟩ := l.mp pa
      obtain ⟨b',hb,r⟩ := r.mp pb
      have ea := uniq h q
      have eb := uniq h r
      rw [← ea] at ha
      rw [← eb] at hb
      simp [Nat.testBit_xor,ha,hb] at hj

def dagShiftCheck (width mask goal oldMask oldGoal : Word) (stock old : List Word) (move : WordMove) : Bool :=
  Nat.beq (mask &&& fullMask width) mask && dagShiftUnique mask move width 0 &&
    Nat.beq (dagShift mask move mask) oldMask && Nat.beq (dagShift mask move goal) oldGoal &&
    stock.all (fun w => availableB oldMask old (dagShift mask move w))

theorem dagShiftLower {width mask goal oldMask oldGoal : Word} {stock old : List Word} {min : Nat}
    (move : WordMove) (origin : Lower oldMask old oldGoal min)
    (ok : dagShiftCheck width mask goal oldMask oldGoal stock old move = true) :
    Lower mask stock goal min := by
  simp only [dagShiftCheck,Bool.and_eq_true,Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded,unique⟩,masks⟩,goals⟩,supply⟩ := ok
  obtain ⟨andG,orG,xorG⟩ := dagShiftGates bounded unique
  have zero : dagShift mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [dagShiftLinear]
    simp
  apply lowerMap (dagShift mask move) zero masks (fun w => by rw [xorG,masks]) andG orG (suppliesOfCheck supply)
  rwa [goals]

def moveSchedule (stages : Array WordMoveStep) (indices : List Nat) : WordMove :=
  List.rec [] (fun i _ rest => stages[i]?.getD ([],[]) :: rest) indices

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

theorem hcsGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    GateWord (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl | rfl
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact Or.inl ⟨0, zeroAv, by simpa [hcsGateVal] using notNat (0 : BitVec rows)⟩
    | cons a _ => exact Or.inl ⟨_, toNatAvailable bank a, by simpa [hcsGateVal] using notNat (bank.getD a 0)⟩

theorem hcsBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ WordBuilds (fullMask rows) (bank.map BitVec.toNat) vs ∧
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
    refine ⟨v.toNat :: xs, by simp [len], ⟨hcsGateWord bank g hg.1 hg.2, buildsWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

theorem hcsLowerEq {m1 m2 g1 g2 min : Nat} {b1 b2 : List Word}
    (hm : m1 = m2) (hb : b1 = b2) (hg : g1 = g2)
    (h : Lower m1 b1 g1 min) : Lower m2 b2 g2 min := by
  subst hm; subst hb; subst hg; exact h

theorem hcsLower {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) (min : Nat)
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (claim : Lower (fullMask (2 ^ n)) (raw.map BitVec.toNat) goal.toNat min)
    (t : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize n f t) : min ≤ t := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  obtain ⟨vs, len, built, sub⟩ := hcsBuilds raw C.gates hfan
  let eb := C.gates.foldl hcsStep raw
  have same : eb.getD C.output 0 = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let y : Fin n → Bool := fun k => j.testBit k.val
    have hbank : raw.map (fun v => v.getLsbD j) = List.ofFn y :=
      beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hfg : goal.getLsbD j = f y :=
      beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hbits := hcsFoldBits raw ⟨j, hj⟩ C.gates hfan
    have hevj : (C.wires (List.ofFn y)).getD C.output false = f y := hev y
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
      (List.ofFn y)).getD C.output false = f y at hevj
    rw [← hbank, ← hbits] at hevj
    rw [hfg, ← hevj, ← hcsGetDBit]
  have av : AvailableWord (fullMask (2 ^ n)) (vs ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← same, List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (Or.inr (sub v (List.mem_of_getElem? h)))
  have lb := claim vs built av
  have hs : C.gates.length ≤ t := hsz
  omega

def moveStage0 : WordMoveStep := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)])
def moveStage1 : WordMoveStep := ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])
def moveStage2 : WordMoveStep := ([(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 32)], [(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 32)])
def moveStage3 : WordMoveStep := ([(0x9999999999999999999999999999999999999999999999999999999999999999, 0), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x4444444444444444444444444444444444444444444444444444444444444444, 1)])
def moveStage4 : WordMoveStep := ([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)])
def moveStage5 : WordMoveStep := ([(0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f, 0), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60)], [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000, 60)])
def moveStage6 : WordMoveStep := ([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff, 0), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 24)])
def moveStage7 : WordMoveStep := ([(0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff, 0), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000, 48)])
def moveStage8 : WordMoveStep := ([(0xffffffffffffffff0000000000000000ffffffffffffffff, 64)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 64)])
def moveStage9 : WordMoveStep := ([(0xffffffffffffffffffffffffffffffff, 128)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])
def moveStage10 : WordMoveStep := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])
def moveStage11 : WordMoveStep := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000, 16)])
def moveStage12 : WordMoveStep := ([(0xff00ff00ff00ff0000ff00ff00ff00ffff00ff00ff00ff0000ff00ff00ff00ff, 0), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000, 56)])
def moveStage13 : WordMoveStep := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])
def moveStage14 : WordMoveStep := ([(0xcccccccccccccccc3333333333333333cccccccccccccccc3333333333333333, 0), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0x3333333333333333000000000000000033333333333333330000000000000000, 62)])
def moveStage15 : WordMoveStep := ([(0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0f, 0), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 28)])
def moveStage16 : WordMoveStep := ([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)])
def moveStage17 : WordMoveStep := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])
def moveStage18 : WordMoveStep := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])
def moveStage19 : WordMoveStep := ([(0xffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff, 0), (0xffffffff00000000ffffffff00000000, 96)], [(0xffffffff00000000ffffffff00000000000000000000000000000000, 96)])
def moveStage20 : WordMoveStep := ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])
def moveStage21 : WordMoveStep := ([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x5050505050505050505050505050505050505050505050505050505050505050, 3)])
def moveStage22 : WordMoveStep := ([(0xff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff, 0), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000, 120)])
def moveStages : Array WordMoveStep := #[moveStage0, moveStage1, moveStage2, moveStage3, moveStage4, moveStage5, moveStage6, moveStage7, moveStage8, moveStage9, moveStage10, moveStage11, moveStage12, moveStage13, moveStage14, moveStage15, moveStage16, moveStage17, moveStage18, moveStage19, moveStage20, moveStage21, moveStage22]
def sBase : List Word := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def sGoal : Word := 0xfffffffffffefefcfffefefcfffafaf8ffffffffffeeeeecffeeeeecffeaeae8
def s0Mask : Word := 0xff
abbrev s0Goal : Word := sGoal &&& s0Mask
abbrev s0StockWords : List Word := projectDAGStock s0Mask sBase [0, 1, 2]
def s0Fact : Bound := (s0Mask, s0StockWords, 4, s0Goal)
def s0Cuts : List Bound := []
def s0Chart : Option RowChart := some ⟨[3, 5, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1], rfl⟩
def s0Sample : DagSample := (0x201804060201402050100c0203, 6)
def s0Witnesses := unpackWitnesses s0StockWords [2564, 265220, 527362]
def s0Links : DagLinks := 
  dagLookupLinks 0x1 0x7 2 1 3 1 1 1
def s0Data : Forest := fun i => decodeNode 1 4 0xe i
def s0Tags := dagTraceTags s0Mask 6 (dagTagBases s0StockWords 0x3cccf 0x28485 6) 3 s0Data
def s0States := dagTrace s0Mask s0StockWords 3 s0Data
def s0MoveCert : List (DagMoveRecord 256) := []
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 256 s0Moves := dagMovesOfCheck (by decide +kernel)
def s0Check := dagCheckNode s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) 1 s0States s0Moves s0Links s0Sample s0Tags
def s0RootAt (token : Nat) : Bool :=
  let s := rootState s0StockWords 3 token
  !dagAllowedRoot s0Witnesses s.2.1 || dagLocal s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s ||
  dagRef 1 s0States s0Moves s0Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0RootBlock0 : treeBlock 0 8 s0RootAt = true := by decide +kernel
theorem s0Roots : dagCheckRoots s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s0Witnesses (dagRef 1 s0States s0Moves s0Links 0) s0StockWords 3 = true := s0RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block0 : treeBlock 0 1 s0Check = true := by decide +kernel
theorem s0Blocks : treeBlock 0 1 s0Check = true := s0Block0
theorem s0Known : Known s0Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Stock : Lower s0Mask s0StockWords s0Goal 4 := by
  apply lowerDag _ _ _ _ s0Autos _ _ _ s0Known _ s0Roots s0Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s0StockWords; decide +kernel
  · decide +kernel
  · simp only [s0Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s1Mask : Word := 0x3030303
abbrev s1Goal : Word := sGoal &&& s1Mask
abbrev s1StockWords : List Word := projectDAGStock s1Mask sBase [0, 3, 4]
def s1Fact : Bound := (s1Mask, s1StockWords, 4, s1Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Stock : Lower s1Mask s1StockWords s1Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [0, 1]) s0Stock (by decide +kernel)
def s2Mask : Word := 0x303030300000000
abbrev s2Goal : Word := sGoal &&& s2Mask
abbrev s2StockWords : List Word := projectDAGStock s2Mask sBase [0, 3, 4]
def s2Fact : Bound := (s2Mask, s2StockWords, 4, s2Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [0, 1, 2]) s0Stock (by decide +kernel)
def s3Mask : Word := 0x50000000500000005000000050000
abbrev s3Goal : Word := sGoal &&& s3Mask
abbrev s3StockWords : List Word := projectDAGStock s3Mask sBase [1, 5, 6]
def s3Fact : Bound := (s3Mask, s3StockWords, 4, s3Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Stock : Lower s3Mask s3StockWords s3Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 4, 5, 6, 7, 8]) s0Stock (by decide +kernel)
def s4Mask : Word := 0x303030300000000000000000000000000000000
abbrev s4Goal : Word := sGoal &&& s4Mask
abbrev s4StockWords : List Word := projectDAGStock s4Mask sBase [0, 3, 4]
def s4Fact : Bound := (s4Mask, s4StockWords, 4, s4Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Stock : Lower s4Mask s4StockWords s4Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [0, 1, 9]) s0Stock (by decide +kernel)
def s5Mask : Word := 0x500000005000000050000000500000000000000000000000000000000
abbrev s5Goal : Word := sGoal &&& s5Mask
abbrev s5StockWords : List Word := projectDAGStock s5Mask sBase [1, 5, 6]
def s5Fact : Bound := (s5Mask, s5StockWords, 4, s5Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Stock : Lower s5Mask s5StockWords s5Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 4, 5, 6, 7, 9]) s0Stock (by decide +kernel)
def s6Mask : Word := 0xffff
abbrev s6Goal : Word := sGoal &&& s6Mask
abbrev s6StockWords : List Word := projectDAGStock s6Mask sBase [0, 1, 2, 3]
def s6Fact : Bound := (s6Mask, s6StockWords, 5, s6Goal)
def s6Witnesses := unpackWitnesses s6StockWords [6668, 269324, 531466, 791041]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Stock : Lower s6Mask s6StockWords s6Goal 5 := by
  apply essentialLift (witnesses := s6Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s7Mask : Word := 0xff00ff
abbrev s7Goal : Word := sGoal &&& s7Mask
abbrev s7StockWords : List Word := projectDAGStock s7Mask sBase [0, 1, 2, 4]
def s7Fact : Bound := (s7Mask, s7StockWords, 5, s7Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Stock : Lower s7Mask s7StockWords s7Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [10]) s6Stock (by decide +kernel)
def s8Mask : Word := 0xf0f0f0f
abbrev s8Goal : Word := sGoal &&& s8Mask
abbrev s8StockWords : List Word := projectDAGStock s8Mask sBase [0, 1, 3, 4]
def s8Fact : Bound := (s8Mask, s8StockWords, 5, s8Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Stock : Lower s8Mask s8StockWords s8Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [0, 1]) s6Stock (by decide +kernel)
def s9Mask : Word := 0x33333333
abbrev s9Goal : Word := sGoal &&& s9Mask
abbrev s9StockWords : List Word := projectDAGStock s9Mask sBase [0, 2, 3, 4]
def s9Fact : Bound := (s9Mask, s9StockWords, 5, s9Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Stock : Lower s9Mask s9StockWords s9Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [0, 1, 10]) s6Stock (by decide +kernel)
def s10Mask : Word := 0xff000000ff
abbrev s10Goal : Word := sGoal &&& s10Mask
abbrev s10StockWords : List Word := projectDAGStock s10Mask sBase [0, 1, 2, 5]
def s10Fact : Bound := (s10Mask, s10StockWords, 5, s10Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Stock : Lower s10Mask s10StockWords s10Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 11]) s6Stock (by decide +kernel)
def s11Mask : Word := 0xf0f0f0f00000000
abbrev s11Goal : Word := sGoal &&& s11Mask
abbrev s11StockWords : List Word := projectDAGStock s11Mask sBase [0, 1, 3, 4]
def s11Fact : Bound := (s11Mask, s11StockWords, 5, s11Goal)
def s11Witnesses := unpackWitnesses s11StockWords [287792, 25136, 553008, 815144]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Stock : Lower s11Mask s11StockWords s11Goal 5 := by
  apply essentialLift (witnesses := s11Witnesses) (cut := s2Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s2StockWords) (by decide +kernel)
  · exact s2Stock
  · decide +kernel
def s12Mask : Word := 0x3333333300000000
abbrev s12Goal : Word := sGoal &&& s12Mask
abbrev s12StockWords : List Word := projectDAGStock s12Mask sBase [0, 2, 3, 4]
def s12Fact : Bound := (s12Mask, s12StockWords, 5, s12Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Stock : Lower s12Mask s12StockWords s12Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [0, 1, 10, 2]) s6Stock (by decide +kernel)
def s13Mask : Word := 0xf0f0f0f0000000000000000
abbrev s13Goal : Word := sGoal &&& s13Mask
abbrev s13StockWords : List Word := projectDAGStock s13Mask sBase [0, 1, 3, 4]
def s13Fact : Bound := (s13Mask, s13StockWords, 5, s13Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Stock : Lower s13Mask s13StockWords s13Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [2, 8]) s11Stock (by decide +kernel)
def s14Mask : Word := 0x333333330000000000000000
abbrev s14Goal : Word := sGoal &&& s14Mask
abbrev s14StockWords : List Word := projectDAGStock s14Mask sBase [0, 2, 3, 4]
def s14Fact : Bound := (s14Mask, s14StockWords, 5, s14Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Stock : Lower s14Mask s14StockWords s14Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [0, 1, 10, 8]) s6Stock (by decide +kernel)
def s15Mask : Word := 0xf0000000f0000000f0000000f00
abbrev s15Goal : Word := sGoal &&& s15Mask
abbrev s15StockWords : List Word := projectDAGStock s15Mask sBase [0, 1, 5, 6]
def s15Fact : Bound := (s15Mask, s15StockWords, 5, s15Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s11Stock (by decide +kernel)
def s16Mask : Word := 0xf0000000f0000000f0000000f0000
abbrev s16Goal : Word := sGoal &&& s16Mask
abbrev s16StockWords : List Word := projectDAGStock s16Mask sBase [0, 1, 5, 6]
def s16Fact : Bound := (s16Mask, s16StockWords, 5, s16Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7, 2, 8]) s11Stock (by decide +kernel)
def s17Mask : Word := 0x550000005500000055000000550000
abbrev s17Goal : Word := sGoal &&& s17Mask
abbrev s17StockWords : List Word := projectDAGStock s17Mask sBase [1, 2, 5, 6]
def s17Fact : Bound := (s17Mask, s17StockWords, 5, s17Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 4, 5, 12, 11, 13, 8]) s6Stock (by decide +kernel)
def s18Mask : Word := 0x3030303000000000303030300000000
abbrev s18Goal : Word := sGoal &&& s18Mask
abbrev s18StockWords : List Word := projectDAGStock s18Mask sBase [0, 3, 4, 6]
def s18Fact : Bound := (s18Mask, s18StockWords, 5, s18Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [14, 5, 13, 2, 8]) s11Stock (by decide +kernel)
def s19Mask : Word := 0x3030303030303030000000000000000
abbrev s19Goal : Word := sGoal &&& s19Mask
abbrev s19StockWords : List Word := projectDAGStock s19Mask sBase [0, 3, 4, 5]
def s19Fact : Bound := (s19Mask, s19StockWords, 5, s19Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [4, 15, 2, 8]) s11Stock (by decide +kernel)
def s20Mask : Word := 0x5000500050005000500050005000500
abbrev s20Goal : Word := sGoal &&& s20Mask
abbrev s20StockWords : List Word := projectDAGStock s20Mask sBase [1, 4, 5, 6]
def s20Fact : Bound := (s20Mask, s20StockWords, 5, s20Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 16, 1, 6, 7, 13, 2, 8]) s11Stock (by decide +kernel)
def s21Mask : Word := 0x5050000050500000505000005050000
abbrev s21Goal : Word := sGoal &&& s21Mask
abbrev s21StockWords : List Word := projectDAGStock s21Mask sBase [1, 3, 5, 6]
def s21Fact : Bound := (s21Mask, s21StockWords, 5, s21Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 0, 17, 6, 7, 2, 8]) s11Stock (by decide +kernel)
def s22Mask : Word := 0xf0f0f0f00000000000000000000000000000000
abbrev s22Goal : Word := sGoal &&& s22Mask
abbrev s22StockWords : List Word := projectDAGStock s22Mask sBase [0, 1, 3, 4]
def s22Fact : Bound := (s22Mask, s22StockWords, 5, s22Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [0, 1, 9]) s6Stock (by decide +kernel)
def s23Mask : Word := 0x5500000055000000550000005500000000000000000000000000000000
abbrev s23Goal : Word := sGoal &&& s23Mask
abbrev s23StockWords : List Word := projectDAGStock s23Mask sBase [1, 2, 5, 6]
def s23Fact : Bound := (s23Mask, s23StockWords, 5, s23Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Stock : Lower s23Mask s23StockWords s23Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 18, 6, 7, 2, 9]) s11Stock (by decide +kernel)
def s24Mask : Word := 0xffffffff
abbrev s24Goal : Word := sGoal &&& s24Mask
abbrev s24StockWords : List Word := projectDAGStock s24Mask sBase [0, 1, 2, 3, 4]
def s24Fact : Bound := (s24Mask, s24StockWords, 8, s24Goal)
def s24Cuts : List Bound := [s6Fact, s7Fact, s8Fact, s9Fact, s0Fact, s1Fact]
def s24Chart : Option RowChart := some ⟨[3, 5, 6, 9, 17, 24, 3, 3, 3, 3, 3, 3, 10, 12, 18, 20, 1, 10, 10, 10, 10, 10, 10, 10], rfl⟩
def s24Sample : DagSample := (0x281c06070241a0506824180a05824160a054241100844180e05038180d0502c02090601802050100c0203, 19)
def s24Witnesses := unpackWitnesses s24StockWords [10772, 273428, 535570, 800788, 1062924]
def s24Links : DagLinks := 
  dagLookupLinks 0x4cc0000003d03c01 0x3b0e0692c08c52ac388a4b1262008c52dc38964b1f6375d8ad56203ccdc732b14c52c037900ad401f1004c300904020001f 9 4 12 3 3 4
def s24Data : Forest := fun i => decodeNode 4 16 0x32b192c63141013100913142008101f0 i
def s24Tags := dagTraceTags s24Mask 19 (dagTagBases s24StockWords 0x7fe00f83e18e730d8d580e77 0x57c00503d18a520ea5100215 19) 7 s24Data
def s24States := dagTrace s24Mask s24StockWords 7 s24Data
def s24Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s24Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s24Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s24Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 5, 6, 7] 0 i.val)
def s24Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 5, 6, 7] 0 i.val)
def s24Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 5, 6, 7] 0 i.val)
def s24Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 3, 4, 1, 2, 5, 6, 7] 0 i.val)
def s24Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 3, 4, 1, 2, 5, 6, 7] 0 i.val)
def s24Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 3, 1, 2, 5, 6, 7] 0 i.val)
def s24Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 3, 4, 2, 1, 5, 6, 7] 0 i.val)
def s24MoveCert : List (DagMoveRecord 256) := [((moveSchedule moveStages [10]), s24Move0Map, s24Move0Inverse), ((moveSchedule moveStages [18]), s24Move1Map, s24Move1Inverse), ((moveSchedule moveStages [18, 10]), s24Move2Map, s24Move2Inverse), ((moveSchedule moveStages [0, 1]), s24Move3Map, s24Move3Inverse), ((moveSchedule moveStages [16, 17, 10]), s24Move4Map, s24Move4Inverse)]
def s24Moves := dagMoves s24MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Autos : DagMovesOK s24Mask s24Goal 256 s24Moves := dagMovesOfCheck (by decide +kernel)
def s24Check := dagCheckNode s24Mask s24Goal s24Chart (dagKnownCloses s24Goal s24Cuts) 8 s24States s24Moves s24Links s24Sample s24Tags
def s24RootAt (token : Nat) : Bool :=
  let s := rootState s24StockWords 7 token
  !dagAllowedRoot s24Witnesses s.2.1 || dagLocal s24Mask s24Goal s24Chart (dagKnownCloses s24Goal s24Cuts) s ||
  dagRef 8 s24States s24Moves s24Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24RootBlock0 : treeBlock 0 32 s24RootAt = true := by decide +kernel
theorem s24Roots : dagCheckRoots s24Mask s24Goal s24Chart (dagKnownCloses s24Goal s24Cuts) s24Witnesses (dagRef 8 s24States s24Moves s24Links 0) s24StockWords 7 = true := s24RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Block0 : treeBlock 0 8 s24Check = true := by decide +kernel
theorem s24Blocks : treeBlock 0 8 s24Check = true := s24Block0
theorem s24Known : Known s24Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s1Stock) s0Stock) s9Stock) s8Stock) s7Stock) s6Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Stock : Lower s24Mask s24StockWords s24Goal 8 := by
  apply lowerDag _ _ _ _ s24Autos _ _ _ s24Known _ s24Roots s24Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s24StockWords; decide +kernel
  · decide +kernel
  · simp only [s24Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s25Mask : Word := 0xffff0000ffff
abbrev s25Goal : Word := sGoal &&& s25Mask
abbrev s25StockWords : List Word := projectDAGStock s25Mask sBase [0, 1, 2, 3, 5]
def s25Fact : Bound := (s25Mask, s25StockWords, 6, s25Goal)
def s25Witnesses := unpackWitnesses s25StockWords [23084, 285740, 543265, 807457, 1070090]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Stock : Lower s25Mask s25StockWords s25Goal 6 := by
  apply essentialLift (witnesses := s25Witnesses) (cut := s10Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s10StockWords) (by decide +kernel)
  · exact s10Stock
  · decide +kernel
def s26Mask : Word := 0xf0f0f0f0f0f0f0f
abbrev s26Goal : Word := sGoal &&& s26Mask
abbrev s26StockWords : List Word := projectDAGStock s26Mask sBase [0, 1, 3, 4, 5]
def s26Fact : Bound := (s26Mask, s26StockWords, 7, s26Goal)
def s26Cuts : List Bound := [s8Fact, s11Fact, s2Fact]
def s26Chart : Option RowChart := some ⟨[3, 9, 17, 24, 34, 3, 3, 3, 3, 3, 3, 3, 10, 18, 33, 40, 48, 10, 10, 10, 10, 10, 10, 10], rfl⟩
def s26Sample : DagSample := (0x180e05038180c82432180c44231140a8142a140a4241a0506802090100c0203, 14)
def s26Witnesses := unpackWitnesses s26StockWords [25136, 287792, 553008, 815144, 1074194]
def s26Links : DagLinks := 
  dagLookupLinks 0xe1 0xd2589880804001f 5 2 12 2 1 2
def s26Data : Forest := fun i => decodeNode 2 13 0x620404207c i
def s26Tags := dagTraceTags s26Mask 14 (dagTagBases s26StockWords 0x3fe0fc630fc336c327 0x3ba0b8410e81168105 14) 6 s26Data
def s26States := dagTrace s26Mask s26StockWords 6 s26Data
def s26Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s26Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s26MoveCert : List (DagMoveRecord 256) := [((moveSchedule moveStages [10]), s26Move0Map, s26Move0Inverse)]
def s26Moves := dagMoves s26MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Autos : DagMovesOK s26Mask s26Goal 256 s26Moves := dagMovesOfCheck (by decide +kernel)
def s26Check := dagCheckNode s26Mask s26Goal s26Chart (dagKnownCloses s26Goal s26Cuts) 3 s26States s26Moves s26Links s26Sample s26Tags
def s26RootAt (token : Nat) : Bool :=
  let s := rootState s26StockWords 6 token
  !dagAllowedRoot s26Witnesses s.2.1 || dagLocal s26Mask s26Goal s26Chart (dagKnownCloses s26Goal s26Cuts) s ||
  dagRef 3 s26States s26Moves s26Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26RootBlock0 : treeBlock 0 32 s26RootAt = true := by decide +kernel
theorem s26Roots : dagCheckRoots s26Mask s26Goal s26Chart (dagKnownCloses s26Goal s26Cuts) s26Witnesses (dagRef 3 s26States s26Moves s26Links 0) s26StockWords 6 = true := s26RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Block0 : treeBlock 0 3 s26Check = true := by decide +kernel
theorem s26Blocks : treeBlock 0 3 s26Check = true := s26Block0
theorem s26Known : Known s26Cuts := extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s2Stock) s11Stock) s8Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Stock : Lower s26Mask s26StockWords s26Goal 7 := by
  apply lowerDag _ _ _ _ s26Autos _ _ _ s26Known _ s26Roots s26Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s26StockWords; decide +kernel
  · decide +kernel
  · simp only [s26Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl <;> decide +kernel
def s27Mask : Word := 0xffffffff00000000
abbrev s27Goal : Word := sGoal &&& s27Mask
abbrev s27StockWords : List Word := projectDAGStock s27Mask sBase [0, 1, 2, 3, 4]
def s27Witnesses := unpackWitnesses s27StockWords [289844, 27188, 543265, 817204, 1079340]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 6 := by
  apply essentialLift (witnesses := s27Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s28Mask : Word := 0xf0f0f0f000000000f0f0f0f
abbrev s28Goal : Word := sGoal &&& s28Mask
abbrev s28StockWords : List Word := projectDAGStock s28Mask sBase [0, 1, 3, 4, 6]
def s28Fact : Bound := (s28Mask, s28StockWords, 7, s28Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [13]) s26Stock (by decide +kernel)
def s29Mask : Word := 0xff000000ff000000ff000000ff
abbrev s29Goal : Word := sGoal &&& s29Mask
abbrev s29StockWords : List Word := projectDAGStock s29Mask sBase [0, 1, 2, 5, 6]
def s29Fact : Bound := (s29Mask, s29StockWords, 8, s29Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s24Stock (by decide +kernel)
def s30Mask : Word := 0xf0f00000f0f00000f0f00000f0f
abbrev s30Goal : Word := sGoal &&& s30Mask
abbrev s30StockWords : List Word := projectDAGStock s30Mask sBase [0, 1, 3, 5, 6]
def s30Fact : Bound := (s30Mask, s30StockWords, 7, s30Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Stock : Lower s30Mask s30StockWords s30Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s26Stock (by decide +kernel)
def s31Mask : Word := 0xf000f000f000f000f000f000f000f
abbrev s31Goal : Word := sGoal &&& s31Mask
abbrev s31StockWords : List Word := projectDAGStock s31Mask sBase [0, 1, 4, 5, 6]
def s31Fact : Bound := (s31Mask, s31StockWords, 7, s31Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Stock : Lower s31Mask s31StockWords s31Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7, 13]) s26Stock (by decide +kernel)
def s32Mask : Word := 0x3030303030303030303030303030303
abbrev s32Goal : Word := sGoal &&& s32Mask
abbrev s32StockWords : List Word := projectDAGStock s32Mask sBase [0, 3, 4, 5, 6]
def s32Fact : Bound := (s32Mask, s32StockWords, 6, s32Goal)
def s32Witnesses := unpackWitnesses s32StockWords [41552, 307280, 569416, 843856, 1105968]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Stock : Lower s32Mask s32StockWords s32Goal 6 := by
  apply essentialLift (witnesses := s32Witnesses) (cut := s19Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s19StockWords) (by decide +kernel)
  · exact s19Stock
  · decide +kernel
def s33Mask : Word := 0x5050505050505050505050505050505
abbrev s33Goal : Word := sGoal &&& s33Mask
abbrev s33StockWords : List Word := projectDAGStock s33Mask sBase [1, 3, 4, 5, 6]
def s33Fact : Bound := (s33Mask, s33StockWords, 6, s33Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Stock : Lower s33Mask s33StockWords s33Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s32Stock (by decide +kernel)
def s34Mask : Word := 0xf000f000f000f000f000f000f000f00
abbrev s34Goal : Word := sGoal &&& s34Mask
abbrev s34StockWords : List Word := projectDAGStock s34Mask sBase [0, 1, 4, 5, 6]
def s34Fact : Bound := (s34Mask, s34StockWords, 6, s34Goal)
def s34Witnesses := unpackWitnesses s34StockWords [37448, 569416, 300104, 839752, 1101864]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Stock : Lower s34Mask s34StockWords s34Goal 6 := by
  apply essentialLift (witnesses := s34Witnesses) (cut := s20Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s20StockWords) (by decide +kernel)
  · exact s20Stock
  · decide +kernel
def s35Mask : Word := 0xf0f00000f0f00000f0f00000f0f0000
abbrev s35Goal : Word := sGoal &&& s35Mask
abbrev s35StockWords : List Word := projectDAGStock s35Mask sBase [0, 1, 3, 5, 6]
def s35Fact : Bound := (s35Mask, s35StockWords, 6, s35Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Stock : Lower s35Mask s35StockWords s35Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [10]) s34Stock (by decide +kernel)
def s36Mask : Word := 0xf0f0f0f000000000f0f0f0f00000000
abbrev s36Goal : Word := sGoal &&& s36Mask
abbrev s36StockWords : List Word := projectDAGStock s36Mask sBase [0, 1, 3, 4, 6]
def s36Fact : Bound := (s36Mask, s36StockWords, 6, s36Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Stock : Lower s36Mask s36StockWords s36Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s34Stock (by decide +kernel)
def s37Mask : Word := 0xf0f0f0f0f0f0f0f0000000000000000
abbrev s37Goal : Word := sGoal &&& s37Mask
abbrev s37StockWords : List Word := projectDAGStock s37Mask sBase [0, 1, 3, 4, 5]
def s37Fact : Bound := (s37Mask, s37StockWords, 6, s37Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Stock : Lower s37Mask s37StockWords s37Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 12, 11, 13]) s34Stock (by decide +kernel)
def s38Mask : Word := 0x33333333000000003333333300000000
abbrev s38Goal : Word := sGoal &&& s38Mask
abbrev s38StockWords : List Word := projectDAGStock s38Mask sBase [0, 2, 3, 4, 6]
def s38Fact : Bound := (s38Mask, s38StockWords, 6, s38Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Stock : Lower s38Mask s38StockWords s38Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [14, 13, 2, 8]) s27Stock (by decide +kernel)
def s39Mask : Word := 0x33333333333333330000000000000000
abbrev s39Goal : Word := sGoal &&& s39Mask
abbrev s39StockWords : List Word := projectDAGStock s39Mask sBase [0, 2, 3, 4, 5]
def s39Fact : Bound := (s39Mask, s39StockWords, 6, s39Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Stock : Lower s39Mask s39StockWords s39Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [4, 2, 8]) s27Stock (by decide +kernel)
def s40Mask : Word := 0x55005500550055005500550055005500
abbrev s40Goal : Word := sGoal &&& s40Mask
abbrev s40StockWords : List Word := projectDAGStock s40Mask sBase [1, 2, 4, 5, 6]
def s40Fact : Bound := (s40Mask, s40StockWords, 6, s40Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Stock : Lower s40Mask s40StockWords s40Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 16, 6, 7, 13, 2, 8]) s27Stock (by decide +kernel)
def s41Mask : Word := 0x55550000555500005555000055550000
abbrev s41Goal : Word := sGoal &&& s41Mask
abbrev s41StockWords : List Word := projectDAGStock s41Mask sBase [1, 2, 3, 5, 6]
def s41Fact : Bound := (s41Mask, s41StockWords, 6, s41Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Stock : Lower s41Mask s41StockWords s41Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 0, 6, 7, 2, 8]) s27Stock (by decide +kernel)
def s42Mask : Word := 0xffff0000000000000000000000000000ffff
abbrev s42Goal : Word := sGoal &&& s42Mask
abbrev s42StockWords : List Word := projectDAGStock s42Mask sBase [0, 1, 2, 3, 7]
def s42Fact : Bound := (s42Mask, s42StockWords, 6, s42Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Stock : Lower s42Mask s42StockWords s42Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [18, 19, 20]) s25Stock (by decide +kernel)
def s43Mask : Word := 0x3333333300000000000000000000000033333333
abbrev s43Goal : Word := sGoal &&& s43Mask
abbrev s43StockWords : List Word := projectDAGStock s43Mask sBase [0, 2, 3, 4, 7]
def s43Fact : Bound := (s43Mask, s43StockWords, 7, s43Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Stock : Lower s43Mask s43StockWords s43Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [18, 19, 20]) s26Stock (by decide +kernel)
def s44Mask : Word := 0xff000000ff0000000000000000000000ff000000ff
abbrev s44Goal : Word := sGoal &&& s44Mask
abbrev s44StockWords : List Word := projectDAGStock s44Mask sBase [0, 1, 2, 5, 7]
def s44Fact : Bound := (s44Mask, s44StockWords, 6, s44Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Stock : Lower s44Mask s44StockWords s44Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 18, 6, 11, 19, 20]) s25Stock (by decide +kernel)
def s45Mask : Word := 0xf0f0f0f0f0f0f0f00000000000000000000000000000000
abbrev s45Goal : Word := sGoal &&& s45Mask
abbrev s45StockWords : List Word := projectDAGStock s45Mask sBase [0, 1, 3, 4, 5]
def s45Fact : Bound := (s45Mask, s45StockWords, 7, s45Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Stock : Lower s45Mask s45StockWords s45Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [9]) s26Stock (by decide +kernel)
def s46Mask : Word := 0x333333330000000000000000000000003333333300000000
abbrev s46Goal : Word := sGoal &&& s46Mask
abbrev s46StockWords : List Word := projectDAGStock s46Mask sBase [0, 2, 3, 4, 7]
def s46Fact : Bound := (s46Mask, s46StockWords, 7, s46Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Stock : Lower s46Mask s46StockWords s46Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [18, 19, 20, 8]) s26Stock (by decide +kernel)
def s47Mask : Word := 0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000
abbrev s47Goal : Word := sGoal &&& s47Mask
abbrev s47StockWords : List Word := projectDAGStock s47Mask sBase [0, 1, 3, 4, 6]
def s47Fact : Bound := (s47Mask, s47StockWords, 7, s47Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Stock : Lower s47Mask s47StockWords s47Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [13, 9]) s26Stock (by decide +kernel)
def s48Mask : Word := 0x33333333000000000000000000000000333333330000000000000000
abbrev s48Goal : Word := sGoal &&& s48Mask
abbrev s48StockWords : List Word := projectDAGStock s48Mask sBase [0, 2, 3, 4, 7]
def s48Fact : Bound := (s48Mask, s48StockWords, 7, s48Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Stock : Lower s48Mask s48StockWords s48Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [18, 19, 20, 9]) s26Stock (by decide +kernel)
def s49Mask : Word := 0x5500000055000000550000005500000055000000550000005500000055
abbrev s49Goal : Word := sGoal &&& s49Mask
abbrev s49StockWords : List Word := projectDAGStock s49Mask sBase [1, 2, 5, 6, 7]
def s49Fact : Bound := (s49Mask, s49StockWords, 7, s49Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Stock : Lower s49Mask s49StockWords s49Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 18, 6, 7, 19, 20]) s26Stock (by decide +kernel)
def s50Mask : Word := 0x550000005500000055000000550000005500000055000000550000005500
abbrev s50Goal : Word := sGoal &&& s50Mask
abbrev s50StockWords : List Word := projectDAGStock s50Mask sBase [1, 2, 5, 6, 7]
def s50Fact : Bound := (s50Mask, s50StockWords, 7, s50Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Stock : Lower s50Mask s50StockWords s50Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 18, 6, 7, 19, 20, 8]) s26Stock (by decide +kernel)
def s51Mask : Word := 0xf000f000f000f000f000f000f000f00000000000000000000000000000000
abbrev s51Goal : Word := sGoal &&& s51Mask
abbrev s51StockWords : List Word := projectDAGStock s51Mask sBase [0, 1, 4, 5, 6]
def s51Fact : Bound := (s51Mask, s51StockWords, 7, s51Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Stock : Lower s51Mask s51StockWords s51Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7, 13, 9]) s26Stock (by decide +kernel)
def s52Mask : Word := 0x55000000550000005500000055000000550000005500000055000000550000
abbrev s52Goal : Word := sGoal &&& s52Mask
abbrev s52StockWords : List Word := projectDAGStock s52Mask sBase [1, 2, 5, 6, 7]
def s52Fact : Bound := (s52Mask, s52StockWords, 7, s52Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Stock : Lower s52Mask s52StockWords s52Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 18, 6, 7, 19, 20, 9]) s26Stock (by decide +kernel)
def s53Mask : Word := 0x303030303030303030303030303030300000000000000000000000000000000
abbrev s53Goal : Word := sGoal &&& s53Mask
abbrev s53StockWords : List Word := projectDAGStock s53Mask sBase [0, 3, 4, 5, 6]
def s53Fact : Bound := (s53Mask, s53StockWords, 6, s53Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Stock : Lower s53Mask s53StockWords s53Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [9]) s32Stock (by decide +kernel)
def s54Mask : Word := 0x505050505050505050505050505050500000000000000000000000000000000
abbrev s54Goal : Word := sGoal &&& s54Mask
abbrev s54StockWords : List Word := projectDAGStock s54Mask sBase [1, 3, 4, 5, 6]
def s54Fact : Bound := (s54Mask, s54StockWords, 6, s54Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Stock : Lower s54Mask s54StockWords s54Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7, 9]) s32Stock (by decide +kernel)
def s55Mask : Word := 0xffffffffffffffff
abbrev s55Goal : Word := sGoal &&& s55Mask
abbrev s55StockWords : List Word := projectDAGStock s55Mask sBase [0, 1, 2, 3, 4, 5]
def s55Fact : Bound := (s55Mask, s55StockWords, 9, s55Goal)
def s55Witnesses := unpackWitnesses s55StockWords [27188, 289844, 543265, 817204, 1079340, 1336338]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Stock : Lower s55Mask s55StockWords s55Goal 9 := by
  apply essentialLift (witnesses := s55Witnesses) (cut := s24Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s24StockWords) (by decide +kernel)
  · exact s24Stock
  · decide +kernel
def s56Mask : Word := 0xffffffff00000000ffffffff
abbrev s56Goal : Word := sGoal &&& s56Mask
abbrev s56StockWords : List Word := projectDAGStock s56Mask sBase [0, 1, 2, 3, 4, 6]
def s56Fact : Bound := (s56Mask, s56StockWords, 9, s56Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Stock : Lower s56Mask s56StockWords s56Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [13]) s55Stock (by decide +kernel)
def s57Mask : Word := 0xff00ff00ff00ff00ff00ff00ff00ff
abbrev s57Goal : Word := sGoal &&& s57Mask
abbrev s57StockWords : List Word := projectDAGStock s57Mask sBase [0, 1, 2, 4, 5, 6]
def s57Fact : Bound := (s57Mask, s57StockWords, 9, s57Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57Stock : Lower s57Mask s57StockWords s57Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7, 13]) s55Stock (by decide +kernel)
def s58Mask : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev s58Goal : Word := sGoal &&& s58Mask
abbrev s58StockWords : List Word := projectDAGStock s58Mask sBase [0, 1, 3, 4, 5, 6]
def s58Fact : Bound := (s58Mask, s58StockWords, 10, s58Goal)
def s58Cuts : List Bound := [s26Fact, s28Fact, s30Fact, s31Fact, s32Fact, s33Fact, s34Fact, s35Fact, s36Fact, s37Fact, s11Fact, s13Fact, s15Fact, s16Fact, s18Fact, s19Fact, s20Fact, s21Fact, s3Fact]
def s58Chart : Option RowChart := some ⟨[3, 9, 17, 24, 34, 66, 96, 3, 3, 3, 3, 3, 10, 18, 33, 40, 48, 65, 72, 80, 10, 10, 10, 10], rfl⟩
def s58Sample : DagSample := (0x281c06070241a050682098442612418082602816090582814ca05228144904a2412482492090c8242011086038140e06032180c4142a140a442291088c042209068141a0904c02110502c02091080c14030100c0203, 38)
def s58Witnesses := unpackWitnesses s58StockWords [41552, 304208, 569424, 831560, 1106000, 1368112]
def s58Links : DagLinks := 
  dagLookupLinks 0xb03000a84000a238ac0008430007e30000007070006840000000005c60000005440004e300000000046400032a038001 0x5ec94275e89163149b7a20db0e221258106203b7a20db0e22925878f441d6218e30e0692596c6439631bc7988624c40703431819b8a0c7c1c628b092c18310070020da4a02cf448618a5a494251e88a8c3814496099882346281a008b102648810144068220282f92807bd1214c405c34e0e1a1068c7829e8890c3808496421880a1e8810c3804310523d12118708892c0431014bd102d88612c3847496039880986860c3370518a818c500801f72f449e621ccb0e1fd286be937594961f990c7cc6e3c62b193105a8d0e5466fae32b9718fc60c56046286e0431701baa80ac5403e2401310007860024040100003f 12 5 13 5 3 5
def s58Data : Forest := fun i => decodeNode 6 18 0x637058ac1c436b0e1ac386e4b1a62005881803707d11601f064b136204c04c10284403c1f4434d08d31e340241c430bd10ac380b0e0862008cdc23150988043140803c2008040fc0 i
def s58Tags := dagTraceTags s58Mask 38 (dagTagBases s58StockWords 0xffffe00003fc007fc00c0f81e0f00c31c673300034e53ebc30ae0b8ff 0xabffc0000150007b808c0b8160a00c918261240000211e98340701859 38) 9 s58Data
def s58States := dagTrace s58Mask s58StockWords 9 s58Data
def s58Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s58Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s58Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s58Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s58Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 6, 5, 7] 0 i.val)
def s58Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 6, 5, 7] 0 i.val)
def s58Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 6, 3, 4, 7] 0 i.val)
def s58Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 6, 3, 4, 7] 0 i.val)
def s58Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 5, 3, 4, 7] 0 i.val)
def s58Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 6, 4, 3, 7] 0 i.val)
def s58Move5Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 6, 4, 3, 7] 0 i.val)
def s58Move5Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 5, 3, 4, 7] 0 i.val)
def s58MoveCert : List (DagMoveRecord 256) := [((moveSchedule moveStages [13]), s58Move0Map, s58Move0Inverse), ((moveSchedule moveStages [10]), s58Move1Map, s58Move1Inverse), ((moveSchedule moveStages [10, 13]), s58Move2Map, s58Move2Inverse), ((moveSchedule moveStages [3, 6, 7]), s58Move3Map, s58Move3Inverse), ((moveSchedule moveStages [3, 12, 11, 13]), s58Move4Map, s58Move4Inverse), ((moveSchedule moveStages [3, 6, 7, 13]), s58Move5Map, s58Move5Inverse)]
def s58Moves := dagMoves s58MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Autos : DagMovesOK s58Mask s58Goal 256 s58Moves := dagMovesOfCheck (by decide +kernel)
def s58Check := dagCheckNode s58Mask s58Goal s58Chart (dagKnownCloses s58Goal s58Cuts) 32 s58States s58Moves s58Links s58Sample s58Tags
def s58RootAt (token : Nat) : Bool :=
  let s := rootState s58StockWords 9 token
  !dagAllowedRoot s58Witnesses s.2.1 || dagLocal s58Mask s58Goal s58Chart (dagKnownCloses s58Goal s58Cuts) s ||
  dagRef 32 s58States s58Moves s58Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58RootBlock0 : treeBlock 0 64 s58RootAt = true := by decide +kernel
theorem s58Roots : dagCheckRoots s58Mask s58Goal s58Chart (dagKnownCloses s58Goal s58Cuts) s58Witnesses (dagRef 32 s58States s58Moves s58Links 0) s58StockWords 9 = true := s58RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Block0 : treeBlock 0 16 s58Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Block16 : treeBlock 16 16 s58Check = true := by decide +kernel
theorem s58Verified : treeBlock 0 32 s58Check = true := (@treeBlock_merge 0 16 16 s58Check s58Block0 s58Block16)
theorem s58Blocks : treeBlock 0 32 s58Check = true := s58Verified
theorem s58Known : Known s58Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s3Stock) s21Stock) s20Stock) s19Stock) s18Stock) s16Stock) s15Stock) s13Stock) s11Stock) s37Stock) s36Stock) s35Stock) s34Stock) s33Stock) s32Stock) s31Stock) s30Stock) s28Stock) s26Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Stock : Lower s58Mask s58StockWords s58Goal 10 := by
  apply lowerDag _ _ _ _ s58Autos _ _ _ s58Known _ s58Roots s58Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s58StockWords; decide +kernel
  · decide +kernel
  · simp only [s58Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s59Mask : Word := 0x33333333333333333333333333333333
abbrev s59Goal : Word := sGoal &&& s59Mask
abbrev s59StockWords : List Word := projectDAGStock s59Mask sBase [0, 2, 3, 4, 5, 6]
def s59Fact : Bound := (s59Mask, s59StockWords, 7, s59Goal)
def s59Witnesses := unpackWitnesses s59StockWords [43604, 297537, 571476, 833612, 1108052, 1370164]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Stock : Lower s59Mask s59StockWords s59Goal 7 := by
  apply essentialLift (witnesses := s59Witnesses) (cut := s39Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s39StockWords) (by decide +kernel)
  · exact s39Stock
  · decide +kernel
def s60Mask : Word := 0x55555555555555555555555555555555
abbrev s60Goal : Word := sGoal &&& s60Mask
abbrev s60StockWords : List Word := projectDAGStock s60Mask sBase [1, 2, 3, 4, 5, 6]
def s60Fact : Bound := (s60Mask, s60StockWords, 7, s60Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Stock : Lower s60Mask s60StockWords s60Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s59Stock (by decide +kernel)
def s61Mask : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00
abbrev s61Goal : Word := sGoal &&& s61Mask
abbrev s61StockWords : List Word := projectDAGStock s61Mask sBase [0, 1, 2, 4, 5, 6]
def s61Fact : Bound := (s61Mask, s61StockWords, 7, s61Goal)
def s61Witnesses := unpackWitnesses s61StockWords [39500, 302156, 531466, 833612, 1103948, 1366060]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Stock : Lower s61Mask s61StockWords s61Goal 7 := by
  apply essentialLift (witnesses := s61Witnesses) (cut := s40Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s40StockWords) (by decide +kernel)
  · exact s40Stock
  · decide +kernel
def s62Mask : Word := 0xffff0000ffff0000ffff0000ffff0000
abbrev s62Goal : Word := sGoal &&& s62Mask
abbrev s62StockWords : List Word := projectDAGStock s62Mask sBase [0, 1, 2, 3, 5, 6]
def s62Fact : Bound := (s62Mask, s62StockWords, 7, s62Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Stock : Lower s62Mask s62StockWords s62Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [10]) s61Stock (by decide +kernel)
def s63Mask : Word := 0xffffffff00000000ffffffff00000000
abbrev s63Goal : Word := sGoal &&& s63Mask
abbrev s63StockWords : List Word := projectDAGStock s63Mask sBase [0, 1, 2, 3, 4, 6]
def s63Fact : Bound := (s63Mask, s63StockWords, 7, s63Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Stock : Lower s63Mask s63StockWords s63Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s61Stock (by decide +kernel)
def s64Mask : Word := 0xffffffffffffffff0000000000000000
abbrev s64Goal : Word := sGoal &&& s64Mask
abbrev s64StockWords : List Word := projectDAGStock s64Mask sBase [0, 1, 2, 3, 4, 5]
def s64Fact : Bound := (s64Mask, s64StockWords, 7, s64Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Stock : Lower s64Mask s64StockWords s64Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 12, 11, 13]) s61Stock (by decide +kernel)
def s65Mask : Word := 0xffffffff000000000000000000000000ffffffff
abbrev s65Goal : Word := sGoal &&& s65Mask
abbrev s65StockWords : List Word := projectDAGStock s65Mask sBase [0, 1, 2, 3, 4, 7]
def s65Fact : Bound := (s65Mask, s65StockWords, 9, s65Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Stock : Lower s65Mask s65StockWords s65Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [18, 19, 20]) s55Stock (by decide +kernel)
def s66Mask : Word := 0xffff0000ffff00000000000000000000ffff0000ffff
abbrev s66Goal : Word := sGoal &&& s66Mask
abbrev s66StockWords : List Word := projectDAGStock s66Mask sBase [0, 1, 2, 3, 5, 7]
def s66Fact : Bound := (s66Mask, s66StockWords, 8, s66Goal)
def s66Cuts : List Bound := [s25Fact, s42Fact, s44Fact]
def s66Chart : Option RowChart := some ⟨[3, 5, 6, 9, 34, 132, 3, 3, 3, 3, 3, 3, 44, 138, 161, 168, 44, 44, 44, 44, 44, 44, 44, 44], rfl⟩
def s66Sample : DagSample := (0x542b058ac542a914aa542a542a950a8d42a245239148b02210582e160b4582501088580e0082402050100c0203, 20)
def s66Witnesses := unpackWitnesses s66StockWords [86696, 349352, 612520, 873121, 1135754, 1398828]
def s66Links : DagLinks := 
  dagLookupLinks 0x1c01 0xbe357e296e209b415b29931f4b1438411835301f10130808003f 8 4 11 2 3 4
def s66Data : Forest := fun i => decodeNode 3 9 0xd4a6483f8 i
def s66Tags := dagTraceTags s66Mask 20 (dagTagBases s66StockWords 0xffe00ff1e0fcd98c0bd433d330e4cf 0xbfc00ef1d0f8dd0403d010c220700d 20) 7 s66Data
def s66States := dagTrace s66Mask s66StockWords 7 s66Data
def s66Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 7, 6, 5] 0 i.val)
def s66Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 7, 6, 5] 0 i.val)
def s66Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 4, 3, 6, 7] 0 i.val)
def s66Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 4, 3, 6, 7] 0 i.val)
def s66Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 0, 1, 7, 4, 3, 6, 5] 0 i.val)
def s66Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 2, 0, 5, 4, 7, 6, 3] 0 i.val)
def s66Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 2, 0, 5, 4, 7, 6, 3] 0 i.val)
def s66Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 0, 1, 7, 4, 3, 6, 5] 0 i.val)
def s66Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 7, 4, 5, 6, 3] 0 i.val)
def s66Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 7, 4, 5, 6, 3] 0 i.val)
def s66MoveCert : List (DagMoveRecord 256) := [((moveSchedule moveStages [18, 19]), s66Move0Map, s66Move0Inverse), ((moveSchedule moveStages [3, 6]), s66Move1Map, s66Move1Inverse), ((moveSchedule moveStages [21, 18, 22, 19]), s66Move2Map, s66Move2Inverse), ((moveSchedule moveStages [3, 18, 6, 19]), s66Move3Map, s66Move3Inverse), ((moveSchedule moveStages [21, 22]), s66Move4Map, s66Move4Inverse)]
def s66Moves := dagMoves s66MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Autos : DagMovesOK s66Mask s66Goal 256 s66Moves := dagMovesOfCheck (by decide +kernel)
def s66Check := dagCheckNode s66Mask s66Goal s66Chart (dagKnownCloses s66Goal s66Cuts) 4 s66States s66Moves s66Links s66Sample s66Tags
def s66RootAt (token : Nat) : Bool :=
  let s := rootState s66StockWords 7 token
  !dagAllowedRoot s66Witnesses s.2.1 || dagLocal s66Mask s66Goal s66Chart (dagKnownCloses s66Goal s66Cuts) s ||
  dagRef 4 s66States s66Moves s66Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66RootBlock0 : treeBlock 0 64 s66RootAt = true := by decide +kernel
theorem s66Roots : dagCheckRoots s66Mask s66Goal s66Chart (dagKnownCloses s66Goal s66Cuts) s66Witnesses (dagRef 4 s66States s66Moves s66Links 0) s66StockWords 7 = true := s66RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Block0 : treeBlock 0 4 s66Check = true := by decide +kernel
theorem s66Blocks : treeBlock 0 4 s66Check = true := s66Block0
theorem s66Known : Known s66Cuts := extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s44Stock) s42Stock) s25Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Stock : Lower s66Mask s66StockWords s66Goal 8 := by
  apply lowerDag _ _ _ _ s66Autos _ _ _ s66Known _ s66Roots s66Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s66StockWords; decide +kernel
  · decide +kernel
  · simp only [s66Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl <;> decide +kernel
def s67Mask : Word := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
abbrev s67Goal : Word := sGoal &&& s67Mask
abbrev s67StockWords : List Word := projectDAGStock s67Mask sBase [0, 1, 2, 4, 5, 7]
def s67Fact : Bound := (s67Mask, s67StockWords, 8, s67Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Stock : Lower s67Mask s67StockWords s67Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [10]) s66Stock (by decide +kernel)
def s68Mask : Word := 0xffffffff000000000000000000000000ffffffff00000000
abbrev s68Goal : Word := sGoal &&& s68Mask
abbrev s68StockWords : List Word := projectDAGStock s68Mask sBase [0, 1, 2, 3, 4, 7]
def s68Fact : Bound := (s68Mask, s68StockWords, 8, s68Goal)
def s68Witnesses := unpackWitnesses s68StockWords [353456, 90800, 616624, 880816, 1142952, 1402932]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Stock : Lower s68Mask s68StockWords s68Goal 8 := by
  apply essentialLift (witnesses := s68Witnesses) (cut := s46Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s46StockWords) (by decide +kernel)
  · exact s46Stock
  · decide +kernel
def s69Mask : Word := 0xffffffffffffffff00000000000000000000000000000000
abbrev s69Goal : Word := sGoal &&& s69Mask
abbrev s69StockWords : List Word := projectDAGStock s69Mask sBase [0, 1, 2, 3, 4, 5]
def s69Fact : Bound := (s69Mask, s69StockWords, 8, s69Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Stock : Lower s69Mask s69StockWords s69Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [18, 13, 20, 2, 8]) s68Stock (by decide +kernel)
def s70Mask : Word := 0xffff000000000000ffff000000000000ffff000000000000ffff
abbrev s70Goal : Word := sGoal &&& s70Mask
abbrev s70StockWords : List Word := projectDAGStock s70Mask sBase [0, 1, 2, 3, 6, 7]
def s70Fact : Bound := (s70Mask, s70StockWords, 8, s70Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70Stock : Lower s70Mask s70StockWords s70Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [13]) s66Stock (by decide +kernel)
def s71Mask : Word := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
abbrev s71Goal : Word := sGoal &&& s71Mask
abbrev s71StockWords : List Word := projectDAGStock s71Mask sBase [0, 1, 2, 4, 6, 7]
def s71Fact : Bound := (s71Mask, s71StockWords, 8, s71Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Stock : Lower s71Mask s71StockWords s71Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [10, 13]) s66Stock (by decide +kernel)
def s72Mask : Word := 0xffffffff000000000000000000000000ffffffff0000000000000000
abbrev s72Goal : Word := sGoal &&& s72Mask
abbrev s72StockWords : List Word := projectDAGStock s72Mask sBase [0, 1, 2, 3, 4, 7]
def s72Fact : Bound := (s72Mask, s72StockWords, 8, s72Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Stock : Lower s72Mask s72StockWords s72Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [2, 8]) s68Stock (by decide +kernel)
def s73Mask : Word := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
abbrev s73Goal : Word := sGoal &&& s73Mask
abbrev s73StockWords : List Word := projectDAGStock s73Mask sBase [0, 1, 2, 5, 6, 7]
def s73Fact : Bound := (s73Mask, s73StockWords, 9, s73Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Stock : Lower s73Mask s73StockWords s73Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 18, 6, 7, 19, 20]) s55Stock (by decide +kernel)
def s74Mask : Word := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
abbrev s74Goal : Word := sGoal &&& s74Mask
abbrev s74StockWords : List Word := projectDAGStock s74Mask sBase [0, 1, 2, 5, 6, 7]
def s74Fact : Bound := (s74Mask, s74StockWords, 8, s74Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Stock : Lower s74Mask s74StockWords s74Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s68Stock (by decide +kernel)
def s75Mask : Word := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
abbrev s75Goal : Word := sGoal &&& s75Mask
abbrev s75StockWords : List Word := projectDAGStock s75Mask sBase [0, 1, 2, 5, 6, 7]
def s75Fact : Bound := (s75Mask, s75StockWords, 8, s75Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Stock : Lower s75Mask s75StockWords s75Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7, 2, 8]) s68Stock (by decide +kernel)
def s76Mask : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000
abbrev s76Goal : Word := sGoal &&& s76Mask
abbrev s76StockWords : List Word := projectDAGStock s76Mask sBase [0, 1, 2, 4, 5, 6]
def s76Fact : Bound := (s76Mask, s76StockWords, 8, s76Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Stock : Lower s76Mask s76StockWords s76Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 18, 6, 7, 20, 2, 8]) s68Stock (by decide +kernel)
def s77Mask : Word := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000
abbrev s77Goal : Word := sGoal &&& s77Mask
abbrev s77StockWords : List Word := projectDAGStock s77Mask sBase [0, 1, 3, 4, 5, 6]
def s77Fact : Bound := (s77Mask, s77StockWords, 10, s77Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s77Stock : Lower s77Mask s77StockWords s77Goal 10 := dagShiftLower (width := 256) (moveSchedule moveStages [9]) s58Stock (by decide +kernel)
def s78Mask : Word := 0x3333333300000000333333330000000033333333000000003333333300000000
abbrev s78Goal : Word := sGoal &&& s78Mask
abbrev s78StockWords : List Word := projectDAGStock s78Mask sBase [0, 2, 3, 4, 6, 7]
def s78Fact : Bound := (s78Mask, s78StockWords, 8, s78Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s78Stock : Lower s78Mask s78StockWords s78Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [14, 13, 2, 8]) s68Stock (by decide +kernel)
def s79Mask : Word := 0x3333333333333333000000000000000033333333333333330000000000000000
abbrev s79Goal : Word := sGoal &&& s79Mask
abbrev s79StockWords : List Word := projectDAGStock s79Mask sBase [0, 2, 3, 4, 5, 7]
def s79Fact : Bound := (s79Mask, s79StockWords, 8, s79Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Stock : Lower s79Mask s79StockWords s79Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [4, 2, 8]) s68Stock (by decide +kernel)
def s80Mask : Word := 0x3333333333333333333333333333333300000000000000000000000000000000
abbrev s80Goal : Word := sGoal &&& s80Mask
abbrev s80StockWords : List Word := projectDAGStock s80Mask sBase [0, 2, 3, 4, 5, 6]
def s80Witnesses := unpackWitnesses s80StockWords [370896, 107216, 635088, 897224, 1171664, 1433776]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Stock : Lower s80Mask s80StockWords s80Goal 7 := by
  apply essentialLift (witnesses := s80Witnesses) (cut := s53Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s53StockWords) (by decide +kernel)
  · exact s53Stock
  · decide +kernel
def s81Mask : Word := 0x5500550055005500550055005500550055005500550055005500550055005500
abbrev s81Goal : Word := sGoal &&& s81Mask
abbrev s81StockWords : List Word := projectDAGStock s81Mask sBase [1, 2, 4, 5, 6, 7]
def s81Fact : Bound := (s81Mask, s81StockWords, 8, s81Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s81Stock : Lower s81Mask s81StockWords s81Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 16, 6, 7, 13, 2, 8]) s68Stock (by decide +kernel)
def s82Mask : Word := 0x5555000055550000555500005555000055550000555500005555000055550000
abbrev s82Goal : Word := sGoal &&& s82Mask
abbrev s82StockWords : List Word := projectDAGStock s82Mask sBase [1, 2, 3, 5, 6, 7]
def s82Fact : Bound := (s82Mask, s82StockWords, 8, s82Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Stock : Lower s82Mask s82StockWords s82Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 0, 6, 7, 2, 8]) s68Stock (by decide +kernel)
def s83Mask : Word := 0x5555555555555555555555555555555500000000000000000000000000000000
abbrev s83Goal : Word := sGoal &&& s83Mask
abbrev s83StockWords : List Word := projectDAGStock s83Mask sBase [1, 2, 3, 4, 5, 6]
def s83Fact : Bound := (s83Mask, s83StockWords, 7, s83Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s83Stock : Lower s83Mask s83StockWords s83Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s80Stock (by decide +kernel)
def s84Mask : Word := 0xffffffffffffffffffffffffffffffff
abbrev s84Goal : Word := sGoal &&& s84Mask
abbrev s84StockWords : List Word := projectDAGStock s84Mask sBase [0, 1, 2, 3, 4, 5, 6]
def s84Fact : Bound := (s84Mask, s84StockWords, 11, s84Goal)
def s84Witnesses := unpackWitnesses s84StockWords [43604, 306260, 559681, 833620, 1095756, 1370196, 1632308]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Stock : Lower s84Mask s84StockWords s84Goal 11 := by
  apply essentialLift (witnesses := s84Witnesses) (cut := s58Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s58StockWords) (by decide +kernel)
  · exact s58Stock
  · decide +kernel
def s85Mask : Word := 0xffffffffffffffff0000000000000000ffffffffffffffff
abbrev s85Goal : Word := sGoal &&& s85Mask
abbrev s85StockWords : List Word := projectDAGStock s85Mask sBase [0, 1, 2, 3, 4, 5, 7]
def s85Fact : Bound := (s85Mask, s85StockWords, 11, s85Goal)
def s85Cuts : List Bound := [s55Fact, s65Fact, s66Fact, s67Fact, s68Fact, s69Fact, s45Fact, s46Fact, s44Fact, s12Fact, s4Fact]
def s85Chart : Option RowChart := some ⟨[3, 5, 6, 9, 17, 24, 34, 132, 3, 3, 3, 3, 44, 52, 138, 146, 161, 168, 176, 44, 44, 44, 44, 44], rfl⟩
def s85Sample : DagSample := (0x160b9582e150b8582d068b4582cd60b2492c960b150ac550ac162b150aa452a950a950aa542a55829150a450a9140a41229142a35428942a250289249a4526924964925028944924d249145239148b4920d14831a0f0583c1a0d868351a0c86831160b8582d1a098582512095422201088681c45068241a0a06024184905868160a058241600845140e16038180e0402402090501808050081502030100c0203, 71)
def s85Witnesses := unpackWitnesses s85StockWords [90800, 353456, 616624, 880816, 1142952, 1402002, 1665076]
def s85Links : DagLinks := 
  dagLookupLinks 0xd87e89f09e000000600ae4e000000000000000000000000016e2a9700000000009e5800000134400000025c716c00000021c8000000420c0010237560001d020000000001cc2e4100000000000000000001c42bb400000000000005c080000000000002d840000000002d052628e200023040008a1000000108600000000000006120000000aca000000140c00000000000009460000000ac0068001 0x56d936acc83496202d9ac958d049a63e49314a102c9081346e082b303519814ca807c540260e008ad620d230e0b529a4892ca0b269059041ac405dc38acca0f5e4de8f2585964d6bb1b9318ac8ec414034d201a0ae0cde526562931f0d98a830c50b58700b3146ce1c16e4dcb3258b20371901586802412010510402801415fd10ad88455c382a32192d8d4a6c5346620291a14fc1644a06a4f0311881488804410010ccf4426e219330e1972844b936580218c00dc480532101d1080881c020918704592c9f3268198818b8704592c02b1031f0e09326e4792c6331b9198ac88c413d34d5799b8bccae5063e193150218a1070e07d2583c34d0b18a2fb0e07d258153145e61c0f24b030010c0c382149b9024b17ec6e3f62b1eb100ec1355c06e2e02b9000f85c024280103903c1a8200b40d05ac6838f441be210db0f4698703394299326c958d662c532f620191ac894cd4626523031f1798a4b81645c09a2c0428f80f87c04c26010279540f00e07807153e882ac4314e1c0a24b04ccb2a564212b1b0918a846c40a23421119b084ca8400b29f0430f81b8740a824011166580b326455960306b096c380b49605588137e881bc388d4a6c664b034cb2196208b9acc50d602e69a1434c499a104ccda246541231e488210440da200541001e06e1c42e5060d2580b64d0331022f0e0172580a0494361c01a4b00ac408cc380749b8324b212c838863784315c118801269a883370419581cc7c086288303701815c0807c04026dcc382f49b9724b2b0c83ce637a7315d0d880b069ace33727195928c7c866293a04d1d020aac0dc560571c01f0e00983c024020100007f 13 5 12 7 2 5
def s85Data : Forest := fun i => decodeNode 7 19 0x126e070e2ec9601937b38716a4b2c9a681f449f8853f0e27b21cf6299e6853c1028014500319e6560710e5e1c4b9369663e064de261c4892c88c57124b22b10443140326eef0e20c963b62b77258f9881dc963c04d76082040f1cfa22cc425987ab0101ae1c2c942586b2b0ca5618fac3145809ab18d168212c02b03886770e0ec961d9544ecb2758d8eb151d6203a66c74ca8e82c9d0373a038780a8e80981c3820cb24188081ac1834d2125855880a9a6103362063c400d8800f100090326e0b0e06c960292c1409228d3411958231f0525815880298a0202b0402608020083f80 i
def s85Tags := dagTraceTags s85Mask 71 (dagTagBases s85StockWords 0x1fffffffff000000003ffffff001fff000007fe0001fc3f01ff800e03f003066183e0f803061f81c8f3e43dce01c300fe5e55367b93c261c100dc558008df 0x1efdff7fbf001221013fbefff001ffe821006fc02017caf217f000203e21106a1a100f40102008040ffe498c40041000f7e0016ca110020c940000040084d 71) 10 s85Data
def s85States := dagTrace s85Mask s85StockWords 10 s85Data
def s85Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s85Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s85Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 7, 6, 5] 0 i.val)
def s85Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 3, 4, 7, 6, 5] 0 i.val)
def s85Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 7, 6, 5] 0 i.val)
def s85Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 2, 1, 4, 3, 7, 6, 5] 0 i.val)
def s85MoveCert : List (DagMoveRecord 256) := [((moveSchedule moveStages [10]), s85Move0Map, s85Move0Inverse), ((moveSchedule moveStages [18, 19]), s85Move1Map, s85Move1Inverse), ((moveSchedule moveStages [18, 10, 19]), s85Move2Map, s85Move2Inverse)]
def s85Moves := dagMoves s85MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Autos : DagMovesOK s85Mask s85Goal 256 s85Moves := dagMovesOfCheck (by decide +kernel)
def s85Check := dagCheckNode s85Mask s85Goal s85Chart (dagKnownCloses s85Goal s85Cuts) 95 s85States s85Moves s85Links s85Sample s85Tags
def s85RootAt (token : Nat) : Bool :=
  let s := rootState s85StockWords 10 token
  !dagAllowedRoot s85Witnesses s.2.1 || dagLocal s85Mask s85Goal s85Chart (dagKnownCloses s85Goal s85Cuts) s ||
  dagRef 95 s85States s85Moves s85Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85RootBlock0 : treeBlock 0 64 s85RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85RootBlock64 : treeBlock 64 64 s85RootAt = true := by decide +kernel
theorem s85RootVerified : treeBlock 0 128 s85RootAt = true := (@treeBlock_merge 0 64 64 s85RootAt s85RootBlock0 s85RootBlock64)
theorem s85Roots : dagCheckRoots s85Mask s85Goal s85Chart (dagKnownCloses s85Goal s85Cuts) s85Witnesses (dagRef 95 s85States s85Moves s85Links 0) s85StockWords 10 = true := s85RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Block0 : treeBlock 0 16 s85Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Block16 : treeBlock 16 16 s85Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Block32 : treeBlock 32 16 s85Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Block48 : treeBlock 48 16 s85Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Block64 : treeBlock 64 16 s85Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Block80 : treeBlock 80 15 s85Check = true := by decide +kernel
theorem s85Verified : treeBlock 0 95 s85Check = true := (@treeBlock_merge 0 48 47 s85Check (@treeBlock_merge 0 16 32 s85Check s85Block0 (@treeBlock_merge 16 16 16 s85Check s85Block16 s85Block32)) (@treeBlock_merge 48 16 31 s85Check s85Block48 (@treeBlock_merge 64 16 15 s85Check s85Block64 s85Block80)))
theorem s85Blocks : treeBlock 0 95 s85Check = true := s85Verified
theorem s85Known : Known s85Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s4Stock) s12Stock) s44Stock) s46Stock) s45Stock) s69Stock) s68Stock) s67Stock) s66Stock) s65Stock) s55Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Stock : Lower s85Mask s85StockWords s85Goal 11 := by
  apply lowerDag _ _ _ _ s85Autos _ _ _ s85Known _ s85Roots s85Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s85StockWords; decide +kernel
  · decide +kernel
  · simp only [s85Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s86Mask : Word := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
abbrev s86Goal : Word := sGoal &&& s86Mask
abbrev s86StockWords : List Word := projectDAGStock s86Mask sBase [0, 1, 2, 3, 4, 6, 7]
def s86Fact : Bound := (s86Mask, s86StockWords, 11, s86Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s86Stock : Lower s86Mask s86StockWords s86Goal 11 := dagShiftLower (width := 256) (moveSchedule moveStages [13]) s85Stock (by decide +kernel)
def s87Mask : Word := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
abbrev s87Goal : Word := sGoal &&& s87Mask
abbrev s87StockWords : List Word := projectDAGStock s87Mask sBase [0, 1, 2, 3, 5, 6, 7]
def s87Fact : Bound := (s87Mask, s87StockWords, 11, s87Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Stock : Lower s87Mask s87StockWords s87Goal 11 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s85Stock (by decide +kernel)
def s88Mask : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
abbrev s88Goal : Word := sGoal &&& s88Mask
abbrev s88StockWords : List Word := projectDAGStock s88Mask sBase [0, 1, 2, 4, 5, 6, 7]
def s88Fact : Bound := (s88Mask, s88StockWords, 11, s88Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Stock : Lower s88Mask s88StockWords s88Goal 11 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7, 13]) s85Stock (by decide +kernel)
def s89Mask : Word := 0x3333333333333333333333333333333333333333333333333333333333333333
abbrev s89Goal : Word := sGoal &&& s89Mask
abbrev s89StockWords : List Word := projectDAGStock s89Mask sBase [0, 2, 3, 4, 5, 6, 7]
def s89Fact : Bound := (s89Mask, s89StockWords, 9, s89Goal)
def s89Witnesses := unpackWitnesses s89StockWords [107216, 370896, 635088, 897224, 1171664, 1433776, 1681492]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Stock : Lower s89Mask s89StockWords s89Goal 9 := by
  apply essentialLift (witnesses := s89Witnesses) (cut := s79Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s79StockWords) (by decide +kernel)
  · exact s79Stock
  · decide +kernel
def s90Mask : Word := 0x5555555555555555555555555555555555555555555555555555555555555555
abbrev s90Goal : Word := sGoal &&& s90Mask
abbrev s90StockWords : List Word := projectDAGStock s90Mask sBase [1, 2, 3, 4, 5, 6, 7]
def s90Fact : Bound := (s90Mask, s90StockWords, 9, s90Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Stock : Lower s90Mask s90StockWords s90Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s89Stock (by decide +kernel)
def s91Mask : Word := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
abbrev s91Goal : Word := sGoal &&& s91Mask
abbrev s91StockWords : List Word := projectDAGStock s91Mask sBase [0, 1, 2, 4, 5, 6, 7]
def s91Fact : Bound := (s91Mask, s91StockWords, 9, s91Goal)
def s91Witnesses := unpackWitnesses s91StockWords [103112, 365768, 628936, 897224, 1167560, 1429672, 1677388]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Stock : Lower s91Mask s91StockWords s91Goal 9 := by
  apply essentialLift (witnesses := s91Witnesses) (cut := s81Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s81StockWords) (by decide +kernel)
  · exact s81Stock
  · decide +kernel
def s92Mask : Word := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
abbrev s92Goal : Word := sGoal &&& s92Mask
abbrev s92StockWords : List Word := projectDAGStock s92Mask sBase [0, 1, 2, 3, 5, 6, 7]
def s92Fact : Bound := (s92Mask, s92StockWords, 9, s92Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Stock : Lower s92Mask s92StockWords s92Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [10]) s91Stock (by decide +kernel)
def s93Mask : Word := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
abbrev s93Goal : Word := sGoal &&& s93Mask
abbrev s93StockWords : List Word := projectDAGStock s93Mask sBase [0, 1, 2, 3, 4, 6, 7]
def s93Fact : Bound := (s93Mask, s93StockWords, 9, s93Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Stock : Lower s93Mask s93StockWords s93Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 6, 7]) s91Stock (by decide +kernel)
def s94Mask : Word := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
abbrev s94Goal : Word := sGoal &&& s94Mask
abbrev s94StockWords : List Word := projectDAGStock s94Mask sBase [0, 1, 2, 3, 4, 5, 7]
def s94Fact : Bound := (s94Mask, s94StockWords, 9, s94Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Stock : Lower s94Mask s94StockWords s94Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 12, 11, 13]) s91Stock (by decide +kernel)
def s95Mask : Word := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
abbrev s95Goal : Word := sGoal &&& s95Mask
abbrev s95StockWords : List Word := projectDAGStock s95Mask sBase [0, 1, 2, 3, 4, 5, 6]
def s95Fact : Bound := (s95Mask, s95StockWords, 11, s95Goal)
def s95Witnesses := unpackWitnesses s95StockWords [107216, 369872, 633040, 897232, 1159368, 1433808, 1695920]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Stock : Lower s95Mask s95StockWords s95Goal 11 := by
  apply essentialLift (witnesses := s95Witnesses) (cut := s77Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s77StockWords) (by decide +kernel)
  · exact s77Stock
  · decide +kernel
def s96Mask : Word := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
abbrev s96Goal : Word := sGoal &&& s96Mask
abbrev s96StockWords : List Word := projectDAGStock s96Mask sBase [0, 1, 2, 3, 4, 5, 6, 7]
def s96Cuts : List Bound := [s84Fact, s85Fact, s86Fact, s87Fact, s88Fact, s95Fact, s58Fact, s77Fact, s56Fact, s57Fact, s65Fact, s73Fact, s89Fact, s90Fact, s91Fact, s92Fact, s93Fact, s94Fact, s24Fact, s29Fact, s67Fact, s68Fact, s70Fact, s71Fact, s72Fact, s74Fact, s75Fact, s76Fact, s78Fact, s79Fact, s81Fact, s82Fact, s43Fact, s45Fact, s46Fact, s47Fact, s48Fact, s49Fact, s50Fact, s51Fact, s52Fact, s59Fact, s60Fact, s61Fact, s62Fact, s63Fact, s64Fact, s83Fact, s38Fact, s39Fact, s40Fact, s41Fact, s53Fact, s54Fact, s14Fact, s17Fact, s18Fact, s19Fact, s20Fact, s21Fact, s22Fact, s23Fact, s4Fact, s5Fact]
def s96Chart : Option RowChart := some ⟨[3, 5, 6, 9, 17, 24, 34, 66, 96, 132, 3, 3, 44, 52, 76, 84, 138, 146, 161, 168, 176, 193, 200, 208], rfl⟩
def s96Sample : DagSample := (0x2a3d9a0f1683c160f0643a150e860b8542e16838190e060b8150e050b8140e02a379a0d96836190d82a35da0d62a359a0d568350a8d46834da0d249349a0d160b44a0d12633590cc60b3098cc6432d90ca4532990c960b2582c660b15a0c46431182c42631088c460b0da0c26430982c24530960b8542e068b5582d068b4582cd60b2492c960b150ac460b1162b550ac162b150aa452a950a950aa542a55429142a45029142a35428942a250289249a4526960984926114984925924956825160944925068940a25124930924da09158245249148244249145239508c45231148b0522d90895422514894521d248645219048660a11828350a0d24834520d048340a0ca8741a1d0a870261b0586c2219068646098542612098442616098142602a170985c2a160a8572a158a8552a148a0522a144a05126138984d2612898492611888466091498452211482456090804421a0f0583c1a0d868351a0c86831160b542251609448251089542231088c04220a070241a4906018184905868160a058241649054a8151a054281549044021145038580e06038140e0502c14090082418050081404030080c0003, 190)
def s96Witnesses := unpackWitnesses s96StockWords [107216, 369872, 633040, 897232, 1159368, 1433808, 1695920, 1943636]
def s96Links : DagLinks := 
  dagLookupLinks 0x9c5569c2ca000009c2039c1c19c1819c1029bfc50000000000000009be079bb8a9b45d9afd29af819a9599a64c9a1d29a04699ad699a810000099a0299847995ca994859914d98cd2985dc98542984c2984039828697f0e97c8a97890972d700000000009724200000971c29700796e86969d3000000000000000968c49658d00000963c700000000000000096342960ca95ec80000095d460000095c050000095bc1957139568200000955c39558195541000000000094fd694e4694d0594c4394b8394a0600000000000000000000948c59484200000000000000094783945c79424e939259360c00000000009358200000935029328a9310692e0c92d82000000000092bc792b420000092a83000009284992393922450000092201000009214392044000009200191c109198a00000917c7000000000000000917429158700000914c30000000000914030000000000912c5000009128100000911c390bd89094a00000908c290881906c70000090642000000000090544000009044400000000000000000000902098fd148fa8a00000000008f80a0000000000000008f7c18f7818f7410000000000000008f3508f3018f2c100000000008f185000000000000000000008ef498e6258e38a8e2c38e04a8df448dcca8db858dac3000008d9c48d8468d783000008d6848d50600000000008d443000008d3448d2838d1c300000000008d0c400000000008d0030000000000000008cf438cd48000008cc8300000000008cb848ca84000008c9c3000008c903000008c8430000000000000008c7838c58800000000008c484000008be988b9168b29a8ae518ab4c8a69300000000008a6418a58300000000008a5028a3080000000000000008a2828a0c700000000008a04289e87000000000089e0289c47000000000089b8389b0289a8289945000000000000000898c28970700000000008958600000000008950200000000000000089482892c788fcc8891b000000000000000000008884388393000000000087f5187d8787a4d0000000000879830000000000878c38760b8719286b98867cf8650b86092000000000085fc3000000000085f4285d8785bc785b0385908000000000085882856c7853cc84dd8849138460c8430c84282841c383e8d83e410000083d8300000000000000083a0e8384783744836440000000000834c60000000000000008318d82bd782a8582a0282982826cb825858220e82182000000000081fc70000081f0381e820000081dc30000081b89000000000081a8481a41819c20000081903818c181881000000000000000817458129300000000000000080f4d80ec2000000000080d070000000000000000000080b4780b01806538009700000000007ff0600000000007fe827fcc7000000000000000000007fa4a7f9837f8c37f842000000000000000000000000000000000007f58b7ef1a00000000007ee827ecc77ea897ea027e9827e9027e68a7e5457e4c27e289000007e1847e0847e0027df827df417dd097d9cd7d9427d9017d7087d6430000000000000007d4c67d442000007d3830000000000000007d2c37d14600000000007d0837cd0e0000000000000007cc82000007cbc37cb817cb027ca820000000000000007c9847c7c7000007c5c87c4c40000000000000007c3077c282000007c1847c1020000000000000007c0047be4700000000007bd447bd017b94f7b4157b38200000000007b3417b2057b1827b0c3000007b0817b0027af04000007ae827ad457ac837abc37ab420000000000000007a9097a882000007a7c3000007a6c47a5467a1ce7a1810000000000000007a10279ec9000000000079e42000000000079dc279c46792e678ed078917787c57840f77dd977d8177d4177c05000000000077b047780c774cd00000774030000000000773047700c000000000076f0476c0c76b0476ac176a8176a4176887767c300000000000000076646762ce75f0f75ec175e8175d4575a0d757c975742756837560275486752c775242000007520100000000007518274cd374b850000074b410000074a83749840000000000748c3748810000000000747840000000000747020000000000746c1000007458500000741900000073fc773e850000073e410000073d8373c84000000000073bc300000737d0732d4000000000000000000007328100000000000000073241732010000000000000007318272c55000000000072bc272a0700000000007274b7270100000726437254400000000007248300000723c37238100000722c3721c4721817208471b1600000000007184b71801000007174371644000007158300000714c37148100000713c3712c4712817118470cd3000000000070c8100000000000000070c4170c010000070b8200000000007041e703c1703810000070341702447020100000700c56ffc40000000000000006fe46000006fd836fd026fc82000000000000000000006fb8400000000006fa846f8c70000000000000006f7c4000006f7036f34f00000000006f2c2000006f107000000000000000000000000000000000006f0430000000000000000000000000000006efc200000000006ebd06eb816eb416ea0500000000006e9046e60c000006e5c16e581000006e4c36e3c46e381000006e2c36e1c4000006e1816de4d6d6216d1146ce0c6c620000000000000000000006c5436c3c600000000006c10b00000000006bf08000006bd086b79600000000006b7416b70100000000006b6c16b5466b09300000000006b0026ae4700000000006ac4800000000006abc26aa070000000000000006a9436a70900000000006a48a000006a345000006a244000006a18300000000006a10269c53000000000069b44000000000069a446974c0000069701000000000000000696c1696810000000000000006964169601695c1000000000000000000006958168f5968ec20000068d8568b8868b41000000000068ac20000068a81000000000000000685d368407682c5000000000068281681c30000000000000000000068046680010000067e4767a50679c2000006790300000676c9676816764167601675c1672cc0000067203671c16714267101670c167081670416700166d8a66d4166d0166cc166b85000000000066ac365e7200000000000000065e0100000000000000065dc165d03000000000065c8200000658cf0000000000000000000065881655cb64b6a6422500000641c163f890000063b51638ca00000000006354e00000631ce6296262883627c3623d0000000000061f52000000000061d480000061d010000000000000006194f61121610c1000000000060cd060a4a00000000006088760841608010000000000000000000000000605c9000000000060485603c30000060303601865f9225ee6b5ee015edc15eb4a000000000000000000005e88b5dee75de815de025ddc15dd815dd415da4c000005da010000000000000005d74b5cda75c3a8000005c3410000000000000005c28300000000005c2415c201000005c1435c044000005bc115bb430000000000000005b9c65b9420000000000000005b883000005b7c35b64600000000005b5835b20e0000000000000005ad92000000000000000000005ac06000005abc10000000000000005a9895a25d000005a2015a1c15a1815a08400000000005a0415a0010000059c8e598cf0000059881000005980200000000005974300000596440000059601000005958258e1e58a8e00000000000000000000000005861258543584c25848158441584010000000000583045800c57b1457ac1000005774e576c2576810000000000000005740a56f92000000000056f0256e4356e0156d8200000000000000056c065698a5674956701000000000000000566c1000000000056681000005640a000005563800000000005548600000552880000000000551c30000000000000000000054f4a54a15549c1549425490100000548c1547c45478154741546c2000005464254601545c1545810000054541544440000054401543825434100000542c25424200000000000000000000541c2000000000054181000000000053f0a53c0c0000053bc153b81000000000053ac3536d053585000000000000000533c75334200000000000000053205000005314352f48000000000052e0552dc10000052c8552b0600000000000000052ac152a8100000000000000052a41000000000052a01000005278a00000000005274100000000005270100000525c552191000000000000000000000000000000520c300000000005208100000000000000000000000000000051bd351b4251b0151ac10000000000519c400000519815194151901518825184151393513415130150fcd50f8150f4150f0150ec150cc850c8150c0250bc150b8150b4150b01000005084b000000000000000506c6506815064100000505c25058150541505010000000000000005014f50101000005008200000000004ffc34ff814ff414fdc64fd034fc4300000000004fb834fa060000000000000000000000000000000000000000000004f9044f58e000000000000000000004f3c7000004f3810000000000000000000000000000004f206000000000000000000004f0084e85f4df644d1b74cb984c90a4c8434c6874c2904c1064bd8e4bc064b88e4b60a4b5434b2ca4b1c44af4a4ae054ad43000004ac444aac64a4d84a385000004a284000004a2410000049e8f4971e496824944948ed648dc448b0b489c5488854850e483c548285481450000047f0947e0447cc547b4647a054798247788000004768447584474844730646f1046d8646cc346a4a468c646803467430000046644464c6464034628600000461c345f4a45ec245d8545c8445bc345a4645887457c3456c445585000004554145501453c5452c4451c4450c40000044f4644e8344dc30000044c460000044c0100000000000000044bc1000000000044a464470d4464344583444064408e43f4543e830000043dc343d4200000000000000043c830000043bc343a46000004398300000000004378843684435844348400000432c7432030000000000000004318200000430c3000000000000000430420000042f8342d4942b4842a444280942743000004268342488423c300000423034210841f4741ec241d4641cc241b46000000000041a0541904000004184300000417830000000000416c300000414c841442412874118400000410c300000410030000040f4300000000000000040e8340c884098c4088400000407c300000407034050800000000004040400000000004028600000401c340181401413ff87000000000000000000003fec300000000003fe81000003fe41000003fe013fdc1000003fd813fb493fa83000003f9063f8820000000000000003f7c3000003f7033f586000003f4c33f481000003f3c33f2c400000000003f2813f2410000000000000003f20100000000003f1c13f00700000000003ef433ecca3e90f3e7473e6c23e6813e5453e5013e3863e3413e2c23e1073e0823dd0e3dc433db443dac23da423d8c63d8813d8023d6863d34d3d2443d1443cf873ce4500000000003cdc20000000000000003cd42000003cc833ca883c80a3c704000003c6433c4093c3823c1c73c1423bf873be84000003bd84000003bcc30000000000000003bc033b98a3b60e000003b5823b54100000000003b444000003b10d0000000000000003af863af413adc60000000000000003ad0300000000003acc1000003ac42000003ac01000003a98a3a8c3000003a7463a6c20000000000000003a603000003a5433a3c6000003a3033a2c1000003a2033a10400000000003a0c13a0810000000000000003a04100000000003a00139e47000000000039d8339b0a396d100000000003964200000396013954338ce2386d83819537f0a37b4f3741d37247371c2000003718136f0a36a143668e366023638a3628436184000003604500000000000000035f050000035ec10000035e033569e3540a0000035247351c2351813504500000000000000000000000003500134ccd000000000000000000000000034a89349843484500000000000000000000347830000000000346c33444a00000000003430500000342c1000003420333c180000033a0833847000003370500000000003325332b5c00000000000000032ac200000000000000032a42000003249732441000003214c0000031f873195900000000003164c316013144700000312c631242000003114430f873099830902308c13084230801307c1307813070230682305c330542000003044400000303c2000003038130302302c12fb1f2fa432f90500000000002f8042f7c10000000000000002f685000002f641000002f5832eda02ec452eb052ea432e8872e74500000000002e7012e643000002e5c2000002e5422e5012e14f2d7e62d781000002d6842d602000002d5432d28b2d1062d0432ce8700000000002ce022cc47000002cc010000000000000002cbc12cb8100000000002cb41000002c8ca2c8810000000000000002c8022c50c2c28a000002c2412c20100000000002c1820000000000000002c1412c0c22bfc42bf81000000000000000000002bf02000002bd86000002b9902b7c72b7032b6430000000000000002b34c2b3012b2040000000000000002b1820000000000000002afc72ad8900000000002ad020000000000000002aac900000000002aa032a9822a9022a882000002a7842a7410000000000000002a701000002a5862a5412a5010000000000000002a4c1000002a3462a1090000000000000002a0c10000029f460000029f0129a92299c300000000000000029846298010000000000000002974329605000000000029543000002948300000000000000029441290ce0000000000290420000028d8b000000000028bc70000028a0700000000002898200000000000000028902000000000000000286c92868100000286412854428093000002804100000000000000027f83000000000027f0227ec10000027e810000027e4127e0100000000000000027c860000027c4127c010000027bc1277910000027549000000000000000271ce000000000026e8d26e0226d820000000000000000000026bc70000000000000000000026989000000000026902265cd26581000000000000000263492630126282000000000026049000002600125d0c0000025cc125c8100000000000000025c410000025ac60000000000000000000025907000002588225841000002580100000000002574325548000000000000000000000000000000000002530900000252c1000000000000000252810000000000252410000024ece2471f2448a24384241882400623ec523dc423c8523a0a00000239432360d2354323309231c52308522f450000022dc622cc422a89000000000022a410000022983228c30000022803000002274322701226c10000000000000000000022603224c50000000000224030000000000222082214300000220832204100000000000000021f8321e450000021d83000000000000000000000000021cc321ac821a8121a412190500000218c121785216c30000021603215c100000000000000021503213c5000002130300000000000000000000212432104820c5020b8320b0220ac1209c40000000000209420000020805207c10000000000205c820581000002050200000000000000020443202091ff4b0000000000000001fec2000001fe031fd430000000000000001fbc61fb420000000000000001fa83000001f9c31f84600000000001f78300000000001f684000000000000000000001f6021f28e00000000001f1c300000000001f14200000000001f0441ee481ed050000000000000001eb471eac20000000000000001e985000001e8c31e6c800000000001e585000001e4c3000001e48100000000001e441000001e38300000000001e2841de51000001de01000001dd821dd411dd011dcc100000000001dc421db44000001db01000001dac1000001da421d9c200000000001d846000001d78300000000001d7021d6c1000001d68100000000001d602000001d5c1000001d5421d0931cfc3000001ce851cdc3000001cd031cc8200000000001cbc3000001cb031c947000001c883000001c784000001c7411c6440000000000000001c5440000000000000001c48300000000001c44100000000001c4011c2081bf4b1b5e61b0d41ac131a98a1a5cf19f5a19ec219e81000000000019d8419b49000000000019a441974c1958719388193411924418f0d000000000018e0418b0c186d1183cc0000018342182441818317f4917d090000017cc10000017ac80000000000000000000000000000001780b177c117781000000000000000175c716d2316a8a0000016a02169c11680700000167c100000000001668500000165c30000000000000000000000000165811624d161c2000000000016142000000000000000000001610115c92000000000015b84000000000000000000000000000000159491545414ed614e030000014d4314cc200000000000000000000000000000014a0b00000149821494100000148c21480300000000000000014647141150000000000140820000013e8813d0613c431385000000000001378300000136c300000000001360300000135431330912d9612cc312c031294b00000000001288300000000001278400000126c31244a000000000012305000001224311f4c11997118451178311684115c311503114c100000113461118711084000000000000000110410000000000000001100110fc10000010bd010b8110b0210ac1000000000010a810000000000109451078700000000001068400000000001064100000000000000010601105c1000001034a000000000010283101c30000010181000001014110044000000000000000100010000000000000000fe080f75b0f6830000000000000000f5060f4c10000000000000000f4030f2c500000000000f203000000f143000000edce00000000000ec07000000000000000000000e94b0000000000000000e8830000000000000000000000000000000e6490000000000000000e54400000000000e501000000e4c10000000000000000e3070da240d6cd000000d3cc0d381000000d3410d3010ce920ce410ce01000000000000000000000cc080c84f0000000000000000c50d000000c4820c2c70c2030000000000000000c10400000000000bfc50bd89000000000000000000000bc06000000bbc1000000000000000000000ba46000000000000000000000b8c600000000000b7460000000000000000b70100000000000b54700000000000b483000000b441000000b3c20000000000000000b3810b30200000000000b2c1000000b281000000b2410b2010ae4f0a5e20a152000000a08309fc309f42000000000009d870000009cc30990f00000000000988209412000000000009343000000000000000000000928308d9400000000000000008d4108c83000000000008c4100000000000000008c010881007fe107e4607dc207c070000007bc1000000000007a4607a01079c10000000000079810768c07602000000758200000073c70724600000071830000007102000000000000000000000000006f8606c8c06a0a0698206941068c200000068420000000000067c2066c4000000000006681065c30000006581000000000000000065020000000000063c5000000000006342000000000000000062830604905f4400000000000000005dc605d810000005d0200000000000000005c0405a860000000000059840594100000058830578400000000000000000000057020000000000055c500000000000554200000055010000005482000000000000000000000000000000052c704f0f000000000004e820000000000000000000004e0200000000000000004d0404b0804a04000000000000000048860484100000047c2000000000000000046c4045460000000000044440440100000043430424400000000000420100000041c10414200000000000000000000000000000003f8703bcf03989000000378800000000000344d033c2033420330100000000000000000000030c90000000000000000000002f0702bcd00000000000298900000028c30000000000000000000002746000000000000000027010000002547024c2024810000000000023c30000000000023030208a000000000000000020020000001f04000000000001e4300000000000000001e01000000000001c8600000000000000000000000000000001ac700000000000000001a8100000000000000001a4101848013930000001302012c100000000000124201183009220006300001 0xb76355c97632507782f5b5782f4f5762f443782c5b1782c4f1762c38b34c65b934c64fd4f664394f66378a1862184dc62034f635b14f634f534c343134c337103631f0d0031b0a1831504dc314178155c9332659977865594e863584d26201332359177835514e834d103431f04d231417818681748961154492c1542620154062084ce92c177432ab75955cb59c65a916e329916c31d84cc31417758681744961153e92c1772665916e62a1770620916a32a1779868b75755c1742961b59a95b153c92c9514665916862b84ca620177602a176e01e1783868b75555c976725a177f250177cc5b1766c4d977ac415754c38177a95a1740661b59865b158e64d5598637153a6209512365933034d976c349d4ea33794e6329916631f84c8314151206534ea05b133004d176c04914e6041116601f103001304c8008958c665158c64115386209510371932e365b306359930634d94e2341916431f84c6314151007114e2065132e04153060351306029116401f102e01304c60081536620b76155c176925b97612503766f5a1766f4eb5a465b95a464f15866411534620951c365b34a35b934a34f94f2341917631f8a1631584da314150a06534de05b14de04f132804153000351300029116001f102c01304c0008375f55c175f250b34895b934894f8a1492d84d892c34dc65b14dc64f102a62b0cfe6270a0e62104be6201752c3895889595596937153292c950c665932a659b30264d9302641d4e4637916262b84c2620150836514d83595342337115e32b102831f0a0c31504bc3148a0ac3984bac3810269370cfc9330a0a92d04ba92c175f55c974f250375af4f174ef44173ec55b592c4f5592c431530c389504959b33e94fd4da943915a9378a0692d84b692c150465934da64f533e643115a637102462b0cfa6270a0662104b6620152ec38152cc381758636175b55cf59e95b152a92cd5166651756649d17062bc4d0620958ac591528c38950e965932c959b30494d930494184c492c150266514ce65904b462015272509500f5984b2f441500c5904b2c381751250b594f4f1524f449506c59b340c4f915cc438a08c3984b8c3814fe95934d094f1158943102293704b092c374f2501752f4f174ef44b5a2c4f95a2c431522c38951a959b34694f934694391749378a1292d84d692c14fc65934ca64f14ca6431156637102062b04ae620176355c375d2501760f4f175cf443754c4f1754c43174cc38173c955b5a094f95a09435590937152092c9518659b34464f9344643d4f4637917262b8a1062184d462014fa35934c834f14c83435334337115432b101e31f0cf831b0a0431504ac31496ca62816ca328973832984a8314973862897363281732028973462996c262884a662017303281746028174401e174955c92fc359974235594c4335972e31d96c031c84a431412fc059174205514c404d172e01d16c001c101c01304a4008972c93596be9348a0092d84a292c172c63516be634101a62b0cf66270a0062104a2620373f55c173f250b2fe65b92fe64f973a62996cc6288a0262184aa62034c035b14c034f172a32916bc328101831f0cf431b09fe31504a0314572d250172cf44571ec4f171ec43171ac391710c38d4be64f94be6431700637900c63516f063389fa621849662052b634f52b234e12b634312b23420ffc31f0ff431e0cf231b0cee31a0996315099231417383341736010849c314173201217343551010329849a31412b00581730054147e04c0ff2012170ef44100e941849892c0ff062a0cec6260990620372d55c172d2503726c5b1726c4f170cc38b2f265b92f264f16fe637100c63589fc621849e620348635b347a35a148634f147a34e0ffa31f0fee31e0cea31a098e31416fa634172436413d83280fec01c172955c5726f441726c38171892c92ec359172235592ea34d16f8329849231452a604212a60360fea012098c008371f868171f55c16f632984943143478066147805a0fe801204f40341716010371b868171b55c3718c661718c5a16f463584906203476366147635a0fe631e171401a570f250170ef44848c92c52a464e12a46420fe462a0ce8626170a32a370f55c170f250848e92c347465a147464e0fe262a370b55c170b250847e314347205a147204e170601c371155c1711250570cf44170cc38b2e865b92e864f89f66218488620348435b347035a148434f147034e52a234212a23360ff831f0fde31e0ce631a170801e170401b16ec6300ce231816ea6300cde3180ec60280e5231c16fa3543701868170155c56ff25016fef44b2ecc6692ecc5a16fcc3836f896616f895a56f694e16f694216f492c16ee32516e832489f4314346e066146e05a52a004e12a00420ce400e0cdc00c098a00816ec94036e466456dc65816dc64c0aba6340fd632836e036416e035856da34c16da3400a8232856d864c16d86400a6062856d664016d66340a5e62836ed55c16ed25016ea92c56d434016d43340a5c31c16e555c16e325016e032989f03140fdc01216d86340fd431c36d925016d8f4416d662036dd55c16dd25016da32916d432889f23140fda0120fd201036f186816f155c16ee63516e863489ee62036e636636de36416e635a16de35856d234c16d23400ab83280fd801e0fd001c373b55c173b250772ef5b572ef4f572af44372ec5b172ec4f172ac38372095b172094f571c943171c937171292d170292cb2e635b92e634fd4bc34394bc33716f232b0ffe32916d032789e4315847a314348205b346c05a148204f146c04e52b4043529e04212b4037129e0360ff60130fce0120cf000f0cda00e0994009098800856bef4416bec3856a694316a6937169492d166a92cd4b434394b4337164632b161432789de315847031416c801d8476008166892c16c402a16cb25016a464d16c664916b8641166662092e204d16c204994b8029164401f84740081692c391664c381642637161263389e0621847262036bf25016bef4436b494f16b4943169092d166292cb2e434f92e4343164032b161032789e2315847831456b6f4416b6c3816b7250168c92c92d634d16b234992d03411626329846431416b035813d632856b0c3816b092c168a62056b2f4416b2c38168892c162a32a16ae05892ce04c56ac04016ac03413d001c16bb25056a4c4d56b8c4156b4c3816a494d16b894116b492c569a637169a62b168e621168662092d404d16aa04992cc041d49c037949c02b162801f162201d846200816a2f44168492c94b234194a2335846a31416a034c36a125016a0f44846e00836a355c16a3250846c314169e04094a403436a755c16a725036a4c5a16a4c4e169cc38369a65b169a64f1682620b2d805b92d804f94b0035169803194a0029162001f89dc009846600856932501692f445684c4e1684c42161c635160e631845e620567e34e167e342167a31e369355c1693250368cc5a168cc4e161a6358460620167031a168a35813d4328568cc38168c92c92ca34d168834992c8341845a3141678012368555c1685250845c314367f55c167f2508458008367b55c167b250367895a167894e842e00816740345670f441670c38051602a369555c16952505690f441690c38368e95b368695a168e94f168694e56829421682936b2c635b92c634f161e32b1618329160c32589d83158454314368005a168004e567c042167c0361676012167200f166e00e5664f441664c38d49a643949a63789d4621844c620565c343165c337165631f165231b16683498450314844e92c36652501664f44b2c464f92c464389d66218452620165031b16603498448314365d55c165d250165a331844a314365755c165725089d2314164e00e365355c16532505650f441650c3889d0620164e31e364c05a164c04e89a4008366b250166af447666c4f5666c435662c38366694f1666943166292cb2bc34f92bc343d498337949832b89ca3158440314365e04f165e0435658037165802b1654013164a00f56432501642f44d4b2c4e94b2c421636c38161c92cd49234e9492342160832689c4314364355c1643250b2d6c5a92d6c4e1634c38362695a162694e161a92c160032589c6314163a01c0ec43280ec2328363755c16372505634f441634c38362495a162494e89cc92cd4903429490336160432615fc32584563141632029163001d0ec001c162e01113d2010162a0545626c38162692c1624620d48e036948e02a361d55c161d250561af44161ac38b2ca95a92ca94e89cc92c89c23140fe0025364755c16472507644f5b5644f4f5640f443644c5b1644c4f1640c38363e95bb2d495a163e94f92d494e563c943d4b0942163c93794b0936163892d162c92c362865b362265a162864f162264e56206431620637161e6211618620b2ba05b92ba04fd494043d48c0429494037948c036160a01b160201a15fa01989c800989be00856132501612f44160ec38160863635ee35855d434e55ca34c15d434215ca3400ab632835ea65855c864c0ab4634361355c1613250160063589bc62035f835a35e635815f834e15e634c55c63400ab232835e465855c064c15c06400ab0634360f55c160f25089ba62035f635a35e035815f634e15e034c55be34015be3340aae32835de06415de05855bc04c15bc0400aac01c55ba34c15ba3400aaa31c55b834015b83340aa831c1606010360955c1609250160492c55b604015b60340aa601035dc35815dc34c8a6032835da35815da34c8a5e32815fe0105600f441600c3815fc92c35d805815d804c8a5c01c55f8c3815f892c15f662015f205855d004015d003415b201c55eaf4415eac3815e492c55e8f4415e8c3815e292c15eb25015e8f4415dc32989ae31415e525015e2f4489ac31455dcc3815dc92c15da62015ef25015ecf4455e6c3815e692c15e062015de01f15d801d89aa00835d555c15d525089b800835d005815d004c15ce04015b001c15c8f4415c4c3815c092c15ba32a35c925015c8f4489b631435c525015c4f4489b431435c125015c0f4489b231435bb25015baf4415b862035cb25015caf4415c6c3815c292c15be62015bc01f15b601e89b000835b205815b204c55b004015b0034361555c16152505610f441610c38160c92c160a32b160232a15fa32989a831435f405a35f005935d605815f404e15f004d15d604c55d204255cc04155b404015d203615cc03515b403415ae01d0aa401c15ac00836cd25016ccf4476c0c4f56c0c4356bcc3836c094f16c094316bc92c36a864f16a86435696637169662b166c6211648620b2b804f92b8043d48a037948a02b161601f15aa01b8998009842a008b73d55c973d2507740f5b5740f4f573cf443740c5b1740c4f173cc38b29c35b929c34fd46a343946a33796ce31d95a831c89863158428314346a05b146a04f529c043129c03716ce01d15a801c0fcc0130cca00f098600904280081596f44158cc421584c38157c6429290365b288359928834dd46834391403359462329841c31414580651132035156e031127c029110601d03fa008159555c158b25a1583250157ac5a913e94d9460941841492c113064d156c649127a641110463503f862015a355c359f25b15932501588f4e1580f44157894eb29265bd46664f913c641945e635897e6218412620345a35b112e341156a33d127833511023290fca31f03f6314159c328159f868159a355841e314159555c841a92c359355c159725b1593250b29a65b929a64f157463d89846218426620158b55c8418620358955c158d25b1589250b29835b929834f89823158422314158355c841692c358155c158525b1581250b29665b929664f89806218420620157b55c8410620357955c157d25b1579250b28635b928634f897c315840e3141574f44157201103f40081566040155801c15646581556634156d55c840c92c156234c155e32a15543281565250840a62035632501566f4f1562f44b28434f9284343897a3158408314355f55c155f250155c620b28235a928234e89783141557250154e620354f250154ef4435552501558f4f1554f44355234f15523431550315154c314356b55c156f25b156b250b28065b928064f897662184066203568058156804c1560040155a01e154a01c35a155c15a525b15a12503598f5b1598f4f1590f44358ec5a158ec4e1586c42157ec381576642b27e35b927e34fd464343913a3351570331945c329897231583fc314345205b145204f112c0351548031127602910fa01d0fc601303f2008b52d55c83e892c153e32ab52b55c953725a15452501542c5b1536c4d9540c41552ac38154095a926664d953c649d44a637944862983e6620344a35b126634d153c34914483410fc431f03e6314b53355c153925b95332503536f5a1536f4eb27465b927464f944e641897062183f0620344635b144634f1262341525233512523290fc231f03e23141528c389264959b25494d925494183e492c144265903e06209525250352ef4f1524f44b26ec4fd444c43896ac3983dcc38344494f526e9430fc09370cc8933096a92d03dc92c152f55c152c949c3ea92c152725083def4403dac3835252501528f4f1524f44b272c4f9272c43896ec3983eec38343e94f143e9430fbe93703d892c35312501532f4f1530f44352ac4f152ac431522c38b27094f9270943d450937896c92d83ec92c343c64f143c64352686370fbc62b0cc6627096862103d6620b5212509534f4f9520f44753ac4f553ac435520c38353a94f153a9431534937152092cb25064f9250643d43a637943a62b896662183d4620343a34f143a3435250337125032b0fba31f0cc431b096631503d43145508c381510937150892c923e359b22e34d922e341d438337943832b83c8314138205951ce03711ce02b0ea201308e800908da0085507250150ef4f1506f44d43694f943694383be92c51cc64f11cc6430ea062b08e662108d8620151b2507516f4f5504f443516c4f150cc431504c38b24264fd4346439434637895c62183bc620338434f51ca34311ca3370e9e31f0cc231b08e431508d6314151755c151434983cc314150f55c83c6620350d55c151125b150d250b24e35b924e34f896431583d23141502c389240659b23064d923064183ca620137c35908d4314150125083c0c3808d292c150725014fef44b24894f895e92d83c292c337e64f0e9c62b08d0620150125083c4c3834ff2501502f4f14fef44b24c94f924c943896292d83d092c35052501508f4f1504f4414fcc38b24a64f924a643896062183ce620337834f13783430e9a31f08ce3143519250151cf4f1518f447512c4f5512c4354fac38351294f1512943150a93714fa92cb22c34f922c343d432337943232b894e31583ae314336a04f136a04351c603711c602b0e880130cc000f08dc00908a800814f155c5332f5954e8f4d54dcf441332c5914e8c4d14dcc388f7e6591430655920064d53a064313a0637833062051c434311c43370e8631f0e3031e08a6315087a31454daf4414e4c4314dac38545a943145a937145092c138436551c234311c2337106032b08a4315087831454d8c3814e293714d892c5458637145862b144e620138206551c003711c002b105e01f08a2009087600854d725014d6f4454d4f4414d4c38105c01d14f186854d2f4414e0c4314d2c3814c696154569431456937144c92c138036551be34311be337105a32b14ee02a144a62014e986814c4661144862014e586814e356614e155c14686671140659146264d144662014383718f7c359142e35591fe34d832e314135c0660e2e01214d755c8f7a959142c95591fc94d832c92c0e2c62a087462014d0f441444c38137e665087262014cec38144292c137c365087031414d786814ccf4414c2c611440c38137a66514d403614d155c14cf25a14cd250113ec4d1460c41143ec3814369658f7894d142a94991fa941832a92c135a65a0e2a62a14dd86814db55c14d925a14d325014cac3814c0961146695b113c94d145e941143c92c14346658f7664d142864991f864190d262b83286201378365136835b135835a105832b0e8431f0e2831e086e31454c325014c2f4414ba6281488329148032814b831c147e01c14b6934147c63414c355c8f74659142665591f264d14be62914b462883266201486329147a3280e2631e086c3148f6a658142465491e464c0e223340e1c31c54bef4414bec388f68358142235491e034cd38e342938e33651bc04311bc0370e820290e1e0280e800110e1a010086a00854b6f4414b6c3814b725014b294d14ae94914a2941149a92c149232a086831454b2c3814b292c086600814ac95813bc62854acc3814ac92c086400854aef4414aec3814aa65814a464c54a864014a863413ba31c1496029086200814a4f4854a2c3814a292c08600089392334149ec54148e01c549ac38149a92c085e3140e5231c14966545492c38149292c1490620548e336148e32a14bb25052e2c4d54b8c4154b4c3812e294d14b894114b492c14b064d14a664914a0641549c637149c62b149862051ba03711ba02b149401f148c01e08a0009085a008148955c5486f441486c38148492c8f72359141c35591ee34d0e82329832431451b804211b80360e7e012089e008547cf44147cc38147d250147492c8f7034d141a34991ec3410e2232983223145474c38147492c8f6e34d141834991e8341832031414720121416054148125052b0c4d547ec41547ac3812b094d147e941147a92c5478637147862b147662114706208f6c04d141404991e6041538e037138e02b146e01f0e1e01d831e00814c755c52fcf5954c4f4d54c0f4412fcc5914c4c4d14c0c388f66359141235591de34d538c343138c33714bc31d148a31c831c31451b604311b6037148201d146c01c0e7c0130e18012089c00908580085466c381468937146692c51b403711b402b08560081460c380854314545ec381462937145e92c51b203711b202b089a0090852008145b8681459566145755c1454c568f64359141035591dc34d831a31413560660e160125444f441444c3808506205442c38144292c084e3145440f441440c38144555c144325a1441250143ec388f6294d140e94991da941831892c135465a0e1462a084c620145155c144f25a144d250544ac5b5266c4d5448c41543cc38144a95b126694d14489411446937143c92c8f6064d140c64991d66415388637138862b8316620136635b135235a51b033711b032b0e7a31f0e1231e0898315084a3141436c3808483145434c381438937143492c51ae03711ae02b08960090844008542d250142cf44140a66491f665853e864c13e864013c86340e703290842314140836413c6328140696413c4940140495813c2940142d868142af441426c61140ec38140265813dc63613c063413763650e6e32908403141424934140066413da6401420634141a33413fe65813bc6285424f441424c3813fc35891e234c53e634013e633413ba31c0e6c029083e0085420f441420c380e6a011083c0080e6c63413fa36413d83280e6801c13f835813d632813f635813d432813d2010541af44141ac38141892c141632a13f405891ea04c53e404013e403413d001c54272501426f44142262813f236491f035853e234c13e234013ce334141e328141c02914140280e6601d083a00813f036413cc32813ee958540ef44140ec3813ec65891d864c53e064013e06340e6432908383145406f441406c380836314140755c1404c38140095513ee92c1374359083431413fe62813f832853fec3813fe92c083200853f8c3813f892c13f66205400f441400c3813fc31c13fa01d13f401c083000853eec3813ee92c082e314140b55c5402c381408937140292c13f265553f063713f062b13ec620137205951ac03711ac02b105401f0894009082c00813e631c13e401c13e955c13e265513e062013da96013bc62813d63280e5231c0e5c01053d6c3813d692c13d431413d201253daf4413dac3813ba31c13d801d13d001c0e5a011082a00853dcf4413dcc3813ce66053cc64213cc636105201d0e58011082800853c4f4413c4c380e5631d082631413c555c13c2c3813be95513aa92c13703590e5431d082431413bc62813b632853bcc3813bc92c0e5201d08220080e523280e5001053b6c3813b692c13b462013b201e53bef4413bec3813ba31c13b801d13b001c0e4e011082000853aac3813aa92c0e4c31d081e3140e4401013c955c53c0c3813c693713c092c13ae65553ac63713ac62b13a8620136e05951aa03711aa02b13a601f0e420110892009081c00814318685428f44142ec431428c38141296154109431410937140c92c13ea35891f434c53de34013de33413ca32a13a4328136c06551a804311a8037105002b0e4001d0890009081a008139ef600dec31c1396660139f868139cc381394661139a635138a620939231c139201c1396940939031c139001c13923341390c540dea01c1394f60938e31c138e01c0de8010138ac540de631c13a1b741398c54138c66d13886200dde010537ef44137ec38088c314537cc38137c92c088a008537af44137ac38137f55c137d25a137b2500e9664d137664991d46418314620136235a0e3831e137465813706345374c38137492c08880085370c38137092c0e3e01108860085376f441376c381372358136e3280e3c01d0884008138555c138325a13812505378c38137892c0e9434d136c34991d23418312314136405b136005a0e3a0130e3401208800081362370536292c13626205368c38136892c13666201364071136007051a403611a402a104801e087e008135a92c1354620535492c1354620535892c135c62b1358620535632b135631f135231414f786814f555c14f325a14ed25054eac5b5330c4d54e6c4154c8c3814ea95b133094d14e694114de93714c892c146a661146465b113a64d145c6415452637145262b143a62014323658f5e34d13a234991d03415386337138632b90cc31f830e314136a065135e05b135005a51a203711a202b104601f0e320130ddc012087c00908080083349868134955c3332f661332f5a131ef44322a667122a65b0f7e641121063d1200635894c62183ac62031c436711c435b0dda31f08063141342f44132ec421326c3d131cc38130694212986651132635127c6291274620124e3719224365b21c359921c34d0f7c33511fe32990ea31f839831411ce07111c006511a0042104401f0dd80130804008131b2500f7a94d11fc941839692c0802620134155c132d25a132525513192501304f5a1130c4d127ac411272c38124c9650f7894d11fa941838692c11cc665119e65a08006201349868134755c133f250132af4e1322f491316f441302c4e12fe961329a95b112e9411278935127092c124a665b22665b0f7664111f863590e862b893c621838462011ca36531c235b119c34e104232b0dd631f07fe314133c03c133a654134155c126ec381248965839292c1338348133b250126cc381246959839492c3339250133cf4f1338f44329494f1294943126a92c1244659322864f122864390f862b894a62183aa620333f55c134325b133f250329295b129294f126892c1242665322665b122664f90f662b894862183a8620133603c133386812fc6611266620132d55c126492c12406658390620332b55c132f25b132b250329065b129064f1262620123e365322435b122434f90f431f894631583a6314132555c126092c123c665838e620332355c132725b1323250328e65b128e64f125e620123a365322235b122234f90f231f894431583a4314331b868131b55c83a292c131434c13120401310658130e658131b868131955c12fac61125cc381238965838a92c130c34c331155c131125083a0620131155c130f25012f8955125a92c1236659838c620131555c330d2501312f4f130cf4412f6655328c64f128c64312586201234359322034f122034390f031f8942315839e314131f868331755c131d25b131725012f4961328a95b128a94f125692c1232665321e65b121e64f90ee62b8940621839c620130a040119a034119864c130555c125492c123066583886201196340330355c130725b1303250328865b128864f1252620122e365321c35b121c34f90ec31f893e315839a314119403412fb2500f7464d11f264112f262912e4628837e62012b632912b232807fc31412e231c12b001c12e093412ae63412f835812de62812ac32832f955c12f925012f031d12dc31c838231412aa01c32fb86812fb55c12ee62912da628838062012a832812f604c0f7064c11ec64012f004c0f6e64011e863432f386812f355c12eef4412ec94112ea93512e892cb21a366921a35a0f723410f6c340120e33c11ee33511e6334893831431bc06711bc05b0dd40290dd201107fa00812e0f4412d694112d093512c492c07f831412de34c32df25012def4412c262032e155c12e125012c092c12dc04032d755c12d725012ca62012ce63432d155c12d125012ce93012c862012ca94012c893412c204032c555c12c525012c0c3807f631412be03132e555c12e525032e2c5a12e2c4e12dac3832d865b12d864f12d463512d263112cc62912c662112bc62031ba05b11ba04f12ba01f07f400832b786812b755c0dd4329837c31431b806611b805a0dd001212aef4412a492c0f6a34111e4335837631412ac34c32ad25012acf44837a00832af55c12af250837831412aa04032a555c12a5250837431432b355c12b325032b0c5a12b0c4e12a8c3832a665b12a664f12a2620321a05b121a04f0f68035120a03111e002912a001f893a009837200832ff86812ff55c32fcf6612fcf5a12f4f443218367121835b0f66341120833d11de33512e631d12b831c8936315837031431b606711b605b12b401d129e01c0dce01307f2008129403c128c040119203412843641282010129b8681299566129755c1292f441290c42128ec3d128ac381288942128666690de3591280355921634d0f6433511dc32990da31d836831431b4067104005911b204d119004207f0008127b55c836e620327955c127d25b1279250321635b121634f8934315836a314127355c126f2501264f4e1260f49125cf441254c4e0f6294111da935835892c118e64e07ee620126c348326d250126cf44836692c326f55c126f250836492c126a03c326555c12652508362620326155c12612508360620125a34c325b250125af44835e620325d55c125d250835c92c1258040118c640325555c1255250835a620118a334327155c127525b12712501268f443266c5a1266c4e1262c42125ec3d1256c381252942321465b121464f0f60635120663111d66298932621835662031b035b11b034f11883420dcc31f07ec314124d55c12492501240f4e123cf491238f441230c4e8e9664111d463588be620118634e07ea314124634832472501246f4488cc620324955c124925088ca620124403c324155c124125088c8314323d55c123d25088c6314123634c32372501236f4488c4314323955c123925088c262012340401184340323155c123125088c03141182034324b55c124f25b124b2501242f44123ec42123ac3d1232c38122e942b1c835b91c834f8e9433511d232988e231588b631431ae05b11ae04f11800420dc001307e8008122803c1220040117e034921a31c121a01c122bb74922786892255669223561921f55c921d2661226f441224c421222c3d121ec38121c942121866d90de659921664d10de6351216629121462091c8371917c3668dc633591a6329903e31f87e631411c80710dc605911a604d117c042103e01f0dbe01307e600811f664011ea33411e2034120e62811f0340120c328120a02811d863412118681208961120692c11f4334120432a31fd86811fd55c11f6c3c881862011fd86811fb55c11f296111da92c11d4665881662011f755c11f065511d862011ec62811e432811ea31c11e201c31ed55c11ed25011ea93011e862031e555c11e525011e2930881400831f386811f355c11f0c3c11ee31d11e631c881231411e001c31db55c11db25011d8930881062031d555c11d52508882314120186831f955c11ff25b11f925011f493011de66131dc65b11dc64f11d662011d2365b1a635b91a634f904e31f888e315880e31411cd55c835462031cb55c11cf25b11cb25031c835b11c834f8930315835031411bc31d11ba31c11b801c11ac36411aa32811c5b7411c386811c156611bf55c11b666d11b4667104065911b264d11b062011ae3710dc635911a835511a634d831031411a40660dbc012119a6341198c4c119f55c1196940118e6201186365834a3141199250118c6201184359834c3143197250119af4f1196f44319234f1192343118a3141182059317e04f117e04390d8013892e009834e0081192634118c940318d250118cf448348314318f55c118f250118a6348346314118494031852501184f4488bc008318755c1187250118263488ba008117e634319d55c11a125b119d2501194634319035b119034f11883141180065317c05b117c04f90d6013892c0098344008134d868334555c134b25b13452501334f443330c5a1330c4e1328c421320c3d1308c381300942129c661327e65b127e64f112c63512766291250620122c365321235b121234f0f5e335120233111d032990d431f8928315833231411c606531a205b11a204f117a042103a01f0dba01307de008515ef441164c43115ec38114e96551329421132936112092c5106642110663610f436530ec35910ec34d8f52329908c31d8304314105e065504404310440370d9e01207d2008515d55c115d2505130f5a1130f4e111ef445104c5a1104c4e8f4e9419088935830092c0d9c62a07d0620117555c717125b515b2503170f5b1162f4f115af443152c5b5138c4f512ec4e1138c43112ec42112ac39111cc38510294e110294230f665b50d264f10d264310ca6378f4c63510b66339086629892462182fe620306035b504234f10423430db831f0d9a31e0cbe31b07dc31507ce314116e334116c328116a010117186811683550f54329108e31d83063140d9801231638681165567116355c3140966114095a30ea36710ea35b0f52329108c31d830c3140d96012115d55c1159250111af440f50941108a935830292c0d9462a07cc620315955c1159250313ef5a113ef4e0f4e9411088935830a92c0d9262a315b55c115f25b115b2501156f44314ac5b313cc5a114ac4f113cc4e1118c3830e865b10e864f10c86370f4c6351098631108662989266218308620305835b105834f0db631f0d9031e07ca3141150360105c02810e434c10e265810c26341084628114636410523280d8e01c1153868114f566114d55c514af44114ac38114896651369421136936112892c5100642110063610c6359114435510e034d10c0329108231d82f43140d8c01207c8008113ec3807c6314513cc381140937113c92c5040037104002b07da00907c40083139868113955c3136966113695a10be329108031d82fc3140d8a012113155c82fa620312f55c113325b112f25030de35b10de34f892231582f631404e803404fa0281126010312b868112b55c3128c661128c5a10bc635107a62982f26200d8831e112401a111f55c511b250111af4450fec4e10fec42107893582ee92c0d8662a1116335111232a311b55c111b250107693582f092c0d8462a311755c111725082ec6200d8231e311355c111325082d0314110e034110c01c311d55c112125b111d2505118f441118c3850fc94210fc93630dc65b10dc64f1072629891e62182e8620305635b105634f0db431f0d8031e1114029111001e110a01b110555c10fe92c82e66200d7e31e30ff55c10ff25082e46200d7c31e310355c110725b1103250310065b110064f10fc62030da35b10da34f10ba31f891c31582e03140d7801210f806010f006410d835810e6f4810e435810e235410d8f5810f786810f556610f356110ef55c10ed26650e8f4410eac4310e8c3810c695910e094d50de94210de93610dc92c50da64210da63610d63668dc4329903c31d87e43140db2059104e04d503e043103e0370d6001207c200810d0c480d5a31c30d155c10d1250904c31d880c3140d5e01230d386810d355c10ce93c8e74329904a31d880a3140d5c0120d5601010b263010ae6300db002810c235430cb86810cb55c50c925010c8f4430c6c6610c6c5a10c4c3830c096610c095a50be94e10be94210bc92c50ba64e10ba64210b432510ac324107031d891a31407c000810b2940906893430a866450a065810a064c0a886340d4e32830a436410a4358509e34c109e3400a7632810b001c30b355c10b325010ae92c10a955c10a725010a4329906c31d89163140d540120d4a31c30a155c10a1250109e329906e31d89183140d520120d4601030b786810b755c10b463510ac634906a6299064628891462030aa36630a236410aa35a10a2358509c34c109c3400a863280d5001e0d4401c3096658109664c5096c38109692c07be0085098f441098c383094358109434c50923401092334107c3280daa01d07bc0080d2c0100d2a0100d286280d26628308b55c108b2501088f449078c388a88932107692c87ba62010683320d4031e8d4231d0d2431c07b8314105295410843540d200100d1e0100a769340d1c0100a206200d1a31c0d186280d166280d14628307955c10792505076f441076c38107492c87b662010663260d3c31e8d3e31d0d1231c0a766248d320108d340108d3031c306e064106e058506c04c106c0405068f441068c381066620b08755c908d25b9087250708ef5b508ef4f5086f44308ec5b108ec4f108cc431086c38b08095b908094fd0829439082937907a92d907292c308265b108264f50806431080637107062b107e6278a866260a86625107c624107a6211072620b03c35b903c34fd04a343904a337107031f906a31b906431a87d831587b4314304a05b104a04f503c043103c037107002b106a02710640260da80130d2e0128d2e0110d060100cbc00f07d800907b4008105c0280d22010105436410523280da601c104c9548d360101061868105f566105b55c5058f441058c38105692c0db23591050355104e34d0e74329104a31d82dc31410480660da401207d60088d3801030438681045567104355c3040966104095a303e367103e35b0dc4329103c31d82de3140da2012317355c117725b11732507166f5b5166f4f5154f443166c5b1166c4f1160c431154c38314295b313a95a114294f113a94e5134943512c9421134937112c936112292d110892c50fa64210fa63630d435b10d434f50cc34310cc33710b832b0f3e329109a3271090325106231d890a31582cc314304605b104604f503a043103a0370da00130d040120cba00f07d400907aa008b02b868902b55c7035267503525b502b2503034f671034f5b102af44af9c967af7e9668f9c95b8f7e95a4f9c94f4f7e94e0f9c9430f7e9420f3c92d0f0892cadda6678dda65bce8664fce3064e8e866438e3064287a862187746202e863672e303660e8635b0e3035a4dda34f0dda3430cb831b8c9631a0c9631907a831507743140fb89701035b74101c96d0fc492c0fb667110326550f5462a0f066208d9832a0d9802ab029868102f567902955c0fc292c0fb4671af7c6668f7c65a0f5262a0f046208ea2371add83678dd835b8d9e32a87723142e2e0660e2e05a0d9602a3027868102755caf7ac668f7ac5a0f02c38877092c2e2c6660e2c65a8c94626076a6201027868902355c1023250101af610fc0f440fb2c650f50c420f00c388e9c9658d94942876892c0e9c6650d946420768620302355c10232500fbef440fb0c65af78c5a8f78c4e0f4ec420efec388ea09658d9c942876e92c2e2a65a0e2a64e0d92642102b868302555c102925b10252501020f441018c61afcac5b8fcac4f0fbcc380fae965af9a95baf7695a8f9a94f8f7694e0f5c9370f4c9360f3a92d0efc92c8e9e665add665b8dd664f8db86378d9a63687a6621876c6200e9a3652e8435b2e2835a0e8434f0e2834e0db63370d903368c9231a076631410106288ff23280ff2028100ec408ff09400ff0640301b868101b55caf749668f7495a1016935100c9340efa92c8ffc6358ff463487646202e263660e2635a0ffa3350fee3348c9031a0762314b017868901755c50172501016f441014c38af986668f9865a4f9864e0f986420f38620ce2434e8e2434287603142e240660e2405a8c8e00e0c8e00d0760008300f55c100f2501006c38875e6202e2235a0e2234e8c8c31a075c3140f1c028b00755c90072505006f441006c38ce206428e20636848a6202e2035a0e2034e8c8831a0c88319048a3141004029900201d1002011b00d55c900d2507010f5b5010f4f500cf443010c5b1010c4f100cc38b00a95b900a94f500a943100a937100892d100092cadd435b8dd434fce82343ce1e3428e823378e1e33687a431587583142e8205b2e1e05a0e8204f0e1e04e4dd40430dd40370cb600f8c8600e0c8600d07a400907580080c843182ffd8680ffd55c4ffb2500ffaf440ff8c38af726668f7265a0ef862087563142e7e0660e7e05a4dd004e0dd00420cb400e0c8200c07a00084ff12500ff0f440fe4c384f6a64e0f6a6420ef6620ce1c34e8e1c3420fd633287523142ff155c0ff12500fe2c38af7065a8f7064e0ef462087543140e5c01c0fec0542fe555c0fe52504fe2f440fe2c38af6e65a8f6e64e0ef262087503140fe00192fdc0640fdc0584fda04c0fda0400a800284fd434c0fd43400a5a3282fd52500fd4f440ef00082fd755c0fd72500eec3144fd20400fd20340a5801c2ff555c0ff52506ff2f5b4ff2f4f4feef442ff2c5b0ff2c4f0feec382fea95b0fea94f4fe89430fe89370fe692d0fde92caf9635baf6c35a8f9634f8f6c34e4f943434f683420f943370f683360f363150eea314add205b8dd204fce80043ce1a0428e800378e1a0360fd80270fd002687a2009874e008b019868901955c701d267501d25b5019250301cf67101cf5b1018f44af92667af666668f9265b8f6665a4f9264f4f6664e0f926430f6664210126290ffe6280f346210ee8620adce3678dce35bce7c34fce1834e8e7c3438e183428ff63298fce328879e31587463142e7c0672e180660e7c05b0e1805a4dce04f0dce0430ff60290fce0280cb000f8c7c00e0c7c00d079e00907460080d7e3340d7a0342fcb8680fcb55caf646668f6465a0fc863d0ee662087443142e160660e1605a0d780282fc155c0fc12500fbef44af62c5a8f62c4e0ee4c38874292c2e1465a0e1464e8c7a6260740620afbd55c8fc325b8fbd2506fc4f5b4fc4f4f4fbcf442fc4c5b0fc4c4f0fc2c430fbcc38af9095baf6095a8f9094f8f6094e4f909434f609420f909370f609360f3292d0ee292cadcc65b8dcc64fce7a643ce126428e7a6378e12636879c621873c6202e7a35b2e1235a0e7a34f0e1234e4dcc3430dcc3370cae31b8c7831a0c78319079c315073c3140fac9600faa96c0fb86540fa896c0fa6f600fa4f602fb355c0fb32500fb0f440fa2c60af8a95a8f8a94e0f2c92c873a6202e1035a0e1034e8c7631a07383140fac6542fa755c0fa72500fa4f44af8895a8f8894e0f2a92c87366202e0e35a0e0e34e8c7431a0734314afa355c8fa925b8fa32506faaf5b4faaf4f4fa2f442faac5b0faac4f0fa8c430fa2c38af8e65baf8665a8f8e64f8f8664e4f8e6434f866420f8e6370f866360f306210f28620adca35b8dca34fce78343ce0c3428e783378e0c336879a31587323142e7805b2e0c05a0e7804f0e0c04e4dca0430dca0370cac00f8c7200e0c7200d079a0090732008afaf55c8fb525b8faf2506fb6f5b4fb6f4f4faef442fb6c5b0fb6c4f0fb4c430faec380fa0960af8c65baf8465a8f8c64f8f8464e4f8c6434f846420f8c6370f846360f2e6210f26620adc835b8dc834fce76343ce0a3428e763378e0a3368798315872c3142e7605b2e0a05a0e7604f0e0a04e4dc80430dc80370caa00f8c7000e0c7000d0798009072c0080f8a9700f986280f963280f940280f8e96c0f889602f8955c0f89250872a3142f8b55c0f8b2500f8666087283140f9db742f9b8680f9b55c0f9296d0f9092c0f8c6710f846702f826660f8265a0f5862a0f246208e983718d7632a87263142e080660e0805a0d7402a2f7b8680f7b55c87246200f7b8680f7955c0f749610f6292c8e9666587226200f706280f6a3282f7155c0f712500f6e6202f6b55c0f6b25087200082f758680f7555c0f7231d0f6c31c871e3140f6801c2f6355c0f63250871c6200f7f8682f7755c0f7d25b0f772500f666612f6465b0f6464f0f606208e94365adc635b8dc634f8db231f8796315871a314af5d8688f5d55c4f5d2500f5cf440f5ac38af586668f5865a4f5864e0f586420f22620ce0634e8e0634287183142e060660e0605a8c6e00e0c6e00d07180082f5155c0f512500f4ef440f46c38871662007143140f16028af4755c8f472504f46f440f46c3882ea62002ea3140f440298f4201d0f42011af4d55c8f5325b8f4d2506f54f5b4f54f4f4f4cf442f54c5b0f54c4f0f52c430f4cc38af4a95b8f4a94f4f4a9430f4a9370f4892d0f4092cadc435b8dc434fce743438e74337879431587103142e7405b0e7404f4dc40430dc40370ca800f079400907100080f2cc700f1c0280f1a0280f389348f366340f363340f180400f30c6c0f2ac60af2b55c8f2b2504f2af440f2ac38ce046428e04636870e6202e0435a0e0434e8c6c31a0c6c319070e3148f1201d0f12011af2d55c8f2d2504f2cf440f2cc380f28960ce026428e02636870c6202e0235a0e0234e8c6a31a0c6a319070c3148f1001d0f100110f160288f200280f2001c0f1c6288f1a3280f1a0280f1896c0f166288d723280d720280f129600f109700f0e01c0f3db74af3b8688f3b55c4f3b2500f3af440f34c6d0f32c380f2e9710f26970af249668f2495a4f2494e0f249420f229368e92671ce0064e8e006428d70636870a6200e923712e003660e0035a0d703368c6231a0c62319070a3140f1e06d0f140368f0c01d0f0c011af038688f0355c4f032500f02f44cdfe94e8dfe942824692c2dfe6660dfe65a8c606260c6062502466208eb83290eb831d0f038682f0155c0f012500efef440efac610ee4c388e909658d6e936824492c0e8e6652dfc65a0dfc64e0d6c6368c5e62602426200ee03610eca3360eb631d8ef69340ef46340ec83400c5c3180ec60280ec43280ec232889ce3284ef03400ef03340a3c31c0eee0102ef755c0ef72504ef4f440ef4c380ef292ccdfa3428dfa3360eec32682403140ed001d0ec001c8eb4011aefb8688efb55c4efb2500efaf44cdf864e8df86428ef86298eea628823e6202df83660df835a0ef83290eea3288c5831a0c58319023e3140ece0350ebe0348eb201d0eb20110d68328aee555c8ee52504ee4f440ee4c38cdf69428df6936823c92c2df665a0df664e8c566260c56625023c6208eb03290eb031d8edc3340eda3280c543242edd55c0edd2504edaf440edac38cdf46428df463681a46200c543190ed83148eae01daee18688ee155c4ee12500ee0f44cdf294e8df2942823492c2df26660df265a8c506260c5062502346208eac3290eac31d8ede02a8ed60280ede01e0ed601c8ed06280ed03280ece96c8d666280d663280ec89608ec46280ec23282ec52500ec4f444ec2c380ec292c89ce6208232008aec955c8ec92504ec8f440ec8c388ec631d8ec031c82303140ec601d0ec001c0230008aecb55c8ecb2504ecaf440ecac380ebe6608db031d822e3140db001d022e0080e8c3700eb46280eae0280eb98684eb6f440eb6c380eb29610eb092ccdf06428df06368d6462a0eac0610eaa01d0f09868aefd55c8f0525b8efd2506f06f5b4f06f4f4efcf442f06c5b0f06c4f0f04c430efcc380ee8961aee695b8ee694f4ee69430ee69370ee292c8e8a665adc265b8dc264fce72643cdee6428e726378dee6368dae62b8d6262a8792621822c6200e8a3652e7235b2dee35a0e7234f0dee34e4dc23430dc23370dae32b0d6232a0ea631f0ca431b8c3c31a0c3c3190792315022c3140ed4061aed205b8ed204f4ed20430ed20370ecc02b0ebc02a8eba01f8ea801d0eba0130ea80110ea600904e20080ea155c4e9d2500e9cf440e9092c8706620078a3142e9d55c0e9d2502e9695a0e9694e0e8e92c87086202e3835a0e3834e4e96c380e9692c07880082e9155c0e912504e8ef440e8ec3882386202e3635a0e3634e0ca031a07863140e8c0112e9f55c0ea325b0e9f2504e9af440e9ac382e9865b2e9465a0e9864f0e9464e0e926210e8a620adc035b8dc034f878e31586fe3142e3a05b2e3405a0e3a04f0e3404e0c9e00e07840080e706600e6e6540e383700e6c3540e680540e826280e663600e803280e7e0280e646540e623540e7896c0e603540e5e6540e363700e566340e546340e5231c0e5c01c0e6c6280e5a3340e6a3280e680280e4a3280e629600e483280e466280e5231c0e5c01c0e5a6600d2201c0e5231c0e5001c0e4a6540e5755c4e54c380e5492c0e4e6550e4c6200e483590e463140e3e0590e4401e07820080e718684e6ef440e6ec380e669610e6492c0e606650e5e6200e5832a0e423280e3c0650da602a07800080e3e3280e3c3544e38c380e3892c0e363140e87b744e84f440e84c380e7c96d0e7a92c0e766710e7462a0e726200e403548d5c32a0e3a0710e340704dbc0420dbc0360da402a077e0084e2cf440e2cc380dfe6204dec3420dec3360e2d8680e2ac380e269610e1492c0e106650dfc6208d5a32a0e226280e1c3284e22c380e2292c0e206204dea0360dea02a4e1cc380e1c92c0dfa0084e26f440e26c380e2431d0e1e31c0df83144de80420de80360e1a01c4e14c380e1492c0df66204de63360de632a0e0e9604e0ec380e0e92c0e043144de40360de402a4e10c380e1092c0e0c6600e023144de20360de202a0e046600e026700dfa31c0df401c0dff8684dfcc380dfc92c0df86610df66204de03360de032a8d5831e0df20610df00110dea0100de43600ded8680de83610de63140de20650de00080e318684e28c380e2e9370e2892c0e186614e166370e1662b0e126200e0a3654e083370e0832b0e0631f0e003150dee3144dde0360dde02a8d5601e0dd46280dd23280dd00280dca96c0ddbb742dd78680dd95670dd755c0dce96d0dcc92c0dc86712dc66660dc665a0dc462a0dc26200dc03712dbe3670dbe35b8d6032a86fc3142dbc0660dbc05a0da202a8d406340c3a3188d426348d3e6340dac6308d3a6280c383180db00280dac6200c9c00c0d2201c0da60548d3601c8d3801c2db98680db955c4db72500db6f440db4c382db26660db265a0dae6200daa3300da83298d2e32886fa3142da40660da405a4da204e0da20420c9a00e0c3600c077a0088d2a01c8d266340d9d55c4d952500d94f440d86c384d7e94e0d7e9420d6e6204d5a34e0d5a3420d4e3320d423298d2432886f63140d2c01c0d2a01c0d286340d266342d9555c0d952500d92f440d84c380d6c6200d403290d2432886f83140d2201c0d8e0540d2001c0d1e01c0d1a3280d186340d166342d8755c0d872504d84f440d84c384d7c9420d7c9360d6a6200d3c3290d1232886f43140d820292d7f55c0d7f2500d7c6200d7a3310d6831486f20088d1001c0d1001c0d0e3280d720288d0c6280d0c6280d0a6282d6f55c0d6f2504d6cf440d6cc380d6a92c4d686420d686364d583420d583360d4c3260d3a31d0d0831c82363140d6601d0d640110d3801c0d5e93c0d3601c2d5b55c0d5b2500d580080d3401c0d3201c0d303282d540640d540584d5204c0d520400a6e0284d4a34c0d4a3400a303284d483400d483340a2e31c2d4b2500d4af440d480082d4f55c0d4f2500d4c3144d460400d460340a2c01c2d340580d3404c4d320400d320342d4355c0d432504d40f440d40c380d3e92c0a6e6250d3c6200d3a3142d3805a0d3804e4d360420d360360d3001a877c0082d292500d28f440d26c388d1892c8a306260d166200d0c3140d226482d192500d18f444d16c380d1692c0d146200d0a314ad0d2508d0cf444d0cc380d0c92c8d0a6208a2e31a0a2e3190d0a314ad252508d2af4f8d24f446d2cc4f4d2cc434d24c382d2c94f0d2c9430d2a9370d2492cad1e64f8d1e643cd206378d2062b8d1a6218d126202d2034f0d203434d1e3370d1e32b0d1c31b8a2c31a0a2c3190d1a3150d12314ad1004f8d100434d100370d1002b0d0e0090d080082d9b55c0d9f25b0d9b2506d98f5b4d98f4f4d90f442d98c5b0d98c4f0d96c430d90c382d8c95b0d8c94f4d8a9430d8a9370d8892d0d8092c4d786420d786362d7635b0d7634f4d743430d743370d703150d623142d6005b0d6004f4d5c0434d560420d5c0370d560360d500270d440260d2e01d0d0601c878c00986ee0081037868b01f55c902d25b901f2507030f5b5030f4f501ef443030c5b1030c4f102cc43101ec380fcc961afc695b8fc694f4fc69430fc69370fba92c0f9e665af8065baf5e65a8f8064f8f5e64e4f806434f5e6420f806370f5e6360f5662b0f3e62a0f0a6210ea46208e88365adba35b8dba34fce32343cddc3428e323378ddc3368da032b8d0432a877831586d63140e880652e3205b2ddc05a0e3204f0ddc04e4dba0430dba0370da002b0d0402a0c9800f8c3400e0c3400d077800906d6008acff8688cff55c4cff2500cfef4486d492c0cb862b8c9662a0c9662906d4620ac30366ac10365abea3648c3035a8c103598bea3584c3034e4c1034d4bea34c0c303420c103410bea3400ae43350ac83340a263142cfd8680cfd55c86d2c388c94936ac2e666abe86648c2e65a8be86584be464c0ac6640abe29644be29580ac494c0cfd8680cf6f610cc8f44abe06584be064c0b046420ac26400cff8682cfb55c0cfb2500cf4c610cc6c388cc29658cbe93786d092c8c9262aac2c35aabe63588c2c34e8be634c4bde3400b023360ac03348cecc400cec940abd26644bd26580afe64c0cd66402cf78680cf755c8cf29358cee93486ce92c0cea6348c9062aac2a366abd43648c2a35a8bd43584bd034c0afc3400cd43340c8c9400c84628abca3644bb03580bb034c0aba3342cf38680cf355c0cb66350c8663486cc6200cb431e0c8231cac28066abc60648c2805a8bc60584bae04c0bae0400ab80284ced2500cecf440ce8c380ce2636abc03584c2034e4bac34c0c203420bac3400ab6328abc26584baa64c0ab46342ced55c0ced2508c8c63586ca620ac2635aabc43588c2634e8bc434c4ba83400ab2328abba6584ba264c0ba26400ab06342ce955c0ce925086c8620ac2435aabb63588c2434e8bb634c4ba03400ba03340aae328abb40648bb40584b9e04c0b9e0400aac01c4b9c34c0b9c3400aaa31c4b9a3400b9a3340aa831c0ce00102ce355c0ce32500cde92c4b980400b980340aa60102cef55c0cef2504ceaf440ceac380ce692c0ce432b0cdc32a8c8632986c6314ac2205aac0e059abb20588c2204e8c0e04d8bb204c4c1e0424c0c0414b960400c1e0360c0c0350b960340ae201d0aa401c0a24008ac0a0648c0a0584c0a04c0c0a0400adc0282cd755c0cd725086c46208c8031e0cd2940acd555c8cd52504cd4f440cd4c38acd09598cd094d4cd09410cd09350cce92c0adc62a86c23140cb20138c7e0120c7e01106c2008acf58688cf555c4cf52500cf4f448cf06298cda62886c06200cf03290cda3280cb031f8c7c31e0c7c31d06c0314ac1c066ac08065ab940648c1c05a8c080598b940584c1c04e4c0804d4b9404c0c1c0420c080410b940400b0c0350af80340cd80290ccc0280a22008ab909584b9094c2cc955c0cc925086bec388c7a936ac1a65aab926588c1a64e8b9264c4b8e640acc755c8cc72504cc6f440cc6c3886bc92c0cae62b8c7862a0c7862906bc620ac1835aac06359ab883588c1834e8c0634d8b8834c4c183424c063414b883400c183360c063350b883340a1e314ab863584b7a34c0b7a3400a903342cc355c0cc325086ba6200c9e31eac1605aab820588c1604e8b8204c4b780400b780340a8a0280c3a628ab803644b763580b7634c0a883340c9c31cab740648b740584b7404c0b740402cbf8680cbf55c0ca86350cbc62986b86200c9a31e0c3631cac14066ab7c0648c1405a8b7c0584b7204c0b720400a86028ab703708b703644b703580b7034c0a84340ab6e0648b6e0584b6e04c0b6e0400a82028ab6c0648b6c0584b6a04c0b6a0400a800280cb69348cb46340cb4334ab680708b680644b680580b6804c0af60400cb2034ab663648b663584b6634c0b66340ab640648b640584b6404c0b640400a7a0340cacc6cab620648b620584b6204c0b620400a78034ab600648b600584b6004c0b600400a760288ca26640ca23648ca09700ca0670ab5e3648b5e3584b5e34c0b5e3400a743340ca6010ab5c3588b5c34c0a723280ca20100ca0620ab5a0588b5a04c0a70028ab560588b5604c4b560400b560340c9c328ab580648b580584b5404c0b540400a6e0280cb9b740cb0c6d0caec380caa9710ca89360ca492c8c9e6708c9a6360c9e3700c9a336ab520648b520584b5204c0b520400af40360a6c0342c958680c9555c0c6092c4b5034c0b503400a6a3344b4e6580b4e64c0a686400c958680c90c610c7ac380c769650c5e92c0c3a6364b4c34c0b4c3400af23360a663340c8c9340c846344b4a3580b4a34c0af03400c803344b4804c0b480400a620284b4634c0b463400a603284b443400b443340a5e3280c8a0102c8d55c0c8d2500c8892c4b420400b420340a5c01c4b4034c0b403400a5a3282c8555c0c852500c5c3144b3e0400b3e0340a5801c2c8155c0c812500c5a3142c918680c9155c0c8e6290c866280c586200c823284b3c04c0b3c0400aee0340c7e0284b3a64c0b3a6402c7b55c0c7b2500c5692c4b383400b383340c74c604b3634c0b363400a503344b3434c0b343400a4e3342c7555c0c752500c6c6204b320400b320340a4c0282c7755c0c772500c729600c6a6204b300400b300340a4a0284b2e04c0b2e0400a480284b2c3400b2c3340a463280c680100c6c9604b2a3400b2a3340a443280c660100c686540c666640c6a9704b2834c0b283400a423340c640104b2664c0b266400a406340c4a31c4b2464c0b246400a3e6340c4831c4b223400b223340a3c31c0c460100c5c6284b2034c0b203400aec3340c5a3280c440104b1e6400b1e6340c4231c4b1c3400b1c3340a363284b1a64c0b1a6400a346340c4e31c0c540280c5201c0c4e0600c4631c0c4b55c2c492500c48f440c446550c426200c400550c618682c5f55c0c5f2500c589610c5692c0c3862a4b183400b183340aea32a0a323280c500610c4c0110c3e0104b1634c0b163400a303284b143400b143340a2e31c2c3b55c0c3b2500c383144b120400b120340a2c01c0c978682c9355c0c932500c7c9610c7892c0c706650c6e62b0c626210c3c6200c3632a4b100400b100340ae802a0a2a028ac040588c0404c4c040400c040340ad80282c2f8680c2f55c86ac6200c2f8680c2a9610c1a92c0c266280c203282c2755c0c272500c246202c2155c0c2125086aa0082c2b8680c2b55c0c2831d0c2231c86a83140c1e01c2c1b55c0c1b25086a66200c318682c2d55c0c2d2500c1c6610c186200c163650c1431f86a43142c023640c023580bf834c0ad6334ac000588c0004c0bf60400ad401c2c000580c0004c0bf40400ad201c0c0e6280c0c3282bfe0640bfe0580bf204c0b0a0340c0a0282bfc3580bfc34c0bf03408c0031c0c0001c0c0355c0bfe6550bfc6200bf631c0bf401c0bf955c0bf26550bf06200c118680c089610c0692c0c040642bfa0580bfa04c0bee0400b0802a0acc0282be955c0be92500be4f440bdcc3886a26200b7031f0b5031d067c3140be32500bdaf440b4e629067a6200be955c0be0f440bd8c380bd49550b9292c0b7a3590b7632b0b4c31d06783142be355c0be325086a092c0be355c0bd2c550b90c380be555c2be12500be0f440bd09550b8e92c0b866590b8062b869e6202bdb55c0bdb250869c92c0bdb55c0bcec550b8cc380bdd55c2bd92500bd8f440bcc9550b8a92c0b846590b7e62b869a6200bd32500bcef440bc46280bb03290bac3280b4a31d06763140bc29340baa6342bd355c0bd32500bca6290bc062886986200ba83280bbe9340ba66342bcf55c0bcf2500bc86290bbc62886966200ba43280bcaf440bc8c380b6e0290b6c01106740080bc2f440bbec380b4632906723142bc32500bc2f440bba92c2bbf2500bbef440bb892c0bbac380bb892c06703142bc52500bc4f440bc0c380bbc92c0bb66200bb401f0b4201d066e0080b466340b4031c2bb155c0bb12500b6e3290b4232886943140b6a0120b3e0100baaf440ba6c380ba292c0b9c32a2bab2500baaf4486923142ba72500ba6f4486903142ba32500ba2f44868e3142b9d2500b9cf440b9a6202bad2500bacf440ba8c380ba492c0ba06200b9e01f0b9801e868c0082bd555c0bd52500bd0f440bccc380bc631d0bb231c868a3140bae01d0b9601c0b680130b3c011066c0080b90f440b8cc380b3a629066a6202b912500b90f44868892c2b8d2500b8cf44868692c2b932500b92f440b8ec380b8a92c86846200b6631f0b3831d06683140b86c380b8492c0b5a01106660080b80f440b7ec380b600290b7401d0b5801106640082b7b2500b7af4486823140b1631c0b560102b7755c0b772500b603290b7431d86803140b540120b120100b6e6280b6c3280b6a0280b649600b5c6640b5c3140b5601c0b5601c0b718680b689610b6692c0b626650b6062a0b5e6200b5a3640b5832a0b5402a2b4f55c0b4f2500b266200b4f55c0b4a9550b3a92c0b366590b246200b1632a0b466280b403282b472500b46f440b446202b412500b40f440b220082b4b55c0b4b2500b4831d0b4231c0b203140b3e01c2b3b2500b3af440b1e6200b349542b352500b34f440b2c3142b372500b36f440b326540b2a3140b2c6540b2a6640b2231c0b1c01c0b2755c2b252500b24f440b206550b1e6200b1431e0b1a0552b172500b16f440b140080b5155c2b4d2500b4cf440b3c6550b386200b303590b2e31f0b283150b183140b1201e0beb55c2be72500be6f440bdec380bd692c0b946550b886200b823590b7c31f867e3140b780590b7201f0b520130b10011065a0088ae26280ae2328ab0a0648b0a0584b0a04c0b0a0400adc0280ad431c0ad201c0b0a6600b0c96cab080648b080584b0804c0b080400afec602b0555c0b052500afc9608a8862986586208af231e0afa9608ab49340ab46342aff55c0aff2508aba6298ab662886566200ab23288af031e8aa06280aa0328aafd55c8afd2504afcf440afcc380afa92c8ab831d8aa431c86543140ab801d0aa401c0af60138aee0120aee01106540080a826288a803280a800280af696c0a766288a6e3280a6e0280af09600a303280a606280a5a3282af155c0af12500a6231d0a5c31c0aec3140a5801c0a3c31c0aec6600a2e31c2af355c0af32500aee6600a4831d0aea3140a2c01cab0355c8b032504b02f440b02c380b0092c0af86608a8631d864e3140a8601d0af40138ae80120ae8011064e008aad63648ad63584ad634c0ad6340aad40588ad404c4ad20400ad20348ae26280ae2328aad00648ad00584ad004c0ad00400adc0280ada364aace3588ace34c4ace3400ace3340adc6550ada6200ad431c0ad201c0ad755c0ad06550ace6200ae58680ae09610ade92c0ad8064aacc0588acc04c4acc0400acc034aac755c8ac72504ac6f440ac6c380a9a92c864c6200a8431f8a6a31e0a6a31d064c3142ac555c0ac5250864a92c8a6862a0ac555c0abec550a98c380ac755c2ac32500ac2f440abc9550a9692c8a906598a8862b86486208a6631e8ab49340ab46342abf55c0abf2508aba6298ab662886466200ab23288a6431e0a606340a5a31c2abb55c0abb2500a823290a5c32886443140a800120a580104ab4f440ab4c380ab092c0aaa32a2ab52500ab4f448a6032986423142ab12500ab0f4486403142aab2500aaaf440aa86202ab72500ab6f444ab2c380ab292c0aae6200aa03140aac01f0aa601e8a5c01d863e008aabd55c8abd2504abcf440abcc380a9e92c8ab831d8aa431c863c3140ab801d0aa401c0a7e0138a560120a56011063c0088aa06280aa03280a9e9602a992500a98f44863a92c8a5462a0a9b55caa972508a96f444a96c380a9692c8a8c65986386200a8c3590a7c31f8a5231e0a5231d06383140a940592a912500a90f440a8e6550a8c62086363140a700120a3031c2a8955c0a892500a7632986343140a6e0120a2c0100a826288a803280a800280a7a9608a726640a723640a723140a858680a7e9610a7c92c0a786650a7662a0a746208a703648a6e32a0a700640a6e02a2a6955c0a692500a406200a6955c0a649550a5492c0a506590a3e6200a3032a0a606280a5a3282a612500a60f440a5e6202a5b2500a5af440a3c0082a6555c0a652500a6231d0a5c31c0a3a3140a5801c2a552500a54f440a386200a4e9542a4f2500a4ef440a463142a512500a50f440a4c6540a443140a466540a446640a3c31c0a3601c0a4155c2a3f2500a3ef440a3a6550a386200a2e31e0a340552a312500a30f440a2e0080a6b55c2a672500a66f440a566550a526200a4a3590a4831f0a423150a323140a2c01e0ac955caac12508ac0f444ac0c380ac092c0aa26550a9c6210a926208a8a3598a8631f862c3140a8a0590a8601f0a6c0138a2a0120a2a011062c0088a246280a243280a2000c0a278680a229610a1e92c0d01868acf955c8cf92504cf8f440cf8c380cca9610cc492c8cc06658cba62b862a6200cc03650cba32b0c9831f8c3431e0c3431d062a3140c32065ac1205aabec059ab0e0588c1204e8bec04d8b0e04c4c120424bec0414b0e0400c120360bec0350b0e0340b0602b0ae602a0aca0290a280280a1c0082a158680a1555c4a0f2500a0ef44294c967094c95b090892d82ca92c28a6667287a66608a665b087a65a480664e080664207a862b077462a06d462625fc36605fc35a45f034e05f034205aa32a056e32705263264a0cf440a0cc380982965097092c09646710946665293e659093e64d82c462008e837108da37008a236508763644804342080433607d232a077231e45ee04205ee03605be02a05a801e4a0b55c0a0b25082c2c38480295a080294e077093606d293245ec65a05ec64e05a66364a0955c0a09250096ef440962c6582bec3808e696508d8964480095a080094e07d0942076e93645ea65a05ea64e05bc64205a46360a158680a1355c4a072500a06f440a02c612984c5b096cc380960965294895b0926937890692d82bc92c08e466508d666428a465b287865a47fe64e07fe64207dc63707ce63607a662b076c62a06d0626062836145e834e05e834205ba33605a232a056a3272a0b8680a0b55c82c8c382874966087495a076a936052463208d4670087066408d2c640a0b8680a0955c0a00f61096af44095ec6582c0c3808d0964287295a07cc94207689360a0f8682a0755c0a0d25b0a0725009fec61297ec5b097ec4f0968c38095c965293c95b093c94f0924937090692d82c692c08ce664286e65a086e64e07ca636076662a05223264a0155c0a0125009fc93509e293482b892c47fc65a07fc64e09966350992634076462a06ce62645e635a05e634e05a032a09e0c4009909402a018680a0155c09fa93509de93482ba92c286c666086c65a098e634076262a0520326075e640075462806ca624059c328075c640075262809e833c051e324075062806c8624059a328047e01c09f800c29f236409f235849f034c09f03400644328056201c49e8f4409e8c3804f401229fd86809fd55c49fb25009faf4409f6c38293a666093a65a8904620286a366086a35a47fa34e07fa34209f433607a4335075833409ee332075631e07a231d074e31c06cc31a06c631845e404e05e404209ec03609ea03109e6030059e01e059801c0568019051c01849e125009e0f4409d6c3847f864e07f864209c663609bc63245e234e05e234209a633629e155c09e125009d4c38286865a086864e09c4636099c3320866358086034c88f201c09c263409ba63009a4334042e01c09da00c09ce02829d755c09d725049d4f4409d4c38285e65a085e64e47f664207f663645e034205e033609d201d09d001909cc00d29c755c09c725049c4f4409c4c38286695a086694e045692c09c262009c002529b665849ae64c09ae640064262829b265809b264c49ac64009ac634064062809b725009b4f4409b262029af25009aef4409ac62029bd55c09bd25009ba92c29b835a29b035809b834e09b034c49aa34009aa334063e31c29a755c09a725009a4620285c05a085c04e09a001c499cf44099cc38851601229e355c09e325049def4409dec3829dc95b09dc94f09d892d09ca92c28a035b285a35a08a034f085a34e47f434207f433609c832b09be32a09a832625fa05a05fa04e45de04205de03609a202a099e027099a0262997868099755c07a463582b6620289e366089e35a07a031e051a01a49912500990f44075e63582b262045dc34e05dc342059631e299155c0991250075c63582b4620051831a299355c0993250498ef44098ec38298c95b098c94f293835b093834f098a32b0758329090431582ae31425f805a05f804e45da04205da0360594012056600f051400e2a038680a0355c49ff25009fef442936667093665b09e46290998628090262182ac620289c3672858366089c35b085835a47f234e07f234209943290988328079e31f074631e06c031a25f606605f605a45d804e05d8042059201e055c01b050e01a07c6658085464c097a664097831c09858680983566098155c497ef44097ec38097c96609226590976655093464d091c62982aa620285636607da35907c4358089a34d085234c47f034207f0336074431e097405545d604205d6036059001e084e664096f55c496b250096af4482a6c38285095a47ee94e07ee942074293606be93245d464e05d4642058e636296b55c096b25082a8c38284c95a084c94e0740936050c632296d55c097125b096d2504968f440968c38293295b093294f090092d82a492c289865b284a65a089864f084a64e47ec64207ec636079c62b073c62a06bc62625f435a05f434e45d234205d2336058c32a0558327050a326096355c495f250095ef4488b292c47ea64e07ea642070862a095a361095636045d034e05d0342058a32a0954660295f55c095f25088b492c284865a084864e070662a0952360295b868095b55c88b092c2846666084665a070462a49552500954f44295555c095525088ae92c070262a295755c09572504952f440952c3888ac620079031f070031e296155c096525b0961250495cf44095cc38293065b093064f88de62188aa620289635b284435a089634f084434e47e834207e8336078e31f06fe31e06ba31a0958061095006045cc04205cc036058801e055401b0724664081865808cc66408ca670094a06008c837008c637008c436408c26700942064092e65808c037008be6700722658081664c0720358081434c093a628071e36408123580938328071c658081064c08bc364092ef5808ba37008b8670094db74094986809475660945561094155c093f266493cf44093cc38093696d0922959093494d093292c0930671092c66687e062008e237108b63700796359071a358088e34d080e34c47e634207e633607c232a06fc31e062606d092a05545ca04205ca03605b802a058601e071664007ba63406f8628071464007b863406f6628090e33c050832407b663406f462802d001c092000c06f231c29183640918358491634c09163400634328053601c490ef44090ec3804e80122927868092755c49252500924f442922c660922c5a091ec38291c966091c95a87ac620280a366080a35a47e434e07e4342091a33607943350710334091433207d832907b432806fa31e078c31d06ee31c06b831a45c804e05c804209120360910031090c030058401e0550019050601806e893406b69308024634002432808fe31888b4c7008b297006e6934002232808fc31806e4634802031c08fa00c8904934090463406e262806b2624801e328001e01c08f800c06e093406b0930801c634001c32808f631808f201c88fa62808fa32808f0034060c028860c01c88f231c08f201c08f066008ff868a8fd55c88fd25048fcf4408fcc3808f896108f692c88e066587ae62a800a62008e036507ae32a000a31408f406108ee02a0909b74a907868890755c49072500906f440902c6d0900c3888de97188aa970a7e096687e095a87ac93608de67108aa67047e064e07e064207ac63606ea62a86ea62906d862806ae624062236d45c234e05c234205b4336852a32a8014328054e325862206da5c206685c205a85b4036052a01e001401c854e019079200e879200d08ec00c088a36408e755c82a292c288c65a078a62a0788358088234c86ec628052c01c08e000c28e555c08e925b08e525028e265b08e264f08de621829e620288035a088034e078431e050401a48d4c3808d492c08c835928c034d08c0341829a31448d325008d2f44829692c08d925048d0f4408d0c3828ca64f08b46218294620054c31b08d3250829892c28d125008d4f4f08d0f4428be64f08be64308b2621829c62008cc05408c405808bc34c08bcc4c08cb55c08c925a08c725508c325008c0f5a48bec3808be92c08ba35a87e231408b804908ae36028af55c08af25028b555c08b525048b2f4408b2c38a7e265a87e264e054a31908b006108ac060a5c605a85c604e078600e28d725008daf4f08d6f4448cec3808ce92c28b634f08b634308aa315828c314054800f088c670088a37008a0628089e32808883640886364078231c0894664089263408843700780328088237008883580886328088d55c088b25a078834d08843490882341828031408a7b7408a586808a3566089c96d07da959089a94d089892c089667107966590890655088e64d827e6200880370087e36607d632a077e31e4874f440874c3807246590842655081864d827c620058231e4872f440872c38085092c4870c38087092c084e6200875868087355c087125a086c96107c694d0854941084c92c0848665072264d08406490816641827a62008686280720358083e354081434c05800100864658082231c4868c38086892c086664d08626490860641085e620085c01e486cf44086cc38071e359083a355081234d086a31d085a31c8278314057e0124854c38085492c085155c084f25a484cc38084c92c071c64d083864908106418276620057c31e4848c38084892c084606108366640826634083465808246340832358082231c083e6280830364082a334083c328082e658083231c083755c4834c38083492c0830655082e6200620055082231c082a660082231c082755c4824c38082492c0820655081e620061e05508438684840f440840c38083a961083892c082c358082832a081c328061c061081431c08198684816c38081692c08126610810620061a061080c954087b868087955c087725a486ec38086e92c0858661085665b07c464d0852641084a6200844365071a34d081a349080e341080a31f82743140618061057a0122803868080355c828a6200803868080155c07fc96107ee92c07ea665828862007f862827f955c07f925007f662027fd86807fd55c07fa31d07f431c828631427ef55c07ef250828462027eb55c07eb25007e231407e2670080786827ff55c080525b07ff25007f266127f065b07f064f07ec62007e836527e635b07e634f07e431f07e03158282314077c31c050201827dd86807dd55c27dac6607dac5a079463507d8629827262027d636607d635a077a31e050001a07d155c47cd25007ccf44071663507ba629826e620057831e27cd55c07cd25027c6c5a07c6c4e071463507b8629827062047c6c3807c692c27be35807be34c27bb55c07bb25047b8f4407b8c3807b692c063462607b23140576012054600d07b000c07b031c06da63407b2628801a31c07ae00c27cf55c07d325b07cf25047caf4407cac3827c895b27c495a07c894f07c494e27c235b07c234f07c032b071032907bc32507b431d07ac315826a3140574012054400f078a67007a493407a263407a0334079ac6c079006c07883700786670079006c077c328278b55c078b250278865a078864e078662086ec31407823280780354077c32807a9b7427a786807a755c079ec6d079cc3807989712796966079695a0794936079292c078e671078c63686ea6200784370277e366077e35a077a3362771868077155c476b250076af442724966072495a024692c06e862007763250771868076f55c47692500768f440764c610742c38073a9650716936024492c070866506f863686e6620061636105b2336076b868276955c07692500762c610740c380738965272295a072294e0714936024292c070666506f663606e6620075e9340754634075c9340752634275f55c075f250475cf44075cc38048a92c06e4314075a025275555c07552504752f440752c38075092c272035a072034e0240314074c00d074c628074a0282765868076555c47632500762f44271e666071e65a07606290758628023e6200756329074e32806e2314074801906f2328274355c07432504740f440740c38271c95a071c94e023c92c06e0620073e3250736c600734c600702360273755c07372504734f440734c38272a65a072a64e070e62006de31407300190730960273b55c073b2504738f440738c380732960272865a072864e070c62006dc31407040610700060072e019072a6600728670072031c07258684722c38072292c071e661071c6200614061271755c07172504714f440714c3802ea92c06da3140712025070e960023a360070c97007023604702f440702c38023a620270955c07092504706f440706c38023862006ec3140704061070006026f955c06f925046f6f4406f6c3806f492c26f265a06f264e023631406f000d06ec67006e462806de96006e9868a6e755c86e725046e6f4406e6c3806e296106e092c06dc66506da62a00b2620061236105b032a861206185b002a0775868276d55c077325b076d2504766f440766c380746961274495b074494f073c92c072c665272665b271a65a072664f071a64e071862b071062a070a621022c62006fe36526fc35b06fc34f06fa32b06ee32a06ea31506d8314061006105ae02a052e01b04fe019052e00f26d386806d355c06b692c26ac66626a266406ac65a06a2658467c64c067c640064c63426a0964467a958067a94c064a94006d386806cec6106bec38269e658467864c06786400658636064863406ca93426986644676658067664c065664006c463426943640694358467434c067434006443282692658467264c06726400642628268e658068e64c46706400670634064062826cb55c06cb25006c892c26aa35a268c35806aa34e068c34c466e340066e334063e31c26c555c06c525006b431426cf86806cf55c06cc62906c662806b262026a8366268a36406a835a068a358466c34c066c340065433406c23282688958466a94c066a94026bf55c06bf25006b092c26a665a268465806a664e068464c466864006686342682358068234c46663400666334063632826803640680358466434c06643400634328a6629648662958466294c06629400632934a6606648660658466064c0660640065263406b4628a65e958865e94c465e940065e93406b786806b296106b092ca65c658865c64c465c640065c634065062a062e62806aa31c06ad86806a866106a662006a155c069d250866262006a155c0698955068892c069d55c0696955068692c0692628069062806932500690f44068e620069955c0697250069431d068c31c866031406892500686f44865e62006a355c069f250069af44068a65506846200682359068031f865c314267b55c067b2500662620067b55c0676955066a92c067262826732500672f440670620267755c0677250067431d066e31c0660314266b250066af44065e620066355c0660655065e620067d55c26792500678f44066c65506686200666359066431f065c31406569600642628265755c0657250064431d063e31c06523140652660265955c06592500654660063431d0650314264b55c064b2500632620064b55c0646955063a92c064262826432500642f440640620264755c0647250064431d063e31c0630314263b250063af4401f4620063355c063065501f4620064d55c26492500648f44063c65506386200636359063431f062e31406d586826d155c06d125006c096106bc92c06ba66506b862b06ae62026a435a267e35806a434e067e34c465a340065a334064e32a062c3288268c380616936060e3360614664061a658060c3280612934060a334001602806240180620664061e6340614659061c655061a64d8266620060801e06043282617868061755c2614966061495a01c492c0612620060601e060201c0604628001801c060c00c260555c060525001a4620260f868060f55c060a6202608366060835a060631e060231c054002405420182629868062955c2626967062695b062292d826492c2618666061865a061062a053e326060002a05fa31c05f801c05fd86805f666105f462025ed86805ed55c826262005ed86805eb55c05e696105d492c05d0665826062005e262805dc32825e355c05e325005e062025dd55c05dd250825e00825e786805e755c05e431d05de31c825c31405da01c25d555c05d5250825a62025d155c05d125005cec6005c631405c667005c403c05f186825e955c05ef25b05e925005d866125d665b05d664f05d262005cc36525ca35b05ca34f05c831f05c2315825631405bd55c825462005b231e05b031c05b603025b355c05b325000fe31405b000825bb55c05bf25b05bb25025b835b05b834f05b4315825031405ae01225a786805a755c80246202582366058235a05a786805a555c05a0c61058ec38058a66580226200578336059c6340596334259d55c059d250059a92c258005a058004e259755c0597250802000825a186805a155c059e3290598328801e314257e066057e05a0594028258f55c058f250801c620257c35a057c34e258b55c058b250852c3140576028058001c0583868057e661057c620257955c0579250057601d801a00805ab86825a355c05a925b05a32500592961259095b059094f058c92c0588365258635b058634f058432b852a3158014314257a05a057a04e057402a0570328054c970056c328056001c0562034056233405626280560328056893405666340564034055e01c055a328055601c0546628055201c054a9700008328254d55c054d250054a620253a05a053a04e052c00805466280536034053402805423280540010053001c053a370053633405343280530070052c3700010018056fb74256b868056b55c055cc6d0558c3805549710550936054e92c05486700544636052e62a053e36c053c0712538066053805a0532036052e01d000601c052a00845252500524f4404f631e05258680520c61050cc38050893604fc336051e93405186340512334451ef44051ec3884f201204f403404f20104518f440518c38051602a4512f440512c3804f402945212500520f44051c628051a3290514328051002804f0012450cf44050cc3804ee31e4508f440508c38050231d84e401204e6010050262804e803404fa02804e401044fcf4404fcc3804e802904fa01d04f462884f232804f202804ec96004e601c04f786804f096104ee92c04ea66504e862a001062084e432a04e402a05278684522f440522c38050e961050a92c050662a0504365050032b04fe31404f802a04e20120a198682a1155c0a1725b0a112504a04f440a04c380986961297295b097294f096692c094e665292865b092864f090a62b08ea621822a62008dc36508a8364287c35b280835a087c34f080834e47de34207de33607d432b07aa32a077831f06d631e062a31a05fe06125f205a05f204e45c004205c003605ac02a057201e052801b04e001a24d955c04d925064d2f5b44d2f4f44bef4424d2c5b04d2c4f04bec3823ac65b03ac64f4330643033063702ca6210228620219c35b019c34f4160343016033700f031f00ac31b44bcc3804c693704bc92c042265943fa63703fa62b03f062003d236503a6359239a34d039a341432e337032e32b030c31f8222314415e037015e02b010a01f00ee01344bb25004baf44432c94f032c94302c892d822092c415c64f015c64300ec62b00aa62744b925004c4f4f04b8f4443f8c4f03f8c4303eec3803d0959432a94f032a943030a937821692c415a64f015a643010863700ea62b04d955c04d725064d0f4f44b6f4424d0c4f04c2c4304b6c3804aa955242694f43f694303f693703ec92c03ce65923a864f43286430328637030862b02c6621821462001dc355219834f41583430158337010632b00e831f00a831b04ce655022662003ea92c04cf86804a696103e892c04cc32a04d386804d155c04a4661241e65b03e662003cc36504ca349030631f022431404c555c03e492c03ca665821e62024c355c04c725b04c3250241c65b041c64f03e262003c8365239835b039834f030431f02c4315022231424bb55c04bb250239695b039694f02c292d022092c00a662704b4c38041895903e092c03c66650390659238864d0388641021e620021cc3804b325003def4403c4c598218c3804bb55c04b925004b0f4404a2c55241ac4f03dcc3803c2959239294f030293702c092d021a92c01da65500a462704b325003daf4403c0c590218c3824b125004b4f4f04b0f442414c4f0414c4303d8c3803be959238694f0386943030093702be92d021692c04bf55c24b725004bcf4f04b6f4404aec3804a0955241294f041294303d692c03bc659238464f038464302fe62b02bc621021462001d835500a231b44a325004a2f44432664f0326643049e629047862802ba621820e620415634f015634300e631f00a031b049c62804a832804a6355049a31d047431c021231404989350472934021092c24a355c04a3250237e65b037e64f0496629047062802b8621020e620009e31b44992500498f44048ec38432264e032264202b4620048233100e031d009a319049c354249955c0499250048cc38237665a037664e02b262004803310098319248f55c048f250448cf44048cc38237465a037464e4320642032063600de31d0096319048a00e009400c00dc31c248355c04832504480f440480c3802b062000e431e047e008249f55c049f250649af5b449af4f4496f44249ac5b049ac4f0496c38249495b049494f44929430492937049092d048892c237c35b237235a037c34f037234e4324343431e3420324337031e33602b631502ae314219405b019404f41520430152037048602b0484027047c02500e201300da011009c00f009200d4472f440472c3844649430464937046092d045292c41503430150337043e32b043832704766490450620044ec3824732500472f44246a94f046a943045e92d044c92c0436327046e058046d250446ac38046a92c045c6200468049246555c0465250045a620023201c246155c0461250445ef44045ec38245c95a045c94e445a942045a936043c3290434325245805a045804e045600e444ef44044ec38244f250044ef44044402824532500452f446450c4f4450c43444cc38245094f0450943044c92c219034f0190343414c337014c32b244a04f044a0434448037044802b0446013044200f243f55c043f250043c620043201a243955c04392504436f440436c38043492c043232a243005a043004e042e00824792500478f446474c4f4474c434470c38247494f0474943047092c246664f04666434462637046262b04546210440620218e04f018e043414a037014a02b043a01f042c01b24ab55c04ab25064a4f5b44a4f4f44a0f4424a4c5b04a4c4f04a0c38237035b037034f431c343031c337047a31d042a31c02ac315020c314218c05b018c04f4148043014803700d8013008600f441af44041ac3804043554418c38041892c04240554416f440416c38041b55c041925a04172500414c38041095a02fa64d040c649036e64102e6629820a6200402349441092c0410620040a658440ac38040a92c440cf44040cc380408358040555c4402f440402c38036c64d02e26298208620040001e042755c042325a0421250441ec5b4412c38041e95b041c937041292c040e65a02f634d0406349036a341431a337031a32b02e031d8206314218a05b03fe0494146037014602b00d601303f955c020a62023f755c03fb25b03f7250236835b036834f03f433102aa315020631443e0c3803e092c0362659235a64d035a641820262043df25003def4481fec3803ef25063eaf4f43dcf4423eac4f03e4c4303dcc38236494f4318943031893702a892d81fc92c218664f4144643014463700d462b008462703eb55c03e8649020462023e555c03e5250020262003df25003daf440200c3823db25003daf4401fec3823dd25003e0f4f03dcf4403d8c38235894f035894302a692d01fc92c008262723ed25003f0f4f03ecf4463e6c4f43e6c4343d6c3823e694f03e694303e293703d692c235664f03566434316637031662b02a462101fa620218434f01843434142337014232b00d231f008031b43c6c3803c692c03ba06143c525003c4f4403b865503d125043c2f4403cac4303c2c3843146430314637029c62003b63554140343014033700d031f23cb55c03cb250029a31403c525003c0f44029892c03b465523c125003c0f44029692c23c325003c6f4f03c2f4403bec38235464f035464302a2621029462003b2355007e31b03b955c43b525003b4f44029292c00ce62a23b555c03b5250029092c23b755c03bb25b03b725043b2f4403b2c38235265b035264f02a0621028e62000cc31e004431b004401b23cf25003d2f4f03cef4463ccc4f43ccc4343bcc3823cc94f03cc94303c893703bc92c235034f03503434312337031232b029e315028c31403b0055218004f0180043413a037013a02b00ca013007c00f03a355c4396f440396c38028a62003423554394f440394c38036692c4392f440392c38036492c03aa0544390c38039092c0362620438ec38038e92c036062003a036403a155c438cc38038c92c0382655035e62001d605503a3868438af44038ac380380961035c92c01d4361039e0584388c38038892c035a620034e34c0394054038c058034c64c0397868039355c039125a038f255038b2500388f5a0386c38037e96102fa94d036e941035892c0354665034a65a028862001d23610340349037a31c037862803820640376628037a05803792504376c38037692c0374620033e049038155c437ef44037ec38037c31d037231c0286314033c055436ec38036e92c036c049033a03d0366054035e058034864c036555c036325a0361255035d250035af5a4358c38035892c034665a028462003383494354c38035492c0352061434c92c034c6200348314034cc4c0348c4c034ec4c434a92c034a6200346314033e62803438684340f440340c38033c961033a94d033892c01d0361033602a03ad86803a955c03a725a03a5255039d250039af5a4384c380398937038492c037066102f664d036a6414368637036862b03566200350365034435a4310337031032b02de31f028231401ce06103340494138037013802b010401f00c8013232d868032d55c027c620032d868032b55c0326961031892c0314665027a6200322628232355c032325003206202327868032755c032431d031e31c0278314231955c03192500276620231555c031525002803140331868232955c032f25b0329250031c661231a65b031a64f03166200312365231035b031034f02dc31f027e3150274314030b55c43032500302f4402f0c38027062002d43310078319230355c03032500300f4422fac5a02fac4e02eec3822e695a02e694e026e62002d2331007631942fac3802fa92c02f804922f155c02f125042eef4402eec3822e495a02e494e007431902ec02902ea00e42e6c3802e692c02e462002e204902d802402d833422d555c02d525042d2f4402d2c38026c62000c631e02d0008230955c030d25b03092506306f5b4306f4f42fef442306c5b0306c4f0304c4302fec3822fc95b22f695a02fc94f02f694e42f494302f493702f292d02e892c22e065a02e064e22de35b02de34f42dc34302dc3370272315026a314216c05b016c04f4124043012403702da02b02d602702ce02500c4013007a00f007200d22c986802c955c42c325002c2f44228a966028a95a427c94e027c94200bc62900706252262366026235a024631a02c986842c125002c0f4402bac6102a8c38029c964427a94e027a942027093601cc66100ba629024431a029a6700298c640296c6402c386822c155c02c125002bef4402b8c6102a6c3802a29650294964228895a028894e026e93601ca661006e6250268361226035a026034e0254336024231a02b493402b293422b555c02b525042b2f4402b2c3802b0325225e05a025e04e024000e22bb86802bb55c42b925002b8f442286666028665a427864e027864202b662902ae62800b831d006a319225c066025c05a023e00e22a955c02a925042a6f4402a6c38228495a028494e4276942027693600b66290068625225a35a025a34e023c31a00c2628023a01842a2f4402a2c384280642028063602a036100c031d023800e4298f440298c38029265522992500298f440296c380290655229355c02932504290f440290c38024e019229d250029cf444294c38029a937029492c028e3554120337012032b024c00f028b8684288c38028892c0286661028462001c83610280670027d868227b55c027b250027866102766200266061227155c0271250426ef44026ec38026c325023600e42692500268f44426694e026694200b4629024a31a025e31c02638684260c38026092c025c661025a62001c606102580494254f440254c380252025024e660024c970024a36c023201c02406280230034023a36001a4028023231c02306600247868224555c02452504242f440242c38023e961023c92c0238665023662a00b262001c436100fe32a00103140234061022e02a02cb86822c755c02c725042bcf4402c4c4302bcc3802ac96142aa94302aa93702a492c029e665028c664228265a028264e427e6434274642027e6370274636027262b026a62a01c2361411c343011c33700fc32b00be31f00b031d0066319000e3150264061225605a025604e025002a024800f022c00ea22155c82212506226f5b4226f4f4220f442226c5b0226c4f0220c38216a65b016a64f411a643011a637a11a35b811a34fc16a343816a33701f831f01ee31b022786802126610204620a21f55c821f2500202620221d55c021d250021d55c82192500218f440210c550200c3801be95581be65522192500218f4401fec38022155c221b250021ef4f021af440216c38020e955a20a94f820a94301fc92c01bc65581c0355a11834f811834380fa32b01ec31b221155c0211250a20f55c820f2506212f5b4212f4f420ef442212c5b0212c4f020ec38216835b016834f41163430116337a11605b811604fc168043816803701f601301ea00f220b55c020b250020803122012500200f4401fec38a1fd2508202f4f81fcf446204c4f4204c4341fcc38220494f0204943020293701fc92c216664f01666434114637011462ba11434f8114343c166337816632b01f231f01e831b01f402401f986801f696101f292c01e403401e466001ef868a1ed55c81ed25041ecf4401ecc3801ea96101e892c01ba66100f662a800a62081ba36180f632a000a31401e606101e202a0008008022955ca2152508222f4f8214f446224c4f4224c434214c38222494f02249430222937021492c020c655a20664f82066434206637020662b01fa62001b8355216434f0164343410e337010e32b00f431f000c31581b8055a10e04f810e043c164037816402b80f401f01f001301e000f800c00941db25001daf4401cc92d01c092c006462701b632a01bec3801b463621db55c01db25021d295b01d294f01ca92d01bc92c01b232a01d606401d555c41d2f4401d2c3801c862001d035501ac01e01a863401a663401a432821cd86801cd55c41cb25001caf4421c896601c895a006262501aa32a01a232821c606601c605a01c401a41bf25001bef4421bf55c01bf25021c155c01c125041bcf4401bcc38a11205b811204f01ba01b41b525001b4f4401b092c01a8620005a325005e31921b555c01b525001a662021b155c01b125021a955c01a925041a6f4401a6c38005831901a400e21b755c01b725041b2f4401b2c3801ae62021ac35b01ac34f01aa31501a23140056019006000f005c00d21dd55c01dd25041d8f4401d8c3821ce65b01ce64f01c262101b8620005431b01a001e017e655016a620018892c018692c019a0540196954017c354019264901906200178355019431d018e31c01683140188054018755c017664901666200183260017c628017a328017f8680178961017692c016e62a017432a0170954016e354016b86801686610166620019d868019955c018c661018a65b018462001803650172349016c31f0164314215d868015d55c013663d011a620015d868015b55c0156961014492c014066501186200150628015493c013433c215155c0151250014e631014c6202157868015755c013033d015231d014a31c0116314214555c0145250012e6310114620013ef60213f55c013f2500122314214155c0141250013cc6001203140134628013232801378680130961012e92c012662a012c32a012893c012633c0122c600120670011e03c011b868211955c011925001166610114620011206101100310161868215955c015f25b01592500148661214665b014664f0142620013a365213835b013834f012a331012431f011c315010e314010955c00fa620010003000fe00c20fb55c00fb25000f802500f600d210755c010b25b0107250210435b010434f010232500fc31500f431420ed86800ed55c00bc620005231a00ed86800eb55c00e6c6100d4c3800d066500ba62000e063400e4030005000c20e155c00e125000de92c00dc02620e786800e755c00e232900da32800b8314004c00e20d555c00d525000b6620004a31a00ce36020cf55c00cf25000c231420d155c00d125000c031400cc06000c603000c236000c0670000a02400bd86820bb55c00bb25000b896100b692c00b406100b201900f186820e955c00ef25b00e925000d896120d695b00d694f00d292c00ca36520c835b00c834f00c432b00be31500b0314004800e20ab86800ab55c40a725000a6f44007092c005262a2040366004035a002431400ab86840a525000a4f4400a0c610084c3800789360064661003033600a786820a555c00a5250009ec610082c38007e9650076936006e92c0046365203e35a003e34e002e3360022314009a934008e3340098934008c334005031c209b55c009b2504098f440098c38009692c009432a203c05a003c04e0020008208f55c008f250408cf44008cc38008a92c006c314004e01220a186800a155c409f250009ef44009c6290092628006a620004c31e203a066003a05a00900290088028001e008208555c00852504082f440082c38006892c004a62a203835a003834e001c314407ef44007ec380044361207955c00792504076f440076c38007492c001a008006c3280071868406ef44006ec38006a961006892c0062661002a32a005e634005a31c005831c205f55c005f2500018008205b55c005b25000586202065868006555c006292c006032a005c3282036066003605a0044011005601000160080050328004e0280053868004c961004a92c002802a4046f440046c380044361003c31c0041868403ec38003e92c003a66100386200036061203155c0031250402ef44002ec38002c92c002a31400280120020628001802800258684022f440022c38001e961001c92c001a62a0016061000a00d00ad86820a955c00a925040a2f4400a2c380086961008092c007c665007a62b007262a00666200054361004831e0042065203405a003404e003202b002602a00140080008628001000c800a00d000a6200008314000e621000c620000631e04dd55c24d525004daf4f04d4f4464c8c4f44c8c4344acc3824c894f04c894304c093704ac92c042865523fc64f03fc64343f263703f262b03d462003ae359233234f0332343430e337030e32b02cc31f022a31501de314019e055216204f0162043410c037010c02b00f201f00ae013001200f0004009178555cb74b2509764f4f974af44776ac4f576ac43574ac38376a94f176a9431764937174a92c15a6655b54664f95466435546637154662b151e62094f8359b17834f9178343d34e337934e32b903831f84de315800231414f8059334e04f134e0435178037117802b103801f0d020130a1a00f04de009000200800000ff 20 6 13 12 3 6
def s96Data : Forest := fun i => decodeNode 12 25 0x55700070d176d868bc09285db316eed92b576d868bb70155dbe1a2ee0ccb770620bb800f5db8126ed928600325bbb37a75d9a4dc006ab974cf4fba6aae5d7bd12e9aab9756636bac324dd5b10ee99e9f74f250ba87a25d3b0e2e9925800355cba10145d1007ae880ab742c4fad49285cfb0e2b524a16d0334b9b0085cd8d56e60025732054b98627db44942e598716d155cb9161c5c88d92e486ab72294fb68aae5c7a4deda2ab9714c5ab8a0085c5806ae2925b6d1250b829285c3b0e2e0a4a170a01eb8200e5c1806ee092596d155cb7a7a25bd30e2de86a96fa95ab7a4a15bd24b2de86576d155cb6931adb4c942dd52596ea634b691ad5b4d572dc24a16e0329b701ac5b4c942da86536d4f44b6b3105b58ca2da86816d2327b6800ed6a3d12b564a16c201db64324db080aad880936c2943ad57a25afa4b2b564a16aa941b559285ada4b2d558716ac92cb5802c5ab00d2d580936aa643ad59285a6313ad324a169ef44b500205a7b0e2d30c9f698031b4c315d6ac942cde4a1692c38b374a7d9ba4b2d106b168a349b444a759bc942d0926d66e04eb3792859f80dacde4a167894eb3c00959b80d2ce801f66ec38b3800759b9886b55e8964a349b344a1d92bd12cc925964a349b30021d92c942cb466365a02bb25928595804ec964a164cc38b2618f593013ac9801f64a620ad5928586313ec324a1642c38b0c4a7d8624dec3003963a92db0c92858bb0e2c5c05362e01db17008d8ba4b2c300a962a64fb0c4965891882c48c9d618637b0c310d864942c3587161a620b0c00fd6ac942b5a4a1612c38ad6928583a4b2b586575ad250b02008581a4b2c086555acc38afe00857fa4b2bf86535ac92cafb31057d813ab580b15f204dad69285763d12bb24a15e8f44af44965764942bc5e895e2620aec00fd7624b2bb4c415da01daec02656b4942ba806d5ac04cae702057380d6b59e895b6f44ae461c56dbd12b892595b6f44ae031056d807eb6de895b8620adc00f56d80d2b580995b0034ad800ed6b0022b580375aa01cad432a800c96ea92ab95a3250aa4c345668ca2b386ab59af4faa492dd64d572b2a4a1592f44aa4627552496eb12ab958b250ac4621552496eb02ab9583250ac061c552496eaf2ab957b250abc3215523d12ae4023572331aa492dd52d572ada4a154a04caa57a7d58c942ac9e89562040aa59285571882ab803d54af4faa6928555bd12a9868754c315aa67a25538c52a9803954a031aa4315800c942a798b753c95aa9e19554f8d26a7928752125ba9b7a754da4dea41e9f522f44a91aae54b2526a59887522f4fa92928549bd12a4987152292ca90310000bd3e9f64a151af44a7daae5450d26a292874fb25ba86aae543c942a1926f4faf4fa7e928541bd129f9e9f4ff250a807a253fb0e29f92594fa059001c344d455726a24b5351868a7701553bc9426a12b7351868a744a0cd461a29c2acd4e155ca7049bcd461a2996ab94cb25aa65c3453500da9aa4a14cb55ca6692d53349429998714ca92c9a8aae51b31368daab94c2c38a3661c52f8c768da4a148c941a4692852da4b29192594b264da4661c52a24b2958cb14a8634a54324d233d229452594a2641a4662a52798ae91925949a620a4632a525807e91925948e620a47195523807a91863946d55ca4261c52124b290803b46d250a374a0d1bc9428f925946e62ba37310d1ba4b28e4025472620a3700fd1b80728d8cc3350937a33496519996e6a126f45ec38a3049651799066a30d1455566a2aaae515315a8a8c5735155ca1e92d50f49428792b743c941a1e49bd0f557287e4b543f250a1f61c50fa4b2878c41350937a1a61c50da4b28686cb3518689d2621ce961a2855e8942ac389d27a250530e2848c51414c38a1019450500a682987141692ca0b19550580a28292c33a49379d261c503a4b274aab93ec9379f6aae50130e28092593ecc389fa4964ff8c727e803b3f492c9fb3104fd80727e8cab3ec62b9f64964fb98827d86b13a555c9f018e4f900727c8cab3e06209f019a4e930e27998713d001d9e84964f48c527a40253d201c9e83304f318da7986553a555c9d349bce9d5727858713c292c9d361c4ec24b27786393b001d9d84964ec988276403d3b201c9d832ace998ae74d2593aa6209d300fce98ca2748693351b749c4c344e6b0e2734c6b39ac549c44a04e5bd8271c669392c549c800e4e399b67118a938a6209c4195cd455726da4b536d2509b6aae4dec96a6f64a137a92c9b661c4dba4b26e86b136e92c9b81944db8d266d80cb35092c9b03104d801c66c0c413620709b002dcd418ae6a525935a6209a918fcd498826a862935205a9a8021800e1a22f64b717b8689a3aae4d1c9422f64b733755c9a09284cdbd3e6724a133af4499c01e4cdbd122f70d1332c4e8bd92dccad57265a4a132ac428bd92dcc8d57264a4a1322c3d8bdc344c2c96e6170d131955c98c9284c2d572619e9f30d55c9879284c3bd1261808130ac388bd92dcc0d57260a4a13029428bdaae4a7bd6a53eab92f725097c0264bdbd1253eab92e804c9787a24ba25065d126b2e892c97418eca7c94257589d2bb25096e7a24b781025b98712ba64f95d9284b598d6574c632bb2509674984b398a65752812c8934964310caec94257c0812c2c3895f018caf988257403f2ba31c94faae4ad807653e4a12a0c4e9509284aabd125580812aac38950327ca84942548c412a001f95000e4a799862f70d1281566940aae4a000f2529e89280c4294061eca001025198712809429403334a00d92504021282355940327c5ec96e4f2ab927b25093c314c5ec96e4a6ab927325092992849abd124d807926af44929627494c9424c988525325093061ec94c9424b1e8925a04092c61c494c9424a92852526208bd92dc8bd57249a4a122f2509227a249180f2489e8922f25092062148bc94247987b22f25091a7a248d810246987122f2509184a148b8d962f76e921403c9147a2485310a42987b21404091061c485250a42803921a66d90a314c85188242869f17b8689023144828ca241405120a9619024964810caa40866317b8688e992dc74e1a23f6ab91fb2508e9aae47da4c23a6ab91e0c3c8f018ec7849423d12611e86208f418e47849423c52611e201c8f0330c74993e3a64a11d89308ec310474c9423a86cb1d23298bd92dc72557239a4a11c834f8e4032c5eedd234b0d11a55668d2aae4690c763706391b801c8dc336c69199e348c9b1a46208d21b8c690d923546511aa3558d21a6c69019a34809f17b25b8beaae467c9422f9e9f1972508cc7a246598d22f8c6919234f8be928462bd12318c6918a3148be928460bd12308c691820658be31a45f813e2f808517a02b00192dc0ed5722ea4a103b8688b419a45a8ca22d402116a3558b4627c0ed59e2c6ab9162c4381d92dc55d5722ba4a11572508ac7a2455b0e20770d11443608a8ab345155722898711449668a21b24518d5628929f03a93789e61c44fa4b227929d03b55c89b4ad44da4de0764b712f55c89892844ba4da076ab9124c5a892008449806a24925b03b25b885aae447c9422164a111ac3888592844580a62164a111201e88501a443007221803710a92c81d92dc3f557220a4a10fc64f87e92843f98821f8c6d03a06087cc34435d59a1aeac30d6064878aae435c99a1ad8870d6c3886b7a44398d621c86a90e294d86b49b435a4b21acc6d0d6f5886c1b34358d3e076ab90cf25086849e4338cde076ab90baf4485d62d42eb0e21746a90c295a85d4a142ea4b2174c850ba32b81daae42718d613a4a10ae01c85849642b98d21386b509d55c8529284290ca61486b109d25084f194c278d0213864f03ac388494964258d3212466909232581d627c19310e0ca4a1088f4484461c4190d52108c9f064637832313c1918920c8c4306525083a61c41d24b20e8c4106402b83202c41b01020d804f064c38833310419809a0c863b03b868824ab341200a20baab9048c388244964120d920a46510523558241a6c12255209863b048066824027c0ed59e07aab903c95a81e1adc0f0c7607806f03a01f001c343416dd2064cab032c4f682ab3c0bb10da0b0d102125b810c34409c9420424a1022f4481061c3413d6df9eab901af447e77a240530e2028c52fcec4f800928403b0e200126f00092d80061c40080a600402300292c8003143f3d571ff1e88ff8c387fc014bf3c941fa189efd12507f861c3f40151fd929efd09377e8496bf44941fc1870fe00197f04963f40161fb4080fda0277e89283f4bd11fa8068fd20267e80143f3a585a0aab8fc863d7e449bb41313df79886fbd2507df7a23efb0e1f79258d046547dc627be8310df424a0fb0f447d861c3e81951f5989efa2c437d19283e93d11f49870fa29607d0332b416dd1f06ab8f826287ca1943e500a1f292daf8292c7c14b63e399c5f064a0f872507c43303e199c1f04cb4f82637682c343d8496dec30d0f7955c7bc9283d85571ed063af692507b73103db8c71ed24a0f6a01c7b4330bd8193dec24a0f626207b031b3413d11eb1870f586427ac315b41313de81886f412507a77a23d3b0e1e8126ef4092d7a061c3d080a5e84022f4292c7a03153416dd1e19e88f0c93479b19a3cdb1b5e19870f0cc6c7984b8bc330e1e51870f2a9607944b83c32509e1926cf0c01c790036bc318a1e34050f1a96c78b3143c580d9e192c0f1297078700e3c38045e18c42d05868753627ba9b10dd4f0d0eff25077f7a23bfb0e1d4de88eea3297759283bb30e1dd9258eec3347770083bb8c99dd8650eea96175349bba9b0e1dc9258ea6f4476b00f3b5c941db1870ed831476c00e3b58185d4c06eea63287684b63b380add4d870ebec3876000ebb03d11d85258ec201c7603303af80a9d4c026ea786875561c3aa98a1d692c2eaa92c7550143ab8185d5403aeaa011753004ba99881a0a4b6e8b55c7509283a2c941d39870e8a64f7454963a59939d14c42e8b25074661c3a30045d18c40e8a065682dba38d30e1c68c50e7e32873f01439fa5b5c69258e3496c73c338b8d18a9c68c40e3586872161c39098a1cd0650e680287344b0b90a4b1c852c0e626657213103908071cb8cc0e5a32a721aae39124b1c88638e5001c72832ab911881c88ca8e4a35972218a3910079c88650e4235471a19438f8d51c780e2e3492c71b18a38d81c1c6809ed058686ef49bb77e1a1c55870e2a92c6ef61c3868c75c35258e2062071018e386a4b1c38038e1a6616ef315b77a4b1c28c40dde92c7064963839981c186cadde32b6ef18fb779981c08ce0e023156efc3437c24b1be0638dfa6616f831037c0071be80c2df00116f818a377e1a1bc0020dea3616f018a3780d81bc80cade00086f00153778139a0b6e8dbd5676deaae36f18a1ba0650dd00286e84b6b6f24b1b792d8dca6716de32d36f18a9b78c40dbc3716de1adb6f0169b7806ed0555c6d17a2368b0e1b44cb4da20286d83103689881b58660da23296d102a3698169b44084da202b68292db41d571b3a4a0d06c4f683621b41c941b25e88d92c3868302a363a53da0d26ed0692d683928360b0e1b04052d8292c68392835e9881af4662d7a6366831a7b418cdda0c050d7231568392835930e1ac9258d646366b200eb590045ac8628d0604f68349e35780dda0e4a0d580086ac01b3418161aa4080d520276839283518c51a8de88d480086a401a3518099a0e4a0d30c3869849634c1881a60628d3004e69801b34c0131a64068d3201a69800eb41a50da1126ed08f4469361c349a4b1a10c90d22343684195b420c6da1062ad08f4468a4963451881a28628d0802b684004b4224b1a14628d0a00868400e34180a9a0802600386850ec3433ee1a19fa4a0cfac3850eaae33dbd1199aab8cf232966692833749419d9870cdd2506744963370cad9ba4a0cde0106704963378ca99b8650ccc029666928335b0e199d280cd293566749633380a19992c2a1d25066461c331a4b143a4a0cc236550eaae32f18a5978656a1db7464d49a32c8cd1964068cb2c6d64d61c326b1b19592e2c9a93664d008329a4b1934020ca26206501b83268ca193866cc9a31f50ec3430de1a192a4a0c3755c63f314b1fc941910020c8a92c64431431fc941908650c7f25064001431fa58586e4a0c7a92c61b92831cc9418e92c0c7266561b315b0da5818d92e0c6465463433231980418c8c42c3786861f92830f98a18b4650c5a96161f49630f80a18a4038c5206161f030313804587eab8c40f4462018e3119955880c40c4005562000830f988186e4a0c3831461c19530d8c754380caa1d86860ac3430bc94182aab8c1e31d60f9283091881848638c1f25061000e307998582a4a0c1a62060a1b2b050c7d82806ca1d8685f73143028ca1814050c0a9615f74962fb81917deab8bfc01c60032aaff18817f8098bef55c5f818e2fd00717e8caabf06205f80202fb80d543aab8b1155c5f47a22c455717c2ab8be2f445f061c2c455717b2ab8bdaf445ec4962c4494172e4a0bd2f445cb9282f3b0e172de88bc8c385e418eae5bd11769e88bc2c385da7a22efa4b1769870bb892c5dc3102ed007d768638b972505d800eae5bd11731e88baac385cc7a22e9a4b1731e88ba26205cc00fae63d11734c40b9a01e5cc00e2e59955621e88b8af445c861c2e2bd11719258b8a62058861c2e124b17086b2b10f445bf61c2df8c7d621e88b7a0595889282dd0c756e803eb118685aa3142da8ca16d4050b6a9615aa4962d525816c8ccab5462a5aa3102d50c516b86c8b5432a5aa00e2d580a96a8026b1155c589aae2d3bd116264a0b3e31d59f7a22d11881688638b3ef445a000e2cf9955625e88b3a6205897a22ccbd11668ca8b3235958918fac49951658cc8b2a315589aae2c6bd11634638b2265558d3102c680716380aab1a3145897a22c5002162803cb1201158801a28725b1610cc0b0a040584015a874941609870ae892c5749282bfb0e15f5258afa6605744b62bd804d5d24a0aeb2505783302ba99815d8628aea01157401528761a1598650ae29615664962b319555b4c40ada064566aae2b38c715a4038ad26555673102b380d1598052a1d55c515aae2b0d571589e88ac292c5159282afb0e154a4a0aba01d5527a22a9bd11569258aa6f445583102a9807d54de88aa862055400f2a98071548caaa2a3285504b02a79885456ab8a94f4454c4962a50165528c40a2af4454632aaa318815180b2a2b25054400fa8ae1a14dcc50a800285404b0a9ba4b14dd2c0a7a66553731529b98814dc628a7206453701529b804d456ab8a2d55c5347a228b49414b063aa58f4452f3102978c714b1e88a5a01c52c32aa8b3d114a8c40a2cf445267a229399514986b2a2c31f51632a291999148862aa2d55c51a7a228d0c71478caaa3462051a00e28d8155468628a2cf4451700428b8079458022a2a02850ec342878ca14492c2a1e00c510496287802143801e00386827092d93861a1426ab8a13250270c34281c96d40f0d0a0955c504928281b0e09c2ab898955c5007a226255713cde889e600c4fc61c2798cd93cc6b09f03404f819927980d93cc0629e6c384f401827998a53124a099b2504f061c266a53d3340189da92d4cd92827330e139803a9cc0194e6014273803539925899a32b4cd92827030e1380c409c00254e0195266c9413552589aa34e4d592826cbd11364c409b234c4d57a226b18813586689aa3264cd928269188134805499a01c4d0013a66b0e133804c99a6284c4aae2658ca53124a098b2504c861c262a53d31465698a3284c44b093861a12eaacc97555c4ba61c25d25992e8cc897831c4bc32aa5d01552e929e4e125b4b4aae25bc9412d24a096ac384b4496138496d2a2ab89632504a8928257b0e12a2ab895a0614a8928254c9412a98709520604a83329386dd12540c094b868495ab324ad5852540c894355c49593324ab0e1254c5093832849c4b6a4aa53525525892a6714957ac24b99992540aa92a64f270aae2433d112198b490c00c49061c243256921866c90c35848b1a02458cc921806c90c03148661c24380c1218c564e1b744767a223b18d12098da8ecc38476c3423bb0e11dc6508fa96147749623b81851dc0388f266047801523b80311d8c424e125b46faae239c9411bcc9e8de00c470310a378d949c1e9e8ab25046c7a222abd3d1a24a08d2f4446849622a815119aab88b925a45c92aa2e016118a4a08b8f5a45c49622e31311786b48b804945c1a1a2ac9411598708ac06145692822b818115862a8aa364270dba21fe1a10feacc87e62844f194227a5b50fd29a87e92c43f338a1f9991124c6889265543f326a1fd5711064b48823584431942218d2510468288237043f1b321f8d3c9c30d080b55c40592d202e1a10e2ab887125a438496202b0e10b463a85a92c42e326a1719610c8c9285c64142e31021700790b863885a66140532da02a4b10a8c8280b55c42692d21324b1098c4080a92c423030a118d950170d081cc3840e31420f0ca10792c281c92c40eaae20ba4b105c63883265541731020b8d61038cc082a32a40eaae207a4b103c63882265540f3102078ca103869280b8684084962040c71028cc28106204081a0a02a55101863e80a34e270c341f8496cfc30d080155c4009281f85570fe863a7f52503fb3101fd8c70fe8cc27e064f3f09281fb9880fc24a07ea3653f01a79f80c7cfc0ce07e23153f019b1385570fad8b47d66293eb1ad1f58cac9c24b67ad55c3e89281eb4940f998707ac94f3d64961f1a538f5869e7ac32b3d61a61ef8c94f5a4a07b6c383db4961ed8c74f58c507ae31c3d80061eb8c54f586544e1b743bdaae1dea4d0f40c687a03343d06369deb0e0ef58d879a9713bd4ad1dea4d8ef525877a06c3c83389de98d8ef64a078664e3c33101e18dc0ef46507823543c01ad1de8ca0ef866c77a31f2701929dde1a0db24b66d98683b7aae1dbc940db30d07692503b461c1b65570e91e887486293a49281d6b0e0eb404a75a6283a41949d24940ea187075092c3a81941d218a0e9405074a0193a44b09b6253cdb24a073ec3839f1929cfa4b0db24a072ec383979281cd30e0e692c072e96039800c9cb9994db0cc072a6703943279b661a0e3925871c31c3903309c71880e38c9c6d862b36c9281c4b0e0e2404a71262a36c4b01c3a5c0e18c426d925038061c1c00184e018707020603801b29b60d3cdb06566d925037861c1bc24b0de0c9c6f000d3781951b619c0dd862a6d986836d61c1b698a0dc92c26da92c36d4b01b79994db4c546da31436c18f13861a0c5b0d06d3250316aae1b098a4d864a06c892c3643141b0c940d886506c29613169281afa4b0c58cca62c62b316c341ac18a0d692c26b092c35831018b61a0d4c6386aa6613533101a98d38c5aab868155c3509281a05570d39e8868155c3469281a30c74d1a4a068ef443473101a38c70d18caa6812503437a21a19880d006b268031f3401a618b5570cbaab867af4432e92819b8c74cdde8867062033818e19b9954cb9e8866a62032e1ac9970c7ccbaab865e65532f3101978c50cb866862d2503289281959980ca0cc065231432819518b5570c5eab864af4431792818f8c74c7de8864062032018e18f9954c5de8863a6203171ac98b8c7cc5eab863065531818a18b8ca0c586344e155c3004ad9800060c4925a60066430f31a1879954c34c9a61a65a300aae184a568c24c4061262a300aae1808030c18c4060235a30118f180c940c0863860202a30003093861a0be86385f801c2fc33097d1880be809c4e18682e192d970e1a0bd6ab85eb2502e1aae1768c74bb64a05e06202f018e176c940bb80385da6612e1327970c940ba8c405c32502e76301738d94b8469e5c231f2e133817100f0b8862a5c203627092d96bd570b7a4a05ae34f2d701816d8c54b5e4a05b00082d800916b80a89c30d057525b2bac341695570b4a4a057555c2ca1949654940b3525859a3282ca92816580a0b292c257494f2ba928163a4b0aea4a058a3652ba1a795d0cacaeb0d057c01c2c033095f1880af809c5752502bb00e95d80a8ae803c4e03282b8dba14a8ca0adaab852a9342af31a15780d0abcc505603282b000e157b1b4a5465055ac3829500e155a5c4a5403855293629549614ac940a94c4054a67029531415198d8a546505400102a01b614a81c4a546e053a05a29519a14d0ca0a6806c52a07029800e94a8dc0a5801052a01b270c34138e1a0a498704e2f4428861c14798a0a20652510c3828b0151458ca0a218705120282884b0938b0e0a192584e2c382843151388d949c4c5050232b27118a138b0e09f403a4fa02a271c3413918a09e40504f296127249613925809d8cca4e462a27200e13980a89c80244e201a270004800d570009e9e00555c26b928135bd1000b0d04cb55c265c341330ca89986924ca94300292d930d57098a4a04c2937002aae12bbd3c95eab84b925025c7a212bbd3c9624a04b2f4425861c12ba4b000a4a042a3282541aa929b13c8564a04a2c3821592811f0d5093989e47d25024c61c11f253c8f926e47c92d23e928122b0e091401c48a92c23e01591f009c8fa4a047ec3823f00411f80948f863a42af4421632491da50c859e8847292c21602c11bc9408d125846804923432190b49408c8c5642d25022b61c115a5388ad26c45604e22b0071159884859e884429432217a2113a4b088408644202b22100991080a088801e44262021692810f188087803e42d25021761c10ba4b085c65442e04e21700410b806c85863842a655002aae0ff815484a4b43ff2501ff4ad8ffa4dc7feab841525a20a92810530e08292583fe62020832d0ffb0e081125840a3582041a48ffd57080187040001e2000248ff990c00a4b63f555c1fc9280fd0cc47e8c56004f4f1eb9280fbbd107aeab83e86491f44a18f5c9407c926e3d6f4f1ec9280f7bd107b1e883dac381ec4960f59880009e9e3b12501e87a20ec250c7624a03ca9371d87a78efc940789e883bef441e061c0efa4b07624b63b355c1dc9280ecc9407698703b20551d81ac80161a06680a83ab55c19a92d0cd495466b0d039f55c1d002c0e7c940669eb433493719ac340e1815072aab838725a1c392a8e1816071a4a0386f5a1c361c0e1a4b06680c838355c1b961c0dc8c746e40b037b2501ba4960dd18806e863837266119a4960db01246d8c8233462b19a02a0d9d5706b24b43592551ac02c0d7c9406b1eb435892c1ac3100cd24b06a40c235236519a6260d1b130698c40346c4c1a418a0d18d6866b0d0336c3819b3140cfa58466d29a33692c19b0150cd812466868600586818892d8c461a0656ab832b250188aae0c78c7463e4a032062019018e0c79984620c9e31125018c3100c449406286ca31034f188195801496c59eab830b2501676278b3b10c59e4a0300f4418061c0b3a53c59d2582f804917c4a70b3a4dc59d25a2cf25017561c0ba80a45d401c2ea92c1674960b898805c40922e264e1671a78b38cdc59c0562ce33416c0138b3c9405a18702d00081680128b38c7c00b0d022d86816492808b310c45b0d02bf25015f7a20afb0e045aab82aef441573148abc9405618702b03251583140aba58445926e22d25015361c0a9a4b04598702a036115033288b3d1051d26e28ef4414b61c0a5a4b051e4a0290c381481aa8a3999045b0d028492c1423308a11880508c9c22c67014031b88b61a04ee4a027666113b31009d98d8458c5622d25013661c09b0c944d8c5422cf441334a1099818445b0d025892c12c18e09799844b0c4025804912c02708b30e04a404a25202a116330093a5c04946d824a00f116c3408bc94045d87022e6281204b088ba4b045c6c023a66511731508b818445c63823266011801508b803845862a00555c0f0c34089a50c3c126e1e155c10b7a7885d570439e88216f4410c61c085a4b03c189e20f25010861c08399543c24a0208031104315878250c3f926e1fcf440ff61c07fa4b03f8c401e18680f94b087c80903e92581f20130f0c34078b0e03c52c21e292c0f103087899803c80541e200f0f018a00149403424a01dac380d0032075d5703a18701d03550e83278685570389e881c495a0e202d0710068388c421a12500dd92806fb0e03740361ba6200d0928068c9403698701a32500d83100688d3c34462a1a32500d261c06900383486281a201e0d002a80161a02c80a819b55c0b24aa0658c7431cc921906200c818e06399842c8cb61640540c4aae06198802ca4c01823650b2c3405d18a02f465017a9610ba49605d0ca82e86921649540b71aa05b8c7c2cb0d01666610b33100598c502c808600586808792d843e1a02b6ab815b250087aae052a4f02a863a14b2500a6318853188029863814a661087327843c940288c4010f25009e92804fb1802786ca10e34f087c3404b18a026465013296109649604b0ca825866210e93c09319e0498c7c21d8c012267008f01e0478c5421f0d011125008833084418802200c211003108818a04380ac00a4b60f555c08492803d0d3c1e864a0f403007f00603f8c541ea4a00f602507b00683d8c501e803e00586805892d82c61a01d6ab80eb250058aae03680c01c86520db25006e49603700981b86500da9610584a782c49401a92580b125006692803381801986ca0b034f0580180318cac1606c00c267006018a82c61a01664a00b296105949602c81841640320b231405800980161a002b0d00ab25000ac34029494014987001555c0447a202218a41124a0094c3804a4960250ca8128c50088029044928022b0e011525808a0280444b0805494010587008292c00a61c01f9994028c5601525003a61c01d24b00e8c5401586803461c01a0ca00d92c206892c03431000555700ad25805632a02b9280178ca00ae4a005862002c0080158d8402b0d004a328027014013a58409525804a31e00a61c0110d840880ca01586801b49600d8c70078cc203662001b03080d813802805601525001461c00a24b005062802801201401500561a002d8700166280104b0805a4b002cc5401602800c030805802002801e00400c008310801988000cc4000831400418f00180240080100020ff000 i
def s96Tags := dagTraceTags s96Mask 190 (dagTagBases s96StockWords 0xffffffffffffffffffffffffffffe0000000000000000003ffffffffffff80000000000000007ffffffff0000000000fffc000000001ffffff8000000001fff000003fff0000003c00ffff000007ff0001ffffc00007003ff000fc03fff0000c03c003fe001803f807c000ff000300e03c03080f003f820008fc0f07f01c0e1e00fe0383e06f0370cfcf3e23fcf18800238e03903e0e0607e206098f7e0001b2b0ca074f03e1d0c0492789a081278710041fc7e1f80f05353c17f803f0ff 0x7ffdd6f9bff3faf97ffffe5ef7ffe033000088044288a003ab8fff7fdfff00000000204010305aabffffe0000010000151c000000001fdfdff9050842020955000003ffe0421003c20effd001045fd00016fffc01047102ff000bc03bfe0000c5040037c28a803f2224000ffa08300403e410a01003f420008a4090030140a0000060000007f03fafd8fec259c61000000020080020202006f265b9f1c000000004001698a7100ca000220e49002035400000003880fc00026013800102a 190) 13 s96Data
def s96States := dagTrace s96Mask s96StockWords 13 s96Data
def s96Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s96Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s96Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s96Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s96Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 6, 5, 7] 0 i.val)
def s96Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 6, 5, 7] 0 i.val)
def s96Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 6, 3, 4, 7] 0 i.val)
def s96Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 6, 3, 4, 7] 0 i.val)
def s96Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 5, 3, 4, 7] 0 i.val)
def s96Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 6, 4, 3, 7] 0 i.val)
def s96Move5Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 6, 4, 3, 7] 0 i.val)
def s96Move5Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 5, 3, 4, 7] 0 i.val)
def s96Move6Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 5, 4, 3, 7] 0 i.val)
def s96Move6Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 6, 5, 4, 3, 7] 0 i.val)
def s96MoveCert : List (DagMoveRecord 256) := [((moveSchedule moveStages [13]), s96Move0Map, s96Move0Inverse), ((moveSchedule moveStages [10]), s96Move1Map, s96Move1Inverse), ((moveSchedule moveStages [10, 13]), s96Move2Map, s96Move2Inverse), ((moveSchedule moveStages [3, 6, 7]), s96Move3Map, s96Move3Inverse), ((moveSchedule moveStages [3, 12, 11, 13]), s96Move4Map, s96Move4Inverse), ((moveSchedule moveStages [3, 6, 7, 13]), s96Move5Map, s96Move5Inverse), ((moveSchedule moveStages [3, 12, 11]), s96Move6Map, s96Move6Inverse)]
def s96Moves := dagMoves s96MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Autos : DagMovesOK s96Mask s96Goal 256 s96Moves := dagMovesOfCheck (by decide +kernel)
def s96Check := dagCheckNode s96Mask s96Goal s96Chart (dagKnownCloses s96Goal s96Cuts) 3011 s96States s96Moves s96Links s96Sample s96Tags
def s96RootAt (token : Nat) : Bool :=
  let s := rootState s96StockWords 13 token
  !dagAllowedRoot s96Witnesses s.2.1 || dagLocal s96Mask s96Goal s96Chart (dagKnownCloses s96Goal s96Cuts) s ||
  dagRef 3011 s96States s96Moves s96Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96RootBlock0 : treeBlock 0 64 s96RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96RootBlock64 : treeBlock 64 64 s96RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96RootBlock128 : treeBlock 128 64 s96RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96RootBlock192 : treeBlock 192 64 s96RootAt = true := by decide +kernel
theorem s96RootVerified : treeBlock 0 256 s96RootAt = true := (@treeBlock_merge 0 128 128 s96RootAt (@treeBlock_merge 0 64 64 s96RootAt s96RootBlock0 s96RootBlock64) (@treeBlock_merge 128 64 64 s96RootAt s96RootBlock128 s96RootBlock192))
theorem s96Roots : dagCheckRoots s96Mask s96Goal s96Chart (dagKnownCloses s96Goal s96Cuts) s96Witnesses (dagRef 3011 s96States s96Moves s96Links 0) s96StockWords 13 = true := s96RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block0 : treeBlock 0 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block16 : treeBlock 16 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block32 : treeBlock 32 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block48 : treeBlock 48 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block64 : treeBlock 64 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block80 : treeBlock 80 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block96 : treeBlock 96 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block112 : treeBlock 112 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block128 : treeBlock 128 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block144 : treeBlock 144 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block160 : treeBlock 160 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block176 : treeBlock 176 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block192 : treeBlock 192 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block208 : treeBlock 208 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block224 : treeBlock 224 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block240 : treeBlock 240 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block256 : treeBlock 256 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block272 : treeBlock 272 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block288 : treeBlock 288 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block304 : treeBlock 304 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block320 : treeBlock 320 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block336 : treeBlock 336 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block352 : treeBlock 352 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block368 : treeBlock 368 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block384 : treeBlock 384 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block400 : treeBlock 400 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block416 : treeBlock 416 2 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block418 : treeBlock 418 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block434 : treeBlock 434 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block450 : treeBlock 450 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block466 : treeBlock 466 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block482 : treeBlock 482 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block498 : treeBlock 498 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block514 : treeBlock 514 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block530 : treeBlock 530 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block546 : treeBlock 546 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block562 : treeBlock 562 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block578 : treeBlock 578 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block594 : treeBlock 594 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block610 : treeBlock 610 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block626 : treeBlock 626 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block642 : treeBlock 642 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block658 : treeBlock 658 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block674 : treeBlock 674 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block690 : treeBlock 690 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block706 : treeBlock 706 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block722 : treeBlock 722 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block738 : treeBlock 738 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block754 : treeBlock 754 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block770 : treeBlock 770 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block786 : treeBlock 786 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block802 : treeBlock 802 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block818 : treeBlock 818 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block834 : treeBlock 834 12 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block846 : treeBlock 846 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block862 : treeBlock 862 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block878 : treeBlock 878 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block894 : treeBlock 894 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block910 : treeBlock 910 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block926 : treeBlock 926 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block942 : treeBlock 942 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block958 : treeBlock 958 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block974 : treeBlock 974 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block990 : treeBlock 990 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1006 : treeBlock 1006 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1022 : treeBlock 1022 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1038 : treeBlock 1038 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1054 : treeBlock 1054 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1070 : treeBlock 1070 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1086 : treeBlock 1086 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1102 : treeBlock 1102 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1118 : treeBlock 1118 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1134 : treeBlock 1134 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1150 : treeBlock 1150 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1166 : treeBlock 1166 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1182 : treeBlock 1182 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1198 : treeBlock 1198 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1214 : treeBlock 1214 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1230 : treeBlock 1230 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1246 : treeBlock 1246 15 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1261 : treeBlock 1261 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1277 : treeBlock 1277 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1293 : treeBlock 1293 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1309 : treeBlock 1309 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1325 : treeBlock 1325 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1341 : treeBlock 1341 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1357 : treeBlock 1357 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1373 : treeBlock 1373 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1389 : treeBlock 1389 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1405 : treeBlock 1405 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1421 : treeBlock 1421 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1437 : treeBlock 1437 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1453 : treeBlock 1453 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1469 : treeBlock 1469 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1485 : treeBlock 1485 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1501 : treeBlock 1501 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1517 : treeBlock 1517 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1533 : treeBlock 1533 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1549 : treeBlock 1549 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1565 : treeBlock 1565 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1581 : treeBlock 1581 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1597 : treeBlock 1597 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1613 : treeBlock 1613 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1629 : treeBlock 1629 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1645 : treeBlock 1645 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1661 : treeBlock 1661 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1677 : treeBlock 1677 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1693 : treeBlock 1693 14 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1707 : treeBlock 1707 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1723 : treeBlock 1723 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1739 : treeBlock 1739 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1755 : treeBlock 1755 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1771 : treeBlock 1771 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1787 : treeBlock 1787 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1803 : treeBlock 1803 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1819 : treeBlock 1819 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1835 : treeBlock 1835 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1851 : treeBlock 1851 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1867 : treeBlock 1867 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1883 : treeBlock 1883 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1899 : treeBlock 1899 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1915 : treeBlock 1915 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1931 : treeBlock 1931 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1947 : treeBlock 1947 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1963 : treeBlock 1963 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1979 : treeBlock 1979 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block1995 : treeBlock 1995 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2011 : treeBlock 2011 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2027 : treeBlock 2027 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2043 : treeBlock 2043 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2059 : treeBlock 2059 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2075 : treeBlock 2075 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2091 : treeBlock 2091 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2107 : treeBlock 2107 8 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2115 : treeBlock 2115 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2131 : treeBlock 2131 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2147 : treeBlock 2147 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2163 : treeBlock 2163 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2179 : treeBlock 2179 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2195 : treeBlock 2195 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2211 : treeBlock 2211 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2227 : treeBlock 2227 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2243 : treeBlock 2243 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2259 : treeBlock 2259 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2275 : treeBlock 2275 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2291 : treeBlock 2291 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2307 : treeBlock 2307 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2323 : treeBlock 2323 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2339 : treeBlock 2339 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2355 : treeBlock 2355 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2371 : treeBlock 2371 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2387 : treeBlock 2387 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2403 : treeBlock 2403 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2419 : treeBlock 2419 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2435 : treeBlock 2435 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2451 : treeBlock 2451 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2467 : treeBlock 2467 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2483 : treeBlock 2483 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2499 : treeBlock 2499 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2515 : treeBlock 2515 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2531 : treeBlock 2531 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2547 : treeBlock 2547 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2563 : treeBlock 2563 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2579 : treeBlock 2579 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2595 : treeBlock 2595 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2611 : treeBlock 2611 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2627 : treeBlock 2627 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2643 : treeBlock 2643 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2659 : treeBlock 2659 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2675 : treeBlock 2675 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2691 : treeBlock 2691 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2707 : treeBlock 2707 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2723 : treeBlock 2723 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2739 : treeBlock 2739 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2755 : treeBlock 2755 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2771 : treeBlock 2771 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2787 : treeBlock 2787 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2803 : treeBlock 2803 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2819 : treeBlock 2819 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2835 : treeBlock 2835 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2851 : treeBlock 2851 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2867 : treeBlock 2867 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2883 : treeBlock 2883 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2899 : treeBlock 2899 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2915 : treeBlock 2915 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2931 : treeBlock 2931 8 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2939 : treeBlock 2939 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2955 : treeBlock 2955 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2971 : treeBlock 2971 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block2987 : treeBlock 2987 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block3003 : treeBlock 3003 8 s96Check = true := by decide +kernel
theorem s96Verified : treeBlock 0 3011 s96Check = true := (@treeBlock_merge 0 1501 1510 s96Check (@treeBlock_merge 0 738 763 s96Check (@treeBlock_merge 0 368 370 s96Check (@treeBlock_merge 0 176 192 s96Check (@treeBlock_merge 0 80 96 s96Check (@treeBlock_merge 0 32 48 s96Check (@treeBlock_merge 0 16 16 s96Check s96Block0 s96Block16) (@treeBlock_merge 32 16 32 s96Check s96Block32 (@treeBlock_merge 48 16 16 s96Check s96Block48 s96Block64))) (@treeBlock_merge 80 48 48 s96Check (@treeBlock_merge 80 16 32 s96Check s96Block80 (@treeBlock_merge 96 16 16 s96Check s96Block96 s96Block112)) (@treeBlock_merge 128 16 32 s96Check s96Block128 (@treeBlock_merge 144 16 16 s96Check s96Block144 s96Block160)))) (@treeBlock_merge 176 96 96 s96Check (@treeBlock_merge 176 48 48 s96Check (@treeBlock_merge 176 16 32 s96Check s96Block176 (@treeBlock_merge 192 16 16 s96Check s96Block192 s96Block208)) (@treeBlock_merge 224 16 32 s96Check s96Block224 (@treeBlock_merge 240 16 16 s96Check s96Block240 s96Block256))) (@treeBlock_merge 272 48 48 s96Check (@treeBlock_merge 272 16 32 s96Check s96Block272 (@treeBlock_merge 288 16 16 s96Check s96Block288 s96Block304)) (@treeBlock_merge 320 16 32 s96Check s96Block320 (@treeBlock_merge 336 16 16 s96Check s96Block336 s96Block352))))) (@treeBlock_merge 368 178 192 s96Check (@treeBlock_merge 368 82 96 s96Check (@treeBlock_merge 368 48 34 s96Check (@treeBlock_merge 368 16 32 s96Check s96Block368 (@treeBlock_merge 384 16 16 s96Check s96Block384 s96Block400)) (@treeBlock_merge 416 2 32 s96Check s96Block416 (@treeBlock_merge 418 16 16 s96Check s96Block418 s96Block434))) (@treeBlock_merge 450 48 48 s96Check (@treeBlock_merge 450 16 32 s96Check s96Block450 (@treeBlock_merge 466 16 16 s96Check s96Block466 s96Block482)) (@treeBlock_merge 498 16 32 s96Check s96Block498 (@treeBlock_merge 514 16 16 s96Check s96Block514 s96Block530)))) (@treeBlock_merge 546 96 96 s96Check (@treeBlock_merge 546 48 48 s96Check (@treeBlock_merge 546 16 32 s96Check s96Block546 (@treeBlock_merge 562 16 16 s96Check s96Block562 s96Block578)) (@treeBlock_merge 594 16 32 s96Check s96Block594 (@treeBlock_merge 610 16 16 s96Check s96Block610 s96Block626))) (@treeBlock_merge 642 48 48 s96Check (@treeBlock_merge 642 16 32 s96Check s96Block642 (@treeBlock_merge 658 16 16 s96Check s96Block658 s96Block674)) (@treeBlock_merge 690 16 32 s96Check s96Block690 (@treeBlock_merge 706 16 16 s96Check s96Block706 s96Block722)))))) (@treeBlock_merge 738 380 383 s96Check (@treeBlock_merge 738 188 192 s96Check (@treeBlock_merge 738 96 92 s96Check (@treeBlock_merge 738 48 48 s96Check (@treeBlock_merge 738 16 32 s96Check s96Block738 (@treeBlock_merge 754 16 16 s96Check s96Block754 s96Block770)) (@treeBlock_merge 786 16 32 s96Check s96Block786 (@treeBlock_merge 802 16 16 s96Check s96Block802 s96Block818))) (@treeBlock_merge 834 44 48 s96Check (@treeBlock_merge 834 12 32 s96Check s96Block834 (@treeBlock_merge 846 16 16 s96Check s96Block846 s96Block862)) (@treeBlock_merge 878 16 32 s96Check s96Block878 (@treeBlock_merge 894 16 16 s96Check s96Block894 s96Block910)))) (@treeBlock_merge 926 96 96 s96Check (@treeBlock_merge 926 48 48 s96Check (@treeBlock_merge 926 16 32 s96Check s96Block926 (@treeBlock_merge 942 16 16 s96Check s96Block942 s96Block958)) (@treeBlock_merge 974 16 32 s96Check s96Block974 (@treeBlock_merge 990 16 16 s96Check s96Block990 s96Block1006))) (@treeBlock_merge 1022 48 48 s96Check (@treeBlock_merge 1022 16 32 s96Check s96Block1022 (@treeBlock_merge 1038 16 16 s96Check s96Block1038 s96Block1054)) (@treeBlock_merge 1070 16 32 s96Check s96Block1070 (@treeBlock_merge 1086 16 16 s96Check s96Block1086 s96Block1102))))) (@treeBlock_merge 1118 191 192 s96Check (@treeBlock_merge 1118 96 95 s96Check (@treeBlock_merge 1118 48 48 s96Check (@treeBlock_merge 1118 16 32 s96Check s96Block1118 (@treeBlock_merge 1134 16 16 s96Check s96Block1134 s96Block1150)) (@treeBlock_merge 1166 16 32 s96Check s96Block1166 (@treeBlock_merge 1182 16 16 s96Check s96Block1182 s96Block1198))) (@treeBlock_merge 1214 47 48 s96Check (@treeBlock_merge 1214 16 31 s96Check s96Block1214 (@treeBlock_merge 1230 16 15 s96Check s96Block1230 s96Block1246)) (@treeBlock_merge 1261 16 32 s96Check s96Block1261 (@treeBlock_merge 1277 16 16 s96Check s96Block1277 s96Block1293)))) (@treeBlock_merge 1309 96 96 s96Check (@treeBlock_merge 1309 48 48 s96Check (@treeBlock_merge 1309 16 32 s96Check s96Block1309 (@treeBlock_merge 1325 16 16 s96Check s96Block1325 s96Block1341)) (@treeBlock_merge 1357 16 32 s96Check s96Block1357 (@treeBlock_merge 1373 16 16 s96Check s96Block1373 s96Block1389))) (@treeBlock_merge 1405 48 48 s96Check (@treeBlock_merge 1405 16 32 s96Check s96Block1405 (@treeBlock_merge 1421 16 16 s96Check s96Block1421 s96Block1437)) (@treeBlock_merge 1453 16 32 s96Check s96Block1453 (@treeBlock_merge 1469 16 16 s96Check s96Block1469 s96Block1485))))))) (@treeBlock_merge 1501 758 752 s96Check (@treeBlock_merge 1501 382 376 s96Check (@treeBlock_merge 1501 192 190 s96Check (@treeBlock_merge 1501 96 96 s96Check (@treeBlock_merge 1501 48 48 s96Check (@treeBlock_merge 1501 16 32 s96Check s96Block1501 (@treeBlock_merge 1517 16 16 s96Check s96Block1517 s96Block1533)) (@treeBlock_merge 1549 16 32 s96Check s96Block1549 (@treeBlock_merge 1565 16 16 s96Check s96Block1565 s96Block1581))) (@treeBlock_merge 1597 48 48 s96Check (@treeBlock_merge 1597 16 32 s96Check s96Block1597 (@treeBlock_merge 1613 16 16 s96Check s96Block1613 s96Block1629)) (@treeBlock_merge 1645 16 32 s96Check s96Block1645 (@treeBlock_merge 1661 16 16 s96Check s96Block1661 s96Block1677)))) (@treeBlock_merge 1693 94 96 s96Check (@treeBlock_merge 1693 46 48 s96Check (@treeBlock_merge 1693 14 32 s96Check s96Block1693 (@treeBlock_merge 1707 16 16 s96Check s96Block1707 s96Block1723)) (@treeBlock_merge 1739 16 32 s96Check s96Block1739 (@treeBlock_merge 1755 16 16 s96Check s96Block1755 s96Block1771))) (@treeBlock_merge 1787 48 48 s96Check (@treeBlock_merge 1787 16 32 s96Check s96Block1787 (@treeBlock_merge 1803 16 16 s96Check s96Block1803 s96Block1819)) (@treeBlock_merge 1835 16 32 s96Check s96Block1835 (@treeBlock_merge 1851 16 16 s96Check s96Block1851 s96Block1867))))) (@treeBlock_merge 1883 192 184 s96Check (@treeBlock_merge 1883 96 96 s96Check (@treeBlock_merge 1883 48 48 s96Check (@treeBlock_merge 1883 16 32 s96Check s96Block1883 (@treeBlock_merge 1899 16 16 s96Check s96Block1899 s96Block1915)) (@treeBlock_merge 1931 16 32 s96Check s96Block1931 (@treeBlock_merge 1947 16 16 s96Check s96Block1947 s96Block1963))) (@treeBlock_merge 1979 48 48 s96Check (@treeBlock_merge 1979 16 32 s96Check s96Block1979 (@treeBlock_merge 1995 16 16 s96Check s96Block1995 s96Block2011)) (@treeBlock_merge 2027 16 32 s96Check s96Block2027 (@treeBlock_merge 2043 16 16 s96Check s96Block2043 s96Block2059)))) (@treeBlock_merge 2075 88 96 s96Check (@treeBlock_merge 2075 40 48 s96Check (@treeBlock_merge 2075 16 24 s96Check s96Block2075 (@treeBlock_merge 2091 16 8 s96Check s96Block2091 s96Block2107)) (@treeBlock_merge 2115 16 32 s96Check s96Block2115 (@treeBlock_merge 2131 16 16 s96Check s96Block2131 s96Block2147))) (@treeBlock_merge 2163 48 48 s96Check (@treeBlock_merge 2163 16 32 s96Check s96Block2163 (@treeBlock_merge 2179 16 16 s96Check s96Block2179 s96Block2195)) (@treeBlock_merge 2211 16 32 s96Check s96Block2211 (@treeBlock_merge 2227 16 16 s96Check s96Block2227 s96Block2243)))))) (@treeBlock_merge 2259 384 368 s96Check (@treeBlock_merge 2259 192 192 s96Check (@treeBlock_merge 2259 96 96 s96Check (@treeBlock_merge 2259 48 48 s96Check (@treeBlock_merge 2259 16 32 s96Check s96Block2259 (@treeBlock_merge 2275 16 16 s96Check s96Block2275 s96Block2291)) (@treeBlock_merge 2307 16 32 s96Check s96Block2307 (@treeBlock_merge 2323 16 16 s96Check s96Block2323 s96Block2339))) (@treeBlock_merge 2355 48 48 s96Check (@treeBlock_merge 2355 16 32 s96Check s96Block2355 (@treeBlock_merge 2371 16 16 s96Check s96Block2371 s96Block2387)) (@treeBlock_merge 2403 16 32 s96Check s96Block2403 (@treeBlock_merge 2419 16 16 s96Check s96Block2419 s96Block2435)))) (@treeBlock_merge 2451 96 96 s96Check (@treeBlock_merge 2451 48 48 s96Check (@treeBlock_merge 2451 16 32 s96Check s96Block2451 (@treeBlock_merge 2467 16 16 s96Check s96Block2467 s96Block2483)) (@treeBlock_merge 2499 16 32 s96Check s96Block2499 (@treeBlock_merge 2515 16 16 s96Check s96Block2515 s96Block2531))) (@treeBlock_merge 2547 48 48 s96Check (@treeBlock_merge 2547 16 32 s96Check s96Block2547 (@treeBlock_merge 2563 16 16 s96Check s96Block2563 s96Block2579)) (@treeBlock_merge 2595 16 32 s96Check s96Block2595 (@treeBlock_merge 2611 16 16 s96Check s96Block2611 s96Block2627))))) (@treeBlock_merge 2643 192 176 s96Check (@treeBlock_merge 2643 96 96 s96Check (@treeBlock_merge 2643 48 48 s96Check (@treeBlock_merge 2643 16 32 s96Check s96Block2643 (@treeBlock_merge 2659 16 16 s96Check s96Block2659 s96Block2675)) (@treeBlock_merge 2691 16 32 s96Check s96Block2691 (@treeBlock_merge 2707 16 16 s96Check s96Block2707 s96Block2723))) (@treeBlock_merge 2739 48 48 s96Check (@treeBlock_merge 2739 16 32 s96Check s96Block2739 (@treeBlock_merge 2755 16 16 s96Check s96Block2755 s96Block2771)) (@treeBlock_merge 2787 16 32 s96Check s96Block2787 (@treeBlock_merge 2803 16 16 s96Check s96Block2803 s96Block2819)))) (@treeBlock_merge 2835 96 80 s96Check (@treeBlock_merge 2835 48 48 s96Check (@treeBlock_merge 2835 16 32 s96Check s96Block2835 (@treeBlock_merge 2851 16 16 s96Check s96Block2851 s96Block2867)) (@treeBlock_merge 2883 16 32 s96Check s96Block2883 (@treeBlock_merge 2899 16 16 s96Check s96Block2899 s96Block2915))) (@treeBlock_merge 2931 40 40 s96Check (@treeBlock_merge 2931 8 32 s96Check s96Block2931 (@treeBlock_merge 2939 16 16 s96Check s96Block2939 s96Block2955)) (@treeBlock_merge 2971 16 24 s96Check s96Block2971 (@treeBlock_merge 2987 16 8 s96Check s96Block2987 s96Block3003))))))))
theorem s96Blocks : treeBlock 0 3011 s96Check = true := s96Verified
theorem s96Known : Known s96Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s5Stock) s4Stock) s23Stock) s22Stock) s21Stock) s20Stock) s19Stock) s18Stock) s17Stock) s14Stock) s54Stock) s53Stock) s41Stock) s40Stock) s39Stock) s38Stock) s83Stock) s64Stock) s63Stock) s62Stock) s61Stock) s60Stock) s59Stock) s52Stock) s51Stock) s50Stock) s49Stock) s48Stock) s47Stock) s46Stock) s45Stock) s43Stock) s82Stock) s81Stock) s79Stock) s78Stock) s76Stock) s75Stock) s74Stock) s72Stock) s71Stock) s70Stock) s68Stock) s67Stock) s29Stock) s24Stock) s94Stock) s93Stock) s92Stock) s91Stock) s90Stock) s89Stock) s73Stock) s65Stock) s57Stock) s56Stock) s77Stock) s58Stock) s95Stock) s88Stock) s87Stock) s86Stock) s85Stock) s84Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Stock : Lower s96Mask s96StockWords s96Goal 14 := by
  apply lowerDag _ _ _ _ s96Autos _ _ _ s96Known _ s96Roots s96Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s96StockWords; decide +kernel
  · decide +kernel
  · simp only [s96Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end PEqualNP.Outside.L_meta_8447

open PEqualNP.Outside.L_meta_8447 in
theorem PEqualNP.Outside.L_meta_8447 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 4) || (x 5 && x 6)) t → 14 ≤ t := by
  intro t h
  let raw : List (BitVec 256) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
  let goal : BitVec 256 := 0xfffffffffffefefcfffefefcfffafaf8ffffffffffeeeeecffeeeeecffeaeae8
  have root : Lower (fullMask 256) (raw.map BitVec.toNat) goal.toNat 14 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s96Stock
  exact hcsLower (n := 8) raw goal 14 _ (by decide +kernel) (by decide +kernel) root t h

