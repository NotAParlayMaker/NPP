import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12226

-- The live-wire evaluator and exclusion-certificate checker are adapted from L-meta-8467 under Apache-2.0.
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


def pinRelabel {rows : Nat} (sourceIndex : Fin rows → Nat) (word : Word) : Word :=
  pointWord fun i => word.testBit (sourceIndex i)

theorem lowerPinMap {rows : Nat} (sourceIndex : Fin rows → Nat)
    {mask : Word} {bank roots : List Word} {src dst minimum : Word}
    (indices : ∀ i, mask.testBit (sourceIndex i) = true)
    (old : Lower (fullMask rows) bank src minimum)
    (goal : pinRelabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord (fullMask rows) bank (pinRelabel sourceIndex w)) :
    Lower mask roots dst minimum := by
  have pzero : pinRelabel sourceIndex 0 = 0 := by
    simpa [pinRelabel] using (pointZero (rows := rows))
  have pones : pinRelabel sourceIndex mask = fullMask rows := by
    have all : (fun i => mask.testBit (sourceIndex i)) = fun _ => true := funext indices
    have bits : encodePoint (fun _ : Fin rows => true) = BitVec.allOnes rows := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [encodeBit _ ⟨i, hi⟩]
      simp [hi]
    simp [pinRelabel, all, pointWord, bits, fullMask]
  have pnot (a : Word) : pinRelabel sourceIndex (mask ^^^ a) =
      fullMask rows ^^^ pinRelabel sourceIndex a := by
    have eq : (fun i => (mask ^^^ a).testBit (sourceIndex i)) =
        fun i => !a.testBit (sourceIndex i) := by
      funext i
      simp [Nat.testBit_xor, indices i]
    simp only [pinRelabel, eq, pointWord, encodeNot, notNat]
  have pand (a b : Word) : pinRelabel sourceIndex (a &&& b) =
      pinRelabel sourceIndex a &&& pinRelabel sourceIndex b := by
    simp only [pinRelabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]
  have por (a b : Word) : pinRelabel sourceIndex (a ||| b) =
      pinRelabel sourceIndex a ||| pinRelabel sourceIndex b := by
    simp only [pinRelabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]
  exact lowerMap (pinRelabel sourceIndex) pzero pones pnot pand por supply (goal.symm ▸ old)

def pinIx (i : ℕ) (b : Bool) {rows : ℕ} (row : Fin rows) : Nat :=
  row.val % 2 ^ i + (if b then 2 ^ i else 0) + 2 ^ (i + 1) * (row.val / 2 ^ i)

def M3Mask : Word := 0xff
def M3Goal : Word := 0xe8
def M3Stock : List Word := [0xaa, 0xcc, 0xf0]
def M3Sample : DagSample := (0x10180205020180203020140403, 6)
def M3Witnesses := unpackWitnesses M3Stock [1538, 263681, 526849]
def M3Cuts : List Bound := []
theorem M3Known : Known M3Cuts := by
  unfold M3Cuts
  exact (show Known [] from by intro b hb; simp at hb)
def M3MoveCert : List (DagMoveRecord 8) := [
  ([], fun i => Fin.ofNat 8 (permuteAxes [0, 1, 2] 0 i.val),
    fun i => Fin.ofNat 8 (permuteAxes [0, 1, 2] 0 i.val)),
  ([([(0xc3, 0), (0xc, 2)], [(0x30, 2)])], fun i => Fin.ofNat 8 (permuteAxes [0, 2, 1] 0 i.val),
    fun i => Fin.ofNat 8 (permuteAxes [0, 2, 1] 0 i.val)),
  ([([(0x99, 0), (0x22, 1)], [(0x44, 1)])], fun i => Fin.ofNat 8 (permuteAxes [1, 0, 2] 0 i.val),
    fun i => Fin.ofNat 8 (permuteAxes [1, 0, 2] 0 i.val)),
  ([([(0x99, 0), (0x22, 1)], [(0x44, 1)]), ([(0xa5, 0), (0xa, 3)], [(0x50, 3)])], fun i => Fin.ofNat 8 (permuteAxes [2, 0, 1] 0 i.val),
    fun i => Fin.ofNat 8 (permuteAxes [1, 2, 0] 0 i.val)),
  ([([(0xa5, 0), (0xa, 3)], [(0x50, 3)]), ([(0x99, 0), (0x22, 1)], [(0x44, 1)])], fun i => Fin.ofNat 8 (permuteAxes [1, 2, 0] 0 i.val),
    fun i => Fin.ofNat 8 (permuteAxes [2, 0, 1] 0 i.val)),
  ([([(0xa5, 0), (0xa, 3)], [(0x50, 3)])], fun i => Fin.ofNat 8 (permuteAxes [2, 1, 0] 0 i.val),
    fun i => Fin.ofNat 8 (permuteAxes [2, 1, 0] 0 i.val)),
]
def M3Moves := dagMoves M3MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem M3Autos : DagMovesOK M3Mask M3Goal 8 M3Moves := dagMovesOfCheck (by decide +kernel)
def M3Links : DagLinks := dagLookupLinks 0x9 0x7
  2 1 3 1 1 2
def M3Data : Forest := fun i => decodeNode 1 4 0xe i
def M3States := dagTrace M3Mask M3Stock 3 M3Data
def M3Tags := dagTraceTags M3Mask 6
  (dagTagBases M3Stock 0x3ab57 0xa854 6) 3 M3Data
def M3Check := dagCheckNode M3Mask M3Goal none (dagKnownCloses M3Goal M3Cuts)
  1 M3States M3Moves M3Links M3Sample M3Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem M3Roots : dagCheckRoots M3Mask M3Goal none (dagKnownCloses M3Goal M3Cuts) M3Witnesses (dagRef 1 M3States M3Moves M3Links 0) M3Stock 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem M3Nodes0 : treeBlock 0 1 M3Check = true := by decide +kernel
theorem M3All : treeBlock 0 1 M3Check = true := M3Nodes0
theorem floorM3 : Lower M3Mask M3Stock M3Goal 4 := by
  apply lowerDag (chart := none) _ _ _ _ M3Autos _ _ _ M3Known _ M3Roots M3All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · simp
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
def T24Mask : Word := 0xffff
def T24Goal : Word := 0xfee8
def T24Stock : List Word := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
def T24Sample : DagSample := (0x2030040a00824100c0101802050402808060080c1009020140403, 12)
def T24Witnesses := unpackWitnesses T24Stock [1538, 263681, 526849, 791041]
def T24Cut0 : Bound := (0x5555, [0x4444, 0x5050, 0x5500], 4, 0x5440)
theorem T24Cut0Lower : Lower T24Cut0.1 T24Cut0.2.1 T24Cut0.2.2.2 T24Cut0.2.2.1 := by
  exact lowerPinMap (pinIx 0 false : Fin 8 → Nat) (by decide +kernel)
    floorM3 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T24Cut1 : Bound := (0x3333, [0x2222, 0x3030, 0x3300], 4, 0x3220)
theorem T24Cut1Lower : Lower T24Cut1.1 T24Cut1.2.1 T24Cut1.2.2.2 T24Cut1.2.2.1 := by
  exact lowerPinMap (pinIx 1 false : Fin 8 → Nat) (by decide +kernel)
    floorM3 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T24Cut2 : Bound := (0xf0f, [0xa0a, 0xc0c, 0xf00], 4, 0xe08)
theorem T24Cut2Lower : Lower T24Cut2.1 T24Cut2.2.1 T24Cut2.2.2.2 T24Cut2.2.2.1 := by
  exact lowerPinMap (pinIx 2 false : Fin 8 → Nat) (by decide +kernel)
    floorM3 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T24Cut3 : Bound := (0xff, [0xaa, 0xcc, 0xf0], 4, 0xe8)
theorem T24Cut3Lower : Lower T24Cut3.1 T24Cut3.2.1 T24Cut3.2.2.2 T24Cut3.2.2.1 := by
  exact lowerPinMap (pinIx 3 false : Fin 8 → Nat) (by decide +kernel)
    floorM3 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T24Cuts : List Bound := [T24Cut0, T24Cut1, T24Cut2, T24Cut3]
theorem T24Known : Known T24Cuts := by
  unfold T24Cuts
  exact (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from by intro b hb; simp at hb) T24Cut3Lower) T24Cut2Lower) T24Cut1Lower) T24Cut0Lower)
def T24MoveCert : List (DagMoveRecord 16) := [
  ([], fun i => Fin.ofNat 16 (permuteAxes [0, 1, 2, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 1, 2, 3] 0 i.val)),
  ([([(0xf00f, 0), (0xf0, 4)], [(0xf00, 4)])], fun i => Fin.ofNat 16 (permuteAxes [0, 1, 3, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 1, 3, 2] 0 i.val)),
  ([([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)])], fun i => Fin.ofNat 16 (permuteAxes [0, 2, 1, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 2, 1, 3] 0 i.val)),
  ([([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)]), ([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)])], fun i => Fin.ofNat 16 (permuteAxes [0, 3, 1, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 2, 3, 1] 0 i.val)),
  ([([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)]), ([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)])], fun i => Fin.ofNat 16 (permuteAxes [0, 2, 3, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 3, 1, 2] 0 i.val)),
  ([([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)])], fun i => Fin.ofNat 16 (permuteAxes [0, 3, 2, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 3, 2, 1] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)])], fun i => Fin.ofNat 16 (permuteAxes [1, 0, 2, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 0, 2, 3] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xf00f, 0), (0xf0, 4)], [(0xf00, 4)])], fun i => Fin.ofNat 16 (permuteAxes [1, 0, 3, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 0, 3, 2] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)])], fun i => Fin.ofNat 16 (permuteAxes [2, 0, 1, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 2, 0, 3] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)])], fun i => Fin.ofNat 16 (permuteAxes [3, 0, 1, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 2, 3, 0] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)])], fun i => Fin.ofNat 16 (permuteAxes [2, 0, 3, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 3, 0, 2] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)])], fun i => Fin.ofNat 16 (permuteAxes [3, 0, 2, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 3, 2, 0] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)])], fun i => Fin.ofNat 16 (permuteAxes [1, 2, 0, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 0, 1, 3] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)])], fun i => Fin.ofNat 16 (permuteAxes [1, 3, 0, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 0, 3, 1] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)])], fun i => Fin.ofNat 16 (permuteAxes [2, 1, 0, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 1, 0, 3] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)])], fun i => Fin.ofNat 16 (permuteAxes [3, 1, 0, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 1, 3, 0] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)])], fun i => Fin.ofNat 16 (permuteAxes [2, 3, 0, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 3, 0, 1] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)])], fun i => Fin.ofNat 16 (permuteAxes [3, 2, 0, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 3, 1, 0] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)])], fun i => Fin.ofNat 16 (permuteAxes [1, 2, 3, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 0, 1, 2] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)])], fun i => Fin.ofNat 16 (permuteAxes [1, 3, 2, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 0, 2, 1] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)])], fun i => Fin.ofNat 16 (permuteAxes [2, 1, 3, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 1, 0, 2] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)])], fun i => Fin.ofNat 16 (permuteAxes [3, 1, 2, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 1, 2, 0] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)])], fun i => Fin.ofNat 16 (permuteAxes [2, 3, 1, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 2, 0, 1] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)])], fun i => Fin.ofNat 16 (permuteAxes [3, 2, 1, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 2, 1, 0] 0 i.val)),
]
def T24Moves := dagMoves T24MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T24Autos : DagMovesOK T24Mask T24Goal 16 T24Moves := dagMovesOfCheck (by decide +kernel)
def T24Links : DagLinks := dagLookupLinks 0x160b0582a2e7702cc3401 0x501c176360762a06620443363c32a140360402a2292c1a620023145192c8b62b496207332b6b31f393142302b1b01f03013010080000f
  9 4 12 3 5 5
def T24Data : Forest := fun i => decodeNode 3 14 0xc553104039415402658a20104078 i
def T24States := dagTrace T24Mask T24Stock 6 T24Data
def T24Tags := dagTraceTags T24Mask 12
  (dagTagBases T24Stock 0xf249d24b924f 0x124812481248 12) 6 T24Data
def T24Check := dagCheckNode T24Mask T24Goal none (dagKnownCloses T24Goal T24Cuts)
  8 T24States T24Moves T24Links T24Sample T24Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T24Roots : dagCheckRoots T24Mask T24Goal none (dagKnownCloses T24Goal T24Cuts) T24Witnesses (dagRef 8 T24States T24Moves T24Links 0) T24Stock 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T24Nodes0 : treeBlock 0 8 T24Check = true := by decide +kernel
theorem T24All : treeBlock 0 8 T24Check = true := T24Nodes0
theorem floorT24 : Lower T24Mask T24Stock T24Goal 7 := by
  apply lowerDag (chart := none) _ _ _ _ T24Autos _ _ _ T24Known _ T24Roots T24All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · simp
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
def T34Mask : Word := 0xffff
def T34Goal : Word := 0xe880
def T34Stock : List Word := [0xaaaa, 0xcccc, 0xf0f0, 0xff00]
def T34Sample : DagSample := (0x30380a0d0182c140e04834060706038120b0281c180d0502c0c07, 12)
def T34Witnesses := unpackWitnesses T34Stock [3590, 265733, 527875, 792067]
def T34Cut0 : Bound := (0xaaaa, [0x8888, 0xa0a0, 0xaa00], 4, 0xa880)
theorem T34Cut0Lower : Lower T34Cut0.1 T34Cut0.2.1 T34Cut0.2.2.2 T34Cut0.2.2.1 := by
  exact lowerPinMap (pinIx 0 true : Fin 8 → Nat) (by decide +kernel)
    floorM3 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T34Cut1 : Bound := (0xcccc, [0x8888, 0xc0c0, 0xcc00], 4, 0xc880)
theorem T34Cut1Lower : Lower T34Cut1.1 T34Cut1.2.1 T34Cut1.2.2.2 T34Cut1.2.2.1 := by
  exact lowerPinMap (pinIx 1 true : Fin 8 → Nat) (by decide +kernel)
    floorM3 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T34Cut2 : Bound := (0xf0f0, [0xa0a0, 0xc0c0, 0xf000], 4, 0xe080)
theorem T34Cut2Lower : Lower T34Cut2.1 T34Cut2.2.1 T34Cut2.2.2.2 T34Cut2.2.2.1 := by
  exact lowerPinMap (pinIx 2 true : Fin 8 → Nat) (by decide +kernel)
    floorM3 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T34Cut3 : Bound := (0xff00, [0xaa00, 0xcc00, 0xf000], 4, 0xe800)
theorem T34Cut3Lower : Lower T34Cut3.1 T34Cut3.2.1 T34Cut3.2.2.2 T34Cut3.2.2.1 := by
  exact lowerPinMap (pinIx 3 true : Fin 8 → Nat) (by decide +kernel)
    floorM3 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T34Cuts : List Bound := [T34Cut0, T34Cut1, T34Cut2, T34Cut3]
theorem T34Known : Known T34Cuts := by
  unfold T34Cuts
  exact (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from by intro b hb; simp at hb) T34Cut3Lower) T34Cut2Lower) T34Cut1Lower) T34Cut0Lower)
def T34MoveCert : List (DagMoveRecord 16) := [
  ([], fun i => Fin.ofNat 16 (permuteAxes [0, 1, 2, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 1, 2, 3] 0 i.val)),
  ([([(0xf00f, 0), (0xf0, 4)], [(0xf00, 4)])], fun i => Fin.ofNat 16 (permuteAxes [0, 1, 3, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 1, 3, 2] 0 i.val)),
  ([([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)])], fun i => Fin.ofNat 16 (permuteAxes [0, 2, 1, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 2, 1, 3] 0 i.val)),
  ([([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)]), ([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)])], fun i => Fin.ofNat 16 (permuteAxes [0, 3, 1, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 2, 3, 1] 0 i.val)),
  ([([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)]), ([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)])], fun i => Fin.ofNat 16 (permuteAxes [0, 2, 3, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 3, 1, 2] 0 i.val)),
  ([([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)])], fun i => Fin.ofNat 16 (permuteAxes [0, 3, 2, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [0, 3, 2, 1] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)])], fun i => Fin.ofNat 16 (permuteAxes [1, 0, 2, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 0, 2, 3] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xf00f, 0), (0xf0, 4)], [(0xf00, 4)])], fun i => Fin.ofNat 16 (permuteAxes [1, 0, 3, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 0, 3, 2] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)])], fun i => Fin.ofNat 16 (permuteAxes [2, 0, 1, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 2, 0, 3] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)])], fun i => Fin.ofNat 16 (permuteAxes [3, 0, 1, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 2, 3, 0] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)])], fun i => Fin.ofNat 16 (permuteAxes [2, 0, 3, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 3, 0, 2] 0 i.val)),
  ([([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)])], fun i => Fin.ofNat 16 (permuteAxes [3, 0, 2, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [1, 3, 2, 0] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)])], fun i => Fin.ofNat 16 (permuteAxes [1, 2, 0, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 0, 1, 3] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)])], fun i => Fin.ofNat 16 (permuteAxes [1, 3, 0, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 0, 3, 1] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)])], fun i => Fin.ofNat 16 (permuteAxes [2, 1, 0, 3] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 1, 0, 3] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)])], fun i => Fin.ofNat 16 (permuteAxes [3, 1, 0, 2] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 1, 3, 0] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)])], fun i => Fin.ofNat 16 (permuteAxes [2, 3, 0, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 3, 0, 1] 0 i.val)),
  ([([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)]), ([(0xcc33, 0), (0xcc, 6)], [(0x3300, 6)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)])], fun i => Fin.ofNat 16 (permuteAxes [3, 2, 0, 1] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [2, 3, 1, 0] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)]), ([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)])], fun i => Fin.ofNat 16 (permuteAxes [1, 2, 3, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 0, 1, 2] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)])], fun i => Fin.ofNat 16 (permuteAxes [1, 3, 2, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 0, 2, 1] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0xa5a5, 0), (0xa0a, 3)], [(0x5050, 3)])], fun i => Fin.ofNat 16 (permuteAxes [2, 1, 3, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 1, 0, 2] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)])], fun i => Fin.ofNat 16 (permuteAxes [3, 1, 2, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 1, 2, 0] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)]), ([(0x9999, 0), (0x2222, 1)], [(0x4444, 1)])], fun i => Fin.ofNat 16 (permuteAxes [2, 3, 1, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 2, 0, 1] 0 i.val)),
  ([([(0xaa55, 0), (0xaa, 7)], [(0x5500, 7)]), ([(0xc3c3, 0), (0xc0c, 2)], [(0x3030, 2)])], fun i => Fin.ofNat 16 (permuteAxes [3, 2, 1, 0] 0 i.val),
    fun i => Fin.ofNat 16 (permuteAxes [3, 2, 1, 0] 0 i.val)),
]
def T34Moves := dagMoves T34MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T34Autos : DagMovesOK T34Mask T34Goal 16 T34Moves := dagMovesOfCheck (by decide +kernel)
def T34Links : DagLinks := dagLookupLinks 0x160a8d42a0e7702cc3401 0x7624466323e62616332063261503205026040082292c1a620023145192c8b62749620733276b31b39314230271b01b0300f010080000f
  9 4 12 3 5 5
def T34Data : Forest := fun i => decodeNode 3 14 0xc49d93404d004401e58a20104078 i
def T34States := dagTrace T34Mask T34Stock 6 T34Data
def T34Tags := dagTraceTags T34Mask 12
  (dagTagBases T34Stock 0xfb6dedb7b6df 0x1b6c2db436d8 12) 6 T34Data
def T34Check := dagCheckNode T34Mask T34Goal none (dagKnownCloses T34Goal T34Cuts)
  8 T34States T34Moves T34Links T34Sample T34Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T34Roots : dagCheckRoots T34Mask T34Goal none (dagKnownCloses T34Goal T34Cuts) T34Witnesses (dagRef 8 T34States T34Moves T34Links 0) T34Stock 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T34Nodes0 : treeBlock 0 8 T34Check = true := by decide +kernel
theorem T34All : treeBlock 0 8 T34Check = true := T34Nodes0
theorem floorT34 : Lower T34Mask T34Stock T34Goal 7 := by
  apply lowerDag (chart := none) _ _ _ _ T34Autos _ _ _ T34Known _ T34Roots T34All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · simp
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
def T45Mask : Word := 0xffffffff
def T45Goal : Word := 0xe8808000
def T45Stock : List Word := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def T45Sample : DagSample := (0x70781a1d0586c0e170b0782a1d0986c0e0f0d078321d0985c160f0e078321b0a85c1a0f0e074341b0b05c1c0f, 20)
def T45Witnesses := unpackWitnesses T45Stock [7694, 269837, 531979, 794119, 1060359]
def T45Cut0 : Bound := (0xaaaaaaaa, [0x88888888, 0xa0a0a0a0, 0xaa00aa00, 0xaaaa0000], 7, 0xa8808000)
theorem T45Cut0Lower : Lower T45Cut0.1 T45Cut0.2.1 T45Cut0.2.2.2 T45Cut0.2.2.1 := by
  exact lowerPinMap (pinIx 0 true : Fin 16 → Nat) (by decide +kernel)
    floorT34 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T45Cut1 : Bound := (0xcccccccc, [0x88888888, 0xc0c0c0c0, 0xcc00cc00, 0xcccc0000], 7, 0xc8808000)
theorem T45Cut1Lower : Lower T45Cut1.1 T45Cut1.2.1 T45Cut1.2.2.2 T45Cut1.2.2.1 := by
  exact lowerPinMap (pinIx 1 true : Fin 16 → Nat) (by decide +kernel)
    floorT34 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T45Cut2 : Bound := (0xf0f0f0f0, [0xa0a0a0a0, 0xc0c0c0c0, 0xf000f000, 0xf0f00000], 7, 0xe0808000)
theorem T45Cut2Lower : Lower T45Cut2.1 T45Cut2.2.1 T45Cut2.2.2.2 T45Cut2.2.2.1 := by
  exact lowerPinMap (pinIx 2 true : Fin 16 → Nat) (by decide +kernel)
    floorT34 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T45Cut3 : Bound := (0xff00ff00, [0xaa00aa00, 0xcc00cc00, 0xf000f000, 0xff000000], 7, 0xe8008000)
theorem T45Cut3Lower : Lower T45Cut3.1 T45Cut3.2.1 T45Cut3.2.2.2 T45Cut3.2.2.1 := by
  exact lowerPinMap (pinIx 3 true : Fin 16 → Nat) (by decide +kernel)
    floorT34 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T45Cut4 : Bound := (0xffff0000, [0xaaaa0000, 0xcccc0000, 0xf0f00000, 0xff000000], 7, 0xe8800000)
theorem T45Cut4Lower : Lower T45Cut4.1 T45Cut4.2.1 T45Cut4.2.2.2 T45Cut4.2.2.1 := by
  exact lowerPinMap (pinIx 4 true : Fin 16 → Nat) (by decide +kernel)
    floorT34 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def T45Cuts : List Bound := [T45Cut0, T45Cut1, T45Cut2, T45Cut3, T45Cut4]
theorem T45Known : Known T45Cuts := by
  unfold T45Cuts
  exact (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from by intro b hb; simp at hb) T45Cut4Lower) T45Cut3Lower) T45Cut2Lower) T45Cut1Lower) T45Cut0Lower)
def T45MoveCert : List (DagMoveRecord 32) := [
  ([], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 2, 3, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 2, 3, 4] 0 i.val)),
  ([([(0xff0000ff, 0), (0xff00, 8)], [(0xff0000, 8)])], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 2, 4, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 2, 4, 3] 0 i.val)),
  ([([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 3, 2, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 3, 2, 4] 0 i.val)),
  ([([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 4, 2, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 3, 4, 2] 0 i.val)),
  ([([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 3, 4, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 4, 2, 3] 0 i.val)),
  ([([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 4, 3, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 4, 3, 2] 0 i.val)),
  ([([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [0, 2, 1, 3, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 2, 1, 3, 4] 0 i.val)),
  ([([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xff0000ff, 0), (0xff00, 8)], [(0xff0000, 8)])], fun i => Fin.ofNat 32 (permuteAxes [0, 2, 1, 4, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 2, 1, 4, 3] 0 i.val)),
  ([([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [0, 3, 1, 2, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 2, 3, 1, 4] 0 i.val)),
  ([([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [0, 4, 1, 2, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 2, 3, 4, 1] 0 i.val)),
  ([([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [0, 3, 1, 4, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 2, 4, 1, 3] 0 i.val)),
  ([([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [0, 4, 1, 3, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 2, 4, 3, 1] 0 i.val)),
  ([([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [0, 2, 3, 1, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 3, 1, 2, 4] 0 i.val)),
  ([([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [0, 2, 4, 1, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 3, 1, 4, 2] 0 i.val)),
  ([([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [0, 3, 2, 1, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 3, 2, 1, 4] 0 i.val)),
  ([([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [0, 4, 2, 1, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 3, 2, 4, 1] 0 i.val)),
  ([([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [0, 3, 4, 1, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 3, 4, 1, 2] 0 i.val)),
  ([([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [0, 4, 3, 1, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 3, 4, 2, 1] 0 i.val)),
  ([([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [0, 2, 3, 4, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 4, 1, 2, 3] 0 i.val)),
  ([([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [0, 2, 4, 3, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 4, 1, 3, 2] 0 i.val)),
  ([([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [0, 3, 2, 4, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 4, 2, 1, 3] 0 i.val)),
  ([([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [0, 4, 2, 3, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 4, 2, 3, 1] 0 i.val)),
  ([([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [0, 3, 4, 2, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 4, 3, 1, 2] 0 i.val)),
  ([([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [0, 4, 3, 2, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 4, 3, 2, 1] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 2, 3, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 2, 3, 4] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xff0000ff, 0), (0xff00, 8)], [(0xff0000, 8)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 2, 4, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 2, 4, 3] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 3, 2, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 3, 2, 4] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 4, 2, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 3, 4, 2] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 3, 4, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 4, 2, 3] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 4, 3, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 4, 3, 2] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [2, 0, 1, 3, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 2, 0, 3, 4] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xff0000ff, 0), (0xff00, 8)], [(0xff0000, 8)])], fun i => Fin.ofNat 32 (permuteAxes [2, 0, 1, 4, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 2, 0, 4, 3] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)])], fun i => Fin.ofNat 32 (permuteAxes [3, 0, 1, 2, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 2, 3, 0, 4] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)])], fun i => Fin.ofNat 32 (permuteAxes [4, 0, 1, 2, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 2, 3, 4, 0] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)])], fun i => Fin.ofNat 32 (permuteAxes [3, 0, 1, 4, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 2, 4, 0, 3] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)])], fun i => Fin.ofNat 32 (permuteAxes [4, 0, 1, 3, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 2, 4, 3, 0] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [2, 0, 3, 1, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 3, 0, 2, 4] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [2, 0, 4, 1, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 3, 0, 4, 2] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)])], fun i => Fin.ofNat 32 (permuteAxes [3, 0, 2, 1, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 3, 2, 0, 4] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)])], fun i => Fin.ofNat 32 (permuteAxes [4, 0, 2, 1, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 3, 2, 4, 0] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [3, 0, 4, 1, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 3, 4, 0, 2] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [4, 0, 3, 1, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 3, 4, 2, 0] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [2, 0, 3, 4, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 4, 0, 2, 3] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [2, 0, 4, 3, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 4, 0, 3, 2] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)])], fun i => Fin.ofNat 32 (permuteAxes [3, 0, 2, 4, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 4, 2, 0, 3] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)])], fun i => Fin.ofNat 32 (permuteAxes [4, 0, 2, 3, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 4, 2, 3, 0] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [3, 0, 4, 2, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 4, 3, 0, 2] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [4, 0, 3, 2, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 4, 3, 2, 0] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [1, 2, 0, 3, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 0, 1, 3, 4] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xff0000ff, 0), (0xff00, 8)], [(0xff0000, 8)])], fun i => Fin.ofNat 32 (permuteAxes [1, 2, 0, 4, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 0, 1, 4, 3] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [1, 3, 0, 2, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 0, 3, 1, 4] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [1, 4, 0, 2, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 0, 3, 4, 1] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [1, 3, 0, 4, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 0, 4, 1, 3] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [1, 4, 0, 3, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 0, 4, 3, 1] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [2, 1, 0, 3, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 1, 0, 3, 4] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xff0000ff, 0), (0xff00, 8)], [(0xff0000, 8)])], fun i => Fin.ofNat 32 (permuteAxes [2, 1, 0, 4, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 1, 0, 4, 3] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)])], fun i => Fin.ofNat 32 (permuteAxes [3, 1, 0, 2, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 1, 3, 0, 4] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)])], fun i => Fin.ofNat 32 (permuteAxes [4, 1, 0, 2, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 1, 3, 4, 0] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)])], fun i => Fin.ofNat 32 (permuteAxes [3, 1, 0, 4, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 1, 4, 0, 3] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)])], fun i => Fin.ofNat 32 (permuteAxes [4, 1, 0, 3, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 1, 4, 3, 0] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [2, 3, 0, 1, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 3, 0, 1, 4] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [2, 4, 0, 1, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 3, 0, 4, 1] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [3, 2, 0, 1, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 3, 1, 0, 4] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)])], fun i => Fin.ofNat 32 (permuteAxes [4, 2, 0, 1, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 3, 1, 4, 0] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [3, 4, 0, 1, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 3, 4, 0, 1] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)])], fun i => Fin.ofNat 32 (permuteAxes [4, 3, 0, 1, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 3, 4, 1, 0] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [2, 3, 0, 4, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 4, 0, 1, 3] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [2, 4, 0, 3, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 4, 0, 3, 1] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)])], fun i => Fin.ofNat 32 (permuteAxes [3, 2, 0, 4, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 4, 1, 0, 3] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [4, 2, 0, 3, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 4, 1, 3, 0] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)])], fun i => Fin.ofNat 32 (permuteAxes [3, 4, 0, 2, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 4, 3, 0, 1] 0 i.val)),
  ([([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [4, 3, 0, 2, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [2, 4, 3, 1, 0] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [1, 2, 3, 0, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 0, 1, 2, 4] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [1, 2, 4, 0, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 0, 1, 4, 2] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [1, 3, 2, 0, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 0, 2, 1, 4] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [1, 4, 2, 0, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 0, 2, 4, 1] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [1, 3, 4, 0, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 0, 4, 1, 2] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [1, 4, 3, 0, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 0, 4, 2, 1] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [2, 1, 3, 0, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 1, 0, 2, 4] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [2, 1, 4, 0, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 1, 0, 4, 2] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)])], fun i => Fin.ofNat 32 (permuteAxes [3, 1, 2, 0, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 1, 2, 0, 4] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)])], fun i => Fin.ofNat 32 (permuteAxes [4, 1, 2, 0, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 1, 2, 4, 0] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [3, 1, 4, 0, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 1, 4, 0, 2] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [4, 1, 3, 0, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 1, 4, 2, 0] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [2, 3, 1, 0, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 2, 0, 1, 4] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [2, 4, 1, 0, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 2, 0, 4, 1] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [3, 2, 1, 0, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 2, 1, 0, 4] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)])], fun i => Fin.ofNat 32 (permuteAxes [4, 2, 1, 0, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 2, 1, 4, 0] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [3, 4, 1, 0, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 2, 4, 0, 1] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [4, 3, 1, 0, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 2, 4, 1, 0] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [2, 3, 4, 0, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 4, 0, 1, 2] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [2, 4, 3, 0, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 4, 0, 2, 1] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [3, 2, 4, 0, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 4, 1, 0, 2] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [4, 2, 3, 0, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 4, 1, 2, 0] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)])], fun i => Fin.ofNat 32 (permuteAxes [3, 4, 2, 0, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 4, 2, 0, 1] 0 i.val)),
  ([([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)]), ([(0xcccc3333, 0), (0xcccc, 14)], [(0x33330000, 14)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [4, 3, 2, 0, 1] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [3, 4, 2, 1, 0] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [1, 2, 3, 4, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 0, 1, 2, 3] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [1, 2, 4, 3, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 0, 1, 3, 2] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [1, 3, 2, 4, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 0, 2, 1, 3] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [1, 4, 2, 3, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 0, 2, 3, 1] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [1, 3, 4, 2, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 0, 3, 1, 2] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [1, 4, 3, 2, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 0, 3, 2, 1] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [2, 1, 3, 4, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 1, 0, 2, 3] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [2, 1, 4, 3, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 1, 0, 3, 2] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)])], fun i => Fin.ofNat 32 (permuteAxes [3, 1, 2, 4, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 1, 2, 0, 3] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)])], fun i => Fin.ofNat 32 (permuteAxes [4, 1, 2, 3, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 1, 2, 3, 0] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [3, 1, 4, 2, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 1, 3, 0, 2] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [4, 1, 3, 2, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 1, 3, 2, 0] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [2, 3, 1, 4, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 2, 0, 1, 3] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [2, 4, 1, 3, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 2, 0, 3, 1] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xaa55aa55, 0), (0xaa00aa, 7)], [(0x55005500, 7)])], fun i => Fin.ofNat 32 (permuteAxes [3, 2, 1, 4, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 2, 1, 0, 3] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [4, 2, 1, 3, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 2, 1, 3, 0] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [3, 4, 1, 2, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 2, 3, 0, 1] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [4, 3, 1, 2, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 2, 3, 1, 0] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [2, 3, 4, 1, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 3, 0, 1, 2] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [2, 4, 3, 1, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 3, 0, 2, 1] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)]), ([(0xa5a5a5a5, 0), (0xa0a0a0a, 3)], [(0x50505050, 3)])], fun i => Fin.ofNat 32 (permuteAxes [3, 2, 4, 1, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 3, 1, 0, 2] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0xc3c3c3c3, 0), (0xc0c0c0c, 2)], [(0x30303030, 2)])], fun i => Fin.ofNat 32 (permuteAxes [4, 2, 3, 1, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 3, 1, 2, 0] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)]), ([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [3, 4, 2, 1, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 3, 2, 0, 1] 0 i.val)),
  ([([(0xaaaa5555, 0), (0xaaaa, 15)], [(0x55550000, 15)]), ([(0xcc33cc33, 0), (0xcc00cc, 6)], [(0x33003300, 6)])], fun i => Fin.ofNat 32 (permuteAxes [4, 3, 2, 1, 0] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [4, 3, 2, 1, 0] 0 i.val)),
]
def T45Moves := dagMoves T45MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T45Autos : DagMovesOK T45Mask T45Goal 32 T45Moves := dagMovesOfCheck (by decide +kernel)
def T45Links : DagLinks := dagLookupLinks 0xbf9af07ba12e04b612d80b22295a9eb67a09b9a5aa96065809586522930e4c092864a0920648091863e489361297a55c147001be16d91b606d81b226c81b016c01b006b0994c60a568d581154654854e251154024e113614c893204c0528447951074401100428d0a042810a04204fa73d0cf403c08d2f3480ce23304cc03300c632bb0ae02a88aa02a04a802a00a42204859416005611580560112444011004020d1820a00bc001 0x19d063c63418904d033c0f40c901c203c010809005ec48673d8f18cf624133ccf03cf32407040f00410246730cc18cc31813300c03cc0186728cf18ca31813280f03ca0186720cc18c831813200c03c801801724f805b93d016a4f005992c671ccc18c7318131c0c03c7018bb5bd2add6c4ab6d6529e9292c39599299c663c63198c2ac0626929d89025634a1318cf03c63307b00c986a732408d41281c003d429c0f00400313e9c0c1edd02a01740a40580287ae809803a025007c0900120084d525212d493cb6ce4c0e5464837518f26b363001158908303481ec0cf09a433014c01204b003c0a900c0055c3cb6c64c273163cc2958907af33014bc0f2db19329ac58c87313323748c7805231d0138c702310324b480a83d20290f380a005163001464c005293001418f004d326012cc94049324013589004b930012589004e6240130cc804a3310120cc0dd4c3e01524f80539309acd8fa5bf62592b989073333e1afccc47ae330373cc7804f31d011cc7023003e94bd8f24af630c29589072f33c1abccc09a532408bc0f01af0300a9409110ac3801164cd08a92c94f98ce52e63292f989e4ae62662698858916201cf8ccc72e3321af8c9c6ae3260e68c5439131408f80cc22e03206f809c1ae02600680240110084427d10056c3f42270e044693e0f1a4c814663e01198c80446241cf4cfc72733e1af4ccc6a73320e64c5439031408f40fc22703e06f40cc1a70320064024010008010a4f0cbf93c00fd8f003c33c0104cd003fc3c00fa4f003cc3c32e40900390180503128040c3e34f6528cbd93e04f592803d63e04ecd2803b33e0060c5013a04a00e80f803800840d18f0fa96303ed1890d3433c32a4cc0cb432404d00f002903000d00910339483ece4f0fa893034cd920cb363c32a18c013334800cccf002833044901210a403c00d80d00220300ec98c0faa62400c8cc0caa3240ec64f0fac93000c58f0cac63014940f00340343ead890fad93000c80d0031c3c64be4f03af93032b18c012c33c32b58c002d33000be4c8cac63200b0cc812503200ac04002d93000a804002b62410a98c03aa62404a8cc002a32410b24f03ac93004b18f002c63000a4040033c3e0ec24f83ae93000c18f802e63000a0cf812403e12970f03a593c00958f002103c42930f8fa493e32918f802433e008c10402203e00800200160300e5809189601804740f801d0324423d10035c3f42230e102793e3e9e4c8d2763e329d8c812733e009ccc812603f047c0f8026033007c0c801e009007002001a930005c0c0016030325e4c00176300058cc0e1994a36664f8c99932086592819963e00658c821834a0660cf8018332085412819503e00540c8013028003809001162404380f800e032441fd10292c3f421f0e011293f004a4ccf8792c38418f8d90632324189821033e0640cc8010326083c0fc20d03e063c0cc18d032003c09c00d026441bd102d7c3f421b0e015793f015e4ccf8692c390d8f8dc3632330d89824333e070ccc804332608dc0fc21b03e06dc0cc19b03200dc09c01b026005002400c008002a4c0505f4412170e040993e0e264c810963e00258c810833e0020cc800731404130e000492c080f0e0285933060e4b0105633001589c003620140b0e0886933120a4b07066331a1989c3826200818ccc1863270018c6c00231444070e208b93342064b1f0b6337a2d89cf81620682cccd98b327622cc6cc81314142c0cc48b0270e2c06c00b00f000402000001f
  14 5 12 7 7 6
def T45Data : Forest := fun i => decodeNode 7 19 0x1891780a6c49f5993db3279664b2c814589331987f130f2ac9f479308f261424c28b1e5031d8ec4921892699948930966632189249984831c8ec65124ce2b12443261927908cd20e1f38c3c7d278f98f9c61e3c33e7007ce0061c8043802718068db0fce01a34c3e50068cb0f18b1f289325ec60a24c16b182962456648a8041499f2833238066718f1299f200414007c800f108042003238012700c8e8041c02619260698c8a999156302c660580c8a8048c028272663589089930d0271a0643809868040c00f03260298c83999073140e6360989c1c96046200662808020080f80 i
def T45States := dagTrace T45Mask T45Stock 9 T45Data
def T45Tags := dagTraceTags T45Mask 20
  (dagTagBases T45Stock 0xfeeeeefdddddfbbbbbf77777f 0xeeeee0ddddd0bbbbb0777770 20) 9 T45Data
def T45Check := dagCheckNode T45Mask T45Goal none (dagKnownCloses T45Goal T45Cuts)
  95 T45States T45Moves T45Links T45Sample T45Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T45Roots : dagCheckRoots T45Mask T45Goal none (dagKnownCloses T45Goal T45Cuts) T45Witnesses (dagRef 95 T45States T45Moves T45Links 0) T45Stock 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T45Nodes0 : treeBlock 0 16 T45Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T45Nodes16 : treeBlock 16 16 T45Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T45Nodes32 : treeBlock 32 16 T45Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T45Nodes48 : treeBlock 48 16 T45Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T45Nodes64 : treeBlock 64 16 T45Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem T45Nodes80 : treeBlock 80 15 T45Check = true := by decide +kernel
theorem T45All : treeBlock 0 95 T45Check = true := (@treeBlock_merge 0 48 47 T45Check (@treeBlock_merge 0 16 32 T45Check T45Nodes0 (@treeBlock_merge 16 16 16 T45Check T45Nodes16 T45Nodes32)) (@treeBlock_merge 48 16 31 T45Check T45Nodes48 (@treeBlock_merge 64 16 15 T45Check T45Nodes64 T45Nodes80)))
theorem floorT45 : Lower T45Mask T45Stock T45Goal 10 := by
  apply lowerDag (chart := none) _ _ _ _ T45Autos _ _ _ T45Known _ T45Roots T45All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · simp
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
def A1Mask : Word := 0xffffffff
def A1Goal : Word := 0xeee8e880
def A1Stock : List Word := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def A1Sample : DagSample := (0x141a048640c16028540613090682219030380a0d0182c241608854140e0483406070e078301a0a058221306038120b0281c381d0c06428150904c180d0502c0c07, 29)
def A1Witnesses := unpackWitnesses A1Stock [3590, 265733, 527875, 792067, 1058307]
def A1Cut0 : Bound := (0xaaaaaaaa, [0x88888888, 0xa0a0a0a0, 0xaa00aa00, 0xaaaa0000], 7, 0xaaa8a880)
theorem A1Cut0Lower : Lower A1Cut0.1 A1Cut0.2.1 A1Cut0.2.2.2 A1Cut0.2.2.1 := by
  exact lowerPinMap (pinIx 0 true : Fin 16 → Nat) (by decide +kernel)
    floorT24 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def A1Cut1 : Bound := (0xcccccccc, [0x88888888, 0xc0c0c0c0, 0xcc00cc00, 0xcccc0000], 7, 0xccc8c880)
theorem A1Cut1Lower : Lower A1Cut1.1 A1Cut1.2.1 A1Cut1.2.2.2 A1Cut1.2.2.1 := by
  exact lowerPinMap (pinIx 1 true : Fin 16 → Nat) (by decide +kernel)
    floorT24 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def A1Cut2 : Bound := (0xf0f0f0f, [0xa0a0a0a, 0xc0c0c0c, 0xf000f00, 0xf0f0000], 7, 0xe080800)
theorem A1Cut2Lower : Lower A1Cut2.1 A1Cut2.2.1 A1Cut2.2.2.2 A1Cut2.2.2.1 := by
  exact lowerPinMap (pinIx 2 false : Fin 16 → Nat) (by decide +kernel)
    floorT34 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def A1Cut3 : Bound := (0xff00ff, [0xaa00aa, 0xcc00cc, 0xf000f0, 0xff0000], 7, 0xe80080)
theorem A1Cut3Lower : Lower A1Cut3.1 A1Cut3.2.1 A1Cut3.2.2.2 A1Cut3.2.2.1 := by
  exact lowerPinMap (pinIx 3 false : Fin 16 → Nat) (by decide +kernel)
    floorT34 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def A1Cut4 : Bound := (0xffff, [0xaaaa, 0xcccc, 0xf0f0, 0xff00], 7, 0xe880)
theorem A1Cut4Lower : Lower A1Cut4.1 A1Cut4.2.1 A1Cut4.2.2.2 A1Cut4.2.2.1 := by
  exact lowerPinMap (pinIx 4 false : Fin 16 → Nat) (by decide +kernel)
    floorT34 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def A1Cuts : List Bound := [A1Cut0, A1Cut1, A1Cut2, A1Cut3, A1Cut4]
theorem A1Known : Known A1Cuts := by
  unfold A1Cuts
  exact (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from by intro b hb; simp at hb) A1Cut4Lower) A1Cut3Lower) A1Cut2Lower) A1Cut1Lower) A1Cut0Lower)
def A1MoveCert : List (DagMoveRecord 32) := [
  ([], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 2, 3, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 2, 3, 4] 0 i.val)),
  ([([(0xff0000ff, 0), (0xff00, 8)], [(0xff0000, 8)])], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 2, 4, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 2, 4, 3] 0 i.val)),
  ([([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 3, 2, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 3, 2, 4] 0 i.val)),
  ([([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 4, 2, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 3, 4, 2] 0 i.val)),
  ([([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 3, 4, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 4, 2, 3] 0 i.val)),
  ([([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [0, 1, 4, 3, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [0, 1, 4, 3, 2] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 2, 3, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 2, 3, 4] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xff0000ff, 0), (0xff00, 8)], [(0xff0000, 8)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 2, 4, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 2, 4, 3] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 3, 2, 4] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 3, 2, 4] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 4, 2, 3] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 3, 4, 2] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)]), ([(0xf00ff00f, 0), (0xf000f0, 4)], [(0xf000f00, 4)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 3, 4, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 4, 2, 3] 0 i.val)),
  ([([(0x99999999, 0), (0x22222222, 1)], [(0x44444444, 1)]), ([(0xf0f00f0f, 0), (0xf0f0, 12)], [(0xf0f0000, 12)])], fun i => Fin.ofNat 32 (permuteAxes [1, 0, 4, 3, 2] 0 i.val),
    fun i => Fin.ofNat 32 (permuteAxes [1, 0, 4, 3, 2] 0 i.val)),
]
def A1Moves := dagMoves A1MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Autos : DagMovesOK A1Mask A1Goal 32 A1Moves := dagMovesOfCheck (by decide +kernel)
def A1Links : DagLinks := dagLookupLinks 0xc4030c2c3030a1c283062bcaae85ba02e61b982de4b706d63b582d60b582ce4b382c83b202c23b082c20ae92a0da786983a602942a38e8c1a18e7689d827609c8a7209c826e295b2560948a50194025008cbe1ac8682181858616085061218482120802600080020007f09fc07e85fa07d89f417d01f407c09de970b9c207081b856d09ac468199a3650d867618186060897c35c957205a9162458815e257815c1560952354815205481520529123448811854601180460118045850e443810c13f20f633a1ce803a00e803a00e803984dc53684da03588d603580d033400cc23300ca13280ca02f1ca6b2904a2128809e2260c8c62300882220088022008421b3050e14004e113804e013044c00f9c3e00f803a20c903200c802e2089814700a4001 0x3a401a05200a0288690114c38774198851c940225870f4234a7a01a4bcf8d21dcc66214204a0a002484f81201cc062f2e6480971a40438100a1c068b0e02809c00e3cd8075e6803413601109a0073ca992022008051003458801404bbd1025867c12a33d09419e02b8c681580341240084900201c800d0240050e2031408f007847002423401013af450997a23cc0cfde4c67cf2233d78c19e3878c5026007e12603e09101e84600f015401e01e0080880203c5192022869010e04078819e04400f021d8806f694007b32003280c019067870a034085014044bd38de989c0f494e77231e8390cf421809cf0801a0840073c08cf420407a0fc04205300d22ebd10de58840f294270e3100290c6c0386281040430800213bf806ddf40340fe00f07d00703c25001ec0800ee93457861cabbb0e09e125a4ee92c07831083b9882dc46670e232777118db868c515c40664e202707100d828803c0340104f4f452797a203d24b41e52580ec63487019fbb80c9dc306284e003f070013828003c0300100e864806400c038a50013c6480e6f4e0727a21b831381c129c0de63d04e18d03701381240340da00806a7a20348cf419c0986ca03406501403200601880840c201a45c7a238598801346340d6043068021033006c1080340c600906000422dbd10279886116c4208361c83e30e0dd52840ea64276c199baf8cc5c286280d803305f018820803c0280100baf4475c31eb84988017067a01231470861c00424b0169870e0e92c04031380398809658700b693705949638318800fc63600c31442802019400d00a005085204032901a01480a1d5cc900ae34803102602b012109c08064e03402701402a004014c01864804002401a11200a014528004604c42502011180d0c9405009e63c04c02019100d008805067803532101a01e00a4084050e9833004c0180250130cec06807602833a1a001d0cd012009808c042045020822010010c0100aaf4e0527a21a8313814129ce9c63e74d31e0270cf813467886804e04b02101f01040b408009203e04701e82100f0ce406a64003403901481000a005c010480f4404061c2198d08ccc66c02c31403b02039e18f00f067807403c03801a01c18d08f989c07cc4203d61c11ca5380e528446e04e03702100f0020898c8004c634029314018a5300d5290c4694052349a0139930894c8004a63402f020018b1080c187a05cc385234a1111990806c05045604202b01b01498f1ca067805003c02631e01218d0090c6804ec420254a10119909c88664e4233002201901080c08cde88068c4303361c119250c8b528406493702d49b01624b40a925844064202031b00d80a0070050e3831801c00c38e98c007466003602841e1a718f0d0807866c83404e31a02100d00d805008003003c2144a100a24d9059e88a2ec4331661c10ba50c05d26e02c92c415021a098108c5406e62603601501580980a90fde88a82c4333f61c120a50c10526e07e92c436021a0f8108cd806e63e03603601580f80a806401202400801019e00698d1025e8801ec4200e61c1862508030c8401633100518a00430e001125840ec3800949b803a4b000cc40408c38004496201b0e141526e60692c20531b80298ac00cc4080cc3850a49b98324b0828c6e01462b0063100010c51161870abc93735849612f18dc178c560b062070118a008803c00401000001f
  14 5 13 8 4 6
def A1Data : Forest := fun i => decodeNode 8 21 0x28a49284f8d22880953e0499f0244fb10d7de8b1801c9c008cd003a69e891803f8c7a24a0cfa5067b2833c9401f4600224807b1802890007c68026340111a03c8c6212f8d2229e9d0803c8862043813a100510a00e8461caf810df407b020427d007be8109f801cfac385f0203da4b5d9258ec621773103b98d1d8c84be648747a736bd11b5280e294e6d31eb68139b4010da0335f021b03d11a467ad20426002633806d80050ca01864004b0010984034c200860018af98ac05e88b833d5c49bacb0e169258b2620011a42b012159e9c840105300629bd1109280a294e4231e278cf908678840304c0212101312807c8404c4801ea101090c08286040430042180f10926e24c3840496093108dd8706e33c3a0201d80f0e92846e634380211b80ac492906ac432061c1024dc818845cc3d2e02017b0e0b926c4092d2001b15a4b080c785003c286211098f09928442634243211080c8840604263620015090cd868660360181c0140d80d8680122403c1849b89a4b04c05626936140150980204801e0233c1062105b0e02cc681a6420b1988598ac0926e0ec380849603988008c560692c04310018c50080100201f00 i
def A1States := dagTrace A1Mask A1Stock 9 A1Data
def A1Tags := dagTraceTags A1Mask 29
  (dagTagBases A1Stock 0x1fc63c78c7cd9b318dfab56b5aff16b5ac5ff 0xc63c78c00d9b318c0ab56b5a8016b5ac580 29) 9 A1Data
def A1Check := dagCheckNode A1Mask A1Goal none (dagKnownCloses A1Goal A1Cuts)
  165 A1States A1Moves A1Links A1Sample A1Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Roots : dagCheckRoots A1Mask A1Goal none (dagKnownCloses A1Goal A1Cuts) A1Witnesses (dagRef 165 A1States A1Moves A1Links 0) A1Stock 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Nodes0 : treeBlock 0 16 A1Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Nodes16 : treeBlock 16 16 A1Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Nodes32 : treeBlock 32 16 A1Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Nodes48 : treeBlock 48 16 A1Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Nodes64 : treeBlock 64 16 A1Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Nodes80 : treeBlock 80 16 A1Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Nodes96 : treeBlock 96 16 A1Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Nodes112 : treeBlock 112 16 A1Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Nodes128 : treeBlock 128 16 A1Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Nodes144 : treeBlock 144 16 A1Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A1Nodes160 : treeBlock 160 5 A1Check = true := by decide +kernel
theorem A1All : treeBlock 0 165 A1Check = true := (@treeBlock_merge 0 80 85 A1Check (@treeBlock_merge 0 32 48 A1Check (@treeBlock_merge 0 16 16 A1Check A1Nodes0 A1Nodes16) (@treeBlock_merge 32 16 32 A1Check A1Nodes32 (@treeBlock_merge 48 16 16 A1Check A1Nodes48 A1Nodes64))) (@treeBlock_merge 80 48 37 A1Check (@treeBlock_merge 80 16 32 A1Check A1Nodes80 (@treeBlock_merge 96 16 16 A1Check A1Nodes96 A1Nodes112)) (@treeBlock_merge 128 16 21 A1Check A1Nodes128 (@treeBlock_merge 144 16 5 A1Check A1Nodes144 A1Nodes160))))
theorem floorA1 : Lower A1Mask A1Stock A1Goal 10 := by
  apply lowerDag (chart := none) _ _ _ _ A1Autos _ _ _ A1Known _ A1Roots A1All
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · simp
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
def FinalMask : Word := 0xffffffffffffffff
def FinalGoal : Word := 0xe8e8e880e8808000
def FinalStock : List Word := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def FinalSample : DagSample := (0xb0d82a35098cc1c2e068b4162b0389c4c36128d44633070781a1d0586c0e17130b84a2d118ac2c1e0a874261b0383c743e1c8f46436188d4542e148b446270d078321d0985c160f1e0f8723b1a0d86233160b8522b1289c381e0c86c2a170683c783d1d0ec6835190cc582d150ac4c270e074341b0b05c1c0f, 54)
def FinalWitnesses := unpackWitnesses FinalStock [7694, 269837, 531979, 794119, 1060359, 1330695]
def FinalCut0 : Bound := (0xaaaaaaaaaaaaaaaa, [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000], 10, 0xa8a8a880a8808000)
theorem FinalCut0Lower : Lower FinalCut0.1 FinalCut0.2.1 FinalCut0.2.2.2 FinalCut0.2.2.1 := by
  exact lowerPinMap (pinIx 0 true : Fin 32 → Nat) (by decide +kernel)
    floorA1 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def FinalCut1 : Bound := (0xcccccccccccccccc, [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000], 10, 0xc8c8c880c8808000)
theorem FinalCut1Lower : Lower FinalCut1.1 FinalCut1.2.1 FinalCut1.2.2.2 FinalCut1.2.2.1 := by
  exact lowerPinMap (pinIx 1 true : Fin 32 → Nat) (by decide +kernel)
    floorA1 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def FinalCut2 : Bound := (0xf0f0f0f0f0f0f0f0, [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000], 10, 0xe0e0e080e0808000)
theorem FinalCut2Lower : Lower FinalCut2.1 FinalCut2.2.1 FinalCut2.2.2.2 FinalCut2.2.2.1 := by
  exact lowerPinMap (pinIx 2 true : Fin 32 → Nat) (by decide +kernel)
    floorA1 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def FinalCut3 : Bound := (0xff00ff00ff00ff, [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000], 10, 0xe8008000800000)
theorem FinalCut3Lower : Lower FinalCut3.1 FinalCut3.2.1 FinalCut3.2.2.2 FinalCut3.2.2.1 := by
  exact lowerPinMap (pinIx 3 false : Fin 32 → Nat) (by decide +kernel)
    floorT45 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def FinalCut4 : Bound := (0xffff0000ffff, [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000], 10, 0xe88000008000)
theorem FinalCut4Lower : Lower FinalCut4.1 FinalCut4.2.1 FinalCut4.2.2.2 FinalCut4.2.2.1 := by
  exact lowerPinMap (pinIx 4 false : Fin 32 → Nat) (by decide +kernel)
    floorT45 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def FinalCut5 : Bound := (0xffffffff, [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000], 10, 0xe8808000)
theorem FinalCut5Lower : Lower FinalCut5.1 FinalCut5.2.1 FinalCut5.2.2.2 FinalCut5.2.2.1 := by
  exact lowerPinMap (pinIx 5 false : Fin 32 → Nat) (by decide +kernel)
    floorT45 (by decide +kernel) (by unfold AvailableWord; decide +kernel)
def FinalCuts : List Bound := [FinalCut0, FinalCut1, FinalCut2, FinalCut3, FinalCut4, FinalCut5]
theorem FinalKnown : Known FinalCuts := by
  unfold FinalCuts
  exact (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from by intro b hb; simp at hb) FinalCut5Lower) FinalCut4Lower) FinalCut3Lower) FinalCut2Lower) FinalCut1Lower) FinalCut0Lower)
def FinalChart : Option RowChart := some ⟨[15, 23, 27, 29, 30, 39, 43, 45, 46, 51, 53, 54, 7, 11, 13, 14, 19, 21, 35, 37, 38, 57, 58, 60], rfl⟩
def FinalMoveCert : List (DagMoveRecord 64) := [
  ([], fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 4, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 4, 5] 0 i.val)),
  ([([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])], fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)),
  ([([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)),
  ([([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 3, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 5, 3] 0 i.val)),
  ([([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 5, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 3, 4] 0 i.val)),
  ([([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val)),
  ([([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])], fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)),
  ([([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)]), ([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])], fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 5, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 5, 4] 0 i.val)),
  ([([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val)),
  ([([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 5, 3, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 5, 3] 0 i.val)),
  ([([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 5, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 5, 3, 4] 0 i.val)),
  ([([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 5, 4, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [0, 2, 1, 5, 4, 3] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])], fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])], fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 5, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 5, 4] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 4, 3, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 4, 3, 5] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 5, 3, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 4, 5, 3] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 4, 5, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 5, 3, 4] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 5, 4, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 0, 2, 5, 4, 3] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])], fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])], fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 5, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 5, 4] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 4, 3, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 4, 3, 5] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 5, 3, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 4, 5, 3] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 4, 5, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 5, 3, 4] 0 i.val)),
  ([([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 5, 4, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 5, 4, 3] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])], fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])], fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 5, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 5, 4] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 4, 3, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 4, 3, 5] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 5, 3, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 4, 5, 3] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 4, 5, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 5, 3, 4] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [1, 2, 0, 5, 4, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 0, 1, 5, 4, 3] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])], fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])], fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 5, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 5, 4] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 4, 3, 5] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 4, 3, 5] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 5, 3, 4] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 4, 5, 3] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)]), ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])], fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 4, 5, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 5, 3, 4] 0 i.val)),
  ([([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)]), ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])], fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 5, 4, 3] 0 i.val),
    fun i => Fin.ofNat 64 (permuteAxes [2, 1, 0, 5, 4, 3] 0 i.val)),
]
def FinalMoves := dagMoves FinalMoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalAutos : DagMovesOK FinalMask FinalGoal 64 FinalMoves := dagMovesOfCheck (by decide +kernel)
def FinalLinks : DagLinks := dagLookupLinks 0xff10ffac6fe90bfa40fe903f905fde1bf780fde03f684fda03f680fd70ff191fc40bf100fc10ff040fc007f000fbb17eec0fb90beb0dfac03e84bfa007e743f9d03e605f8b37dbdcf6f03d9c8f6217d880f5f0fd7c0f5c0fd508f4e1bcd98f3603cacbf2b03cac0f2a07ca41f1e2fc780f1e03c780f1623c580f1603c541f0c27be92ef613bd41ef30bb94eee017b782ede03b780eda13b680ed613b24dec807b143ec503b140ec20faec7ebb03ad46eb503ad01eab27aac0eab03aa42ea903a9c2ea703a981ea603a980ea40ba6c9e8a47a280e870fa181e8603a180e830f9f07e712f9c01e70039a86e6a039a80e641b9900e5f179607e445390c1e3f138f81e3b0f8e42e38078c47e20478800e1d0f8683e1a0385c3e17038542e15038483e06338141e020f7d4ddf4077c43df0077bc1deb137ac0deb037a03de31778c0de10b7801dd82371d1dae676b80dac0b684bda1036840d9c17640cd90036400d8c136300d8b0762c0d851b5d8fd76035d80d76035c45d71035c40d6c175b00d6a0b578cd4d475340d49135201d470751c0d450b5044d34374d00d320b4b06d2c034a04d27074981d26034902d20134410d10034382d032f40c0d03033fc4cff033f42cea4f3555cc4473100cc20b3080cc2032fc3cbf032f81cbb0f2ec0cba072e41cb9032e01cb60b2b88ca03b27c1c9d0b2740c9b0b26c0c990b228fc89072201c88032200c793f1e40c78071a8ec670f18c4c600f1704c4d3f1340c4d031340c4c071282c4a031241c40270f82c3d070e44c39030dc2c36070d80c36030cc3c33030c81c300b0c00c2f070b81c2e030b02c1e3b0198c06030180bfc2afec1bfb02fec0bf616fd80bf602fc84be926fa40be806fa00be802f9c1bdd2af701bdb06f6c0bd90af640bd70af503bd402f482bd202f480bce12f149bb836ee00bb60aed41bb502ed40bb016eb82bae02ea45ba902ea40ba512e709b8f36e04eb6e4edb41b6a0ed849b6102d7c2b5f02d646b4d32d301b4b06d2c0b412ad040b4102cfc2b3e06cf80b3e02cf02b351eca8bb1c3ac586b0f1ec189b0212c080b0106bec6af616bc84ae632b980ae602b902ae012b743ad61eb580ad602b502ad402b482ad202b3c3ac91ab240ac902b183ac602b006ac002af43abd02af40abc06ae04ab802adc1ab702adc0ab216a7d3a9e06a702a9716a3c8a8f02a342a8d02a2c2a8b02a2c0a8b02a107a8402a100a820aa080a82029ec7a6a469a41a69029458a3e4e8e84a35168d40a330a8cc0a310a8b05a175685c0a16068445a11028440a0c168300a090e8240a04168004a00027f439fd027e839f2227c809f10677939de0277809db0e76819d61274459cf0a73819cc0a73009ca0a70889c20270029c0026fc19b2366c809b1066c409af0a66d499b0266819990666409990265c29950a65409950265409930a62c897e365f029751e5d019710e5b0596c025a8296a025a419660e57c795c0e570095c0255869560255419511253c294c0e52049460a50c39400e5000940024f4393d024ec29380e4d8292a324a41928064a009270649429240649009230648819200a480091f0647c091f02478191e0246459190246409170a434a8fc463e438f70a3dc08f6063d028f0123a868ea023a808e70e39818e60239418e30a38c08e206358c8d60235808d30e324a8c90232408c90231838c60231418c50230c28c30230c08c3022ec88b12a24de8930224c08910a244088d122187886022102884021f8687c0a1f0087b061ec0877121dc0877021dc087216185185c16148a8443a10c1842060f4583d020ec283a060d45834060cc18300e09c982606090281c2206c18190a064081902060181412050081306028980a02028080a02028080a02028080611ff497fd01fe837fa01fe417f511fd407f501fcc27f00dfc007ee09fb417ec05fa047ca79f2807c809f1c17c215f0417bd11ec4c7b101eb837ae01eac37ab01eac07a80de9827a601e9417a20de8417a101e8017a001e8007a001e70477a89de807770dddc077311d90f74f55cf9173c09cf0073c01ccc973301ca4a72901ca0172801c98272601c94172405c90072209c88072105c80171b15c6c071b01c6c071909c64071709c3c870235c04170101c00170001bf826fe01bf416f131bc406f101bc406f101bbc26ef01b9896e505b8c26e205b8806e105b7c26de05b7806dd05b7406dd01b7406d425b2c96cb01b2c06cb01b2816c905b2406c805b0086aa59aa806aa01aa026a801a9c16a701a9c06a701a9036a305a88169e11a4cb6900da20868801a18268601a14168405a10068401a08268009a00067f059fc067f019fc067f019ec46702d9bc166d0999876660199026610d98406610198406600596c56561595806530d948164d15934064d01930164c01928264a019280649059240648058fc963f018f8163e018f4163d018f4063c058f006390d8e40638058c86632018c80632018bc362e058b8062e018b8062d058a4461e2d874161c05868261a0186416180586006160982cb60b018242609018105604018100604018100600118000600017e865fa017e805f8097e005f8017e005f3157a0b5e8017a005e60979805e60177885db0d76815d51575405d20d74805d20174805cf0d73c05cf0173815ca1172805c90572405c90172405c4156ec95af316bc05ae056ac35ab0169c45a70169c05a50968835a201684159f0967c059e05678059d05629358a016088582016080581056040580055e08577055dc0576055c84572015c41571015c40571015b8356e015b8056e015b8056a115a8055f2d57c055c0d568255a0156415590156405560d550255401550055209548054f0d504e52b5949c45240d470851c014700518114543510154382508194182506013f0a4fa093e804f8093c864f2013c414ef093b034ec013b004ec013ac14eb0139854cf5d33034cc0131474c50130834b9252e404b9012d834b6012d804b6012d414b0152c004af05294a4a20d26c749b0125c449701250349401240449001234348a0d2280489052240489012183486012102478311dc1477011dc0477011d0346d1d1a8346a011a804661119804660119024640118c14600d180046001180046001174345131118b4430d108143f0d0ec443b010e4242a3d0a8042a01094542501078741e0106c341b0106c041b01050741401050040f15000f3f238fc803f200fc413f100fc013ef04f9c83e700f70b3db04f6423d900f6403cb38eed03ba04ee413b900ee403b708ed423b500ed013a734e9813a504e9013992ce60139800e5823930ce40339000e40038d0ce20538800e18238600e18037f1cdf8137e00df0237a08de8037904dd4437500dd0137400dc8237200dc8037200db0636b04dac036a04da0235744d5c035700d5033510cd44034d10d34034b08d2c034b00d20334800d2003450cce0d31f64c7c031f00c7c031a14c68031a00c64131708c5c031604c58031018c40030e08c3803071cc1c030508c14030500c14030500bf872e954ba402e900b9442e500b7c62d330b4812d200b4022cf04b3812c914b2012c314b0c02c300b0032c000af042a94caa402a804aa002a800a9822a504a9402a500a84429b18a2d028908a24028708a0c428300a08128200a08027c189ec127b009e42277089dc0276049c842720098cf2630098422610096c625b0096422590096402590095832560095802560093c724f0093c024f0093c024a14928024a009280245148e4c237088dc0237008cc4233008cc023108898b22600898022210888021e10878021e00878021e00864520d307f111e94c7a401e90079831e60079411e50079401e110754c1d30873461cc0473001ca0872801c90472401c90071051c2086dcb1b6046d801b2106c801b2006c021b0006bc11a9186a401a51069401a50069011a01064cd1920463c318f00634218a0c62411860c5ecb179085e40175105d40173085cc0173005b4616130584015f08578115e00564515900564015510518f13a304e80139044e01138004dc1136044d80136004acb12b004ac012b004a03128004a001260849411250049401250048c211d1845091063841801060040841020040800fe103d490f20c3b840e8183a000e80039040e40039000e20838800e10438400df0837c00dc0c37000da0836800da0036800da0035c30c64431800c60030840c2002fc30b6242d800b6002d800b6002b880ae002b020ac002a430a9002a400a8042a000a8002a000a80029820a21028410a10028400a10027050932424c00920424800920023c3086242180086002084082001f8407e001f0207c001f0007c001d8606a30170e05c0016c105b0016420590016400590016010531414c00530014c004d18130104c0012040441011000440011000410c0dca037000dc00340c0cc1031080b4402d000b4002d000b010271409c00270009810230c07460161c0349001300001 0x9d8332a36c18d50160c0a93b049606d8233002c10d80145c0b03b24040059201a0ec78100163c0680b1e058058e0204ec580a1b62c0380b160109cc531ecc679881b31467ad19e31404c501e80678020762c0800b160343d8a01402c5007016200983b0e040058701a4e61a5266335258d98664968cd31002618d2403346280b200591d8d0208ec60100163406a0b180349d89014cec30099b62403adb0c01a058900882c3003a75fd2c0dafe660051802c0ec18100160c0680b0265405217a24e6118f66330c40dafa314057d0041ebe995015f46a80b0555c05207a21ec01958f5fccaa7afc6549cc131ecc65988016006ac0afe355057e1aa36608cf5a32c6280af8008051f9284e6025266329258d980649cc40313b4651880f0f064c087831a3c3b013021d806815e8011987e6246cbe324661f189815e064c0a3cf449cbf31ecc649881b2fc67ad19231405237a2828ebd12731cc7f397263d98c831036638cfdb2e467b987a31b68c818a1ebb806c15dc01e0aec009057500402c8d5741616ab80a44f45051c7a24ec2195e75eccad3af26559d7432a4e6318fe72e0c7b318e6206d841abb6bd8d59b5e46aadae83546cc619fb65c0cf730e8636d18e314058402b82bd815815e40aa0ae805404c601f825c00f4f0e8036087400f00c70044ea9a551b54cca80aa6354157202602b9010275b8050dadc01c056e00812b7813075bc0800ade0343d6d01402b680727548c90daa4348056f0244ea89921b5b46900ada0489d504aa36a8195015c06a84adc04c1d6e02002b700d0f5b00500ad801c9d4e4aa36a7195014d06a80a0e04c1507020168380d275512ad3ab09559d4d4aa4c62a4b1b550cacdab06556d4d32a3462988015506ac0ab0355054d1aa00628c5095c409a0a2404c1d710208a89010015c406a5a240349d6b014ceb50099b5ac03adad401a056b00882b5003a6311258d18862000c418a0ab4013415a00833acc0299d6101336b30075b5840340acc011056100702b280a2630cc41318492c68c231012b3013475980820acc0353d640149eb180a2758004c0ac801d056300e36b0006895846b03ac234c05611a01eb00cd015806504abe0581d5f02602af81001570051318092c68c031012ae813475740820aba0353d5b0149e1c0098156c03a087001a98bb496661b989da2ecc40786e327043718d805d8c50959c09a3ace041056701aceb100a6757804f3ab40266d6200eb6af006db5680340ac4011055e00782ad003814500b02a2804c2d14020029a006010a86493a8c9546d4632a02ac557275312ac7aae9559d454aa4c5d24b1b530cac0aae6556d4532a345d1880f0a464c085231a3c1f013020f806815580107a96954054b32a028a813054540805a2a0343d5201402a9007095480983aa4040055201a02a880a1b424098ea120408d0901a02a7804262e1258d17062000bd18a12a98134144c0983aa6041151302002a980d4b44c0687aa00293d4e01302a8007415380347a9295405160260a8b0100b4580693a786206d3c18a029e0020152e4a00a9464a054932482a4192262dcc40da76314053b0044c5b24b330acc4d9840326054618a02a0006414e80100a8862498b531066a08c6db4f862ada703143d4100d82a1804c150001e0a7c009053800402a0a5501500ca87a7c954053e32a029e192262d0c400a7231400bd9281e9d9928f4e8c927a7064898b3310029d8d2814e86920a7034868b318a02aa494415364a07a9864b3d473251ea29924f508c913164620054c1a582a38d2815146920a84348cc3618db4590c50f4fc0360a7e00f053d004829b802014200982a100402d0801a029a006094c40983a62040053101a4c58a4b1a2c4c407850326042818d1e99009814c80340a6000d98b0496661a189da2c0c40784e326042718d1e9a809cf07004c0a6a01b041c00d0299802414bc011986462498af4966618989814b464c0a54314cc2d0130296002262b9258d15c6203d2a19302950c68f4a404c0a5201a98ad31066198c6da2b46287a4e01b0527007cc56188330b0636d1583143d2b00d8295803c14a00120a4c008056992882acc9427554c973a6c64a9d2e324ce92992262acc40daaa34b6d361a536970d25b494691983631b68ab18a02aa812c14d80940a5c04905250241e0d806c106c01e0156008051802c4e91a581b48ccc00a46360051702c028b0130f4852a80a426540515026028a0160142c030417e04c98aa4963455188014786280a3604d05130264e860099b4300353a409569d1f4aace8ea55262a5258da406566d1f32ab68e9951a2a4c400a40356051f1aa828e8d5002a46280a3404d05120264e850099b4280340a1400e9d1b4aa368d9950146c6a80a352581ce57ac0272b1627460ca8da30354051802a1e8b19201458691315062068a818a105f80227454c953a286499d133244c539881b454694da283496d131a434538c5014540940a2804905130240053802011d407808e83481d11020028880d0145de9a0a24f4c1ce4626027225327440cab396c63d98a631036880d55b2d867ad14c314051002a825b00f40298010096634804b232a0e87013014380800a1204c05080261e8625501430ca80a1635405070261e84992014246900a1004805077a60e71b160738989809c695804e24a602370d20141408008da33c24599280e703138138d29c0a0692c98a531034528c50126007c08d803c2458aae02854968737deb409bec5a9cb44a4cc5224b1b2d0c92d14862004971a502358d2014180b43a080411d02020028200d414080687830026041800d122bd570148a4b60a3925a1cde7ad026f316a72dd297396294998a3496365b992db2c4c93982e62768a3310025b8d2c12c4692782e327041718d80518c5014640b60a1e05a9d0d013ce808099b434036da0201a050d0078280803873fc69809fe3401cd97a6026cb13273f92ab314492c6cfe32ab451188013f86aa01443149cf8013367c006813e001d314292c68a13101e0b0098105803409f60089cfc325ce7d19266280c40d9f834b6cfa1a4e60a8c6da28062809f804b04fa0249e0a806c105401e01400081cd87ac0e6bbd3013618b009aec4c04f5026122b49407355e9c09b0c4e04f361c4c4fa4b1a27cc4048ab55c1cd492d026a3d6a6279870d13c92c04f81ad1e7b8cc813dc64c09ec05a1cf40268e79013013d008209e40403c0c0190206009813be4a079dc649989d31002770d25a27462848a925004ec61c4c4e24b1a270c4009d60411ce902602748100914e4a1313692ccc13313b44d988013c009e09da04e1cea020827500d4f3a004e781202604e800d82048068914a4a039a6f4e04d36274c4d24b33020c4ed1346203c0819382040c6c026862809fa04f04f90274e78809e739c04cd9e201b6ce700d0278803c139c01c29bb2509899310344c8c50026401009a49401cd24a00270a520734928009a2c4c04e302c02710130138006829b955c04d06264e57a4f66261258d95e63d689831002578cf4026062809ca04d04e40264e6f8099b37c03409be00e04cf7a6026e81001335e99312ec386897496004b9880136869a29b404104da9284c4b24b1a258c40012c31404cc6200e66310013598903998c4004cb7a6026c0160135c09809aa04004dc928826dc9401329881496094b98954963a58192f301cc4ed12a62014b01a59e038c9c101c636012a31404d9020ce6a009db35003609a800f1cd202602690100b33e4a0299ef449cad498cc4a24b1b2b4c62d12862004ad198804a0c52734404cd9a201a04d100702673d12624d870d12692c00933100e6601301330080399ef451ccd7a20267b0e41335871795c93fa4ae499cc4924b232b8c7ee95c633cc06313b4491880b2b867e295c3333c0619382030c6c024862939960276ccb00d8265803cb341e8a5994f4414d061c8a6530e0134125a099492cbcac31fd25618ce72b0c4f31226208cac19fba560ccdb2b064f980a31b689118a165600fc52b006609580273c0500d8202803c024401029bd25114d3928026f30e4134d8700992940a4a9325ce5498ce6240c40e95234b6ca9199e6020c6da240628295204b04a90199e02006c101001e01200083cc74b0026399807314098098a04004c4008026125500f9c64807a43186b87012025d8c7012f0018097831804bd312025d8032623d258097e6203be8193025f0c68ee2004c097401e6b8700d024a8020130eab879829563cc04aa9e5ca5526239258098265604c032a825c9951a238c4077cc32603e618d1dc300980e180340926008049700c023a0d501284098079a01804b50080e59813012cc08048a355c1caf92d0257bd6a6235870d11a92c3be531901f2989812806b4770a3320385193025b0168f2d0064096802604b200c8235806012b9eb0095af4c1cae92802573d1012b5870794c931988c496025318c7300cc4ed1186201cab1a502558cf8ef9064c07c831a3b8401301c2006812480100956c4c04b0aae0257bd1012b1898794a93d988b496025298f73008c4ed11662004aa1ab1df18c980f8c6347706026038300d024880232f7127877b833c03dc192025431572f8926477c433203db19265f0a4c8ef8466407b432404a67a665f024c8ef8066407b23242450aae0e52c9681295eb53114c38cbdd499364e996b326cc6797046326c903101dee8cc80f60648093a05a3c9b0199dc100c81240010094204c049e324660098981278ca8094555c04a07a21e4f9954f274c7b3112620049f1aa824e8cf73000636d112314fbdf49e1deb98f32ffd2600936c55cbfe4991deb18c812686643930040049801a024b8060f2552a8092a654049402a024931300f54648d8f4024048f7aa363d192072300800918034244faae0249c9687245eb40922c5a3c904a4cc4424b01240c92d1106203bd419301ea0c6812380b4791a026048d00d02458034913aab8098d25b04b892d025bc94412c64a03952f5a04a962d1e53a52cf291293310e92c04a7325825219272ff0c4ed10e6203bd319301e98c68128c0b6093805a3c990139dbf8098126403606fe01a0496004824500201222ab8790e955988649602439955a218c4077a232603d118d1e3e809811f403408ee00804730264c42a4b1a214c40090804d3c830130241806a621125997f6626cbfa19302400c5012164a209052503c813259e3f9926620cc40090234b047f1a4e5fc8c6da20c62997ea930047a00c1226d572620987197e89323bd0319023e8d6811f066408ec314047b02d65f500c811e401008e604c6b740120e3a8d0011d466808e8354047302601e79891add0648079a0181c70026023801009131e8808da92c988131034408c50912e4a1310092c68803100e37010471b008008dc035046c01a1de680980f34034489555c987f61c343fa4b0ef30c64079862604771ad1e3b0cc811d864c08e405a3c710190238809811bc03208d60181c691a002348cd011a06a878cc649987e31002330d25a1f862808ca04a03ca31201e4006091264a130fa92c3bcb1930231013b2fdc04c4890f44045f4964c3e1881a1f0628488f250987b496343d9880718008238bc040046001a822f00d0ef2004c079001a24469284c3d24b32fd8c4ed0f46203bc719301e38c68119c09e08c804e3c630139e308098118c03608c201a045d0069222c94261e525997d262768793101de30c980f18634090c04f047e0271e3c009cedb804c08f001b036e00d023500241170010488925005737a782923d381401e8a09ccf441cc86270264253a7224c7f38b663d987831036448cfdb16c67b96da31b687818a024480fc116c07a76da01b036d007803c0020113069008966541459026022c810271458ab30eec386c514aab43ba4b01144caa00ee6209c58019362c0098116003428ac05804560264c3b30e1a1d925828a804d04540209db580c80dac04d30eac38cb6a499b43aa4b0eda8c6606d462700753104e2a80ce714c064d8aa0276c53013022a806c114c034089602403663180228d570f1418ab30e8c3804504aab43a24b0ed94c6406ca6263b5d19901ae8c98113c628289804c044c02002258c9051200980890040987361c3439a4b0ed90c6406c86263c4919902248c98111c63330e4c38cb67499b43924b0ed8cc6406c66263c4d1999dad0cc8113464e06b4326044a18a82230c50115e4a208a52509c4e4a5ce22a52661c5258d89c64b6c45324e5ac989da1c4c40089c34b04451a49dac8c9c0d6463600e231498707a265ac30fda1c187076b093f0358499803824b0110de8930dec38cb57499b437a4b0ed5cc6606ae627006f3100a213d1011118860884c38986e49665ab189da1b8c4076ac327035618d80370c532d54c6196a86243b551981daa0c9010fcc48d7d06486c3e31301f40d2010f864c076c04c038802435f39921ad54c4c76a832603b502601c38121af48c90d6a862603d21a401aa0c9811012c2087a9606c3c33035f31921ad4cc4c087836003e61a401a98c988b040c8087606003b402601c3012010e4020087000c6c2b32a02158d5010900b0084005499cc31265a90c60ed4803196a2630cb503121da88cc0ed40649340203004350140100009010c8c4808600286c3018c0218006090b8098385c040042e01a0219a4b1b0c4c4c0862326042f0150216809805140100856954042a32a0211016261b5258d6a26263b5019302140c50080404c0288008042632436118d20108c0900846648042532a02121921b088690084404804204aa4c3624b1ad40c4c06a03260200013020e802010deab8086c95604344aa8216255261ad258d8526566c2732a35a7989810a46ac084e354034f193021081680bec0b20536058041f02b020f015410700a803fe026014200400b88121af38678079c03c6bcd32401e68d20063c0983832040041901a35f2a551ad3926407ca654034e31901d98d600e146a8083401004180061162816010580a8082801001fd00611b6494261a9258d69a626034d19311628138104004c03020081c0d026020681008dae4a130d292c040b0270e050104102806a03fa026019200411b55570701e4b4080ef5a986861c35a624c80d30c64458635a01fc199009f0c5010540b40826032041200902088044103c020081c00e040c006820480301019e98580d25014067a2020330e0b00d296280693f0403499cc33a4b22f90c94e7c863e6be431935a59898af9069427c833e03e419901a58c98aec809c570804a13b202109c200f80ec806c0708032023b01380fd809804f4010280f55c04077a20202b13050092ae080493f986649639f19959af8cc7cd69062613e31ab01f18cf80d2064c276205a138302b01d881080e0c07c047402701fa013009e0021af84c79968e63003e119e1da38cc0100deb0d7c0648cb4631801f00d20ed18660d80266004011b035ef99500ffcc4933e86246bde1a465a00c600f7809076800181c0293302013d9810012ccd7c46566bdd32a659f98c1aff8c4d965862403e21ab01ee8d50ecfc66007fc3263b2c19201d281600e3c0aa07040540239018ccfc00c00ff4050045c02501ef01210dd0131afecca807f635422bc02c01fd01508aec099967a9303b3d3184cfb8cc00fe002007ee00ccb3e31801fa98900fcc05133ec930cb3c19235f98c60ecf004807e6018021b498659d9890ecec648047002403f0318659d0c60ece803196726243b3919201f701308da24a0457894e03ef4a481f6a4b00bb8c4d3386624cb3818c1d9c00600fac0b046cf55c03f94ad01fb24b32cdcc60d7e8626cb293121d9b8cc00fd064c765232422ba02d011b80c667d406007e402a03f101481f600a00fa804c045802501e7012009d00200fa12a807ce65403d202a01e680300f8526207b46306b4731301ce80d00f9189807c093d03d931e35a318980e7008007b86546b4531835a218c00f85e98d68663039f331265a08c606f824b407c0f5a6b4231801ef989b2cb4c48046c03139f901801ef00a00f71292074404c03da62011b349406f65e9c07b2c4e986549635eb989f2cb4c4cd7aa62003d71939d968c980f54628046a02701f9013009c80200f5d2a807aa64803921a611b2d5700f9a4b407cb2501be37ad01f1b1680f8929607ba949986449601ed99280f60c90d67e62603d61939d960c980f50628074204e03bc02681c8813008d004e03f0026013800401e90151acf9260379c04003ce01a01e780900f34018379204003c901a11b24942618d258d67a62601f7193009b8c500f2c04c079401903c800691b1c9426189258d66e62603d11a781e80c9ceca464c079831503c718a1182813c08cc04e03ea0260193004809b0021af00c90d66c6246bbf32a359a98c1af14c48077e354033519801e28c900e380a8071a03c6bbe32401e198900e30090d77a6486bc231301de8d200f0864c07160486b3431801e018900ef8c4c077e94903bd4a4359998980f112aa07829546bbc324359918980ef06900664326038a02401d81951ae80678074003c6b9e32401cf0d200ee40b0032404c1bb802001dc00d00eb0c78076c65403ab31e35da8d500ed40a8075494800f202401d498c1ae74648073a02403b24a601d418f1ae7066007380306b9b19e01cd80f00ec24a8d73433c039a01e4cfb2521ae64690073204803ad32435d60d200eb0090d730324039801201d4a501ae5c660072e0306b9631e01cb0cf08d8a4a00756f4e03aa7a20dd431380ea129d338a64199f631e81d39881ae9067cd72a33c03a401f01ca80f267d9290074633c03a331e01d219200e886780736648039f00801cc18900e75280072e630039b7a401cc24d08d85e88372ec4203974a101cb18800e50010072863c039301e11b049400e81e92073cf441b9c62701ce25380e68c7c073263d039531e4c3098800e4801046bd55c22c192d01dd49540ede4a00768f5a03b37a20dd8b1680ec52b4075e64a03ae32481d319200e94c7b30c06206ba119f35c88cf00e8407c072203c6b3149e019898f008c8678d660630033019801c69891ae30c4c0718326038e4a481c5a521acbcc4c065e326038f62ab59724c80cb8c6407143580231199011700c80e212a8d70e65403871aa009800400e11898d65a630032d19800c081208d76ab8070d25a03859280dc1bd680e0d8b40704949985f496359618980cb064c070205a01ef01301c00021adf404806fa01800f200611ae55726179870d656932032b31911820d6808c06640322314037e02d011600c80df001006f32500378324cc2e98800dd80b0d6e8024037400c11adc9426171258d654626032a19301b901380dc404cd6e0019037000691ad4942616d258d652626032919301bd013c0ddc09c06ea02701e701301b980240dbc01046b355c043a92d820dc968105e4a208112501c047ad020231680ff129607d2949985a49635e99929af18c90d65062603d31a501e30d200ca064c460605b22b902d01dd813c0e4009c05d804d027402601c4812c0dfc09406f6049036e0240115809c079804c031a009012e00401b600700dac0317388930cb273121d938c900da4061964c93ccb254981d9318f0ec94c6133ca33c036819a00f20cc00d992a806c0358985961c359324c8ec94c6406c862001e519900968c51ad84c9006c234803614a401b12551ad80c9006c0348035f02a4c2c30e1ac95264064a63201e419901ad8c500daaab806cec55985761c35b2a559ad8d2a8d648932036532b01b199500c90c6406bc35a2afd1ac95518d600d746ac06b8355035a1aa00f18cc804ac62930ad2506b237a50191b1280789294025492c03589284c2abd11ac8987c064493e2302327915c193808a8c7e03c263e018c310809498804d5e4a006b2f4f03577a24c2a30e1ac85264064263223011a7915b8d386c04686356e342022919980f00cc8062c62a0250314cb2031201901890ed552c006aa660031f3121daa0d800d500c1963c624035218e018f1890ed452a806a2654031d3121da80d500d400a80638930031b312018d24c0ed34038069a0105b474a521a3a4f8ed1d264568e64a134731f01a398c80c64c48769433e034a01f018c18900d29898062e624034b62621a32558ed1927c268c656034631f018b1890ed246ac0692056034449801a3b1300d0d2780688c401b437a701a1b1380d046387682028034131e0da33d680d198b4068a94a03424a465891890ecc4692765a348034018e019981348c9de88067433d033918a009300208c9a4a0067c625cb0f312019e98800cf063c067631d033818e1c938c50049401006686480336312019801200cd1290066a9540333324018a98900cbc090066094803143120198b1500c4d260065e358032d4a4018918900c452600620624232592801879890e49062806540082324aae01a9c96c0d3e4b4069d251034c9280da43d680d218b4767e94a3b374a4019f99280cdcc90061c62452db1ad9d990d3ceb5c69a765c34b3b2c1a51d958d24eca46907314315392218a116d816c0cc809e05ae04d032e025819601280cac0920652048018a004809100232c35260064e628030d4981d9331500c992a806189303b2532a01928d500c2de900647250030a61e1c90a4b00484c40264525003247a781913d100c25260a5b464f4ada3219cc49884e480c4045b434f1ada1a180c48c54048062996406543b201aa019001532c78c90763c348031e024658d80a0ec6c03806360103b18199018c00c80c6128006329403b171a5018b81280c50078062834c230d7a2648f9880e47c6280620008230c928018fbd3c0c75e9c0638f45031a7a20d8b31380c5929dc5a864fcb15321e56919072c4cc7f962463ecb1131ee58798f32620c43923a62052d41a79d8a8d0ceb48682762633f3b1219f1d888cf4ec3c6787310315391d18a116a013c0c5408605a4041031301f818900f80c4407a061e03c0188004808e80232c35290761a648030d1a40185bd132471870723892c011c31009853d100c318860614c38e2d34a1ed69a4df261d25b923692c52d3321a56998dce61cc42723662022d31a18d698cdc061c62a023631423097a21587310c6c25870261c943030e49b8184a4b38b40c87b5a0637cad0315e4c318872468c40a5a03434ad019b9d680cace61862a723431422d00218d6800dc0b40056030c009011a0041190c940aca1e9e3642f4413286278194310c0c85870061062452cf1a7a5678d0ceb3c66e730a315390f18a1167813c6b3c086059e037018500480878021ab70c4c05b832602fb7b201833d800b8927ad60a6606adb31301828d800b6c64c35960640304030018155704bf64b405d525002e1624cc29b0e1ab6926405b463212cd1ad01138cc8060c628060095402f362a017f01500bf12a805ee95402f902c009800400bde4a8d5b26246ad8318357a98900b6066005ea32499de018017898900bbc050d5de31802ef00c0179c9400bc9258d5e062602f0193096601380bb805533bc0260182004017ed5700bee4b405f525502f8928017b25280bd129205da9489852496356b98980b5c64c259605a022601300c00020057c08035600406ae849e017418f00b9802025d555c02ea9284c28b0e1ab5926405ac63212ca1ad01650d38089066425d205a02e9027017381040b94064d5c064802e01a40970d5700b8a4b605c325012df4ad016fa5380b79258259005a02c802700bf80200b54c4805b8f6002d43120169a4c00b64c4805b094802d23120168a4c00b558a825a725002d47a78169bd104b4989c05a4c4202d161c648c9880e46462802fc00812daaae016dc96c0b6a4a025aef5a02d77a7016b3d100b40c487230314017d004016619506ac0080059294802cdaae0d65c9686b2a4a00596c5a02ca61c0d6419240b20c6330a06201301aae0181c96c0c064a025fef5b12ec7ad017fbd3c0bb1e9c05d6f4502e47a20171a4fc0b7527b309e92c6acf31301678c984b380b6258e05a02ce0278163813808a004e0446026018400480be00200b14080058803c02c232a015f30e0093cc63309c62099cc31800dd24c009412780578640024f31e015d98d00b0eab80582c5a02b362c814db1600b018ac057ec5502bd62a0134b0e00ae8caa049c631984d3100134494009358933098c3802b8928095abd3c4a8de9c04e6f4502677a2012b24fc093127b309692c02aa4aa015b01500ad0ca8055a65402b102c015800d04aa4ca8055263c02ad92a015549400aa589c04e4c3802a8310015ad5700ace4b4056525502af9280157316809c5870055864a02ab324815399200954c63309462002884a44c24a4b00500010052b25002874a5013f252409e9291309092c02a5025015201200a88ca8050c63c014002608a00100a500068053a62002a0928014f99280a78c9205386489847310014c49400a14c94051464902843244c23188005000983532040029901a014198f00a624a80504948029702c0137810069bc068051e02802927a24c2298800a3c098051a04c02959284c21a4b00a5009c052604d02910260d4801040a4006a051c029028c013014549500a20090050262002830260138010069c00680502f48028792801433d380a15e920508f4802827a20140188009fa4a004fa64e027c310013ba4b009dde8804f4f440279321813c188409d8c40054725002a17a7814dbd380a69e92052cf45028b7a2014498fc09fcc7c04f663d027531e4c211880057868004e004002724a40137810009c0c7804dec40024349e00a480d049ceab804e725012717ad0138bd38095127b308292c126e02d0137013809b406a02b6034026c0130132016009a80a804d1250984061c09328d38098468204b6332026592801323d38098cc7b307e62012619280130bd1260f9258d4c06320260199012f0098097868004ba040125b928012dbd10496809c04b4042025901a8933c94009a5e9e04cef44983d4960933013c498809c04cc0430262021012f80d4097004e04b0026015d020012180c0495aab804ad25012557ad012abd380951e8824a665a0253327012918804918c98048c64099cc31400dd18d009412a80490658024f32a092299300914c80049b250124a4a70120a4b26730c90d492348024902401231920092a4a00490f4e02477a20122b138090c060248325002417a2092001380900084047e025124c92801273d3c0931e88249664f12443270125990c0910c840484621023e310095bc9400ae5e9e056ef4412a6627893a31380a9988604e8c42026b61c812bb0e00944c66047a631983c310011dbd61a8d92a8046c65402321aa011c0cd0685c098042e040021b01a011b315008d52a8342c04c0216020010d007008c98a8342a04c02150200117819008b40b03475266023a7b3011cb15808dd8a8d4689566a334aa011a195808ccca8044c35802311ab01180d5088740cc0432058022e02b01160150688809a342804c0222020810a010048aaab80455250222732d0d13993805e8c40443835a1a1c1a701078c526779290044a0101227aae0113c9404899eb4044cf4e02247a211098168684c09c041a00802210260110b1304889ecc0444f5a1220033011001680879ec004369486a1a324010d0d20085d290d42c64802161a4010a81204872ab8043b25b021c928090cbd680865e9c0430f44121462d010a3138484c0b4042604e017900400a680f1a84406004220246a0519801028c900838078d41863c020c19e010580f1a8206600410324020819801038c9088164a0340af44020561c1107d570683e4a0041ef44220d1ad0d068d380834684441405a1a0a027010501080824062d40c0256a04012010300640810030445355c2a2b92d8d14c94048adeb60456f4f02297a211140d6c888c6b4345034f1a231a701140d0c088c68402f6315017818a110f816c88480b4343e04f1a12027010f810c08480840420009020300410dc813066e4080037203401cc00810dd013066e808003740349a014aa3500995008046a80396058020002a10dc013066e0080037003419b71a600db8d0007f802003fa00c19b402600da010046d006803f6c4c01b302c10da813046cc080336a03401f300e34f98040e7e529003f264801f20260cd8810006c406803e801019ae1a000d70cd087964a003ee31419db0208cd68100076c06a035a03401f600900ef0044070c020034600899f331e34f98cf0e7ccc7803e633c99f43244cf918f1a7d0690d3e433c01f402400f900f007c00b033b404001da01a0cec8d30076468003dc05801ea7a210f2494007b009c03d604d01e902600f40020878eab803ff25a01fc9280cfd3d6807e98b533f094a99f54a434fc1929a7d4c9003f034a01f51a410e9816807c409c03ba04d01c202600f7812807b409203ce04819d80208cd60100076006a035803401a100418d80d30a6c0680538831c99e562a34f2a5500794ca8539a35801e41aa18dd8d30a6ec68003c525021d232700d0188047864a003c6f4f01e17a210ef8d3c874469c33be34319d11a100d50c54067c62933bc94869de32400ef0d20076809933b694869db32400ed8d20076409003ae04001d74a008efd570077e4a023baf5a01dd7a700ee3d1047618b403b0c4e11d602d00eb013806a4010236c94c01b64a000dd24d0072d8b003a8c5431b362614d9b10006e12b0236a94c01b54a000e949404735e9c0380f4411bb6274ce81921a74069003a004899c44a434e219200710690039c04899cc32434e60d200730091338e64869c71a400e381200724098038ef4839c631e00e30cf00711e88008800801cd92800e5bd380729e920390f4429b362708d9a53a6714c7d338663c69c519f34e18cf0071407c038603c01a801a4cdf24c1a6f8c60037c33011c092800e03d1046c989c0364c4211bf02700df810806f406b336094869b032400d80d2006e9291337264869b91a400dc812006d9290036894001b44a04cd7a4f1a6bcc78035e33c01b07a200d7a4b006b8010037725001b87a700dbbd1006d589c036694e01b24964cd898fa66b4c78d36233e69ad19e00d880f806b407823a325001d37a780e8bd10473d89e2384c4e01cf62180e1310807058720378c3811ac4a700d6250805306787298330c94c19200d400d00564c4872b2324c95901200ad24f0e568c7992b433c01a801a1cd30cc00698648435555c19aa92800d53d1086a46b4335234e01a91a110d38168669c09c034e04299a501880a580c1a69404a729602401a500ce4a58062668d290d34664801a31a400cd81300688090234125001a07a210ce0d3866706853330331699819280cc0c666679278d33c63c019e19e08ce49400671e882336c4e019b6214ccd18c9a668664033403221989280ccc3d100661870732e325019718c90cfc940a685e9e333ef4411a162780d0b10c067d870433a04f21990270cce810c6664084033a037019901b4ccb0095a658032032c00d21e092814f33d3c6781e8823ccc4f01e662180f030e0875409e435604e19d50218cd58108075406e035603601a400480ca80200648020032063c018f00834c9a551a6292640326654018a31900c00d6006446a802e0058018e02a08c6557006324a13076f44698961f00c4a4f8860ccb4330664e017a31f10b98d6865cc69c02a433e018849800c3b0f00544678430f25029887a78cc3bd10462189e0310c43018761c648ba4b0e45cc4042fc34e197e1a100bf0cd8859809c32cc042016601b10c4d570a62a4b63313250118a7ad80c53d3c0625e88030c930391531010be8d6865f469c02fa342216302d0cb18138058c08402aa031015001800af810005786800304948018102400ae8100053c06002fc6241183aae00c1c9404601eb40300f4e017f49ecc1d24b1a5f4c4c02fa326216102d0cb0813805d406a02b6034014e01300a680f0053067802b0034217aaae0cbd494005e9e8842f235a19791a700bc8d08855c0b432ae04e015702100aa00c4052c06002ec340697631800bb0cc1a5dd29002ee64801751a034b6252005b0c9002bc340697232400b90d2005c4090d2d2630696431200b48cc0059064802b4030016e31e00ae00d045b24a002d8f44983949634b39898059064c02d6314016001ab4b29891a594c4802d031c696531800b28cc00594c4802d293c016731e00b31890059067802c4c48696031800b00cc0457a4a002bcf44015d318cc1c1881a57064c02b8026015901a00ac9890056927802b00341173aae00b9c94045c1eb402e0f4e016f49ecc1ba4b1a5b4c7cd2d463c696331300b68cf805a867802c6326116102d00b08138057c06a02b6034015701334aab0f0055527802a863c695161e00a8a4f00530c7842a325019517a200a8b0e0e458c40029e93c014901a10a649406531e880298c38694a31e00a50cf0052406842a555c195292800a93d11a54126002a0630214e1ad0ca70d380538684029a331014b19810a40168652009c0290042218baae14c6c96c662e4a0231af5b018d7a780c5bd1260d9870d30a932018531910c20d6c85f06b4330834f197c1a700c20d0c05f068402f6333017819910ba016c85580b432e804f195602700ba010c055808402a6033014701900a2a551a510ca8028835400f302c00a1815005000980282010013f006009eb131a49cc60d248624012719800920c9004ec05001b60240139324009a813084b64a1306a92c692531300920c9804dc62801b80260135009349a8cf004d40784259250983449634919898048c64c026204e00db0130098002084aeab8028525a013e9280c9e3d6804f18b402749499833496349c1929a4d8c90d24462601381a5009b0d20048864c41f605a01340270086013403bc098026604a013202480978120036804cd25a954012d32a147b0d6004b06a8025525098327a23490b0f8048527c41f464e00d931f0894c94004ade9e0252f44983161c349024c80480c64421c34f20f91a70c870d0c63e468401c833300d8199348f9891a47cc48024c31c011f312008f1890049d290024a648011d31200920d20048c0900238c3c11219280090bd10046d260022862000e3198b48f98f0047c678023c03c111c7a2008e30e1a44d2580226620211b7a2148eb10c646d870223a943011d49b808da4b20464c86f2326376919315b48b9885a444c404232343191919b808c8cac045c62a022231421020218c8100dc040805602326240117498008b0090044d2604226f44191361c0089a4b00448c40422925019147a2008a30e00444c4801c432538e200c90904940a489e9e3240f4411226278091310c0481870023462421181a78c8c0d0c046066e022a315011018a107f813c63fc08601fe03700e1012b48425200420c90d21a648010d1a4348298c1a400c48020a3300100192008518f044224a00210f44983049634819898040064c020e3146901312348098900410638d2026300101198008098900415278020663c010231200800cf0443aab8021d250110c7ad00863d38042d27b305e92c690931f348318f1a3fcc4c021233e010619e007f8c9843f80b401fc04e00e00130079b16003f18a801f525010f67a70076a4f660b9258d1d263e00e919f347c0d2003e009001ea64868f41a4007a012003da4a001e6f4e00f27a2007898f660b4c40d1e033e00f001f0876c94003b5e8821d864e00ec3210075988043a64a001d2f44982c31000740cc8039c01021f325000fb7a7807cbd1043dd89e21dec4e00f76218077b10803b8c6601d4631982b31034730cc80398064d1c6c3c00e349e1071c940638de8801c6c3800e2310346f98f0037c67841c955c18e492800723d11a38526001c263020e01ad0c700d38038068441bc05a18de027006f0109a370c9001b834800d5026006d812043664a001b2f4420d61a70c6b0d08435a4a001acf4410d5627006ab108035187041b125028da7a78c6c3d10436989e01b4c4300d861c106b813c834c09c31ae04318d3021006b80dc034c06c4251250292e7a78c943d1044b989e025cc43012861c4c1524b1a43cc4c021e32620fd0279072813863f408631ca04200fd01b807280d8037404e01a4026235692815b6bd3c6d59e8826dac4f036d62181ab30e260a5258d60e62603071931163013c88f009c358c0431a3c021016300dc08f006c0404027019401300a300240344010319e04000cf01a006700400330ca80154f44388f31e9c1418800324628019b55c00a97a21c659958e328caa7190654388e31e9c139880032c6ac019435500c81aa00470cf4009c628717264800b91a41c5c255002e0ca8014e04c10a7020145380d00318020017e01000c3014005f00400304020417e04c18bf020005f80d0e2f8050017c01c982631034130c50e095258004a62020c40268c620104031006a718402938c0013006100740300034017a01100bc0081c5b255002a0098215004028a801a005c8040e2d0c40016831400b4324005c494002dcc94016c64900b53241c12188002cc628704692c006d31300360c9802c46287044620382131000578c6c02b862a015a31400c5928805dc940e2e8c96716464a38b03249c561920e080c40017434b00b21a500580d2402b069000d631b002018a00540130e2a92a8015465400a70261c54192002a0690014ef4c1899626004ca5300204678010064818a5020005280d081deab8015325a18987ad004c3168e235292703e92c008d324800f988002980b4714802600a400d0c4b3d3002598987142649381e31000508d240078628313e04c009f020103b4940e075258013a04e189c020804e00d401a404c40eb25018957a7004ab138e07125800d0627001c3100051013c028009c713c027389b013004f006c026c0340128c4c00990260049bd30025e4a00124c40381b496000d988002580823126f44009361c1c0d24b00068c405128f4528927a2084a30e44249870012892d00924962c4618fd0230c667118627381931014460cfc42306660118327006718d800c8c5042624a2212b250009861c804ab0e00245280811664b388b3199c0c1880422c6960116333006618d800c0c50023d2a80100024008c626003298c081d2ab8011d25a008d9280c45bd68022d8b4011494938174960032189802246b400be326008818a0042c9400210c92702c6201881020004080d0020004830f8040007c01a1039c940e05525800c6626007e027003e809801ec03240e5250381449600311898021869e010634e0082193802d8c9801fc62a00f431420719280063bd3c02ade9c0146f45009a7a20c483138024129c710e63f387931e9c099880021c67e00f233d005a18d80098c50e049870002492c3876019003b0098e04587000b293200583190039988001de4a200eb25038744a59c392524e04125800e864b0072324802b989c0040c40701ef44005661f8007b0e001c1e88701cc380055499800724b041bde8800e2c43006f61c1c06a4b00150c4e001a620386d4aa00369950011c6b000d8354006a00e00348060019d89800ca94800611a6102cc940018cc40006a314386131e00308cf081624a000ba34e005c18a102bd57001ae4b400d125018667ad00333168e19129470c494800643250031192081346b400c034e00521a680210d30017c69400bc349005b1a400198c50e1658a800b2954284832c002c1950015a4a0409894e0032496082ac940015de9e00aaf44205332790259938614cc863096642003b31080189880414eab800a725010527ad00293d380145e8820a035a00501a7001d0c50011d8b0009cc54004c92808243d380101e88009204800450260022004001224a0008ef4e00467a48021bd1000e0068208125000407a2081f813800fc084007c035104b9280026bd3c012de882094c4f10426270025310c01098840082c39003d61c001c00d0e0e5278007263c003819a101dd57060ee4a00076f44203a32d0c1d193800e8c84406e05a1837027001b8108e0d5290006a648002d026001a012040ca4a00064f44202e1a70c170d08e0c1278006063c102e92800173d1040b589c005ac42382c31900160cc880c64a05066f4f18317a20819b13c00cd8860062c38202f0279015813860bc0863056042002f01b801580d881524a050b4f4f18547a2082d313c016988600a8c38204f1a7901e0d38613c6863078342004f19b801e0cd800d862a0054314002832a3413007000980200044620002592800121928008cc920042648000c31010094940606de9c0036c4e000b496000f0138007404c0034c40281a7a2080d30e000692580014620101b928000db0e0006528000126202011928000b19380054c40402125000277a780103d38007de8a0038f441818627000c2538005cc7e002863d0008310000949400045292000e92c00067a20007bd100015870201cf440010621800730e000112580014940200792800063d38002de883012c4e00094a700033d104015e88000ec43000561c10023d10a0218863008c3810084a1800424dc0011258401af4428136218c06b0e0404d2860026937000d4960001988081b9e8850f0c43186e61c083c250c01e126e00dc92c380231000148c6c00086284882f442c5a6218e20b0e0516928608b493704414964c0098832340636d00231438d000d8068003c0004010000003f
  18 6 13 11 5 7
def FinalData : Forest := fun i => decodeNode 11 24 0x1a592aaed7402cd8602c58e02058e01ad8601a58601a58a00e58a008d8602658701a587007586aae57402bd7401a583aae57c32a5811ab57c1aad7c1aa57c1aa57d00457c02b57400457a02ad74193578007d75004d7500457502a5747a7c5b02057201ad6a1aa56c02456f01a56c02456d00e56c008d6a00756a928d25020d6801ad5a01ad6301456500ed6300e563008d5a1a055f19455f02055f007d5a01ad5b01455c00ed5b00755a928525aae55632ad56004556025d25928d3701ad4e01a55101455100ed4e00854f00d54e9285371a5d37928548325548324d483245481a553718a5461a4d37312544009d431a45374aa54032a540007d3732a53e004d3732453c1a55381a4d3818a5391a453800453702552500dd2f00c534004d2f00d53001a531006d3000452f024d2519352c00452c007d2618d52900d529004d26007d270045260245257a745b1b052392dd0132a5211ab51d1aad1d18a51e1aa51d92d5011aa51b92c51a02dd0102a5187a6d101a4516025513024d130245137a651001a51102ad1002d50102050e007d0132a50b1aa50b92d5021a45080245087a650702d50202050501ad0249650301a5020075017a2c5b1a04ff1aacfe027ce7025cfa0044fb024cfa0274e71ad4f21934f202d4f20264f5020cf261c4f30204f2007ce7027ce89284ee1a4cee0274e861c4eb020ceb01ace80204e900dce80074e77a245b026cdf0264df02c4e00264e04a44e101a4e00074df61ccc90204dd928cd49284d49284da020cd402c4d50264d56244d60204d5007cd461c4c90204d20074d1496cca61cccb7a24ce61c4cb0204cc007ccb4964ca4a04c94a745b3304c792dc8a0204c40084c4aae4b94aa4c232b4b932acb93104ba18d4ba3124bb18c4bc0064bb00f4ba32a4b992d48a928c8a02d4b20084b50134b20204b300ccb292848aaae4aa7a24aa7a24ad61c4ad6264aa6264ab1ab4aa62d48a62aca8325c8a7a64a67ad4a5324c8a02dc8aaae49d0264a17a249d1aac9d32a49e19ec9d02d48a62ac9a19949a00dc8a01a49800c497004c8a32a49402a49492d48b62649262d48b324c8b7aa48f02d48b00d48b01a48c006c8b00448a01fc5baae48732ac87027c5c928c7f026c8300d48392847f1a5c7f18a4801a4c7f02745c1ad47919947902d47900c47a00447900dc5c1ad46b19346b19a4751aa47302647302d46b01346b02047000cc6b01ac6c49646d01a46c00c46b004c5c19a4691aa468027c5d1a4c6502546502745d00dc5d02746200d45d01ac5e49645f01a45e006c5d00445c01ec5b49b80102045900d458928c4502645600dc53020c5400d453928445aae44f4aac4f18a44f1a5c45193c4602044c19244b18ac4619344702044818cc4718a4461a4c45621c427a244361c4424960014b0c3b31243f19343e4b043b1b043b03043b92db6e008438006438aae41c4ab41c0144354aac1c49642d31243219342d00c43001542d01a42e01342d4aa41c4aa42a32a42a1ab41c18a4281aa41c32442632a42232442232442302442202d41c4aa42002b41c02ac1c00441d02a41c92d36e00841801a419006418928b6e02a41602d409008414019409009409008c0901341000840900740902040d006c0902740a01ac0a00640992836e7a240561c40662640562d36e7ac4037b33fd1b04014b33fd3123ff1933fd0143fd4a5b6e1aa3fa02a3fa4ad3ea0083f70063f74963ea3123f51933ea00c3f30153ea014bea3183f04a4bed0263ee4963ed0143ea02c3eb0133ea4a4b6e4aa3e732a3e792d3d49283d46263e462d3d44a5bd47a63e17ad3de3133de0143de4a4bd44a4bdc3253d46203da6273d93243d44aa3d7193bd43243d518a3d41a536e02a3d21a7bc7193bc70123cd01a3ce0063cd18abc70133c800cbc801a3c9006bc818a3c71a436e1923c54aabbc3123c31933c24aa3bc3123c04a4bbd3133be4a43bd1a43bc027b6e92ab9102c3b801a3b892839132a3b502a3b57ad3917a23914a63b24ad39192a3b0325391324b913243ac0243ac7a73a77a23a74a03a94a73a73103a732439131eb913243a231e3a319e3a201f3917a4b9200839f7a23924a039d4a73927a439b31f39231eb9249a3984a139631039631e39231e39301e39300439201e39102736e62ab8a4a4b8b31238d19338c4a438b1ac38a025b6e4aa3871aa38792d38092838062638462d3804a4b8002d38000438002536e02d37c00c37d00437c024b6e027b6f928378324b7802736f02c376013b6f00c374004b6f027370013370006b7000436f02436e6218d100e36b00c36baae35a01836919a36862ab5a4aa36632b35a31036432a35a4aa35f4a43611a435f02a35f1ad35a1ab35a1aab5a18a35b1aa35a7a7b579283587a235761c0d133035403035492db2918e35232a35002a35092d329928b2900834d92832962634962634a02b34962d32962634762d3404a53406203446273434a434031e34118e340325329312b3831033818f33818eb3819eb3918a33918e3383243293123364aa3334a4334324333027b2962a32f4a43301ac32f025b294a432d025329024b2900432a024329621b083143274aa3251aa3257a7b229283237a232261c30802a3207a7b0f02431e7a730f7a2b0f00831b7a230f4a03174a03180253174a730f021b0f1a631401fb0f01f30f01eb0f00431001e30f49bb091a430d621b0a7a230b61c30a4963093123081930d17b03041b030403030492dac7aae3029282c74aa3007a7ac702a2feaae2ed4aa2fc92d2ed92aaed02c2f99282ed92a2f74a52ed1922f54a4aed9282ee4962ee3122f11932ee00c2ef0152ee4a42ed7a72c77a2ac79282e50272e531e2e8020ae50082e60192e57a22c749fac792dade9282de1a42e04a72de4962de49eac77b02dc92dad09282d03122d94a42d87a72d07a22d062a2d57a7ad17a22d16212d161c2d13122d01932c7027ac7aae2c832a2cc62d2c861c2c84a42c9318ac80272c701b8d10202c401e2c4aae2ba32a2c262d2ba62b2ba62aaba61c2be62a2ba3202bb31a2bb32aaba7a7a3d9282b87a223d02a2b6aae2a732a2b492d2a792aaa702c2b001a2b09282a762d2a792a2ad3252a7324aa79282a86272a83102a83242a7621a3d0252a40242a492827532a2a27a7a7592829c32529c324a9c31029d32429c7a72757a4a7501a29992a29702c2977a2a7592828c02728c026a8c7a229202628c01aa8c02628f014a8c02628d01328c7a227592a28a31fa750242889282807a72807a4a807a42800262837a22807a428131028031f27592827c32727c31027c31ea757a2276321a76310a767a227731027631e27562123d92826c4a42727a726c31e27062026f02726c01aa6c01326c61ca3d02a26a7a7a589282687a2258021a589282637a726331ea630212587a226019926001aa581a025d02025d013a587a225902125901aa5901325861c23d9282527a72527a2252327252310252319a3d4aa24f32a24f7a7a3e92824d7a223e321a3e9282450242497a72457a224532424662724532123e018243310a3e7a223f02123f012a3f31023e318a3d01b0d17ac23b7b322c62b22c19a23862a22c62a2354aa23532b22c32a22c62a2321ab22c1aa22c03222f02b22c02c22d02a22c7a7a0392822a7a22031a1a039282247a72240082257a22241a12037ad22062622102d220021a037b021e92da139282134a421a1a421a7a72137a22134a42151a4215024215627213027213021203012211004a037a220401e20e1a120419e20b01e20b021204018a0419820719220700ca0461c20500c2040042030138d11aa20002a20092d1e70081fd0061fd9281e76261fb62d1e73241f91a51e718a1f60091f61a41e70241f219e1f301e1f20271e702c1f00251e702c1ee0249e70271e80269e87a21ea0261e80041e80241e762199532a1e41aa1e47a79e19281e27a21e161c1959281d61a41de7a71d67a21d61a41d90261da0241d96271d64a01d70271d601b99562a1d47a79ac9281d27a21ac0241d06219ac0241ce9281c30241cc7a71c37a49c30261c97a21c37a41c619e1c601f1c37a21c401e1c36211ac61c9ac7a21bd0211bd1981be01a9bd61c1ac9281ad4a41b90241b97a71ad7a21ad4a41b66271ad4a01b44a71ad4961ad01f1ad7a21ae4961ae0041ae01e1ad4a11ac01b1957a21a51a11a501a1a80211a51921a600c9a50049951a41a20241a26219967a21a061c19619e19e01b9967a219a62119a01919a01b19661c19718c9970069960041950130d132a18e0081921aa18e31e19000818f02a18e7a794792818c7a21477a79867a218662198761c1874981863191471a194792817d4a41810241817a717d49e97d31217e19317d1a11471999477a21791a11791991473241751981761a01750219479281571a41710241717a715749e95731e16e19f1577a216b18a16b19e15749e16418e16831e16431216431216519e16419315762416202715719816001a9577a215c31895c01315c01a15749e15831215901a15801315702114749e15431e1540199477a214861c15131814849e14f1a114819894861c14c19814819e14901a1490211480191470048d14aa1431aa14302a14392d12f00813f02614000613f92812f62613d62d12f01413b4a492f3241391a512f18a1371a412f01e13502712f02512f02492f02713000413002412f6218d232a12c1aa12c7a792992812a7a212961c0d24a412318e1263241231a41230241236219107a212161c11019e11e01e11e49b91b61c11c49611b31211031211919b91049811601211618a91061c11149611231011231211118a1101930d29280fe1a410d7a70fe49e8fe31e10a19f0fe7a210718a10719e0fe49e10018e10431e10031210031210119e1001930fe0270fe01b8d262a0fc7a78e69280fa7a20e60240f86218e69280f03240f40240f47a70f07a20f031e8f001f0f06210e63198e67a20eb3210eb3100eb3188e67a20e71990e70040e70190e601b0d27a20de61c0e23100e23180de1a10de19e0df0210de0138d21a40db0240db6218d37a20d961c0d301b8d37a20d46210d461c0d401b0d30130d20040d100780101a0ce0080ceaae0c832a0cc1ab0c81aa8c818a0c91aa0c87a78790080c69288ac01a8bc0140c300e8bc0080c100d0bc01a0be00e0be0088bc0080bc9280ac1a58ac0080b99280b33250b33248b33240b33240b418a0b31a50ac18a0b11a48ac18d8ad18a8ad18a0ad1a40ac7a707932a0aa92d0a41a40a87a60a702d0a401a0a500d0a47a287902789b1a48a102709b02009f00d89b02709c01a89c00d09b7a207902609961c89192809602089661c09149689261c0934960924a00914a70794aa08f92d08892808862608c62d0884a48881ad08818a08819f8791a787a9280843248841a707a19387a01a08101208018a87a02707b01307b01a07c00c87b18a07a19e87949b80292887201307692807232587231007332487262186f7a207061c06f49600232a06c1aa06c92d05b00e06900c06992805b62606762d05b4a406532505b31006332405b19e0611a705b1a505b1a485b1a705c18a05c1a405b62182a4aa05832a0587a78559280567a205561c02a9280507a70507a20501a705019b82a62a04e7a783d92804c7a203d62183d0240499280437a70437a48430260440080447a204362103d61c83d7a203e02103e01a83e61c03d19b02a7a203732103731e03819a03802103718a82a32403402403462182b7a203261c02b31e03001b82b7a202c62102c19902c01b02b18a02a18d80232a0287a78140080269280213250213248213100223240217a70147a281402701d01301d7a201461c01949601a4a00194a701431f81432701531001531e81449b8039280114a481162180e7a200f61c00e4960037a70097a20094a000a4a700949b8046218057a200661c00549600431000318a00200400101f800 i
def FinalStates := dagTrace FinalMask FinalStock 12 FinalData
def FinalTags := dagTraceTags FinalMask 54
  (dagTagBases FinalStock 0xffc387f0fe1fc387f1de3bc778e1c3bfe6dcdb9b76eddbffeadd5bb76edd5bffeaddbb76eadd5bfff 0x1c387f0fe1fc38001de3bc778e1c38066dcdb9b76edda002add5bb76edd5b000addbb76eadd5b800 54) 12 FinalData
def FinalCheck := dagCheckNode FinalMask FinalGoal FinalChart (dagKnownCloses FinalGoal FinalCuts)
  1427 FinalStates FinalMoves FinalLinks FinalSample FinalTags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalRoots : dagCheckRoots FinalMask FinalGoal FinalChart (dagKnownCloses FinalGoal FinalCuts) FinalWitnesses (dagRef 1427 FinalStates FinalMoves FinalLinks 0) FinalStock 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes0 : treeBlock 0 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes16 : treeBlock 16 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes32 : treeBlock 32 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes48 : treeBlock 48 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes64 : treeBlock 64 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes80 : treeBlock 80 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes96 : treeBlock 96 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes112 : treeBlock 112 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes128 : treeBlock 128 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes144 : treeBlock 144 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes160 : treeBlock 160 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes176 : treeBlock 176 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes192 : treeBlock 192 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes208 : treeBlock 208 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes224 : treeBlock 224 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes240 : treeBlock 240 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes256 : treeBlock 256 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes272 : treeBlock 272 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes288 : treeBlock 288 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes304 : treeBlock 304 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes320 : treeBlock 320 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes336 : treeBlock 336 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes352 : treeBlock 352 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes368 : treeBlock 368 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes384 : treeBlock 384 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes400 : treeBlock 400 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes416 : treeBlock 416 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes432 : treeBlock 432 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes448 : treeBlock 448 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes464 : treeBlock 464 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes480 : treeBlock 480 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes496 : treeBlock 496 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes512 : treeBlock 512 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes528 : treeBlock 528 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes544 : treeBlock 544 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes560 : treeBlock 560 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes576 : treeBlock 576 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes592 : treeBlock 592 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes608 : treeBlock 608 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes624 : treeBlock 624 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes640 : treeBlock 640 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes656 : treeBlock 656 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes672 : treeBlock 672 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes688 : treeBlock 688 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes704 : treeBlock 704 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes720 : treeBlock 720 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes736 : treeBlock 736 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes752 : treeBlock 752 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes768 : treeBlock 768 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes784 : treeBlock 784 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes800 : treeBlock 800 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes816 : treeBlock 816 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes832 : treeBlock 832 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes848 : treeBlock 848 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes864 : treeBlock 864 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes880 : treeBlock 880 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes896 : treeBlock 896 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes912 : treeBlock 912 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes928 : treeBlock 928 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes944 : treeBlock 944 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes960 : treeBlock 960 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes976 : treeBlock 976 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes992 : treeBlock 992 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1008 : treeBlock 1008 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1024 : treeBlock 1024 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1040 : treeBlock 1040 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1056 : treeBlock 1056 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1072 : treeBlock 1072 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1088 : treeBlock 1088 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1104 : treeBlock 1104 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1120 : treeBlock 1120 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1136 : treeBlock 1136 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1152 : treeBlock 1152 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1168 : treeBlock 1168 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1184 : treeBlock 1184 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1200 : treeBlock 1200 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1216 : treeBlock 1216 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1232 : treeBlock 1232 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1248 : treeBlock 1248 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1264 : treeBlock 1264 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1280 : treeBlock 1280 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1296 : treeBlock 1296 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1312 : treeBlock 1312 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1328 : treeBlock 1328 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1344 : treeBlock 1344 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1360 : treeBlock 1360 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1376 : treeBlock 1376 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1392 : treeBlock 1392 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1408 : treeBlock 1408 16 FinalCheck = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem FinalNodes1424 : treeBlock 1424 3 FinalCheck = true := by decide +kernel
theorem FinalAll : treeBlock 0 1427 FinalCheck = true := (@treeBlock_merge 0 720 707 FinalCheck (@treeBlock_merge 0 352 368 FinalCheck (@treeBlock_merge 0 176 176 FinalCheck (@treeBlock_merge 0 80 96 FinalCheck (@treeBlock_merge 0 32 48 FinalCheck (@treeBlock_merge 0 16 16 FinalCheck FinalNodes0 FinalNodes16) (@treeBlock_merge 32 16 32 FinalCheck FinalNodes32 (@treeBlock_merge 48 16 16 FinalCheck FinalNodes48 FinalNodes64))) (@treeBlock_merge 80 48 48 FinalCheck (@treeBlock_merge 80 16 32 FinalCheck FinalNodes80 (@treeBlock_merge 96 16 16 FinalCheck FinalNodes96 FinalNodes112)) (@treeBlock_merge 128 16 32 FinalCheck FinalNodes128 (@treeBlock_merge 144 16 16 FinalCheck FinalNodes144 FinalNodes160)))) (@treeBlock_merge 176 80 96 FinalCheck (@treeBlock_merge 176 32 48 FinalCheck (@treeBlock_merge 176 16 16 FinalCheck FinalNodes176 FinalNodes192) (@treeBlock_merge 208 16 32 FinalCheck FinalNodes208 (@treeBlock_merge 224 16 16 FinalCheck FinalNodes224 FinalNodes240))) (@treeBlock_merge 256 48 48 FinalCheck (@treeBlock_merge 256 16 32 FinalCheck FinalNodes256 (@treeBlock_merge 272 16 16 FinalCheck FinalNodes272 FinalNodes288)) (@treeBlock_merge 304 16 32 FinalCheck FinalNodes304 (@treeBlock_merge 320 16 16 FinalCheck FinalNodes320 FinalNodes336))))) (@treeBlock_merge 352 176 192 FinalCheck (@treeBlock_merge 352 80 96 FinalCheck (@treeBlock_merge 352 32 48 FinalCheck (@treeBlock_merge 352 16 16 FinalCheck FinalNodes352 FinalNodes368) (@treeBlock_merge 384 16 32 FinalCheck FinalNodes384 (@treeBlock_merge 400 16 16 FinalCheck FinalNodes400 FinalNodes416))) (@treeBlock_merge 432 48 48 FinalCheck (@treeBlock_merge 432 16 32 FinalCheck FinalNodes432 (@treeBlock_merge 448 16 16 FinalCheck FinalNodes448 FinalNodes464)) (@treeBlock_merge 480 16 32 FinalCheck FinalNodes480 (@treeBlock_merge 496 16 16 FinalCheck FinalNodes496 FinalNodes512)))) (@treeBlock_merge 528 96 96 FinalCheck (@treeBlock_merge 528 48 48 FinalCheck (@treeBlock_merge 528 16 32 FinalCheck FinalNodes528 (@treeBlock_merge 544 16 16 FinalCheck FinalNodes544 FinalNodes560)) (@treeBlock_merge 576 16 32 FinalCheck FinalNodes576 (@treeBlock_merge 592 16 16 FinalCheck FinalNodes592 FinalNodes608))) (@treeBlock_merge 624 48 48 FinalCheck (@treeBlock_merge 624 16 32 FinalCheck FinalNodes624 (@treeBlock_merge 640 16 16 FinalCheck FinalNodes640 FinalNodes656)) (@treeBlock_merge 672 16 32 FinalCheck FinalNodes672 (@treeBlock_merge 688 16 16 FinalCheck FinalNodes688 FinalNodes704)))))) (@treeBlock_merge 720 352 355 FinalCheck (@treeBlock_merge 720 176 176 FinalCheck (@treeBlock_merge 720 80 96 FinalCheck (@treeBlock_merge 720 32 48 FinalCheck (@treeBlock_merge 720 16 16 FinalCheck FinalNodes720 FinalNodes736) (@treeBlock_merge 752 16 32 FinalCheck FinalNodes752 (@treeBlock_merge 768 16 16 FinalCheck FinalNodes768 FinalNodes784))) (@treeBlock_merge 800 48 48 FinalCheck (@treeBlock_merge 800 16 32 FinalCheck FinalNodes800 (@treeBlock_merge 816 16 16 FinalCheck FinalNodes816 FinalNodes832)) (@treeBlock_merge 848 16 32 FinalCheck FinalNodes848 (@treeBlock_merge 864 16 16 FinalCheck FinalNodes864 FinalNodes880)))) (@treeBlock_merge 896 80 96 FinalCheck (@treeBlock_merge 896 32 48 FinalCheck (@treeBlock_merge 896 16 16 FinalCheck FinalNodes896 FinalNodes912) (@treeBlock_merge 928 16 32 FinalCheck FinalNodes928 (@treeBlock_merge 944 16 16 FinalCheck FinalNodes944 FinalNodes960))) (@treeBlock_merge 976 48 48 FinalCheck (@treeBlock_merge 976 16 32 FinalCheck FinalNodes976 (@treeBlock_merge 992 16 16 FinalCheck FinalNodes992 FinalNodes1008)) (@treeBlock_merge 1024 16 32 FinalCheck FinalNodes1024 (@treeBlock_merge 1040 16 16 FinalCheck FinalNodes1040 FinalNodes1056))))) (@treeBlock_merge 1072 176 179 FinalCheck (@treeBlock_merge 1072 80 96 FinalCheck (@treeBlock_merge 1072 32 48 FinalCheck (@treeBlock_merge 1072 16 16 FinalCheck FinalNodes1072 FinalNodes1088) (@treeBlock_merge 1104 16 32 FinalCheck FinalNodes1104 (@treeBlock_merge 1120 16 16 FinalCheck FinalNodes1120 FinalNodes1136))) (@treeBlock_merge 1152 48 48 FinalCheck (@treeBlock_merge 1152 16 32 FinalCheck FinalNodes1152 (@treeBlock_merge 1168 16 16 FinalCheck FinalNodes1168 FinalNodes1184)) (@treeBlock_merge 1200 16 32 FinalCheck FinalNodes1200 (@treeBlock_merge 1216 16 16 FinalCheck FinalNodes1216 FinalNodes1232)))) (@treeBlock_merge 1248 96 83 FinalCheck (@treeBlock_merge 1248 48 48 FinalCheck (@treeBlock_merge 1248 16 32 FinalCheck FinalNodes1248 (@treeBlock_merge 1264 16 16 FinalCheck FinalNodes1264 FinalNodes1280)) (@treeBlock_merge 1296 16 32 FinalCheck FinalNodes1296 (@treeBlock_merge 1312 16 16 FinalCheck FinalNodes1312 FinalNodes1328))) (@treeBlock_merge 1344 48 35 FinalCheck (@treeBlock_merge 1344 16 32 FinalCheck FinalNodes1344 (@treeBlock_merge 1360 16 16 FinalCheck FinalNodes1360 FinalNodes1376)) (@treeBlock_merge 1392 16 19 FinalCheck FinalNodes1392 (@treeBlock_merge 1408 16 3 FinalCheck FinalNodes1408 FinalNodes1424)))))))
theorem floorFinal : Lower FinalMask FinalStock FinalGoal 13 := by
  apply lowerDag (chart := FinalChart) _ _ _ _ FinalAutos _ _ _ FinalKnown _ FinalRoots FinalAll
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def f (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3907577984 * 2 ^ 32 + 3900735488)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

private def mono : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [6, 8]⟩,
    ⟨.and, [6, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [12, 5]⟩,
    ⟨.or, [11, 13]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [9, 14]⟩, ⟨.and, [10, 15]⟩,
    ⟨.or, [16, 17]⟩], 18⟩

private theorem monoValid : Monotone2 mono := by
  simp [mono, Monotone2]

private theorem monoSize : mono.size = 13 := rfl

set_option maxHeartbeats 1000000 in
private theorem monoComputes : ∀ x : Fin 6 → Bool, mono.eval (List.ofFn x) = f x := by
  decide +kernel

theorem oppositeOfLower (lower : ∀ s, HasCircuitSize 6 f s → 13 ≤ s) :
    ∀ s, HasCircuitSize 6 f s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x := by
  intro s h
  exact ⟨mono, monoValid, monoSize ▸ lower s h, monoComputes⟩


theorem main : ∀ s, HasCircuitSize 6 f s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
    ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x := by
  apply oppositeOfLower
  intro s hs
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
  let goal : BitVec 64 := 0xe8e8e880e8808000
  exact hcsLower (n := 6) raw goal 13 f (by decide +kernel) (by decide +kernel) floorFinal s hs

end PEqualNP.Outside.L_meta_12226

theorem PEqualNP.Outside.L_meta_12226 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3907577984 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3907577984 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_12226.main
