import PEqualNP.Defs
-- The displayed circuit has eleven gates. To match it, a circuit using
-- a negation needs at least ten binary gates. The proof examines its first
-- binary gate, restricts one of its inputs, and saves a second gate because
-- two assignments still have to be distinguished.
-- Two five-input functions remain. Their eight-gate lower bounds are checked
-- below by enumerating which wires a smaller circuit could still use.
-- Search framework adapted from L-meta-10880 and its credited contributors.
namespace PEqualNP.Outside.L_meta_12316
abbrev Fn (X : Type) := X → Bool
abbrev Pool (X : Type) := Fn X → Prop
def inv {X : Type} (f : Fn X) : Fn X := fun x => !(f x)
def both {X : Type} (f g : Fn X) : Fn X := fun x => f x && g x
def extend {X : Type} (R : Pool X) (f : Fn X) : Pool X := fun g => R g ∨ g=f ∨ g=inv f
def Stable {X : Type} (R : Pool X) : Prop :=
  (∀ b : Bool, R (fun _ => b)) ∧ ∀ g, R g → R (inv g)
theorem doubleInv {X : Type} (g : Fn X) : inv (inv g) = g := by funext x; simp [inv]
theorem stableExt {X : Type} {R : Pool X} (st : Stable R) (f : Fn X) : Stable (extend R f) := by
  refine ⟨fun b => Or.inl (st.1 b),?_⟩
  intro g h
  rcases h with h|rfl|rfl
  · exact Or.inl (st.2 g h)
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (doubleInv f))
def Can {X : Type} (f : Fn X) : ℕ → Pool X → Prop
  | 0, R => R f
  | k+1, R => Can f k R ∨ ∃ a b, R a ∧ R b ∧ Can f k (extend R (both a b))
theorem Can.ready {X : Type} {f : Fn X} {R : Pool X} (h : R f) : Can f 0 R := h
theorem Can.skip {X : Type} {f : Fn X} {R : Pool X} {k : ℕ} (h : Can f k R) : Can f (k+1) R :=
  Or.inl h
theorem Can.gate {X : Type} {f : Fn X} {k : ℕ} {R : Pool X} (a b : Fn X) (ha : R a) (hb : R b)
    (h : Can f k (extend R (both a b))) : Can f (k+1) R := Or.inr ⟨a,b,ha,hb,h⟩
theorem Can.ind {X : Type} {f : Fn X} {motive : ∀ k R, Can f k R → Prop}
    (ready : ∀ {R : Pool X} (hf : R f), motive 0 R (Can.ready hf))
    (skip : ∀ {k : ℕ} {R : Pool X} (h : Can f k R), motive k R h → motive (k+1) R (Can.skip h))
    (gate : ∀ {k : ℕ} {R : Pool X} (a b : Fn X) (ha : R a) (hb : R b)
      (h : Can f k (extend R (both a b))), motive k (extend R (both a b)) h →
      motive (k+1) R (Can.gate a b ha hb h))
    {k : ℕ} {R : Pool X} (h : Can f k R) : motive k R h := by
  induction k generalizing R with
  | zero => exact ready h
  | succ k ih =>
    rcases h with old|⟨a,b,ha,hb,tail⟩
    · exact skip old (ih old)
    · exact gate a b ha hb tail (ih tail)

open PEqualNP.CircuitLowerBounds

def useBinary (g : Gate) := match g.op with | .not => false | _ => true
def cost (gs : List Gate) := (gs.filter useBinary).length
def readF {X : Type} (w : List (Fn X)) (i : ℕ) : Fn X := w.getD i (fun _ => false)
def outF {X : Type} (w : List (Fn X)) (g : Gate) : Fn X :=
  fun x => g.op.eval (g.inputs.map (fun i => readF w i x))
def traceF {X : Type} (gs : List Gate) (w : List (Fn X)) : List (Fn X) :=
  gs.foldl (fun old g => old ++ [outF old g]) w
def fan (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem readIn {X : Type} {w : List (Fn X)} {R : Pool X} (st : Stable R)
    (hw : ∀ u ∈ w, R u) (i : ℕ) : R (readF w i) := by
  by_cases h : i < w.length
  · rw [readF,List.getD_eq_getElem _ _ h]; exact hw _ (List.getElem_mem _)
  · rw [readF,List.getD_eq_default _ _ (by omega)]; exact st.1 false

theorem gateClass {X : Type} (w : List (Fn X)) (g : Gate) (hg : fan g) (R : Pool X)
    (st : Stable R) (hw : ∀ u ∈ w, R u) :
    if useBinary g then R (outF w g) ∨
      ∃ a b, R a ∧ R b ∧ (outF w g = both a b ∨ outF w g = inv (both a b))
    else R (outF w g) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨hop,len⟩ := hg
  change (op = .and ∨ op = .or ∨ op = .not) at hop
  change ins.length ≤ 2 at len
  rcases hop with rfl|rfl|rfl
  · change R _ ∨ _
    cases ins with
    | nil => exact Or.inl (st.1 true)
    | cons i t =>
      cases t with
      | nil =>
        apply Or.inl
        convert readIn st hw i using 1
        funext x
        simp [outF,GateOp.eval]
      | cons j t =>
        have hnil : t=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        subst t
        exact Or.inr ⟨readF w i,readF w j,readIn st hw i,readIn st hw j,Or.inl (by funext x; simp [outF,GateOp.eval,both])⟩
  · change R _ ∨ _
    cases ins with
    | nil => exact Or.inl (st.1 false)
    | cons i t =>
      cases t with
      | nil =>
        apply Or.inl
        convert readIn st hw i using 1
        funext x
        simp [outF,GateOp.eval]
      | cons j t =>
        have hnil : t=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        subst t
        refine Or.inr ⟨inv (readF w i),inv (readF w j),st.2 _ (readIn st hw i),
          st.2 _ (readIn st hw j),Or.inr ?_⟩
        funext x
        simp [outF,GateOp.eval,inv,both]
  · cases ins with
    | nil => exact st.1 true
    | cons i t => exact st.2 _ (readIn st hw i)

theorem comp {X : Type} (gs : List Gate) (o : ℕ) (legal : ∀ g ∈ gs, fan g)
    (w : List (Fn X)) (R : Pool X) (st : Stable R) (hw : ∀ u ∈ w, R u) :
    Can (readF (traceF gs w) o) (cost gs) R := by
  induction gs generalizing w R with
  | nil => exact Can.ready (readIn st hw o)
  | cons g gs ih =>
    have cont := ih (fun u hu => legal u (List.mem_cons_of_mem _ hu))
    have cl := gateClass w g (legal g List.mem_cons_self) R st hw
    change Can (readF (traceF gs (w ++ [outF w g])) o) _ R
    have same (h : R (outF w g)) : Can (readF (traceF gs (w ++ [outF w g])) o) (cost gs) R := by
      apply cont _ R st
      intro z hz
      rcases List.mem_append.mp hz with hz|hz
      · exact hw z hz
      · obtain rfl := List.mem_singleton.mp hz
        exact h
    cases hb : useBinary g with
    | false =>
      simp only [hb, Bool.false_eq_true, ite_false] at cl
      simpa [cost,hb] using same cl
    | true =>
      simp only [hb,ite_true] at cl
      have len : cost (g::gs)=cost gs+1 := by simp [cost,hb]
      rw [len]
      rcases cl with h|⟨a,b,ha,hb',eq⟩
      · exact Can.skip (same h)
      · apply Can.gate a b ha hb'
        apply cont _ _ (stableExt st _)
        intro z hz
        rcases List.mem_append.mp hz with hz|hz
        · exact Or.inl (hw z hz)
        · obtain rfl := List.mem_singleton.mp hz
          exact Or.inr eq

theorem readAt {X : Type} (w : List (Fn X)) (i : ℕ) (x : X) :
    (w.map (fun z => z x)).getD i false = readF w i x := by
  by_cases h : i < w.length
  · simp [readF,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
  · simp [readF,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_none (by omega : w.length ≤ i)]

theorem traceAt {X : Type} (gs : List Gate) (w : List (Fn X)) (x : X) :
    (traceF gs w).map (fun z => z x) =
      gs.foldl (fun old g => old ++ [g.op.eval (g.inputs.map (fun i => old.getD i false))])
        (w.map (fun z => z x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (traceF gs (w ++ [outF w g])).map _ = _
    rw [ih,List.foldl_cons]
    simp only [List.map_append,List.map_cons,List.map_nil,outF,readAt]


abbrev BaseX := Fin 6 → Bool
open PEqualNP.MetaComplexity
def f (x : Fin 6 → Bool) : Bool := Nat.testBit (4276682240 * 2 ^ 32 + 4261412864)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [3, 11]⟩, ⟨.and, [7, 13]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [14, 15]⟩], 16⟩

theorem witnessSize : witness.size = 11 := rfl

theorem witnessMonotone : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem computes : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = f x := by decide +kernel

def prim (z : Fn BaseX) : Prop :=
  (∃ b : Bool, z=fun _ => b) ∨ ∃ i : Fin 6, z=(fun x => x i) ∨ z=inv (fun x => x i)
theorem stablePrim : Stable prim := by
  refine ⟨fun b => Or.inl ⟨b,rfl⟩,?_⟩
  intro z h
  rcases h with ⟨v,rfl⟩|⟨i,rfl|rfl⟩
  · exact Or.inl ⟨!v,rfl⟩
  · exact Or.inr ⟨i,Or.inr rfl⟩
  · exact Or.inr ⟨i,Or.inl (doubleInv _)⟩

def projFn {X Y : Type} (p : Y → X) (f : Fn X) : Fn Y := fun y => f (p y)

theorem mapProj {X Y : Type} {f : Fn X} {k : ℕ} {S : Pool X}
    (h : Can f k S) (p : Y → X) (R : Pool Y) (st : Stable R)
    (hr : ∀ z, S z → R (projFn p z)) : Can (projFn p f) k R := by
  induction h using Can.ind generalizing R with
  | ready hf => exact .ready (hr _ hf)
  | skip _ ih => exact .skip (ih R st hr)
  | gate a b ha hb _ ih =>
    apply Can.gate (projFn p a) (projFn p b) (hr a ha) (hr b hb)
    apply ih _ (stableExt st _)
    intro z hz
    rcases hz with hz|rfl|rfl
    · exact Or.inl (hr _ hz)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

def Good {X Y : Type} (p : Y → X) (u v : X) (R : Pool Y) (z : Fn X) : Prop :=
  z u = z v ∧ R (projFn p z)
def Fixed {X Y : Type} (p : Y → X) (z : Fn X) : Prop := ∃ c : Bool, projFn p z = fun _ => c

theorem guardInv {X Y : Type} {p : Y → X} {u v : X} {R : Pool Y} (st : Stable R) {z : Fn X}
    (hz : Good p u v R z ∨ Fixed p z) : Good p u v R (inv z) ∨ Fixed p (inv z) := by
  rcases hz with ⟨eq,hr⟩ | ⟨c,hc⟩
  · exact Or.inl ⟨congrArg Bool.not eq,st.2 _ hr⟩
  · exact Or.inr ⟨!c,congrArg inv hc⟩

theorem saveGate {X Y : Type} {f : Fn X} {S : Pool X} {k : ℕ}
    (h : Can f k S) (p : Y → X) (u v : X) (diff : f u ≠ f v)
    (nc : ¬ Fixed p f) (R : Pool Y) (st : Stable R)
    (hs : ∀ z, S z → Good p u v R z ∨ Fixed p z) :
    ∃ t, t+1 ≤ k ∧ Can (projFn p f) t R := by
  have val {Q : Pool Y} (sq : Stable Q) {z : Fn X}
      (hz : Good p u v Q z ∨ Fixed p z) : Q (projFn p z) := by
    rcases hz with ⟨_,ok⟩ | ⟨c,hc⟩
    · exact ok
    · rw [hc]; exact sq.1 c
  induction h using Can.ind generalizing R with
  | ready hf =>
    rcases hs _ hf with ⟨same,_⟩|hc
    · exact (diff same).elim
    · exact (nc hc).elim
  | skip _ ih =>
    obtain ⟨t,sz,pr⟩ := ih R st hs
    exact ⟨t,by omega,pr⟩
  | @gate k S a b ha hb rest ih =>
    have aa := hs _ ha
    have bb := hs _ hb
    have save (ok : R (projFn p (both a b))) : ∃ t, t+1 ≤ k+1 ∧ Can (projFn p f) t R := by
      refine ⟨k,le_rfl,mapProj rest p R st ?_⟩
      intro z hz
      rcases hz with hz|rfl|rfl
      · exact val st (hs _ hz)
      · exact ok
      · exact st.2 _ ok
    rcases aa with ⟨ea,ra⟩ | ⟨c,hc⟩
    · rcases bb with ⟨eb,rb⟩ | ⟨d,hd⟩
      · let T := extend R (projFn p (both a b))
        have eq : (both a b) u = (both a b) v := by simp [both,ea,eb]
        obtain ⟨t,sz,pr⟩ := ih T (stableExt st _) (by
          intro z hz
          rcases hz with hz|rfl|rfl
          · rcases hs _ hz with ⟨e,r⟩|c
            · exact Or.inl ⟨e,Or.inl r⟩
            · exact Or.inr c
          · exact Or.inl ⟨eq,Or.inr (Or.inl rfl)⟩
          · exact Or.inl ⟨congrArg Bool.not eq,Or.inr (Or.inr rfl)⟩)
        exact ⟨t+1,by omega,Can.gate _ _ ra rb pr⟩
      · apply save
        change R (both (projFn p a) (projFn p b))
        rw [hd]
        cases d
        · rw [show both (projFn p a) (fun _ => false) = (fun _ => false) by funext x; simp [both]]
          exact st.1 false
        · rw [show both (projFn p a) (fun _ => true) = projFn p a by funext x; simp [both]]
          exact ra
    · apply save
      change R (both (projFn p a) (projFn p b))
      rw [hc]
      cases c
      · rw [show both (fun _ => false) (projFn p b) = (fun _ => false) by funext x; simp [both]]
        exact st.1 false
      · rw [show both (fun _ => true) (projFn p b) = projFn p b by funext x; simp [both]]
        exact val st bb

abbrev X5 := Fin 5 → Bool
def prim5 (z : Fn X5) : Prop := (∃ b : Bool, z = fun _ => b) ∨
    ∃ i : Fin 5, z = (fun x => x i) ∨ z = inv (fun x => x i)
theorem stable5 : Stable prim5 := by
  refine ⟨fun b => Or.inl ⟨b,rfl⟩,?_⟩
  intro z h
  rcases h with ⟨v,rfl⟩|⟨i,rfl|rfl⟩
  · exact Or.inl ⟨!v,rfl⟩
  · exact Or.inr ⟨i,Or.inr rfl⟩
  · exact Or.inr ⟨i,Or.inl (doubleInv _)⟩
def fa (x : X5) : Bool := f ![false, x 0, x 1, x 2, x 3, x 4]
def fe (x : X5) : Bool := f ![x 0, x 1, x 2, x 3, true, x 4]

namespace FA
-- The live-wire search below adapts the signed separation argument of L_meta_9146.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 440
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 220 := ((x >>> 220) ^^^ x).setWidth 220
def cuts (ws : List W) : BitVec 220 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 220) ++ (0 : BitVec 220)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 220) (w : W) : Prop :=
  w.getLsbD (220+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 220) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 220+i.val < 440 := by omega
  have hi' : i.val < 440 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 220) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 220)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 440 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 440)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))


def rowList : List W := [0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff, 0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000, 0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff, 0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff, 0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000]
def sampled (i : Fin 440) (j : Fin 5) : Bool :=
  (rowList.getD j.val 0)[i.val]
def repr (f : Fn X5) (w : W) : Prop := ∀ i : Fin 440, w[i.val] = f (sampled i)
theorem reprAnd {a b : Fn X5} {wa wb : W} (ha : repr a wa) (hb : repr b wb) :
    repr (both a b) (wa &&& wb) := by
  intro i
  simp only [BitVec.getElem_and,ha i,hb i,both]
theorem reprInv {f : Fn X5} {w : W} (h : repr f w) : repr (inv f) (~~~w) := by
  intro i
  simp only [BitVec.getElem_not,h i,inv]
set_option maxRecDepth 12000 in
theorem sampleCore : repr fa (~~~goal) := by unfold repr; decide +kernel

def represents (R : Pool X5) (av : Finset W) : Prop :=
  ∀ f, R f → ∃ w, holds av w ∧ repr f w
theorem reprExtend {R : Pool X5} {av : Finset W} {f : Fn X5} {w : W}
    (hr : represents R av) (ha : holds av w) (hw : repr f w) : represents (extend R f) av := by
  intro z hz
  rcases hz with h|rfl|rfl
  · exact hr _ h
  · exact ⟨_,ha,hw⟩
  · exact ⟨_,holds_not ha,reprInv hw⟩
theorem reprInsert {R : Pool X5} {av : Finset W} (z : W) (hr : represents R av) :
    represents R (insert z av) := by
  intro f hf
  obtain ⟨w,hold,rep⟩ := hr f hf
  exact ⟨w,holds_insert hold,rep⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem signCompile {R : Pool X5} {k : ℕ} (h : Can fa k R)
    (av : Finset W) (hr : represents R av) :
    ∃ t, (t=goal ∨ t= ~~~goal) ∧ build basicOps t k av := by
  induction h using Can.ind generalizing av with
  | ready hf =>
    obtain ⟨w,hold,rep⟩ := hr _ hf
    have eq : w= ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro j hj
      exact (rep ⟨j,hj⟩).trans (sampleCore ⟨j,hj⟩).symm
    rw [eq] at hold
    rcases hold with zero|ones|⟨t,ht,he|he⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t,Or.inr he.symm,ht⟩
    · exact ⟨t,Or.inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) he.symm),ht⟩
  | skip _ ih =>
    obtain ⟨t,eq,h⟩ := ih av hr
    exact ⟨t,eq,Or.inl h⟩
  | gate a b ha hb _ ih =>
    obtain ⟨wa,ha',ra⟩ := hr a ha
    obtain ⟨wb,hb',rb⟩ := hr b hb
    have rep := reprAnd ra rb
    rcases and_reach ha' hb' with old|⟨x,hx,y,hy,ne,z,hop,hz⟩
    · obtain ⟨t,eq,h⟩ := ih av (reprExtend hr old rep)
      exact ⟨t,eq,Or.inl h⟩
    · obtain ⟨t,eq,h⟩ := ih (insert z av) (reprExtend (reprInsert z hr) hz rep)
      exact ⟨t,eq,Or.inr ⟨x,hx,y,hy,ne,z,hop,h⟩⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem primRep : represents prim5 rowList.toFinset := by
  intro f hf
  rcases hf with ⟨v,rfl⟩|⟨i,rfl|rfl⟩
  · cases v
    · exact ⟨0,Or.inl rfl,by unfold repr; decide +kernel⟩
    · exact ⟨~~~0,Or.inr (Or.inl rfl),by unfold repr; decide +kernel⟩
  · let w := rowList.getD i.val 0
    have hw : w ∈ rowList.toFinset := by fin_cases i <;> decide
    exact ⟨w,Or.inr (Or.inr ⟨w,hw,Or.inl rfl⟩),fun _ => rfl⟩
  · let w := rowList.getD i.val 0
    have hw : w ∈ rowList.toFinset := by fin_cases i <;> decide
    exact ⟨~~~w,Or.inr (Or.inr ⟨w,hw,Or.inr rfl⟩),reprInv (w:=w) (fun _ => rfl)⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem baseBound (rejected : search 7 rowList = false) (k : ℕ) (h : Can fa k prim5) : 8 ≤ k := by
  by_contra! bad
  obtain ⟨t,ht,run⟩ := signCompile h _ primRep
  have lift {a b : ℕ} (le : a ≤ b) (hr : build basicOps t a rowList.toFinset) :
      build basicOps t b rowList.toFinset := by
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have yes := search_complete ht 7 rowList (by decide) (lift (by omega) run)
  exact Bool.noConfusion (rejected.symm.trans yes)
def nextCheck (ws : List W) (e : ℕ) (next : ℕ → List W → Bool) : Bool :=
  (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a,b,r) => dispatch e next a b r)

theorem optChecked {k e : ℕ} {ws : List W} (kids : List (ℕ × List W))
    (all : ∀ t ∈ kids, optimized k t.1 t.2 = false)
    (check : nextCheck ws e (fun i w => !kids.contains (i,w)) = false) :
    optimized (k+1) e ws = false := by
  by_contra! h
  have imp {i w} (ok : optimized k i w = true) : (!kids.contains (i,w)) = true := by
    simp only [Bool.not_eq_true', List.contains_eq_mem]
    by_contra! hm
    have hh := all (i,w) (by simpa using hm)
    simp_all
  have yes : optimized (k+1) e ws = true := by cases he : optimized (k+1) e ws <;> simp_all
  change nextCheck ws e (optimized k) = true at yes
  unfold nextCheck at yes check
  simp only [Bool.or_eq_true, List.any_eq_true] at yes
  have h' : ((ws == [goal] || ws == [~~~goal]) ||
      (pairs ws).any (fun (a,b,r) => dispatch e (fun i w => !kids.contains (i,w)) a b r)) = true := by
    simp only [Bool.or_eq_true,List.any_eq_true]
    rcases yes with h|⟨⟨a,b,r⟩,hm,hd⟩
    · exact Or.inl h
    · refine Or.inr ⟨(a,b,r),hm,?_⟩
      unfold dispatch at hd ⊢
      rw [List.any_eq_true] at hd ⊢
      obtain ⟨z,hz,ok⟩ := hd
      refine ⟨z,hz,?_⟩
      dsimp only at ok ⊢
      simp only [Bool.or_eq_true,Bool.and_eq_true] at ok ⊢
      rcases ok with ((⟨c,t⟩ | ⟨c,(⟨v,t⟩|⟨v,t⟩)⟩) | ⟨c,t⟩)
      · exact Or.inl (Or.inl ⟨c,imp t⟩)
      · exact Or.inl (Or.inr ⟨c,Or.inl ⟨v,imp t⟩⟩)
      · exact Or.inl (Or.inr ⟨c,Or.inr ⟨v,imp t⟩⟩)
      · exact Or.inr ⟨c,imp t⟩
  exact Bool.noConfusion (check.symm.trans h')

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem certifyRoot (h : optimized 7 3 rowList = false) : search 7 rowList = false := by
  have uni : rowList.sublists.filter (fun ws => decide (ws.length ≤ 8) && (cuts ws == -1)) = [rowList] := by decide +kernel
  by_contra! hh
  have ok0 : search 7 rowList = true := by cases he : search 7 rowList <;> simp_all
  unfold search at ok0
  obtain ⟨w,hw,ok⟩ := List.any_eq_true.mp ok0
  change ((decide (w.length ≤ 8) && (cuts w == -1)) && optimized 7 (8-w.length) w) = true at ok
  obtain ⟨good,done⟩ := Bool.and_eq_true_iff.mp ok
  have hw' : w ∈ rowList.sublists.filter (fun ws => decide (ws.length ≤ 8) && (cuts ws == -1)) := List.mem_filter.mpr ⟨hw,good⟩
  rw [uni] at hw'
  obtain rfl := List.mem_singleton.mp hw'
  exact Bool.noConfusion (h.symm.trans done)

end FA

namespace FE
-- The live-wire search below adapts the signed separation argument of L_meta_9146.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 504
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 252 := ((x >>> 252) ^^^ x).setWidth 252
def cuts (ws : List W) : BitVec 252 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 252) ++ (0 : BitVec 252)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 252) (w : W) : Prop :=
  w.getLsbD (252+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 252) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 252+i.val < 504 := by omega
  have hi' : i.val < 504 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 252) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 252)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 504 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 504)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))


def rowList : List W := [0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff, 0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000, 0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000, 0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff, 0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000]
def sampled (i : Fin 504) (j : Fin 5) : Bool :=
  (rowList.getD j.val 0)[i.val]
def repr (f : Fn X5) (w : W) : Prop := ∀ i : Fin 504, w[i.val] = f (sampled i)
theorem reprAnd {a b : Fn X5} {wa wb : W} (ha : repr a wa) (hb : repr b wb) :
    repr (both a b) (wa &&& wb) := by
  intro i
  simp only [BitVec.getElem_and,ha i,hb i,both]
theorem reprInv {f : Fn X5} {w : W} (h : repr f w) : repr (inv f) (~~~w) := by
  intro i
  simp only [BitVec.getElem_not,h i,inv]
set_option maxRecDepth 12000 in
theorem sampleCore : repr fe (~~~goal) := by unfold repr; decide +kernel

def represents (R : Pool X5) (av : Finset W) : Prop :=
  ∀ f, R f → ∃ w, holds av w ∧ repr f w
theorem reprExtend {R : Pool X5} {av : Finset W} {f : Fn X5} {w : W}
    (hr : represents R av) (ha : holds av w) (hw : repr f w) : represents (extend R f) av := by
  intro z hz
  rcases hz with h|rfl|rfl
  · exact hr _ h
  · exact ⟨_,ha,hw⟩
  · exact ⟨_,holds_not ha,reprInv hw⟩
theorem reprInsert {R : Pool X5} {av : Finset W} (z : W) (hr : represents R av) :
    represents R (insert z av) := by
  intro f hf
  obtain ⟨w,hold,rep⟩ := hr f hf
  exact ⟨w,holds_insert hold,rep⟩
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem signCompile {R : Pool X5} {k : ℕ} (h : Can fe k R)
    (av : Finset W) (hr : represents R av) :
    ∃ t, (t=goal ∨ t= ~~~goal) ∧ build basicOps t k av := by
  induction h using Can.ind generalizing av with
  | ready hf =>
    obtain ⟨w,hold,rep⟩ := hr _ hf
    have eq : w= ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro j hj
      exact (rep ⟨j,hj⟩).trans (sampleCore ⟨j,hj⟩).symm
    rw [eq] at hold
    rcases hold with zero|ones|⟨t,ht,he|he⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t,Or.inr he.symm,ht⟩
    · exact ⟨t,Or.inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) he.symm),ht⟩
  | skip _ ih =>
    obtain ⟨t,eq,h⟩ := ih av hr
    exact ⟨t,eq,Or.inl h⟩
  | gate a b ha hb _ ih =>
    obtain ⟨wa,ha',ra⟩ := hr a ha
    obtain ⟨wb,hb',rb⟩ := hr b hb
    have rep := reprAnd ra rb
    rcases and_reach ha' hb' with old|⟨x,hx,y,hy,ne,z,hop,hz⟩
    · obtain ⟨t,eq,h⟩ := ih av (reprExtend hr old rep)
      exact ⟨t,eq,Or.inl h⟩
    · obtain ⟨t,eq,h⟩ := ih (insert z av) (reprExtend (reprInsert z hr) hz rep)
      exact ⟨t,eq,Or.inr ⟨x,hx,y,hy,ne,z,hop,h⟩⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem primRep : represents prim5 rowList.toFinset := by
  intro f hf
  rcases hf with ⟨v,rfl⟩|⟨i,rfl|rfl⟩
  · cases v
    · exact ⟨0,Or.inl rfl,by unfold repr; decide +kernel⟩
    · exact ⟨~~~0,Or.inr (Or.inl rfl),by unfold repr; decide +kernel⟩
  · let w := rowList.getD i.val 0
    have hw : w ∈ rowList.toFinset := by fin_cases i <;> decide
    exact ⟨w,Or.inr (Or.inr ⟨w,hw,Or.inl rfl⟩),fun _ => rfl⟩
  · let w := rowList.getD i.val 0
    have hw : w ∈ rowList.toFinset := by fin_cases i <;> decide
    exact ⟨~~~w,Or.inr (Or.inr ⟨w,hw,Or.inr rfl⟩),reprInv (w:=w) (fun _ => rfl)⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem baseBound (rejected : search 7 rowList = false) (k : ℕ) (h : Can fe k prim5) : 8 ≤ k := by
  by_contra! bad
  obtain ⟨t,ht,run⟩ := signCompile h _ primRep
  have lift {a b : ℕ} (le : a ≤ b) (hr : build basicOps t a rowList.toFinset) :
      build basicOps t b rowList.toFinset := by
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have yes := search_complete ht 7 rowList (by decide) (lift (by omega) run)
  exact Bool.noConfusion (rejected.symm.trans yes)
def nextCheck (ws : List W) (e : ℕ) (next : ℕ → List W → Bool) : Bool :=
  (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a,b,r) => dispatch e next a b r)

theorem optChecked {k e : ℕ} {ws : List W} (kids : List (ℕ × List W))
    (all : ∀ t ∈ kids, optimized k t.1 t.2 = false)
    (check : nextCheck ws e (fun i w => !kids.contains (i,w)) = false) :
    optimized (k+1) e ws = false := by
  by_contra! h
  have imp {i w} (ok : optimized k i w = true) : (!kids.contains (i,w)) = true := by
    simp only [Bool.not_eq_true', List.contains_eq_mem]
    by_contra! hm
    have hh := all (i,w) (by simpa using hm)
    simp_all
  have yes : optimized (k+1) e ws = true := by cases he : optimized (k+1) e ws <;> simp_all
  change nextCheck ws e (optimized k) = true at yes
  unfold nextCheck at yes check
  simp only [Bool.or_eq_true, List.any_eq_true] at yes
  have h' : ((ws == [goal] || ws == [~~~goal]) ||
      (pairs ws).any (fun (a,b,r) => dispatch e (fun i w => !kids.contains (i,w)) a b r)) = true := by
    simp only [Bool.or_eq_true,List.any_eq_true]
    rcases yes with h|⟨⟨a,b,r⟩,hm,hd⟩
    · exact Or.inl h
    · refine Or.inr ⟨(a,b,r),hm,?_⟩
      unfold dispatch at hd ⊢
      rw [List.any_eq_true] at hd ⊢
      obtain ⟨z,hz,ok⟩ := hd
      refine ⟨z,hz,?_⟩
      dsimp only at ok ⊢
      simp only [Bool.or_eq_true,Bool.and_eq_true] at ok ⊢
      rcases ok with ((⟨c,t⟩ | ⟨c,(⟨v,t⟩|⟨v,t⟩)⟩) | ⟨c,t⟩)
      · exact Or.inl (Or.inl ⟨c,imp t⟩)
      · exact Or.inl (Or.inr ⟨c,Or.inl ⟨v,imp t⟩⟩)
      · exact Or.inl (Or.inr ⟨c,Or.inr ⟨v,imp t⟩⟩)
      · exact Or.inr ⟨c,imp t⟩
  exact Bool.noConfusion (check.symm.trans h')

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem certifyRoot (h : optimized 7 3 rowList = false) : search 7 rowList = false := by
  have uni : rowList.sublists.filter (fun ws => decide (ws.length ≤ 8) && (cuts ws == -1)) = [rowList] := by decide +kernel
  by_contra! hh
  have ok0 : search 7 rowList = true := by cases he : search 7 rowList <;> simp_all
  unfold search at ok0
  obtain ⟨w,hw,ok⟩ := List.any_eq_true.mp ok0
  change ((decide (w.length ≤ 8) && (cuts w == -1)) && optimized 7 (8-w.length) w) = true at ok
  obtain ⟨good,done⟩ := Bool.and_eq_true_iff.mp ok
  have hw' : w ∈ rowList.sublists.filter (fun ws => decide (ws.length ≤ 8) && (cuts ws == -1)) := List.mem_filter.mpr ⟨hw,good⟩
  rw [uni] at hw'
  obtain rfl := List.mem_singleton.mp hw'
  exact Bool.noConfusion (h.symm.trans done)

end FE

namespace FA
def b0 : ℕ × List W := (1, [0x422201088804222010888042220108880422201088804222010888fffffc00000000003ffffffffffc00000000003fffff00000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no0 : optimized 6 b0.1 b0.2 = false := by decide +kernel

def b1 : ℕ × List W := (1, [0x673bb99ceee673bb99ceee673bb99ceee673bb99ceee673bb99ceeefffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no1 : optimized 6 b1.1 b1.2 = false := by decide +kernel

def b2 : ℕ × List W := (1, [0x210888842222108888422221088884222210888842222108888422200000000000fffffc0000000000000000fffffc00000000003fffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no2 : optimized 6 b2.1 b2.2 = false := by decide +kernel

def b3 : ℕ × List W := (1, [0x4211110844442111108444421111084444211110844442111108444000003fffff00000000000000003fffff00000000000fffffc00000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no3 : optimized 6 b3.1 b3.2 = false := by decide +kernel

def b4 : ℕ × List W := (1, [0x280000a0000280000a0000280000a0000280000a0000280000a0fffffc00000fffffc00000fffffc00000fffffffffff000003fffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no4 : optimized 6 b4.1 b4.2 = false := by decide +kernel

def b5 : ℕ × List W := (1, [0xad6beab5afaad6beab5afaad6beab5afaad6beab5afaad6beab5afafffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no5 : optimized 6 b5.1 b5.2 = false := by decide +kernel

def b6 : ℕ × List W := (1, [0x25282894a0a25282894a0a25282894a0a25282894a0a25282894a0a00000000000000003fffff000000000000000000000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no6 : optimized 6 b6.1 b6.2 = false := by decide +kernel

def b7 : ℕ × List W := (1, [0x8841422105088414221050884142210508841422105088414221050000003fffff00000000000000003fffff00000000000fffffc00000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no7 : optimized 6 b7.1 b7.2 = false := by decide +kernel

def b8 : ℕ × List W := (1, [0x20280080a0020280080a0020280080a0020280080a0020280080a00fffffc00000fffffffffff00000000000000003fffff000003fffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no8 : optimized 6 b8.1 b8.2 = false := by decide +kernel

def b9 : ℕ × List W := (1, [0xf57eabd5faaf57eabd5faaf57eabd5faaf57eabd5faaf57eabd5faafffffffffffffffffffffffffffc00000ffffffffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no9 : optimized 6 b9.1 b9.2 = false := by decide +kernel

def b10 : ℕ × List W := (1, [0x502a8140aa0502a8140aa0502a8140aa0502a8140aa0502a8140aa0000000000000000000000fffffc00000fffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no10 : optimized 6 b10.1 b10.2 = false := by decide +kernel

def b11 : ℕ × List W := (1, [0xd0540341500d0540341500d0540341500d0540341500d0540341500000003fffff000000000000000000000000000000000fffffc00000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no11 : optimized 6 b11.1 b11.2 = false := by decide +kernel

def b12 : ℕ × List W := (1, [0x2500009400025000094000250000940002500009400025000094000fffffc00000ffffffffffffffffc00000fffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no12 : optimized 6 b12.1 b12.2 = false := by decide +kernel

def b13 : ℕ × List W := (1, [0xffaaabfeaaaffaaabfeaaaffaaabfeaaaffaaabfeaaaffaaabfeaaaffffffffffffffffffffffffffffffffffffffffffff000003fffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no13 : optimized 6 b13.1 b13.2 = false := by decide +kernel

def b14 : ℕ × List W := (1, [0x2aa800aaa002aa800aaa002aa800aaa002aa800aaa002aa800aaa000000000000000000000000000000000000003fffff000003fffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no14 : optimized 6 b14.1 b14.2 = false := by decide +kernel

def b15 : ℕ × List W := (1, [0xda80036a000da80036a000da80036a000da80036a000da80036a000000003fffff00000000000000003fffff0000000000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no15 : optimized 6 b15.1 b15.2 = false := by decide +kernel

def b16 : ℕ × List W := (1, [0x300000c0000300000c0000300000c0000300000c0000300000c0fffffffffff00000000000fffffffffff000003ffffffffffc00000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no16 : optimized 6 b16.1 b16.2 = false := by decide +kernel

def b17 : ℕ × List W := (1, [0xce73f339cfcce73f339cfcce73f339cfcce73f339cfcce73f339cfcfffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no17 : optimized 6 b17.1 b17.2 = false := by decide +kernel

def b18 : ℕ × List W := (1, [0x46303118c0c46303118c0c46303118c0c46303118c0c46303118c0c00000000000000003fffff000000000000000000000000000000000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no18 : optimized 6 b18.1 b18.2 = false := by decide +kernel

def b19 : ℕ × List W := (1, [0x8840c2210308840c2210308840c2210308840c2210308840c22103000000000000fffffc0000000000000000fffffc00000000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no19 : optimized 6 b19.1 b19.2 = false := by decide +kernel

def b20 : ℕ × List W := (1, [0x40300100c0040300100c0040300100c0040300100c0040300100c00fffffffffff000003fffff00000000000000003ffffffffffc00000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no20 : optimized 6 b20.1 b20.2 = false := by decide +kernel

def b21 : ℕ × List W := (1, [0xf67f33d9fccf67f33d9fccf67f33d9fccf67f33d9fccf67f33d9fccfffffffffffffffffffffffffffffffff000003ffffffffffffffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no21 : optimized 6 b21.1 b21.2 = false := by decide +kernel

def b22 : ℕ × List W := (1, [0x60330180cc060330180cc060330180cc060330180cc060330180cc0000000000000000000000fffffffffff0000000000000000000000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no22 : optimized 6 b22.1 b22.2 = false := by decide +kernel

def b23 : ℕ × List W := (1, [0xb04c02c1300b04c02c1300b04c02c1300b04c02c1300b04c02c130000000000000fffffc000000000000000000000000000000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no23 : optimized 6 b23.1 b23.2 = false := by decide +kernel

def b24 : ℕ × List W := (1, [0x4600011800046000118000460001180004600011800046000118000fffffffffff000003ffffffffffffffff0000000000000000000000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no24 : optimized 6 b24.1 b24.2 = false := by decide +kernel

def b25 : ℕ × List W := (1, [0xffb333fecccffb333fecccffb333fecccffb333fecccffb333fecccfffffffffffffffffffffffffffffffffffffffffffffffffc00000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no25 : optimized 6 b25.1 b25.2 = false := by decide +kernel

def b26 : ℕ × List W := (1, [0x333000ccc00333000ccc00333000ccc00333000ccc00333000ccc000000000000000000000000000000000000003ffffffffffc00000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no26 : optimized 6 b26.1 b26.2 = false := by decide +kernel

def b27 : ℕ × List W := (1, [0xb98002e6000b98002e6000b98002e6000b98002e6000b98002e600000000000000fffffc0000000000000000fffffc0000000000000000,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no27 : optimized 6 b27.1 b27.2 = false := by decide +kernel

def b28 : ℕ × List W := (1, [0x8040020100080400201000804002010008040020100080400201000ffffffffffffffffc0000000000000000000003ffffffffffffffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no28 : optimized 6 b28.1 b28.2 = false := by decide +kernel

def b29 : ℕ × List W := (1, [0xf87fc3e1ff0f87fc3e1ff0f87fc3e1ff0f87fc3e1ff0f87fc3e1ff0fffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no29 : optimized 6 b29.1 b29.2 = false := by decide +kernel

def b30 : ℕ × List W := (1, [0x803c0200f00803c0200f00803c0200f00803c0200f00803c0200f00000000000000000000000ffffffffffffffffc0000000000000000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no30 : optimized 6 b30.1 b30.2 = false := by decide +kernel

def b31 : ℕ × List W := (1, [0x703c01c0f00703c01c0f00703c01c0f00703c01c0f00703c01c0f0000000000000000003fffff000000000000000000000000000000000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no31 : optimized 6 b31.1 b31.2 = false := by decide +kernel

def b32 : ℕ × List W := (1, [0x8800022000088000220000880002200008800022000088000220000ffffffffffffffffc00000ffffffffffffffffc0000000000000000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no32 : optimized 6 b32.1 b32.2 = false := by decide +kernel

def b33 : ℕ × List W := (1, [0xffc3c3ff0f0ffc3c3ff0f0ffc3c3ff0f0ffc3c3ff0f0ffc3c3ff0f0fffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no33 : optimized 6 b33.1 b33.2 = false := by decide +kernel

def b34 : ℕ × List W := (1, [0x43c0010f00043c0010f00043c0010f00043c0010f00043c0010f0000000000000000000000000000000000000003ffffffffffffffff,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no34 : optimized 6 b34.1 b34.2 = false := by decide +kernel

def b35 : ℕ × List W := (1, [0x778001de000778001de000778001de000778001de000778001de00000000000000000003fffff000000000000000000000000000000000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no35 : optimized 6 b35.1 b35.2 = false := by decide +kernel

def b36 : ℕ × List W := (1, [0xf00003c0000f00003c0000f00003c0000f00003c0000f00003c0000ffffffffffffffffffffff000000000000000000000000000000000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no36 : optimized 6 b36.1 b36.2 = false := by decide +kernel

def b37 : ℕ × List W := (1, [0xfffc03fff00fffc03fff00fffc03fff00fffc03fff00fffc03fff00fffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no37 : optimized 6 b37.1 b37.2 = false := by decide +kernel

def b38 : ℕ × List W := (1, [0x7c0001f00007c0001f00007c0001f00007c0001f00007c0001f00000000000000000000000000000000000000003ffffffffffffffff,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no38 : optimized 6 b38.1 b38.2 = false := by decide +kernel

def b39 : ℕ × List W := (1, [0xf80003e0000f80003e0000f80003e0000f80003e0000f80003e0000000000000000000000000ffffffffffffffffc0000000000000000,0xf07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00f07c03c1f00ffffffffffffffffffffff00000000000000003ffffffffffffffff,0xff8003fe000ff8003fe000ff8003fe000ff8003fe000ff8003fe000ffffffffffffffffffffffffffffffffffffffc0000000000000000,0x252aa894aaa252aa894aaa252aa894aaa252aa894aaa252aa894aaafffffc00000ffffffffffffffffc00000fffffffffff000003fffff,0x46333118ccc46333118ccc46333118ccc46333118ccc46333118cccfffffffffff000003ffffffffffffffff000003ffffffffffc00000,0x8843c2210f08843c2210f08843c2210f08843c2210f08843c2210f0ffffffffffffffffc00000fffffffffffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no39 : optimized 6 b39.1 b39.2 = false := by decide +kernel

def kids := [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,b32,b33,b34,b35,b36,b37,b38,b39]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem noSeven : search 7 rowList = false := by
  apply certifyRoot
  apply optChecked kids
  · intro t ht
    simp only [kids,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact no0
    · exact no1
    · exact no2
    · exact no3
    · exact no4
    · exact no5
    · exact no6
    · exact no7
    · exact no8
    · exact no9
    · exact no10
    · exact no11
    · exact no12
    · exact no13
    · exact no14
    · exact no15
    · exact no16
    · exact no17
    · exact no18
    · exact no19
    · exact no20
    · exact no21
    · exact no22
    · exact no23
    · exact no24
    · exact no25
    · exact no26
    · exact no27
    · exact no28
    · exact no29
    · exact no30
    · exact no31
    · exact no32
    · exact no33
    · exact no34
    · exact no35
    · exact no36
    · exact no37
    · exact no38
    · exact no39
  · decide +kernel

end FA

namespace FE
def b0 : ℕ × List W := (1, [0x22008802200880220088022008802200880220088022008802200880220088fffc0000000000fffc0000003fff0000000fffffff00000000003fff0000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no0 : optimized 6 b0.1 b0.2 = false := by decide +kernel

def b1 : ℕ × List W := (1, [0x33b8cee33b8cee33b8cee33b8cee33b8cee33b8cee33b8cee33b8cee33b8ceeffffffffffc000fffffffffffffffffffffffffffffffffff0003ffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no1 : optimized 6 b1.1 b1.2 = false := by decide +kernel

def b2 : ℕ × List W := (1, [0x1088422108842210884221088422108842210884221088422108842210884220000000fffc0000000000fffc0000003fff00000000003fff00000000003fff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no2 : optimized 6 b2.1 b2.2 = false := by decide +kernel

def b3 : ℕ × List W := (1, [0x2110844211084421108442110844211084421108442110844211084421108440003fff00000000003fff0000000fffc0000000000fffc0000000000fffc000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no3 : optimized 6 b3.1 b3.2 = false := by decide +kernel

def b4 : ℕ × List W := (1, [0x2800a002800a002800a002800a002800a002800a002800a002800a002800a0fffc000fffc00000000000003fff0003fff0003fff0003fff00000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no4 : optimized 6 b4.1 b4.2 = false := by decide +kernel

def b5 : ℕ × List W := (1, [0x53e94fa53e94fa53e94fa53e94fa53e94fa53e94fa53e94fa53e94fa53e94fafffffffffffffffffc000fffffffffffffffffffffffffffffffffff0003fff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no5 : optimized 6 b5.1 b5.2 = false := by decide +kernel

def b6 : ℕ × List W := (1, [0x102840a102840a102840a102840a102840a102840a102840a102840a102840a00000000000000fffc000fffc0000000000fffc00000000000003fff0003fff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no6 : optimized 6 b6.1 b6.2 = false := by decide +kernel

def b7 : ℕ × List W := (1, [0x4141050414105041410504141050414105041410504141050414105041410500003fff0003fff00000000000000fffc0000000000fffc000fffc0000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no7 : optimized 6 b7.1 b7.2 = false := by decide +kernel

def b8 : ℕ × List W := (1, [0xfffc000fffc000fffc000fffc00000000000003fff0003fff0003fff0003fff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no8 : optimized 6 b8.1 b8.2 = false := by decide +kernel

def b9 : ℕ × List W := (1, [0x96aa5aa96aa5aa96aa5aa96aa5aa96aa5aa96aa5aa96aa5aa96aa5aa96aa5aaffffffffffffffffffffffffffff0003fffffffffffffffffffffffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no9 : optimized 6 b9.1 b9.2 = false := by decide +kernel

def b10 : ℕ × List W := (1, [0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa0000000000000000000000003fff0003ffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no10 : optimized 6 b10.1 b10.2 = false := by decide +kernel

def b11 : ℕ × List W := (1, [0x8402100840210084021008402100840210084021008402100840210084021000003fff0003fff0003fff000000000000000000000fffc000fffc000fffc000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no11 : optimized 6 b11.1 b11.2 = false := by decide +kernel

def b12 : ℕ × List W := (1, [0x100040010004001000400100040010004001000400100040010004001000400fffc000fffc000fffc000fffffff0003ffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no12 : optimized 6 b12.1 b12.2 = false := by decide +kernel

def b13 : ℕ × List W := (1, [0xfaabeaafaabeaafaabeaafaabeaafaabeaafaabeaafaabeaafaabeaafaabeaaffffffffffffffffffffffffffffffffffffffffff0003fff0003fff0003fff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no13 : optimized 6 b13.1 b13.2 = false := by decide +kernel

def b14 : ℕ × List W := (1, [0x2a80aa02a80aa02a80aa02a80aa02a80aa02a80aa02a80aa02a80aa02a80aa000000000000000000000000000000000000003fff0003fff0003fff0003fff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no14 : optimized 6 b14.1 b14.2 = false := by decide +kernel

def b15 : ℕ × List W := (1, [0xe803a00e803a00e803a00e803a00e803a00e803a00e803a00e803a00e803a000003fff0003fff0003fff0000000fffc0000000000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no15 : optimized 6 b15.1 b15.2 = false := by decide +kernel

def b16 : ℕ × List W := (1, [0x3000c003000c003000c003000c003000c003000c003000c003000c003000c0fffffff000000000000000003ffffffc0000003ffffffc00000000000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no16 : optimized 6 b16.1 b16.2 = false := by decide +kernel

def b17 : ℕ × List W := (1, [0x63f18fc63f18fc63f18fc63f18fc63f18fc63f18fc63f18fc63f18fc63f18fcfffffffffffffffffffff0003ffffffffffffffffffffffffffffffffffc000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no17 : optimized 6 b17.1 b17.2 = false := by decide +kernel

def b18 : ℕ × List W := (1, [0x203080c203080c203080c203080c203080c203080c203080c203080c203080c00000000000000fffffff00000000000000fffc00000000000003ffffffc000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no18 : optimized 6 b18.1 b18.2 = false := by decide +kernel

def b19 : ℕ × List W := (1, [0x40c103040c103040c103040c103040c103040c103040c103040c103040c10300000000fffffff000000000000000003fff00000000003ffffffc0000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no19 : optimized 6 b19.1 b19.2 = false := by decide +kernel

def b20 : ℕ × List W := (1, [0xfffffff0000000fffffff000000000000000003ffffffc0000003ffffffc000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no20 : optimized 6 b20.1 b20.2 = false := by decide +kernel

def b21 : ℕ × List W := (1, [0xa7329cca7329cca7329cca7329cca7329cca7329cca7329cca7329cca7329ccfffffffffffffffffffffffffffffffc000ffffffffffffffffffffffffffff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no21 : optimized 6 b21.1 b21.2 = false := by decide +kernel

def b22 : ℕ × List W := (1, [0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc0000000000000000000000003ffffffc000fffc000000000000000000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no22 : optimized 6 b22.1 b22.2 = false := by decide +kernel

def b23 : ℕ × List W := (1, [0x8402100840210084021008402100840210084021008402100840210084021000000000fffffff0000000fffc000000000000000000003ffffffc0000003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no23 : optimized 6 b23.1 b23.2 = false := by decide +kernel

def b24 : ℕ × List W := (1, [0x200080020008002000800200080020008002000800200080020008002000800fffffff0000000fffffff0003ffffffc000fffc000000000000000000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no24 : optimized 6 b24.1 b24.2 = false := by decide +kernel

def b25 : ℕ × List W := (1, [0xfb33eccfb33eccfb33eccfb33eccfb33eccfb33eccfb33eccfb33eccfb33eccfffffffffffffffffffffffffffffffffffffffffffffc0000003ffffffc000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no25 : optimized 6 b25.1 b25.2 = false := by decide +kernel

def b26 : ℕ × List W := (1, [0x3300cc03300cc03300cc03300cc03300cc03300cc03300cc03300cc03300cc000000000000000000000000000000000000003ffffffc0000003ffffffc000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no26 : optimized 6 b26.1 b26.2 = false := by decide +kernel

def b27 : ℕ × List W := (1, [0xd803600d803600d803600d803600d803600d803600d803600d803600d8036000000000fffffff0000000fffc0000003fff0000000000000000000000000000,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no27 : optimized 6 b27.1 b27.2 = false := by decide +kernel

def b28 : ℕ × List W := (1, [0xffffffffffffff0000000000000000000000003fffffffffffffc0000000000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no28 : optimized 6 b28.1 b28.2 = false := by decide +kernel

def b29 : ℕ × List W := (1, [0xc7c31f0c7c31f0c7c31f0c7c31f0c7c31f0c7c31f0c7c31f0c7c31f0c7c31f0fffffffffffffffffffffffffffffffffff0003ffffffffffffffffffffffff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no29 : optimized 6 b29.1 b29.2 = false := by decide +kernel

def b30 : ℕ × List W := (1, [0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f00000000000000000000000003ffffffffff0000000000000000000000000000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no30 : optimized 6 b30.1 b30.2 = false := by decide +kernel

def b31 : ℕ × List W := (1, [0x84021008402100840210084021008402100840210084021008402100840210000000000000000ffffffffffc0000000000000000000000000003ffffffffff,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no31 : optimized 6 b31.1 b31.2 = false := by decide +kernel

def b32 : ℕ × List W := (1, [0x400100040010004001000400100040010004001000400100040010004001000ffffffffffffff00000000003ffffffffff0000000000000000000000000000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no32 : optimized 6 b32.1 b32.2 = false := by decide +kernel

def b33 : ℕ × List W := (1, [0xfbc3ef0fbc3ef0fbc3ef0fbc3ef0fbc3ef0fbc3ef0fbc3ef0fbc3ef0fbc3ef0ffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no33 : optimized 6 b33.1 b33.2 = false := by decide +kernel

def b34 : ℕ × List W := (1, [0x3c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f003c00f0000000000000000000000000000000000000003fffffffffffffc0000000000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no34 : optimized 6 b34.1 b34.2 = false := by decide +kernel

def b35 : ℕ × List W := (1, [0xb802e00b802e00b802e00b802e00b802e00b802e00b802e00b802e00b802e0000000000000000ffffffffffc0000000000fffc000000000000000000000000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no35 : optimized 6 b35.1 b35.2 = false := by decide +kernel

def b36 : ℕ × List W := (1, [0x800200080020008002000800200080020008002000800200080020008002000ffffffffffffffffffffffffc00000000000000000000000000000000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no36 : optimized 6 b36.1 b36.2 = false := by decide +kernel

def b37 : ℕ × List W := (2, [0xfc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no37 : optimized 6 b37.1 b37.2 = false := by decide +kernel

def b38 : ℕ × List W := (1, [0xfc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fc03f00fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no38 : optimized 6 b38.1 b38.2 = false := by decide +kernel

def b39 : ℕ × List W := (1, [0x40010004001000400100040010004001000400100040010004001000400100000000000000000000000000000000000000003ffffffffffffffffffffffff,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no39 : optimized 6 b39.1 b39.2 = false := by decide +kernel

def b40 : ℕ × List W := (2, [0x7801e007801e007801e007801e007801e007801e007801e007801e007801e000000000000000000000000003fffffffffffffc000000000000000000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no40 : optimized 6 b40.1 b40.2 = false := by decide +kernel

def b41 : ℕ × List W := (1, [0x7801e007801e007801e007801e007801e007801e007801e007801e007801e000000000000000000000000003fffffffffffffc000000000000000000000000,0x840210084021008402100840210084021008402100840210084021008402100ffffffffffffffffffffffffc00000000000003ffffffffffffffffffffffff,0xf803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00f803e00ffffffffffffffffffffffffffffffffffffffc000000000000000000000000,0x12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aa12a84aafffc000fffc000fffc000fffffff0003ffffffffff0003fff0003fff0003fff,0x23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308cc23308ccfffffff0000000fffffff0003ffffffc000ffffffffffc0000003ffffffc000,0x43c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f043c10f0ffffffffffffff00000000003ffffffffff0003fffffffffffffc0000000000])
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem no41 : optimized 6 b41.1 b41.2 = false := by decide +kernel

def kids := [b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,b32,b33,b34,b35,b36,b37,b38,b39,b40,b41]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem noSeven : search 7 rowList = false := by
  apply certifyRoot
  apply optChecked kids
  · intro t ht
    simp only [kids,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact no0
    · exact no1
    · exact no2
    · exact no3
    · exact no4
    · exact no5
    · exact no6
    · exact no7
    · exact no8
    · exact no9
    · exact no10
    · exact no11
    · exact no12
    · exact no13
    · exact no14
    · exact no15
    · exact no16
    · exact no17
    · exact no18
    · exact no19
    · exact no20
    · exact no21
    · exact no22
    · exact no23
    · exact no24
    · exact no25
    · exact no26
    · exact no27
    · exact no28
    · exact no29
    · exact no30
    · exact no31
    · exact no32
    · exact no33
    · exact no34
    · exact no35
    · exact no36
    · exact no37
    · exact no38
    · exact no39
    · exact no40
    · exact no41
  · decide +kernel

end FE


def plane (j : Fin 5) (x : X5) : BaseX :=
  match j.val with
  | 0 => ![false, x 0, x 1, x 2, x 3, x 4]
  | 1 => ![x 0, false, x 1, x 2, x 3, x 4]
  | 2 => ![x 1, x 0, false, x 2, x 3, x 4]
  | 3 => ![x 0, x 1, x 2, x 3, true, x 4]
  | _ => ![x 0, x 1, x 2, x 3, x 4, true]

def literal {n : ℕ} (i : Fin (2*n+2)) (x : Fin n → Bool) : Bool :=
  if h : i.val < n then x ⟨i.val,h⟩
  else if h' : i.val-n < n then !(x ⟨i.val-n,h'⟩)
  else decide (i.val=2*n+1)
def wire (a b : Fin 14) (w : Fin 15) : Fn BaseX :=
  if h : w.val < 14 then literal ⟨w.val,h⟩ else both (literal a) (literal b)
def point (r : ℕ) : BaseX := fun i => r.testBit i.val

-- Each literal pair selects a restriction and two assignments on which the
-- function differs. The finite check verifies every entry against the function.
def selected : List (Fin 5 × ℕ × ℕ) := [
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (1,24,26),
  (1,24,26),
  (1,24,26),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (1,24,26),
  (1,24,26),
  (1,24,26),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (0,24,25),
  (2,24,28),
  (2,24,28),
  (2,24,28),
  (0,24,25),
  (1,24,26),
  (0,24,25),
  (2,24,28),
  (2,24,28),
  (2,24,28),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (2,24,28),
  (0,24,25),
  (3,35,51),
  (4,19,51),
  (0,50,51),
  (1,49,51),
  (2,49,53),
  (0,24,25),
  (3,9,25),
  (4,9,41),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (2,24,28),
  (3,35,51),
  (0,24,25),
  (3,9,25),
  (0,40,41),
  (1,40,42),
  (2,40,44),
  (3,9,25),
  (0,24,25),
  (3,35,51),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (2,24,28),
  (4,19,51),
  (3,9,25),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (2,24,28),
  (4,9,41),
  (3,9,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,50,51),
  (0,40,41),
  (0,24,25),
  (0,24,25),
  (0,50,51),
  (0,52,53),
  (0,24,25),
  (0,24,25),
  (0,40,41),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (1,49,51),
  (1,40,42),
  (1,24,26),
  (0,50,51),
  (0,24,25),
  (1,52,54),
  (1,24,26),
  (1,24,26),
  (1,40,42),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (0,24,25),
  (2,49,53),
  (2,40,44),
  (2,24,28),
  (0,52,53),
  (1,52,54),
  (0,24,25),
  (2,24,28),
  (2,24,28),
  (2,40,44),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (2,24,28),
  (0,24,25),
  (3,9,25),
  (4,9,41),
  (0,24,25),
  (1,24,26),
  (2,24,28),
  (0,24,25),
  (3,9,25),
  (4,9,41),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (2,24,28),
  (3,9,25),
  (0,24,25),
  (3,9,25),
  (0,24,25),
  (1,24,26),
  (2,24,28),
  (3,9,25),
  (0,24,25),
  (3,9,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (1,24,26),
  (2,24,28),
  (4,9,41),
  (3,35,51),
  (0,24,25),
  (0,40,41),
  (1,40,42),
  (2,40,44),
  (4,9,41),
  (3,9,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25),
  (0,24,25)
]
def selection (a b : Fin 14) := selected.getD (14*a.val+b.val) (0,0,0)
def checkPair (a b : Fin 14) : Prop :=
  let t := selection a b
  let p := plane t.1
  let u := point t.2.1
  let v := point t.2.2
  f u ≠ f v ∧ ∀ w : Fin 15,
    (∃ c : Bool, ∀ x : X5, wire a b w (p x) = c) ∨
    (wire a b w u = wire a b w v ∧ ∃ i : Fin 12, ∀ x : X5, wire a b w (p x) = literal i x)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow0 : ∀ b : Fin 14, checkPair 0 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow1 : ∀ b : Fin 14, checkPair 1 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow2 : ∀ b : Fin 14, checkPair 2 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow3 : ∀ b : Fin 14, checkPair 3 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow4 : ∀ b : Fin 14, checkPair 4 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow5 : ∀ b : Fin 14, checkPair 5 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow6 : ∀ b : Fin 14, checkPair 6 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow7 : ∀ b : Fin 14, checkPair 7 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow8 : ∀ b : Fin 14, checkPair 8 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow9 : ∀ b : Fin 14, checkPair 9 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow10 : ∀ b : Fin 14, checkPair 10 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow11 : ∀ b : Fin 14, checkPair 11 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow12 : ∀ b : Fin 14, checkPair 12 b := by
  unfold checkPair
  decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checkRow13 : ∀ b : Fin 14, checkPair 13 b := by
  unfold checkPair
  decide +kernel
theorem checkAll : ∀ a b : Fin 14, checkPair a b := by
  intro a
  fin_cases a
  · exact checkRow0
  · exact checkRow1
  · exact checkRow2
  · exact checkRow3
  · exact checkRow4
  · exact checkRow5
  · exact checkRow6
  · exact checkRow7
  · exact checkRow8
  · exact checkRow9
  · exact checkRow10
  · exact checkRow11
  · exact checkRow12
  · exact checkRow13

theorem lit5_mem (i : Fin 12) : prim5 (literal i) := by
  by_cases h : i.val < 5
  · exact Or.inr ⟨⟨i.val,h⟩,Or.inl (funext fun x => by simp [literal,h])⟩
  by_cases hh : i.val-5 < 5
  · exact Or.inr ⟨⟨i.val-5,hh⟩,Or.inr (funext fun x => by simp [literal,h,hh,inv])⟩
  · exact Or.inl ⟨decide (i.val = 11),funext fun x => by simp [literal,h,hh]⟩

theorem encode6 {z : Fn BaseX} (h : prim z) : ∃ i : Fin 14, z = literal i := by
  rcases h with ⟨v,rfl⟩ | ⟨i,rfl|rfl⟩
  · cases v
    · exact ⟨12,rfl⟩
    · exact ⟨13,rfl⟩
  · exact ⟨⟨i.val,by omega⟩,funext fun x => by simp [literal,i.isLt]⟩
  · refine ⟨⟨6+i.val,by omega⟩,funext fun x => ?_⟩
    simp [literal,inv,i.isLt]

theorem guardFor (a b : Fin 14) :
    ∃ (j : Fin 5) (u v : BaseX), f u ≠ f v ∧
    ∀ z, extend prim (both (literal a) (literal b)) z →
      Good (plane j) u v prim5 z ∨ Fixed (plane j) z := by
  let t := selection a b
  let u := point t.2.1
  let v := point t.2.2
  obtain ⟨diff, cert⟩ := checkAll a b
  refine ⟨t.1,u,v,diff,?_⟩
  have hit (w : Fin 15) : Good (plane t.1) u v prim5 (wire a b w) ∨ Fixed (plane t.1) (wire a b w) := by
    rcases cert w with ⟨c,hc⟩|⟨eq,i,hi⟩
    · exact Or.inr ⟨c,funext hc⟩
    · refine Or.inl ⟨eq,?_⟩
      have e : projFn (plane t.1) (wire a b w) = literal i := funext hi
      rw [e]; exact lit5_mem i
  have last : wire a b 14 = both (literal a) (literal b) := rfl
  intro z hz
  rcases hz with old|rfl|rfl
  · obtain ⟨i,rfl⟩ := encode6 old
    have eq : wire a b ⟨i.val,by omega⟩ = literal i := by simp [wire,i.isLt]
    exact eq ▸ hit _
  · exact last ▸ hit 14
  · exact guardInv stable5 (last ▸ hit 14)

set_option maxRecDepth 12000 in
theorem plane_eq (j : Fin 5) : projFn (plane j) f = if j.val < 3 then fa else fe := by
  exact (by decide +kernel : ∀ k : Fin 5, projFn (plane k) f = if k.val < 3 then fa else fe) j

theorem planeVaries (j : Fin 5) : ¬ Fixed (plane j) f := by
  rintro ⟨b,hb⟩
  have lo := congrFun hb (fun _ => false)
  have hi := congrFun hb (fun _ => true)
  rw [plane_eq] at lo hi
  split at lo <;> rename_i h <;> simp [h] at hi <;>
    revert lo hi <;> cases b <;> decide +kernel

theorem startBound (la : ∀ k, Can fa k prim5 → 8 ≤ k) (le : ∀ k, Can fe k prim5 → 8 ≤ k) :
    ∀ k, Can f k prim → 10 ≤ k := by
  intro k
  induction k with
  | zero =>
    intro h
    obtain ⟨i,hi⟩ := encode6 h
    have diff : ∀ j : Fin 14, f ≠ literal j := by decide +kernel
    exact (diff i hi).elim
  | succ k ih =>
    intro h
    rcases h with old|⟨a,b,ha,hb,tail⟩
    · have := ih old; omega
    · obtain ⟨i,rfl⟩ := encode6 ha
      obtain ⟨j,rfl⟩ := encode6 hb
      obtain ⟨p,u,v,d,good⟩ := guardFor i j
      obtain ⟨t,sz,run⟩ := saveGate tail (plane p) u v d (planeVaries p) prim5 stable5 good
      rw [plane_eq] at run
      split at run
      · have := la _ run; omega
      · have := le _ run; omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem binaryBound (C : Circuit) (legal : FanInTwo C)
    (ev : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x) : 10 ≤ cost C.gates := by
  let inputs : List (Fn BaseX) := List.ofFn fun i : Fin 6 => fun x => x i
  have known : ∀ z ∈ inputs, prim z := by
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    exact Or.inr ⟨i,Or.inl rfl⟩
  have run := comp C.gates C.output legal inputs prim stablePrim known
  have eq : readF (traceF C.gates inputs) C.output = f := by
    funext x
    rw [← readAt,traceAt]
    have inp : inputs.map (fun z => z x) = List.ofFn x := by simp [inputs]
    rw [inp]; exact ev x
  rw [eq] at run
  exact startBound (FA.baseBound FA.noSeven) (FE.baseBound FE.noSeven) _ run

theorem replaceCircuit (s : ℕ) (h : HasCircuitSize 6 f s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x := by
  obtain ⟨C,legal,sz,ev⟩ := h
  by_cases neg : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g,hg,hn⟩ := neg
    have lt : cost C.gates < C.gates.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g,hg,by simp [useBinary,hn]⟩
    have lb := binaryBound C legal ev
    change C.gates.length ≤ s at sz
    exact ⟨witness, witnessMonotone, by rw [witnessSize]; omega, computes⟩
  · refine ⟨C,?_,sz,ev⟩
    intro g hg
    obtain ⟨ops,len⟩ := legal g hg
    refine ⟨?_,len⟩
    rcases ops with ha|ho|hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (neg ⟨g,hg,hn⟩).elim

end PEqualNP.Outside.L_meta_12316

theorem PEqualNP.Outside.L_meta_12316 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682240 * 2 ^ 32 + 4261412864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_12316.replaceCircuit
