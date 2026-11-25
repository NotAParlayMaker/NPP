import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_13657
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
def tf (x : BaseX) : Bool := Nat.testBit (4008373472 * 2 ^ 32 + 4008373248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def prim (z : Fn BaseX) : Prop :=
  (∃ b : Bool, z=fun _ => b) ∨ ∃ i : Fin 6, z=(fun x => x i) ∨ z=inv (fun x => x i)
theorem stablePrim : Stable prim := by
  refine ⟨fun b => Or.inl ⟨b,rfl⟩,?_⟩
  intro z h
  rcases h with ⟨v,rfl⟩|⟨i,rfl|rfl⟩
  · exact Or.inl ⟨!v,rfl⟩
  · exact Or.inr ⟨i,Or.inr rfl⟩
  · exact Or.inr ⟨i,Or.inl (doubleInv _)⟩
def wires : List (Fn BaseX) := List.ofFn (fun i : Fin 6 => fun x => x i)
theorem knownWires : ∀ z ∈ wires, prim z := by
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  exact Or.inr ⟨i,Or.inl rfl⟩
def upper : List Gate := [⟨.and, [0,2]⟩, ⟨.or, [6,1]⟩, ⟨.and, [0,4]⟩, ⟨.or, [4,5]⟩, ⟨.and, [2,9]⟩, ⟨.or, [10,3]⟩, ⟨.and, [7,11]⟩, ⟨.or, [8,12]⟩]
set_option maxRecDepth 10000 in
theorem upper_eq : ∀ x : Fin 6 → Bool, Circuit.eval ⟨upper,13⟩ (List.ofFn x) = tf x := by decide +kernel
theorem upper_mono : PEqualNP.MetaComplexity.Monotone2 ⟨upper,13⟩ := by
  intro g hg
  simp only [upper, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

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
abbrev W := BitVec 440
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


def rowList : List W := [0x29465c0167182c50d50033011184155472c44ba82810a730c18563cfffffc0fff00fc03ff03ff03ff80ffffffc0fff80133ef31d38fe7c, 0x2ca0c50094955545114054406a51360914508b29845817604b328507c03ff01ffffffc03fc0ffc0fff03f007ff01fffecd93fe2cf338f, 0x581026baa0209a9b1baed0208b56d84125b6ac20530a181b70dc3d0f8003fffe000fffffffff0000ffffc0007fffe00030e1c3ff0fc3f0, 0x24332cd2b2008182cb6aaba01040024638f14563b01e803b0016a00003fffffff000003fffffff000000007fffffffff01fc03f003ff, 0x94b8820800c0030202f38cf2cc78e28b8010200183ef40003e6a800ffffc0000000000003fffffffffffffff800000003ffe0003fffc00, 0xe73f3bcf1cfce3e3e08200c30060830c0020c18603ffffed8000000fffffffffffffffffc000000000000000000000003ffffffc000000]
def sampled (i : Fin 440) (j : Fin 6) : Bool :=
  (rowList.getD j.val 0)[i.val]
def repr (f : Fn BaseX) (w : W) : Prop := ∀ i : Fin 440, w[i.val] = f (sampled i)
theorem reprAnd {a b : Fn BaseX} {wa wb : W} (ha : repr a wa) (hb : repr b wb) :
    repr (both a b) (wa &&& wb) := by
  intro i
  simp only [BitVec.getElem_and,ha i,hb i,both]
theorem reprInv {f : Fn BaseX} {w : W} (h : repr f w) : repr (inv f) (~~~w) := by
  intro i
  simp only [BitVec.getElem_not,h i,inv]
set_option maxRecDepth 12000 in
theorem sampleTf : repr tf (~~~goal) := by unfold repr; decide +kernel
def represents (R : Pool BaseX) (av : Finset W) : Prop :=
  ∀ f, R f → ∃ w, holds av w ∧ repr f w
theorem reprExtend {R : Pool BaseX} {av : Finset W} {f : Fn BaseX} {w : W}
    (hr : represents R av) (ha : holds av w) (hw : repr f w) : represents (extend R f) av := by
  intro z hz
  rcases hz with h|rfl|rfl
  · exact hr _ h
  · exact ⟨_,ha,hw⟩
  · exact ⟨_,holds_not ha,reprInv hw⟩
theorem reprInsert {R : Pool BaseX} {av : Finset W} (z : W) (hr : represents R av) :
    represents R (insert z av) := by
  intro f hf
  obtain ⟨w,hold,rep⟩ := hr f hf
  exact ⟨w,holds_insert hold,rep⟩
theorem signCompile {R : Pool BaseX} {k : ℕ} (h : Can tf k R)
    (av : Finset W) (hr : represents R av) :
    ∃ t, (t=goal ∨ t= ~~~goal) ∧ build basicOps t k av := by
  induction h using Can.ind generalizing av with
  | ready hf =>
    obtain ⟨w,hold,rep⟩ := hr _ hf
    have eq : w= ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro j hj
      exact (rep ⟨j,hj⟩).trans (sampleTf ⟨j,hj⟩).symm
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
theorem primRep : represents prim rowList.toFinset := by
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
theorem tfBound (rejected : search 7 rowList = false) (k : ℕ) (h : Can tf k prim) : 8 ≤ k := by
  by_contra! bad
  obtain ⟨t,ht,run⟩ := signCompile h _ primRep
  have lift {a b : ℕ} (le : a ≤ b) (hr : build basicOps t a rowList.toFinset) :
      build basicOps t b rowList.toFinset := by
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have yes := search_complete ht 7 rowList (by decide) (lift (by omega) run)
  exact Bool.noConfusion (rejected.symm.trans yes)
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem smallReject : search 7 rowList = false := by decide +kernel
theorem circuitLower (gs : List Gate) (o : ℕ) (legal : ∀ g ∈ gs, fan g)
    (ev : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tf x) : 8 ≤ cost gs := by
  have program := comp gs o legal wires prim stablePrim knownWires
  have eq : readF (traceF gs wires) o = tf := by
    funext y
    rw [← readAt,traceAt]
    have inp : wires.map (fun z => z y) = List.ofFn y := by simp [wires]
    rw [inp]
    exact ev y
  rw [eq] at program
  exact tfBound smallReject _ program

end PEqualNP.Outside.L_meta_13657

theorem PEqualNP.Outside.L_meta_13657 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373472 * 2 ^ 32 + 4008373248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373472 * 2 ^ 32 + 4008373248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨C, hfan, hsize, hev⟩ := h
  have legal : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_13657.fan g := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    refine ⟨?_, hlen⟩
    simpa using hop
  have lb := PEqualNP.Outside.L_meta_13657.circuitLower C.gates C.output legal hev
  have le : PEqualNP.Outside.L_meta_13657.cost C.gates ≤ C.gates.length := List.length_filter_le _ _
  refine ⟨⟨PEqualNP.Outside.L_meta_13657.upper, 13⟩, PEqualNP.Outside.L_meta_13657.upper_mono, ?_, PEqualNP.Outside.L_meta_13657.upper_eq⟩
  have sz : C.size = C.gates.length := rfl
  have hl : PEqualNP.Outside.L_meta_13657.upper.length = 8 := rfl
  change PEqualNP.Outside.L_meta_13657.upper.length ≤ s
  omega
