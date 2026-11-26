import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17134_aux

structure Port where
  raw : Finset (Fin 10)
  prev : Finset (Fin 5)
  deriving DecidableEq

structure Program where
  left : Fin 5 → Port
  right : Fin 5 → Port
  output : Port

def Port.eval (p : Port) (x : Fin 10 → Bool) (value : Fin 5 → Bool) : Bool :=
  decide ((∃ j∈p.raw, x j=true) ∨ ∃ j∈p.prev, value j=true)

def Port.before (p : Port) (k : ℕ) := ∀ j∈p.prev, j.val<k

def Program.WellFormed (p : Program) := ∀ i, (p.left i).before i.val ∧ (p.right i).before i.val

def Program.values (p : Program) (x : Fin 10 → Bool) (i : Fin 5) : Bool :=
  let prev j := if h : j.val < i.val then p.values x j else false
  (p.left i).eval x prev && (p.right i).eval x prev
termination_by i.val

def Program.eval (p : Program) (x : Fin 10 → Bool) : Bool := p.output.eval x (p.values x)

theorem Port.eval_congr (p : Port) (x : Fin 10 → Bool) {u v : Fin 5 → Bool}
    (h : ∀ j∈p.prev, u j=v j) : p.eval x u=p.eval x v := by
  unfold Port.eval; congr 1
  apply propext
  constructor <;> rintro (p|⟨j,hj,b⟩)
  · exact Or.inl p
  · exact Or.inr ⟨j,hj,(h j hj) ▸ b⟩
  · exact Or.inl p
  · exact Or.inr ⟨j,hj,(h j hj).symm ▸ b⟩

theorem Program.values_eq (p : Program) (wf : p.WellFormed) (x : Fin 10 → Bool) (i : Fin 5) :
    p.values x i=((p.left i).eval x (p.values x) && (p.right i).eval x (p.values x)) := by
  conv_lhs => rw [Program.values]
  congr 1
  · apply Port.eval_congr; intro j hj; simp [(wf i).1 j hj]
  · apply Port.eval_congr; intro j hj; simp [(wf i).2 j hj]

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

abbrev Word := Fin 32

def selected (p : Program) (w : Word) (i : Fin 5) : Port :=
  if w.val.testBit (4-i.val) then p.right i else p.left i

inductive Reach (p : Program) (w : Word) : Fin 5 → Prop
  | output {i} : i ∈ p.output.prev → Reach p w i
  | previous {i j} : Reach p w j → i ∈ (selected p w j).prev → Reach p w i

def Present (p : Program) (w : Word) (v : Fin 10) : Prop :=
  v ∈ p.output.raw ∨ ∃ i : Fin 5, Reach p w i ∧ v ∈ (selected p w i).raw

private theorem port_false {a : Port} {x : Fin 10 → Bool} {z : Fin 5 → Bool} :
    a.eval x z = false ↔ (∀ v ∈ a.raw, x v = false) ∧ (∀ i ∈ a.prev, z i = false) := by
  simp [Port.eval]

theorem true_hits (p : Program) (wf : p.WellFormed) {x : Fin 10 → Bool}
    (hp : p.eval x = true) (w : Word) :
    ∃ v : Fin 10, Present p w v ∧ x v = true := by
  by_contra! missing
  have zraw {v : Fin 10} (h : Present p w v) : x v = false := by simpa using missing v h
  have vanish (k : ℕ) : ∀ i : Fin 5, i.val = k → Reach p w i → p.values x i = false := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hk active
      have portzero : (selected p w i).eval x (p.values x) = false := by
        apply port_false.mpr
        constructor
        · intro v hv
          exact zraw (Or.inr ⟨i,active,hv⟩)
        · intro j hj
          have hlt : j.val < i.val := by
            unfold selected at hj
            split at hj
            · exact (wf i).2 j hj
            · exact (wf i).1 j hj
          exact ih j.val (hk ▸ hlt) j rfl (.previous active hj)
      rw [p.values_eq wf]
      unfold selected at portzero
      split at portzero <;> simp [portzero]
  have zero : p.output.eval x (p.values x) = false := by
    apply port_false.mpr
    exact ⟨fun _ hv => zraw (Or.inl hv), fun i hi => vanish i.val i rfl (.output hi)⟩
  rw [Program.eval, zero] at hp
  contradiction

private theorem word_complete : ∀ d : Fin 5 → Bool, ∃ w : Word,
    ∀ i : Fin 5, w.val.testBit (4-i.val) = d i := by decide +kernel

theorem false_misses (p : Program) (wf : p.WellFormed) {x : Fin 10 → Bool}
    (hp : p.eval x = false) :
    ∃ w : Word, ∀ v : Fin 10, Present p w v → x v = false := by
  obtain ⟨w, hw⟩ := word_complete (fun i => (p.left i).eval x (p.values x))
  refine ⟨w, ?_⟩
  have select0 (i : Fin 5) (hi : p.values x i = false) :
      (selected p w i).eval x (p.values x) = false := by
    rw [p.values_eq wf] at hi
    unfold selected
    rw [hw]
    cases h : (p.left i).eval x (p.values x) <;> simp_all
  have start := port_false.mp hp
  have vanish {i : Fin 5} (hi : Reach p w i) : p.values x i = false := by
    induction hi with
    | output hv => exact start.2 _ hv
    | previous _ hj ih => exact (port_false.mp (select0 _ ih)).2 _ hj
  intro v hv
  rcases hv with hor | ⟨i,hr,hraw⟩
  · exact start.1 v hor
  · exact (port_false.mp (select0 i (vanish hr))).1 v hraw

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

abbrev Vertex := Fin 10

structure GraphData where
  adj : Vertex → Vertex → Bool
  negatives : List Nat

def bits (m : Nat) (v : Vertex) : Bool := m.testBit v.val

def edgeInput (u v : Vertex) (k : Vertex) : Bool := decide (k = u ∨ k = v)

def GraphData.Boundary (g : GraphData) (p : Program) : Prop :=
  (∀ u v, g.adj u v = true → p.eval (edgeInput u v) = true) ∧
  (∀ m ∈ g.negatives, p.eval (bits m) = false)

def GraphData.Maximal (g : GraphData) : Prop :=
  ∀ m ∈ g.negatives, ∀ v, bits m v = false →
    ∃ u, bits m u = true ∧ g.adj u v = true

structure Represents (g : GraphData) (absent : Vertex → Word → Prop) : Prop where
  edge : ∀ u v, g.adj u v = true → ∀ w, ¬(absent u w ∧ absent v w)
  row : ∀ m ∈ g.negatives, ∃ w, ∀ v, absent v w ↔ bits m v = true

theorem choice_represents (p : Program) (wf : p.WellFormed)
    {g : GraphData} (h : g.Boundary p) (hm : g.Maximal) :
    Represents g (fun v w => ¬ Present p w v) := by
  have ed u v (a : g.adj u v = true) (w : Word) :
      ¬ ((¬ Present p w u) ∧ (¬ Present p w v)) := by
    obtain ⟨z, hz, on⟩ := true_hits p wf (h.1 u v a) w
    simp only [edgeInput, decide_eq_true_eq] at on
    rcases on with rfl | rfl <;> tauto
  refine ⟨ed, ?_⟩
  intro m mem
  obtain ⟨w, hw⟩ := false_misses p wf (h.2 m mem)
  refine ⟨w, fun v => ⟨?_, ?_⟩⟩
  · intro absent
    by_contra! off
    obtain ⟨u, on, adj⟩ := hm m mem v (by simpa using off)
    exact ed u v adj w ⟨fun present => by simpa [on] using hw u present, absent⟩
  · intro on hit
    simpa [on] using hw v hit

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

abbrev Family := Set (Set Word)

structure UClosed (F : Family) : Prop where
  empty : ∅ ∈ F
  full : Set.univ ∈ F
  join : ∀ {a b : Set Word}, a ∈ F → b ∈ F → a ∪ b ∈ F

inductive Extend (F : Family) (a b : Set Word) : Set Word → Prop
  | old {s} : s ∈ F → Extend F a b s
  | left : Extend F a b a
  | right : Extend F a b b
  | join {s t} : Extend F a b s → Extend F a b t → Extend F a b (s ∪ t)

def initFamily : Family := {s | s = ∅ ∨ s = Set.univ}

def cut (n : Nat) (b : Bool) : Set Word := {w | w.val.testBit n = b}

inductive Envelope : Nat → Family → Prop
  | start : Envelope 0 initFamily
  | split {n F} (prev : Envelope n F) {s : Set Word} (inside : s ∈ F) :
      Envelope (n+1) {t | Extend F (s ∩ cut n false) (s ∩ cut n true) t}

theorem Envelope.closed {n F} (e : Envelope n F) : UClosed F := by
  induction e with
  | start =>
    refine ⟨Or.inl rfl, Or.inr rfl, ?_⟩
    rintro _ _ (rfl|rfl) (rfl|rfl) <;> simp [initFamily]
  | split _ _ ih => exact ⟨.old ih.empty, .old ih.full, fun h1 h2 => .join h1 h2⟩

private theorem ufinite {α : Type} {F : Family} (hc : UClosed F) (s : Finset α)
    (f : α → Set Word) (ok : ∀ a ∈ s, f a ∈ F) :
    {w | ∃ i ∈ s, w ∈ f i} ∈ F := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hc.empty
  | insert a tail _ ih =>
    have ho := hc.join (ok a (by simp)) (ih (fun i hi => ok i (by simp [hi])))
    convert ho using 1
    ext w
    simp

def slot (p : Program) (i : Fin 5) (b : Bool) : Port :=
  if b then p.right i else p.left i

def portWords (p : Program) (k : Fin 5 × Bool) : Set Word :=
  {w | Reach p w k.1 ∧ w.val.testBit (4-k.1.val) = k.2}

private theorem collect (p : Program) {F : Family} (hf : UClosed F) (P : Port → Prop)
    (all : ∀ k : Fin 5 × Bool, P (slot p k.1 k.2) → portWords p k ∈ F) :
    {w | P p.output ∨ ∃ j, Reach p w j ∧ P (selected p w j)} ∈ F := by
  classical
  let s := Finset.univ.filter (fun k : Fin 5 × Bool => P (slot p k.1 k.2))
  have h := ufinite hf s (portWords p) (fun k hk => all k (by simpa [s] using hk))
  have equiv (w : Word) : (∃ j, Reach p w j ∧ P (selected p w j)) ↔
      ∃ k ∈ s, w ∈ portWords p k := by
    constructor
    · rintro ⟨j,hj,hp⟩
      exact ⟨(j,w.val.testBit (4-j.val)), by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, hj, rfl⟩
    · rintro ⟨⟨j,b⟩, hk, hreach, hbit⟩
      refine ⟨j,hreach,?_⟩
      have hport : P (slot p j b) := by simpa [s] using hk
      change P (slot p j (w.val.testBit (4-j.val)))
      exact hbit.symm ▸ hport
  by_cases output : P p.output
  · have e : {w | P p.output ∨ ∃ j, Reach p w j ∧ P (selected p w j)} = Set.univ := by
      ext w; simp [output]
    rw [e]; exact hf.full
  · convert h using 1
    ext w; simpa [output] using equiv w

private theorem nextReach (p : Program) (wf : p.WellFormed) {F : Family}
    (hf : UClosed F) (i : Fin 5)
    (done : ∀ k : Fin 5 × Bool, i.val < k.1.val → portWords p k ∈ F) :
    {w | Reach p w i} ∈ F := by
  have h := collect p hf (fun port => i ∈ port.prev) (fun k hk => done k (by
    cases hb : k.2 <;> simp [slot,hb] at hk
    · exact (wf k.1).1 i hk
    · exact (wf k.1).2 i hk))
  convert h using 1
  ext w
  constructor
  · rintro (h | @⟨_,j,prior,hj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_,prior,hj⟩
  · rintro (h | ⟨j,prior,hj⟩)
    · exact .output h
    · exact .previous prior hj

theorem envelope_for (p : Program) (wf : p.WellFormed) :
    ∃ F, Envelope 5 F ∧ ∀ v : Vertex, {w | Present p w v} ∈ F := by
  have step (d : Nat) (hd : d ≤ 5) : ∃ F, Envelope d F ∧
      ∀ k : Fin 5 × Bool, 5-d ≤ k.1.val → portWords p k ∈ F := by
    induction d with
    | zero => exact ⟨initFamily,.start,fun k hk => by omega⟩
    | succ d ih =>
      obtain ⟨F,hF,done⟩ := ih (by omega)
      let i : Fin 5 := ⟨4-d,by omega⟩
      have hR := nextReach p wf hF.closed i (fun k hk => done k (by simp [i] at hk; omega))
      refine ⟨_, .split hF hR, ?_⟩
      rintro ⟨k,b⟩ hk
      by_cases ke : k=i
      · subst k
        have hbit : 4-i.val=d := by simp [i]; omega
        cases b
        · exact (by simpa [portWords,cut,hbit,Set.inter_def] using
              (Extend.left (F:=F) (a:={w | Reach p w i} ∩ cut d false) (b:={w | Reach p w i} ∩ cut d true)))
        · exact (by simpa [portWords,cut,hbit,Set.inter_def] using
              (Extend.right (F:=F) (a:={w | Reach p w i} ∩ cut d false) (b:={w | Reach p w i} ∩ cut d true)))
      · have neq : k.val ≠ i.val := fun e => ke (Fin.ext e)
        exact .old (done (k,b) (by simp [i] at neq; simp at hk ⊢; omega))
  obtain ⟨F,hF,done⟩ := step 5 (by decide)
  exact ⟨F,hF,fun v => collect p hF.closed (fun port => v ∈ port.raw) (fun k _ => done k (by omega))⟩

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

abbrev PMask := BitVec 32

def modelSet (m : PMask) : Set Word := {w | m.getLsbD w.val = true}

inductive Span (g : List PMask) : Set Word → Prop
  | zero : Span g ∅
  | seed {m} : m ∈ g → Span g (modelSet m)
  | join {x y} : Span g x → Span g y → Span g (x ∪ y)

def allUnions : List PMask → List PMask
  | [] => [0]
  | h::t => let xs := allUnions t; xs ++ xs.map (fun x => x ||| h)

theorem set_or (a b : PMask) : modelSet (a ||| b) = modelSet a ∪ modelSet b := by
  ext x; simp [modelSet]

theorem unions_zero (g : List PMask) : (0:PMask) ∈ allUnions g := by
  induction g with
  | nil => simp [allUnions]
  | cons h t ih => exact List.mem_append_left _ ih

theorem unions_seed {v : PMask} {g : List PMask} (h : v ∈ g) : v ∈ allUnions g := by
  induction g with
  | nil => simp at h
  | cons m t ih =>
    rcases List.mem_cons.mp h with rfl | ho
    · simp only [allUnions, List.mem_append, List.mem_map]
      exact Or.inr ⟨0, unions_zero _, by simp⟩
    · simp [allUnions,ih ho]

theorem unions_join (g : List PMask) {a b} (ha : a ∈ allUnions g) (hb : b ∈ allUnions g) :
    a ||| b ∈ allUnions g := by
  induction g generalizing a b with
  | nil => simp [allUnions] at *; simp_all
  | cons m t ih =>
    simp only [allUnions, List.mem_append, List.mem_map] at ha hb ⊢
    rcases ha with h1 | ⟨a,h1,rfl⟩ <;> rcases hb with h2 | ⟨b,h2,rfl⟩
    · exact Or.inl (ih h1 h2)
    · exact Or.inr ⟨_,ih h1 h2,by apply BitVec.eq_of_getLsbD_eq_iff.mpr; intro i h; simp only [BitVec.getLsbD_or]; cases a.getLsbD i <;> cases b.getLsbD i <;> cases m.getLsbD i <;> decide⟩
    · exact Or.inr ⟨_,ih h1 h2,by apply BitVec.eq_of_getLsbD_eq_iff.mpr; intro i h; simp only [BitVec.getLsbD_or]; cases a.getLsbD i <;> cases b.getLsbD i <;> cases m.getLsbD i <;> decide⟩
    · exact Or.inr ⟨_,ih h1 h2,by apply BitVec.eq_of_getLsbD_eq_iff.mpr; intro i h; simp only [BitVec.getLsbD_or]; cases a.getLsbD i <;> cases b.getLsbD i <;> cases m.getLsbD i <;> decide⟩

theorem Span.numeric {g s} (h : Span g s) : ∃m ∈ allUnions g, s=modelSet m := by
  induction h with
  | zero => exact ⟨0,unions_zero _, by ext x; simp [modelSet]⟩
  | seed hm => exact ⟨_,unions_seed hm,rfl⟩
  | join _ _ ia ib =>
    obtain ⟨a,ha,rfl⟩ := ia
    obtain ⟨b,hb,rfl⟩ := ib
    exact ⟨_,unions_join _ ha hb,(set_or a b).symm⟩

theorem Span.map {g t} (e : Word ≃ Word) (h : ∀ m ∈ g, Span t (e '' modelSet m))
    {s} (inside : Span g s) : Span t (e '' s) := by
  induction inside with
  | zero => simp; exact .zero
  | seed hm => exact h _ hm
  | join _ _ ha hb => rw [Set.image_union]; exact .join ha hb

def Preserves (d : Nat) (e : Word ≃ Word) : Prop :=
  ∀ n, d ≤ n → ∀ w, (e w).val.testBit n = w.val.testBit n

lemma image_cut {d n b} {e : Word ≃ Word} (h : Preserves d e) (hn : d ≤ n) :
    e '' cut n b = cut n b := by
  ext w
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (h n hn x).trans hx
  · intro hw
    change w.val.testBit n=b at hw
    refine ⟨e.symm w, ?_, by simp⟩
    change (e.symm w).val.testBit n = b
    have hh := (h n hn (e.symm w)).symm
    simpa using hh.trans (by simpa using hw : (e (e.symm w)).val.testBit n=b)

lemma pres_comp {d : Nat} {a b : Word ≃ Word} (ha : Preserves d a) (hb : Preserves (d+1) b) :
    Preserves (d+1) (a.trans b) := fun n hn w =>
  (hb n hn (a w)).trans (ha n (by omega) w)

structure StepWitness (d : Nat) (g : List PMask) (r : PMask) (t : List PMask) where
  perm : Word ≃ Word
  preserves : Preserves (d+1) perm
  previous : ∀ m ∈ g, Span t (perm '' modelSet m)
  arm : ∀ b : Bool, Span t (perm '' (modelSet r ∩ cut d b))

def Connect (d : Nat) (prior next : List (List PMask)) : Prop :=
  ∀ g ∈ prior, ∀ r ∈ allUnions g, ∃ t ∈ next, Nonempty (StepWitness d g r t)

def Fits (n : Nat) (states : List (List PMask)) (F : Family) : Prop :=
  ∃ g ∈ states, ∃ e : Word ≃ Word, Preserves n e ∧ ∀s ∈ F, Span g (e '' s)

theorem fits_next {d F s prior next} (hs : s ∈ F) (fit : Fits d prior F)
    (connect : Connect d prior next) :
    Fits (d+1) next {t | Extend F (s ∩ cut d false) (s ∩ cut d true) t} := by
  obtain ⟨g,hg,a,ha,within⟩ := fit
  obtain ⟨m,hm,me⟩ := (within s hs).numeric
  obtain ⟨t,ht,⟨ww⟩⟩ := connect g hg m hm
  refine ⟨t,ht,a.trans ww.perm,pres_comp ha ww.preserves,?_⟩
  intro z hz
  change Extend F (s ∩ cut d false) (s ∩ cut d true) z at hz
  have im (z : Set Word) : (a.trans ww.perm) '' z = ww.perm '' (a '' z) := by
    rw [Set.image_image]; rfl
  have arm (b : Bool) : Span t ((a.trans ww.perm) '' (s ∩ cut d b)) := by
    rw [im,Set.image_inter a.injective,me,image_cut ha (le_refl d)]
    exact ww.arm b
  induction hz with
  | old h => rw [im]; exact (within _ h).map ww.perm ww.previous
  | left => exact arm false
  | right => exact arm true
  | join _ _ hx hy => rw [Set.image_union]; exact .join hx hy

theorem stage_cover (states : Nat → List (List PMask))
    (start : Fits 0 (states 0) initFamily)
    (steps : ∀ d < 5, Connect d (states d) (states (d+1)))
    {n F} (h : Envelope n F) (hn : n ≤ 5) : Fits n (states n) F := by
  induction h with
  | start => exact start
  | split h hs ih => exact fits_next hs (ih (by omega)) (steps _ (by omega))

theorem program_cover (states : Nat → List (List PMask))
    (start : Fits 0 (states 0) initFamily) (steps : ∀ d < 5, Connect d (states d) (states (d+1)))
    (p : Program) (wf : p.WellFormed) :
    ∃ g ∈ states 5, ∃ e : Word ≃ Word, ∀v : Vertex, ∃m ∈ allUnions g,
        e '' {w | Present p w v} = modelSet m := by
  obtain ⟨F,hF,ports⟩ := envelope_for p wf
  obtain ⟨g,hg,e,_,within⟩ := stage_cover states start steps hF (by decide)
  exact ⟨g,hg,e,fun v => (within _ (ports v)).numeric⟩

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux
open CircuitLowerBounds

def zeroPort : Port := ⟨∅,∅⟩
def rawPort (i : Fin 10) : Port := ⟨{i},∅⟩
def gatePort (i : Fin 5) : Port := ⟨∅,{i}⟩
def merge (a b : Port) : Port := ⟨a.raw∪b.raw,a.prev∪b.prev⟩

@[simp] theorem zero_eval (x v) : zeroPort.eval x v=false := by simp [Port.eval,zeroPort]
@[simp] theorem raw_eval (i : Fin 10) (x v) : (rawPort i).eval x v=x i := by simp [Port.eval,rawPort]
@[simp] theorem gate_eval (i : Fin 5) (x v) : (gatePort i).eval x v=v i := by simp [Port.eval,gatePort]
@[simp] theorem merge_eval (a b : Port) (x v) : (merge a b).eval x v=(a.eval x v || b.eval x v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Port.eval,merge,decide_eq_true_eq,Finset.mem_union,Bool.or_eq_true]
  aesop

theorem zero_before (k : ℕ) : zeroPort.before k := by simp [Port.before,zeroPort]
theorem merge_before (a b : Port) (k : ℕ) (ha : a.before k) (hb : b.before k) : (merge a b).before k := by
  intro j hj; rcases Finset.mem_union.mp hj with h|h; exact ha j h; exact hb j h

def WireMap (w : List Port) (x : Fin 10 → Bool) (v : Fin 5 → Bool) := w.map fun p => p.eval x v

theorem WireMap.read (w : List Port) (k : ℕ) (x v) :
    (WireMap w x v).getD k false=(w.getD k zeroPort).eval x v := by
  simpa [WireMap] using List.getD_map (n:=k) w zeroPort (fun p => p.eval x v)

theorem read_before (w : List Port) (k t : ℕ) (all : ∀p∈w,p.before k) : (w.getD t zeroPort).before k := by
  by_cases h : t<w.length
  · rw [List.getD_eq_getElem _ _ h]; exact all _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]; exact zero_before k

noncomputable def isAnd (g : Gate) : Bool := GateOp.rec true false false (fun _ => false) false g.op

def agree (p : Program) (k : ℕ) (x : Fin 10 → Bool) (v : Fin 5 → Bool) :=
  ∀ i : Fin 5, i.val<k → v i=((p.left i).eval x v && (p.right i).eval x v)

def addGate (p : Program) (j : Fin 5) (l r : Port) : Program :=
  ⟨Function.update p.left j l,Function.update p.right j r,p.output⟩

theorem update_wf (p : Program) (wf : p.WellFormed) (j : Fin 5) (l r : Port)
    (hl : l.before j.val) (hr : r.before j.val) : (addGate p j l r).WellFormed := by
  intro i; by_cases e : i=j
  · subst i; simpa [addGate] using And.intro hl hr
  · simpa [addGate,e] using wf i

theorem old_agree (p : Program) (j : Fin 5) (l r : Port) (x v)
    (h : agree (addGate p j l r) (j.val+1) x v) : agree p j.val x v := by
  intro i before
  have ne : i≠j := fun e => (Nat.ne_of_lt before) (congrArg Fin.val e)
  simpa [addGate,ne] using h i (by omega)

theorem construct (inputs : List Port) (start : ∀p∈inputs,p.before 0) :
    ∀ gs : List Gate, (∀g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length=2) →
      gs.countP isAnd ≤ 5 → ∃ (p : Program) (w : List Port), p.WellFormed ∧
        (∀ a∈w, a.before (gs.countP isAnd)) ∧ ∀ x v, agree p (gs.countP isAnd) x v →
        WireMap w x v = (Circuit.mk gs 0).wires (WireMap inputs x v) := by
  intro gs; induction gs using List.reverseRecOn with
  | nil =>
    intro _ _
    exact ⟨⟨fun _ => zeroPort,fun _ => zeroPort,zeroPort⟩,inputs,fun i => ⟨zero_before _,zero_before _⟩,
      start,fun _ _ _ => rfl⟩
  | append_singleton gs g ih =>
    intro good bound
    have pre (t : Gate) (ht : t∈gs) := good t (List.mem_append_left _ ht)
    have data := good g (by simp)
    have upto : gs.countP isAnd≤5 := by rw [List.countP_append] at bound; omega
    obtain ⟨p,w,wf,small,correct⟩ := ih pre upto
    obtain ⟨i,j,I⟩ := List.length_eq_two.mp data.2
    let a := w.getD i zeroPort
    let b := w.getD j zeroPort
    have A := read_before w _ i small
    have B := read_before w _ j small
    rcases data.1 with op|op
    · have len : (gs++[g]).countP isAnd=gs.countP isAnd+1 := by simp [List.countP_append,isAnd,op]
      let t : Fin 5 := ⟨gs.countP isAnd,by omega⟩
      refine ⟨addGate p t a b,w++[gatePort t],update_wf p wf t a b A B,?_,?_⟩
      · intro q h; rw [len]; rcases List.mem_append.mp h with old|fresh
        · exact fun k hk => Nat.lt_succ_of_lt (small q old k hk)
        · have eq : q=gatePort t := by simpa using fresh
          subst q; intro j hj
          have same : j=t := by simpa [gatePort] using hj
          rw [same]; exact Nat.lt_succ_self _
      · intro x v keep; rw [len] at keep
        have prev := correct x v (old_agree p t a b x v keep)
        have gate : v t=(a.eval x v && b.eval x v) := by simpa [addGate] using keep t (Nat.lt_succ_self _)
        simp only [WireMap,List.map_append,List.map_cons,List.map_nil]
        change (WireMap w x v)++[(gatePort t).eval x v]=_
        simp only [Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil,I,op,GateOp.eval,
          List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true,gate_eval]
        let out := (Circuit.mk gs 0).wires (WireMap inputs x v)
        change WireMap w x v++[v t] = out ++ [out.getD i false && out.getD j false]
        change WireMap w x v=out at prev
        rw [← prev,WireMap.read,WireMap.read,gate]
    · have len : (gs++[g]).countP isAnd=gs.countP isAnd := by simp [List.countP_append,isAnd,op]
      refine ⟨p,w++[merge a b],wf,?_,?_⟩
      · intro q h; rw [len]; rcases List.mem_append.mp h with old|fresh
        · exact small q old
        · have eq : q=merge a b := by simpa using fresh
          exact eq.symm ▸ merge_before a b _ A B
      · intro x v keep; rw [len] at keep
        have prev := correct x v keep
        simp only [WireMap,List.map_append,List.map_cons,List.map_nil]
        change (WireMap w x v)++[(merge a b).eval x v]=_
        simp only [Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil,I,op,GateOp.eval,
          List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,merge_eval]
        let out := (Circuit.mk gs 0).wires (WireMap inputs x v)
        change WireMap w x v++[a.eval x v || b.eval x v] = out ++ [out.getD i false || out.getD j false]
        change WireMap w x v=out at prev
        rw [← prev,WireMap.read,WireMap.read]

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux
open CircuitLowerBounds

def pinnedSources (pin : Fin 11) : List Port := List.ofFn (pin.insertNth zeroPort rawPort)

theorem sources_correct (pin : Fin 11) (x : Fin 10 → Bool) (v : Fin 5 → Bool) :
    WireMap (pinnedSources pin) x v=List.ofFn (pin.insertNth false x) := by
  rw [WireMap,pinnedSources,List.map_ofFn]
  congr 1
  funext i
  rcases Fin.eq_self_or_eq_succAbove pin i with rfl|⟨j,rfl⟩ <;> simp

theorem sources_before (pin : Fin 11) : ∀ p∈pinnedSources pin, p.before 0 := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  rcases Fin.eq_self_or_eq_succAbove pin i with rfl|⟨j,rfl⟩
  · simpa using zero_before 0
  · simp [Port.before,rawPort]

theorem pinned_program (pin : Fin 11) (C : Circuit) (ao : TopForm.IsAO2 11 C)
    (small : C.gates.countP isAnd ≤ 5) :
    ∃ P : Program, P.WellFormed ∧ ∀ x : Fin 10 → Bool,
      P.eval x=MetaComplexity.circuitFun 11 C (pin.insertNth false x) := by
  have good (g : Gate) (hg : g∈C.gates) := And.intro (ao.1 g hg) (ao.2.2 g hg)
  obtain ⟨p,w,wf,_,correct⟩ := construct (pinnedSources pin) (sources_before pin) C.gates good small
  let P : Program := {p with output:=w.getD C.output zeroPort}
  have wf' : P.WellFormed := wf
  refine ⟨P,wf',?_⟩
  intro x
  let v := P.values x
  have eq := correct x v (fun j _ => P.values_eq wf' x j)
  rw [sources_correct] at eq
  have result := congrArg (fun xs : List Bool => xs.getD C.output false) eq
  rw [WireMap.read] at result
  exact result

theorem pinned_graph (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (pin : Fin 11) (C : Circuit)
    (ao : TopForm.IsAO2 11 C) (small : C.gates.countP isAnd ≤ 5)
    (agrees : ∀x : Fin 11 → Bool, x pin=false →
      MetaComplexity.circuitFun 11 C x=MetaComplexity.NestedCover.graphFun G ∅ x) :
    ∃ P : Program, P.WellFormed ∧ ∀ x : Fin 10 → Bool,
      P.eval x=MetaComplexity.NestedCover.graphFun G ∅ (pin.insertNth false x) := by
  obtain ⟨P,wf,eq⟩ := pinned_program pin C ao small
  exact ⟨P,wf,fun x => (eq x).trans (agrees _ (by simp))⟩

theorem pinned_graph_relation (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
    (pin : Fin 11) (x : Fin 10 → Bool) :
    MetaComplexity.NestedCover.graphFun G ∅ (pin.insertNth false x)=
      decide (∃ u v : Fin 10, G.Adj (pin.succAbove u) (pin.succAbove v) ∧ x u=true ∧ x v=true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [MetaComplexity.NestedCover.graphFun,Finset.notMem_empty,false_and,exists_const,
    decide_false,Bool.false_or,decide_eq_true_eq]
  constructor
  · rintro ⟨a,b,adj,ha,hb⟩
    rcases Fin.eq_self_or_eq_succAbove pin a with rfl|⟨u,rfl⟩
    · simp at ha
    rcases Fin.eq_self_or_eq_succAbove pin b with rfl|⟨v,rfl⟩
    · simp at hb
    exact ⟨u,v,adj,by simpa using ha,by simpa using hb⟩
  · rintro ⟨u,v,adj,ha,hb⟩
    exact ⟨_,_,adj,by simpa using ha,by simpa using hb⟩

theorem lower_bound_of_separation (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
    (separation : ∀ pin : Fin 11, pin.val<4 → ∀ P : Program, P.WellFormed →
      (∀ x : Fin 10 → Bool, P.eval x=
        decide (∃ u v : Fin 10, G.Adj (pin.succAbove u) (pin.succAbove v) ∧ x u=true ∧ x v=true)) → False)
    (pin : Fin 11) (C : Circuit) (hp : pin.val<4) (ao : TopForm.IsAO2 11 C)
    (agrees : ∀ x : Fin 11 → Bool, x pin=false →
      MetaComplexity.circuitFun 11 C x=MetaComplexity.NestedCover.graphFun G ∅ x) :
    6≤C.gates.countP (fun g => GateOp.rec true false false (fun _ => false) false g.op) := by
  by_contra! fewer
  have small : C.gates.countP isAnd≤5 := by
    change C.gates.countP isAnd<6 at fewer
    omega
  obtain ⟨P,wf,eq⟩ := pinned_graph G pin C ao small agrees
  exact separation pin hp P wf (fun x => (eq x).trans (pinned_graph_relation G pin x))

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

abbrev target17134 : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]

theorem posted_of_program_separation
    (separation : ∀ pin : Fin 11, pin.val<4 → ∀ P : Program, P.WellFormed →
      (∀ x : Fin 10 → Bool, P.eval x=decide
        (∃ u v : Fin 10, target17134.Adj (pin.succAbove u) (pin.succAbove v) ∧ x u=true ∧ x v=true)) → False) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (6 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.false Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x3.gates := by
  exact lower_bound_of_separation target17134 separation

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

def adjRows (k : Fin 4) : List Nat :=
  (![[136, 528, 96, 641, 386, 580, 292, 281, 208, 42],
    [768, 528, 96, 640, 386, 580, 292, 280, 209, 43],
    [768, 136, 96, 642, 384, 580, 292, 282, 209, 41],
    [768, 136, 528, 642, 388, 576, 288, 282, 209, 45]] : Fin 4 → List Nat) k

def negativeRows (k : Fin 4) : List Nat :=
  (![[28, 49, 56, 67, 74, 88, 134, 162, 194, 263, 270, 291, 298, 533, 593, 644, 704, 773],
    [15, 29, 43, 57, 75, 89, 135, 163, 195, 270, 298, 532, 592, 644, 704, 772],
    [23, 29, 51, 57, 83, 89, 133, 161, 193, 268, 290, 296, 534, 594, 644, 704, 774],
    [39, 45, 51, 57, 71, 77, 83, 89, 165, 197, 294, 300, 594, 704, 770]] : Fin 4 → List Nat) k

def graphData (k : Fin 4) : GraphData where
  adj u v := (adjRows k)[u.val]!.testBit v.val
  negatives := negativeRows k

def embedPin (k : Fin 4) : Fin 11 := ⟨k.val,by omega⟩

theorem adjRows_correct : ∀ (k : Fin 4) (u v : Fin 10),
    (graphData k).adj u v=true ↔ target17134.Adj ((embedPin k).succAbove u) ((embedPin k).succAbove v) := by decide

theorem data_maximal (k : Fin 4) : (graphData k).Maximal := by
  have checked : ∀ t : Fin 4, (negativeRows t).all (fun m => decide
      (∀ v : Fin 10, bits m v=false → ∃ u, bits m u=true ∧ (graphData t).adj u v=true))=true := by decide
  exact fun m h => of_decide_eq_true ((List.all_eq_true.mp (checked k)) m h)

theorem data_independent (k : Fin 4) (m : Nat) (hm : m∈(graphData k).negatives)
    (u v : Fin 10) : (graphData k).adj u v=true → bits m u=true → bits m v=true → False := by
  have checked : ∀ t : Fin 4, (negativeRows t).all (fun m => decide
      (∀ u v : Fin 10, (graphData t).adj u v=true → bits m u=true → bits m v=true → False))=true := by decide
  exact (of_decide_eq_true ((List.all_eq_true.mp (checked k)) m hm)) u v

theorem data_boundary (k : Fin 4) (p : Program)
    (eq : ∀ x : Fin 10 → Bool, p.eval x=decide (∃ u v : Fin 10,
      target17134.Adj ((embedPin k).succAbove u) ((embedPin k).succAbove v) ∧ x u=true ∧ x v=true)) :
    (graphData k).Boundary p := by
  constructor
  · intro u v adj
    rw [eq,decide_eq_true_eq]
    exact ⟨u,v,(adjRows_correct k u v).mp adj,by simp [edgeInput],by simp [edgeInput]⟩
  · intro m hm
    rw [eq,decide_eq_false_iff_not]
    rintro ⟨u,v,adj,hu,hv⟩
    exact data_independent k m hm u v ((adjRows_correct k u v).mpr adj) hu hv

theorem boundary_separates (no : ∀ (k : Fin 4) (p : Program), p.WellFormed → (graphData k).Boundary p → False)
    (pin : Fin 11) (hp : pin.val<4) (p : Program) (wf : p.WellFormed)
    (eq : ∀ x : Fin 10 → Bool, p.eval x=decide
      (∃ u v : Fin 10, target17134.Adj (pin.succAbove u) (pin.succAbove v) ∧ x u=true ∧ x v=true)) : False := by
  exact no ⟨pin.val,hp⟩ p wf (data_boundary ⟨pin.val,hp⟩ p eq)

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

abbrev Negative (k : Fin 4) := {m : Nat // m ∈ (graphData k).negatives}

theorem negatives_separated (k : Fin 4) (m n : Negative k)
    (h : ∀ v : Vertex, bits m.val v = bits n.val v) : m=n := by
  have table : ∀ t : Fin 4, (negativeRows t).all (fun a => (negativeRows t).all (fun b =>
    decide ((∀ v : Vertex, bits a v=bits b v) → a=b)))=true := by decide
  have inner := (List.all_eq_true.mp (table k)) m.val m.property
  exact Subtype.ext ((of_decide_eq_true ((List.all_eq_true.mp inner) n.val n.property)) h)

theorem Represents.row_embedding {k : Fin 4} {absent : Vertex → Word → Prop}
    (r : Represents (graphData k) absent) : ∃ f : Negative k ↪ Word,
      ∀ m v, absent v (f m) ↔ bits m.val v=true := by
  classical
  choose wit spec using fun m : Negative k => r.row m.val m.property
  refine ⟨⟨wit,?_⟩,spec⟩
  intro m n eq
  apply negatives_separated k m n
  intro v
  apply Bool.eq_iff_iff.mpr
  rw [←spec m v,←spec n v,eq]

theorem Represents.count_le {k : Fin 4} {absent : Vertex → Word → Prop}
    (r : Represents (graphData k) absent) (rows : Finset (Negative k)) (words : Finset Word)
    (keep : ∀ m ∈ rows, ∀ w, (∀ v, absent v w ↔ bits m.val v=true) → w∈words) :
    rows.card≤words.card := by
  obtain ⟨f,spec⟩ := r.row_embedding
  exact Finset.card_le_card_of_injOn f (fun m h => keep m h _ (spec m)) f.injective.injOn

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
abbrev Mask := BitVec 32
def hit (a : Mask) (w : Word) : Bool := a.getLsbD w.val
def Cards (a : Mask) : Finset Word := Finset.univ.filter fun i => hit a i=true

def bytePop (b : BitVec 8) : Nat := (95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224 >>> (4*b.toNat)) % 16

theorem bytePop_correct : ∀ b : BitVec 8, bytePop b =
    ∑ j : Fin 8, if b.getLsbD j.val then 1 else 0 := by decide

def pop (a : Mask) : Nat := bytePop (a.extractLsb' 0 8)+bytePop (a.extractLsb' 8 8)+
  bytePop (a.extractLsb' 16 8)+bytePop (a.extractLsb' 24 8)

theorem pop_eq_card (a : Mask) : pop a=(Cards a).card := by
  let f (j : Nat) : Nat := if a.getLsbD j then 1 else 0
  have byte (off : Nat) : bytePop (a.extractLsb' off 8)=∑ j∈Finset.range 8, f (off+j) := by
    rw [bytePop_correct,←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp [f,BitVec.getLsbD_extractLsb',j.isLt]
  have tot : (Cards a).card = ∑ j∈Finset.range 32,f j := by
    rw [←Fin.sum_univ_eq_sum_range]
    simp [Cards,hit,f,Finset.sum_boole]
  rw [tot,show 32=24+8 from rfl,Finset.sum_range_add,show 24=16+8 from rfl,
    Finset.sum_range_add,show 16=8+8 from rfl,Finset.sum_range_add]
  simp [pop,byte]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP

def live (k : Fin 4) : Mask := ![262143, 65535, 131071, 32767] k

def column (k : Fin 4) (v : Vertex) : Mask :=
  (![[158218, 8152, 173633, 5173, 24615, 6278, 82232, 98752, 138752, 253952],
    [511, 2005, 43587, 1599, 6186, 1164, 20784, 25024, 34304, 63488],
    [511, 78869, 86595, 2602, 12351, 3212, 41264, 49600, 69120, 126976],
    [1023, 21589, 3891, 2218, 4300, 3343, 13040, 8960, 19456, 28672]] : Fin 4 → List Mask) k |>.getD v.val 0

def row (k : Fin 4) (j : Word) : Nat := (negativeRows k).getD j.val 0

theorem row_mem (k : Fin 4) (j : Word) (h : hit (live k) j=true) : row k j ∈ (graphData k).negatives := by
  have all : ∀ t : Fin 4, ∀ i : Word, hit (live t) i=true → row t i∈(graphData t).negatives := by decide
  exact all k j h

theorem row_ext (k : Fin 4) : ∀ i j : Word, hit (live k) i=true → hit (live k) j=true →
    row k i=row k j → i=j := by
  have table : ∀ t : Fin 4, ∀ i j : Word, hit (live t) i=true → hit (live t) j=true →
    row t i=row t j → i=j := by decide
  exact table k

theorem column_eq : ∀ (k : Fin 4) (j : Word) (v : Vertex),
    hit (column k v) j=bits (row k j) v := by decide

@[simp] theorem mem_cards {a : Mask} {i : Word} : i∈Cards a ↔ hit a i=true := by simp [Cards]
@[simp] theorem hit_and (a b : Mask) (i : Word) : hit (a &&& b) i=(hit a i && hit b i) := by simp [hit]
@[simp] theorem hit_not (a : Mask) (i : Word) : hit (~~~a) i = !(hit a i) := by simp [hit,i.isLt]
theorem mask_zero (a : Mask) (h : ∀i:Word,hit a i=false) : a=0 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simpa [hit] using h ⟨j,hj⟩

structure Assignment (k : Fin 4) (E : Mask) (domain : Vertex → List Mask) where
  value : Vertex → Mask
  allowed : ∀ v, value v∈domain v
  witness : Word → Word
  inj : ∀ i j, hit (live k) i=true → hit (live k) j=true → witness i=witness j → i=j
  into : ∀ i, hit (live k) i=true → hit E (witness i)=true
  agrees : ∀ i, hit (live k) i=true → ∀ v, hit (value v) (witness i)=hit (column k v) i
  edge : ∀ v u, (graphData k).adj v u=true → value v &&& value u=0

def base (U : List Mask) (E : Mask) := U.map (fun a => E &&& ~~~a)

def Complete (U : List Mask) (E : Mask) : Prop :=
  ∀ w : Word, ∃ q : Word, hit E q=true ∧ ∀a∈U,hit a q=hit a w

theorem assignment_of_represents (k : Fin 4) (E : Mask) (U : List Mask) (full : Complete U E)
    (presence : Vertex → Mask) (mem : ∀v,presence v∈U)
    (rep : Represents (graphData k) (fun v w => hit (presence v) w=false)) :
    Nonempty (Assignment k E (fun _ => base U E)) := by
  classical
  choose compress inside same using full
  obtain ⟨embed,pattern⟩ := rep.row_embedding
  let raw (j : Word) := if h : hit (live k) j=true then embed ⟨row k j,row_mem k j h⟩ else 0
  let W (j : Word) := compress (raw j)
  let A (v : Vertex) := E &&& ~~~(presence v)
  have agree (j : Word) (h : hit (live k) j=true) (v : Vertex) : hit (A v) (W j)=hit (column k v) j := by
    simp only [A,W,hit_and,hit_not,inside,Bool.true_and,same _ _ (mem v),column_eq,raw,dif_pos h]
    apply Bool.eq_iff_iff.mpr
    simpa using pattern ⟨row k j,row_mem k j h⟩ v
  refine ⟨⟨A,fun v => List.mem_map.mpr ⟨presence v,mem v,rfl⟩,W,?_,fun j _ => inside _,agree,?_⟩⟩
  · intro i j hi hj sameW
    apply row_ext k i j hi hj
    apply congrArg Subtype.val (negatives_separated k ⟨row k i,row_mem k i hi⟩ ⟨row k j,row_mem k j hj⟩ ?_)
    intro v
    simpa only [←column_eq,←agree i hi v,←agree j hj v,sameW]
  · intro u v edge
    apply mask_zero
    intro w
    have forbid := rep.edge u v edge w
    simp only [A,hit_and,hit_not]
    cases hit E w <;> cases h₁ : hit (presence u) w <;> cases h₂ : hit (presence v) w <;> simp_all
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP

structure Piece where
  rows : Mask
  words : Mask

def Piece.Valid (p : Piece) (s : Assignment k E D) : Prop :=
  ∀j, hit p.rows j=true → hit (live k) j=true ∧ hit p.words (s.witness j)=true

theorem Piece.enough (p : Piece) (s : Assignment k E D) (valid : p.Valid s) :
    pop p.rows ≤ pop p.words := by
  rw [pop_eq_card,pop_eq_card]
  apply Finset.card_le_card_of_injOn s.witness
  · intro i h
    exact mem_cards.mpr (valid i (mem_cards.mp h)).2
  · intro i hi j hj eq
    exact s.inj i j (valid i (mem_cards.mp hi)).1 (valid j (mem_cards.mp hj)).1 eq

def Piece.yes (p : Piece) (c m : Mask) : Piece := ⟨p.rows &&& c,p.words &&& m⟩
def Piece.no (p : Piece) (c m : Mask) : Piece := ⟨p.rows &&& ~~~c,p.words &&& ~~~m⟩

theorem Piece.yes_valid (p : Piece) (s : Assignment k E D) (h : p.Valid s) (v : Vertex) :
    (p.yes (column k v) (s.value v)).Valid s := by
  intro j hj
  simp only [Piece.yes,hit_and,Bool.and_eq_true] at hj
  obtain ⟨first,on⟩ := hj
  obtain ⟨active,word⟩ := h j first
  exact ⟨active,by simp [Piece.yes,word,s.agrees j active v,on]⟩

theorem Piece.no_valid (p : Piece) (s : Assignment k E D) (h : p.Valid s) (v : Vertex) :
    (p.no (column k v) (s.value v)).Valid s := by
  intro j hj
  simp only [Piece.no,hit_and,hit_not,Bool.and_eq_true,Bool.not_eq_true'] at hj
  obtain ⟨active,word⟩ := h j hj.1
  exact ⟨active,by simp [Piece.no,word,s.agrees j active v,hj.2]⟩

def startPiece (k : Fin 4) (E : Mask) : Piece := ⟨live k,E⟩
theorem start_valid (s : Assignment k E D) : (startPiece k E).Valid s :=
  fun j hj => ⟨hj,s.into j hj⟩

def Piece.fits (p : Piece) (k : Fin 4) (v : Vertex) (m : Mask) : Bool :=
  let y := p.yes (column k v) m
  let n := p.no (column k v) m
  decide (pop y.rows≤pop y.words ∧ pop n.rows≤pop n.words)

theorem Piece.fits_actual (p : Piece) (s : Assignment k E D) (h : p.Valid s) (v : Vertex) :
    p.fits k v (s.value v)=true :=
  decide_eq_true ⟨Piece.enough _ s (p.yes_valid s h v),Piece.enough _ s (p.no_valid s h v)⟩

def disjointOnEdge (k : Fin 4) (v u : Vertex) (a b : Mask) : Bool :=
  !(graphData k).adj v u || (a &&& b == 0)

theorem disjoint_actual (s : Assignment k E D) (v u : Vertex) :
    disjointOnEdge k v u (s.value v) (s.value u)=true := by
  unfold disjointOnEdge
  cases h : (graphData k).adj v u <;> simp [s.edge v u,h]

def compatible (k : Fin 4) (E : Mask) (v u : Vertex) (a b : Mask) : Bool :=
  disjointOnEdge k v u a b &&
    ((startPiece k E).yes (column k v) a).fits k u b &&
    ((startPiece k E).no (column k v) a).fits k u b

theorem compatible_actual (s : Assignment k E D) (v u : Vertex) :
    compatible k E v u (s.value v) (s.value u)=true := by
  simp [compatible,disjoint_actual s,Piece.fits_actual _ s
    ((startPiece k E).yes_valid s (start_valid s) v),Piece.fits_actual _ s
    ((startPiece k E).no_valid s (start_valid s) v)]

end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP

abbrev Domains := Vertex → List Mask
abbrev Fixed := List (Vertex × Mask)
def vertices : List Vertex := List.finRange 10

def choices (k : Fin 4) (D : Domains) (pieces : List Piece) (fixed : Fixed) (v : Vertex) : List Mask :=
  (D v).filter fun a => (fixed.all fun q => disjointOnEdge k v q.1 a q.2) &&
    (pieces.all fun p => p.fits k v a)

def follow (pieces : List Piece) (k : Fin 4) (v : Vertex) (a : Mask) : List Piece :=
  (pieces.flatMap fun p => [p.yes (column k v) a,p.no (column k v) a]).filter fun p => p.rows != 0

def pick (k : Fin 4) (D : Domains) (pieces : List Piece) (fixed : Fixed)
    (head : Vertex) (tail : List Vertex) : Vertex × List Mask :=
  tail.foldl (fun best v =>
    let other := choices k D pieces fixed v
    if other.length < best.2.length then (v,other) else best) (head,choices k D pieces fixed head)

theorem pick_choices (k : Fin 4) (D : Domains) (pieces : List Piece) (fixed : Fixed)
    (head : Vertex) (tail : List Vertex) :
    (pick k D pieces fixed head tail).2 = choices k D pieces fixed (pick k D pieces fixed head tail).1 := by
  let next (best : Vertex × List Mask) (v : Vertex) :=
    if (choices k D pieces fixed v).length<best.2.length then (v,choices k D pieces fixed v) else best
  have generalize (vs : List Vertex) (b : Vertex × List Mask)
      (h : b.2=choices k D pieces fixed b.1) :
      (vs.foldl next b).2=choices k D pieces fixed (vs.foldl next b).1 := by
    induction vs generalizing b with
    | nil => exact h
    | cons v vs ih =>
      apply ih
      unfold next
      split <;> simp_all
  exact generalize tail _ rfl

def dfs (k : Fin 4) (D : Domains) : Nat → List Piece → Fixed → List Vertex → Bool
  | 0,_,_,_ => false
  | _+1,_,_,[] => false
  | fuel+1,pieces,fixed,head::tail =>
      let best := pick k D pieces fixed head tail
      best.2.all fun a => dfs k D fuel (follow pieces k best.1 a)
        ((best.1,a)::fixed) ((head::tail).erase best.1)

theorem dfs_sound (s : Assignment k E D) (D' : Domains) (inDomain : ∀v,s.value v∈D' v)
    (fuel : Nat) (pieces : List Piece) (fixed : Fixed) (todo : List Vertex)
    (pc : ∀p∈pieces,p.Valid s) (fc : ∀q∈fixed,q.2=s.value q.1) :
    dfs k D' fuel pieces fixed todo=true → False := by
  induction fuel generalizing pieces fixed todo with
  | zero => simp [dfs]
  | succ fuel ih =>
    cases todo with
    | nil => simp [dfs]
    | cons head tail =>
      intro hard
      let best := pick k D' pieces fixed head tail
      have member : s.value best.1∈best.2 := by
        rw [show best.2=choices k D' pieces fixed best.1 from pick_choices ..]
        apply List.mem_filter.mpr
        refine ⟨inDomain _,Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr ?_,List.all_eq_true.mpr ?_⟩⟩
        · intro q mem; rw [fc q mem]; exact disjoint_actual s _ _
        · intro p mem; exact p.fits_actual s (pc p mem) _
      have sub := List.all_eq_true.mp hard _ member
      apply ih _ _ _ ?_ ?_ sub
      · intro p hp
        obtain ⟨base,hb,child⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
        rcases (show p=base.yes _ _ ∨ p=base.no _ _ by simpa using child) with rfl|rfl
        · exact base.yes_valid s (pc base hb) _
        · exact base.no_valid s (pc base hb) _
      · intro q h; rcases List.mem_cons.mp h with rfl|h
        · rfl
        · exact fc q h

def sweep (k : Fin 4) (E : Mask) (D : Domains) : Domains := fun v =>
  (D v).filter fun a => vertices.all fun u => u==v || (D u).any fun b => compatible k E v u a b

def prune (k : Fin 4) (E : Mask) : Nat → Domains → Domains
  | 0,D => D
  | n+1,D =>
    let next := List.ofFn (sweep k E D)
    let D' := fun v : Vertex => next.getD v.val []
    if vertices.all (fun v => (D' v).length==(D v).length) then D' else prune k E n D'

theorem sweep_preserves (s : Assignment k E D) (D' : Domains) (ok : ∀ v,s.value v∈D' v) :
    ∀v,s.value v∈sweep k E D' v := by
  intro v
  apply List.mem_filter.mpr
  refine ⟨ok v,List.all_eq_true.mpr fun u _ => ?_⟩
  exact Bool.or_eq_true_iff.mpr (Or.inr (List.any_eq_true.mpr ⟨_,ok u,compatible_actual s v u⟩))

theorem prune_preserves (s : Assignment k E D) (n : Nat) (D' : Domains) (ok : ∀v,s.value v∈D' v) :
    ∀v,s.value v∈prune k E n D' v := by
  induction n generalizing D' with
  | zero => exact ok
  | succ n ih =>
    unfold prune
    have step (v : Vertex) : s.value v∈(List.ofFn (sweep k E D')).getD v.val [] := by
      rw [List.getD_eq_getElem _ _ (show v.val < (List.ofFn (sweep k E D')).length by simp), List.getElem_ofFn]
      exact sweep_preserves s D' ok v
    intro v
    dsimp only
    split
    · exact step v
    · exact ih _ step v

def reject (k : Fin 4) (E : Mask) (U : List Mask) (rounds : Nat := 10) : Bool :=
  let support := fun v => (base U E).filter (fun a => (startPiece k E).fits k v a)
  let D := prune k E rounds support
  decide (pop E < pop (live k)) || dfs k D 10 [startPiece k E] [] vertices

theorem reject_sound (k : Fin 4) (E : Mask) (U : List Mask) (rounds : Nat) (full : Complete U E)
    (presence : Vertex → Mask) (mem : ∀v,presence v∈U)
    (hard : reject k E U rounds=true) :
    ¬ Represents (graphData k) (fun v w => hit (presence v) w=false) := by
  intro rep
  obtain ⟨s⟩ := assignment_of_represents k E U full presence mem rep
  have init (v : Vertex) : s.value v∈(base U E).filter (fun a => (startPiece k E).fits k v a) :=
    List.mem_filter.mpr ⟨s.allowed v,Piece.fits_actual _ s (start_valid s) v⟩
  have size := Piece.enough (startPiece k E) s (start_valid s)
  have big : ¬pop E < pop (live k) := Nat.not_lt.mpr size
  simp only [reject,big,decide_false,Bool.false_or] at hard
  apply dfs_sound s _ (prune_preserves s rounds _ init) _ _ _ _ ?_ (by simp) hard
  intro p hp
  simpa using (show p=startPiece k E from by simpa using hp) ▸ start_valid s

end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux

def TerminalCheck (U : List PMask) : Prop :=
  ∀ (k : Fin 4) (presence : Vertex → PMask), (∀ v, presence v ∈ U) →
    ¬ Represents (graphData k) (fun v w => CSP.hit (presence v) w = false)

theorem terminal_of_rejections (U : List PMask) (rejections : ∀ k : Fin 4,
    ∃ (E : CSP.Mask) (rounds : Nat), CSP.Complete U E ∧ CSP.reject k E U rounds = true) :
    TerminalCheck U := by
  intro k presence mem
  obtain ⟨E, rounds, complete, rejected⟩ := rejections k
  exact CSP.reject_sound k E U rounds complete presence mem rejected

theorem transport_representation (p : Program) (k : Fin 4) (e : Word ≃ Word)
    (presence : Vertex → PMask)
    (model : ∀ v, e '' {w | Present p w v} = modelSet (presence v))
    (rep : Represents (graphData k) (fun v w => ¬ Present p w v)) :
    Represents (graphData k) (fun v w => CSP.hit (presence v) w = false) := by
  have present (v : Vertex) (w : Word) :
      CSP.hit (presence v) (e w) = true ↔ Present p w v := by
    have h : (e w ∈ e '' {z | Present p z v}) ↔ Present p w v := by simp
    rw [model v] at h
    exact h
  have absent (v : Vertex) (w : Word) :
      CSP.hit (presence v) (e w) = false ↔ ¬ Present p w v := by
    rw [←present v w]
    cases CSP.hit (presence v) (e w) <;> decide
  constructor
  · intro u v edge w
    obtain ⟨w,rfl⟩ := e.surjective w
    intro both
    exact rep.edge u v edge w ⟨(absent u w).mp both.1, (absent v w).mp both.2⟩
  · intro m hm
    obtain ⟨w, hw⟩ := rep.row m hm
    exact ⟨e w, fun v => (absent v w).trans (hw v)⟩

theorem separation_from_cover (banks : List (List PMask)) (candidates : List PMask → List PMask)
    (cover : ∀ (p : Program), p.WellFormed → ∃ g ∈ banks, ∃ e : Word ≃ Word,
      ∀ v : Vertex, ∃ m ∈ candidates g, e '' {w | Present p w v} = modelSet m)
    (terminal : ∀ g ∈ banks, TerminalCheck (candidates g))
    (k : Fin 4) (p : Program) (wf : p.WellFormed) (boundary : (graphData k).Boundary p) :
    False := by
  obtain ⟨g, hg, e, masks⟩ := cover p wf
  choose presence mem model using masks
  apply terminal g hg k presence mem
  exact transport_representation p k e presence model (choice_represents p wf boundary (data_maximal k))

theorem separation_of_terminals (states : Nat → List (List PMask))
    (start : Fits 0 (states 0) initFamily)
    (steps : ∀ d < 5, Connect d (states d) (states (d+1)))
    (terminal : ∀ g ∈ states 5, TerminalCheck (allUnions g))
    (k : Fin 4) (p : Program) (wf : p.WellFormed) (boundary : (graphData k).Boundary p) :
    False := by
  exact separation_from_cover (states 5) allUnions (program_cover states start steps) terminal k p wf boundary

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

theorem posted_of_terminals (states : Nat → List (List PMask))
    (start : Fits 0 (states 0) initFamily)
    (steps : ∀ d < 5, Connect d (states d) (states (d+1)))
    (finals : ∀ g ∈ states 5, TerminalCheck (allUnions g)) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (6 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.false Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x3.gates := by
  exact posted_of_program_separation (boundary_separates (separation_of_terminals states start steps finals))

theorem posted_from_cover (banks : List (List PMask)) (candidates : List PMask → List PMask)
    (cover : ∀ (p : Program), p.WellFormed → ∃ g ∈ banks, ∃ e : Word ≃ Word,
      ∀ v : Vertex, ∃ m ∈ candidates g, e '' {w | Present p w v} = modelSet m)
    (finals : ∀ g ∈ banks, TerminalCheck (candidates g)) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (6 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.false Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x3.gates := by
  exact posted_of_program_separation (boundary_separates (separation_from_cover banks candidates cover finals))

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux
def seedBank0 : Array (List (BitVec 32)) := #[
[4294967295]
]
def seedBank1 : Array (List (BitVec 32)) := #[
[1431655765, 2863311530]
]
def seedBank2 : Array (List (BitVec 32)) := #[
[858993459, 1431655765, 2863311530, 3435973836],
[286331153, 1145324612, 2863311530]
]
def seedBank3 : Array (List (BitVec 32)) := #[
[252645135, 858993459, 1431655765, 2863311530, 3435973836, 4042322160],
[117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836],
[50529027, 808464432, 1431655765, 2863311530, 3435973836],
[84215045, 286331153, 1145324612, 1347440720, 2863311530],
[185273099, 286331153, 1145324612, 2863311530, 2964369584],
[16843009, 269488144, 1145324612, 2863311530],
[168430090, 286331153, 1145324612, 2694881440]
]
def seedBank4 : Array (List (BitVec 32)) := #[
[16711935, 252645135, 858993459, 1431655765, 2863311530, 3435973836, 4042322160, 4278255360],
[8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 3435973836, 4042322160],
[4128831, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 4042322160],
[12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836],
[7798903, 117901063, 858993459, 1431655765, 1886417008, 1996519168, 2863311530, 3435973836],
[15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808],
[11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836],
[3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836],
[12255419, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3137387264, 3435973836],
[15597806, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 3993038336],
[983055, 251662080, 858993459, 1431655765, 2863311530, 3435973836, 4042322160],
[3342387, 117901063, 855651072, 1431655765, 1886417008, 2863311530, 3435973836],
[14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256],
[3342387, 50529027, 808464432, 855651072, 1431655765, 2863311530, 3435973836],
[458759, 117442304, 858993459, 1431655765, 1886417008, 2863311530, 3435973836],
[5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836],
[11141290, 117901063, 858993459, 1431655765, 1886417008, 2852170240, 3435973836],
[13566159, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3472936704],
[12255419, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 3137387264],
[12517567, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 3204497152],
[15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 4009815808],
[5570645, 84215045, 286331153, 1145324612, 1347440720, 1426085120, 2863311530],
[6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584],
[11468975, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 2936057600],
[1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584],
[5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584],
[15597806, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 3993038336],
[1376277, 84215045, 286331153, 352326912, 1145324612, 1347440720, 2863311530],
[11206827, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2964369584],
[5570645, 50529027, 808464432, 1426085120, 2863311530, 3435973836],
[13369548, 50529027, 808464432, 1431655765, 2863311530, 3422604288],
[196611, 50332416, 808464432, 1431655765, 2863311530, 3435973836],
[1114129, 185273099, 285217024, 1145324612, 2863311530, 2964369584],
[11141290, 185273099, 286331153, 1145324612, 2852170240, 2964369584],
[327685, 83887360, 286331153, 1145324612, 1347440720, 2863311530],
[720907, 184552192, 286331153, 1145324612, 2863311530, 2964369584],
[15663343, 16843009, 269488144, 1145324612, 2863311530, 4009815808],
[4522053, 16843009, 269488144, 1145324612, 1157645568, 2863311530],
[1114129, 16843009, 269488144, 285217024, 1145324612, 2863311530],
[11141290, 84215045, 286331153, 1145324612, 1347440720, 2852170240],
[11206827, 16843009, 269488144, 1145324612, 2863311530, 2868947712],
[4456516, 185273099, 286331153, 1140868096, 2863311530, 2964369584],
[1769499, 168430090, 286331153, 452991744, 1145324612, 2694881440],
[65537, 16777472, 269488144, 1145324612, 2863311530],
[11141290, 16843009, 269488144, 1145324612, 2852170240],
[4456516, 16843009, 269488144, 1140868096, 2863311530]
]
def seedBank5 : Array (List (BitVec 32)) := #[
[65535, 16711935, 252645135, 858993459, 1431655765, 2863311530, 3435973836, 4042322160, 4278255360, 4294901760],
[32767, 16711935, 252645135, 858993459, 1431655765, 2147418112, 2863311530, 3435973836, 4042322160, 4278255360],
[16383, 16711935, 252645135, 858993459, 1073676288, 1431655765, 2863311530, 3435973836, 4042322160, 4278255360],
[65279, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 3435973836, 4042322160, 4278124544],
[61439, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 3435973836, 4026466304, 4042322160],
[49151, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 3221159936, 3435973836, 4042322160],
[32639, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2139029504, 2863311530, 3435973836, 4042322160],
[65278, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 3435973836, 4042322160, 4278059008],
[61423, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 3435973836, 4025417728, 4042322160],
[49087, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 3216965632, 3435973836, 4042322160],
[61183, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 3435973836, 4009689088, 4042322160],
[45055, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 2952724480, 3435973836, 4042322160],
[16255, 8323199, 252645135, 858993459, 1065287680, 1431655765, 2130738944, 2863311530, 3435973836, 4042322160],
[4095, 16711935, 252645135, 268369920, 858993459, 1431655765, 2863311530, 3435973836, 4042322160, 4278255360],
[16191, 8323199, 252645135, 858993459, 1061093376, 1431655765, 2130738944, 2863311530, 3435973836, 4042322160],
[65023, 4128831, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 4042322160, 4261347328],
[57343, 4128831, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 3758030848, 4042322160],
[3967, 8323199, 252645135, 259981312, 858993459, 1431655765, 2130738944, 2863311530, 3435973836, 4042322160],
[16191, 4128831, 252645135, 858993459, 1056980736, 1061093376, 1431655765, 2863311530, 3435973836, 4042322160],
[43775, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 2868838400, 3435973836, 4042322160],
[53247, 4128831, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 3489595392, 4042322160],
[24447, 4128831, 252645135, 858993459, 1056980736, 1431655765, 1602158592, 2863311530, 3435973836, 4042322160],
[64767, 4128831, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 4042322160, 4244570112],
[61166, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 3435973836, 4008574976, 4042322160],
[56831, 4128831, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 3724476416, 4042322160],
[44975, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 2947481600, 3435973836, 4042322160],
[61439, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4026466304],
[49151, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3221159936, 3435973836, 4009815808],
[49151, 7798903, 117901063, 858993459, 1431655765, 1886417008, 1996519168, 2863311530, 3221159936, 3435973836],
[64511, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808, 4227792896],
[30719, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2013200384, 2863311530, 3435973836, 4009815808],
[30719, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2013200384, 2863311530, 3204497152, 3435973836],
[30583, 7798903, 117901063, 858993459, 1431655765, 1886417008, 1996519168, 2004287488, 2863311530, 3435973836],
[61423, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808, 4025417728],
[65279, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4278124544],
[61439, 7798903, 117901063, 858993459, 1431655765, 1886417008, 1996519168, 2863311530, 3435973836, 4026466304],
[65023, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4261347328],
[65279, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808, 4278124544],
[49087, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3216965632, 3435973836],
[64511, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4227792896],
[57343, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 3758030848],
[64767, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4244570112],
[29695, 12517567, 117901063, 858993459, 1431655765, 1886417008, 1946091520, 2863311530, 3204497152, 3435973836],
[61183, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4009689088],
[61423, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4025417728],
[14271, 12517567, 117901063, 858993459, 935264256, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836],
[64255, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4211015680],
[56831, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 3724476416],
[53247, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 3489595392],
[57311, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 3755933696],
[65021, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4261216256],
[48063, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3149856768, 3204497152, 3435973836],
[65278, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808, 4278059008],
[65278, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4278059008],
[45039, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2951675904, 3435973836, 4009815808],
[22527, 12517567, 117901063, 858993459, 1431655765, 1476329472, 1886417008, 2863311530, 3204497152, 3435973836],
[30583, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2004287488, 2863311530, 3204497152, 3435973836],
[45055, 7798903, 117901063, 858993459, 1431655765, 1886417008, 1996519168, 2863311530, 2952724480, 3435973836],
[44991, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2948530176, 3204497152, 3435973836],
[61183, 7798903, 117901063, 858993459, 1431655765, 1886417008, 1996519168, 2863311530, 3435973836, 4009689088],
[64255, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808, 4211015680],
[48127, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3154051072, 3435973836, 4009815808],
[14335, 15663343, 117901063, 858993459, 939458560, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808],
[14199, 7798903, 117901063, 858993459, 930545664, 1431655765, 1886417008, 1996519168, 2863311530, 3435973836],
[61167, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4008640512, 4009815808],
[29695, 15663343, 117901063, 858993459, 1431655765, 1886417008, 1946091520, 2863311530, 3435973836, 4009815808],
[30207, 12517567, 117901063, 858993459, 1431655765, 1886417008, 1979645952, 2863311530, 3204497152, 3435973836],
[64507, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4227530752],
[24415, 4128831, 252645135, 858993459, 1056980736, 1431655765, 1600061440, 2863311530, 3435973836, 4042322160],
[64764, 4128831, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 4042322160, 4244373504],
[56797, 4128831, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 3722248192, 4042322160],
[21887, 4128831, 252645135, 858993459, 1056980736, 1431655765, 1434386432, 2863311530, 3435973836, 4042322160],
[53199, 4128831, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 3486449664, 4042322160],
[52479, 4128831, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 3439263744, 4042322160],
[3903, 4128831, 252645135, 255787008, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 4042322160],
[57343, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 3758030848],
[65279, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 4278124544],
[65023, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 4261347328],
[48059, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3149594624, 3204497152, 3435973836],
[61166, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4008574976, 4009815808],
[61439, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 4026466304],
[57343, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 3758030848],
[64511, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 4227792896],
[14135, 12517567, 117901063, 858993459, 926351360, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836],
[57343, 12255419, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3137387264, 3435973836, 3758030848],
[13247, 12517567, 117901063, 858993459, 868155392, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836],
[13311, 15663343, 117901063, 858993459, 872349696, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808],
[22015, 12517567, 117901063, 858993459, 1431655765, 1442775040, 1886417008, 2863311530, 3204497152, 3435973836],
[13175, 7798903, 117901063, 858993459, 863436800, 1431655765, 1886417008, 1996519168, 2863311530, 3435973836],
[65023, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 4261347328],
[49151, 15597806, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3221159936, 3435973836, 3993038336],
[65279, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 4278124544],
[44975, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2947481600, 3204497152, 3435973836],
[44975, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2947481600, 3435973836, 4009815808],
[30719, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2013200384, 2863311530, 2936057600, 3435973836],
[64511, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 4227792896],
[53231, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 3488546816],
[61183, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 4009689088],
[14135, 3604535, 117901063, 858993459, 922760960, 926351360, 1431655765, 1886417008, 2863311530, 3435973836],
[64250, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4210688000],
[53199, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 3486449664],
[56831, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 3724476416],
[29559, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 1937178624, 2863311530, 3435973836],
[22391, 3604535, 117901063, 858993459, 922760960, 1431655765, 1467416576, 1886417008, 2863311530, 3435973836],
[43775, 7798903, 117901063, 858993459, 1431655765, 1886417008, 1996519168, 2863311530, 2868838400, 3435973836],
[30207, 11468975, 117901063, 858993459, 1431655765, 1886417008, 1979645952, 2863311530, 2936057600, 3435973836],
[29695, 11468975, 117901063, 858993459, 1431655765, 1886417008, 1946091520, 2863311530, 2936057600, 3435973836],
[22527, 11468975, 117901063, 858993459, 1431655765, 1476329472, 1886417008, 2863311530, 2936057600, 3435973836],
[64767, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 4244570112],
[61167, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 4008640512],
[30071, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 1970733056, 2863311530, 3435973836],
[61166, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4008574976],
[48063, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3149856768, 3435973836],
[64250, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808, 4210688000],
[48063, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3149856768, 3435973836],
[64255, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 4211015680],
[44991, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 2948530176, 3435973836],
[14271, 11468975, 117901063, 858993459, 935264256, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836],
[44975, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 2947481600, 3435973836],
[64764, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 4244373504],
[43759, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2867789824, 3435973836, 4009815808],
[43711, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2864644096, 3204497152, 3435973836],
[52479, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 3439263744],
[48059, 7798903, 117901063, 858993459, 1431655765, 1886417008, 1996519168, 2863311530, 3149594624, 3435973836],
[48059, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3149594624, 3435973836, 4009815808],
[64255, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 4211015680],
[61166, 7798903, 117901063, 858993459, 1431655765, 1886417008, 1996519168, 2863311530, 3435973836, 4008574976],
[28927, 15663343, 117901063, 858993459, 1431655765, 1886417008, 1895759872, 2863311530, 3435973836, 4009815808],
[28927, 12517567, 117901063, 858993459, 1431655765, 1886417008, 1895759872, 2863311530, 3204497152, 3435973836],
[29555, 12517567, 117901063, 858993459, 1431655765, 1886417008, 1936916480, 2863311530, 3204497152, 3435973836],
[2031, 15663343, 117901063, 133103616, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808],
[53247, 12255419, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3137387264, 3435973836, 3489595392],
[1983, 12517567, 117901063, 129957888, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836],
[53247, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 3489595392],
[1911, 7798903, 117901063, 125239296, 858993459, 1431655765, 1886417008, 1996519168, 2863311530, 3435973836],
[14271, 12255419, 117901063, 858993459, 935264256, 1431655765, 1886417008, 2863311530, 3137387264, 3435973836],
[22527, 12255419, 117901063, 858993459, 1431655765, 1476329472, 1886417008, 2863311530, 3137387264, 3435973836],
[29555, 15663343, 117901063, 858993459, 1431655765, 1886417008, 1936916480, 2863311530, 3435973836, 4009815808],
[14335, 15597806, 117901063, 858993459, 939458560, 1431655765, 1886417008, 2863311530, 3435973836, 3993038336],
[30069, 12517567, 117901063, 858993459, 1431655765, 1886417008, 1970601984, 2863311530, 3204497152, 3435973836],
[64767, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 4244570112],
[56831, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 3724476416],
[22359, 12517567, 117901063, 858993459, 1431655765, 1465319424, 1886417008, 2863311530, 3204497152, 3435973836],
[14135, 15663343, 117901063, 858993459, 926351360, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808],
[56797, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836, 3722248192],
[14135, 11468975, 117901063, 858993459, 926351360, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836],
[22015, 11468975, 117901063, 858993459, 1431655765, 1442775040, 1886417008, 2863311530, 2936057600, 3435973836],
[13111, 3604535, 117901063, 858993459, 859242496, 922760960, 1431655765, 1886417008, 2863311530, 3435973836],
[21879, 3604535, 117901063, 858993459, 922760960, 1431655765, 1433862144, 1886417008, 2863311530, 3435973836],
[29555, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 1936916480, 2863311530, 3435973836],
[22359, 3604535, 117901063, 858993459, 922760960, 1431655765, 1465319424, 1886417008, 2863311530, 3435973836],
[30069, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 1970601984, 2863311530, 3435973836],
[61166, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 4008574976],
[48059, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3149594624, 3435973836],
[53199, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 3486449664],
[13247, 11468975, 117901063, 858993459, 868155392, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836],
[48059, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3149594624, 3435973836],
[61166, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 4008574976],
[56797, 12255419, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3137387264, 3435973836, 3722248192],
[29555, 11468975, 117901063, 858993459, 1431655765, 1886417008, 1936916480, 2863311530, 2936057600, 3435973836],
[28927, 11468975, 117901063, 858993459, 1431655765, 1886417008, 1895759872, 2863311530, 2936057600, 3435973836],
[2031, 15597806, 117901063, 133103616, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 3993038336],
[43711, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 2864644096, 3435973836],
[43695, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2863595520, 2936057600, 3435973836],
[255, 16711680, 252645135, 858993459, 1431655765, 2863311530, 3435973836, 4042322160, 4278255360],
[52479, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 3439263744],
[22359, 11468975, 117901063, 858993459, 1431655765, 1465319424, 1886417008, 2863311530, 2936057600, 3435973836],
[64764, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 4244373504],
[1983, 12255419, 117901063, 129957888, 858993459, 1431655765, 1886417008, 2863311530, 3137387264, 3435973836],
[56797, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 3722248192],
[56797, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836, 3722248192],
[28791, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 1886846976, 2863311530, 3435973836],
[30069, 11468975, 117901063, 858993459, 1431655765, 1886417008, 1970601984, 2863311530, 2936057600, 3435973836],
[64250, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 4210688000],
[1967, 11468975, 117901063, 128909312, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836],
[1847, 3604535, 117901063, 121044992, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836],
[52463, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836, 3438215168],
[3855, 8323199, 252641280, 858993459, 1431655765, 2130738944, 2863311530, 3435973836, 4042322160],
[63487, 983055, 251662080, 858993459, 1431655765, 2863311530, 3435973836, 4042322160, 4160684032],
[43690, 8323199, 252645135, 858993459, 1431655765, 2130738944, 2863267840, 3435973836, 4042322160],
[62463, 983055, 251662080, 858993459, 1431655765, 2863311530, 3435973836, 4042322160, 4093575168],
[30591, 983055, 251662080, 858993459, 1431655765, 2004811776, 2863311530, 3435973836, 4042322160],
[127, 8323072, 252645135, 858993459, 1431655765, 2130738944, 2863311530, 3435973836, 4042322160],
[3855, 4128831, 252641280, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 4042322160],
[65023, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256, 4261347328],
[13107, 7798903, 117901063, 858980352, 1431655765, 1886417008, 1996519168, 2863311530, 3435973836],
[30719, 14614751, 50529027, 808464432, 1431655765, 2013200384, 2863311530, 3435973836, 3741376256],
[65279, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256, 4278124544],
[57311, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256, 3755933696],
[61439, 3342387, 117901063, 855651072, 1431655765, 1886417008, 2863311530, 3435973836, 4026466304],
[57343, 3342387, 117901063, 855651072, 1431655765, 1886417008, 2863311530, 3435973836, 3758030848],
[61439, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256, 4026466304],
[13107, 12517567, 117901063, 858980352, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836],
[48127, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3154051072, 3435973836, 3741376256],
[22391, 3342387, 117901063, 855651072, 1431655765, 1467416576, 1886417008, 2863311530, 3435973836],
[47871, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3137273856, 3435973836, 3741376256],
[13311, 14614751, 50529027, 808464432, 872349696, 1431655765, 2863311530, 3435973836, 3741376256],
[13107, 12255419, 117901063, 858980352, 1431655765, 1886417008, 2863311530, 3137387264, 3435973836],
[44991, 3342387, 117901063, 855651072, 1431655765, 1886417008, 2863311530, 2948530176, 3435973836],
[53215, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3487498240, 3741376256],
[53247, 3342387, 117901063, 855651072, 1431655765, 1886417008, 2863311530, 3435973836, 3489595392],
[56831, 3342387, 117901063, 855651072, 1431655765, 1886417008, 2863311530, 3435973836, 3724476416],
[21845, 12517567, 117901063, 858993459, 1431633920, 1886417008, 2863311530, 3204497152, 3435973836],
[56799, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3722379264, 3741376256],
[61183, 3342387, 117901063, 855651072, 1431655765, 1886417008, 2863311530, 3435973836, 4009689088],
[13107, 15663343, 117901063, 858980352, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808],
[64767, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256, 4244570112],
[61183, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256, 4009689088],
[13107, 3604535, 117901063, 858980352, 922760960, 1431655765, 1886417008, 2863311530, 3435973836],
[61423, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256, 4025417728],
[65021, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256, 4261216256],
[22495, 14614751, 50529027, 808464432, 1431655765, 1474232320, 2863311530, 3435973836, 3741376256],
[44031, 14614751, 50529027, 808464432, 1431655765, 2863311530, 2885615616, 3435973836, 3741376256],
[65278, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256, 4278059008],
[30207, 14614751, 50529027, 808464432, 1431655765, 1979645952, 2863311530, 3435973836, 3741376256],
[21845, 4128831, 252645135, 858993459, 1056980736, 1431633920, 2863311530, 3435973836, 4042322160],
[52428, 4128831, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435921408, 4042322160],
[61695, 983055, 251662080, 858993459, 1431655765, 2863311530, 3435973836, 4042322160, 4043243520],
[63, 4128768, 252645135, 858993459, 1056980736, 1431655765, 2863311530, 3435973836, 4042322160],
[13119, 983055, 251662080, 858993459, 859766784, 1431655765, 2863311530, 3435973836, 4042322160],
[3855, 983055, 251662080, 252641280, 858993459, 1431655765, 2863311530, 3435973836, 4042322160],
[57343, 11141290, 117901063, 858993459, 1431655765, 1886417008, 2852170240, 3435973836, 3758030848],
[1799, 12517567, 117899264, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836],
[13107, 3342387, 117901063, 855651072, 858980352, 1431655765, 1886417008, 2863311530, 3435973836],
[21983, 14614751, 50529027, 808464432, 1431655765, 1440677888, 2863311530, 3435973836, 3741376256],
[65023, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 4261347328],
[65279, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 4278124544],
[61439, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 4026466304],
[21845, 3604535, 117901063, 858993459, 922760960, 1431633920, 1886417008, 2863311530, 3435973836],
[22359, 14614751, 50529027, 808464432, 1431655765, 1465319424, 2863311530, 3435973836, 3741376256],
[56797, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3722248192, 3741376256],
[13107, 11468975, 117901063, 858980352, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836],
[57343, 3342387, 50529027, 808464432, 855651072, 1431655765, 2863311530, 3435973836, 3758030848],
[65023, 13566159, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3472936704, 4261347328],
[21879, 3342387, 117901063, 855651072, 1431655765, 1433862144, 1886417008, 2863311530, 3435973836],
[48127, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3154051072, 3435973836],
[43775, 14614751, 50529027, 808464432, 1431655765, 2863311530, 2868838400, 3435973836, 3741376256],
[239, 15663104, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808],
[191, 12517376, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435973836],
[43690, 15663343, 117901063, 858993459, 1431655765, 1886417008, 2863267840, 3435973836, 4009815808],
[53199, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3486449664, 3741376256],
[43690, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863267840, 3204497152, 3435973836],
[30719, 13566159, 50529027, 808464432, 1431655765, 2013200384, 2863311530, 3435973836, 3472936704],
[65279, 458759, 117442304, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4278124544],
[64511, 458759, 117442304, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4227792896],
[1799, 15663343, 117899264, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4009815808],
[119, 7798784, 117901063, 858993459, 1431655765, 1886417008, 1996519168, 2863311530, 3435973836],
[30069, 14614751, 50529027, 808464432, 1431655765, 1970601984, 2863311530, 3435973836, 3741376256],
[53247, 3342387, 50529027, 808464432, 855651072, 1431655765, 2863311530, 3435973836, 3489595392],
[64764, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256, 4244373504],
[43690, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863267840, 2936057600, 3435973836],
[29559, 458759, 117442304, 858993459, 1431655765, 1886417008, 1937178624, 2863311530, 3435973836],
[47802, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3132751872, 3435973836, 3741376256],
[44031, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 2885615616, 3435973836],
[56799, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 3722379264],
[1799, 11468975, 117899264, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836],
[61183, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 4009689088],
[48063, 458759, 117442304, 858993459, 1431655765, 1886417008, 2863311530, 3149856768, 3435973836],
[12543, 14614751, 50529027, 808464432, 822018048, 1431655765, 2863311530, 3435973836, 3741376256],
[43947, 14614751, 50529027, 808464432, 1431655765, 2863311530, 2880110592, 3435973836, 3741376256],
[61167, 458759, 117442304, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4008640512],
[43707, 3342387, 117901063, 855651072, 1431655765, 1886417008, 2863311530, 2864381952, 3435973836],
[13311, 13566159, 50529027, 808464432, 872349696, 1431655765, 2863311530, 3435973836, 3472936704],
[64255, 458759, 117442304, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 4211015680],
[28784, 12517567, 117901063, 858993459, 1431655765, 1886388224, 2863311530, 3204497152, 3435973836],
[22359, 5701719, 50529027, 808464432, 1431655765, 1459640064, 1465319424, 2863311530, 3435973836],
[28784, 15663343, 117901063, 858993459, 1431655765, 1886388224, 2863311530, 3435973836, 4009815808],
[991, 14614751, 50529027, 64946176, 808464432, 1431655765, 2863311530, 3435973836, 3741376256],
[64767, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 4244570112],
[53199, 13566159, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3472936704, 3486449664],
[53215, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 3487498240],
[43690, 7798903, 117901063, 858993459, 1431655765, 1886417008, 1996519168, 2863267840, 3435973836],
[13107, 15597806, 117901063, 858980352, 1431655765, 1886417008, 2863311530, 3435973836, 3993038336],
[30207, 13566159, 50529027, 808464432, 1431655765, 1979645952, 2863311530, 3435973836, 3472936704],
[61166, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256, 4008574976],
[56799, 13566159, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3472936704, 3722379264],
[52428, 12517567, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3204497152, 3435921408],
[1799, 3604535, 117899264, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836],
[13175, 5701719, 50529027, 808464432, 863436800, 1431655765, 1459640064, 2863311530, 3435973836],
[52479, 3342387, 117901063, 855651072, 1431655765, 1886417008, 2863311530, 3435973836, 3439263744],
[21845, 11468975, 117901063, 858993459, 1431633920, 1886417008, 2863311530, 2936057600, 3435973836],
[22391, 3342387, 50529027, 808464432, 855651072, 1431655765, 1467416576, 2863311530, 3435973836],
[13107, 3342387, 50529027, 808464432, 855651072, 858980352, 1431655765, 2863311530, 3435973836],
[22527, 11141290, 117901063, 858993459, 1431655765, 1476329472, 1886417008, 2852170240, 3435973836],
[53231, 11141290, 117901063, 858993459, 1431655765, 1886417008, 2852170240, 3435973836, 3488546816],
[1847, 3342387, 117901063, 121044992, 855651072, 1431655765, 1886417008, 2863311530, 3435973836],
[21845, 12255419, 117901063, 858993459, 1431633920, 1886417008, 2863311530, 3137387264, 3435973836],
[47871, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3137273856, 3435973836],
[52447, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3437166592, 3741376256],
[13107, 14614751, 50529027, 808464432, 858980352, 1431655765, 2863311530, 3435973836, 3741376256],
[30071, 5701719, 50529027, 808464432, 1431655765, 1459640064, 1970733056, 2863311530, 3435973836],
[14271, 11141290, 117901063, 858993459, 935264256, 1431655765, 1886417008, 2852170240, 3435973836],
[22495, 13566159, 50529027, 808464432, 1431655765, 1474232320, 2863311530, 3435973836, 3472936704],
[64767, 13566159, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3472936704, 4244570112],
[62975, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 4127129600],
[65279, 12517567, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 3204497152, 4278124544],
[61439, 12517567, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 3204497152, 4026466304],
[65279, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 4009815808, 4278124544],
[49151, 5570645, 84215045, 286331153, 1145324612, 1347440720, 1426085120, 2863311530, 3221159936],
[49087, 12517567, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 3204497152, 3216965632],
[61439, 12255419, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 3137387264, 4026466304],
[22015, 12517567, 84215045, 286331153, 1145324612, 1347440720, 1442775040, 2863311530, 3204497152],
[21845, 5570645, 84215045, 286331153, 1145324612, 1347440720, 1426085120, 1431633920, 2863311530],
[24415, 6226015, 185273099, 286331153, 1145324612, 1593859840, 1600061440, 2863311530, 2964369584],
[65279, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 4278124544],
[61423, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 4009815808, 4025417728],
[61439, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 4026466304],
[48059, 12255419, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 3137387264, 3149594624],
[48127, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 3154051072],
[48127, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 3154051072, 4009815808],
[62975, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 4009815808, 4127129600],
[24575, 15663343, 185273099, 286331153, 1145324612, 1610547200, 2863311530, 2964369584, 4009815808],
[24575, 12255419, 185273099, 286331153, 1145324612, 1610547200, 2863311530, 2964369584, 3137387264],
[21759, 12517567, 84215045, 286331153, 1145324612, 1347440720, 1425997824, 2863311530, 3204497152],
[22015, 15663343, 185273099, 286331153, 1145324612, 1442775040, 2863311530, 2964369584, 4009815808],
[7099, 12255419, 185273099, 286331153, 465240064, 1145324612, 2863311530, 2964369584, 3137387264],
[24415, 15663343, 185273099, 286331153, 1145324612, 1600061440, 2863311530, 2964369584, 4009815808],
[47871, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 3137273856],
[44031, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2885615616, 2964369584],
[20463, 15663343, 185273099, 286331153, 1145324612, 1341063168, 2863311530, 2964369584, 4009815808],
[44991, 12517567, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 2948530176, 3204497152],
[7167, 15663343, 185273099, 286331153, 469696512, 1145324612, 2863311530, 2964369584, 4009815808],
[61423, 12517567, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 3204497152, 4025417728],
[61183, 12517567, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 3204497152, 4009689088],
[17919, 12517567, 84215045, 286331153, 1145324612, 1174339584, 1347440720, 2863311530, 3204497152],
[65278, 12517567, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 3204497152, 4278059008],
[45567, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 2986278912, 4009815808],
[22015, 12255419, 185273099, 286331153, 1145324612, 1442775040, 2863311530, 2964369584, 3137387264],
[5567, 12517567, 84215045, 286331153, 364838912, 1145324612, 1347440720, 2863311530, 3204497152],
[21855, 6226015, 185273099, 286331153, 1145324612, 1432289280, 1593859840, 2863311530, 2964369584],
[62719, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 4110352384],
[43963, 12255419, 185273099, 286331153, 1145324612, 2863311530, 2881159168, 2964369584, 3137387264],
[62965, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 4009815808, 4126474240],
[45567, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 2986278912],
[62965, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 4126474240],
[62719, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 4009815808, 4110352384],
[21845, 12517567, 84215045, 286331153, 1145324612, 1347440720, 1431633920, 2863311530, 3204497152],
[65278, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 4009815808, 4278059008],
[20479, 12255419, 185273099, 286331153, 1145324612, 1342111744, 2863311530, 2964369584, 3137387264],
[20319, 6226015, 185273099, 286331153, 1145324612, 1331625984, 1593859840, 2863311530, 2964369584],
[61167, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 4008640512, 4009815808],
[5461, 5570645, 84215045, 286331153, 357892096, 1145324612, 1347440720, 1426085120, 2863311530],
[7007, 6226015, 185273099, 286331153, 459210752, 1145324612, 1593859840, 2863311530, 2964369584],
[61183, 12255419, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 3137387264, 4009689088],
[44015, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2884567040, 2964369584, 4009815808],
[47871, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 3137273856, 4009815808],
[61183, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 4009689088],
[28784, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886388224, 2863311530, 3435973836],
[52428, 11468975, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435921408],
[22015, 11141290, 117901063, 858993459, 1431655765, 1442775040, 1886417008, 2852170240, 3435973836],
[30069, 5701719, 50529027, 808464432, 1431655765, 1459640064, 1970601984, 2863311530, 3435973836],
[175, 11468800, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 2936057600, 3435973836],
[187, 12255232, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3137387264, 3435973836],
[238, 15597568, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3435973836, 3993038336],
[21847, 5701719, 50529027, 808464432, 1431655765, 1431764992, 1459640064, 2863311530, 3435973836],
[55, 3604480, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435973836],
[43775, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 2868838400, 3435973836],
[56797, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 3722248192],
[43690, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863267840, 3435973836],
[13111, 458759, 117442304, 858993459, 859242496, 1431655765, 1886417008, 2863311530, 3435973836],
[21983, 13566159, 50529027, 808464432, 1431655765, 1440677888, 2863311530, 3435973836, 3472936704],
[53199, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 3486449664],
[21879, 3342387, 50529027, 808464432, 855651072, 1431655765, 1433862144, 2863311530, 3435973836],
[52428, 12255419, 117901063, 858993459, 1431655765, 1886417008, 2863311530, 3137387264, 3435921408],
[43947, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 2880110592, 3435973836],
[819, 3342387, 50529027, 53673984, 808464432, 855651072, 1431655765, 2863311530, 3435973836],
[975, 13566159, 50529027, 63897600, 808464432, 1431655765, 2863311530, 3435973836, 3472936704],
[61166, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 4008574976],
[47802, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3132751872, 3435973836],
[1799, 458759, 117442304, 117899264, 858993459, 1431655765, 1886417008, 2863311530, 3435973836],
[52447, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 3437166592],
[1967, 11141290, 117901063, 128909312, 858993459, 1431655765, 1886417008, 2852170240, 3435973836],
[52431, 13566159, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3436118016, 3472936704],
[64764, 13566159, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3472936704, 4244373504],
[28784, 11468975, 117901063, 858993459, 1431655765, 1886388224, 2863311530, 2936057600, 3435973836],
[56797, 3342387, 50529027, 808464432, 855651072, 1431655765, 2863311530, 3435973836, 3722248192],
[12543, 13566159, 50529027, 808464432, 822018048, 1431655765, 2863311530, 3435973836, 3472936704],
[52428, 3604535, 117901063, 858993459, 922760960, 1431655765, 1886417008, 2863311530, 3435921408],
[43695, 458759, 117442304, 858993459, 1431655765, 1886417008, 2863311530, 2863595520, 3435973836],
[855, 5701719, 50529027, 56033280, 808464432, 1431655765, 1459640064, 2863311530, 3435973836],
[12407, 5701719, 50529027, 808464432, 813105152, 1431655765, 1459640064, 2863311530, 3435973836],
[52479, 3342387, 50529027, 808464432, 855651072, 1431655765, 2863311530, 3435973836, 3439263744],
[28791, 458759, 117442304, 858993459, 1431655765, 1886417008, 1886846976, 2863311530, 3435973836],
[64764, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836, 4244373504],
[62975, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584, 4127129600],
[20303, 15663343, 185273099, 286331153, 1145324612, 1330577408, 2863311530, 2964369584, 4009815808],
[62975, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 4127129600],
[2911, 6226015, 185273099, 190775296, 286331153, 1145324612, 1593859840, 2863311530, 2964369584],
[61439, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 4026466304],
[45311, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 2969501696],
[65279, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 4278124544],
[6939, 6226015, 185273099, 286331153, 454754304, 1145324612, 1593859840, 2863311530, 2964369584],
[43775, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2868838400, 2964369584],
[4447, 6226015, 185273099, 286331153, 291438592, 1145324612, 1593859840, 2863311530, 2964369584],
[64511, 11468975, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 2936057600, 4227792896],
[44975, 12517567, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 2947481600, 3204497152],
[3003, 12255419, 185273099, 196804608, 286331153, 1145324612, 2863311530, 2964369584, 3137387264],
[3055, 15663343, 185273099, 200212480, 286331153, 1145324612, 2863311530, 2964369584, 4009815808],
[45311, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 2969501696, 4009815808],
[21845, 6226015, 185273099, 286331153, 1145324612, 1431633920, 1593859840, 2863311530, 2964369584],
[17663, 12517567, 84215045, 286331153, 1145324612, 1157562368, 1347440720, 2863311530, 3204497152],
[1471, 12517567, 84215045, 96403456, 286331153, 1145324612, 1347440720, 2863311530, 3204497152],
[24575, 11206827, 185273099, 286331153, 1145324612, 1610547200, 2863311530, 2868947712, 2964369584],
[62975, 11206827, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2964369584, 4127129600],
[24575, 15597806, 185273099, 286331153, 1145324612, 1610547200, 2863311530, 2964369584, 3993038336],
[43707, 12255419, 185273099, 286331153, 1145324612, 2863311530, 2864381952, 2964369584, 3137387264],
[43947, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2880110592, 2964369584, 4009815808],
[65279, 11206827, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2964369584, 4278124544],
[4607, 15663343, 185273099, 286331153, 301924352, 1145324612, 2863311530, 2964369584, 4009815808],
[43759, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2867789824, 2964369584, 4009815808],
[61166, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 4008574976, 4009815808],
[48127, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584, 3154051072],
[65279, 1376277, 84215045, 286331153, 352326912, 1145324612, 1347440720, 2863311530, 4278124544],
[5397, 12517567, 84215045, 286331153, 353697792, 1145324612, 1347440720, 2863311530, 3204497152],
[1365, 5570645, 84215045, 89456640, 286331153, 1145324612, 1347440720, 1426085120, 2863311530],
[65279, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584, 4278124544],
[20303, 6226015, 185273099, 286331153, 1145324612, 1330577408, 1593859840, 2863311530, 2964369584],
[61439, 1376277, 84215045, 286331153, 352326912, 1145324612, 1347440720, 2863311530, 4026466304],
[4539, 12255419, 185273099, 286331153, 297467904, 1145324612, 2863311530, 2964369584, 3137387264],
[7007, 5177423, 185273099, 286331153, 459210752, 1145324612, 1325420288, 2863311530, 2964369584],
[43947, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2880110592, 2964369584],
[62719, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584, 4110352384],
[45567, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584, 2986278912],
[62708, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 4109631488],
[61183, 1376277, 84215045, 286331153, 352326912, 1145324612, 1347440720, 2863311530, 4009689088],
[44991, 1376277, 84215045, 286331153, 352326912, 1145324612, 1347440720, 2863311530, 2948530176],
[43711, 12517567, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 2864644096, 3204497152],
[61167, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584, 4008640512],
[21845, 15663343, 185273099, 286331153, 1145324612, 1431633920, 2863311530, 2964369584, 4009815808],
[44015, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2884567040, 2964369584],
[17733, 12517567, 84215045, 286331153, 1145324612, 1162149888, 1347440720, 2863311530, 3204497152],
[21589, 1376277, 84215045, 286331153, 352326912, 1145324612, 1347440720, 1414856704, 2863311530],
[62708, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 4009815808, 4109631488],
[47871, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584, 3137273856],
[21588, 12517567, 84215045, 286331153, 1145324612, 1347440720, 1414791168, 2863311530, 3204497152],
[17663, 12255419, 185273099, 286331153, 1145324612, 1157562368, 2863311530, 2964369584, 3137387264],
[20303, 5177423, 185273099, 286331153, 1145324612, 1325420288, 1330577408, 2863311530, 2964369584],
[17503, 6226015, 185273099, 286331153, 1145324612, 1147076608, 1593859840, 2863311530, 2964369584],
[61166, 12517567, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 3204497152, 4008574976],
[17749, 1376277, 84215045, 286331153, 352326912, 1145324612, 1163198464, 1347440720, 2863311530],
[13107, 983055, 251662080, 858980352, 1431655765, 2863311530, 3435973836, 4042322160],
[20991, 11468975, 84215045, 286331153, 1145324612, 1347440720, 1375666176, 2863311530, 2936057600],
[20463, 11206827, 185273099, 286331153, 1145324612, 1341063168, 2863311530, 2868947712, 2964369584],
[21855, 1769499, 185273099, 286331153, 452991744, 1145324612, 1432289280, 2863311530, 2964369584],
[62719, 11206827, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2964369584, 4110352384],
[43775, 5570645, 84215045, 286331153, 1145324612, 1347440720, 1426085120, 2863311530, 2868838400],
[5397, 1376277, 84215045, 286331153, 352326912, 353697792, 1145324612, 1347440720, 2863311530],
[7167, 15597806, 185273099, 286331153, 469696512, 1145324612, 2863311530, 2964369584, 3993038336],
[48063, 11468975, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 2936057600, 3149856768],
[43947, 11206827, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2880110592, 2964369584],
[21845, 12255419, 185273099, 286331153, 1145324612, 1431633920, 2863311530, 2964369584, 3137387264],
[22015, 11206827, 185273099, 286331153, 1145324612, 1442775040, 2863311530, 2868947712, 2964369584],
[17647, 15663343, 185273099, 286331153, 1145324612, 1156513792, 2863311530, 2964369584, 4009815808],
[21855, 5177423, 185273099, 286331153, 1145324612, 1325420288, 1432289280, 2863311530, 2964369584],
[44015, 15597806, 185273099, 286331153, 1145324612, 2863311530, 2884567040, 2964369584, 3993038336],
[45489, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 2981167104, 4009815808],
[6939, 15663343, 185273099, 286331153, 454754304, 1145324612, 2863311530, 2964369584, 4009815808],
[61183, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 4009689088],
[61166, 12255419, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 3137387264, 4008574976],
[47803, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 3132817408],
[6939, 1769499, 185273099, 286331153, 452991744, 454754304, 1145324612, 2863311530, 2964369584],
[43963, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2881159168, 2964369584],
[61166, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 4008574976],
[7099, 11206827, 185273099, 286331153, 465240064, 1145324612, 2863311530, 2868947712, 2964369584],
[47802, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 3132751872, 4009815808],
[62719, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 4110352384],
[61167, 11206827, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2964369584, 4008640512],
[45499, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 2981822464],
[20319, 1769499, 185273099, 286331153, 452991744, 1145324612, 1331625984, 2863311530, 2964369584],
[45499, 11206827, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2964369584, 2981822464],
[45489, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 2981167104],
[47803, 11206827, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2964369584, 3132817408],
[47802, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584, 3132751872],
[5567, 11468975, 84215045, 286331153, 364838912, 1145324612, 1347440720, 2863311530, 2936057600],
[21845, 14614751, 50529027, 808464432, 1431633920, 2863311530, 3435973836, 3741376256],
[61439, 5570645, 50529027, 808464432, 1426085120, 2863311530, 3435973836, 4026466304],
[21845, 3342387, 117901063, 855651072, 1431633920, 1886417008, 2863311530, 3435973836],
[21845, 5701719, 50529027, 808464432, 1431633920, 1459640064, 2863311530, 3435973836],
[1799, 3342387, 117899264, 855651072, 1431655765, 1886417008, 2863311530, 3435973836],
[43690, 3342387, 117901063, 855651072, 1431655765, 1886417008, 2863267840, 3435973836],
[223, 14614528, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3741376256],
[44031, 5570645, 50529027, 808464432, 1426085120, 2863311530, 2885615616, 3435973836],
[43690, 14614751, 50529027, 808464432, 1431655765, 2863267840, 3435973836, 3741376256],
[4379, 1769499, 185273099, 286331153, 286982144, 452991744, 1145324612, 2863311530, 2964369584],
[5397, 11468975, 84215045, 286331153, 353697792, 1145324612, 1347440720, 2863311530, 2936057600],
[4543, 11468975, 84215045, 286331153, 297730048, 1145324612, 1347440720, 2863311530, 2936057600],
[1455, 11468975, 84215045, 95354880, 286331153, 1145324612, 1347440720, 2863311530, 2936057600],
[43691, 11206827, 185273099, 286331153, 1145324612, 2863311530, 2863333376, 2868947712, 2964369584],
[3055, 15597806, 185273099, 200212480, 286331153, 1145324612, 2863311530, 2964369584, 3993038336],
[4539, 11206827, 185273099, 286331153, 297467904, 1145324612, 2863311530, 2868947712, 2964369584],
[47802, 11206827, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2964369584, 3132751872],
[45489, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 2981167104],
[45243, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 2965045248],
[43758, 15597806, 185273099, 286331153, 1145324612, 2863311530, 2867724288, 2964369584, 3993038336],
[20303, 1769499, 185273099, 286331153, 452991744, 1145324612, 1330577408, 2863311530, 2964369584],
[43707, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2864381952, 2964369584],
[48059, 11468975, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 2936057600, 3149594624],
[43947, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2880110592, 2964369584],
[47802, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 3132751872],
[45243, 11206827, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2964369584, 2965045248],
[2843, 1769499, 185273099, 186318848, 286331153, 452991744, 1145324612, 2863311530, 2964369584],
[2987, 11206827, 185273099, 195756032, 286331153, 1145324612, 2863311530, 2868947712, 2964369584],
[1301, 1376277, 84215045, 85262336, 286331153, 352326912, 1145324612, 1347440720, 2863311530],
[45311, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584, 2969501696],
[17493, 1376277, 84215045, 286331153, 352326912, 1145324612, 1146421248, 1347440720, 2863311530],
[17733, 1376277, 84215045, 286331153, 352326912, 1145324612, 1162149888, 1347440720, 2863311530],
[21588, 1376277, 84215045, 286331153, 352326912, 1145324612, 1347440720, 1414791168, 2863311530],
[2895, 5177423, 185273099, 189726720, 286331153, 1145324612, 1325420288, 2863311530, 2964369584],
[43947, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2880110592, 2964369584],
[4447, 5177423, 185273099, 286331153, 291438592, 1145324612, 1325420288, 2863311530, 2964369584],
[43759, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2867789824, 2964369584],
[61166, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584, 4008574976],
[20735, 11468975, 84215045, 286331153, 1145324612, 1347440720, 1358888960, 2863311530, 2936057600],
[43711, 1376277, 84215045, 286331153, 352326912, 1145324612, 1347440720, 2863311530, 2864644096],
[17647, 11206827, 185273099, 286331153, 1145324612, 1156513792, 2863311530, 2868947712, 2964369584],
[17487, 5177423, 185273099, 286331153, 1145324612, 1146028032, 1325420288, 2863311530, 2964369584],
[61680, 983055, 251662080, 858993459, 1431655765, 2863311530, 3435973836, 4042260480],
[62708, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 4109631488],
[20817, 11468975, 84215045, 286331153, 1145324612, 1347440720, 1364262912, 2863311530, 2936057600],
[17503, 1769499, 185273099, 286331153, 452991744, 1145324612, 1147076608, 2863311530, 2964369584],
[61166, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584, 4008574976],
[62708, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584, 4109631488],
[47802, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584, 3132751872],
[64250, 11468975, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 2936057600, 4210688000],
[43695, 11468975, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 2863595520, 2936057600],
[15, 983040, 251662080, 858993459, 1431655765, 2863311530, 3435973836, 4042322160],
[52428, 14614751, 50529027, 808464432, 1431655765, 2863311530, 3435921408, 3741376256],
[21845, 13566159, 50529027, 808464432, 1431633920, 2863311530, 3435973836, 3472936704],
[65023, 196611, 50332416, 808464432, 1431655765, 2863311530, 3435973836, 4261347328],
[51, 3342336, 117901063, 855651072, 1431655765, 1886417008, 2863311530, 3435973836],
[771, 14614751, 50528256, 808464432, 1431655765, 2863311530, 3435973836, 3741376256],
[21845, 3342387, 50529027, 808464432, 855651072, 1431633920, 2863311530, 3435973836],
[87, 5701632, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435973836],
[771, 5701719, 50528256, 808464432, 1431655765, 1459640064, 2863311530, 3435973836],
[43690, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863267840, 3435973836],
[52428, 11141290, 117901063, 858993459, 1431655765, 1886417008, 2852170240, 3435921408],
[51, 3342336, 50529027, 808464432, 855651072, 1431655765, 2863311530, 3435973836],
[12336, 14614751, 50529027, 808452096, 1431655765, 2863311530, 3435973836, 3741376256],
[64767, 196611, 50332416, 808464432, 1431655765, 2863311530, 3435973836, 4244570112],
[30071, 196611, 50332416, 808464432, 1431655765, 1970733056, 2863311530, 3435973836],
[52428, 3342387, 117901063, 855651072, 1431655765, 1886417008, 2863311530, 3435921408],
[855, 5570645, 50529027, 56033280, 808464432, 1426085120, 2863311530, 3435973836],
[207, 13565952, 50529027, 808464432, 1431655765, 2863311530, 3435973836, 3472936704],
[771, 13566159, 50528256, 808464432, 1431655765, 2863311530, 3435973836, 3472936704],
[22495, 13369548, 50529027, 808464432, 1431655765, 1474232320, 2863311530, 3422604288],
[43690, 458759, 117442304, 858993459, 1431655765, 1886417008, 2863267840, 3435973836],
[52428, 13566159, 50529027, 808464432, 1431655765, 2863311530, 3435921408, 3472936704],
[56799, 196611, 50332416, 808464432, 1431655765, 2863311530, 3435973836, 3722379264],
[65279, 720907, 184552192, 286331153, 1145324612, 2863311530, 2964369584, 4278124544],
[2827, 15663343, 185270272, 286331153, 1145324612, 2863311530, 2964369584, 4009815808],
[4369, 6226015, 185273099, 286326784, 1145324612, 1593859840, 2863311530, 2964369584],
[95, 6225920, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964369584],
[85, 5570560, 84215045, 286331153, 1145324612, 1347440720, 1426085120, 2863311530],
[43690, 15663343, 185273099, 286331153, 1145324612, 2863267840, 2964369584, 4009815808],
[24575, 11141290, 185273099, 286331153, 1145324612, 1610547200, 2852170240, 2964369584],
[4369, 12255419, 185273099, 286326784, 1145324612, 2863311530, 2964369584, 3137387264],
[239, 15663104, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 4009815808],
[191, 12517376, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 3204497152],
[48127, 15663343, 16843009, 269488144, 1145324612, 2863311530, 3154051072, 4009815808],
[187, 12255232, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 3137387264],
[65279, 15663343, 16843009, 269488144, 1145324612, 2863311530, 4009815808, 4278124544],
[22015, 15663343, 16843009, 269488144, 1145324612, 1442775040, 2863311530, 4009815808],
[2827, 6226015, 185270272, 286331153, 1145324612, 1593859840, 2863311530, 2964369584],
[61439, 1114129, 185273099, 285217024, 1145324612, 2863311530, 2964369584, 4026466304],
[61423, 15663343, 16843009, 269488144, 1145324612, 2863311530, 4009815808, 4025417728],
[43690, 12255419, 185273099, 286331153, 1145324612, 2863267840, 2964369584, 3137387264],
[62975, 720907, 184552192, 286331153, 1145324612, 2863311530, 2964369584, 4127129600],
[1285, 12517567, 84213760, 286331153, 1145324612, 1347440720, 2863311530, 3204497152],
[64511, 327685, 83887360, 286331153, 1145324612, 1347440720, 2863311530, 4227792896],
[1285, 11468975, 84213760, 286331153, 1145324612, 1347440720, 2863311530, 2936057600],
[43963, 1114129, 185273099, 285217024, 1145324612, 2863311530, 2881159168, 2964369584],
[61167, 720907, 184552192, 286331153, 1145324612, 2863311530, 2964369584, 4008640512],
[62719, 720907, 184552192, 286331153, 1145324612, 2863311530, 2964369584, 4110352384],
[61167, 15663343, 16843009, 269488144, 1145324612, 2863311530, 4008640512, 4009815808],
[43690, 15597806, 185273099, 286331153, 1145324612, 2863267840, 2964369584, 3993038336],
[45232, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863311530, 2964324352],
[45232, 15663343, 185273099, 286331153, 1145324612, 2863311530, 2964324352, 4009815808],
[4369, 15663343, 185273099, 286326784, 1145324612, 2863311530, 2964369584, 4009815808],
[17476, 12517567, 84215045, 286331153, 1145307136, 1347440720, 2863311530, 3204497152],
[7099, 11141290, 185273099, 286331153, 465240064, 1145324612, 2852170240, 2964369584],
[48063, 327685, 83887360, 286331153, 1145324612, 1347440720, 2863311530, 3149856768],
[22015, 11141290, 185273099, 286331153, 1145324612, 1442775040, 2852170240, 2964369584],
[21759, 15663343, 16843009, 269488144, 1145324612, 1425997824, 2863311530, 4009815808],
[21855, 720907, 184552192, 286331153, 1145324612, 1432289280, 2863311530, 2964369584],
[65278, 15663343, 16843009, 269488144, 1145324612, 2863311530, 4009815808, 4278059008],
[64255, 327685, 83887360, 286331153, 1145324612, 1347440720, 2863311530, 4211015680],
[2827, 5177423, 185270272, 286331153, 1145324612, 1325420288, 2863311530, 2964369584],
[61183, 1114129, 185273099, 285217024, 1145324612, 2863311530, 2964369584, 4009689088],
[20319, 1114129, 185273099, 285217024, 1145324612, 1331625984, 2863311530, 2964369584],
[44015, 15663343, 16843009, 269488144, 1145324612, 2863311530, 2884567040, 4009815808],
[47803, 720907, 184552192, 286331153, 1145324612, 2863311530, 2964369584, 3132817408],
[20463, 11141290, 185273099, 286331153, 1145324612, 1341063168, 2852170240, 2964369584],
[4369, 1769499, 185273099, 286326784, 452991744, 1145324612, 2863311530, 2964369584],
[45499, 720907, 184552192, 286331153, 1145324612, 2863311530, 2964369584, 2981822464],
[47871, 15663343, 16843009, 269488144, 1145324612, 2863311530, 3137273856, 4009815808],
[1285, 1376277, 84213760, 286331153, 352326912, 1145324612, 1347440720, 2863311530],
[4607, 15663343, 16843009, 269488144, 301924352, 1145324612, 2863311530, 4009815808],
[17903, 15663343, 16843009, 269488144, 1145324612, 1173291008, 2863311530, 4009815808],
[2827, 11206827, 185270272, 286331153, 1145324612, 2863311530, 2868947712, 2964369584],
[20821, 327685, 83887360, 286331153, 1145324612, 1347440720, 1364525056, 2863311530],
[43690, 11206827, 185273099, 286331153, 1145324612, 2863267840, 2868947712, 2964369584],
[2827, 1769499, 185270272, 286331153, 452991744, 1145324612, 2863311530, 2964369584],
[43690, 6226015, 185273099, 286331153, 1145324612, 1593859840, 2863267840, 2964369584],
[52428, 5701719, 50529027, 808464432, 1431655765, 1459640064, 2863311530, 3435921408],
[170, 11141120, 117901063, 858993459, 1431655765, 1886417008, 2852170240, 3435973836],
[12336, 5701719, 50529027, 808452096, 1431655765, 1459640064, 2863311530, 3435973836],
[21847, 196611, 50332416, 808464432, 1431655765, 1431764992, 2863311530, 3435973836],
[28784, 458759, 117442304, 858993459, 1431655765, 1886388224, 2863311530, 3435973836],
[7, 458752, 117442304, 858993459, 1431655765, 1886417008, 2863311530, 3435973836],
[12339, 196611, 50332416, 808464432, 808648704, 1431655765, 2863311530, 3435973836],
[771, 196611, 50332416, 50528256, 808464432, 1431655765, 2863311530, 3435973836],
[52428, 3342387, 50529027, 808464432, 855651072, 1431655765, 2863311530, 3435921408],
[52431, 196611, 50332416, 808464432, 1431655765, 2863311530, 3435973836, 3436118016],
[975, 13369548, 50529027, 63897600, 808464432, 1431655765, 2863311530, 3422604288],
[12336, 13566159, 50529027, 808452096, 1431655765, 2863311530, 3435973836, 3472936704],
[171, 11206656, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2964369584],
[43690, 12517567, 84215045, 286331153, 1145324612, 1347440720, 2863267840, 3204497152],
[61439, 1114129, 16843009, 269488144, 285217024, 1145324612, 2863311530, 4026466304],
[17647, 15663343, 16843009, 269488144, 1145324612, 1156513792, 2863311530, 4009815808],
[4373, 327685, 83887360, 286331153, 286588928, 1145324612, 1347440720, 2863311530],
[2827, 720907, 184552192, 185270272, 286331153, 1145324612, 2863311530, 2964369584],
[4379, 720907, 184552192, 286331153, 286982144, 1145324612, 2863311530, 2964369584],
[1285, 327685, 83887360, 84213760, 286331153, 1145324612, 1347440720, 2863311530],
[20565, 327685, 83887360, 286331153, 1145324612, 1347440720, 1347747840, 2863311530],
[43691, 720907, 184552192, 286331153, 1145324612, 2863311530, 2863333376, 2964369584],
[48127, 4522053, 16843009, 269488144, 1145324612, 1157645568, 2863311530, 3154051072],
[17733, 15663343, 16843009, 269488144, 1145324612, 1162149888, 2863311530, 4009815808],
[79, 5177344, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964369584],
[45243, 720907, 184552192, 286331153, 1145324612, 2863311530, 2964369584, 2965045248],
[27, 1769472, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964369584],
[65279, 4522053, 16843009, 269488144, 1145324612, 1157645568, 2863311530, 4278124544],
[17476, 1376277, 84215045, 286331153, 352326912, 1145307136, 1347440720, 2863311530],
[45232, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863311530, 2964324352],
[43690, 1769499, 185273099, 286331153, 452991744, 1145324612, 2863267840, 2964369584],
[45232, 11206827, 185273099, 286331153, 1145324612, 2863311530, 2868947712, 2964324352],
[4369, 11468975, 84215045, 286326784, 1145324612, 1347440720, 2863311530, 2936057600],
[43690, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863267840, 2964369584],
[61183, 1769499, 168430090, 286331153, 452991744, 1145324612, 2694881440, 4009689088],
[21, 1376256, 84215045, 286331153, 352326912, 1145324612, 1347440720, 2863311530],
[175, 11468800, 84215045, 286331153, 1145324612, 1347440720, 2863311530, 2936057600],
[238, 15597568, 185273099, 286331153, 1145324612, 2863311530, 2964369584, 3993038336],
[2843, 1114129, 185273099, 186318848, 285217024, 1145324612, 2863311530, 2964369584],
[495, 15663343, 16843009, 32440320, 269488144, 1145324612, 2863311530, 4009815808],
[4351, 15663343, 16843009, 269488144, 285147136, 1145324612, 2863311530, 4009815808],
[4539, 11141290, 185273099, 286331153, 297467904, 1145324612, 2852170240, 2964369584],
[61166, 15663343, 16843009, 269488144, 1145324612, 2863311530, 4008574976, 4009815808],
[4369, 1114129, 185273099, 285217024, 286326784, 1145324612, 2863311530, 2964369584],
[4369, 5177423, 185273099, 286326784, 1145324612, 1325420288, 2863311530, 2964369584],
[2987, 11141290, 185273099, 195756032, 286331153, 1145324612, 2852170240, 2964369584],
[17476, 15663343, 185273099, 286331153, 1145307136, 2863311530, 2964369584, 4009815808],
[22015, 11206827, 16843009, 269488144, 1145324612, 1442775040, 2863311530, 2868947712],
[17476, 6226015, 185273099, 286331153, 1145307136, 1593859840, 2863311530, 2964369584],
[43707, 1114129, 185273099, 285217024, 1145324612, 2863311530, 2864381952, 2964369584],
[43947, 15663343, 16843009, 269488144, 1145324612, 2863311530, 2880110592, 4009815808],
[65279, 11206827, 16843009, 269488144, 1145324612, 2863311530, 2868947712, 4278124544],
[43759, 15663343, 16843009, 269488144, 1145324612, 2863311530, 2867789824, 4009815808],
[4369, 11206827, 185273099, 286326784, 1145324612, 2863311530, 2868947712, 2964369584],
[43690, 11141290, 185273099, 286331153, 1145324612, 2852170240, 2863267840, 2964369584],
[4369, 15663343, 16843009, 269488144, 286326784, 1145324612, 2863311530, 4009815808],
[17749, 1114129, 16843009, 269488144, 285217024, 1145324612, 1163198464, 2863311530],
[43690, 11468975, 84215045, 286331153, 1145324612, 1347440720, 2863267840, 2936057600],
[17903, 11206827, 16843009, 269488144, 1145324612, 1173291008, 2863311530, 2868947712],
[4369, 15597806, 185273099, 286326784, 1145324612, 2863311530, 2964369584, 3993038336],
[4539, 11206827, 16843009, 269488144, 297467904, 1145324612, 2863311530, 2868947712],
[17646, 11141290, 185273099, 286331153, 1145324612, 1156448256, 2852170240, 2964369584],
[58623, 1769499, 168430090, 286331153, 452991744, 1145324612, 2694881440, 3841916928],
[20560, 11468975, 84215045, 286331153, 1145324612, 1347420160, 2863311530, 2936057600],
[4437, 4522053, 16843009, 269488144, 290783232, 1145324612, 1157645568, 2863311530],
[44015, 4456516, 185273099, 286331153, 1140868096, 2863311530, 2884567040, 2964369584],
[47802, 15663343, 16843009, 269488144, 1145324612, 2863311530, 3132751872, 4009815808],
[5567, 11141290, 84215045, 286331153, 364838912, 1145324612, 1347440720, 2852170240],
[61167, 11206827, 16843009, 269488144, 1145324612, 2863311530, 2868947712, 4008640512],
[17487, 720907, 184552192, 286331153, 1145324612, 1146028032, 2863311530, 2964369584],
[21855, 1769499, 168430090, 286331153, 452991744, 1145324612, 1432289280, 2694881440],
[47803, 11206827, 16843009, 269488144, 1145324612, 2863311530, 2868947712, 3132817408],
[4369, 1114129, 16843009, 269488144, 285217024, 286326784, 1145324612, 2863311530],
[43947, 11206827, 16843009, 269488144, 1145324612, 2863311530, 2868947712, 2880110592],
[45232, 5177423, 185273099, 286331153, 1145324612, 1325420288, 2863311530, 2964324352],
[17476, 5177423, 185273099, 286331153, 1145307136, 1325420288, 2863311530, 2964369584],
[17733, 4522053, 16843009, 269488144, 1145324612, 1157645568, 1162149888, 2863311530],
[20063, 1769499, 168430090, 286331153, 452991744, 1145324612, 1314848768, 2694881440],
[21589, 4522053, 16843009, 269488144, 1145324612, 1157645568, 1414856704, 2863311530],
[43695, 327685, 83887360, 286331153, 1145324612, 1347440720, 2863311530, 2863595520],
[17493, 1114129, 185273099, 285217024, 1145324612, 1146421248, 2863311530, 2964369584],
[17476, 12255419, 185273099, 286331153, 1145307136, 2863311530, 2964369584, 3137387264],
[44015, 4522053, 16843009, 269488144, 1145324612, 1157645568, 2863311530, 2884567040],
[47871, 4522053, 16843009, 269488144, 1145324612, 1157645568, 2863311530, 3137273856],
[43963, 1114129, 16843009, 269488144, 285217024, 1145324612, 2863311530, 2881159168],
[61167, 4522053, 16843009, 269488144, 1145324612, 1157645568, 2863311530, 4008640512],
[7007, 4456516, 185273099, 286331153, 459210752, 1140868096, 2863311530, 2964369584],
[43690, 5570645, 84215045, 286331153, 1145324612, 1347440720, 1426085120, 2863267840],
[21588, 15663343, 16843009, 269488144, 1145324612, 1414791168, 2863311530, 4009815808],
[6939, 1769499, 168430090, 286331153, 452991744, 454754304, 1145324612, 2694881440],
[21759, 11206827, 16843009, 269488144, 1145324612, 1425997824, 2863311530, 2868947712],
[85, 5570560, 50529027, 808464432, 1426085120, 2863311530, 3435973836],
[43690, 5570645, 50529027, 808464432, 1426085120, 2863267840, 3435973836],
[4283, 11206827, 16843009, 269488144, 280690688, 1145324612, 2863311530, 2868947712],
[4369, 4522053, 16843009, 269488144, 286326784, 1145324612, 1157645568, 2863311530],
[17503, 1769499, 168430090, 286331153, 452991744, 1145324612, 1147076608, 2694881440],
[2587, 1769499, 168430090, 169541632, 286331153, 452991744, 1145324612, 2694881440],
[61166, 4522053, 16843009, 269488144, 1145324612, 1157645568, 2863311530, 4008574976],
[43759, 4522053, 16843009, 269488144, 1145324612, 1157645568, 2863311530, 2867789824],
[43690, 1376277, 84215045, 286331153, 352326912, 1145324612, 1347440720, 2863267840],
[17647, 11206827, 16843009, 269488144, 1145324612, 1156513792, 2863311530, 2868947712],
[17476, 1769499, 185273099, 286331153, 452991744, 1145307136, 2863311530, 2964369584],
[43947, 4522053, 16843009, 269488144, 1145324612, 1157645568, 2863311530, 2880110592],
[20046, 1769499, 168430090, 286331153, 452991744, 1145324612, 1313734656, 2694881440],
[21588, 4522053, 16843009, 269488144, 1145324612, 1157645568, 1414791168, 2863311530],
[17477, 4522053, 16843009, 269488144, 1145324612, 1145372672, 1157645568, 2863311530],
[43691, 11206827, 16843009, 269488144, 1145324612, 2863311530, 2863333376, 2868947712],
[47802, 11206827, 16843009, 269488144, 1145324612, 2863311530, 2868947712, 3132751872],
[1455, 11141290, 84215045, 95354880, 286331153, 1145324612, 1347440720, 2852170240],
[61166, 11206827, 16843009, 269488144, 1145324612, 2863311530, 2868947712, 4008574976],
[2895, 4456516, 185273099, 189726720, 286331153, 1140868096, 2863311530, 2964369584],
[4181, 4522053, 16843009, 269488144, 274006016, 1145324612, 1157645568, 2863311530],
[17476, 11206827, 185273099, 286331153, 1145307136, 2863311530, 2868947712, 2964369584],
[325, 4522053, 16843009, 21299200, 269488144, 1145324612, 1157645568, 2863311530],
[43707, 1114129, 16843009, 269488144, 285217024, 1145324612, 2863311530, 2864381952],
[273, 1114129, 16843009, 17891328, 269488144, 285217024, 1145324612, 2863311530],
[427, 11206827, 16843009, 27983872, 269488144, 1145324612, 2863311530, 2868947712],
[43690, 11141290, 84215045, 286331153, 1145324612, 1347440720, 2852170240, 2863267840],
[61166, 1114129, 16843009, 269488144, 285217024, 1145324612, 2863311530, 4008574976],
[4369, 327685, 83887360, 286326784, 1145324612, 1347440720, 2863311530],
[58596, 1769499, 168430090, 286331153, 452991744, 1145324612, 2694881440, 3840147456],
[239, 15663104, 16843009, 269488144, 1145324612, 2863311530, 4009815808],
[2827, 11141290, 185270272, 286331153, 1145324612, 2852170240, 2964369584],
[47802, 4522053, 16843009, 269488144, 1145324612, 1157645568, 2863311530, 3132751872],
[2827, 1114129, 185270272, 285217024, 1145324612, 2863311530, 2964369584],
[3, 196608, 50332416, 808464432, 1431655765, 2863311530, 3435973836],
[12336, 196611, 50332416, 808452096, 1431655765, 2863311530, 3435973836],
[204, 13369344, 50529027, 808464432, 1431655765, 2863311530, 3422604288],
[5, 327680, 83887360, 286331153, 1145324612, 1347440720, 2863311530],
[17, 1114112, 185273099, 285217024, 1145324612, 2863311530, 2964369584],
[257, 15663343, 16842752, 269488144, 1145324612, 2863311530, 4009815808],
[20560, 327685, 83887360, 286331153, 1145324612, 1347420160, 2863311530],
[17476, 15663343, 16843009, 269488144, 1145307136, 2863311530, 4009815808],
[11, 720896, 184552192, 286331153, 1145324612, 2863311530, 2964369584],
[43690, 15663343, 16843009, 269488144, 1145324612, 2863267840, 4009815808],
[43690, 1114129, 185273099, 285217024, 1145324612, 2863267840, 2964369584],
[65279, 65537, 16777472, 269488144, 1145324612, 2863311530, 4278124544],
[45232, 720907, 184552192, 286331153, 1145324612, 2863311530, 2964324352],
[170, 11141120, 185273099, 286331153, 1145324612, 2852170240, 2964369584],
[17903, 11141290, 16843009, 269488144, 1145324612, 1173291008, 2852170240],
[257, 11206827, 16842752, 269488144, 1145324612, 2863311530, 2868947712],
[27, 1769472, 168430090, 286331153, 452991744, 1145324612, 2694881440],
[17, 1114112, 16843009, 269488144, 285217024, 1145324612, 2863311530],
[69, 4521984, 16843009, 269488144, 1145324612, 1157645568, 2863311530],
[61167, 65537, 16777472, 269488144, 1145324612, 2863311530, 4008640512],
[47803, 65537, 16777472, 269488144, 1145324612, 2863311530, 3132817408],
[2570, 1769499, 168427520, 286331153, 452991744, 1145324612, 2694881440],
[17476, 4522053, 16843009, 269488144, 1145307136, 1157645568, 2863311530],
[21589, 65537, 16777472, 269488144, 1145324612, 1414856704, 2863311530],
[17476, 720907, 184552192, 286331153, 1145307136, 2863311530, 2964369584],
[43690, 327685, 83887360, 286331153, 1145324612, 1347440720, 2863267840],
[43690, 11206827, 16843009, 269488144, 1145324612, 2863267840, 2868947712],
[17476, 1114129, 185273099, 285217024, 1145307136, 2863311530, 2964369584],
[44015, 4456516, 16843009, 269488144, 1140868096, 2863311530, 2884567040],
[4112, 15663343, 16843009, 269484032, 1145324612, 2863311530, 4009815808],
[257, 4522053, 16842752, 269488144, 1145324612, 1157645568, 2863311530],
[17476, 11141290, 185273099, 286331153, 1145307136, 2852170240, 2964369584],
[171, 11206656, 16843009, 269488144, 1145324612, 2863311530, 2868947712],
[43691, 65537, 16777472, 269488144, 1145324612, 2863311530, 2863333376],
[43690, 4522053, 16843009, 269488144, 1145324612, 1157645568, 2863267840],
[4112, 11206827, 16843009, 269484032, 1145324612, 2863311530, 2868947712],
[4112, 4522053, 16843009, 269484032, 1145324612, 1157645568, 2863311530],
[17477, 65537, 16777472, 269488144, 1145324612, 1145372672, 2863311530],
[17476, 1769499, 168430090, 286331153, 452991744, 1145307136, 2694881440],
[17476, 11206827, 16843009, 269488144, 1145307136, 2863311530, 2868947712],
[427, 11141290, 16843009, 27983872, 269488144, 1145324612, 2852170240],
[170, 11141120, 84215045, 286331153, 1145324612, 1347440720, 2852170240],
[43690, 1114129, 16843009, 269488144, 285217024, 1145324612, 2863267840],
[17476, 1114129, 16843009, 269488144, 285217024, 1145307136, 2863311530],
[4113, 65537, 16777472, 269488144, 269549568, 1145324612, 2863311530],
[257, 65537, 16777472, 16842752, 269488144, 1145324612, 2863311530],
[68, 4456448, 185273099, 286331153, 1140868096, 2863311530, 2964369584],
[325, 4456516, 16843009, 21299200, 269488144, 1140868096, 2863311530],
[1, 65536, 16777472, 269488144, 1145324612, 2863311530],
[170, 11141120, 16843009, 269488144, 1145324612, 2852170240],
[4112, 65537, 16777472, 269484032, 1145324612, 2863311530],
[17476, 11141290, 16843009, 269488144, 1145307136, 2852170240],
[17476, 65537, 16777472, 269488144, 1145307136, 2863311530],
[43690, 65537, 16777472, 269488144, 1145324612, 2863267840]
]
def seedBank : Nat → Array (List (BitVec 32))
| 0 => seedBank0
| 1 => seedBank1
| 2 => seedBank2
| 3 => seedBank3
| 4 => seedBank4
| 5 => seedBank5
| _ => #[]
end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux
set_option maxRecDepth 65536 in
def rowBank0 : Array (Array Nat) := #[
#[0, 0]
]
set_option maxRecDepth 65536 in
def rowBank1 : Array (Array Nat) := #[
#[0, 1, 1025, 0]
]
set_option maxRecDepth 65536 in
def rowBank2 : Array (Array Nat) := #[
#[0, 2, 6146, 1, 38914, 1025, 2050, 2049, 33793, 0],
#[171010, 5, 2053, 3, 6, 4, 2052, 171010]
]
set_option maxRecDepth 65536 in
def rowBank3 : Array (Array Nat) := #[
#[0, 10, 10250, 2, 169994, 6146, 171010, 1, 956426, 38914, 695298, 1025, 59402, 2050, 957442, 2049, 13278210, 33793, 3082, 3074, 55298, 3073, 825346, 50177, 51202, 51201, 820225, 0],
#[3596290, 14, 11, 7, 6155, 6151, 3086, 3079, 55303, 4, 16, 6, 8, 3, 6160, 6150, 6152, 6147, 9, 5, 3078, 3075, 55302, 55299, 3077, 3596290],
#[224266, 31, 3103, 13, 29, 15, 3087, 13323, 1053, 1039, 50191, 29707, 30, 17, 481296, 12, 8869904, 1036, 3089, 3084, 50188, 224266],
#[3596301, 34, 10274, 27, 59426, 2075, 3106, 3099, 51227, 21, 39, 23, 10263, 19, 59415, 2067, 3095, 3091, 51219, 3596301],
#[3596305, 35, 32, 24, 41, 25, 224279, 22, 33, 28, 3107, 3096, 3100, 18, 26, 20, 3097, 3094, 3092, 3596305],
#[3596319, 43, 3115, 38, 45, 37, 3109, 224290, 44, 40, 3112, 13344, 46121, 36, 3108, 3596319],
#[3596318, 485420, 13356, 42, 46124, 2090, 13351, 485409, 8874028, 485415, 3114, 13345, 51242, 46113, 8874017, 3596318]
]
set_option maxRecDepth 65536 in
def rowBank4 : Array (Array Nat) := #[
#[0, 164, 13476, 13, 223396, 10253, 224269, 2, 3578020, 169997, 3594253, 6146, 187405, 171010, 3596290, 1, 20355236, 956429, 16177165, 38914, 973837, 695298, 11984898, 1025, 1271972, 59405, 1010701, 2050, 1235981, 957442, 16179202, 2049, 17751053, 13278210, 213311490, 33793, 79012, 3085, 1272845, 3074, 20371469, 55298, 20373506, 3073, 284612621, 825346, 280420354, 50177, 17787917, 51202, 284614658, 51201, 4508278786, 820225, 4260, 4109, 75789, 4098, 1218573, 71682, 1219586, 4097, 17733645, 1087490, 17472514, 66561, 1107981, 67586, 17734658, 67585, 281713666, 1082369, 68621, 68610, 1103874, 68609, 17602562, 1098753, 1099778, 1099777, 17597441, 0],
#[66790402, 182, 177, 17, 10417, 10257, 14, 12, 170161, 170001, 6158, 6156, 171022, 171020, 4278, 4113, 75793, 4108, 1218577, 71692, 1219596, 6, 179, 19, 25, 11, 10265, 10251, 9, 5, 6323, 6163, 6169, 6155, 170009, 169995, 6153, 6149, 23, 10, 8, 4, 171187, 171027, 171033, 171019, 7193, 7179, 171017, 171013, 10263, 10250, 10248, 10244, 170007, 169994, 169992, 169988, 7, 3, 4115, 4107, 75787, 4101, 71699, 71691, 1218571, 71685, 4106, 4100, 1219603, 1219595, 72715, 1219589, 75786, 75780, 1218570, 1218564, 4099, 66790402],
#[4173837, 218, 183, 74, 10423, 10314, 4314, 4170, 75850, 18, 215, 71, 68, 21, 10308, 10261, 4167, 4117, 75797, 15374, 1239, 1095, 1092, 1045, 26692, 26645, 66631, 66581, 1075221, 31758, 216, 73, 72, 20, 70, 24, 514073, 16, 1094, 1048, 8902681, 1040, 10456, 10313, 10312, 10260, 10310, 10264, 8297497, 10256, 26694, 26648, 142515225, 26640, 69, 22, 142514199, 15, 3363739671, 1039, 4169, 4116, 4120, 4112, 66584, 66576, 75849, 75796, 75800, 75792, 1075224, 1075216, 4118, 4111, 66575, 4173837],
#[66790420, 238, 222, 132, 192, 85, 83, 45, 202, 87, 142, 55, 264, 128, 129, 42, 139, 66, 56, 31, 241, 121, 92, 58, 78, 51, 4334, 4228, 4181, 4141, 4217, 4154, 4147, 38, 276, 122, 100, 48, 144, 47, 49, 40, 111, 43, 44, 26, 99, 46, 67, 39, 119, 41, 50, 36, 53, 34, 4183, 4151, 4224, 4138, 4162, 4127, 4218, 4144, 4143, 4136, 4139, 4122, 4142, 4135, 4137, 4132, 4130, 66790420],
#[66790418, 246, 13558, 134, 185, 88, 13400, 63, 6329, 6232, 219224, 6207, 79094, 3206, 78936, 3135, 1267800, 55359, 4342, 4230, 4184, 4159, 71768, 71743, 68742, 68671, 1103935, 32, 271, 104, 13416, 57, 123, 259128, 15416, 28, 6415, 6248, 219240, 6201, 6267, 4151352, 251960, 6172, 126, 59, 13371, 35, 78952, 3129, 64568, 3100, 1267816, 55353, 1038392, 55324, 78907, 3107, 4200, 4153, 1045560, 4124, 71784, 71737, 16734264, 71708, 4155, 4131, 68665, 68636, 1103929, 1103900, 68643, 66790418],
#[66790422, 237, 245, 130, 205, 86, 143, 62, 6349, 6230, 6287, 6206, 266, 127, 137, 65, 6281, 6209, 260155, 30, 239, 120, 93, 54, 124, 61, 15404, 27, 6383, 6264, 6237, 6198, 6268, 6205, 251948, 6171, 79, 64, 4333, 4226, 4216, 4150, 71800, 71734, 4160, 33, 113, 60, 64565, 29, 6257, 6204, 1038389, 6173, 52, 37, 4182, 4158, 71766, 71742, 4223, 4161, 71745, 4126, 4157, 4123, 71741, 71707, 4156, 4125, 71740, 71709, 4133, 66790422],
#[66790473, 351, 255, 174, 231, 155, 145, 117, 280, 146, 166, 107, 374, 160, 159, 106, 172, 105, 260200, 94, 250, 163, 4447, 4270, 4259, 118, 156, 114, 4251, 4213, 4210, 15452, 348, 176, 154, 96, 169, 101, 252004, 75, 152, 109, 4272, 4192, 4205, 15453, 173, 115, 64611, 95, 167, 108, 1038455, 89, 64625, 91, 4242, 4203, 4256, 4202, 4201, 4190, 4197, 4171, 4211, 4191, 4204, 4185, 4187, 66790473],
#[66790474, 355, 277, 175, 208, 147, 4451, 4271, 4243, 98, 228, 148, 150, 103, 347, 171, 149, 102, 151, 110, 4244, 4199, 4267, 4198, 4206, 260184, 358, 162, 15505, 116, 153, 112, 4258, 4212, 4208, 15443, 377, 165, 252070, 133, 170, 141, 252046, 81, 157, 97, 15503, 80, 64671, 125, 64641, 82, 1038508, 140, 1038475, 77, 64649, 76, 4261, 4229, 4237, 4177, 4193, 4176, 4221, 4178, 4236, 4173, 4172, 66790474],
#[66790472, 352, 30048, 168, 197, 521369, 15513, 135, 286, 521372, 252074, 136, 1078624, 3240, 64665, 3207, 1038506, 3208, 15483, 521294, 29982, 12540074, 15516, 29832, 4448, 13104281, 213866666, 521339, 4264, 4231, 816264, 15438, 363, 12540073, 252073, 131, 158, 521340, 252048, 84, 29854, 12540048, 15484, 29780, 64668, 1078408, 68776, 68743, 17593480, 64590, 1038505, 3203, 1038480, 3156, 64636, 1078356, 13104284, 4232, 68744, 13104206, 213866665, 4227, 13104252, 4180, 213866640, 816212, 68739, 68692, 17593428, 66790472],
#[66790469, 353, 554337, 161, 272, 142563480, 15517, 138, 6416, 8909976, 252061, 6282, 17331553, 3233, 64669, 3210, 1038493, 55434, 15486, 8909903, 8870160, 142563485, 15512, 8870026, 522398, 142563439, 15471, 90, 554256, 8909981, 252056, 554122, 47262, 8909935, 252015, 554074, 4449, 3363788957, 210236573, 8909950, 4257, 210196618, 13137034, 15439, 64664, 277305482, 64623, 3162, 1038488, 17331338, 1038447, 17331290, 68769, 4505163914, 281572490, 64591, 3363788952, 4234, 210236568, 71818, 68746, 1104010, 210236495, 3363788911, 4186, 210236527, 13136986, 68698, 281572442, 66790469],
#[260260, 525, 4621, 220, 440, 219, 4315, 15543, 6584, 6363, 71899, 252087, 4103383, 181, 4277, 15537, 39352, 39131, 1087707, 776375, 12491991, 1205, 66741, 31921, 2488, 2267, 67803, 48311, 16686295, 2229, 67765, 48305, 213818583, 33973, 1082549, 556209, 516, 217, 780504, 180, 12490968, 6324, 8297651, 178, 213817560, 39092, 142515379, 1202, 13363416, 2228, 209624243, 2226, 3363740851, 33970, 4313, 4276, 71860, 4274, 1087668, 66738, 67764, 67762, 1082546, 260260],
#[66790583, 529, 478, 285, 4625, 223, 4381, 15568, 476, 234, 252132, 194, 3550, 3357, 68893, 64720, 1038564, 3266, 4330, 4290, 68802, 15545, 479, 261, 15591, 198, 4357, 15557, 4294, 15552, 540, 279, 252184, 200, 252190, 201, 252106, 190, 15632, 204, 15565, 189, 64743, 3270, 68806, 64704, 1038616, 3272, 1038538, 3262, 64717, 3261, 4375, 4296, 4297, 4286, 4300, 4285, 68808, 68798, 68797, 66790583],
#[66790580, 480, 530, 267, 537, 258, 289, 196, 474, 224, 229, 211, 247, 214, 260297, 186, 482, 236, 259, 212, 252, 195, 522444, 193, 526, 288, 240, 199, 230, 203, 4576, 4363, 4320, 4307, 4384, 4295, 4299, 188, 274, 207, 209, 191, 249, 206, 210, 184, 213, 187, 4354, 4292, 4310, 4282, 4332, 4308, 4291, 4289, 4303, 4287, 4302, 4280, 4283, 66790580],
#[4174044, 536, 13848, 365, 79384, 3437, 4632, 4461, 68973, 282, 531, 362, 13674, 281, 79210, 3353, 4458, 4377, 68889, 260319, 1555, 1386, 30058, 1305, 1078634, 50457, 66922, 66841, 1099033, 522463, 611, 381, 13693, 248, 375, 259361, 15649, 232, 1399, 521505, 32033, 1256, 79229, 3320, 64801, 3304, 818465, 50408, 4477, 4344, 1045793, 4328, 13104417, 66792, 68856, 68840, 1098984, 4174044],
#[66790618, 608, 4704, 369, 15838, 359, 4455, 15637, 252382, 6503, 72039, 252181, 607, 382, 64859, 251, 1038683, 6395, 4478, 4347, 71931, 260342, 545, 378, 4474, 15615, 522592, 257, 4353, 15582, 6689, 6522, 72058, 252159, 8362336, 6401, 71937, 252126, 8911201, 260, 4356, 15605, 64886, 263, 64776, 244, 1038710, 6407, 1038600, 6388, 64778, 243, 4359, 4340, 71943, 71924, 4339, 66790618],
#[66790619, 532, 533, 379, 605, 380, 260458, 278, 477, 354, 4628, 4475, 4450, 265, 350, 290, 4476, 4374, 4386, 260330, 534, 356, 364, 253, 368, 287, 522501, 235, 603, 370, 361, 270, 357, 254, 4466, 4366, 4350, 15589, 367, 256, 32003, 227, 383, 268, 64759, 225, 818428, 226, 4452, 4349, 4383, 4331, 4352, 4323, 4364, 4321, 4322, 66790619],
#[66790616, 604, 15905, 371, 15839, 12540261, 15718, 291, 252444, 349, 252281, 283, 65057, 3443, 64870, 3363, 1038713, 3355, 15631, 12540134, 4700, 12540279, 4467, 15610, 213866853, 522526, 4387, 15601, 535, 142563695, 252252, 284, 252267, 142563602, 252180, 221, 3363789167, 142579984, 4380, 15599, 68979, 64762, 68899, 64753, 1038684, 3356, 1038612, 3293, 68892, 64751, 4445, 4379, 68891, 213866726, 3363789074, 4317, 68829, 66790616],
#[4174041, 542, 543, 366, 614, 376, 260477, 262, 527, 360, 15721, 292, 64895, 273, 260375, 242, 1551, 1384, 32105, 1316, 818559, 1297, 522519, 1266, 546, 372, 4638, 4462, 4468, 269, 8362333, 275, 4456, 4388, 4371, 15600, 142580061, 1299, 66920, 66852, 66835, 31984, 373, 293, 64761, 233, 818425, 1257, 4472, 4358, 4369, 4338, 66833, 66802, 4389, 4329, 66793, 4174041],
#[66790669, 559, 13871, 396, 555, 418, 13730, 315, 684, 435, 13747, 338, 450, 327, 13639, 312, 565, 405, 13717, 331, 79407, 3468, 79266, 3387, 79253, 3403, 4655, 4492, 4514, 4411, 4501, 4427, 69004, 68923, 68939, 307, 458, 343, 13655, 300, 79283, 3410, 79175, 3384, 79191, 3372, 4531, 4434, 4423, 4408, 4439, 4396, 68946, 68920, 68908, 66790669],
#[66790648, 557, 567, 401, 10807, 10641, 413, 328, 578, 400, 430, 324, 10818, 10640, 10670, 10564, 434, 313, 336, 301, 616, 426, 395, 320, 10635, 10560, 4653, 4497, 76177, 4424, 4522, 4416, 76096, 299, 438, 323, 322, 296, 10678, 10563, 10562, 10536, 325, 295, 4496, 4420, 76176, 76100, 4409, 4397, 4419, 4392, 76099, 76072, 4391, 66790648],
#[66790693, 556, 549, 397, 577, 408, 456, 321, 649, 452, 385, 319, 428, 314, 316, 311, 553, 409, 406, 344, 576, 398, 455, 326, 464, 345, 260439, 309, 410, 340, 4652, 4493, 4548, 4415, 4505, 4440, 4436, 305, 432, 335, 332, 310, 337, 297, 4504, 4417, 4410, 4407, 4494, 4422, 4441, 4405, 4431, 4406, 4393, 66790693],
#[66790682, 552, 13864, 414, 223784, 10654, 224670, 341, 1272360, 59806, 1011102, 2389, 79400, 3486, 1273246, 3413, 17788318, 51541, 4648, 4510, 76190, 4437, 1108382, 67925, 69022, 68949, 1100117, 302, 690, 445, 13757, 4155728, 223677, 259408, 15696, 298, 1272253, 783696, 48464, 2346, 79293, 12544336, 64848, 3370, 834896, 51498, 4541, 16738640, 1045840, 4394, 13366608, 67882, 213870928, 68906, 1100074, 66790682],
#[66790662, 551, 562, 387, 550, 393, 391, 342, 651, 437, 416, 339, 399, 329, 4647, 4483, 4489, 4438, 4533, 4435, 4425, 303, 602, 392, 420, 318, 575, 389, 470, 333, 472, 317, 260423, 308, 462, 346, 15676, 306, 423, 330, 334, 294, 64844, 304, 4488, 4414, 4485, 4429, 4413, 4404, 4442, 4402, 4426, 4390, 4400, 66790662],
#[66790781, 639, 569, 486, 635, 485, 484, 473, 2683, 2533, 2532, 2521, 666, 512, 518, 441, 2566, 2489, 260541, 4155791, 660, 524, 4735, 4582, 4620, 4155842, 496, 448, 4581, 4569, 4544, 15755, 2544, 2496, 68069, 68057, 68032, 48523, 523, 4155820, 780726, 394, 13363638, 2442, 4608, 4537, 68025, 16738703, 16738732, 4490, 67978, 66790781],
#[66790766, 629, 601, 500, 592, 483, 4725, 4596, 4579, 460, 704, 519, 494, 468, 4174310, 443, 4615, 4564, 4539, 15751, 633, 495, 497, 461, 632, 492, 491, 467, 498, 459, 4591, 4557, 4588, 4563, 4555, 260514, 520, 457, 15816, 388, 517, 465, 64982, 386, 64967, 390, 4553, 4484, 4561, 4482, 4486, 66790766],
#[66790776, 627, 586, 507, 647, 509, 15854, 419, 678, 515, 4723, 4603, 4611, 436, 4174336, 453, 4605, 4515, 4549, 15776, 636, 510, 508, 429, 677, 503, 65029, 422, 522, 433, 260531, 411, 511, 427, 4606, 4525, 4523, 15745, 521, 421, 64935, 384, 64944, 415, 4599, 4518, 4529, 4507, 4517, 4480, 4511, 66790776],
#[66790773, 640, 46720, 488, 662, 783871, 15880, 447, 46742, 783880, 15871, 46527, 4174347, 783822, 15822, 404, 574, 493, 46573, 454, 1095296, 3560, 65032, 3519, 1095149, 3526, 15818, 783770, 4736, 13366792, 4589, 783818, 4584, 832959, 4550, 15770, 65023, 1095103, 64974, 3476, 69096, 69062, 17610175, 64922, 13366783, 4543, 13366734, 4500, 69055, 13366682, 69012, 66790773],
#[66790765, 638, 595, 502, 10835, 10742, 4734, 4598, 76278, 446, 631, 504, 505, 439, 10871, 10744, 10745, 10679, 506, 431, 4600, 4535, 76280, 76215, 4527, 4174238, 702, 513, 15844, 425, 256484, 10665, 4609, 4521, 76201, 15773, 1042950, 424, 48558, 417, 65030, 10664, 780718, 10657, 834994, 412, 4520, 4513, 76200, 76193, 4508, 66790765],
#[66790772, 615, 598, 501, 656, 489, 15857, 463, 715, 514, 15868, 442, 4174348, 451, 15780, 402, 600, 487, 4711, 4597, 4583, 449, 634, 499, 65010, 469, 490, 471, 4585, 4559, 4595, 4565, 4567, 260501, 784877, 466, 4610, 4538, 4562, 15766, 65034, 444, 64984, 403, 64976, 407, 4547, 4498, 4540, 4499, 4503, 66790772],
#[66790840, 694, 219830, 541, 1268406, 3613, 15891, 4151773, 4790, 4151827, 4637, 15837, 69149, 64989, 16734685, 260572, 695, 4151823, 32278, 481, 818710, 3553, 522719, 4151770, 219831, 8346134, 15887, 219617, 209672726, 498143, 1006049, 15834, 555543, 8346082, 32226, 475, 65039, 1268193, 17783265, 64986, 818658, 3547, 16734735, 4577, 69089, 16734682, 209672674, 4571, 69083, 66790840],
#[4174340, 730, 46810, 613, 1095386, 3685, 15971, 783906, 4168375, 783963, 15963, 544, 65115, 3616, 260636, 783886, 12556983, 8910427, 32347, 1568, 818779, 50720, 522780, 8910350, 4826, 783971, 4709, 15906, 13366875, 47644, 4640, 15886, 210237019, 555548, 67104, 32270, 69221, 65058, 69152, 65038, 1099296, 818702, 13366818, 13366798, 210236942, 4174340],
#[4174349, 728, 4824, 610, 729, 609, 4705, 260632, 4168374, 606, 4702, 15893, 65117, 539, 4635, 260625, 12556982, 1630, 67166, 32277, 818781, 1563, 67099, 522769, 785114, 612, 4708, 15903, 8362588, 547, 4643, 15890, 142580316, 1571, 67107, 32274, 65126, 538, 65049, 528, 818713, 1552, 4634, 4624, 67088, 4174349],
#[66790943, 732, 727, 641, 4828, 646, 4737, 15952, 755, 683, 16007, 588, 4779, 4174393, 4684, 15910, 738, 652, 16016, 570, 3799, 3713, 69249, 65104, 65168, 3642, 4748, 4666, 69178, 15915, 16022, 587, 15937, 563, 65159, 3660, 69196, 65062, 65089, 3635, 4683, 4659, 69171, 66790943],
#[66790946, 741, 725, 648, 16098, 644, 15993, 579, 759, 664, 15996, 591, 4174484, 581, 15962, 554, 4837, 657, 4744, 15960, 3797, 3720, 65145, 3651, 69256, 65112, 4740, 4675, 69187, 15925, 4760, 15934, 4687, 15913, 65148, 3663, 65114, 3626, 69199, 65065, 4677, 4650, 69162, 66790946],
#[66790936, 731, 4827, 622, 722, 619, 4715, 15955, 2770, 2667, 68203, 48723, 734, 623, 780919, 599, 13363831, 2647, 4719, 4695, 68183, 260648, 753, 682, 4778, 15929, 256635, 580, 4676, 15927, 1043067, 2628, 68164, 48695, 65178, 585, 780866, 568, 13363778, 2616, 4681, 4664, 68152, 66790936],
#[66790942, 736, 4832, 620, 16087, 621, 4717, 15961, 752, 672, 4768, 15946, 4174463, 583, 4679, 15922, 16085, 624, 4720, 15958, 740, 628, 65144, 593, 65146, 590, 4724, 4689, 4686, 260655, 785024, 571, 4667, 15909, 65189, 572, 65087, 566, 65088, 548, 4668, 4662, 4644, 66790942],
#[66790938, 724, 733, 642, 757, 643, 658, 596, 735, 618, 626, 597, 691, 582, 4174409, 561, 737, 655, 653, 589, 669, 594, 260683, 558, 645, 573, 4820, 4738, 4714, 4693, 4751, 4685, 4669, 564, 584, 560, 4739, 4692, 4678, 4657, 4690, 4654, 4656, 66790938],
#[66791009, 746, 758, 716, 764, 714, 697, 667, 750, 708, 4842, 4812, 4804, 679, 707, 681, 4810, 4763, 4777, 4174447, 762, 701, 705, 685, 726, 686, 260779, 625, 700, 688, 4797, 4781, 4784, 15986, 65203, 630, 4782, 4721, 4726, 66791009],
#[66791010, 745, 14057, 718, 79593, 3790, 4841, 4814, 69326, 675, 771, 259769, 16057, 659, 65209, 3731, 1046201, 4755, 69267, 4174446, 770, 717, 14029, 687, 79565, 3759, 4813, 4783, 69295, 260742, 721, 259730, 16018, 617, 65170, 3689, 1046162, 4713, 69225, 66791010],
#[66791011, 769, 16113, 711, 256753, 10951, 16062, 670, 1043185, 60103, 48830, 2718, 65265, 3783, 65214, 3742, 835262, 51870, 16050, 503441, 4865, 720, 4807, 16020, 76487, 256660, 4766, 15976, 1108679, 1043092, 68254, 48744, 69319, 65172, 69278, 65128, 1100446, 835176, 8892049, 66791011],
#[66791012, 760, 743, 719, 763, 696, 260813, 663, 767, 703, 16065, 661, 65238, 693, 4174506, 650, 754, 709, 4856, 4815, 4805, 676, 710, 674, 4792, 4759, 4770, 260748, 712, 671, 4799, 4757, 4767, 16013, 65181, 654, 4789, 4746, 4750, 66791012],
#[66791014, 774, 16112, 713, 16115, 784060, 16064, 689, 4870, 784081, 4809, 16038, 13366972, 4174490, 4785, 16011, 16119, 784072, 16075, 668, 65264, 3785, 65216, 3761, 65227, 3740, 16044, 784005, 13366984, 785046, 4764, 16009, 69321, 65190, 69297, 65163, 69276, 65161, 13366917, 66791014],
#[66791013, 744, 749, 699, 27373, 27323, 4840, 4795, 1075899, 692, 766, 698, 706, 680, 4174535, 673, 4794, 4776, 4769, 8366724, 27390, 27322, 520903, 27297, 27330, 27304, 1075898, 1075873, 1075880, 260740, 723, 665, 785048, 637, 142584472, 27261, 4761, 4733, 1075837, 66791013],
#[66791128, 776, 4872, 773, 778, 772, 4868, 260841, 780, 765, 4861, 16118, 65276, 751, 4847, 4174555, 781, 761, 4857, 16103, 65275, 748, 4844, 260828, 785158, 747, 4843, 16093, 65269, 739, 4835, 66791128],
#[200746714, 777, 16141, 768, 65293, 3840, 16130, 8351469, 779, 784126, 16122, 742, 65274, 3814, 4174577, 503525, 4873, 503553, 4864, 16114, 69376, 65266, 142569197, 260834, 13367038, 47863, 4838, 16097, 69350, 65249, 8892133, 200746714],
#[66791129, 784140, 16140, 775, 65292, 3847, 16131, 784110, 13367052, 784131, 4871, 16110, 69383, 65262, 13367022, 4174558, 16139, 784127, 16127, 756, 65279, 3828, 260851, 784095, 13367039, 47859, 4852, 16095, 69364, 65247, 13367007, 66791129]
]
set_option maxRecDepth 65536 in
def rowBank : Nat → Array (Array Nat)
| 0 => rowBank0
| 1 => rowBank1
| 2 => rowBank2
| 3 => rowBank3
| 4 => rowBank4
| _ => #[]
end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

abbrev Mask := BitVec 32
abbrev SignedSteps := List (Fin 15)

def maskSet (m : Mask) : Set Word := {w | m.getLsbD w.val = true}

namespace WordPerm

structure Move where
  first : Nat
  last : Nat
  stride : Nat
  below : Mask
  above : Mask
  fixed : Mask
  deriving Inhabited

def moves : List Move := [
  ⟨0, 0, 1, 0x55555555, 0xaaaaaaaa, 0x00000000⟩,
  ⟨1, 1, 2, 0x33333333, 0xcccccccc, 0x00000000⟩,
  ⟨2, 2, 4, 0x0f0f0f0f, 0xf0f0f0f0, 0x00000000⟩,
  ⟨3, 3, 8, 0x00ff00ff, 0xff00ff00, 0x00000000⟩,
  ⟨4, 4, 16, 0x0000ffff, 0xffff0000, 0x00000000⟩,
  ⟨0, 1, 1, 0x22222222, 0x44444444, 0x99999999⟩,
  ⟨0, 2, 3, 0x0a0a0a0a, 0x50505050, 0xa5a5a5a5⟩,
  ⟨0, 3, 7, 0x00aa00aa, 0x55005500, 0xaa55aa55⟩,
  ⟨0, 4, 15, 0x0000aaaa, 0x55550000, 0xaaaa5555⟩,
  ⟨1, 2, 2, 0x0c0c0c0c, 0x30303030, 0xc3c3c3c3⟩,
  ⟨1, 3, 6, 0x00cc00cc, 0x33003300, 0xcc33cc33⟩,
  ⟨1, 4, 14, 0x0000cccc, 0x33330000, 0xcccc3333⟩,
  ⟨2, 3, 4, 0x00f000f0, 0x0f000f00, 0xf00ff00f⟩,
  ⟨2, 4, 12, 0x0000f0f0, 0x0f0f0000, 0xf0f00f0f⟩,
  ⟨3, 4, 8, 0x0000ff00, 0x00ff0000, 0xff0000ff⟩]

def move (t : Fin 15) : Move := moves[t.val]!

def wordStep (t : Fin 15) (w : Word) : Word :=
  let m := move t
  if m.first = m.last then Fin.ofNat 32 (w.val ^^^ (1 <<< m.first))
  else if w.val.testBit m.first = w.val.testBit m.last then w
  else Fin.ofNat 32 (w.val ^^^ ((1 <<< m.first) ||| (1 <<< m.last)))

def maskStep (t : Fin 15) (v : Mask) : Mask :=
  let m := move t
  (v &&& m.fixed) ||| ((v <<< m.stride) &&& m.above) |||
    ((v >>> m.stride) &&& m.below)

private theorem involutive : ∀ (t : Fin 15) (w : Word),
    wordStep t (wordStep t w) = w := by decide +kernel

def stepEquiv (t : Fin 15) : Word ≃ Word :=
  ⟨wordStep t, wordStep t, involutive t, involutive t⟩

private theorem routing : ∀ (t : Fin 15) (w : Word),
    let m := move t
    let j := w.val
    let src := (wordStep t w).val
    (m.fixed.getLsbD j = true ∧ m.above.getLsbD j = false ∧ m.below.getLsbD j = false ∧ src = j) ∨
    (m.fixed.getLsbD j = false ∧ m.above.getLsbD j = true ∧ m.below.getLsbD j = false ∧ m.stride ≤ j ∧ src = j - m.stride) ∨
    (m.fixed.getLsbD j = false ∧ m.above.getLsbD j = false ∧ m.below.getLsbD j = true ∧ src = m.stride + j) := by
  decide +kernel

theorem maskStep_bit (t : Fin 15) (v : Mask) (w : Word) :
    (maskStep t v).getLsbD w.val = v.getLsbD (wordStep t w).val := by
  simp only [maskStep, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, w.isLt, decide_true, Bool.true_and]
  rcases routing t w with ⟨f,a,b,e⟩ | ⟨f,a,b,le,e⟩ | ⟨f,a,b,e⟩
  · simp only [f,a,b,e,Bool.and_true,Bool.and_false,Bool.or_false]
  · simp only [f,a,b,e,Nat.not_lt_of_ge le,decide_false,Bool.not_false,Bool.true_and,
      Bool.and_true,Bool.and_false,Bool.or_false,Bool.false_or]
  · simp only [f,a,b,e,Bool.and_true,Bool.and_false,Bool.or_false,Bool.false_or]

def signedEquiv : SignedSteps → Word ≃ Word
  | [] => Equiv.refl Word
  | t :: ts => (stepEquiv t).trans (signedEquiv ts)

end WordPerm

def permMask (steps : SignedSteps) (m : Mask) : Mask :=
  steps.foldl (fun v t => WordPerm.maskStep t v) m

theorem maskSet_permMask (steps : SignedSteps) (m : Mask) :
    maskSet (permMask steps m) = WordPerm.signedEquiv steps '' maskSet m := by
  induction steps generalizing m with
  | nil => ext w; simp [permMask, WordPerm.signedEquiv]
  | cons t ts ih =>
    change maskSet (permMask ts (WordPerm.maskStep t m)) = _
    rw [ih]
    have one : maskSet (WordPerm.maskStep t m) = WordPerm.stepEquiv t '' maskSet m := by
      rw [Equiv.image_eq_preimage_symm]
      ext w
      change (WordPerm.maskStep t m).getLsbD w.val = true ↔
        m.getLsbD (WordPerm.wordStep t w).val = true
      rw [WordPerm.maskStep_bit]
    rw [one, Set.image_image]
    rfl

namespace WordPerm

def stepsBelow (steps : SignedSteps) (d : Nat) : Bool :=
  steps.all (fun t => decide ((move t).last < d))

private theorem unchanged : ∀ (t : Fin 15) (w : Word) (k : Fin 5), (move t).last < k.val →
    (wordStep t w).val.testBit k.val = w.val.testBit k.val := by decide +kernel

theorem bit_preserved (steps : SignedSteps) (d k : Nat) (below : stepsBelow steps d = true)
    (hk : d ≤ k) (w : Word) : ((signedEquiv steps) w).val.testBit k = w.val.testBit k := by
  by_cases h : k < 5
  · induction steps generalizing w with
    | nil => rfl
    | cons t ts ih =>
      simp only [stepsBelow, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at below
      obtain ⟨head,tail⟩ := below
      exact (ih tail (wordStep t w)).trans
        (unchanged t w ⟨k,h⟩ (Nat.lt_of_lt_of_le head hk))
  · have big : 32 ≤ 2 ^ k := by
      calc 32 = 2 ^ 5 := by decide
           _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ((signedEquiv steps w).isLt) big),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le w.isLt big)]

theorem image_cut (steps : SignedSteps) (d k : Nat) (below : stepsBelow steps d = true)
    (hk : d ≤ k) (b : Bool) :
    signedEquiv steps '' {w : Word | w.val.testBit k = b} =
      {w : Word | w.val.testBit k = b} := by
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (bit_preserved steps d k below hk v).trans hv
  · intro hw
    refine ⟨(signedEquiv steps).symm w,?_,(signedEquiv steps).apply_symm_apply w⟩
    have h := bit_preserved steps d k below hk ((signedEquiv steps).symm w)
    simpa using h.symm.trans (by simpa using hw)

end WordPerm
end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

def candidates (g : List PMask) : List PMask :=
  ((allUnions g).eraseDups).insertionSort (fun a b => a.toNat ≤ b.toNat)

@[simp] theorem mem_candidates {g m} : m ∈ candidates g ↔ m ∈ allUnions g := by simp [candidates, List.mem_insertionSort]

def assembled (g : List PMask) (m : PMask) : PMask :=
  g.foldr (fun x acc => if x &&& m == x then x ||| acc else acc) 0

private theorem fold_spans (g : List PMask) {t : List PMask} (m : PMask)
    (h : ∀ x ∈ g, Span t (modelSet x)) : Span t (modelSet (assembled g m)) := by
  induction g with
  | nil => simpa [assembled,modelSet] using (Span.zero (g:=t))
  | cons a g ih =>
    have ha := h a (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    unfold assembled; simp only [List.foldr_cons]
    split
    · rw [set_or]; exact .join ha ht
    · exact ht

theorem inside_of_assembled {t : List PMask} {m : PMask} (h : assembled t m == m) :
    Span t (modelSet m) :=
  (beq_iff_eq.mp h) ▸ fold_spans t m (fun _ hm => .seed hm)

def bitMask (d : Nat) (b : Bool) : PMask :=
  let m : PMask := match d with
    | 0 => 2863311530 | 1 => 3435973836 | 2 => 4042322160 | 3 => 4278255360 | _ => 4294901760
  if b then m else ~~~m

private theorem bitMask_ok : ∀ d : Fin 5, ∀ b : Bool, ∀ w : Word,
    (bitMask d.val b).getLsbD w.val = true ↔ w.val.testBit d.val = b := by decide +kernel

theorem arm_set (r : PMask) {d : Nat} (hd : d < 5) (b : Bool) :
    modelSet (r &&& bitMask d b) = modelSet r ∩ cut d b := by
  ext w
  simpa [modelSet,cut] using
    (and_congr_right fun _ : r.getLsbD w.val = true => bitMask_ok ⟨d,hd⟩ b w)

def stepsCode (code : Nat) : SignedSteps := (List.range 9).filterMap fun i =>
  let n := (code >>> (4*i)) % 16
  if h : n=0 then none else some ⟨n-1,by omega⟩

def maskFits (t : List PMask) (m : PMask) : Bool := assembled t m == m

def linkOK (d : Nat) (g t : List PMask) (r : PMask) (steps : SignedSteps) : Bool :=
  WordPerm.stepsBelow steps (d+1) &&
  (g.all (fun m => maskFits t (permMask steps m))) &&
  maskFits t (permMask steps (r &&& bitMask d false)) &&
  maskFits t (permMask steps (r &&& bitMask d true))

theorem link_sound {d g t r steps} (hd : d < 5) (h : linkOK d g t r steps = true) :
    Nonempty (StepWitness d g r t) := by
  simp only [linkOK,Bool.and_eq_true,List.all_eq_true] at h
  rcases h with ⟨⟨⟨below,old⟩,l⟩,rr⟩
  have transport (m : PMask) (hm : maskFits t (permMask steps m)=true) :
      Span t (WordPerm.signedEquiv steps '' modelSet m) := by
    change Span t (WordPerm.signedEquiv steps '' maskSet m)
    rw [←maskSet_permMask]
    exact inside_of_assembled hm
  refine ⟨⟨WordPerm.signedEquiv steps, ?_, fun m hm => transport m (old m hm), ?_⟩⟩
  · intro n hn w; exact WordPerm.bit_preserved steps (d+1) n below hn w
  · intro b; rw [←arm_set r hd b]; cases b
    · exact transport _ l
    · exact transport _ rr

def checkRow (d : Nat) (g : List PMask) (next : Array (List PMask)) (row : Array Nat) : Bool :=
  let vals := candidates g
  (List.range vals.length).all fun j =>
    let code := row[j]!
    let idx := code % 1024
    (idx < next.size) && linkOK d g next[idx]! vals[j]! (stepsCode (code / 1024))

theorem row_sound {d g next row} (hd : d<5) (h : checkRow d g next row=true) :
    ∀r ∈ allUnions g, ∃ t ∈ next.toList, Nonempty (StepWitness d g r t) := by
  intro r hr
  obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp (mem_candidates.mpr hr)
  simp only [checkRow,List.all_eq_true,List.mem_range,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨hi,pack⟩ := h j hj
  refine ⟨next[row[j]! % 1024]!, ?_, ?_⟩
  · exact Array.mem_toList_iff.mpr (by simp [hi])
  · apply link_sound hd
    simpa [hj,eq] using pack

def levelOK (k : Nat) : Bool :=
  (List.range (seedBank k).size).all fun i =>
    checkRow k (seedBank k)[i]! (seedBank (k+1)) (rowBank k)[i]!

theorem level_sound {k : Nat} (hk : k < 5) (h : levelOK k=true) :
    Connect k (seedBank k).toList (seedBank (k+1)).toList := by
  intro g hg
  obtain ⟨i,hi,eq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hg)
  simp only [levelOK,List.all_eq_true,List.mem_range] at h
  exact row_sound hk (by simpa [hi,eq] using h i hi)

theorem seed_start : Fits 0 (seedBank 0).toList initFamily := by
  refine ⟨[4294967295], by decide, Equiv.refl _, fun _ _ _ => rfl, ?_⟩
  rintro _ (rfl | rfl)
  · simp; exact Span.zero
  · have h : modelSet (4294967295:PMask) = (Set.univ : Set Word) := by
      have all : ∀ w : Word, (4294967295:PMask).getLsbD w.val=true := by decide +kernel
      ext w; exact ⟨fun _ => Set.mem_univ _, fun _ => all w⟩
    have univImage : (Equiv.refl Word) '' (Set.univ : Set Word) = Set.univ := by
      ext w; exact ⟨fun _ => Set.mem_univ _, fun _ => ⟨w,Set.mem_univ _,rfl⟩⟩
    rw [univImage,←h]
    exact .seed (by simp)

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer0Row0 : checkRow 0 seedBank0[0]! seedBank1 rowBank0[0]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem rowsAt0 (i : Nat) (hi : i<1) : checkRow 0 seedBank0[i]! seedBank1 rowBank0[i]! = true := by
  interval_cases i
  · exact checkLayer0Row0
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem numeric_level0 : levelOK 0=true := by
  apply List.all_eq_true.mpr
  intro i mem
  exact rowsAt0 i (List.mem_range.mp mem)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer1Row0 : checkRow 1 seedBank1[0]! seedBank2 rowBank1[0]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem rowsAt1 (i : Nat) (hi : i<1) : checkRow 1 seedBank1[i]! seedBank2 rowBank1[i]! = true := by
  interval_cases i
  · exact checkLayer1Row0
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem numeric_level1 : levelOK 1=true := by
  apply List.all_eq_true.mpr
  intro i mem
  exact rowsAt1 i (List.mem_range.mp mem)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer2Row0 : checkRow 2 seedBank2[0]! seedBank3 rowBank2[0]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer2Row1 : checkRow 2 seedBank2[1]! seedBank3 rowBank2[1]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem rowsAt2 (i : Nat) (hi : i<2) : checkRow 2 seedBank2[i]! seedBank3 rowBank2[i]! = true := by
  interval_cases i
  · exact checkLayer2Row0
  · exact checkLayer2Row1
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem numeric_level2 : levelOK 2=true := by
  apply List.all_eq_true.mpr
  intro i mem
  exact rowsAt2 i (List.mem_range.mp mem)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer3Row0 : checkRow 3 seedBank3[0]! seedBank4 rowBank3[0]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer3Row1 : checkRow 3 seedBank3[1]! seedBank4 rowBank3[1]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer3Row2 : checkRow 3 seedBank3[2]! seedBank4 rowBank3[2]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer3Row3 : checkRow 3 seedBank3[3]! seedBank4 rowBank3[3]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer3Row4 : checkRow 3 seedBank3[4]! seedBank4 rowBank3[4]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer3Row5 : checkRow 3 seedBank3[5]! seedBank4 rowBank3[5]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer3Row6 : checkRow 3 seedBank3[6]! seedBank4 rowBank3[6]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem rowsAt3 (i : Nat) (hi : i<7) : checkRow 3 seedBank3[i]! seedBank4 rowBank3[i]! = true := by
  interval_cases i
  · exact checkLayer3Row0
  · exact checkLayer3Row1
  · exact checkLayer3Row2
  · exact checkLayer3Row3
  · exact checkLayer3Row4
  · exact checkLayer3Row5
  · exact checkLayer3Row6
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem numeric_level3 : levelOK 3=true := by
  apply List.all_eq_true.mpr
  intro i mem
  exact rowsAt3 i (List.mem_range.mp mem)
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row0 : checkRow 4 seedBank4[0]! seedBank5 rowBank4[0]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row1 : checkRow 4 seedBank4[1]! seedBank5 rowBank4[1]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row2 : checkRow 4 seedBank4[2]! seedBank5 rowBank4[2]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row3 : checkRow 4 seedBank4[3]! seedBank5 rowBank4[3]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row4 : checkRow 4 seedBank4[4]! seedBank5 rowBank4[4]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row5 : checkRow 4 seedBank4[5]! seedBank5 rowBank4[5]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row6 : checkRow 4 seedBank4[6]! seedBank5 rowBank4[6]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row7 : checkRow 4 seedBank4[7]! seedBank5 rowBank4[7]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row8 : checkRow 4 seedBank4[8]! seedBank5 rowBank4[8]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row9 : checkRow 4 seedBank4[9]! seedBank5 rowBank4[9]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row10 : checkRow 4 seedBank4[10]! seedBank5 rowBank4[10]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row11 : checkRow 4 seedBank4[11]! seedBank5 rowBank4[11]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row12 : checkRow 4 seedBank4[12]! seedBank5 rowBank4[12]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row13 : checkRow 4 seedBank4[13]! seedBank5 rowBank4[13]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row14 : checkRow 4 seedBank4[14]! seedBank5 rowBank4[14]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row15 : checkRow 4 seedBank4[15]! seedBank5 rowBank4[15]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row16 : checkRow 4 seedBank4[16]! seedBank5 rowBank4[16]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row17 : checkRow 4 seedBank4[17]! seedBank5 rowBank4[17]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row18 : checkRow 4 seedBank4[18]! seedBank5 rowBank4[18]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row19 : checkRow 4 seedBank4[19]! seedBank5 rowBank4[19]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row20 : checkRow 4 seedBank4[20]! seedBank5 rowBank4[20]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row21 : checkRow 4 seedBank4[21]! seedBank5 rowBank4[21]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row22 : checkRow 4 seedBank4[22]! seedBank5 rowBank4[22]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row23 : checkRow 4 seedBank4[23]! seedBank5 rowBank4[23]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row24 : checkRow 4 seedBank4[24]! seedBank5 rowBank4[24]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row25 : checkRow 4 seedBank4[25]! seedBank5 rowBank4[25]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row26 : checkRow 4 seedBank4[26]! seedBank5 rowBank4[26]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row27 : checkRow 4 seedBank4[27]! seedBank5 rowBank4[27]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row28 : checkRow 4 seedBank4[28]! seedBank5 rowBank4[28]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row29 : checkRow 4 seedBank4[29]! seedBank5 rowBank4[29]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row30 : checkRow 4 seedBank4[30]! seedBank5 rowBank4[30]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row31 : checkRow 4 seedBank4[31]! seedBank5 rowBank4[31]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row32 : checkRow 4 seedBank4[32]! seedBank5 rowBank4[32]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row33 : checkRow 4 seedBank4[33]! seedBank5 rowBank4[33]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row34 : checkRow 4 seedBank4[34]! seedBank5 rowBank4[34]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row35 : checkRow 4 seedBank4[35]! seedBank5 rowBank4[35]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row36 : checkRow 4 seedBank4[36]! seedBank5 rowBank4[36]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row37 : checkRow 4 seedBank4[37]! seedBank5 rowBank4[37]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row38 : checkRow 4 seedBank4[38]! seedBank5 rowBank4[38]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row39 : checkRow 4 seedBank4[39]! seedBank5 rowBank4[39]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row40 : checkRow 4 seedBank4[40]! seedBank5 rowBank4[40]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row41 : checkRow 4 seedBank4[41]! seedBank5 rowBank4[41]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row42 : checkRow 4 seedBank4[42]! seedBank5 rowBank4[42]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row43 : checkRow 4 seedBank4[43]! seedBank5 rowBank4[43]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row44 : checkRow 4 seedBank4[44]! seedBank5 rowBank4[44]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem checkLayer4Row45 : checkRow 4 seedBank4[45]! seedBank5 rowBank4[45]! = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem rowsAt4 (i : Nat) (hi : i<46) : checkRow 4 seedBank4[i]! seedBank5 rowBank4[i]! = true := by
  interval_cases i
  · exact checkLayer4Row0
  · exact checkLayer4Row1
  · exact checkLayer4Row2
  · exact checkLayer4Row3
  · exact checkLayer4Row4
  · exact checkLayer4Row5
  · exact checkLayer4Row6
  · exact checkLayer4Row7
  · exact checkLayer4Row8
  · exact checkLayer4Row9
  · exact checkLayer4Row10
  · exact checkLayer4Row11
  · exact checkLayer4Row12
  · exact checkLayer4Row13
  · exact checkLayer4Row14
  · exact checkLayer4Row15
  · exact checkLayer4Row16
  · exact checkLayer4Row17
  · exact checkLayer4Row18
  · exact checkLayer4Row19
  · exact checkLayer4Row20
  · exact checkLayer4Row21
  · exact checkLayer4Row22
  · exact checkLayer4Row23
  · exact checkLayer4Row24
  · exact checkLayer4Row25
  · exact checkLayer4Row26
  · exact checkLayer4Row27
  · exact checkLayer4Row28
  · exact checkLayer4Row29
  · exact checkLayer4Row30
  · exact checkLayer4Row31
  · exact checkLayer4Row32
  · exact checkLayer4Row33
  · exact checkLayer4Row34
  · exact checkLayer4Row35
  · exact checkLayer4Row36
  · exact checkLayer4Row37
  · exact checkLayer4Row38
  · exact checkLayer4Row39
  · exact checkLayer4Row40
  · exact checkLayer4Row41
  · exact checkLayer4Row42
  · exact checkLayer4Row43
  · exact checkLayer4Row44
  · exact checkLayer4Row45
set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem numeric_level4 : levelOK 4=true := by
  apply List.all_eq_true.mpr
  intro i mem
  exact rowsAt4 i (List.mem_range.mp mem)

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem concrete_cover (p : Program) (wf : p.WellFormed) :
    ∃ g ∈ seedBank5.toList, ∃ e : Word ≃ Word, ∀v : Vertex, ∃m ∈ candidates g,
        e '' {w | Present p w v} = modelSet m := by
  have checked (d : Nat) (hd : d<5) : levelOK d=true := by
    interval_cases d
    · exact numeric_level0
    · exact numeric_level1
    · exact numeric_level2
    · exact numeric_level3
    · exact numeric_level4
  obtain ⟨g,hg,e,vals⟩ := program_cover (fun d => (seedBank d).toList) seed_start
    (fun d hd => level_sound hd (checked d hd)) p wf
  refine ⟨g,hg,e,fun v => ?_⟩
  obtain ⟨m,hm,eq⟩ := vals v
  exact ⟨m,mem_candidates.mpr hm,eq⟩

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

def classMask : List PMask → Word → PMask
  | [], _ => ~~~0
  | m :: ms, w => (if CSP.hit m w then m else ~~~m) &&& classMask ms w

theorem classMask_bit (g : List PMask) (w q : Word) :
    CSP.hit (classMask g w) q = true ↔ ∀ m ∈ g, CSP.hit m q = CSP.hit m w := by
  induction g with
  | nil =>
    constructor
    · simp
    · intro _
      have const : ∀ i : Word, (~~~(0 : PMask)).getLsbD i.val = true := by decide
      exact const q
  | cons m ms ih =>
    cases hw : CSP.hit m w <;>
      simp [classMask,hw,ih,CSP.hit_and,CSP.hit_not]

theorem same_on_unions (g : List PMask) (w q : Word)
    (same : ∀ m ∈ g, CSP.hit m q = CSP.hit m w) :
    ∀ a ∈ allUnions g, CSP.hit a q = CSP.hit a w := by
  induction g with
  | nil => simp [allUnions,CSP.hit]
  | cons m ms ih =>
    have tail := ih (fun a h => same a (List.mem_cons_of_mem _ h))
    intro a h
    rcases List.mem_append.mp h with h | h
    · exact tail _ h
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
      have mbit := same m List.mem_cons_self
      have vbit := tail v hv
      simpa only [CSP.hit,BitVec.getLsbD_or] using congrArg₂ (· || ·) vbit mbit

def compressionOK (g : List PMask) (E : PMask) : Bool :=
  (List.finRange 32).all fun w => decide ((classMask g w &&& E) ≠ 0)

theorem complete_of_seed_check (g : List PMask) (E : PMask) (ok : compressionOK g E = true) :
    CSP.Complete (allUnions g) E := by
  intro w
  have nonzero := of_decide_eq_true ((List.all_eq_true.mp ok) w (List.mem_finRange w))
  have someBit : ∃ q : Word, CSP.hit (classMask g w &&& E) q = true := by
    by_contra! no
    apply nonzero
    exact CSP.mask_zero _ (fun q => by simpa using no q)
  obtain ⟨q,hq⟩ := someBit
  rw [CSP.hit_and,Bool.and_eq_true] at hq
  exact ⟨q,hq.2,same_on_unions g w q ((classMask_bit g w q).mp hq.1)⟩

theorem complete_of_subset {U V : List PMask} {E : PMask}
    (sub : ∀ a ∈ U, a ∈ V) (complete : CSP.Complete V E) : CSP.Complete U E := by
  intro w
  obtain ⟨q,inside,same⟩ := complete w
  exact ⟨q,inside,fun a h => same a (sub a h)⟩

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux
def representativeMasks : Array PMask := #[
  4294967295, 2147483647, 1073741823, 2130673663, 1879015423, 1073709055, 2139062271, 2130608127,
  1877966847, 1069514751, 1862238207, 805273599, 1065320447, 268435455, 1061126143, 1040138239,
  536821759, 260014079, 1061109759, 721387519, 268386303, 528433151, 1023361023, 1861124095,
  503267327, 800030719, 796868479, 796880767, 931100543, 1803513727, 1736404863, 931086207,
  2004318079, 1869574015, 1048526719, 1736406911, 1031749503, 1853845375, 1061109631, 998195071,
  528433023, 1014972287, 863977343, 780091263, 795819903, 926891903, 981417855, 494878591,
  259997567, 526335871, 1031618431, 994000767, 1853779839, 1048461183, 795832191, 394215295,
  930561919, 662665087, 792674175, 1719629695, 1786736511, 729771903, 662663039, 930576255,
  1852796799, 1669295999, 897531775, 997932927, 526335999, 1023164415, 501039103, 360660991,
  265240575, 218054655, 255803391, 259993471, 914306943, 897529727, 993738623, 1852731263,
  662648703, 394213247, 863975295, 926367615, 461323135, 859783039, 595554175, 360660863,
  863467391, 763309951, 780103295, 780087167, 791625599, 791637887, 662646655, 729755519,
  258944895, 645871487, 926365567, 981090175, 256851839, 226439039, 863451007, 393688959,
  578779007, 629092223, 595537791, 125775743, 746532735, 779038591, 897005439, 778977151,
  859780991, 1786408831, 725561215, 712978303, 658454399, 658452351, 791621503, 1014775679,
  711946111, 708788095, 209665919, 859535231, 725315455, 847198079, 1718515583, 1618964351,
  813645695, 863190911, 124743551, 192887679, 121585535, 125777791, 125269887, 859782015,
  327105407, 1668509567, 645885567, 896876415, 880752511, 360658815, 391593855, 657944447,
  492650367, 657928063, 92221311, 859256703, 360134527, 863188863, 391591807, 896874367,
  778973055, 859518847, 256847743, 591343487, 725299071, 644757375, 425540479, 594751359,
  545206143, 107966079, 574568319, 707735423, 16777215, 75446143, 123154303, 746336127,
  54475647, 224210815, 358430591, 813119359, 628436863, 712650623, 120532863, 121059199,
  208613247, 252674047, 134156287, 715816959, 67047423, 125767679, 8355839, 252657663,
  490676031, 859010943, 390012735, 507453247, 522133311, 595538815, 327103359, 255795007,
  858996607, 457121599, 326579071, 440344383, 322903871, 858995583, 591344511, 253697855,
  58667903, 293548927, 357908351, 488578879, 578761599, 590573439, 473898815, 239017791,
  858994559, 254746431, 490544959, 387915583, 188686143, 507387711, 356458303, 357908479,
  214712319, 16715775, 4145151, 54464511, 252645375, 176106111, 117915519, 858993535,
  354361151, 356456255, 373233471, 121575231, 357906303, 387391295, 488447807, 590557055,
  322908991, 222236479, 293024639, 322901823, 171908927, 7303039, 4145023, 707424127,
  252649279, 707411839, 121573183, 108988287, 58656639, 117927807, 7829375, 355802943,
  54473535, 473702207, 707407743, 58132351, 440016703, 54466367, 354359103, 117911423,
  104798015, 54462335, 272572223, 187375423, 107939711, 574305151, 54464319, 41879423,
  812662655, 387389247, 1617981311, 52371263, 339679039, 252645183, 119478079, 573208447,
  573795967, 88018751, 237903679, 220139327, 206323583, 117913471, 322377535, 8336255,
  89468799, 322384703, 858993471, 41888383, 175057535, 53949311, 290798463, 306124607,
  203366207, 322117439, 355931967, 574564991, 119476031, 205459263, 355931959, 374806359,
  123148119, 641148727, 358045015, 387389271, 590820151, 358029143, 1431655767, 387389239,
  372709175, 656877367, 121050935, 858993463, 322377527, 590817079, 624371511, 121055031,
  322384695, 341251927, 87500599, 322122551, 118957879, 305600311, 53942071, 120006455,
  118953815, 53946167, 122099543, 106370903, 89593687, 374740823, 557262647, 288830263,
  353834839, 353834807, 339154743, 590558007, 624240439, 288823095, 355800887, 607594295,
  357898071, 641083191, 53949239, 118953783, 640100151, 357913943, 320280375, 574042935,
  589768503, 574039863, 104273719, 812660607, 206319487, 8333951, 355800895, 3092351,
  3881855, 7237247, 353834815, 3618687, 37689151, 354228031, 573192063, 53938047,
  85921599, 118429503, 288830271, 139213695, 53155647, 53687103, 51318591, 103683903,
  305796927, 117901183, 69146431, 36645503, 202313535, 205262655, 544223103, 287126335,
  4132671, 72103807, 36636543, 51844927, 272045887, 4141887, 7800703, 339482431,
  87492407, 117909303, 288822071, 51844919, 53941047, 272045879, 305599287, 320018231,
  37164855, 286725943, 56035159, 117905239, 53687095, 52897591, 540485431, 353703735,
  72816471, 85399383, 53945143, 557261623, 104277559, 573780791, 589506359, 574038839,
  20391735, 572991287, 640034615, 53937975, 341251415, 353703767, 89478487, 104269623,
  117905207, 89593175, 288568119, 51840823, 52631351, 70715191, 20383543, 338958135,
  72815959, 85398871, 35067735, 103221047, 85272375, 52889399, 88414039, 341120343,
  607397687, 37160759, 341055319, 3617591, 117901111, 68622135, 105256791, 89462103,
  53678079, 22480727, 52896567, 286724919, 540484407, 5723479, 353703255, 37168695,
  51840855, 589505335, 286602039, 20390711, 69674807, 85395255, 572991031, 556869431,
  51586871, 37163831, 572928823, 305337143, 320017207, 53678903, 103159607, 53682999,
  573712183, 272044855, 572990263, 288559927, 51843895, 556999479, 288429879, 573776695,
  305272631, 85395287, 353705791, 88020287, 290796415, 353703743, 50803583, 573191039,
  2039615, 20911423, 170532671, 286462775, 85264215, 18286423, 84346711, 572728119,
  36120119, 20128567, 573711159, 288428855, 271782711, 572925495, 50795319, 36901687,
  51578711, 52630327, 305271607, 540222263, 51581751, 52634423, 85267799, 3606327,
  72684887, 88413527, 341054807, 50792247, 52627255, 18286391, 36112183, 103155511,
  5703511, 1512791, 2564919, 67569463, 15732735, 271848247, 22087511, 1512247,
  36049719, 70518583, 36833079, 38930263, 34015063, 987135, 202121023, 85266239,
  20906815, 3355519, 50536255, 286602047, 1513279, 50534207, 36312895, 139209343,
  3355455, 271589183, 4129599, 20382527, 4993919, 18289983, 986943, 50532159,
  69143615, 36308863, 202116927, 18809663, 37159735, 50538295, 286332727, 1513271,
  5592407, 572663607, 37167671, 286339895, 2565943, 1513303, 51840791, 3355447,
  102172439, 85395223, 50534199, 20386103, 117901079, 572666679, 20382519, 84219735,
  22480215, 84215639, 20123959, 36111159, 3605303, 101123863, 572663351, 271587127,
  540026679, 17901367, 71571287, 36905527, 18285911, 3613239, 68618007, 18285367,
  102106903, 5702999, 50530103, 3608887, 18288951, 50792215, 36897591, 36119095,
  286331703, 20120375, 35063575, 84219223, 18286359, 84346647, 50537271, 22349143,
  572662583, 50533175, 35788599, 67901247, 2763391, 271587135, 18285375, 7341951,
  460671, 3343167, 50529087, 799551, 983871, 986175, 3149631, 2302775,
  33691479, 18288919, 67569431, 18154839, 50529079, 18023223, 84215127, 5571927,
  35849015, 18285847, 84215575, 460599, 3343159, 1250103, 68617495, 71570775,
  271586103, 35787575, 540025655, 17893207, 35784503, 36111143, 1381719, 460631,
  2500151, 18026807, 17237783, 1509143, 3351095, 101058327, 286331191, 17893175,
  35856951, 67381047, 18285335, 67376951, 3346743, 50530071, 35062551, 34014999,
  17900343, 572662327, 17893143, 18157847, 33687383, 17236759, 1123895, 18023191,
  2499127, 2556711, 5244759, 18154775, 2556983, 34735895, 1507927, 34013975,
  459575, 17236775, 34800407, 286331159, 50529047, 3147575, 67372855, 84215063,
  34013991, 68486423, 460119, 1380663, 275255, 17237271, 1508631, 18026775,
  67568919, 1508407, 152919, 68421399, 50529063, 1508119, 1381695, 2757951,
  1245975, 17892631, 459559, 33751847, 67503383, 460055, 136535, 459543,
  267063, 16975127, 33948455, 68420887, 67437847, 33751831, 34734871, 459351,
  33948439, 459831, 1377559, 271159, 17106199, 1249559, 17895703, 16974615,
  33686103, 397591, 17892695, 2360103, 460567, 33759799, 1180951, 16978231,
  197439, 3146559, 789567, 329047, 1118519, 16844567, 5244247, 67372823,
  197431, 33687319, 2232631, 1507607, 3146551, 2236983, 459287, 16843543,
  197415, 1118487, 328983, 459031, 1245463, 33686311, 67372311, 1376535,
  262967, 132439, 33686295, 266551, 459799, 1050391, 16844055, 270903,
  197399, 196887, 132375, 1049367, 1049879, 327959, 262951, 262935,
  197143, 131671, 135447, 266519, 1114391, 16843031, 263223, 328727,
  65815, 131607, 1048855, 262679, 262423, 131351
]

def compressionAt (i : Nat) : Bool :=
  compressionOK seedBank5[i]! representativeMasks[i]!
end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

def equalShift (distance : Nat) : List PMask → PMask
  | [] => (~~~(0 : PMask)) <<< distance
  | m :: gs => ~~~(m ^^^ (m <<< distance)) &&& equalShift distance gs

private theorem equalShift_spec (distance : Nat) (g : List PMask) (w : Word)
    (active : CSP.hit (equalShift distance g) w = true) :
    distance ≤ w.val ∧ ∀ m ∈ g, m.getLsbD (w.val - distance) = m.getLsbD w.val := by
  induction g with
  | nil =>
    constructor
    · by_contra! small
      simp only [equalShift,CSP.hit,BitVec.getLsbD_shiftLeft,small,decide_true,
        Bool.not_true,Bool.and_false,Bool.false_and] at active
      contradiction
    · simp
  | cons m gs ih =>
    rcases Bool.and_eq_true_iff.mp (CSP.hit_and _ _ w ▸ active) with ⟨same,rest⟩
    obtain ⟨le,tail⟩ := ih rest
    refine ⟨le,?_⟩
    intro a member
    rcases List.mem_cons.mp member with rfl | hm
    · simp only [CSP.hit,BitVec.getLsbD_not,BitVec.getLsbD_xor,BitVec.getLsbD_shiftLeft,
        w.isLt,decide_true,Bool.true_and,Nat.not_lt_of_ge le,decide_false,Bool.not_false] at same
      cases h : a.getLsbD w.val <;> cases h' : a.getLsbD (w.val-distance) <;> simp_all
    · exact tail a hm

def nearWords (g : List PMask) (E : PMask) (distances : List Nat) : PMask :=
  distances.foldr (fun d v => equalShift d g ||| v) E

private theorem nearWords_cases (g : List PMask) (E : PMask) (ds : List Nat) (w : Word)
    (hw : CSP.hit (nearWords g E ds) w = true) :
    CSP.hit E w = true ∨ ∃ d ∈ ds, CSP.hit (equalShift d g) w = true := by
  induction ds with
  | nil => exact Or.inl hw
  | cons d ds ih =>
    change (equalShift d g ||| nearWords g E ds).getLsbD w.val = true at hw
    rw [BitVec.getLsbD_or,Bool.or_eq_true] at hw
    rcases hw with here | later
    · exact Or.inr ⟨d,List.mem_cons_self,here⟩
    · rcases ih later with inside | ⟨x,hx,found⟩
      · exact Or.inl inside
      · exact Or.inr ⟨x,List.mem_cons_of_mem _ hx,found⟩

def fiveShifts (g : List PMask) (E : PMask) : Bool :=
  nearWords g E [1,2,4,8,16] == ~~~(0 : PMask)

theorem complete_of_five_shifts (g : List PMask) (E : PMask) (ok : fiveShifts g E = true) :
    CSP.Complete (allUnions g) E := by
  have full := (beq_iff_eq.mp ok : nearWords g E [1,2,4,8,16] = ~~~(0 : PMask))
  have ones : ∀ w : Word, CSP.hit (~~~(0 : PMask)) w = true := by decide
  have reach : ∀ idx (w : Word), w.val=idx →
      ∃ q : Word, CSP.hit E q=true ∧ ∀ m ∈ g, CSP.hit m q = CSP.hit m w := by
    intro idx
    induction idx using Nat.strong_induction_on with
    | ind idx ih =>
      intro w index
      rcases nearWords_cases g E [1,2,4,8,16] w (full ▸ ones w) with inside | ⟨d,hd,good⟩
      · exact ⟨w,inside,by simp⟩
      · obtain ⟨bound,same⟩ := equalShift_spec d g w good
        have positive : 0<d := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hd; omega
        let previous : Word := ⟨w.val-d,by omega⟩
        obtain ⟨q,hit,earlier⟩ := ih previous.val (by dsimp [previous]; omega) previous rfl
        exact ⟨q,hit,fun m hm => (earlier m hm).trans (same m hm)⟩
  intro w
  obtain ⟨q,hit,same⟩ := reach w.val w rfl
  exact ⟨q,hit,same_on_unions g w q same⟩

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux
def compressionPairs : List (List PMask × PMask) :=
  seedBank5.toList.zip representativeMasks.toList

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem all_fast_compressions : compressionPairs.all (fun row => fiveShifts row.1 row.2) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
theorem every_terminal_complete (i : Nat) (hi : i < 782) :
    CSP.Complete (allUnions seedBank5[i]!) representativeMasks[i]! := by
  have ns : seedBank5.size = 782 := by decide
  have nr : representativeMasks.size = 782 := by decide
  have h : i < compressionPairs.length := by simp [compressionPairs,ns,nr,hi]
  have good := (List.all_eq_true.mp all_fast_compressions) _ (List.getElem_mem h)
  rw [show compressionPairs[i] = (seedBank5[i]!,representativeMasks[i]!) by
    simp [compressionPairs,List.getElem_zip,getElem!_pos,ns ▸ hi,nr ▸ hi]] at good
  exact complete_of_five_shifts _ _ good

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux

theorem compressed_candidates (i : Nat) (hi : i < 782) :
    CSP.Complete (candidates seedBank5[i]!) representativeMasks[i]! :=
  complete_of_subset (fun _ h => mem_candidates.mp h) (every_terminal_complete i hi)

end PEqualNP.Outside.L_meta_17134_aux

namespace PEqualNP.Outside.L_meta_17134_aux.CSP

def mergeMasks : Nat → List PMask → List PMask → List PMask
  | 0,x,y => x++y
  | _+1,[],ys => ys
  | _+1,xs,[] => xs
  | n+1,a::xs,b::ys =>
      if a=b then a::mergeMasks n xs ys else
      if a.toNat<b.toNat then a::mergeMasks n xs (b::ys) else b::mergeMasks n (a::xs) ys

theorem mem_mergeMasks (n : Nat) (xs ys : List PMask) (m : PMask) :
    m∈mergeMasks n xs ys ↔ m∈xs ∨ m∈ys := by
  induction n generalizing xs ys with
  | zero => simp [mergeMasks]
  | succ n ih =>
    cases xs with
    | nil => simp [mergeMasks]
    | cons a xs =>
      cases ys with
      | nil => simp [mergeMasks]
      | cons b ys =>
        simp only [mergeMasks]
        split
        · rename_i h
          subst b
          simp only [List.mem_cons,ih]
          tauto
        · split <;> simp only [List.mem_cons,ih] <;> tauto

def orderedMasks : Nat → List PMask → List PMask
  | 0,xs => xs
  | _+1,[] => []
  | _+1,[v] => [v]
  | n+1,x::y::tail =>
    let xs := x::y::tail
    let cut := xs.length/2
    let l := orderedMasks n (xs.take cut)
    let r := orderedMasks n (xs.drop cut)
    mergeMasks xs.length l r

theorem mem_orderedMasks (n : Nat) (xs : List PMask) (m : PMask) :
    m∈orderedMasks n xs ↔ m∈xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b t =>
        simp only [orderedMasks,mem_mergeMasks,ih,←List.mem_append,List.take_append_drop]

def unionPool (g : List PMask) := orderedMasks 16 (allUnions g)

@[simp] theorem mem_unionPool {g : List PMask} {m : PMask} :
    m∈unionPool g ↔ m∈allUnions g := mem_orderedMasks ..

end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP

def TerminalCheck (U : List Mask) : Prop :=
  ∀ (k : Fin 4) (presence : Vertex → Mask), (∀v,presence v∈U) →
    ¬Represents (graphData k) (fun v w => hit (presence v) w=false)

theorem terminal_short (k : Fin 4) (E : Mask) (U : List Mask) (full : Complete U E)
    (small : pop E < pop (live k)) (presence : Vertex → Mask) (mem : ∀v,presence v∈U) :
    ¬Represents (graphData k) (fun v w => hit (presence v) w=false) := by
  intro rep
  obtain ⟨s⟩ := assignment_of_represents k E U full presence mem rep
  exact Nat.not_lt_of_le (Piece.enough (startPiece k E) s (start_valid s)) small

def runTrace (k : Fin 4) (D : Domains) : Nat → List Piece → Fixed → Nat → Option Nat
  | 0,_,_,_ => none
  | n+1,pieces,fixed,code =>
      let v : Vertex := ⟨(code % 16) % 10,Nat.mod_lt _ (by decide)⟩
      let opts := choices k D pieces fixed v
      opts.foldlM (fun tail a => runTrace k D n (follow pieces k v a) ((v,a)::fixed) tail) (code>>>4)

theorem each_run {α : Type} (f : Nat → α → Option Nat) (xs : List α) (i o : Nat)
    (ok : xs.foldlM f i=some o) (a : α) (ha : a∈xs) :
    ∃b c,f b a=some c := by
  induction xs generalizing i with
  | nil => simp at ha
  | cons h t ih =>
    cases next : f i h with
    | none => simp [List.foldlM_cons,next] at ok
    | some j =>
      rcases List.mem_cons.mp ha with rfl|rest
      · exact ⟨i,j,next⟩
      · apply ih j _ rest
        simpa [List.foldlM_cons,next] using ok

theorem trace_impossible (s : Assignment k E D) (D' : Domains) (inDomain : ∀v,s.value v∈D' v)
    (fuel : Nat) (pieces : List Piece) (fixed : Fixed)
    (pc : ∀p∈pieces,p.Valid s) (fc : ∀q∈fixed,q.2=s.value q.1) (i o : Nat) :
    runTrace k D' fuel pieces fixed i=some o → False := by
  induction fuel generalizing pieces fixed i o with
  | zero => simp [runTrace]
  | succ n ih =>
    intro ok
    let v : Vertex := ⟨(i % 16) % 10,Nat.mod_lt _ (by decide)⟩
    have member : s.value v∈choices k D' pieces fixed v := by
      apply List.mem_filter.mpr
      refine ⟨inDomain _,Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr ?_,List.all_eq_true.mpr ?_⟩⟩
      · intro q h; rw [fc q h]; exact disjoint_actual s _ _
      · intro p h; exact p.fits_actual s (pc p h) _
    obtain ⟨b,c,step⟩ := each_run _ _ _ _ ok _ member
    apply ih _ _ ?_ ?_ b c step
    · intro p hp
      obtain ⟨base,hb,child⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
      rcases (show p=base.yes _ _ ∨ p=base.no _ _ by simpa using child) with rfl|rfl
      · exact base.yes_valid s (pc base hb) _
      · exact base.no_valid s (pc base hb) _
    · intro q h
      rcases List.mem_cons.mp h with rfl|h
      · rfl
      · exact fc q h

def traceReject (k : Fin 4) (E : Mask) (U : List Mask) (code : Nat) : Bool :=
  let domains := List.ofFn (fun v => (base U E).filter fun a => (startPiece k E).fits k v a)
  let D := fun v : Vertex => domains.getD v.val []
  (runTrace k D 10 [startPiece k E] [] code).isSome

theorem traceReject_sound (k : Fin 4) (E : Mask) (U : List Mask) (full : Complete U E)
    (code : Nat) (checked : traceReject k E U code=true)
    (presence : Vertex → Mask) (mem : ∀v,presence v∈U) :
    ¬Represents (graphData k) (fun v w => hit (presence v) w=false) := by
  intro rep
  obtain ⟨s⟩ := assignment_of_represents k E U full presence mem rep
  let D := fun v => (base U E).filter fun a => (startPiece k E).fits k v a
  have each (v : Vertex) : s.value v∈(List.ofFn D).getD v.val [] := by
    rw [List.getD_eq_getElem _ _ (show v.val < (List.ofFn D).length by simp),List.getElem_ofFn]
    exact List.mem_filter.mpr ⟨s.allowed v,Piece.fits_actual _ s (start_valid s) v⟩
  obtain ⟨o,ok⟩ := Option.isSome_iff_exists.mp checked
  apply trace_impossible s _ each 10 _ _ ?_ (by simp) _ o ok
  intro p hp
  simpa using (show p=startPiece k E from by simpa using hp) ▸ start_valid s

end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP

theorem partition_pop (a b : Mask) : pop (a &&& b)+pop (a &&& ~~~b)=pop a := by
  have un : Cards (a &&& b) ∪ Cards (a &&& ~~~b)=Cards a := by
    ext i
    cases h₁ : hit a i <;> cases h₂ : hit b i <;> simp [h₁,h₂]
  have dis : Disjoint (Cards (a &&& b)) (Cards (a &&& ~~~b)) := by
    apply Finset.disjoint_left.mpr
    intro i yes no
    simp only [mem_cards,hit_and,hit_not,Bool.and_eq_true,Bool.not_eq_true'] at yes no
    simp_all
  rw [pop_eq_card,pop_eq_card,pop_eq_card,←Finset.card_union_of_disjoint dis,un]

def canFit (p : Piece) (lo no room : Nat) (m : Mask) : Bool :=
  let count := pop (p.words &&& m)
  decide (lo≤count ∧ count+no≤room)

def cutValues (p : Piece) (k : Fin 4) (v : Vertex) (candidates : List Mask) : List Mask :=
  let c := column k v
  let lo := pop (p.rows &&& c)
  let no := pop (p.rows &&& ~~~c)
  let room := pop p.words
  candidates.filter (canFit p lo no room)

theorem cut_keep (p : Piece) (s : Assignment k E D) (pv : p.Valid s) (v : Vertex)
    (lst : List Mask) (mem : s.value v∈lst) : s.value v∈cutValues p k v lst := by
  apply List.mem_filter.mpr
  refine ⟨mem,decide_eq_true ?_⟩
  have y := Piece.enough _ s (p.yes_valid s pv v)
  have n := Piece.enough _ s (p.no_valid s pv v)
  have sum := partition_pop p.words (s.value v)
  change pop (p.rows &&& column k v)≤pop (p.words &&& s.value v) at y
  change pop (p.rows &&& ~~~(column k v))≤pop (p.words &&& ~~~(s.value v)) at n
  exact ⟨y,by omega⟩

def fastChoices (k : Fin 4) (D : Domains) (pieces : List Piece) (fixed : Fixed) (v : Vertex) : List Mask :=
  pieces.foldl (fun lst p => cutValues p k v lst)
    ((D v).filter (fun a => fixed.all fun q => disjointOnEdge k v q.1 a q.2))

theorem fast_keep (s : Assignment k E D) (D' : Domains) (inDomain : ∀v,s.value v∈D' v)
    (pieces : List Piece) (fixed : Fixed) (v : Vertex)
    (pc : ∀p∈pieces,p.Valid s) (fc : ∀q∈fixed,q.2=s.value q.1) :
    s.value v∈fastChoices k D' pieces fixed v := by
  have good (ls : List Piece) (h : ∀p∈ls,p.Valid s) (init : List Mask) (hi : s.value v∈init) :
      s.value v∈ls.foldl (fun a p => cutValues p k v a) init := by
    induction ls generalizing init with
    | nil => exact hi
    | cons p t ih =>
      apply ih (fun q hq => h q (by simp [hq]))
      exact cut_keep p s (h p (by simp)) v _ hi
  apply good pieces pc
  refine List.mem_filter.mpr ⟨inDomain _,List.all_eq_true.mpr ?_⟩
  intro q hq
  rw [fc q hq]
  exact disjoint_actual s _ _

def traceFast (k : Fin 4) (D : Domains) : Nat → List Piece → Fixed → Nat → Option Nat
  | 0,_,_,_ => none
  | n+1,pieces,fixed,code =>
      let v : Vertex := ⟨(code % 16) % 10,Nat.mod_lt _ (by decide)⟩
      let opts := fastChoices k D pieces fixed v
      opts.foldlM (fun tail a => traceFast k D n (follow pieces k v a) ((v,a)::fixed) tail) (code>>>4)

theorem fast_impossible (s : Assignment k E D) (D' : Domains) (inDomain : ∀v,s.value v∈D' v)
    (fuel : Nat) (pieces : List Piece) (fixed : Fixed)
    (pc : ∀p∈pieces,p.Valid s) (fc : ∀q∈fixed,q.2=s.value q.1) (i o : Nat) :
    traceFast k D' fuel pieces fixed i=some o → False := by
  induction fuel generalizing pieces fixed i o with
  | zero => simp [traceFast]
  | succ n ih =>
    intro ok
    let v : Vertex := ⟨(i % 16) % 10,Nat.mod_lt _ (by decide)⟩
    have member := fast_keep s D' inDomain pieces fixed v pc fc
    obtain ⟨b,c,step⟩ := each_run _ _ _ _ ok _ member
    apply ih _ _ ?_ ?_ b c step
    · intro p hp
      obtain ⟨base,hb,child⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
      rcases (show p=base.yes _ _ ∨ p=base.no _ _ by simpa using child) with rfl|rfl
      · exact base.yes_valid s (pc base hb) _
      · exact base.no_valid s (pc base hb) _
    · intro q h
      rcases List.mem_cons.mp h with rfl|h
      · rfl
      · exact fc q h

def quick (k : Fin 4) (E : Mask) (U : List Mask) (code : Nat) : Bool :=
  (traceFast k (fun _ => base U E) 10 [startPiece k E] [] code).isSome

theorem quick_sound (k : Fin 4) (E : Mask) (U : List Mask) (full : Complete U E)
    (code : Nat) (checked : quick k E U code=true)
    (presence : Vertex → Mask) (mem : ∀v,presence v∈U) :
    ¬Represents (graphData k) (fun v w => hit (presence v) w=false) := by
  intro rep
  obtain ⟨s⟩ := assignment_of_represents k E U full presence mem rep
  obtain ⟨o,ok⟩ := Option.isSome_iff_exists.mp checked
  apply fast_impossible s _ s.allowed 10 _ _ ?_ (by simp) _ o ok
  intro p hp
  simpa using (show p=startPiece k E from by simpa using hp) ▸ start_valid s

end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP.Packed

def digits (xs : List Nat) : Nat := xs.foldr (fun x acc => 128*acc+x) 0

def fill (xs : List α) (v : Nat) := digits (xs.map fun _ => v)
def sign (a i : Nat) := a.testBit (7*i+6)

theorem digit_sign {zs : List Nat} (bound : ∀v∈zs,v<128) (i : Nat) (hi : i<zs.length) :
    sign (digits zs) i = decide (64≤zs[i]) := by
  induction zs generalizing i with
  | nil => simp at hi
  | cons z zs ih =>
    have top : z<2^7 := bound z (by simp)
    change (2^7*digits zs+z).testBit (7*i+6)=_
    rw [Nat.testBit_two_pow_mul_add _ top]
    cases i with
    | zero =>
      simp only [Nat.mul_zero,Nat.zero_add,show 6<7 by decide,if_true,List.getElem_cons_zero]
      rw [Nat.testBit_eq_decide_div_mod_eq]
      congr 1
      norm_num at top ⊢
      omega
    | succ i =>
      rw [if_neg (by omega),show 7*(i+1)+6-7=7*i+6 by omega]
      exact ih (fun j h => bound j (by simp [h])) i (by simpa using hi)

theorem digit_add (xs : List α) (f g : α → Nat) :
    digits (xs.map f)+digits (xs.map g)=digits (xs.map fun x => f x+g x) := by
  induction xs with
  | nil => simp [digits]
  | cons a t ih =>
    change 128*digits (t.map f)+f a+(128*digits (t.map g)+g a)=128*digits (t.map fun x => f x+g x)+(f a+g a)
    omega

theorem digit_add_fill (U : List α) (f : α → Nat) (v : Nat) :
    digits (U.map f)+fill U v=digits (U.map fun u => f u+v) := by
  induction U with
  | nil => simp [digits,fill]
  | cons a t ih =>
    change 128*digits (t.map f)+f a+(128*fill t v+v)=128*digits (t.map fun u => f u+v)+(f a+v)
    omega

theorem digit_fill_sub (U : List α) (f : α → Nat) (v : Nat) (b : ∀u∈U,f u≤v) :
    fill U v=digits (U.map f)+digits (U.map fun u => v-f u) := by
  induction U with
  | nil => simp [digits,fill]
  | cons a t ih =>
    have h := b a (by simp)
    have rest := ih (fun u hu => b u (by simp [hu]))
    change 128*fill t v+v=128*digits (t.map f)+f a+(128*digits (t.map fun u => v-f u)+(v-f a))
    omega

theorem fill_mul (lst : List α) (v : Nat) : fill lst v=v*fill lst 1 := by
  induction lst with
  | nil => simp [fill,digits]
  | cons h t ih =>
    change 128*fill t v+v=v*(128*fill t 1+1)
    rw [ih]; ring

def boundsMask (ones sums lo hi : Nat) : Nat :=
  (sums+(64-lo)*ones) &&& ((64+hi)*ones-sums)

theorem bounds_keep (arr : List α) (count : α → Nat) (bounded : ∀a∈arr,count a≤32)
    (i : Nat) (idx : i<arr.length) (lo hi : Nat) (lh : lo≤count arr[i]) (hh : count arr[i]≤hi) (cap : hi≤32) :
    sign (boundsMask (fill arr 1) (digits (arr.map count)) lo hi) i=true := by
  have ci := bounded _ (List.getElem_mem idx)
  have total := digit_fill_sub arr count (64+hi) (fun a ha => by have := bounded a ha; omega)
  dsimp [boundsMask,sign]
  rw [← fill_mul,← fill_mul,digit_add_fill,show fill arr (64+hi)-digits (arr.map count)=digits (arr.map fun u => 64+hi-count u) by omega]
  rw [Nat.testBit_and]
  apply Bool.and_eq_true_iff.mpr
  constructor
  · change sign (digits (arr.map fun a => count a+(64-lo))) i=true
    rw [digit_sign (by intro z hz; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz; have := bounded _ ha; omega) i (by simpa using idx)]
    simpa using (show 64≤count arr[i]+(64-lo) by omega)
  · change sign (digits (arr.map fun a => (64+hi)-count a)) i=true
    rw [digit_sign (by intro z hz; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz; omega) i (by simpa using idx)]
    simpa using (show 64≤64+hi-count arr[i] by omega)

end PEqualNP.Outside.L_meta_17134_aux.CSP.Packed

namespace PEqualNP.Outside.L_meta_17134_aux.CSP.Packed

abbrev Bands := List (Word × Nat)

def spectrumFor (ws : List Word) (pool : List Mask) : Bands := ws.map fun w =>
  (w,digits (pool.map (fun a => (hit a w).toNat)))

def spectrum (pool : List Mask) : Bands := spectrumFor (List.finRange 32) pool

def tally (cs : Bands) (c : Mask) : Nat :=
  cs.foldr (fun p v => if hit c p.1 then p.2+v else v) 0

def hits (ws : List Word) (c a : Mask) := ws.countP fun w => hit (c &&& a) w

theorem partial_tally (ws : List Word) (pool : List Mask) (c : Mask) :
    tally (spectrumFor ws pool) c=digits (pool.map (hits ws c)) := by
  induction ws with
  | nil =>
    change 0=fill pool 0
    rw [fill_mul]; omega
  | cons w ws ih =>
    change (if hit c w then digits (pool.map fun a => (hit a w).toNat)+tally (spectrumFor ws pool) c
      else tally (spectrumFor ws pool) c)=_
    rw [ih]
    cases h : hit c w with
    | false =>
      simp only [h,Bool.false_eq_true,ite_false]
      congr 1
      apply List.map_congr_left
      intro m _
      simp [hits,h]
    | true =>
      simp only [h,ite_true,digit_add]
      congr 1
      apply List.map_congr_left
      intro m _
      cases hm : hit m w <;> simp [hits,h,hm,Nat.add_comm]

theorem all_hits (c a : Mask) : hits (List.finRange 32) c a = pop (c &&& a) := by
  rw [pop_eq_card,hits,List.countP_eq_length_filter]
  have unique := (List.nodup_finRange 32).filter (fun w : Word => hit (c &&& a) w)
  rw [← List.toFinset_card_of_nodup unique]
  congr 1
  ext i
  simp [Cards]

theorem tally_spec (pool : List Mask) (c : Mask) :
    tally (spectrum pool) c = digits (pool.map fun a => pop (c &&& a)) := by
  rw [spectrum,partial_tally]
  congr 1
  apply List.map_congr_left
  exact fun m _ => all_hits c m

theorem pop_le (a : Mask) : pop a≤32 := by
  rw [pop_eq_card]
  simpa using (Finset.card_le_univ (Cards a))

def bandFit (cs : Bands) (ones : Nat) (p : Piece) (k : Fin 4) (v : Vertex) : Nat :=
  let c := column k v
  let lo := pop (p.rows &&& c)
  let hi := pop p.words - pop (p.rows &&& ~~~c)
  if pop (p.rows &&& ~~~c) ≤ pop p.words then boundsMask ones (tally cs p.words) lo hi else 0

theorem bandFit_keep (s : Assignment k E D) (pool : List Mask) (i : Nat) (h : i<pool.length)
    (p : Piece) (hp : p.Valid s) (v : Vertex) (idx : pool[i]=s.value v) :
    sign (bandFit (spectrum pool) (fill pool 1) p k v) i=true := by
  let c := column k v
  have y := Piece.enough _ s (p.yes_valid s hp v)
  have n := Piece.enough _ s (p.no_valid s hp v)
  change pop (p.rows &&& c)≤pop (p.words &&& s.value v) at y
  change pop (p.rows &&& ~~~c)≤pop (p.words &&& ~~~(s.value v)) at n
  have part := partition_pop p.words (s.value v)
  have feasible : pop (p.rows &&& ~~~c) ≤ pop p.words := by omega
  change sign (if pop (p.rows &&& ~~~c) ≤ pop p.words then _ else _) i=true
  rw [if_pos feasible,tally_spec]
  let hi := pop p.words-pop (p.rows &&& ~~~c)
  have lower : pop (p.rows &&& c)≤pop (p.words &&& pool[i]) := by rw [idx];exact y
  have upper : pop (p.words &&& pool[i])≤hi := by rw [idx];dsimp only [hi];omega
  exact bounds_keep pool (fun a => pop (p.words &&& a)) (fun _ _ => pop_le _) i h
    (pop (p.rows &&& c)) hi lower upper ((Nat.sub_le _ _).trans (pop_le _))

end PEqualNP.Outside.L_meta_17134_aux.CSP.Packed

namespace PEqualNP.Outside.L_meta_17134_aux.CSP.Packed

def chooseFrom : List Mask → Nat → List Mask
  | [],_ => []
  | a::xs,F => if F=0 then [] else
      if F.testBit 6 then a::chooseFrom xs (F>>>7) else chooseFrom xs (F>>>7)

theorem selected_mem (xs : List Mask) (F i : Nat) (hi : i<xs.length) (on : sign F i=true) :
    xs[i]∈chooseFrom xs F := by
  induction xs generalizing F i with
  | nil => simp at hi
  | cons v vs ih =>
    have nz : F≠0 := by rintro rfl; simp [sign] at on
    rw [chooseFrom,if_neg nz]
    cases i with
    | zero =>
      have eq : F.testBit 6=true := on
      simp [eq]
    | succ i =>
      have shifted : sign (F>>>7) i=true := by
        simpa only [sign,Nat.testBit_shiftRight,show 7+(7*i+6)=7*(i+1)+6 by omega] using on
      have hf := ih (F>>>7) i (by simpa using hi) shifted
      cases F.testBit 6 <;> simp [hf]

def flags (cs : Bands) (ones : Nat) (k : Fin 4) (v : Vertex) (pieces : List Piece) : Nat :=
  pieces.foldl (fun acc p => acc &&& bandFit cs ones p k v) (64*ones)

theorem flags_keep (s : Assignment k E D) (pool : List Mask) (i : Nat) (h : i<pool.length)
    (v : Vertex) (idx : pool[i]=s.value v) (pieces : List Piece) (pc : ∀p∈pieces,p.Valid s) :
    sign (flags (spectrum pool) (fill pool 1) k v pieces) i=true := by
  have all (ls : List Piece) (valid : ∀p∈ls,p.Valid s) (acc : Nat) (has : sign acc i=true) :
      sign (ls.foldl (fun u p => u &&& bandFit (spectrum pool) (fill pool 1) p k v) acc) i=true := by
    induction ls generalizing acc with
    | nil => exact has
    | cons p ps ih =>
      apply ih (fun b hb => valid _ (by simp [hb]))
      unfold sign at has ⊢
      rw [Nat.testBit_and]
      exact Bool.and_eq_true_iff.mpr ⟨has,bandFit_keep s pool i h p (valid p (by simp)) v idx⟩
  apply all pieces pc
  rw [←fill_mul]
  unfold fill
  rw [digit_sign (by simp) i (by simpa using h)]
  simp

def options (pool : List Mask) (cs : Bands) (ones : Nat) (k : Fin 4) (v : Vertex)
    (pieces : List Piece) (fixed : Fixed) : List Mask :=
  (chooseFrom pool (flags cs ones k v pieces)).filter fun a =>
    fixed.all fun q => disjointOnEdge k v q.1 a q.2

theorem options_keep (s : Assignment k E D) (pool : List Mask) (mem : ∀v,s.value v∈pool)
    (v : Vertex) (pieces : List Piece) (fixed : Fixed)
    (pc : ∀p∈pieces,p.Valid s) (fc : ∀q∈fixed,q.2=s.value q.1) :
    s.value v∈options pool (spectrum pool) (fill pool 1) k v pieces fixed := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp (mem v)
  apply List.mem_filter.mpr
  constructor
  · rw [←eq]
    exact selected_mem pool _ i hi (flags_keep s pool i hi v eq pieces pc)
  · apply List.all_eq_true.mpr
    intro q hq; rw [fc q hq]; exact disjoint_actual s _ _

def search (k : Fin 4) (pool : List Mask) (cs : Bands) (ones : Nat) :
    Nat → List Piece → Fixed → Nat → Option Nat
  | 0,_,_,_ => none
  | n+1,pieces,fixed,code =>
      let v : Vertex := ⟨(code % 16) % 10,Nat.mod_lt _ (by decide)⟩
      let opt := options pool cs ones k v pieces fixed
      opt.foldlM (fun tail a => search k pool cs ones n (follow pieces k v a) ((v,a)::fixed) tail) (code>>>4)

theorem search_sound (s : Assignment k E D) (pool : List Mask) (mem : ∀v,s.value v∈pool)
    (fuel : Nat) (pieces : List Piece) (fixed : Fixed)
    (pc : ∀p∈pieces,p.Valid s) (fc : ∀q∈fixed,q.2=s.value q.1) (i o : Nat) :
    search k pool (spectrum pool) (fill pool 1) fuel pieces fixed i=some o → False := by
  induction fuel generalizing pieces fixed i o with
  | zero => simp [search]
  | succ n ih =>
    intro ok
    let v : Vertex := ⟨(i % 16) % 10,Nat.mod_lt _ (by decide)⟩
    obtain ⟨b,c,step⟩ := each_run _ _ _ _ ok _ (options_keep s pool mem v pieces fixed pc fc)
    apply ih _ _ ?_ ?_ b c step
    · intro p hp
      obtain ⟨base,hb,child⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
      rcases (show p=base.yes _ _ ∨ p=base.no _ _ by simpa using child) with rfl|rfl
      · exact base.yes_valid s (pc base hb) _
      · exact base.no_valid s (pc base hb) _
    · intro q h
      rcases List.mem_cons.mp h with rfl|h
      · rfl
      · exact fc q h

def check (k : Fin 4) (E : Mask) (U : List Mask) (code : Nat) : Bool :=
  let pool := base U E
  (search k pool (spectrum pool) (fill pool 1) 10 [startPiece k E] [] code).isSome

theorem check_sound (k : Fin 4) (E : Mask) (U : List Mask) (full : Complete U E)
    (code : Nat) (checked : check k E U code=true)
    (presence : Vertex → Mask) (mem : ∀v,presence v∈U) :
    ¬Represents (graphData k) (fun v w => hit (presence v) w=false) := by
  intro rep
  obtain ⟨s⟩ := assignment_of_represents k E U full presence mem rep
  obtain ⟨o,ok⟩ := Option.isSome_iff_exists.mp checked
  apply search_sound s _ s.allowed 10 _ _ ?_ (by simp) _ o ok
  intro p hp
  simpa using (show p=startPiece k E from by simpa using hp) ▸ start_valid s

end PEqualNP.Outside.L_meta_17134_aux.CSP.Packed

namespace PEqualNP.Outside.L_meta_17134_aux.CSP.Packed

def subset (code : Nat) : List Piece → List Piece
  | [] => []
  | p::ps => if code % 2=1 then p::subset (code/2) ps else subset (code/2) ps

theorem subset_mem (code : Nat) (ps : List Piece) (p : Piece) (h : p∈subset code ps) : p∈ps := by
  induction ps generalizing code with
  | nil => simp [subset] at h
  | cons a t ih =>
    rw [subset] at h
    split at h
    · rcases List.mem_cons.mp h with rfl|g
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ g)
    · exact List.mem_cons_of_mem _ (ih _ h)

def selectedSearch (k : Fin 4) (pool : List Mask) (cs : Bands) (ones : Nat) :
    Nat → List Piece → Fixed → Nat → Option Nat
  | 0,_,_,_ => none
  | n+1,pieces,fixed,code =>
      let v : Vertex := ⟨(code % 16) % 10,Nat.mod_lt _ (by decide)⟩
      let opt := options pool cs ones k v (subset (code>>>4) pieces) fixed
      opt.foldlM (fun tail a => selectedSearch k pool cs ones n (follow pieces k v a) ((v,a)::fixed) tail) (code>>>(4+pieces.length))

theorem selectedSearch_sound (s : Assignment k E D) (pool : List Mask) (mem : ∀v,s.value v∈pool)
    (fuel : Nat) (pieces : List Piece) (fixed : Fixed)
    (pc : ∀p∈pieces,p.Valid s) (fc : ∀q∈fixed,q.2=s.value q.1) (i o : Nat) :
    selectedSearch k pool (spectrum pool) (fill pool 1) fuel pieces fixed i=some o → False := by
  induction fuel generalizing pieces fixed i o with
  | zero => simp [selectedSearch]
  | succ n ih =>
    intro ok
    let v : Vertex := ⟨(i % 16) % 10,Nat.mod_lt _ (by decide)⟩
    obtain ⟨b,c,step⟩ := each_run _ _ _ _ ok _ (options_keep s pool mem v (subset (i>>>4) pieces) fixed (fun p hp => pc p (subset_mem _ _ _ hp)) fc)
    apply ih _ _ ?_ ?_ b c step
    · intro p hp
      obtain ⟨base,hb,child⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
      rcases (show p=base.yes _ _ ∨ p=base.no _ _ by simpa using child) with rfl|rfl
      · exact base.yes_valid s (pc base hb) _
      · exact base.no_valid s (pc base hb) _
    · intro q h
      rcases List.mem_cons.mp h with rfl|h
      · rfl
      · exact fc q h

def selectedCheck (k : Fin 4) (E : Mask) (U : List Mask) (code : Nat) : Bool :=
  let pool := base U E
  (selectedSearch k pool (spectrum pool) (fill pool 1) 10 [startPiece k E] [] code).isSome

theorem selectedCheck_sound (k : Fin 4) (E : Mask) (U : List Mask) (full : Complete U E)
    (code : Nat) (checked : selectedCheck k E U code=true)
    (presence : Vertex → Mask) (mem : ∀v,presence v∈U) :
    ¬Represents (graphData k) (fun v w => hit (presence v) w=false) := by
  intro rep
  obtain ⟨s⟩ := assignment_of_represents k E U full presence mem rep
  obtain ⟨o,ok⟩ := Option.isSome_iff_exists.mp checked
  apply selectedSearch_sound s _ s.allowed 10 _ _ ?_ (by simp) _ o ok
  intro p hp
  simpa using (show p=startPiece k E from by simpa using hp) ▸ start_valid s

end PEqualNP.Outside.L_meta_17134_aux.CSP.Packed

namespace PEqualNP.Outside.L_meta_17134_aux.CSP

def selectiveBank : Array (List Nat) := #[
[0x1b1b1b1b1b1b113b1b1b1b1b113b1b1b1b113b1b1b113b1b1b113b1b113b113139ec6c6c6c6c6c44ec6c6c6c6c44ec6c6c6c44ec6c6c44ec6c6c44ec6c44ec44c4e7b1b1b1b1b1b113b1b1b1b1b113b1b1b1b113b1b1b113b1b1b113b1b113b113139ec6c6c6c6c6c44ec6c6c6c6c44ec6c6c6c44ec6c6c44ec6c6c44ec6c44ec44c4e7b1b1b1b1b1b113b1b1b1b1b113b1b1b1b113b1b1b113b1b1b113b1b113b113139ec6c6c6c6c6c44ec6c6c6c6c44ec6c6c6c44ec6c6c44ec6c6c44ec6c44ec44c4e7b1b1b1b1b1b113b1b1b1b1b113b1b1b1b113b1b1b113b1b1b113b1b113b113139ec6c6c6c6c6c44ec6c6c6c6c44ec6c6c6c44ec6c6c44ec6c6c44ec6c44ec44c4e7b1b1b1b1b1b113b1b1b1b1b113b1b1b1b113b1b1b113b1b1b113b1b113b113139ec6c6c6c6c6c44ec6c6c6c6c44ec6c6c6c44ec6c6c44ec6c6c44ec6c44ec44c4e71,0x1e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e30,0x1a9a9a9a9a9a913a9a9a9a9a913a9a9a9a913a9a9a913a9a9a913a9a913a913139ea6a6a6a6a6a44ea6a6a6a6a44ea6a6a6a44ea6a6a44ea6a6a44ea6a44ea44c4e7a9a9a9a9a9a913a9a9a9a9a913a9a9a9a913a9a9a913a9a9a913a9a913a913139ea6a6a6a6a6a44ea6a6a6a6a44ea6a6a6a44ea6a6a44ea6a6a44ea6a44ea44c4e7a9a9a9a9a9a913a9a9a9a9a913a9a9a9a913a9a9a913a9a9a913a9a913a913139ea6a6a6a6a6a44ea6a6a6a6a44ea6a6a6a44ea6a6a44ea6a6a44ea6a44ea44c4e7a9a9a9a9a9a913a9a9a9a9a913a9a9a9a913a9a9a913a9a9a913a9a913a913139ea6a6a6a6a6a44ea6a6a6a6a44ea6a6a6a44ea6a6a44ea6a6a44ea6a44ea44c4e7a9a9a9a9a9a913a9a9a9a9a913a9a9a9a913a9a9a913a9a9a913a9a913a913139ea6a6a6a6a6a44ea6a6a6a6a44ea6a6a6a44ea6a6a44ea6a6a44ea6a44ea44c4e70,0x14d4d4d4d4d4d4d4dad3535353535353536b4d4d4d4d4d4d4d4dad3535353535353536b4d4d4d4d4d4d4d4dad3535353535353536b4d4d4d4d4d4d4d4dad3535353535353536b4d4d4d4d4d4d4d4dad3535353535353536b0],
[0x1b1b1b1b1b1b1b1b113b1b1b1b113b1b1b113b1b1b14fb1b1b113b1b113b1134f9ec6c6c6c6c6c6c6c44ec6c6c6c44ec6c6c44ec6c6c53ec6c6c44ec6c44ec44d3e7b1b1b1b1b1b1b1b113b1b1b1b113b1b1b113b1b1b14fb1b1b113b1b113b1134f9ec6c6c6c6c6c6c6c44ec6c6c6c44ec6c6c44ec6c6c53ec6c6c44ec6c44ec44d3e6c0c0c1a58181834b0303069606060d326c6c6c6c6c6c6c6c44ec6c6c6c44ec6c6c44ec6c6c44ec6c6c44ec6c44ec44c4e7b1b1b1b1b1b1b1b113b1b1b1b113b1b1b113b1b1b113b1b1b113b1b113b113139ec6c6c6c6c6c6c6c44ec6c6c6c44ec6c6c44ec6c6c44ec6c6c44ec6c44ec44c4e7b1b1b1b1b1b1b1b113b1b1b1b113b1b1b113b1b1b113b1b1b113b1b113b113139b0303069606060d2c0c0c1a58181834c91,0x1e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e347468e8d1d1a3a34f9f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78d1d1a3a347468e8d30,0x820820820820820851d1d1d1d1d1d1d1e282082082147474747474747478a082082147474747474747478a0820851d1d1d1d1d1d1d1e2820821468d1a33a147474747474747478a147474747474747478a147474747474747478a147474747474747478d1a3468cf4,0x14d4d4d4d4d4d4d4dad3535353535353536b4d4d4d4d4d4d4d4dad3535353535353536b4d4d4d4d4d4d4d4dad3535313535353136b4d4d4c4d4d4d4c4dad3535313535353136b4d4d4c4d4d4d4c4dad3535353535353536b0],
[0x3030303030696060606060d2c0c1a581834ca2515d834b069944a2bc8c0c0c0c0c1a581818181834b030696060d328945760d2c1a65128af23030303030696060606060d2c0c1a581834ca2515d834b069944a2bc9b1b1b1b1b1b1b1b113b1b1b1b113b1b1b113b1b1b14fb1b1b113b1b113b1134f9ec6c6c6c6c6c6c6c44ec6c6c6c44ec6c6c44ec6c6c53ec6c6c44ec6c44ec44d3e6c0c1a581834b0306993636363636363622763636362276363636227636363622740a0c4d0283108141a0c489506831224833d8d8d8d8d8d8d889d8d8d8d889d8d8d8d889d8d8d8d889d02831340a0c42050683122541a0c48920cf636363636363622763636362276363636227636363622740a0c4d0283108141a0c4895068312248336060d2c0c1a581834c91,0x79f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e347468e8d1d1a7cfcfcfcf8fcfcf8f1f3f3f3f3e3f3f3e3c7cfcfcfcf8fcfcf8f1a3a347468e8d30,0x820820820820821474747478a0820820851d1d1d1e2820820851d1d1d1e282147474747474747478a0851d1d1d1d1d1d1d1e2820851a3467428e8e8e8e8e8e8e8f1428e8e8e8e8e8e8e8f1428e8e8e8e8e8e8e8f1a3468cf4,0x14d4d4d4d4d4d4d4dad3535353535353536b4d4d4d4d4d4d4d4dad3535313535353136b4d4d4c4d4d4d4c4dad3535353535353536b4d4d4d4c4d4d4c4dad3535353135353136b4d4d4d4c4d4d4c4dad3535353535353536b0],
[0x128944a2bb030696060d2c0c1a646060d2c0c0c0c0c1a581818181834d860d2c1a65128aec0c1a646060d2c0c0c0c0c1a581818181834d860d2c1a65128aec0c1a646060d2c0c0c0c0c1a581818181834d860d2c1a65128aec0c1a646060d2c0c1a581834c91394651d9364c4fc24f6181834b0306989ca308ec908e27e11394611d9211c4fc181834c9ec491394651d9364c4fc24f6181834b0306989ca308ec908e27e11394611d9211c4fc181834c9ec491394651d9364c4fc24f6181834b0306989ca308ec908e27e11394611d9211c4fc181834c9ec48c0c1a581834b0306992512894576060d2c0c1a581834c91,0x51a3a347468e8d3e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78d1d1a3a347469f3f3f3e3f3f3e3f3c7cfcfcf8fcfcf8fcf1f3f3f3e3f3f3e3f3c68e8d1d1a3a34d1a3a347468e8d30,0x410410410410e1468d19d0410a3a3a3a3c50410a3a3a3a3c50410a3a3a3a3c50410428e8e8f1428e8e8e8e4a4a8e8f1428e8e8e8e4a4a8e8f1428e8e8e8e4a4a8e8f1428d1a33f0a3468cf4,0x14d4d4c4d4d4d4c4da93535353535353136a4d4d4d4d4d4d4c4da93535353535353136b4d4d4d4d4d4d4d4dad3535313535313536b4d4d4c4d4d4c4d4dad3535313535313536a4d4d4d4d4d4d4c4dad3535313535353136b0],
[0xc0c1a581834b03069944a2bb06960d32894576060d3230303069944a2515d834b0699181834c9e4c4849e4f6181818181834c9ec306960d32894576060d3230306993c989093c9ec30303030306993d860d2c1a65128aec0c1a646060d2c1a5834c851c4e51d9364c4fc24f2793d893c9ec30306928e2708ec908e27e0c0c1a581834c9e4f62428e2728ec9b2627e12793c9ec49e4f6181834947138476484713f06060d2c0c1a64f27b126c6c6c6c6c6c6c6c516c6c6c6c44ec6c6c44e814189a050626c2834189b112a0d0626c44ec105166c0c1a581834b03069918181834ca25128aec1a5834c91,0x79f9f9f9f9f9f9f9e347468d1d1a3a34f9f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78d1d1a3a347469f3f3f3e3f3f3e3f3c7cfcfcf8fcfcf8fcf1f3f3f3e3f3f3e3f3c68e8d1d1a3a34d1d1a347468e8d30,0x410410410410410428e8f141043851a3467410a3a3a3a3c50428e8e8e8f1410410a3a3a3c50a3a3a3a3a3a3a3a3c50a3a3a3a3a3a3a3a3c68e8e8e8e8e8e8e8f1428d1a33f0a3468cf4,0x14d4d4d4d4d4d4d4dad3535313535353136b4c4d4d4d4d4d4c4dad3135353535353136b4d4d4d4d4d4d4d4dad3535313535313536b4d4d4c4d4d4c4d4da93535313535313136b4c4d4d4d4d4d4c4dad3535313535353136b0],
[0x113e5164c4f13f060d2c1a64f61834ca2515d834c913e5164c4f13f060d2c1a64f61834ca2515d834c8c0c0c1a58181834ca25128afa646060d35093c9a4f62a1279349ec4a2515d834b069944a2bb030699181834b03069d3214651c4f64d9313f093c9e4f624f2793d8944a2c15d81834b030696060d32894582bc9b1b1b1b1b1b1b1b1b1b1b1b113b1b1b113103e2607c6c2834189b112a0d0626c44ec1044e7b1b1b1b1b1b1b1b1b1b1b1b113b1b1b113103e2607c6c2834189b112a0d0626c44ec1044e6c0c1a581834b03069918181834b0303069944a2515f4c91,0x79f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78d1d1a3a3468e8d3e7e7e7e7e7e725e78d1d1a3a347469f3f3f3e3f3f3e3f3c7cfcfcf8fcf8fcf1f3f3f3e3f3e3f3c68e8d1d1a3a34d1d1a3a3468e8d30,0x10410410410410410428e8f1410410428e8f1410a3468d19d0a3a3a3a3c50410428e8e8f1428e8e8e828e8e8e8f1a3a3a3a3a3a3a3a3c68e8e8e8e8e8e8e8f1428d1a33d1a3468cf4,0x14d4d4d4d4d4d4d4dad3535353535353536b4d4d4c4d4d4d4c4dad3531353535353136b4d4d4d4d4d4d4d4dad3535313535313536b4c4d4c4d4d4c4c4dad3135313535313136b4d4c4d4d4d4d4c4dad3535313535353136b0],
[0x44f13ecd13c4fc22789f6689e27e1a74e9d3244f13ecd13c4fc22789f6689e27e1a74e9d3244f13ecd13c4fc22789f6689e27e1a74e9d323030696060d2c0c1a646060d2c0c1a581834c9b1b1b1b1b1b1b1b1b1b1b1f1b1b1f041b1b1f041b1b113b1b113f040419ec6c6c6c6c6c6c6c6c6c6c7c6c6c7c106c6c7c106c6c44ec6c44fc101067b1b1b1b1b1b1b1b1b1b1b1f1b1b1f041b1b1f041b1b113b1b113f040419b030696060d2c0c1a646060d2c0c1a581834c91,0x1e7e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e3e7e7e7e7e7e7e7e78d1d1a3a347469a3a347468e8d3e7e7c7c7c7c78f9f9f1f1f1f1e3e7e7c7c7c7c78d1d1a3a347469a3a347468e8d30,0x20820820820820820851d1e2820820851d1e282082147478a0851a3467428d1a33d1d1d1d1c94951d1e347474747252547478d1d1d1d1c94951d1e2851a3467a3468cf4,0x14d4d4d4d4d4d4d4dad3535353535353536b4d4d4d4d4d4d4d4dad3535313535353136b4d4d4c4d4d4d4c4dad3531313535313136b4d4c4c4d4d4c4c4dad3531313535313136b4d4d4c4d4d4d4c4dad3535313535353136b0],
[0xc0c1a581834b030699181834b030303030696060606060d361834b069b0c0c1a646060d2c0c0c0c0c1a581818181834d860d2c1a6c3030699181834b030303030696060606060d361834b069b0c0c1a646060d2c0c1a581834c8c0c1a6c306960d2c0c0c0c0c1a581818181834b03069b12303069b0c1a5834b030303030696060606060d2c0c1a6c48c0c1a6c306960d2c0c0c0c0c1a581818181834b03069b123030696060d2c0c1a646060d2c0c1a581834c91,0x147468e8d1d1a78fcfcfcfcfcfcf8f1e3f3f3f3f3f3f3e3c78fcfcfcfcfcfcf8f1a3a347468e8d3e7e7e7c7e7e7c7e78f9f9f9f1f9f9f1f9e3e7e7e7c7e7e7c7e78d1d1a3a347469a3a347468e8d30,0x820820851d1d1e2820851d1d1d1e2820851d1d1d1e2820851d1d1d1e28208214747478a1474747478a1474747478a1474747478a14747478d1d1d1e34,0x14d4d4c4d4d4d4c4da93535353535353136a4d4d4d4d4d4d4c4da93535353535353136a4d4d4d4d4d4d4c4dad3535313535313536b4d4d4c4d4d4c4d4dad3535313535313536a4d4d4d4d4d4d4c4dad3535313535353136b0],
[0x128945760d2c1a65128aec1a5834ca2515e5128af230306960d2c1a646060d32793c9ec30303030306993d860d2c1a64f6181834c8c0c1a64f2793d86060606060d327b0c1a5834c9ec3030699181834b06960d3230306993c9e4f624f61834b0303030306960d2c0c1a64f6246060d32793c9ec49ec30696060606060d2c1a581834c9ec4964d9251947c0a328ec9b27814651f028ca3e051947c0a328f814651d9364f0b26c928ca3e1230306960d2c1a646060d2c1a5834c91,0x1e7e7e7e7e7e7e7e78d1d1a3a347469f3e392f3f3f3f3e3c7cf8e4bcfcfcfcf8f1a3a347468e8d3e7e7e7c725e7c7e78f9f9f9f1c979f1f9e3c7e7e7c7e7e7c7c78d1d1a3a347469a3a347468e8d30,0x820820820820862820851d1d1e2821474747478a0851d1d1d1e2820851d1d1e2851d1d1d1e2851d1d1d1e347474747474747478a14747478d1d1d1e34,0x14d4d4d4d4d4d4d4dad3535313535353136b4c4d4d4d4d4d4c4dad3135353535353136b4c4d4d4d4d4d4c4dad3535313535313536b4d4d4c4d4d4c4d4da93535313535313136b4c4d4d4d4d4d4c4dad3535313535353136b0],
[0x6519470a958d352b1a6a562a5624ca328e152b1a6a5634d4ac54ac48c0c1a581834e99181834d424f27b15093c9ec4a2515d834b069944a2bb030699181834b03069d32303069a849e4f62a12793d8944a2bb06960d2c0c1a65128af259251d93c0a3b26c9e162c9e164f028ca3e051d9364f0b24a3b278496494764f028ec9b27858b278593c0a328f814764d93c2c928ec9e123030696060d3a646060d2c0c1a74c91,0x1e7e7e7e7e7e7e78f9f9f9f9f9f9f9e347468e8d1d1a7cfcf8e4bcfce4b8f1a3a347468e8d3e7e725c7e7e7c7258f1f1f9f1f9f1f1e3c7c7e7c7e7c7c78d1d1a3a347469a3a347468e8d30,0x20820820820820821478a0820821478a0851d1d1e285051d1d0628214747478a1414747418d1d1d1d1d1d1d1e3474747474747478a14747478d1d1d1e34,0x1e54d4d4d4d4d4d4daf9535353535353536b4d4d4c4d4d4d4c4dad3531353535353136b4d4c4d4d4d4d4c4dad3535313535313536a4d4c4d4c4c4da9353135313136b4d4c4d4d4d4d4c4dad3535313535353136b0],
[0xc0c1a581834b03069b0c1a5834ca2515d81834c8c0c1a5834b0699181834c9e4c4849e4f6181818181834d860d2c1a65160aec0c1a646060d327931212793d86060606060d361834b06994582bb030699181834b06960d323030303030696060d327b0c1a581818181834b0306960d327b123030303030696060d327b0c1a581818181834b0306960d327b1249c64ba0325d093d893d86060d2c0c1a62728f2808e27e1139479404713f06060d327b123030696060d2c0c1a646060d2c1a5834c91,0x1e7e7e7e7e7e7e7e78d1a3a347469f3e3f3f3f3f3f3e3c7cf8fcfcfcfcfcf8f1a3a347468e8d3e7e7e7c7e7e7c7e78f9f9f9f1f9f9f1f9e3e7e7e7c7e7e7c7e78d1d1a3a347469a347468e8d30,0x410410410410a3a3c50410e1468ce821474747478a0851d1d1d1e2820821478a1474725478a1474725478d1d1d1d1c94951d1e2851a3467e1468cf4,0x4d4d4d4d4d4d4c4dad3535313535353136b4c4d4d4d4d4d4c4dad3135353535353136b4d4d4d4d4d4d4d4dad3535313535313536b4d4d4c4d4d4c4d4da93535313535313136b4c4d4d4d4d4d4c4dad3535313535353136b0],
[0x6060d327b0c1a64f61834ca2815e4f624a874ea161834b069b0c1a65128aec1a646060d32793d8d3230306993c9a4f62a1279349ec49ec306960d32894576060d32306960d3a646060606060d327a849ec3030696060d328b05760d2c1a65160af214651e5164947c24f624f27b0c0c1a627b242389f83030696060d32793d892c928ec908f814651d93c24d62c908f859211f028ec908f814651d93c2c928ec908f848c0c1a581834b030699181834c9e4f634c91,0x1e7e7e7e7e7e7e78f9f9f9f9f9f9f9f9e347468d1d1a7cfcf8fcfcfce4b8f1a3a347468e8d3e7e7e7c7e7e7c7e78f9f9f9f1f9f1f9e3e7c7e7c7e7e7c78d9d1a3a347469a3a3468e8d30,0x10410410410410410a3c50410a3a3c5043851a33a1474747478a0820851d1e2851d1d1d1e347474747474747478d1d1d1d1d1d1d1d1e2851a3467e1468cf4,0x14d4d4d4d4d4d4d4dad3135353535353136b4d4d4c4d4d4d4c4dad3531353535353136b4d4d4d4d4d4d4d4dad3535313535313536b4c4d4c4d4d4c4c4dad31353535313136b4d4c4d4d4d4d4c4dad3535313535353136b0],
[0x18b44fc1834e9b1a6c498b44fc1834e9b1a6c49269349ac49a4d26b1a74e9d323030696060d3a6408ec9b2423e127b127b12894582bb030696060d2c0c1a65128b05791834b06992c9b2423e164d93c2c49ec59211f0b2423e164d93c2c9b2423e1259364847c2c9b2785893d8b2423e164847c2c9b27859364847c246060d2c0c1a581834c8c1a5834c91,0x79f9f9f9f9f9f9e3e7e7e7e7e7e7e78f9f9f9f9f9f9c979e347468e8d1d1a7cfcf8f8f8f8f1a3a347469e3f3e3e3f3e3c78fcf8f8fcf8f1b3a367468e8d347468e8d30,0x10410410410410410a3a3c50410410a3a3c50428e8f1410a3a3a3c68e8e828e4a4a8e8f1428d19e8e8e8e4a8e8e8f1a3a3a392a3a3a3c50a3468cf468cf4,0x14d4d4d4d4d4d4d4dad3535353535353536b4d4d4c4d4d4d4c4dad3535353135353136b4d4c4c4d4d4c4c4dad3535313535353136b4c4d4c4c4c4dad313531313136b4d4d4d4c4d4d4c4dad3535313535353136b0],
[0x60c993264c1829c193264c983053509349ac5424d26b0c0c1a581834ca2515d834b069944a2bc9509349ac5424d26b0c0c1a581834ca2515d834b069944a2bc9509349ac5424d26b0c0c1a581834ca2515d834b069944a2bc9509349ac5424d26b0c0c1a581834ca2515d834b069944a2bc983052519465194764f090482bd9364d93c2c9b26c9e164d9364f0b26c9b2781465194651f028ca328ca3b27848519465194764f090482bd9364d93c2c9b26c9e164d9364f0b26c9b2781465194651f028ca328ca3b27849830531,0x1e7e7e7e7e78f9f9f9f9f9e3e7e7e7e7c7e7e7c78f9f9f9f9f1f9f9f1e3e7e7e7e7c7e7e7c78f9f9f9f9f1f9f9f1e347468e8d3c7e7e7e7e7c7c78f1f9f9f9f9f1f1e347468e8d30,0x20820820820821478a0820820851e2821474747478a0851d1d1d1e2821474747478a0851d1d1d1e282147478a1474747474747478a1474747474747478d1d1e34,0x1e54d4d4d4d4d4d4daf9535353535353536b4d4d4d4c4d4d4c4dad3535353135353136b4d4d4d4c4d4d4c4dad3535353135353136b4d4d4d4d4d4d4d4dad35353536b4d4d4d4dad3535353535353536b0],
[0x60c993064c14e0c993064c14c9a4d624d26b1a74e9d3249a4d624d26b1a646060d350b150b128945760d2c1a581834ca2515e4c182928ec9e164d93c2c325c252e051f0b26c9e051d93c2428ec9e164d93c2c325c252e051f0b26c9e051d93c249349ac49a4d634c9830531,0x79f9f9f9f9e3e7e7e7e7e78f9f9c971f9f9c971e36746ce8d1d1a7cfcf8e4b8e4b1a3a347469e3f3f3e3f3e3c78fcfcf8fcf8f1b3a367468e8d347468e8d30,0x20820820820820851e2820820851e282147478a0851d1d1e3412525418a147478d1d1d1c951d1d1e3474747254747478a14747478d1d1e34,0x1e54d4d4d4d4d4d4daf9535353535353536bc5c54c4d4d4d4c4dad3535353135353136b4d4c4c4d4d4c4c4dad3535313535353136b4c4d4c4dad31353136b4d4d4d4c4d4d4c4dad3535313535353136b0],
[0xc0c1a5834b06960d3264c193260c1929c983264c18325350b0c0c1a581834ca2515d834b069944a2bd42c48c0c1a6a1269358a849a4d62c306960d32894576060d3260c149465194764947c24f624120af13d9313f06060d25194651947c181834c9ec485194651d9251f093d890482bc4f64c4fc1818349465194651f06060d327b1260c14b0306960d2c1a5834c91,0x147468d1d1a3a34f9f9f9f9f9e3e7e7e7e7e78f9f9f9f1f9f9f1f9e3e7e7e7c7e7e7c7e78d1d1a3a34f9f1f9f9f1f1f9e3e7c7e7e7c7c7e78d1d1a3a34d1d1a347468e8d30,0x20820820851d1d1e2820851e2820851e282125258a1474747478a082147478a1474725474747478a1474725474747478a147478d1d1d1e34,0x8208208208208104c82082082081020990410410408104c82082040810204132082081020408104c820820413218d8d8d8d8d8d8d8218d8d8d8d8d8d8d8208104c8104d5],
[0x3260c193064a6a126b0c1a64f634c993064c983064a6a126b0c1a5834c9ec3069944a2bb0699181834c9ac5424d26b127b0c1a5834ca2515d81834c982928ca328ec928f8482415e27b2627e12793d86060d2c0c1a581834c9e4f624b26c9e051d93c0a3e164f0b278147c0a3b27859364f093060a6a126b0c1a64f634c91,0x1e7e7e7e7e78d9d1a3a3468e8d3e7e7e7e7e78f9f9f9f1f9f9f1f9e3e7e7e7c7e7c7e78d1d1a3a34f1f9f9f9f1f1f9e3e7c7e7c7c7e78d1d1a3a34d9d1a3a3468e8d30,0x410410410410410a3c50410a3a3a3c50a3c50428e8f1428e8e8e8f1410428ce851d1d1d1d051d1e3474747474747478a147478d1d1d1e34,0x14de54d4d4d4d4d4dad3535353135353136be44d4d4d4d4d4c4daf1535371535313536b4c4d4c4d4d4c4c4dad3535353535353536b4d4d4d4da935353136b4c4d4d4d4d4d4c4dad3535353135353136b0],
[0x3264a6c3069b1634d892c3069b1634d893264a728b2785893d8b2423e128b057b278593c25160af265164f0b127b164847c25160af64f0b2784a2c15e4a4a328c23e051947c2c58b2423e164847c0a328f814651847c2490482bb030696060d32531,0xf3f3f3c7cfcfcf8fce4b8f1f3f3f3e3f392e3c7cfcfcfcfcf1e3f3e3e3f3e3c78fcf8f8fcf8f1a3a34f9f9f1f1f1e346ce8d9d1a68e8d30,0x10410410410410431410a3a3c50428e8f1410a3c68e4a8f1a392a3c509e8e8c8c8c8f1428d1a33cf4,0x14d4de54d4d4d4d4dad3535353135353136b4d4d4d4c4d4d4c4daf9535353531353136b4c4d4c4c4c4dad313531313136b4d4d4c4d4d4d4c4daab4d4d4d4dad3535313535353136b0],
[0x15ebd7af257af5ebc962c69d3a74c962c69d3a74c98305383053c3870e1c1870e1270e1c387061c384983053830531,0x1e7e7e78f9f9f9e3e7e7252525258f9f9c949494963e547ca8d3e547ca8d3e5e5e5e58f979797963e547ca8d3e547ca8d30,0x1a7a69e925252525a4949494969b2e9b2e94ecba6cba5363636363a58d8d8d8e9b2e9b2e94ecba6cba530,0x8208208208208208254104104104a82082081020408104a82082081020408104a8208104a820412e2e292121212658b8a484848499208104a8104b6],
[0xc0c1a64f61834d860d328a05793d89181834c9ec3069b0c1a65140af27b1260a581834e5164c4fc328b2627e15f870b0582bb03069934e993064c993260c1494651e51c24d624f62c9e194047c181834d93c24f62428ca3ca3849ac49ec593c32808f8303069b27849ec49b170d8b84c53170a70531,0x3cf8fcfcfcfcf8f1f3e3f3f3f3f3e3c68d1d1a7cfcf8fcfcfcf8f1f3f3f3c7cfcfcfcf8f1f3e3f3e3f3f3e3c7cf8fcf8fcfcf8f1b3a367468e8d3468e8d30,0x10410410410a3c50410a3c50428ce85051d1d0628208218a1478d1d1c951e3474725478a1468d19e8cf4,0x8208208208208208102041320820820408104c8208208104c82040810204132082084c82081020990408102040826410204081020990408104c8104d5],
[0x48404848487183064a7260c993060c94d860d2c1a6c3069944a2bb06992c306960d361834ca2515d834c9a6428ca328ec928f8482415d81834b0306994582bb06960d328b05790a3e051f0e164f0b2787028f8147c24c1829c1832531,0x79f9f9e367468d1d1a78fcfcf4b8f1f3f3f3e3f3e3f3c7cfcfcf8fcf8fcf1a3a347469e392f3f3e3e392c4cecbc8cf1f2a347469b3a3468e8d30,0x8208208208208218a0851e2851e2851d1e2851d1e282086b60851d1d1e34747474761478a147478d1e34,0x4104104104104104132082082082041320810209904104081020408264104102040810209904104132081020408104d8d8d8d8d8d8d8d8208104c8104d5],
[0x60ab82ad3634e9af5f4c926b0c1a74d8d36249358d32303069b150b172b1c384a2515d81834c982928ec9e16192e164d93c172e051f028ec9e164d93c24b26c9e051d93c2c5894b8147c0a3b27859364f093060a64d634c91,0x1e7e78f9f9f9f9f9e3e725c7e7e7c7258d9d1a3a34f1f9f1c94971e347468e8d3c7e7e7c7c7e78f1f9f9f1f1f9e367468e8d367468e8d30,0x1a311e8e9a2a47a5a48e9d3e8a9a345345254f25254fa685c745363234f4f11f8d3e9636311d8c47e311f8c4763a44fa247a52a9a34530,0x1e54d4d4d4d4d4d4daf9531353535353136bc5c54dc54d4c4d4dad3535353135353136b4c4c4d4c4c4dad3535313535353136b4c4d4c4daab4d4d4c4d4d4d4c4dad3535353135353136b0],
[0x125834b06993260c993060c94e4c193260c1929a8586060d2c0c1a6c306960d3289457a85892a16181834b03069b0c1a5834ca2515ea1624c1829988a328f3898b8482bb0696060d2c0c1a4a328ca328f830699057926228ca3ce262e120aec1a581834b0306928ca328ca3e0c1a6415e4c182992c1a5834c91,0x51a3a347469e3f3f3f3e3c78fcfcfcf8f1f3f3f3e3f3f3e3f3c7cfcfcf8fcfcf8fcf1a3a347469f3e3f3f3e3e3f3c7cf8fcfcf8f8fcf1a3a347469a347468e8d30,0x8208208218a0851e2821478a125258a125258a08218a1472525478a1472525478a147478e34,0x20820820820820990410410204132082082040826410410204081020990410408102040826410426410204081020990408102040826410209904d5],
[0x4a2515d834b069b0c1a5834d8944a2bc983052c0c1a73889e27e0a0502839d8e1c2c3030699181834e7113c4fc140a05073b1c38586060d3230306960d2c1a64c993060c99305393260c193260a581834d8e1c0a328f814651f06060d36246060d2c1a5834c9830531,0x71f9f9f9f9f9f9f1e347468e8d3e7c7e7c7e7e7c78f9f1f9f1f9f9f1e347468e8d1d1a7cfcf8fcf8f1f3f3e3f3e3c78fcfcf8fcfcf8f8f1a3a347468e8d347468e8d30,0x820820862820851d1e2821474747478a0851d1d1d1e2820851e2851e2851e3474747478a1478d1d1e34,0x208208208208208102041320820820413208204081020413208204081020413208208209904102041320820408264104081020408264104c8104d5],
[0xc983064c192960d327b1a64c983264c18325350a958b0c1a64f61834ca2815ec48c0c1a6e562c908f858e1c25160aec0c1a64c149465194764947c24120af13d9313f093d8b278303069b27849ec4851e71c24f60a3e19c70b278147c0a3b27849ec4983052c1a64f634c91,0x1e7e7e7e7e78d1d1a347469e3f3f3f3e3c7cfcfcfcfcf8fcf1f3e3f3e3f3f3e3c7cfcfcf1e3f3f3f3e3e3f3c7cf8fcf8f8fcf1a3a347469a3a3468e8d30,0x20820820821478a082147478a1478a084962851d1d1d1e2820851e2851d1d1e3474725474747478a147478d1d1e34,0x4104104104104104102041320820820413208204082641041020408264104081020408264104104c8204081020413218d8d8d8d8d8d8d8208104c8104d5],
[0xc12170c12170a6a162a5634d8d362a5624c14b0306990482bc4f64c4fc2e563870b9586060d325c2c3069d3264c193260c98296060d362e5638593c38303069b95892c928f814764f0b051f028f8147c0a3b27859251f092e161834e9930531,0x79f9e3c725e7e7e7e7c78d1d1a3a34f1c971c979c971e367468e8d1d1a7cf8e4bcf8f1e3e3f3e392e3e3c7cf8fcfcfcf8f1b3a347468e8d347468e8d30,0x820820820820862820851e282146742828e831410a3a3c50a3c68e8e8f1a3a3a3a3a3a3c50a3a3c68cf4,0x820820820820820820413208208204081020990410410209904081020408264104102099041020413208204081020413218d8d8d8d8d8d8208104c8104d5],
[0x150b161834c921212121c60c94e4c983060c992990a3b24a328f8542c3069b85860d328b057a85890a3e051f089f870e051f028f844fc24c1829c18325350b161834c91,0x1468d1d1a3a34f9f9f9e367468d1d1a7cf8f4b8fcf1f3e3c7cf8e4b8f8e4bcf133b2f233c7ca8d1d1a6ce8d1a3a34d1a347468e8d30,0x20820820849628218a085963478a0820860851e3236567e4c63a5851d1e3478c9634,0x8208208208208208104c82082082099041040826410408104c8208218192081020408104d8d8d8d8d8d8d8d820820413208104c8104d5],
[0x92c1a64c193060c9929b1a6c6993264c183064c94e090a3ce26228f85860d2c1a5834c82bb069925298b870e17970e171545c384a53170a7060a64b06960d3258d3634c91,0x1468e8d1d1a78fcfcf8fcf1a367468d1d1a78fcfcf8fcf1f3f3c7cf8fcf8f8fcfcf1f3f3e3e3e3f3c68e8d1d1a68d1d1a3a34d1b3a3468e8d30,0x820820820862821478c963478a0820862851d1e3254747258d1d1e38c9634,0x820820820820820826410410204132082081020990410408104c82082132081020408104c82040810204132082041320826408104d5],
[0x60c1258d3a64af5ebd793053829e1c387061c387092c2c2c2c383c3c38c1829c1829b1a74c91,0x1e78d1a3468e8d3e7a5e78f951f2a34f951f2a34f979797963e5e58d1f2a34d1f2a34d1a3468e8d30,0x69e92525a69693171d14cc5c745323236363a58d8e9b2e9d29d974e94c949690,0x20820820820820820820950410408104a8208208254104102095041020971490909093172c52424c5c904102095040825408104b6],
[0xa85860d3a6a562492c1a64c193060c9929c993060c1932538305372f9586060d320aec1a581834b0699057b97cac49294c5c3870bcb870b8aa2e1c25298b85382992c1a5834c950b0c1a74d4ac491,0x51b3a347468d3468e8d1d1a7cf8fcf8fcf1f3e3f3e3f3c68e8d1d1a7cfcf8f8f8fcfcf1f3f3e3e3e3f3c68e8d1d1a68d1d1a3a34d1b3a347468d30,0x1041092c50410c50428f1a3c50431428e831424a8e8e4b1428cf8c9634,0x820820820820810209904104104132082081020990410408104c82082132081020408104c82040810204132082041320826408104d5],
[0x4993064c183264a7064c183264a74b06960d3260c14ca53170e1c2f2e1c0d2a8b87094a62e14ca53170e1c2f2e1c0d2a8b87094a62e14e0c14c960d2c1a64d2c1a5834c91,0x1468e8d1d1a78fcfcf8fcf1e3f3f3e3f3c68d9d1b3a34d1d1a3a34f9f1f9f1f1f9e3e7c7e7c7c7e78d1d1a3a34d1a3a347469a36746ce8d30,0x8208208218a0851e2821478a125258a18d1c951c963472547258d1d1e38c949634,0x820820820820820826410410204132082081020990410408104c82082132081020408104c82040810204132082041320826408104d5],
[0x121c60c94e0c983064c94d8d3a64d3259241f0b24a3e16192e0c38525c2c920f84928bc2c3c2c178584a2f0945e1c60c14e0c1929b1a74c91,0x1e78d9d1a347469e3f3d2e3f3c68d1b3a34f951a3a34f1c979f1f1f9e267658d1a3a34d1a347469a346ce8d30,0x34f491d3a7d34b4749192a7d3453632323a54978c8e96363a44fa74a7a74d14c8c953e90,0x104104104104104104104a820820412a08204082541041020412a0820820950408102040825c5c52424c5c904102095040825408104b6],
[0x124962c4962c4962c49616161616161c5858585858587162c4962c4962c491,0x18e3468d3468d3468d28a3468d3468d3468d30,0x1a69d3a53d3a53d3a52a29d3a53d3a53d3a530,0x208208208208208219208208648208208104c82082041320820413636363636363618d8d8d8d8d8d820820413208104c8104d5],
[0x161834b06992c306960d3264c983060c9929c993060c19325324c5314c53170d3a540a0e7a74c9314c5314c5c34e9502839e9d3260c14d860d2c1a64b0c1a5834c91,0x51a3a347469a347468e8d3c7c7e7c7c78f1f1f9f1f1e3e7e78f9f9f1f1b9f9f9e3e7e7c7c6e7e7e78d1d1a3a34d1a3a347469a347468e8d30,0x8208218e2851e2851e282082182147478a147478d1d1e38e34,0x8208208208208209904104104c82082040826410410204132082084c82040810204132081020408104c8208104c8209904d5],
[0x306960d3a649090809090e3060894e4c983060c9929d3249ec30306990482bca2c15d834b06994582bc9ec4851f0b051f0e1c0a3e051f0b1260c14e0c192960d2c1a74c91,0x51a3a347468d3e7e7e78d9d1a347469f3e3d2e3f3c68e8d1d1a7cf8e4b8f8e4bcf133b2f233c7ca8d1d1a6ce8d1a3a34d1a3a347468d30,0x820821258a08218a085963478a0821ad821478c96951d851c962851f963478c9634,0x410410410410408264104104104104c82082041320820408264104104132081020408104d8d8d8d8d8d8d8d820820413208104c8104d5],
[0x1a74c95ebd7af257af5ebc98305383053c3870e0c3870e1270e1c3830e1c38498305383053a74c91,0x1468d1d1a3a34f9f9f9e3e7e7e78f951f2a34f951f2a34f979797963e5e5e5e58f951f2a34f951f2a34d1a347468e8d30,0x12525a69e9a7a48c8d3e923234fa48c8d8d8e923236363a6cba6cba53b2e9b2e94c949690,0x8208208208208208104a8208208209504104104a820820412a0820412e29212121262e58a484848498b920820412a08104a8104b6],
[0x34b069a95892424202438c18325383260c193253a64b2483e164947c0a3e16187045051f0b2483e12147c2c147c387028f8147c2c49829c183253a5834d4ac491,0x51b3a347468d3e7e7e78d9d1a34746992e3d2e392c68e8d1d1a7cf8e4b8f8fcf133b2f233c7ca8d1d1a6ce8d1a3a34d1b3a347468d30,0x91a7d24b49191d2469f4d14c8d8c8e9585e323a48c8c8d8e9a262e34f46a53d14c8d3e90,0x104104104104102041320820820820826410410209904102041320820820990408102040826c6c6c6c6c6c6c6c104102099040826408104d5],
[0x150b0c1a5834e9924b06960d3264c983060c9929c993060c19325383053f2b0c1a6415d40a0e6c1a6415fe5624f95860d320aea0507360d320aff2b1260c14c960d2c1a64a85860d2c1a74c91,0x51a3a347468d3468e8d1d1a7cf8fcf8fcf1f3e3f3e3f3c68e8d1d1a7ce4b8f8f8fcfcf1f392e3e3e3f3f3c68e8d1d1a68d1d1a3a34d1a3a347468d30,0x20862820862851e2851e2820862851d1e2851d1e2851d1e38e34,0x208208208208104c820820820826410410204132082081020990410426410204081020990408102040826410408264104c8104d5],
[0x1258b1a64b1634c9a74d8af5f4e992428ca3d98a328f8482be9d3a74c9c3830e0c3870e1260c14d8b1a64b1634c91,0x79e3468d1d1a68d1a3a34f1f1f1f1e3e78f1c94971f1c949628d1a3a34d1a347469a3468e8d30,0xd3a74d14f4e9a2992929292d349191f19191d1458f4e94f4e9a29e9d34530,0x10410410410410410c0c904104102099041040826410408104c8208218192081020408104d8d8d8d8d8d8d820820413208104c8104d5],
[0x5893d8d3a64e3064a7264c183064c94e991834b06990482bc9ac306994582bb06993870e1c1870e1c24c14e0c1929b127b1a74c91,0x51a347468d3e78d9d1a347469f3e3e3f3c7ca8d1d1a64b8e4b8f8e4a4b1f2f2c7ca8d1d1a68d1a3a34d1a347468d30,0x125234fa69a3a7a4953c94969a2991b6a79191d2c6c7498b8e8a7a74d14c948d3e90,0x10410410410410408104a8208208208254104102095041020412a0820820950408102040825c524c524c5c904102095040825408104b6],
[0xd3a6c4921210121c69b1260c983064c94d322407c362e1c272e07170bcb85e5c24480f85251f028f870b2787028f8147c2c9e1260c14e0c1929d3a6c491,0x146ce8d1a3a34f9f9f9e367468d1d1a7cf8f4b8fcf1f3e3c7cf8e4b8f8fcf133b2f233c7ca8d1d1a6ce8d1a3a34d1b3a3468e8d30,0x9192a7d24b49191a7d2469f4d14c8d8c8d1545e323a48c8d8d8e913e9b2e94f46a53d14c8c953e90,0x20820820820820820810209904104104c8208204132082040826410410c0c90408102040826c6c6c6c6c6c6c6c104102099040826408104d5],
[0x34e992424202438c1830539393a193a193c69924f62c928f8147c2c30e08a0a3e127b12147c2c147c387028f8147c2c49829c183853a74c91,0x28d1d1a34f1f9f1e3e725e78c971e971c96347468e8d3e7c725c7c7e7899d97919e3c7e5c78d9d1a347469a347468d30,0x8208218a08628218c96282165821478c951e2851e3478e34,0x2082082082082041320820820826410426410408104c820820990408102040826408102040826410413208104c8104d5],
[0x34c9a6c69af5f4c9829d32306960d362c70a4b830699305383070a70531,0x1e78d9d1a3a29e3f3e3f3c68d1a7ca8d1d1a78e4a4b8f8e4b1a347469a3468e8d3468d30,0x69a7a68e923a3a68a6474a9e474f1f1d3a74d14c8e8e90,0x104104104104104104254104104a8208102095041041020950412a081020408104b8a49920820412a08104a8104b6],
[0x2e16227e1248484848718225393860c183864a646060d3638651c39f0b12147c0a3e16387028f870b1260c14e0c1c29b85889f8491,0x28d1d1a3a34f1f9f1e3e7e7c78f1f1e979f1e3e7c78f9f1f1f1c979e26765e4678f951a3a34d9d1a367469a347468e8d30,0x8208218a08628218d1e2820860851e34761478d1f963478e34,0x104104104104104104c820820990410413208102099041043032410204082640810204082641040826410209904d5],
[0x191c5321212121c60c94f0e1c3870e1c24ce3858d370b1cee162c492970e1c387098b84a5c3853c38498325391c531,0x51a3a347469e3f3e3c6ce8d1a3a34f1f1e971f1e3c78f9f1c971c979e26765e4678f2e54d9d1a347469a347468e8d30,0x208208218a0863658d1e2820820851e3414761418f151e3658e34,0x104104104104104104c82082099041040826410408104c820821920810204082640810204082641040826410209904d5],
[0x2c58934d8d35ebe9924e58a3e1634e9d3a64a7060a6c58e12531,0x1e78d1a347469e3e3e3e3c7cf1e392e392e392c68d3468e8d3468d1d1a68d30,0x349192d3474d24647c6474e94cc5c7a53d3a68a7a530,0x410410410410410412a08208208104a82081020950410410412a081020408104a820825302424c9040825410209504b6],
[0x93d8d3a64e3060a7270c183070c94e9924f62c9e1209057935860d28a0a3e127b12392222393922223961829c18385327b1a74c91,0x28d1d1a34f9e3e7e78f1f1f9f1e3e5468e8d325c7c7c725258f97963c7e5c78d1a367469a347468d30,0x1654fa69a323a6951496969a29b6b191d24647498b8e8a7a74d14d953e90,0x10410410410410408254104104104a820820950408104a82082095040810209714931493172410412a08104a8104b6],
[0x34e992434203438c14c8684871494641f0b24a3e051f0b0c38147c0a320f84851f028f870b1c0a3e1c2c49829c183853a74c91,0x3cfce4bcf1e3f3e3c5ca8d1a74b8f1f3e3c7cfce4b8f8fcf1d2b2f233c7ca8d1d1a6ce8d1a3a34f9f9c979e30,0x410410410d0c50c504314314109e8e8e8f1a0a3c68cf478e8634,0x208208208208208208104c8208264104104c8208104c820821819218d8d8d8d8d8d820408102041320820413208104c8104d5],
[0x69b1248484871a64c9c9d0c9d0c9e33828f8542c147c2c3045051f0a85890a3e051f0e1c227e051f028f844fc24c1829c183253a6c491,0x51a347469e3f3e3c6ce8d1d14f9f1e971f9e3e7c78f9f1c971f1f9e26765e4678f951a3a34d9d1a347469a3468e8d30,0x8208208218a18a0863a58a0820851e36161478d1d1e3478e34,0x104104104104104104102099041320820826410408104c82082132081020408104c81020408104c820413208104c8104d5],
[0x1a6c49a101a1c69b124068687051f028f870b95861c2e560a3e12147c0a3e1c2e56187028f85cac49c3849a6c49a6c491,0x59d1a347469e392e3c6ce8d1a3a34f1c971e3c7c7899c97919e26725e4678f2e54d9d1a347469b3a3468e8d30,0x48c96923a48c96923a5323236323a48c8d8c8e9c78d32325a48c9690,0x208208208208208208104c820826410410209904104c820821920408102041320408102041320820413208104c8104d5],
[0x60c9829908090e3060c94c0484871a6428f8147c385861c2c147c2428f858e1c18147c0a3e1624d3260c1929c1930531,0x167468e8d1a78f4b8f1b3a3468e8d3c7a5c78d1d1f2a3499d97919e26765e4678f951a3a34d9d1a347469b3a347468d30,0x48e923a48e923a68a646464647491919191d345323a48e90,0x2082082082082041320820820826410410209904104c820820990408102040826408102040826410413208104c8104d5],
[0x3064a7253a7858af5f86992460d251f0d3638589305362c70932531,0x63468d1d1a68d1d1a78f8e4b8f1f3c64a4b8f8e4a4b1a347469a347953468e8d30,0xd3474d1d1d24b4a474b4d3c6474f1f1d3a74e34e8e8e90,0x208208208208208219208208208104c82082641020413208208606482040810209b1b1b1b1b041040826410209904d5],
[0xc1a5834c9924b06960d3270e1c3870e1c24e1c3870e1c38498305320afa6415f8699057905792415f4c82bf0d320af20af260c14c960d2c1a6460d2c1a64c91,0x147468e8d1a68d1d1a3a34f1f1f171f1e3c7c7c5c7c78d1d1a3a34c94971f1f1c949632525c7c7c725258d1d1a3a34d1a3a347469a3a347468d30,0x8628628716287162820862851e2851e28638e34,0x8208208208209904104104c82082040826410410204132082084c820408102099040810204132084c8209904d5],
[0xc1a64c92121012121c60c1c29e1c3870e1c3849a64905760d2c1a65160afcd834ca2c15e415e428f858e1c38147c0a3e1624c1829c183852c1a64c91,0x147468e8d1a78fcf8f1b3a3468e8d3c7c7a5c7c78d1d1a3a34f9f1c971f1c979e26765a4678b951a3a34d9d1a347469a3a347468d30,0x2086282086285963478a0821ad8218e951e962863658e34,0x104104104104104c8208208264104102099041020413208208209904081020990204081020990426410209904d5],
[0x64714e0c983064c94e4a7270c183070c94cc5c2c3069b1a6c493170d3a4a3e1a74c98305363870932531,0x1468e8d1d1a78f8fcf8f8f1a347469e3e3f3f3e3c7cf1f3e3f373f3f3c7cfcf8f8dcfcf1a3a347469a367468e8d3468e8d30,0x20820862851e38d1e2820820851d1e347478d1d1e38e34,0x104104104104104104c82082040826410410413208102099041042641020408104c8204081020413208104c8209904d5],
[0x38a64342438a6c6992c920f859251f0b161870a4b859241f09251785878582f0b0945e128bc38c1829c183253634c91,0x3cf1b3a3469d2e3c7cfcb1a367469e392e3f3e3f3c4cecb1a367469a3468e8d346ce8d30,0x8208208208628213a1a58a084f47478d051d0632323e5851f963658d1d1e34,0x2082082082082082082095041040825410408254104104104a8208104b8b8b8b8b8b8b862e2921262e4820412a08104a8104b6],
[0xb1a64af5ebd793053a64e1c387061c38709387092c69930531,0x1e78d1a347469e3d2e3c68f951a7ca8b951a7cb4bcbcb1a3ca9a3468e8d347ca8d30,0xc2d24b4d2d2464b4d14c8c8d8c8e9c78d325a48c9690,0x2082082082082082084a820820412a082095041040825410412e292121262926449920820412a08104a8104b6],
[0x183049a74c95ebd7af260a7053c387061c3870e1258585858707878718305383053a74c91,0x1e78f9d95963c7a5c78f97971e3e5e5c78f979797963e5e58d1f2a34d1f2a34f9d959630,0x1a7a595969a5a4c5c74533171d14c8c8d8d8e92323a4c5c7a533171e94d959690,0x820820820820820820825410410408254104a8208209504104b8a484848498b962921262e4820412a08104a8104b6],
[0x24c1929c94e9e162bd7e1a64c58a3e120afa6c69b1278785838787858718305362bf0932531,0x1e78d1a347469a347469e3e3f3e3c71e39292e39292c51a347469a346ce8d3468e8d30,0x349292d29e8a64b4a4b4b4d3c64745262e3d29e94f4534f4530,0x820820820820820860648208208104c820820990408104c8208219208102040826c6c6c6c6c6c6c1040826410209904d5],
[0x4992bd7af5e4af5ebd793060a7060a7870e1c1870e1c24e1c387061c387093060a7870924c91,0x51a3a347469e3f3e3c78fcf8f1f2a3e5469f2a3e5469f2f2f2f2c7cbcbcbcb1f2a3e5469e5ca9a347468e8d30,0x4969a7a69e92323a48c8c96923232363a48c8c8d8e9232325a71e34c9690,0x20820820820820820990410413208208264104264104082640810204082640810204082641040826410209904d5],
[0xb858d3a6493824c193060c9929c9c3060c1c325383053f2b19c70e0a0507360d313f0f95893e561834f028f87089f87cac4982993c384970b1a74c91,0x28d1d1a34f9f9c963e7c7e7c7e78f1f1f9f9f1e347468e8d3e7c7c7c7e7e78f9c971f1f1f9e3c7c7c78d1b3a347469a347468d30,0x20862820862851e3478a0862851e2851d1e2851e38e34,0x8208208208208104c820821320820810209904102041320821320810204132081020408104c8208264104c8104d5],
[0x894e090b86090b853634e993270c183070c94f0c0c1a6c3069b958e1c2e562494a62e1c385a5c385c55170e1294c5c29c14c9e1c24b1a74c91,0xa347469f3e3c68d9d1a3a34f1f1f9e971e3e7e78f1c971f1f9c963e7e7e7c7c7e78d1d1a3a34d1e547469a367468e8d30,0x10410410431410c6cb1a3c5043142831d2a3a3d2c68cf8d9634,0x410410410410410413208208104c82082041320810209904104264102040826431b1b1b1b1b1b0410408264104c8104d5],
[0x93260ab82ad3a6c69af5f4c9c6713170b1c1834947c252e0c1a64b1a6494a62e1c385a5c381a55170e1294c5c29c182993c3849634c91,0x28d1d1a7cf8f1e3f3f3e3f3c7cfcf1f3e3e3f3e3f3c68d9d1a7cf8f8fcf8fcf1b3a347469a347468e8d346ce8d30,0x8208208218a0851e3478a086347478d96347a547a58d1d1e38d9634,0x10410410410410413208208104c8208208102099041041099040810204082641040826c6c6c6c6c6c6c10408264104c8104d5],
[0x49829c14d85858585858714d8b1258b12531,0x18e3468d3468d28d1a68d1a68d1a68d30,0x1a6925a4968a74a7a74a7a74a7a530,0x208208208208208648208208648208208204132082041363636363636360820826c6c6c6c6c1040826410209904d5],
[0x5860d2c1a6460d2c1a64c9c3060c1c325393860c183864a6460d3a6b947c385791834e9ae51f0e15e4c1829b1c3848c1a5834c91,0x1468e8d1d1a68e8d1d1a78f8f8fcf8f1e3e3e3f3e3c7cfcf19292e3e373f392c64a4b8f8dcfce4b1a3a347469a36746ce8d347468e8d30,0x208638a1478a1478a082182147478a147478d1d1e38e34,0x820820820820820826410426410408104c8208102099041042641020408104c8204081020990410209904134d5],
[0x93260ab82ad3a6c69af5f4c9a74c9830534193870bcb87034aa2e1c283253294c5c3870b4b87034aa2e1c25298b85382993c3849a74c91,0xa347469f3e3c78fcfcf8fcf1a367469b3a347469f3e3f3e3e3f3c7cf8fcf8f8fcf1a3a347469a347468e8d346ce8d30,0x10410410c50428f1a3c50d0c50c68e831a392a392c68cf8e8634,0x2082082082082084c820820413208208102099041041020990990408102040826431b1b1b1b1b1b0410408264104c8104d5],
[0x1c60a74243438d3a64d3259241f0b24a3e162c30e14970b2483e124a2f0b0f0b05e16128bc2517871829c183853a74c91,0xf3c6ce8d1a74b8f1a367469f2a367469e392f3e3e3f3c4cecb1a347469a3468e8d346ce8d30,0x125a48c8e923a3a48d3e9a29b19191d2a4bc64749191d3474a7a74d14c8d3e90,0x410410410410410410412a082082541040825410410209504104a862e2e2e2e2e2e18b8a48498b920820412a08104a8104b6],
[0x1c305383853c3870e1c3870934c952b1a7854ac69a958a958934c983853c30531,0x51a3a3469c68d1a3a34f1f1f1f1e3e5468e8d32525c7c725258f951a3a34d1a347469a347468d30,0x1a3a69a3a4949494969a29b6b6d3453a3a68e90,0x208208208208208104a82082084a820820412a0820408254104104a82040810209493172410412a08104a8104b6],
[0x14d8d3a6bd7d3258d3a6be9af260a4a3b2785864b85cac70e172b051d93c24c1494764f0b0c970b958e1c0a3b2785cac48888888888888d4351468888d435147860a70531,0x1e7e78f9f1c979f1e3e7c725e7c78d9d1a3a34d14971c94971e367468e8d3452525c7c7258f9f9f1f1f1f1e367468e8d367468e8d30,0x2082082082086282086862821a18a08519e824a831428cf2541418d1d1d1d1d1d1e28519e8cf4,0x8208208208208212a08208204082541041020412a08208104a8204081020412a0820412a081020408104b8b8b9208104a8104b6],
[0x18305393070e183064a7260e1c3060c94d8e1c2c70e162c4963870b1c3858b1260c14e4c1c3860c9829c983870c19305383053830531,0x147468e8d3c7e7e7c7c78f1f9f9f1f1e3c7e7e7c7e7e7c7c78f1f9f9f1f9f9f1f1e347468e8d3c7e7e7c7c78f1f9f9f1f1e347468e8d347468e8d30,0x8208218a0851e2821478e38a08218a1478a1478a18e34,0x82082082132082040826410408104c820820408104c820820408104c82084c82040826410204132134d5],
[0x41290909082521c60a7260e1c3060c94c1290909082521c67051f0b051f0b1c3858ce0a3e1260a7270c183864c149479c70b1c2c7028f81479c70b1260a70531,0x1e7e78f1f9f9e3c7c7e7c78f9f9e3e7c7e7e7e7c78f9f1f9e3c7e7c7c78f9f9f9f1f1f9e3e7c7e78f1f9f9e30,0x208208218a0821478a1478a08634747478a0851e2851e34747478a1478d1e34,0x8208208208208104c82082082641020413208208104c863636363636360820820990408104c8636363636363608209904d5],
[0x1210909c48424271932534b03069b162bf0e051947c181834c9c1479c70b1624f6072e051f0b27849ec4851e71c2c5893d81cb8147c2c9e127b1260c14d31,0x1e7e78f9f9e3e7e7c78d1d1a7cfcf8e4b8f192f2f2c78fcfce8b8fcf1e3f3f3a2e3f3c6ce8d9d1a68e8d30,0x820820851e2820851e28218a084f41418a18d1d1e347478a147478cf4,0x1e54c4d4d4d4d4c4daf9531353535353136bc5c54dc54d4c4d4dad3535353135353136aad3537913535353136aaab4d4d4d4dad3535353135353136b0],
[0x1a64c983870c18325362c70b1c2c5892c58e163858b126993260e1c3064c14e9934c91,0x63e5468e8d3c72525c78f1c971c971f1e3c725c725c7c78f951a3a34c94971f1e3e5468e8d3e5468e8d30,0x69a29b69191b6d2464749191d345323236d6da68a74530,0x8208208208208408208208264102041320820810204082641041020408104c8208264102041363636363608209904d5],
[0x4848484871a64c983870c18325362c593c2c7045051f0b1258b164f0b1c114147c2c4983264c993060a7870e1297094b87038b870a7060a74c91,0x79f9f9e3468e8d3c7e7e7a5c78f9f1f9f9f9f1e3e7c7e7e7e7c78f1e3c7e7e7c7899d97919e3e5468e8d3468e8d30,0x208208208628218a1478a1258a1258a0820851e3472525618a147478e34,0x41041041041041320820820990408104c8208102041320820408104c82084082040826408102040826410209904d5],
[0x2bd7af5e4b162c58d3624b162c58d3624d3270e1c387061c3849260c14c91,0x1e78f9f9e963e7252525258f9c949494963a545ca8d3a5a5e5a58f951a68f951a7ca8d30,0x14a8e925a4969a299191b191d29d974e94d30,0x208208208208210208208209504104081020412a08208102040825410412e2e2921212126482094c0c0932410209504b6],
[0x1634d892424243893070c183270a7260e1c3060c94f0e1c252e1c1c7094b853c3849a64b1a6c491,0xf3f3f3f3e3c7cfcfcf1d14f9f1e971f9e3c78f9f1f979e26765e4678f2e54d1a3a34f9f9f9f9f1e30,0x9192d24b4d3d246c7491b1f291d246c6474e3c69e94c8c9690,0x104104104104102099041041320820826410204132082082081020990204081020990408264104c8104d5],
[0x2c6992bd7af5e4d3270e1c3830e1c3849260c14c9634c91,0x51d1a3469f3c7cf4bcf1d2a2e5469d2d2f2d2c7ca8d347ca8d3e5469a3a3468d30,0x34a5474d14c8c8c8e94c8d3e94e90,0x20820820820950410410410810410412a0820825c524242424c5c904104a6048619208104a8209504b6],
[0x162c69938d325858585878707871260a64b1634c91,0x12525258e963a58e951a34e97963e5469a3e5469f2a34c94949630,0x694a8e8a3a48d8e94f953e94e90,0x1042824646835410410d7d50435f54384a2a3c24b6b6b6c1094709154366d9b8dd784975e125048c8d06b2],
[0x183853a64e1c3870e1c3849269e1c2bf0af26993070a74c91,0x63468f2a68d1d1a64b8e4b8f1e3c64b8f8e4b1a347469a347953468e8d30,0x123a68e923a523a5a69a3a68e923a68e90,0x8208208208208208208208104a82082541020412a082082541020412b9e4820825410209504b6],
[0x58e1c24c1829e1c3870e1c3849c3870e1c3870924d3c2bf0e15e4d3c2bf0e15e4c1829b1c3849830531,0x146ce8d9d1a68e8d1d1a7cf8f8bcf8f1f3e3e2f3e3c78f8f192e3e37392c64b8f8dce4b1a3a347469a36746ce8d347468e8d30,0x8638a1c58a1c58a0821821478a1478e38e34,0x20820820820990410990410204132082040826410410990408104c820408264109904134d5],
[0xb1624af5ebd7924e1c387061c3849270e124962c491,0x79c94963e78f9e979e365a58e949796963e5469a3ca9f2a34f9c949630,0x125a52a3a28e96323a53c78d34c9690,0x8208208208208104a820820840820820950410412e29212121262e4820825302430c90408254104a8104b6],
[0x162c58938a6c2c2c2c383c283893870924b162c491,0x494963a58e96365a58e95163e5469a3469f2a34c949630,0x92d2951d34532323a53c78d34c9690,0x20820821231012341aa1afaa086bea821c251c24b6b6b6c10e122b51d47c66699b8c971e1248c4048d06b2],
[0x2c57d32404071a64e1c3870e1c3849260a64b15f4c91,0x3ce4a4a4b1f3c7cfcf1a2e5469d2d2f2d2c69a3e5469a34f9c94949630,0x1a6923a48c8c8e9a48f8e94e90,0x208208208208104a820820820820820950410412e29212121262e4820825c90408254104a8104b6],
[0x162c490101c49c3870e1c3849270e1258b12491,0x1e78d1a347469e3e3c6cb1d2d2f2d2c68d347953468d1d1a68d30,0x4969a69236323a53c78d325a530,0x20820820820820820820820412a0820950410412e292121262926482082573c9040825410209504b6],
[0xb1c2c49260e183064e14d3c3870e1c3870934c9a64b1c2c491,0x147951a71e3f2c64b8f8e4b1e3f2c64b8f8e4b1f2a347469f2a347469a3ca8d30,0x91d3451d2db4d14c8d16948e9a29d14c8e90,0x820820820820820413208208408208606482040826410430324102041363636363608208264104c8104d5],
[0x2c492121210121c48c1a6c58b1c2c49260a6c58e12491,0xc7ce4b8f1e3e392e3c7cf192e392e392c68d3468e8d3468f2a68d30,0x3491d34f1d29f1b1d3a74e34d30,0x2082082082082082082082095041020412a082082541020408104a8208253024c9040825410209504b6],
[0x49929e1634d7afa64e33898b858e172b1c385cac494a2222222225cb46888947860a64f0e12531,0x28d1d1a7cf8f1e3e3f3d2e3c7cfcf1a2e392e392c68d9d1a7cfcf8f8f8f8f1b3a347469a3cb95346ce8d30,0x10410410c50431d0c50431a0c67a3a0a3a0c68cf8cf4,0x208208208208212a08212a082040825410425410204082541040825c5c5c90408254104a8104b6],
[0x1c534d34a22222222222350c251a251e188b42c382c168506a2f0d45e1c60a7060e14d31,0x3cf172a3469d2e3c7cfcb1a367469f392e3e3e3e3c74a8b1a367469a34795346ce8d30,0x10410410431410c50c504279e828e831a0d2c68cf658cf4,0x208208208208208209504109504254104104a8208104b8b8b962e2921262e4820412a08104a8104b6],
[0x92c49829b0b0b0b0b0b0e24c14f0e12491,0x638c94963468d28d1a68d1a68d1a68d30,0x69a4968a5325a71e34d30,0x20820820820821aa086bc2a351e125478546a351e122171e125478546a351e120c0307158160e325c78492],
[0xb164f0ca3849212121c4983860c19385393070e183064a6c147c0a3e1c387028f85893053a64b164f0ca38491,0x79c979c971e3e7e7e78d1a3a34c971e971c963c78f9f1f179e26765e4678f951a3a34d1a3a34f9c979c971e30,0x247492d3491b1d2991b1e291d24646474d1c69e94c8e90,0x1041041041320820820820990410413208102099041042041020413204081020413208104c8209904d5],
[0x1824c1c3060c9c29b1c2c7093870e1c3870e126093070c193070a7870e1c3870e1260c14e0c14d8e1638491,0x1c7c78f1f9f1f1f9e346ce8d1b3a34f1f9f971f9e3c7c78f1f9f1f1f9e3e7e5c7c7e78d1d1a3a34d1d1a3a34d1b3a346ce8d30,0x8208218a0879638d1e282086287963478e38e34,0x82082082084c8208102099041020990410204132082084c82040826410204132084c84c8104d5],
[0x2c70d3248484848714f0e1c3870e1c24e183260c1c29b051f0e1c38147c2c4983053a64b1c34c91,0x79f9f9f9f1e3e7e7e78d1a3a34f9f1e971f9e3c78f9f1f1f9e32565e4678f951a3a34d1a3a34f9f9f9f9f1e30,0x8218a08628218d1e2820821c58d1d86287179638e34,0x1041041041320820820820990410413208102099041042041020413204081020413208104c8209904d5],
[0x24c1929d3270e1c3870e1c24c193260c9829f0f0b0e0f0f0a0e387093064a74c91,0x1e78d1a367469a3e5469f3f2f3f2c71e392e392c51a3ca9a346ce8d347ca8d30,0x692525a74a64ac64ac74f1d14e3c699292d3a530,0x820820820820860648208104c820820990408104c82082082040826c6c6c6c6c6c6c1040826410209904d5],
[0xb1c2490909090e34c9c3870e1c387093858e75ec5793869d3c34e99387092c70934c91,0x146ce8d1d1a78fcf8f1a347469f3e3d2f3e3c78f1f3e373f3c4cecbc8cf1e5ca9a367468e8d3468e8d30,0x208208628638d1e2820820851e3e1618f151e38e34,0x410410410410413208208264104104c8204082641041041020413204081020413208104c8209904d5],
[0x121c49a7870af5f84962c6993260e1c3060c94f858587858787871c3849a64b1634c91,0x1e78d1a3a34f1f9e971f9e3468d9d1a7cb1e3f3f2f3c4cecb1a3ca9a347469a346ce8d30,0x1a7a34a74ac749192d29b191f291d246c74e3c69e94c8c9690,0x10410410410410412a082082541020412a0820412a082084082040825c5c52424c5c90408254104a8104b6],
[0xb163869938a7870e1c3870e1264c183260c94b939223911a23961829d3258b1c34c91,0x79c979f1e3e78d1a3a34f9d17979e3e58c971f1c96345e58f951a3a34d1f2a34f9c979f1e30,0x125a6986992b1b192d29a7d246c74e3a29e94c9690,0x1041041041020950410410412a082082541020412a082084082040825c524c524c5c90408254104a8104b6],
[0x24909090e24e1c3870e1c24e161857af624e163858d3624e1c24e12491,0x20d1d1a78fcf8f1d14f9f1e971f9e3e7c7e5e7899d97919e3cb953468e8d3068e8d30,0xb2d24b4b2d246c74b1f2d246c6474e3c69e94d9690,0x8208208208208209904132082082641020413208208208102099020408104c8104c8209904d5],
[0xb1270e1c3849270e1c3830e1c24e1c2492c491,0x51d1a34f9e3c7a5c78d96963a5e5a58f951a68f2a795347468d30,0x694a8e8a3a48c8e94c8e9694e90,0x104104104104104a8208408208254104104a81020412a084a6048619208104a8209504b6],
[0x1249c1870e1c3849249c38492491,0x638a3469a34d1a34d1a68d30,0x69a294d3c78d34d30,0x410410410410435e122171e125c7849c78c971e125c78492],
[0x71a121c70e1c3870e1c24e126090b86090b853a121c711,0x1e5c78e3e78d179f9d163ca8e8d3c78d963e78f971e30,0x3474d3474b19292b1d345385a53a3a68e90,0x208208208208254104109504104a82040825410412a08104a498b9208408209504b6],
[0x49a1a1c69934343828f858e161858b1264c1c3860c9829e1c24d32491,0x68a78e4b8f1f3f373c78e4b8f13392f233c4ce4bc8cf1e5ca9f3f373c74530,0x208208218a18e38a082085863618f179638e34,0x208208208208208264104c82082641041320820820408102099020413208104c8209904d5],
[0x57d324868687121a121c64c1c3860c192928f858e163870b1260a78495f4c91,0x1e7e725c78f1f9f1e34e971e3c78f9f9f179e365e4678f2e54d1a3a34f9f9c971e30,0x10410431c50410c50438b1a0c68cf8e34,0x410410410410413208264104303241020990410410408104c81020413208104c8209904d5],
[0x4927092c2c24242c2c38930532491,0xc68d3a5a58a34d1a34d1a68d30,0x1a69a29a78e94e90,0x410410410410435e125048d06a84951e0b02c1c64b8f0938492],
[0x714c9c38492531,0xc71c68d3658d1a34d1a68d30,0x1a69a3a53c78d34e8e90,0x410410410d504359191d6e3c2443849c78c971e125c78492],
[0x93870e1c24c14f0e1c1870e1c24c14f0e12491,0x1e78f1d963c7a5c78f963e5e78f9797963e5e78d1e54f1d9630,0x185a5969a5a5323a3a48c8d8e923a3a71e34d9690,0x82082082082084a820820950412a0821020825408104a49920825410209504b6],
[0x38d090d0e225393070e183064a511111113e08d130c14f0922531,0xf3c68d3a5c78d1b3a34f963c7e7c5e7899d963479534795346ce8d30,0x410431410424b1431438b191d2c28cf8e34,0x10410410410410412a08212a08104a820825410810408104b8b8a48498b9208104a8209504b6],
[0x70e1c3870e125393060e183253829e12531,0x1e78d1d14d179f979e3468d3e58f1c97949634795347953468d30,0x3491d2c74d29f2d3c6c74e34e90,0x41041041041042541042541020412a08208104a84082040825c524c90408254104a8104b6],
[0x1c48686871129c983870c1832528888888889f089870e1270922531,0x1e78d3a5c78f96346ce8d3c7e7a5e7899d963479534795346ce8d30,0x20820862820869628218f9632387979638e34,0x208208208208208254104104a820412a082082082095020412e2e2921262e48104a8209504b6],
[0x2c69924242438e1c3870e1c24f0b090b0d0f0e2c147c3870e051f0b1260a7849634c91,0x1468e8d1a78fcf8f1e3c64b8f4b8e4b1e3c7cf8f8bcf1b2f233c78fc9cf1a347469a347468d30,0x3492d3491b1d29b1b1d24646474d1c69e94e90,0x4104104104c82082082641042641020413208210208102099020408264104c8209904d5],
[0x1c24e1c3870938e1c3870e1c3849c3060e14f0e1c3870e1270e1270938491,0x59d1a3a34f1f1f1e3468e8d3e7c7a5c7e78f1e3c6e78c9597919e3cb95346ce8d367468e8d30,0x8218a18e3e58a082087163e1618f179638e34,0x4104104104109904104c82082099020413208208208104c8102040826410209904134d5],
[0x53c24930532531,0xc71a34e96963658d1a34d1a68d30,0x69a69a69694e90,0x410410410d50435b8dc7849412341aa171e120c03071a8f092e3c24b8dc78492],
[0x71c3870e12485871c3870e1c387093070c1c29e1c3870e1c3849c38492161c711,0x71f1e3c7c7c78f9f9f1e3c7e7a5e7c78f1e3c7c7899d96919e3cb953e7e7c78f1f1e30,0x208628218e3e58a0820863e58e38e34,0x41041041042641041320820990408104c8208219218dc3920408264109904134d5],
[0x2480e24e1c3870e1c24930532491,0x28e8a78f8f1b2c74b4bcb4b1a68f2a68d3474530,0x1a69a48c8e9a48f8e94e90,0x820820820821c38494141aa1c2491a0a0b8dc28247592e351e0b02c1c64a8dc7849c38492],
[0x7127049c3870e1270e1c3870e1c24e1c24e183070a7870e1c3870e1249c12711,0x51d1a34f9b9e3c7c5c78f1f9e979f1e2e5468e8d3c7c78c959694963c78f9b9e347468d30,0x218a18a18f9628218a18a1478a18e34,0x104104104104c82084c820820990408104c821321c34992081020408264108109904d5],
[0x3c38e3870e1c3870e124842684271829e1278711,0x6346ce8d3e5e58f9d16979e38f1e3479534795346ce8d30,0xd3474d1d34ac6474b4f1d3c6c74e34e8e90,0x41041041041043241041320820826408104c820820870e58d8d8d8d8208104c8209904d5],
[0xc1129e3870e1c3870e12684840486870e4e4e4e5860a7849822531,0x79f1e3e78f1c96267e4678f963c7c78c97963c7e5c78d1e54f9f1e30,0x2cb4d29b1b1b1d29b1d2474e3a29e34d9690,0x104104104104a820820825410425408104a82084082097149314931724104a8209504b6],
[0x1c248080e3870e1c3870924e1c24938491,0x79e3468e8d3c7c78e325e5a58d1a68f2a68d3468e8d30,0x5969a696323a53c78d34d9690,0x41041041090d6e375e0d64a091a0d5042491a0919c282475a8f0938f192a371e125c6ebc1ac92],
[0x93870e1c387092c70d35ebe9929e1c24e12531,0x1e78f97963e5e7e5e78e3c725e5258d1a68f2a68f2a68d30,0x34b2d2c74f1d3474e3c69e34e8e90,0x410410410410412a0820820950408104a82082082081020950412981212648104a8209504b6],
[0x24e127093870e1c3870e1257af5ebc8e4e4e4e5870e1270938491,0x1e78d1e54d1e54f979797963c7c58a3468d347953479530,0x1a71a78d363636363a78e8a71e34f1a78d30,0x10410410410410c0c904104c8209902041320820821219636363636363608104c8209904d5],
[0x49210121c585869f12121c7090a3e1c385861c2c147c24c983870c1930536161a7c491,0x51d1a34f1e971e3e7e78f1e971e3cbca8d26765e467899d919e3c78f9f9e347468d30,0x8218208628638a0848e08638a18e14,0x208208208209904104c82084c820826410413208102041320408264108109904d5],
[0xe20948484841290e38c9c3060c1c3253c38533170e15ec70af260a6c70e12711,0x3ce4b1e2f3c68e8d3c7c7e7c78f9e3c6e7e78c94979f1b9c9634747953468d9d1a68e8d30,0x208628638d1e282086367e7851e38e34,0x1041041041042641041020990410990408104c82084c870f0636486363636363608209904134d5],
[0x38e34f0b15ebf0d3264e14e0a6c57e12711,0x31f3c68e8d3c7c7c78e3c7258f179e3468d1a68e8d30,0x208208208638e2820862859638e34,0x2082082086bc38747849d1e121313136a8212214da3aa1c362a0a6d660e2b071e327478492],
[0x4921a1a1c6848719c147c2c70b0c385893064e1c3260c14e0a7060e14c91,0xa347469e3f3e3c71d2f3c7cf8f1f3f3e3e3f3c6cbc8cf1e547469a3a346ce8d3468e8d30,0x208208628628218a0851e3478d1e3478e34,0x10410410410410413208264104204102099041099040810209902041320826410209904d5],
[0x24d0d080e3849c24e1c3870e1c3849c24e12491,0x1c78f1f1e34795347953a5a5a5a58d1e54d1e54f1e30,0x1a6923a48e923232323a48e923a690,0x8208208208208208208606482099041041320820990204132082099041360655],
[0x1c29e3870e1c3870e1248686871c24e14f11,0x165c78e3c7e58e971e971e3658f1e3cb95365c78f1f9630,0x8208628213e28208628eb618cf4,0x20821c3ac8821af0a8f09208fc68208fc6835410eb22141aab75e151a8f0938759385478492],
[0x38699202038e1270e1c3870e1c24c14c9c34c91,0xf3b2b2c7cf1e3e3c68b951a74bcb4b1c7cb8f1a34f9d959630,0x1a6923a48c8c8e9a48f8e94e90,0x4104104104104a8208208208209504104a81020412a08209724104a8209504b6],
[0x49c3870e1270e1c3849c3849c3849c387061c387093870e0c3870e1270e1270e12491,0x1c7c78b9f139e2e7c4e78f2e54f2e54f979797963e5e5e5e58f2e54f2e54f1f1e30,0x8218208608218638e38e38e14,0x8208208213208209904104c82084c82132040826408104c82132134d5],
[0x908484e242121389387093e56265e1c0a3e1c252e1f2b127cac4cbc38147c384a5c3e5624e24f0e12491,0x31f373c7cdcf1834d9d1b3a34f1f9f1d179e3c7e7c745e78f979696346ce8d9d1a60d30,0x20820851e3478a18a18d1e3478e38e34,0x410410410410c904102099041020990410413213208102041320810204132084c8209904d5],
[0x34389384927b164f0b1638165c24f624e3060e14c91,0xf3c7cf1f3c68d3cace8d3c725c745258f96963468d9d1a68d30,0x694e8e94e8a74ac74b1d1d3a74d14d30,0x41041041041042541042541020950410412a08254102040825c524c90425410209504b6],
[0x34c901c49c24e1c3870e1c3849c24d32491,0x1e7658f1f1e34d172a34e96969696347953e7658d30,0x1a69a48e92323a48e9a690,0x10410410410424246835a0a0d50910e351a8f0924682828246835a8f0a8d47849212341ac92],
[0x24908484e24212138b160a3e1634d892c5828f858d362493060a6bf0e12491,0x20d3e6e78f9b9e38f9f1f9b9f9e3e7c7e6e7e78d36746ce8d3e7e7c7c78d30,0x820863478d1e282147478d1d1e38d1d1e38e34,0x1c5c54d4c4c4c4dad250fbd27ad2654943ef49eb49953535353796aaaa4d4d4d4d4c4c4daaaa935353535313136b0],
[0x53c3870e1c3849c3870e1c3849c24e12531,0x51a34e3c7e58c971f1c963c7e58c971f1c963ca8e8d3ca8e8d3468d30,0x1a68a3a6968a3a6969a29d14e90,0x208208208208208204132102082132081020990410990408104d8d8d8d8d8208264104c8104d5],
[0xe38b162c58d362493060a6c57e12491,0x1e78c971e3e78e3c72525c7258d346ce8d3e7c7c78d30,0x1a4969a3a78e94cc5c7a53256363a530,0x208208208486bc38492330cc361aa08494121412338506a849bb715838c9101634141ac92],
[0x53c39393939393961c38492531,0x594963a58e96365a58e94963e5469a3469e54d949630,0x165a52a3a28e9a53c78d34d9690,0x104104246202c6835435f5435f5410e1c24b6f5f5c10e122bc78c971e1248c4058d06b2],
[0x1c71258b1258b12491,0x18e3258c9634d1a34d1a34d30,0x19e7a3a68e94f4e94f4e94d30,0x820820821aa086bc3849c3848821250d0d0eb434343ac92],
[0x49a1a121a1a1c4921a1a1a1a1c49c24e12491,0x71e3c725c7258f1e3c725c7258d1a68d1d1a68d1d1a68d30,0x1a68e9a68e9a68e9a3a690,0x82082082082087092832390a0c8e435e1250647214191c86bc24b8f0a8d4784971e151a8f0938492],
[0xd0d090e38e14f0e1c3870e1c24e1270938531,0x638f1e3c78d1e54f1e971e96346ce8d3468e8d3479530,0x1a68e9a3a48e94523a523a68e9a3a48e90,0x4104104104104104104104a820412a08208209504104a8102095cf24104a8209504b6],
[0x93270e1c3849270e1270e1c3830e1c3849c24932491,0x1e7658f9e3c7a5c78f951a68f951a74bcb4b4b1e5ca9f3b2c7ca8d30,0x34a5474a64749191d38d3a530,0x8208208208212a0821020820950410412a12a0408104a6048619208209509504b6],
[0x3070c1c29e1c3870e1c24e3870e1c387092253c3870e1c38709387093870922531,0x1c78f1b9e3c725e4e7258f1f1e3c5c7e7c7e78d1b3a34f971f9f1f9e367468e8d347468e8d346ce8d30,0x2082082087963478e3e58e3c58e38e34,0x10410410426410e1a4c904102041320820821320810209904104c810209909909904d5],
[0x182993849c24c14c91,0x6963258e963e5469e5469a3ca992c7ca8d30,0xa3a694d3e5a28e9a530,0x20820821afaa16341aa1a3aa175e122141e341aabeb6d8546a3c38496341add78492],
[0x44a78e1239393939393961829922531,0x595963a58e963ca8d3a5e58f951a7cb8f1e54d959630,0x694a8e8a3a48e94c8d3e94e90,0x10428246835410d7d50d7d50e136a8f092dbd6db04251c24550c362506b75e125048d06b2],
[0x29e30532531,0x125258e963a58e962e5469a3469e54c949630,0x1a52a3a28e94e9694e90,0x410410b191a0d50d1d50435f54385478496d6d821c2456a3a8f8d4784971e1258c8d06b2],
[0x14c9c38494c91,0x1258d963258d95963e5469a3469b2c7ca8d30,0x28e9a3a534d3c78d3a3a530,0x82082086bea870e1221a1aa0870e1270915f5b6c38f193870938492],
[0xb1270e1c3849c3870e0c3870924e1c24b12491,0x79d963e78f1e971e3a58c9794963e5469a3ca9f3b2c7ca8d30,0x125a52a3a5363a53c78d325a530,0x10410a8f06b2208786b41af41aa087592dbd7d713d70a8f0915e3c64a8f06b25478492],
[0x1268406871829e1c3870e1c3849c24c14c91,0x1c7e58f1f1e365c78e3e5c78e9796963cb95365c78f1f9630,0x1474d2474d29919191d38d323a28e90,0x1041042830d89aa14141aa190c4a0d50d5043870915a6a0a6d6a351e171e1264312835a0c3626b2],
[0x12404071212121e1e1c49c38492491,0x79e3e5658f979638c9794963469a3ca9f2b2c68d30,0x165a6963a53c78d365a530,0x2082082121ad078eb412341aa084941e341ad47849c78c941e3ad478492],
[0xe29e3250e1c2850c94a222227c2261829e12711,0x1e78d3a5c78f96346ce8d3e7c7c5c78d163479534795346ce8d30,0x410431410431410c78b191c28cf8e34,0x208208208208254104109504104104b8b49920408104a8104a8209504b6],
[0x2493830e1c3870924930532491,0x31c51a69a3469a34d30,0x1a68a69a58e94e90,0x820820820821af0910924e3c64e32492],
[0x38930532491,0xc71c68d3658d1a34d1a68d30,0x1a69a69694e90,0x20820821aa086b23adc7849c24e3c64e325c78492],
[0x1249c484848484848712712491,0x18d3a5a58a34e969634d30,0x1a69a29a69a690,0x820820820821ac9412341aa1248d0506b2492],
[0x1249c38492491,0x638e3658d963468d3658d9630,0x694d3c78d34d30,0x20820821aa086bc3849c24e1271e3270938492],
[0x49c24938492491,0x820820820849c24938492491,0x1a69a69a690,0x20820821aa086b71e125048d06b71e1248d0506b71e125c78492],
[0x71c3870e1271e5e5e5e5e5e5853c3870e1c3849c3849c711,0x71b9e3c745c78d1b3a34f1f1e971f1e3c78f1b9e32565a5258f2e54d1b3a34f1b9e30,0x218a18e3c58a0820863e18e38e34,0x82082084a820825410412e2d26482082084a81020950950412cb6],
[0x93893434343438938492491,0x71e3c7c78d963a5a5a5a58d3479534f1e30,0x1a69a48e9a48e9a690,0x10410410410438494141af092828282835938d46a3c24938492],
[0x12686871268687121e121a1e1c487848687871c38492491,0x1a29e392e3c7453c725c7899c97919e26725e4678f2e54e8a74530,0x165a48e965a48e92363a48d8e9c78d365a59690,0x820820820820990413208209904132082082040826408104c8104c8209904d5],
[0x686868406871210909c49829e12491,0x18f9796345e7a5e78e3e58d1a68f2a68f2a68d30,0x3491d3c74d3c6c74e34e90,0x82082086bc384941414141aa084971b86b75e1271e3271e325d78492],
[0x38e3c913c9111111130a7849c711,0x18f9e365e58f1d15171e38f1e34795365e58f9e30,0x208208213e38a08218d8e18cf4,0x410410410410410412a08209693241041095cf24104a8209504b6],
[0x1010101c5848485871c38491,0x839e0821871f1e18386722743953239e11,0x208218628e34,0x106b2208386b40e141af5929b5a8f0915e3c64a8f091ac92],
[0x11,0x208608608608618269e18611,0x208208208a34,0x20875910d50eb221af0e122aaf0e127593ac92],
[0x203890b0b0e38491,0x79596345458e38e96347953e5658e30,0x208208608218e34,0x2082086262614141aa1221ad06bc78c989898492],
[0xd0e24343438e38491,0x79e3e58d3e58f1d163e5a58d1e54d30,0xd2c74d29b1d2c6c74e34e90,0x410b0d504346835424438c96743afaca2eb870e1271e32492],
[0x1216161c48585871216161c48585871c3849c38491,0x21e4e787939e1e4e787939e127cb87cb849f2e1f2e12491,0x21e58f963e58f9638e34,0x21270b86bc2e1ac9c2e1af0b86b216bc4b5e3216bc4b5e32492],
[0x2038e1c29c14c91,0x3453c7c78e3e5a58e3c5c78d1a74530,0x208208608638e34,0x10410438494141aa1253506b271e3271938492],
[0x60a78491,0x63a58f2a78b1f2c68d1a79530,0x694d34d8e945a530,0x82086bc3ac9d1e122a8208386a871e3270e327478492],
[0x57d3a74e9af5e4afa74e9d35ebc95f4e9d3a6bd792be9d3a74d7af257d3a74e9af5e4afa74e9d35ebc91,0x63252525258c949494963252525258c949494963252525258c9494949638e30,0x28a28a28a28a28a68a29a28a68a29a28a68a29a291,0x2082082082084082081020990410204132082040826410408104c8208102099041020413210415],
[0xc14c91,0x29d2c74b1d2c7cb1e54d30,0x694a8e8a3a58e94e90,0x1042443475435f54387092dbd70415e3c24e32492],
[0x11,0x49634c963ca9a79530,0xa3a534d34d30,0x821afaa1221a1aa0870915f5f5c15938492],
[0x12121c4848716121a161c58486858711,0x1c78f1e971e3c78f1e971e3c58d963658f163c78f1e30,0x8628628208638a14,0x2082084c82099041099041320840870b865c2e192102134d5],
[0x71c70938491,0x820820879e1e7849c24e12491,0x208208218e38e34,0x82082084941ac941ac9c6a3c24e351e12492],
[0x343438d0d0e38491,0x71f963c7c78d38f963cb9534f1f9630,0x8218208208238c8e14,0x821c38494141aa1221aa082b41af1e3249c38492],
[0x38491,0x18e3658f2a68a8b1e54e30,0x69a534e94e90,0x10410910d50432189af0915e3c24e12492],
[0x3849c491,0x31a68a8b1c74b1a34d30,0x19e9a68e94e90,0x4104104359282835424e1c24e32492],
[0x38491,0x6963658e963e58f96347953658f9630,0x8208208238e14,0x435f542ebc244347542ebc2443848afafae1c784975e125d78492],
[0x11,0x1e58e3e58d9638d963e58f9630,0x14e94d3a534d30,0x875e1221aa1c3ac8aa0871910d7d7d70438c9c3ac9d78492],
[0x38808080e38491,0x1e78d3e58f1e9634d1e54d30,0x694d8e8a3a5345a530,0x2082121ac92341aa0850386a848af1e32492],
[0x491,0xc71b2c69a34d30,0x674d3a530,0x82082086b221c24915e12492],
[0x121a1a1c68487161a161c70e14e0a78491,0x41093271f9f1e1a5e7820879f16165c5e7872e54e9924c91,0x8218e2821c58e3c58e34,0x149ebebeb4992bc5c54de5c5aab49c74992b4d4daaaad27afafad2650],
[0x48484071212101c64c94e9afc3857d35e4d35f870afa6bc9932531,0x63252525258c949494963252525258c94949632525258e3252525258e30,0x123a48e92323a48c8c8e9232323a692323a690,0x820820820820820810209904102041320820990410204132082040826410810413415],
[0x64c94c8404871210121c69afc3857afa64d35f870af5f4c9932531,0x49494949638c949494963252525258c94949632525258e38c9494949630,0x12323a6923a48e9232323a48c8c8e9a48c8e90,0x820820820826410410810410204132082040826410408104c820810209904108104d5],
[0x487121c69d3269e15ebf0d35e4d3c2bd7e1a6bc9a74c91,0x4963258e365658e325a5a58c969696365658e30,0x48e923a48c8e9a48c8c8e9232323a48c8e90,0x20820821a3920821a392082082084c82102081020990408104c84d5],
[0xd324071c71c3870e1c3870934c91,0xe5468d38c949632525258c9494963a5a58e2e5468d30,0x123a69a69a48c8e9a48e90,0x8208208208209908104104c820810209904102041320810209904108104d5],
[0x487121c69d3269afc3857afa64d35f870af5f4c9a74c91,0x63258c96365658c969696325a5a58e38d959630,0x48e923a48c8e9232323a48c8c8e9a48c8e90,0x20820820820820868e4821a392084c82040826410204132082104d5],
[0xe38e2bd8b1a74d7af257b1634e9af5e4af62c69d35ebc91,0x49496325258c949638c9496325258c949638e30,0x12323a48c8e92323a48c8e92323a48c8e90,0x29a9a9a9b5a6a6a6a6d69a9a9a9b5a4ad495a92b50aaaad256a4ad495a8a4ad495a92b510],
[0x80e38e34c9c3870e1c3870934c91,0x125258c94949632525258d172a34e969638d172a34e30,0x1a69a48e92323a6923a690,0x820820820820820826410408104c820810209904104c81020990810413415],
[0xe29e11111108d1111130e12711,0x1258d9638e3a58e325258c9630,0x6923a69a48e9a690,0x104246c35410432189ac8821adb7afae0820849616361ac8d86b2],
[0x1271c40484848484071c711,0x18c9496325258a38c9496325258e30,0x1a69a29a69a690,0x820820820820821ad848d86b612361aa125848d86b612361ac92],
[0xa78e111111111108d130e12711,0x1658e38c963a58e325258c9630,0x48e9a6923a69a690,0x10410410c8626a848821aa12361adb7afae0849616361ac8d86b2],
[0xe2480e20242438e12711,0x494963658e325258e969638f2a34c949630,0x69a69a48e923a690,0x4104104132082086064821020820990408104c8208208209904d5],
[0x1c71248484040484871c711,0x125258c949638e28e325258c949630,0x1a69a68a69a690,0x820821612361ad848d86b22086a820820849612361ad848d86b2],
[0xe2038924202438e12711,0x49496325258d963a5a58e3479538c949630,0x69a6923a48e9a690,0x4104104104c82082082082099043032408104c8208209908104d5],
[0xe38a511111111108d130e12711,0x1258e3658e9638c949638c9630,0x69a48e923a69a690,0x104104246c35410435410c8626beb6deb82125858d86b248d86b2],
[0xe24e242438e12711,0x494963658e325258e969638f2a34c949630,0x1a69a6923a6923a690,0x10410410413208218192084082082641020413208208210209904d5],
[0xe389242438e12711,0x49496325258d963a5a58e34795325258e30,0x1a69a48e9a48e9a690,0x104104104104104104c820826410c0c902041320840820990413415],
[0x93880e20242438e12711,0x59638c9496325258e969638f2a34c949630,0x69a6923a6923a690,0x410410410c0c904104104c82082641020413208208210209904d5],
[0x1c71c711,0x638d9638e969638d9630,0x1a69a69a690,0x82082082086b23adc7848849c38c925c78492],
[0x3880e2438e12711,0x638d95963a5a58e9638f2a34d959630,0x1a69a48e923a690,0x20821ac88706b250506a8506a849c78c9c1ac92],
[0x38e38e12711,0x59638e963658e3a5a58d9630,0x69a69a69a690,0x8208208486a86bebe7cb8212361aa1271e1248d86b2],
[0x12712712491,0x1658e96963658e969638d963658e30,0x1a69a69a69a690,0x820820820821c24a0a0d78494141ac9c24e12492],
[0x38e2438e12711,0x595963a5a58e3a58e3479538d959630,0x69a6923a48e9a690,0x820820848586b4141aa084941ac9c78c9248586b2],
[0x1249271c491,0x18d38e28e3a5a58d30,0x1a69a68a69a690,0x10410e1249221aa0820821271e12492],
[0x38e38e12711,0x59638d963a58e969638d9630,0x69a69a69a690,0x820848d86a821aa08486bcbebe7821c38c9248d86b2],
[0x1c71c711,0x18e38e38e30,0x1a69a69a690,0x2082163aa0821aa163afafae0858eb258eb2],
[0x38e12711,0x63258d9638c94963258e30,0x69a53a690,0x410410410950425410410950409324104a84b6],
[0x1c71c711,0x63658e38e3a5a58d9630,0x1a69a69a690,0x820848eb71e1248821aa0821271e125c78492],
[0x124071240712491,0x5963a5a58d963a5a58d9638d9630,0x69a69a69a690,0x82121aa08214141aa121ad0506a8486b2486b2],
[0x3880e2438e12711,0x595963a5a58e3a58e34795365658e30,0x1a69a48e923a690,0x208706b220850506a821ad06b271e32706b2492],
[0x38e38e12711,0x5963658e38e963a5a58d9630,0x69a69a69a690,0x8212361aa08486b221afaf2f9e0820871e1248d86b2],
[0x38e2438e12711,0x5959638e3a5a58e9638f2a34d959630,0x69a69a48e923a690,0x8212161aa0849250506a8506a821271e3248586b2],
[0x1249c49c491,0x18e28d38e969634e30,0x1a68a69a69a690,0x10410410410435e1221249c38c92492],
[0x1249c712491,0x1658d9638e96963a5a58e3658d9630,0x1a69a69a69a690,0x820870938492214141aa14141aa0821270938492],
[0x1c71c711,0x18e38e38e30,0x1a69a69a690,0x2163aa0858eb22086bebeb82082163ad8eb2],
[0x1c71c711,0x638e3658e3a5a58d9630,0x1a69a69a690,0x820848eb22086a85c7848821271e125c78492],
[0x38e2438e12711,0x638d95963a5a58e9638f2a34d959630,0x69a6923a6923a690,0x820821248848586b4141aa141aa1271e3248586b2],
[0x124901c40712491,0x5963658e3a5a58e96963658d9630,0x69a69a69a690,0x8486a8486b2214141aa14141aa082121ac86b2],
[0x38e12711,0x59638e3258e325258c9630,0x53a69a690,0x41041041095041042541094932410410412cb6],
[0x1c71c2222227c60888889f18711,0x4963258e38d959632545458c951516365658e30,0x28a28a28a28a28a28a28a69a291,0x2082084a82084a82082082084b8b962e484b6],
[0x1c711,0x18e38d9638d9630,0x1a69a53a530,0x820821aa086baa087591091543ac92],
[0x1c71c711,0x18e38e38e38e30,0x1a69a69a69a690,0x8208210210208264104c820990413208210415],
[0x1c711,0x1258c9638e30,0x14d3a690,0x208208686a821a1aebaa082aaa12],
[0x1c711,0x18e38d9638d9630,0x1a69a53a530,0x820820821aebaa087591541093ac92],
[0x1c71c711,0x18e38e38e38e30,0x1a69a69a69a690,0x820820820820826413209904c8210210210415],
[0x1c711,0x18e3658e3658e30,0x69a694e90,0x821aea820821c24915eb26b2],
[0x1c711,0x1258e38e30,0x69a690,0x208208486bae86a820aeb2],
[0x1249c491,0x18e28e38e38e30,0x1a68a69a69a690,0x2082082082086bc24424938492492],
[0x711,0x638e3658e345458d9630,0x1a69a690,0x20848eb22086a870910938f0938492],
[0x1c711,0x18e38e38e30,0x69a690,0x35410410d50424424eb26b2],
[0x1c711,0x18e3658e3658e30,0x1a694e90,0x6a821aa0835915424eb26b2],
[0x1c711,0x18e3658e3658e30,0x69a694e90,0x86a821aa0870915424eb26b2],
[0x711,0x638e3658d15163658e30,0x1a69a690,0x2082086a82123ac9c24e3c24e12492],
[0x1c711,0x18e38e38e30,0x69a69a690,0x2086a821aa1d64424d7ac92],
[0x1c711,0x18e38e38e30,0x69a69a690,0x2086bd64910435410d7ac92],
[0x38e38491,0x10410435d2d2c10430b0e126b1,0x69a48e923a690,0x8208208208213209904264104c84d5],
[0x1c6bc711,0x18e38e38e38e30,0x1a69a69a690,0x4104109904104324132082084104d5],
[0x1c6bc711,0x18e38e38e38e30,0x1a69a69a690,0x4109904104204324104c82082104d5],
[0x1c711,0x18e38e38e30,0x69a69a690,0x2082082086baf593593ac92],
[0x1c711,0x18e3658e3658e30,0x69a694e90,0x820821aea821c24564eb26b2],
[0x38e38491,0x10410435d2d2c10c2c10e126b1,0x69a48e923a690,0x8208208208213209909904104134d5],
[0x71c71c711,0x1258c9638c9516325458d959630,0x8638a08638e34,0x868eba3aa084942e1ad0b86bc38492],
[0x71c711,0x638e3458d9630,0x6923a48e90,0x2082086baa084943af0eb2],
[0x1c711,0x18e3658e3658e30,0x1a694e90,0x21aa1aa0835910915eb26b2],
[0x1249c491,0x18e38e28e38e30,0x1a69a68a69a690,0x20821c24924435410410424e12492],
[0x1c711,0x18e38e38e30,0x69a690,0x10410435d50424424eb26b2],
[0x1af1c711,0x18e38e38e38e30,0x1a69a69a690,0x410410410c909904132082084104d5],
[0x12491,0x18c963258e30,0x1a534e90,0x1aa1a1aa1a1aa0aaa86b2],
[0x1c711,0x18c9638e30,0x69a690,0x21aa08486a8686a82a86b2],
[0x12491,0x18c963258e30,0x1a534e90,0x821ae86ba1aa082aaeb2],
[0x1c711,0x18e38e30,0x1a690,0x8208219a0867aeb2],
[0x11,0x18e38e30,0x1a690,0x21aa0821221ac92],
[0x18e30,0x18e38e38e30,0x1a638e9a690,0x20821aa1aea82084926b2],
[0x11,0x18e38e38e30,0x1a69a690,0x2122121ac886beb82082121ac92],
[0x11,0x18e38e30,0x69a690,0x10435d50410e326b2],
[0x11,0x638e30,0x1a690,0x20820867aeb2],
[0x11,0x63658e38d9630,0x69a690,0x1aa0d64550d50d5ac92],
[0x11,0x638e3658e30,0x69a694e90,0x19aaaf16b9eaaab0],
[0x11,0x638e38e30,0x69a690,0x21aa0821249aeb2],
[0x11,0x1258e38e30,0x69a690,0x208486b2686a820ac92],
[0x11,0x638e3658e30,0x1a694e90,0x35435410564e326b2],
[0x11,0x638e30,0x69a690,0x82086baa0aeb2],
[0x11,0x634d30,0x690,0x82086baa1220ac92],
[0x11,0x18d9638e38d9630,0x1a69a690,0x848870915435424938492],
[0x11,0x18c963258e30,0x208a34,0xaaaae79d4a942b0],
[0x11,0x1658e38e38d9630,0x1a69a690,0x820821c24564d64938492],
[0x18e30,0x18e38e38e30,0x18e3a69a690,0x20820821aea86a84926b2],
[0x11,0x18c9638e30,0x69a690,0x488486a8686a82a8492],
[0x11,0x638e30,0x69a690,0x82086baa0aeb2],
[0x11,0x638e38e30,0x8208214,0x196aaab96aaab0],
[0x11,0x18c963258e30,0x208a34,0xaaaae752a50ae70],
[0x11,0x638d38d30,0x19e90,0x20849aa0821248ac92],
[0x11,0x18e38e30,0x69a690,0x35410d50410e326b2],
[0x10,0x18e38a28e38e30,0x1a69a638e9a690,0x8208492488208208208492492],
[0x11,0x18e38e38e30,0x1a69a690,0x21221aa1c24424e32492],
[0x11,0x638e38e30,0x8208214,0x1ae4aabaaaae50],
[0x11,0x59638e38d9630,0x69a690,0x835910415d75d5ac92],
[0x11,0x18e38e38e30,0x1a69a690,0x20821221aa121afae08492486b2],
[0x11,0x1658e38e38d9630,0x1a69a690,0x870924915435410938492],
[0x11,0x638e38e38e30,0x69a69a690,0x821c24924435410424938492],
[0x11,0x638e3658e30,0x69a694e90,0x19aaaf16baaaae70],
[0x11,0x638e30,0x1a690,0x20820867aeb2],
[0x11,0x18e38e38e30,0x1a69a690,0x2082086bc24924e32492],
[0x11,0x18e38e38e30,0x1a69a690,0x20848821aa121afae08486b2492],
[0x11,0x634d30,0x690,0x86a84882086aac92],
[0x11,0x638e38e38e30,0x69a69a690,0x82082086bc24424924938492],
[0x10,0x8a38e38e38e30,0x18e3a69a69a690,0x8208208208208212492492492],
[0x11,0x18e38e38e30,0x1a69a690,0x2086a821c24924e32492],
[0x11,0x638e3658e30,0x1a694e90,0x10d75410915e326b2],
[0x11,0x638d38d30,0x19e90,0x2082086b22122b2492],
[0x11,0x18e38e30,0x1a690,0x2082084886bac92],
[0x11,0x638e3658e30,0x1a694e90,0x10d75410564e326b2],
[0x11,0x634e38d30,0x1a670,0x20849249aa0820ac92],
[0x11,0x18e38e38e30,0x1a69a690,0x2082121aa1afae084884921ac92],
[0x11,0x638e38e30,0x69a690,0x2082086b249aeb2],
[0x11,0x638e38e30,0x69a690,0x2082084926baeb2],
[0x11,0x638e38e38e30,0x69a69a690,0x82124886a870910424938492],
[0x18e30,0x18e38e38e30,0x1a698e3a690,0x2086a82126baa082126b2],
[0x0,0x18e38e38e30,0x18e9a630,0x1c5c5aebc7c7979796b0],
[0x0,0x18e38e38e30,0x63a630,0x6a86a821249aeb2],
[0x0,0x18e38e38e30,0x18e9a630,0x1c7c796bc5c5af9796b0],
[0x0,0x18e38e38e30,0x18e9a630,0x1c7c7971716baf9796b0],
[0x0,0x8e38e38e38a30,0x28a291,0x79796be5e5af9796b0],
[0x0,0x18e28a38e30,0x19659651,0x19650],
[0x0,0x8e38e38e38a30,0x28a291,0x79796be5e5af9796b0],
[0x0,0x18e38e28e30,0x8208214,0x71f1e5c5c5af1716b0],
[0x0,0x8a28a28a28a30,0x11,0x10],
[0x0,0x18e28a38e30,0x19659651,0x19650],
[0x0,0x18e38e38e30,0x63a630,0x6a82086b249aeb2],
[0x0,0x18e28a38e30,0x19659651,0x19650],
[0x0,0x18e38e38e30,0x18e9a630,0x1af1716bc7c7979796b0],
[0x0,0x8a28a28a28a30,0x11,0x10],
[0x0,0x18e38e28e30,0x8208214,0x71716bc5c5af1f1e50],
[0x0,0x18e38e28e30,0x8208214,0x71f1e5c5c5af1716b0],
[0x0,0x18e38e38e30,0x63a630,0x6a86a848849aeb2],
[0x0,0x18e38e38e30,0x18e9a630,0x1c7c796be5e5af1716b0],
[0x0,0x18e38a38e38a30,0x28a291,0x79796be5e5af9796b0],
[0x0,0x8211,0x0,0x6aaab0],
[0x0,0x638e30,0x0,0x1ae5aab0],
[0x0,0x410412,0x0,0x10],
[0x0,0x18e38e30,0x0,0x1aeb0],
[0x0,0x8211,0x0,0x2aaeb0],
[0x0,0x638e30,0x0,0x6aaeb0],
[0x0,0x18a38e30,0x0,0x650],
[0x0,0x18e28e30,0x0,0x650],
[0x0,0x638e30,0x0,0x6baab0],
[0x0,0x18e38e30,0x0,0x1aeb0],
[0x0,0x638e30,0x0,0x1ae4aeb0],
[0x0,0x638e30,0x0,0x6baab0],
[0x0,0x8211,0x0,0x1aebaeb0],
[0x0,0x8211,0x0,0x6aaab0],
[0x0,0x18612,0x0,0x1aeb0],
[0x0,0x638e30,0x0,0x19650],
[0x0,0x18e28e30,0x0,0x650],
[0x0,0x638e30,0x0,0xae5aeb0],
[0x0,0x410412,0x0,0x10],
[0x0,0x8211,0x0,0x1aebaeb0],
[0x0,0x638e30,0x0,0x2baeb0],
[0x0,0x18e38e30,0x0,0x1aeb0],
[0x0,0x638e30,0x0,0x1aab96b0],
[0x0,0x18612,0x0,0x1aeb0],
[0x0,0x18e38e30,0x0,0x1aeb0],
[0x0,0x18612,0x0,0x1aeb0],
[0x0,0x18e28e30,0x0,0x650],
[0x0,0x18e28e30,0x0,0x650],
[0x0,0x410412,0x0,0x10],
[0x0,0x638e30,0x0,0x19650],
[0x0,0x18612,0x0,0x1aeb0],
[0x0,0x638e30,0x0,0x19650],
[0x0,0x638e30,0x0,0x6aaeb0],
[0x0,0x638e30,0x0,0x192baeb0],
[0x0,0x638e30,0x10,0x8208672492],
[0x0,0x638e3458e30,0x1a530,0x19abc5aeaae70],
[0x0,0x208208411,0x690,0x1af16aaf16be5aab0],
[0x0,0x208211,0x10,0x208212492492],
[0x0,0x18d1630,0x670,0x2b9d2659e70],
[0x0,0x638e30,0x690,0x20820ae1ae12],
[0x0,0x9a78611,0x13,0x66aab9e70],
[0x0,0x8208611,0x690,0x65aaaae5aab0],
[0x0,0x18e30,0x10,0x82086722b2],
[0x0,0x638e3458e30,0x1a530,0x19abc5ae7aab0],
[0x0,0x208211,0x10,0x212208492492],
[0x0,0x8208611,0x690,0x6b92baaaae50],
[0x0,0x638e30,0x10,0x8208672492],
[0x0,0x208208411,0x690,0x1e5aabaf16aaf16b0],
[0x0,0x208208411,0x690,0xaf96baf16bc5aab0],
[0x0,0x208208411,0x690,0x1af16be5aaaaf16b0],
[0x0,0x10,0x0,0xaaaaab0],
[0x0,0x10,0x0,0xaaaaab0],
[0x0,0x10,0x0,0x8208208212492],
[0x0,0x10,0x0,0x8208208212492],
[0x0,0x10,0x0,0xaab2],
[0x0,0x10,0x0,0xaab2],
[0x0,0x10,0x0,0x8212],
[0x0,0x10,0x0,0x82b2],
[0x0,0x10,0x0,0x82b2],
[0x0,0x10,0x0,0x8212208208492],
[0x0,0x10,0x0,0xe3938e4e3938e50],
[0x0,0x10,0x0,0x2a82b2],
[0x0,0x10,0x0,0x208212],
[0x0,0x10,0x0,0xe3938e4e3938e50],
[0x0,0x10,0x0,0x219ab2],
[0x0,0x10,0x0,0x2a82b2],
[0x0,0x10,0x0,0x219ab2],
[0x0,0x10,0x0,0x82b2],
[0x0,0x10,0x0,0xe3938e4e3938e50],
[0x0,0x10,0x0,0x8212],
[0x0,0x10,0x0,0x208212],
[0x0,0x0,0x0,0x1aeb0],
[0x0,0x0,0x0,0x650],
[0x0,0x0,0x0,0x1aeb0],
[0x0,0x0,0x0,0x650],
[0x0,0x0,0x0,0x1aeb0],
[0x0,0x0,0x0,0x196b0],
[0x0,0x0,0x0,0x6b0],
[0x0,0x0,0x0,0x19650],
[0x0,0x0,0x0,0x196b0],
[0x0,0x0,0x0,0x650],
[0x0,0x0,0x0,0x1aeb0],
[0x0,0x0,0x0,0x650],
[0x0,0x0,0x0,0x10],
[0x0,0x0,0x0,0x650],
[0x0,0x0,0x0,0x1ae50],
[0x0,0x0,0x0,0x650],
[0x0,0x0,0x0,0x1ae50],
[0x0,0x0,0x0,0x650],
[0x0,0x0,0x0,0x1aeb0],
[0x0,0x0,0x0,0x6b0],
[0x0,0x0,0x0,0x1aeb0],
[0x0,0x0,0x0,0x10],
[0x0,0x0,0x0,0x19650],
[0x0,0x0,0x0,0x1aeb0],
[0x0,0x0,0x0,0x1ae50],
[0x0,0x0,0x0,0x650],
[0x0,0x0,0x0,0x650],
[0x0,0x0,0x0,0x650],
[0x0,0x0,0x0,0x6b0],
[0x0,0x0,0x0,0x19650],
[0x0,0x0,0x0,0x10],
[0x0,0x0,0x0,0x1aeb0],
[0x0,0x0,0x0,0x650],
[0x0,0x0,0x0,0x1aeb0],
[0x0,0x0,0x0,0x10],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x10,0x18e30,0x18e30,0x20820821aea8208212],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x18e30,0x18e30,0x21aa082086b2],
[0x0,0x18e30,0x18e30,0x6a82082086b2],
[0x0,0x18e30,0x18e30,0x20820821aeb2],
[0x0,0x18e30,0x0,0x64ae5aab0],
[0x0,0x630,0x0,0x8208672],
[0x0,0x18e30,0x0,0x65aaaae50],
[0x0,0x630,0x0,0x8668212],
[0x0,0x18e30,0x0,0x64ae5aab0],
[0x0,0x18e30,0x0,0x2b96aae50],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x10,0x0,0x10],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x10,0x0,0x10],
[0x0,0x0,0x0,0x10],
[0x0,0x0,0x0,0x11],
[0x0,0x0,0x0,0x10],
[0x0,0x0,0x0,0x10],
[0x0,0x0,0x0,0x10],
[0x0,0x0,0x0,0x11],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0],
[0x0,0x0,0x0,0x0]
]

def selectedHint (i : Nat) (k : Fin 4) := selectiveBank[i]!.getD k.val 0

def selectedFamily (i : Nat) : Bool :=
  let E := representativeMasks[i]!
  if pop E < 15 then true else
    let pool := base (unionPool seedBank5[i]!) E
    let cs := Packed.spectrum pool
    let ones := Packed.fill pool 1
    (List.finRange 4).all fun k => decide (pop E<pop (live k)) ||
      (Packed.selectedSearch k pool cs ones 10 [startPiece k E] [] (selectedHint i k)).isSome

theorem selected_terminal (i : Nat) (hi : i<782) (numeric : selectedFamily i=true) :
    TerminalCheck (candidates seedBank5[i]!) := by
  let g := seedBank5[i]!
  let E := representativeMasks[i]!
  by_cases small : pop E<15
  · intro k p mem
    have mins : ∀ k : Fin 4, 15≤pop (live k) := by decide
    exact terminal_short k E _ (compressed_candidates i hi) (Nat.lt_of_lt_of_le small (mins k)) p mem
  · have full : Complete (unionPool g) E :=
      complete_of_subset (fun _ h => mem_unionPool.mp h) (every_terminal_complete i hi)
    simp only [selectedFamily,show ¬pop representativeMasks[i]!<15 from small,ite_false] at numeric
    intro k p mem
    have inside (v : Vertex) : p v∈unionPool g := mem_unionPool.mpr (mem_candidates.mp (mem v))
    rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp numeric k (by simp)) with easy|hard
    · exact terminal_short k E _ full (of_decide_eq_true easy) p inside
    · exact Packed.selectedCheck_sound k E _ full (selectedHint i k) hard p inside

end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch000 : (List.range' 0 1).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch001 : (List.range' 1 1).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch002 : (List.range' 2 1).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch003 : (List.range' 3 2).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch005 : (List.range' 5 2).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch007 : (List.range' 7 2).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch009 : (List.range' 9 2).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch011 : (List.range' 11 2).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch013 : (List.range' 13 2).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch015 : (List.range' 15 3).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch018 : (List.range' 18 3).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch021 : (List.range' 21 3).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch024 : (List.range' 24 3).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch027 : (List.range' 27 4).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch031 : (List.range' 31 4).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch035 : (List.range' 35 4).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch039 : (List.range' 39 4).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch043 : (List.range' 43 5).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch048 : (List.range' 48 5).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch053 : (List.range' 53 5).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch058 : (List.range' 58 5).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch063 : (List.range' 63 5).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch068 : (List.range' 68 4).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part072 : (List.range' 72 2).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part074 : (List.range' 74 2).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part076 : (List.range' 76 2).all selectedFamily = true := by decide +kernel
theorem batch072 : (List.range' 72 6).all selectedFamily = true := by
  change (List.range' 72 2 ++ List.range' 74 2 ++ List.range' 76 2).all selectedFamily = true
  simp only [List.all_append, part072, part074, part076, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part078 : (List.range' 78 2).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part080 : (List.range' 80 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part083 : (List.range' 83 2).all selectedFamily = true := by decide +kernel
theorem batch078 : (List.range' 78 7).all selectedFamily = true := by
  change (List.range' 78 2 ++ List.range' 80 3 ++ List.range' 83 2).all selectedFamily = true
  simp only [List.all_append, part078, part080, part083, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part085 : (List.range' 85 2).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part087 : (List.range' 87 2).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part089 : (List.range' 89 2).all selectedFamily = true := by decide +kernel
theorem batch085 : (List.range' 85 6).all selectedFamily = true := by
  change (List.range' 85 2 ++ List.range' 87 2 ++ List.range' 89 2).all selectedFamily = true
  simp only [List.all_append, part085, part087, part089, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part091 : (List.range' 91 2).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part093 : (List.range' 93 2).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part095 : (List.range' 95 2).all selectedFamily = true := by decide +kernel
theorem batch091 : (List.range' 91 6).all selectedFamily = true := by
  change (List.range' 91 2 ++ List.range' 93 2 ++ List.range' 95 2).all selectedFamily = true
  simp only [List.all_append, part091, part093, part095, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part097 : (List.range' 97 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part100 : (List.range' 100 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part103 : (List.range' 103 3).all selectedFamily = true := by decide +kernel
theorem batch097 : (List.range' 97 9).all selectedFamily = true := by
  change (List.range' 97 3 ++ List.range' 100 3 ++ List.range' 103 3).all selectedFamily = true
  simp only [List.all_append, part097, part100, part103, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part106 : (List.range' 106 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part109 : (List.range' 109 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part112 : (List.range' 112 2).all selectedFamily = true := by decide +kernel
theorem batch106 : (List.range' 106 8).all selectedFamily = true := by
  change (List.range' 106 3 ++ List.range' 109 3 ++ List.range' 112 2).all selectedFamily = true
  simp only [List.all_append, part106, part109, part112, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part114 : (List.range' 114 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part117 : (List.range' 117 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part120 : (List.range' 120 2).all selectedFamily = true := by decide +kernel
theorem batch114 : (List.range' 114 8).all selectedFamily = true := by
  change (List.range' 114 3 ++ List.range' 117 3 ++ List.range' 120 2).all selectedFamily = true
  simp only [List.all_append, part114, part117, part120, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part122 : (List.range' 122 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part125 : (List.range' 125 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part128 : (List.range' 128 2).all selectedFamily = true := by decide +kernel
theorem batch122 : (List.range' 122 8).all selectedFamily = true := by
  change (List.range' 122 3 ++ List.range' 125 3 ++ List.range' 128 2).all selectedFamily = true
  simp only [List.all_append, part122, part125, part128, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part130 : (List.range' 130 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part133 : (List.range' 133 4).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part137 : (List.range' 137 1).all selectedFamily = true := by decide +kernel
theorem batch130 : (List.range' 130 8).all selectedFamily = true := by
  change (List.range' 130 3 ++ List.range' 133 4 ++ List.range' 137 1).all selectedFamily = true
  simp only [List.all_append, part130, part133, part137, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part138 : (List.range' 138 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part141 : (List.range' 141 4).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part145 : (List.range' 145 3).all selectedFamily = true := by decide +kernel
theorem batch138 : (List.range' 138 10).all selectedFamily = true := by
  change (List.range' 138 3 ++ List.range' 141 4 ++ List.range' 145 3).all selectedFamily = true
  simp only [List.all_append, part138, part141, part145, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part148 : (List.range' 148 5).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part153 : (List.range' 153 4).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part157 : (List.range' 157 4).all selectedFamily = true := by decide +kernel
theorem batch148 : (List.range' 148 13).all selectedFamily = true := by
  change (List.range' 148 5 ++ List.range' 153 4 ++ List.range' 157 4).all selectedFamily = true
  simp only [List.all_append, part148, part153, part157, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part161 : (List.range' 161 4).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part165 : (List.range' 165 7).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part172 : (List.range' 172 4).all selectedFamily = true := by decide +kernel
theorem batch161 : (List.range' 161 15).all selectedFamily = true := by
  change (List.range' 161 4 ++ List.range' 165 7 ++ List.range' 172 4).all selectedFamily = true
  simp only [List.all_append, part161, part165, part172, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part176 : (List.range' 176 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part179 : (List.range' 179 3).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part182 : (List.range' 182 4).all selectedFamily = true := by decide +kernel
theorem batch176 : (List.range' 176 10).all selectedFamily = true := by
  change (List.range' 176 3 ++ List.range' 179 3 ++ List.range' 182 4).all selectedFamily = true
  simp only [List.all_append, part176, part179, part182, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part186 : (List.range' 186 5).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part191 : (List.range' 191 6).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part197 : (List.range' 197 4).all selectedFamily = true := by decide +kernel
theorem batch186 : (List.range' 186 15).all selectedFamily = true := by
  change (List.range' 186 5 ++ List.range' 191 6 ++ List.range' 197 4).all selectedFamily = true
  simp only [List.all_append, part186, part191, part197, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part201 : (List.range' 201 7).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part208 : (List.range' 208 7).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part215 : (List.range' 215 5).all selectedFamily = true := by decide +kernel
theorem batch201 : (List.range' 201 19).all selectedFamily = true := by
  change (List.range' 201 7 ++ List.range' 208 7 ++ List.range' 215 5).all selectedFamily = true
  simp only [List.all_append, part201, part208, part215, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part220 : (List.range' 220 11).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part231 : (List.range' 231 10).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part241 : (List.range' 241 7).all selectedFamily = true := by decide +kernel
theorem batch220 : (List.range' 220 28).all selectedFamily = true := by
  change (List.range' 220 11 ++ List.range' 231 10 ++ List.range' 241 7).all selectedFamily = true
  simp only [List.all_append, part220, part231, part241, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part248 : (List.range' 248 16).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part264 : (List.range' 264 16).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part280 : (List.range' 280 8).all selectedFamily = true := by decide +kernel
theorem batch248 : (List.range' 248 40).all selectedFamily = true := by
  change (List.range' 248 16 ++ List.range' 264 16 ++ List.range' 280 8).all selectedFamily = true
  simp only [List.all_append, part248, part264, part280, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part288 : (List.range' 288 18).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part306 : (List.range' 306 30).all selectedFamily = true := by decide +kernel
theorem batch288 : (List.range' 288 48).all selectedFamily = true := by
  change (List.range' 288 18 ++ List.range' 306 30).all selectedFamily = true
  simp only [List.all_append, part288, part306, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part336 : (List.range' 336 40).all selectedFamily = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem part376 : (List.range' 376 8).all selectedFamily = true := by decide +kernel
theorem batch336 : (List.range' 336 48).all selectedFamily = true := by
  change (List.range' 336 40 ++ List.range' 376 8).all selectedFamily = true
  simp only [List.all_append, part336, part376, Bool.true_and]
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch384 : (List.range' 384 48).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch432 : (List.range' 432 48).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch480 : (List.range' 480 48).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch528 : (List.range' 528 48).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch576 : (List.range' 576 48).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch624 : (List.range' 624 48).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch672 : (List.range' 672 48).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch720 : (List.range' 720 48).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem batch768 : (List.range' 768 14).all selectedFamily = true := by decide +kernel
end PEqualNP.Outside.L_meta_17134_aux.CSP

namespace PEqualNP.Outside.L_meta_17134_aux.CSP

theorem every_selected (i : Nat) (hi : i<782) : selectedFamily i=true := by
  by_cases below_85 : i < 85
  ·
    by_cases below_24 : i < 24
    ·
      by_cases below_9 : i < 9
      ·
        by_cases below_3 : i < 3
        ·
          by_cases below_1 : i < 1
          ·
            exact List.all_eq_true.mp batch000 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_2 : i < 2
            ·
              exact List.all_eq_true.mp batch001 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch002 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
        ·
          by_cases below_5 : i < 5
          ·
            exact List.all_eq_true.mp batch003 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_7 : i < 7
            ·
              exact List.all_eq_true.mp batch005 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch007 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
      ·
        by_cases below_15 : i < 15
        ·
          by_cases below_11 : i < 11
          ·
            exact List.all_eq_true.mp batch009 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_13 : i < 13
            ·
              exact List.all_eq_true.mp batch011 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch013 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
        ·
          by_cases below_18 : i < 18
          ·
            exact List.all_eq_true.mp batch015 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_21 : i < 21
            ·
              exact List.all_eq_true.mp batch018 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch021 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
    ·
      by_cases below_48 : i < 48
      ·
        by_cases below_35 : i < 35
        ·
          by_cases below_27 : i < 27
          ·
            exact List.all_eq_true.mp batch024 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_31 : i < 31
            ·
              exact List.all_eq_true.mp batch027 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch031 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
        ·
          by_cases below_39 : i < 39
          ·
            exact List.all_eq_true.mp batch035 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_43 : i < 43
            ·
              exact List.all_eq_true.mp batch039 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch043 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
      ·
        by_cases below_63 : i < 63
        ·
          by_cases below_53 : i < 53
          ·
            exact List.all_eq_true.mp batch048 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_58 : i < 58
            ·
              exact List.all_eq_true.mp batch053 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch058 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
        ·
          by_cases below_72 : i < 72
          ·
            by_cases below_68 : i < 68
            ·
              exact List.all_eq_true.mp batch063 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch068 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_78 : i < 78
            ·
              exact List.all_eq_true.mp batch072 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch078 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
  ·
    by_cases below_220 : i < 220
    ·
      by_cases below_130 : i < 130
      ·
        by_cases below_106 : i < 106
        ·
          by_cases below_91 : i < 91
          ·
            exact List.all_eq_true.mp batch085 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_97 : i < 97
            ·
              exact List.all_eq_true.mp batch091 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch097 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
        ·
          by_cases below_114 : i < 114
          ·
            exact List.all_eq_true.mp batch106 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_122 : i < 122
            ·
              exact List.all_eq_true.mp batch114 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch122 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
      ·
        by_cases below_161 : i < 161
        ·
          by_cases below_138 : i < 138
          ·
            exact List.all_eq_true.mp batch130 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_148 : i < 148
            ·
              exact List.all_eq_true.mp batch138 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch148 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
        ·
          by_cases below_186 : i < 186
          ·
            by_cases below_176 : i < 176
            ·
              exact List.all_eq_true.mp batch161 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch176 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_201 : i < 201
            ·
              exact List.all_eq_true.mp batch186 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch201 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
    ·
      by_cases below_480 : i < 480
      ·
        by_cases below_336 : i < 336
        ·
          by_cases below_248 : i < 248
          ·
            exact List.all_eq_true.mp batch220 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_288 : i < 288
            ·
              exact List.all_eq_true.mp batch248 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch288 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
        ·
          by_cases below_384 : i < 384
          ·
            exact List.all_eq_true.mp batch336 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_432 : i < 432
            ·
              exact List.all_eq_true.mp batch384 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch432 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
      ·
        by_cases below_624 : i < 624
        ·
          by_cases below_528 : i < 528
          ·
            exact List.all_eq_true.mp batch480 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_576 : i < 576
            ·
              exact List.all_eq_true.mp batch528 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch576 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
        ·
          by_cases below_720 : i < 720
          ·
            by_cases below_672 : i < 672
            ·
              exact List.all_eq_true.mp batch624 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch672 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
          ·
            by_cases below_768 : i < 768
            ·
              exact List.all_eq_true.mp batch720 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)
            ·
              exact List.all_eq_true.mp batch768 i (List.mem_range'_1.mpr ⟨by omega,by omega⟩)

set_option maxRecDepth 65536 in
theorem all_terminals : ∀ g ∈ seedBank5.toList, TerminalCheck (candidates g) := by
  intro g hg
  obtain ⟨i,idx,eq⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hg)
  have size : seedBank5.size=782 := by decide +kernel
  have hi : i<782 := by omega
  simpa [idx,eq] using selected_terminal i hi (every_selected i hi)
end PEqualNP.Outside.L_meta_17134_aux.CSP

open PEqualNP.Outside.L_meta_17134_aux in
theorem PEqualNP.Outside.L_meta_17134 : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x2 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → (6 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.false Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x3.gates := by
  exact posted_from_cover seedBank5.toList candidates concrete_cover CSP.all_terminals
