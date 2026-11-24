import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3102

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 8 → Bool
abbrev F := X → Bool → Bool
abbrev Bank := X → Bool → List Bool
abbrev Pool := F → Prop

def gateOK (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
def good (gs : List Gate) := ∀ g ∈ gs, gateOK g
def plus (s : Pool) (f : F) : Pool := fun h => s h ∨ h = f
def readB (w : Bank) (i : ℕ) : F := fun x b => (w x b).getD i false
def real (n : ℕ) (w : Bank) (f : F) := ∃ i < n, readB w i = f
-- a function of the switched input only; with `u = 0` it is not the negation
def pureU (u : ℕ) (f : F) :=
  ∃ c : Bool → Bool, (∀ x b, f x b = c b) ∧ (u = 0 → c false = true → c true = true)
def low (f : F) : F := fun x _ => f x false
def lowConst (f : F) := ∃ c : Bool, ∀ x, f x false = c
-- the circuit before the switch reads the eight inputs and the given OR wire
def base (p : List Gate) : Bank := fun x b => (Circuit.mk p 0).wires (List.ofFn x ++ [x 1 || b])
-- the circuit of the low restriction reads the eight inputs only
def lbase (l : List Gate) : Bank := fun x _ => (Circuit.mk l 0).wires (List.ofFn x)
def joint (p : List Gate) (i : ℕ) (t : List Gate) : Bank := fun x b =>
  let w := base p x b
  (Circuit.mk t 0).wires (w ++ [if b then true else w.getD i false])
def sz (p : List Gate) := 9 + p.length
def lsz (l : List Gate) := 8 + l.length
def jsz (p t : List Gate) := sz p + 1 + t.length

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem run_ext (gs : List Gate) (w : List Bool) :
    ∃ e, run gs w = w ++ e ∧ e.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [run],rfl⟩
  | cons g gs ih =>
    obtain ⟨e,he,hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: e,?_,by simpa using hl⟩
    change run gs (step w g) = _
    rw [he]
    simp [step,List.append_assoc]
theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨e,he,hl⟩ := run_ext gs w
  simp [he,hl]
theorem base_len (p : List Gate) (x : X) (b : Bool) : (base p x b).length = sz p := by
  change (run p _).length = _
  simp [run_len,sz]
theorem lbase_len (l : List Gate) (x : X) (b : Bool) : (lbase l x b).length = lsz l := by
  change (run l _).length = _
  simp [run_len,lsz]
theorem joint_len (p t : List Gate) (i : ℕ) (x : X) (b : Bool) :
    (joint p i t x b).length = jsz p t := by
  change (run t _).length = _
  simp [run_len,base_len,jsz]
theorem snocGood {p : List Gate} {g : Gate} (h : good p) (hg : gateOK g) : good (p ++ [g]) := by
  intro a ha
  rcases List.mem_append.mp ha with hp | hs
  · exact h _ hp
  · simpa only [List.mem_singleton.mp hs] using hg

def extend (w : Bank) (g : Gate) : Bank := fun x b => step (w x b) g
theorem base_snoc (p : List Gate) (g : Gate) : base (p ++ [g]) = extend (base p) g := by
  funext x b
  simp [base,Circuit.wires,List.foldl_append,extend,step]
theorem lbase_snoc (l : List Gate) (g : Gate) : lbase (l ++ [g]) = extend (lbase l) g := by
  funext x b
  simp [lbase,Circuit.wires,List.foldl_append,extend,step]
theorem joint_snoc (p t : List Gate) (i : ℕ) (g : Gate) :
    joint p i (t ++ [g]) = extend (joint p i t) g := by
  funext x b
  simp [joint,Circuit.wires,List.foldl_append,extend,step]
theorem real_keep {n : ℕ} {w : Bank} {f : F} (len : ∀ x b, (w x b).length = n)
    (g : Gate) (h : real n w f) : real (n+1) (extend w g) f := by
  obtain ⟨i,hi,rfl⟩ := h
  refine ⟨i,by omega,?_⟩
  funext x b
  exact List.getD_append _ _ _ _ (by simpa only [len] using hi)

def builds (n : ℕ) (w : Bank) (f : F) := ∃ g, gateOK g ∧ readB (extend w g) n = f
def neg (a : F) : F := fun x b => !(a x b)
def op (d a b : Bool) := if d then a || b else a && b
def binary (d : Bool) (a b : F) : F := fun x k => op d (a x k) (b x k)
theorem op_comm (d a b : Bool) : op d a b = op d b a := by cases d <;> cases a <;> cases b <;> rfl
theorem bin_comm (d : Bool) (a b : F) : binary d a b = binary d b a := by
  funext x k; exact op_comm _ _ _
theorem op_hot (d a : Bool) : op d d a = d := by cases d <;> cases a <;> rfl
theorem op_cold (d a : Bool) : op d (!d) a = a := by cases d <;> cases a <;> rfl
theorem lastRead {n : ℕ} {w : Bank} (len : ∀ x b, (w x b).length = n) (g : Gate) (x : X) (b : Bool) :
    readB (extend w g) n x b = g.op.eval (g.inputs.map fun i => readB w i x b) := by
  simp only [readB,extend,step]
  rw [List.getD_append_right _ _ _ _ (by simp [len])]
  simp [len]
theorem builds_neg {n : ℕ} {w : Bank} {a : F} (len : ∀ x b, (w x b).length = n)
    (h : real n w a) : builds n w (neg a) := by
  obtain ⟨i,_,rfl⟩ := h
  refine ⟨⟨.not,[i]⟩,by simp [gateOK],?_⟩
  funext x b
  rw [lastRead len]
  rfl
theorem builds_bin {n : ℕ} {w : Bank} {a b : F} (len : ∀ x b, (w x b).length = n)
    (d : Bool) (ha : real n w a) (hb : real n w b) : builds n w (binary d a b) := by
  obtain ⟨i,_,rfl⟩ := ha
  obtain ⟨j,_,rfl⟩ := hb
  cases d
  · refine ⟨⟨.and,[i,j]⟩,by simp [gateOK],?_⟩
    funext x k
    rw [lastRead len]
    simp [GateOp.eval,binary,op]
  · refine ⟨⟨.or,[i,j]⟩,by simp [gateOK],?_⟩
    funext x k
    rw [lastRead len]
    simp [GateOp.eval,binary,op]

def lowReal (l : List Gate) (f : F) := real (lsz l) (lbase l) (low f)
def both (p l : List Gate) (f : F) := real (sz p) (base p) f ∧ lowReal l f
def ahead (u : ℕ) (p l : List Gate) (f : F) := pureU u f ∨ both p l f
def behind (p t l : List Gate) (i : ℕ) (f : F) :=
  lowConst f ∨ (real (jsz p t) (joint p i t) f ∧ lowReal l f)
def restricted (l : List Gate) (f : F) := lowConst f ∨ lowReal l f

def Stage (k : ℕ) (s : Pool) : Prop :=
  (∃ p l u, good p ∧ good l ∧ p.length+u ≤ k ∧ l.length+u ≤ k ∧ ∀ f, s f → ahead u p l f) ∨
  (∃ p t l i, good p ∧ good t ∧ good l ∧
    p.length+t.length+1 ≤ k ∧ l.length+1 ≤ k ∧ ∀ f, s f → behind p t l i f) ∨
  (∃ l, good l ∧ l.length+2 ≤ k ∧ ∀ f, s f → restricted l f)

theorem Stage.before {k : ℕ} {s : Pool} (p l : List Gate) (u : ℕ) (hp : good p) (hl : good l)
    (bud : p.length+u ≤ k) (lb : l.length+u ≤ k) (all : ∀ f, s f → ahead u p l f) : Stage k s :=
  Or.inl ⟨p,l,u,hp,hl,bud,lb,all⟩
theorem Stage.afterSwitch {k : ℕ} {s : Pool} (p t l : List Gate) (i : ℕ)
    (hp : good p) (ht : good t) (hl : good l)
    (bud : p.length+t.length+1 ≤ k) (lb : l.length+1 ≤ k)
    (all : ∀ f, s f → behind p t l i f) : Stage k s :=
  Or.inr (Or.inl ⟨p,t,l,i,hp,ht,hl,bud,lb,all⟩)
theorem Stage.cheap {k : ℕ} {s : Pool} (l : List Gate) (hl : good l) (bud : l.length+2 ≤ k)
    (all : ∀ f, s f → restricted l f) : Stage k s :=
  Or.inr (Or.inr ⟨l,hl,bud,all⟩)

theorem includeMore {s : Pool} {a : F} {P : F → Prop}
    (old : ∀ f, s f → P f) (new : P a) : ∀ f, plus s a f → P f := by
  intro f h
  rcases h with h | rfl
  · exact old f h
  · exact new
theorem keepBase {p : List Gate} {f : F} (g : Gate) (h : real (sz p) (base p) f) :
    real (sz (p ++ [g])) (base (p ++ [g])) f := by
  rw [base_snoc]
  simpa [sz,Nat.add_assoc] using real_keep (base_len p) g h
theorem keepLow {l : List Gate} {f : F} (g : Gate) (h : lowReal l f) : lowReal (l ++ [g]) f := by
  unfold lowReal at h ⊢
  rw [lbase_snoc]
  simpa [lsz,Nat.add_assoc] using real_keep (lbase_len l) g h
theorem keepJoint {p t : List Gate} {i : ℕ} {f : F} (g : Gate)
    (h : real (jsz p t) (joint p i t) f) :
    real (jsz p (t ++ [g])) (joint p i (t ++ [g])) f := by
  rw [joint_snoc]
  simpa [jsz,Nat.add_assoc] using real_keep (joint_len p t i) g h
theorem lastBase {p : List Gate} {g : Gate} {f : F} (h : readB (extend (base p) g) (sz p) = f) :
    real (sz (p ++ [g])) (base (p ++ [g])) f := by
  refine ⟨sz p,by simp [sz],by rwa [base_snoc]⟩
theorem lastLow {l : List Gate} {g : Gate} {f : F}
    (h : readB (extend (lbase l) g) (lsz l) = low f) : lowReal (l ++ [g]) f := by
  refine ⟨lsz l,by simp [lsz],by rwa [lbase_snoc]⟩
theorem lastJoint {p t : List Gate} {i : ℕ} {g : Gate} {f : F}
    (h : readB (extend (joint p i t) g) (jsz p t) = f) :
    real (jsz p (t ++ [g])) (joint p i (t ++ [g])) f := by
  refine ⟨jsz p t,by simp [jsz],by rwa [joint_snoc]⟩

theorem pure_low {u : ℕ} {f : F} (h : pureU u f) : lowConst f := by
  obtain ⟨c,hc,_⟩ := h
  exact ⟨c false,fun x => hc x false⟩
theorem pure_up {u : ℕ} {f : F} (h : pureU u f) : pureU (u+1) f := by
  obtain ⟨c,hc,_⟩ := h
  exact ⟨c,hc,fun e => absurd e (Nat.succ_ne_zero u)⟩
theorem liftJoint {p : List Gate} {f : F} (i : ℕ) (h : real (sz p) (base p) f) :
    real (jsz p []) (joint p i []) f := by
  obtain ⟨j,hj,rfl⟩ := h
  refine ⟨j,by simp [jsz]; omega,?_⟩
  funext x b
  exact List.getD_append _ _ _ _ (by simpa only [base_len] using hj)
theorem switchWire (p : List Gate) (i : ℕ) :
    real (jsz p []) (joint p i [])
      (fun x b => if b then true else readB (base p) i x b) := by
  refine ⟨sz p,by simp [jsz],?_⟩
  funext x b
  change (base p x b ++ [_]).getD (sz p) false = _
  rw [List.getD_append_right _ _ _ _ (by simp [base_len])]
  simp [base_len,readB]

theorem aStay {k u : ℕ} {s : Pool} {f : F} {p l : List Gate}
    (hp : good p) (hl : good l) (bud : p.length+u ≤ k) (lb : l.length+u ≤ k)
    (all : ∀ a, s a → ahead u p l a) (h : ahead u p l f) : Stage (k+1) (plus s f) :=
  .before p l u hp hl (by omega) (by omega) (includeMore all h)

theorem aBuild {k u : ℕ} {s : Pool} {f : F} {p l : List Gate}
    (hp : good p) (hl : good l) (bud : p.length+u ≤ k) (lb : l.length+u ≤ k)
    (all : ∀ a, s a → ahead u p l a)
    (jb : builds (sz p) (base p) f) (cb : builds (lsz l) (lbase l) (low f)) :
    Stage (k+1) (plus s f) := by
  obtain ⟨g,hg,he⟩ := jb
  obtain ⟨q,hq,he'⟩ := cb
  refine .before (p++[g]) (l++[q]) u (snocGood hp hg) (snocGood hl hq)
    (by simp; omega) (by simp; omega)
    (includeMore ?_ (Or.inr ⟨lastBase he,lastLow he'⟩))
  intro a ha
  rcases all a ha with c | ⟨r,r'⟩
  · exact Or.inl c
  · exact Or.inr ⟨keepBase g r,keepLow q r'⟩

theorem aBump {k u : ℕ} {s : Pool} {f : F} {p l : List Gate}
    (hp : good p) (hl : good l) (bud : p.length+u ≤ k) (lb : l.length+u ≤ k)
    (all : ∀ a, s a → ahead u p l a) (h : pureU (u+1) f) : Stage (k+1) (plus s f) := by
  refine .before p l (u+1) hp hl (by omega) (by omega) (includeMore ?_ (Or.inl h))
  intro a ha
  exact (all a ha).imp pure_up id

theorem beginSwitch {k u : ℕ} {s : Pool} {f : F} {p l : List Gate} (i : ℕ)
    (hp : good p) (hl : good l) (bud : p.length+u ≤ k) (lb : l.length+u ≤ k)
    (all : ∀ a, s a → ahead u p l a)
    (new : behind p [] l i f) : Stage (k+1) (plus s f) := by
  refine .afterSwitch p [] l i hp (by intro q h; cases h) hl (by simp; omega) (by omega)
    (includeMore ?_ new)
  intro a ha
  rcases all a ha with h | ⟨h,h'⟩
  · exact Or.inl (pure_low h)
  · exact Or.inr ⟨liftJoint i h,h'⟩

theorem aCheap {k u : ℕ} {s : Pool} {f : F} {p l : List Gate}
    (hl : good l) (lb : l.length+1 ≤ k)
    (all : ∀ a, s a → ahead u p l a) (h : restricted l f) : Stage (k+1) (plus s f) := by
  refine .cheap l hl (by omega) (includeMore ?_ h)
  intro a ha
  rcases all a ha with h | ⟨_,h'⟩
  · exact Or.inl (pure_low h)
  · exact Or.inr h'

theorem afterBuild {k : ℕ} {s : Pool} {f : F} {p t l : List Gate} {i : ℕ}
    (hp : good p) (ht : good t) (hl : good l)
    (bud : p.length + t.length + 1 ≤ k) (lb : l.length + 1 ≤ k)
    (all : ∀ a, s a → behind p t l i a)
    (jb : builds (jsz p t) (joint p i t) f) (cb : builds (lsz l) (lbase l) (low f)) :
    Stage (k+1) (plus s f) := by
  obtain ⟨g,hg,he⟩ := jb
  obtain ⟨q,hq,he'⟩ := cb
  refine .afterSwitch p (t++[g]) (l++[q]) i hp (snocGood ht hg) (snocGood hl hq)
    (by simp; omega) (by simp; omega)
    (includeMore ?_ (Or.inr ⟨lastJoint he,lastLow he'⟩))
  intro a ha
  rcases all a ha with c | ⟨r,r'⟩
  · exact Or.inl c
  · exact Or.inr ⟨keepJoint g r,keepLow q r'⟩

theorem afterDrop {k : ℕ} {s : Pool} {f : F} {p t l : List Gate} {i : ℕ}
    (hl : good l) (lb : l.length+1 ≤ k) (all : ∀ a, s a → behind p t l i a)
    (h : restricted l f) : Stage (k+1) (plus s f) := by
  refine .cheap l hl (by omega) (includeMore ?_ h)
  intro a ha
  exact (all a ha).imp id And.right

theorem cheapNext {k : ℕ} {s : Pool} {f : F} {l : List Gate}
    (hl : good l) (lb : l.length + 2 ≤ k) (all : ∀ a, s a → restricted l a)
    (how : restricted l f ∨ builds (lsz l) (lbase l) (low f)) : Stage (k+1) (plus s f) := by
  rcases how with h | ⟨g,hg,he⟩
  · exact .cheap l hl (by omega) (includeMore all h)
  · refine .cheap (l++[g]) (snocGood hl hg) (by simp; omega) (includeMore ?_ (Or.inr (lastLow he)))
    intro a ha
    exact (all a ha).imp id (keepLow g)

theorem mix {k u : ℕ} {s : Pool} {p l : List Gate} {a b : F} (d : Bool)
    (hp : good p) (hl : good l) (bud : p.length+u ≤ k) (lb : l.length+u ≤ k)
    (all : ∀ f, s f → ahead u p l f)
    (pa : pureU u a) (rb : both p l b) : Stage (k+1) (plus s (binary d a b)) := by
  obtain ⟨c,hc,mono⟩ := pa
  by_cases hot : c false = d
  · apply beginSwitch 0 hp hl bud lb all
    exact Or.inl ⟨d,fun x => by simp [binary,hc,hot,op_hot]⟩
  · have cold : c false = !d := by cases e : c false <;> cases d <;> simp_all
    have lowSame : low (binary d a b) = low b := by
      funext x j
      simp [low,binary,hc,cold,op_cold]
    by_cases hotHigh : c true = d
    · cases d
      · have hu : u ≠ 0 := by
          intro e
          have h := mono e (by simpa using cold)
          rw [hotHigh] at h
          cases h
        apply aCheap (p := p) hl (by omega) all
        right
        unfold lowReal
        rw [lowSame]
        exact rb.2
      · obtain ⟨⟨i,hi,rfl⟩,rl⟩ := rb
        apply beginSwitch i hp hl bud lb all
        right
        constructor
        · have same : binary true a (readB (base p) i) =
              (fun x b => if b then true else readB (base p) i x b) := by
            funext x b
            cases b
            · have cf : c false = false := by simpa using cold
              simp [binary,hc,cf,op]
            · simp [binary,hc,hotHigh,op]
          rw [same]
          exact switchWire p i
        · unfold lowReal
          rw [lowSame]
          exact rl
    · have coldHigh : c true = !d := by cases e : c true <;> cases d <;> simp_all
      apply aStay hp hl bud lb all
      have same : binary d a b = b := by
        funext x j
        cases j <;> simp [binary,hc,cold,coldHigh,op_cold]
      rw [same]; exact Or.inr rb

theorem lowMix {l : List Gate} {a b : F} (d : Bool)
    (h : lowConst a) (h' : restricted l b) : restricted l (binary d a b) := by
  obtain ⟨c,hc⟩ := h
  rcases h' with ⟨v,hv⟩ | r
  · exact Or.inl ⟨op d c v,fun x => by simp [binary,hc,hv]⟩
  · by_cases e : c = d
    · exact Or.inl ⟨d,fun x => by simp [binary,hc,e,op_hot]⟩
    · have ne : c = !d := by cases c <;> cases d <;> simp_all
      have same : low (binary d a b) = low b := by
        funext x j
        simp [low,binary,hc,ne,op_cold]
      exact Or.inr (by unfold lowReal; rw [same]; exact r)

theorem addBin {k : ℕ} {s : Pool} {a b : F} (h : Stage k s) (d : Bool) (ha : s a) (hb : s b) :
    Stage (k+1) (plus s (binary d a b)) := by
  rcases h with ⟨p,l,u,hp,hl,bud,lb,all⟩ | ⟨p,t,l,i,hp,ht,hl,bud,lb,all⟩ | ⟨l,hl,lb,all⟩
  ·
    rcases all a ha with pa | ra <;> rcases all b hb with pb | rb
    · obtain ⟨c,hc,mc⟩ := pa
      obtain ⟨v,hv,mv⟩ := pb
      apply aStay hp hl bud lb all
      refine Or.inl ⟨fun j => op d (c j) (v j),fun x j => by simp [binary,hc,hv],?_⟩
      intro e
      have h1 := mc e
      have h2 := mv e
      show op d (c false) (v false) = true → op d (c true) (v true) = true
      revert h1 h2
      generalize c false = a0
      generalize c true = a1
      generalize v false = b0
      generalize v true = b1
      cases d <;> cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> simp [op]
    · exact mix d hp hl bud lb all pa rb
    · rw [bin_comm d a b]
      exact mix d hp hl bud lb all pb ra
    · exact aBuild hp hl bud lb all (builds_bin (base_len p) d ra.1 rb.1)
        (builds_bin (lbase_len l) d ra.2 rb.2)
  ·
    rcases all a ha with ca | ⟨ra,la⟩ <;> rcases all b hb with cb | ⟨rb,lb'⟩
    · exact afterDrop hl lb all (lowMix d ca (Or.inl cb))
    · exact afterDrop hl lb all (lowMix d ca (Or.inr lb'))
    · rw [bin_comm d a b]
      exact afterDrop hl lb all (lowMix d cb (Or.inr la))
    · exact afterBuild hp ht hl bud lb all (builds_bin (joint_len p t i) d ra rb)
          (builds_bin (lbase_len l) d la lb')
  ·
    rcases all a ha with ca | la <;> rcases all b hb with cb | lb'
    · exact cheapNext hl lb all (Or.inl (lowMix d ca (Or.inl cb)))
    · exact cheapNext hl lb all (Or.inl (lowMix d ca (Or.inr lb')))
    · rw [bin_comm d a b]
      exact cheapNext hl lb all (Or.inl (lowMix d cb (Or.inr la)))
    · exact cheapNext hl lb all (Or.inr (builds_bin (lbase_len l) d la lb'))

theorem addNeg {k : ℕ} {s : Pool} {a : F} (h : Stage k s) (ha : s a) :
    Stage (k+1) (plus s (neg a)) := by
  rcases h with ⟨p,l,u,hp,hl,bud,lb,all⟩ | ⟨p,t,l,i,hp,ht,hl,bud,lb,all⟩ | ⟨l,hl,lb,all⟩
  ·
    rcases all a ha with ⟨c,hc,_⟩ | ra
    · exact aBump hp hl bud lb all
        ⟨fun j => !(c j), fun x j => by simp [neg,hc], fun e => absurd e (Nat.succ_ne_zero u)⟩
    · exact aBuild hp hl bud lb all (builds_neg (base_len p) ra.1) (builds_neg (lbase_len l) ra.2)
  ·
    rcases all a ha with ⟨c,hc⟩ | ⟨ra,la⟩
    · exact afterDrop hl lb all (Or.inl ⟨!c,fun x => by simp [neg,hc]⟩)
    · exact afterBuild hp ht hl bud lb all (builds_neg (joint_len p t i) ra)
        (builds_neg (lbase_len l) la)
  ·
    rcases all a ha with ⟨c,hc⟩ | la
    · exact cheapNext hl lb all (Or.inl (Or.inl ⟨!c,fun x => by simp [neg,hc]⟩))
    · exact cheapNext hl lb all (Or.inr (builds_neg (lbase_len l) la))

theorem addConst {k : ℕ} {s : Pool} (h : Stage k s) (b : Bool) :
    Stage (k+1) (plus s (fun _ _ => b)) := by
  have lc : lowConst (fun _ _ => b) := ⟨b, fun _ => rfl⟩
  rcases h with ⟨p,l,u,hp,hl,bud,lb,all⟩ | ⟨p,t,l,i,hp,ht,hl,bud,lb,all⟩ | ⟨l,hl,lb,all⟩
  · exact aStay hp hl bud lb all (Or.inl ⟨fun _ => b, fun _ _ => rfl, fun _ e => e⟩)
  · exact afterDrop hl lb all (Or.inl lc)
  · exact cheapNext hl lb all (Or.inl (Or.inl lc))

theorem addCopy {k : ℕ} {s : Pool} {a : F} (h : Stage k s) (ha : s a) : Stage (k+1) (plus s a) := by
  rcases h with ⟨p,l,u,hp,hl,bud,lb,all⟩ | ⟨p,t,l,i,hp,ht,hl,bud,lb,all⟩ | ⟨l,hl,lb,all⟩
  · exact aStay hp hl bud lb all (all a ha)
  · exact afterDrop hl lb all ((all a ha).imp id And.right)
  · exact cheapNext hl lb all (Or.inl (all a ha))

def gfun (g : Gate) (w : Bank) : F := fun x b => g.op.eval (g.inputs.map fun i => readB w i x b)

theorem evalStage {k : ℕ} {s : Pool} {w : Bank} (g : Gate) (ok : gateOK g)
    (hs : Stage k s) (hw : ∀ i, s (readB w i)) : Stage (k+1) (plus s (gfun g w)) := by
  obtain ⟨o,ins⟩ := g
  obtain ⟨ho,hlen⟩ := ok
  change o = GateOp.and ∨ o = GateOp.or ∨ o = GateOp.not at ho
  change ins.length ≤ 2 at hlen
  rcases ho with rfl | rfl | rfl
  · cases ins with
    | nil => exact addConst hs true
    | cons i rest =>
      cases rest with
      | nil =>
        have he : gfun ⟨.and,[i]⟩ w = readB w i := by funext x b; simp [gfun,GateOp.eval]
        rw [he]; exact addCopy hs (hw i)
      | cons j rest =>
        have he : rest = [] := by simpa using hlen
        subst rest
        have eq : gfun ⟨.and,[i,j]⟩ w = binary false (readB w i) (readB w j) := by
          funext x b; simp [gfun,GateOp.eval,binary,op]
        rw [eq]; exact addBin hs false (hw i) (hw j)
  · cases ins with
    | nil => exact addConst hs false
    | cons i rest =>
      cases rest with
      | nil =>
        have he : gfun ⟨.or,[i]⟩ w = readB w i := by funext x b; simp [gfun,GateOp.eval]
        rw [he]; exact addCopy hs (hw i)
      | cons j rest =>
        have he : rest = [] := by simpa using hlen
        subst rest
        have eq : gfun ⟨.or,[i,j]⟩ w = binary true (readB w i) (readB w j) := by
          funext x b; simp [gfun,GateOp.eval,binary,op]
        rw [eq]; exact addBin hs true (hw i) (hw j)
  · cases ins with
    | nil => exact addConst hs true
    | cons i _ => exact addNeg hs (hw i)

theorem later {n : ℕ} {w : Bank} (len : ∀ x b, (w x b).length = n) (g : Gate) (i : ℕ) (hn : i ≠ n) :
    readB (extend w g) i = readB w i := by
  funext x b
  by_cases lt : i < n
  · exact List.getD_append _ _ _ _ (by rw [len]; exact lt)
  · change (w x b ++ [_]).getD i false = (w x b).getD i false
    rw [List.getD_eq_default _ _ (by simp [len]; omega),List.getD_eq_default _ _ (by rw [len]; omega)]

theorem process (gs : List Gate) (ok : good gs) {n k : ℕ} {s : Pool} {w : Bank}
    (len : ∀ x b, (w x b).length = n) (hs : Stage k s) (hw : ∀ i, s (readB w i)) :
    ∃ v : Pool, Stage (k+gs.length) v ∧ ∀ i, v (readB (fun x b => run gs (w x b)) i) := by
  induction gs generalizing n k s w with
  | nil => exact ⟨s,by simpa using hs,hw⟩
  | cons g rest ih =>
    let next := plus s (gfun g w)
    have hnext : Stage (k+1) next := evalStage g (ok g List.mem_cons_self) hs hw
    have wires (i : ℕ) : next (readB (extend w g) i) := by
      by_cases e : i = n
      · subst i
        exact Or.inr (funext fun x => funext fun b => lastRead len g x b)
      · exact Or.inl (later len g i e ▸ hw i)
    obtain ⟨v,stage,hv⟩ := ih (fun a ha => ok a (List.mem_cons_of_mem _ ha))
      (n := n+1) (fun x b => by simp [extend,step,len]) hnext wires
    exact ⟨v,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using stage,hv⟩

def seed (x : X) (b : Bool) : List Bool := [x 1,x 0,x 4,x 7,x 5,x 2,b,x 6,x 3,x 1 || b]

theorem inputWire (j : Fin 8) : both [] [] (fun x _ => x j) := by
  refine ⟨⟨j.val,by simp [sz]; omega,?_⟩,⟨j.val,by simp [lsz],?_⟩⟩
  · funext x b
    change (List.ofFn x ++ [x 1 || b]).getD j.val false = x j
    fin_cases j <;> rfl
  · funext x b
    change (List.ofFn x).getD j.val false = x j
    fin_cases j <;> rfl

theorem orWire : both [] [] (fun x b => x 1 || b) := by
  refine ⟨⟨8,by simp [sz],?_⟩,⟨1,by simp [lsz],?_⟩⟩
  · funext x b
    change (List.ofFn x ++ [x 1 || b]).getD 8 false = (x 1 || b)
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  · funext x b
    change (List.ofFn x).getD 1 false = (x 1 || false)
    simp

theorem start (i : ℕ) : ahead 0 [] [] (readB seed i) := by
  by_cases h : i < 10
  · interval_cases i
    · exact Or.inr (inputWire 1)
    · exact Or.inr (inputWire 0)
    · exact Or.inr (inputWire 4)
    · exact Or.inr (inputWire 7)
    · exact Or.inr (inputWire 5)
    · exact Or.inr (inputWire 2)
    · exact Or.inl ⟨id,fun _ _ => rfl,fun _ _ => rfl⟩
    · exact Or.inr (inputWire 6)
    · exact Or.inr (inputWire 3)
    · exact Or.inr orWire
  · refine Or.inl ⟨fun _ => false,fun x b => ?_,fun _ e => e⟩
    exact List.getD_eq_default _ _ (by simp [seed]; omega)

def result (lo hi : X → Bool) : Prop :=
  HasCircuitSize 8 lo 12 ∨ ∃ (p t : Circuit) (i : ℕ),
    FanInTwo p ∧ FanInTwo t ∧ p.size+t.size ≤ 13 ∧
      (∀ x : X, t.eval (p.wires (List.ofFn x ++ [x 1 || false]) ++
        [(p.wires (List.ofFn x ++ [x 1 || false])).getD i false]) = lo x) ∧
      ∀ x : X, t.eval (p.wires (List.ofFn x ++ [x 1 || true]) ++ [true]) = hi x

theorem constantCore {lo : X → Bool} (c : Bool) (h : ∀ x, lo x = c) : HasCircuitSize 8 lo 12 := by
  cases c
  · refine ⟨(⟨[],8⟩ : Circuit), ?_, by decide, ?_⟩
    · intro g hg
      change g ∈ ([] : List Gate) at hg
      cases hg
    · intro x
      rw [h]
      change (List.ofFn x).getD 8 false = false
      exact List.getD_eq_default _ _ (by simp)
  · refine ⟨⟨[⟨.and,[]⟩],8⟩,?_,by decide,?_⟩
    · intro g hg
      have : g = ⟨.and,[]⟩ := List.mem_singleton.mp hg
      subst g; simp
    · intro x
      rw [h]
      change (List.ofFn x ++ [true]).getD 8 false = true
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp

theorem finish {k : ℕ} {s : Pool} {f : F} {lo hi : X → Bool} (hk : k ≤ 14)
    (hs : Stage k s) (haveOut : s f) (he : ∀ x b, f x b = if b then hi x else lo x)
    (wit : ∃ x : X, x 1 = true ∧ lo x = false ∧ hi x = true) : result lo hi := by
  have constEnd (h : lowConst f) : result lo hi := by
    obtain ⟨c,hc⟩ := h
    exact Or.inl (constantCore c (fun x => (he x false).symm.trans (hc x)))
  rcases hs with ⟨p,l,u,hp,hl,bud,lb,all⟩ | ⟨p,t,l,i,hp,ht,hl,bud,lb,all⟩ | ⟨l,hl,bud,all⟩
  ·
    rcases all f haveOut with h | ⟨⟨i,_,rfl⟩,_⟩
    · exact constEnd (pure_low h)
    · obtain ⟨x,x1,xlo,xhi⟩ := wit
      have same : readB (base p) i x false = readB (base p) i x true := by
        simp [readB,base,x1]
      have h0 := he x false
      have h1 := he x true
      rw [same] at h0
      rw [h0] at h1
      simp [xlo,xhi] at h1
  ·
    rcases all f haveOut with c | ⟨⟨j,_,rfl⟩,_⟩
    · exact constEnd c
    · refine Or.inr ⟨⟨p,0⟩,⟨t,j⟩,i,hp,ht,?_,?_,?_⟩
      · change p.length+t.length ≤ 13
        omega
      · intro x
        exact he x false
      · intro x
        exact he x true
  ·
    rcases all f haveOut with c | ⟨i,_,hr⟩
    · exact constEnd c
    · refine Or.inl ⟨⟨l,i⟩,hl,?_,?_⟩
      · change l.length ≤ 12; omega
      · intro x
        exact (congrFun (congrFun hr x) false).trans (he x false)

theorem solve (C : Circuit) (lo hi : X → Bool) (fan : FanInTwo C) (small : C.size ≤ 14)
    (spec : ∀ (b : Bool) (x : X), C.eval (seed x b) = if b = true then hi x else lo x)
    (wit : ∃ x : X, x 1 = true ∧ lo x = false ∧ hi x = true) : result lo hi := by
  obtain ⟨gs,out⟩ := C
  let s : Pool := ahead 0 [] []
  have hs : Stage 0 s :=
    .before [] [] 0 (by intro a h; cases h) (by intro a h; cases h) (by decide) (by decide)
      (fun _ h => h)
  obtain ⟨v,hv,avail⟩ := process gs fan (fun x b => show (seed x b).length = 10 from rfl) hs start
  apply finish (s := v) (k := 0 + gs.length) (by change gs.length ≤ 14 at small; omega)
    hv (avail out) _ wit
  intro x b
  have h := spec b x
  change (run gs (seed x b)).getD out false = _ at h
  exact h
end PEqualNP.Outside.L_meta_3102

theorem PEqualNP.Outside.L_meta_3102 : have x1 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x1 : Bool) (x2 : Fin (8 : ℕ) → Bool) => [x2 (1 : Fin (8 : ℕ)), x2 (0 : Fin (8 : ℕ)), x2 (4 : Fin (8 : ℕ)), x2 (7 : Fin (8 : ℕ)), x2 (5 : Fin (8 : ℕ)), x2 (2 : Fin (8 : ℕ)), x1, x2 (6 : Fin (8 : ℕ)), x2 (3 : Fin (8 : ℕ)), x2 (1 : Fin (8 : ℕ)) || x1]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : (Fin (8 : ℕ) → Bool) → Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (14 : ℕ) →       (∀ (x7 : Bool) (x8 : Fin (8 : ℕ) → Bool), x2.eval (x1 x7 x8) = if x7 = Bool.true then x4 x8 else x3 x8) →         (∃ (x8 : Fin (8 : ℕ) → Bool), x8 (1 : Fin (8 : ℕ)) = Bool.true ∧ x3 x8 = Bool.false ∧ x4 x8 = Bool.true) →           PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x3 (12 : ℕ) ∨             ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : ℕ),               PEqualNP.MetaComplexity.FanInTwo x9 ∧                 PEqualNP.MetaComplexity.FanInTwo x10 ∧                   x9.size + x10.size ≤ (13 : ℕ) ∧                     have x12 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x12 : Bool) (x13 : Fin (8 : ℕ) → Bool) => x9.wires (List.ofFn x13 ++ [x13 (1 : Fin (8 : ℕ)) || x12]);                     (∀ (x13 : Fin (8 : ℕ) → Bool), x10.eval (x12 Bool.false x13 ++ [(x12 Bool.false x13).getD x11 Bool.false]) = x3 x13) ∧ ∀ (x13 : Fin (8 : ℕ) → Bool), x10.eval (x12 Bool.true x13 ++ [Bool.true]) = x4 x13 :=
  fun C lo hi fan small spec wit => PEqualNP.Outside.L_meta_3102.solve C lo hi fan small spec wit
