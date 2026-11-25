import PEqualNP.Defs

namespace Witness11065
open PEqualNP.CircuitLowerBounds
def gates : List Gate := [⟨.or,[3,4]⟩,⟨.or,[2,5]⟩,⟨.or,[1,6]⟩,⟨.or,[7,8]⟩,⟨.and,[7,8]⟩,⟨.and,[10,9]⟩,⟨.or,[11,12]⟩,⟨.or,[0,13]⟩,⟨.or,[4,5]⟩,⟨.or,[15,6]⟩,⟨.and,[14,16]⟩]
def G (x : Fin 7 → Bool) := decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
theorem mono : ∀ g ∈ gates,(g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by simp [gates]
theorem computes : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates,17⟩ (List.ofFn x) = G x := by decide +kernel
end Witness11065

namespace Signed11065
open PEqualNP.CircuitLowerBounds
abbrev X := Fin 7 → Bool
abbrev F := X → Bool
def flip (s : Bool) (f : F) (x : X) := xor s (f x)
def Av (L : List F) (f : F) := (∃ b, f=fun _ => b) ∨ ∃ g ∈ L, ∃ s, f=flip s g
inductive Built : Nat → List F → Prop
| base : Built 0 (List.ofFn fun i : Fin 7 => fun x : X => x i)
| step {n L a b} : Built n L → Av L a → Av L b → Built (n+1) ((fun x => a x && b x)::L)
theorem raw {L : List F} {f : F} (h : f∈L) : Av L f := Or.inr ⟨f,h,false,by funext x; simp [flip]⟩
theorem inv {L f} (h : Av L f) : Av L (fun x => !(f x)) := by
  rcases h with ⟨b,rfl⟩|⟨g,hg,s,rfl⟩
  · exact Or.inl ⟨!b,rfl⟩
  · exact Or.inr ⟨g,hg,!s,by funext x; unfold flip; cases s <;> cases g x <;> rfl⟩
theorem more {L f} (h : Av L f) (g : F) : Av (g::L) f := by
  rcases h with hc|⟨a,ha,s,rfl⟩; exact Or.inl hc; exact Or.inr ⟨a,List.mem_cons_of_mem _ ha,s,rfl⟩
def step (ws : X → List Bool) (g : Gate) (x : X) := ws x ++ [g.op.eval (g.inputs.map fun i => (ws x).getD i false)]
def cost (g : Gate) := match g.op with | .not => 0 | _ => 1
def Tracks (L : List F) (ws : X → List Bool) := ∀ i,Av L (fun x => (ws x).getD i false)
theorem addGate {k L ws len} (build : Built k L) (track : Tracks L ws) (length : ∀ x,(ws x).length=len) (g : Gate) (ok : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) : ∃ k' L',k'≤k+cost g ∧ Built k' L' ∧ Tracks L' (step ws g) := by
  let val : F := fun x => g.op.eval (g.inputs.map fun i => (ws x).getD i false)
  suffices aux : ∃ k' L', k'≤k+cost g ∧ Built k' L' ∧ (∀ f,Av L f → Av L' f) ∧ Av L' val by
    obtain ⟨k',L',h,b,incl,good⟩ := aux; refine ⟨k',L',h,b,?_⟩; intro i; by_cases lt : i<len
    · convert incl _ (track i) using 1; congr 1; funext x; exact List.getD_append _ _ _ _ (by rwa [length])
    · by_cases eq : i=len
      · subst i; convert good using 1; congr 1; funext x; simp [step,val,List.getD_eq_getElem?_getD,List.getElem?_append,length]
      · apply Or.inl; refine ⟨false,?_⟩; funext x; apply List.getD_eq_default; simp [step,length]; omega
  rcases g with ⟨op,ins⟩; obtain ⟨ops,n⟩ := ok
  cases ins with
  | nil => exact ⟨k,L,by omega,build,fun _ h=>h,Or.inl ⟨op.eval [],rfl⟩⟩
  | cons a rest =>
    cases rest with
    | nil => rcases ops with rfl|rfl|rfl <;> refine ⟨k,L,by omega,build,fun _ h=>h,?_⟩
             · simpa [val,GateOp.eval] using track a
             · simpa [val,GateOp.eval] using track a
             · exact inv (track a)
    | cons b tail =>
      have nil : tail=[] := by simpa using n
      subst tail; rcases ops with rfl|rfl|rfl
      · let q : F := fun x => (ws x).getD a false && (ws x).getD b false
        exact ⟨_,q::L,by rfl,Built.step build (track a) (track b),fun _ h=>more h _,by simpa [val,GateOp.eval,q] using (raw (L:=q::L) (f:=q) List.mem_cons_self)⟩
      · let q : F := fun x => !((ws x).getD a false) && !((ws x).getD b false)
        refine ⟨_,q::L,by rfl,Built.step build (inv (track a)) (inv (track b)),fun _ h=>more h _,?_⟩
        have h := inv (raw (L:=q::L) (f:=q) List.mem_cons_self); convert h using 1; congr 1; funext x; simp [q,val,GateOp.eval]
      · exact ⟨k,L,by omega,build,fun _ h=>h,inv (track a)⟩
end Signed11065

namespace Signed11065
open PEqualNP.CircuitLowerBounds
def Ok (g : Gate) := (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2
def run (gs : List Gate) (ws : X → List Bool) := gs.foldl step ws
theorem foldRun (gs : List Gate) (ok : ∀ g∈gs,Ok g) {k L ws len} (build : Built k L) (track : Tracks L ws) (length : ∀ x,(ws x).length=len) : ∃ k' L',k'≤k+(gs.map cost).sum ∧ Built k' L' ∧ Tracks L' (run gs ws) := by
  induction gs generalizing k L ws len with
  | nil => exact ⟨_,_,by simp,build,track⟩
  | cons g gs ih =>
    obtain ⟨a,l,le,b,tr⟩ := addGate build track length g (ok _ List.mem_cons_self)
    obtain ⟨a',l',le',b',tr'⟩ := ih (fun q h=>ok _ (List.mem_cons_of_mem _ h)) b tr (len:=len+1) (by intro x; simp [step,length])
    exact ⟨a',l',by simp; omega,b',tr'⟩
private theorem evalRun (gs : List Gate) (ws : X → List Bool) (x : X) : run gs ws x=gs.foldl (fun z g => z++[g.op.eval (g.inputs.map fun i => z.getD i false)]) (ws x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih => exact ih (step ws g)
theorem normalize (gs : List Gate) (o : ℕ) (ok : ∀ g∈gs,Ok g) : ∃ k L,k≤(gs.map cost).sum ∧ Built k L ∧ Av L (fun x => Circuit.eval ⟨gs,o⟩ (List.ofFn x)) := by
  have tr : Tracks (List.ofFn fun i : Fin 7 => fun x : X => x i) (fun x => List.ofFn x) := by
    intro i; by_cases h : i<7
    · convert raw (List.mem_ofFn.mpr ⟨⟨i,h⟩,rfl⟩ : (fun x : X => x ⟨i,h⟩)∈List.ofFn (fun j : Fin 7 => fun x : X => x j)) using 1; funext x; rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),List.getElem_ofFn]
    · left; exact ⟨false,by funext x; apply List.getD_eq_default; simp; omega⟩
  obtain ⟨k,L,le,b,track⟩ := foldRun gs ok Built.base tr (len:=7) (by simp)
  refine ⟨k,L,by simpa using le,b,?_⟩; convert track o using 1; funext x; rw [evalRun]; rfl
theorem binaryCost (gs : List Gate) : (gs.map cost).sum + (gs.filter (fun g=>match g.op with | .not => true | _ => false)).length=gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g with | mk op ins => cases op <;> simp [cost] at * <;> omega
end Signed11065

open Signed11065 Witness11065 PEqualNP.CircuitLowerBounds
theorem positiveFromSigned (lower : ∀ k L, k≤9 → Built k L → ¬ Av L G) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o ok unique correct
  by_cases many : 11≤gs.length
  · exact ⟨gates,17,mono,many,computes⟩
  by_cases used : ∃ g ∈ gs,g.op=.not
  · obtain ⟨g,hg,notg⟩ := used
    obtain ⟨k,L,le,build,av⟩ := normalize gs o ok
    have count := binaryCost gs
    have mem : g ∈ gs.filter (fun g=>match g.op with | .not => true | _ => false) := List.mem_filter.mpr ⟨hg,by simp [notg]⟩
    have positive := List.length_pos_of_mem mem
    have eq : (fun x : X => Circuit.eval ⟨gs,o⟩ (List.ofFn x))=G := funext correct
    have budget := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right positive) (le_of_eq count)
    rw [eq] at av; exact False.elim (lower k L (by omega) build av)
  · refine ⟨gs,o,?_,le_rfl,correct⟩; intro g hg; obtain ⟨ops,sz⟩ := ok g hg; refine ⟨?_,sz⟩; rcases ops with a|a|a; exact Or.inl a; exact Or.inr a; exact False.elim (used ⟨g,hg,a⟩)

namespace ReduceFour11065
abbrev F (ι : Type) := ι → Bool
def flip {ι} (s : Bool) (f : F ι) : F ι := fun x => xor s (f x)
def Av {ι} (L : List (F ι)) (f : F ι) : Prop := (∃ b, f = fun _ => b) ∨ ∃ g ∈ L, ∃ s, f = flip s g
inductive Build {ι : Type} (P : List (F ι)) : Nat → List (F ι) → Prop
| base : Build P 0 P
| step {n L a b} : Build P n L → Av L a → Av L b → Build P (n+1) ((fun x => a x && b x)::L)
abbrev Row (n : Nat) := Fin n → Bool
def bank (n : Nat) : List (F (Row n)) := List.ofFn fun i : Fin n => fun x : Row n => x i
def K4 (x : Row 4) : Bool := (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) || (x 2 && x 3)
end ReduceFour11065

namespace ReduceFour11065
variable {α β : Type}
private theorem avRaw {L : List (F α)} {f} (h : f ∈ L) : Av L f :=
  .inr ⟨f,h,false,by funext x; simp [flip]⟩
private theorem avFlip {L : List (F α)} {f} (h : Av L f) (s : Bool) : Av L (flip s f) := by
  rcases h with ⟨v,rfl⟩ | ⟨g,hg,t,rfl⟩
  · exact .inl ⟨xor s v,rfl⟩
  · exact .inr ⟨g,hg,xor s t, by funext x; unfold flip; cases s <;> cases t <;> cases g x <;> rfl⟩
private theorem avMore {L : List (F α)} {f} (h : Av L f) (g : F α) : Av (g::L) f := by
  rcases h with h|⟨a,ha,s,rfl⟩
  · exact .inl h
  · exact .inr ⟨a,List.mem_cons_of_mem _ ha,s,rfl⟩
private theorem avMap {L : List (F α)} {M : List (F β)} (r : β → α)
    (ctx : ∀ g ∈ L, Av M (g ∘ r)) {f} (h : Av L f) : Av M (f ∘ r) := by
  rcases h with ⟨v,rfl⟩|⟨g,hg,s,rfl⟩
  · exact .inl ⟨v,rfl⟩
  · exact avFlip (ctx g hg) s
private def Good (p q : α) (r : β → α) (f : F α) : Prop :=
  f p = f q ∨ ∃ b, f ∘ r = fun _ => b
private theorem goodAv {L : List (F α)} {p q : α} {r : β → α}
    (ctx : ∀ g ∈ L, Good p q r g) {f} (av : Av L f) : Good p q r f := by
  rcases av with ⟨v,rfl⟩ | ⟨g,hg,s,rfl⟩
  · exact .inl rfl
  · rcases ctx g hg with h|⟨v,h⟩
    · exact .inl (congrArg (xor s) h)
    · exact .inr ⟨xor s v, funext fun x => congrArg (xor s) (congrFun h x)⟩
private theorem collapse {r : β → α} {a b : F α} {M : List (F β)}
    (ha : Av M (a ∘ r)) (hb : Av M (b ∘ r))
    (one : (∃ c, a ∘ r = fun _ => c) ∨ ∃ c, b ∘ r = fun _ => c) :
    Av M ((fun x => a x && b x) ∘ r) := by
  rcases one with ⟨v,h⟩|⟨v,h⟩
  · change Av M (fun x => (a ∘ r) x && (b ∘ r) x); rw [h]; cases v <;> simp
    · exact .inl ⟨false,rfl⟩
    · exact hb
  · change Av M (fun x => (a ∘ r) x && (b ∘ r) x); rw [h]; cases v <;> simp
    · exact .inl ⟨false,rfl⟩
    · exact ha
private theorem project {P : List (F α)} {Q : List (F β)} {n L} (r : β → α) (p q : α)
    (hP : ∀ f ∈ P, Av Q (f ∘ r)) (baseGood : ∀ f ∈ P, Good p q r f)
    (bd : Build P n L) : ∃ k M, k ≤ n ∧ Build Q k M ∧
      (∀ f ∈ L, Av M (f ∘ r)) ∧ (k=n → ∀ f ∈ L, Good p q r f) := by
  induction bd with
  | base => exact ⟨0,Q,le_rfl,.base,hP,fun _=>baseGood⟩
  | @step n L a b _ ha hb ih =>
    obtain ⟨k,M,le,built,ctx,eqGood⟩ := ih
    have avA := avMap r ctx ha
    have avB := avMap r ctx hb
    let f : F α := fun x => a x && b x
    by_cases free : (∃ c, a ∘ r = fun _ => c) ∨ ∃ c, b ∘ r = fun _ => c
    · refine ⟨k,M,by omega,built,?_,by omega⟩
      intro g hg; rcases List.mem_cons.mp hg with rfl|inL
      · exact collapse avA avB free
      · exact ctx _ inL
    · refine ⟨k+1,(f ∘ r)::M,by omega,Build.step built avA avB,?_,?_⟩
      · intro g hg; rcases List.mem_cons.mp hg with rfl|inL
        · exact avRaw List.mem_cons_self
        · exact avMore (ctx _ inL) _
      · intro e g hg; have eq : k=n := by omega
        rcases List.mem_cons.mp hg with rfl|inL
        · have sa := (goodAv (eqGood eq) ha).resolve_right (fun h=>free (.inl h))
          have sb := (goodAv (eqGood eq) hb).resolve_right (fun h=>free (.inr h))
          exact .inl (congrArg₂ Bool.and sa sb)
        · exact eqGood eq _ inL

theorem restrictCost {P : List (F α)} {Q : List (F β)} {n L f}
    (r : β → α) (p q : α) (ctx : ∀ w ∈ P, Av Q (w ∘ r))
    (pure : ∀ w ∈ P, w p = w q ∨ ∃ b, w ∘ r = fun _ => b)
    (diff : f p ≠ f q) (nonc : ∃ y z, f (r y) ≠ f (r z))
    (bd : Build P n L) (av : Av L f) : ∃ k M, k < n ∧ Build Q k M ∧ Av M (f ∘ r) := by
  obtain ⟨k,M,le,b,track,peq⟩ := project r p q ctx pure bd
  refine ⟨k,M,?_,b,avMap r track av⟩
  by_contra! ge
  have g := goodAv (peq (by omega)) av
  obtain ⟨v,h⟩ := g.resolve_left diff
  obtain ⟨y,z,ne⟩ := nonc
  exact ne ((congrFun h y).trans (congrFun h z).symm)

private theorem reindex {P : List (F α)} {Q : List (F β)} {n L} (r : β → α)
    (hP : ∀ f ∈ P, Av Q (f ∘ r)) (bd : Build P n L) :
    ∃ M, Build Q n M ∧ ∀ f ∈ L, Av M (f ∘ r) := by
  induction bd with
  | base => exact ⟨Q,.base,hP⟩
  | @step n L a b _ ha hb ih =>
    obtain ⟨M,bd,track⟩ := ih
    refine ⟨_,Build.step bd (avMap r track ha) (avMap r track hb),?_⟩
    intro f h; rcases List.mem_cons.mp h with rfl|inL
    · exact avRaw List.mem_cons_self
    · exact avMore (track _ inL) _
private theorem convertBuild {n L} (h : Signed11065.Built n L) : Build (bank 7) n L := by
  induction h with
  | base => exact .base
  | step _ a b ih => exact .step ih a b
private def pin (i : Fin 7) (x : Row 7) : Row 7 := Function.update x i false
private theorem rawBank (n) (i : Fin n) : Av (bank n) (fun x => x i) :=
  avRaw (List.mem_ofFn.mpr ⟨i,rfl⟩)
private theorem pinCtx (i : Fin 7) : ∀ f ∈ bank 7, Av (bank 7) (f ∘ pin i) := by
  intro f m; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp m
  by_cases h : j=i
  · subst j; exact .inl ⟨false,by funext x; simp [pin]⟩
  · simpa [Function.comp_def,pin,h] using rawBank 7 j
private theorem pinPure (i : Fin 7) (p q : Row 7) (agree : ∀ j, j≠i → p j=q j) :
    ∀ f ∈ bank 7, f p = f q ∨ ∃ b, f ∘ pin i = fun _ => b := by
  intro f m; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp m
  by_cases h : j=i
  · subst j; exact .inr ⟨false,by funext x; simp [pin]⟩
  · exact .inl (agree j h)
private def four (x : Row 4) : Row 7 := ![x 0,false,false,false,x 1,x 2,x 3]
private theorem fourCtx : ∀ f ∈ bank 7, Av (bank 4) (f ∘ four) := by
  intro f m; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp m
  fin_cases j <;> first | exact .inl ⟨false,rfl⟩ | exact rawBank 4 0 | exact rawBank 4 1 | exact rawBank 4 2 | exact rawBank 4 3
private def p (v : Fin 7) : Row 7 := fun j => decide (j=v)
private def q (i v : Fin 7) : Row 7 := Function.update (p v) i true
private theorem pureAt (i v : Fin 7) : ∀ w ∈ bank 7, w (p v) = w (q i v) ∨ ∃ b, w ∘ pin i = fun _ => b :=
  pinPure i (p v) (q i v) (by intro j h; simp [q,h])
private def f1 := Witness11065.G ∘ pin 1
private def f2 := f1 ∘ pin 2
private def f3 := f2 ∘ pin 3
private theorem nonconst (f : F (Row 7)) (i : Fin 7)
    (h : f (pin i (fun _ => false)) ≠ f (pin i (fun _ => true))) :
    ∃ y z, f (pin i y) ≠ f (pin i z) := ⟨_,_,h⟩

theorem reduce {n L} (bd : Signed11065.Built n L) (av : Signed11065.Av L Witness11065.G) :
    ∃ k M, k+3 ≤ n ∧ Build (bank 4) k M ∧ Av M K4 := by
  obtain ⟨k1,M1,h1,b1,a1⟩ := restrictCost (pin 1) (p 4) (q 1 4) (pinCtx 1) (pureAt 1 4)
    (f:=Witness11065.G) (by decide +kernel) (nonconst _ _ (by decide +kernel)) (convertBuild bd) av
  change Av M1 f1 at a1
  obtain ⟨k2,M2,h2,b2,a2⟩ := restrictCost (pin 2) (p 4) (q 2 4) (pinCtx 2) (pureAt 2 4)
    (f:=f1) (by decide +kernel) (nonconst _ _ (by decide +kernel)) b1 a1
  change Av M2 f2 at a2
  obtain ⟨k3,M3,h3,b3,a3⟩ := restrictCost (pin 3) (p 5) (q 3 5) (pinCtx 3) (pureAt 3 5)
    (f:=f2) (by decide +kernel) (nonconst _ _ (by decide +kernel)) b2 a2
  change Av M3 f3 at a3
  obtain ⟨M,b,ctx⟩ := reindex four fourCtx b3
  refine ⟨_,M,by omega,b,?_⟩
  have e : f3 ∘ four = K4 := by funext x; revert x; decide +kernel
  rw [←e]; exact avMap four ctx a3
end ReduceFour11065

namespace CoreFour11065Check
open ReduceFour11065
abbrev B := BitVec 55
abbrev W := B × B
def goal : W := (BitVec.allOnes 55, 0)
def zero : W := (0,0)
def raw : List W := [(0x55bab756eadd5b,0x3ff800),(0x66dcdb9b736e6d,0x1ffc00000),(0x78ef1de3bc778e,0xffe00000000),(0x7f0fe1fc3f87f0,0x7ff00000000000)]
def initial := zero :: raw
abbrev R := Bool × Fin 55
def bit (q : R) (w : W) := (if q.1 then w.1 else w.2).getLsbD q.2.val
inductive Op | meet | join | diff | rdiff
def run : Op → W → W → W
  | .meet,a,b => (a.1 &&& b.1,a.2 &&& b.2)
  | .join,a,b => (a.1 ||| b.1,a.2 ||| b.2)
  | .diff,a,b => (a.1 &&& ~~~b.1,a.2 &&& ~~~b.2)
  | .rdiff,a,b => (~~~a.1 &&& b.1,~~~a.2 &&& b.2)
def act : Op → Bool → Bool → Bool
  | .meet,a,b => a && b
  | .join,a,b => a || b
  | .diff,a,b => a && !b
  | .rdiff,a,b => !a && b
theorem bit_run (o : Op) (a b : W) (q : R) : bit q (run o a b) = act o (bit q a) (bit q b) := by
  obtain ⟨s,i⟩ := q; cases o <;> cases s <;> simp [bit,run,act,i.isLt]
-- A straight-line program, with unused gates admissible via `idle`.
inductive Prog : Finset W → ℕ → Prop
  | done {S k} : goal ∈ S → Prog S k
  | idle {S k} : Prog S k → Prog S (k+1)
  | step {S k a b} (o : Op) : a ∈ S → b ∈ S → Prog (insert (run o a b) S) k → Prog S (k+1)
theorem mono {S k} (h : Prog S k) {T} (st : S ⊆ T) : Prog T k := by
  induction h generalizing T with
  | done m => exact .done (st m)
  | idle _ ih => exact .idle (ih st)
  | step o ha hb _ ih => exact .step o (st ha) (st hb) (ih (Finset.insert_subset_insert _ st))

-- Trace demand backwards: a gate can replace one needed word by at most two.
theorem sparse {S k} (h : Prog S k) : ∃ T ⊆ S, T.card ≤ k+1 ∧ Prog T k := by
  induction h with
  | done m => exact ⟨{goal},by simpa,by simp,.done (by simp)⟩
  | idle _ ih => obtain ⟨T,sub,c,pr⟩ := ih; exact ⟨T,sub,by omega,.idle pr⟩
  | @step S k a b o ha hb _ ih =>
    obtain ⟨T,sub,c,pr⟩ := ih
    let z := run o a b
    by_cases need : z ∈ T
    · let U := insert a (insert b (T.erase z))
      refine ⟨U,?_,?_,.step (a:=a) (b:=b) o (by simp [U]) (by simp [U]) (mono pr ?_)⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl|hx; exact ha
        rcases Finset.mem_insert.mp hx with rfl|hx; exact hb
        exact (Finset.mem_insert.mp (sub (Finset.mem_erase.mp hx).2)).resolve_left (Finset.mem_erase.mp hx).1
      · have e := Finset.card_erase_of_mem need
        have p := Finset.card_insert_le b (T.erase z)
        have q := Finset.card_insert_le a (insert b (T.erase z)); dsimp [U]; omega
      · intro x hx; by_cases e : x=z
        · exact Finset.mem_insert.mpr (Or.inl e)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,hx⟩)))
    · exact ⟨T,fun x hx => (Finset.mem_insert.mp (sub hx)).resolve_left (by rintro rfl; exact need hx),by omega,.idle pr⟩

theorem onBits : ∀ i : Fin 55, (BitVec.allOnes 55).getLsbD i.val = true := by decide +kernel
theorem splits {S k} (h : Prog S k) (i : Fin 55) : ∃ w ∈ S, bit (true,i) w ≠ bit (false,i) w := by
  induction h with
  | done m => exact ⟨goal,m,by change (BitVec.allOnes 55).getLsbD i.val ≠ (0:B).getLsbD i.val; rw [onBits]; simp⟩
  | idle _ ih => exact ih
  | @step S k a b o ha hb _ ih =>
    obtain ⟨w,hm,d⟩ := ih
    rcases Finset.mem_insert.mp hm with rfl|hm
    · rw [bit_run,bit_run] at d
      by_cases e : bit (true,i) a = bit (false,i) a
      · exact ⟨b,hb,fun f => d (by rw [e,f])⟩
      · exact ⟨a,ha,e⟩
    · exact ⟨w,hm,d⟩
def mask : List W → B
  | [] => 0
  | w::ws => (w.1 ^^^ w.2) ||| mask ws
theorem masked {L : List W} {k} (h : Prog L.toFinset k) : mask L = BitVec.allOnes 55 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨w,hw,sep⟩ := splits h ⟨i,hi⟩
  have hw' : w ∈ L := by simpa using hw
  have aux (l : List W) (m : w ∈ l) : (mask l).getLsbD i=true := by
    induction l with
    | nil => simp at m
    | cons x xs ih =>
      rcases List.mem_cons.mp m with rfl|m
      · simp only [bit,ite_true] at sep
        simp [mask,show ((w.1.getLsbD i) ^^ (w.2.getLsbD i)) = true by grind]
      · simp [mask,ih m]
  rw [show (BitVec.allOnes 55).getLsbD i = true from onBits ⟨i,hi⟩]; exact aux L hw'
def candidates (l : List W) := (l.flatMap fun a => l.flatMap fun b => [run .meet a b,run .join a b,run .diff a b,run .rdiff a b]).dedup
theorem candidate (l : List W) (o : Op) {a b} (ha : a ∈ l) (hb : b ∈ l) : run o a b ∈ candidates l := by
  simp only [candidates,List.mem_dedup,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false]
  refine ⟨a,ha,b,hb,?_⟩; cases o <;> simp
def check : ℕ → List W → Bool
  | 0,L => L.contains goal
  | k+1,L => L.sublists.any fun Q => decide (Q.length ≤ k+2) && (mask Q == BitVec.allOnes 55) &&
      (check k Q || (candidates Q).any (fun z => !(Q.contains z) && check k (z::Q)))

theorem checked {L : List W} {k} (h : Prog L.toFinset k) : check k L=true := by
  induction k generalizing L with
  | zero => cases h with | done h => simpa [check] using h
  | succ k ih =>
    obtain ⟨T,sub,sz,pr⟩ := sparse h
    let Q := L.dedup.filter fun w => decide (w ∈ T)
    have eqT : Q.toFinset=T := by ext w; simp [Q]; exact fun h => (show w∈L by simpa using sub h)
    have mq : Q ∈ L.sublists := List.mem_sublists.mpr (List.filter_sublist.trans (List.dedup_sublist _))
    have len : Q.length ≤ k+2 := by
      rw [← List.toFinset_card_of_nodup (l:=Q) ((List.nodup_dedup L).filter _),eqT]; exact sz
    rw [← eqT] at pr
    apply List.any_eq_true.mpr; refine ⟨Q,mq,?_⟩
    simp only [decide_eq_true len,masked pr,beq_self_eq_true,Bool.true_and,Bool.or_eq_true]
    generalize hs : Q.toFinset=S at pr
    cases pr with
    | done m => left; exact ih (.done (hs ▸ m))
    | idle p => left; exact ih (hs ▸ p)
    | @step _ _ a b o ma mb p =>
      subst S
      by_cases old : run o a b ∈ Q
      · left; apply ih; simpa [Finset.insert_eq_of_mem (List.mem_toFinset.mpr old)] using p
      · right; apply List.any_eq_true.mpr
        refine ⟨_,candidate _ o (by simpa using ma) (by simpa using mb),?_⟩
        have yes := ih (L:=run o a b :: Q) (by simpa using p)
        simp [old,yes]
end CoreFour11065Check

namespace SparseBridge11065
open ReduceFour11065 CoreFour11065Check
private def sample (q : R) (i : Fin 4) : Bool := bit q (raw.getD i.val zero)
private def code (f : F (Row 4)) (q : R) := xor (f (fun _ => false)) (f (sample q))
private def Holds (S : Finset W) (f : F (Row 4)) := ∃ w ∈ S, ∀ q, bit q w = code f q
private def Track (S : Finset W) (L : List (F (Row 4))) := ∀ f ∈ L, Holds S f
private theorem avHolds {S L f} (hz : zero ∈ S) (ctx : Track S L) (av : Av L f) : Holds S f := by
  rcases av with ⟨v,rfl⟩ | ⟨g,hg,s,rfl⟩
  · refine ⟨zero,hz,?_⟩; intro ⟨t,i⟩; cases t <;> simp [bit,zero,code]
  · obtain ⟨w,hw,eq⟩ := ctx _ hg
    refine ⟨w,hw,fun q=>?_⟩; rw [eq]; unfold code ReduceFour11065.flip
    cases s <;> cases g (fun _ => false) <;> cases g (sample q) <;> rfl
private theorem rawTrack : Track initial.toFinset (bank 4) := by
  intro f m; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp m
  refine ⟨raw.getD j.val zero,?_,?_⟩
  · revert j; decide +kernel
  · intro q; simp [code,sample]
private def opcode (a b : Bool) : Op := match a,b with
  | false,false => .meet | false,true => .diff | true,false => .rdiff | true,true => .join
private theorem combine {a b : F (Row 4)} {u v : W}
    (hu : ∀ q, bit q u = code a q) (hv : ∀ q, bit q v = code b q) :
    ∀ q, bit q (run (opcode (a (fun _=>false)) (b (fun _=>false))) u v) = code (fun x=>a x && b x) q := by
  intro q; rw [bit_run,hu,hv]; unfold code; dsimp only
  cases a (fun _ => false) <;> cases b (fun _ => false) <;> cases a (sample q) <;> cases b (sample q) <;> rfl
private theorem convert {k L} (b : Build (bank 4) k L) : ∀ t,
    (∀ S, zero ∈ S → Track S L → Prog S t) → Prog initial.toFinset (k+t) := by
  induction b with
  | base => intro t cont; simpa using cont _ (by simp [initial]) rawTrack
  | @step k L a b _ ha hb ih =>
    intro t cont
    have res := ih (t+1) (by
      intro S hz ctx
      obtain ⟨u,hu,cu⟩ := avHolds hz ctx ha
      obtain ⟨v,hv,cv⟩ := avHolds hz ctx hb
      let op := opcode (a (fun _=>false)) (b (fun _=>false))
      apply Prog.step op hu hv
      apply cont _ (Finset.mem_insert_of_mem hz)
      intro f hf; rcases List.mem_cons.mp hf with rfl|mem
      · exact ⟨run op u v,Finset.mem_insert_self ..,combine cu cv⟩
      · obtain ⟨w,hw,cw⟩ := ctx _ mem; exact ⟨w,Finset.mem_insert_of_mem hw,cw⟩)
    convert res using 1; omega
private theorem targetBits : ∀ q, code K4 q = bit q goal := by decide +kernel
private theorem word_ext {w z : W} (e : ∀ q, bit q w = bit q z) : w = z := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq; intro i hi; exact e (true,⟨i,hi⟩)
  · apply BitVec.eq_of_getLsbD_eq; intro i hi; exact e (false,⟨i,hi⟩)
private theorem pad {S k m} (p : Prog S k) (le : k≤m) : Prog S m := by
  induction le with | refl => exact p | step _ ih => exact .idle ih
theorem bridge {k L} (b : Build (bank 4) k L) (a : Av L K4) (le : k≤6) : Prog initial.toFinset 6 := by
  apply pad (k:=k) _ le
  simpa using convert b 0 (by
    intro S hz ctx
    obtain ⟨w,hw,eq⟩ := avHolds hz ctx a
    have e : w=goal := word_ext (fun q=>(eq q).trans (targetBits q))
    exact .done (e ▸ hw))
end SparseBridge11065

namespace CoreFour11065Check
abbrev Batch := List (List W)
def covered (D : Batch) (P : List W) := D.any (fun T => P.all (fun w=>T.contains w))
def localValid (k : ℕ) (Q : List W) (D : Batch) := Q.sublists.all fun P =>
  (!(decide (P.length≤k+1) && (mask P == BitVec.allOnes 55)) || covered D P) &&
  (!(decide (P.length≤k)) || (candidates Q).all fun z => !(mask (z::P) == BitVec.allOnes 55) || covered D (z::P))
private theorem consume {D : Batch} {P k} (cov : covered D P=true) (no : ∀ T∈D,¬Prog T.toFinset k) (prog : Prog P.toFinset k) : False := by
  obtain ⟨T,ht,sub⟩ := List.any_eq_true.mp cov; apply no _ ht; apply mono prog; intro w hw
  simpa using List.all_eq_true.mp sub w (by simpa using hw)
private theorem extract {Z : List W} {k} (p : Prog Z.toFinset k) : ∃ R ∈ Z.sublists,R.length≤k+1 ∧ mask R=BitVec.allOnes 55 ∧ Prog R.toFinset k := by
  obtain ⟨T,sub,sz,pr⟩ := sparse p
  let R := Z.dedup.filter fun w=>decide (w∈T)
  have eqT : R.toFinset=T := by ext w; simp [R]; exact fun h => (show w∈Z by simpa using sub h)
  refine ⟨R,List.mem_sublists.mpr (List.filter_sublist.trans (List.dedup_sublist _)),?_,masked (eqT.symm ▸ pr),eqT.symm ▸ pr⟩
  rw [← List.toFinset_card_of_nodup (l:=R) ((List.nodup_dedup Z).filter _),eqT]; exact sz
theorem localSound (k : Nat) (Q : List W) (D : Batch) (v : localValid k Q D=true) (no : ∀ T∈D,¬Prog T.toFinset k) : ¬Prog Q.toFinset (k+1) := by
  have ok := List.all_eq_true.mp v
  have old (R : List W) (hr : R∈Q.sublists) (len : R.length≤k+1) (ms : mask R=BitVec.allOnes 55) (pr : Prog R.toFinset k) : False := by
    have c := ok _ hr; simp only [Bool.and_eq_true] at c; have c' := c.1; simp [ms,len] at c'; exact consume c' no pr
  intro p; generalize eq : Q.toFinset=S at p; cases p with
  | done h => subst S; obtain ⟨R,hr,len,ms,pr⟩ := extract (k:=k) (Z:=Q) (.done h); exact old _ hr len ms pr
  | idle p => subst S; obtain ⟨R,hr,len,ms,pr⟩ := extract p; exact old _ hr len ms pr
  | @step _ _ a b o ma mb p =>
    subst S; let z := run o a b
    have cz := candidate Q o (by simpa using ma) (by simpa using mb)
    obtain ⟨R,hr,len,ms,pr⟩ := extract (Z:=z::Q) (by simpa using p)
    have sub := List.mem_sublists.mp hr
    cases sub with
    | cons _ tail => exact old _ (List.mem_sublists.mpr tail) len ms pr
    | @cons_cons R _ _ tail =>
      have c := ok _ (List.mem_sublists.mpr tail); simp only [Bool.and_eq_true] at c; have c' := c.2
      simp only [List.length_cons] at len; have lr : R.length≤k := by omega
      simp only [decide_eq_true lr,Bool.not_true,Bool.false_or] at c'
      have hz := List.all_eq_true.mp c' _ cz; change mask (run o a b::R)=BitVec.allOnes 55 at ms
      simp only [ms,beq_self_eq_true,Bool.not_true,Bool.false_or] at hz; exact consume hz no pr
end CoreFour11065Check

namespace Cert11065
open CoreFour11065Check
private theorem nilSafe (k : Nat) : ∀ Q∈([] : Batch), ¬Prog Q.toFinset k := by simp
private theorem consSafe {k : Nat} {Q : List W} {L : Batch} (a : ¬Prog Q.toFinset k) (b : ∀ T∈L, ¬Prog T.toFinset k) : ∀ T∈Q::L, ¬Prog T.toFinset k := by intro T m; rcases List.mem_cons.mp m with rfl|m; exact a; exact b _ m
private def w0 : W := (0,0)
private def w1 : W := (17600780175361,4192256)
private def w2 : W := (17600780175361,8585740288)
private def w3 : W := (35201560350722,4192256)
private def w4 : W := (35201560350722,17583596109824)
private def w5 : W := (70403120701444,8585740288)
private def w6 : W := (70403120701444,17583596109824)
private def w7 : W := (158407021578249,0)
private def w8 : W := (176007801753610,0)
private def w9 : W := (193608581928971,4192256)
private def w10 : W := (211209362104332,0)
private def w11 : W := (228810142279693,8585740288)
private def w12 : W := (246410922455054,17583596109824)
private def w13 : W := (264011702630415,8589932544)
private def w14 : W := (264011702630415,17583600302080)
private def w15 : W := (264011702630415,17592181850112)
private def w16 : W := (264011702630415,17592186042368)
private def w17 : W := (281612482805776,4192256)
private def w18 : W := (281612482805776,36011204832919552)
private def w19 : W := (475221064734747,4192256)
private def w20 : W := (563224965611552,8585740288)
private def w21 : W := (563224965611552,36011204832919552)
private def w22 : W := (792035107891245,8585740288)
private def w23 : W := (1144050711398465,0)
private def w24 : W := (1408062414028880,0)
private def w25 : W := (1425663194204241,4192256)
private def w26 : W := (1460864754554963,4192256)
private def w27 : W := (1601670995957851,4192256)
private def w28 : W := (1689674896834656,0)
private def w29 : W := (1707275677010017,8585740288)
private def w30 : W := (1777678797711461,8585740288)
private def w31 : W := (1918485039114349,8585740288)
private def w32 : W := (1971287379640432,36011204832919552)
private def w33 : W := (1988888159815793,8589932544)
private def w34 : W := (1988888159815793,36011204837111808)
private def w35 : W := (1988888159815793,36011213418659840)
private def w36 : W := (1988888159815793,36011213422852096)
private def w37 : W := (2217698302095486,36028788429029376)
private def w38 : W := (2252899862446208,17583596109824)
private def w39 : W := (2252899862446208,36011204832919552)
private def w40 : W := (2499310784901262,17583596109824)
private def w41 : W := (4224187242086640,36011204832919552)
private def w42 : W := (4541001285243138,0)
private def w43 : W := (4787412207698192,0)
private def w44 : W := (4822613768048914,4192256)
private def w45 : W := (4840214548224275,4192256)
private def w46 : W := (4981020789627163,4192256)
private def w47 : W := (5966664479447379,4192256)
private def w48 : W := (6107470720850267,4192256)
private def w49 : W := (6758699587338624,0)
private def w50 : W := (6793901147689346,17583596109824)
private def w51 : W := (6864304268390790,17583596109824)
private def w52 : W := (7005110509793678,17583596109824)
private def w53 : W := (7040312070144400,36011204832919552)
private def w54 : W := (7075513630495122,17583600302080)
private def w55 : W := (7075513630495122,36011204837111808)
private def w56 : W := (7075513630495122,36028788429029376)
private def w57 : W := (7075513630495122,36028788433221632)
private def w58 : W := (7269122212424093,36011213418659840)
private def w59 : W := (7603537035755952,36011204832919552)
private def w60 : W := (8501176824699363,17592181850112)
private def w61 : W := (8729986966979056,36011204832919552)
private def w62 : W := (9082002570486276,0)
private def w63 : W := (9574824415396384,0)
private def w64 : W := (9645227536097828,8585740288)
private def w65 : W := (9662828316273189,8585740288)
private def w66 : W := (9803634557676077,8585740288)
private def w67 : W := (10789278247496293,8585740288)
private def w68 : W := (10930084488899181,8585740288)
private def w69 : W := (11264499312231040,0)
private def w70 : W := (11334902432932484,17583596109824)
private def w71 : W := (11370103993283206,17583596109824)
private def w72 : W := (11510910234686094,17583596109824)
private def w73 : W := (11827724277842592,36011204832919552)
private def w74 : W := (11898127398544036,17592181850112)
private def w75 : W := (11898127398544036,36011213418659840)
private def w76 : W := (11898127398544036,36028788429029376)
private def w77 : W := (11898127398544036,36028797014769664)
private def w78 : W := (12021332859771563,36011204837111808)
private def w79 : W := (12109336760648368,36011204832919552)
private def w80 : W := (12760565627136725,17583600302080)
private def w81 : W := (13235786691871472,36011204832919552)
private def w82 : W := (14467841304146742,8589932544)
private def w83 : W := (15875903718175622,17583596109824)
private def w84 : W := (16016709959578510,17583596109824)
private def w85 : W := (16615136485540784,36011204832919552)
private def w86 : W := (17741586416763888,36011204832919552)
private def w87 : W := (18164005140972552,0)
private def w88 : W := (19149648830792768,0)
private def w89 : W := (19308055852371017,0)
private def w90 : W := (19343257412721739,4192256)
private def w91 : W := (19378458973072461,8585740288)
private def w92 : W := (19589668335176793,4192256)
private def w93 : W := (19624869895527515,4192256)
private def w94 : W := (19871280817982569,8585740288)
private def w95 : W := (19941683938684013,8585740288)
private def w96 : W := (22528998624462080,0)
private def w97 : W := (22705006426215690,0)
private def w98 : W := (22722607206391051,4192256)
private def w99 : W := (22775409546917134,17583596109824)
private def w100 : W := (22986618909021466,4192256)
private def w101 : W := (23004219689196827,4192256)
private def w102 : W := (23849057137614155,0)
private def w103 : W := (23937061038490960,0)
private def w104 : W := (23954661818666321,4192256)
private def w105 : W := (23972262598841682,4192256)
private def w106 : W := (23989863379017043,4192256)
private def w107 : W := (24095468060069209,0)
private def w108 : W := (24113068840244570,0)
private def w109 : W := (24130669620419931,0)
private def w110 : W := (24130669620419931,4192256)
private def w111 : W := (24201072741121375,4192256)
private def w112 : W := (24201072741121375,8589932544)
private def w113 : W := (24201072741121375,17583600302080)
private def w114 : W := (24500286004102512,36011204832919552)
private def w115 : W := (24693894586031483,4192256)
private def w116 : W := (24693894586031483,8589932544)
private def w117 : W := (24693894586031483,36011204837111808)
private def w118 : W := (24957906288661898,17583596109824)
private def w119 : W := (25028309409363342,17583596109824)
private def w120 : W := (26189960900937168,36011204832919552)
private def w121 : W := (26383569482866139,4192256)
private def w122 : W := (26383569482866139,17583600302080)
private def w123 : W := (26383569482866139,36011204837111808)
private def w124 : W := (26753185866548720,36011204832919552)
private def w125 : W := (27034798349354496,0)
private def w126 : W := (27246007711458828,0)
private def w127 : W := (27263608491634189,8585740288)
private def w128 : W := (27281209271809550,17583596109824)
private def w129 : W := (27809232677070380,8585740288)
private def w130 : W := (27826833457245741,8585740288)
private def w131 : W := (28390058422857293,0)
private def w132 : W := (28724473246189152,0)
private def w133 : W := (28742074026364513,8585740288)
private def w134 : W := (28794876366890596,8585740288)
private def w135 : W := (28812477147065957,8585740288)
private def w136 : W := (28882880267767401,0)
private def w137 : W := (28935682608293484,0)
private def w138 : W := (28953283388468845,0)
private def w139 : W := (28953283388468845,8585740288)
private def w140 : W := (28988484948819567,8585740288)
private def w141 : W := (28988484948819567,8589932544)
private def w142 : W := (28988484948819567,17592181850112)
private def w143 : W := (29006085728994928,36011204832919552)
private def w144 : W := (29234895871274621,8585740288)
private def w145 : W := (29234895871274621,8589932544)
private def w146 : W := (29234895871274621,36011213418659840)
private def w147 : W := (29498907573905036,17583596109824)
private def w148 : W := (29534109134255758,17583596109824)
private def w149 : W := (30977373108635360,36011204832919552)
private def w150 : W := (31206183250915053,8585740288)
private def w151 : W := (31206183250915053,17592181850112)
private def w152 : W := (31206183250915053,36011213418659840)
private def w153 : W := (31258985591441136,36011204832919552)
private def w154 : W := (31787008996701966,0)
private def w155 : W := (33142269070204763,4192256)
private def w156 : W := (33212672190906207,4192256)
private def w157 : W := (33459083113361261,8585740288)
private def w158 : W := (33494284673711983,8585740288)
private def w159 : W := (33511885453887344,0)
private def w160 : W := (33705494035816315,4192256)
private def w161 : W := (33740695596167037,8585740288)
private def w162 : W := (33775897156517759,4192256)
private def w163 : W := (33775897156517759,8585740288)
private def w164 : W := (33775897156517759,8589932544)
private def w165 : W := (33793497936693120,0)
private def w166 : W := (33828699497043842,17583596109824)
private def w167 : W := (33863901057394564,17583596109824)
private def w168 : W := (33899102617745286,17583596109824)
private def w169 : W := (33969505738446730,0)
private def w170 : W := (34004707298797452,0)
private def w171 : W := (34039908859148174,0)
private def w172 : W := (34039908859148174,17583596109824)
private def w173 : W := (34057509639323535,17583596109824)
private def w174 : W := (34057509639323535,17583600302080)
private def w175 : W := (34057509639323535,17592181850112)
private def w176 : W := (34075110419498896,36011204832919552)
private def w177 : W := (34321521341953950,17583596109824)
private def w178 : W := (34321521341953950,17583600302080)
private def w179 : W := (34321521341953950,36028788429029376)
private def w180 : W := (34356722902304672,36011204832919552)
private def w181 : W := (34603133824759726,17583596109824)
private def w182 : W := (34603133824759726,17592181850112)
private def w183 : W := (34603133824759726,36028788429029376)
private def w184 : W := (34638335385110448,36011204832919552)
private def w185 : W := (35166358790371278,17583596109824)
private def w186 : W := (35183959570546639,17583596109824)
private def w187 : W := (35201560350722000,0)
private def w188 : W := (35395168932650971,4192256)
private def w189 : W := (35447971273177054,17583596109824)
private def w190 : W := (35465572053352415,4192256)
private def w191 : W := (35465572053352415,17583596109824)
private def w192 : W := (35465572053352415,17583600302080)
private def w193 : W := (35483172833527776,0)
private def w194 : W := (35711982975807469,8585740288)
private def w195 : W := (35729583755982830,17583596109824)
private def w196 : W := (35747184536158191,8585740288)
private def w197 : W := (35747184536158191,17583596109824)
private def w198 : W := (35747184536158191,17592181850112)
private def w199 : W := (35764785316333552,0)
private def w200 : W := (35764785316333552,36011204832919552)
private def w201 : W := (35782386096508913,36011204832919552)
private def w202 : W := (35782386096508913,36011204837111808)
private def w203 : W := (35782386096508913,36011213418659840)
private def w204 : W := (35799986876684274,36011204832919552)
private def w205 : W := (35799986876684274,36011204837111808)
private def w206 : W := (35799986876684274,36028788429029376)
private def w207 : W := (35835188437034996,36011204832919552)
private def w208 : W := (35835188437034996,36011213418659840)
private def w209 : W := (35835188437034996,36028788429029376)
private def w210 : W := (35905591557736440,36011204832919552)
private def w211 : W := (35923192337911801,36011204832919552)
private def w212 : W := (35940793118087162,36011204832919552)
private def w213 : W := (35958393898262523,4192256)
private def w214 : W := (35958393898262523,36011204832919552)
private def w215 : W := (35958393898262523,36011204837111808)
private def w216 : W := (35975994678437884,36011204832919552)
private def w217 : W := (35993595458613245,8585740288)
private def w218 : W := (35993595458613245,36011204832919552)
private def w219 : W := (35993595458613245,36011213418659840)
private def w220 : W := (36011196238788606,17583596109824)
private def w221 : W := (36011196238788606,36011204832919552)
private def w222 : W := (36011196238788606,36028788429029376)
private def w223 : W := (36028797018963967,17592186042368)
private def w224 : W := (36028797018963967,36011213422852096)
private def w225 : W := (36028797018963967,36028788433221632)
private def w226 : W := (36028797018963967,36028797014769664)
private def q0 : List W := [w0,w9,w110,w139,w172,w200]
private def q1 : List W := [w0,w11,w110,w139,w172,w200]
private def q2 : List W := [w0,w12,w110,w139,w172,w200]
private def q3 : List W := [w0,w25,w110,w139,w172,w200]
private def q4 : List W := [w0,w27,w139,w172,w200]
private def q5 : List W := [w0,w29,w110,w139,w172,w200]
private def q6 : List W := [w0,w31,w110,w172,w200]
private def q7 : List W := [w0,w32,w110,w139,w172,w200]
private def q8 : List W := [w0,w44,w110,w139,w172,w200]
private def q9 : List W := [w0,w46,w139,w172,w200]
private def q10 : List W := [w0,w47,w139,w172,w200]
private def q11 : List W := [w0,w50,w110,w139,w172,w200]
private def q12 : List W := [w0,w52,w110,w139,w200]
private def q13 : List W := [w0,w53,w110,w139,w172,w200]
private def q14 : List W := [w0,w61,w110,w139,w172]
private def q15 : List W := [w0,w64,w110,w139,w172,w200]
private def q16 : List W := [w0,w66,w110,w172,w200]
private def q17 : List W := [w0,w67,w110,w172,w200]
private def q18 : List W := [w0,w70,w110,w139,w172,w200]
private def q19 : List W := [w0,w72,w110,w139,w200]
private def q20 : List W := [w0,w73,w110,w139,w172,w200]
private def q21 : List W := [w0,w81,w110,w139,w172]
private def q22 : List W := [w0,w83,w110,w139,w200]
private def q23 : List W := [w0,w85,w110,w139,w172]
private def q24 : List W := [w0,w89,w110,w139,w172,w200]
private def q25 : List W := [w0,w89,w164,w172,w200]
private def q26 : List W := [w0,w97,w110,w139,w172,w200]
private def q27 : List W := [w0,w97,w139,w192,w200]
private def q28 : List W := [w0,w103,w110,w139,w172,w200]
private def q29 : List W := [w0,w103,w139,w172,w215]
private def q30 : List W := [w0,w110,w126,w139,w172,w200]
private def q31 : List W := [w0,w110,w126,w198,w200]
private def q32 : List W := [w0,w110,w132,w139,w172,w200]
private def q33 : List W := [w0,w110,w132,w172,w219]
private def q34 : List W := [w0,w110,w139,w164,w172,w200]
private def q35 : List W := [w0,w110,w139,w165,w172,w200]
private def q36 : List W := [w0,w110,w139,w165,w222]
private def q37 : List W := [w0,w110,w139,w172,w192,w200]
private def q38 : List W := [w0,w110,w139,w172,w198,w200]
private def q39 : List W := [w0,w110,w139,w172,w200]
private def q40 : List W := [w0,w110,w139,w172,w200,w215]
private def q41 : List W := [w0,w110,w139,w172,w200,w219]
private def q42 : List W := [w0,w110,w139,w172,w200,w222]
private def q43 : List W := [w0,w110,w139,w172,w211]
private def q44 : List W := [w0,w110,w139,w172,w212]
private def q45 : List W := [w0,w110,w139,w172,w216]
private def q46 : List W := [w0,w110,w139,w186,w200]
private def q47 : List W := [w0,w110,w139,w189,w200]
private def q48 : List W := [w0,w110,w139,w195,w200]
private def q49 : List W := [w0,w110,w158,w172,w200]
private def q50 : List W := [w0,w110,w161,w172,w200]
private def q51 : List W := [w0,w110,w172,w194,w200]
private def q52 : List W := [w0,w110,w194,w222]
private def q53 : List W := [w0,w110,w195,w219]
private def q54 : List W := [w0,w110,w198,w216]
private def q55 : List W := [w0,w139,w156,w172,w200]
private def q56 : List W := [w0,w139,w160,w172,w200]
private def q57 : List W := [w0,w139,w172,w188,w200]
private def q58 : List W := [w0,w139,w188,w222]
private def q59 : List W := [w0,w139,w189,w215]
private def q60 : List W := [w0,w139,w192,w212]
private def q61 : List W := [w0,w156,w198,w200]
private def q62 : List W := [w0,w158,w192,w200]
private def q63 : List W := [w0,w160,w172,w219]
private def q64 : List W := [w0,w161,w172,w215]
private def q65 : List W := [w0,w164,w172,w211]
private def q66 : List W := [w0,w164,w186,w200]
private def q67 : List W := [w1,w110,w139,w172,w200]
private def q68 : List W := [w2,w110,w139,w172,w200]
private def q69 : List W := [w3,w110,w139,w172,w200]
private def q70 : List W := [w4,w110,w139,w172,w200]
private def q71 : List W := [w5,w110,w139,w172,w200]
private def q72 : List W := [w6,w110,w139,w172,w200]
private def q73 : List W := [w7,w110,w139,w172,w200]
private def q74 : List W := [w7,w164,w172,w200]
private def q75 : List W := [w8,w110,w139,w172,w200]
private def q76 : List W := [w8,w139,w192,w200]
private def q77 : List W := [w9,w25,w139,w172,w200]
private def q78 : List W := [w9,w44,w139,w172,w200]
private def q79 : List W := [w9,w73,w110,w139,w172]
private def q80 : List W := [w9,w73,w139,w172,w200]
private def q81 : List W := [w9,w103,w139,w172,w200]
private def q82 : List W := [w9,w110,w139,w172,w200]
private def q83 : List W := [w9,w110,w139,w172,w215]
private def q84 : List W := [w9,w139,w164,w172,w200]
private def q85 : List W := [w9,w139,w172,w192,w200]
private def q86 : List W := [w9,w139,w189,w200]
private def q87 : List W := [w9,w161,w172,w200]
private def q88 : List W := [w10,w110,w139,w172,w200]
private def q89 : List W := [w10,w110,w198,w200]
private def q90 : List W := [w11,w29,w110,w172,w200]
private def q91 : List W := [w11,w53,w110,w139,w172]
private def q92 : List W := [w11,w53,w110,w172,w200]
private def q93 : List W := [w11,w64,w110,w172,w200]
private def q94 : List W := [w11,w110,w132,w172,w200]
private def q95 : List W := [w11,w110,w139,w172,w200]
private def q96 : List W := [w11,w110,w139,w172,w219]
private def q97 : List W := [w11,w110,w164,w172,w200]
private def q98 : List W := [w11,w110,w172,w198,w200]
private def q99 : List W := [w11,w110,w195,w200]
private def q100 : List W := [w11,w160,w172,w200]
private def q101 : List W := [w12,w32,w110,w139,w172]
private def q102 : List W := [w12,w32,w110,w139,w200]
private def q103 : List W := [w12,w50,w110,w139,w200]
private def q104 : List W := [w12,w70,w110,w139,w200]
private def q105 : List W := [w12,w110,w139,w165,w200]
private def q106 : List W := [w12,w110,w139,w172,w200]
private def q107 : List W := [w12,w110,w139,w172,w222]
private def q108 : List W := [w12,w110,w139,w192,w200]
private def q109 : List W := [w12,w110,w139,w198,w200]
private def q110 : List W := [w12,w110,w194,w200]
private def q111 : List W := [w12,w139,w188,w200]
private def q112 : List W := [w13,w110,w139,w172,w200]
private def q113 : List W := [w14,w110,w139,w172,w200]
private def q114 : List W := [w15,w110,w139,w172,w200]
private def q115 : List W := [w16,w110,w139,w172]
private def q116 : List W := [w17,w110,w139,w172,w200]
private def q117 : List W := [w18,w110,w139,w172,w200]
private def q118 : List W := [w19,w139,w172,w200]
private def q119 : List W := [w20,w110,w139,w172,w200]
private def q120 : List W := [w21,w110,w139,w172,w200]
private def q121 : List W := [w22,w110,w172,w200]
private def q122 : List W := [w23,w110,w139,w172,w200]
private def q123 : List W := [w23,w164,w172,w200]
private def q124 : List W := [w24,w110,w139,w172,w200]
private def q125 : List W := [w24,w139,w172,w215]
private def q126 : List W := [w25,w44,w139,w172,w200]
private def q127 : List W := [w25,w70,w110,w139,w200]
private def q128 : List W := [w25,w70,w139,w172,w200]
private def q129 : List W := [w25,w97,w139,w172,w200]
private def q130 : List W := [w25,w110,w139,w172,w200]
private def q131 : List W := [w25,w110,w139,w192,w200]
private def q132 : List W := [w25,w139,w164,w172,w200]
private def q133 : List W := [w25,w139,w172,w200,w215]
private def q134 : List W := [w25,w139,w172,w212]
private def q135 : List W := [w25,w158,w172,w200]
private def q136 : List W := [w26,w139,w172,w200]
private def q137 : List W := [w27,w31,w172,w200]
private def q138 : List W := [w27,w110,w139,w172,w200]
private def q139 : List W := [w27,w139,w165,w172,w200]
private def q140 : List W := [w27,w139,w165,w222]
private def q141 : List W := [w27,w139,w172,w200]
private def q142 : List W := [w27,w172,w194,w200]
private def q143 : List W := [w27,w194,w222]
private def q144 : List W := [w28,w110,w139,w172,w200]
private def q145 : List W := [w28,w110,w172,w219]
private def q146 : List W := [w29,w50,w110,w139,w200]
private def q147 : List W := [w29,w50,w110,w172,w200]
private def q148 : List W := [w29,w64,w110,w172,w200]
private def q149 : List W := [w29,w110,w126,w172,w200]
private def q150 : List W := [w29,w110,w139,w172,w200]
private def q151 : List W := [w29,w110,w139,w198,w200]
private def q152 : List W := [w29,w110,w164,w172,w200]
private def q153 : List W := [w29,w110,w172,w200,w219]
private def q154 : List W := [w29,w110,w172,w216]
private def q155 : List W := [w29,w156,w172,w200]
private def q156 : List W := [w30,w110,w172,w200]
private def q157 : List W := [w31,w110,w139,w172,w200]
private def q158 : List W := [w31,w110,w165,w172,w200]
private def q159 : List W := [w31,w110,w165,w222]
private def q160 : List W := [w31,w110,w172,w200]
private def q161 : List W := [w31,w172,w188,w200]
private def q162 : List W := [w31,w188,w222]
private def q163 : List W := [w32,w53,w110,w139,w172]
private def q164 : List W := [w32,w73,w110,w139,w172]
private def q165 : List W := [w32,w110,w139,w165,w172]
private def q166 : List W := [w32,w110,w139,w172,w200]
private def q167 : List W := [w32,w110,w139,w172,w215]
private def q168 : List W := [w32,w110,w139,w172,w219]
private def q169 : List W := [w32,w110,w139,w200,w222]
private def q170 : List W := [w32,w110,w172,w194]
private def q171 : List W := [w32,w139,w172,w188]
private def q172 : List W := [w33,w110,w139,w172,w200]
private def q173 : List W := [w34,w110,w139,w172,w200]
private def q174 : List W := [w35,w110,w139,w172,w200]
private def q175 : List W := [w36,w110,w139,w200]
private def q176 : List W := [w37,w110,w139,w165]
private def q177 : List W := [w37,w110,w139,w172]
private def q178 : List W := [w37,w110,w139,w200]
private def q179 : List W := [w37,w110,w139,w222]
private def q180 : List W := [w38,w110,w139,w172,w200]
private def q181 : List W := [w39,w110,w139,w172,w200]
private def q182 : List W := [w40,w110,w139,w200]
private def q183 : List W := [w41,w110,w139,w172]
private def q184 : List W := [w42,w110,w139,w172,w200]
private def q185 : List W := [w42,w139,w192,w200]
private def q186 : List W := [w43,w110,w139,w172,w200]
private def q187 : List W := [w43,w139,w172,w215]
private def q188 : List W := [w44,w64,w110,w172,w200]
private def q189 : List W := [w44,w64,w139,w172,w200]
private def q190 : List W := [w44,w89,w139,w172,w200]
private def q191 : List W := [w44,w110,w139,w172,w200]
private def q192 : List W := [w44,w110,w164,w172,w200]
private def q193 : List W := [w44,w139,w172,w192,w200]
private def q194 : List W := [w44,w139,w172,w200,w215]
private def q195 : List W := [w44,w139,w172,w211]
private def q196 : List W := [w44,w139,w186,w200]
private def q197 : List W := [w45,w139,w172,w200]
private def q198 : List W := [w46,w52,w139,w200]
private def q199 : List W := [w46,w110,w139,w172,w200]
private def q200 : List W := [w46,w132,w139,w172,w200]
private def q201 : List W := [w46,w132,w172,w219]
private def q202 : List W := [w46,w139,w172,w200]
private def q203 : List W := [w46,w139,w195,w200]
private def q204 : List W := [w46,w195,w219]
private def q205 : List W := [w47,w61,w139,w172]
private def q206 : List W := [w47,w110,w139,w172,w200]
private def q207 : List W := [w47,w126,w139,w172,w200]
private def q208 : List W := [w47,w126,w198,w200]
private def q209 : List W := [w47,w139,w172,w200]
private def q210 : List W := [w47,w139,w172,w216]
private def q211 : List W := [w47,w198,w216]
private def q212 : List W := [w48,w139,w172,w200]
private def q213 : List W := [w49,w110,w139,w172,w200]
private def q214 : List W := [w49,w110,w139,w222]
private def q215 : List W := [w50,w70,w110,w139,w200]
private def q216 : List W := [w50,w110,w126,w139,w200]
private def q217 : List W := [w50,w110,w139,w172,w200]
private def q218 : List W := [w50,w110,w139,w192,w200]
private def q219 : List W := [w50,w110,w139,w200,w222]
private def q220 : List W := [w50,w110,w139,w216]
private def q221 : List W := [w50,w110,w172,w198,w200]
private def q222 : List W := [w50,w139,w156,w200]
private def q223 : List W := [w51,w110,w139,w200]
private def q224 : List W := [w52,w110,w132,w139,w200]
private def q225 : List W := [w52,w110,w132,w219]
private def q226 : List W := [w52,w110,w139,w172,w200]
private def q227 : List W := [w52,w110,w139,w200]
private def q228 : List W := [w52,w139,w160,w200]
private def q229 : List W := [w52,w160,w219]
private def q230 : List W := [w53,w73,w110,w139,w172]
private def q231 : List W := [w53,w110,w132,w139,w172]
private def q232 : List W := [w53,w110,w139,w172,w200]
private def q233 : List W := [w53,w110,w139,w172,w215]
private def q234 : List W := [w53,w110,w139,w172,w222]
private def q235 : List W := [w53,w110,w139,w195]
private def q236 : List W := [w53,w110,w172,w200,w219]
private def q237 : List W := [w53,w139,w160,w172]
private def q238 : List W := [w54,w110,w139,w172,w200]
private def q239 : List W := [w55,w110,w139,w172,w200]
private def q240 : List W := [w56,w110,w139,w172,w200]
private def q241 : List W := [w57,w110,w172,w200]
private def q242 : List W := [w58,w110,w132,w172]
private def q243 : List W := [w58,w110,w139,w172]
private def q244 : List W := [w58,w110,w172,w200]
private def q245 : List W := [w58,w110,w172,w219]
private def q246 : List W := [w59,w110,w139,w172]
private def q247 : List W := [w60,w110,w126,w200]
private def q248 : List W := [w60,w110,w139,w200]
private def q249 : List W := [w60,w110,w172,w200]
private def q250 : List W := [w60,w110,w198,w200]
private def q251 : List W := [w61,w110,w126,w139,w172]
private def q252 : List W := [w61,w110,w126,w198]
private def q253 : List W := [w61,w110,w139,w172]
private def q254 : List W := [w61,w110,w139,w172,w200]
private def q255 : List W := [w61,w139,w156,w172]
private def q256 : List W := [w61,w156,w198]
private def q257 : List W := [w62,w110,w139,w172,w200]
private def q258 : List W := [w62,w110,w198,w200]
private def q259 : List W := [w63,w110,w139,w172,w200]
private def q260 : List W := [w63,w110,w172,w219]
private def q261 : List W := [w64,w89,w110,w172,w200]
private def q262 : List W := [w64,w110,w139,w172,w200]
private def q263 : List W := [w64,w110,w172,w198,w200]
private def q264 : List W := [w64,w110,w172,w200,w219]
private def q265 : List W := [w64,w110,w172,w211]
private def q266 : List W := [w64,w110,w186,w200]
private def q267 : List W := [w64,w139,w164,w172,w200]
private def q268 : List W := [w65,w110,w172,w200]
private def q269 : List W := [w66,w72,w110,w200]
private def q270 : List W := [w66,w103,w110,w172,w200]
private def q271 : List W := [w66,w103,w172,w215]
private def q272 : List W := [w66,w110,w139,w172,w200]
private def q273 : List W := [w66,w110,w172,w200]
private def q274 : List W := [w66,w110,w189,w200]
private def q275 : List W := [w66,w189,w215]
private def q276 : List W := [w67,w81,w110,w172]
private def q277 : List W := [w67,w97,w110,w172,w200]
private def q278 : List W := [w67,w97,w192,w200]
private def q279 : List W := [w67,w110,w139,w172,w200]
private def q280 : List W := [w67,w110,w172,w200]
private def q281 : List W := [w67,w110,w172,w212]
private def q282 : List W := [w67,w192,w212]
private def q283 : List W := [w68,w110,w172,w200]
private def q284 : List W := [w69,w110,w139,w172,w200]
private def q285 : List W := [w69,w110,w139,w222]
private def q286 : List W := [w70,w97,w110,w139,w200]
private def q287 : List W := [w70,w110,w139,w172,w200]
private def q288 : List W := [w70,w110,w139,w198,w200]
private def q289 : List W := [w70,w110,w139,w200,w222]
private def q290 : List W := [w70,w110,w139,w212]
private def q291 : List W := [w70,w110,w158,w200]
private def q292 : List W := [w70,w139,w172,w192,w200]
private def q293 : List W := [w71,w110,w139,w200]
private def q294 : List W := [w72,w103,w110,w139,w200]
private def q295 : List W := [w72,w103,w139,w215]
private def q296 : List W := [w72,w110,w139,w172,w200]
private def q297 : List W := [w72,w110,w139,w200]
private def q298 : List W := [w72,w110,w161,w200]
private def q299 : List W := [w72,w161,w215]
private def q300 : List W := [w73,w103,w110,w139,w172]
private def q301 : List W := [w73,w110,w139,w172,w200]
private def q302 : List W := [w73,w110,w139,w172,w219]
private def q303 : List W := [w73,w110,w139,w172,w222]
private def q304 : List W := [w73,w110,w139,w189]
private def q305 : List W := [w73,w110,w161,w172]
private def q306 : List W := [w73,w139,w172,w200,w215]
private def q307 : List W := [w74,w110,w139,w172,w200]
private def q308 : List W := [w75,w110,w139,w172,w200]
private def q309 : List W := [w76,w110,w139,w172,w200]
private def q310 : List W := [w77,w139,w172,w200]
private def q311 : List W := [w78,w103,w139,w172]
private def q312 : List W := [w78,w110,w139,w172]
private def q313 : List W := [w78,w139,w172,w200]
private def q314 : List W := [w78,w139,w172,w215]
private def q315 : List W := [w79,w110,w139,w172]
private def q316 : List W := [w80,w97,w139,w200]
private def q317 : List W := [w80,w110,w139,w200]
private def q318 : List W := [w80,w139,w172,w200]
private def q319 : List W := [w80,w139,w192,w200]
private def q320 : List W := [w81,w97,w110,w139,w172]
private def q321 : List W := [w81,w97,w139,w192]
private def q322 : List W := [w81,w110,w139,w172]
private def q323 : List W := [w81,w110,w139,w172,w200]
private def q324 : List W := [w81,w110,w158,w172]
private def q325 : List W := [w81,w158,w192]
private def q326 : List W := [w82,w89,w172,w200]
private def q327 : List W := [w82,w110,w172,w200]
private def q328 : List W := [w82,w139,w172,w200]
private def q329 : List W := [w82,w164,w172,w200]
private def q330 : List W := [w83,w85,w110,w139]
private def q331 : List W := [w83,w89,w110,w139,w200]
private def q332 : List W := [w83,w89,w164,w200]
private def q333 : List W := [w83,w110,w139,w172,w200]
private def q334 : List W := [w83,w110,w139,w200]
private def q335 : List W := [w83,w110,w139,w211]
private def q336 : List W := [w83,w164,w211]
private def q337 : List W := [w84,w110,w139,w200]
private def q338 : List W := [w85,w89,w110,w139,w172]
private def q339 : List W := [w85,w89,w164,w172]
private def q340 : List W := [w85,w110,w139,w172]
private def q341 : List W := [w85,w110,w139,w172,w200]
private def q342 : List W := [w85,w110,w139,w186]
private def q343 : List W := [w85,w164,w186]
private def q344 : List W := [w86,w110,w139,w172]
private def q345 : List W := [w87,w110,w139,w172,w200]
private def q346 : List W := [w88,w110,w139,w172,w200]
private def q347 : List W := [w89,w110,w139,w172,w200]
private def q348 : List W := [w89,w110,w139,w172,w211]
private def q349 : List W := [w89,w110,w139,w186,w200]
private def q350 : List W := [w89,w110,w164,w172,w200]
private def q351 : List W := [w89,w139,w164,w172,w200]
private def q352 : List W := [w89,w164,w172,w200]
private def q353 : List W := [w89,w164,w172,w211]
private def q354 : List W := [w89,w164,w186,w200]
private def q355 : List W := [w90,w110,w139,w172,w200]
private def q356 : List W := [w91,w110,w139,w172,w200]
private def q357 : List W := [w92,w110,w139,w172,w200]
private def q358 : List W := [w93,w139,w172,w200]
private def q359 : List W := [w94,w110,w139,w172,w200]
private def q360 : List W := [w95,w110,w172,w200]
private def q361 : List W := [w96,w110,w139,w172,w200]
private def q362 : List W := [w97,w110,w139,w172,w200]
private def q363 : List W := [w97,w110,w139,w172,w212]
private def q364 : List W := [w97,w110,w139,w192,w200]
private def q365 : List W := [w97,w110,w158,w172,w200]
private def q366 : List W := [w97,w139,w172,w192,w200]
private def q367 : List W := [w97,w139,w192,w200]
private def q368 : List W := [w97,w139,w192,w212]
private def q369 : List W := [w97,w158,w192,w200]
private def q370 : List W := [w98,w110,w139,w172,w200]
private def q371 : List W := [w99,w110,w139,w172,w200]
private def q372 : List W := [w100,w110,w139,w172,w200]
private def q373 : List W := [w101,w139,w172,w200]
private def q374 : List W := [w102,w110,w139,w172,w200]
private def q375 : List W := [w102,w139,w192,w200]
private def q376 : List W := [w102,w164,w172,w200]
private def q377 : List W := [w103,w110,w139,w172,w200]
private def q378 : List W := [w103,w110,w139,w172,w215]
private def q379 : List W := [w103,w110,w139,w189,w200]
private def q380 : List W := [w103,w110,w161,w172,w200]
private def q381 : List W := [w103,w139,w172,w200,w215]
private def q382 : List W := [w103,w139,w172,w215]
private def q383 : List W := [w103,w139,w189,w215]
private def q384 : List W := [w103,w161,w172,w215]
private def q385 : List W := [w104,w110,w139,w172,w200]
private def q386 : List W := [w105,w110,w139,w172,w200]
private def q387 : List W := [w106,w139,w172,w200]
private def q388 : List W := [w107,w110,w139,w172,w200]
private def q389 : List W := [w107,w139,w172,w215]
private def q390 : List W := [w107,w164,w172,w200]
private def q391 : List W := [w108,w110,w139,w172,w200]
private def q392 : List W := [w108,w139,w172,w215]
private def q393 : List W := [w108,w139,w192,w200]
private def q394 : List W := [w109,w139,w172,w200]
private def q395 : List W := [w110,w112,w139,w172,w200]
private def q396 : List W := [w110,w113,w139,w172,w200]
private def q397 : List W := [w110,w114,w139,w172,w200]
private def q398 : List W := [w110,w116,w139,w172,w200]
private def q399 : List W := [w110,w117,w139,w172,w200]
private def q400 : List W := [w110,w118,w139,w172,w200]
private def q401 : List W := [w110,w119,w139,w200]
private def q402 : List W := [w110,w120,w139,w172,w200]
private def q403 : List W := [w110,w122,w139,w172,w200]
private def q404 : List W := [w110,w123,w139,w172,w200]
private def q405 : List W := [w110,w124,w139,w172]
private def q406 : List W := [w110,w125,w139,w172,w200]
private def q407 : List W := [w110,w126,w139,w172,w200]
private def q408 : List W := [w110,w126,w139,w172,w216]
private def q409 : List W := [w110,w126,w139,w198,w200]
private def q410 : List W := [w110,w126,w172,w198,w200]
private def q411 : List W := [w110,w126,w198,w200]
private def q412 : List W := [w110,w126,w198,w216]
private def q413 : List W := [w110,w127,w139,w172,w200]
private def q414 : List W := [w110,w128,w139,w172,w200]
private def q415 : List W := [w110,w129,w139,w172,w200]
private def q416 : List W := [w110,w130,w172,w200]
private def q417 : List W := [w110,w131,w139,w172,w200]
private def q418 : List W := [w110,w131,w198,w200]
private def q419 : List W := [w110,w132,w139,w172,w200]
private def q420 : List W := [w110,w132,w139,w172,w219]
private def q421 : List W := [w110,w132,w139,w195,w200]
private def q422 : List W := [w110,w132,w172,w200,w219]
private def q423 : List W := [w110,w132,w172,w219]
private def q424 : List W := [w110,w132,w195,w219]
private def q425 : List W := [w110,w133,w139,w172,w200]
private def q426 : List W := [w110,w134,w139,w172,w200]
private def q427 : List W := [w110,w135,w172,w200]
private def q428 : List W := [w110,w136,w139,w172,w200]
private def q429 : List W := [w110,w136,w172,w219]
private def q430 : List W := [w110,w137,w139,w172,w200]
private def q431 : List W := [w110,w137,w172,w219]
private def q432 : List W := [w110,w137,w198,w200]
private def q433 : List W := [w110,w138,w172,w200]
private def q434 : List W := [w110,w139,w141,w172,w200]
private def q435 : List W := [w110,w139,w142,w172,w200]
private def q436 : List W := [w110,w139,w143,w172,w200]
private def q437 : List W := [w110,w139,w145,w172,w200]
private def q438 : List W := [w110,w139,w146,w172,w200]
private def q439 : List W := [w110,w139,w147,w172,w200]
private def q440 : List W := [w110,w139,w148,w200]
private def q441 : List W := [w110,w139,w149,w172,w200]
private def q442 : List W := [w110,w139,w151,w172,w200]
private def q443 : List W := [w110,w139,w152,w172,w200]
private def q444 : List W := [w110,w139,w153,w172]
private def q445 : List W := [w110,w139,w154,w172,w200]
private def q446 : List W := [w110,w139,w156,w172,w200]
private def q447 : List W := [w110,w139,w158,w172,w200]
private def q448 : List W := [w110,w139,w159,w172,w200]
private def q449 : List W := [w110,w139,w160,w172,w200]
private def q450 : List W := [w110,w139,w161,w172,w200]
private def q451 : List W := [w110,w139,w164,w172,w200]
private def q452 : List W := [w110,w139,w165,w172,w200]
private def q453 : List W := [w110,w139,w165,w172,w222]
private def q454 : List W := [w110,w139,w165,w200,w222]
private def q455 : List W := [w110,w139,w165,w222]
private def q456 : List W := [w110,w139,w166,w172,w200]
private def q457 : List W := [w110,w139,w167,w172,w200]
private def q458 : List W := [w110,w139,w168,w200]
private def q459 : List W := [w110,w139,w169,w172,w200]
private def q460 : List W := [w110,w139,w169,w222]
private def q461 : List W := [w110,w139,w170,w172,w200]
private def q462 : List W := [w110,w139,w170,w222]
private def q463 : List W := [w110,w139,w171,w200]
private def q464 : List W := [w110,w139,w172,w174,w200]
private def q465 : List W := [w110,w139,w172,w175,w200]
private def q466 : List W := [w110,w139,w172,w176,w200]
private def q467 : List W := [w110,w139,w172,w178,w200]
private def q468 : List W := [w110,w139,w172,w179,w200]
private def q469 : List W := [w110,w139,w172,w180,w200]
private def q470 : List W := [w110,w139,w172,w182,w200]
private def q471 : List W := [w110,w139,w172,w183,w200]
private def q472 : List W := [w110,w139,w172,w184]
private def q473 : List W := [w110,w139,w172,w186,w200]
private def q474 : List W := [w110,w139,w172,w187,w200]
private def q475 : List W := [w110,w139,w172,w188,w200]
private def q476 : List W := [w110,w139,w172,w189,w200]
private def q477 : List W := [w110,w139,w172,w192,w200]
private def q478 : List W := [w110,w139,w172,w193,w200]
private def q479 : List W := [w110,w139,w172,w194,w200]
private def q480 : List W := [w110,w139,w172,w195,w200]
private def q481 : List W := [w110,w139,w172,w198,w200]
private def q482 : List W := [w110,w139,w172,w199]
private def q483 : List W := [w110,w139,w172,w200]
private def q484 : List W := [w110,w139,w172,w200,w202]
private def q485 : List W := [w110,w139,w172,w200,w203]
private def q486 : List W := [w110,w139,w172,w200,w205]
private def q487 : List W := [w110,w139,w172,w200,w206]
private def q488 : List W := [w110,w139,w172,w200,w208]
private def q489 : List W := [w110,w139,w172,w200,w209]
private def q490 : List W := [w110,w139,w172,w200,w211]
private def q491 : List W := [w110,w139,w172,w200,w212]
private def q492 : List W := [w110,w139,w172,w200,w215]
private def q493 : List W := [w110,w139,w172,w200,w216]
private def q494 : List W := [w110,w139,w172,w200,w219]
private def q495 : List W := [w110,w139,w172,w200,w222]
private def q496 : List W := [w110,w139,w172,w200,w223]
private def q497 : List W := [w110,w139,w172,w200,w224]
private def q498 : List W := [w110,w139,w172,w200,w225]
private def q499 : List W := [w110,w139,w172,w200,w226]
private def q500 : List W := [w110,w139,w172,w201]
private def q501 : List W := [w110,w139,w172,w204]
private def q502 : List W := [w110,w139,w172,w207]
private def q503 : List W := [w110,w139,w172,w210]
private def q504 : List W := [w110,w139,w172,w211]
private def q505 : List W := [w110,w139,w172,w212]
private def q506 : List W := [w110,w139,w172,w214]
private def q507 : List W := [w110,w139,w172,w215,w219]
private def q508 : List W := [w110,w139,w172,w215,w222]
private def q509 : List W := [w110,w139,w172,w216]
private def q510 : List W := [w110,w139,w172,w218]
private def q511 : List W := [w110,w139,w172,w219,w222]
private def q512 : List W := [w110,w139,w172,w221]
private def q513 : List W := [w110,w139,w173,w200]
private def q514 : List W := [w110,w139,w177,w200]
private def q515 : List W := [w110,w139,w181,w200]
private def q516 : List W := [w110,w139,w185,w200]
private def q517 : List W := [w110,w139,w186,w200]
private def q518 : List W := [w110,w139,w186,w211]
private def q519 : List W := [w110,w139,w187,w222]
private def q520 : List W := [w110,w139,w188,w222]
private def q521 : List W := [w110,w139,w189,w200]
private def q522 : List W := [w110,w139,w189,w215]
private def q523 : List W := [w110,w139,w191,w200]
private def q524 : List W := [w110,w139,w192,w198,w200]
private def q525 : List W := [w110,w139,w192,w200,w222]
private def q526 : List W := [w110,w139,w192,w212]
private def q527 : List W := [w110,w139,w193,w222]
private def q528 : List W := [w110,w139,w194,w222]
private def q529 : List W := [w110,w139,w195,w200]
private def q530 : List W := [w110,w139,w195,w219]
private def q531 : List W := [w110,w139,w197,w200]
private def q532 : List W := [w110,w139,w198,w200,w222]
private def q533 : List W := [w110,w139,w198,w216]
private def q534 : List W := [w110,w139,w200,w220]
private def q535 : List W := [w110,w140,w172,w200]
private def q536 : List W := [w110,w144,w172,w200]
private def q537 : List W := [w110,w150,w172,w200]
private def q538 : List W := [w110,w150,w222]
private def q539 : List W := [w110,w154,w198,w200]
private def q540 : List W := [w110,w156,w198,w200]
private def q541 : List W := [w110,w157,w172,w200]
private def q542 : List W := [w110,w158,w172,w200]
private def q543 : List W := [w110,w158,w172,w212]
private def q544 : List W := [w110,w158,w192,w200]
private def q545 : List W := [w110,w159,w172,w219]
private def q546 : List W := [w110,w160,w172,w219]
private def q547 : List W := [w110,w161,w172,w200]
private def q548 : List W := [w110,w161,w172,w215]
private def q549 : List W := [w110,w161,w189,w200]
private def q550 : List W := [w110,w163,w172,w200]
private def q551 : List W := [w110,w164,w172,w198,w200]
private def q552 : List W := [w110,w164,w172,w200,w219]
private def q553 : List W := [w110,w164,w172,w211]
private def q554 : List W := [w110,w164,w186,w200]
private def q555 : List W := [w110,w165,w172,w194,w200]
private def q556 : List W := [w110,w165,w194,w222]
private def q557 : List W := [w110,w170,w198,w200]
private def q558 : List W := [w110,w172,w193,w219]
private def q559 : List W := [w110,w172,w194,w200]
private def q560 : List W := [w110,w172,w194,w222]
private def q561 : List W := [w110,w172,w195,w219]
private def q562 : List W := [w110,w172,w196,w200]
private def q563 : List W := [w110,w172,w198,w200,w219]
private def q564 : List W := [w110,w172,w198,w216]
private def q565 : List W := [w110,w172,w200,w217]
private def q566 : List W := [w110,w181,w219]
private def q567 : List W := [w110,w194,w200,w222]
private def q568 : List W := [w110,w194,w222]
private def q569 : List W := [w110,w195,w200,w219]
private def q570 : List W := [w110,w195,w219]
private def q571 : List W := [w110,w196,w222]
private def q572 : List W := [w110,w197,w219]
private def q573 : List W := [w110,w198,w200,w216]
private def q574 : List W := [w110,w198,w207]
private def q575 : List W := [w110,w198,w216]
private def q576 : List W := [w110,w198,w218]
private def q577 : List W := [w110,w198,w219,w222]
private def q578 : List W := [w110,w198,w221]
private def q579 : List W := [w110,w217,w222]
private def q580 : List W := [w110,w219,w220]
private def q581 : List W := [w111,w139,w172,w200]
private def q582 : List W := [w111,w198,w200]
private def q583 : List W := [w115,w139,w172,w200]
private def q584 : List W := [w115,w172,w219]
private def q585 : List W := [w121,w139,w172,w200]
private def q586 : List W := [w121,w139,w222]
private def q587 : List W := [w126,w139,w156,w172,w200]
private def q588 : List W := [w126,w156,w198,w200]
private def q589 : List W := [w131,w164,w172,w200]
private def q590 : List W := [w132,w139,w160,w172,w200]
private def q591 : List W := [w132,w160,w172,w219]
private def q592 : List W := [w136,w164,w172,w200]
private def q593 : List W := [w139,w154,w192,w200]
private def q594 : List W := [w139,w155,w172,w200]
private def q595 : List W := [w139,w156,w172,w200]
private def q596 : List W := [w139,w156,w172,w216]
private def q597 : List W := [w139,w156,w198,w200]
private def q598 : List W := [w139,w158,w192,w200]
private def q599 : List W := [w139,w159,w172,w215]
private def q600 : List W := [w139,w160,w172,w200]
private def q601 : List W := [w139,w160,w172,w219]
private def q602 : List W := [w139,w160,w195,w200]
private def q603 : List W := [w139,w161,w172,w215]
private def q604 : List W := [w139,w162,w172,w200]
private def q605 : List W := [w139,w164,w172,w192,w200]
private def q606 : List W := [w139,w164,w172,w200,w215]
private def q607 : List W := [w139,w164,w172,w211]
private def q608 : List W := [w139,w164,w186,w200]
private def q609 : List W := [w139,w165,w172,w188,w200]
private def q610 : List W := [w139,w165,w188,w222]
private def q611 : List W := [w139,w169,w192,w200]
private def q612 : List W := [w139,w172,w187,w215]
private def q613 : List W := [w139,w172,w188,w200]
private def q614 : List W := [w139,w172,w188,w222]
private def q615 : List W := [w139,w172,w189,w215]
private def q616 : List W := [w139,w172,w190,w200]
private def q617 : List W := [w139,w172,w192,w200,w215]
private def q618 : List W := [w139,w172,w192,w212]
private def q619 : List W := [w139,w172,w200,w213]
private def q620 : List W := [w139,w177,w215]
private def q621 : List W := [w139,w188,w200,w222]
private def q622 : List W := [w139,w188,w222]
private def q623 : List W := [w139,w189,w200,w215]
private def q624 : List W := [w139,w189,w215]
private def q625 : List W := [w139,w190,w222]
private def q626 : List W := [w139,w191,w215]
private def q627 : List W := [w139,w192,w200,w212]
private def q628 : List W := [w139,w192,w204]
private def q629 : List W := [w139,w192,w212]
private def q630 : List W := [w139,w192,w214]
private def q631 : List W := [w139,w192,w215,w222]
private def q632 : List W := [w139,w192,w221]
private def q633 : List W := [w139,w213,w222]
private def q634 : List W := [w139,w215,w220]
private def q635 : List W := [w140,w192,w200]
private def q636 : List W := [w144,w172,w215]
private def q637 : List W := [w156,w172,w198,w200]
private def q638 : List W := [w156,w198,w200]
private def q639 : List W := [w156,w198,w216]
private def q640 : List W := [w158,w172,w192,w200]
private def q641 : List W := [w158,w192,w200]
private def q642 : List W := [w158,w192,w212]
private def q643 : List W := [w160,w172,w200,w219]
private def q644 : List W := [w160,w172,w219]
private def q645 : List W := [w160,w195,w219]
private def q646 : List W := [w161,w172,w200,w215]
private def q647 : List W := [w161,w172,w215]
private def q648 : List W := [w161,w189,w215]
private def q649 : List W := [w162,w172,w219]
private def q650 : List W := [w162,w198,w200]
private def q651 : List W := [w163,w172,w215]
private def q652 : List W := [w163,w192,w200]
private def q653 : List W := [w164,w172,w186,w200]
private def q654 : List W := [w164,w172,w200,w211]
private def q655 : List W := [w164,w172,w201]
private def q656 : List W := [w164,w172,w211]
private def q657 : List W := [w164,w172,w214]
private def q658 : List W := [w164,w172,w215,w219]
private def q659 : List W := [w164,w172,w218]
private def q660 : List W := [w164,w173,w200]
private def q661 : List W := [w164,w186,w200]
private def q662 : List W := [w164,w186,w211]
private def q663 : List W := [w164,w191,w200]
private def q664 : List W := [w164,w192,w198,w200]
private def q665 : List W := [w164,w197,w200]
private def q666 : List W := [w172,w188,w194,w200]
private def q667 : List W := [w172,w213,w219]
private def q668 : List W := [w172,w215,w217]
private def q669 : List W := [w188,w194,w222]
private def q670 : List W := [w190,w198,w200]
private def q671 : List W := [w192,w196,w200]
set_option maxHeartbeats 10000000 in
private theorem h2_143 : ¬Prog q143.toFinset 2 := localSound 1 q143 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_162 : ¬Prog q162.toFinset 2 := localSound 1 q162 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_204 : ¬Prog q204.toFinset 2 := localSound 1 q204 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_211 : ¬Prog q211.toFinset 2 := localSound 1 q211 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_229 : ¬Prog q229.toFinset 2 := localSound 1 q229 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_256 : ¬Prog q256.toFinset 2 := localSound 1 q256 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_275 : ¬Prog q275.toFinset 2 := localSound 1 q275 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_282 : ¬Prog q282.toFinset 2 := localSound 1 q282 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_299 : ¬Prog q299.toFinset 2 := localSound 1 q299 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_325 : ¬Prog q325.toFinset 2 := localSound 1 q325 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_336 : ¬Prog q336.toFinset 2 := localSound 1 q336 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_343 : ¬Prog q343.toFinset 2 := localSound 1 q343 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_538 : ¬Prog q538.toFinset 2 := localSound 1 q538 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_566 : ¬Prog q566.toFinset 2 := localSound 1 q566 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_568 : ¬Prog q568.toFinset 2 := localSound 1 q568 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_570 : ¬Prog q570.toFinset 2 := localSound 1 q570 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_571 : ¬Prog q571.toFinset 2 := localSound 1 q571 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_572 : ¬Prog q572.toFinset 2 := localSound 1 q572 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_574 : ¬Prog q574.toFinset 2 := localSound 1 q574 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_575 : ¬Prog q575.toFinset 2 := localSound 1 q575 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_576 : ¬Prog q576.toFinset 2 := localSound 1 q576 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_578 : ¬Prog q578.toFinset 2 := localSound 1 q578 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_579 : ¬Prog q579.toFinset 2 := localSound 1 q579 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_580 : ¬Prog q580.toFinset 2 := localSound 1 q580 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_582 : ¬Prog q582.toFinset 2 := localSound 1 q582 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_584 : ¬Prog q584.toFinset 2 := localSound 1 q584 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_586 : ¬Prog q586.toFinset 2 := localSound 1 q586 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_620 : ¬Prog q620.toFinset 2 := localSound 1 q620 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_622 : ¬Prog q622.toFinset 2 := localSound 1 q622 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_624 : ¬Prog q624.toFinset 2 := localSound 1 q624 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_625 : ¬Prog q625.toFinset 2 := localSound 1 q625 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_626 : ¬Prog q626.toFinset 2 := localSound 1 q626 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_628 : ¬Prog q628.toFinset 2 := localSound 1 q628 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_629 : ¬Prog q629.toFinset 2 := localSound 1 q629 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_630 : ¬Prog q630.toFinset 2 := localSound 1 q630 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_632 : ¬Prog q632.toFinset 2 := localSound 1 q632 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_633 : ¬Prog q633.toFinset 2 := localSound 1 q633 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_634 : ¬Prog q634.toFinset 2 := localSound 1 q634 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_635 : ¬Prog q635.toFinset 2 := localSound 1 q635 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_636 : ¬Prog q636.toFinset 2 := localSound 1 q636 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_638 : ¬Prog q638.toFinset 2 := localSound 1 q638 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_639 : ¬Prog q639.toFinset 2 := localSound 1 q639 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_641 : ¬Prog q641.toFinset 2 := localSound 1 q641 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_642 : ¬Prog q642.toFinset 2 := localSound 1 q642 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_644 : ¬Prog q644.toFinset 2 := localSound 1 q644 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_645 : ¬Prog q645.toFinset 2 := localSound 1 q645 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_647 : ¬Prog q647.toFinset 2 := localSound 1 q647 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_648 : ¬Prog q648.toFinset 2 := localSound 1 q648 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_649 : ¬Prog q649.toFinset 2 := localSound 1 q649 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_650 : ¬Prog q650.toFinset 2 := localSound 1 q650 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_651 : ¬Prog q651.toFinset 2 := localSound 1 q651 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_652 : ¬Prog q652.toFinset 2 := localSound 1 q652 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_655 : ¬Prog q655.toFinset 2 := localSound 1 q655 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_656 : ¬Prog q656.toFinset 2 := localSound 1 q656 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_657 : ¬Prog q657.toFinset 2 := localSound 1 q657 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_659 : ¬Prog q659.toFinset 2 := localSound 1 q659 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_660 : ¬Prog q660.toFinset 2 := localSound 1 q660 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_661 : ¬Prog q661.toFinset 2 := localSound 1 q661 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_662 : ¬Prog q662.toFinset 2 := localSound 1 q662 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_663 : ¬Prog q663.toFinset 2 := localSound 1 q663 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_665 : ¬Prog q665.toFinset 2 := localSound 1 q665 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_667 : ¬Prog q667.toFinset 2 := localSound 1 q667 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_668 : ¬Prog q668.toFinset 2 := localSound 1 q668 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_669 : ¬Prog q669.toFinset 2 := localSound 1 q669 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_670 : ¬Prog q670.toFinset 2 := localSound 1 q670 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h2_671 : ¬Prog q671.toFinset 2 := localSound 1 q671 [] (by decide +kernel) (nilSafe 1)
set_option maxHeartbeats 10000000 in
private theorem h3_52 : ¬Prog q52.toFinset 3 := localSound 2 q52 [q568] (by decide +kernel) (consSafe h2_568 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_53 : ¬Prog q53.toFinset 3 := localSound 2 q53 [q570] (by decide +kernel) (consSafe h2_570 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_54 : ¬Prog q54.toFinset 3 := localSound 2 q54 [q575] (by decide +kernel) (consSafe h2_575 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_58 : ¬Prog q58.toFinset 3 := localSound 2 q58 [q622] (by decide +kernel) (consSafe h2_622 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_59 : ¬Prog q59.toFinset 3 := localSound 2 q59 [q624] (by decide +kernel) (consSafe h2_624 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_60 : ¬Prog q60.toFinset 3 := localSound 2 q60 [q629] (by decide +kernel) (consSafe h2_629 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_61 : ¬Prog q61.toFinset 3 := localSound 2 q61 [q638] (by decide +kernel) (consSafe h2_638 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_62 : ¬Prog q62.toFinset 3 := localSound 2 q62 [q641] (by decide +kernel) (consSafe h2_641 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_63 : ¬Prog q63.toFinset 3 := localSound 2 q63 [q644] (by decide +kernel) (consSafe h2_644 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_64 : ¬Prog q64.toFinset 3 := localSound 2 q64 [q647] (by decide +kernel) (consSafe h2_647 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_65 : ¬Prog q65.toFinset 3 := localSound 2 q65 [q656] (by decide +kernel) (consSafe h2_656 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_66 : ¬Prog q66.toFinset 3 := localSound 2 q66 [q661] (by decide +kernel) (consSafe h2_661 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_74 : ¬Prog q74.toFinset 3 := localSound 2 q74 [q656,q660] (by decide +kernel) (consSafe h2_656 (consSafe h2_660 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_76 : ¬Prog q76.toFinset 3 := localSound 2 q76 [q629,q635] (by decide +kernel) (consSafe h2_629 (consSafe h2_635 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_86 : ¬Prog q86.toFinset 3 := localSound 2 q86 [q624] (by decide +kernel) (consSafe h2_624 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_87 : ¬Prog q87.toFinset 3 := localSound 2 q87 [q647] (by decide +kernel) (consSafe h2_647 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_89 : ¬Prog q89.toFinset 3 := localSound 2 q89 [q575,q582] (by decide +kernel) (consSafe h2_575 (consSafe h2_582 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_99 : ¬Prog q99.toFinset 3 := localSound 2 q99 [q570] (by decide +kernel) (consSafe h2_570 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_100 : ¬Prog q100.toFinset 3 := localSound 2 q100 [q644] (by decide +kernel) (consSafe h2_644 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_110 : ¬Prog q110.toFinset 3 := localSound 2 q110 [q568] (by decide +kernel) (consSafe h2_568 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_111 : ¬Prog q111.toFinset 3 := localSound 2 q111 [q622] (by decide +kernel) (consSafe h2_622 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_115 : ¬Prog q115.toFinset 3 := localSound 2 q115 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_118 : ¬Prog q118.toFinset 3 := localSound 2 q118 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_121 : ¬Prog q121.toFinset 3 := localSound 2 q121 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_123 : ¬Prog q123.toFinset 3 := localSound 2 q123 [q655,q661] (by decide +kernel) (consSafe h2_655 (consSafe h2_661 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_125 : ¬Prog q125.toFinset 3 := localSound 2 q125 [q624,q636] (by decide +kernel) (consSafe h2_624 (consSafe h2_636 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_134 : ¬Prog q134.toFinset 3 := localSound 2 q134 [q629] (by decide +kernel) (consSafe h2_629 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_135 : ¬Prog q135.toFinset 3 := localSound 2 q135 [q641] (by decide +kernel) (consSafe h2_641 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_136 : ¬Prog q136.toFinset 3 := localSound 2 q136 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_137 : ¬Prog q137.toFinset 3 := localSound 2 q137 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_140 : ¬Prog q140.toFinset 3 := localSound 2 q140 [q143,q622] (by decide +kernel) (consSafe h2_143 (consSafe h2_622 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_141 : ¬Prog q141.toFinset 3 := localSound 2 q141 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_142 : ¬Prog q142.toFinset 3 := localSound 2 q142 [q143] (by decide +kernel) (consSafe h2_143 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_145 : ¬Prog q145.toFinset 3 := localSound 2 q145 [q570,q584] (by decide +kernel) (consSafe h2_570 (consSafe h2_584 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_154 : ¬Prog q154.toFinset 3 := localSound 2 q154 [q575] (by decide +kernel) (consSafe h2_575 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_155 : ¬Prog q155.toFinset 3 := localSound 2 q155 [q638] (by decide +kernel) (consSafe h2_638 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_156 : ¬Prog q156.toFinset 3 := localSound 2 q156 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_159 : ¬Prog q159.toFinset 3 := localSound 2 q159 [q162,q568] (by decide +kernel) (consSafe h2_162 (consSafe h2_568 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_160 : ¬Prog q160.toFinset 3 := localSound 2 q160 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_161 : ¬Prog q161.toFinset 3 := localSound 2 q161 [q162] (by decide +kernel) (consSafe h2_162 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_170 : ¬Prog q170.toFinset 3 := localSound 2 q170 [q568] (by decide +kernel) (consSafe h2_568 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_171 : ¬Prog q171.toFinset 3 := localSound 2 q171 [q622] (by decide +kernel) (consSafe h2_622 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_175 : ¬Prog q175.toFinset 3 := localSound 2 q175 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_176 : ¬Prog q176.toFinset 3 := localSound 2 q176 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_177 : ¬Prog q177.toFinset 3 := localSound 2 q177 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_178 : ¬Prog q178.toFinset 3 := localSound 2 q178 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_179 : ¬Prog q179.toFinset 3 := localSound 2 q179 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_182 : ¬Prog q182.toFinset 3 := localSound 2 q182 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_183 : ¬Prog q183.toFinset 3 := localSound 2 q183 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_185 : ¬Prog q185.toFinset 3 := localSound 2 q185 [q628,q641] (by decide +kernel) (consSafe h2_628 (consSafe h2_641 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_187 : ¬Prog q187.toFinset 3 := localSound 2 q187 [q620,q647] (by decide +kernel) (consSafe h2_620 (consSafe h2_647 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_195 : ¬Prog q195.toFinset 3 := localSound 2 q195 [q656] (by decide +kernel) (consSafe h2_656 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_196 : ¬Prog q196.toFinset 3 := localSound 2 q196 [q661] (by decide +kernel) (consSafe h2_661 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_197 : ¬Prog q197.toFinset 3 := localSound 2 q197 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_198 : ¬Prog q198.toFinset 3 := localSound 2 q198 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_201 : ¬Prog q201.toFinset 3 := localSound 2 q201 [q204,q644] (by decide +kernel) (consSafe h2_204 (consSafe h2_644 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_202 : ¬Prog q202.toFinset 3 := localSound 2 q202 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_203 : ¬Prog q203.toFinset 3 := localSound 2 q203 [q204] (by decide +kernel) (consSafe h2_204 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_205 : ¬Prog q205.toFinset 3 := localSound 2 q205 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_208 : ¬Prog q208.toFinset 3 := localSound 2 q208 [q211,q638] (by decide +kernel) (consSafe h2_211 (consSafe h2_638 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_209 : ¬Prog q209.toFinset 3 := localSound 2 q209 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_210 : ¬Prog q210.toFinset 3 := localSound 2 q210 [q211] (by decide +kernel) (consSafe h2_211 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_212 : ¬Prog q212.toFinset 3 := localSound 2 q212 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_214 : ¬Prog q214.toFinset 3 := localSound 2 q214 [q568,q586] (by decide +kernel) (consSafe h2_568 (consSafe h2_586 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_220 : ¬Prog q220.toFinset 3 := localSound 2 q220 [q575] (by decide +kernel) (consSafe h2_575 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_222 : ¬Prog q222.toFinset 3 := localSound 2 q222 [q638] (by decide +kernel) (consSafe h2_638 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_223 : ¬Prog q223.toFinset 3 := localSound 2 q223 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_225 : ¬Prog q225.toFinset 3 := localSound 2 q225 [q229,q570] (by decide +kernel) (consSafe h2_229 (consSafe h2_570 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_227 : ¬Prog q227.toFinset 3 := localSound 2 q227 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_228 : ¬Prog q228.toFinset 3 := localSound 2 q228 [q229] (by decide +kernel) (consSafe h2_229 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_235 : ¬Prog q235.toFinset 3 := localSound 2 q235 [q570] (by decide +kernel) (consSafe h2_570 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_237 : ¬Prog q237.toFinset 3 := localSound 2 q237 [q644] (by decide +kernel) (consSafe h2_644 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_241 : ¬Prog q241.toFinset 3 := localSound 2 q241 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_242 : ¬Prog q242.toFinset 3 := localSound 2 q242 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_243 : ¬Prog q243.toFinset 3 := localSound 2 q243 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_244 : ¬Prog q244.toFinset 3 := localSound 2 q244 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_245 : ¬Prog q245.toFinset 3 := localSound 2 q245 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_246 : ¬Prog q246.toFinset 3 := localSound 2 q246 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_247 : ¬Prog q247.toFinset 3 := localSound 2 q247 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_248 : ¬Prog q248.toFinset 3 := localSound 2 q248 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_249 : ¬Prog q249.toFinset 3 := localSound 2 q249 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_250 : ¬Prog q250.toFinset 3 := localSound 2 q250 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_252 : ¬Prog q252.toFinset 3 := localSound 2 q252 [q256,q575] (by decide +kernel) (consSafe h2_256 (consSafe h2_575 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_253 : ¬Prog q253.toFinset 3 := localSound 2 q253 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_255 : ¬Prog q255.toFinset 3 := localSound 2 q255 [q256] (by decide +kernel) (consSafe h2_256 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_258 : ¬Prog q258.toFinset 3 := localSound 2 q258 [q574,q638] (by decide +kernel) (consSafe h2_574 (consSafe h2_638 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_260 : ¬Prog q260.toFinset 3 := localSound 2 q260 [q566,q644] (by decide +kernel) (consSafe h2_566 (consSafe h2_644 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_265 : ¬Prog q265.toFinset 3 := localSound 2 q265 [q656] (by decide +kernel) (consSafe h2_656 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_266 : ¬Prog q266.toFinset 3 := localSound 2 q266 [q661] (by decide +kernel) (consSafe h2_661 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_268 : ¬Prog q268.toFinset 3 := localSound 2 q268 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_269 : ¬Prog q269.toFinset 3 := localSound 2 q269 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_271 : ¬Prog q271.toFinset 3 := localSound 2 q271 [q275,q647] (by decide +kernel) (consSafe h2_275 (consSafe h2_647 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_273 : ¬Prog q273.toFinset 3 := localSound 2 q273 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_274 : ¬Prog q274.toFinset 3 := localSound 2 q274 [q275] (by decide +kernel) (consSafe h2_275 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_276 : ¬Prog q276.toFinset 3 := localSound 2 q276 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_278 : ¬Prog q278.toFinset 3 := localSound 2 q278 [q282,q641] (by decide +kernel) (consSafe h2_282 (consSafe h2_641 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_280 : ¬Prog q280.toFinset 3 := localSound 2 q280 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_281 : ¬Prog q281.toFinset 3 := localSound 2 q281 [q282] (by decide +kernel) (consSafe h2_282 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_283 : ¬Prog q283.toFinset 3 := localSound 2 q283 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_285 : ¬Prog q285.toFinset 3 := localSound 2 q285 [q538,q622] (by decide +kernel) (consSafe h2_538 (consSafe h2_622 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_290 : ¬Prog q290.toFinset 3 := localSound 2 q290 [q629] (by decide +kernel) (consSafe h2_629 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_291 : ¬Prog q291.toFinset 3 := localSound 2 q291 [q641] (by decide +kernel) (consSafe h2_641 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_293 : ¬Prog q293.toFinset 3 := localSound 2 q293 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_295 : ¬Prog q295.toFinset 3 := localSound 2 q295 [q299,q624] (by decide +kernel) (consSafe h2_299 (consSafe h2_624 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_297 : ¬Prog q297.toFinset 3 := localSound 2 q297 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_298 : ¬Prog q298.toFinset 3 := localSound 2 q298 [q299] (by decide +kernel) (consSafe h2_299 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_304 : ¬Prog q304.toFinset 3 := localSound 2 q304 [q624] (by decide +kernel) (consSafe h2_624 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_305 : ¬Prog q305.toFinset 3 := localSound 2 q305 [q647] (by decide +kernel) (consSafe h2_647 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_310 : ¬Prog q310.toFinset 3 := localSound 2 q310 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_311 : ¬Prog q311.toFinset 3 := localSound 2 q311 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_312 : ¬Prog q312.toFinset 3 := localSound 2 q312 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_313 : ¬Prog q313.toFinset 3 := localSound 2 q313 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_314 : ¬Prog q314.toFinset 3 := localSound 2 q314 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_315 : ¬Prog q315.toFinset 3 := localSound 2 q315 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_316 : ¬Prog q316.toFinset 3 := localSound 2 q316 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_317 : ¬Prog q317.toFinset 3 := localSound 2 q317 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_318 : ¬Prog q318.toFinset 3 := localSound 2 q318 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_319 : ¬Prog q319.toFinset 3 := localSound 2 q319 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_321 : ¬Prog q321.toFinset 3 := localSound 2 q321 [q325,q629] (by decide +kernel) (consSafe h2_325 (consSafe h2_629 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_322 : ¬Prog q322.toFinset 3 := localSound 2 q322 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_324 : ¬Prog q324.toFinset 3 := localSound 2 q324 [q325] (by decide +kernel) (consSafe h2_325 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_326 : ¬Prog q326.toFinset 3 := localSound 2 q326 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_327 : ¬Prog q327.toFinset 3 := localSound 2 q327 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_328 : ¬Prog q328.toFinset 3 := localSound 2 q328 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_329 : ¬Prog q329.toFinset 3 := localSound 2 q329 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_330 : ¬Prog q330.toFinset 3 := localSound 2 q330 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_332 : ¬Prog q332.toFinset 3 := localSound 2 q332 [q336,q661] (by decide +kernel) (consSafe h2_336 (consSafe h2_661 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_334 : ¬Prog q334.toFinset 3 := localSound 2 q334 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_335 : ¬Prog q335.toFinset 3 := localSound 2 q335 [q336] (by decide +kernel) (consSafe h2_336 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_337 : ¬Prog q337.toFinset 3 := localSound 2 q337 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_339 : ¬Prog q339.toFinset 3 := localSound 2 q339 [q343,q656] (by decide +kernel) (consSafe h2_343 (consSafe h2_656 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_340 : ¬Prog q340.toFinset 3 := localSound 2 q340 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_342 : ¬Prog q342.toFinset 3 := localSound 2 q342 [q343] (by decide +kernel) (consSafe h2_343 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_344 : ¬Prog q344.toFinset 3 := localSound 2 q344 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_352 : ¬Prog q352.toFinset 3 := localSound 2 q352 [q656,q661] (by decide +kernel) (consSafe h2_656 (consSafe h2_661 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_353 : ¬Prog q353.toFinset 3 := localSound 2 q353 [q336,q656,q662] (by decide +kernel) (consSafe h2_336 (consSafe h2_656 (consSafe h2_662 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_354 : ¬Prog q354.toFinset 3 := localSound 2 q354 [q343,q661,q662] (by decide +kernel) (consSafe h2_343 (consSafe h2_661 (consSafe h2_662 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_358 : ¬Prog q358.toFinset 3 := localSound 2 q358 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_360 : ¬Prog q360.toFinset 3 := localSound 2 q360 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_367 : ¬Prog q367.toFinset 3 := localSound 2 q367 [q629,q641] (by decide +kernel) (consSafe h2_629 (consSafe h2_641 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_368 : ¬Prog q368.toFinset 3 := localSound 2 q368 [q282,q629,q642] (by decide +kernel) (consSafe h2_282 (consSafe h2_629 (consSafe h2_642 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_369 : ¬Prog q369.toFinset 3 := localSound 2 q369 [q325,q641,q642] (by decide +kernel) (consSafe h2_325 (consSafe h2_641 (consSafe h2_642 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_373 : ¬Prog q373.toFinset 3 := localSound 2 q373 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_375 : ¬Prog q375.toFinset 3 := localSound 2 q375 [q630,q641] (by decide +kernel) (consSafe h2_630 (consSafe h2_641 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_376 : ¬Prog q376.toFinset 3 := localSound 2 q376 [q657,q661] (by decide +kernel) (consSafe h2_657 (consSafe h2_661 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_382 : ¬Prog q382.toFinset 3 := localSound 2 q382 [q624,q647] (by decide +kernel) (consSafe h2_624 (consSafe h2_647 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_383 : ¬Prog q383.toFinset 3 := localSound 2 q383 [q275,q624,q648] (by decide +kernel) (consSafe h2_275 (consSafe h2_624 (consSafe h2_648 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_384 : ¬Prog q384.toFinset 3 := localSound 2 q384 [q299,q647,q648] (by decide +kernel) (consSafe h2_299 (consSafe h2_647 (consSafe h2_648 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_387 : ¬Prog q387.toFinset 3 := localSound 2 q387 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_389 : ¬Prog q389.toFinset 3 := localSound 2 q389 [q626,q647] (by decide +kernel) (consSafe h2_626 (consSafe h2_647 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_390 : ¬Prog q390.toFinset 3 := localSound 2 q390 [q656,q663] (by decide +kernel) (consSafe h2_656 (consSafe h2_663 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_392 : ¬Prog q392.toFinset 3 := localSound 2 q392 [q624,q651] (by decide +kernel) (consSafe h2_624 (consSafe h2_651 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_393 : ¬Prog q393.toFinset 3 := localSound 2 q393 [q629,q652] (by decide +kernel) (consSafe h2_629 (consSafe h2_652 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_394 : ¬Prog q394.toFinset 3 := localSound 2 q394 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_401 : ¬Prog q401.toFinset 3 := localSound 2 q401 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_405 : ¬Prog q405.toFinset 3 := localSound 2 q405 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_411 : ¬Prog q411.toFinset 3 := localSound 2 q411 [q575,q638] (by decide +kernel) (consSafe h2_575 (consSafe h2_638 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_412 : ¬Prog q412.toFinset 3 := localSound 2 q412 [q211,q575,q639] (by decide +kernel) (consSafe h2_211 (consSafe h2_575 (consSafe h2_639 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_416 : ¬Prog q416.toFinset 3 := localSound 2 q416 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_418 : ¬Prog q418.toFinset 3 := localSound 2 q418 [q576,q638] (by decide +kernel) (consSafe h2_576 (consSafe h2_638 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_423 : ¬Prog q423.toFinset 3 := localSound 2 q423 [q570,q644] (by decide +kernel) (consSafe h2_570 (consSafe h2_644 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_424 : ¬Prog q424.toFinset 3 := localSound 2 q424 [q204,q570,q645] (by decide +kernel) (consSafe h2_204 (consSafe h2_570 (consSafe h2_645 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_427 : ¬Prog q427.toFinset 3 := localSound 2 q427 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_429 : ¬Prog q429.toFinset 3 := localSound 2 q429 [q572,q644] (by decide +kernel) (consSafe h2_572 (consSafe h2_644 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_431 : ¬Prog q431.toFinset 3 := localSound 2 q431 [q570,q649] (by decide +kernel) (consSafe h2_570 (consSafe h2_649 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_432 : ¬Prog q432.toFinset 3 := localSound 2 q432 [q575,q650] (by decide +kernel) (consSafe h2_575 (consSafe h2_650 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_433 : ¬Prog q433.toFinset 3 := localSound 2 q433 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_440 : ¬Prog q440.toFinset 3 := localSound 2 q440 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_444 : ¬Prog q444.toFinset 3 := localSound 2 q444 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_455 : ¬Prog q455.toFinset 3 := localSound 2 q455 [q568,q622] (by decide +kernel) (consSafe h2_568 (consSafe h2_622 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_458 : ¬Prog q458.toFinset 3 := localSound 2 q458 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_460 : ¬Prog q460.toFinset 3 := localSound 2 q460 [q571,q622] (by decide +kernel) (consSafe h2_571 (consSafe h2_622 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_462 : ¬Prog q462.toFinset 3 := localSound 2 q462 [q568,q625] (by decide +kernel) (consSafe h2_568 (consSafe h2_625 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_463 : ¬Prog q463.toFinset 3 := localSound 2 q463 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_472 : ¬Prog q472.toFinset 3 := localSound 2 q472 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_482 : ¬Prog q482.toFinset 3 := localSound 2 q482 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_483 : ¬Prog q483.toFinset 3 := localSound 2 q483 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_500 : ¬Prog q500.toFinset 3 := localSound 2 q500 [q655] (by decide +kernel) (consSafe h2_655 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_501 : ¬Prog q501.toFinset 3 := localSound 2 q501 [q628] (by decide +kernel) (consSafe h2_628 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_502 : ¬Prog q502.toFinset 3 := localSound 2 q502 [q574] (by decide +kernel) (consSafe h2_574 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_503 : ¬Prog q503.toFinset 3 := localSound 2 q503 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_504 : ¬Prog q504.toFinset 3 := localSound 2 q504 [q656] (by decide +kernel) (consSafe h2_656 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_505 : ¬Prog q505.toFinset 3 := localSound 2 q505 [q629] (by decide +kernel) (consSafe h2_629 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_506 : ¬Prog q506.toFinset 3 := localSound 2 q506 [q630,q657] (by decide +kernel) (consSafe h2_630 (consSafe h2_657 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_509 : ¬Prog q509.toFinset 3 := localSound 2 q509 [q575] (by decide +kernel) (consSafe h2_575 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_510 : ¬Prog q510.toFinset 3 := localSound 2 q510 [q576,q659] (by decide +kernel) (consSafe h2_576 (consSafe h2_659 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_512 : ¬Prog q512.toFinset 3 := localSound 2 q512 [q578,q632] (by decide +kernel) (consSafe h2_578 (consSafe h2_632 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_513 : ¬Prog q513.toFinset 3 := localSound 2 q513 [q660] (by decide +kernel) (consSafe h2_660 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_514 : ¬Prog q514.toFinset 3 := localSound 2 q514 [q620] (by decide +kernel) (consSafe h2_620 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_515 : ¬Prog q515.toFinset 3 := localSound 2 q515 [q566] (by decide +kernel) (consSafe h2_566 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_516 : ¬Prog q516.toFinset 3 := localSound 2 q516 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_517 : ¬Prog q517.toFinset 3 := localSound 2 q517 [q661] (by decide +kernel) (consSafe h2_661 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_518 : ¬Prog q518.toFinset 3 := localSound 2 q518 [q662] (by decide +kernel) (consSafe h2_662 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_519 : ¬Prog q519.toFinset 3 := localSound 2 q519 [q579,q622] (by decide +kernel) (consSafe h2_579 (consSafe h2_622 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_520 : ¬Prog q520.toFinset 3 := localSound 2 q520 [q622] (by decide +kernel) (consSafe h2_622 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_521 : ¬Prog q521.toFinset 3 := localSound 2 q521 [q624] (by decide +kernel) (consSafe h2_624 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_522 : ¬Prog q522.toFinset 3 := localSound 2 q522 [q624] (by decide +kernel) (consSafe h2_624 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_523 : ¬Prog q523.toFinset 3 := localSound 2 q523 [q626,q663] (by decide +kernel) (consSafe h2_626 (consSafe h2_663 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_526 : ¬Prog q526.toFinset 3 := localSound 2 q526 [q629] (by decide +kernel) (consSafe h2_629 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_527 : ¬Prog q527.toFinset 3 := localSound 2 q527 [q568,q633] (by decide +kernel) (consSafe h2_568 (consSafe h2_633 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_528 : ¬Prog q528.toFinset 3 := localSound 2 q528 [q568] (by decide +kernel) (consSafe h2_568 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_529 : ¬Prog q529.toFinset 3 := localSound 2 q529 [q570] (by decide +kernel) (consSafe h2_570 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_530 : ¬Prog q530.toFinset 3 := localSound 2 q530 [q570] (by decide +kernel) (consSafe h2_570 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_531 : ¬Prog q531.toFinset 3 := localSound 2 q531 [q572,q665] (by decide +kernel) (consSafe h2_572 (consSafe h2_665 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_533 : ¬Prog q533.toFinset 3 := localSound 2 q533 [q575] (by decide +kernel) (consSafe h2_575 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_534 : ¬Prog q534.toFinset 3 := localSound 2 q534 [q580,q634] (by decide +kernel) (consSafe h2_580 (consSafe h2_634 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_535 : ¬Prog q535.toFinset 3 := localSound 2 q535 [q635] (by decide +kernel) (consSafe h2_635 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_536 : ¬Prog q536.toFinset 3 := localSound 2 q536 [q636] (by decide +kernel) (consSafe h2_636 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_537 : ¬Prog q537.toFinset 3 := localSound 2 q537 [q538] (by decide +kernel) (consSafe h2_538 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_539 : ¬Prog q539.toFinset 3 := localSound 2 q539 [q578,q638] (by decide +kernel) (consSafe h2_578 (consSafe h2_638 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_540 : ¬Prog q540.toFinset 3 := localSound 2 q540 [q638] (by decide +kernel) (consSafe h2_638 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_541 : ¬Prog q541.toFinset 3 := localSound 2 q541 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_542 : ¬Prog q542.toFinset 3 := localSound 2 q542 [q641] (by decide +kernel) (consSafe h2_641 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_543 : ¬Prog q543.toFinset 3 := localSound 2 q543 [q642] (by decide +kernel) (consSafe h2_642 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_544 : ¬Prog q544.toFinset 3 := localSound 2 q544 [q641] (by decide +kernel) (consSafe h2_641 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_545 : ¬Prog q545.toFinset 3 := localSound 2 q545 [q580,q644] (by decide +kernel) (consSafe h2_580 (consSafe h2_644 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_546 : ¬Prog q546.toFinset 3 := localSound 2 q546 [q644] (by decide +kernel) (consSafe h2_644 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_547 : ¬Prog q547.toFinset 3 := localSound 2 q547 [q647] (by decide +kernel) (consSafe h2_647 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_548 : ¬Prog q548.toFinset 3 := localSound 2 q548 [q647] (by decide +kernel) (consSafe h2_647 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_549 : ¬Prog q549.toFinset 3 := localSound 2 q549 [q648] (by decide +kernel) (consSafe h2_648 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_550 : ¬Prog q550.toFinset 3 := localSound 2 q550 [q651,q652] (by decide +kernel) (consSafe h2_651 (consSafe h2_652 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_553 : ¬Prog q553.toFinset 3 := localSound 2 q553 [q656] (by decide +kernel) (consSafe h2_656 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_554 : ¬Prog q554.toFinset 3 := localSound 2 q554 [q661] (by decide +kernel) (consSafe h2_661 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_556 : ¬Prog q556.toFinset 3 := localSound 2 q556 [q143,q568,q669] (by decide +kernel) (consSafe h2_143 (consSafe h2_568 (consSafe h2_669 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_557 : ¬Prog q557.toFinset 3 := localSound 2 q557 [q575,q670] (by decide +kernel) (consSafe h2_575 (consSafe h2_670 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_558 : ¬Prog q558.toFinset 3 := localSound 2 q558 [q570,q667] (by decide +kernel) (consSafe h2_570 (consSafe h2_667 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_559 : ¬Prog q559.toFinset 3 := localSound 2 q559 [q568] (by decide +kernel) (consSafe h2_568 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_560 : ¬Prog q560.toFinset 3 := localSound 2 q560 [q568] (by decide +kernel) (consSafe h2_568 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_561 : ¬Prog q561.toFinset 3 := localSound 2 q561 [q570] (by decide +kernel) (consSafe h2_570 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_562 : ¬Prog q562.toFinset 3 := localSound 2 q562 [q571,q671] (by decide +kernel) (consSafe h2_571 (consSafe h2_671 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_564 : ¬Prog q564.toFinset 3 := localSound 2 q564 [q575] (by decide +kernel) (consSafe h2_575 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_565 : ¬Prog q565.toFinset 3 := localSound 2 q565 [q579,q668] (by decide +kernel) (consSafe h2_579 (consSafe h2_668 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_567 : ¬Prog q567.toFinset 3 := localSound 2 q567 [q568] (by decide +kernel) (consSafe h2_568 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_569 : ¬Prog q569.toFinset 3 := localSound 2 q569 [q570] (by decide +kernel) (consSafe h2_570 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_573 : ¬Prog q573.toFinset 3 := localSound 2 q573 [q575] (by decide +kernel) (consSafe h2_575 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_577 : ¬Prog q577.toFinset 3 := localSound 2 q577 [q568,q570,q575] (by decide +kernel) (consSafe h2_568 (consSafe h2_570 (consSafe h2_575 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_581 : ¬Prog q581.toFinset 3 := localSound 2 q581 [q582] (by decide +kernel) (consSafe h2_582 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_583 : ¬Prog q583.toFinset 3 := localSound 2 q583 [q584] (by decide +kernel) (consSafe h2_584 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_585 : ¬Prog q585.toFinset 3 := localSound 2 q585 [q586] (by decide +kernel) (consSafe h2_586 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_588 : ¬Prog q588.toFinset 3 := localSound 2 q588 [q256,q638,q639] (by decide +kernel) (consSafe h2_256 (consSafe h2_638 (consSafe h2_639 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_589 : ¬Prog q589.toFinset 3 := localSound 2 q589 [q659,q661] (by decide +kernel) (consSafe h2_659 (consSafe h2_661 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_591 : ¬Prog q591.toFinset 3 := localSound 2 q591 [q229,q644,q645] (by decide +kernel) (consSafe h2_229 (consSafe h2_644 (consSafe h2_645 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_592 : ¬Prog q592.toFinset 3 := localSound 2 q592 [q656,q665] (by decide +kernel) (consSafe h2_656 (consSafe h2_665 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_593 : ¬Prog q593.toFinset 3 := localSound 2 q593 [q632,q641] (by decide +kernel) (consSafe h2_632 (consSafe h2_641 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_594 : ¬Prog q594.toFinset 3 := localSound 2 q594 [] (by decide +kernel) (nilSafe 2)
set_option maxHeartbeats 10000000 in
private theorem h3_595 : ¬Prog q595.toFinset 3 := localSound 2 q595 [q638] (by decide +kernel) (consSafe h2_638 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_596 : ¬Prog q596.toFinset 3 := localSound 2 q596 [q639] (by decide +kernel) (consSafe h2_639 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_597 : ¬Prog q597.toFinset 3 := localSound 2 q597 [q638] (by decide +kernel) (consSafe h2_638 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_598 : ¬Prog q598.toFinset 3 := localSound 2 q598 [q641] (by decide +kernel) (consSafe h2_641 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_599 : ¬Prog q599.toFinset 3 := localSound 2 q599 [q634,q647] (by decide +kernel) (consSafe h2_634 (consSafe h2_647 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_600 : ¬Prog q600.toFinset 3 := localSound 2 q600 [q644] (by decide +kernel) (consSafe h2_644 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_601 : ¬Prog q601.toFinset 3 := localSound 2 q601 [q644] (by decide +kernel) (consSafe h2_644 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_602 : ¬Prog q602.toFinset 3 := localSound 2 q602 [q645] (by decide +kernel) (consSafe h2_645 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_603 : ¬Prog q603.toFinset 3 := localSound 2 q603 [q647] (by decide +kernel) (consSafe h2_647 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_604 : ¬Prog q604.toFinset 3 := localSound 2 q604 [q649,q650] (by decide +kernel) (consSafe h2_649 (consSafe h2_650 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_607 : ¬Prog q607.toFinset 3 := localSound 2 q607 [q656] (by decide +kernel) (consSafe h2_656 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_608 : ¬Prog q608.toFinset 3 := localSound 2 q608 [q661] (by decide +kernel) (consSafe h2_661 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_610 : ¬Prog q610.toFinset 3 := localSound 2 q610 [q162,q622,q669] (by decide +kernel) (consSafe h2_162 (consSafe h2_622 (consSafe h2_669 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_611 : ¬Prog q611.toFinset 3 := localSound 2 q611 [q629,q671] (by decide +kernel) (consSafe h2_629 (consSafe h2_671 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_612 : ¬Prog q612.toFinset 3 := localSound 2 q612 [q624,q668] (by decide +kernel) (consSafe h2_624 (consSafe h2_668 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_613 : ¬Prog q613.toFinset 3 := localSound 2 q613 [q622] (by decide +kernel) (consSafe h2_622 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_614 : ¬Prog q614.toFinset 3 := localSound 2 q614 [q622] (by decide +kernel) (consSafe h2_622 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_615 : ¬Prog q615.toFinset 3 := localSound 2 q615 [q624] (by decide +kernel) (consSafe h2_624 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_616 : ¬Prog q616.toFinset 3 := localSound 2 q616 [q625,q670] (by decide +kernel) (consSafe h2_625 (consSafe h2_670 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_618 : ¬Prog q618.toFinset 3 := localSound 2 q618 [q629] (by decide +kernel) (consSafe h2_629 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_619 : ¬Prog q619.toFinset 3 := localSound 2 q619 [q633,q667] (by decide +kernel) (consSafe h2_633 (consSafe h2_667 (nilSafe 2)))
set_option maxHeartbeats 10000000 in
private theorem h3_621 : ¬Prog q621.toFinset 3 := localSound 2 q621 [q622] (by decide +kernel) (consSafe h2_622 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_623 : ¬Prog q623.toFinset 3 := localSound 2 q623 [q624] (by decide +kernel) (consSafe h2_624 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_627 : ¬Prog q627.toFinset 3 := localSound 2 q627 [q629] (by decide +kernel) (consSafe h2_629 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_631 : ¬Prog q631.toFinset 3 := localSound 2 q631 [q622,q624,q629] (by decide +kernel) (consSafe h2_622 (consSafe h2_624 (consSafe h2_629 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_637 : ¬Prog q637.toFinset 3 := localSound 2 q637 [q638] (by decide +kernel) (consSafe h2_638 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_640 : ¬Prog q640.toFinset 3 := localSound 2 q640 [q641] (by decide +kernel) (consSafe h2_641 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_643 : ¬Prog q643.toFinset 3 := localSound 2 q643 [q644] (by decide +kernel) (consSafe h2_644 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_646 : ¬Prog q646.toFinset 3 := localSound 2 q646 [q647] (by decide +kernel) (consSafe h2_647 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_653 : ¬Prog q653.toFinset 3 := localSound 2 q653 [q661] (by decide +kernel) (consSafe h2_661 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_654 : ¬Prog q654.toFinset 3 := localSound 2 q654 [q656] (by decide +kernel) (consSafe h2_656 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h3_658 : ¬Prog q658.toFinset 3 := localSound 2 q658 [q644,q647,q656] (by decide +kernel) (consSafe h2_644 (consSafe h2_647 (consSafe h2_656 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_664 : ¬Prog q664.toFinset 3 := localSound 2 q664 [q638,q641,q661] (by decide +kernel) (consSafe h2_638 (consSafe h2_641 (consSafe h2_661 (nilSafe 2))))
set_option maxHeartbeats 10000000 in
private theorem h3_666 : ¬Prog q666.toFinset 3 := localSound 2 q666 [q669] (by decide +kernel) (consSafe h2_669 (nilSafe 2))
set_option maxHeartbeats 10000000 in
private theorem h4_4 : ¬Prog q4.toFinset 4 := localSound 3 q4 [q141] (by decide +kernel) (consSafe h3_141 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_6 : ¬Prog q6.toFinset 4 := localSound 3 q6 [q160] (by decide +kernel) (consSafe h3_160 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_9 : ¬Prog q9.toFinset 4 := localSound 3 q9 [q202] (by decide +kernel) (consSafe h3_202 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_10 : ¬Prog q10.toFinset 4 := localSound 3 q10 [q209] (by decide +kernel) (consSafe h3_209 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_12 : ¬Prog q12.toFinset 4 := localSound 3 q12 [q227] (by decide +kernel) (consSafe h3_227 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_14 : ¬Prog q14.toFinset 4 := localSound 3 q14 [q253] (by decide +kernel) (consSafe h3_253 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_16 : ¬Prog q16.toFinset 4 := localSound 3 q16 [q273] (by decide +kernel) (consSafe h3_273 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_17 : ¬Prog q17.toFinset 4 := localSound 3 q17 [q280] (by decide +kernel) (consSafe h3_280 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_19 : ¬Prog q19.toFinset 4 := localSound 3 q19 [q297] (by decide +kernel) (consSafe h3_297 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_21 : ¬Prog q21.toFinset 4 := localSound 3 q21 [q322] (by decide +kernel) (consSafe h3_322 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_22 : ¬Prog q22.toFinset 4 := localSound 3 q22 [q334] (by decide +kernel) (consSafe h3_334 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_23 : ¬Prog q23.toFinset 4 := localSound 3 q23 [q340] (by decide +kernel) (consSafe h3_340 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_25 : ¬Prog q25.toFinset 4 := localSound 3 q25 [q65,q66,q74,q123,q326,q329,q332,q339,q352,q353,q354,q653,q654] (by decide +kernel) (consSafe h3_65 (consSafe h3_66 (consSafe h3_74 (consSafe h3_123 (consSafe h3_326 (consSafe h3_329 (consSafe h3_332 (consSafe h3_339 (consSafe h3_352 (consSafe h3_353 (consSafe h3_354 (consSafe h3_653 (consSafe h3_654 (nilSafe 3))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_27 : ¬Prog q27.toFinset 4 := localSound 3 q27 [q60,q62,q76,q185,q278,q316,q319,q321,q367,q368,q369,q598,q627] (by decide +kernel) (consSafe h3_60 (consSafe h3_62 (consSafe h3_76 (consSafe h3_185 (consSafe h3_278 (consSafe h3_316 (consSafe h3_319 (consSafe h3_321 (consSafe h3_367 (consSafe h3_368 (consSafe h3_369 (consSafe h3_598 (consSafe h3_627 (nilSafe 3))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_29 : ¬Prog q29.toFinset 4 := localSound 3 q29 [q59,q64,q125,q187,q271,q295,q311,q314,q382,q383,q384,q603,q615] (by decide +kernel) (consSafe h3_59 (consSafe h3_64 (consSafe h3_125 (consSafe h3_187 (consSafe h3_271 (consSafe h3_295 (consSafe h3_311 (consSafe h3_314 (consSafe h3_382 (consSafe h3_383 (consSafe h3_384 (consSafe h3_603 (consSafe h3_615 (nilSafe 3))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_31 : ¬Prog q31.toFinset 4 := localSound 3 q31 [q54,q61,q89,q208,q247,q250,q252,q258,q411,q412,q540,q573,q588] (by decide +kernel) (consSafe h3_54 (consSafe h3_61 (consSafe h3_89 (consSafe h3_208 (consSafe h3_247 (consSafe h3_250 (consSafe h3_252 (consSafe h3_258 (consSafe h3_411 (consSafe h3_412 (consSafe h3_540 (consSafe h3_573 (consSafe h3_588 (nilSafe 3))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_33 : ¬Prog q33.toFinset 4 := localSound 3 q33 [q53,q63,q145,q201,q225,q242,q245,q260,q423,q424,q546,q561,q591] (by decide +kernel) (consSafe h3_53 (consSafe h3_63 (consSafe h3_145 (consSafe h3_201 (consSafe h3_225 (consSafe h3_242 (consSafe h3_245 (consSafe h3_260 (consSafe h3_423 (consSafe h3_424 (consSafe h3_546 (consSafe h3_561 (consSafe h3_591 (nilSafe 3))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_36 : ¬Prog q36.toFinset 4 := localSound 3 q36 [q52,q58,q140,q159,q176,q179,q214,q285,q455,q520,q528,q556,q610] (by decide +kernel) (consSafe h3_52 (consSafe h3_58 (consSafe h3_140 (consSafe h3_159 (consSafe h3_176 (consSafe h3_179 (consSafe h3_214 (consSafe h3_285 (consSafe h3_455 (consSafe h3_520 (consSafe h3_528 (consSafe h3_556 (consSafe h3_610 (nilSafe 3))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_39 : ¬Prog q39.toFinset 4 := localSound 3 q39 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_43 : ¬Prog q43.toFinset 4 := localSound 3 q43 [q65,q195,q265,q504,q553,q607] (by decide +kernel) (consSafe h3_65 (consSafe h3_195 (consSafe h3_265 (consSafe h3_504 (consSafe h3_553 (consSafe h3_607 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_44 : ¬Prog q44.toFinset 4 := localSound 3 q44 [q60,q134,q290,q505,q526,q618] (by decide +kernel) (consSafe h3_60 (consSafe h3_134 (consSafe h3_290 (consSafe h3_505 (consSafe h3_526 (consSafe h3_618 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_45 : ¬Prog q45.toFinset 4 := localSound 3 q45 [q54,q154,q220,q509,q533,q564] (by decide +kernel) (consSafe h3_54 (consSafe h3_154 (consSafe h3_220 (consSafe h3_509 (consSafe h3_533 (consSafe h3_564 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_46 : ¬Prog q46.toFinset 4 := localSound 3 q46 [q66,q196,q266,q517,q554,q608] (by decide +kernel) (consSafe h3_66 (consSafe h3_196 (consSafe h3_266 (consSafe h3_517 (consSafe h3_554 (consSafe h3_608 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_47 : ¬Prog q47.toFinset 4 := localSound 3 q47 [q59,q86,q304,q521,q522,q623] (by decide +kernel) (consSafe h3_59 (consSafe h3_86 (consSafe h3_304 (consSafe h3_521 (consSafe h3_522 (consSafe h3_623 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_48 : ¬Prog q48.toFinset 4 := localSound 3 q48 [q53,q99,q235,q529,q530,q569] (by decide +kernel) (consSafe h3_53 (consSafe h3_99 (consSafe h3_235 (consSafe h3_529 (consSafe h3_530 (consSafe h3_569 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_49 : ¬Prog q49.toFinset 4 := localSound 3 q49 [q62,q135,q291,q542,q544,q640] (by decide +kernel) (consSafe h3_62 (consSafe h3_135 (consSafe h3_291 (consSafe h3_542 (consSafe h3_544 (consSafe h3_640 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_50 : ¬Prog q50.toFinset 4 := localSound 3 q50 [q64,q87,q305,q547,q548,q646] (by decide +kernel) (consSafe h3_64 (consSafe h3_87 (consSafe h3_305 (consSafe h3_547 (consSafe h3_548 (consSafe h3_646 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_51 : ¬Prog q51.toFinset 4 := localSound 3 q51 [q52,q110,q170,q559,q560,q567] (by decide +kernel) (consSafe h3_52 (consSafe h3_110 (consSafe h3_170 (consSafe h3_559 (consSafe h3_560 (consSafe h3_567 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_55 : ¬Prog q55.toFinset 4 := localSound 3 q55 [q61,q155,q222,q595,q597,q637] (by decide +kernel) (consSafe h3_61 (consSafe h3_155 (consSafe h3_222 (consSafe h3_595 (consSafe h3_597 (consSafe h3_637 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_56 : ¬Prog q56.toFinset 4 := localSound 3 q56 [q63,q100,q237,q600,q601,q643] (by decide +kernel) (consSafe h3_63 (consSafe h3_100 (consSafe h3_237 (consSafe h3_600 (consSafe h3_601 (consSafe h3_643 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_57 : ¬Prog q57.toFinset 4 := localSound 3 q57 [q58,q111,q171,q613,q614,q621] (by decide +kernel) (consSafe h3_58 (consSafe h3_111 (consSafe h3_171 (consSafe h3_613 (consSafe h3_614 (consSafe h3_621 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_67 : ¬Prog q67.toFinset 4 := localSound 3 q67 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_68 : ¬Prog q68.toFinset 4 := localSound 3 q68 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_69 : ¬Prog q69.toFinset 4 := localSound 3 q69 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_70 : ¬Prog q70.toFinset 4 := localSound 3 q70 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_71 : ¬Prog q71.toFinset 4 := localSound 3 q71 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_72 : ¬Prog q72.toFinset 4 := localSound 3 q72 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_73 : ¬Prog q73.toFinset 4 := localSound 3 q73 [q74,q458,q483,q504,q513] (by decide +kernel) (consSafe h3_74 (consSafe h3_458 (consSafe h3_483 (consSafe h3_504 (consSafe h3_513 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_75 : ¬Prog q75.toFinset 4 := localSound 3 q75 [q76,q427,q483,q505,q535] (by decide +kernel) (consSafe h3_76 (consSafe h3_427 (consSafe h3_483 (consSafe h3_505 (consSafe h3_535 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_77 : ¬Prog q77.toFinset 4 := localSound 3 q77 [q141] (by decide +kernel) (consSafe h3_141 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_78 : ¬Prog q78.toFinset 4 := localSound 3 q78 [q202] (by decide +kernel) (consSafe h3_202 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_79 : ¬Prog q79.toFinset 4 := localSound 3 q79 [q312] (by decide +kernel) (consSafe h3_312 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_80 : ¬Prog q80.toFinset 4 := localSound 3 q80 [q313] (by decide +kernel) (consSafe h3_313 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_81 : ¬Prog q81.toFinset 4 := localSound 3 q81 [q86,q87,q382,q483] (by decide +kernel) (consSafe h3_86 (consSafe h3_87 (consSafe h3_382 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_82 : ¬Prog q82.toFinset 4 := localSound 3 q82 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_83 : ¬Prog q83.toFinset 4 := localSound 3 q83 [q382,q483] (by decide +kernel) (consSafe h3_382 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_84 : ¬Prog q84.toFinset 4 := localSound 3 q84 [q74] (by decide +kernel) (consSafe h3_74 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_85 : ¬Prog q85.toFinset 4 := localSound 3 q85 [q76] (by decide +kernel) (consSafe h3_76 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_88 : ¬Prog q88.toFinset 4 := localSound 3 q88 [q89,q387,q483,q509,q581] (by decide +kernel) (consSafe h3_89 (consSafe h3_387 (consSafe h3_483 (consSafe h3_509 (consSafe h3_581 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_90 : ¬Prog q90.toFinset 4 := localSound 3 q90 [q160] (by decide +kernel) (consSafe h3_160 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_91 : ¬Prog q91.toFinset 4 := localSound 3 q91 [q243] (by decide +kernel) (consSafe h3_243 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_92 : ¬Prog q92.toFinset 4 := localSound 3 q92 [q244] (by decide +kernel) (consSafe h3_244 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_93 : ¬Prog q93.toFinset 4 := localSound 3 q93 [q273] (by decide +kernel) (consSafe h3_273 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_94 : ¬Prog q94.toFinset 4 := localSound 3 q94 [q99,q100,q423,q483] (by decide +kernel) (consSafe h3_99 (consSafe h3_100 (consSafe h3_423 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_95 : ¬Prog q95.toFinset 4 := localSound 3 q95 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_96 : ¬Prog q96.toFinset 4 := localSound 3 q96 [q423,q483] (by decide +kernel) (consSafe h3_423 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_97 : ¬Prog q97.toFinset 4 := localSound 3 q97 [q74] (by decide +kernel) (consSafe h3_74 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_98 : ¬Prog q98.toFinset 4 := localSound 3 q98 [q89] (by decide +kernel) (consSafe h3_89 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_101 : ¬Prog q101.toFinset 4 := localSound 3 q101 [q177] (by decide +kernel) (consSafe h3_177 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_102 : ¬Prog q102.toFinset 4 := localSound 3 q102 [q178] (by decide +kernel) (consSafe h3_178 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_103 : ¬Prog q103.toFinset 4 := localSound 3 q103 [q227] (by decide +kernel) (consSafe h3_227 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_104 : ¬Prog q104.toFinset 4 := localSound 3 q104 [q297] (by decide +kernel) (consSafe h3_297 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_105 : ¬Prog q105.toFinset 4 := localSound 3 q105 [q110,q111,q455,q483] (by decide +kernel) (consSafe h3_110 (consSafe h3_111 (consSafe h3_455 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_106 : ¬Prog q106.toFinset 4 := localSound 3 q106 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_107 : ¬Prog q107.toFinset 4 := localSound 3 q107 [q455,q483] (by decide +kernel) (consSafe h3_455 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_108 : ¬Prog q108.toFinset 4 := localSound 3 q108 [q76] (by decide +kernel) (consSafe h3_76 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_109 : ¬Prog q109.toFinset 4 := localSound 3 q109 [q89] (by decide +kernel) (consSafe h3_89 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_112 : ¬Prog q112.toFinset 4 := localSound 3 q112 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_113 : ¬Prog q113.toFinset 4 := localSound 3 q113 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_114 : ¬Prog q114.toFinset 4 := localSound 3 q114 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_116 : ¬Prog q116.toFinset 4 := localSound 3 q116 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_117 : ¬Prog q117.toFinset 4 := localSound 3 q117 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_119 : ¬Prog q119.toFinset 4 := localSound 3 q119 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_120 : ¬Prog q120.toFinset 4 := localSound 3 q120 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_122 : ¬Prog q122.toFinset 4 := localSound 3 q122 [q123,q472,q483,q500,q517] (by decide +kernel) (consSafe h3_123 (consSafe h3_472 (consSafe h3_483 (consSafe h3_500 (consSafe h3_517 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_124 : ¬Prog q124.toFinset 4 := localSound 3 q124 [q125,q416,q483,q521,q536] (by decide +kernel) (consSafe h3_125 (consSafe h3_416 (consSafe h3_483 (consSafe h3_521 (consSafe h3_536 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_126 : ¬Prog q126.toFinset 4 := localSound 3 q126 [q209] (by decide +kernel) (consSafe h3_209 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_127 : ¬Prog q127.toFinset 4 := localSound 3 q127 [q317] (by decide +kernel) (consSafe h3_317 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_128 : ¬Prog q128.toFinset 4 := localSound 3 q128 [q318] (by decide +kernel) (consSafe h3_318 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_129 : ¬Prog q129.toFinset 4 := localSound 3 q129 [q134,q135,q367,q483] (by decide +kernel) (consSafe h3_134 (consSafe h3_135 (consSafe h3_367 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_130 : ¬Prog q130.toFinset 4 := localSound 3 q130 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_131 : ¬Prog q131.toFinset 4 := localSound 3 q131 [q367,q483] (by decide +kernel) (consSafe h3_367 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_132 : ¬Prog q132.toFinset 4 := localSound 3 q132 [q123] (by decide +kernel) (consSafe h3_123 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_133 : ¬Prog q133.toFinset 4 := localSound 3 q133 [q125] (by decide +kernel) (consSafe h3_125 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_138 : ¬Prog q138.toFinset 4 := localSound 3 q138 [q141,q483] (by decide +kernel) (consSafe h3_141 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_139 : ¬Prog q139.toFinset 4 := localSound 3 q139 [q137,q140,q141,q142,q613] (by decide +kernel) (consSafe h3_137 (consSafe h3_140 (consSafe h3_141 (consSafe h3_142 (consSafe h3_613 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_144 : ¬Prog q144.toFinset 4 := localSound 3 q144 [q145,q373,q483,q529,q583] (by decide +kernel) (consSafe h3_145 (consSafe h3_373 (consSafe h3_483 (consSafe h3_529 (consSafe h3_583 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_146 : ¬Prog q146.toFinset 4 := localSound 3 q146 [q248] (by decide +kernel) (consSafe h3_248 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_147 : ¬Prog q147.toFinset 4 := localSound 3 q147 [q249] (by decide +kernel) (consSafe h3_249 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_148 : ¬Prog q148.toFinset 4 := localSound 3 q148 [q280] (by decide +kernel) (consSafe h3_280 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_149 : ¬Prog q149.toFinset 4 := localSound 3 q149 [q154,q155,q411,q483] (by decide +kernel) (consSafe h3_154 (consSafe h3_155 (consSafe h3_411 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_150 : ¬Prog q150.toFinset 4 := localSound 3 q150 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_151 : ¬Prog q151.toFinset 4 := localSound 3 q151 [q411,q483] (by decide +kernel) (consSafe h3_411 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_152 : ¬Prog q152.toFinset 4 := localSound 3 q152 [q123] (by decide +kernel) (consSafe h3_123 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_153 : ¬Prog q153.toFinset 4 := localSound 3 q153 [q145] (by decide +kernel) (consSafe h3_145 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_157 : ¬Prog q157.toFinset 4 := localSound 3 q157 [q160,q483] (by decide +kernel) (consSafe h3_160 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_158 : ¬Prog q158.toFinset 4 := localSound 3 q158 [q137,q159,q160,q161,q559] (by decide +kernel) (consSafe h3_137 (consSafe h3_159 (consSafe h3_160 (consSafe h3_161 (consSafe h3_559 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_163 : ¬Prog q163.toFinset 4 := localSound 3 q163 [q253] (by decide +kernel) (consSafe h3_253 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_164 : ¬Prog q164.toFinset 4 := localSound 3 q164 [q322] (by decide +kernel) (consSafe h3_322 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_165 : ¬Prog q165.toFinset 4 := localSound 3 q165 [q170,q171,q455,q483] (by decide +kernel) (consSafe h3_170 (consSafe h3_171 (consSafe h3_455 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_166 : ¬Prog q166.toFinset 4 := localSound 3 q166 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_167 : ¬Prog q167.toFinset 4 := localSound 3 q167 [q125] (by decide +kernel) (consSafe h3_125 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_168 : ¬Prog q168.toFinset 4 := localSound 3 q168 [q145] (by decide +kernel) (consSafe h3_145 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_169 : ¬Prog q169.toFinset 4 := localSound 3 q169 [q455,q483] (by decide +kernel) (consSafe h3_455 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_172 : ¬Prog q172.toFinset 4 := localSound 3 q172 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_173 : ¬Prog q173.toFinset 4 := localSound 3 q173 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_174 : ¬Prog q174.toFinset 4 := localSound 3 q174 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_180 : ¬Prog q180.toFinset 4 := localSound 3 q180 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_181 : ¬Prog q181.toFinset 4 := localSound 3 q181 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_184 : ¬Prog q184.toFinset 4 := localSound 3 q184 [q185,q444,q483,q501,q542] (by decide +kernel) (consSafe h3_185 (consSafe h3_444 (consSafe h3_483 (consSafe h3_501 (consSafe h3_542 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_186 : ¬Prog q186.toFinset 4 := localSound 3 q186 [q187,q440,q483,q514,q547] (by decide +kernel) (consSafe h3_187 (consSafe h3_440 (consSafe h3_483 (consSafe h3_514 (consSafe h3_547 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_188 : ¬Prog q188.toFinset 4 := localSound 3 q188 [q327] (by decide +kernel) (consSafe h3_327 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_189 : ¬Prog q189.toFinset 4 := localSound 3 q189 [q328] (by decide +kernel) (consSafe h3_328 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_190 : ¬Prog q190.toFinset 4 := localSound 3 q190 [q195,q196,q352,q483] (by decide +kernel) (consSafe h3_195 (consSafe h3_196 (consSafe h3_352 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_191 : ¬Prog q191.toFinset 4 := localSound 3 q191 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_192 : ¬Prog q192.toFinset 4 := localSound 3 q192 [q352,q483] (by decide +kernel) (consSafe h3_352 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_193 : ¬Prog q193.toFinset 4 := localSound 3 q193 [q185] (by decide +kernel) (consSafe h3_185 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_194 : ¬Prog q194.toFinset 4 := localSound 3 q194 [q187] (by decide +kernel) (consSafe h3_187 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_199 : ¬Prog q199.toFinset 4 := localSound 3 q199 [q202,q483] (by decide +kernel) (consSafe h3_202 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_200 : ¬Prog q200.toFinset 4 := localSound 3 q200 [q198,q201,q202,q203,q600] (by decide +kernel) (consSafe h3_198 (consSafe h3_201 (consSafe h3_202 (consSafe h3_203 (consSafe h3_600 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_206 : ¬Prog q206.toFinset 4 := localSound 3 q206 [q209,q483] (by decide +kernel) (consSafe h3_209 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_207 : ¬Prog q207.toFinset 4 := localSound 3 q207 [q205,q208,q209,q210,q595] (by decide +kernel) (consSafe h3_205 (consSafe h3_208 (consSafe h3_209 (consSafe h3_210 (consSafe h3_595 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_213 : ¬Prog q213.toFinset 4 := localSound 3 q213 [q214,q358,q483,q559,q585] (by decide +kernel) (consSafe h3_214 (consSafe h3_358 (consSafe h3_483 (consSafe h3_559 (consSafe h3_585 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_215 : ¬Prog q215.toFinset 4 := localSound 3 q215 [q334] (by decide +kernel) (consSafe h3_334 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_216 : ¬Prog q216.toFinset 4 := localSound 3 q216 [q220,q222,q411,q483] (by decide +kernel) (consSafe h3_220 (consSafe h3_222 (consSafe h3_411 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_217 : ¬Prog q217.toFinset 4 := localSound 3 q217 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_218 : ¬Prog q218.toFinset 4 := localSound 3 q218 [q185] (by decide +kernel) (consSafe h3_185 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_219 : ¬Prog q219.toFinset 4 := localSound 3 q219 [q214] (by decide +kernel) (consSafe h3_214 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_221 : ¬Prog q221.toFinset 4 := localSound 3 q221 [q411,q483] (by decide +kernel) (consSafe h3_411 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_224 : ¬Prog q224.toFinset 4 := localSound 3 q224 [q198,q225,q227,q228,q529] (by decide +kernel) (consSafe h3_198 (consSafe h3_225 (consSafe h3_227 (consSafe h3_228 (consSafe h3_529 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_226 : ¬Prog q226.toFinset 4 := localSound 3 q226 [q227,q483] (by decide +kernel) (consSafe h3_227 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_230 : ¬Prog q230.toFinset 4 := localSound 3 q230 [q340] (by decide +kernel) (consSafe h3_340 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_231 : ¬Prog q231.toFinset 4 := localSound 3 q231 [q235,q237,q423,q483] (by decide +kernel) (consSafe h3_235 (consSafe h3_237 (consSafe h3_423 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_232 : ¬Prog q232.toFinset 4 := localSound 3 q232 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_233 : ¬Prog q233.toFinset 4 := localSound 3 q233 [q187] (by decide +kernel) (consSafe h3_187 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_234 : ¬Prog q234.toFinset 4 := localSound 3 q234 [q214] (by decide +kernel) (consSafe h3_214 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_236 : ¬Prog q236.toFinset 4 := localSound 3 q236 [q423,q483] (by decide +kernel) (consSafe h3_423 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_238 : ¬Prog q238.toFinset 4 := localSound 3 q238 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_239 : ¬Prog q239.toFinset 4 := localSound 3 q239 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_240 : ¬Prog q240.toFinset 4 := localSound 3 q240 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_251 : ¬Prog q251.toFinset 4 := localSound 3 q251 [q205,q252,q253,q255,q509] (by decide +kernel) (consSafe h3_205 (consSafe h3_252 (consSafe h3_253 (consSafe h3_255 (consSafe h3_509 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_254 : ¬Prog q254.toFinset 4 := localSound 3 q254 [q253,q483] (by decide +kernel) (consSafe h3_253 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_257 : ¬Prog q257.toFinset 4 := localSound 3 q257 [q258,q405,q483,q502,q595] (by decide +kernel) (consSafe h3_258 (consSafe h3_405 (consSafe h3_483 (consSafe h3_502 (consSafe h3_595 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_259 : ¬Prog q259.toFinset 4 := localSound 3 q259 [q260,q401,q483,q515,q600] (by decide +kernel) (consSafe h3_260 (consSafe h3_401 (consSafe h3_483 (consSafe h3_515 (consSafe h3_600 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_261 : ¬Prog q261.toFinset 4 := localSound 3 q261 [q265,q266,q352,q483] (by decide +kernel) (consSafe h3_265 (consSafe h3_266 (consSafe h3_352 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_262 : ¬Prog q262.toFinset 4 := localSound 3 q262 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_263 : ¬Prog q263.toFinset 4 := localSound 3 q263 [q258] (by decide +kernel) (consSafe h3_258 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_264 : ¬Prog q264.toFinset 4 := localSound 3 q264 [q260] (by decide +kernel) (consSafe h3_260 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_267 : ¬Prog q267.toFinset 4 := localSound 3 q267 [q352,q483] (by decide +kernel) (consSafe h3_352 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_270 : ¬Prog q270.toFinset 4 := localSound 3 q270 [q269,q271,q273,q274,q547] (by decide +kernel) (consSafe h3_269 (consSafe h3_271 (consSafe h3_273 (consSafe h3_274 (consSafe h3_547 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_272 : ¬Prog q272.toFinset 4 := localSound 3 q272 [q273,q483] (by decide +kernel) (consSafe h3_273 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_277 : ¬Prog q277.toFinset 4 := localSound 3 q277 [q276,q278,q280,q281,q542] (by decide +kernel) (consSafe h3_276 (consSafe h3_278 (consSafe h3_280 (consSafe h3_281 (consSafe h3_542 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_279 : ¬Prog q279.toFinset 4 := localSound 3 q279 [q280,q483] (by decide +kernel) (consSafe h3_280 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_284 : ¬Prog q284.toFinset 4 := localSound 3 q284 [q285,q360,q483,q537,q613] (by decide +kernel) (consSafe h3_285 (consSafe h3_360 (consSafe h3_483 (consSafe h3_537 (consSafe h3_613 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_286 : ¬Prog q286.toFinset 4 := localSound 3 q286 [q290,q291,q367,q483] (by decide +kernel) (consSafe h3_290 (consSafe h3_291 (consSafe h3_367 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_287 : ¬Prog q287.toFinset 4 := localSound 3 q287 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_288 : ¬Prog q288.toFinset 4 := localSound 3 q288 [q258] (by decide +kernel) (consSafe h3_258 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_289 : ¬Prog q289.toFinset 4 := localSound 3 q289 [q285] (by decide +kernel) (consSafe h3_285 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_292 : ¬Prog q292.toFinset 4 := localSound 3 q292 [q367,q483] (by decide +kernel) (consSafe h3_367 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_294 : ¬Prog q294.toFinset 4 := localSound 3 q294 [q269,q295,q297,q298,q521] (by decide +kernel) (consSafe h3_269 (consSafe h3_295 (consSafe h3_297 (consSafe h3_298 (consSafe h3_521 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_296 : ¬Prog q296.toFinset 4 := localSound 3 q296 [q297,q483] (by decide +kernel) (consSafe h3_297 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_300 : ¬Prog q300.toFinset 4 := localSound 3 q300 [q304,q305,q382,q483] (by decide +kernel) (consSafe h3_304 (consSafe h3_305 (consSafe h3_382 (consSafe h3_483 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_301 : ¬Prog q301.toFinset 4 := localSound 3 q301 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_302 : ¬Prog q302.toFinset 4 := localSound 3 q302 [q260] (by decide +kernel) (consSafe h3_260 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_303 : ¬Prog q303.toFinset 4 := localSound 3 q303 [q285] (by decide +kernel) (consSafe h3_285 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_306 : ¬Prog q306.toFinset 4 := localSound 3 q306 [q382,q483] (by decide +kernel) (consSafe h3_382 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_307 : ¬Prog q307.toFinset 4 := localSound 3 q307 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_308 : ¬Prog q308.toFinset 4 := localSound 3 q308 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_309 : ¬Prog q309.toFinset 4 := localSound 3 q309 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_320 : ¬Prog q320.toFinset 4 := localSound 3 q320 [q276,q321,q322,q324,q505] (by decide +kernel) (consSafe h3_276 (consSafe h3_321 (consSafe h3_322 (consSafe h3_324 (consSafe h3_505 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_323 : ¬Prog q323.toFinset 4 := localSound 3 q323 [q322,q483] (by decide +kernel) (consSafe h3_322 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_331 : ¬Prog q331.toFinset 4 := localSound 3 q331 [q330,q332,q334,q335,q517] (by decide +kernel) (consSafe h3_330 (consSafe h3_332 (consSafe h3_334 (consSafe h3_335 (consSafe h3_517 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_333 : ¬Prog q333.toFinset 4 := localSound 3 q333 [q334,q483] (by decide +kernel) (consSafe h3_334 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_338 : ¬Prog q338.toFinset 4 := localSound 3 q338 [q330,q339,q340,q342,q504] (by decide +kernel) (consSafe h3_330 (consSafe h3_339 (consSafe h3_340 (consSafe h3_342 (consSafe h3_504 (nilSafe 3))))))
set_option maxHeartbeats 10000000 in
private theorem h4_341 : ¬Prog q341.toFinset 4 := localSound 3 q341 [q340,q483] (by decide +kernel) (consSafe h3_340 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_345 : ¬Prog q345.toFinset 4 := localSound 3 q345 [q209,q280,q334,q344,q483,q503] (by decide +kernel) (consSafe h3_209 (consSafe h3_280 (consSafe h3_334 (consSafe h3_344 (consSafe h3_483 (consSafe h3_503 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_346 : ¬Prog q346.toFinset 4 := localSound 3 q346 [q202,q273,q337,q340,q483,q516] (by decide +kernel) (consSafe h3_202 (consSafe h3_273 (consSafe h3_337 (consSafe h3_340 (consSafe h3_483 (consSafe h3_516 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_347 : ¬Prog q347.toFinset 4 := localSound 3 q347 [q334,q340,q352,q483,q504,q517] (by decide +kernel) (consSafe h3_334 (consSafe h3_340 (consSafe h3_352 (consSafe h3_483 (consSafe h3_504 (consSafe h3_517 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_348 : ¬Prog q348.toFinset 4 := localSound 3 q348 [q195,q265,q335,q340,q353,q504,q518,q553,q607] (by decide +kernel) (consSafe h3_195 (consSafe h3_265 (consSafe h3_335 (consSafe h3_340 (consSafe h3_353 (consSafe h3_504 (consSafe h3_518 (consSafe h3_553 (consSafe h3_607 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_349 : ¬Prog q349.toFinset 4 := localSound 3 q349 [q196,q266,q334,q342,q354,q517,q518,q554,q608] (by decide +kernel) (consSafe h3_196 (consSafe h3_266 (consSafe h3_334 (consSafe h3_342 (consSafe h3_354 (consSafe h3_517 (consSafe h3_518 (consSafe h3_554 (consSafe h3_608 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_350 : ¬Prog q350.toFinset 4 := localSound 3 q350 [q74,q123,q326,q327,q329,q332,q339,q352,q353,q354,q553,q554,q653,q654] (by decide +kernel) (consSafe h3_74 (consSafe h3_123 (consSafe h3_326 (consSafe h3_327 (consSafe h3_329 (consSafe h3_332 (consSafe h3_339 (consSafe h3_352 (consSafe h3_353 (consSafe h3_354 (consSafe h3_553 (consSafe h3_554 (consSafe h3_653 (consSafe h3_654 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_351 : ¬Prog q351.toFinset 4 := localSound 3 q351 [q74,q123,q326,q328,q329,q332,q339,q352,q353,q354,q607,q608,q653,q654] (by decide +kernel) (consSafe h3_74 (consSafe h3_123 (consSafe h3_326 (consSafe h3_328 (consSafe h3_329 (consSafe h3_332 (consSafe h3_339 (consSafe h3_352 (consSafe h3_353 (consSafe h3_354 (consSafe h3_607 (consSafe h3_608 (consSafe h3_653 (consSafe h3_654 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_355 : ¬Prog q355.toFinset 4 := localSound 3 q355 [q340,q483] (by decide +kernel) (consSafe h3_340 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_356 : ¬Prog q356.toFinset 4 := localSound 3 q356 [q340,q483] (by decide +kernel) (consSafe h3_340 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_357 : ¬Prog q357.toFinset 4 := localSound 3 q357 [q334,q483] (by decide +kernel) (consSafe h3_334 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_359 : ¬Prog q359.toFinset 4 := localSound 3 q359 [q334,q483] (by decide +kernel) (consSafe h3_334 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_361 : ¬Prog q361.toFinset 4 := localSound 3 q361 [q141,q283,q297,q322,q483,q541] (by decide +kernel) (consSafe h3_141 (consSafe h3_283 (consSafe h3_297 (consSafe h3_322 (consSafe h3_483 (consSafe h3_541 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_362 : ¬Prog q362.toFinset 4 := localSound 3 q362 [q280,q322,q367,q483,q505,q542] (by decide +kernel) (consSafe h3_280 (consSafe h3_322 (consSafe h3_367 (consSafe h3_483 (consSafe h3_505 (consSafe h3_542 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_363 : ¬Prog q363.toFinset 4 := localSound 3 q363 [q134,q281,q290,q322,q368,q505,q526,q543,q618] (by decide +kernel) (consSafe h3_134 (consSafe h3_281 (consSafe h3_290 (consSafe h3_322 (consSafe h3_368 (consSafe h3_505 (consSafe h3_526 (consSafe h3_543 (consSafe h3_618 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_364 : ¬Prog q364.toFinset 4 := localSound 3 q364 [q76,q185,q278,q316,q317,q319,q321,q367,q368,q369,q526,q544,q598,q627] (by decide +kernel) (consSafe h3_76 (consSafe h3_185 (consSafe h3_278 (consSafe h3_316 (consSafe h3_317 (consSafe h3_319 (consSafe h3_321 (consSafe h3_367 (consSafe h3_368 (consSafe h3_369 (consSafe h3_526 (consSafe h3_544 (consSafe h3_598 (consSafe h3_627 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_365 : ¬Prog q365.toFinset 4 := localSound 3 q365 [q135,q280,q291,q324,q369,q542,q543,q544,q640] (by decide +kernel) (consSafe h3_135 (consSafe h3_280 (consSafe h3_291 (consSafe h3_324 (consSafe h3_369 (consSafe h3_542 (consSafe h3_543 (consSafe h3_544 (consSafe h3_640 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_366 : ¬Prog q366.toFinset 4 := localSound 3 q366 [q76,q185,q278,q316,q318,q319,q321,q367,q368,q369,q598,q618,q627,q640] (by decide +kernel) (consSafe h3_76 (consSafe h3_185 (consSafe h3_278 (consSafe h3_316 (consSafe h3_318 (consSafe h3_319 (consSafe h3_321 (consSafe h3_367 (consSafe h3_368 (consSafe h3_369 (consSafe h3_598 (consSafe h3_618 (consSafe h3_627 (consSafe h3_640 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_370 : ¬Prog q370.toFinset 4 := localSound 3 q370 [q322,q483] (by decide +kernel) (consSafe h3_322 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_371 : ¬Prog q371.toFinset 4 := localSound 3 q371 [q322,q483] (by decide +kernel) (consSafe h3_322 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_372 : ¬Prog q372.toFinset 4 := localSound 3 q372 [q280,q483] (by decide +kernel) (consSafe h3_280 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_374 : ¬Prog q374.toFinset 4 := localSound 3 q374 [q315,q375,q376,q483,q506,q517,q542] (by decide +kernel) (consSafe h3_315 (consSafe h3_375 (consSafe h3_376 (consSafe h3_483 (consSafe h3_506 (consSafe h3_517 (consSafe h3_542 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_377 : ¬Prog q377.toFinset 4 := localSound 3 q377 [q273,q297,q382,q483,q521,q547] (by decide +kernel) (consSafe h3_273 (consSafe h3_297 (consSafe h3_382 (consSafe h3_483 (consSafe h3_521 (consSafe h3_547 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_378 : ¬Prog q378.toFinset 4 := localSound 3 q378 [q125,q187,q271,q295,q311,q312,q314,q382,q383,q384,q522,q548,q603,q615] (by decide +kernel) (consSafe h3_125 (consSafe h3_187 (consSafe h3_271 (consSafe h3_295 (consSafe h3_311 (consSafe h3_312 (consSafe h3_314 (consSafe h3_382 (consSafe h3_383 (consSafe h3_384 (consSafe h3_522 (consSafe h3_548 (consSafe h3_603 (consSafe h3_615 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_379 : ¬Prog q379.toFinset 4 := localSound 3 q379 [q86,q274,q297,q304,q383,q521,q522,q549,q623] (by decide +kernel) (consSafe h3_86 (consSafe h3_274 (consSafe h3_297 (consSafe h3_304 (consSafe h3_383 (consSafe h3_521 (consSafe h3_522 (consSafe h3_549 (consSafe h3_623 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_380 : ¬Prog q380.toFinset 4 := localSound 3 q380 [q87,q273,q298,q305,q384,q547,q548,q549,q646] (by decide +kernel) (consSafe h3_87 (consSafe h3_273 (consSafe h3_298 (consSafe h3_305 (consSafe h3_384 (consSafe h3_547 (consSafe h3_548 (consSafe h3_549 (consSafe h3_646 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_381 : ¬Prog q381.toFinset 4 := localSound 3 q381 [q125,q187,q271,q295,q311,q313,q314,q382,q383,q384,q603,q615,q623,q646] (by decide +kernel) (consSafe h3_125 (consSafe h3_187 (consSafe h3_271 (consSafe h3_295 (consSafe h3_311 (consSafe h3_313 (consSafe h3_314 (consSafe h3_382 (consSafe h3_383 (consSafe h3_384 (consSafe h3_603 (consSafe h3_615 (consSafe h3_623 (consSafe h3_646 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_385 : ¬Prog q385.toFinset 4 := localSound 3 q385 [q297,q483] (by decide +kernel) (consSafe h3_297 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_386 : ¬Prog q386.toFinset 4 := localSound 3 q386 [q273,q483] (by decide +kernel) (consSafe h3_273 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_388 : ¬Prog q388.toFinset 4 := localSound 3 q388 [q293,q389,q390,q483,q504,q523,q547] (by decide +kernel) (consSafe h3_293 (consSafe h3_389 (consSafe h3_390 (consSafe h3_483 (consSafe h3_504 (consSafe h3_523 (consSafe h3_547 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_391 : ¬Prog q391.toFinset 4 := localSound 3 q391 [q268,q392,q393,q483,q505,q521,q550] (by decide +kernel) (consSafe h3_268 (consSafe h3_392 (consSafe h3_393 (consSafe h3_483 (consSafe h3_505 (consSafe h3_521 (consSafe h3_550 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_395 : ¬Prog q395.toFinset 4 := localSound 3 q395 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_396 : ¬Prog q396.toFinset 4 := localSound 3 q396 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_397 : ¬Prog q397.toFinset 4 := localSound 3 q397 [q297,q483] (by decide +kernel) (consSafe h3_297 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_398 : ¬Prog q398.toFinset 4 := localSound 3 q398 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_399 : ¬Prog q399.toFinset 4 := localSound 3 q399 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_400 : ¬Prog q400.toFinset 4 := localSound 3 q400 [q280,q483] (by decide +kernel) (consSafe h3_280 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_402 : ¬Prog q402.toFinset 4 := localSound 3 q402 [q273,q483] (by decide +kernel) (consSafe h3_273 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_403 : ¬Prog q403.toFinset 4 := localSound 3 q403 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_404 : ¬Prog q404.toFinset 4 := localSound 3 q404 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_406 : ¬Prog q406.toFinset 4 := localSound 3 q406 [q160,q212,q227,q253,q483,q594] (by decide +kernel) (consSafe h3_160 (consSafe h3_212 (consSafe h3_227 (consSafe h3_253 (consSafe h3_483 (consSafe h3_594 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_407 : ¬Prog q407.toFinset 4 := localSound 3 q407 [q209,q253,q411,q483,q509,q595] (by decide +kernel) (consSafe h3_209 (consSafe h3_253 (consSafe h3_411 (consSafe h3_483 (consSafe h3_509 (consSafe h3_595 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_408 : ¬Prog q408.toFinset 4 := localSound 3 q408 [q154,q210,q220,q253,q412,q509,q533,q564,q596] (by decide +kernel) (consSafe h3_154 (consSafe h3_210 (consSafe h3_220 (consSafe h3_253 (consSafe h3_412 (consSafe h3_509 (consSafe h3_533 (consSafe h3_564 (consSafe h3_596 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_409 : ¬Prog q409.toFinset 4 := localSound 3 q409 [q89,q208,q247,q248,q250,q252,q258,q411,q412,q533,q540,q573,q588,q597] (by decide +kernel) (consSafe h3_89 (consSafe h3_208 (consSafe h3_247 (consSafe h3_248 (consSafe h3_250 (consSafe h3_252 (consSafe h3_258 (consSafe h3_411 (consSafe h3_412 (consSafe h3_533 (consSafe h3_540 (consSafe h3_573 (consSafe h3_588 (consSafe h3_597 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_410 : ¬Prog q410.toFinset 4 := localSound 3 q410 [q89,q208,q247,q249,q250,q252,q258,q411,q412,q540,q564,q573,q588,q637] (by decide +kernel) (consSafe h3_89 (consSafe h3_208 (consSafe h3_247 (consSafe h3_249 (consSafe h3_250 (consSafe h3_252 (consSafe h3_258 (consSafe h3_411 (consSafe h3_412 (consSafe h3_540 (consSafe h3_564 (consSafe h3_573 (consSafe h3_588 (consSafe h3_637 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_413 : ¬Prog q413.toFinset 4 := localSound 3 q413 [q253,q483] (by decide +kernel) (consSafe h3_253 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_414 : ¬Prog q414.toFinset 4 := localSound 3 q414 [q253,q483] (by decide +kernel) (consSafe h3_253 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_415 : ¬Prog q415.toFinset 4 := localSound 3 q415 [q209,q483] (by decide +kernel) (consSafe h3_209 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_417 : ¬Prog q417.toFinset 4 := localSound 3 q417 [q246,q418,q483,q510,q517,q589,q595] (by decide +kernel) (consSafe h3_246 (consSafe h3_418 (consSafe h3_483 (consSafe h3_510 (consSafe h3_517 (consSafe h3_589 (consSafe h3_595 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_419 : ¬Prog q419.toFinset 4 := localSound 3 q419 [q202,q227,q423,q483,q529,q600] (by decide +kernel) (consSafe h3_202 (consSafe h3_227 (consSafe h3_423 (consSafe h3_483 (consSafe h3_529 (consSafe h3_600 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_420 : ¬Prog q420.toFinset 4 := localSound 3 q420 [q145,q201,q225,q242,q243,q245,q260,q423,q424,q530,q546,q561,q591,q601] (by decide +kernel) (consSafe h3_145 (consSafe h3_201 (consSafe h3_225 (consSafe h3_242 (consSafe h3_243 (consSafe h3_245 (consSafe h3_260 (consSafe h3_423 (consSafe h3_424 (consSafe h3_530 (consSafe h3_546 (consSafe h3_561 (consSafe h3_591 (consSafe h3_601 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_421 : ¬Prog q421.toFinset 4 := localSound 3 q421 [q99,q203,q227,q235,q424,q529,q530,q569,q602] (by decide +kernel) (consSafe h3_99 (consSafe h3_203 (consSafe h3_227 (consSafe h3_235 (consSafe h3_424 (consSafe h3_529 (consSafe h3_530 (consSafe h3_569 (consSafe h3_602 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_422 : ¬Prog q422.toFinset 4 := localSound 3 q422 [q145,q201,q225,q242,q244,q245,q260,q423,q424,q546,q561,q569,q591,q643] (by decide +kernel) (consSafe h3_145 (consSafe h3_201 (consSafe h3_225 (consSafe h3_242 (consSafe h3_244 (consSafe h3_245 (consSafe h3_260 (consSafe h3_423 (consSafe h3_424 (consSafe h3_546 (consSafe h3_561 (consSafe h3_569 (consSafe h3_591 (consSafe h3_643 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_425 : ¬Prog q425.toFinset 4 := localSound 3 q425 [q227,q483] (by decide +kernel) (consSafe h3_227 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_426 : ¬Prog q426.toFinset 4 := localSound 3 q426 [q202,q483] (by decide +kernel) (consSafe h3_202 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_428 : ¬Prog q428.toFinset 4 := localSound 3 q428 [q223,q429,q483,q504,q531,q592,q600] (by decide +kernel) (consSafe h3_223 (consSafe h3_429 (consSafe h3_483 (consSafe h3_504 (consSafe h3_531 (consSafe h3_592 (consSafe h3_600 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_430 : ¬Prog q430.toFinset 4 := localSound 3 q430 [q197,q431,q432,q483,q509,q529,q604] (by decide +kernel) (consSafe h3_197 (consSafe h3_431 (consSafe h3_432 (consSafe h3_483 (consSafe h3_509 (consSafe h3_529 (consSafe h3_604 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_434 : ¬Prog q434.toFinset 4 := localSound 3 q434 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_435 : ¬Prog q435.toFinset 4 := localSound 3 q435 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_436 : ¬Prog q436.toFinset 4 := localSound 3 q436 [q227,q483] (by decide +kernel) (consSafe h3_227 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_437 : ¬Prog q437.toFinset 4 := localSound 3 q437 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_438 : ¬Prog q438.toFinset 4 := localSound 3 q438 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_439 : ¬Prog q439.toFinset 4 := localSound 3 q439 [q209,q483] (by decide +kernel) (consSafe h3_209 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_441 : ¬Prog q441.toFinset 4 := localSound 3 q441 [q202,q483] (by decide +kernel) (consSafe h3_202 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_442 : ¬Prog q442.toFinset 4 := localSound 3 q442 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_443 : ¬Prog q443.toFinset 4 := localSound 3 q443 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_445 : ¬Prog q445.toFinset 4 := localSound 3 q445 [q183,q483,q512,q539,q542,q593,q595] (by decide +kernel) (consSafe h3_183 (consSafe h3_483 (consSafe h3_512 (consSafe h3_539 (consSafe h3_542 (consSafe h3_593 (consSafe h3_595 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_446 : ¬Prog q446.toFinset 4 := localSound 3 q446 [q155,q222,q483,q540,q595,q597,q637] (by decide +kernel) (consSafe h3_155 (consSafe h3_222 (consSafe h3_483 (consSafe h3_540 (consSafe h3_595 (consSafe h3_597 (consSafe h3_637 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_447 : ¬Prog q447.toFinset 4 := localSound 3 q447 [q135,q291,q483,q542,q544,q598,q640] (by decide +kernel) (consSafe h3_135 (consSafe h3_291 (consSafe h3_483 (consSafe h3_542 (consSafe h3_544 (consSafe h3_598 (consSafe h3_640 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_448 : ¬Prog q448.toFinset 4 := localSound 3 q448 [q182,q483,q534,q545,q547,q599,q600] (by decide +kernel) (consSafe h3_182 (consSafe h3_483 (consSafe h3_534 (consSafe h3_545 (consSafe h3_547 (consSafe h3_599 (consSafe h3_600 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_449 : ¬Prog q449.toFinset 4 := localSound 3 q449 [q100,q237,q483,q546,q600,q601,q643] (by decide +kernel) (consSafe h3_100 (consSafe h3_237 (consSafe h3_483 (consSafe h3_546 (consSafe h3_600 (consSafe h3_601 (consSafe h3_643 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_450 : ¬Prog q450.toFinset 4 := localSound 3 q450 [q87,q305,q483,q547,q548,q603,q646] (by decide +kernel) (consSafe h3_87 (consSafe h3_305 (consSafe h3_483 (consSafe h3_547 (consSafe h3_548 (consSafe h3_603 (consSafe h3_646 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_451 : ¬Prog q451.toFinset 4 := localSound 3 q451 [q352,q483] (by decide +kernel) (consSafe h3_352 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_452 : ¬Prog q452.toFinset 4 := localSound 3 q452 [q141,q160,q455,q483,q559,q613] (by decide +kernel) (consSafe h3_141 (consSafe h3_160 (consSafe h3_455 (consSafe h3_483 (consSafe h3_559 (consSafe h3_613 (nilSafe 3)))))))
set_option maxHeartbeats 10000000 in
private theorem h4_453 : ¬Prog q453.toFinset 4 := localSound 3 q453 [q140,q159,q176,q177,q179,q214,q285,q455,q520,q528,q556,q560,q610,q614] (by decide +kernel) (consSafe h3_140 (consSafe h3_159 (consSafe h3_176 (consSafe h3_177 (consSafe h3_179 (consSafe h3_214 (consSafe h3_285 (consSafe h3_455 (consSafe h3_520 (consSafe h3_528 (consSafe h3_556 (consSafe h3_560 (consSafe h3_610 (consSafe h3_614 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_454 : ¬Prog q454.toFinset 4 := localSound 3 q454 [q140,q159,q176,q178,q179,q214,q285,q455,q520,q528,q556,q567,q610,q621] (by decide +kernel) (consSafe h3_140 (consSafe h3_159 (consSafe h3_176 (consSafe h3_178 (consSafe h3_179 (consSafe h3_214 (consSafe h3_285 (consSafe h3_455 (consSafe h3_520 (consSafe h3_528 (consSafe h3_556 (consSafe h3_567 (consSafe h3_610 (consSafe h3_621 (nilSafe 3)))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_456 : ¬Prog q456.toFinset 4 := localSound 3 q456 [q160,q483] (by decide +kernel) (consSafe h3_160 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_457 : ¬Prog q457.toFinset 4 := localSound 3 q457 [q141,q483] (by decide +kernel) (consSafe h3_141 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_459 : ¬Prog q459.toFinset 4 := localSound 3 q459 [q156,q460,q483,q505,q562,q611,q613] (by decide +kernel) (consSafe h3_156 (consSafe h3_460 (consSafe h3_483 (consSafe h3_505 (consSafe h3_562 (consSafe h3_611 (consSafe h3_613 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_461 : ¬Prog q461.toFinset 4 := localSound 3 q461 [q136,q462,q483,q509,q557,q559,q616] (by decide +kernel) (consSafe h3_136 (consSafe h3_462 (consSafe h3_483 (consSafe h3_509 (consSafe h3_557 (consSafe h3_559 (consSafe h3_616 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_464 : ¬Prog q464.toFinset 4 := localSound 3 q464 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_465 : ¬Prog q465.toFinset 4 := localSound 3 q465 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_466 : ¬Prog q466.toFinset 4 := localSound 3 q466 [q160,q483] (by decide +kernel) (consSafe h3_160 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_467 : ¬Prog q467.toFinset 4 := localSound 3 q467 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_468 : ¬Prog q468.toFinset 4 := localSound 3 q468 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_469 : ¬Prog q469.toFinset 4 := localSound 3 q469 [q141,q483] (by decide +kernel) (consSafe h3_141 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_470 : ¬Prog q470.toFinset 4 := localSound 3 q470 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_471 : ¬Prog q471.toFinset 4 := localSound 3 q471 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_473 : ¬Prog q473.toFinset 4 := localSound 3 q473 [q196,q266,q483,q517,q554,q608,q653] (by decide +kernel) (consSafe h3_196 (consSafe h3_266 (consSafe h3_483 (consSafe h3_517 (consSafe h3_554 (consSafe h3_608 (consSafe h3_653 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_474 : ¬Prog q474.toFinset 4 := localSound 3 q474 [q121,q483,q519,q521,q565,q612,q613] (by decide +kernel) (consSafe h3_121 (consSafe h3_483 (consSafe h3_519 (consSafe h3_521 (consSafe h3_565 (consSafe h3_612 (consSafe h3_613 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_475 : ¬Prog q475.toFinset 4 := localSound 3 q475 [q111,q171,q483,q520,q613,q614,q621] (by decide +kernel) (consSafe h3_111 (consSafe h3_171 (consSafe h3_483 (consSafe h3_520 (consSafe h3_613 (consSafe h3_614 (consSafe h3_621 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_476 : ¬Prog q476.toFinset 4 := localSound 3 q476 [q86,q304,q483,q521,q522,q615,q623] (by decide +kernel) (consSafe h3_86 (consSafe h3_304 (consSafe h3_483 (consSafe h3_521 (consSafe h3_522 (consSafe h3_615 (consSafe h3_623 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_477 : ¬Prog q477.toFinset 4 := localSound 3 q477 [q367,q483] (by decide +kernel) (consSafe h3_367 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_478 : ¬Prog q478.toFinset 4 := localSound 3 q478 [q118,q483,q527,q529,q558,q559,q619] (by decide +kernel) (consSafe h3_118 (consSafe h3_483 (consSafe h3_527 (consSafe h3_529 (consSafe h3_558 (consSafe h3_559 (consSafe h3_619 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_479 : ¬Prog q479.toFinset 4 := localSound 3 q479 [q110,q170,q483,q528,q559,q560,q567] (by decide +kernel) (consSafe h3_110 (consSafe h3_170 (consSafe h3_483 (consSafe h3_528 (consSafe h3_559 (consSafe h3_560 (consSafe h3_567 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_480 : ¬Prog q480.toFinset 4 := localSound 3 q480 [q99,q235,q483,q529,q530,q561,q569] (by decide +kernel) (consSafe h3_99 (consSafe h3_235 (consSafe h3_483 (consSafe h3_529 (consSafe h3_530 (consSafe h3_561 (consSafe h3_569 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_481 : ¬Prog q481.toFinset 4 := localSound 3 q481 [q411,q483] (by decide +kernel) (consSafe h3_411 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_484 : ¬Prog q484.toFinset 4 := localSound 3 q484 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_485 : ¬Prog q485.toFinset 4 := localSound 3 q485 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_486 : ¬Prog q486.toFinset 4 := localSound 3 q486 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_487 : ¬Prog q487.toFinset 4 := localSound 3 q487 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_488 : ¬Prog q488.toFinset 4 := localSound 3 q488 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_489 : ¬Prog q489.toFinset 4 := localSound 3 q489 [q483] (by decide +kernel) (consSafe h3_483 (nilSafe 3))
set_option maxHeartbeats 10000000 in
private theorem h4_490 : ¬Prog q490.toFinset 4 := localSound 3 q490 [q195,q265,q483,q504,q553,q607,q654] (by decide +kernel) (consSafe h3_195 (consSafe h3_265 (consSafe h3_483 (consSafe h3_504 (consSafe h3_553 (consSafe h3_607 (consSafe h3_654 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_491 : ¬Prog q491.toFinset 4 := localSound 3 q491 [q134,q290,q483,q505,q526,q618,q627] (by decide +kernel) (consSafe h3_134 (consSafe h3_290 (consSafe h3_483 (consSafe h3_505 (consSafe h3_526 (consSafe h3_618 (consSafe h3_627 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_492 : ¬Prog q492.toFinset 4 := localSound 3 q492 [q382,q483] (by decide +kernel) (consSafe h3_382 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_493 : ¬Prog q493.toFinset 4 := localSound 3 q493 [q154,q220,q483,q509,q533,q564,q573] (by decide +kernel) (consSafe h3_154 (consSafe h3_220 (consSafe h3_483 (consSafe h3_509 (consSafe h3_533 (consSafe h3_564 (consSafe h3_573 (nilSafe 3))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_494 : ¬Prog q494.toFinset 4 := localSound 3 q494 [q423,q483] (by decide +kernel) (consSafe h3_423 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_495 : ¬Prog q495.toFinset 4 := localSound 3 q495 [q455,q483] (by decide +kernel) (consSafe h3_455 (consSafe h3_483 (nilSafe 3)))
set_option maxHeartbeats 10000000 in
private theorem h4_496 : ¬Prog q496.toFinset 4 := localSound 3 q496 [q115,q482,q483] (by decide +kernel) (consSafe h3_115 (consSafe h3_482 (consSafe h3_483 (nilSafe 3))))
set_option maxHeartbeats 10000000 in
private theorem h4_497 : ¬Prog q497.toFinset 4 := localSound 3 q497 [q175,q463,q483] (by decide +kernel) (consSafe h3_175 (consSafe h3_463 (consSafe h3_483 (nilSafe 3))))
set_option maxHeartbeats 10000000 in
private theorem h4_498 : ¬Prog q498.toFinset 4 := localSound 3 q498 [q241,q433,q483] (by decide +kernel) (consSafe h3_241 (consSafe h3_433 (consSafe h3_483 (nilSafe 3))))
set_option maxHeartbeats 10000000 in
private theorem h4_499 : ¬Prog q499.toFinset 4 := localSound 3 q499 [q310,q394,q483] (by decide +kernel) (consSafe h3_310 (consSafe h3_394 (consSafe h3_483 (nilSafe 3))))
set_option maxHeartbeats 10000000 in
private theorem h4_507 : ¬Prog q507.toFinset 4 := localSound 3 q507 [q389,q429,q504,q658] (by decide +kernel) (consSafe h3_389 (consSafe h3_429 (consSafe h3_504 (consSafe h3_658 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_508 : ¬Prog q508.toFinset 4 := localSound 3 q508 [q392,q460,q505,q631] (by decide +kernel) (consSafe h3_392 (consSafe h3_460 (consSafe h3_505 (consSafe h3_631 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_511 : ¬Prog q511.toFinset 4 := localSound 3 q511 [q431,q462,q509,q577] (by decide +kernel) (consSafe h3_431 (consSafe h3_462 (consSafe h3_509 (consSafe h3_577 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_524 : ¬Prog q524.toFinset 4 := localSound 3 q524 [q375,q418,q517,q664] (by decide +kernel) (consSafe h3_375 (consSafe h3_418 (consSafe h3_517 (consSafe h3_664 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_525 : ¬Prog q525.toFinset 4 := localSound 3 q525 [q393,q519,q521,q631] (by decide +kernel) (consSafe h3_393 (consSafe h3_519 (consSafe h3_521 (consSafe h3_631 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_532 : ¬Prog q532.toFinset 4 := localSound 3 q532 [q432,q527,q529,q577] (by decide +kernel) (consSafe h3_432 (consSafe h3_527 (consSafe h3_529 (consSafe h3_577 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_551 : ¬Prog q551.toFinset 4 := localSound 3 q551 [q376,q539,q542,q664] (by decide +kernel) (consSafe h3_376 (consSafe h3_539 (consSafe h3_542 (consSafe h3_664 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_552 : ¬Prog q552.toFinset 4 := localSound 3 q552 [q390,q545,q547,q658] (by decide +kernel) (consSafe h3_390 (consSafe h3_545 (consSafe h3_547 (consSafe h3_658 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_555 : ¬Prog q555.toFinset 4 := localSound 3 q555 [q110,q142,q160,q170,q556,q559,q560,q567,q666] (by decide +kernel) (consSafe h3_110 (consSafe h3_142 (consSafe h3_160 (consSafe h3_170 (consSafe h3_556 (consSafe h3_559 (consSafe h3_560 (consSafe h3_567 (consSafe h3_666 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_563 : ¬Prog q563.toFinset 4 := localSound 3 q563 [q557,q558,q559,q577] (by decide +kernel) (consSafe h3_557 (consSafe h3_558 (consSafe h3_559 (consSafe h3_577 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_587 : ¬Prog q587.toFinset 4 := localSound 3 q587 [q155,q209,q222,q255,q588,q595,q596,q597,q637] (by decide +kernel) (consSafe h3_155 (consSafe h3_209 (consSafe h3_222 (consSafe h3_255 (consSafe h3_588 (consSafe h3_595 (consSafe h3_596 (consSafe h3_597 (consSafe h3_637 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_590 : ¬Prog q590.toFinset 4 := localSound 3 q590 [q100,q202,q228,q237,q591,q600,q601,q602,q643] (by decide +kernel) (consSafe h3_100 (consSafe h3_202 (consSafe h3_228 (consSafe h3_237 (consSafe h3_591 (consSafe h3_600 (consSafe h3_601 (consSafe h3_602 (consSafe h3_643 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_605 : ¬Prog q605.toFinset 4 := localSound 3 q605 [q589,q593,q595,q664] (by decide +kernel) (consSafe h3_589 (consSafe h3_593 (consSafe h3_595 (consSafe h3_664 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_606 : ¬Prog q606.toFinset 4 := localSound 3 q606 [q592,q599,q600,q658] (by decide +kernel) (consSafe h3_592 (consSafe h3_599 (consSafe h3_600 (consSafe h3_658 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h4_609 : ¬Prog q609.toFinset 4 := localSound 3 q609 [q111,q141,q161,q171,q610,q613,q614,q621,q666] (by decide +kernel) (consSafe h3_111 (consSafe h3_141 (consSafe h3_161 (consSafe h3_171 (consSafe h3_610 (consSafe h3_613 (consSafe h3_614 (consSafe h3_621 (consSafe h3_666 (nilSafe 3))))))))))
set_option maxHeartbeats 10000000 in
private theorem h4_617 : ¬Prog q617.toFinset 4 := localSound 3 q617 [q611,q612,q613,q631] (by decide +kernel) (consSafe h3_611 (consSafe h3_612 (consSafe h3_613 (consSafe h3_631 (nilSafe 3)))))
set_option maxHeartbeats 10000000 in
private theorem h5_0 : ¬Prog q0.toFinset 5 := localSound 4 q0 [q39,q67,q69,q73,q75,q77,q78,q79,q80,q81,q82,q83,q84,q85,q95,q106,q130,q150,q166,q191,q217,q232,q262,q287,q301,q347,q362,q377,q407,q419,q426,q434,q451,q452,q457,q464,q477,q481,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_67 (consSafe h4_69 (consSafe h4_73 (consSafe h4_75 (consSafe h4_77 (consSafe h4_78 (consSafe h4_79 (consSafe h4_80 (consSafe h4_81 (consSafe h4_82 (consSafe h4_83 (consSafe h4_84 (consSafe h4_85 (consSafe h4_95 (consSafe h4_106 (consSafe h4_130 (consSafe h4_150 (consSafe h4_166 (consSafe h4_191 (consSafe h4_217 (consSafe h4_232 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_362 (consSafe h4_377 (consSafe h4_407 (consSafe h4_419 (consSafe h4_426 (consSafe h4_434 (consSafe h4_451 (consSafe h4_452 (consSafe h4_457 (consSafe h4_464 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_1 : ¬Prog q1.toFinset 5 := localSound 4 q1 [q39,q68,q71,q73,q82,q88,q90,q91,q92,q93,q94,q95,q96,q97,q98,q106,q130,q150,q166,q191,q217,q232,q262,q287,q301,q347,q362,q377,q386,q395,q407,q419,q451,q452,q456,q465,q477,q481,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_68 (consSafe h4_71 (consSafe h4_73 (consSafe h4_82 (consSafe h4_88 (consSafe h4_90 (consSafe h4_91 (consSafe h4_92 (consSafe h4_93 (consSafe h4_94 (consSafe h4_95 (consSafe h4_96 (consSafe h4_97 (consSafe h4_98 (consSafe h4_106 (consSafe h4_130 (consSafe h4_150 (consSafe h4_166 (consSafe h4_191 (consSafe h4_217 (consSafe h4_232 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_362 (consSafe h4_377 (consSafe h4_386 (consSafe h4_395 (consSafe h4_407 (consSafe h4_419 (consSafe h4_451 (consSafe h4_452 (consSafe h4_456 (consSafe h4_465 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_2 : ¬Prog q2.toFinset 5 := localSound 4 q2 [q39,q70,q72,q75,q82,q88,q95,q101,q102,q103,q104,q105,q106,q107,q108,q109,q130,q150,q166,q191,q217,q232,q262,q287,q301,q347,q362,q377,q385,q396,q407,q419,q425,q435,q451,q452,q477,q481,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_70 (consSafe h4_72 (consSafe h4_75 (consSafe h4_82 (consSafe h4_88 (consSafe h4_95 (consSafe h4_101 (consSafe h4_102 (consSafe h4_103 (consSafe h4_104 (consSafe h4_105 (consSafe h4_106 (consSafe h4_107 (consSafe h4_108 (consSafe h4_109 (consSafe h4_130 (consSafe h4_150 (consSafe h4_166 (consSafe h4_191 (consSafe h4_217 (consSafe h4_232 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_362 (consSafe h4_377 (consSafe h4_385 (consSafe h4_396 (consSafe h4_407 (consSafe h4_419 (consSafe h4_425 (consSafe h4_435 (consSafe h4_451 (consSafe h4_452 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_3 : ¬Prog q3.toFinset 5 := localSound 4 q3 [q39,q67,q77,q82,q95,q106,q116,q122,q124,q126,q127,q128,q129,q130,q131,q132,q133,q150,q166,q191,q217,q232,q262,q287,q301,q347,q362,q377,q407,q415,q419,q437,q451,q452,q469,q477,q481,q484,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_67 (consSafe h4_77 (consSafe h4_82 (consSafe h4_95 (consSafe h4_106 (consSafe h4_116 (consSafe h4_122 (consSafe h4_124 (consSafe h4_126 (consSafe h4_127 (consSafe h4_128 (consSafe h4_129 (consSafe h4_130 (consSafe h4_131 (consSafe h4_132 (consSafe h4_133 (consSafe h4_150 (consSafe h4_166 (consSafe h4_191 (consSafe h4_217 (consSafe h4_232 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_362 (consSafe h4_377 (consSafe h4_407 (consSafe h4_415 (consSafe h4_419 (consSafe h4_437 (consSafe h4_451 (consSafe h4_452 (consSafe h4_469 (consSafe h4_477 (consSafe h4_481 (consSafe h4_484 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_5 : ¬Prog q5.toFinset 5 := localSound 4 q5 [q39,q68,q82,q90,q95,q106,q119,q122,q130,q144,q146,q147,q148,q149,q150,q151,q152,q153,q166,q191,q217,q232,q262,q287,q301,q347,q362,q372,q377,q398,q407,q419,q451,q452,q466,q477,q481,q485,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_68 (consSafe h4_82 (consSafe h4_90 (consSafe h4_95 (consSafe h4_106 (consSafe h4_119 (consSafe h4_122 (consSafe h4_130 (consSafe h4_144 (consSafe h4_146 (consSafe h4_147 (consSafe h4_148 (consSafe h4_149 (consSafe h4_150 (consSafe h4_151 (consSafe h4_152 (consSafe h4_153 (consSafe h4_166 (consSafe h4_191 (consSafe h4_217 (consSafe h4_232 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_362 (consSafe h4_372 (consSafe h4_377 (consSafe h4_398 (consSafe h4_407 (consSafe h4_419 (consSafe h4_451 (consSafe h4_452 (consSafe h4_466 (consSafe h4_477 (consSafe h4_481 (consSafe h4_485 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_7 : ¬Prog q7.toFinset 5 := localSound 4 q7 [q39,q82,q95,q101,q102,q106,q117,q120,q124,q130,q144,q150,q163,q164,q165,q166,q167,q168,q169,q191,q217,q232,q262,q287,q301,q347,q362,q370,q377,q399,q407,q413,q419,q438,q451,q452,q477,q481,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_82 (consSafe h4_95 (consSafe h4_101 (consSafe h4_102 (consSafe h4_106 (consSafe h4_117 (consSafe h4_120 (consSafe h4_124 (consSafe h4_130 (consSafe h4_144 (consSafe h4_150 (consSafe h4_163 (consSafe h4_164 (consSafe h4_165 (consSafe h4_166 (consSafe h4_167 (consSafe h4_168 (consSafe h4_169 (consSafe h4_191 (consSafe h4_217 (consSafe h4_232 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_362 (consSafe h4_370 (consSafe h4_377 (consSafe h4_399 (consSafe h4_407 (consSafe h4_413 (consSafe h4_419 (consSafe h4_438 (consSafe h4_451 (consSafe h4_452 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_8 : ¬Prog q8.toFinset 5 := localSound 4 q8 [q39,q69,q78,q82,q95,q106,q116,q126,q130,q150,q166,q184,q186,q188,q189,q190,q191,q192,q193,q194,q217,q232,q262,q287,q301,q347,q362,q377,q407,q419,q439,q441,q451,q452,q467,q477,q481,q486,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_69 (consSafe h4_78 (consSafe h4_82 (consSafe h4_95 (consSafe h4_106 (consSafe h4_116 (consSafe h4_126 (consSafe h4_130 (consSafe h4_150 (consSafe h4_166 (consSafe h4_184 (consSafe h4_186 (consSafe h4_188 (consSafe h4_189 (consSafe h4_190 (consSafe h4_191 (consSafe h4_192 (consSafe h4_193 (consSafe h4_194 (consSafe h4_217 (consSafe h4_232 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_362 (consSafe h4_377 (consSafe h4_407 (consSafe h4_419 (consSafe h4_439 (consSafe h4_441 (consSafe h4_451 (consSafe h4_452 (consSafe h4_467 (consSafe h4_477 (consSafe h4_481 (consSafe h4_486 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_11 : ¬Prog q11.toFinset 5 := localSound 4 q11 [q39,q70,q82,q95,q103,q106,q130,q146,q147,q150,q166,q180,q184,q191,q213,q215,q216,q217,q218,q219,q221,q232,q262,q287,q301,q347,q357,q362,q377,q403,q407,q419,q436,q451,q452,q477,q481,q487,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_70 (consSafe h4_82 (consSafe h4_95 (consSafe h4_103 (consSafe h4_106 (consSafe h4_130 (consSafe h4_146 (consSafe h4_147 (consSafe h4_150 (consSafe h4_166 (consSafe h4_180 (consSafe h4_184 (consSafe h4_191 (consSafe h4_213 (consSafe h4_215 (consSafe h4_216 (consSafe h4_217 (consSafe h4_218 (consSafe h4_219 (consSafe h4_221 (consSafe h4_232 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_357 (consSafe h4_362 (consSafe h4_377 (consSafe h4_403 (consSafe h4_407 (consSafe h4_419 (consSafe h4_436 (consSafe h4_451 (consSafe h4_452 (consSafe h4_477 (consSafe h4_481 (consSafe h4_487 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_13 : ¬Prog q13.toFinset 5 := localSound 4 q13 [q39,q82,q91,q92,q95,q106,q117,q130,q150,q163,q166,q181,q186,q191,q213,q217,q230,q231,q232,q233,q234,q236,q262,q287,q301,q347,q355,q362,q377,q404,q407,q414,q419,q451,q452,q468,q477,q481,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_82 (consSafe h4_91 (consSafe h4_92 (consSafe h4_95 (consSafe h4_106 (consSafe h4_117 (consSafe h4_130 (consSafe h4_150 (consSafe h4_163 (consSafe h4_166 (consSafe h4_181 (consSafe h4_186 (consSafe h4_191 (consSafe h4_213 (consSafe h4_217 (consSafe h4_230 (consSafe h4_231 (consSafe h4_232 (consSafe h4_233 (consSafe h4_234 (consSafe h4_236 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_355 (consSafe h4_362 (consSafe h4_377 (consSafe h4_404 (consSafe h4_407 (consSafe h4_414 (consSafe h4_419 (consSafe h4_451 (consSafe h4_452 (consSafe h4_468 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_15 : ¬Prog q15.toFinset 5 := localSound 4 q15 [q39,q71,q82,q93,q95,q106,q119,q130,q148,q150,q166,q188,q189,q191,q217,q232,q257,q259,q261,q262,q263,q264,q267,q287,q301,q347,q362,q377,q400,q402,q407,q419,q451,q452,q470,q477,q481,q488,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_71 (consSafe h4_82 (consSafe h4_93 (consSafe h4_95 (consSafe h4_106 (consSafe h4_119 (consSafe h4_130 (consSafe h4_148 (consSafe h4_150 (consSafe h4_166 (consSafe h4_188 (consSafe h4_189 (consSafe h4_191 (consSafe h4_217 (consSafe h4_232 (consSafe h4_257 (consSafe h4_259 (consSafe h4_261 (consSafe h4_262 (consSafe h4_263 (consSafe h4_264 (consSafe h4_267 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_362 (consSafe h4_377 (consSafe h4_400 (consSafe h4_402 (consSafe h4_407 (consSafe h4_419 (consSafe h4_451 (consSafe h4_452 (consSafe h4_470 (consSafe h4_477 (consSafe h4_481 (consSafe h4_488 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_18 : ¬Prog q18.toFinset 5 := localSound 4 q18 [q39,q72,q82,q95,q104,q106,q127,q128,q130,q150,q166,q180,q191,q215,q217,q232,q257,q262,q284,q286,q287,q288,q289,q292,q301,q347,q359,q362,q377,q397,q407,q419,q442,q451,q452,q477,q481,q489,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_72 (consSafe h4_82 (consSafe h4_95 (consSafe h4_104 (consSafe h4_106 (consSafe h4_127 (consSafe h4_128 (consSafe h4_130 (consSafe h4_150 (consSafe h4_166 (consSafe h4_180 (consSafe h4_191 (consSafe h4_215 (consSafe h4_217 (consSafe h4_232 (consSafe h4_257 (consSafe h4_262 (consSafe h4_284 (consSafe h4_286 (consSafe h4_287 (consSafe h4_288 (consSafe h4_289 (consSafe h4_292 (consSafe h4_301 (consSafe h4_347 (consSafe h4_359 (consSafe h4_362 (consSafe h4_377 (consSafe h4_397 (consSafe h4_407 (consSafe h4_419 (consSafe h4_442 (consSafe h4_451 (consSafe h4_452 (consSafe h4_477 (consSafe h4_481 (consSafe h4_489 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_20 : ¬Prog q20.toFinset 5 := localSound 4 q20 [q39,q79,q80,q82,q95,q106,q120,q130,q150,q164,q166,q181,q191,q217,q230,q232,q259,q262,q284,q287,q300,q301,q302,q303,q306,q347,q356,q362,q371,q377,q407,q419,q443,q451,q452,q471,q477,q481,q492,q494,q495] (by decide +kernel) (consSafe h4_39 (consSafe h4_79 (consSafe h4_80 (consSafe h4_82 (consSafe h4_95 (consSafe h4_106 (consSafe h4_120 (consSafe h4_130 (consSafe h4_150 (consSafe h4_164 (consSafe h4_166 (consSafe h4_181 (consSafe h4_191 (consSafe h4_217 (consSafe h4_230 (consSafe h4_232 (consSafe h4_259 (consSafe h4_262 (consSafe h4_284 (consSafe h4_287 (consSafe h4_300 (consSafe h4_301 (consSafe h4_302 (consSafe h4_303 (consSafe h4_306 (consSafe h4_347 (consSafe h4_356 (consSafe h4_362 (consSafe h4_371 (consSafe h4_377 (consSafe h4_407 (consSafe h4_419 (consSafe h4_443 (consSafe h4_451 (consSafe h4_452 (consSafe h4_471 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_24 : ¬Prog q24.toFinset 5 := localSound 4 q24 [q22,q23,q25,q39,q43,q46,q73,q82,q95,q106,q122,q130,q150,q166,q190,q191,q217,q232,q261,q262,q287,q301,q331,q333,q338,q341,q345,q346,q347,q348,q349,q350,q351,q362,q377,q407,q419,q451,q452,q473,q477,q481,q490,q492,q494,q495] (by decide +kernel) (consSafe h4_22 (consSafe h4_23 (consSafe h4_25 (consSafe h4_39 (consSafe h4_43 (consSafe h4_46 (consSafe h4_73 (consSafe h4_82 (consSafe h4_95 (consSafe h4_106 (consSafe h4_122 (consSafe h4_130 (consSafe h4_150 (consSafe h4_166 (consSafe h4_190 (consSafe h4_191 (consSafe h4_217 (consSafe h4_232 (consSafe h4_261 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_331 (consSafe h4_333 (consSafe h4_338 (consSafe h4_341 (consSafe h4_345 (consSafe h4_346 (consSafe h4_347 (consSafe h4_348 (consSafe h4_349 (consSafe h4_350 (consSafe h4_351 (consSafe h4_362 (consSafe h4_377 (consSafe h4_407 (consSafe h4_419 (consSafe h4_451 (consSafe h4_452 (consSafe h4_473 (consSafe h4_477 (consSafe h4_481 (consSafe h4_490 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_26 : ¬Prog q26.toFinset 5 := localSound 4 q26 [q17,q21,q27,q39,q44,q49,q75,q82,q95,q106,q129,q130,q150,q166,q184,q191,q217,q232,q262,q277,q279,q286,q287,q301,q320,q323,q345,q347,q361,q362,q363,q364,q365,q366,q377,q407,q419,q447,q451,q452,q477,q481,q491,q492,q494,q495] (by decide +kernel) (consSafe h4_17 (consSafe h4_21 (consSafe h4_27 (consSafe h4_39 (consSafe h4_44 (consSafe h4_49 (consSafe h4_75 (consSafe h4_82 (consSafe h4_95 (consSafe h4_106 (consSafe h4_129 (consSafe h4_130 (consSafe h4_150 (consSafe h4_166 (consSafe h4_184 (consSafe h4_191 (consSafe h4_217 (consSafe h4_232 (consSafe h4_262 (consSafe h4_277 (consSafe h4_279 (consSafe h4_286 (consSafe h4_287 (consSafe h4_301 (consSafe h4_320 (consSafe h4_323 (consSafe h4_345 (consSafe h4_347 (consSafe h4_361 (consSafe h4_362 (consSafe h4_363 (consSafe h4_364 (consSafe h4_365 (consSafe h4_366 (consSafe h4_377 (consSafe h4_407 (consSafe h4_419 (consSafe h4_447 (consSafe h4_451 (consSafe h4_452 (consSafe h4_477 (consSafe h4_481 (consSafe h4_491 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_28 : ¬Prog q28.toFinset 5 := localSound 4 q28 [q16,q19,q29,q39,q47,q50,q81,q82,q95,q106,q124,q130,q150,q166,q186,q191,q217,q232,q262,q270,q272,q287,q294,q296,q300,q301,q346,q347,q361,q362,q377,q378,q379,q380,q381,q407,q419,q450,q451,q452,q476,q477,q481,q492,q494,q495] (by decide +kernel) (consSafe h4_16 (consSafe h4_19 (consSafe h4_29 (consSafe h4_39 (consSafe h4_47 (consSafe h4_50 (consSafe h4_81 (consSafe h4_82 (consSafe h4_95 (consSafe h4_106 (consSafe h4_124 (consSafe h4_130 (consSafe h4_150 (consSafe h4_166 (consSafe h4_186 (consSafe h4_191 (consSafe h4_217 (consSafe h4_232 (consSafe h4_262 (consSafe h4_270 (consSafe h4_272 (consSafe h4_287 (consSafe h4_294 (consSafe h4_296 (consSafe h4_300 (consSafe h4_301 (consSafe h4_346 (consSafe h4_347 (consSafe h4_361 (consSafe h4_362 (consSafe h4_377 (consSafe h4_378 (consSafe h4_379 (consSafe h4_380 (consSafe h4_381 (consSafe h4_407 (consSafe h4_419 (consSafe h4_450 (consSafe h4_451 (consSafe h4_452 (consSafe h4_476 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_30 : ¬Prog q30.toFinset 5 := localSound 4 q30 [q10,q14,q31,q39,q45,q55,q82,q88,q95,q106,q130,q149,q150,q166,q191,q206,q207,q216,q217,q232,q251,q254,q257,q262,q287,q301,q345,q347,q362,q377,q406,q407,q408,q409,q410,q419,q446,q451,q452,q477,q481,q492,q493,q494,q495,q587] (by decide +kernel) (consSafe h4_10 (consSafe h4_14 (consSafe h4_31 (consSafe h4_39 (consSafe h4_45 (consSafe h4_55 (consSafe h4_82 (consSafe h4_88 (consSafe h4_95 (consSafe h4_106 (consSafe h4_130 (consSafe h4_149 (consSafe h4_150 (consSafe h4_166 (consSafe h4_191 (consSafe h4_206 (consSafe h4_207 (consSafe h4_216 (consSafe h4_217 (consSafe h4_232 (consSafe h4_251 (consSafe h4_254 (consSafe h4_257 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_345 (consSafe h4_347 (consSafe h4_362 (consSafe h4_377 (consSafe h4_406 (consSafe h4_407 (consSafe h4_408 (consSafe h4_409 (consSafe h4_410 (consSafe h4_419 (consSafe h4_446 (consSafe h4_451 (consSafe h4_452 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_493 (consSafe h4_494 (consSafe h4_495 (consSafe h4_587 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_32 : ¬Prog q32.toFinset 5 := localSound 4 q32 [q9,q12,q33,q39,q48,q56,q82,q94,q95,q106,q130,q144,q150,q166,q191,q199,q200,q217,q224,q226,q231,q232,q259,q262,q287,q301,q346,q347,q362,q377,q406,q407,q419,q420,q421,q422,q449,q451,q452,q477,q480,q481,q492,q494,q495,q590] (by decide +kernel) (consSafe h4_9 (consSafe h4_12 (consSafe h4_33 (consSafe h4_39 (consSafe h4_48 (consSafe h4_56 (consSafe h4_82 (consSafe h4_94 (consSafe h4_95 (consSafe h4_106 (consSafe h4_130 (consSafe h4_144 (consSafe h4_150 (consSafe h4_166 (consSafe h4_191 (consSafe h4_199 (consSafe h4_200 (consSafe h4_217 (consSafe h4_224 (consSafe h4_226 (consSafe h4_231 (consSafe h4_232 (consSafe h4_259 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_346 (consSafe h4_347 (consSafe h4_362 (consSafe h4_377 (consSafe h4_406 (consSafe h4_407 (consSafe h4_419 (consSafe h4_420 (consSafe h4_421 (consSafe h4_422 (consSafe h4_449 (consSafe h4_451 (consSafe h4_452 (consSafe h4_477 (consSafe h4_480 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (consSafe h4_590 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_34 : ¬Prog q34.toFinset 5 := localSound 4 q34 [q25,q39,q82,q84,q95,q97,q106,q112,q130,q132,q150,q152,q166,q172,q180,q181,q191,q192,q217,q232,q262,q267,q287,q301,q347,q350,q351,q362,q377,q407,q419,q445,q448,q451,q452,q477,q481,q492,q494,q495,q496,q497,q551,q552,q605,q606] (by decide +kernel) (consSafe h4_25 (consSafe h4_39 (consSafe h4_82 (consSafe h4_84 (consSafe h4_95 (consSafe h4_97 (consSafe h4_106 (consSafe h4_112 (consSafe h4_130 (consSafe h4_132 (consSafe h4_150 (consSafe h4_152 (consSafe h4_166 (consSafe h4_172 (consSafe h4_180 (consSafe h4_181 (consSafe h4_191 (consSafe h4_192 (consSafe h4_217 (consSafe h4_232 (consSafe h4_262 (consSafe h4_267 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_350 (consSafe h4_351 (consSafe h4_362 (consSafe h4_377 (consSafe h4_407 (consSafe h4_419 (consSafe h4_445 (consSafe h4_448 (consSafe h4_451 (consSafe h4_452 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (consSafe h4_496 (consSafe h4_497 (consSafe h4_551 (consSafe h4_552 (consSafe h4_605 (consSafe h4_606 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_35 : ¬Prog q35.toFinset 5 := localSound 4 q35 [q4,q6,q36,q39,q51,q57,q82,q95,q105,q106,q130,q138,q139,q150,q157,q158,q165,q166,q191,q213,q217,q232,q262,q284,q287,q301,q347,q361,q362,q377,q406,q407,q419,q451,q452,q453,q454,q475,q477,q479,q481,q492,q494,q495,q555,q609] (by decide +kernel) (consSafe h4_4 (consSafe h4_6 (consSafe h4_36 (consSafe h4_39 (consSafe h4_51 (consSafe h4_57 (consSafe h4_82 (consSafe h4_95 (consSafe h4_105 (consSafe h4_106 (consSafe h4_130 (consSafe h4_138 (consSafe h4_139 (consSafe h4_150 (consSafe h4_157 (consSafe h4_158 (consSafe h4_165 (consSafe h4_166 (consSafe h4_191 (consSafe h4_213 (consSafe h4_217 (consSafe h4_232 (consSafe h4_262 (consSafe h4_284 (consSafe h4_287 (consSafe h4_301 (consSafe h4_347 (consSafe h4_361 (consSafe h4_362 (consSafe h4_377 (consSafe h4_406 (consSafe h4_407 (consSafe h4_419 (consSafe h4_451 (consSafe h4_452 (consSafe h4_453 (consSafe h4_454 (consSafe h4_475 (consSafe h4_477 (consSafe h4_479 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (consSafe h4_555 (consSafe h4_609 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_37 : ¬Prog q37.toFinset 5 := localSound 4 q37 [q27,q39,q82,q85,q95,q106,q108,q113,q119,q120,q130,q131,q150,q166,q191,q193,q217,q218,q232,q238,q262,q287,q292,q301,q347,q362,q364,q366,q377,q407,q417,q419,q451,q452,q474,q477,q481,q492,q494,q495,q496,q498,q524,q525,q605,q617] (by decide +kernel) (consSafe h4_27 (consSafe h4_39 (consSafe h4_82 (consSafe h4_85 (consSafe h4_95 (consSafe h4_106 (consSafe h4_108 (consSafe h4_113 (consSafe h4_119 (consSafe h4_120 (consSafe h4_130 (consSafe h4_131 (consSafe h4_150 (consSafe h4_166 (consSafe h4_191 (consSafe h4_193 (consSafe h4_217 (consSafe h4_218 (consSafe h4_232 (consSafe h4_238 (consSafe h4_262 (consSafe h4_287 (consSafe h4_292 (consSafe h4_301 (consSafe h4_347 (consSafe h4_362 (consSafe h4_364 (consSafe h4_366 (consSafe h4_377 (consSafe h4_407 (consSafe h4_417 (consSafe h4_419 (consSafe h4_451 (consSafe h4_452 (consSafe h4_474 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (consSafe h4_496 (consSafe h4_498 (consSafe h4_524 (consSafe h4_525 (consSafe h4_605 (consSafe h4_617 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_38 : ¬Prog q38.toFinset 5 := localSound 4 q38 [q31,q39,q82,q95,q98,q106,q109,q114,q116,q117,q130,q150,q151,q166,q191,q217,q221,q232,q262,q263,q287,q288,q301,q307,q347,q362,q374,q377,q407,q409,q410,q419,q451,q452,q477,q478,q481,q492,q494,q495,q496,q499,q524,q532,q551,q563] (by decide +kernel) (consSafe h4_31 (consSafe h4_39 (consSafe h4_82 (consSafe h4_95 (consSafe h4_98 (consSafe h4_106 (consSafe h4_109 (consSafe h4_114 (consSafe h4_116 (consSafe h4_117 (consSafe h4_130 (consSafe h4_150 (consSafe h4_151 (consSafe h4_166 (consSafe h4_191 (consSafe h4_217 (consSafe h4_221 (consSafe h4_232 (consSafe h4_262 (consSafe h4_263 (consSafe h4_287 (consSafe h4_288 (consSafe h4_301 (consSafe h4_307 (consSafe h4_347 (consSafe h4_362 (consSafe h4_374 (consSafe h4_377 (consSafe h4_407 (consSafe h4_409 (consSafe h4_410 (consSafe h4_419 (consSafe h4_451 (consSafe h4_452 (consSafe h4_477 (consSafe h4_478 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (consSafe h4_496 (consSafe h4_499 (consSafe h4_524 (consSafe h4_532 (consSafe h4_551 (consSafe h4_563 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_40 : ¬Prog q40.toFinset 5 := localSound 4 q40 [q29,q39,q71,q72,q82,q83,q95,q106,q130,q133,q150,q166,q167,q173,q191,q194,q217,q232,q233,q239,q262,q287,q301,q306,q347,q362,q377,q378,q381,q407,q419,q428,q451,q452,q459,q477,q481,q492,q494,q495,q497,q498,q507,q508,q606,q617] (by decide +kernel) (consSafe h4_29 (consSafe h4_39 (consSafe h4_71 (consSafe h4_72 (consSafe h4_82 (consSafe h4_83 (consSafe h4_95 (consSafe h4_106 (consSafe h4_130 (consSafe h4_133 (consSafe h4_150 (consSafe h4_166 (consSafe h4_167 (consSafe h4_173 (consSafe h4_191 (consSafe h4_194 (consSafe h4_217 (consSafe h4_232 (consSafe h4_233 (consSafe h4_239 (consSafe h4_262 (consSafe h4_287 (consSafe h4_301 (consSafe h4_306 (consSafe h4_347 (consSafe h4_362 (consSafe h4_377 (consSafe h4_378 (consSafe h4_381 (consSafe h4_407 (consSafe h4_419 (consSafe h4_428 (consSafe h4_451 (consSafe h4_452 (consSafe h4_459 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (consSafe h4_497 (consSafe h4_498 (consSafe h4_507 (consSafe h4_508 (consSafe h4_606 (consSafe h4_617 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_41 : ¬Prog q41.toFinset 5 := localSound 4 q41 [q33,q39,q69,q70,q82,q95,q96,q106,q130,q150,q153,q166,q168,q174,q191,q217,q232,q236,q262,q264,q287,q301,q302,q308,q347,q362,q377,q388,q407,q419,q420,q422,q451,q452,q461,q477,q481,q492,q494,q495,q497,q499,q507,q511,q552,q563] (by decide +kernel) (consSafe h4_33 (consSafe h4_39 (consSafe h4_69 (consSafe h4_70 (consSafe h4_82 (consSafe h4_95 (consSafe h4_96 (consSafe h4_106 (consSafe h4_130 (consSafe h4_150 (consSafe h4_153 (consSafe h4_166 (consSafe h4_168 (consSafe h4_174 (consSafe h4_191 (consSafe h4_217 (consSafe h4_232 (consSafe h4_236 (consSafe h4_262 (consSafe h4_264 (consSafe h4_287 (consSafe h4_301 (consSafe h4_302 (consSafe h4_308 (consSafe h4_347 (consSafe h4_362 (consSafe h4_377 (consSafe h4_388 (consSafe h4_407 (consSafe h4_419 (consSafe h4_420 (consSafe h4_422 (consSafe h4_451 (consSafe h4_452 (consSafe h4_461 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (consSafe h4_497 (consSafe h4_499 (consSafe h4_507 (consSafe h4_511 (consSafe h4_552 (consSafe h4_563 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h5_42 : ¬Prog q42.toFinset 5 := localSound 4 q42 [q36,q39,q67,q68,q82,q95,q106,q107,q130,q150,q166,q169,q191,q217,q219,q232,q234,q240,q262,q287,q289,q301,q303,q309,q347,q362,q377,q391,q407,q419,q430,q451,q452,q453,q454,q477,q481,q492,q494,q495,q498,q499,q508,q511,q525,q532] (by decide +kernel) (consSafe h4_36 (consSafe h4_39 (consSafe h4_67 (consSafe h4_68 (consSafe h4_82 (consSafe h4_95 (consSafe h4_106 (consSafe h4_107 (consSafe h4_130 (consSafe h4_150 (consSafe h4_166 (consSafe h4_169 (consSafe h4_191 (consSafe h4_217 (consSafe h4_219 (consSafe h4_232 (consSafe h4_234 (consSafe h4_240 (consSafe h4_262 (consSafe h4_287 (consSafe h4_289 (consSafe h4_301 (consSafe h4_303 (consSafe h4_309 (consSafe h4_347 (consSafe h4_362 (consSafe h4_377 (consSafe h4_391 (consSafe h4_407 (consSafe h4_419 (consSafe h4_430 (consSafe h4_451 (consSafe h4_452 (consSafe h4_453 (consSafe h4_454 (consSafe h4_477 (consSafe h4_481 (consSafe h4_492 (consSafe h4_494 (consSafe h4_495 (consSafe h4_498 (consSafe h4_499 (consSafe h4_508 (consSafe h4_511 (consSafe h4_525 (consSafe h4_532 (nilSafe 4)))))))))))))))))))))))))))))))))))))))))))))))
set_option maxHeartbeats 10000000 in
private theorem h6_39 : ¬Prog q39.toFinset 6 := localSound 5 q39 [q0,q1,q2,q3,q5,q7,q8,q11,q13,q15,q18,q20,q24,q26,q28,q30,q32,q34,q35,q37,q38,q40,q41,q42] (by decide +kernel) (consSafe h5_0 (consSafe h5_1 (consSafe h5_2 (consSafe h5_3 (consSafe h5_5 (consSafe h5_7 (consSafe h5_8 (consSafe h5_11 (consSafe h5_13 (consSafe h5_15 (consSafe h5_18 (consSafe h5_20 (consSafe h5_24 (consSafe h5_26 (consSafe h5_28 (consSafe h5_30 (consSafe h5_32 (consSafe h5_34 (consSafe h5_35 (consSafe h5_37 (consSafe h5_38 (consSafe h5_40 (consSafe h5_41 (consSafe h5_42 (nilSafe 5)))))))))))))))))))))))))
theorem core : ¬Prog initial.toFinset 6 := h6_39
end Cert11065

theorem PEqualNP.Outside.L_meta_11064 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  apply positiveFromSigned
  intro k L le build av
  obtain ⟨d,M,budget,b,a⟩ := ReduceFour11065.reduce build av
  exact Cert11065.core (SparseBridge11065.bridge b a (by omega))
