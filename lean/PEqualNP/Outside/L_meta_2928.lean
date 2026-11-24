import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Sublists
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Forall2
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2928

-- The signed circuit certificate and finite decisions are adapted from project pull request 5922 by Great-Leader-of-ISLAND.
-- The variable OR seed, binary gate count, and bit-vector specialization are derived here.


namespace CoThetaFreeCore

def phase (sign bit : Bool) : Bool := if sign then !bit else bit

def base (join a b : Bool) : Bool := if join then a || b else a && b

inductive Kind where
  | conj | disj | leftOnly | rightOnly

def applyKind : Kind → Bool → Bool → Bool
  | .conj, a, b => a && b
  | .disj, a, b => a || b
  | .leftOnly, a, b => a && !b
  | .rightOnly, a, b => !a && b

def normalizedKind : Bool → Bool → Bool → Kind
  | false, false, false => .conj
  | false, false, true  => .leftOnly
  | false, true, false  => .rightOnly
  | false, true, true   => .disj
  | true, false, false  => .disj
  | true, false, true   => .rightOnly
  | true, true, false   => .leftOnly
  | true, true, true    => .conj

theorem normalization_table : ∀ join a0 b0 a b : Bool,
    phase (base join a0 b0) (base join a b) =
    applyKind (normalizedKind join a0 b0) (phase a0 a) (phase b0 b) := by decide

theorem inversion_table : ∀ a0 a : Bool, phase (!a0) (!a) = phase a0 a := by decide

variable {ρ : Type}

def norm (empty : ρ) (a : ρ → Bool) : ρ → Bool := fun i => phase (a empty) (a i)

theorem normalize_binary (empty : ρ) (join : Bool) (a b : ρ → Bool) :
    norm empty (fun i => base join (a i) (b i)) =
    fun i => applyKind (normalizedKind join (a empty) (b empty)) (norm empty a i) (norm empty b i) := by
  funext i
  exact normalization_table join (a empty) (b empty) (a i) (b i)

theorem normalize_unary (empty : ρ) (a : ρ → Bool) :
    norm empty (fun i => !(a i)) = norm empty a := by
  funext i
  exact inversion_table (a empty) (a i)

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

 

inductive Ordinary (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Ordinary raw 0 raw
  | inv {n ws a} (pre : Ordinary raw n ws) (ha : a ∈ ws) :
      Ordinary raw n ((fun i => !(a i)) :: ws)
  | binary {n ws a b} (pre : Ordinary raw n ws) (join : Bool) (ha : a ∈ ws) (hb : b ∈ ws) :
      Ordinary raw (n+1) ((fun i => base join (a i) (b i)) :: ws)

inductive Free (raw : List (ρ → Bool)) : Nat → List (ρ → Bool) → Prop
  | start : Free raw 0 raw
  | binary {n ws a b} (pre : Free raw n ws) (kind : Kind) (ha : a ∈ ws) (hb : b ∈ ws) :
      Free raw (n+1) ((fun i => applyKind kind (a i) (b i)) :: ws)

theorem simulate_all_wires (empty : ρ) {raw ws : List (ρ → Bool)} {n : Nat}
    (run : Ordinary raw n ws) :
    ∃ ys, Free (raw.map (norm empty)) n ys ∧
          ∀ a ∈ ws, norm empty a ∈ ys := by
  induction run with
  | start =>
    exact ⟨_, Free.start, fun a ha => List.mem_map_of_mem ha⟩
  | @inv n ws a pre ha ih =>
    obtain ⟨ys,hy,old⟩ := ih
    refine ⟨ys,hy,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq | was
    · rw [eq,normalize_unary]
      exact old a ha
    · exact old w was
  | @binary n ws a b pre join ha hb ih =>
    obtain ⟨ys,hy,old⟩ := ih
    let kk := normalizedKind join (a empty) (b empty)
    have fresh := Free.binary hy kk (old a ha) (old b hb)
    refine ⟨_,fresh,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq | was
    · rw [eq,normalize_binary]
      simp [kk]
    · exact List.mem_cons_of_mem _ (old w was)

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

def absentBit : ρ → Bool := fun _ => false
def ins {α : Type} (a : α) (U : α → Prop) : α → Prop := fun v => v = a ∨ U v

 

inductive Live (goal : ρ → Bool) : Nat → ((ρ → Bool) → Prop) → Prop
  | stop : Live goal 0 (fun v => v=goal)
  | step {k U a b} (kind : Kind) (ab : a≠b)
      (ha : a≠absentBit) (hb : b≠absentBit)
      (fresh : ¬ins a (ins b U) (fun i => applyKind kind (a i) (b i)))
      (tail : Live goal k (ins (fun i => applyKind kind (a i) (b i)) U)) :
      Live goal (k+1) (ins a (ins b U))

private theorem same_result (kind : Kind) (a : ρ → Bool) :
    (fun i => applyKind kind (a i) (a i)) = a ∨
    (fun i => applyKind kind (a i) (a i)) = absentBit := by
  cases kind with
  | conj => left; funext i; cases a i <;> rfl
  | disj => left; funext i; cases a i <;> rfl
  | leftOnly => right; funext i; cases a i <;> rfl
  | rightOnly => right; funext i; cases a i <;> rfl

private theorem zero_left (kind : Kind) (b : ρ → Bool) :
    (fun i => applyKind kind false (b i)) = b ∨
    (fun i => applyKind kind false (b i)) = absentBit := by
  cases kind with
  | conj => right; rfl
  | disj => left; funext i; cases b i <;> rfl
  | leftOnly => right; rfl
  | rightOnly => left; funext i; cases b i <;> rfl

private theorem zero_right (kind : Kind) (a : ρ → Bool) :
    (fun i => applyKind kind (a i) false) = a ∨
    (fun i => applyKind kind (a i) false) = absentBit := by
  cases kind with
  | conj => right; funext i; cases a i <;> rfl
  | disj => left; funext i; cases a i <;> rfl
  | leftOnly => left; funext i; cases a i <;> rfl
  | rightOnly => right; funext i; cases a i <;> rfl

private theorem free_keeps_raw {raw ws : List (ρ → Bool)} {n : Nat}
    (run : Free raw n ws) {v} (h : v∈raw) : v∈ws := by
  induction run with
  | start => exact h
  | binary _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem rewind {raw ws : List (ρ → Bool)} {n : Nat} (run : Free raw n ws)
    (hz : absentBit∈raw) {goal : ρ → Bool} {k : Nat} {S : (ρ → Bool) → Prop}
    (needed : Live goal k S) (available : ∀ w, S w → w∈ws) :
    ∃ m T, m≤k+n ∧ Live goal m T ∧ ∀ w, T w → w∈raw := by
  classical
  induction run generalizing k S with
  | start => exact ⟨k,S,by omega,needed,available⟩
  | @binary n ws a b pre kind ha hb ih =>
    let z : ρ → Bool := fun i => applyKind kind (a i) (b i)
    have rawzero : absentBit∈ws := free_keeps_raw pre hz
    have values (w) (hw : S w) : w=z ∨ w∈ws := List.mem_cons.mp (available w hw)
    by_cases used : S z
    · by_cases old : z∈ws
      · obtain ⟨m,T,hm,ht,hsub⟩ := ih needed (fun w hw =>
          (values w hw).elim (fun e => e.symm ▸ old) id)
        exact ⟨m,T,by omega,ht,hsub⟩
      · let U : (ρ → Bool) → Prop := fun w => w≠z ∧ S w
        have eq : ins z U = S := by
          funext w
          apply propext
          constructor
          · intro hw
            rcases hw with h | h
            · exact h.symm ▸ used
            · exact h.2
          · intro hw
            by_cases e : w=z
            · exact Or.inl e
            · exact Or.inr ⟨e,hw⟩
        have memU (w) (hw : U w) : w∈ws := (values w hw.2).resolve_left hw.1
        have memAll (w) (hw : ins a (ins b U) w) : w∈ws := by
          rcases hw with e | e | hu
          · exact e.symm ▸ ha
          · exact e.symm ▸ hb
          · exact memU w hu
        have distinct : a≠b := by
          intro hab
          subst b
          rcases same_result kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonA : a≠absentBit := by
          intro ea
          subst a
          rcases zero_left kind b with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr hb)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonB : b≠absentBit := by
          intro eb
          subst b
          rcases zero_right kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nxt : Live goal (k+1) (ins a (ins b U)) :=
          Live.step kind distinct nonA nonB (fun bad => old (memAll z bad)) (eq.symm ▸ needed)
        obtain ⟨m,T,hm,ht,hsub⟩ := ih nxt memAll
        exact ⟨m,T,by omega,ht,hsub⟩
    · obtain ⟨m,T,hm,ht,hsub⟩ := ih needed (fun w hw =>
        (values w hw).resolve_left (fun e => used (e ▸ hw)))
      exact ⟨m,T,by omega,ht,hsub⟩

end CoThetaFreeCore

namespace CoThetaFreeCore

variable {ρ : Type}

theorem Live.separates {goal : ρ → Bool} {S k} (h : Live goal k S)
    (pos neg : ρ) (different : goal pos≠goal neg) :
    ∃ w, S w ∧ w pos≠w neg := by
  induction h with
  | stop => exact ⟨goal,rfl,different⟩
  | @step n U a b kind hab ha hb hf tail ih =>
    obtain ⟨w,hw,diff⟩ := ih
    rcases hw with eq | inU
    · subst w
      by_cases ea : a pos=a neg
      · refine ⟨b,Or.inr (Or.inl rfl),?_⟩
        intro eb
        apply diff
        change applyKind kind (a pos) (b pos) = applyKind kind (a neg) (b neg)
        rw [ea,eb]
      · exact ⟨a,Or.inl rfl,ea⟩
    · exact ⟨w,Or.inr (Or.inr inU),diff⟩

private def eraseOnce {α : Type} [DecidableEq α] (v : α) : List α → List α
  | [] => []
  | x::xs => if x=v then xs else x::eraseOnce v xs

private theorem erase_len {α : Type} [DecidableEq α] (v : α) (xs : List α) (h : v∈xs) :
    (eraseOnce v xs).length+1=xs.length := by
  induction xs with
  | nil => simp at h
  | cons a l ih =>
    by_cases e : a=v
    · simp [eraseOnce,e]
    · have hit : v∈l := (List.mem_cons.mp h).resolve_left (Ne.symm e)
      have hlen := ih hit
      simp [eraseOnce,e]
      omega

private theorem erase_preserves {α : Type} [DecidableEq α] {v w : α} (hw : w≠v)
    (xs : List α) (hin : w∈xs) : w∈eraseOnce v xs := by
  induction xs with
  | nil => simp at hin
  | cons a l ih =>
    by_cases e : a=v
    · subst a
      simpa [eraseOnce] using (List.mem_cons.mp hin).resolve_left hw
    · simp only [eraseOnce,if_neg e,List.mem_cons]
      rcases List.mem_cons.mp hin with eq | old
      · exact Or.inl eq
      · exact Or.inr (ih old)

theorem Live.width_cover {goal : ρ → Bool} {S k} (h : Live goal k S) :
    ∃ xs : List (ρ→Bool), xs.length≤k+1 ∧ ∀ w, S w → w∈xs := by
  classical
  induction h with
  | stop =>
    refine ⟨[goal],by simp,?_⟩
    intro w eq
    change w=goal at eq
    subst w
    simp
  | @step n U a b kind hab ha hb fresh tail ih =>
    let z : ρ → Bool := fun i => applyKind kind (a i) (b i)
    obtain ⟨xs,len,sub⟩ := ih
    have inside : z∈xs := sub z (Or.inl rfl)
    have reduced := erase_len z xs inside
    refine ⟨a::b::eraseOnce z xs,?_,?_⟩
    · simp only [List.length_cons]
      omega
    · intro w hw
      rcases hw with eq | eq | hu
      · simp [eq]
      · simp [eq]
      · have ne : w≠z := by
          intro eq
          apply fresh
          exact Or.inr (Or.inr ((congrArg U eq).mp hu))
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (erase_preserves ne xs (sub w (Or.inr hu))))

end CoThetaFreeCore

namespace CoThetaFreeCore

def theta (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 1 && x 4) || (x 0 && x 5) || (x 5 && x 6) || (x 1 && x 6)

def neigh (i : Fin 7) : Fin 7 := match i.val with
  | 0 => 2
  | 1 => 2
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 0
  | _ => 1

end CoThetaFreeCore

namespace CoThetaFreeCore

structure TraceGate (ρ : Type) where
  kind : Kind
  left : ρ → Bool
  right : ρ → Bool

def TraceGate.value {ρ} (g : TraceGate ρ) : ρ → Bool :=
  fun r => applyKind g.kind (g.left r) (g.right r)

def registered {ρ} (raw : List (ρ→Bool)) : List (TraceGate ρ) → Prop
  | [] => True
  | g::gs => g.left∈raw ∧ g.right∈raw ∧ registered (g.value::raw) gs

def traceWires {ρ} (raw : List (ρ→Bool)) : List (TraceGate ρ) → List (ρ→Bool)
  | [] => raw
  | g::gs => traceWires (g.value::raw) gs

def restrict {ρ σ} (lift : σ→ρ) (wire : ρ→Bool) : σ→Bool := fun i => wire (lift i)

def disappears {ρ σ} (lift : σ→ρ) (g : TraceGate ρ) : Prop :=
  restrict lift g.left=absentBit ∨ restrict lift g.right=absentBit

noncomputable def remaining {ρ σ} (lift : σ→ρ) : List (TraceGate ρ) → Nat
  | [] => 0
  | g::gs => by
    classical
    exact (if disappears lift g then 0 else 1) + remaining lift gs

noncomputable def saved {ρ σ} (lift : σ→ρ) : List (TraceGate ρ) → Nat
  | [] => 0
  | g::gs => by
    classical
    exact (if disappears lift g then 1 else 0) + saved lift gs

theorem accounted {ρ σ} (lift : σ→ρ) (gs : List (TraceGate ρ)) :
    remaining lift gs + saved lift gs = gs.length := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [remaining,saved,h] <;> omega

private theorem trace_step {ρ σ} (lift : σ→ρ) (g : TraceGate ρ)
    {init pool : List (σ→Bool)} {n} (live : Free init n pool)
    (ha : restrict lift g.left∈pool) (hb : restrict lift g.right∈pool)
    (hz : absentBit∈pool) :
    ∃ k ys, (disappears lift g → k=0) ∧ (¬disappears lift g → k=1) ∧
      Free init (n+k) ys ∧ (∀ a∈pool,a∈ys) ∧ restrict lift g.value∈ys := by
  classical
  by_cases drop : disappears lift g
  · refine ⟨0,pool,fun _ => rfl,fun n => (n drop).elim,live,fun _ h => h,?_⟩
    change (fun r => applyKind g.kind (restrict lift g.left r) (restrict lift g.right r))∈pool
    rcases drop with lo|lo
    · rw [lo]
      rcases zero_left g.kind (restrict lift g.right) with e|e
      · exact (congrArg (fun v => v∈pool) e).mpr hb
      · exact (congrArg (fun v => v∈pool) e).mpr hz
    · rw [lo]
      rcases zero_right g.kind (restrict lift g.left) with e|e
      · exact (congrArg (fun v => v∈pool) e).mpr ha
      · exact (congrArg (fun v => v∈pool) e).mpr hz
  · exact ⟨1,_,fun h => (drop h).elim,fun _ => rfl,Free.binary live g.kind ha hb,
      fun _ h => List.mem_cons_of_mem _ h,List.mem_cons_self⟩

theorem restrict_trace {ρ σ} (lift : σ→ρ) (gs : List (TraceGate ρ))
    {start : List (ρ→Bool)} {init pool : List (σ→Bool)} {n}
    (good : registered start gs) (pre : Free init n pool) (hz : absentBit∈pool)
    (known : ∀ w∈start,restrict lift w∈pool) :
    ∃ ys, Free init (n+remaining lift gs) ys ∧ ∀ w∈traceWires start gs,restrict lift w∈ys := by
  classical
  induction gs generalizing start pool n with
  | nil => exact ⟨_,pre,known⟩
  | cons g gs ih =>
    rcases good with ⟨left,right,rest⟩
    obtain ⟨k,mid,zeroCost,oneCost,step,old,output⟩ :=
      trace_step lift g pre (known _ left) (known _ right) hz
    have fresh (w) (h : w∈g.value::start) : restrict lift w∈mid := by
      rcases List.mem_cons.mp h with e|h
      · exact (congrArg (fun v => restrict lift v∈mid) e).mpr output
      · exact old _ (known _ h)
    obtain ⟨ys,tail,available⟩ := ih rest step (old _ hz) fresh
    refine ⟨ys,?_,available⟩
    by_cases d : disappears lift g
    · have eq := zeroCost d
      simpa [remaining,d,eq] using tail
    · have eq := oneCost d
      simpa [remaining,d,eq,Nat.add_assoc] using tail

end CoThetaFreeCore

namespace CoThetaFreeCore

theorem trace_append {ρ} (raw : List (ρ→Bool)) (a b : List (TraceGate ρ)) :
    traceWires raw (a++b)=traceWires (traceWires raw a) b := by
  induction a generalizing raw with
  | nil => rfl
  | cons x xs ih => exact ih (x.value::raw)

theorem registered_append {ρ} (raw : List (ρ→Bool)) (a b : List (TraceGate ρ)) :
    registered raw (a++b) ↔ registered raw a ∧ registered (traceWires raw a) b := by
  induction a generalizing raw with
  | nil => simp [registered,traceWires]
  | cons x xs ih =>
    simp only [List.cons_append,registered,traceWires,ih]
    simp [and_assoc]

theorem trace_of_free {ρ} {raw ws : List (ρ→Bool)} {n} (p : Free raw n ws) :
    ∃ gs : List (TraceGate ρ), gs.length=n ∧ registered raw gs ∧ traceWires raw gs=ws := by
  induction p with
  | start => exact ⟨[],rfl,True.intro,rfl⟩
  | @binary n ws a b pre kind ha hb ih =>
    obtain ⟨s,len,reg,eq⟩ := ih
    let g : TraceGate ρ := ⟨kind,a,b⟩
    refine ⟨s++[g],by simp [len],(registered_append _ _ _).2 ⟨reg,?_⟩,?_⟩
    · simpa [eq,registered,g] using And.intro ha hb
    · rw [trace_append,eq]
      rfl

def reads {ρ} (g : TraceGate ρ) (wire : ρ→Bool) : Prop := g.left=wire ∨ g.right=wire

theorem reading_zero_disappears {ρ σ} (lift : σ→ρ) {g : TraceGate ρ} {wire}
    (drop : restrict lift wire=absentBit) (h : reads g wire) : disappears lift g := by
  rcases h with e|e
  · exact Or.inl ((congrArg (restrict lift) e).trans drop)
  · exact Or.inr ((congrArg (restrict lift) e).trans drop)

theorem two_zero_propagate {ρ σ} (lift : σ→ρ) (g : TraceGate ρ)
    (l : restrict lift g.left=absentBit) (r : restrict lift g.right=absentBit) :
    restrict lift g.value=absentBit := by
  funext i
  change applyKind g.kind (restrict lift g.left i) (restrict lift g.right i) = false
  rw [l,r]
  cases g.kind <;> rfl

end CoThetaFreeCore
namespace CoThetaFreeCore

def agreeOutside {ρ : Type} (E : (ρ → Bool) → Prop) (r s : ρ)
    (ws : List (ρ → Bool)) : Prop := ∀ w∈ws, ¬ E w → w r = w s

theorem trace_barrier {ρ : Type} (E : (ρ→Bool)→Prop) (r s : ρ)
    (gs : List (TraceGate ρ)) {raw} (well : registered raw gs)
    (sources : agreeOutside E r s raw)
    (blocked : ∀ g∈gs, (E g.left ∨ E g.right) → g.value r=g.value s) :
    agreeOutside E r s (traceWires raw gs) := by
  classical
  induction gs generalizing raw with
  | nil => exact sources
  | cons g gs ih =>
    rcases well with ⟨hl,hr,rest⟩
    have same : g.value r=g.value s := by
      by_cases h : E g.left ∨ E g.right
      · exact blocked g (by simp) h
      · have le := sources g.left hl (fun x => h (Or.inl x))
        have re := sources g.right hr (fun x => h (Or.inr x))
        simp only [TraceGate.value,le,re]
    apply ih rest _ (fun t ht => blocked t (List.mem_cons_of_mem _ ht))
    intro w hw n
    rcases List.mem_cons.mp hw with e|h
    · exact e ▸ same
    · exact sources w h n

theorem reader_witness {ρ : Type} (E : (ρ→Bool)→Prop) (r s : ρ)
    {gs : List (TraceGate ρ)} {raw out} (well : registered raw gs)
    (sources : agreeOutside E r s raw) (hOut : out∈traceWires raw gs)
    (clear : ¬ E out) (diff : out r ≠ out s) :
    ∃ g∈gs, (E g.left ∨ E g.right) ∧ g.value r≠g.value s := by
  classical
  apply Classical.byContradiction
  intro bad
  apply diff
  apply trace_barrier E r s gs well sources _ out hOut clear
  intro g hg he
  apply Classical.byContradiction
  intro ne
  exact bad ⟨g,hg,he,ne⟩

theorem second_reader {ρ : Type} (x : ρ→Bool) (r s : ρ)
    {gs : List (TraceGate ρ)} {raw out} (gate : TraceGate ρ)
    (well : registered raw gs) (source : agreeOutside (·=x) r s raw)
    (hOut : out∈traceWires raw gs) (distinct : out≠x) (diff : out r ≠ out s)
    (masked : gate.value r=gate.value s) :
    ∃ g∈gs, reads g x ∧ g≠gate := by
  obtain ⟨g,hg,reader,ne⟩ := reader_witness (·=x) r s well source hOut distinct diff
  exact ⟨g,hg,reader,fun e => ne (e ▸ masked)⟩

end CoThetaFreeCore
namespace CoThetaFreeCore

def sufficient {ρ : Type} (raw : List (ρ→Bool)) (out : ρ→Bool)
    (gs : List (TraceGate ρ)) : Prop := registered raw gs ∧ out∈traceWires raw gs

def freshTrace {ρ : Type} (raw : List (ρ→Bool)) : List (TraceGate ρ)→Prop
  | [] => True
  | g::gs => g.value∉raw ∧ freshTrace (g.value::raw) gs

theorem trace_subset {ρ : Type} (gs : List (TraceGate ρ)) {as bs}
    (sub : ∀ w∈as,w∈bs) :
    (registered as gs → registered bs gs) ∧
      ∀ w∈traceWires as gs,w∈traceWires bs gs := by
  induction gs generalizing as bs with
  | nil => exact ⟨fun _ => True.intro,sub⟩
  | cons g tail ih =>
    have next : ∀ w∈g.value::as,w∈g.value::bs := by
      intro w hw
      rcases List.mem_cons.mp hw with e|h
      · exact List.mem_cons.mpr (Or.inl e)
      · exact List.mem_cons_of_mem _ (sub _ h)
    have h := ih next
    exact ⟨fun ok => ⟨sub _ ok.1,sub _ ok.2.1,h.1 ok.2.2⟩,h.2⟩

theorem simplify_trace {ρ : Type} {raw : List (ρ→Bool)} {out : ρ→Bool}
    (gs : List (TraceGate ρ)) (solves : sufficient raw out gs) :
    ∃ ts : List (TraceGate ρ), sufficient raw out ts ∧ freshTrace raw ts ∧
      (ts.length≤gs.length ∧ (¬freshTrace raw gs → ts.length<gs.length)) := by
  classical
  induction gs generalizing raw with
  | nil => exact ⟨[],solves,True.intro,Nat.le_refl _,fun bad => (bad True.intro).elim⟩
  | cons g gs ih =>
    obtain ⟨reg,output⟩ := solves
    rcases reg with ⟨left,right,rest⟩
    by_cases seen : g.value∈raw
    · have cover : ∀ w∈g.value::raw,w∈raw := by
        intro w h
        rcases List.mem_cons.mp h with e|h
        · exact e ▸ seen
        · exact h
      have reduce := trace_subset gs cover
      obtain ⟨ts,ok,fresh,le,_⟩ := ih ⟨reduce.1 rest,reduce.2 out output⟩
      refine ⟨ts,ok,fresh,?_,?_⟩ <;> simp only [List.length_cons] <;> omega
    · obtain ⟨ts,ok,fresh,le,lt⟩ := ih ⟨rest,output⟩
      refine ⟨g::ts,⟨⟨left,right,ok.1⟩,ok.2⟩,⟨seen,fresh⟩,?_,?_⟩
      · simp only [List.length_cons]
        omega
      · intro bad
        have h := lt (fun f => bad (And.intro seen f))
        simp only [List.length_cons]
        omega

theorem fresh_outputs {ρ : Type} {raw : List (ρ→Bool)} {gs : List (TraceGate ρ)}
    (fresh : freshTrace raw gs) (g : TraceGate ρ) (hg : g∈gs) : g.value∉raw := by
  induction gs generalizing raw with
  | nil => simp at hg
  | cons t ts ih =>
    rcases fresh with ⟨ft,fs⟩
    rcases List.mem_cons.mp hg with e|h
    · exact e ▸ ft
    · exact fun hRaw => ih fs h (List.mem_cons_of_mem _ hRaw)

end CoThetaFreeCore
namespace CoThetaFreeCore

def pairCode (op : Kind) (sw : Bool) (u v : Bool) : Bool :=
  if sw then applyKind op v u else applyKind op u v

theorem pair_collision (A B : Kind) : ∀ (sa sb : Bool),
    ∃ a b c d : Bool, (a,b)≠(c,d) ∧
      pairCode A sa a b=pairCode A sa c d ∧ pairCode B sb a b=pairCode B sb c d := by
  cases A <;> cases B <;> decide

theorem joint_reader_code {ρ : Type} (x y : ρ→Bool) (different : x≠y) (g : TraceGate ρ)
    (rx : reads g x) (ry : reads g y) :
    ∃ sw : Bool, ∀ i, g.value i=pairCode g.kind sw (x i) (y i) := by
  rcases rx with xl|xr <;> rcases ry with yl|yr
  · exact (different (xl.symm.trans yl)).elim
  · exact ⟨false,by simp [TraceGate.value,pairCode,xl,yr]⟩
  · exact ⟨true,by simp [TraceGate.value,pairCode,xr,yl]⟩
  · exact (different (xr.symm.trans yr)).elim

theorem two_joint_readers_impossible {ρ τ : Type} (x y out : ρ→Bool)
    (raw : List (ρ→Bool)) (gs : List (TraceGate ρ)) (A B : TraceGate ρ)
    (rxA : reads A x) (ryA : reads A y) (rxB : reads B x) (ryB : reads B y)
    (different : x≠y) (notPrimary : out≠x ∧ out≠y)
    (well : registered raw gs) (available : out∈traceWires raw gs)
    (point : Bool→Bool→τ→ρ)
    (px : ∀ a b j, x (point a b j)=a)
    (py : ∀ a b j, y (point a b j)=b)
    (fixed : ∀ a b c d j, agreeOutside (fun f => f=x ∨ f=y) (point a b j) (point c d j) raw)
    (separate : ∀ a b c d : Bool, (a,b)≠(c,d) → ∃ j : τ, out (point a b j)≠out (point c d j)) :
    ∃ g∈gs, (reads g x ∨ reads g y) ∧ g≠A ∧ g≠B := by
  classical
  obtain ⟨sa,saCode⟩ := joint_reader_code x y different A rxA ryA
  obtain ⟨sb,sbCode⟩ := joint_reader_code x y different B rxB ryB
  obtain ⟨a,b,c,d,ne,ca,cb⟩ := pair_collision A.kind B.kind sa sb
  obtain ⟨j,away⟩ := separate a b c d ne
  have eA : A.value (point a b j)=A.value (point c d j) := by
    simpa only [saCode,px,py] using ca
  have eB : B.value (point a b j)=B.value (point c d j) := by
    simpa only [sbCode,px,py] using cb
  have badOut : ¬(out=x ∨ out=y) := fun e => e.elim notPrimary.1 notPrimary.2
  obtain ⟨g,hg,read,diff⟩ := reader_witness (fun f => f=x ∨ f=y) _ _ well
    (fixed a b c d j) available badOut away
  refine ⟨g,hg,?_,fun eq => diff (eq ▸ eA),fun eq => diff (eq ▸ eB)⟩
  rcases read with (h|h)|(h|h)
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

end CoThetaFreeCore


namespace CoPetersenThetaGeometry

def nine (m : Nat) : Bool :=
  let x := m.testBit
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def theta (m : Nat) : Bool :=
  let x := m.testBit
  (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 1 && x 4) || (x 0 && x 5) || (x 5 && x 6) || (x 1 && x 6)

def embedding (j : Fin 6) : List Nat := match j.val with
  | 0 => [2, 8, 3, 1, 6, 7, 5]
  | 1 => [3, 5, 8, 2, 7, 4, 0]
  | 2 => [8, 0, 5, 3, 4, 6, 1]
  | 3 => [5, 1, 0, 8, 6, 7, 2]
  | 4 => [0, 2, 1, 5, 7, 4, 3]
  | _ => [1, 3, 2, 0, 4, 6, 8]

def cycleEnd (j : Fin 6) : Nat := match j.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 8
  | _ => 5

def subEnd (j : Fin 6) : Nat := match j.val with
  | 0 => 4
  | 1 => 6
  | 2 => 7
  | 3 => 4
  | 4 => 6
  | _ => 7

def outerNeighbor (j : Fin 6) : Nat := match j.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 8
  | 4 => 5
  | _ => 0

def shortNeighbor (j : Fin 6) : Nat := match j.val with
  | 0 => 3
  | 1 => 8
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | _ => 2

def sensitive : List Nat := [2, 0, 16, 2, 2, 20, 2, 10, 2, 16, 2, 32, 2, 80, 2, 130, 2, 258, 4, 1, 1, 0, 1, 4, 1, 9, 1, 20, 1, 36, 1, 64, 1, 129, 1, 257, 2, 9, 8, 2, 2, 0, 2, 8, 2, 18, 2, 34, 2, 72, 2, 128, 2, 258, 4, 5, 4, 18, 16, 4, 4, 0, 4, 16, 4, 36, 4, 68, 4, 144, 4, 256, 8, 1, 1, 10, 1, 5, 1, 8, 1, 0, 1, 40, 1, 65, 1, 129, 1, 257, 128, 1, 1, 130, 1, 5, 1, 9, 1, 144, 1, 0, 1, 65, 1, 128, 1, 256, 2, 257, 256, 2, 2, 260, 2, 10, 2, 18, 2, 34, 2, 0, 2, 130, 2, 256, 4, 5, 4, 34, 32, 4, 4, 40, 4, 20, 4, 32, 4, 68, 4, 0, 4, 260, 8, 9, 8, 10, 8, 36, 32, 8, 8, 48, 8, 32, 8, 64, 8, 136, 8, 0]

def plant (j : Fin 6) (m : Nat) : Nat :=
  (List.range 7).foldl (fun val i => if m.testBit i then
    val ||| (1 <<< ((embedding j).getD i 0)) else val) 0

def sensRow (p q : Fin 9) (v : Bool) : Nat :=
  sensitive.getD (2*(9*p.val+q.val)+v.toNat) 0

inductive Kind where | conj | disj | leftOnly | rightOnly
def binary : Kind → Bool → Bool → Bool
  | .conj,a,b => a&&b
  | .disj,a,b => a||b
  | .leftOnly,a,b => a && !b
  | .rightOnly,a,b => !a && b

end CoPetersenThetaGeometry
namespace CoThetaNine
open CoThetaFreeCore
open CoPetersenThetaGeometry (nine sensRow cycleEnd subEnd outerNeighbor shortNeighbor)

abbrev Input := Fin 512
def vtx (i : Fin 9) (r : Input) : Bool := r.val.testBit i.val
def ans (r : Input) : Bool := nine r.val
def vertices : List (Input→Bool) := absentBit::List.ofFn vtx

def row (n : Nat) : Input := ⟨n % 512,Nat.mod_lt _ (by decide)⟩
def index (n : Nat) : Fin 9 := ⟨n % 9,Nat.mod_lt _ (by decide)⟩
def ep (j : Fin 6) := index (cycleEnd j)
def eqp (j : Fin 6) := index (subEnd j)
def low (p q : Fin 9) (v : Bool) : Input := row (sensRow p q v)
def high (p q : Fin 9) (v : Bool) : Input := row ((low p q v).val ||| (1 <<< p.val))

theorem sens_data : ∀ (p q : Fin 9), p≠q → ∀ b : Bool,
    vtx p (low p q b)=false ∧ vtx p (high p q b)=true ∧
    vtx q (low p q b)=b ∧ vtx q (high p q b)=b ∧
    ans (low p q b)≠ans (high p q b) ∧
    ∀ t : Fin 9, t≠p → vtx t (low p q b)=vtx t (high p q b) := by decide +kernel

theorem distinct_raw : ∀ i j : Fin 9, i≠j → ∃ r : Input, vtx i r≠vtx j r := by
  decide +kernel

theorem not_raw : ∀ i : Fin 9, ∃ r : Input, ans r≠vtx i r := by decide +kernel

theorem distinct_inputs {i j : Fin 9} (ne : i≠j) : vtx i≠vtx j := by
  obtain ⟨r,d⟩ := distinct_raw i j ne
  exact fun h => d (congrFun h r)

theorem not_input (i : Fin 9) : ans≠vtx i := by
  obtain ⟨r,d⟩ := not_raw i
  exact fun h => d (congrFun h r)

theorem agree_on_vertices (E : (Input→Bool)→Prop) (r s : Input)
    (ok : ∀ i : Fin 9, ¬E (vtx i) → vtx i r=vtx i s) :
    agreeOutside E r s vertices := by
  intro w hw h
  rcases List.mem_cons.mp hw with z|h2
  · subst w
    rfl
  · obtain ⟨i,hi⟩ := List.mem_ofFn.mp h2
    subst w
    exact ok i h

def point (j : Fin 6) (a b : Bool) (t : Fin 3) : Input :=
  let u := (if a then 1 <<< cycleEnd j else 0) ||| (if b then 1 <<< subEnd j else 0)
  row (match t.val with
    | 0 => u
    | 1 => u ||| (1 <<< outerNeighbor j)
    | _ => u ||| (1 <<< shortNeighbor j))

theorem panel_data : ∀ (j : Fin 6), ep j≠eqp j ∧
    (∀ a b t, vtx (ep j) (point j a b t)=a ∧ vtx (eqp j) (point j a b t)=b) ∧
    (∀ a b c d t, ∀ i : Fin 9, i≠ep j → i≠eqp j →
      vtx i (point j a b t)=vtx i (point j c d t)) ∧
    (∀ a b c d : Bool, (a,b)≠(c,d) → ∃ t : Fin 3, ans (point j a b t)≠ans (point j c d t)) := by
  decide +kernel

theorem third_joint_reader (j : Fin 6) (gs : List (TraceGate Input)) (A B : TraceGate Input)
    (rxA : reads A (vtx (ep j))) (ryA : reads A (vtx (eqp j)))
    (rxB : reads B (vtx (ep j))) (ryB : reads B (vtx (eqp j)))
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, (reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) ∧ g≠A ∧ g≠B := by
  obtain ⟨distinct,axis,other,apart⟩ := panel_data j
  apply two_joint_readers_impossible (vtx (ep j)) (vtx (eqp j)) ans vertices gs A B
    rxA ryA rxB ryB (distinct_inputs distinct) ⟨not_input _,not_input _⟩ well out
    (point j) (fun a b t => (axis a b t).1) (fun a b t => (axis a b t).2) _ apart
  intro a b c d t
  apply agree_on_vertices
  intro i ni
  exact other a b c d t i (fun e => ni (Or.inl (congrArg vtx e)))
    (fun e => ni (Or.inr (congrArg vtx e)))

theorem masks_some_value (op : CoThetaFreeCore.Kind) : ∀ sw : Bool, ∃ v : Bool,
    ∀ a b : Bool, pairCode op sw a v=pairCode op sw b v := by
  cases op <;> decide

theorem another_raw_reader {p q : Fin 9} (ne : p≠q) (gs : List (TraceGate Input))
    (gate : TraceGate Input) (rx : reads gate (vtx p)) (ry : reads gate (vtx q))
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, reads g (vtx p) ∧ g≠gate := by
  obtain ⟨sw,code⟩ := joint_reader_code _ _ (distinct_inputs ne) gate rx ry
  obtain ⟨b,masked⟩ := masks_some_value gate.kind sw
  obtain ⟨pl,ph,ql,qh,diff,fixed⟩ := sens_data p q ne b
  have source : agreeOutside (fun w => w=vtx p) (low p q b) (high p q b) vertices := by
    apply agree_on_vertices
    intro i ni
    exact fixed i (fun e => ni (congrArg vtx e))
  have mask : gate.value (low p q b)=gate.value (high p q b) := by
    simpa only [code,pl,ph,ql,qh] using masked false true
  exact second_reader (vtx p) (low p q b) (high p q b) gate well source out (not_input p) diff mask

end CoThetaNine
namespace CoThetaNine
open CoThetaFreeCore

def neighborIndex (p : Fin 9) := index (p.val+1)
theorem neighbor_diff : ∀ p : Fin 9, p≠neighborIndex p := by decide

theorem a_raw_reader (p : Fin 9) {gs : List (TraceGate Input)}
    (well : registered vertices gs) (out : ans∈traceWires vertices gs) :
    ∃ g∈gs, reads g (vtx p) := by
  let q := neighborIndex p
  have ne : p≠q := neighbor_diff p
  obtain ⟨_,_,_,_,diff,fix⟩ := sens_data p q ne false
  have source : agreeOutside (fun w => w=vtx p) (low p q false) (high p q false) vertices := by
    apply agree_on_vertices
    intro i ni
    exact fix i (fun e => ni (congrArg vtx e))
  obtain ⟨g,hg,h,_⟩ := reader_witness (·=vtx p) _ _ well source out (not_input p) diff
  exact ⟨g,hg,h⟩

def ThreeReaders {ρ : Type} (P : TraceGate ρ→Prop) (gs : List (TraceGate ρ)) : Prop :=
  ∃ A∈gs, ∃ B∈gs, ∃ C∈gs, P A ∧ P B ∧ P C ∧ A≠B ∧ A≠C ∧ B≠C

theorem three_for_pair (j : Fin 6) {gs : List (TraceGate Input)}
    (well : registered vertices gs) (out : ans∈traceWires vertices gs)
    (known : (∃ A∈gs, ∃ B∈gs, reads A (vtx (ep j)) ∧ reads B (vtx (ep j)) ∧ A≠B) ∨
             (∃ A∈gs, ∃ B∈gs, reads A (vtx (eqp j)) ∧ reads B (vtx (eqp j)) ∧ A≠B)) :
    ThreeReaders (fun g => reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) gs := by
  classical
  have ne := (panel_data j).1
  by_cases shared : ∃ J∈gs, reads J (vtx (ep j)) ∧ reads J (vtx (eqp j))
  · obtain ⟨J,hJ,Jp,Jq⟩ := shared
    obtain ⟨A,hA,Ap,AJ⟩ := another_raw_reader ne gs J Jp Jq well out
    obtain ⟨B,hB,Bq,BJ⟩ := another_raw_reader ne.symm gs J Jq Jp well out
    by_cases e : A=B
    · subst B
      obtain ⟨C,hC,read,CJ,CA⟩ := third_joint_reader j gs J A Jp Jq Ap Bq well out
      exact ⟨J,hJ,A,hA,C,hC,Or.inl Jp,Or.inl Ap,read,AJ.symm,CJ.symm,CA.symm⟩
    · exact ⟨J,hJ,A,hA,B,hB,Or.inl Jp,Or.inl Ap,Or.inr Bq,AJ.symm,BJ.symm,e⟩
  · rcases known with ⟨A,hA,B,hB,Ap,Bp,AB⟩|⟨A,hA,B,hB,Aq,Bq,AB⟩
    · obtain ⟨C,hC,Cq⟩ := a_raw_reader (eqp j) well out
      exact ⟨A,hA,B,hB,C,hC,Or.inl Ap,Or.inl Bp,Or.inr Cq,AB,
        fun e => shared ⟨A,hA,Ap,e ▸ Cq⟩,fun e => shared ⟨B,hB,Bp,e ▸ Cq⟩⟩
    · obtain ⟨C,hC,Cp⟩ := a_raw_reader (ep j) well out
      exact ⟨A,hA,B,hB,C,hC,Or.inr Aq,Or.inr Bq,Or.inl Cp,AB,
        fun e => shared ⟨A,hA,e ▸ Cp,Aq⟩,fun e => shared ⟨B,hB,e ▸ Cp,Bq⟩⟩

end CoThetaNine
namespace CoThetaFreeCore

theorem fresh_ports {ρ : Type} {ws : List (ρ→Bool)} (g : TraceGate ρ)
    (hl : g.left∈ws) (hr : g.right∈ws) (hz : absentBit∈ws) (fresh : g.value∉ws) :
    g.left≠absentBit ∧ g.right≠absentBit ∧ g.left≠g.right := by
  refine ⟨?_,?_,?_⟩
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases zero_left g.kind g.right with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hr
    · exact (congrArg (fun v => v∈ws) ez).mpr hz
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases zero_right g.kind g.left with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hl
    · exact (congrArg (fun v => v∈ws) ez).mpr hz
  · intro e
    apply fresh
    change (fun i => applyKind g.kind (g.left i) (g.right i))∈ws
    rw [e]
    rcases same_result g.kind g.right with er|ez
    · exact (congrArg (fun v => v∈ws) er).mpr hr
    · exact (congrArg (fun v => v∈ws) ez).mpr hz

noncomputable def vanishing {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) :=
  gs.filter (fun g => @decide (disappears lift g) (Classical.propDecidable _))

theorem saved_eq_length {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) :
    saved lift gs = (vanishing lift gs).length := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [saved,vanishing,h] at * <;> omega

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore

theorem endpoint_in_slice : ∀ p : Fin 9, ∃ j : Fin 6, p=ep j ∨ p=eqp j := by decide

theorem ans_not_zero : ans≠absentBit := by
  intro e
  have bad := congrFun e (row 3)
  have test : ans (row 3)=true := by decide
  exact Bool.noConfusion (test.symm.trans bad)

theorem fresh_slice_head {g : TraceGate Input} {tail : List (TraceGate Input)}
    (h : sufficient vertices ans (g::tail)) (fresh : freshTrace vertices (g::tail)) :
    ∃ j : Fin 6, ThreeReaders (fun t => reads t (vtx (ep j)) ∨ reads t (vtx (eqp j))) (g::tail) := by
  obtain ⟨nonL,nonR,different⟩ := fresh_ports g h.1.1 h.1.2.1 (List.mem_cons_self) fresh.1
  have rawL := (List.mem_cons.mp h.1.1).resolve_left nonL
  have rawR := (List.mem_cons.mp h.1.2.1).resolve_left nonR
  obtain ⟨x,ex⟩ := List.mem_ofFn.mp rawL
  obtain ⟨y,ey⟩ := List.mem_ofFn.mp rawR
  have xy : x≠y := fun eq => different (ex.symm.trans ((congrArg vtx eq).trans ey))
  have rx : reads g (vtx x) := Or.inl ex.symm
  have ry : reads g (vtx y) := Or.inr ey.symm
  obtain ⟨s,hs,sx,other⟩ := another_raw_reader xy _ g rx ry h.1 h.2
  obtain ⟨j,side⟩ := endpoint_in_slice x
  refine ⟨j,three_for_pair j h.1 h.2 ?_⟩
  rcases side with eq|eq
  · exact Or.inl ⟨g,List.mem_cons_self,s,hs,eq ▸ rx,eq ▸ sx,other.symm⟩
  · exact Or.inr ⟨g,List.mem_cons_self,s,hs,eq ▸ rx,eq ▸ sx,other.symm⟩

theorem nonempty_solution {gs : List (TraceGate Input)} (h : sufficient vertices ans gs) : gs≠[] := by
  intro e
  subst gs
  have m : ans∈vertices := h.2
  rcases List.mem_cons.mp m with z|r
  · exact ans_not_zero z
  · obtain ⟨i,eq⟩ := List.mem_ofFn.mp r
    exact not_input i eq.symm

end CoThetaNine
namespace CoThetaBits
open CoThetaFreeCore

abbrev Width := 440
abbrev Bits := BitVec Width
abbrev Wire := Bits × Bits
abbrev Row := Bool × Fin Width
def zero : Wire := (0,0)
def full : Bits := BitVec.allOnes Width
def target : Wire := (full,0)

def den (wire : Wire) (r : Row) : Bool :=
  (if r.1 then wire.1 else wire.2).getLsbD r.2.val

def gate : Kind → Wire → Wire → Wire
  | .conj,a,b => (a.1 &&& b.1,a.2 &&& b.2)
  | .disj,a,b => (a.1 ||| b.1,a.2 ||| b.2)
  | .leftOnly,a,b => (a.1 &&& ~~~b.1,a.2 &&& ~~~b.2)
  | .rightOnly,a,b => (~~~a.1 &&& b.1,~~~a.2 &&& b.2)

theorem den_injective {a b : Wire} (h : den a=den b) : a=b := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact congrFun h (true,⟨i,hi⟩)
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    exact congrFun h (false,⟨i,hi⟩)

theorem den_gate (kind : Kind) (a b : Wire) :
    den (gate kind a b) = fun i => applyKind kind (den a i) (den b i) := by
  funext r
  obtain ⟨side,i⟩ := r
  cases kind <;> cases side <;>
    simp [den,gate,applyKind,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,i.isLt]

theorem den_zero : den zero = absentBit := by
  funext r
  obtain ⟨s,i⟩ := r
  cases s <;> simp [den,zero,absentBit]

theorem den_target (r : Row) : den target r = r.1 := by
  obtain ⟨s,i⟩ := r
  cases s <;> simp [den,target,full,BitVec.getLsbD_allOnes,i.isLt]

def sep (w : Wire) : Bits := w.1 ^^^ w.2

def coverage : List Wire → Bits
  | [] => 0
  | w::ws => sep w ||| coverage ws

theorem bit_covered {l : List Wire} {w : Wire} (hw : w∈l) (i : Fin Width)
    (h : den w (true,i) ≠ den w (false,i)) : (coverage l).getLsbD i.val=true := by
  induction l with
  | nil => simp at hw
  | cons a xs ih =>
    rw [coverage,BitVec.getLsbD_or]
    rcases List.mem_cons.mp hw with e|mem
    · subst a
      have hd : w.1.getLsbD i.val ≠ w.2.getLsbD i.val := h
      simp only [sep,BitVec.getLsbD_xor]
      cases hp : w.1.getLsbD i.val <;> cases hn : w.2.getLsbD i.val <;> simp_all
    · simp [ih mem]

theorem live_coverage {k} {S : (Row → Bool) → Prop} (l : List Wire)
    (h : Live (den target) k S) (sub : ∀ w, S w → ∃ v∈l, den v=w) :
    coverage l = full := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let j : Fin Width := ⟨i,hi⟩
  have ne : den target (true,j) ≠ den target (false,j) := by simp [den_target]
  obtain ⟨w,hw,hd⟩ := h.separates (true,j) (false,j) ne
  obtain ⟨v,hv,eq⟩ := sub w hw
  have h1 := bit_covered hv j (eq.symm ▸ hd)
  simpa [full,BitVec.getLsbD_allOnes,hi,j] using h1

end CoThetaBits

namespace CoThetaFreeCore

theorem length_of_cover {α : Type} (xs ys : List α) (nd : xs.Nodup)
    (sub : ∀ a∈xs, a∈ys) : xs.length≤ys.length := by
  classical
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have parts := List.nodup_cons.mp nd
    have has : a∈ys := sub a (by simp)
    have hl := erase_len a ys has
    have nextOK : xs.length≤(eraseOnce a ys).length := ih (eraseOnce a ys) parts.2 (by
      intro x hx
      have ne : x≠a := fun eq => parts.1 (eq ▸ hx)
      exact erase_preserves ne ys (sub x (List.mem_cons_of_mem _ hx)))
    simp only [List.length_cons]
    omega

end CoThetaFreeCore

namespace CoThetaBits
open CoThetaFreeCore

def Rep (ws : List Wire) (S : (Row→Bool)→Prop) : Prop :=
  ∀ f, S f ↔ ∃ w∈ws, den w=f

private theorem mem_rep {S ws} (rep : Rep ws S) (w : Wire) : w∈ws ↔ S (den w) := by
  constructor
  · intro h
    exact (rep _).2 ⟨w,h,rfl⟩
  · intro h
    obtain ⟨v,hv,e⟩ := (rep _).1 h
    exact den_injective e ▸ hv

private theorem den_nodup {ws : List Wire} (nd : ws.Nodup) : (ws.map den).Nodup := by
  induction ws with
  | nil => simp
  | cons a l ih =>
    rcases List.nodup_cons.mp nd with ⟨hne,ht⟩
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih ht⟩
    intro hm
    obtain ⟨v,hv,e⟩ := List.mem_map.mp hm
    exact hne (den_injective e ▸ hv)

theorem state_width {k S ws} (h : Live (den target) k S) (nd : ws.Nodup) (rep : Rep ws S) :
    ws.length≤k+1 := by
  obtain ⟨xs,hsize,hsub⟩ := h.width_cover
  have le := length_of_cover (ws.map den) xs (den_nodup nd) (by
    intro f hf
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp hf
    exact hsub f ((rep _).2 ⟨w,hw,eq⟩))
  simpa using Nat.le_trans le hsize

def trim (a b : Wire) (ws : List Wire) : List Wire :=
  ws.filter (fun w => w != a && w != b)

theorem mem_trim {w a b : Wire} {ws : List Wire} :
    w∈trim a b ws ↔ w∈ws ∧ w≠a ∧ w≠b := by simp [trim]

end CoThetaBits

namespace CoThetaBits
open CoThetaFreeCore

noncomputable def kept (a b : Wire) (U : (Row→Bool)→Prop) : List Wire := by
  classical
  exact (if U (den a) then [a] else []) ++ (if U (den b) then [b] else [])

theorem mem_kept {v a b : Wire} {U : (Row→Bool)→Prop} :
    v∈kept a b U ↔ (v=a ∧ U (den a)) ∨ (v=b ∧ U (den b)) := by
  classical
  by_cases p : U (den a) <;> by_cases q : U (den b) <;> simp [kept,p,q]

theorem edit_member {a b v : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (rep : Rep ws (ins (den a) (ins (den b) U))) :
    v∈(kept a b U ++ trim a b ws) ↔ U (den v) := by
  classical
  constructor
  · intro hm
    rcases List.mem_append.mp hm with inK | inR
    · rcases mem_kept.mp inK with ⟨e,yes⟩ | ⟨e,yes⟩ <;> subst v <;> exact yes
    · obtain ⟨inside,na,nb⟩ := mem_trim.mp inR
      rcases (mem_rep rep v).1 inside with e | e | hu
      · exact (na (den_injective e)).elim
      · exact (nb (den_injective e)).elim
      · exact hu
  · intro hu
    by_cases ea : v=a
    · exact List.mem_append.mpr (Or.inl (mem_kept.mpr (Or.inl ⟨ea,ea ▸ hu⟩)))
    by_cases eb : v=b
    · exact List.mem_append.mpr (Or.inl (mem_kept.mpr (Or.inr ⟨eb,eb ▸ hu⟩)))
    apply List.mem_append.mpr
    right
    exact mem_trim.mpr ⟨(mem_rep rep v).2 (Or.inr (Or.inr hu)),ea,eb⟩

theorem edit_distinct {a b : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (ab : a≠b) (nd : ws.Nodup) : (kept a b U ++ trim a b ws).Nodup := by
  classical
  have ndr : (trim a b ws).Nodup := nd.filter _
  have ha : a∉trim a b ws := fun h => (mem_trim.mp h).2.1 rfl
  have hb : b∉trim a b ws := fun h => (mem_trim.mp h).2.2 rfl
  by_cases p : U (den a) <;> by_cases q : U (den b) <;>
    simp [kept,p,q,List.nodup_cons,ha,hb,ab,ndr]

theorem edit_rep {a b z : Wire} {U : (Row→Bool)→Prop} {ws : List Wire}
    (rep : Rep ws (ins (den a) (ins (den b) U))) :
    Rep (z::(kept a b U ++ trim a b ws)) (ins (den z) U) := by
  intro f
  constructor
  · intro hf
    rcases hf with e | hu
    · exact ⟨z,by simp,e.symm⟩
    · obtain ⟨v,hv,e⟩ := (rep f).1 (Or.inr (Or.inr hu))
      refine ⟨v,List.mem_cons_of_mem _ ((edit_member rep).2 ?_),e⟩
      exact e.symm ▸ hu
  · intro h
    obtain ⟨v,hv,e⟩ := h
    rcases List.mem_cons.mp hv with vz | tail
    · subst v
      exact Or.inl e.symm
    · exact Or.inr (e ▸ (edit_member rep).1 tail)

end CoThetaBits

namespace CoThetaFreeCore
variable {ρ : Type}

theorem Live.excludes_zero {goal : ρ→Bool} {k S} (h : Live goal k S)
    (ng : goal≠absentBit) : ¬S absentBit := by
  induction h with
  | stop => exact fun eq => ng eq.symm
  | step _ _ ha hb _ _ ih =>
    intro bad
    rcases bad with eq | eq | u
    · exact ha eq.symm
    · exact hb eq.symm
    · exact ih (Or.inr u)

end CoThetaFreeCore

namespace CoThetaBits
open CoThetaFreeCore

private theorem target_nonzero : den target≠absentBit := by
  intro eq
  have q := congrFun eq (true,0)
  simp [den_target,absentBit] at q

end CoThetaBits

namespace CoThetaBits
open CoThetaFreeCore

def raw : List Wire := [(0xaa1404600a0270047003878002808c017f84fc07ff0fffe0050138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff,0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a),
(0xcc1807800c0380078003f8000300f00181ff3ff807f00ffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000,0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c),
(0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00007fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff,0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0),
(0xffe000000ffffff80000000003fffffe0007fffff800000007fffffc000003fff000000007ffffffffff000000003ffffffffc00000000,0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220),
(0xfffffffff00000000000000003fffffffff800000000000007fffffffffffc000000000007ffffffffffffffffffc00000000000000000,0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0),
(0xfffffffffffffffffffffffffc000000000000000000000007fffffffffffffffffffffff8000000000000000000000000000000000000,0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300),
(0xfffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000,0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00)]

def col (j : Fin 7) : Wire := raw[j.val]?.getD zero
def sample (r : Row) (j : Fin 7) : Bool := den (col j) r
def empty : Row := (false,0)
def start : List (Row→Bool) := (fun _ => false)::(fun _ => true)::raw.map den

def edgeWord : Wire := (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .conj (col 0) (col 2)) (gate .conj (col 1) (col 2))) (gate .conj (col 0) (col 3))) (gate .conj (col 3) (col 4))) (gate .conj (col 1) (col 4))) (gate .conj (col 0) (col 5))) (gate .conj (col 5) (col 6))) (gate .conj (col 1) (col 6)))

theorem edge_exact : edgeWord=target := by decide +kernel
theorem sample_correct (r : Row) : CoThetaFreeCore.theta (sample r)=den target r := by
  have h := congrFun (congrArg den edge_exact) r
  simp only [edgeWord,den_gate,applyKind] at h
  exact h

theorem raw_is_ofFn : List.ofFn col=raw := rfl
theorem raw_nodup : raw.Nodup := by decide +kernel
def privateIndex (j : Fin 7) : Fin Width := match j.val with
  | 0 => 4
  | 1 => 17
  | 2 => 1
  | 3 => 35
  | 4 => 71
  | 5 => 148
  | _ => 244

theorem private_row : ∀ j k : Fin 7,
    den (col k) (true,privateIndex j) ≠ den (col k) (false,privateIndex j) → k=j := by decide +kernel

private theorem indexed {v : Wire} (h : v∈raw) : ∃ j, col j=v := by
  rw [←raw_is_ofFn] at h
  exact List.mem_ofFn.mp h

theorem root_rep {k S} (h : Live (den target) k S)
    (inputs : ∀ f, S f → f=absentBit ∨ ∃ j, den (col j)=f) : Rep raw S := by
  have allcol (j : Fin 7) : S (den (col j)) := by
    let i := privateIndex j
    have diff : den target (true,i) ≠ den target (false,i) := by simp [den_target]
    obtain ⟨v,hv,hd⟩ := h.separates (true,i) (false,i) diff
    rcases inputs v hv with z | ⟨l,e⟩
    · subst v
      exact (hd rfl).elim
    · subst v
      obtain rfl := private_row j l hd
      exact hv
  intro f
  constructor
  · intro hf
    rcases inputs f hf with z | ⟨j,eq⟩
    · exact (h.excludes_zero target_nonzero (z ▸ hf)).elim
    · refine ⟨col j,?_,eq⟩
      rw [←raw_is_ofFn]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · rintro ⟨v,hv,eq⟩
    obtain ⟨j,rfl⟩ := indexed hv
    exact eq ▸ allcol j

end CoThetaBits
namespace CoThetaFreeCore

theorem Free.map_rows {ρ σ : Type} (lift : σ→ρ)
    {init ws n} (run : @Free ρ init n ws) :
    Free (init.map (restrict lift)) n (ws.map (restrict lift)) := by
  induction run with
  | start => exact Free.start
  | @binary n ws a b pre kind ha hb ih =>
    have h1 := List.mem_map_of_mem (f:=restrict lift) ha
    have h2 := List.mem_map_of_mem (f:=restrict lift) hb
    exact Free.binary ih kind h1 h2

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore

abbrev SmallInput := Fin 128
def raw7 (i : Fin 7) (r : SmallInput) : Bool := r.val.testBit i.val
def ans7 (r : SmallInput) : Bool := CoPetersenThetaGeometry.theta r.val
def vertices7 : List (SmallInput→Bool) := absentBit::List.ofFn raw7
def sliceLift (j : Fin 6) (r : SmallInput) : Input := row (CoPetersenThetaGeometry.plant j r.val)

def coord7 (j : Fin 6) (v : Fin 9) : Option (Fin 7) :=
  match j.val,v.val with
  | 0,2 => some 0
  | 0,8 => some 1
  | 0,3 => some 2
  | 0,1 => some 3
  | 0,6 => some 4
  | 0,7 => some 5
  | 0,5 => some 6
  | 1,3 => some 0
  | 1,5 => some 1
  | 1,8 => some 2
  | 1,2 => some 3
  | 1,7 => some 4
  | 1,4 => some 5
  | 1,0 => some 6
  | 2,8 => some 0
  | 2,0 => some 1
  | 2,5 => some 2
  | 2,3 => some 3
  | 2,4 => some 4
  | 2,6 => some 5
  | 2,1 => some 6
  | 3,5 => some 0
  | 3,1 => some 1
  | 3,0 => some 2
  | 3,8 => some 3
  | 3,6 => some 4
  | 3,7 => some 5
  | 3,2 => some 6
  | 4,0 => some 0
  | 4,2 => some 1
  | 4,1 => some 2
  | 4,5 => some 3
  | 4,7 => some 4
  | 4,4 => some 5
  | 4,3 => some 6
  | 5,1 => some 0
  | 5,3 => some 1
  | 5,2 => some 2
  | 5,0 => some 3
  | 5,4 => some 4
  | 5,6 => some 5
  | 5,8 => some 6
  | _,_ => none

theorem slice7_values : ∀(j : Fin 6) (r : SmallInput),
    ans (sliceLift j r)=ans7 r ∧ vtx (ep j) (sliceLift j r)=false ∧
    vtx (eqp j) (sliceLift j r)=false ∧
    ∀ i : Fin 9, vtx i (sliceLift j r)=
      match coord7 j i with | none => false | some k => raw7 k r := by decide +kernel

theorem slice_known (j : Fin 6) : ∀ w∈vertices, restrict (sliceLift j) w∈vertices7 := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp r
    subst w
    cases h : coord7 j i with
    | none =>
      have eq : restrict (sliceLift j) (vtx i)=absentBit := by
        funext r
        simpa [restrict,h,absentBit] using (slice7_values j r).2.2.2 i
      exact eq ▸ List.mem_cons_self
    | some k =>
      have eq : restrict (sliceLift j) (vtx i)=raw7 k := by
        funext r
        simpa [restrict,h] using (slice7_values j r).2.2.2 i
      exact eq ▸ List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨k,rfl⟩)

def packBits (a b c d e f g : Bool) : SmallInput :=
  ⟨(a.toNat+2*b.toNat+4*c.toNat+8*d.toNat+16*e.toNat+32*f.toNat+64*g.toNat) % 128,
    Nat.mod_lt _ (by decide)⟩

def pack (x : Fin 7 → Bool) : SmallInput := packBits (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

theorem pack_exact : ∀ a b c d e f g : Bool,
    let t := packBits a b c d e f g
    (raw7 0 t,raw7 1 t,raw7 2 t,raw7 3 t,raw7 4 t,raw7 5 t,raw7 6 t)=(a,b,c,d,e,f,g) := by
  intro a b c d e f g
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> rfl

theorem unpack (x : Fin 7→Bool) (j : Fin 7) : raw7 j (pack x)=x j := by
  have h := pack_exact (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
  change (_,_,_,_,_,_,_) = (_,_,_,_,_,_,_) at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨e0,e1,e2,e3,e4,e5,e6⟩ := h
  have total : ∀ t : Fin 7, t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by decide
  rcases total j with e|e|e|e|e|e|e <;> subst j <;> assumption

theorem numeric_goal (r : SmallInput) : ans7 r=CoThetaFreeCore.theta (fun j => raw7 j r) := by
  rfl

def toRows (r : CoThetaBits.Row) := pack (CoThetaBits.sample r)

theorem numeric_target : restrict toRows ans7=CoThetaBits.den CoThetaBits.target := by
  funext r
  change ans7 (toRows r)=_
  rw [numeric_goal]
  have eq : (fun j => raw7 j (toRows r))=CoThetaBits.sample r :=
    funext (unpack (CoThetaBits.sample r))
  rw [eq]
  exact CoThetaBits.sample_correct r

end CoThetaNine
namespace CoThetaNine
open CoThetaFreeCore

def SignedLower : Prop := ∀ {n ws}, Free vertices7 n ws → ans7∈ws → 11≤n

theorem three_saved (j : Fin 6) {gs : List (TraceGate Input)}
    (three : ThreeReaders (fun g => reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) gs) :
    3≤ saved (sliceLift j) gs := by
  classical
  obtain ⟨A,hA,B,hB,C,hC,rA,rB,rC,AB,AC,BC⟩ := three
  have zp : restrict (sliceLift j) (vtx (ep j))=absentBit :=
    funext (fun r => (slice7_values j r).2.1)
  have zq : restrict (sliceLift j) (vtx (eqp j))=absentBit :=
    funext (fun r => (slice7_values j r).2.2.1)
  have retain (g : TraceGate Input) (hg : g∈gs) (r : reads g (vtx (ep j)) ∨ reads g (vtx (eqp j))) :
      g∈vanishing (sliceLift j) gs := by
    have d : disappears (sliceLift j) g := r.elim (reading_zero_disappears _ zp) (reading_zero_disappears _ zq)
    simp [vanishing,hg,d]
  have nd : [A,B,C].Nodup := by simp [AB,AC,BC]
  have sub : ∀ t∈[A,B,C],t∈vanishing (sliceLift j) gs := by
    intro t h
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain A hA rA
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain B hB rB
    rcases List.mem_cons.mp h with e|h
    · exact e ▸ retain C hC rC
    · simp at h
  rw [saved_eq_length]
  exact length_of_cover [A,B,C] _ nd sub

theorem residual_at_least_eleven (cert : SignedLower)
    (j : Fin 6) {gs : List (TraceGate Input)} (ok : sufficient vertices ans gs) :
    11≤remaining (sliceLift j) gs := by
  obtain ⟨ws,run,sub⟩ := restrict_trace (sliceLift j) gs ok.1
    (Free.start (raw:=vertices7)) List.mem_cons_self (slice_known j)
  have read := sub ans ok.2
  have ax : restrict (sliceLift j) ans=ans7 := funext (fun r => (slice7_values j r).1)
  rw [ax] at read
  simpa only [Nat.zero_add] using cert run read

theorem any_nine_lower (cert : SignedLower)
    {gs : List (TraceGate Input)} (ok : sufficient vertices ans gs) : 14≤gs.length := by
  classical
  obtain ⟨ts,solves,fresh,le,_⟩ := simplify_trace gs ok
  cases ts with
  | nil => exact (nonempty_solution solves rfl).elim
  | cons g tail =>
    obtain ⟨j,readers⟩ := fresh_slice_head solves fresh
    have gain := three_saved j readers
    have cost := residual_at_least_eleven cert j solves
    have eq := accounted (sliceLift j) (g::tail)
    omega

end CoThetaNine
namespace CoNatBench
abbrev Word := Nat × Nat
def project (w : CoThetaBits.Wire) : Word := (w.1.toNat,w.2.toNat)
def target := project CoThetaBits.target
def all := target.1
def sep (w : Word) := w.1 ^^^ w.2
def meet (a b : Word) : Word := (a.1 &&& b.1,a.2 &&& b.2)
def join (a b : Word) : Word := (a.1 ||| b.1,a.2 ||| b.2)
def skip (a b : Word) : Word := (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
def cover (ws : List Word) := ws.foldl (fun c w => c ||| sep w) 0
def pairs {α : Type} (f : α → α → Bool) : List α → Bool
  | [] => false
  | x::xs => xs.any (f x) || pairs f xs
def successors (k : Nat) (next : List Word→Bool) (ws : List Word) : Bool :=
  let n := ws.length
  if n>k+2 then false else
  pairs (fun a b =>
    let rest := ws.filter (fun w => w != a && w != b)
    let base := cover rest
    let ca := base ||| sep a
    let cb := base ||| sep b
    let stay := n+1≤k+1
    let half := n≤k+1
    ([meet a b,join a b,skip a b,skip b a] : List Word).any fun z =>
      z != (0,0) && !(ws.contains z) &&
        (let cut := sep z
         ((base ||| cut)==all && next (z::rest)) ||
         (half && (ca ||| cut)==all && next (z::a::rest)) ||
         (half && (cb ||| cut)==all && next (z::b::rest)) ||
         (stay && next (z::a::b::rest)))) ws


def search : Nat → List Word → Bool
  | 0,ws => ws.contains target
  | k+1,ws => ws.contains target || successors k (search k) ws
end CoNatBench
namespace CoNatBench

def multiplicities : List Word → Nat×Nat
  | [] => (0,0)
  | w::ws =>
    let s := sep w
    let m := multiplicities ws
    (s ||| m.1, (s &&& m.1) ||| m.2)

def guarded (k : Nat) (next : List Word→Bool) (ws : List Word) : Bool :=
  let n := ws.length
  if n>k+2 then false else
  let bucket := multiplicities ws
  let once := bucket.1 ^^^ bucket.2
  let cols := ws.map fun w => (w,sep w &&& once)
  let half := n≤k+1
  let stay := n≤k
  pairs (fun a b =>
    let a0 := (a.2 &&& b.1.1)==0
    let a1 := (a.2 &&& b.1.1)==a.2
    let b0 := (b.2 &&& a.1.1)==0
    let b1 := (b.2 &&& a.1.1)==b.2
    let rest := ws.filter (fun w => w != a.1 && w != b.1)
    let base := cover rest
    let attempt (oka okb : Bool) (value : Unit → Word) :=
      (stay || (half && (oka || okb)) || (oka && okb)) &&
        (let z := value ()
         z != (0,0) && !(ws.contains z) &&
          ((oka && okb && (base ||| sep z)==all && next (z::rest)) ||
           (half && okb && next (z::a.1::rest)) ||
           (half && oka && next (z::b.1::rest)) ||
           (stay && next (z::a.1::b.1::rest))))
    attempt a1 b1 (fun _ => meet a.1 b.1) ||
      attempt a0 b0 (fun _ => join a.1 b.1) ||
      attempt a0 b1 (fun _ => skip a.1 b.1) ||
      attempt a1 b0 (fun _ => skip b.1 a.1)) cols

def guardedSearch : Nat → List Word → Bool
  | 0,ws => ws.contains target
  | k+1,ws => ws.contains target || guarded k (guardedSearch k) ws

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

private theorem foldBits (ws : List Word) (i : Nat) (seed : Nat) :
    (ws.foldl (fun c w => c ||| sep w) seed).testBit i =
    (seed.testBit i || ws.any (fun w => (sep w).testBit i)) := by
  induction ws generalizing seed with
  | nil => simp
  | cons a xs ih =>
    simp [List.foldl_cons,ih,Nat.testBit_or,Bool.or_assoc]

theorem covered_iff (ws : List Word) (i : Nat) :
    (cover ws).testBit i=true ↔ ∃ w∈ws,(sep w).testBit i=true := by
  simp [cover,foldBits,List.any_eq_true]

private theorem firstMask (ws : List Word) (i : Nat) (w : Word)
    (h : w∈ws) (bit : (sep w).testBit i=true) : (multiplicities ws).1.testBit i=true := by
  induction ws with
  | nil => simp at h
  | cons a xs ih =>
    change (sep a ||| (multiplicities xs).1).testBit i=true
    rw [Nat.testBit_or,Bool.or_eq_true]
    rcases List.mem_cons.mp h with e|h
    · exact Or.inl (e ▸ bit)
    · exact Or.inr (ih h)

private theorem secondMask (ws : List Word) (i : Nat) {a b : Word} (ab : a≠b)
    (ha : a∈ws) (hb : b∈ws) (da : (sep a).testBit i=true) (db : (sep b).testBit i=true) :
    (multiplicities ws).2.testBit i=true := by
  induction ws with
  | nil => simp at ha
  | cons h xs ih =>
    change ((sep h &&& (multiplicities xs).1) ||| (multiplicities xs).2).testBit i=true
    rw [Nat.testBit_or,Bool.or_eq_true]
    by_cases x : a=h
    · subst h
      have bt := (List.mem_cons.mp hb).resolve_left ab.symm
      exact Or.inl (by simp [Nat.testBit_and,da,firstMask xs i b bt db])
    · have atail := (List.mem_cons.mp ha).resolve_left x
      by_cases y : b=h
      · subst h
        exact Or.inl (by simp [Nat.testBit_and,db,firstMask xs i a atail da])
      · exact Or.inr (ih atail ((List.mem_cons.mp hb).resolve_left y))

def privateMask (ws : List Word) (a : Word) :=
  sep a &&& ((multiplicities ws).1 ^^^ (multiplicities ws).2)

theorem private_only {ws : List Word} {a : Word} (ha : a∈ws) {i : Nat}
    (h : (privateMask ws a).testBit i=true) :
    (sep a).testBit i=true ∧ ∀ b∈ws, b≠a → (sep b).testBit i=false := by
  simp only [privateMask,Nat.testBit_and,Nat.testBit_xor,Bool.and_eq_true] at h
  obtain ⟨bit,one⟩ := h
  have first := firstMask ws i a ha bit
  have no : (multiplicities ws).2.testBit i=false := by
    cases m : (multiplicities ws).2.testBit i <;> simp_all
  refine ⟨bit,?_⟩
  intro b hb diff
  cases d : (sep b).testBit i with
  | false => rfl
  | true => exact Bool.noConfusion (no.symm.trans (secondMask ws i diff hb ha d bit))

def wordGate : Kind→Word→Word→Word
  | .conj => meet
  | .disj => join
  | .leftOnly => skip
  | .rightOnly => fun a b => skip b a

def leftNeeds : Kind→Bool
  | .conj | .rightOnly => true
  | .disj | .leftOnly => false

theorem bit_rule (op : Kind) (a b : Word) (i : Nat) :
    (wordGate op a b).1.testBit i = applyKind op (a.1.testBit i) (b.1.testBit i) ∧
    (wordGate op a b).2.testBit i = applyKind op (a.2.testBit i) (b.2.testBit i) := by
  cases op <;> simp only [wordGate,meet,join,skip,applyKind,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor]
  all_goals
    cases a.1.testBit i <;> cases b.1.testBit i <;> cases a.2.testBit i <;> cases b.2.testBit i <;> decide

theorem masked_l (op : Kind) (a b u : Bool) (miss : u≠leftNeeds op) :
    applyKind op a u = applyKind op b u := by
  cases op <;> cases u <;> simp_all [leftNeeds,applyKind]

theorem needed_bit {ws out : List Word} {a b : Word} (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (op : Kind) (same : cover out=cover ws)
    (others : ∀w∈out, w=wordGate op a b ∨ w∈ws ∧ w≠a)
    {i : Nat} (p : (privateMask ws a).testBit i=true) :
    b.1.testBit i = leftNeeds op := by
  obtain ⟨da,only⟩ := private_only ha p
  have db := only b hb ab.symm
  have beq : b.1.testBit i=b.2.testBit i := by
    simp only [sep,Nat.testBit_xor] at db
    cases hl : b.1.testBit i <;> cases hr : b.2.testBit i <;> simp_all
  have on := (covered_iff ws i).2 ⟨a,ha,da⟩
  rw [←same] at on
  obtain ⟨w,hw,good⟩ := (covered_iff out i).1 on
  rcases others w hw with e|⟨belongs,no⟩
  · subst w
    apply Classical.byContradiction
    intro neg
    obtain ⟨lo,hi⟩ := bit_rule op a b i
    have flat := masked_l op (a.1.testBit i) (a.2.testBit i) (b.1.testBit i) neg
    rw [←beq] at hi
    simp [sep,Nat.testBit_xor,lo,hi,flat] at good
  · exact Bool.noConfusion ((only w belongs no).symm.trans good)

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

def maskOK (word mask : Nat) (want : Bool) : Bool :=
  if want then (mask &&& word)==mask else (mask &&& word)==0

theorem mask_hit {ws out : List Word} {a b : Word} (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (op : Kind) (same : cover out=cover ws)
    (others : ∀w∈out, w=wordGate op a b ∨ w∈ws ∧ w≠a) :
    maskOK b.1 (privateMask ws a) (leftNeeds op)=true := by
  have key := fun i => @needed_bit ws out a b ha hb ab op same others i
  cases d : leftNeeds op with
  | false =>
    simp only [maskOK,Bool.false_eq_true,↓reduceIte,beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    cases h : (privateMask ws a).testBit i with
    | false => simp [Nat.testBit_and,h]
    | true => simp [Nat.testBit_and,h,key i h,d]
  | true =>
    simp only [maskOK,↓reduceIte,beq_iff_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    cases h : (privateMask ws a).testBit i with
    | false => simp [Nat.testBit_and,h]
    | true => simp [Nat.testBit_and,h,key i h,d]

def reflectOp : Kind→Kind
  | .conj => .conj
  | .disj => .disj
  | .leftOnly => .rightOnly
  | .rightOnly => .leftOnly

theorem gate_swap (op : Kind) (a b : Word) : wordGate (reflectOp op) b a=wordGate op a b := by
  cases op <;> simp [reflectOp,wordGate,meet,join,skip,Nat.and_comm,Nat.or_comm]

def restOf (ws : List Word) (a b : Word) := ws.filter (fun w => w != a && w != b)
def keepList (ka kb : Bool) (a b : Word) := (if ka then [a] else [])++(if kb then [b] else [])
def extension (ws : List Word) (a b : Word) (op : Kind) (ka kb : Bool) :=
  wordGate op a b::(keepList ka kb a b ++ restOf ws a b)

theorem rest_mem {ws : List Word} {a b w} : w∈restOf ws a b ↔ w∈ws ∧ w≠a ∧ w≠b := by
  simp [restOf]

theorem kept_mask_left {ws : List Word} {a b : Word} (op : Kind)
    (ha : a∈ws) (hb : b∈ws) (ab : a≠b) (kb : Bool)
    (full : cover (extension ws a b op false kb)=cover ws) :
    maskOK b.1 (privateMask ws a) (leftNeeds op)=true := by
  apply mask_hit ha hb ab op full
  intro w hw
  rcases List.mem_cons.mp hw with eq|ht
  · exact Or.inl eq
  · right
    rcases List.mem_append.mp ht with hk|hr
    · cases kb <;> simp [keepList] at hk
      exact hk ▸ And.intro hb ab.symm
    · have h := rest_mem.mp hr
      exact ⟨h.1,h.2.1⟩

theorem kept_mask_right {ws : List Word} {a b : Word} (op : Kind)
    (ha : a∈ws) (hb : b∈ws) (ab : a≠b) (ka : Bool)
    (full : cover (extension ws a b op ka false)=cover ws) :
    maskOK a.1 (privateMask ws b) (leftNeeds (reflectOp op))=true := by
  apply mask_hit hb ha ab.symm (reflectOp op) full
  intro w hw
  rcases List.mem_cons.mp hw with eq|ht
  · exact Or.inl (eq.trans (gate_swap op a b).symm)
  · right
    rcases List.mem_append.mp ht with hk|hr
    · cases ka <;> simp [keepList] at hk
      exact hk ▸ And.intro ha ab
    · have h := rest_mem.mp hr
      exact ⟨h.1,h.2.2⟩

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

def tryField (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) (op : Kind) : Bool :=
  let n := ws.length
  let half := n≤k+1
  let stay := n≤k
  let rest := restOf ws a.1 b.1
  let base := cover rest
  let oka := maskOK b.1.1 a.2 (leftNeeds op)
  let okb := maskOK a.1.1 b.2 (leftNeeds (reflectOp op))
  (stay || (half && (oka || okb)) || (oka && okb)) &&
    (let z := wordGate op a.1 b.1
     z != (0,0) && !(ws.contains z) &&
      ((oka && okb && (base ||| sep z)==all && next (z::rest)) ||
       (half && okb && next (z::a.1::rest)) ||
       (half && oka && next (z::b.1::rest)) ||
       (stay && next (z::a.1::b.1::rest))))

def pairTry (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) : Bool :=
  tryField k next ws a b .conj || tryField k next ws a b .disj ||
    tryField k next ws a b .leftOnly || tryField k next ws a b .rightOnly

theorem guarded_eq (k : Nat) (next : List Word→Bool) (ws : List Word) :
    guarded k next ws =
      if ws.length>k+2 then false else
        pairs (pairTry k next ws) (ws.map fun a => (a,privateMask ws a)) := rfl

theorem cover_cons (w : Word) (ws : List Word) : cover (w::ws)=sep w ||| cover ws := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [cover,foldBits,Nat.testBit_or]

theorem drop_len (ws : List Word) (d : Word) (nd : ws.Nodup) (hd : d∈ws) :
    (ws.filter (fun w => w != d)).length+1=ws.length := by
  induction ws with
  | nil => simp at hd
  | cons x xs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    by_cases e : x=d
    · subst x
      have self : xs.filter (fun w => w != d)=xs := List.filter_eq_self.mpr (by
        intro v hv
        have neq : v≠d := fun eq => fresh (eq ▸ hv)
        simp [neq])
      simp [self]
    · have hit := (List.mem_cons.mp hd).resolve_left (Ne.symm e)
      have n := ih rest hit
      simp [e,n]

theorem rest_len (ws : List Word) (a b : Word) (nd : ws.Nodup) (ha : a∈ws) (hb : b∈ws) (ab : a≠b) :
    (restOf ws a b).length+2=ws.length := by
  let after := ws.filter (fun w => w != a)
  have inside : b∈after := by simp [after,hb,ab.symm]
  have n1 := drop_len ws a nd ha
  have n2 := drop_len after b (nd.filter _) inside
  have order : (after.filter (fun w => w != b))=restOf ws a b := by
    simp [after,restOf,List.filter_filter,Bool.and_comm]
  rw [order] at n2
  dsimp [after] at n2
  omega

theorem tryField_hit {k : Nat} {ws : List Word} {a b : Word} (op : Kind) (ka kb : Bool)
    (next : List Word→Bool) (nd : ws.Nodup) (ha : a∈ws) (hb : b∈ws) (ab : a≠b)
    (non : wordGate op a b≠(0,0)) (fresh : wordGate op a b∉ws)
    (wide : (extension ws a b op ka kb).length≤k+1) (old : cover ws=all)
    (new : cover (extension ws a b op ka kb)=all) (pass : next (extension ws a b op ka kb)=true) :
    tryField k next ws (a,privateMask ws a) (b,privateMask ws b) op=true := by
  have remaining := rest_len ws a b nd ha hb ab
  have same := new.trans old.symm
  cases ka <;> cases kb
  · have l := kept_mask_left op ha hb ab false same
    have r := kept_mask_right op ha hb ab false same
    have cc : cover (restOf ws a b) ||| sep (wordGate op a b)=all := by
      simpa [extension,keepList,cover_cons,Nat.or_comm] using new
    simp [extension,keepList] at pass
    simp [tryField,l,r,non,fresh,cc,pass]
  · have l := kept_mask_left op ha hb ab true same
    have width : ws.length≤k+1 := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,l,width,non,fresh,pass]
  · have r := kept_mask_right op ha hb ab true same
    have width : ws.length≤k+1 := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,r,width,non,fresh,pass]
  · have width : ws.length≤k := by simp [extension,keepList] at wide; omega
    simp [extension,keepList] at pass
    simp [tryField,width,non,fresh,pass]

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

theorem project_inj {a b : CoThetaBits.Wire} (h : project a=project b) : a=b := by
  apply Prod.ext <;> apply BitVec.eq_of_toNat_eq
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

@[simp] theorem project_eq {a b : CoThetaBits.Wire} : project a=project b ↔ a=b :=
  ⟨project_inj,congrArg project⟩

private theorem mask_sub {n} (a b : BitVec n) :
    (a &&& ~~~b)=a ^^^ (a &&& b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

private theorem mask_rev {n} (a b : BitVec n) :
    (~~~a &&& b)=b ^^^ (b &&& a) := by rw [BitVec.and_comm,mask_sub]

theorem project_gate (op : Kind) (a b : CoThetaBits.Wire) :
    project (CoThetaBits.gate op a b)=wordGate op (project a) (project b) := by
  cases op <;> simp only [project,CoThetaBits.gate,wordGate,meet,join,skip,mask_sub,mask_rev,
    BitVec.toNat_and,BitVec.toNat_or,BitVec.toNat_xor]

theorem project_cover (ws : List CoThetaBits.Wire) :
    cover (ws.map project)=(CoThetaBits.coverage ws).toNat := by
  induction ws with
  | nil => change 0=(0:CoThetaBits.Bits).toNat; simp
  | cons w ws ih => simp [cover_cons,project,sep,CoThetaBits.coverage,CoThetaBits.sep,ih]

theorem project_trim (xs : List CoThetaBits.Wire) (a b : CoThetaBits.Wire) :
    (CoThetaBits.trim a b xs).map project=restOf (xs.map project) (project a) (project b) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases e : x=a <;> by_cases h : x=b <;>
      simp [CoThetaBits.trim,restOf,e,h,project_eq] at * <;> exact ih

theorem project_edit (ws : List CoThetaBits.Wire) (a b : CoThetaBits.Wire) (op : Kind)
    (U : (CoThetaBits.Row→Bool)→Prop) :
    (CoThetaBits.gate op a b::(CoThetaBits.kept a b U++CoThetaBits.trim a b ws)).map project=
      extension (ws.map project) (project a) (project b) op
        (@decide _ (Classical.propDecidable (U (CoThetaBits.den a))))
        (@decide _ (Classical.propDecidable (U (CoThetaBits.den b)))) := by
  classical
  by_cases p : U (CoThetaBits.den a) <;> by_cases q : U (CoThetaBits.den b) <;>
    simp [CoThetaBits.kept,extension,keepList,p,q,project_gate,project_trim]

theorem pair_hit (k : Nat) (next : List Word→Bool) (ws : List Word) (a b : Word×Nat) (op : Kind)
    (h : tryField k next ws a b op=true) : pairTry k next ws a b=true := by
  cases op <;> simp [pairTry,h]

theorem pairs_hit {α} (test : α→α→Bool) {a b : α} {ws : List α}
    (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (go : test a b=true) (back : test b a=true) :
    pairs test ws=true := by
  classical
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    rw [pairs,Bool.or_eq_true]
    by_cases eq : a=w
    · subst w
      exact Or.inl (List.any_eq_true.mpr ⟨b,(List.mem_cons.mp hb).resolve_left ne.symm,go⟩)
    · by_cases e : b=w
      · subst w
        exact Or.inl (List.any_eq_true.mpr ⟨a,(List.mem_cons.mp ha).resolve_left ne,back⟩)
      · exact Or.inr (ih ((List.mem_cons.mp ha).resolve_left eq) ((List.mem_cons.mp hb).resolve_left e))

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Row Rep den gate full)

private theorem project_nodup {xs : List Wire} (h : xs.Nodup) : (xs.map project).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨no,rest⟩ := List.nodup_cons.mp h
    simp only [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih rest⟩
    intro h
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp h
    exact no (project_inj eq ▸ hb)

private theorem seen_iff {S ws} (rep : Rep ws S) (a : Wire) : a∈ws ↔ S (den a) := by
  constructor
  · exact fun ha => (rep _).2 ⟨a,ha,rfl⟩
  · intro h
    obtain ⟨b,hb,eq⟩ := (rep _).1 h
    exact CoThetaBits.den_injective eq ▸ hb

private theorem direction_hit {m k : Nat} {ws : List Wire} {x y : Wire} {U}
    (op : Kind) (nd : ws.Nodup) (hx : x∈ws) (hy : y∈ws) (ne : x≠y)
    (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (remaining : Live (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k)
    (old : CoThetaBits.coverage ws=full)
    (recur : ∀ zs, zs.Nodup → Rep zs (ins (den (gate op x y)) U) →
      guardedSearch k (zs.map project)=true) :
    pairTry k (guardedSearch k) (ws.map project)
      (project x,privateMask (ws.map project) (project x))
      (project y,privateMask (ws.map project) (project y))=true := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  have nz : wordGate op (project x) (project y)≠(0,0) := by
    rw [←project_gate]
    intro eq
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using eq
  have nf : wordGate op (project x) (project y)∉ws.map project := by
    rw [←project_gate]
    intro v
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp v
    exact fresh (project_inj eq ▸ hw)
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  have width := CoThetaBits.state_width remaining d ro
  have cov := CoThetaBits.live_coverage out remaining (fun w h => (ro w).1 h)
  apply pair_hit k _ _ _ _ op
  apply tryField_hit op ka kb _ (project_nodup nd) (List.mem_map_of_mem hx)
    (List.mem_map_of_mem hy) (fun eq => ne (project_inj eq)) nz nf
  · rw [←em,List.length_map]
    omega
  · rw [project_cover,old]
    rfl
  · rw [←em,project_cover,cov]
    rfl
  · rw [←em]
    exact recur out d ro

theorem guarded_complete {m S} (run : Live (den CoThetaBits.target) m S) :
    ∀ fuel, m≤fuel → ∀ ws, ws.Nodup → Rep ws S → guardedSearch fuel (ws.map project)=true := by
  classical
  induction run with
  | stop =>
    intro fuel _ ws _ rep
    have hit := List.mem_map_of_mem (f:=project) ((seen_iff rep CoThetaBits.target).2 rfl)
    cases fuel <;> simp [guardedSearch,target,hit]
  | @step m U a b kind ab ha hb fresh tail ih =>
    intro fuel bound ws nd rep
    cases fuel with
    | zero => omega
    | succ k =>
      obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
      obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
      subst a
      subst b
      let z := gate kind x y
      have e : den z=(fun i => applyKind kind (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
      have dist : x≠y := fun eq => ab (congrArg den eq)
      have rt : Live (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail
      have ng : den CoThetaBits.target≠absentBit := by
        intro h
        have bad := congrFun h (true,0)
        simp [CoThetaBits.den_target,absentBit] at bad
      have non : z≠CoThetaBits.zero := by
        intro eq
        have eq2 := (congrArg den eq).trans CoThetaBits.den_zero
        exact rt.excludes_zero ng (Or.inl eq2.symm)
      have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
      have current := Live.step kind ab ha hb fresh tail
      have fullWs := CoThetaBits.live_coverage ws current (fun w h => (rep w).1 h)
      have boundK : m≤k := by omega
      have recurse : ∀ ys, ys.Nodup → Rep ys (ins (den z) U) → guardedSearch k (ys.map project)=true := by
        intro ys h r
        rw [e] at r
        exact ih k boundK ys h r
      have forward := direction_hit kind nd hx hy dist non nf rep rt boundK fullWs recurse
      have swapped : gate (reflectOp kind) y x=z := by
        apply project_inj
        simp [z,project_gate,gate_swap]
      have revRep : Rep ws (ins (den y) (ins (den x) U)) := by
        intro w
        simpa [ins,or_left_comm] using rep w
      have reverse : pairTry k (guardedSearch k) (ws.map project)
          (project y,privateMask (ws.map project) (project y)) (project x,privateMask (ws.map project) (project x))=true := by
        apply direction_hit (reflectOp kind) nd hy hx dist.symm <;> try rw [swapped]
        · exact non
        · exact nf
        · exact revRep
        · exact rt
        · exact boundK
        · exact fullWs
        · exact recurse
      let natWs := ws.map project
      let points := natWs.map (fun v => (v,privateMask natWs v))
      have one : (project x,privateMask natWs (project x))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hx)
      have two : (project y,privateMask natWs (project y))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hy)
      have distinct : (project x,privateMask natWs (project x))≠(project y,privateMask natWs (project y)) :=
        fun eq => dist (project_inj (congrArg Prod.fst eq))
      have pass := pairs_hit (pairTry k (guardedSearch k) natWs) one two distinct forward reverse
      have size := CoThetaBits.state_width current nd rep
      have limit : ¬(ws.map project).length>k+2 := by simp only [List.length_map]; omega
      rw [guardedSearch,Bool.or_eq_true]
      right
      rw [guarded_eq,if_neg limit]
      exact pass

end CoNatBench
namespace CoThetaSix
open CoThetaBits
open CoNatBench
def cycle : List CoThetaBits.Wire := [(0x401f80fff40701fff,0x400f006ba486086a6),
(0x81e3f3070807ffe00,0x80a1a10608232d414),
(0x3067c0c180ff801fff,0x3027004100a3001958),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07800fe00ffffe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc05000ac005c4d0020),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000ffff00000000,0x590000f94410060040),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa675a4000820080180)]
theorem cycle_small : CoNatBench.guardedSearch 7 (cycle.map CoNatBench.project)=false := by decide +kernel
def cyclePrivate : List Nat := [3, 16, 1, 14, 33, 49]
def pendant : List CoThetaBits.Wire := [(0x118fc1cffbf0601ff,0x108780c5d1e420896),
(0x2071fe33847fffe00,0x2020d213003924c04),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc19e003c07807ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc118002806005b168),
(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01e007c007ff80000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff05c00580074602030),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007fff80000000,0x56400073a20080c040),
(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa99dd2000400010180)]
theorem pendant_small : CoNatBench.guardedSearch 7 (pendant.map CoNatBench.project)=false := by decide +kernel
def pendantPrivate : List Nat := [3, 12, 1, 20, 32, 48]
end CoThetaSix
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Row Rep den)

def essentialBasis (roots : List Wire) : Prop :=
  ∀ w∈roots, ∃ i : Fin CoThetaBits.Width, ∀ v∈roots,
    den v (true,i)≠den v (false,i) → v=w

theorem generic_rep {m S} {roots : List Wire} (live : Live (den CoThetaBits.target) m S)
    (onlyRaw : ∀ f, S f → f=absentBit ∨ ∃ w∈roots, den w=f)
    (required : essentialBasis roots) : Rep roots S := by
  have ng : den CoThetaBits.target≠absentBit := by
    intro e
    have no := congrFun e (true,0)
    simp [CoThetaBits.den_target,absentBit] at no
  intro f
  constructor
  · intro hf
    rcases onlyRaw f hf with z|h
    · exact (live.excludes_zero ng (z ▸ hf)).elim
    · exact h
  · rintro ⟨w,hw,eq⟩
    obtain ⟨i,key⟩ := required w hw
    have d : den CoThetaBits.target (true,i)≠den CoThetaBits.target (false,i) := by simp [CoThetaBits.den_target]
    obtain ⟨v,hv,diff⟩ := live.separates (true,i) (false,i) d
    rcases onlyRaw v hv with z|⟨u,hu,e⟩
    · subst v
      exact (diff rfl).elim
    · subst v
      obtain rfl := key u hu diff
      exact eq ▸ hv

theorem table_bound {roots : List Wire} (required : essentialBasis roots)
    (nd : roots.Nodup) {n ws} (run : Free (absentBit::roots.map den) n ws)
    (goal : den CoThetaBits.target∈ws) {cap : Nat} (cert : guardedSearch cap (roots.map project)=false) : cap<n := by
  obtain ⟨k,S,le,live,sub⟩ := rewind run List.mem_cons_self
    (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ goal)
  apply Classical.byContradiction
  intro bad
  apply Bool.false_ne_true
  rw [←cert]
  apply guarded_complete live cap (by omega) roots nd
  apply generic_rep live _ required
  intro f h
  rcases List.mem_cons.mp (sub f h) with z|raw
  · exact Or.inl z
  · exact Or.inr (List.mem_map.mp raw)

end CoNatBench

namespace CoThetaSix
open CoThetaFreeCore
open CoThetaBits (Wire Row den)

def basisAt (ws : List Wire) (ids : List Nat) : Bool :=
  (List.range ws.length).all fun a =>
    let i := (ids.getD a 0) % CoThetaBits.Width
    ws.all fun v =>
      let want := ws.getD a CoThetaBits.zero
      (den v (true,⟨i,Nat.mod_lt _ (by decide)⟩) == den v (false,⟨i,Nat.mod_lt _ (by decide)⟩)) || v==want

theorem basisAt_sound (ws : List Wire) (ids : List Nat) (cert : basisAt ws ids=true) :
    CoNatBench.essentialBasis ws := by
  intro w hw
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp hw
  let i := (ids.getD k 0) % CoThetaBits.Width
  refine ⟨⟨i,Nat.mod_lt _ (by decide)⟩,?_⟩
  intro v hv ne
  have each := List.all_eq_true.mp cert k (List.mem_range.mpr hk)
  have hit := List.all_eq_true.mp each v hv
  simp only [Bool.or_eq_true,beq_iff_eq] at hit
  have vwant := hit.resolve_left ne
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,eq] using vwant

theorem cycle_basis : CoNatBench.essentialBasis cycle := basisAt_sound cycle cyclePrivate (by decide +kernel)
theorem pendant_basis : CoNatBench.essentialBasis pendant := basisAt_sound pendant pendantPrivate (by decide +kernel)
theorem cycle_nd : cycle.Nodup := by decide +kernel
theorem pendant_nd : pendant.Nodup := by decide +kernel

end CoThetaSix
namespace CoThetaSix
open CoThetaFreeCore
open CoThetaBits (Wire Row den gate)
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack numeric_goal)

def rootsFor (gone : Fin 7) := if gone=2 then cycle else pendant

def indexAt (gone vertex : Fin 7) : Option Nat :=
  match gone.val,vertex.val with
  | 2,0 => some 0
  | 2,1 => some 1
  | 2,3 => some 2
  | 2,4 => some 3
  | 2,5 => some 4
  | 2,6 => some 5
  | 3,0 => some 0
  | 3,1 => some 1
  | 3,2 => some 2
  | 3,4 => some 3
  | 3,5 => some 4
  | 3,6 => some 5
  | 4,1 => some 0
  | 4,0 => some 1
  | 4,2 => some 2
  | 4,3 => some 3
  | 4,6 => some 4
  | 4,5 => some 5
  | 5,0 => some 0
  | 5,1 => some 1
  | 5,2 => some 2
  | 5,6 => some 3
  | 5,3 => some 4
  | 5,4 => some 5
  | 6,1 => some 0
  | 6,0 => some 1
  | 6,2 => some 2
  | 6,5 => some 3
  | 6,4 => some 4
  | 6,3 => some 5
  | _,_ => none

def minorCol (gone vertex : Fin 7) : Wire :=
  match indexAt gone vertex with
  | none => CoThetaBits.zero
  | some n => (rootsFor gone).getD n CoThetaBits.zero

def minorLift (g : Fin 7) (r : Row) : SmallInput := pack (fun j => den (minorCol g j) r)
def minorGraph (g : Fin 7) : Wire :=
  gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj
    (gate .conj (minorCol g 0) (minorCol g 2)) (gate .conj (minorCol g 1) (minorCol g 2)))
    (gate .conj (minorCol g 0) (minorCol g 3))) (gate .conj (minorCol g 3) (minorCol g 4)))
    (gate .conj (minorCol g 1) (minorCol g 4))) (gate .conj (minorCol g 0) (minorCol g 5)))
    (gate .conj (minorCol g 5) (minorCol g 6))) (gate .conj (minorCol g 1) (minorCol g 6))

theorem minor_table : ∀ g : Fin 7, 2≤g.val → minorGraph g=CoThetaBits.target ∧
    minorCol g g=CoThetaBits.zero := by decide +kernel

theorem minor_input (g j : Fin 7) :
    restrict (minorLift g) (raw7 j)=den (minorCol g j) :=
  funext (fun r => unpack (fun v => den (minorCol g v) r) j)

theorem minor_goal {g : Fin 7} (small : 2≤g.val) :
    restrict (minorLift g) ans7=den CoThetaBits.target := by
  have graph := congrArg den (minor_table g small).1
  funext r
  change ans7 (minorLift g r)=_
  rw [numeric_goal]
  have values : (fun j => raw7 j (minorLift g r))=(fun j => den (minorCol g j) r) :=
    funext (fun j => congrFun (minor_input g j) r)
  rw [values]
  have equality := congrFun graph r
  simp only [minorGraph,CoThetaBits.den_gate,applyKind] at equality
  exact equality

theorem minor_off {g : Fin 7} (small : 2≤g.val) :
    restrict (minorLift g) (raw7 g)=absentBit :=
  (minor_input g g).trans ((congrArg den (minor_table g small).2).trans CoThetaBits.den_zero)

theorem minor_known (g : Fin 7) : ∀ w∈vertices7,
    restrict (minorLift g) w∈absentBit::(rootsFor g).map den := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨j,e⟩ := List.mem_ofFn.mp r
    subst w
    rw [minor_input]
    cases h : indexAt g j with
    | none => simp [minorCol,h,CoThetaBits.den_zero]
    | some n =>
      cases hn : (rootsFor g)[n]? with
      | none => simp [minorCol,h,List.getD_eq_getElem?_getD,hn,CoThetaBits.den_zero]
      | some v =>
        have inList := List.mem_map_of_mem (f:=den) (List.mem_of_getElem? hn)
        simp [minorCol,h,List.getD_eq_getElem?_getD,hn,inList]

theorem minor_lower {g : Fin 7} (small : 2≤g.val) {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 gs) : 8≤remaining (minorLift g) gs := by
  let roots := rootsFor g
  obtain ⟨ws,run,all⟩ := restrict_trace (minorLift g) gs ok.1
    (Free.start (raw:=absentBit::roots.map den)) List.mem_cons_self (minor_known g)
  have h := all ans7 ok.2
  rw [minor_goal small] at h
  have yes : 7<0+remaining (minorLift g) gs := by
    by_cases e : g=2
    · exact CoNatBench.table_bound (roots:=roots) (by simpa [roots,rootsFor,e] using cycle_basis)
        (by simpa [roots,rootsFor,e] using cycle_nd) run h (by simpa [roots,rootsFor,e] using cycle_small)
    · exact CoNatBench.table_bound (roots:=roots) (by simpa [roots,rootsFor,e] using pendant_basis)
        (by simpa [roots,rootsFor,e] using pendant_nd) run h (by simpa [roots,rootsFor,e] using pendant_small)
  omega

end CoThetaSix
namespace CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

noncomputable def readerSet {ρ : Type} (gs : List (TraceGate ρ)) (p : ρ → Bool) :
    Finset (TraceGate ρ) := by classical exact gs.toFinset.filter (fun g => reads g p)

theorem mem_readerSet {ρ : Type} {gs : List (TraceGate ρ)} {p : ρ → Bool}
    {g : TraceGate ρ} : g ∈ readerSet gs p ↔ g ∈ gs ∧ reads g p := by
  classical
  simp [readerSet]

 

inductive UsePath {ρ : Type} (gs : List (TraceGate ρ)) :
    (ρ → Bool) → (ρ → Bool) → Prop
  | stop {w} : UsePath gs w w
  | through {w out} (g : TraceGate ρ) (mem : g ∈ gs) (input : reads g w)
      (rest : UsePath gs g.value out) : UsePath gs w out

private theorem two_reads_zero {ρ σ : Type} (lift : σ → ρ)
    {g : TraceGate ρ} {w p : ρ → Bool} (ne : w ≠ p) (hw : reads g w) (hp : reads g p)
    (zw : restrict lift w = absentBit) (zp : restrict lift p = absentBit) :
    restrict lift g.value = absentBit := by
  apply two_zero_propagate
  · rcases hw with h|h <;> rcases hp with h'|h'
    · exact (ne (h.symm.trans h')).elim
    · exact (congrArg (restrict lift) h).trans zw
    · exact (congrArg (restrict lift) h').trans zp
    · exact (ne (h.symm.trans h')).elim
  · rcases hw with h|h <;> rcases hp with h'|h'
    · exact (ne (h.symm.trans h')).elim
    · exact (congrArg (restrict lift) h').trans zp
    · exact (congrArg (restrict lift) h).trans zw
    · exact (ne (h.symm.trans h')).elim

 



theorem extra_loss_on_path {ρ σ : Type} (lift : σ → ρ) {gs : List (TraceGate ρ)}
    {p q z out : ρ → Bool} (zp : restrict lift p = absentBit) (zq : restrict lift q = absentBit)
    (aliasFree : ∀ g ∈ gs, g.value ≠ p ∧ g.value ≠ q)
    (path : UsePath gs z out) (zz : restrict lift z = absentBit)
    (distinct : z ≠ p ∧ z ≠ q) (ends : restrict lift out ≠ absentBit) :
    ∃ g ∈ gs, ¬reads g p ∧ ¬reads g q ∧ disappears lift g := by
  induction path with
  | stop => exact (ends zz).elim
  | @through w out g hg hw more ih =>
    by_cases hp : reads g p
    · exact ih (two_reads_zero lift distinct.1 hw hp zz zp) (aliasFree g hg) ends
    by_cases hq : reads g q
    · exact ih (two_reads_zero lift distinct.2 hw hq zz zq) (aliasFree g hg) ends
    exact ⟨g,hg,hp,hq,reading_zero_disappears lift zz hw⟩

private noncomputable def lostList {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ)) :
    List (TraceGate ρ) := by classical exact gs.filter (fun g => decide (disappears lift g))

private theorem lost_length {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ)) :
    (lostList lift gs).length = saved lift gs := by
  classical
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : disappears lift g <;> simp [lostList,saved,h,lostList] at ih ⊢ <;> omega

theorem four_saved_raw_head {ρ σ : Type} (lift : σ → ρ) (gs : List (TraceGate ρ))
    (p q : ρ → Bool) (zp : restrict lift p = absentBit) (zq : restrict lift q = absentBit)
    (three : 3 ≤ (readerSet gs p ∪ readerSet gs q).card)
    (extra : ∃ g ∈ gs, ¬reads g p ∧ ¬reads g q ∧ disappears lift g) :
    4 ≤ saved lift gs := by
  classical
  obtain ⟨g,hg,hp,hq,hd⟩ := extra
  let A := readerSet gs p ∪ readerSet gs q
  have hout : g ∉ A := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · exact hp (mem_readerSet.mp h).2
    · exact hq (mem_readerSet.mp h).2
  have sub : insert g A ⊆ (lostList lift gs).toFinset := by
    intro v hv
    have hv' : v∈gs ∧ disappears lift v := by
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact ⟨hg,hd⟩
      · rcases Finset.mem_union.mp hv with h|h
        · obtain ⟨hm,hr⟩ := mem_readerSet.mp h
          exact ⟨hm,reading_zero_disappears lift zp hr⟩
        · obtain ⟨hm,hr⟩ := mem_readerSet.mp h
          exact ⟨hm,reading_zero_disappears lift zq hr⟩
    simpa [lostList] using hv'
  have bound := (Finset.card_le_card sub).trans (List.toFinset_card_le _)
  rw [Finset.card_insert_of_notMem hout,lost_length] at bound
  change 3 ≤ A.card at three
  omega

end CoThetaFreeCore
namespace CoThetaFreeCore

theorem UsePath.trans {ρ : Type} {chain : List (TraceGate ρ)} {a b c : ρ → Bool}
    (first : UsePath chain a b) (last : UsePath chain b c) : UsePath chain a c := by
  induction first with
  | stop => exact last
  | through g hg hr _ ih => exact .through g hg hr (ih last)

 

theorem omit_path_scan {ρ : Type} (chain : List (TraceGate ρ)) (z : ρ → Bool)
    (gs : List (TraceGate ρ)) (sub : ∀ g∈gs, g∈chain)
    {raw start pool : List (ρ → Bool)} {b : Nat}
    (reg : registered start gs) (pre : Free raw b pool)
    (known : ∀ w∈start, ¬UsePath chain z w → w∈pool) :
    ∃ j ys, j ≤ b+gs.length ∧ Free raw j ys ∧
      ∀ w∈traceWires start gs, ¬UsePath chain z w → w∈ys := by
  induction gs generalizing start pool b with
  | nil => exact ⟨b,pool,by simp,pre,known⟩
  | cons g gs ih =>
    obtain ⟨hl,hr,rest⟩ := reg
    have hg := sub g List.mem_cons_self
    have tail (v) (hv : v∈gs) := sub v (List.mem_cons_of_mem _ hv)
    by_cases path : UsePath chain z g.value
    · have carry : ∀ w∈g.value::start, ¬UsePath chain z w → w∈pool := by
        intro w hw hn
        rcases List.mem_cons.mp hw with rfl|hw
        · exact (hn path).elim
        · exact known _ hw hn
      obtain ⟨j,ys,hj,run,avail⟩ := ih tail rest pre carry
      exact ⟨j,ys,by simp; omega,run,avail⟩
    · have pl : ¬UsePath chain z g.left := fun p =>
        path (p.trans (.through g hg (Or.inl rfl) .stop))
      have pr : ¬UsePath chain z g.right := fun p =>
        path (p.trans (.through g hg (Or.inr rfl) .stop))
      have next : Free raw (b+1) (g.value::pool) :=
        .binary pre g.kind (known _ hl pl) (known _ hr pr)
      have carry : ∀ w∈g.value::start, ¬UsePath chain z w → w∈g.value::pool := by
        intro w hw hn
        rcases List.mem_cons.mp hw with rfl|hw
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (known _ hw hn)
      obtain ⟨j,ys,hj,run,avail⟩ := ih tail rest next carry
      exact ⟨j,ys,by simp; omega,run,avail⟩

theorem omit_dead_head {ρ : Type} (raw : List (ρ → Bool))
    (gs : List (TraceGate ρ)) (z target : ρ → Bool)
    (reg : registered (z::raw) gs) (out : target∈traceWires (z::raw) gs)
    (dead : ¬UsePath gs z target) :
    ∃ j ys, j ≤ gs.length ∧ Free raw j ys ∧ target∈ys := by
  have known (w) (hw : w∈z::raw) (hn : ¬UsePath gs z w) : w∈raw := by
    rcases List.mem_cons.mp hw with rfl|hw
    · exact (hn .stop).elim
    · exact hw
  obtain ⟨j,ys,hj,run,avail⟩ := omit_path_scan gs z gs (fun _ h => h) reg (Free.start (raw:=raw)) known
  exact ⟨j,ys,by simpa using hj,run,avail _ out dead⟩

end CoThetaFreeCore

namespace CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

end CoThetaFreeCore
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack)
open CoThetaSix (minorLift minor_off minor_goal minor_lower)

def smallRow (n : Nat) : SmallInput := ⟨n % 128,Nat.mod_lt _ (by decide)⟩
def sensSeeds : List Nat :=
  [0, 0, 4, 10, 8, 4, 4, 8, 4, 20, 4, 32, 4, 68, 4, 17, 0, 0, 16, 4, 4, 12, 4, 16, 4, 36, 4, 64, 2, 1, 1, 2, 0, 0, 1, 10, 1, 17, 1, 34, 1, 65, 16, 1, 1, 3, 1, 20, 0, 0, 1, 16, 1, 48, 1, 65, 2, 3, 8, 2, 2, 12, 2, 8, 0, 0, 2, 34, 2, 72, 64, 1, 1, 3, 1, 68, 1, 72, 1, 17, 0, 0, 1, 64, 2, 3, 32, 2, 2, 36, 2, 10, 2, 48, 2, 32, 0, 0]

def loRow (x y : Fin 7) (b : Bool) := smallRow (sensSeeds.getD (2*(7*x.val+y.val)+b.toNat) 0)
def hiRow (x y : Fin 7) (b : Bool) := smallRow ((loRow x y b).val ||| (1 <<< x.val))
theorem seven_sensitivity : ∀ (x y : Fin 7), x≠y → ∀ b : Bool,
    raw7 x (loRow x y b)=false ∧ raw7 x (hiRow x y b)=true ∧
    raw7 y (loRow x y b)=b ∧ raw7 y (hiRow x y b)=b ∧
    ans7 (loRow x y b)≠ans7 (hiRow x y b) ∧
    ∀ z : Fin 7, z≠x → raw7 z (loRow x y b)=raw7 z (hiRow x y b) := by decide +kernel

theorem seven_diff : ∀ (x y : Fin 7), x≠y → ∃ r : SmallInput, raw7 x r≠raw7 y r := by
  have table : ∀ p q : Fin 7, p≠q → raw7 p (smallRow (1 <<< p.val))≠raw7 q (smallRow (1 <<< p.val)) := by decide +kernel
  exact fun p q pq => ⟨_,table p q pq⟩
theorem seven_not_raw : ∀ x : Fin 7, ∃ r : SmallInput, ans7 r≠raw7 x r := by
  have table : ∀ p : Fin 7, ans7 (smallRow (1 <<< p.val))≠raw7 p (smallRow (1 <<< p.val)) := by decide +kernel
  exact fun p => ⟨_,table p⟩

theorem raw_mem (x : Fin 7) : raw7 x∈vertices7 := List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨x,rfl⟩)

theorem read_twice (x y : Fin 7) (xy : x≠y) (g : TraceGate SmallInput)
    (gx : reads g (raw7 x)) (gy : reads g (raw7 y)) {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 gs) : ∃ t∈gs, reads t (raw7 x) ∧ t≠g := by
  obtain ⟨r,ne⟩ := seven_diff x y xy
  have diff : raw7 x≠raw7 y := fun h => ne (congrFun h r)
  obtain ⟨sw,code⟩ := joint_reader_code _ _ diff g gx gy
  obtain ⟨b,mask⟩ := CoThetaNine.masks_some_value g.kind sw
  obtain ⟨lx,hx,ly,hy,out,fixed⟩ := seven_sensitivity x y xy b
  obtain ⟨r,notSame⟩ := seven_not_raw x
  apply second_reader (raw7 x) (loRow x y b) (hiRow x y b) g ok.1 _ ok.2
    (fun eq => notSame (congrFun eq r)) out
  · simpa only [code,lx,hx,ly,hy] using mask false true
  · intro w hw no
    rcases List.mem_cons.mp hw with e|h
    · subst w
      rfl
    · obtain ⟨i,e⟩ := List.mem_ofFn.mp h
      subst w
      exact fixed i (fun e => no (congrArg raw7 e))

theorem three_losses {ρ σ : Type} (lift : σ→ρ) (gs : List (TraceGate ρ)) {a b c : TraceGate ρ}
    (ha : a∈gs) (hb : b∈gs) (hc : c∈gs) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (da : disappears lift a) (db : disappears lift b) (dc : disappears lift c) :
    3≤ saved lift gs := by
  classical
  have nd : [a,b,c].Nodup := by simp [ab,ac,bc]
  rw [saved_eq_length]
  apply length_of_cover [a,b,c] _ nd
  intro w h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with e|e|e <;> subst w <;> simp [vanishing,ha,hb,hc,da,db,dc]

theorem absorbing_head {g : TraceGate SmallInput} {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (g::gs)) (fresh : freshTrace vertices7 (g::gs))
    (budget : (g::gs).length≤10) {x y : Fin 7} (xy : x≠y)
    (rx : reads g (raw7 x)) (ry : reads g (raw7 y)) (nonhub : 2≤x.val)
    (zero : restrict (minorLift x) g.value=absentBit) :
    ∃ n ws, n≤gs.length ∧ Free vertices7 n ws ∧ ans7∈ws := by
  classical
  by_cases path : UsePath gs g.value ans7
  · exfalso
    have off := minor_off nonhub
    have fin : restrict (minorLift x) ans7≠absentBit := by
      rw [minor_goal nonhub]
      intro e
      have no := congrFun e (true,0)
      simp [CoThetaBits.den_target,absentBit] at no
    have distinct {t : TraceGate SmallInput} (ht : t∈g::gs) : t.value≠raw7 x :=
      fun e => fresh_outputs fresh _ ht (e ▸ raw_mem x)
    have headNe := distinct (List.mem_cons_self (a:=g) (l:=gs))
    obtain ⟨b,hb,rb,bg⟩ := read_twice x y xy g rx ry ok
    obtain ⟨c,hc,nr,_,gone⟩ := extra_loss_on_path (minorLift x) off off
      (fun t ht => ⟨distinct (List.mem_cons_of_mem _ ht),distinct (List.mem_cons_of_mem _ ht)⟩)
      path zero ⟨headNe,headNe⟩ fin
    have gain := three_losses (minorLift x) (g::gs) List.mem_cons_self hb
      (List.mem_cons_of_mem _ hc) (Ne.symm bg) (fun e => nr (e ▸ rx)) (fun e => nr (e ▸ rb))
      (reading_zero_disappears _ off rx) (reading_zero_disappears _ off rb) gone
    have lo := minor_lower nonhub ok
    have tot := accounted (minorLift x) (g::gs)
    omega
  · exact omit_dead_head vertices7 gs g.value ans7 ok.1.2.2 ok.2 path

end CoThetaSeven
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack)
open CoThetaSix (minorLift minor_off)
def opIndex : Kind→Nat
  | .conj => 0 | .disj => 1 | .leftOnly => 2 | .rightOnly => 3
def opAt (n : Nat) : Kind := match n with
  | 0 => .conj | 1 => .disj | 2 => .leftOnly | _ => .rightOnly
def allPerms : List (List (Fin 7)) := [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 5, 6, 3, 4], [1, 0, 2, 4, 3, 6, 5], [1, 0, 2, 6, 5, 4, 3]]
def casesA : List (Fin 7) := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 3, 3, 3]
def casesB : List (Fin 7) := [1, 1, 1, 2, 2, 3, 3, 4, 4, 3, 4, 5, 6]
def casesOp : List Nat := [0, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1]
def tags : List Nat := [0, 0, 0, 0, 2, 6, 10, 12, 1, 14, 18, 1, 1, 22, 26, 1, 1, 30, 34, 1, 1, 23, 27, 1, 1, 31, 35, 1, 2, 6, 12, 10, 0, 0, 0, 0, 1, 16, 20, 1, 1, 32, 36, 1, 1, 24, 28, 1, 1, 33, 37, 1, 1, 25, 29, 1, 0, 14, 0, 18, 0, 16, 0, 20, 0, 0, 0, 0, 0, 38, 0, 1, 0, 40, 0, 1, 0, 39, 0, 1, 0, 41, 0, 1, 0, 22, 0, 26, 0, 32, 0, 36, 0, 38, 0, 1, 0, 0, 0, 0, 0, 42, 0, 1, 0, 46, 0, 1, 0, 50, 0, 1, 0, 30, 0, 34, 0, 24, 0, 28, 0, 40, 0, 1, 0, 42, 0, 1, 0, 0, 0, 0, 0, 51, 0, 1, 0, 48, 0, 1, 0, 23, 0, 27, 0, 33, 0, 37, 0, 39, 0, 1, 0, 46, 0, 1, 0, 51, 0, 1, 0, 0, 0, 0, 0, 43, 0, 1, 0, 31, 0, 35, 0, 25, 0, 29, 0, 41, 0, 1, 0, 50, 0, 1, 0, 48, 0, 1, 0, 43, 0, 1, 0, 0, 0, 0]
def numbered (i : Fin 13) : TraceGate SmallInput :=
  ⟨opAt (casesOp.getD i.val 0),raw7 (casesA.getD i.val 0),raw7 (casesB.getD i.val 0)⟩
def position (s : Fin 4) (j : Fin 7) := (allPerms.getD s.val []).getD j.val 0
def rowPerm (s : Fin 4) (r : SmallInput) := pack (fun j => raw7 (position s j) r)
def tag (x y : Fin 7) (op : Kind) := tags.getD (4*(7*x.val+y.val)+opIndex op) 0
def picked (n : Nat) : Fin 13 := ⟨((n-2)/4) % 13,Nat.mod_lt _ (by decide)⟩
def rotation (n : Nat) : Fin 4 := ⟨(n-2) % 4,Nat.mod_lt _ (by decide)⟩

theorem perm_graph : ∀ (s : Fin 4) (r : SmallInput), ans7 (rowPerm s r)=ans7 r := by decide +kernel

theorem raw_permute (s : Fin 4) (j : Fin 7) :
    restrict (rowPerm s) (raw7 j)=raw7 (position s j) :=
  funext (fun r => unpack (fun k => raw7 (position s k) r) j)

theorem dispatch_rules (op : Kind) : ∀ x y : Fin 7, x≠y →
    let n := tag x y op
    if n=0 then 2≤x.val ∧ ∀ b : Bool, applyKind op false b=false else
    if n=1 then 2≤y.val ∧ ∀ a : Bool, applyKind op a false=false else
    ∀r : SmallInput, applyKind op (raw7 x (rowPerm (rotation n) r)) (raw7 y (rowPerm (rotation n) r)) =
      (numbered (picked n)).value r := by
  cases op <;> decide +kernel

def Selected : Prop := (∃ n ws, n≤9 ∧ Free vertices7 n ws ∧ ans7∈ws) ∨
  ∃ i : Fin 13, ∃ n ws, n≤9 ∧ Free ((numbered i).value::vertices7) n ws ∧ ans7∈ws

theorem dispatch_head {g : TraceGate SmallInput} {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (g::gs)) (fresh : freshTrace vertices7 (g::gs))
    (size : (g::gs).length≤10) : Selected := by
  classical
  obtain ⟨nL,nR,separate⟩ := fresh_ports g ok.1.1 ok.1.2.1 List.mem_cons_self fresh.1
  obtain ⟨x,ex⟩ := List.mem_ofFn.mp ((List.mem_cons.mp ok.1.1).resolve_left nL)
  obtain ⟨y,ey⟩ := List.mem_ofFn.mp ((List.mem_cons.mp ok.1.2.1).resolve_left nR)
  have xy : x≠y := fun e => separate (ex.symm.trans ((congrArg raw7 e).trans ey))
  have rx : reads g (raw7 x) := Or.inl ex.symm
  have ry : reads g (raw7 y) := Or.inr ey.symm
  let t := tag x y g.kind
  have rule := dispatch_rules g.kind x y xy
  change (if t=0 then _ else if t=1 then _ else _) at rule
  have n : gs.length≤9 := by simp only [List.length_cons] at size; omega
  by_cases a : t=0
  · rw [if_pos a] at rule
    have drop : restrict (minorLift x) g.value=absentBit := by
      funext r
      change applyKind g.kind (g.left (minorLift x r)) (g.right (minorLift x r))=false
      rw [←ex,←ey]
      have zero := congrFun (minor_off rule.1) r
      change raw7 x (minorLift x r)=false at zero
      rw [zero]
      exact rule.2 _
    obtain ⟨k,ws,h,run,out⟩ := absorbing_head ok fresh size xy rx ry rule.1 drop
    exact Or.inl ⟨k,ws,Nat.le_trans h n,run,out⟩
  · rw [if_neg a] at rule
    by_cases b : t=1
    · rw [if_pos b] at rule
      have drop : restrict (minorLift y) g.value=absentBit := by
        funext r
        change applyKind g.kind (g.left (minorLift y r)) (g.right (minorLift y r))=false
        rw [←ex,←ey]
        have zero := congrFun (minor_off rule.1) r
        change raw7 y (minorLift y r)=false at zero
        rw [zero]
        exact rule.2 _
      obtain ⟨k,ws,h,run,out⟩ := absorbing_head ok fresh size (Ne.symm xy) ry rx rule.1 drop
      exact Or.inl ⟨k,ws,Nat.le_trans h n,run,out⟩
    · rw [if_neg b] at rule
      let s := rotation t
      let i := picked t
      let pool := (numbered i).value::vertices7
      have eq : restrict (rowPerm s) g.value=(numbered i).value := by
        funext r
        change applyKind g.kind (g.left (rowPerm s r)) (g.right (rowPerm s r))=_
        rw [←ex,←ey]
        exact rule r
      have old : ∀ w∈g.value::vertices7, restrict (rowPerm s) w∈pool := by
        intro w hw
        rcases List.mem_cons.mp hw with z|h
        · subst w
          rw [eq]
          exact List.mem_cons_self
        rcases List.mem_cons.mp h with z|other
        · subst w
          exact List.mem_cons_of_mem _ List.mem_cons_self
        · obtain ⟨j,hj⟩ := List.mem_ofFn.mp other
          subst w
          rw [raw_permute]
          exact List.mem_cons_of_mem _ (raw_mem _)
      obtain ⟨ws,run,sub⟩ := restrict_trace (rowPerm s) gs ok.1.2.2 (Free.start (raw:=pool))
        (List.mem_cons_of_mem _ List.mem_cons_self) old
      have goal := sub ans7 ok.2
      have unchanged : restrict (rowPerm s) ans7=ans7 := funext (perm_graph s)
      rw [unchanged] at goal
      have account := accounted (rowPerm s) gs
      exact Or.inr ⟨i,_,ws,by omega,run,goal⟩

theorem select_program {n ws} (run : Free vertices7 n ws) (small : n≤10) (hit : ans7∈ws) :
    Selected := by
  obtain ⟨ts,len,well,eq⟩ := trace_of_free run
  obtain ⟨clean,solves,fresh,le,_⟩ := simplify_trace ts ⟨well,eq ▸ hit⟩
  cases clean with
  | nil =>
    have h : ans7∈vertices7 := solves.2
    rcases List.mem_cons.mp h with z|r
    · have test : ans7 (smallRow 5)=true := by decide
      exact Bool.noConfusion (test.symm.trans (congrFun z (smallRow 5)))
    · obtain ⟨i,e⟩ := List.mem_ofFn.mp r
      obtain ⟨s,d⟩ := seven_not_raw i
      exact (d (congrFun e.symm s)).elim
  | cons g gs => exact dispatch_head solves fresh (by omega)

end CoThetaSeven
namespace CoNatBench

def firstPairs : List (Nat×Nat) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)]
def secondPairs : List (Nat×Nat) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

def rootWords : List Word := CoThetaBits.raw.map project
def nth (ws : List Word) (i : Nat) := ws.getD i (0,0)
def kinds (i : Nat) (x y : Word) : Word :=
  match i with | 0 => meet x y | 1 => join x y | 2 => skip x y | _ => skip y x



def firstWords (index : Nat) : List Word :=
  let pair := firstPairs[index/4]?.getD (0,1)
  let a := nth rootWords pair.1
  let b := nth rootWords pair.2
  let z := kinds (index % 4) a b
  z::a::b::(rootWords.filter (fun w => w != a && w != b))

end CoNatBench
namespace CoThetaSeven
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack toRows numeric_target)
open CoThetaBits (Row Wire den col Rep)

def numbers : List Nat := [0,1,2,5,6,9,10,13,14,45,61,65,69]
def numberedWord (i : Fin 13) :=
  CoThetaBits.gate (numbered i).kind (col (casesA.getD i.val 0)) (col (casesB.getD i.val 0))

def postPool (i : Fin 13) :=
  let a := col (casesA.getD i.val 0)
  let b := col (casesB.getD i.val 0)
  numberedWord i::a::b::CoThetaBits.trim a b CoThetaBits.raw

theorem post_data : ∀ i : Fin 13,
    (postPool i).Nodup ∧ ((postPool i).map CoNatBench.project)=CoNatBench.firstWords (numbers.getD i.val 0) ∧
    ((postPool i).Perm (numberedWord i::CoThetaBits.raw)) ∧
    ∀ j : Fin 7, CoThetaBits.coverage ((postPool i).filter fun v => v != col j)≠CoThetaBits.full := by
  decide +kernel

theorem proj_raw (j : Fin 7) : restrict toRows (raw7 j)=den (col j) :=
  funext (fun r => unpack (CoThetaBits.sample r) j)

theorem proj_head (i : Fin 13) : restrict toRows (numbered i).value=den (numberedWord i) := by
  rw [numberedWord,CoThetaBits.den_gate]
  funext r
  change applyKind (numbered i).kind (raw7 (casesA.getD i.val 0) (toRows r))
    (raw7 (casesB.getD i.val 0) (toRows r))=_
  change applyKind _ (raw7 _ (pack (CoThetaBits.sample r))) (raw7 _ (pack (CoThetaBits.sample r)))=_
  rw [unpack,unpack]
  rfl

theorem collect_init (i : Fin 13) {f : Row→Bool}
    (hf : f∈((numbered i).value::vertices7).map (restrict toRows)) :
    f=absentBit ∨ ∃ w∈postPool i, den w=f := by
  obtain ⟨v,hv,eq⟩ := List.mem_map.mp hf
  subst f
  have perm := (post_data i).2.2.1
  rcases List.mem_cons.mp hv with h|rest
  · subst v
    exact Or.inr ⟨_,perm.mem_iff.mpr List.mem_cons_self,(proj_head i).symm⟩
  rcases List.mem_cons.mp rest with h|final
  · subst v
    exact Or.inl rfl
  · obtain ⟨j,h⟩ := List.mem_ofFn.mp final
    subst v
    have mem : col j∈CoThetaBits.raw := by
      rw [←CoThetaBits.raw_is_ofFn]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
    exact Or.inr ⟨_,perm.mem_iff.mpr (List.mem_cons_of_mem _ mem),(proj_raw j).symm⟩

theorem classify_pool (i : Fin 13) {k S} (live : Live (den CoThetaBits.target) k S)
    (sub : ∀ f, S f → f=absentBit ∨ ∃w∈postPool i,den w=f) :
    Rep CoThetaBits.raw S ∨ Rep (postPool i) S := by
  classical
  have ng : den CoThetaBits.target≠absentBit := by
    intro bad
    have no := congrFun bad (true,0)
    simp [CoThetaBits.den_target,absentBit] at no
  have present (f) (h : S f) : ∃w∈postPool i,den w=f := by
    rcases sub f h with z|p
    · exact (live.excludes_zero ng (z ▸ h)).elim
    · exact p
  have core (j : Fin 7) : S (den (col j)) := by
    apply Classical.byContradiction
    intro missing
    apply (post_data i).2.2.2 j
    apply CoThetaBits.live_coverage _ live
    intro f hf
    obtain ⟨w,hw,eq⟩ := present f hf
    have ne : w≠col j := by
      intro same
      exact missing (same ▸ (eq ▸ hf))
    exact ⟨w,List.mem_filter.mpr ⟨hw,by simp [ne]⟩,eq⟩
  have raw_has {w : Wire} (hw : w∈CoThetaBits.raw) : S (den w) := by
    obtain ⟨j,e⟩ := CoThetaBits.indexed hw
    exact e ▸ core j
  have perm := (post_data i).2.2.1
  by_cases hit : S (den (numberedWord i))
  · right
    intro f
    refine ⟨present f,?_⟩
    rintro ⟨w,hw,eq⟩
    rcases List.mem_cons.mp (perm.mem_iff.mp hw) with z|r
    · subst w
      exact eq ▸ hit
    · exact eq ▸ raw_has r
  · left
    intro f
    constructor
    · intro hf
      obtain ⟨w,m,eq⟩ := present f hf
      rcases List.mem_cons.mp (perm.mem_iff.mp m) with e|r
      · subst w
        exact (hit (eq ▸ hf)).elim
      · exact ⟨w,r,eq⟩
    · rintro ⟨w,hw,eq⟩
      exact eq ▸ raw_has hw

def RawNine : Prop := ∀ {m S}, Live (den CoThetaBits.target) m S → m≤9 → Rep CoThetaBits.raw S → False
end CoThetaSeven
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Rep den gate)

def Supported (k : Nat) (ws : List Word) (a b : Word) (op : Kind) (ka kb : Bool) : Prop :=
  let z := wordGate op a b
  let out := extension ws a b op ka kb
  z≠(0,0) ∧ z∉ws ∧ out.length≤k+1 ∧ cover out=all ∧ guardedSearch k out=true

private theorem support_from {m k} {ws : List Wire} {x y : Wire} {U} (op : Kind)
    (nd : ws.Nodup) (ne : x≠y) (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (tail : Live (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k) :
    ∃ ka kb : Bool, Supported k (ws.map project) (project x) (project y) op ka kb := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  refine ⟨ka,kb,?_,?_,?_,?_,?_⟩
  · rw [←project_gate]
    intro e
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using e
  · rw [←project_gate]
    intro h
    obtain ⟨v,hv,e⟩ := List.mem_map.mp h
    exact fresh (project_inj e ▸ hv)
  · rw [←em,List.length_map]
    have b := CoThetaBits.state_width tail d ro
    omega
  · rw [←em,project_cover,CoThetaBits.live_coverage out tail (fun w h => (ro w).1 h)]
    rfl
  · rw [←em]
    exact guarded_complete tail k enough out d ro

theorem supported_step {m k S} {ws : List Wire} (run : Live (den CoThetaBits.target) m S)
    (nd : ws.Nodup) (rep : Rep ws S) (size : m≤k+1) (stop : CoThetaBits.target∉ws) :
    ∃ i j : Nat, i<j ∧ j<ws.length ∧ ∃ op : Kind, ∃ ka kb : Bool,
      Supported k (ws.map project) (nth (ws.map project) i) (nth (ws.map project) j) op ka kb := by
  classical
  cases run with
  | stop => exact (stop ((seen_iff rep CoThetaBits.target).2 rfl)).elim
  | @step m U a b op ab ha hb fresh tail =>
    obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
    obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
    subst a
    subst b
    let z := gate op x y
    have e : den z=(fun i => applyKind op (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
    have ne : x≠y := fun eq => ab (congrArg den eq)
    have rest : Live (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail
    have ng : den CoThetaBits.target≠absentBit := by
      intro h
      have bad := congrFun h (true,0)
      simp [CoThetaBits.den_target,absentBit] at bad
    have non : z≠CoThetaBits.zero := by
      intro h
      exact rest.excludes_zero ng (Or.inl (((congrArg den h).trans CoThetaBits.den_zero).symm))
    have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
    obtain ⟨i,hi,vi⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j,hj,vj⟩ := List.mem_iff_getElem.mp hy
    have i_ne : i≠j := by intro h; subst j; exact ne (vi.symm.trans vj)
    have each (l : Nat) (h : l<ws.length) :
        nth (ws.map project) l=project ws[l] := by
      simp [nth,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
    by_cases order : i<j
    · refine ⟨i,j,order,hj,op,?_⟩
      rw [each i hi,each j hj,vi,vj]
      exact support_from op nd ne non nf rep rest (by omega)
    · refine ⟨j,i,by omega,hi,reflectOp op,?_⟩
      rw [each j hj,each i hi,vj,vi]
      have sw : gate (reflectOp op) y x=z := by apply project_inj; simp [z,project_gate,gate_swap]
      apply support_from (reflectOp op) nd (Ne.symm ne) <;> try rw [sw]
      · exact non
      · exact nf
      · intro w
        simpa [ins,or_left_comm] using rep w
      · exact rest
      · omega

end CoNatBench
namespace CoThetaSeven
open CoThetaFreeCore CoNatBench
open CoThetaBits (Wire Row Rep den)

def keepIndex (a b : Bool) : Nat := a.toNat+2*b.toNat

theorem pair7_index : ∀ a b : Fin 7, a.val<b.val →
    ∃ q : Fin 21, firstPairs[q.val]?.getD (0,1)=(a.val,b.val) := by decide +kernel

theorem pair8_index : ∀ a b : Fin 8, a.val<b.val →
    ∃ q : Fin 28, secondPairs[q.val]?.getD (0,1)=(a.val,b.val) := by decide +kernel

theorem first_keep (op : Kind) : ∀ a b : Fin 7, a.val<b.val → ∀ ka kb : Bool,
    cover (extension rootWords (nth rootWords a.val) (nth rootWords b.val) op ka kb)=all → ka=true ∧ kb=true := by
  cases op <;> decide +kernel

theorem first_repr (op : Kind) (q : Fin 21) :
    let pair := firstPairs[q.val]?.getD (0,1)
    extension rootWords (nth rootWords pair.1) (nth rootWords pair.2) op true true =
    firstWords (4*q.val+opIndex op) := by
  revert q
  cases op <;> decide +kernel

theorem class_data : ∀ i : Fin 13, (postPool i).length=8 ∧ CoThetaBits.target∉postPool i := by decide +kernel
theorem target_out : CoThetaBits.target∉CoThetaBits.raw := by decide +kernel

theorem root_from_cases (checks : ∀ i : Fin 84, guardedSearch 8 (firstWords i.val)=false) : RawNine := by
  intro m S live cost rep
  obtain ⟨a,b,ab,limit,op,ka,kb,hit⟩ := supported_step live CoThetaBits.raw_nodup rep cost target_out
  change b<7 at limit
  let u : Fin 7 := ⟨a,by omega⟩
  let v : Fin 7 := ⟨b,limit⟩
  obtain ⟨q,eq⟩ := pair7_index u v ab
  obtain ⟨_,_,_,cov,more⟩ := hit
  obtain ⟨k1,k2⟩ := first_keep op u v ab ka kb cov
  subst ka
  subst kb
  have link := first_repr op q
  change firstPairs[q.val]?.getD (0,1)=(a,b) at eq
  rw [eq] at link
  change guardedSearch 8 (extension rootWords (nth rootWords a) (nth rootWords b) op true true)=true at more
  rw [link] at more
  have bound : 4*q.val+opIndex op<84 := by
    have h := q.isLt
    cases op <;> simp [opIndex] <;> omega
  exact Bool.false_ne_true ((checks ⟨_,bound⟩).symm.trans more)

theorem digits (q : Nat) (op : Kind) (ka kb : Bool) :
    let n := 16*q+4*opIndex op+keepIndex ka kb
    n/16=q ∧ (n/4) % 4=opIndex op ∧ n % 4=keepIndex ka kb := by
  cases op <;> cases ka <;> cases kb <;> simp [opIndex,keepIndex] <;> omega

theorem bits_op (op : Kind) (a b : Word) : kinds (opIndex op) a b=wordGate op a b := by cases op <;> rfl

end CoThetaSeven

namespace CoNatBench
def rankSignal (z : Word) : Nat :=
  if z.1<0x8810040008020004000380000200800101843c0007000fe0040100021e0002030e000fe0040003800000e000fe0038001fe003fc000000 || (z.1==0x8810040008020004000380000200800101843c0007000fe0040100021e0002030e000fe0040003800000e000fe0038001fe003fc000000 && z.2<0x800000000000008004000100008020000000020000010200008020000080000020020801080800801010010008) then (if z.1<0x1ffffff00000000000000000000001fff800000000000000000003fffffc0000000000000000000000ffffffffc00000000000000000 || (z.1==0x1ffffff00000000000000000000001fff800000000000000000003fffffc0000000000000000000000ffffffffc00000000000000000 && z.2<0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0) then (if z.1<0x3fffffffff800000000000000000000000000000000000007ffffffffffffffffffc00000000000000000 || (z.1==0x3fffffffff800000000000000000000000000000000000007ffffffffffffffffffc00000000000000000 && z.2<0x1030a5c100000000800004000624b84e7500004000c080000040808240d1800000000004268c26311c0d1b8e1380002080300821010c0) then (if z.1<0x7fffffffffffffffffffffff8000000000000000000000000000000000000 || (z.1==0x7fffffffffffffffffffffff8000000000000000000000000000000000000 && z.2<0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300) then (if z.1<0x7fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff || (z.1==0x7fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2<0x5800802c008110e8000080030000040000002020200000ae02814108815409a4a0020353a8408120946400202291440481e0da03b0) then (if z.1<0x601c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0x601c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c) then (if z.1==0x50138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff && z.2==0x80800800000002800400090010a02000080026001401120010a070200282208260134a11080a28a2181401404a then 6 else 20) else (if z.1==0x601c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c then 8 else 20)) else (if z.1<0x7fffffc000003fff000000007ffffffffff000000003ffffffffc00000000 || (z.1==0x7fffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2<0x200000003490e800400001000110020001087030000000403250e40040019ea0c0040001913118c2380800100633e19704e0408c0220) then (if z.1==0x7fe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2==0x5800802c008110e8000080030000040000002020200000ae02814108815409a4a0020353a8408120946400202291440481e0da03b0 then 0 else 20) else (if z.1<0x7fffffffffffc000000000007ffffffffffffffffffc00000000000000000 || (z.1==0x7fffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2<0x406920d0000100008000020002000c061000000000000000c4ab09758cd800010000044262c26305c0d07860b80002080300801000c0) then (if z.1==0x7fffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2==0x200000003490e800400001000110020001087030000000403250e40040019ea0c0040001913118c2380800100633e19704e0408c0220 then 0 else 20) else (if z.1==0x7fffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2==0x406920d0000100008000020002000c061000000000000000c4ab09758cd800010000044262c26305c0d07860b80002080300801000c0 then 0 else 20)))) else (if z.1<0x300f00181ff3ff807f00ffff80000000000000000000000078003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0x300f00181ff3ff807f00ffff80000000000000000000000078003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x88001000100000890c28011000c07000000002020009020200c02080019400142a021c05984c02c0501805800c) then (if z.1<0x2808c017f84fc07ff0fffe000000000000000000000000004700383e000e1fffe003803fffffffc001fff || (z.1==0x2808c017f84fc07ff0fffe000000000000000000000000004700383e000e1fffe003803fffffffc001fff && z.2<0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a) then (if z.1==0x7fffffffffffffffffffffff8000000000000000000000000000000000000 && z.2==0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300 then 0 else 20) else (if z.1==0x2808c017f84fc07ff0fffe000000000000000000000000004700383e000e1fffe003803fffffffc001fff && z.2==0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a then 8 else 20)) else (if z.1<0x3ff0001fe07c00007fff00000000000000000000000000007fffc000000ffff00003fffe00003ffffffff || (z.1==0x3ff0001fe07c00007fff00000000000000000000000000007fffc000000ffff00003fffe00003ffffffff && z.2<0x28810014408024e08001000570240d402820224ab2008000600000008001000042000035ca8408120952401202491440082e31a18b0) then (if z.1==0x300f00181ff3ff807f00ffff80000000000000000000000078003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x88001000100000890c28011000c07000000002020009020200c02080019400142a021c05984c02c0501805800c then 6 else 20) else (if z.1<0x3fffffe0007fffff800000000000000000000000000000007ffffffffff000000003ffffffffc00000000 || (z.1==0x3fffffe0007fffff800000000000000000000000000000007ffffffffff000000003ffffffffc00000000 && z.2<0x80000201854c0804000020001934620003ab333002001040020404000000182000000001943118c8380800100634e18710e0400c0020) then (if z.1==0x3ff0001fe07c00007fff00000000000000000000000000007fffc000000ffff00003fffe00003ffffffff && z.2==0x28810014408024e08001000570240d402820224ab2008000600000008001000042000035ca8408120952401202491440082e31a18b0 then 0 else 20) else (if z.1==0x3fffffe0007fffff800000000000000000000000000000007ffffffffff000000003ffffffffc00000000 && z.2==0x80000201854c0804000020001934620003ab333002001040020404000000182000000001943118c8380800100634e18710e0400c0020 then 0 else 20))))) else (if z.1<0xffffff800000000000000000007fffff800000000000000000003fff0000000000000000000000000003ffffffffc00000000 || (z.1==0xffffff800000000000000000007fffff800000000000000000003fff0000000000000000000000000003ffffffffc00000000 && z.2<0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220) then (if z.1<0xa02700470038780000000000004fc07ff0fffe00000000000000207fe01fffff80000000000000000003803fffffffc001fff || (z.1==0xa02700470038780000000000004fc07ff0fffe00000000000000207fe01fffff80000000000000000003803fffffffc001fff && z.2<0x20002002848808000000088054008b0094a42000000002000401120118b030000080200220030a01080820a8181401440a) then (if z.1<0x3fffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0x3fffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00) then (if z.1==0x3fffffffff800000000000000000000000000000000000007ffffffffffffffffffc00000000000000000 && z.2==0x1030a5c100000000800004000624b84e7500004000c080000040808240d1800000000004268c26311c0d1b8e1380002080300821010c0 then 0 else 20) else (if z.1==0x3fffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00 then 0 else 20)) else (if z.1<0xc0380078003f8000000000000073ff807f00ffff8000000000003fb0ffe0fe0000000000000000000003ffc1fe003ffffe000 || (z.1==0xc0380078003f8000000000000073ff807f00ffff8000000000003fb0ffe0fe0000000000000000000003ffc1fe003ffffe000 && z.2<0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c) then (if z.1==0xa02700470038780000000000004fc07ff0fffe00000000000000207fe01fffff80000000000000000003803fffffffc001fff && z.2==0x20002002848808000000088054008b0094a42000000002000401120118b030000080200220030a01080820a8181401440a then 6 else 20) else (if z.1<0xffc0007fffc0000000000000007c00007fff00000000000000003fc0ffff000000000000000000000003fffe00003ffffffff || (z.1==0xffc0007fffc0000000000000007c00007fff00000000000000003fc0ffff000000000000000000000003fffe00003ffffffff && z.2<0x9000016c088356680010801500401002820224a32008002a00800000015408a4a00201152800802004040000269144048361ca0b30) then (if z.1==0xc0380078003f8000000000000073ff807f00ffff8000000000003fb0ffe0fe0000000000000000000003ffc1fe003ffffe000 && z.2==0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c then 8 else 20) else (if z.1==0xffc0007fffc0000000000000007c00007fff00000000000000003fc0ffff000000000000000000000003fffe00003ffffffff && z.2==0x9000016c088356680010801500401002820224a32008002a00800000015408a4a00201152800802004040000269144048361ca0b30 then 0 else 20)))) else (if z.1<0x1404600000000470038780000000017f800000070fffe0000000027e01fc000e01fffff80000000000e1fffe000000000003fc001fff || (z.1==0x1404600000000470038780000000017f800000070fffe0000000027e01fc000e01fffff80000000000e1fffe000000000003fc001fff && z.2<0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a) then (if z.1<0xffffffffffffffffc000000000000000000000000000000000003fffffffffff8000000000000000000000000000000000000 || (z.1==0xffffffffffffffffc000000000000000000000000000000000003fffffffffff8000000000000000000000000000000000000 && z.2<0x201080203890f190713101e00000000000004000400101803850f0887021e6ccf8c70380010000020000000040030010040100e00300) then (if z.1==0xffffff800000000000000000007fffff800000000000000000003fff0000000000000000000000000003ffffffffc00000000 && z.2==0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220 then 0 else 20) else (if z.1<0xffffffffffffffffc0000000007fffffffffffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0xffffffffffffffffc0000000007fffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x80800301c16e026702463c001c24701822f383c683c61e00000400000000000001081800040000080000000000040000180201000c00) then (if z.1==0xffffffffffffffffc000000000000000000000000000000000003fffffffffff8000000000000000000000000000000000000 && z.2==0x201080203890f190713101e00000000000004000400101803850f0887021e6ccf8c70380010000020000000040030010040100e00300 then 0 else 20) else (if z.1==0xffffffffffffffffc0000000007fffffffffffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x80800301c16e026702463c001c24701822f383c683c61e00000400000000000001081800040000080000000000040000180201000c00 then 0 else 20))) else (if z.1<0x180780000000078003f8000000000181f8000007f00ffff80000039ffe00000ffe0fe0000000000000fe00ffffc000000003ffffe000 || (z.1==0x180780000000078003f8000000000181f8000007f00ffff80000039ffe00000ffe0fe0000000000000fe00ffffc000000003ffffe000 && z.2<0x80000000008001a8005000000000880408015001c1300000008a220021061202c120000084000422020c41880c00c0101821800c) then (if z.1==0x1404600000000470038780000000017f800000070fffe0000000027e01fc000e01fffff80000000000e1fffe000000000003fc001fff && z.2==0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a then 8 else 20) else (if z.1<0x1ff80000000007fffc000000000001fe00000007fff00000000003e00000000ffff000000000000000ffff00000000000003ffffffff || (z.1==0x1ff80000000007fffc000000000001fe00000007fff00000000003e00000000ffff000000000000000ffff00000000000003ffffffff && z.2<0x2d810804800035aa8001080460200d400000004a92008008c0201410880400924a002024a88400100956401200010400003a3521990) then (if z.1==0x180780000000078003f8000000000181f8000007f00ffff80000039ffe00000ffe0fe0000000000000fe00ffffc000000003ffffe000 && z.2==0x80000000008001a8005000000000880408015001c1300000008a220021061202c120000084000422020c41880c00c0101821800c then 6 else 20) else (if z.1==0x1ff80000000007fffc000000000001fe00000007fff00000000003e00000000ffff000000000000000ffff00000000000003ffffffff && z.2==0x2d810804800035aa8001080460200d400000004a92008008c0201410880400924a002024a88400100956401200010400003a3521990 then 0 else 20)))))) else (if z.1<0x3007f80003fc00007ffc000000ff00007e00c000000ff00001fe0000600000040001f000007ffc00000001ff00000003e0000000001fff || (z.1==0x3007f80003fc00007ffc000000ff00007e00c000000ff00001fe0000600000040001f000007ffc00000001ff00000003e0000000001fff && z.2<0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0) then (if z.1<0xfe000000003fff8000000000000fffe00003ffff80000000001fffc00000003f0000000000003ffffff0000000000001ffffc00000000 || (z.1==0xfe000000003fff8000000000000fffe00003ffff80000000001fffc00000003f0000000000003ffffff0000000000001ffffc00000000 && z.2<0xa000020091d46800000021000834220001297110000010401054640040008aa0400400008011184a1808001006116093106000040000) then (if z.1<0x1ffffff0000007fffffffffc000001fff8000007fffffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0x1ffffff0000007fffffffffc000001fff8000007fffffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x103825d004022026b02465c00644b90f9605084c68dce0e00000000000100000001081800080000100001808100000000080203001c00) then (if z.1<0x1ffffff0000007fffffffffc000000000000000000000000000003fffffc000ffffffff8000000000000000000000000000000000000 || (z.1==0x1ffffff0000007fffffffffc000000000000000000000000000003fffffc000ffffffff8000000000000000000000000000000000000 && z.2<0x4071a0e008011190b13102e0000008000000000040010180c8a311d9b0e0604d38c307800200000400004000c0000000000100600100) then (if z.1==0x1ffffff00000000000000000000001fff800000000000000000003fffffc0000000000000000000000ffffffffc00000000000000000 && z.2==0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0 then 0 else 20) else (if z.1==0x1ffffff0000007fffffffffc000000000000000000000000000003fffffc000ffffffff8000000000000000000000000000000000000 && z.2==0x4071a0e008011190b13102e0000008000000000040010180c8a311d9b0e0604d38c307800200000400004000c0000000000100600100 then 0 else 20)) else (if z.1<0xa000460000270000003878000008c0001803c07f8000fe0000138001e01fc03f0000ffff8000383e0000000fe0000001ffffc00000000 || (z.1==0xa000460000270000003878000008c0001803c07f8000fe0000138001e01fc03f0000ffff8000383e0000000fe0000001ffffc00000000 && z.2<0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a) then (if z.1==0x1ffffff0000007fffffffffc000001fff8000007fffffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x103825d004022026b02465c00644b90f9605084c68dce0e00000000000100000001081800080000100001808100000000080203001c00 then 0 else 20) else (if z.1<0xc000780000380000003f8000000f00001f83ff800000ffff801c0001ffe000300000fe0000003fc00000000ffffc0001fe00000000000 || (z.1==0xc000780000380000003f8000000f00001f83ff800000ffff801c0001ffe000300000fe0000003fc00000000ffffc0001fe00000000000 && z.2<0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c) then (if z.1==0xa000460000270000003878000008c0001803c07f8000fe0000138001e01fc03f0000ffff8000383e0000000fe0000001ffffc00000000 && z.2==0x480000200020028488080009002b8054048b049ca42000080026011401120118b07020028220826093ca11080a28aa181401444a then 7 else 20) else (if z.1==0xc000780000380000003f8000000f00001f83ff800000ffff801c0001ffe000300000fe0000003fc00000000ffffc0001fe00000000000 && z.2==0x80000080408001a8005000100000890c68015001c1700040408a6200ab065206c12080019400142a021c45994c12c0501825800c then 7 else 20)))) else (if z.1<0xfe007fff003fff80003fffffc00000000000000000000000001fffc1ffffc03f0000ffff8000000000000000000000000000000000000 || (z.1==0xfe007fff003fff80003fffffc00000000000000000000000001fffc1ffffc03f0000ffff8000000000000000000000000000000000000 && z.2<0x6021a060109170801131036000000800000040004001018050f17098f060a2c4584705800000000600000000c0010010000000200000) then (if z.1<0xfe007fff0000000000000000000fffe01f80000000000000001fffc1ffffc0000000000000003ffffff0000ffffc00000000000000000 || (z.1==0xfe007fff0000000000000000000fffe01f80000000000000001fffc1ffffc0000000000000003ffffff0000ffffc00000000000000000 && z.2<0x141236c50000100000000420020498c23500004000408000040a90834855800000000044020422314c04098e098000208030000000040) then (if z.1==0xfe000000003fff8000000000000fffe00003ffff80000000001fffc00000003f0000000000003ffffff0000000000001ffffc00000000 && z.2==0xa000020091d46800000021000834220001297110000010401054640040008aa0400400008011184a1808001006116093106000040000 then 0 else 20) else (if z.1==0xfe007fff0000000000000000000fffe01f80000000000000001fffc1ffffc0000000000000003ffffff0000ffffc00000000000000000 && z.2==0x141236c50000100000000420020498c23500004000408000040a90834855800000000044020422314c04098e098000208030000000040 then 0 else 20)) else (if z.1<0xfe007fff003fff80003fffffc00fffe01f83ffff8000ffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0xfe007fff003fff80003fffffc00fffe01f83ffff8000ffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x181024f008166002102466c00286db029607185c204ce1600000400000100000001081800000000180000808000000000180000000400) then (if z.1==0xfe007fff003fff80003fffffc00000000000000000000000001fffc1ffffc03f0000ffff8000000000000000000000000000000000000 && z.2==0x6021a060109170801131036000000800000040004001018050f17098f060a2c4584705800000000600000000c0010010000000200000 then 0 else 20) else (if z.1<0x22040060020070007000078000800c007e00c007f80ff000010038006001fc04f001f01ff8700003e00001ff00000003e01ffc00001fff || (z.1==0x22040060020070007000078000800c007e00c007f80ff000010038006001fc04f001f01ff8700003e00001ff00000003e01ffc00001fff && z.2<0x480000200020020488080009002b0050048a049c240000080024011400100118305020020220824091c2100002282a0804004442) then (if z.1==0xfe007fff003fff80003fffffc00fffe01f83ffff8000ffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x181024f008166002102466c00286db029607185c204ce1600000400000100000001081800000000180000808000000000180000000400 then 0 else 20) else (if z.1==0x22040060020070007000078000800c007e00c007f80ff000010038006001fc04f001f01ff8700003e00001ff00000003e01ffc00001fff && z.2==0x480000200020020488080009002b0050048a049c240000080024011400100118305020020220824091c2100002282a0804004442 then 11 else 20))))) else (if z.1<0x44080380040180038000780001007000807b03f800f0001ffa00c00181fe01f801fe00000380007c00001e0001ffc7fc00000003ffe000 || (z.1==0x44080380040180038000780001007000807b03f800f0001ffa00c00181fe01f801fe00000380007c00001e0001ffc7fc00000003ffe000 && z.2<0x80000080408001280050001000000908680050014150004040886200aa045206410080011400140a001444914412404008248004) then (if z.1<0x33e7f87ff00000000000000000ff0ffe7e0000000000000001fe3ffc6001fc0000000000007ffc03ffff01ff0000000000000000000000 || (z.1==0x33e7f87ff00000000000000000ff0ffe7e0000000000000001fe3ffc6001fc0000000000007ffc03ffff01ff0000000000000000000000 && z.2<0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0) then (if z.1<0x33e0000003fc7ff80000000000ff0ffe0000c007f800000001fe3ffc00000004f0000000007ffc03ffff000000000003e01ffc00000000 || (z.1==0x33e0000003fc7ff80000000000ff0ffe0000c007f800000001fe3ffc00000004f0000000007ffc03ffff000000000003e01ffc00000000 && z.2<0xa0000201b55ca804400021001924620002a31330020010003214a400000114a080000001153008ca280000000226a18514a040880220) then (if z.1==0x3007f80003fc00007ffc000000ff00007e00c000000ff00001fe0000600000040001f000007ffc00000001ff00000003e0000000001fff && z.2==0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0 then 0 else 20) else (if z.1==0x33e0000003fc7ff80000000000ff0ffe0000c007f800000001fe3ffc00000004f0000000007ffc03ffff000000000003e01ffc00000000 && z.2==0xa0000201b55ca804400021001924620002a31330020010003214a400000114a080000001153008ca280000000226a18514a040880220 then 0 else 20)) else (if z.1<0x33e7f87ff3fc7ff87ffc07fffc000000000000000000000001fe3ffc6001fc04f001f01ff8000000000000000000000000000000000000 || (z.1==0x33e7f87ff3fc7ff87ffc07fffc000000000000000000000001fe3ffc6001fc04f001f01ff8000000000000000000000000000000000000 && z.2<0x607120e03811b110f01103a0000008000000000000000080f8b3b15190e144c9a8c10680030000060000400080020000040100c00300) then (if z.1==0x33e7f87ff00000000000000000ff0ffe7e0000000000000001fe3ffc6001fc0000000000007ffc03ffff01ff0000000000000000000000 && z.2==0x1436b7cd00001000880004200624b8ce7500004000c080000c4ab09758dd80001000004426ac26315c0d1f8e1b80002080300821010c0 then 0 else 20) else (if z.1<0x33e7f87ff3fc7ff87ffc07fffcff0ffe7e00c007f80ff00000000000000000000000000000000000000000000000000000000000000000 || (z.1==0x33e7f87ff3fc7ff87ffc07fffcff0ffe7e00c007f80ff00000000000000000000000000000000000000000000000000000000000000000 && z.2<0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00) then (if z.1==0x33e7f87ff3fc7ff87ffc07fffc000000000000000000000001fe3ffc6001fc04f001f01ff8000000000000000000000000000000000000 && z.2==0x607120e03811b110f01103a0000008000000000000000080f8b3b15190e144c9a8c10680030000060000400080020000040100c00300 then 0 else 20) else (if z.1==0x33e7f87ff3fc7ff87ffc07fffcff0ffe7e00c007f80ff00000000000000000000000000000000000000000000000000000000000000000 && z.2==0x183825f01c16e026f02467c007c6ff0f962f387c68fce1e000004000001000000010818000c0000180001808100040000180203001c00 then 0 else 20)))) else (if z.1<0x55ebfb9ff000000000000000017f73fe807800000000000002fec7fd81fe000000000000038ffc7c1fff1e0001ffc00000000000000000 || (z.1==0x55ebfb9ff000000000000000017f73fe807800000000000002fec7fd81fe000000000000038ffc7c1fff1e0001ffc00000000000000000 && z.2<0x1436b34d0000100088000420062428cc45000000008000000c4a309518cc80001000004024ac0611540916821a8000000010082101080) then (if z.1<0x500bf80005fc00038ffc0000017f00008003000000f0000002fe0001800001f801fe0000038ffc0000001e00000007fc00000003ffe000 || (z.1==0x500bf80005fc00038ffc0000017f00008003000000f0000002fe0001800001f801fe0000038ffc0000001e00000007fc00000003ffe000 && z.2<0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0) then (if z.1==0x44080380040180038000780001007000807b03f800f0001ffa00c00181fe01f801fe00000380007c00001e0001ffc7fc00000003ffe000 && z.2==0x80000080408001280050001000000908680050014150004040886200aa045206410080011400140a001444914412404008248004 then 11 else 20) else (if z.1<0x55e0000005fd8ff800000000017f73fe000303f80000000002fec7fc000001f800000000038ffc7c1fff0000000007fc00000000000000 || (z.1==0x55e0000005fd8ff800000000017f73fe000303f80000000002fec7fc000001f800000000038ffc7c1fff0000000007fc00000000000000 && z.2<0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220) then (if z.1==0x500bf80005fc00038ffc0000017f00008003000000f0000002fe0001800001f801fe0000038ffc0000001e00000007fc00000003ffe000 && z.2==0x2d810816c08835ee8001080570240d402820224ab200800ae02814108815409a4a002035fa8408120956401202691440483e3da1bb0 then 0 else 20) else (if z.1==0x55e0000005fd8ff800000000017f73fe000303f80000000002fec7fc000001f800000000038ffc7c1fff0000000007fc00000000000000 && z.2==0xa0000201b5dce804400021001934620003ab7330020010403254e40040019ea0c0040001953118ca380800100637e19714e0408c0220 then 0 else 20))) else (if z.1<0x55ebfb9ff5fd8ffb8ffc787ffc000000000000000000000002fec7fd81fe01f801fe000000000000000000000000000000000000000000 || (z.1==0x55ebfb9ff5fd8ffb8ffc787ffc000000000000000000000002fec7fd81fe01f801fe000000000000000000000000000000000000000000 && z.2<0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300) then (if z.1==0x55ebfb9ff000000000000000017f73fe807800000000000002fec7fd81fe000000000000038ffc7c1fff1e0001ffc00000000000000000 && z.2==0x1436b34d0000100088000420062428cc45000000008000000c4a309518cc80001000004024ac0611540916821a8000000010082101080 then 0 else 20) else (if z.1<0x55ebfb9ff5fd8ffb8ffc787ffd7f73fe807b03f800f0001ff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0x55ebfb9ff5fd8ffb8ffc787ffd7f73fe807b03f800f0001ff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x183821701c14e024f004274007c66f0d062a383448b421a000004000000000000000008000c0000180001000100040000100203001800) then (if z.1==0x55ebfb9ff5fd8ffb8ffc787ffc000000000000000000000002fec7fd81fe01f801fe000000000000000000000000000000000000000000 && z.2==0x6071a0e03891f190f13103e0000008000000400040010180f8f3f1d9f0e1e6cdf8c707800300000600004000c0030010040100e00300 then 0 else 20) else (if z.1==0x55ebfb9ff5fd8ffb8ffc787ffd7f73fe807b03f800f0001ff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x183821701c14e024f004274007c66f0d062a383448b421a000004000000000000000008000c0000180001000100040000100203001800 then 0 else 20))))))) else (if z.1<0xfff404600ffffffc7003878003ffffff7f87ffffff0fffe007fffffe7e01fffffe01ffffffffffffffffe1fffe003ffffffffffc001fff || (z.1==0xfff404600ffffffc7003878003ffffff7f87ffffff0fffe007fffffe7e01fffffe01ffffffffffffffffe1fffe003ffffffffffc001fff && z.2<0xa0004a01b5fce8244284a908193d622b83ff77bb069cb460325ce42641159fb2c11cb071b5339aeaba6893da173febbfbef8548d466a) then (if z.1<0xcc1807800c0380078003f8000300f00181ff3ff807f00ffff8000000000000000000000000000000000000000000000000000000000000 || (z.1==0xcc1807800c0380078003f8000300f00181ff3ff807f00ffff8000000000000000000000000000000000000000000000000000000000000 && z.2<0x0) then (if z.1<0xaa1404600a0270047003878002808c017f84fc07ff0fffe000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xaa1404600a0270047003878002808c017f84fc07ff0fffe000000000000000000000000000000000000000000000000000000000000000 && z.2<0x480000200020020408000009002900500482048c0400000000000100000001081000000000000000808000000000080000000400) then (if z.1<0xaa0000000a0270000000000002808c000004fc07f80000000501380000000207f000000004700383e000000000003803fffffc00000000 || (z.1==0xaa0000000a0270000000000002808c000004fc07f80000000501380000000207f000000004700383e000000000003803fffffc00000000 && z.2<0x0) then (if z.1<0xa01400000a00000470000000028000017e04c000070ff00005000002600002040e01f000047000000000e1ff00003803e00003fc001fff || (z.1==0xa01400000a00000470000000028000017e04c000070ff00005000002600002040e01f000047000000000e1ff00003803e00003fc001fff && z.2<0x0) then (if z.1==0x8810040008020004000380000200800101843c0007000fe0040100021e0002030e000fe0040003800000e000fe0038001fe003fc000000 && z.2==0x800000000000008004000100008020000000020000010200008020000080000020020801080800801010010008 then 5 else 20) else (if z.1==0xa01400000a00000470000000028000017e04c000070ff00005000002600002040e01f000047000000000e1ff00003803e00003fc001fff && z.2==0x0 then 0 else 20)) else (if z.1<0xaa140460000000000000000002808c017f80000000000000050138027e01fc000000000004700383e000e1fffe00000000000000000000 || (z.1==0xaa140460000000000000000002808c017f80000000000000050138027e01fc000000000004700383e000e1fffe00000000000000000000 && z.2<0x4800000000000000000000090023000004000408000000080024011000000000004020020200804090c010000208020000000040) then (if z.1==0xaa0000000a0270000000000002808c000004fc07f80000000501380000000207f000000004700383e000000000003803fffffc00000000 && z.2==0x0 then 0 else 20) else (if z.1<0xaa1404600a02700470038780000000000000000000000000050138027e01fe07fe01fffff8000000000000000000000000000000000000 || (z.1==0xaa1404600a02700470038780000000000000000000000000050138027e01fe07fe01fffff8000000000000000000000000000000000000 && z.2<0x0) then (if z.1==0xaa140460000000000000000002808c017f80000000000000050138027e01fc000000000004700383e000e1fffe00000000000000000000 && z.2==0x4800000000000000000000090023000004000408000000080024011000000000004020020200804090c010000208020000000040 then 0 else 20) else (if z.1==0xaa1404600a02700470038780000000000000000000000000050138027e01fe07fe01fffff8000000000000000000000000000000000000 && z.2==0x0 then 0 else 20)))) else (if z.1<0xcc0000000c038000000000000300f00000073ff8000000000601c000000003fb00000000078003fc0000000000003ffc1fe00000000000 || (z.1==0xcc0000000c038000000000000300f00000073ff8000000000601c000000003fb00000000078003fc0000000000003ffc1fe00000000000 && z.2<0x804000000000000010000001086000000000400040400040008a0040040000800110001008001004114012004000040000) then (if z.1<0xc01800000c00000780000000030000018007000007f0000006000003800003f80ffe0000078000000000fe0000003ffc000003ffffe000 || (z.1==0xc01800000c00000780000000030000018007000007f0000006000003800003f80ffe0000078000000000fe0000003ffc000003ffffe000 && z.2<0x0) then (if z.1==0xaa1404600a0270047003878002808c017f84fc07ff0fffe000000000000000000000000000000000000000000000000000000000000000 && z.2==0x480000200020020408000009002900500482048c0400000000000100000001081000000000000000808000000000080000000400 then 0 else 20) else (if z.1==0xc01800000c00000780000000030000018007000007f0000006000003800003f80ffe0000078000000000fe0000003ffc000003ffffe000 && z.2==0x0 then 0 else 20)) else (if z.1<0xcc18078000000000000000000300f00181f80000000000000601c0039ffe000000000000078003fc0000fe00ffffc00000000000000000 || (z.1==0xcc18078000000000000000000300f00181f80000000000000601c0039ffe000000000000078003fc0000fe00ffffc00000000000000000 && z.2<0x0) then (if z.1==0xcc0000000c038000000000000300f00000073ff8000000000601c000000003fb00000000078003fc0000000000003ffc1fe00000000000 && z.2==0x804000000000000010000001086000000000400040400040008a0040040000800110001008001004114012004000040000 then 0 else 20) else (if z.1<0xcc1807800c0380078003f8000000000000000000000000000601c0039ffe03fb0ffe0fe000000000000000000000000000000000000000 || (z.1==0xcc1807800c0380078003f8000000000000000000000000000601c0039ffe03fb0ffe0fe000000000000000000000000000000000000000 && z.2<0x80000080408001200040000000000000400040010100004040886000a20450060100000000000000000040010010000000200000) then (if z.1==0xcc18078000000000000000000300f00181f80000000000000601c0039ffe000000000000078003fc0000fe00ffffc00000000000000000 && z.2==0x0 then 0 else 20) else (if z.1==0xcc1807800c0380078003f8000000000000000000000000000601c0039ffe03fb0ffe0fe000000000000000000000000000000000000000 && z.2==0x80000080408001200040000000000000400040010100004040886000a20450060100000000000000000040010010000000200000 then 0 else 20))))) else (if z.1<0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00000000000000000000000000000000000000000000000000000000000000000 && z.2<0x28010014008024e00001000540240d0028202048b0008000000000000000000000000000c0000000001000100040000000203001800) then (if z.1<0xf00000000ffc00000000000003ff00000007c0000000000007fe0000000003fc0000000007fffc000000000000003fffe0000000000000 || (z.1==0xf00000000ffc00000000000003ff00000007c0000000000007fe0000000003fc0000000007fffc000000000000003fffe0000000000000 && z.2<0x12408800440000000110040000282022002000000220080000001140080000001152000802000000000268104048040880220) then (if z.1<0xee1c07e00e03f007f003ff800380fc01ffffffffffffffffff01f803fffffffffffffffffff003ffe000ffffffffffffffffffffffffff || (z.1==0xee1c07e00e03f007f003ff800380fc01ffffffffffffffffff01f803fffffffffffffffffff003ffe000ffffffffffffffffffffffffff && z.2<0xc80000a040a003ac88580019002b895c6c8b549de570004840ae6314ab16531ef170a0039620966a93de55994e3aea581c25c44e) then (if z.1==0xcc1807800c0380078003f8000300f00181ff3ff807f00ffff8000000000000000000000000000000000000000000000000000000000000 && z.2==0x0 then 0 else 20) else (if z.1==0xee1c07e00e03f007f003ff800380fc01ffffffffffffffffff01f803fffffffffffffffffff003ffe000ffffffffffffffffffffffffff && z.2==0xc80000a040a003ac88580019002b895c6c8b549de570004840ae6314ab16531ef170a0039620966a93de55994e3aea581c25c44e then 12 else 20)) else (if z.1<0xf01ff800000000000000000003ff0001fe0000000000000007fe0003e00000000000000007fffc000000ffff0000000000000000000000 || (z.1==0xf01ff800000000000000000003ff0001fe0000000000000007fe0003e00000000000000007fffc000000ffff0000000000000000000000 && z.2<0x24810800000000880000000420200c400000000080000008402014108800001000000024a8040010091600120000000000082101080) then (if z.1==0xf00000000ffc00000000000003ff00000007c0000000000007fe0000000003fc0000000007fffc000000000000003fffe0000000000000 && z.2==0x12408800440000000110040000282022002000000220080000001140080000001152000802000000000268104048040880220 then 0 else 20) else (if z.1<0xf01ff8000ffc0007fffc000000000000000000000000000007fe0003e00003fc0ffff00000000000000000000000000000000000000000 || (z.1==0xf01ff8000ffc0007fffc000000000000000000000000000007fe0003e00003fc0ffff00000000000000000000000000000000000000000 && z.2<0x50008028008110e0000080000000000000000000000000a802814100814409a0800200030000000000400000020000040100c00300) then (if z.1==0xf01ff800000000000000000003ff0001fe0000000000000007fe0003e00000000000000007fffc000000ffff0000000000000000000000 && z.2==0x24810800000000880000000420200c400000000080000008402014108800001000000024a8040010091600120000000000082101080 then 0 else 20) else (if z.1==0xf01ff8000ffc0007fffc000000000000000000000000000007fe0003e00003fc0ffff00000000000000000000000000000000000000000 && z.2==0x50008028008110e0000080000000000000000000000000a802814100814409a0800200030000000000400000020000040100c00300 then 0 else 20)))) else (if z.1<0xffe00000000000000000000003fffffe000000000000000007fffffc000000000000000007ffffffffff00000000000000000000000000 || (z.1==0xffe00000000000000000000003fffffe000000000000000007fffffc000000000000000007ffffffffff00000000000000000000000000 && z.2<0x0) then (if z.1<0xfa1ffc600ffe7007ffff878003ff8c01ff87fc07ffffffe007ff3803fe01ffffffffffffffffff83e000fffffe003fffffffffffffffff || (z.1==0xfa1ffc600ffe7007ffff878003ff8c01ff87fc07ffffffe007ff3803fe01ffffffffffffffffff83e000fffffe003fffffffffffffffff && z.2<0x2d858816c28837eea849888570b40ff82d606afafbcac20ae0a81670995551ba5b8b2737faac2a1a2f5f7cb312e9b6cae9bf7db5ffa) then (if z.1==0xf01ff8000ffc0007fffc000003ff0001fe07c00007fff00000000000000000000000000000000000000000000000000000000000000000 && z.2==0x28010014008024e00001000540240d0028202048b0008000000000000000000000000000c0000000001000100040000000203001800 then 0 else 20) else (if z.1<0xfc1fff800fff8007fffff80003fff001fffffff807ffffffffffc003fffe03ff0fffffe007fffffc0000ffffffffffffffe003ffffffff || (z.1==0xfc1fff800fff8007fffff80003fff001fffffff807ffffffffffc003fffe03ff0fffffe007fffffc0000ffffffffffffffe003ffffffff && z.2<0x2d890816c88c3dee9a810d0571240d48b8e6a25fb21c970ae42c1cb6a81ff0ff6a6c323dfa9d48134bf661d65bfdd56c4d3fbff9bbc) then (if z.1==0xfa1ffc600ffe7007ffff878003ff8c01ff87fc07ffffffe007ff3803fe01ffffffffffffffffff83e000fffffe003fffffffffffffffff && z.2==0x2d858816c28837eea849888570b40ff82d606afafbcac20ae0a81670995551ba5b8b2737faac2a1a2f5f7cb312e9b6cae9bf7db5ffa then 1 else 20) else (if z.1==0xfc1fff800fff8007fffff80003fff001fffffff807ffffffffffc003fffe03ff0fffffe007fffffc0000ffffffffffffffe003ffffffff && z.2==0x2d890816c88c3dee9a810d0571240d48b8e6a25fb21c970ae42c1cb6a81ff0ff6a6c323dfa9d48134bf661d65bfdd56c4d3fbff9bbc then 1 else 20))) else (if z.1<0xffe000000ffffff80000000000000000000000000000000007fffffc000003fff000000000000000000000000000000000000000000000 || (z.1==0xffe000000ffffff80000000000000000000000000000000007fffffc000003fff000000000000000000000000000000000000000000000 && z.2<0x200000003090e000400001000000000000004000000000003050e00040018680c0040000010000020000000000030010040000800200) then (if z.1==0xffe00000000000000000000003fffffe000000000000000007fffffc000000000000000007ffffffffff00000000000000000000000000 && z.2==0x0 then 0 else 20) else (if z.1<0xffe000000ffffff80000000003fffffe0007fffff800000000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xffe000000ffffff80000000003fffffe0007fffff800000000000000000000000000000000000000000000000000000000000000000000 && z.2<0x80000201814c0004000020001824600002a3030002001000000400000000000000000000040000080000000000040000100000000000) then (if z.1==0xffe000000ffffff80000000000000000000000000000000007fffffc000003fff000000000000000000000000000000000000000000000 && z.2==0x200000003090e000400001000000000000004000000000003050e00040018680c0040000010000020000000000030010040000800200 then 0 else 20) else (if z.1==0xffe000000ffffff80000000003fffffe0007fffff800000000000000000000000000000000000000000000000000000000000000000000 && z.2==0x80000201814c0004000020001824600002a3030002001000000400000000000000000000040000080000000000040000100000000000 then 0 else 20)))))) else (if z.1<0xfffffffffffffffffffffffffe808c017f84fc07ff0fffe007fffffffffffffffffffffffc700383e000e1fffe003803fffffffc001fff || (z.1==0xfffffffffffffffffffffffffe808c017f84fc07ff0fffe007fffffffffffffffffffffffc700383e000e1fffe003803fffffffc001fff && z.2<0x6071e8e038b1f1b0f3b58be80009082b8054448b449da5a0f8fbf1fff1f5e7dff9dfb7f0230282268260d3cad10b0a38ae1914e1474a) then (if z.1<0xfffffffffa0270047003878003fffffffffcfc07ff0fffe007fffffffffffe07fe01fffffffffffffffffffffffff803fffffffc001fff || (z.1==0xfffffffffa0270047003878003fffffffffcfc07ff0fffe007fffffffffffe07fe01fffffffffffffffffffffffff803fffffffc001fff && z.2<0x1436b7cd0002100288284ca08624b8cefd054048b0c9ca420c4ab09778ddc01130118b4726ac2e335c2f1fbebb9080a28ab18961154ca) then (if z.1<0xfffff8000ffffffffffc000003fffffffe07fffffffff00007ffffffe00003fffffff00007ffffffffffffff00003fffffffffffffffff || (z.1==0xfffff8000ffffffffffc000003fffffffe07fffffffff00007ffffffe00003fffffff00007ffffffffffffff00003fffffffffffffffff && z.2<0xa2d81281fddceb5ee80031805f3662d403ab7334ab201840be56e5414881dea9e4a40203dfb958cb389d64112637f1d714e3e3de1bb0) then (if z.1<0xfff807800fffffff8003f80003ffffff81fffffffff00fffffffffff9ffe03fffffe0fe007fffffffffffe00ffffffffffffffffffe000 || (z.1==0xfff807800fffffff8003f80003ffffff81fffffffff00fffffffffff9ffe03fffffe0fe007fffffffffffe00ffffffffffffffffffe000 && z.2<0xa0008201b5dce88441a82150193462008baf7b315201d1703254e48a6201bfa6d206c12195319cca3c2a021c47bfed97d4f058ad822c) then (if z.1==0xfff404600ffffffc7003878003ffffff7f87ffffff0fffe007fffffe7e01fffffe01ffffffffffffffffe1fffe003ffffffffffc001fff && z.2==0xa0004a01b5fce8244284a908193d622b83ff77bb069cb460325ce42641159fb2c11cb071b5339aeaba6893da173febbfbef8548d466a then 4 else 20) else (if z.1==0xfff807800fffffff8003f80003ffffff81fffffffff00fffffffffff9ffe03fffffe0fe007fffffffffffe00ffffffffffffffffffe000 && z.2==0xa0008201b5dce88441a82150193462008baf7b315201d1703254e48a6201bfa6d206c12195319cca3c2a021c47bfed97d4f058ad822c then 13 else 20)) else (if z.1<0xfffffffff00000000000000000000000000000000000000007fffffffffffc000000000000000000000000000000000000000000000000 || (z.1==0xfffffffff00000000000000000000000000000000000000007fffffffffffc000000000000000000000000000000000000000000000000 && z.2<0x406120c00001000080000200000008000000000000000000c0a3015180c0000100000400020000040000400080000000000000000000) then (if z.1==0xfffff8000ffffffffffc000003fffffffe07fffffffff00007ffffffe00003fffffff00007ffffffffffffff00003fffffffffffffffff && z.2==0xa2d81281fddceb5ee80031805f3662d403ab7334ab201840be56e5414881dea9e4a40203dfb958cb389d64112637f1d714e3e3de1bb0 then 10 else 20) else (if z.1<0xfffffffff00000000000000003fffffffff800000000000000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xfffffffff00000000000000003fffffffff800000000000000000000000000000000000000000000000000000000000000000000000000 && z.2<0x103025c000000000800004000604b80e1400004000c080000000000000100000000000000080000100001808100000000000002001000) then (if z.1==0xfffffffff00000000000000000000000000000000000000007fffffffffffc000000000000000000000000000000000000000000000000 && z.2==0x406120c00001000080000200000008000000000000000000c0a3015180c0000100000400020000040000400080000000000000000000 then 0 else 20) else (if z.1==0xfffffffff00000000000000003fffffffff800000000000000000000000000000000000000000000000000000000000000000000000000 && z.2==0x103025c000000000800004000604b80e1400004000c080000000000000100000000000000080000100001808100000000000002001000 then 0 else 20)))) else (if z.1<0xfffffffffffc0007fffc000003ffffffffffc00007fff00007fffffffffffffc0ffff00007ffffffffffffffffffffffe00003ffffffff || (z.1==0xfffffffffffc0007fffc000003ffffffffffc00007fff00007fffffffffffffc0ffff00007ffffffffffffffffffffffe00003ffffffff && z.2<0x143fb7cd16c09835ee8005280774bccf752820624af280800eeab89758dd95409a4a006437fea6395e0d5fce1b826934c0783e3da1bf0) then (if z.1<0xfffffffffc0380078003f80003ffffffffff3ff807f00ffffffffffffffffffb0ffe0fe007fffffffffffffffffffffc1fe003ffffe000 || (z.1==0xfffffffffc0380078003f80003ffffffffff3ff807f00ffffffffffffffffffb0ffe0fe007fffffffffffffffffffffc1fe003ffffe000 && z.2<0x1436bfcd00081408881a84250625b8ce7d90c6c015c09c170c4eb49ffefd8ab075206c562eac3f715d4fbfafdfd994e1ac3509a3590cc) then (if z.1==0xfffffffffa0270047003878003fffffffffcfc07ff0fffe007fffffffffffe07fe01fffffffffffffffffffffffff803fffffffc001fff && z.2==0x1436b7cd0002100288284ca08624b8cefd054048b0c9ca420c4ab09778ddc01130118b4726ac2e335c2f1fbebb9080a28ab18961154ca then 13 else 20) else (if z.1==0xfffffffffc0380078003f80003ffffffffff3ff807f00ffffffffffffffffffb0ffe0fe007fffffffffffffffffffffc1fe003ffffe000 && z.2==0x1436bfcd00081408881a84250625b8ce7d90c6c015c09c170c4eb49ffefd8ab075206c562eac3f715d4fbfafdfd994e1ac3509a3590cc then 4 else 20)) else (if z.1<0xfffffffffffffff80000000003fffffffffffffff800000007fffffffffffffff000000007fffffffffffffffffffffffffffc00000000 || (z.1==0xfffffffffffffff80000000003fffffffffffffff800000007fffffffffffffff000000007fffffffffffffffffffffffffffc00000000 && z.2<0x1e36b7ed1b5dde80cc00063007b7feee753ab77300e081040f6ffed75cdd99ea1c0040443fff37bdff8d9f8f1be37e39f17e0c29c12e0) then (if z.1==0xfffffffffffc0007fffc000003ffffffffffc00007fff00007fffffffffffffc0ffff00007ffffffffffffffffffffffe00003ffffffff && z.2==0x143fb7cd16c09835ee8005280774bccf752820624af280800eeab89758dd95409a4a006437fea6395e0d5fce1b826934c0783e3da1bf0 then 10 else 20) else (if z.1<0xfffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000 || (z.1==0xfffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000 && z.2<0x0) then (if z.1==0xfffffffffffffff80000000003fffffffffffffff800000007fffffffffffffff000000007fffffffffffffffffffffffffffc00000000 && z.2==0x1e36b7ed1b5dde80cc00063007b7feee753ab77300e081040f6ffed75cdd99ea1c0040443fff37bdff8d9f8f1be37e39f17e0c29c12e0 then 2 else 20) else (if z.1==0xfffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000 && z.2==0x0 then 0 else 20))))) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffd0138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffd0138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff && z.2<0x183825f01c16e026f02c6fc087c6ff0fbe2f787cf8fdebe20000c0026011401120118b8702c028238826193cb110c0a28ba1a17015c4a) then (if z.1<0xffffffffffffffffffffffffffff0001fe07c00007fff00007fffffffffffffffffffffffffffc000000ffff00003fffe00003ffffffff || (z.1==0xffffffffffffffffffffffffffff0001fe07c00007fff00007fffffffffffffffffffffffffffc000000ffff00003fffe00003ffffffff && z.2<0x62f9b0e17c99f3def93113e0570248d402824224eb210980fef3f1d9f8e1f6cdfce707835fa8408720956401e02791540483e3fa1bb0) then (if z.1<0xffffffffffffffffffffffffff00f00181ff3ff807f00fffffffffffffffffffffffffffff8003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0xffffffffffffffffffffffffff00f00181ff3ff807f00fffffffffffffffffffffffffffff8003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x6071a0e03891f190f1b903f000100800890c68015001c1f0f8f3f1dbf2e1efcffac7c7a083019406142a421cc59b4c12c45118e5830c) then (if z.1==0xfffffffffffffffffffffffffe808c017f84fc07ff0fffe007fffffffffffffffffffffffc700383e000e1fffe003803fffffffc001fff && z.2==0x6071e8e038b1f1b0f3b58be80009082b8054448b449da5a0f8fbf1fff1f5e7dff9dfb7f0230282268260d3cad10b0a38ae1914e1474a then 4 else 20) else (if z.1==0xffffffffffffffffffffffffff00f00181ff3ff807f00fffffffffffffffffffffffffffff8003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x6071a0e03891f190f1b903f000100800890c68015001c1f0f8f3f1dbf2e1efcffac7c7a083019406142a421cc59b4c12c45118e5830c then 13 else 20)) else (if z.1<0xfffffffffffffffffffffffffffffffe0007fffff800000007ffffffffffffffffffffffffffffffffff000000003ffffffffc00000000 || (z.1==0xfffffffffffffffffffffffffffffffe0007fffff800000007ffffffffffffffffffffffffffffffffff000000003ffffffffc00000000 && z.2<0xe071a2e1bdddf994f13123e019346a0003ab7330420111c0faf7f5d9f0e1feedf8c70781973118ce38084010c637e19714e140ec0320) then (if z.1==0xffffffffffffffffffffffffffff0001fe07c00007fff00007fffffffffffffffffffffffffffc000000ffff00003fffe00003ffffffff && z.2==0x62f9b0e17c99f3def93113e0570248d402824224eb210980fef3f1d9f8e1f6cdfce707835fa8408720956401e02791540483e3fa1bb0 then 10 else 20) else (if z.1<0xfffffffffffffffffffffffffffffffffff800000000000007ffffffffffffffffffffffffffffffffffffffffffc00000000000000000 || (z.1==0xfffffffffffffffffffffffffffffffffff800000000000007ffffffffffffffffffffffffffffffffffffffffffc00000000000000000 && z.2<0x1637bfcf03891f198f13143e0624b8ce7500044004c090180fcfbf9fdfdf9e6cdf8c707c26bc26317c0d1f8e1f8030218070182f013c0) then (if z.1==0xfffffffffffffffffffffffffffffffe0007fffff800000007ffffffffffffffffffffffffffffffffff000000003ffffffffc00000000 && z.2==0xe071a2e1bdddf994f13123e019346a0003ab7330420111c0faf7f5d9f0e1feedf8c70781973118ce38084010c637e19714e140ec0320 then 9 else 20) else (if z.1==0xfffffffffffffffffffffffffffffffffff800000000000007ffffffffffffffffffffffffffffffffffffffffffc00000000000000000 && z.2==0x1637bfcf03891f198f13143e0624b8ce7500044004c090180fcfbf9fdfdf9e6cdf8c707c26bc26317c0d1f8e1f8030218070182f013c0 then 3 else 20)))) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffc000003fff000000007ffffffffff000000003ffffffffc00000000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2<0x1a3825f01f5feea6f42467d007d7ff2f963fbf7f68fce1e403254e40041019ea0c10c18019d3118da380980910637e1971ce2438c1e20) then (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2<0x18382df01c1ee42ef03ee7c507c7ff0f9ebffefc7dfcfdf700044408a6300ab06530ed9208c019418142b829d459d4c12d8521b259c0c) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffd0138027e01fe07fe01fffffc700383e000e1fffe003803fffffffc001fff && z.2==0x183825f01c16e026f02c6fc087c6ff0fbe2f787cf8fdebe20000c0026011401120118b8702c028238826193cb110c0a28ba1a17015c4a then 13 else 20) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2<0x183da5f81ed6e837fea467c807f6ff0fd62f387e6afee1e00ae06814109815409a5a81a035fa840992095e481202691441c83e3da1fb0) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffe01c0039ffe03fb0ffe0fe0078003fc0000fe00fffffffc1fe003ffffe000 && z.2==0x18382df01c1ee42ef03ee7c507c7ff0f9ebffefc7dfcfdf700044408a6300ab06530ed9208c019418142b829d459d4c12d8521b259c0c then 4 else 20) else (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffe0003e00003fc0ffff00007fffc000000ffff00003fffe00003ffffffff && z.2==0x183da5f81ed6e837fea467c807f6ff0fd62f387e6afee1e00ae06814109815409a5a81a035fa840992095e481202691441c83e3da1fb0 then 10 else 20))) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000007ffffffffffffffffffc00000000000000000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2<0x1c3eb7fd1c16f026f82467e007e6ffcff72f387c68fce1e00c4af09758dd8000101081c426ec2631dc0d1f8e1b80402081b0283101cc0) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffc000003fff000000007ffffffffff000000003ffffffffc00000000 && z.2==0x1a3825f01f5feea6f42467d007d7ff2f963fbf7f68fce1e403254e40041019ea0c10c18019d3118da380980910637e1971ce2438c1e20 then 3 else 20) else (if z.1<0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000 || (z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000 && z.2<0x1e3f3ffe1f9fff3fff3777fe07c6ff8f962f3c7c6cfcf1f80f8f7f1d9f1e1e6cdf9cf1f800f00001e0001c081c00700101c0303e01f00) then (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000007ffffffffffffffffffc00000000000000000 && z.2==0x1c3eb7fd1c16f026f82467e007e6ffcff72f387c68fce1e00c4af09758dd8000101081c426ec2631dc0d1f8e1b80402081b0283101cc0 then 9 else 20) else (if z.1==0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000 && z.2==0x1e3f3ffe1f9fff3fff3777fe07c6ff8f962f3c7c6cfcf1f80f8f7f1d9f1e1e6cdf9cf1f800f00001e0001c081c00700101c0303e01f00 then 2 else 20)))))))
def headOK (bound : Nat) : List Word → Bool
  | [] => true
  | x::_ => decide (bound≤rankSignal x)

def permittedSearch (bound : Nat) : Nat → List Word → Bool
  | 0,ws => headOK bound ws && ws.contains target
  | k+1,ws => headOK bound ws && (ws.contains target || guarded k (permittedSearch bound k) ws)

end CoNatBench

namespace CoNatBench
def permitPrefix (bound i j : Nat) : Bool :=
  let ws := firstWords i
  let p := secondPairs[j/16]?.getD (0,1)
  let a := nth ws p.1
  let b := nth ws p.2
  let z := kinds ((j/4) % 4) a b
  let rest := ws.filter (fun w => w != a && w != b)
  let next := match j % 4 with
    | 0 => z::rest
    | 1 => z::a::rest
    | 2 => z::b::rest
    | _ => z::a::b::rest
  if rankSignal z < bound || z == (0,0) || ws.contains z || next.length>9 || cover next != all then true
  else !(permittedSearch bound 8 next)

def permitBlock (bound i first count : Nat) : Bool :=
  (List.range count).all (fun d => permitPrefix bound i (first+d))


end CoNatBench

namespace CoThetaFreeCore

variable {ρ : Type}

theorem free_enlarge {raw ws : List (ρ→Bool)} {k} (run : Free raw k ws)
    (base : List (ρ→Bool)) (inc : ∀ f∈raw, f∈base) :
    ∃ xs, Free base k xs ∧ ∀ f∈ws, f∈xs := by
  induction run with
  | start => exact ⟨_,Free.start,inc⟩
  | @binary n us a b pre op ha hb ih =>
    obtain ⟨ys,prev,sub⟩ := ih
    refine ⟨_,Free.binary prev op (sub a ha) (sub b hb),?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with e|old
    · exact e ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub f old)

theorem free_move {raw ws : List (ρ→Bool)} {k} (run : Free raw k ws)
    {w : ρ→Bool} (atEnd : w∈ws) (notRaw : w∉raw) :
    ∃ m xs, m<k ∧ Free (w::raw) m xs ∧ ∀ f∈ws, f∈xs := by
  induction run with
  | start => exact (notRaw atEnd).elim
  | @binary n us a b pre op ha hb ih =>
    by_cases found : w∈us
    · obtain ⟨m,ys,cap,prev,sub⟩ := ih found
      refine ⟨m+1,_,by omega,Free.binary prev op (sub a ha) (sub b hb),?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with e|old
      · exact e ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sub f old)
    · have eq := (List.mem_cons.mp atEnd).resolve_right found
      obtain ⟨ys,prev,sub⟩ := free_enlarge pre (w::raw) (fun _ h => List.mem_cons_of_mem _ h)
      refine ⟨n,ys,by omega,prev,?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with e|old
      · exact (e.trans eq.symm).symm ▸ free_keeps_raw prev List.mem_cons_self
      · exact sub f old

end CoThetaFreeCore

namespace CoThetaFreeCore
variable {ρ : Type}
inductive Marked (p : (ρ→Bool)→Prop) (goal : ρ→Bool) : Nat→((ρ→Bool)→Prop)→Prop
  | stop (allowed : p goal) : Marked p goal 0 (fun v => v=goal)
  | step {k U a b} (allowed : ∀ w, ins a (ins b U) w → p w)
      (kind : Kind) (ab : a≠b) (ha : a≠absentBit) (hb : b≠absentBit)
      (fresh : ¬ins a (ins b U) (fun i => applyKind kind (a i) (b i)))
      (tail : Marked p goal k (ins (fun i => applyKind kind (a i) (b i)) U)) :
      Marked p goal (k+1) (ins a (ins b U))

theorem Marked.live {p : (ρ→Bool)→Prop} {goal k S} (r : Marked p goal k S) : Live goal k S := by
  induction r with
  | stop => exact .stop
  | step _ op ab ha hb fresh _ ih => exact .step op ab ha hb fresh ih

theorem rewindMarked {raw ws : List (ρ → Bool)} {n : Nat} (run : Free raw n ws)
    (hz : absentBit∈raw) {p : (ρ→Bool)→Prop} (hs : ∀ w∈ws, p w) {goal : ρ → Bool} {k : Nat} {S : (ρ → Bool) → Prop}
    (needed : Marked p goal k S) (available : ∀ w, S w → w∈ws) :
    ∃ m T, m≤k+n ∧ Marked p goal m T ∧ ∀ w, T w → w∈raw := by
  classical
  induction run generalizing k S with
  | start => exact ⟨k,S,by omega,needed,available⟩
  | @binary n ws a b pre kind ha hb ih =>
    let z : ρ → Bool := fun i => applyKind kind (a i) (b i)
    have rawzero : absentBit∈ws := free_keeps_raw pre hz
    have values (w) (hw : S w) : w=z ∨ w∈ws := List.mem_cons.mp (available w hw)
    by_cases used : S z
    · by_cases old : z∈ws
      · obtain ⟨m,T,hm,ht,hsub⟩ := ih (fun w h => hs w (List.mem_cons_of_mem _ h)) needed (fun w hw =>
          (values w hw).elim (fun e => e.symm ▸ old) id)
        exact ⟨m,T,by omega,ht,hsub⟩
      · let U : (ρ → Bool) → Prop := fun w => w≠z ∧ S w
        have eq : ins z U = S := by
          funext w
          apply propext
          constructor
          · intro hw
            rcases hw with h | h
            · exact h.symm ▸ used
            · exact h.2
          · intro hw
            by_cases e : w=z
            · exact Or.inl e
            · exact Or.inr ⟨e,hw⟩
        have memU (w) (hw : U w) : w∈ws := (values w hw.2).resolve_left hw.1
        have memAll (w) (hw : ins a (ins b U) w) : w∈ws := by
          rcases hw with e | e | hu
          · exact e.symm ▸ ha
          · exact e.symm ▸ hb
          · exact memU w hu
        have distinct : a≠b := by
          intro hab
          subst b
          rcases same_result kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonA : a≠absentBit := by
          intro ea
          subst a
          rcases zero_left kind b with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr hb)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nonB : b≠absentBit := by
          intro eb
          subst b
          rcases zero_right kind a with e|e
          · exact old ((congrArg (fun v => v∈ws) e).mpr ha)
          · exact old ((congrArg (fun v => v∈ws) e).mpr rawzero)
        have nxt : Marked p goal (k+1) (ins a (ins b U)) :=
          Marked.step (fun w h => hs w (List.mem_cons_of_mem _ (memAll w h))) kind distinct nonA nonB (fun bad => old (memAll z bad)) (eq.symm ▸ needed)
        obtain ⟨m,T,hm,ht,hsub⟩ := ih (fun w h => hs w (List.mem_cons_of_mem _ h)) nxt memAll
        exact ⟨m,T,by omega,ht,hsub⟩
    · obtain ⟨m,T,hm,ht,hsub⟩ := ih (fun w h => hs w (List.mem_cons_of_mem _ h)) needed (fun w hw =>
        (values w hw).resolve_left (fun e => used (e ▸ hw)))
      exact ⟨m,T,by omega,ht,hsub⟩

end CoThetaFreeCore
namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Row Rep den gate full)

def allowedWire (bnd : Nat) (f : Row→Bool) : Prop := ∀ v : Wire, den v=f → bnd≤rankSignal (project v)

theorem head_allowed {bnd ws S} (rep : Rep ws S) (h : ∀ f, S f → allowedWire bnd f) :
    headOK bnd (ws.map project)=true := by
  cases ws with
  | nil => rfl
  | cons w ws =>
    change decide (bnd≤rankSignal (project w))=true
    exact decide_eq_true_eq.mpr (h (den w) ((rep _).2 ⟨w,List.mem_cons_self,rfl⟩) w rfl)

private theorem marked_direction (bnd : Nat) {m k : Nat} {ws : List Wire} {x y : Wire} {U}
    (op : Kind) (nd : ws.Nodup) (hx : x∈ws) (hy : y∈ws) (ne : x≠y)
    (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (remaining : Live (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k)
    (old : CoThetaBits.coverage ws=full)
    (recur : ∀ zs, zs.Nodup → Rep zs (ins (den (gate op x y)) U) →
      permittedSearch bnd k (zs.map project)=true) :
    pairTry k (permittedSearch bnd k) (ws.map project)
      (project x,privateMask (ws.map project) (project x))
      (project y,privateMask (ws.map project) (project y))=true := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  have nz : wordGate op (project x) (project y)≠(0,0) := by
    rw [←project_gate]
    intro eq
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using eq
  have nf : wordGate op (project x) (project y)∉ws.map project := by
    rw [←project_gate]
    intro v
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp v
    exact fresh (project_inj eq ▸ hw)
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  have width := CoThetaBits.state_width remaining d ro
  have cov := CoThetaBits.live_coverage out remaining (fun w h => (ro w).1 h)
  apply pair_hit k _ _ _ _ op
  apply tryField_hit op ka kb _ (project_nodup nd) (List.mem_map_of_mem hx)
    (List.mem_map_of_mem hy) (fun eq => ne (project_inj eq)) nz nf
  · rw [←em,List.length_map]
    omega
  · rw [project_cover,old]
    rfl
  · rw [←em,project_cover,cov]
    rfl
  · rw [←em]
    exact recur out d ro

theorem marked_complete (bnd : Nat) {m S} (run : Marked (allowedWire bnd) (den CoThetaBits.target) m S) :
    ∀ fuel, m≤fuel → ∀ ws, ws.Nodup → Rep ws S → permittedSearch bnd fuel (ws.map project)=true := by
  classical
  induction run with
  | stop permitted =>
    intro fuel _ ws _ rep
    have hit := List.mem_map_of_mem (f:=project) ((seen_iff rep CoThetaBits.target).2 rfl)
    have good := head_allowed rep (fun _ eq => eq.symm ▸ permitted)
    cases fuel <;> simp [permittedSearch,good,target,hit]
  | @step m U a b admissible kind ab ha hb fresh tail ih =>
    intro fuel bound ws nd rep
    cases fuel with
    | zero => omega
    | succ k =>
      obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
      obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
      subst a
      subst b
      let z := gate kind x y
      have e : den z=(fun i => applyKind kind (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
      have dist : x≠y := fun eq => ab (congrArg den eq)
      have rt : Live (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail.live
      have ng : den CoThetaBits.target≠absentBit := by
        intro h
        have bad := congrFun h (true,0)
        simp [CoThetaBits.den_target,absentBit] at bad
      have non : z≠CoThetaBits.zero := by
        intro eq
        have eq2 := (congrArg den eq).trans CoThetaBits.den_zero
        exact rt.excludes_zero ng (Or.inl eq2.symm)
      have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
      have current := Live.step kind ab ha hb fresh tail.live
      have fullWs := CoThetaBits.live_coverage ws current (fun w h => (rep w).1 h)
      have boundK : m≤k := by omega
      have recurse : ∀ ys, ys.Nodup → Rep ys (ins (den z) U) → permittedSearch bnd k (ys.map project)=true := by
        intro ys h r
        rw [e] at r
        exact ih k boundK ys h r
      have forward := marked_direction bnd kind nd hx hy dist non nf rep rt boundK fullWs recurse
      have swapped : gate (reflectOp kind) y x=z := by
        apply project_inj
        simp [z,project_gate,gate_swap]
      have revRep : Rep ws (ins (den y) (ins (den x) U)) := by
        intro w
        simpa [ins,or_left_comm] using rep w
      have reverse : pairTry k (permittedSearch bnd k) (ws.map project)
          (project y,privateMask (ws.map project) (project y)) (project x,privateMask (ws.map project) (project x))=true := by
        apply marked_direction bnd (reflectOp kind) nd hy hx dist.symm <;> try rw [swapped]
        · exact non
        · exact nf
        · exact revRep
        · exact rt
        · exact boundK
        · exact fullWs
        · exact recurse
      let natWs := ws.map project
      let points := natWs.map (fun v => (v,privateMask natWs v))
      have one : (project x,privateMask natWs (project x))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hx)
      have two : (project y,privateMask natWs (project y))∈points :=
        List.mem_map_of_mem (List.mem_map_of_mem hy)
      have distinct : (project x,privateMask natWs (project x))≠(project y,privateMask natWs (project y)) :=
        fun eq => dist (project_inj (congrArg Prod.fst eq))
      have pass := pairs_hit (pairTry k (permittedSearch bnd k) natWs) one two distinct forward reverse
      have size := CoThetaBits.state_width current nd rep
      have limit : ¬(ws.map project).length>k+2 := by simp only [List.length_map]; omega
      rw [permittedSearch,head_allowed rep admissible,Bool.true_and,Bool.or_eq_true]
      right
      rw [guarded_eq,if_neg limit]
      exact pass

end CoNatBench

namespace CoNatBench
open CoThetaFreeCore
open CoThetaBits (Wire Rep den gate)

def MarkSupport (bnd : Nat) (k : Nat) (ws : List Word) (a b : Word) (op : Kind) (ka kb : Bool) : Prop :=
  let z := wordGate op a b
  let out := extension ws a b op ka kb
  z≠(0,0) ∧ z∉ws ∧ out.length≤k+1 ∧ cover out=all ∧ permittedSearch bnd k out=true

private theorem marked_support_from (bnd : Nat) {m k} {ws : List Wire} {x y : Wire} {U} (op : Kind)
    (nd : ws.Nodup) (ne : x≠y) (non : gate op x y≠CoThetaBits.zero) (fresh : gate op x y∉ws)
    (rep : Rep ws (ins (den x) (ins (den y) U)))
    (tail : Marked (allowedWire bnd) (den CoThetaBits.target) m (ins (den (gate op x y)) U)) (enough : m≤k) :
    ∃ ka kb : Bool, MarkSupport bnd k (ws.map project) (project x) (project y) op ka kb := by
  classical
  let z := gate op x y
  let out := z::(CoThetaBits.kept x y U++CoThetaBits.trim x y ws)
  have ro : Rep out (ins (den z) U) := CoThetaBits.edit_rep rep
  have d : out.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,CoThetaBits.edit_distinct ne nd⟩
    intro hz
    exact fresh ((seen_iff rep z).2 (Or.inr (Or.inr ((CoThetaBits.edit_member rep).1 hz))))
  let ka := decide (U (den x))
  let kb := decide (U (den y))
  have em : out.map project=extension (ws.map project) (project x) (project y) op ka kb :=
    project_edit ws x y op U
  refine ⟨ka,kb,?_,?_,?_,?_,?_⟩
  · rw [←project_gate]
    intro e
    apply non
    apply project_inj
    simpa [project,CoThetaBits.zero] using e
  · rw [←project_gate]
    intro h
    obtain ⟨v,hv,e⟩ := List.mem_map.mp h
    exact fresh (project_inj e ▸ hv)
  · rw [←em,List.length_map]
    have b := CoThetaBits.state_width tail.live d ro
    omega
  · rw [←em,project_cover,CoThetaBits.live_coverage out tail.live (fun w h => (ro w).1 h)]
    rfl
  · rw [←em]
    exact marked_complete bnd tail k enough out d ro

theorem marked_step (bnd : Nat) {m k S} {ws : List Wire} (run : Marked (allowedWire bnd) (den CoThetaBits.target) m S)
    (nd : ws.Nodup) (rep : Rep ws S) (size : m≤k+1) (stop : CoThetaBits.target∉ws) :
    ∃ i j : Nat, i<j ∧ j<ws.length ∧ ∃ op : Kind, ∃ ka kb : Bool,
      MarkSupport bnd k (ws.map project) (nth (ws.map project) i) (nth (ws.map project) j) op ka kb := by
  classical
  cases run with
  | stop => exact (stop ((seen_iff rep CoThetaBits.target).2 rfl)).elim
  | @step m U a b admissible op ab ha hb fresh tail =>
    obtain ⟨x,hx,ex⟩ := (rep a).1 (Or.inl rfl)
    obtain ⟨y,hy,ey⟩ := (rep b).1 (Or.inr (Or.inl rfl))
    subst a
    subst b
    let z := gate op x y
    have e : den z=(fun i => applyKind op (den x i) (den y i)) := CoThetaBits.den_gate _ _ _
    have ne : x≠y := fun eq => ab (congrArg den eq)
    have rest : Marked (allowedWire bnd) (den CoThetaBits.target) m (ins (den z) U) := by rw [e]; exact tail
    have ng : den CoThetaBits.target≠absentBit := by
      intro h
      have bad := congrFun h (true,0)
      simp [CoThetaBits.den_target,absentBit] at bad
    have non : z≠CoThetaBits.zero := by
      intro h
      exact rest.live.excludes_zero ng (Or.inl (((congrArg den h).trans CoThetaBits.den_zero).symm))
    have nf : z∉ws := fun h => fresh (e ▸ (seen_iff rep z).1 h)
    obtain ⟨i,hi,vi⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨j,hj,vj⟩ := List.mem_iff_getElem.mp hy
    have i_ne : i≠j := by intro h; subst j; exact ne (vi.symm.trans vj)
    have each (l : Nat) (h : l<ws.length) :
        nth (ws.map project) l=project ws[l] := by
      simp [nth,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem h]
    by_cases order : i<j
    · refine ⟨i,j,order,hj,op,?_⟩
      rw [each i hi,each j hj,vi,vj]
      exact marked_support_from bnd op nd ne non nf rep rest (by omega)
    · refine ⟨j,i,by omega,hi,reflectOp op,?_⟩
      rw [each j hj,each i hi,vj,vi]
      have sw : gate (reflectOp op) y x=z := by apply project_inj; simp [z,project_gate,gate_swap]
      apply marked_support_from bnd (reflectOp op) nd (Ne.symm ne) <;> try rw [sw]
      · exact non
      · exact nf
      · intro w
        simpa [ins,or_left_comm] using rep w
      · exact rest
      · omega

end CoNatBench
namespace CoNatBench
open CoThetaFreeCore

theorem allowed_head {bnd k w ws} (yes : permittedSearch bnd k (w::ws)=true) : bnd≤rankSignal w := by
  cases k <;> simp only [permittedSearch,headOK,Bool.and_eq_true,decide_eq_true_eq] at yes <;> exact yes.1

end CoNatBench
namespace CoThetaSeven
open CoNatBench CoThetaFreeCore
open CoThetaBits (Wire Row Rep den)
theorem marked_conflict (bnd label q : Nat) (qBound : q<28) {a b : Nat}
    (pair : secondPairs[q]?.getD (0,1)=(a,b)) (op : Kind) (ka kb : Bool)
    (hit : MarkSupport bnd 8 (firstWords label) (nth (firstWords label) a) (nth (firstWords label) b) op ka kb) :
    ∃ j : Fin 448, permitPrefix bnd label j.val=false := by
  let j := 16*q+4*opIndex op+keepIndex ka kb
  have cap : j<448 := by cases op <;> cases ka <;> cases kb <;> simp [j,opIndex,keepIndex] <;> omega
  refine ⟨⟨j,cap⟩,?_⟩
  obtain ⟨hq,ho,hk⟩ := digits q op ka kb
  change j/16=q at hq
  change (j/4) % 4=opIndex op at ho
  change j % 4=keepIndex ka kb at hk
  obtain ⟨non,fresh,width,cov,yes⟩ := hit
  have certified : bnd≤rankSignal (wordGate op (nth (firstWords label) a) (nth (firstWords label) b)) := allowed_head yes
  simp only [permitPrefix,hq,ho,hk,pair,bits_op,Prod.fst,Prod.snd]
  cases ka <;> cases kb <;>
    simp [extension,keepList,restOf] at width cov yes <;>
    simp [keepIndex,restOf,non,fresh,Nat.not_lt_of_ge width,Nat.not_lt_of_ge certified,cov,yes]

theorem marked_after (bnd : Nat) (i : Fin 13) (checks : ∀ j : Fin 448, permitPrefix bnd (numbers.getD i.val 0) j.val=true) :
    ∀ {m S}, Marked (allowedWire bnd) (den CoThetaBits.target) m S → m≤9 → Rep (postPool i) S → False := by
  intro m S live bound rep
  obtain ⟨n,stop⟩ := class_data i
  obtain ⟨a,b,ab,lb,op,ka,kb,hit⟩ := marked_step bnd live (post_data i).1 rep bound stop
  rw [n] at lb
  obtain ⟨q,eq⟩ := pair8_index ⟨a,by omega⟩ ⟨b,lb⟩ ab
  rw [(post_data i).2.1] at hit
  obtain ⟨j,fault⟩ := marked_conflict bnd (numbers.getD i.val 0) q.val q.isLt eq op ka kb hit
  exact Bool.false_ne_true (fault.symm.trans (checks j))

theorem marked_blocks (bnd : Nat) (i : Fin 13) (tests : ∀ b : Fin 38,
    permitBlock bnd (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true) :
    ∀ j : Fin 448, permitPrefix bnd (numbers.getD i.val 0) j.val=true := by
  intro j
  let b : Fin 38 := ⟨j.val/12,by have h := j.isLt; omega⟩
  have all := tests b
  have d : j.val % 12 < min 12 (448-12*b.val) := by
    have h := j.isLt
    dsimp [b]
    omega
  have yes := List.all_eq_true.mp all (j.val % 12) (List.mem_range.mpr d)
  have eq : 12*b.val+j.val % 12=j.val := by dsimp [b]; omega
  exact eq ▸ yes


open CoThetaNine (SmallInput vertices7 ans7 toRows numeric_target)
theorem safe_after (r9 : RawNine) (bnd : Nat) (i : Fin 13)
    (tests : ∀ j : Fin 448, CoNatBench.permitPrefix bnd (numbers.getD i.val 0) j.val=true)
    {n ws} (run : Free ((numbered i).value::vertices7) n ws) (n9 : n≤9) (out : ans7∈ws) (ok : ∀ w∈ws, CoNatBench.allowedWire bnd (restrict toRows w)) : False := by
  let basis := ((numbered i).value::vertices7).map (restrict toRows)
  have zero : absentBit∈basis := List.mem_cons_of_mem _ List.mem_cons_self
  have goal := List.mem_map_of_mem (f:=restrict toRows) out
  rw [numeric_target] at goal
  have permit : ∀ w∈ws.map (restrict toRows), CoNatBench.allowedWire bnd w := by
    intro w hw
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp hw
    exact eq ▸ ok a ha
  obtain ⟨k,S,le,live,sub⟩ := rewindMarked (run.map_rows toRows) zero permit
    (Marked.stop (permit _ goal)) (fun w e => e.symm ▸ goal)
  rcases classify_pool i live.live (fun f hf => collect_init i (sub f hf)) with raw|extra
  · exact r9 live.live (by omega) raw
  · exact marked_after bnd i tests live (by omega) extra

end CoThetaSeven

namespace CoThetaFixedOrbit
open CoThetaFreeCore
open CoThetaNine (SmallInput raw7 ans7 vertices7)
open CoThetaSix (minorLift minor_off)
open CoThetaSeven (tag picked rotation numbered raw_mem rowPerm)

def rawGate (x y : Fin 7) (k : Kind) : TraceGate SmallInput := ⟨k,raw7 x,raw7 y⟩

theorem fresh_data (k : Kind) : ∀ (x y : Fin 7), x≠y →
    (∃ r : SmallInput, (rawGate x y k).value r ≠ false) ∧
    ∀ j : Fin 7, ∃ r : SmallInput, (rawGate x y k).value r ≠ raw7 j r := by
  cases k <;> decide +kernel

theorem head_fresh (x y : Fin 7) (k : Kind) (xy : x≠y) :
    (rawGate x y k).value∉vertices7 := by
  intro h
  rcases List.mem_cons.mp h with z|other
  · obtain ⟨r,off⟩ := (fresh_data k x y xy).1
    exact off (congrFun z r)
  · obtain ⟨j,eq⟩ := List.mem_ofFn.mp other
    obtain ⟨r,ne⟩ := (fresh_data k x y xy).2 j
    exact ne (congrFun eq.symm r)

def RawNine : Prop := ∃ n ws, n≤9 ∧ Free vertices7 n ws ∧ ans7∈ws
def PostNine (i : Fin 13) : Prop := ∃ n ws, n≤9 ∧ Free ((numbered i).value::vertices7) n ws ∧ ans7∈ws

theorem named_trace {x y : Fin 7} {k : Kind} (xy : x≠y)
    {n ws} (run : Free ((rawGate x y k).value::vertices7) n ws) (hit : ans7∈ws) :
    ∃ clean, sufficient vertices7 ans7 (rawGate x y k::clean) ∧
      freshTrace vertices7 (rawGate x y k::clean) ∧ clean.length≤n := by
  obtain ⟨ts,len,well,eq⟩ := trace_of_free run
  obtain ⟨clean,ok,fresh,le,_⟩ := simplify_trace ts ⟨well,eq ▸ hit⟩
  exact ⟨clean,⟨⟨raw_mem x,raw_mem y,ok.1⟩,ok.2⟩,⟨head_fresh x y k xy,fresh⟩,by omega⟩

theorem dispatch (x y : Fin 7) (k : Kind) (xy : x≠y) {n ws}
    (run : Free ((rawGate x y k).value::vertices7) n ws) (small : n≤9) (hit : ans7∈ws) :
    if tag x y k < 2 then RawNine else PostNine (picked (tag x y k)) := by
  classical
  let g := rawGate x y k
  obtain ⟨gs,ok,fresh,le⟩ := named_trace xy run hit
  change sufficient vertices7 ans7 (g::gs) at ok
  change freshTrace vertices7 (g::gs) at fresh
  have size : (g::gs).length≤10 := by simp only [List.length_cons]; omega
  have rx : reads g (raw7 x) := Or.inl rfl
  have ry : reads g (raw7 y) := Or.inr rfl
  let t := tag x y k
  change (if t<2 then _ else _)
  have rule := CoThetaSeven.dispatch_rules k x y xy
  change (if t=0 then _ else if t=1 then _ else _) at rule
  by_cases a : t=0
  · rw [if_pos a] at rule
    rw [if_pos (by omega : t<2)]
    have drop : restrict (minorLift x) g.value=absentBit := by
      funext r
      change applyKind k (raw7 x (minorLift x r)) (raw7 y (minorLift x r))=false
      have zero := congrFun (minor_off rule.1) r
      change raw7 x (minorLift x r)=false at zero
      rw [zero]
      exact rule.2 _
    obtain ⟨m,vs,sz,rest,out⟩ := CoThetaSeven.absorbing_head ok fresh size xy rx ry rule.1 drop
    exact ⟨m,vs,by omega,rest,out⟩
  · rw [if_neg a] at rule
    by_cases b : t=1
    · rw [if_pos b] at rule
      rw [if_pos (by omega : t<2)]
      have drop : restrict (minorLift y) g.value=absentBit := by
        funext r
        change applyKind k (raw7 x (minorLift y r)) (raw7 y (minorLift y r))=false
        have zero := congrFun (minor_off rule.1) r
        change raw7 y (minorLift y r)=false at zero
        rw [zero]
        exact rule.2 _
      obtain ⟨m,vs,sz,rest,out⟩ := CoThetaSeven.absorbing_head ok fresh size xy.symm ry rx rule.1 drop
      exact ⟨m,vs,by omega,rest,out⟩
    · rw [if_neg b] at rule
      rw [if_neg (by omega : ¬t<2)]
      let s := rotation t
      let i := picked t
      let pool := (numbered i).value::vertices7
      have eq : restrict (rowPerm s) g.value=(numbered i).value := funext rule
      have old : ∀ w∈g.value::vertices7, restrict (rowPerm s) w∈pool := by
        intro w hw
        rcases List.mem_cons.mp hw with z|h
        · subst w
          rw [eq]
          exact List.mem_cons_self
        rcases List.mem_cons.mp h with z|other
        · subst w
          exact List.mem_cons_of_mem _ List.mem_cons_self
        · obtain ⟨j,hj⟩ := List.mem_ofFn.mp other
          subst w
          rw [CoThetaSeven.raw_permute]
          exact List.mem_cons_of_mem _ (raw_mem _)
      obtain ⟨vs,newRun,sub⟩ := restrict_trace (rowPerm s) gs ok.1.2.2 (Free.start (raw:=pool))
        (List.mem_cons_of_mem _ List.mem_cons_self) old
      have goal := sub ans7 ok.2
      have unchanged : restrict (rowPerm s) ans7=ans7 := funext (CoThetaSeven.perm_graph s)
      rw [unchanged] at goal
      have account := accounted (rowPerm s) gs
      exact ⟨_,vs,by omega,newRun,goal⟩

end CoThetaFixedOrbit
namespace CoThetaCycleFive
open CoThetaFreeCore
open CoThetaBits (Wire Row den gate)
open CoThetaNine (SmallInput raw7 ans7 vertices7 pack unpack numeric_goal)
open CoThetaSeven (read_twice raw_mem)

def roots : List Wire := [
(0xffffffff800ffe003ff800fffffc007ff001ffffffffffe003fffff001ffc007ff001ffc007ff001fffff800ffe003ffffffffffc007ff,0xfffffffd20a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a4148290520a),
(0xfffffffffff000003fffff001ffffffffffe003ff800fffffc007ffffe000007ffffe000007ffffe003ffffffffffc007ff001fffff800,0xfffffffe04c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c0981302604c),
(0x3fffffffe000007fffffffc00000fffffffffffffffffff800000000007fffffffc00000ffffffff800001ffffffff,0x490921242484909212424849092124248490921242484909212424849092124248490921242484909212424849092124248490),
(0xffffffffffffffffc00000000000007fffffffffffff000000007fffffffffffffffffffff80000000000000fffffffffffffe00000000,0xe01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e0),
(0xffffffffffffffffffffffffffffff80000000000000000000007fffffffffffffffffffffffffffffffffff0000000000000000000000,0x700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700)]
def basis : CoNatBench.essentialBasis roots := CoThetaSix.basisAt_sound roots [4, 15, 1, 34, 90] (by decide +kernel)
theorem nd : roots.Nodup := by decide +kernel
theorem small : CoNatBench.guardedSearch 6 (roots.map CoNatBench.project)=false := by decide +kernel

def indexAt (v : Fin 7) : Option Nat := match v.val with
  | 0 => some 0 | 1 => some 1 | 2 => some 2 | 5 => some 3 | 6 => some 4 | _ => none

def column (vertex : Fin 7) : Wire := match indexAt vertex with
  | none => CoThetaBits.zero
  | some n => roots.getD n CoThetaBits.zero
def liftRows (r : Row) : SmallInput := pack (fun j => den (column j) r)

def cycleGraph : Wire :=
  gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj (gate .disj
    (gate .conj (column 0) (column 2)) (gate .conj (column 1) (column 2)))
    (gate .conj (column 0) (column 3))) (gate .conj (column 3) (column 4)))
    (gate .conj (column 1) (column 4))) (gate .conj (column 0) (column 5)))
    (gate .conj (column 5) (column 6))) (gate .conj (column 1) (column 6))


theorem table : cycleGraph=CoThetaBits.target := by decide +kernel

theorem input (j : Fin 7) : restrict liftRows (raw7 j)=den (column j) :=
  funext (fun r => unpack (fun v => den (column v) r) j)

theorem goal : restrict liftRows ans7=den CoThetaBits.target := by
  funext r
  change ans7 (liftRows r)=_
  rw [numeric_goal]
  have values : (fun j => raw7 j (liftRows r))=(fun j => den (column j) r) :=
    funext (fun j => congrFun (input j) r)
  rw [values]
  have equality := congrFun (congrArg den table) r
  simp only [cycleGraph,CoThetaBits.den_gate,applyKind] at equality
  exact equality

theorem known : ∀ w∈vertices7, restrict liftRows w∈absentBit::roots.map den := by
  intro w hw
  rcases List.mem_cons.mp hw with z|r
  · subst w
    exact List.mem_cons_self
  · obtain ⟨j,e⟩ := List.mem_ofFn.mp r
    subst w
    rw [input]
    cases h : indexAt j with
    | none => simp [column,h,CoThetaBits.den_zero]
    | some n =>
      cases hn : roots[n]? with
      | none => simp [column,h,List.getD_eq_getElem?_getD,hn,CoThetaBits.den_zero]
      | some v =>
        have inList := List.mem_map_of_mem (f:=den) (List.mem_of_getElem? hn)
        simp [column,h,List.getD_eq_getElem?_getD,hn,inList]

theorem residual {gs : List (TraceGate SmallInput)} (ok : sufficient vertices7 ans7 gs) :
    7≤remaining liftRows gs := by
  obtain ⟨ws,run,all⟩ := restrict_trace liftRows gs ok.1
    (Free.start (raw:=absentBit::roots.map den)) List.mem_cons_self known
  have h := all ans7 ok.2
  rw [goal] at h
  have yes := CoNatBench.table_bound basis nd run h small
  omega

def joint (a b : Bool) (j : Fin 32) : SmallInput :=
  pack (fun i => if i=3 then a else if i=4 then b else j.val.testBit ((indexAt i).getD 0))

theorem separation : ∀ a b c d : Bool, (a,b)≠(c,d) →
    ∃ j : Fin 32, ans7 (joint a b j)≠ans7 (joint c d j) := by decide +kernel

theorem panel_fixed (a b c d : Bool) (j : Fin 32) :
    agreeOutside (fun f => f=raw7 3 ∨ f=raw7 4) (joint a b j) (joint c d j) vertices7 := by
  intro f hf outside
  rcases List.mem_cons.mp hf with z|other
  · subst f
    rfl
  · obtain ⟨i,e⟩ := List.mem_ofFn.mp other
    subst f
    have i3 : i≠3 := fun e => outside (Or.inl (congrArg raw7 e))
    have i4 : i≠4 := fun e => outside (Or.inr (congrArg raw7 e))
    simp [joint,unpack,i3,i4]

def head : TraceGate SmallInput := ⟨.disj,raw7 3,raw7 4⟩

theorem no_live_ten {gs : List (TraceGate SmallInput)}
    (ok : sufficient vertices7 ans7 (head::gs)) (fresh : freshTrace vertices7 (head::gs))
    (budget : (head::gs).length≤10) :
    ∃ k ws, k≤gs.length ∧ Free vertices7 k ws ∧ ans7∈ws := by
  classical
  have h3 : reads head (raw7 3) := Or.inl rfl
  have h4 : reads head (raw7 4) := Or.inr rfl
  by_cases path : UsePath gs head.value ans7
  · exfalso
    have gone3 := (input 3).trans (show den (column 3)=absentBit from CoThetaBits.den_zero)
    have gone4 := (input 4).trans (show den (column 4)=absentBit from CoThetaBits.den_zero)
    have newp (g : TraceGate SmallInput) (hg : g∈head::gs) :
        g.value≠raw7 3 ∧ g.value≠raw7 4 :=
      ⟨fun e => fresh_outputs fresh g hg (e ▸ raw_mem 3),
       fun e => fresh_outputs fresh g hg (e ▸ raw_mem 4)⟩
    have head0 : restrict liftRows head.value=absentBit := by
      funext r
      change (raw7 3 (liftRows r) || raw7 4 (liftRows r))=false
      have a := congrFun gone3 r
      have b := congrFun gone4 r
      change raw7 3 (liftRows r)=false at a
      change raw7 4 (liftRows r)=false at b
      simp only [a,b,Bool.false_or]
    have nz : restrict liftRows ans7 ≠ absentBit := by
      rw [goal]
      intro e
      have bad := congrFun e (true,0)
      simp [CoThetaBits.den_target,absentBit] at bad
    obtain ⟨other,hm,n3,n4,drop⟩ := extra_loss_on_path liftRows gone3 gone4
      (fun g hg => newp g (List.mem_cons_of_mem _ hg)) path head0
      (newp head List.mem_cons_self) nz
    let all := head::gs
    let R := readerSet all (raw7 3) ∪ readerSet all (raw7 4)
    have card3 {a b c : TraceGate SmallInput} (ha : a∈R) (hb : b∈R) (hc : c∈R)
        (ab : a≠b) (ac : a≠c) (bc : b≠c) : 3≤R.card := by
      have sub : ({a,b,c}:Finset _) ⊆ R := by
        intro g hg
        simp only [Finset.mem_insert,Finset.mem_singleton] at hg
        rcases hg with rfl|rfl|rfl
        · exact ha
        · exact hb
        · exact hc
      have ct := Finset.card_le_card sub
      simpa [ab,ac,bc] using ct
    have from3 {g} (h : g∈all) (p : reads g (raw7 3)) : g∈R :=
      Finset.mem_union_left _ (mem_readerSet.mpr ⟨h,p⟩)
    have from4 {g} (h : g∈all) (p : reads g (raw7 4)) : g∈R :=
      Finset.mem_union_right _ (mem_readerSet.mpr ⟨h,p⟩)
    obtain ⟨A,ha,r3,ah⟩ := read_twice 3 4 (by decide) head h3 h4 ok
    obtain ⟨B,hb,r4,bh⟩ := read_twice 4 3 (by decide) head h4 h3 ok
    have three : 3≤R.card := by
      by_cases same : A=B
      · subst B
        have nraw (j : Fin 7) : ans7≠raw7 j := by
          obtain ⟨r,h⟩ := CoThetaSeven.seven_not_raw j
          exact fun e => h (congrFun e r)
        obtain ⟨row,ne⟩ := CoThetaSeven.seven_diff 3 4 (by decide)
        obtain ⟨C,hc,read,ch,ca⟩ := two_joint_readers_impossible (raw7 3) (raw7 4) ans7
          vertices7 all head A h3 h4 r3 r4 (fun e => ne (congrFun e row))
          ⟨nraw 3,nraw 4⟩ ok.1 ok.2 joint
          (fun a b j => by simp [joint,unpack])
          (fun a b j => by simp [joint,unpack]) panel_fixed separation
        exact card3 (from3 List.mem_cons_self h3) (from3 ha r3)
          (read.elim (from3 hc) (from4 hc)) ah.symm ch.symm ca.symm
      · exact card3 (from3 List.mem_cons_self h3) (from3 ha r3) (from4 hb r4)
          ah.symm bh.symm same
    have saved4 := four_saved_raw_head liftRows all (raw7 3) (raw7 4) gone3 gone4 three
      ⟨other,List.mem_cons_of_mem _ hm,n3,n4,drop⟩
    have cost := residual ok
    have eq := accounted liftRows (head::gs)
    change 4 ≤ saved liftRows (head::gs) at saved4
    omega
  · exact omit_dead_head vertices7 gs head.value ans7 ok.1.2.2 ok.2 path

end CoThetaCycleFive
namespace CoThetaCycleFive
open CoThetaNine (vertices7 ans7)
open CoThetaFreeCore
theorem no_post {n ws} (run : Free (head.value::vertices7) n ws)
    (bound : n≤9) (hit : ans7∈ws) : CoThetaFixedOrbit.RawNine := by
  obtain ⟨gs,ok,fresh,le⟩ := CoThetaFixedOrbit.named_trace (x:=3) (y:=4) (k:=.disj) (by decide) run hit
  have size : (head::gs).length≤10 := by simp only [List.length_cons]; omega
  obtain ⟨j,vs,small,prog,out⟩ := no_live_ten ok fresh size
  exact ⟨j,vs,by omega,prog,out⟩
end CoThetaCycleFive

namespace CoThetaSeven
open CoNatBench CoThetaBits CoThetaFreeCore

def orbitPriority (i : Fin 13) : Nat := ([5,12,11,1,7,4,8,13,6,10,2,9,3] : List Nat).getD i.val 20

def priority (x y : Fin 7) (op : Kind) : Nat :=
  let t := tag x y op
  if t<2 then 0 else orbitPriority (picked t)

private theorem rankLeaf {z : Word} {n p r bound : Nat} (x y : Fin 7) (op : Kind)
    (hit : (z.1==n && z.2==p)=true) (less : r<bound)
    (cert : x≠y ∧ project (gate op (col x) (col y))=(n,p) ∧ priority x y op=r) :
    ∃ (x y : Fin 7) (op : Kind), x≠y ∧ project (gate op (col x) (col y))=z ∧ priority x y op<bound := by
  have eq : z=(n,p) := Prod.ext (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hit).1) (beq_iff_eq.mp (Bool.and_eq_true_iff.mp hit).2)
  exact ⟨x,y,op,cert.1,cert.2.1.trans eq.symm,lt_of_eq_of_lt cert.2.2 less⟩

private theorem rankFork {c : Prop} [Decidable c] {a b bound : Nat} {P : Prop}
    (v : (if c then a else b)<bound) (left : a<bound → P) (right : b<bound → P) : P := by
  by_cases h : c
  · rw [if_pos h] at v
    exact left v
  · rw [if_neg h] at v
    exact right v

private theorem rankMatch {c : Bool} {r bound : Nat} {P : Prop}
    (v : (if c then r else 20)<bound) (cap : bound≤13) (take : c=true → r<bound → P) : P := by
  cases c with
  | false => change 20<bound at v; omega
  | true => exact take rfl v

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem rankSignal_sound (bound : Nat) (cap : bound≤13) (z : Word) (bad : rankSignal z<bound) :
    ∃ (x y : Fin 7) (op : Kind), x≠y ∧ project (gate op (col x) (col y))=z ∧ priority x y op<bound := by
  unfold rankSignal at bad
  exact (rankFork bad
    (fun bad => (rankFork bad
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .leftOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .leftOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .leftOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .leftOnly hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .leftOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .rightOnly hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .leftOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .leftOnly hit smaller (by decide +kernel))))))))))))))
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .leftOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .leftOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .leftOnly hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .rightOnly hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .rightOnly hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .rightOnly hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .rightOnly hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .rightOnly hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .rightOnly hit smaller (by decide +kernel))))))))))))))))
    (fun bad => (rankFork bad
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .conj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .conj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .conj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .conj hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 1 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .conj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 2 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 2 .disj hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .conj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .conj hit smaller (by decide +kernel))))))))))))))
      (fun bad => (rankFork bad
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 3 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 3 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 3 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .conj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .conj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 4 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 4 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 4 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 4 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .conj hit smaller (by decide +kernel))))))))))))
        (fun bad => (rankFork bad
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 5 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 5 .disj hit smaller (by decide +kernel))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 5 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 5 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 5 .disj hit smaller (by decide +kernel))))))))))
          (fun bad => (rankFork bad
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 0 6 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 1 6 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 2 6 .disj hit smaller (by decide +kernel))))))))
            (fun bad => (rankFork bad
              (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 3 6 .disj hit smaller (by decide +kernel))))
              (fun bad => (rankFork bad
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 4 6 .disj hit smaller (by decide +kernel))))
                (fun bad => (rankMatch bad cap (fun hit smaller => rankLeaf 5 6 .disj hit smaller (by decide +kernel)))))))))))))))))
end CoThetaSeven

namespace CoThetaFreeCore
variable {ρ : Type}

theorem free_compose {raw us ws : List (ρ→Bool)} {m n} (pre : Free raw m us) (post : Free us n ws) : Free raw (m+n) ws := by
  induction post with
  | start => simpa using pre
  | binary _ op ha hb ih => exact .binary ih op ha hb

end CoThetaFreeCore

namespace CoThetaSeven
open CoThetaFreeCore CoNatBench
open CoThetaNine (SmallInput raw7 vertices7 ans7 toRows numeric_target)
open CoThetaBits (den col gate)

def sampleCodes : List Nat := [0, 1, 2, 3, 4, 440, 453, 466, 37, 474, 18, 485, 5, 493, 498, 507, 40, 6, 510, 521, 7, 528, 537, 541, 544, 557, 562, 567, 570, 580, 583, 586, 151, 587, 21, 597, 8, 604, 609, 617, 113, 620, 52, 624, 9, 626, 627, 633, 79, 634, 641, 649, 94, 653, 655, 657, 658, 667, 670, 672, 673, 680, 681, 682, 155, 10, 683, 693, 11, 700, 708, 712, 44, 715, 723, 730, 66, 734, 736, 738, 116, 87, 739, 743, 12, 745, 751, 752, 753, 762, 764, 767, 768, 775, 776, 777, 778, 791, 795, 799, 802, 812, 815, 818, 819, 828, 831, 833, 834, 841, 842, 843, 844, 853, 855, 858, 859, 866, 867, 868, 869, 873, 874, 875, 876, 877, 878, 879]
def inverseRow (r : SmallInput) : CoThetaBits.Row :=
  let q := sampleCodes.getD r.val 0
  (decide (440≤q),⟨q % 440,Nat.mod_lt _ (by decide)⟩)

theorem sample_surjective : ∀ r : SmallInput, toRows (inverseRow r)=r := by decide +kernel

theorem reflect_rows {f g : SmallInput→Bool} (h : restrict toRows f=restrict toRows g) : f=g := by
  funext r
  have e := congrFun h (inverseRow r)
  change f (toRows (inverseRow r))=g (toRows (inverseRow r)) at e
  simpa only [sample_surjective] using e

theorem raw_gate_sample (x y : Fin 7) (op : Kind) :
    restrict toRows (CoThetaFixedOrbit.rawGate x y op).value=den (gate op (col x) (col y)) := by
  rw [CoThetaBits.den_gate]
  funext r
  change applyKind op (raw7 x (toRows r)) (raw7 y (toRows r))=_
  rw [show raw7 x (toRows r)=den (col x) r from congrFun (proj_raw x) r,
    show raw7 y (toRows r)=den (col y) r from congrFun (proj_raw y) r]

theorem raw_gate_fresh (op : Kind) : ∀ x y : Fin 7, x≠y → (CoThetaFixedOrbit.rawGate x y op).value∉vertices7 := by
  cases op <;> decide +kernel

theorem reject_raw (r9 : RawNine) : ¬ CoThetaFixedOrbit.RawNine := by
  rintro ⟨h,ys,cost,reduced,goal⟩
  let raw0 := vertices7.map (restrict toRows)
  have zero : absentBit∈raw0 := List.mem_cons_self
  have endw := List.mem_map_of_mem (f:=restrict toRows) goal
  rw [numeric_target] at endw
  obtain ⟨m,S,le,live,sub⟩ := rewind (reduced.map_rows toRows) zero
    (Live.stop (goal:=den CoThetaBits.target)) (fun w e => e.symm ▸ endw)
  have rep := CoThetaBits.root_rep live (by
    intro f hf
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp (sub f hf)
    subst f
    rcases List.mem_cons.mp hw with z|l
    · subst w
      exact Or.inl rfl
    · obtain ⟨j,e⟩ := List.mem_ofFn.mp l
      subst w
      exact Or.inr ⟨j,(proj_raw j).symm⟩)
  exact r9 live (by omega) rep

theorem numbered_start (i : Fin 13) : Free vertices7 1 ((numbered i).value::vertices7) :=
  .binary .start _ (raw_mem (casesA.getD i.val 0)) (raw_mem (casesB.getD i.val 0))

theorem orbit_cap : ∀ i : Fin 13, orbitPriority i≤13 := by decide +kernel

theorem prove_post (r9 : RawNine) (checks : ∀ i : Fin 13, i≠10 → ∀ j : Fin 448,
    permitPrefix (orbitPriority i) (numbers.getD i.val 0) j.val=true) : ∀ i, ¬CoThetaFixedOrbit.PostNine i := by
  have byrank : ∀ t : Nat, ∀ i : Fin 13, orbitPriority i=t → ¬CoThetaFixedOrbit.PostNine i := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro i key post
      obtain ⟨n,ws,small,run,out⟩ := post
      by_cases five : i=10
      · subst i
        exact reject_raw r9 (CoThetaCycleFive.no_post run small out)
      apply safe_after r9 (orbitPriority i) i (checks i five) run small out
      intro f hf v eq
      by_contra no
      have low : rankSignal (project v)<orbitPriority i := by omega
      obtain ⟨x,y,k,xy,word,earlier⟩ := rankSignal_sound _ (orbit_cap i) _ low
      have same : (CoThetaFixedOrbit.rawGate x y k).value=f := by
        apply reflect_rows
        rw [raw_gate_sample,project_inj word,eq]
      have whole := free_compose (numbered_start i) run
      obtain ⟨m,ys,cap,moved,sub⟩ := free_move whole hf (same ▸ raw_gate_fresh k x y xy)
      rw [←same] at moved
      have alt := CoThetaFixedOrbit.dispatch x y k xy moved (by omega) (sub _ out)
      by_cases bad : tag x y k<2
      · rw [if_pos bad] at alt
        exact reject_raw r9 alt
      · rw [if_neg bad] at alt
        have lt : orbitPriority (picked (tag x y k))<t := by simpa [priority,bad,key] using earlier
        exact ih _ lt _ rfl alt
  intro i
  exact byrank _ i rfl

theorem lower_from_ranked (r9 : RawNine) (checks : ∀ i : Fin 13, i≠10 → ∀ b : Fin 38,
    permitBlock (orbitPriority i) (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true)
    {n ws} (run : Free vertices7 n ws) (out : ans7∈ws) : 11≤n := by
  by_contra bad
  rcases select_program run (by omega) out with raw|⟨i,post⟩
  · exact reject_raw r9 raw
  · exact prove_post r9 (fun i ne => marked_blocks _ i (checks i ne)) i post

end CoThetaSeven

namespace CoThetaNine
open CoThetaFreeCore

noncomputable local instance {ρ : Type} : DecidableEq (TraceGate ρ) := Classical.decEq _

def or04 : TraceGate Input := ⟨.disj,vtx 0,vtx 4⟩
end CoThetaNine

namespace CoThetaNine
open CoThetaFreeCore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

end CoThetaNine


namespace CoThetaFreeCore

variable {ρ : Type}

inductive PinForm where
  | constant (v : Bool)
  | copy (i : Nat)
  | inv (i : Nat)
  | binary (join : Bool) (i j : Nat)

def PinForm.value : PinForm → List (ρ→Bool) → (ρ→Bool)
  | .constant v, _ => fun _ => v
  | .copy i, w => w.getD i absentBit
  | .inv i, w => fun r => !(w.getD i absentBit r)
  | .binary join i j, w => fun r => base join (w.getD i absentBit r) (w.getD j absentBit r)

def PinForm.binaryCost : PinForm → Nat
  | .binary _ _ _ => 1
  | _ => 0

def cost : List PinForm → Nat
  | [] => 0
  | f::fs => f.binaryCost + cost fs

def execute : List PinForm → List (ρ→Bool) → List (ρ→Bool)
  | [], w => w
  | f::fs, w => execute fs (w ++ [f.value w])

private theorem read_registered (w pool : List (ρ→Bool)) (i : Nat) (hz : absentBit∈pool)
    (known : ∀ v∈w, v∈pool) : w.getD i absentBit∈pool := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact hz
  | some a => exact known a (List.mem_of_getElem? h)

private theorem pin_step (f : PinForm) (w pool raw : List (ρ→Bool)) (n : Nat)
    (pre : Ordinary raw n pool) (consts : ∀ b : Bool, (fun _ : ρ => b) ∈ pool)
    (known : ∀ v∈w, v∈pool) :
    ∃ ys, Ordinary raw (n+f.binaryCost) ys ∧
      (∀ v∈pool, v∈ys) ∧ f.value w∈ys := by
  have reg := read_registered w pool
  have hz : absentBit∈pool := consts false
  cases f with
  | constant v => exact ⟨pool,pre,fun _ h => h,consts _⟩
  | copy i => exact ⟨pool,pre,fun _ h => h,reg i hz known⟩
  | inv i =>
    exact ⟨_, Ordinary.inv pre (reg i hz known),
      fun _ h => List.mem_cons_of_mem _ h,by simp [PinForm.value]⟩
  | binary join i j =>
    exact ⟨_, Ordinary.binary pre join (reg i hz known) (reg j hz known),
      fun _ h => List.mem_cons_of_mem _ h,by simp [PinForm.value]⟩

theorem pins_to_program (fs : List PinForm) (w pool raw : List (ρ→Bool)) (n : Nat)
    (pre : Ordinary raw n pool) (consts : ∀ b : Bool, (fun _ : ρ => b) ∈ pool)
    (known : ∀ v∈w, v∈pool) :
    ∃ ys, Ordinary raw (n+cost fs) ys ∧ ∀ v∈execute fs w, v∈ys := by
  induction fs generalizing w pool n with
  | nil => exact ⟨_,pre,known⟩
  | cons f fs ih =>
    obtain ⟨mid,hmid,old,hw⟩ := pin_step f w pool raw n pre consts known
    have available (v) (h : v∈w++[f.value w]) : v∈mid := by
      rcases List.mem_append.mp h with original | fresh
      · exact old _ (known _ original)
      · exact (congrArg (fun u => u∈mid) (List.mem_singleton.mp fresh)).mpr hw
    obtain ⟨ys,hy,sub⟩ := ih (w++[f.value w]) mid (n+f.binaryCost) hmid
      (fun b => old _ (consts b)) available
    exact ⟨ys,by simpa [cost,Nat.add_assoc] using hy,sub⟩

end CoThetaFreeCore

namespace CoThetaPhysical
open CoThetaFreeCore PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gateForm (g : Gate) : PinForm :=
  match g.op, g.inputs with
  | .and, [] => .constant true
  | .or, [] => .constant false
  | .not, [] => .constant true
  | .and, [i] | .or, [i] => .copy i
  | .not, i::_ => .inv i
  | .and, i::j::_ => .binary false i j
  | .or, i::j::_ => .binary true i j
  | _, _ => .constant false

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length≤2

private theorem read_word {ρ : Type} (w : List (ρ→Bool)) (i : Nat) (r : ρ) :
    ((w.map (fun f => f r)).getD i false) = w.getD i absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[i]? <;> rfl

private theorem read_option {ρ : Type} (o : Option (ρ→Bool)) (r : ρ) :
    (o.map (fun f => f r)).getD false = o.getD absentBit r := by cases o <;> rfl

theorem form_agrees {ρ : Type} (g : Gate) (hg : legal g) (w : List (ρ→Bool)) (r : ρ) :
    (gateForm g).value w r =
    g.op.eval (g.inputs.map fun i => (w.map (fun f => f r)).getD i false) := by
  obtain ⟨op,pins⟩ := g
  obtain ⟨hop,hlen⟩ := hg
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
  change op=GateOp.and ∨ op=GateOp.or ∨ op=GateOp.not at hop
  change pins.length≤2 at hlen
  rcases hop with rfl | rfl | rfl <;>
    cases pins with
    | nil => rfl
    | cons i xs =>
      cases xs with
      | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
      | cons j t =>
        cases t with
        | nil => simp [gateForm,PinForm.value,GateOp.eval,base,read_word,read_option]
        | cons h t => simp at hlen

theorem map_execute {ρ : Type} (gs : List Gate) (w : List (ρ→Bool)) (r : ρ)
    (hg : ∀ g∈gs, legal g) :
    (execute (gs.map gateForm) w).map (fun f => f r) =
    gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)])
      (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,execute,List.foldl_cons]
    rw [ih _ (fun a ha => hg a (List.mem_cons_of_mem _ ha))]
    simp [form_agrees g (hg _ (by simp)) w r]

theorem circuit_rows {ρ : Type} (C : Circuit) (hf : FanInTwo C) (w : List (ρ→Bool)) (r : ρ) :
    (execute (C.gates.map gateForm) w).map (fun f => f r) = C.wires (w.map (fun f => f r)) :=
  map_execute C.gates w r hf

end CoThetaPhysical

namespace CoThetaFreeCore

theorem pin_cost_length (fs : List PinForm) : cost fs≤fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    cases f <;> simp only [cost,PinForm.binaryCost,List.length_cons] <;> omega

end CoThetaFreeCore

namespace CoThetaNine
open CoThetaFreeCore CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def rawOrHead : TraceGate Input := ⟨.disj,vtx 0,vtx 4⟩
def prefixInputs : List (Input→Bool) := List.ofFn vtx ++ [rawOrHead.value]
def seed : List (Input→Bool) := absentBit::(fun _ => true)::prefixInputs

end CoThetaNine

namespace CoThetaProofData
open CoNatBench CoThetaSeven
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem raw_all (i : Fin 84) : guardedSearch 8 (firstWords i.val)=false := by
  fin_cases i <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block0 (b : Fin 38) : permitBlock 5 0 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block1 (b : Fin 38) : permitBlock 12 1 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block2 (b : Fin 38) : permitBlock 11 2 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block5 (b : Fin 38) : permitBlock 1 5 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block6 (b : Fin 38) : permitBlock 7 6 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block9 (b : Fin 38) : permitBlock 4 9 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block10 (b : Fin 38) : permitBlock 8 10 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block13 (b : Fin 38) : permitBlock 13 13 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block14 (b : Fin 38) : permitBlock 6 14 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block45 (b : Fin 38) : permitBlock 10 45 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block65 (b : Fin 38) : permitBlock 9 65 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
set_option maxRecDepth 6000 in
set_option maxHeartbeats 0 in
theorem block69 (b : Fin 38) : permitBlock 3 69 (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases b <;> decide +kernel
theorem all_blocks (i : Fin 13) (ne : i≠10) (b : Fin 38) : permitBlock (orbitPriority i) (numbers.getD i.val 0) (12*b.val) (min 12 (448-12*b.val))=true := by
  fin_cases i
  · exact block0 b
  · exact block1 b
  · exact block2 b
  · exact block5 b
  · exact block6 b
  · exact block9 b
  · exact block10 b
  · exact block13 b
  · exact block14 b
  · exact block45 b
  · exact (ne rfl).elim
  · exact block65 b
  · exact block69 b
end CoThetaProofData

namespace CoThetaSeven

theorem checked_lower : CoThetaNine.SignedLower :=
  fun run out => lower_from_ranked (root_from_cases CoThetaProofData.raw_all) CoThetaProofData.all_blocks run out

end CoThetaSeven

namespace Co1940Physical
open CoThetaNine CoThetaFreeCore CoThetaPhysical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def firstBank : List (Input→Bool) := List.ofFn vtx ++ [fun r => !(vtx 0 r)]
def secondNot (pins : List Nat) : Input→Bool := fun r =>
  GateOp.not.eval (pins.map fun i => firstBank.getD i absentBit r)
def rawBank (pins : List Nat) := firstBank ++ [secondNot pins]
def bank (pins : List Nat) := absentBit::(fun _ : Input => true)::rawBank pins

private theorem invNorm (f : Input→Bool) :
    norm (row 0) (fun r => !(f r)) = norm (row 0) f := by
  funext r
  cases a : f (row 0) <;> cases b : f r <;> simp [CoThetaFreeCore.norm,phase,a,b]

private theorem vertexNorm (i : Fin 9) : norm (row 0) (vtx i)∈vertices := by
  have z : ∀ j : Fin 9, vtx j (row 0)=false := by decide
  have eq : norm (row 0) (vtx i)=vtx i := by
    funext r
    simp [CoThetaFreeCore.norm,phase,z]
  rw [eq]
  exact List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem knownFirst (w : Input→Bool) (h : w∈firstBank) : norm (row 0) w∈vertices := by
  rcases List.mem_append.mp h with raw|inv
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp raw
    exact vertexNorm i
  · obtain rfl := List.mem_singleton.mp inv
    rw [invNorm]
    exact vertexNorm 0

theorem knownBank (pins : List Nat) :
    ∀ w∈(bank pins).map (norm (row 0)), w∈vertices := by
  intro w h
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
  rcases List.mem_cons.mp ht with rfl|ht
  · exact List.mem_cons_self
  rcases List.mem_cons.mp ht with rfl|ht
  · exact List.mem_cons_self
  rcases List.mem_append.mp ht with hold|hlast
  · exact knownFirst _ hold
  obtain rfl := List.mem_singleton.mp hlast
  cases pins with
  | nil => exact List.mem_cons_self
  | cons p ps =>
    change norm (row 0) (fun r => !(firstBank.getD p absentBit r))∈vertices
    rw [invNorm]
    cases e : firstBank[p]? with
    | none =>
      simp only [List.getD_eq_getElem?_getD,e,Option.getD_none]
      exact List.mem_cons_self
    | some w =>
      simp only [List.getD_eq_getElem?_getD,e,Option.getD_some]
      exact knownFirst w (List.mem_of_getElem? e)

theorem rows_read (w : List (Input→Bool)) (j : Nat) (r : Input) :
    (w.map (fun f => f r)).getD j false = w.getD j absentBit r := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? <;> rfl

end Co1940Physical

namespace Co2928
open CoThetaNine CoThetaFreeCore CoThetaPhysical Co1940Physical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem costSaving (gates : List Gate) (has : ∃ g ∈ gates, g.op = GateOp.not) :
    cost (gates.map gateForm) < gates.length := by
  induction gates with
  | nil => simp at has
  | cons g gs ih =>
    obtain ⟨h, hh, ho⟩ := has
    rcases List.mem_cons.mp hh with eq|mem
    · subst h
      have z : (gateForm g).binaryCost = 0 := by
        cases g with
        | mk op pins =>
          change op = GateOp.not at ho
          subst op
          cases pins <;> rfl
      have bound := pin_cost_length (gs.map gateForm)
      simp only [List.length_map] at bound
      simp only [List.map_cons, cost, z, Nat.zero_add, List.length_cons]
      omega
    · have smaller := ih ⟨h,mem,ho⟩
      have unit : (gateForm g).binaryCost ≤ 1 := by cases gateForm g <;> simp [PinForm.binaryCost]
      simp only [List.map_cons,cost,List.length_cons]
      omega

theorem firstBankRows (r : Input) :
    firstBank.map (fun f => f r) = List.ofFn (fun i => vtx i r) ++ [!(vtx 0 r)] := by
  simp [firstBank,List.map_ofFn]

def seed (i j : Fin 11) : PinForm :=
  if i = 10 then .copy j.val else if j = 10 then .copy i.val
  else if i = j then .copy i.val
  else if (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0) then .constant true
  else .binary true i.val j.val

theorem seedValue (i j : Fin 11) (r : Input) :
    (seed i j).value firstBank r =
      (firstBank.getD i.val absentBit r || firstBank.getD j.val absentBit r) := by
  have missing : firstBank.getD 10 absentBit r = false := by rfl
  by_cases a : i=10
  · subst i
    simp [seed,PinForm.value,missing]
  by_cases b : j=10
  · subst j
    simp [seed,PinForm.value,a,missing]
  by_cases c : i=j
  · subst j
    simp [seed,PinForm.value,a]
  by_cases k : (i=0 ∧ j=9) ∨ (i=9 ∧ j=0)
  · rcases k with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · change true = (vtx 0 r || !(vtx 0 r))
      cases vtx 0 r <;> rfl
    · change true = (!(vtx 0 r) || vtx 0 r)
      cases vtx 0 r <;> rfl
  · simp [seed,a,b,c,k,PinForm.value,base]

theorem seedBound (i j : Fin 11) : (seed i j).binaryCost ≤ 1 := by
  cases seed i j <;> simp [PinForm.binaryCost]

theorem orTrace (i j : Fin 11) (D : Circuit) (fan : FanInTwo D)
    (correct : ∀ r : Input, let z := List.ofFn (fun i => vtx i r) ++ [!(vtx 0 r)]
      D.eval (z ++ [z.getD i false || z.getD j false]) = ans r) :
    ∃ gs, gs.length = (seed i j).binaryCost + cost (D.gates.map gateForm) ∧ sufficient vertices ans gs := by
  let qo := seed i j
  let start := firstBank ++ [qo.value firstBank]
  let fs := D.gates.map gateForm
  let result := (execute fs start).getD D.output absentBit
  have word : result = ans := by
    funext r
    have ev := congrArg (fun w : List Bool => w.getD D.output false) (circuit_rows D fan start r)
    change ((execute fs start).map (fun f => f r)).getD D.output false = _ at ev
    rw [rows_read] at ev
    change result r = D.eval (start.map (fun f => f r)) at ev
    rw [ev]
    have cs := correct r
    dsimp only at cs
    rw [←firstBankRows r] at cs
    simpa only [start, qo, List.map_append,List.map_cons,List.map_nil,seedValue,rows_read] using cs
  have hm : result ∈ execute fs start := by
    cases e : (execute fs start)[D.output]? with
    | none =>
      have z : result = absentBit := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (ans_not_zero (word.symm.trans z)).elim
    | some w =>
      have eq : result = w := by simp [result,List.getD_eq_getElem?_getD,e]
      exact (congrArg (fun v => v ∈ execute fs start) eq).mpr (List.mem_of_getElem? e)
  have cs (b : Bool) : (fun _ : Input => b) ∈ bank [] := by
    cases b
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  have initial (v) (hv : v ∈ firstBank) : v ∈ bank [] := by
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hv))
  obtain ⟨ws,program,coverage⟩ := pins_to_program (qo::fs) firstBank (bank []) (bank []) 0 Ordinary.start cs initial
  have atResult := coverage _ hm
  obtain ⟨ys,free,sub⟩ := simulate_all_wires (row 0) program
  have ng : norm (row 0) ans = ans := by
    have z : ans (row 0) = false := by decide
    funext r
    simp [CoThetaFreeCore.norm,phase,z]
  have goal := sub _ atResult
  rw [word,ng] at goal
  obtain ⟨gs,len,reg,eq⟩ := trace_of_free free
  have use := trace_subset gs (knownBank [])
  exact ⟨gs,by simpa only [Nat.zero_add,cost,qo,fs] using len,use.1 reg,use.2 _ (eq ▸ goal)⟩

theorem entryBit (r : Input) (i : Fin 9) :
    (BitVec.ofFin r : BitVec 9).getLsbD i.val = vtx i r := by rfl

def graphResult (x : Fin 9 → Bool) : Bool :=
  [((0 : Fin 9), (1 : Fin 9)), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)].any
    (fun e => x e.1 && x e.2)

theorem graphRow : ∀ r : Input, graphResult (fun i => vtx i r) = ans r := by decide +kernel

theorem signedTail (i j : Fin 11) (D : Circuit) (hf : FanInTwo D) (hs : D.size ≤ 13)
    (saving : D.size ≤ 12 ∨ (∃ g ∈ D.gates, g.op = GateOp.not) ∨ cost (D.gates.map gateForm) ≤ 12 ∨ i = j ∨ i = 10 ∨ j = 10 ∨ (i = 0 ∧ j = 9) ∨ (i = 9 ∧ j = 0)) :
    ∃ b : BitVec 9,
      let x : Fin 9 → Bool := fun k => b.getLsbD k.val
      let z := List.ofFn x ++ [!(x 0)]
      D.eval (z ++ [z.getD i.val false || z.getD j.val false]) ≠ graphResult x := by
  classical
  by_contra! all
  have works (r : Input) : let z := List.ofFn (fun i => vtx i r) ++ [!(vtx 0 r)]
      D.eval (z ++ [z.getD i.val false || z.getD j.val false]) = ans r := by
    have h := all (BitVec.ofFin r)
    dsimp only at h ⊢
    simpa only [entryBit,graphRow] using (Classical.not_not.mp h)
  obtain ⟨gs, len, ok⟩ := orTrace i j D hf works
  have lo := any_nine_lower CoThetaSeven.checked_lower ok
  have lim : cost (D.gates.map gateForm) ≤ 13 := (by simpa only [List.length_map] using pin_cost_length (D.gates.map gateForm) : cost (D.gates.map gateForm) ≤ D.gates.length).trans hs
  have seedLimit := seedBound i j
  by_cases zero : (seed i j).binaryCost = 0
  · omega
  have bound : cost (D.gates.map gateForm) ≤ 12 := by
    rcases saving with size|reader|direct|degenerate
    · have k := pin_cost_length (D.gates.map gateForm)
      simp only [List.length_map] at k
      exact k.trans size
    · have k := costSaving D.gates reader
      change D.gates.length ≤ 13 at hs
      omega
    · exact direct
    · exfalso
      have h : ∀ (a b : Fin 11), a=b ∨ a=10 ∨ b=10 ∨ (a=0 ∧ b=9) ∨ (a=9 ∧ b=0) → (seed a b).binaryCost=0 := by decide
      exact zero (h i j degenerate)
  omega

end Co2928


namespace Mono2928
abbrev Wire := Nat × Nat × Nat

def bits {α : Type} (xs : List α) (p : α → Bool) : Nat :=
  xs.foldr (fun x n => 2 * n + (p x).toNat) 0

def edges : List (Nat × Nat) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def edge (r : Nat) : Bool := edges.any fun e => r.testBit e.1 && r.testBit e.2
def pos : List Nat := [3,6,12,13,17,24,33,66,132,133,160,264,265,288,320,321]
def neg : List Nat := [42,50,69,104,116,138,200,201,208,261,276,385,402]
def samples : List (Nat × Nat) := pos.flatMap fun a => neg.map fun b => (a,b)
def table (p : Nat → Bool) := bits (List.range 512) p
def pack (p : Nat → Bool) : Wire := (table p, bits samples (fun s => p s.1), bits samples (fun s => p s.2))
def inputs : List Wire := (List.range 9).map (fun j => pack fun r => r.testBit j) ++ [pack fun r => !(r.testBit 0)]
def target := table edge
def top512 : Nat := 2^512-1
def top208 : Nat := 2^208-1
def cuts : List (Nat × Nat) := [(0,4),(1,6),(2,7),(3,4),(8,6),(5,7)]
def masks : List Nat := cuts.map fun c => table fun r => !(r.testBit c.1 || r.testBit c.2)
def gate (d : Bool) (a b : Wire) : Wire :=
  if d then (a.1 ||| b.1,a.2.1 ||| b.2.1,a.2.2 ||| b.2.2)
  else (a.1 &&& b.1,a.2.1 &&& b.2.1,a.2.2 &&& b.2.2)

def covered (v : List Wire) : Bool :=
  v.foldl (fun t w => t ||| (w.2.1 &&& (top208 ^^^ w.2.2))) 0 == top208
def picks {α : Type} : List α → List (α × List α)
  | [] => []
  | x :: xs => (x,xs) :: (picks xs).map (fun t => (t.1,x :: t.2))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | x :: xs => (picks xs).map (fun t => (x,t.1,t.2)) ++
    (pairs xs).map (fun t => (t.1,t.2.1,x :: t.2.2))

def collapses (m : Nat) (a b z : Wire) : Bool :=
  let f := z.1 &&& m
  f == 0 || f == m || f == a.1 &&& m || f == b.1 &&& m
def charge (a b z : Wire) (spent : List Nat) : List Nat :=
  List.zipWith (fun m c => c + (collapses m a b z).toNat) masks spent
def constants (m : Nat) (v : List Wire) : Nat :=
  v.countP fun w => (w.1 &&& m) == 0 || (w.1 &&& m) == m
def allowed (k : Nat) (v : List Wire) (s : List Nat) : Bool :=
  decide (v.length ≤ k+1) && covered v &&
  (masks.zip s).all (fun p => decide (p.2 + constants p.1 v ≤ 3))
def keeps (a b z : Wire) (rest : List Wire) : List (List Wire) :=
  [z::rest, z::a::rest, z::b::rest, z::a::b::rest]
def fresh (z : Wire) (v : List Wire) : Bool :=
  !(z.1 == 0 || z.1 == top512 || v.any (fun w => w.1 == z.1))
def next (k : Nat) (v : List Wire) (spent : List Nat) : List (List Wire × List Nat) :=
  (pairs v).flatMap fun t => [false,true].flatMap fun d =>
    let a := t.1
    let b := t.2.1
    let z := gate d a b
    let s := charge a b z spent
    if fresh z v then
      ((keeps a b z t.2.2).filter fun u => allowed k u s).map fun u => (u,s)
    else []
def search : Nat → List Wire → List Nat → Bool
  | 0,v,_ => v.any fun w => w.1 == target
  | k+1,v,s => (v.any fun w => w.1 == target) || (next k v s).any (fun p => search k p.1 p.2)
def initial : List Nat := [0,0,0,0,0,0]
def roots := inputs.sublists.filter covered
end Mono2928



namespace Mono2928

inductive ValidTrace {W : Type} [DecidableEq W] (gate : Bool → W → W → W) (goal : W) :
    Finset W → List (Bool × W × W) → Prop where
  | stop : ValidTrace gate goal {goal} []
  | step {U} {a b : W} {d : Bool} {gs} (ne : a ≠ b)
      (fresh : gate d a b ∉ insert a (insert b U))
      (tail : ValidTrace gate goal (insert (gate d a b) U) gs) :
      ValidTrace gate goal (insert a (insert b U)) ((d,a,b)::gs)

section
variable {W : Type} [DecidableEq W] {gate : Bool → W → W → W} {goal : W}

theorem trace_length_bound {S gs} (h : ValidTrace gate goal S gs) : S.card ≤ gs.length + 1 := by
  induction h with
  | stop => simp
  | @step U a b d gs ne fresh tail ih =>
    have zU : gate d a b ∉ U := fun hz => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
    rw [Finset.card_insert_of_notMem zU] at ih
    have ab := Finset.card_insert_le a (insert b U)
    have bc := Finset.card_insert_le b U
    simp only [List.length_cons]
    omega

theorem trace_has_separator {S gs} (h : ValidTrace gate goal S gs)
    (test : W → Prop) (hg : test goal)
    (hgates : ∀ d a b, test (gate d a b) → test a ∨ test b) :
    ∃ w ∈ S, test w := by
  induction h with
  | stop => exact ⟨goal, by simp, hg⟩
  | @step U a b d gs ne fresh tail ih =>
    obtain ⟨w,hm,ht⟩ := ih
    obtain rfl | mem := Finset.mem_insert.mp hm
    · obtain ha | hb := hgates _ _ _ ht
      · exact ⟨a, by simp, ha⟩
      · exact ⟨b, by simp, hb⟩
    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem), ht⟩

theorem trace_const_bound {S gs} (h : ValidTrace gate goal S gs)
    (isConst : W → Bool) (lost : Bool × W × W → Bool)
    (target_nonconst : isConst goal = false)
    (either : ∀ d a b, (isConst a = true ∨ isConst b = true) → lost (d,a,b) = true)
    (both : ∀ d a b, isConst a = true → isConst b = true → isConst (gate d a b) = true) :
    (S.filter fun w => isConst w).card ≤ (gs.filter lost).length := by
  induction h with
  | stop => simp [target_nonconst]
  | @step U a b d gs ne fresh tail ih =>
    let z := gate d a b
    have zU : z ∉ U := fun hz => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
    let V := U.filter fun w => isConst w
    have zv : z ∉ V := fun hz => zU (Finset.mem_filter.mp hz).1
    have card1 := Finset.card_insert_le a (insert b V)
    have card2 := Finset.card_insert_le b V
    have cardA := Finset.card_insert_le a V
    have aux : V.card ≤ ((insert z U).filter fun w => isConst w).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    change ((insert z U).filter fun w => isConst w).card ≤ _ at ih
    cases ha : isConst a <;> cases hb : isConst b
    · simp only [Finset.filter_insert, ha, hb, Bool.false_eq_true, ↓reduceIte]
      cases e : lost (d,a,b) <;> simp [List.filter_cons,e] <;> change V.card ≤ _ <;> omega
    · have l := either d a b (Or.inr hb)
      simp only [Finset.filter_insert, ha, hb, Bool.false_eq_true, ↓reduceIte, List.filter_cons_of_pos l,List.length_cons]
      change (insert b V).card ≤ _
      omega
    · have l := either d a b (Or.inl ha)
      simp only [Finset.filter_insert, ha, hb, Bool.false_eq_true, ↓reduceIte, List.filter_cons_of_pos l,List.length_cons]
      change (insert a V).card ≤ _
      omega
    · have l := either d a b (Or.inl ha)
      have zz : isConst z = true := both d a b ha hb
      simp only [Finset.filter_insert,zz,↓reduceIte] at ih
      change (insert z V).card ≤ _ at ih
      rw [Finset.card_insert_of_notMem zv] at ih
      simp only [Finset.filter_insert, ha, hb, ↓reduceIte, List.filter_cons_of_pos l,List.length_cons]
      change (insert a (insert b V)).card ≤ _
      omega

end
end Mono2928


namespace Mono2928

theorem picks_spec {α : Type} {v : List α} {a : α} (hm : a ∈ v) :
    ∃ r, (a,r) ∈ picks v ∧ v.Perm (a::r) := by
  induction v with
  | nil => simp at hm
  | cons x xs ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨xs, by simp [picks], List.Perm.refl _⟩
    · obtain ⟨r,hp,hr⟩ := ih hm
      refine ⟨x::r,List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,r),hp,rfl⟩),?_⟩
      exact (hr.cons x).trans (.swap _ _ _)

theorem pairs_spec {α : Type} {v : List α} {a b : α}
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    ∃ r, ((a,b,r) ∈ pairs v ∨ (b,a,r) ∈ pairs v) ∧ v.Perm (a::b::r) := by
  induction v with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · obtain ⟨r,h,hr⟩ := picks_spec ((List.mem_cons.mp hb).resolve_left (Ne.symm hab))
      exact ⟨r,Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),h,rfl⟩)),hr.cons a⟩
    · rcases List.mem_cons.mp hb with rfl | hb
      · obtain ⟨r,h,hr⟩ := picks_spec (v := xs) ((List.mem_cons.mp ha).resolve_left hab)
        exact ⟨r,Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),h,rfl⟩)),
          (hr.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r,h,hr⟩ := ih ha hb
        refine ⟨x::r,?_,(hr.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _))⟩
        rcases h with h | h
        · exact Or.inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),h,rfl⟩))
        · exact Or.inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),h,rfl⟩))

theorem selected_keep [DecidableEq α] {v r : List α} {a b z : α} {U : Finset α}
    (vnodup : v.Nodup) (p : v.Perm (a::b::r))
    (hset : v.toFinset = insert a (insert b U))
    (fresh : z ∉ v.toFinset) :
    ∃ u ∈ [z::r,z::a::r,z::b::r,z::a::b::r],
      u.Nodup ∧ u.toFinset = insert z U := by
  have nd := p.nodup_iff.mp vnodup
  have eq : v.toFinset = (a::b::r).toFinset := by ext i; simpa using (p.mem_iff (a := i))
  simp only [List.toFinset_cons] at eq
  rw [hset] at eq
  have ra := (List.nodup_cons.mp nd).1
  have rb := (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
  have rn := (List.nodup_cons.mp (List.nodup_cons.mp nd).2).2
  have hz : z ∉ a::b::r := by
    intro h
    exact fresh (List.mem_toFinset.mpr (p.mem_iff.mpr h))
  have rr : ∀ i, i ≠ a → i ≠ b → (i ∈ U ↔ i ∈ r) := by
    intro i ha hb
    have e := congrArg (fun X : Finset α => i ∈ X) eq
    simpa [ha,hb] using Iff.of_eq e
  classical
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U
  · refine ⟨z::a::b::r,by simp, List.nodup_cons.mpr ⟨hz,nd⟩,?_⟩
    simp only [List.toFinset_cons]
    rw [← eq,Finset.insert_eq_of_mem hb,Finset.insert_eq_of_mem ha]
  · refine ⟨z::a::r,by simp,?_,?_⟩
    · simp only [List.nodup_cons,List.mem_cons,not_or] at hz ra nd ⊢
      tauto
    · simp only [List.toFinset_cons]
      apply congrArg (insert z)
      ext i
      by_cases ia : i=a <;> by_cases ib : i=b <;> simp_all [List.mem_cons,not_or]
  · refine ⟨z::b::r,by simp,?_,?_⟩
    · simp only [List.nodup_cons,List.mem_cons,not_or] at hz ra nd ⊢
      tauto
    · simp only [List.toFinset_cons]
      apply congrArg (insert z)
      ext i
      by_cases ia : i=a <;> by_cases ib : i=b <;> simp_all [List.mem_cons,not_or]
  · refine ⟨z::r,by simp,?_,?_⟩
    · simp only [List.nodup_cons,List.mem_cons,not_or] at hz nd ⊢
      tauto
    · simp only [List.toFinset_cons]
      apply congrArg (insert z)
      ext i
      by_cases ia : i=a <;> by_cases ib : i=b <;> simp_all [List.mem_cons,not_or]

end Mono2928


namespace Mono2928

abbrev Move := Bool × Wire × Wire

def cost (m : Nat) (g : Move) :=
  collapses m g.2.1 g.2.2 (gate g.1 g.2.1 g.2.2)

def Bounded (gs : List Move) (ms spent : List Nat) : Prop :=
  List.Forall₂ (fun m s => s+(gs.filter (cost m)).length ≤ 3) ms spent

theorem charge_bounded {gs : List Move} {d : Bool} {a b : Wire} {ms spent : List Nat}
    (h : Bounded ((d,a,b)::gs) ms spent) :
    Bounded gs ms (List.zipWith (fun m c => c+(collapses m a b (gate d a b)).toNat) ms spent) := by
  induction h with
  | nil => exact .nil
  | @cons m c ms cs h _ ih =>
    exact .cons (by cases e : collapses m a b (gate d a b) <;> simp [List.filter_cons,cost,e] at h ⊢ <;> omega) ih

theorem budget_zip {gs ms spent} (h : Bounded gs ms spent) :
    ∀ p ∈ ms.zip spent, p.2+(gs.filter (cost p.1)).length ≤ 3 := by
  induction h with
  | nil => simp
  | @cons m c ms cs h hcs ih =>
    intro p hp
    obtain rfl | ht := List.mem_cons.mp hp
    · exact h
    · exact ih p ht

theorem gate_comm (d : Bool) (a b : Wire) : gate d b a = gate d a b := by
  cases d <;> simp [gate,Nat.and_comm,Nat.or_comm]

theorem charge_comm (a b z : Wire) (s : List Nat) : charge b a z s = charge a b z s := by
  have e : (fun m c => c+(collapses m b a z).toNat) =
      (fun m c => c+(collapses m a b z).toNat) := by
    funext m c
    simp [collapses,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm]
  exact congrArg (fun f => List.zipWith f masks s) e

theorem keeps_swap {a b z : Wire} {r : List Wire} {u : List Wire}
    (h : u ∈ keeps a b z r) :
    ∃ v ∈ keeps b a z r, u.Perm v := by
  simp only [keeps,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨_,by simp [keeps],.refl _⟩
  · exact ⟨_,by simp [keeps],.refl _⟩
  · exact ⟨_,by simp [keeps],.refl _⟩
  · exact ⟨_,by simp [keeps],(List.Perm.swap _ _ _).cons z⟩

theorem next_exists {U : Finset Wire} {a b : Wire} {d : Bool} {k : Nat} {v : List Wire}
    {s : List Nat} (neq : a ≠ b) (vd : v.Nodup) (vs : v.toFinset = insert a (insert b U))
    (f : fresh (gate d a b) v = true) (fz : gate d a b ∉ v.toFinset)
    (permit : ∀ u : List Wire, u.Nodup → u.toFinset = insert (gate d a b) U →
        allowed k u (charge a b (gate d a b) s) = true) :
    ∃ u, (u,charge a b (gate d a b) s) ∈ next k v s ∧
      u.Nodup ∧ u.toFinset = insert (gate d a b) U := by
  have ha : a ∈ v := List.mem_toFinset.mp (vs ▸ Finset.mem_insert_self _ _)
  have hb : b ∈ v := List.mem_toFinset.mp (vs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨r,hp,hperm⟩ := pairs_spec ha hb neq
  obtain ⟨u,hu,und,us⟩ := selected_keep vd hperm vs fz
  change u ∈ keeps a b (gate d a b) r at hu
  rcases hp with hp | hp
  · refine ⟨u,?_,und,us⟩
    unfold next
    apply List.mem_flatMap.mpr
    refine ⟨_,hp,List.mem_flatMap.mpr ⟨d,by cases d <;> simp,?_⟩⟩
    simp only [f,↓reduceIte]
    exact List.mem_map.mpr ⟨u,List.mem_filter.mpr ⟨hu,permit u und us⟩,rfl⟩
  · obtain ⟨u',hu',pr⟩ := keeps_swap hu
    have nd' := pr.nodup_iff.mp und
    have e : u'.toFinset = u.toFinset := by ext x; simpa using (pr.mem_iff (a:=x)).symm
    refine ⟨u',?_,nd',e.trans us⟩
    unfold next
    apply List.mem_flatMap.mpr
    refine ⟨_,hp,List.mem_flatMap.mpr ⟨d,by cases d <;> simp,?_⟩⟩
    change _ ∈ (if fresh (gate d b a) v then ((keeps b a (gate d b a) r).filter _).map _ else [])
    rw [gate_comm d a b, f]
    simp only [↓reduceIte,charge_comm a b]
    exact List.mem_map.mpr ⟨u',List.mem_filter.mpr ⟨hu',permit u' nd' (e.trans us)⟩,rfl⟩

end Mono2928



namespace SliceCost
open PEqualNP.Outside.L_meta_2928.CoThetaFreeCore
open PEqualNP.Outside.L_meta_2928.CoThetaNine

variable {W : Type}

def operation (d : Bool) (a b : Nat) := if d then a ||| b else a &&& b

def isCheap (mask a b z : Nat) : Bool :=
  let rz := mask &&& z
  rz == 0 || rz == mask || rz == (mask &&& a) || rz == (mask &&& b)

def value (j : Fin 6) (z : Nat) (r : SmallInput) : Bool :=
  z.testBit (sliceLift j r).val

def project (j : Fin 6) (z : Nat) := norm (0 : SmallInput) (value j z)

theorem value_operation (j : Fin 6) (d : Bool) (a b : Nat) :
    value j (operation d a b) = fun r => base d (value j a r) (value j b r) := by
  funext r
  cases d <;> simp [operation, value, base, Nat.testBit_or, Nat.testBit_and]

theorem masked (j : Fin 6) {m : Nat} (hm : ∀ r : SmallInput, m.testBit (sliceLift j r).val = true)
    {a b : Nat} (h : m &&& a = m &&& b) : value j a = value j b := by
  funext r
  have e := congrArg (fun t : Nat => t.testBit (sliceLift j r).val) h
  simpa [Nat.testBit_and,hm,value] using e

theorem cheap_mem (j : Fin 6) {m a b z : Nat}
    (hm : ∀ r : SmallInput, m.testBit (sliceLift j r).val = true)
    {pool : List (SmallInput → Bool)}
    (hn : absentBit ∈ pool) (ha : project j a ∈ pool) (hb : project j b ∈ pool)
    (cheap : isCheap m a b z = true) : project j z ∈ pool := by
  simp only [isCheap,Bool.or_eq_true,beq_iff_eq] at cheap
  rcases cheap with ((hz|ho)|h)|h
  · have e : value j z = value j 0 := masked j hm (by simpa using hz)
    have en : project j z = absentBit := by
      unfold project
      rw [e]
      funext r
      simp [PEqualNP.Outside.L_meta_2928.CoThetaFreeCore.norm,phase,value,absentBit]
    exact en ▸ hn
  · have e : value j z = value j m := masked j hm (by simpa using ho)
    have en : project j z = absentBit := by
      unfold project
      rw [e]
      funext r
      simp [PEqualNP.Outside.L_meta_2928.CoThetaFreeCore.norm,phase,value,hm,absentBit]
    exact en ▸ hn
  · simpa [project,masked j hm h] using ha
  · simpa [project,masked j hm h] using hb

def Works (gate : Bool → W → W → W) (goal : W) (bank : List W) :
    List (Bool × W × W) → Prop
  | [] => goal ∈ bank
  | (d,a,b)::t => a∈bank ∧ b∈bank ∧ Works gate goal (gate d a b :: bank) t

def cheapCount (col : W → Nat) (gate : Bool → W → W → W) (m : Nat) :
    List (Bool × W × W) → Nat
  | [] => 0
  | (d,a,b)::t => (isCheap m (col a) (col b) (col (gate d a b))).toNat + cheapCount col gate m t

theorem simulate (gate : Bool → W → W → W) (col : W → Nat)
    (hgate : ∀ d a b, col (gate d a b) = operation d (col a) (col b))
    (j : Fin 6) (m : Nat) (hm : ∀ r : SmallInput, m.testBit (sliceLift j r).val = true)
    (goal : W) (moves : List (Bool × W × W)) :
    ∀ (bank : List W) (start : List (SmallInput → Bool)) (k : Nat),
    Works gate goal bank moves →
    Free vertices7 k start → absentBit ∈ start →
    (∀ w ∈ bank, project j (col w) ∈ start) →
    ∃ t ys, Free vertices7 t ys ∧ project j (col goal) ∈ ys ∧
      t + cheapCount col gate m moves ≤ k + moves.length := by
  induction moves with
  | nil =>
    intro bank start k good run _ incl
    exact ⟨k,start,run,incl goal good,by simp [cheapCount]⟩
  | cons s tail ih =>
    obtain ⟨d,a,b⟩ := s
    intro bank start k good run hn incl
    obtain ⟨ha,hb,rest⟩ := good
    let z := gate d a b
    have addIncl {ys : List (SmallInput → Bool)} (hz : project j (col z) ∈ ys)
        (old : ∀ w ∈ start, w ∈ ys) :
        ∀ w ∈ z::bank, project j (col w) ∈ ys := by
      intro w hw
      rcases List.mem_cons.mp hw with eq | h
      · exact eq ▸ hz
      · exact old _ (incl w h)
    cases ch : isCheap m (col a) (col b) (col z) with
    | true =>
      have hz := cheap_mem j hm hn (incl a ha) (incl b hb) ch
      obtain ⟨t,ys,h1,h2,h3⟩ := ih (z::bank) start k rest run hn (addIncl hz (fun _ h => h))
      exact ⟨t,ys,h1,h2,by simp only [cheapCount,show gate d a b = z from rfl,ch,Bool.toNat_true,List.length_cons]; omega⟩
    | false =>
      let kk := normalizedKind d (value j (col a) 0) (value j (col b) 0)
      have ev : project j (col z) = fun i => applyKind kk (project j (col a) i) (project j (col b) i) := by
        unfold project
        rw [show col z = _ from hgate d a b,value_operation]
        exact normalize_binary 0 d _ _
      have hr : Free vertices7 (k+1) (project j (col z) :: start) := by
        rw [ev]
        exact Free.binary run kk (incl a ha) (incl b hb)
      obtain ⟨t,ys,h1,h2,h3⟩ := ih (z::bank) _ (k+1) rest hr (List.mem_cons_of_mem _ hn)
        (addIncl List.mem_cons_self (fun _ h => List.mem_cons_of_mem _ h))
      exact ⟨t,ys,h1,h2,by simp only [cheapCount,show gate d a b = z from rfl,ch,Bool.toNat_false,List.length_cons]; omega⟩

theorem at_most_three (cert : SignedLower) (gate : Bool → W → W → W) (col : W → Nat)
    (hgate : ∀ d a b, col (gate d a b) = operation d (col a) (col b))
    (j : Fin 6) (m : Nat) (hm : ∀ r : SmallInput, m.testBit (sliceLift j r).val = true)
    (goal : W) (hout : project j (col goal) = ans7)
    (moves : List (Bool × W × W)) (bank : List W) (good : Works gate goal bank moves)
    (hin : ∀ w ∈ bank, project j (col w) ∈ vertices7) (len : moves.length ≤ 14) :
    cheapCount col gate m moves ≤ 3 := by
  obtain ⟨t,ys,hr,hv,hb⟩ := simulate gate col hgate j m hm goal moves bank vertices7 0 good
    Free.start List.mem_cons_self hin
  rw [hout] at hv
  have h := cert hr hv
  omega

end SliceCost



namespace SliceData
open Mono2928
open PEqualNP.Outside.L_meta_2928.CoThetaFreeCore
open PEqualNP.Outside.L_meta_2928.CoThetaNine
open PEqualNP.Outside.L_meta_2928.SliceCost

theorem bitsAt {α : Type} (xs : List α) (p : α → Bool) (i : Nat) (h : i < xs.length) :
    (bits xs p).testBit i = p xs[i] := by
  induction xs generalizing i with
  | nil => simp at h
  | cons a t ih =>
    change (2 * bits t p + (p a).toNat).testBit i = _
    cases i with
    | zero => cases e : p a <;> simp [e, Nat.testBit_zero, Nat.add_mod]
    | succ i =>
      rw [Nat.testBit_succ]
      have ht : (2 * bits t p + (p a).toNat) / 2 = bits t p := by
        cases p a <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
      rw [ht]
      exact ih i (by simpa using h)

theorem tableAt (p : Nat → Bool) (i : Fin 512) : (table p).testBit i.val = p i.val := by
  simpa [table] using bitsAt (List.range 512) p i.val (by simpa using i.isLt)

theorem gateFirst (d : Bool) (a b : Wire) :
    (gate d a b).1 = operation d a.1 b.1 := by cases d <;> rfl

theorem sameCheap (m : Nat) (a b z : Wire) :
    isCheap m a.1 b.1 z.1 = collapses m a b z := by
  simp only [isCheap,collapses,Nat.and_comm m]

theorem selected (m : Nat) (h : m ∈ masks) :
    ∃ j : Fin 6, ∀ r : SmallInput, m.testBit (sliceLift j r).val = true := by
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp h
  have hc' : cuts = List.ofFn (fun j : Fin 6 => ((ep j).val,(eqp j).val)) := by decide
  rw [hc'] at hc
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hc
  refine ⟨j, fun r => ?_⟩
  rw [tableAt]
  obtain ⟨_,ha,hb,_⟩ := slice7_values j r
  simpa [vtx] using (show !(vtx (ep j) (sliceLift j r) || vtx (eqp j) (sliceLift j r)) = true by simp [ha,hb])

theorem targetProjection (j : Fin 6) : project j target = ans7 := by
  have same : ∀ r : Fin 512, Mono2928.edge r.val = ans r := by decide +kernel
  have val : ∀ r : SmallInput, value j target r = ans7 r := by
    intro r
    change (table Mono2928.edge).testBit (sliceLift j r).val = _
    rw [tableAt, same, (slice7_values j r).1]
  funext r
  change phase (value j target 0) (value j target r) = ans7 r
  rw [val,val]
  rfl

set_option maxRecDepth 8000 in
theorem inputProjection (j : Fin 6) (w : Wire) (h : w ∈ inputs) : project j w.1 ∈ vertices7 := by
  have baseZero : ∀ (j : Fin 6) (a : Fin 9), vtx a (sliceLift j 0) = false := by decide
  have incl (a : Fin 9) : restrict (sliceLift j) (vtx a) ∈ vertices7 :=
    slice_known j (vtx a) (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨a,rfl⟩))
  rcases List.mem_append.mp h with hr | hn
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    let a : Fin 9 := ⟨i,List.mem_range.mp hi⟩
    have val (r : SmallInput) : value j (table fun n => n.testBit i) r = vtx a (sliceLift j r) := tableAt _ _
    have eq : project j (table fun n => n.testBit i) = restrict (sliceLift j) (vtx a) := by
      funext r
      change phase (value j _ 0) (value j _ r) = _
      rw [val,val,baseZero]
      rfl
    change project j (table fun n => n.testBit i) ∈ vertices7
    rw [eq]
    exact incl a
  · obtain rfl := List.mem_singleton.mp hn
    have val (r : SmallInput) : value j (table fun n => !(n.testBit 0)) r = !vtx 0 (sliceLift j r) := tableAt _ _
    have eq : project j (table fun n => !(n.testBit 0)) = restrict (sliceLift j) (vtx 0) := by
      funext r
      change phase (value j _ 0) (value j _ r) = vtx 0 (sliceLift j r)
      simp only [val,baseZero,Bool.not_false,phase,ite_true,Bool.not_not]
    change project j (table fun n => !(n.testBit 0)) ∈ vertices7
    rw [eq]
    exact incl 0

theorem collapseBound (cert : SignedLower) (goal : Wire) (hg : goal.1 = target)
    (moves : List (Bool × Wire × Wire)) (good : Works gate goal inputs moves)
    (len : moves.length ≤ 14) (m : Nat) (hm : m ∈ masks) :
    cheapCount Prod.fst gate m moves ≤ 3 := by
  obtain ⟨j,hj⟩ := selected m hm
  exact at_most_three cert gate Prod.fst gateFirst j m hj goal (hg ▸ targetProjection j)
    moves inputs good (inputProjection j) len

end SliceData



namespace Mono2928

open PEqualNP.CircuitLowerBounds

namespace Physical

variable {W : Type} [DecidableEq W]

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def isOr : GateOp → Bool
  | .or => true
  | _ => false

def gv (gate : Bool → W → W → W) (z o : W) (w : List W) (g : Gate) : W :=
  match g.inputs with
  | [] => if isAnd g.op then o else z
  | [i] => w.getD i z
  | i :: j :: _ => gate (isOr g.op) (w.getD i z) (w.getD j z)

def run (gate : Bool → W → W → W) (z o : W) (w : List W) (gs : List Gate) : List W :=
  gs.foldl (fun q g => q ++ [gv gate z o q g]) w

def witness (gate : Bool → W → W → W) (z o : W) (w : List W) (x : W) : Prop :=
  x ∈ w ∨ x = z ∨ x = o ∨
  ∃ d a b, a ∈ w ∧ b ∈ w ∧ a ≠ z ∧ a ≠ o ∧ b ≠ z ∧ b ≠ o ∧ a ≠ b ∧ x = gate d a b

lemma get_wire (w : List W) (i : Nat) (z : W) : w.getD i z ∈ w ∨ w.getD i z = z := by
  rw [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr rfl
  | some a => exact Or.inl (List.mem_of_getElem? h)

lemma gate_witness (gate : Bool → W → W → W) (z o : W) (w : List W)
    (laws : ∀ d a b, (a ∈ w ∨ a = z) → (b ∈ w ∨ b = z) →
       (a = z ∨ a = o ∨ b = z ∨ b = o ∨ a = b) →
       gate d a b = z ∨ gate d a b = o ∨ gate d a b = a ∨ gate d a b = b)
    (g : Gate) : witness gate z o w (gv gate z o w g) := by
  rcases g with ⟨op, pins⟩
  cases pins with
  | nil =>
    cases op <;> simp [gv, witness, isAnd]
  | cons i ks =>
    cases ks with
    | nil =>
      change witness gate z o w (w.getD i z)
      rcases get_wire w i z with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    | cons j tl =>
      let a := w.getD i z
      let b := w.getD j z
      let d := isOr op
      change witness gate z o w (gate d a b)
      have ha : a ∈ w ∨ a = z := get_wire w i z
      have hb : b ∈ w ∨ b = z := get_wire w j z
      by_cases h : a = z ∨ a = o ∨ b = z ∨ b = o ∨ a = b
      · rcases laws d a b ha hb h with r | r | r | r
        · exact Or.inr (Or.inl r)
        · exact Or.inr (Or.inr (Or.inl r))
        · rw [r]; rcases ha with m | m
          · exact Or.inl m
          · exact Or.inr (Or.inl m)
        · rw [r]; rcases hb with m | m
          · exact Or.inl m
          · exact Or.inr (Or.inl m)
      · simp only [not_or] at h
        exact Or.inr (Or.inr (Or.inr ⟨d,a,b,ha.resolve_right h.1,hb.resolve_right h.2.2.1,
          h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,rfl⟩))

lemma pull {gate : Bool → W → W → W} {z o goal x : W} {w : List W}
    {S : Finset W} {gs : List (Bool × W × W)}
    (trace : ValidTrace gate goal S gs) (nonc : ∀ u ∈ S, u ≠ z ∧ u ≠ o)
    (hw : witness gate z o w x) (sub : ∀ u ∈ S, u ∈ w ++ [x]) :
    ∃ T gs', gs'.length ≤ gs.length + 1 ∧ ValidTrace gate goal T gs' ∧
      (∀ u ∈ T, u ≠ z ∧ u ≠ o) ∧ ∀ u ∈ T, u ∈ w := by
  by_cases h : x ∈ S ∧ x ∉ w
  · obtain ⟨hm,hn⟩ := h
    rcases hw with h | h | h | ⟨d,a,b,ha,hb,az,ao,bz,bo,ne,eq⟩
    · exact False.elim (hn h)
    · exact False.elim ((nonc _ hm).1 h)
    · exact False.elim ((nonc _ hm).2 h)
    · subst x
      let U := S.erase (gate d a b)
      have hu : ∀ u ∈ U, u ∈ w := by
        intro u h
        obtain ⟨h1,h2⟩ := Finset.mem_erase.mp h
        simpa [h1] using sub u h2
      have hc : ∀ u ∈ U, u ≠ z ∧ u ≠ o := fun u h => nonc u (Finset.mem_erase.mp h).2
      have ht : ValidTrace gate goal (insert (gate d a b) U) gs := by
        simpa [U, Finset.insert_erase hm] using trace
      have hf : gate d a b ∉ insert a (insert b U) := by
        intro hh
        rcases Finset.mem_insert.mp hh with e | e
        · exact hn (by rw [e]; exact ha)
        rcases Finset.mem_insert.mp e with e | e
        · exact hn (by rw [e]; exact hb)
        · exact hn (hu _ e)
      refine ⟨_, _, le_rfl, ValidTrace.step ne hf ht, ?_, ?_⟩
      · simpa only [Finset.forall_mem_insert] using And.intro (And.intro az ao) (And.intro (And.intro bz bo) hc)
      · simpa only [Finset.forall_mem_insert] using And.intro ha (And.intro hb hu)
  · refine ⟨S, gs, by omega, trace, nonc, ?_⟩
    intro u hu
    rcases List.mem_append.mp (sub u hu) with hm | hm
    · exact hm
    obtain rfl := List.mem_singleton.mp hm
    by_contra hh
    exact h ⟨hu,hh⟩

lemma extract (gate : Bool → W → W → W) (z o goal : W) (Good : W → Prop)
    (hz : Good z) (ho : Good o)
    (closed : ∀ d a b, Good a → Good b → Good (gate d a b))
    (laws : ∀ d a b, Good a → Good b → (a = z ∨ a = o ∨ b = z ∨ b = o ∨ a = b) →
       gate d a b = z ∨ gate d a b = o ∨ gate d a b = a ∨ gate d a b = b)
    (gn : goal ≠ z ∧ goal ≠ o) (gs : List Gate) (w : List W) (hw : ∀ a ∈ w, Good a)
    (hout : goal ∈ run gate z o w gs) :
    ∃ S moves, moves.length ≤ gs.length ∧ ValidTrace gate goal S moves ∧
      (∀ a ∈ S, a ≠ z ∧ a ≠ o) ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨{goal}, [], by simp, .stop, by simpa using gn, by simpa [run] using hout⟩
  | cons g gs ih =>
    have hh : ∀ a, (a ∈ w ∨ a = z) → Good a := by
      intro a h; rcases h with h | rfl
      · exact hw a h
      · exact hz
    have gx := gate_witness gate z o w (fun d a b ha hb => laws d a b (hh a ha) (hh b hb)) g
    have hg : Good (gv gate z o w g) := by
      rcases gx with h | h | h | ⟨_,a,b,ha,hb,_,_,_,_,_,e⟩
      · exact hw _ h
      · rw [h]; exact hz
      · rw [h]; exact ho
      · rw [e]; exact closed _ _ _ (hw a ha) (hw b hb)
    have hnew : ∀ a ∈ w ++ [gv gate z o w g], Good a := by
      intro a h; rcases List.mem_append.mp h with m | m
      · exact hw a m
      · simpa only [List.mem_singleton.mp m] using hg
    obtain ⟨S, l, hk, tr, nc, sub⟩ := ih _ hnew hout
    obtain ⟨T, l', hk', tr', nc', sub'⟩ := pull tr nc gx sub
    exact ⟨T, l', by simp; omega, tr', nc', sub'⟩

end Physical
end Mono2928



namespace Mono2928
namespace DataBridge

open PEqualNP.CircuitLowerBounds

def boolOp (d a b : Bool) := if d then a || b else a && b

lemma bits_read {A : Type} (xs : List A) (p : A → Bool) (j : Nat) :
    (bits xs p).testBit j = ((xs.map p).getD j false) := by
  induction xs generalizing j with
  | nil => simp [bits]
  | cons a xs ih =>
    change (2 * bits xs p + (p a).toNat).testBit j = ((p a :: xs.map p).getD j false)
    cases j with
    | zero => cases h : p a <;> simp [Nat.testBit_eq_decide_div_mod_eq, h]
    | succ j =>
      rw [Nat.testBit_succ]
      have he : (2 * bits xs p + (p a).toNat) / 2 = bits xs p := by
        cases h : p a <;> simp [h] <;> omega
      simpa [he] using ih j

lemma bits_join {A : Type} (xs : List A) (p q : A → Bool) (d : Bool) :
    bits xs (fun a => boolOp d (p a) (q a)) =
      (if d then bits xs p ||| bits xs q else bits xs p &&& bits xs q) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or, bits_read]
  all_goals
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases xs[i]? <;> rfl

lemma pack_join (p q : Nat → Bool) (d : Bool) :
    pack (fun i => boolOp d (p i) (q i)) = gate d (pack p) (pack q) := by
  cases d <;> simp [pack, gate, table, bits_join]

set_option maxRecDepth 4096 in
lemma pack_ext (p q : Nat → Bool) (h : ∀ i < 512, p i = q i) : pack p = pack q := by
  have transform {A : Type} (xs : List A) (f g : A → Bool) (e : ∀ a ∈ xs, f a = g a) :
      bits xs f = bits xs g := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      have e0 := e a (by simp)
      have es := ih (fun x hx => e x (by simp [hx]))
      change 2 * bits xs f + _ = 2 * bits xs g + _
      rw [e0,es]
  have pos_range : ∀ v ∈ pos, v < 512 := by decide
  have neg_range : ∀ v ∈ neg, v < 512 := by decide
  have sc : ∀ s ∈ samples, s.1 < 512 ∧ s.2 < 512 := by
    intro s hs
    obtain ⟨a,ha,v⟩ := List.mem_flatMap.mp hs
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp v
    exact ⟨pos_range a ha, neg_range b hb⟩
  exact Prod.ext (transform _ _ _ (fun a ha => h _ (List.mem_range.mp ha))) (Prod.ext
    (transform _ _ _ (fun a ha => h _ (sc a ha).1)) (transform _ _ _ (fun a ha => h _ (sc a ha).2)))

def bottom : Wire := pack fun _ => false
def ceiling : Wire := pack fun _ => true
def Packed (w : Wire) := ∃ p, w = pack p

lemma packed_laws (d : Bool) (a b : Wire) (ha : Packed a) (hb : Packed b)
    (h : a = bottom ∨ a = ceiling ∨ b = bottom ∨ b = ceiling ∨ a = b) :
    gate d a b = bottom ∨ gate d a b = ceiling ∨ gate d a b = a ∨ gate d a b = b := by
  obtain ⟨p,rfl⟩ := ha
  obtain ⟨q,rfl⟩ := hb
  rcases h with h | h | h | h | h
  all_goals
    rw [h]
    cases d <;> simp [bottom, ceiling, ←pack_join, boolOp]

lemma get_map (w : List (Nat → Bool)) (i : Nat) :
    (w.map pack).getD i bottom = pack (w.getD i fun _ => false) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> rfl

def raw (w : List (Nat → Bool)) (g : Gate) : Nat → Bool :=
  fun r => g.op.eval (g.inputs.map fun i => (w.getD i fun _ => false) r)

def rawRun (w : List (Nat → Bool)) (gs : List Gate) :=
  gs.foldl (fun ws g => ws ++ [raw ws g]) w

lemma gv_map (w : List (Nat → Bool)) (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    (hl : g.inputs.length ≤ 2) :
    Physical.gv gate bottom ceiling (w.map pack) g = pack (raw w g) := by
  obtain ⟨op,l⟩ := g
  simp only at hg hl
  rcases hg with rfl | rfl <;> cases l with
  | nil => rfl
  | cons i l =>
    cases l with
    | nil =>
      simp only [Physical.gv, get_map]
      apply congrArg pack
      funext r
      simp [raw, GateOp.eval]
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        simp only [Physical.gv, Physical.isOr,get_map,←pack_join]
        apply congrArg pack
        funext r
        simp [boolOp,raw,GateOp.eval]

lemma run_map (gs : List Gate) (w : List (Nat → Bool))
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    Physical.run gate bottom ceiling (w.map pack) gs = (rawRun w gs).map pack := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have h0 := hg g (by simp)
    change Physical.run gate bottom ceiling (w.map pack ++ [_]) gs = (rawRun (w ++ [_]) gs).map pack
    rw [gv_map w g h0.1 h0.2, ← List.map_singleton, ← List.map_append]
    exact ih _ (fun a ha => hg a (by simp [ha]))

lemma get_row (w : List (Nat → Bool)) (i r : Nat) :
    (w.map (fun f => f r)).getD i false = (w.getD i fun _ => false) r := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> rfl

lemma row_run (gs : List Gate) (w : List (Nat → Bool)) (r : Nat) :
    (rawRun w gs).map (fun f => f r) =
      gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)])
        (w.map (fun f => f r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (rawRun (w ++ [raw w g]) gs).map _ = _
    rw [ih]
    simp only [List.map_append,List.map_singleton,List.foldl_cons,raw,get_row]

def baseFns : List (Nat → Bool) :=
  (List.range 9).map (fun j r => r.testBit j) ++ [fun r => !r.testBit 0]

lemma inputs_eq : inputs = baseFns.map pack := by simp [inputs, baseFns, List.map_map,Function.comp_def]

def rowInput (r : Nat) : List Bool := baseFns.map (fun f => f r)

set_option maxRecDepth 4096 in
lemma extract (C : Circuit)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (h : ∀ r < 512, C.eval (rowInput r) = edge r) :
    ∃ S moves, moves.length ≤ C.gates.length ∧ ValidTrace gate (pack edge) S moves ∧
      (∀ a ∈ S, a ≠ bottom ∧ a ≠ ceiling) ∧ ∀ a ∈ S, a ∈ inputs := by
  classical
  let result := (rawRun baseFns C.gates).getD C.output fun _ => false
  have f : pack result = pack edge := by
    apply pack_ext
    intro r hr
    have q := h r hr
    change (C.wires (rowInput r)).getD C.output false = edge r at q
    rw [← q]
    change _ = (C.gates.foldl _ (baseFns.map (fun f => f r))).getD _ _
    rw [← row_run C.gates baseFns r, get_row]
  have ng : pack edge ≠ bottom ∧ pack edge ≠ ceiling := by decide +kernel
  have mem : result ∈ rawRun baseFns C.gates := by
    by_contra hn
    rcases Physical.get_wire (rawRun baseFns C.gates) C.output (fun _ => false) with hm | hm
    · exact hn hm
    · apply ng.1
      rw [← f]; exact congrArg pack hm
  rw [inputs_eq]
  refine Physical.extract gate bottom ceiling (pack edge) Packed ⟨_,rfl⟩ ⟨_,rfl⟩ ?_ packed_laws ng
    C.gates (baseFns.map pack) ?_ ?_
  · rintro d _ _ ⟨p,rfl⟩ ⟨q,rfl⟩
    exact ⟨_,(pack_join p q d).symm⟩
  · intro a ha
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
    exact ⟨_,rfl⟩
  · rw [run_map C.gates baseFns hg, ← f]
    exact List.mem_map.mpr ⟨_,mem,rfl⟩

end DataBridge
end Mono2928



namespace Mono2928
namespace DataBridge

lemma pack_mem_inputs (a : Wire) (h : a ∈ inputs) : Packed a := by
  rw [inputs_eq] at h
  obtain ⟨_,_,rfl⟩ := List.mem_map.mp h
  exact ⟨_,rfl⟩

lemma packed_gate (d : Bool) {a b : Wire} (ha : Packed a) (hb : Packed b) :
    Packed (gate d a b) := by
  obtain ⟨p,rfl⟩ := ha
  obtain ⟨q,rfl⟩ := hb
  exact ⟨_,(pack_join p q d).symm⟩

set_option maxRecDepth 4096 in
lemma table_read (p : Nat → Bool) {r : Nat} (hr : r < 512) :
    (table p).testBit r = p r := by
  unfold table
  rw [bits_read, List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range] using hr)]
  simp only [List.getElem_map, List.getElem_range]

set_option maxRecDepth 4096 in
lemma packed_inj {a b : Wire} (ha : Packed a) (hb : Packed b) (eq : a.1 = b.1) : a = b := by
  obtain ⟨p,rfl⟩ := ha
  obtain ⟨q,rfl⟩ := hb
  change table p = table q at eq
  apply pack_ext
  intro r hr
  rw [←table_read p hr, ←table_read q hr, eq]

set_option maxRecDepth 4096 in
lemma bottom_bits : bottom.1 = 0 := by decide +kernel

set_option maxRecDepth 4096 in
lemma ceiling_bits : ceiling.1 = top512 := by decide +kernel

lemma gate_trivial (d : Bool) {a b : Wire} (ha : Packed a) (hb : Packed b)
    (h : a.1 = 0 ∨ a.1 = top512 ∨ b.1 = 0 ∨ b.1 = top512) :
    gate d a b = a ∨ gate d a b = b := by
  have zP : Packed bottom := ⟨_,rfl⟩
  have oP : Packed ceiling := ⟨_,rfl⟩
  rcases h with h | h | h | h
  · have e := packed_inj ha zP (h.trans bottom_bits.symm)
    subst a
    obtain ⟨p,rfl⟩ := hb
    cases d <;> simp [bottom, ←pack_join, boolOp]
  · have e := packed_inj ha oP (h.trans ceiling_bits.symm)
    subst a
    obtain ⟨p,rfl⟩ := hb
    cases d <;> simp [ceiling, ←pack_join, boolOp]
  · have e := packed_inj hb zP (h.trans bottom_bits.symm)
    subst b
    obtain ⟨p,rfl⟩ := ha
    cases d <;> simp [bottom, ←pack_join, boolOp]
  · have e := packed_inj hb oP (h.trans ceiling_bits.symm)
    subst b
    obtain ⟨p,rfl⟩ := ha
    cases d <;> simp [ceiling, ←pack_join, boolOp]

def properTable (v : Wire) : Prop := v.1 ≠ 0 ∧ v.1 ≠ top512

set_option maxRecDepth 4096 in
lemma trace_coherent {S : Finset Wire} {moves : List (Bool × Wire × Wire)} {goal : Wire}
    (trace : ValidTrace gate goal S moves) (hg : properTable goal) (hw : ∀ a ∈ S, Packed a) :
    (∀ a ∈ S, properTable a) ∧
    ∀ g ∈ moves, Packed (gate g.1 g.2.1 g.2.2) ∧ properTable (gate g.1 g.2.1 g.2.2) := by
  induction trace with
  | stop => simpa using hg
  | @step U a b d gs ne fresh tail ih =>
    have hpa := hw a (by simp)
    have hpb := hw b (by simp)
    have pc := packed_gate d hpa hpb
    have hU : ∀ a ∈ U, Packed a := fun v hv => hw v (by simp [hv])
    obtain ⟨proper, facts⟩ := ih (by simpa only [Finset.forall_mem_insert] using And.intro pc hU)
    have hboth : properTable a ∧ properTable b := by
      by_contra! deny
      have h : a.1 = 0 ∨ a.1 = top512 ∨ b.1 = 0 ∨ b.1 = top512 := by
        unfold properTable at deny; tauto
      rcases gate_trivial d hpa hpb h with he | he <;> exact fresh (by simp [he])
    have suff : ∀ v ∈ U, properTable v := fun v hv => proper v (Finset.mem_insert_of_mem hv)
    constructor
    · simpa only [Finset.forall_mem_insert] using And.intro hboth.1 (And.intro hboth.2 suff)
    · intro g h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨pc,proper _ (by simp)⟩
      · exact facts g h

set_option maxRecDepth 4096 in
lemma goal_proper : properTable (pack edge) := by
  change (table edge ≠ 0 ∧ table edge ≠ top512)
  decide +kernel

end DataBridge
end Mono2928



namespace Mono2928

def Ic (m : Nat) (w : Wire) : Bool := ((w.1 &&& m) == 0) || ((w.1 &&& m) == m)

theorem maskedGate (d : Bool) (a b : Wire) (m : Nat) :
    (gate d a b).1 &&& m = if d then (a.1 &&& m) ||| (b.1 &&& m) else (a.1 &&& m) &&& (b.1 &&& m) := by
  cases d
  · apply Nat.eq_of_testBit_eq
    intro k
    simp only [gate,Bool.false_eq_true,↓reduceIte,Nat.testBit_and]
    cases a.1.testBit k <;> cases b.1.testBit k <;> cases m.testBit k <;> rfl
  · exact Nat.and_or_distrib_right _ _ _

theorem mask_identities (a m : Nat) :
    (a &&& m) &&& m = a &&& m ∧ m &&& (a &&& m) = a &&& m ∧
    (a &&& m) ||| m = m ∧ m ||| (a &&& m) = m := by
  refine ⟨?_,?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro k <;>
    simp only [Nat.testBit_and,Nat.testBit_or] <;> cases a.testBit k <;> cases m.testBit k <;> rfl

theorem collapse_of_const (m : Nat) (d : Bool) (a b : Wire) (h : Ic m a = true ∨ Ic m b = true) :
    collapses m a b (gate d a b) = true := by
  have ea := mask_identities a.1 m
  have eb := mask_identities b.1 m
  simp only [Ic,Bool.or_eq_true,beq_iff_eq] at h
  unfold collapses
  rw [maskedGate]
  rcases h with (h|h)|(h|h) <;> cases d <;> simp [h,ea.1,ea.2.1,ea.2.2.1,ea.2.2.2,eb.1,eb.2.1,eb.2.2.1,eb.2.2.2]

theorem const_gate (m : Nat) (d : Bool) (a b : Wire) (ha : Ic m a = true) (hb : Ic m b = true) :
    Ic m (gate d a b) = true := by
  simp only [Ic,Bool.or_eq_true,beq_iff_eq] at ha hb ⊢
  rw [maskedGate]
  rcases ha with ha|ha <;> rcases hb with hb|hb <;> cases d <;> simp [ha,hb]

def separatorBit (k : Nat) (w : Wire) : Prop :=
  w.2.1.testBit k = true ∧ w.2.2.testBit k = false

theorem gate_separator (k : Nat) (d : Bool) (a b : Wire) (h : separatorBit k (gate d a b)) :
    separatorBit k a ∨ separatorBit k b := by
  unfold separatorBit at *
  cases d <;> simp only [gate,Bool.false_eq_true,↓reduceIte,Nat.testBit_and,Nat.testBit_or] at h <;>
    cases ea : a.2.1.testBit k <;> cases eb : a.2.2.testBit k <;> cases ec : b.2.1.testBit k <;> cases ed : b.2.2.testBit k <;> simp_all

def sepMask (w : Wire) := w.2.1 &&& (top208 ^^^ w.2.2)

theorem foldBits (k t : Nat) (u : List Wire) :
    (u.foldl (fun x w => x ||| sepMask w) t).testBit k = true ↔
       t.testBit k = true ∨ ∃ w ∈ u, (sepMask w).testBit k = true := by
  induction u generalizing t with
  | nil => simp
  | cons w u ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_or,Bool.or_eq_true,List.mem_cons]
    aesop

theorem covered_of_trace {goal : Wire} {u : List Wire} {gs}
    (h : ValidTrace gate goal u.toFinset gs)
    (hp : goal.2.1 = top208) (hn : goal.2.2 = 0)
    (bounded : ∀ w ∈ u, w.2.1 ≤ top208) : covered u = true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro k
  change (u.foldl (fun x w => x ||| sepMask w) 0).testBit k = top208.testBit k
  by_cases hk : k < 208
  · have mask : top208.testBit k = true := by unfold top208; rw [Nat.testBit_two_pow_sub_one]; simp [hk]
    rw [mask,foldBits]
    obtain ⟨w,hw,wp,wn⟩ := trace_has_separator h (separatorBit k) ⟨hp ▸ mask,by simp [hn]⟩ (gate_separator k)
    exact Or.inr ⟨w,List.mem_toFinset.mp hw,by simp [sepMask,Nat.testBit_and,Nat.testBit_xor,mask,wp,wn]⟩
  · have mask : top208.testBit k = false := by unfold top208; rw [Nat.testBit_two_pow_sub_one]; simp [hk]
    rw [mask]
    cases he : (u.foldl (fun x w => x ||| sepMask w) 0).testBit k with
    | false => rfl
    | true =>
      rcases (foldBits k 0 u).mp he with ht|⟨w,hw,hh⟩
      · simp at ht
      · have bound0 : top208 < 2^208 := by decide
        have pow : (2:Nat)^208 ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
        have bit : w.2.1.testBit k = false := Nat.testBit_lt_two_pow ((lt_of_le_of_lt (bounded w hw) bound0).trans_le pow)
        simp [sepMask,Nat.testBit_and,bit] at hh

theorem target_not_const : ∀ m ∈ masks, Ic m (pack edge) = false := by decide +kernel

end Mono2928


namespace Mono2928

theorem works_trace {W : Type} [DecidableEq W] {gate : Bool → W → W → W} {goal : W}
    {S gs} (tr : ValidTrace gate goal S gs) (bank : List W) (hb : S ⊆ bank.toFinset) :
    PEqualNP.Outside.L_meta_2928.SliceCost.Works gate goal bank gs := by
  induction tr generalizing bank with
  | stop => exact List.mem_toFinset.mp (hb (Finset.mem_singleton_self _))
  | @step U a b d gs ne fresh tail ih =>
    refine ⟨List.mem_toFinset.mp (hb (by simp)),List.mem_toFinset.mp (hb (by simp)),ih _ ?_⟩
    intro x h
    obtain rfl|hm := Finset.mem_insert.mp h
    · simp
    · exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp (hb (by simp [hm]))))

theorem len_equal {gs : List Move} (m : Nat) :
    (gs.filter (cost m)).length = PEqualNP.Outside.L_meta_2928.SliceCost.cheapCount
      Prod.fst gate m gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨d,a,b⟩ := g
    have eq : cost m (d,a,b) = PEqualNP.Outside.L_meta_2928.SliceCost.isCheap m a.1 b.1 (gate d a b).1 := by
      simp [cost,collapses,PEqualNP.Outside.L_meta_2928.SliceCost.isCheap,Nat.and_comm]
    cases e : cost m (d,a,b) <;> simp [e,PEqualNP.Outside.L_meta_2928.SliceCost.cheapCount,← eq, ih,Nat.add_comm]

theorem zero_budget (gs : List Move)
    (hc : ∀ m ∈ masks, (gs.filter (cost m)).length ≤ 3) : Bounded gs masks initial := by
  have gen (ms : List Nat) (h : ∀ m∈ms, (gs.filter (cost m)).length ≤ 3) :
      Bounded gs ms (ms.map (fun _ => 0)) := by
    induction ms with
    | nil => exact .nil
    | cons m ms ih => exact .cons (by simpa using h m (by simp)) (ih (fun x hx => h x (by simp [hx])))
  exact gen masks hc

theorem const_length {goal S gs} (tr : ValidTrace gate goal S gs)
    (m : Nat) (u : List Wire) (uS : u.toFinset = S) (un : u.Nodup)
    (nh : ((goal.1 &&& m) == 0 || (goal.1 &&& m) == m) = false)
    (either : ∀ d (a b : Wire),
      (((a.1 &&& m) == 0 || (a.1 &&& m) == m) = true ∨ ((b.1 &&& m) == 0 || (b.1 &&& m) == m) = true) →
      cost m (d,a,b) = true)
    (both : ∀ d (a b : Wire),
      ((a.1 &&& m) == 0 || (a.1 &&& m) == m) = true → ((b.1 &&& m) == 0 || (b.1 &&& m) == m) = true →
      (((gate d a b).1 &&& m) == 0 || ((gate d a b).1 &&& m) == m) = true) :
    constants m u ≤ (gs.filter (cost m)).length := by
  have h := trace_const_bound tr (fun w => (w.1 &&& m) == 0 || (w.1 &&& m) == m) (cost m) nh either both
  rw [←uS,un.card_eq_countP] at h
  exact h

theorem trace_search {goal : Wire} (goalEq : goal.1 = target) (Good : Wire → Prop)
    (cancel : ∀ {a b : Wire}, Good a → Good b → a.1 = b.1 → a = b)
    (covers : ∀ {S gs} (tr : ValidTrace gate goal S gs) (v : List Wire),
      v.toFinset = S → (∀ w∈v, Good w) → covered v = true)
    (future : ∀ {S gs} (tr : ValidTrace gate goal S gs) (v : List Wire),
      v.toFinset = S → v.Nodup → ∀ m ∈ masks, constants m v ≤ (gs.filter (cost m)).length)
    {S gs} (tr : ValidTrace gate goal S gs) (v : List Wire) (vS : v.toFinset = S)
    (vn : v.Nodup) (gv : ∀ w ∈ v, Good w)
    (gm : ∀ g ∈ gs, Good (gate g.1 g.2.1 g.2.2) ∧
      (gate g.1 g.2.1 g.2.2).1 ≠ 0 ∧ (gate g.1 g.2.1 g.2.2).1 ≠ top512)
    (k : Nat) (len : gs.length ≤ k) (spent : List Nat) (budget : Bounded gs masks spent) :
    search k v spent = true := by
  induction tr generalizing v k spent with
  | stop =>
    have mem : goal ∈ v := List.mem_toFinset.mp (vS ▸ Finset.mem_singleton_self _)
    have now : v.any (fun w => w.1 == target) = true := List.any_eq_true.mpr ⟨goal,mem,beq_iff_eq.mpr goalEq⟩
    cases k <;> simp [search,now]
  | @step U a b d gs ne hz tr ih =>
    cases k with
    | zero => simp at len
    | succ n =>
      have valid := gm (d,a,b) (by simp)
      have ge : Good (gate d a b) := valid.1
      have notin : gate d a b ∉ v.toFinset := vS ▸ hz
      have fr : fresh (gate d a b) v = true := by
        simp only [fresh,Bool.not_eq_true',Bool.or_eq_false_iff,beq_eq_false_iff_ne,List.any_eq_false]
        refine ⟨⟨valid.2.1,valid.2.2⟩,?_⟩
        intro w hw
        intro eq
        exact notin (List.mem_toFinset.mpr ((cancel (gv w hw) ge (beq_iff_eq.mp eq)) ▸ hw))
      have bn := charge_bounded budget
      change Bounded gs masks (charge a b (gate d a b) spent) at bn
      have size : gs.length ≤ n := by simpa using len
      have ug : ∀ {u : List Wire}, u.toFinset = insert (gate d a b) U → ∀ w∈u, Good w := by
        intro u hu w hw
        have mem := List.mem_toFinset.mpr hw
        rw [hu] at mem
        obtain rfl | hm := Finset.mem_insert.mp mem
        · exact ge
        · exact gv w (List.mem_toFinset.mp (vS ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm)))
      obtain ⟨u,hm,und,us⟩ := next_exists (k := n) ne vn vS fr notin (by
        intro u und us
        have cc := covers tr u us (ug us)
        have lens := trace_length_bound tr
        rw [← us, List.toFinset_card_of_nodup und] at lens
        simp only [allowed,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
        refine ⟨⟨by omega,cc⟩,?_⟩
        intro p hp
        have hh := budget_zip bn p hp
        have fm := future tr u us und p.1 (List.of_mem_zip hp).1
        omega)
      have last := ih u us und (ug us) (fun g h => gm g (List.mem_cons_of_mem _ h)) n size _ bn
      simp only [search,Bool.or_eq_true]
      exact Or.inr (List.any_eq_true.mpr ⟨(u,charge a b (gate d a b) spent),hm,last⟩)

end Mono2928



namespace Mono2928
open DataBridge
open PEqualNP.Outside.L_meta_2928.CoThetaNine
open PEqualNP.Outside.L_meta_2928.SliceData

theorem sample_bounded {α} (xs : List α) (p : α → Bool) : bits xs p < 2^xs.length := by
  induction xs with
  | nil => simp [bits]
  | cons x xs ih =>
    change 2 * bits xs p + (p x).toNat < 2^(xs.length+1)
    rw [Nat.pow_succ]
    cases p x <;> simp <;> omega

set_option maxRecDepth 10000 in
theorem packed_bounded {a : Wire} (h : Packed a) : a.2.1 ≤ top208 := by
  obtain ⟨p,rfl⟩ := h
  have bound := sample_bounded samples (fun s => p s.1)
  have sz : samples.length = 208 := by decide +kernel
  rw [sz] at bound
  change bits samples (fun s => p s.1) ≤ 2^208-1
  omega

set_option maxRecDepth 4096 in
theorem input_nd : inputs.Nodup := by decide +kernel
set_option maxRecDepth 4096 in
theorem target_cols : (pack edge).2.1 = top208 ∧ (pack edge).2.2 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem successful_root (cert : SignedLower) {S : Finset Wire} {moves : List Move}
    (tr : ValidTrace gate (pack edge) S moves) (hs : S ⊆ inputs.toFinset)
    (len : moves.length ≤ 14) :
    ∃ v ∈ roots, search 14 v initial = true := by
  let v := inputs.filter (fun w => decide (w∈S))
  have vS : v.toFinset = S := by
    ext a
    simp only [v,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun h => ⟨List.mem_toFinset.mp (hs h),h⟩⟩
  have nodup := input_nd.filter (fun w => decide (w∈S))
  have good : ∀ a ∈ S, Packed a := fun a h => pack_mem_inputs _ (List.mem_toFinset.mp (hs h))
  have cv : ∀ u ∈ v, Packed u := by
    intro a ha
    exact good a (vS ▸ List.mem_toFinset.mpr ha)
  have rb : Bounded moves masks initial := zero_budget _ (fun m hm => by
    rw [len_equal]
    exact collapseBound cert (pack edge) rfl moves (works_trace tr inputs hs) len m hm)
  have covers {T gs} (t : ValidTrace gate (pack edge) T gs) (u : List Wire)
      (eq : u.toFinset = T) (gu : ∀ w∈u, Packed w) : covered u = true :=
    covered_of_trace (eq.symm ▸ t) target_cols.1 target_cols.2 (fun w hw => packed_bounded (gu w hw))
  have mem : v ∈ roots := List.mem_filter.mpr ⟨List.mem_sublists.mpr (List.filter_sublist),covers tr v vS cv⟩
  refine ⟨v,mem,trace_search rfl Packed (@packed_inj) (@covers) ?_ tr v vS nodup cv
    (trace_coherent tr goal_proper good).2 14 len initial rb⟩
  intro T gs t u eq nd m hm
  exact const_length t m u eq nd (target_not_const m hm)
    (collapse_of_const m) (const_gate m)

end Mono2928



namespace Mono2928.FinalBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2928.Co2928

def withOr (i j : Fin 11) (D : Circuit) : Circuit :=
  ⟨⟨.or, [i.val,j.val]⟩ :: D.gates, D.output⟩

lemma withOrEval (i j : Fin 11) (D : Circuit) (w : List Bool) :
    (withOr i j D).eval w = D.eval (w ++ [w.getD i.val false || w.getD j.val false]) := by
  unfold Circuit.eval Circuit.wires withOr
  simp [GateOp.eval]

lemma row_data (r : Fin 512) :
    DataBridge.rowInput r.val = List.ofFn (fun k : Fin 9 => (BitVec.ofFin r : BitVec 9).getLsbD k.val) ++
      [!((BitVec.ofFin r : BitVec 9).getLsbD 0)] := by rfl

lemma row_goal (r : Fin 512) :
    edge r.val = graphResult (fun k : Fin 9 => (BitVec.ofFin r : BitVec 9).getLsbD k.val) := by rfl

theorem deskFromMono
    (noTrace : ∀ (S : Finset Wire) (moves : List (Bool × Wire × Wire)),
      S ⊆ inputs.toFinset → ValidTrace gate (pack edge) S moves → moves.length ≤ 14 → False) :
    ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 ≤ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2 := by
  classical
  intro i j D _ hf hs
  by_cases neg : ∃ g ∈ D.gates, g.op = GateOp.not
  · exact signedTail i j D hf hs (Or.inr (Or.inl neg))
  by_contra! failure
  have legal : ∀ g ∈ (withOr i j D).gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g h
    rcases List.mem_cons.mp h with rfl | hm
    · simp
    obtain ⟨ho,hl⟩ := hf g hm
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ho
    rcases ho with h | h | h
    · exact ⟨Or.inl h,hl⟩
    · exact ⟨Or.inr h,hl⟩
    · exact False.elim (neg ⟨g,hm,h⟩)
  have works : ∀ r < 512, (withOr i j D).eval (DataBridge.rowInput r) = edge r := by
    intro r hr
    let f : Fin 512 := ⟨r,hr⟩
    have q := Classical.not_not.mp (failure (BitVec.ofFin f : BitVec 9))
    rw [withOrEval, row_data f, row_goal f]
    exact q
  obtain ⟨S,moves,hm,tr,_,sub⟩ := DataBridge.extract _ legal works
  apply noTrace S moves (fun a ha => List.mem_toFinset.mpr (sub a ha)) tr
  change moves.length ≤ D.gates.length + 1 at hm
  change D.gates.length ≤ 13 at hs
  omega

end Mono2928.FinalBridge


namespace Bench2928
abbrev Wire := Nat × Nat × Nat

def bits {α : Type} (xs : List α) (p : α → Bool) : Nat :=
  xs.foldr (fun x n => 2 * n + (p x).toNat) 0

def edges : List (Nat × Nat) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
def edge (r : Nat) : Bool := edges.any fun e => r.testBit e.1 && r.testBit e.2
def pos : List Nat := [3,6,12,13,17,24,33,66,132,133,160,264,265,288,320,321]
def neg : List Nat := [42,50,69,104,116,138,200,201,208,261,276,385,402]
def samples : List (Nat × Nat) := pos.flatMap fun a => neg.map fun b => (a,b)
def table (p : Nat → Bool) := bits (List.range 512) p
def pack (p : Nat → Bool) : Wire := (table p, bits samples (fun s => p s.1), bits samples (fun s => p s.2))
def inputs : List Wire := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xfff8000001fff0000003ffe0000007ffc001ffffff8000001fff, 0x5422a11508a845422a11508a845422a11508a845422a11508a84),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xfff80000000000000003ffffff, 0x811c08e047023811c08e047023811c08e047023811c08e047023),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x3ffffff0000000000000fffffffffe000, 0x30a1850c2861430a1850c2861430a1850c2861430a1850c28614),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0x1ffffff80000000000000003ffe000ffffffc000000, 0x7483a41d20e907483a41d20e907483a41d20e907483a41d20e9),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0x3ffffff0000000000000, 0xa89544aa25512a89544aa25512a89544aa25512a89544aa25512),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0x3ffe0000007ffc0000000007ffc0000000000000000000, 0xd806c03601b00d806c03601b00d806c03601b00d806c03601b),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffc0000000000000000000fff80000000000000000000000, 0xee07703b81dc0ee07703b81dc0ee07703b81dc0ee07703b81dc),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0x7fffffffff00000000000000000000000000, 0xcf067833c19e0cf067833c19e0cf067833c19e0cf067833c19e0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffff800000000000000000000000000000000000, 0xf007803c01e00f007803c01e00f007803c01e00f007803c01e00),(0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 0x7fffffe000ffffffc001ffffff8003ffe0000007fffffe000, 0xabdd5eeaf757babdd5eeaf757babdd5eeaf757babdd5eeaf757b)]
def target : Nat := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def top512 : Nat := 2^512-1
def top208 : Nat := 2^208-1
def cuts : List (Nat × Nat) := [(0,4),(1,6),(2,7),(3,4),(8,6),(5,7)]
def masks : List Nat := [0x5555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555000055550000555500005555,0x3333333333333333000000000000000033333333333333330000000000000000333333333333333300000000000000003333333333333333,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f000000000000000000000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff000000ff,0xffffffffffffffff0000000000000000ffffffffffffffff,0xffffffff00000000ffffffff0000000000000000000000000000000000000000ffffffff00000000ffffffff]
def gate (d : Bool) (a b : Wire) : Wire :=
  if d then (a.1 ||| b.1,a.2.1 ||| b.2.1,a.2.2 ||| b.2.2)
  else (a.1 &&& b.1,a.2.1 &&& b.2.1,a.2.2 &&& b.2.2)

def covered (v : List Wire) : Bool :=
  v.foldl (fun t w => t ||| (w.2.1 &&& (top208 ^^^ w.2.2))) 0 == top208
def picks {α : Type} : List α → List (α × List α)
  | [] => []
  | x :: xs => (x,xs) :: (picks xs).map (fun t => (t.1,x :: t.2))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | x :: xs => (picks xs).map (fun t => (x,t.1,t.2)) ++
    (pairs xs).map (fun t => (t.1,t.2.1,x :: t.2.2))

def collapses (m : Nat) (a b z : Wire) : Bool :=
  let f := z.1 &&& m
  f == 0 || f == m || f == a.1 &&& m || f == b.1 &&& m
def charge (a b z : Wire) (spent : List Nat) : List Nat :=
  List.zipWith (fun m c => c + (collapses m a b z).toNat) masks spent
def constants (m : Nat) (v : List Wire) : Nat :=
  v.countP fun w => (w.1 &&& m) == 0 || (w.1 &&& m) == m
def allowed (k : Nat) (v : List Wire) (s : List Nat) : Bool :=
  decide (v.length ≤ k+1) && covered v &&
  (masks.zip s).all (fun p => decide (p.2 + constants p.1 v ≤ 3))
def keeps (a b z : Wire) (rest : List Wire) : List (List Wire) :=
  [z::rest, z::a::rest, z::b::rest, z::a::b::rest]
def fresh (z : Wire) (v : List Wire) : Bool :=
  !(z.1 == 0 || z.1 == top512 || v.any (fun w => w.1 == z.1))
def next (k : Nat) (v : List Wire) (spent : List Nat) : List (List Wire × List Nat) :=
  (pairs v).flatMap fun t => [false,true].flatMap fun d =>
    let a := t.1
    let b := t.2.1
    let z := gate d a b
    let s := charge a b z spent
    if fresh z v then
      ((keeps a b z t.2.2).filter fun u => allowed k u s).map fun u => (u,s)
    else []
def search : Nat → List Wire → List Nat → Bool
  | 0,v,_ => v.any fun w => w.1 == target
  | k+1,v,s => (v.any fun w => w.1 == target) || (next k v s).any (fun p => search k p.1 p.2)
def initial : List Nat := [0,0,0,0,0,0]
def roots := inputs.sublists.filter covered
end Bench2928


namespace Mono2928

set_option maxRecDepth 8192 in
theorem inputs_truth : inputs = Bench2928.inputs := by decide +kernel
set_option maxRecDepth 8192 in
theorem masks_truth : masks = Bench2928.masks := by decide +kernel
set_option maxRecDepth 8192 in
theorem target_truth : target = Bench2928.target := by decide +kernel

theorem picks_literal {α : Type} (v : List α) : picks v = Bench2928.picks v := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp only [picks,Bench2928.picks,ih]

theorem pairs_literal {α : Type} (v : List α) : pairs v = Bench2928.pairs v := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp only [pairs,Bench2928.pairs,picks_literal,ih]

theorem charge_literal (a b z : Wire) (spent : List Nat) :
    charge a b z spent = Bench2928.charge a b z spent := by
  unfold charge Bench2928.charge
  rw [masks_truth]
  rfl

theorem allowed_literal (k : Nat) (v : List Wire) (s : List Nat) :
    allowed k v s = Bench2928.allowed k v s := by
  unfold allowed Bench2928.allowed
  rw [masks_truth]
  rfl

theorem next_literal (k : Nat) (v : List Wire) (s : List Nat) :
    next k v s = Bench2928.next k v s := by
  unfold next Bench2928.next
  simp only [pairs_literal,charge_literal,allowed_literal]
  rfl

theorem search_literal (k : Nat) (v : List Wire) (s : List Nat) :
    search k v s = Bench2928.search k v s := by
  induction k generalizing v s with
  | zero => simp only [search,Bench2928.search,target_truth]
  | succ n ih => simp only [search,Bench2928.search,target_truth,next_literal,ih]

theorem roots_literal : roots = Bench2928.roots := by
  unfold roots Bench2928.roots
  rw [inputs_truth]
  rfl

end Mono2928



namespace Mono2928

lemma any_perm {A : Type} (p : A → Bool) {l m : List A} (h : l.Perm m) :
    l.any p = m.any p := by
  apply Bool.eq_iff_iff.mpr
  simpa only [List.any_eq_true] using
    (show (∃ a ∈ l, p a = true) ↔ (∃ a ∈ m, p a = true) from
      ⟨fun ⟨a,ha,ht⟩ => ⟨a,h.mem_iff.mp ha,ht⟩,fun ⟨a,ha,ht⟩ => ⟨a,h.mem_iff.mpr ha,ht⟩⟩)

lemma fresh_perm (z : Wire) {l m : List Wire} (p : l.Perm m) : fresh z l = fresh z m := by
  unfold fresh
  rw [any_perm _ p]

lemma covered_perm {l m : List Wire} (p : l.Perm m) : covered l = covered m := by
  unfold covered
  congr 1
  apply p.foldl_eq'
  intro x _ y _ z
  simp only [Nat.or_assoc]
  exact congrArg (fun u => z ||| u) (Nat.or_comm _ _)

lemma allowed_perm (k : Nat) (s : List Nat) {l m : List Wire} (p : l.Perm m) :
    allowed k l s = allowed k m s := by
  have co (x : Nat) : constants x l = constants x m := List.Perm.countP_eq _ p
  unfold allowed
  simp only [p.length_eq,covered_perm p,co]

lemma perm_of_pick {A : Type} {v : List A} {a : A} {r : List A} (h : (a,r) ∈ picks v) :
    v.Perm (a::r) := by
  induction v generalizing r with
  | nil => simp [picks] at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with he | ht
    · cases he; exact .refl _
    · obtain ⟨⟨b,s⟩,hm,eq⟩ := List.mem_map.mp ht
      cases eq
      exact ((ih hm).cons x).trans (.swap _ _ _)

lemma perm_of_pair {A : Type} {v : List A} {a b : A} {r : List A}
    (h : (a,b,r) ∈ pairs v) : v.Perm (a::b::r) := by
  induction v generalizing a b r with
  | nil => simp [pairs] at h
  | cons x xs ih =>
    rcases List.mem_append.mp h with hm|hm
    · obtain ⟨⟨y,s⟩,hy,eq⟩ := List.mem_map.mp hm
      cases eq
      exact (perm_of_pick hy).cons _
    · obtain ⟨⟨y,z,s⟩,hy,eq⟩ := List.mem_map.mp hm
      cases eq
      exact ((ih hy).cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _))

lemma keep_perm {a b z : Wire} {r t u : List Wire} (p : r.Perm t)
    (h : u ∈ keeps a b z r) : ∃ v ∈ keeps a b z t, u.Perm v := by
  simp only [keeps,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨_,by simp [keeps],p.cons z⟩
  · exact ⟨_,by simp [keeps],(p.cons a).cons z⟩
  · exact ⟨_,by simp [keeps],(p.cons b).cons z⟩
  · exact ⟨_,by simp [keeps],((p.cons b).cons a).cons z⟩

lemma gate_idem (d : Bool) (a : Wire) : gate d a a = a := by
  cases d <;> simp [gate]

lemma next_intro {k v s a b r d u}
    (pair : (a,b,r) ∈ pairs v) (fr : fresh (gate d a b) v = true)
    (keep : u ∈ keeps a b (gate d a b) r)
    (permits : allowed k u (charge a b (gate d a b) s) = true) :
    (u,charge a b (gate d a b) s) ∈ next k v s := by
  unfold next
  refine List.mem_flatMap.mpr ⟨_,pair,List.mem_flatMap.mpr ⟨d,by cases d <;> simp,?_⟩⟩
  simp only [fr,↓reduceIte]
  exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨keep,permits⟩,rfl⟩

lemma next_perm {k v w s u t} (p : v.Perm w)
    (h : (u,t) ∈ next k v s) : ∃ u', (u',t) ∈ next k w s ∧ u.Perm u' := by
  obtain ⟨⟨a,b,r⟩,pair,hm⟩ := List.mem_flatMap.mp h
  obtain ⟨d,_,hm⟩ := List.mem_flatMap.mp hm
  change (u,t) ∈ (if fresh (gate d a b) v then _ else []) at hm
  split at hm
  next freshv =>
    obtain ⟨u0, hu0, eq⟩ := List.mem_map.mp hm
    cases eq
    obtain ⟨ku,allowv⟩ := List.mem_filter.mp hu0
    have base := perm_of_pair pair
    have ain : a ∈ v := base.mem_iff.mpr (by simp)
    have bin : b ∈ v := base.mem_iff.mpr (by simp)
    have ab : a ≠ b := by
      intro e; subst b
      rw [gate_idem] at freshv
      have yes : v.any (fun x => x.1 == a.1) = true := List.any_eq_true.mpr ⟨a,ain,by simp⟩
      simp [fresh,yes] at freshv
    obtain ⟨r',pm,pw⟩ := pairs_spec (p.mem_iff.mp ain) (p.mem_iff.mp bin) ab
    have pr : r.Perm r' := (base.symm.trans (p.trans pw)).cons_inv.cons_inv
    obtain ⟨u',ku',pu⟩ := keep_perm pr ku
    have fw := (fresh_perm _ p).symm.trans freshv
    have al := (allowed_perm k _ pu).symm.trans allowv
    rcases pm with pf | pb
    · exact ⟨u',next_intro pf fw ku' al,pu⟩
    · obtain ⟨u'',ku'',pu'⟩ := keeps_swap ku'
      have al' := (allowed_perm k _ pu').symm.trans al
      have mem : (u'',charge b a (gate d b a) s) ∈ next k w s := by
        apply next_intro pb
        · simpa only [gate_comm d a b] using fw
        · simpa only [gate_comm d a b] using ku''
        · simpa only [gate_comm d a b,charge_comm a b] using al'
      exact ⟨u'',by simpa only [gate_comm d a b, charge_comm a b] using mem,pu.trans pu'⟩
  next => simp at hm

theorem search_perm (k : Nat) {v w : List Wire} (s : List Nat) (h : v.Perm w) :
    search k v s = search k w s := by
  induction k generalizing v w s with
  | zero => exact any_perm _ h
  | succ k ih =>
    simp only [search,any_perm _ h]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    have one {v w : List Wire} (p : v.Perm w) :
       (∃ z ∈ next k v s, search k z.1 z.2 = true) →
         ∃ z ∈ next k w s, search k z.1 z.2 = true := by
      rintro ⟨⟨u,t⟩,hu,ok⟩
      obtain ⟨u',hm,perm⟩ := next_perm p hu
      exact ⟨⟨u',t⟩,hm,(ih t perm).symm.trans ok⟩
    exact ⟨one h,one h.symm⟩

end Mono2928


namespace Mono2928
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem roots_exact : roots = [inputs.take 9, inputs] := by decide +kernel
end Mono2928


namespace Mono2928

def graphAutomorphisms : List (List Nat) := [[0,1,2,3,4,5,6,7,8],[0,5,8,3,4,1,7,6,2],[1,0,5,8,6,2,4,7,3],[1,2,3,8,6,0,7,4,5],[2,1,0,5,7,3,6,4,8],[2,3,8,5,7,1,4,6,0],[3,2,1,0,4,8,7,6,5],[3,8,5,0,4,2,6,7,1],[5,0,1,2,7,8,4,6,3],[5,8,3,2,7,0,6,4,1],[8,3,2,1,6,5,4,7,0],[8,5,0,1,6,3,7,4,2]]
def rawRepresentatives : List Nat := [0,1,2,4,23]
def mixedRepresentatives : List Nat := [0,1,2,3,4,5,7,8,10,15]
def rawOrbit : List (Nat × Nat) := [(0,0),(1,0),(2,0),(0,1),(4,0),(4,1),(1,1),(0,4),(1,6),(4,2),(1,2),(4,8),(2,2),(0,6),(4,11),(2,3),(4,4),(1,10),(1,7),(4,7),(4,6),(0,7),(4,3),(23,0),(23,1),(4,10),(4,9),(0,5),(23,4),(4,5)]
def mixedOrbit : List (Nat × Nat) := [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(4,1),(7,0),(8,0),(1,1),(10,0),(10,1),(5,1),(3,1),(0,1),(15,0),(7,1)]

end Mono2928


namespace Mono2928
def firstPairs (b : Bool) : List (Nat × Nat) :=
  if b then [(1,2),(1,3),(1,5),(1,7),(1,8),(2,3),(2,5),(2,6),(2,8),(3,5),(3,6),(3,7),(3,8),(5,6),(5,8),(6,7),(7,8)] else [(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3),(1,4),(1,5),(1,7),(1,8),(2,3),(2,4),(2,5),(2,6),(2,8),(3,5),(3,6),(3,7),(3,8),(4,5),(4,6),(4,7),(4,8),(5,6),(5,8),(6,7),(7,8)]
def rootV (b : Bool) := if b then inputs else inputs.take 9
def lit (i : Nat) := inputs.getD i (0,0,0)
def rootPairStep (b : Bool) (ij : Nat × Nat) : List Wire × List Nat :=
  let a := lit ij.1
  let c := lit ij.2
  let z := gate true a c
  let tail := (rootV b).filter (fun u => u != a && u != c)
  (z :: a :: c :: tail, charge a c z initial)
def orbitTable (b : Bool) := if b then mixedOrbit else rawOrbit
def reps (b : Bool) := if b then mixedRepresentatives else rawRepresentatives
def pAt (b : Bool) (i : Nat) := (firstPairs b).getD i (0,0)
def route (b : Bool) (i : Nat) := (orbitTable b).getD i (0,0)
def permAt (j : Nat) := graphAutomorphisms.getD j []
def pairImage (p : List Nat) (ij : Nat × Nat) : Nat × Nat :=
  let a := p.getD ij.1 0
  let c := p.getD ij.2 0
  (min a c, max a c)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem first_moves (b : Bool) :
  next 13 (rootV b) initial = (firstPairs b).map (rootPairStep b) := by
  cases b <;> decide +kernel

set_option maxRecDepth 10000 in
theorem orbit_Fin (b : Bool) :
  ∀ i : Fin (firstPairs b).length,
    (route b i.val).1 ∈ reps b ∧
    (route b i.val).1 < (firstPairs b).length ∧
    (route b i.val).2 < graphAutomorphisms.length ∧
    (pAt b i.val).1 < 9 ∧ (pAt b i.val).2 < 9 ∧
    (pAt b i.val).1 < (pAt b i.val).2 ∧
    pairImage (permAt (route b i.val).2) (pAt b i.val) = pAt b (route b i.val).1 ∧
    (b = true → (permAt (route b i.val).2).getD 0 99 = 0) := by
  cases b <;> decide +kernel
end Mono2928

namespace Mono2928
def uniquePair (b : Bool) (ij : Nat × Nat) : Bool :=
  let v := rootV b
  let x := lit ij.1
  let y := lit ij.2
  let z := gate true x y
  !(v.contains z) && v.all (fun a => v.all (fun c => [false,true].all (fun d =>
    !(gate d a c == z) || (d && ((a == x && c == y) || (a == y && c == x))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pairs_unique (b : Bool) : (firstPairs b).all (uniquePair b) = true := by
  cases b <;> decide +kernel

theorem pair_gate_unique {b : Bool} {ij : Nat × Nat} (hij : ij ∈ firstPairs b)
    {a c : Wire} (ha : a ∈ rootV b) (hc : c ∈ rootV b) (d : Bool)
    (e : gate d a c = gate true (lit ij.1) (lit ij.2)) :
    d = true ∧ ((a = lit ij.1 ∧ c = lit ij.2) ∨ (a = lit ij.2 ∧ c = lit ij.1)) := by
  have hu := List.all_eq_true.mp (pairs_unique b) ij hij
  simp only [uniquePair, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hu
  have h := hu.2 a ha c hc d (by cases d <;> simp)
  simpa [e] using h

theorem pair_gate_fresh {b : Bool} {ij : Nat × Nat} (hij : ij ∈ firstPairs b) :
    gate true (lit ij.1) (lit ij.2) ∉ rootV b := by
  have hu := List.all_eq_true.mp (pairs_unique b) ij hij
  simp only [uniquePair, Bool.and_eq_true, Bool.not_eq_true'] at hu
  simpa using hu.1
end Mono2928


namespace Mono2928.Aut
open Mono2928.DataBridge

def rowMap (p : List Nat) (r : Nat) : Nat := bits p (fun i => r.testBit i)
def wireMap (p : List Nat) (w : Wire) : Wire := pack (fun r => w.1.testBit (rowMap p r))
def mapMoves (p : List Nat) (gs : List Move) := gs.map (fun e => (e.1,wireMap p e.2.1,wireMap p e.2.2))

theorem map_gate (p : List Nat) (d : Bool) (a b : Wire) :
    wireMap p (gate d a b) = gate d (wireMap p a) (wireMap p b) := by
  unfold wireMap
  rw [←pack_join]
  apply congrArg pack
  funext r
  cases d <;> simp [gate,boolOp,Nat.testBit_and,Nat.testBit_or]

set_option maxRecDepth 8192 in
theorem map_injective {p : List Nat} (surj : ∀ i < 512, ∃ j < 512, rowMap p j = i)
    {a b : Wire} (ha : Packed a) (hb : Packed b) (h : wireMap p a = wireMap p b) : a = b := by
  obtain ⟨f,rfl⟩ := ha
  obtain ⟨g,rfl⟩ := hb
  apply pack_ext
  intro i hi
  obtain ⟨j,hj,ej⟩ := surj i hi
  have eq := congrArg (fun w : Wire => w.1.testBit j) h
  change (table _).testBit j = (table _).testBit j at eq
  simpa only [table_read _ hj,ej,pack,table_read _ hi] using eq

set_option maxRecDepth 8192 in
theorem map_target {p : List Nat} (bounds : ∀ j < 512, rowMap p j < 512)
    (ok : ∀ j < 512, edge (rowMap p j) = edge j) :
    wireMap p (pack edge) = pack edge := by
  apply pack_ext
  intro j hj
  exact (table_read edge (bounds j hj)).trans (ok j hj)

theorem trace_map {goal S gs} (tr : ValidTrace gate goal S gs) (p : List Nat)
    (surj : ∀ i < 512, ∃ j < 512, rowMap p j = i)
    (packed : ∀ w∈S, Packed w) :
    ValidTrace gate (wireMap p goal) (S.image (wireMap p)) (mapMoves p gs) := by
  induction tr with
  | stop => simpa [mapMoves] using (ValidTrace.stop (gate:=gate) (goal:=wireMap p goal))
  | @step U a b d gs ne hz tr ih =>
    have pa := packed a (by simp)
    have pb := packed b (by simp)
    have zP := packed_gate d pa pb
    have tailP : ∀ w ∈ insert (gate d a b) U, Packed w := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|hw
      · exact zP
      · exact packed _ (by simp [hw])
    simp only [Finset.image_insert,mapMoves,List.map_cons] at ih ⊢
    rw [map_gate] at ih
    apply ValidTrace.step (fun h => ne (map_injective surj pa pb h)) _ (ih tailP)
    intro hf
    have he : wireMap p (gate d a b) ∈ (insert a (insert b U)).image (wireMap p) := by
      simpa only [Finset.image_insert,map_gate] using hf
    obtain ⟨w,hw,h⟩ := Finset.mem_image.mp he
    exact hz ((map_injective surj (packed w hw) zP h) ▸ hw)

end Mono2928.Aut


namespace Mono2928.Aut

def inverseIdx (j : Nat) := [0,1,2,8,4,11,6,7,3,9,10,5].getD j 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
theorem perm_rows (g : Fin 12) : ∀ j : Fin 512,
    rowMap (permAt g) j < 512 ∧ rowMap (permAt (inverseIdx g)) j < 512 ∧
    rowMap (permAt g) (rowMap (permAt (inverseIdx g)) j) = j ∧
    edge (rowMap (permAt g) j) = edge j := by
  revert g
  decide +kernel

theorem group_bounds {g : Nat} (hg : g < graphAutomorphisms.length) :
    (∀ j < 512, rowMap (permAt g) j < 512) ∧
    (∀ i < 512, ∃ j < 512, rowMap (permAt g) j = i) ∧ wireMap (permAt g) (pack edge) = pack edge := by
  have g12 : g < 12 := hg
  let k : Fin 12 := ⟨g,g12⟩
  have bound (j : Nat) (hj : j<512) := (perm_rows k ⟨j,hj⟩).1
  refine ⟨bound,?_,map_target bound (fun j hj => (perm_rows k ⟨j,hj⟩).2.2.2)⟩
  intro i hi
  exact ⟨_,(perm_rows k ⟨i,hi⟩).2.1,(perm_rows k ⟨i,hi⟩).2.2.1⟩

end Mono2928.Aut


namespace Mono2928.Aut
open DataBridge
open PEqualNP.Outside.L_meta_2928.CoThetaNine
open PEqualNP.Outside.L_meta_2928.SliceData

abbrev Goal := pack edge
set_option maxRecDepth 8192 in
abbrev fullBudget {S gs} (tr : ValidTrace gate Goal S gs) (cs : SignedLower) (hs : S ⊆ inputs.toFinset)
    (hl : gs.length ≤ 14) : Bounded gs masks initial :=
  zero_budget _ (fun m hm => by
    rw [len_equal]
    exact collapseBound cs Goal rfl gs (works_trace tr inputs hs) hl m hm)

set_option maxRecDepth 8192 in
theorem good_covered {S gs} (t : ValidTrace gate Goal S gs) (u : List Wire) (e : u.toFinset=S)
    (p : ∀ w∈u, Packed w) : covered u = true :=
  covered_of_trace (e.symm ▸ t) target_cols.1 target_cols.2 (fun _ h => packed_bounded (p _ h))

set_option maxRecDepth 8192 in
theorem good_future {S gs} (t : ValidTrace gate Goal S gs) (u : List Wire) (e : u.toFinset=S)
    (nd : u.Nodup) (m : Nat) (hm : m∈masks) :
    constants m u ≤ (gs.filter (cost m)).length :=
  const_length t m u e nd (target_not_const m hm) (collapse_of_const m) (const_gate m)

set_option maxRecDepth 8192 in
theorem accepts {S gs} (t : ValidTrace gate Goal S gs) {u : List Wire} (e : u.toFinset=S)
    (nd : u.Nodup) (p : ∀ w∈u, Packed w) (k : Nat) (h : gs.length ≤ k) (s : List Nat)
    (bb : Bounded gs masks s) : search k u s=true :=
  trace_search rfl Packed (@packed_inj) (@good_covered) (@good_future) t u e nd p
    (trace_coherent t goal_proper (fun a ha => p a (List.mem_toFinset.mp (e.symm ▸ ha)))).2 k h s bb

set_option maxRecDepth 8192 in
theorem first_state {U a b d gs} (t : ValidTrace gate Goal (insert (gate d a b) U) gs)
    (ne : a ≠ b) (nf : gate d a b ∉ insert a (insert b U)) (cert : SignedLower)
    (v : List Wire) (e : v.toFinset = insert a (insert b U)) (nd : v.Nodup)
    (hs : insert a (insert b U) ⊆ inputs.toFinset) (hl : gs.length ≤ 13) :
    ∃ u, (u,charge a b (gate d a b) initial)∈next 13 v initial ∧
      u.Nodup ∧ u.toFinset = insert (gate d a b) U := by
  have allp : ∀ w∈insert a (insert b U), Packed w := fun w hw => pack_mem_inputs _ (List.mem_toFinset.mp (hs hw))
  have tr := ValidTrace.step ne nf t
  have valid := (trace_coherent tr goal_proper allp).2 (d,a,b) (by simp)
  have Hz : gate d a b ∉ v.toFinset := e ▸ nf
  have fr : fresh (gate d a b) v = true := by
    simp only [fresh,Bool.not_eq_true',Bool.or_eq_false_iff,beq_eq_false_iff_ne,List.any_eq_false]
    refine ⟨⟨valid.2.1,valid.2.2⟩,?_⟩
    intro w hw eq
    exact Hz (List.mem_toFinset.mpr ((packed_inj (allp w (e ▸ List.mem_toFinset.mpr hw)) valid.1
      (beq_iff_eq.mp eq)) ▸ hw))
  have bf := charge_bounded (fullBudget tr cert hs (by simp only [List.length_cons]; omega))
  apply next_exists ne nd e fr Hz
  intro u un us
  have gu : ∀ w∈u, Packed w := by
    intro w hw
    have hh := us ▸ List.mem_toFinset.mpr hw
    obtain rfl|mem := Finset.mem_insert.mp hh
    · exact valid.1
    · exact allp _ (by simp [mem])
  have ce := good_covered t u us gu
  have len := trace_length_bound t
  rw [←us,List.toFinset_card_of_nodup un] at len
  simp only [allowed,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  refine ⟨⟨by omega,ce⟩,?_⟩
  intro p hp
  have hz := budget_zip bf p hp
  have cf := good_future t u us un p.1 (List.of_mem_zip hp).1
  omega

theorem startRoot {S gs} (tr : ValidTrace gate Goal S gs) (h : S ⊆ inputs.toFinset) :
    ∃ b, (rootV b).toFinset = S ∧ (rootV b).Nodup := by
  let v := inputs.filter (fun w => decide (w∈S))
  have vS : v.toFinset = S := by
    ext a
    simp only [v,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    exact ⟨And.right,fun ha => ⟨List.mem_toFinset.mp (h ha),ha⟩⟩
  have vn := input_nd.filter (fun w => decide (w∈S))
  have cv := good_covered tr v vS (fun w hw => pack_mem_inputs w
    (List.mem_toFinset.mp (h (vS ▸ List.mem_toFinset.mpr hw))))
  have hh : v ∈ roots := List.mem_filter.mpr ⟨List.mem_sublists.mpr List.filter_sublist,cv⟩
  rw [roots_exact] at hh
  rcases List.mem_cons.mp hh with he|hm
  · exact ⟨false,by change (inputs.take 9).toFinset = S; rw [←he]; exact vS,by change (inputs.take 9).Nodup; rw [←he]; exact vn⟩
  · have he := List.mem_singleton.mp hm
    exact ⟨true,by change inputs.toFinset = S; rw [←he]; exact vS,by change inputs.Nodup; rw [←he]; exact vn⟩

end Mono2928.Aut


namespace Mono2928
open DataBridge
open Aut

def stub (p : List Nat) (w : Wire) : Wire :=
  let j := inputs.idxOf w
  if j = 9 then lit 9 else lit (p.getD j 0)
def movedList (p : List Nat) (b : Bool) (ij : Nat × Nat) : List Wire :=
  let a := stub p (lit ij.1)
  let c := stub p (lit ij.2)
  gate true a c :: ((rootPairStep b ij).1.tail.map (stub p))

set_option maxRecDepth 4096 in
theorem lit_form (i : Fin 9) : lit i.val = pack (fun r => r.testBit i.val) := by
  unfold lit inputs
  rw [List.getD_append _ _ _ _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp
theorem lit_neg : lit 9 = pack (fun r => !r.testBit 0) := by rfl

theorem row_read {p : List Nat} {i : Nat} (hi : i < p.length) (r : Nat) :
    (rowMap p r).testBit i = r.testBit (p.getD i 0) := by
  simp only [rowMap,bits_read]
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi]
  simp

def boundCheck (p : List Nat) := p.length == 9 && p.all (· < 9)
theorem p_bounds {j : Nat} (hj : j < graphAutomorphisms.length) :
    (permAt j).length = 9 ∧ ∀ x ∈ permAt j, x < 9 := by
  have h : ∀ i : Fin graphAutomorphisms.length, boundCheck (permAt i.val) = true := by decide +kernel
  simpa [boundCheck] using h ⟨j,hj⟩

theorem row_bound {p : List Nat} (h : p.length = 9) (r : Nat) : rowMap p r < 512 := by
  have aux {A : Type} (xs : List A) (q : A → Bool) : bits xs q < 2^xs.length := by
    induction xs with
    | nil => simp [bits]
    | cons x xs ih =>
      change 2 * bits xs q + (q x).toNat < 2^(xs.length+1)
      rw [Nat.pow_succ]
      cases q x <;> simp <;> omega
  simpa [rowMap,h] using aux p (fun x => r.testBit x)

set_option maxRecDepth 16384 in
theorem map_lit {p : List Nat} {i : Fin 9} (hl : p.length = 9)
    (hbound : ∀ x ∈ p, x < 9) : wireMap p (lit i.val) = lit (p.getD i.val 0) := by
  have hi : i.val < p.length := by simpa only [hl] using i.isLt
  have hget : p.getD i.val 0 ∈ p := by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  rw [lit_form i,lit_form (⟨p.getD i.val 0,hbound _ hget⟩ : Fin 9)]
  apply pack_ext
  intro r hr
  change (table _).testBit (rowMap p r) = _
  rw [table_read _ (row_bound hl r),row_read hi]

set_option maxRecDepth 16384 in
theorem map_neg {p : List Nat} (hl : p.length=9) (hf : p.getD 0 0=0) :
    wireMap p (lit 9) = lit 9 := by
  rw [lit_neg]
  apply pack_ext
  intro r hr
  change (table _).testBit (rowMap p r) = _
  rw [table_read _ (row_bound hl r)]
  rw [row_read (by omega : 0 < p.length), hf]

theorem lit_idx (i : Fin 10) : inputs.idxOf (lit i.val) = i.val := by
  exact (by decide +kernel : ∀ j : Fin 10, inputs.idxOf (lit j.val) = j.val) i

theorem root_which (b : Bool) : ∀ w ∈ rootV b,
    ∃ i : Fin 10, w = lit i.val ∧ (i.val < 9 ∨ b=true) := by
  have base (bb : Bool) : (rootV bb).all (fun w => (List.finRange 10).any (fun i => w == lit i.val && (decide (i.val < 9) || bb))) = true := by
    cases bb <;> decide +kernel
  intro w hw
  have h := List.all_eq_true.mp (base b) w hw
  simpa using h

set_option maxRecDepth 16384 in
theorem map_stub (b : Bool) (i : Fin (firstPairs b).length) :
    let p := permAt (route b i.val).2
    ∀ w ∈ rootV b, wireMap p w = stub p w := by
  dsimp only
  intro w hw
  let p := permAt (route b i.val).2
  rcases root_which b w hw with ⟨j,rfl,hj⟩
  rcases orbit_Fin b i with ⟨_,_,hcode,_,_,_,_,hfix⟩
  have ⟨hl,hsmall⟩ := p_bounds hcode
  unfold stub
  rw [lit_idx j]
  by_cases h9 : j.val = 9
  · have hb : b=true := hj.resolve_left (by omega)
    have hlen : p.length = 9 := hl
    have hp : 0 < p.length := by rw [hlen]; decide
    have hfi : p.getD 0 0=0 := by
      have h : p.getD 0 99 = 0 := hfix hb
      rw [List.getD_eq_getElem _ _ hp] at h ⊢
      exact h
    simpa only [h9,if_pos] using map_neg hl hfi
  · have lt : j.val < 9 := by omega
    simpa only [if_neg h9] using map_lit (i:=⟨j.val,lt⟩) hl hsmall
end Mono2928


namespace Fast
open Bench2928
def coverOf (z : Wire) := z.2.1 &&& (top208 ^^^ z.2.2)
def coverWord (v : List Wire) : Nat := v.foldl (fun acc w => acc ||| coverOf w) 0
def check (k len : Nat) (a b z : Wire) (s : List Nat) (rest : List Wire) (cva cvb cvz : Nat) (ka kb : Bool) : Bool :=
  decide (len + 1 + ka.toNat + kb.toNat ≤ k+1) &&
  (cvz ||| (if ka then cva else 0) ||| (if kb then cvb else 0)) == top208 &&
  (masks.zip s).all fun (m,sc) =>
    let f := z.1 &&& m
    let va := a.1 &&& m
    let vb := b.1 &&& m
    let cz := f == 0 || f == m
    let inc := (cz || f == va || f == vb).toNat
    let ca := (ka && (va == 0 || va == m)).toNat
    let cb := (kb && (vb == 0 || vb == m)).toNat
    decide (sc + inc + cz.toNat + ca + cb + constants m rest ≤ 3)
def fastNext (k : Nat) (v : List Wire) (s : List Nat) : List (List Wire × List Nat) :=
  (pairs v).flatMap fun t =>
    let a := t.1
    let b := t.2.1
    let rest := t.2.2
    let cv := coverWord rest
    let ca := coverOf a
    let cb := coverOf b
    let len := rest.length
    [false,true].flatMap fun d =>
      let z := gate d a b
      let sz := charge a b z s
      let cz := cv ||| coverOf z
      if fresh z v then
        [(false,false),(true,false),(false,true),(true,true)].filterMap fun (ka,kb) =>
          if check k len a b z s rest ca cb cz ka kb then
            some (z::((if ka then [a] else []) ++ ((if kb then [b] else []) ++ rest)),sz)
          else none
      else []
def seek : Nat → List Wire → List Nat → Bool
  | 0,v,_ => v.any fun w => w.1 == target
  | k+1,v,s => (v.any fun w => w.1 == target) || (fastNext k v s).any (fun p => seek k p.1 p.2)
def singleFast (j : Nat) := match (fastNext 13 inputs initial)[j]? with
  | none => false
  | some (u,s) => seek 13 u s
end Fast


namespace Fast
open Bench2928

theorem cov_acc (v : List Wire) (n : Nat) :
    v.foldl (fun x w => x ||| coverOf w) n = n ||| coverWord v := by
  induction v generalizing n with
  | nil => simp [coverWord]
  | cons w v ih =>
    change v.foldl _ (n ||| coverOf w) = n ||| v.foldl _ (0 ||| coverOf w)
    rw [ih (n ||| _),ih (0 ||| _)]
    simp [Nat.or_assoc]

theorem cov_cons (a : Wire) (v : List Wire) : coverWord (a::v) = coverOf a ||| coverWord v := by
  change v.foldl _ (0 ||| coverOf a) = _
  rw [cov_acc]
  simp

def kept (a b z : Wire) (r : List Wire) (x y : Bool) :=
  z :: ((if x then [a] else []) ++ ((if y then [b] else []) ++ r))

theorem or_left_exchange (a b c : Nat) : a ||| (b ||| c) = b ||| (a ||| c) := by
  rw [←Nat.or_assoc,Nat.or_comm a b,Nat.or_assoc]

theorem cov_kept (a b z : Wire) (r : List Wire) (x y : Bool) :
    covered (kept a b z r x y) =
     ((coverWord r ||| coverOf z ||| (if x then coverOf a else 0) ||| (if y then coverOf b else 0)) == top208) := by
  change (coverWord _ == _) = _
  cases x <;> cases y <;> simp [kept,cov_cons,Nat.or_comm,or_left_exchange,Nat.or_assoc]

def bump (m : Nat) (u : Wire) := ((u.1 &&& m == 0) || (u.1 &&& m == m)).toNat

theorem counts_kept (m : Nat) (a b z : Wire) (r : List Wire) (x y : Bool) :
    constants m (kept a b z r x y) =
      constants m r + bump m z + (if x then bump m a else 0) + (if y then bump m b else 0) := by
  cases x <;> cases y <;> simp [constants,kept,bump,List.countP_cons, Bool.toNat, Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] <;> omega

theorem charge_all {p : Nat → Nat → Bool} (ms s : List Nat) (a b z : Wire) :
    (ms.zip (List.zipWith (fun m c => c + (collapses m a b z).toNat) ms s)).all (fun e => p e.1 e.2) =
    (ms.zip s).all (fun e => p e.1 (e.2 + (collapses e.1 a b z).toNat)) := by
  induction ms generalizing s with
  | nil => simp
  | cons m ms ih => cases s with
    | nil => rfl
    | cons n s => simp only [List.zipWith_cons_cons,List.zip_cons_cons,List.all_cons,ih]

theorem allowed_kept (k : Nat) (a b z : Wire) (r : List Wire) (s : List Nat) (x y : Bool) :
    allowed k (kept a b z r x y) (charge a b z s) =
      check k r.length a b z s r (coverOf a) (coverOf b) (coverWord r ||| coverOf z) x y := by
  have ll : (kept a b z r x y).length = r.length+1+x.toNat+y.toNat := by
    cases x <;> cases y <;> simp [kept] <;> omega
  unfold allowed check charge
  rw [ll,cov_kept,charge_all (p:=fun m c => decide (c+constants m (kept a b z r x y) ≤3))]
  congr 1
  apply congrArg (fun pred => (masks.zip s).all pred)
  funext q
  obtain ⟨m,c⟩ := q
  rw [counts_kept]
  cases x <;> cases y <;> simp [collapses,bump, Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem kept_filter (k : Nat) (a b z : Wire) (r : List Wire) (s : List Nat) :
    ((keeps a b z r).filter (fun u => allowed k u (charge a b z s))).map (fun u => (u,charge a b z s)) =
      [(false,false),(true,false),(false,true),(true,true)].filterMap (fun (x,y) =>
        if check k r.length a b z s r (coverOf a) (coverOf b) (coverWord r ||| coverOf z) x y then
          some (kept a b z r x y,charge a b z s) else none) := by
  let f := fun (p : Bool × Bool) => kept a b z r p.1 p.2
  let pred := fun u => allowed k u (charge a b z s)
  let mk := fun (u : List Wire) => (u,charge a b z s)
  have gen (ps : List (Bool × Bool)) :
      ((ps.map f).filter pred).map mk = ps.filterMap (fun p =>
        if pred (f p) then some (mk (f p)) else none) := by
    induction ps with
    | nil => rfl
    | cons p ps ih => cases hp : pred (f p) <;> simp [hp,ih]
  have eq : keeps a b z r = [(false,false),(true,false),(false,true),(true,true)].map f := rfl
  rw [eq]
  change ((List.map f _).filter pred).map mk = _
  rw [gen]
  apply congrArg (List.filterMap · _)
  funext p
  cases p with
  | mk x y => simp only [f,pred,mk,allowed_kept]

theorem next_fast (k : Nat) (v : List Wire) (s : List Nat) : next k v s = fastNext k v s := by
  unfold next fastNext
  apply congrArg (List.flatMap · _)
  funext q
  obtain ⟨a,b,r⟩ := q
  apply congrArg (List.flatMap · _)
  funext d
  dsimp only
  split <;> first | exact kept_filter _ _ _ _ _ _ | rfl

theorem search_fast (k : Nat) (v : List Wire) (s : List Nat) : search k v s = seek k v s := by
  induction k generalizing v s with
  | zero => rfl
  | succ k ih => simp only [search,seek,next_fast,ih]

end Fast


namespace Quickest
open Bench2928
def cov (w : Wire) := w.2.1 &&& (top208 ^^^ w.2.2)
def counts (v : List Wire) : Nat × Nat × Nat :=
  v.foldl (fun (t : Nat × Nat × Nat) w =>
    let j:=cov w
    (t.1 ||| j,t.2.1 ||| (t.1 &&& j),t.2.2 ||| (t.2.1 &&& j))) (0,0,0)
def budgets (s : List Nat) (v : List Wire) := (masks.zip s).map fun (m,c) => (m,c+constants m v)
def check (kk ll : Nat) (ones twos ca cb cz : Nat) (bad : List (Nat × Nat)) (a b z : Wire) (ka kb : Bool) : Bool :=
  decide (ll + ka.toNat + kb.toNat ≤ kk+2) &&
  (let aa := if ka then 0 else ca
   let bb := if kb then 0 else cb
   let del := (ones &&& (aa ||| bb)) ||| (twos &&& aa &&& bb)
   del &&& (top208 ^^^ cz) == 0) &&
  bad.all (fun (m,n) =>
    let f := z.1 &&& m
    let av := a.1 &&& m
    let bv := b.1 &&& m
    let zeroz := f==0 || f==m
    decide (n + (zeroz || f==av || f==bv).toNat + zeroz.toNat ≤ 3+(!ka && (av==0 || av==m)).toNat+(!kb && (bv==0 || bv==m)).toNat))
def qnext (k : Nat) (v : List Wire) (s : List Nat) :=
  let l:=v.length
  let t:=counts v
  let one:=t.1 ^^^ t.2.1
  let two:=t.2.1 ^^^ t.2.2
  let bud:=budgets s v
  (pairs v).flatMap fun (a,b,rest) =>
    let ca:=cov a
    let cb:=cov b
    [false,true].flatMap fun d =>
      let z:=gate d a b
      let cs:=charge a b z s
      let cz:=cov z
      if fresh z v then
        [(false,false),(true,false),(false,true),(true,true)].filterMap fun (ka,kb) =>
          if check k l one two ca cb cz bud a b z ka kb then
            some (z::((if ka then [a] else []) ++ ((if kb then [b] else []) ++ rest)),cs)
          else none
      else []
def seek : Nat → List Wire → List Nat → Bool
  | 0,v,_ => v.any fun w => w.1 == target
  | k+1,v,s => (v.any fun w => w.1 == target) || (qnext k v s).any (fun p => seek k p.1 p.2)
def singleQ (j : Nat) := match (qnext 13 inputs initial)[j]? with
  | none => false
  | some (u,s) => seek 13 u s
end Quickest

namespace QuickProof
open Bench2928

theorem rbit (k : Nat) (r : List Wire) : (Fast.coverWord r).testBit k =
    decide (0 < r.countP (fun w => (Quickest.cov w).testBit k)) := by
  induction r with
  | nil => simp [Fast.coverWord]
  | cons w r ih =>
    rw [Fast.cov_cons,Nat.testBit_or,ih]
    change ((Quickest.cov w).testBit k || _) = _
    cases e : (Quickest.cov w).testBit k <;> simp only [List.countP_cons,e,Bool.false_eq_true,↓reduceIte,Bool.false_or,Bool.true_or,Nat.add_zero,Nat.zero_lt_succ,decide_true]

def chkbit (n : Nat) (a b z top x y : Bool) : Prop :=
  (((decide (0 < n) || z) || (if x then a else false)) || (if y then b else false)) = top →
  let l := n + a.toNat + b.toNat
  let aa := if x then false else a
  let bb := if y then false else b
  (((decide (l=1) && (aa || bb)) || (decide (l=2) && aa && bb)) && (top ^^ z)) = false

theorem bit_result (n : Nat) (a b z top x y : Bool) : chkbit n a b z top x y := by
  have finit : ∀ (n : Fin 3) (a b z top x y : Bool), chkbit n.val a b z top x y := by unfold chkbit; decide
  by_cases h : n < 3
  · exact finit ⟨n,h⟩ a b z top x y
  · unfold chkbit
    have ne1 : n+a.toNat+b.toNat ≠ 1 := by omega
    have ne2 : n+a.toNat+b.toNat ≠ 2 := by omega
    simp [ne1,ne2]

theorem check_sufficient {k : Nat} {v r : List Wire} {s : List Nat} {a b z : Wire} {x y : Bool}
    (perm : v.Perm (a::b::r))
    (bitOne : ∀ i, ((Quickest.counts v).1 ^^^ (Quickest.counts v).2.1).testBit i =
      decide ((v.countP (fun w => (Quickest.cov w).testBit i)) = 1))
    (bitTwo : ∀ i, ((Quickest.counts v).2.1 ^^^ (Quickest.counts v).2.2).testBit i =
      decide ((v.countP (fun w => (Quickest.cov w).testBit i)) = 2))
    (passed : Fast.check k r.length a b z s r (Fast.coverOf a) (Fast.coverOf b)
      (Fast.coverWord r ||| Fast.coverOf z) x y = true) :
    Quickest.check k v.length
      ((Quickest.counts v).1 ^^^ (Quickest.counts v).2.1)
      ((Quickest.counts v).2.1 ^^^ (Quickest.counts v).2.2)
      (Quickest.cov a) (Quickest.cov b) (Quickest.cov z) (Quickest.budgets s v) a b z x y = true := by
  simp only [Fast.check,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true] at passed
  obtain ⟨⟨ll,cv⟩,cuts⟩ := passed
  simp only [Quickest.check,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true]
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [perm.length_eq]; simp only [List.length_cons]; omega
  · apply Nat.eq_of_testBit_eq
    intro i
    have hc := congrArg (fun t : Nat => t.testBit i) cv
    simp only [Nat.testBit_or,Fast.coverOf,rbit] at hc
    have cnt := List.Perm.countP_eq (fun w : Wire => (Quickest.cov w).testBit i) perm
    simp only [List.countP_cons] at cnt
    let n := r.countP (fun w => (Quickest.cov w).testBit i)
    let aa := (Quickest.cov a).testBit i
    let bb := (Quickest.cov b).testBit i
    have cn : v.countP (fun w => (Quickest.cov w).testBit i) = n+aa.toNat+bb.toNat := by
      dsimp [n,aa,bb]; rw [cnt]; cases (Quickest.cov a).testBit i <;> cases (Quickest.cov b).testBit i <;> simp <;> omega
    have cd := bit_result n aa bb ((Quickest.cov z).testBit i) (top208.testBit i) x y
    unfold chkbit at cd
    simp only [Nat.testBit_and,Nat.testBit_zero,Nat.testBit_or,bitOne i,bitTwo i,cn,Nat.testBit_xor]
    cases x <;> cases y <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.zero_testBit] at hc cd ⊢ <;> exact cd hc
  · intro mc hm
    obtain ⟨⟨m,c⟩,mem,rfl⟩ := List.mem_map.mp hm
    specialize cuts (m,c) mem
    have tot : constants m v = constants m r + Fast.bump m a + Fast.bump m b := by
      change v.countP _ = _
      rw [perm.countP_eq]
      simp only [List.countP_cons,constants,Fast.bump]
      cases (a.1 &&& m == 0 || a.1 &&& m == m) <;> cases (b.1 &&& m == 0 || b.1 &&& m == m) <;> simp <;> omega
    dsimp only at cuts ⊢
    rw [tot]
    cases x <;> cases y <;> simp [Fast.bump,Bool.toNat] at cuts ⊢ <;> omega

end QuickProof



namespace Quickest

open Bench2928

def multiplicity (v : List Wire) (j : Nat) : Nat :=
  v.countP fun w => (cov w).testBit j

lemma arithmetic (n : Nat) (b : Bool) :
    (decide (1 ≤ n) || b) = decide (1 ≤ n + b.toNat) ∧
    (decide (2 ≤ n) || (decide (1 ≤ n) && b)) = decide (2 ≤ n + b.toNat) ∧
    (decide (3 ≤ n) || (decide (2 ≤ n) && b)) = decide (3 ≤ n + b.toNat) := by
  rcases n with _|n
  · cases b <;> decide
  rcases n with _|n
  · cases b <;> decide
  rcases n with _|n
  · cases b <;> decide
  have h1 : 1 ≤ n+1+1+1 := by omega
  have h2 : 2 ≤ n+1+1+1 := by omega
  have h3 : 3 ≤ n+1+1+1 := by omega
  have g1 : 1 ≤ n+1+1+1+b.toNat := by omega
  have g2 : 2 ≤ n+1+1+1+b.toNat := by omega
  have g3 : 3 ≤ n+1+1+1+b.toNat := by omega
  simp only [h1,h2,h3,g1,g2,g3,decide_true,Bool.true_or,true_and]

theorem counts_at (v : List Wire) (j : Nat) :
    (counts v).1.testBit j = decide (1 ≤ multiplicity v j) ∧
    (counts v).2.1.testBit j = decide (2 ≤ multiplicity v j) ∧
    (counts v).2.2.testBit j = decide (3 ≤ multiplicity v j) := by
  induction v using List.reverseRecOn with
  | nil => simp [counts,multiplicity]
  | append_singleton vs w ih =>
    obtain ⟨h1,h2,h3⟩ := ih
    let n := multiplicity vs j
    have updated : multiplicity (vs ++ [w]) j = n + ((cov w).testBit j).toNat := by
      cases h : (cov w).testBit j <;> simp [n,multiplicity,List.countP_append,h]
    have fold : counts (vs ++ [w]) =
        ((counts vs).1 ||| cov w, (counts vs).2.1 ||| ((counts vs).1 &&& cov w),
          (counts vs).2.2 ||| ((counts vs).2.1 &&& cov w)) := by
      simp [counts,List.foldl_append]
    simp only [fold,Nat.testBit_or,Nat.testBit_and,h1,h2,h3,updated]
    exact arithmetic n _

theorem unique_at (v : List Wire) (j : Nat) :
    ((counts v).1 ^^^ (counts v).2.1).testBit j = decide (multiplicity v j = 1) := by
  obtain ⟨h1,h2,_⟩ := counts_at v j
  rw [Nat.testBit_xor,h1,h2]
  generalize multiplicity v j = n
  rcases n with _|n
  · decide
  rcases n with _|n
  · decide
  have h1 : 1 ≤ n+1+1 := by omega
  have h2 : 2 ≤ n+1+1 := by omega
  have hn : n+1+1 ≠ 1 := by omega
  simp only [h1,h2,hn,decide_true,decide_false]; rfl

theorem double_at (v : List Wire) (j : Nat) :
    ((counts v).2.1 ^^^ (counts v).2.2).testBit j = decide (multiplicity v j = 2) := by
  obtain ⟨_,h2,h3⟩ := counts_at v j
  rw [Nat.testBit_xor,h2,h3]
  generalize multiplicity v j = n
  rcases n with _|n
  · decide
  rcases n with _|n
  · decide
  rcases n with _|n
  · decide
  have h2 : 2 ≤ n+1+1+1 := by omega
  have h3 : 3 ≤ n+1+1+1 := by omega
  have hn : n+1+1+1 ≠ 2 := by omega
  simp only [h2,h3,hn,decide_true,decide_false]; rfl

lemma one_at (v : List Wire) (k : Nat) :
    ((counts v).1 ^^^ (counts v).2.1).testBit k = true ↔ v.countP (fun w => (cov w).testBit k) = 1 := by
  rw [unique_at]; exact decide_eq_true_iff

lemma two_at (v : List Wire) (k : Nat) :
    ((counts v).2.1 ^^^ (counts v).2.2).testBit k = true ↔ v.countP (fun w => (cov w).testBit k) = 2 := by
  rw [double_at]; exact decide_eq_true_iff

end Quickest


namespace QuickProof
open Bench2928

theorem next_quick_correct {k : Nat} {v : List Wire} {s : List Nat} {out : List Wire × List Nat}
    (hm : out ∈ next k v s) : out ∈ Quickest.qnext k v s := by
  rw [Fast.next_fast] at hm
  unfold Fast.fastNext at hm
  obtain ⟨⟨a,b,r⟩,pair,h⟩ := List.mem_flatMap.mp hm
  obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp h
  unfold Quickest.qnext
  apply List.mem_flatMap.mpr
  refine ⟨(a,b,r),pair,List.mem_flatMap.mpr ⟨d,hd,?_⟩⟩
  dsimp only at h ⊢
  split at h
  next ef =>
    rw [if_pos ef]
    obtain ⟨⟨x,y⟩,flags,go⟩ := List.mem_filterMap.mp h
    apply List.mem_filterMap.mpr
    refine ⟨(x,y),flags,?_⟩
    dsimp only at go ⊢
    split at go
    next ok =>
      have perm := Mono2928.perm_of_pair (v:=v) (by rw [Mono2928.pairs_literal]; exact pair)
      have o (i : Nat) := Bool.eq_iff_iff.mpr ((Quickest.one_at v i).trans decide_eq_true_iff.symm)
      have t (i : Nat) := Bool.eq_iff_iff.mpr ((Quickest.two_at v i).trans decide_eq_true_iff.symm)
      have q := check_sufficient perm o t ok
      rw [if_pos q]
      exact go
    next => simp_all
  next => simp at h

theorem quick_correct {k : Nat} {v : List Wire} {s : List Nat} (h : search k v s = true) :
    Quickest.seek k v s = true := by
  induction k generalizing v s with
  | zero => exact h
  | succ k ih =>
    simp only [search,Bool.or_eq_true,List.any_eq_true] at h
    simp only [Quickest.seek,Bool.or_eq_true,List.any_eq_true]
    rcases h with h | ⟨q,hq,ht⟩
    · exact Or.inl h
    · exact Or.inr ⟨q,next_quick_correct hq,ih ht⟩
end QuickProof


namespace Hot
open Bench2928 Quickest
def flags (k n : Nat) : List (Bool × Bool) :=
  if n > k+2 then [] else if n == k+2 then [(false,false)]
  else if n == k+1 then [(false,false),(true,false),(false,true)]
  else [(false,false),(true,false),(false,true),(true,true)]
def nextH (k : Nat) (v : List Wire) (s : List Nat) : List (List Wire × List Nat) :=
  let l := v.length
  let t := counts v
  let one := t.1 ^^^ t.2.1
  let two := t.2.1 ^^^ t.2.2
  let bud := budgets s v
  let choices := flags k l
  (pairs v).flatMap fun (a,b,rest) =>
    let ca:=cov a
    let cb:=cov b
    [false,true].flatMap fun d =>
      let z:=gate d a b
      let cs:=charge a b z s
      let cz:=cov z
      choices.filterMap fun (ka,kb) =>
        if check k l one two ca cb cz bud a b z ka kb && fresh z v then
          some (z::((if ka then [a] else []) ++ ((if kb then [b] else []) ++ rest)),cs)
        else none
end Hot

namespace Hot
open Bench2928 Quickest

def allChoices : List (Bool × Bool) := [(false,false),(true,false),(false,true),(true,true)]

theorem flags_filter {α : Type} (k n : Nat) (f : Bool × Bool → Option α)
    (hf : ∀ x y : Bool, k + 2 < n + x.toNat + y.toNat → f (x,y) = none) :
    (flags k n).filterMap f = allChoices.filterMap f := by
  have f00 := hf false false
  have f10 := hf true false
  have f01 := hf false true
  have f11 := hf true true
  simp only [Bool.toNat_false,Bool.toNat_true] at f00 f10 f01 f11
  by_cases h : n > k+2
  · simp [flags,allChoices,h,f00 (by omega),f10 (by omega),f01 (by omega),f11 (by omega)]
  by_cases h2 : n = k+2
  · simp [flags,allChoices,h,h2,f10 (by omega),f01 (by omega),f11 (by omega),List.filterMap_cons]
  by_cases h1 : n = k+1
  · simp [flags,allChoices,h,h2,h1,f11 (by omega),List.filterMap_cons]
  · simp [flags,allChoices,h,h2,h1]

theorem hot_eq (k : Nat) (v : List Wire) (s : List Nat) : nextH k v s = qnext k v s := by
  unfold nextH qnext
  dsimp only
  apply congrArg (fun h => (pairs v).flatMap h)
  funext p
  rcases p with ⟨a,b,rest⟩
  apply congrArg (fun h => [false,true].flatMap h)
  funext d
  dsimp only
  rw [flags_filter]
  · cases h : fresh (gate d a b) v <;> simp [h,allChoices,List.filterMap_cons]
  · intro x y h
    simp [Quickest.check,show ¬v.length+x.toNat+y.toNat≤k+2 by omega]

end Hot


namespace Sprint
open Bench2928 Quickest
def req (d : Bool) (uni : Nat) (other : Wire) : Nat :=
  if d then uni &&& other.2.2 else uni &&& (top208 ^^^ other.2.1)
def nextS (k : Nat) (v : List Wire) (s : List Nat) : List (List Wire × List Nat) :=
  let l := v.length
  let t := counts v
  let one := t.1 ^^^ t.2.1
  let two := t.2.1 ^^^ t.2.2
  let wish := one &&& top208
  let bud := budgets s v
  let choices := Hot.flags k l
  (pairs v).flatMap fun (a,b,rest) =>
    let ca:=cov a
    let cb:=cov b
    let ua := wish &&& ca
    let ub := wish &&& cb
    [false,true].flatMap fun d =>
      let z:=gate d a b
      let cs:=charge a b z s
      let cz:=cov z
      let freeA := req d ua b == 0
      let freeB := req d ub a == 0
      choices.filterMap fun (ka,kb) =>
        if (ka || freeA) && (kb || freeB) && check k l one two ca cb cz bud a b z ka kb && fresh z v then
          some (z::((if ka then [a] else []) ++ ((if kb then [b] else []) ++ rest)),cs)
        else none
end Sprint

namespace Sprint
open Bench2928 Quickest

def bitL (d x y one two t p n q m : Bool) : Prop :=
  let ca := p && (t ^^ n)
  let cb := q && (t ^^ m)
  let cz := if d then (p || q) && (t ^^ (n || m)) else (p && q) && (t ^^ (n && m))
  let aa := if x then false else ca
  let bb := if y then false else cb
  (((one && (aa || bb)) || (two && aa && bb)) && (t ^^ cz)) = false →
  (x = false → ((one && t && ca) && (if d then m else t ^^ q)) = false) ∧
  (y = false → ((one && t && cb) && (if d then n else t ^^ p)) = false)

theorem bit_law : ∀ d x y one two t p n q m : Bool, bitL d x y one two t p n q m := by unfold bitL; decide +kernel

theorem quick_free {k n one two : Nat} {bud : List (Nat × Nat)} {a b : Wire} {d ka kb : Bool}
    (h : check k n one two (cov a) (cov b) (cov (gate d a b)) bud a b (gate d a b) ka kb = true) :
    (ka || req d (one &&& top208 &&& cov a) b == 0) = true ∧
    (kb || req d (one &&& top208 &&& cov b) a == 0) = true := by
  simp only [check,Bool.and_eq_true,beq_iff_eq] at h
  have hb := h.1.2
  have law (i : Nat) : (ka = false → (req d (one &&& top208 &&& cov a) b).testBit i = false) ∧
      (kb = false → (req d (one &&& top208 &&& cov b) a).testBit i = false) := by
    have hv := congrArg (fun z : Nat => z.testBit i) hb
    have hl := bit_law d ka kb (one.testBit i) (two.testBit i) (top208.testBit i)
      (a.2.1.testBit i) (a.2.2.testBit i) (b.2.1.testBit i) (b.2.2.testBit i)
    cases d <;> cases ka <;> cases kb <;>
      simp only [bitL,req,gate,cov,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,Nat.testBit_and,Nat.testBit_or,
        Nat.testBit_xor,Nat.zero_testBit] at hv hl ⊢ <;> exact hl hv
  constructor
  · cases e : ka
    · simp only [Bool.false_or,beq_iff_eq]
      apply Nat.eq_of_testBit_eq
      intro i; simpa only [Nat.zero_testBit] using (law i).1 e
    · rfl
  · cases e : kb
    · simp only [Bool.false_or,beq_iff_eq]
      apply Nat.eq_of_testBit_eq
      intro i; simpa only [Nat.zero_testBit] using (law i).2 e
    · rfl

theorem sprint_eq (k : Nat) (v : List Wire) (s : List Nat) : nextS k v s = Hot.nextH k v s := by
  unfold nextS Hot.nextH
  dsimp only
  apply congrArg (fun h => (pairs v).flatMap h)
  funext p
  rcases p with ⟨a,b,r⟩
  apply congrArg (fun h => [false,true].flatMap h)
  funext d
  apply congrArg (fun h => (Hot.flags k v.length).filterMap h)
  funext p
  rcases p with ⟨ka,kb⟩
  dsimp only
  split <;> rename_i h
  · simp only [Bool.and_eq_true] at h
    simp [h.1.2,h.2]
  · split <;> rename_i h2
    · simp only [Bool.and_eq_true] at h2
      have hf := quick_free h2.1
      simp [hf.1,hf.2,h2.1,h2.2] at h
    · rfl
end Sprint


namespace Mono2928.Aut
open DataBridge
open PEqualNP.Outside.L_meta_2928.CoThetaNine

set_option maxRecDepth 8192 in
def Feasible (k : Nat) (v : List Wire) (s : List Nat) : Prop :=
  ∃ S gs, v.toFinset = S ∧ v.Nodup ∧ (∀ w∈S,Packed w) ∧
    ValidTrace gate Goal S gs ∧ gs.length ≤ k ∧ Bounded gs masks s

set_option maxRecDepth 8192 in
set_option maxRecDepth 8192 in
theorem has_next {U a b d gs} (t : ValidTrace gate Goal (insert (gate d a b) U) gs)
    (ne : a ≠ b) (nf : gate d a b ∉ insert a (insert b U))
    (v : List Wire) (e : v.toFinset = insert a (insert b U)) (nd : v.Nodup)
    (allp : ∀ w∈insert a (insert b U), Packed w) (k : Nat) (hl : gs.length ≤ k)
    (s : List Nat) (bounded : Bounded ((d,a,b)::gs) masks s) :
    ∃ u, (u,charge a b (gate d a b) s)∈next k v s ∧
      u.Nodup ∧ u.toFinset = insert (gate d a b) U := by
  have tr := ValidTrace.step ne nf t
  have valid := (trace_coherent tr goal_proper allp).2 (d,a,b) (by simp)
  have Hz : gate d a b ∉ v.toFinset := e ▸ nf
  have fr : fresh (gate d a b) v = true := by
    simp only [fresh,Bool.not_eq_true',Bool.or_eq_false_iff,beq_eq_false_iff_ne,List.any_eq_false]
    refine ⟨⟨valid.2.1,valid.2.2⟩,?_⟩
    intro w hw eq
    exact Hz (List.mem_toFinset.mpr ((packed_inj (allp w (e ▸ List.mem_toFinset.mpr hw)) valid.1
      (beq_iff_eq.mp eq)) ▸ hw))
  have bf := charge_bounded bounded
  apply next_exists ne nd e fr Hz
  intro u un us
  have gu : ∀ w∈u, Packed w := by
    intro w hw
    have hh := us ▸ List.mem_toFinset.mpr hw
    obtain rfl|mem := Finset.mem_insert.mp hh
    · exact valid.1
    · exact allp _ (by simp [mem])
  have ce := good_covered t u us gu
  have len := trace_length_bound t
  rw [←us,List.toFinset_card_of_nodup un] at len
  simp only [allowed,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  refine ⟨⟨by omega,ce⟩,?_⟩
  intro p hp
  have hz := budget_zip bf p hp
  have cf := good_future t u us un p.1 (List.of_mem_zip hp).1
  omega

set_option maxRecDepth 8192 in
theorem feasible_zero {v s} (h : Feasible 0 v s) : v.any (fun w => w.1 == target) = true := by
  obtain ⟨S,gs,vS,_,_,tr,len,_⟩ := h
  cases tr with
  | stop =>
    apply List.any_eq_true.mpr
    exact ⟨Goal,List.mem_toFinset.mp (vS ▸ Finset.mem_singleton_self _),by rfl⟩
  | step _ _ _ => simp at len

set_option maxRecDepth 8192 in
theorem feasible_step {k v s} (h : Feasible (k+1) v s) :
    v.any (fun w => w.1 == target) = true ∨ ∃ n∈next k v s, Feasible k n.1 n.2 := by
  obtain ⟨S,gs,vS,nd,packed,tr,len,bud⟩ := h
  cases tr with
  | stop =>
    left
    apply List.any_eq_true.mpr
    exact ⟨Goal,List.mem_toFinset.mp (vS ▸ Finset.mem_singleton_self _),by rfl⟩
  | @step U a b d gs ne nf tail =>
    have hl : gs.length ≤ k := by simpa using len
    have ⟨u,hm,ud,us⟩ := has_next tail ne nf v vS nd packed k hl s bud
    refine Or.inr ⟨_,hm,_,_,us,ud,?_,tail,hl,charge_bounded bud⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|mem
    · exact packed_gate _ (packed _ (by simp)) (packed _ (by simp))
    · exact packed _ (by simp [mem])

set_option maxRecDepth 8192 in
set_option maxRecDepth 8192 in
theorem feasible_root (cert : SignedLower) {S : Finset Wire} {gs : List Move}
    (tr : ValidTrace gate Goal S gs) (hs : S ⊆ inputs.toFinset) (len : gs.length ≤ 14) :
    ∃ b, Feasible 14 (rootV b) initial := by
  obtain ⟨b,es,nd⟩ := startRoot tr hs
  exact ⟨b,_,_,es,nd,(fun w hw => pack_mem_inputs _ (List.mem_toFinset.mp (hs hw))),tr,len,fullBudget tr cert hs len⟩

end Mono2928.Aut


namespace Mono2928.Aut
open DataBridge

def rowTable (p : List Nat) (n : Nat) := table (fun r => n.testBit (rowMap p r))

theorem row_and (p : List Nat) (a b : Nat) :
    rowTable p (a &&& b) = rowTable p a &&& rowTable p b := by
  change bits _ (fun r => (a &&& b).testBit (rowMap p r)) = _
  simp only [Nat.testBit_and]
  exact bits_join _ (fun r => a.testBit (rowMap p r)) (fun r => b.testBit (rowMap p r)) false

theorem row_zero (p : List Nat) : rowTable p 0 = 0 := by
  unfold rowTable table
  have aux (xs : List Nat) : bits xs (fun _ => false) = 0 := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      change 2 * bits xs _ + 0 = 0
      rw [ih]
  simpa only [Nat.zero_testBit] using aux (List.range 512)

theorem row_beq (p : List Nat) (surj : ∀ i<512, ∃ j<512,rowMap p j=i)
    {a b : Nat} (ha : a < 2^512) (hb : b < 2^512) :
    (rowTable p a == rowTable p b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  refine ⟨?_,congrArg _⟩
  intro e
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 512
  · obtain ⟨j,hj,rj⟩ := surj i hi
    have ej := congrArg (fun n : Nat => n.testBit j) e
    change (table _).testBit j = (table _).testBit j at ej
    simpa only [table_read _ hj,rj] using ej
  · have hp : 2^512 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]

set_option maxRecDepth 8192 in
theorem collapse_map (p : List Nat) (surj : ∀ i<512, ∃ j<512,rowMap p j=i)
    (m : Nat) (hm : m < 2^512) (a b z : Wire) :
    collapses (rowTable p m) (wireMap p a) (wireMap p b) (wireMap p z) = collapses m a b z := by
  unfold collapses
  change ((((rowTable p z.1 &&& rowTable p m == 0) || (rowTable p z.1 &&& rowTable p m == rowTable p m))
    || (rowTable p z.1 &&& rowTable p m == rowTable p a.1 &&& rowTable p m))
    || (rowTable p z.1 &&& rowTable p m == rowTable p b.1 &&& rowTable p m)) = _
  have h (w : Wire) : w.1 &&& m < 2^512 := lt_of_le_of_lt Nat.and_le_right hm
  rw [←row_and,←row_and,←row_and,←row_zero p,row_beq p surj (h z) (by decide),
    row_beq p surj (h z) hm,row_beq p surj (h z) (h a),row_beq p surj (h z) (h b),row_zero]
end Mono2928.Aut


namespace Mono2928.Aut
open DataBridge

set_option maxRecDepth 8192 in
def shiftSpend (back : Nat → Nat) (s : List Nat) := (List.range 6).map fun j => s.getD (back j) 0

set_option maxRecDepth 8192 in
theorem cost_map (p : List Nat) (surj : ∀ i<512, ∃ j<512,rowMap p j=i)
    (m : Nat) (hm : m < 2^512) (gs : List Move) :
    ((mapMoves p gs).filter (cost (rowTable p m))).length = (gs.filter (cost m)).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨d,a,b⟩ := g
    have eq : cost (rowTable p m) (d,wireMap p a,wireMap p b) = cost m (d,a,b) := by
      unfold cost
      dsimp only
      rw [←map_gate,collapse_map p surj m hm]
    change (((d,wireMap p a,wireMap p b)::mapMoves p gs).filter _).length = _
    rw [List.filter_cons,List.filter_cons,eq]
    split <;> simp only [List.length_cons,ih]

set_option maxRecDepth 8192 in
theorem mask_low {m : Nat} (h : m∈masks) : m < 2^512 := by
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp h
  simpa only [List.length_range,table] using sample_bounded (List.range 512) (fun r : Nat => !(r.testBit c.1 || r.testBit c.2))

set_option maxRecDepth 8192 in
theorem budget_map (p : List Nat) (surj : ∀ i<512, ∃ j<512,rowMap p j=i)
    (back : Nat → Nat) (hb : ∀ i<6,back i<6)
    (maps : ∀ i<6,masks.getD i 0 = rowTable p (masks.getD (back i) 0))
    {gs s} (h : Bounded gs masks s) : Bounded (mapMoves p gs) masks (shiftSpend back s) := by
  have mlen : masks.length = 6 := rfl
  have slen : s.length = 6 := h.length_eq.symm.trans mlen
  apply List.forall₂_of_length_eq_of_get (by simp [shiftSpend,mlen])
  intro i h₁ h₂
  have hi : i<6 := mlen ▸ h₁
  have hbi : back i < masks.length := mlen ▸ hb i hi
  have hbs : back i < s.length := slen ▸ hb i hi
  have orig := h.get hbi hbs
  change s[back i] + (gs.filter (cost (masks[back i]'hbi))).length ≤ 3 at orig
  have me := maps i hi
  rw [List.getD_eq_getElem _ _ h₁,List.getD_eq_getElem _ _ hbi] at me
  have v : (shiftSpend back s)[i] = s[back i] := by
    simp only [shiftSpend,List.getElem_map,List.getElem_range,List.getD_eq_getElem _ _ hbs]
  change (shiftSpend back s)[i] + ((mapMoves p gs).filter (cost (masks[i]'h₁))).length ≤ 3
  rw [v,me,cost_map p surj _ (mask_low (List.getElem_mem _))]
  exact orig

set_option maxRecDepth 8192 in
theorem feasible_map {k v s w t} (h : Feasible k v s) (g : Nat) (hg : g<12)
    (back : Nat → Nat) (hb : ∀ i<6, back i<6)
    (maps : ∀ i<6,masks.getD i 0 = rowTable (permAt g) (masks.getD (back i) 0))
    (perm : (v.map (wireMap (permAt g))).Perm w) (sp : t = shiftSpend back s) : Feasible k w t := by
  obtain ⟨S,gs,vS,nd,pv,tr,len,bud⟩ := h
  obtain ⟨_,surj,fix⟩ := group_bounds hg
  let f := wireMap (permAt g)
  have eq : w.toFinset = S.image f := by
    ext y
    simp only [List.mem_toFinset, Finset.mem_image]
    rw [←perm.mem_iff]
    simp only [List.mem_map, ←vS, List.mem_toFinset,f]
  have nd' : (v.map f).Nodup := by
    apply nd.map_on
    intro a ha b hb he
    exact map_injective surj (pv a (vS ▸ List.mem_toFinset.mpr ha)) (pv b (vS ▸ List.mem_toFinset.mpr hb)) he
  refine ⟨_,_,eq,perm.nodup_iff.mp nd',?_,fix ▸ trace_map tr _ surj pv,by simpa [mapMoves] using len,?_⟩
  · intro y hy
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hy
    exact ⟨_,rfl⟩
  · rw [sp]
    exact budget_map _ surj back hb maps bud
end Mono2928.Aut

namespace Mono2928.OrbitDAG
open Aut
abbrev State := List Wire × List Nat
abbrev Node := Nat × State
abbrev LinkCheck := Nat → Nat → State → State → Bool

def goodChild (row : Nat → Option Node) (child label : Nat → Nat → Nat)
    (rel : LinkCheck) (size parent fuel : Nat) (e : State × Nat) : Bool :=
  let j := child parent e.2
  let g := label parent e.2
  j < size && match row j with
  | none => false
  | some (k,t) => k == fuel && rel g j e.1 t

def rowOK (advance : Nat → List Wire → List Nat → List State)
    (row : Nat → Option Node) (child label : Nat → Nat → Nat)
    (rel : LinkCheck) (size parent : Nat) : Bool :=
  match row parent with
  | none => false
  | some (k,v,s) => !(v.any (fun w => w.1 == Bench2928.target)) &&
    match k with
    | 0 => true
    | fuel+1 => ((advance fuel v s).zipIdx).all (goodChild row child label rel size parent fuel)

theorem sound {advance : Nat → List Wire → List Nat → List State}
    (incl : ∀ k v s p, p∈next k v s → p∈advance k v s)
    {row : Nat → Option Node} {child label : Nat → Nat → Nat}
    {rel : LinkCheck} {size : Nat}
    (transfer : ∀ (g j k : Nat) (u t : State), row j=some (k,t) → rel g j u t=true →
      Feasible k u.1 u.2 → Feasible k t.1 t.2)
    (checked : ∀ i<size, rowOK advance row child label rel size i=true)
    (k : Nat) : ∀ i v s, i<size → row i=some (k,v,s) → ¬ Feasible k v s := by
  induction k with
  | zero =>
    intro i v s hi hr feas
    have no := checked i hi
    simp only [rowOK,hr,Bool.and_true,Bool.not_eq_true'] at no
    have hit := feasible_zero feas
    rw [target_truth,no] at hit
    contradiction
  | succ k ih =>
    intro i v s hi hr feas
    have ok := checked i hi
    simp only [rowOK,hr,Bool.and_eq_true,Bool.not_eq_true'] at ok
    obtain hit|⟨u,hu,feas'⟩ := feasible_step feas
    · rw [target_truth,ok.1] at hit
      contradiction
    obtain ⟨n,hn,en⟩ := List.mem_iff_getElem.mp (incl _ _ _ _ hu)
    have zipped : (u,n) ∈ (advance k v s).zipIdx := by
      subst u
      exact List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hn)
    have link := List.all_eq_true.mp ok.2 _ zipped
    simp only [goodChild,Bool.and_eq_true,decide_eq_true_eq] at link
    obtain ⟨lt,link⟩ := link
    cases rr : row (child i n) with
    | none => simp [rr] at link
    | some r =>
      obtain ⟨k',w,t⟩ := r
      simp only [rr,Bool.and_eq_true,beq_iff_eq] at link
      obtain ⟨rfl,he⟩ := link
      exact ih _ _ _ lt rr (transfer _ _ _ u (w,t) rr he feas')
end Mono2928.OrbitDAG

namespace Mono2928.Aut
open DataBridge

def maskBackData : List (List Nat) := [[0,1,2,3,4,5],[0,5,4,3,2,1],[1,0,5,4,3,2],[5,0,1,2,3,4],[2,1,0,5,4,3],[4,5,0,1,2,3],[3,2,1,0,5,4],[3,4,5,0,1,2],[1,2,3,4,5,0],[5,4,3,2,1,0],[4,3,2,1,0,5],[2,3,4,5,0,1]]
def maskBack (g j : Nat) : Nat := (maskBackData.getD g []).getD j 0
def cutAt (j : Nat) := cuts.getD j (0,0)
def offCut (c : Nat × Nat) (r : Nat) := !(r.testBit c.1 || r.testBit c.2)

theorem masks_length : masks.length = 6 := rfl

theorem maskBack_lt {g j : Nat} (hg : g < 12) (hj : j < 6) : maskBack g j < 6 := by
  have all : ∀ g : Fin 12, ∀ j : Fin 6, maskBack g j < 6 := by decide
  exact all ⟨g,hg⟩ ⟨j,hj⟩

theorem cut_bounds {g j : Nat} (hg : g < 12) (hj : j < 6) :
    (cutAt (maskBack g j)).1 < (permAt g).length ∧
    (cutAt (maskBack g j)).2 < (permAt g).length ∧
    ((permAt g).getD (cutAt (maskBack g j)).1 0,
      (permAt g).getD (cutAt (maskBack g j)).2 0) = cutAt j := by
  have all : ∀ g : Fin 12, ∀ j : Fin 6,
      (cutAt (maskBack g j)).1 < (permAt g).length ∧
      (cutAt (maskBack g j)).2 < (permAt g).length ∧
      ((permAt g).getD (cutAt (maskBack g j)).1 0,
        (permAt g).getD (cutAt (maskBack g j)).2 0) = cutAt j := by decide
  exact all ⟨g,hg⟩ ⟨j,hj⟩

theorem mask_cut {j : Nat} (hj : j < 6) : masks.getD j 0 = table (offCut (cutAt j)) := by
  have hc : j < cuts.length := hj
  rw [List.getD_eq_getElem masks 0 (masks_length ▸ hj)]
  unfold masks
  rw [List.getElem_map]
  unfold cutAt
  rw [List.getD_eq_getElem cuts _ hc]
  rfl

theorem row_bit_of_lt (p : List Nat) (r i : Nat) (hi : i < p.length) :
    (rowMap p r).testBit i = r.testBit (p.getD i 0) := by
  rw [rowMap,bits_read,List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_map,List.getD_eq_getElem _ _ hi]

theorem tableCongr (f h : Nat → Bool) (e : ∀ r < 512, f r = h r) : table f = table h := by
  have transform (xs : List Nat) (hs : ∀ x ∈ xs, f x = h x) : bits xs f = bits xs h := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      have e0 := hs a (by simp)
      have es := ih (fun x hx => hs x (by simp [hx]))
      change 2 * bits xs f + _ = 2 * bits xs h + _
      rw [e0,es]
  exact transform (List.range 512) (fun x hx => e x (List.mem_range.mp hx))

theorem mask_perm {g j : Nat} (hg : g < 12) (hj : j < 6) : masks.getD j 0 =
    table (fun r => (masks.getD (maskBack g j) 0).testBit (rowMap (permAt g) r)) := by
  rw [mask_cut hj, mask_cut (maskBack_lt hg hj)]
  apply tableCongr
  intro r hr
  rw [table_read _ (perm_rows ⟨g,hg⟩ ⟨r,hr⟩).1]
  obtain ⟨ha,hb,eq⟩ := cut_bounds hg hj
  unfold offCut
  rw [row_bit_of_lt _ _ _ ha,row_bit_of_lt _ _ _ hb]
  rw [← congrArg Prod.fst eq, ← congrArg Prod.snd eq]

end Mono2928.Aut


namespace Mono2928.Aut
open Mono2928.DataBridge

theorem inverse_facts (g : Fin 12) :
    inverseIdx g < 12 ∧ inverseIdx (inverseIdx g) = g := by
  revert g
  decide +kernel

set_option maxRecDepth 4096 in
theorem wireMap_inverse (g : Fin 12) {w : Wire} (h : Packed w) :
    wireMap (permAt g) (wireMap (permAt (inverseIdx g)) w) = w := by
  obtain ⟨f,rfl⟩ := h
  apply pack_ext
  intro r hr
  let gi : Fin 12 := ⟨inverseIdx g,(inverse_facts g).1⟩
  have a := perm_rows g ⟨r,hr⟩
  have b := perm_rows gi ⟨r,hr⟩
  have ei : inverseIdx gi = g := (inverse_facts g).2
  rw [ei] at b
  change (table _).testBit (rowMap (permAt g) r) = f r
  rw [table_read _ a.1]
  change (table f).testBit (rowMap (permAt (inverseIdx g)) (rowMap (permAt g) r)) = f r
  rw [show rowMap (permAt (inverseIdx g)) (rowMap (permAt g) r) = r from b.2.2.1, table_read _ hr]

theorem perm_wireMap_inverse (g : Fin 12) {v w : List Wire} (hw : ∀ x ∈ w, Packed x)
    (h : v.Perm (w.map (wireMap (permAt (inverseIdx g))))) :
    (v.map (wireMap (permAt g))).Perm w := by
  have t := h.map (wireMap (permAt g))
  rw [List.map_map] at t
  have he : w.map (wireMap (permAt g) ∘ wireMap (permAt (inverseIdx g))) = w := by
    conv_rhs => rw [←List.map_id w]
    apply List.map_congr_left
    intro x hx
    exact wireMap_inverse g (hw x hx)
  exact he ▸ t

end Mono2928.Aut

namespace Mono2928.Gurvich
variable {W I : Type} [DecidableEq W]
def Sep (e : I → W → Bool) (i j : I) (w : W) : Prop := e i w = true ∧ e j w = false
def Only (e : I → W → Bool) (S : Finset W) (i j : I) (w : W) : Prop :=
  w ∈ S ∧ Sep e i j w ∧ ∀ t ∈ S, Sep e i j t → t = w
def Must (e : I → W → Bool) (goal : W) (S : Finset W) (p n : I) (w : W) : Prop :=
  (∃ j, e j goal = false ∧ Only e S p j w) ∧ (∃ i, e i goal = true ∧ Only e S i n w)
noncomputable def common (e : I → W → Bool) (goal : W) (S : Finset W) (p n : I) : Finset W := by
  classical
  exact S.filter (Must e goal S p n)

variable (e : I → W → Bool) (gate : Bool → W → W → W)
variable (eval : ∀ i d a b, e i (gate d a b) = if d then e i a || e i b else e i a && e i b)
include eval

omit [DecidableEq W] in
theorem sep_gate (i j : I) (d : Bool) (a b : W) :
    Sep e i j (gate d a b) → Sep e i j a ∨ Sep e i j b := by
  unfold Sep
  rw [eval,eval]
  cases d <;> cases e i a <;> cases e i b <;> cases e j a <;> cases e j b <;> decide

theorem keep_only {U : Finset W} {a b w : W} {i j : I} (d : Bool)
    (ha : w ≠ a) (hb : w ≠ b) (h : Only e (insert a (insert b U)) i j w) :
    Only e (insert (gate d a b) U) i j w := by
  obtain ⟨hm,hs,hu⟩ := h
  have hU : w ∈ U := by simpa [ha,hb] using hm
  refine ⟨Finset.mem_insert_of_mem hU, hs, ?_⟩
  intro t ht hts
  rcases Finset.mem_insert.mp ht with rfl | hm
  · rcases sep_gate e gate eval i j d a b hts with ha' | hb'
    · exact False.elim (ha (hu a (by simp) ha').symm)
    · exact False.elim (hb (hu b (by simp) hb').symm)
  · exact hu t (by simp [hm]) hts

omit eval in
theorem move_only {U : Finset W} {a b w z : W} {i j : I}
    (hw : w ∉ U) (h : Only e (insert a (insert b U)) i j w)
    (hit : ∃ t ∈ insert z U, Sep e i j t) :
    Only e (insert z U) i j z := by
  have nz : ∀ t ∈ U, ¬Sep e i j t := by
    intro t hm ht
    exact hw ((h.2.2 t (by simp [hm]) ht) ▸ hm)
  obtain ⟨t,hm,ht⟩ := hit
  obtain rfl | hm := Finset.mem_insert.mp hm
  · refine ⟨by simp, ht, ?_⟩
    intro x hx hs
    exact (Finset.mem_insert.mp hx).resolve_right (fun hm => nz x hm hs)
  · exact False.elim (nz t hm ht)

omit eval in
theorem keep_if_blocked {U : Finset W} {a b w z : W} {i j : I}
    (h : Only e (insert a (insert b U)) i j w) (hz : ¬ Sep e i j z)
    (hit : ∃ t ∈ insert z U, Sep e i j t) : w ∈ U := by
  obtain ⟨t,hm,ht⟩ := hit
  have hU := (Finset.mem_insert.mp hm).resolve_left (fun eq => hz (eq ▸ ht))
  exact (h.2.2 t (by simp [hU]) ht) ▸ hU

theorem both_kept {goal : W} {U : Finset W} {d : Bool} {a b : W} {p n : I}
    (ab : a ≠ b) (ma : Must e goal (insert a (insert b U)) p n a)
    (mb : Must e goal (insert a (insert b U)) p n b)
    (hp : e p goal = true) (hn : e n goal = false)
    (hit : ∀ i j, e i goal = true → e j goal = false → ∃ t ∈ insert (gate d a b) U, Sep e i j t) :
    a ∈ U ∧ b ∈ U := by
  obtain ⟨⟨ja,hja,ap⟩,⟨ia,hia,an⟩⟩ := ma
  obtain ⟨⟨jb,hjb,bp⟩,⟨ib,hib,bn⟩⟩ := mb
  have bJa : e ja b = true := by
    cases h : e ja b
    · exact False.elim (ab (ap.2.2 b (by simp) ⟨bp.2.1.1,h⟩).symm)
    · rfl
  have aJb : e jb a = true := by
    cases h : e jb a
    · exact False.elim (ab (bp.2.2 a (by simp) ⟨ap.2.1.1,h⟩))
    · rfl
  have bIa : e ia b = false := by
    cases h : e ia b
    · rfl
    · exact False.elim (ab (an.2.2 b (by simp) ⟨h,bn.2.1.2⟩).symm)
  have aIb : e ib a = false := by
    cases h : e ib a
    · rfl
    · exact False.elim (ab (bn.2.2 a (by simp) ⟨h,an.2.1.2⟩))
  cases d
  · constructor
    · exact keep_if_blocked e an (by simp [Sep,eval,bIa]) (hit ia n hia hn)
    · exact keep_if_blocked e bn (by simp [Sep,eval,aIb]) (hit ib n hib hn)
  · constructor
    · exact keep_if_blocked e ap (by simp [Sep,eval,bJa]) (hit p ja hp hja)
    · exact keep_if_blocked e bp (by simp [Sep,eval,aJb]) (hit p jb hp hjb)

theorem length_bound {goal : W} {S : Finset W} {gs : List (Bool × W × W)}
    (h : ValidTrace gate goal S gs) (p n : I) (hp : e p goal = true) (hn : e n goal = false) :
    S.card + (common e goal S p n).card ≤ gs.length + 2 := by
  classical
  induction h with
  | stop =>
    have sub := Finset.card_le_card (Finset.filter_subset (fun w => Must e goal {goal} p n w) {goal})
    simpa [common] using (show ({goal} : Finset W).card + (({goal} : Finset W).filter (fun w => Must e goal {goal} p n w)).card ≤ [].length (α := Bool × W × W) + 2 by simp at sub ⊢; omega)
  | @step U a b d gs ab fresh tail ih =>
    let z := gate d a b
    let V := insert a (insert b U)
    let T := insert z U
    let X := common e goal V p n
    let Y := common e goal T p n
    let K := (X.erase a).erase b
    have zU : z ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have zX : z ∉ X := fun hm => fresh (Finset.mem_filter.mp hm).1
    have hit : ∀ i j, e i goal = true → e j goal = false → ∃ t ∈ T, Sep e i j t := by
      intro i j hi hj
      exact trace_has_separator tail (Sep e i j) ⟨hi,hj⟩ (sep_gate e gate eval i j)
    have stays : K ⊆ Y := by
      intro w hw
      obtain ⟨nb,na,wx⟩ : w ≠ b ∧ w ≠ a ∧ w ∈ X := by simpa [K] using hw
      obtain ⟨⟨j,hj,ap⟩,⟨i,hi,an⟩⟩ := (Finset.mem_filter.mp wx).2
      have cp := keep_only e gate eval d na nb ap
      have cn := keep_only e gate eval d na nb an
      exact Finset.mem_filter.mpr ⟨cp.1,⟨j,hj,cp⟩,⟨i,hi,cn⟩⟩
    have moves : ∀ w ∈ X, w ∉ U → z ∈ Y := by
      intro w hw hU
      obtain ⟨⟨j,hj,ap⟩,⟨i,hi,an⟩⟩ := (Finset.mem_filter.mp hw).2
      have cp := move_only e hU ap (hit p j hp hj)
      have cn := move_only e hU an (hit i n hi hn)
      exact Finset.mem_filter.mpr ⟨cp.1,⟨j,hj,cp⟩,⟨i,hi,cn⟩⟩
    have both : a ∈ X → b ∈ X → a ∈ U ∧ b ∈ U := by
      intro ma mb
      exact both_kept e gate eval ab (Finset.mem_filter.mp ma).2 (Finset.mem_filter.mp mb).2 hp hn hit
    have kY := Finset.card_le_card stays
    have zK : z ∉ K := by simp [K,zX]
    have incr : z ∈ Y → K.card + 1 ≤ Y.card := by
      intro hz
      have hh := Finset.card_le_card (Finset.insert_subset hz stays)
      rwa [Finset.card_insert_of_notMem zK] at hh
    have xeq : X.card = K.card + (if a ∈ X then 1 else 0) + (if b ∈ X then 1 else 0) := by
      have a1 : (X.erase a).card + (if a ∈ X then 1 else 0) = X.card := by
        by_cases h : a ∈ X
        · simpa [h] using Finset.card_erase_add_one h
        · simp [h]
      have b1 : K.card + (if b ∈ X then 1 else 0) = (X.erase a).card := by
        by_cases h : b ∈ X
        · have hh : b ∈ X.erase a := by simp [ab.symm,h]
          simpa [K,h] using Finset.card_erase_add_one hh
        · simp [K,h]
      omega
    have veq : V.card = U.card + (if a ∈ U then 0 else 1) + (if b ∈ U then 0 else 1) := by
      by_cases ca : a ∈ U <;> by_cases cb : b ∈ U <;>
        simp [V,Finset.card_insert_of_notMem,ca,cb,ab,Nat.add_comm,Nat.add_left_comm]
    have teq : T.card = U.card + 1 := Finset.card_insert_of_notMem zU
    change T.card + Y.card ≤ gs.length + 2 at ih
    change V.card + X.card ≤ gs.length + 1 + 2
    by_cases ax : a ∈ X <;> by_cases bx : b ∈ X <;> by_cases au : a ∈ U <;> by_cases bu : b ∈ U <;>
      simp only [ax,bx,au,bu,ite_true,ite_false] at xeq veq <;>
      first | exact False.elim (au (both ax bx).1) | exact False.elim (bu (both ax bx).2) |
        have hz := incr (moves a ax au); omega | have hz := incr (moves b bx bu); omega | omega

end Mono2928.Gurvich


namespace Mono2928.Gurvich
def ev (i : Nat) (w : Wire) := w.1.testBit i
theorem ev_gate (i : Nat) (d : Bool) (a b : Wire) :
    ev i (gate d a b) = if d then ev i a || ev i b else ev i a && ev i b := by
  cases d <;> simp [ev,gate,Nat.testBit_or,Nat.testBit_and]
def sepB (i j : Nat) (w : Wire) := ev i w && !(ev j w)
def onlyB (v : List Wire) (i j : Nat) (w : Wire) :=
  sepB i j w && v.all (fun t => !(sepB i j t) || t == w)
theorem only_sound (v : List Wire) {i j : Nat} {w : Wire} (wm : w ∈ v) (h : onlyB v i j w = true) :
    Only ev v.toFinset i j w := by
  simp only [onlyB,Bool.and_eq_true,List.all_eq_true] at h
  have siff (t : Wire) : sepB i j t = true ↔ Sep ev i j t := by simp [sepB, Sep]
  refine ⟨List.mem_toFinset.mpr wm,(siff w).mp h.1,?_⟩
  intro t ht hs
  have it := h.2 t (List.mem_toFinset.mp ht)
  simpa [(siff t).mpr hs] using it

abbrev Witness := Nat × Nat × Nat
def owner (v : List Wire) (t : Witness) := v.getD t.1 (0,0,0)
def test (goal : Wire) (v : List Wire) (p n : Nat) (t : Witness) :=
  let w := owner v t
  decide (t.1 < v.length) && !(ev t.2.1 goal) && ev t.2.2 goal &&
  onlyB v p t.2.1 w && onlyB v t.2.2 n w

theorem test_sound {goal : Wire} {v : List Wire} {p n : Nat} {t : Witness} (h : test goal v p n t = true) :
    owner v t ∈ common ev goal v.toFinset p n := by
  classical
  simp only [test,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq] at h
  have ht := h.1.1.1.1
  have hm : owner v t ∈ v := by simp [owner,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ht]
  have l := only_sound v hm h.1.2
  have r := only_sound v hm h.2
  exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm,⟨t.2.1,h.1.1.1.2,l⟩,⟨t.2.2,h.1.1.2,r⟩⟩

def reject (goal : Wire) (v : List Wire) (k p n : Nat) (cert : List Witness) : Bool :=
  ev p goal && !(ev n goal) && decide ((cert.map (owner v)).Nodup) &&
  cert.all (test goal v p n) && decide (k + 2 < v.toFinset.card + cert.length)

theorem reject_sound {goal : Wire} {v : List Wire} {k p n : Nat} {cert : List Witness}
    (h : reject goal v k p n cert = true) {gs : List (Bool × Wire × Wire)}
    (run : ValidTrace gate goal v.toFinset gs) (budget : gs.length ≤ k) : False := by
  simp only [reject,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,List.all_eq_true] at h
  have les := length_bound ev gate ev_gate run p n h.1.1.1.1 h.1.1.1.2
  have sub : (cert.map (owner v)).toFinset ⊆ common ev goal v.toFinset p n := by
    intro w hw
    obtain ⟨t,tm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
    exact test_sound (h.1.2 t tm)
  have le := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup h.1.1.2,List.length_map] at le
  omega

end Mono2928.Gurvich


namespace Mono2928.OrbitDAG
open Aut
open PEqualNP.Outside.L_meta_2928.CoThetaNine
abbrev PruneWitness := Nat × Nat × List Gurvich.Witness

def prunedOK (advance : Nat → List Wire → List Nat → List State)
    (row : Nat → Option Node) (child label : Nat → Nat → Nat)
    (rel : LinkCheck) (size parent : Nat) (witness : Nat → Option PruneWitness) : Bool :=
  match witness parent with
  | none => rowOK advance row child label rel size parent
  | some (p,n,ws) => (row parent).any fun (k,v,_) => Gurvich.reject Goal v k p n ws

theorem feasible_checked {advance : Nat → List Wire → List Nat → List State}
    {row : Nat → Option Node} {child label : Nat → Nat → Nat}
    {rel : LinkCheck} {size i : Nat} {witness : Nat → Option PruneWitness}
    {k : Nat} {v : List Wire} {s : List Nat} (r : row i = some (k,v,s))
    (h : prunedOK advance row child label rel size i witness = true) (feas : Feasible k v s) :
    rowOK advance row child label rel size i = true := by
  cases ew : witness i with
  | none => simpa [prunedOK,ew] using h
  | some pack =>
    obtain ⟨p,n,ws⟩ := pack
    have chk : Gurvich.reject Goal v k p n ws = true := by simpa [prunedOK,ew,r] using h
    obtain ⟨S,gs,vS,_,_,tr,len,_⟩ := feas
    exact False.elim (Gurvich.reject_sound chk (vS.symm ▸ tr) len)

theorem sound_with_pruning {advance : Nat → List Wire → List Nat → List State}
    (incl : ∀ k v s p, p∈next k v s → p∈advance k v s)
    {row : Nat → Option Node} {child label : Nat → Nat → Nat}
    {rel : LinkCheck} {size : Nat}
    (transfer : ∀ (g j k : Nat) (u t : State), row j=some (k,t) → rel g j u t=true →
      Feasible k u.1 u.2 → Feasible k t.1 t.2)
    (checked : ∀ i<size, ∀ k v s, row i=some (k,v,s) → Feasible k v s → rowOK advance row child label rel size i=true)
    (k : Nat) : ∀ i v s, i<size → row i=some (k,v,s) → ¬ Feasible k v s := by
  induction k with
  | zero =>
    intro i v s hi hr feas
    have no := checked i hi _ _ _ hr feas
    simp only [rowOK,hr,Bool.and_true,Bool.not_eq_true'] at no
    have hit := feasible_zero feas
    rw [target_truth,no] at hit
    contradiction
  | succ k ih =>
    intro i v s hi hr feas
    have ok := checked i hi _ _ _ hr feas
    simp only [rowOK,hr,Bool.and_eq_true,Bool.not_eq_true'] at ok
    obtain hit|⟨u,hu,feas'⟩ := feasible_step feas
    · rw [target_truth,ok.1] at hit
      contradiction
    obtain ⟨n,hn,en⟩ := List.mem_iff_getElem.mp (incl _ _ _ _ hu)
    have zipped : (u,n) ∈ (advance k v s).zipIdx := by
      subst u
      exact List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hn)
    have link := List.all_eq_true.mp ok.2 _ zipped
    simp only [goodChild,Bool.and_eq_true,decide_eq_true_eq] at link
    obtain ⟨lt,link⟩ := link
    cases rr : row (child i n) with
    | none => simp [rr] at link
    | some r =>
      obtain ⟨k',w,t⟩ := r
      simp only [rr,Bool.and_eq_true,beq_iff_eq] at link
      obtain ⟨rfl,he⟩ := link
      exact ih _ _ _ lt rr (transfer _ _ _ u (w,t) rr he feas')
end Mono2928.OrbitDAG


namespace Bench2928.GurRow
def repFlag : List Nat := [0x3f7fffe8,0x1945985e90,0x267bc5a1ae,0x38c15be7fe,0x4d80200135,0x54a80c8d50,0x5f5f805462,0x6c705fe6b8,0x7e28000430,0x83400f0500,0x8a740f07eb,0x9b7eea83ff,0xb12a0ff550,0xc067fffdd3,0xd960341d18,0xe4bd57ead8,0xf8815aff5d,0x10bfffdd21f,0x123d1ffea87,0x138aa1ffffd,0x1506b70005f,0x15e72a0cf34,0x16d41ffffba,0x184ac18b015,0x1904ffff6b7,0x1a940800017,0x1af00198284,0x1b6d0f01f80,0x1c3ffcf3478,0x1d821346803,0x1e27382a000,0x1ebff004004,0x1f53e03e0a1,0x202fe5a3f1a,0x2168cc01e51,0x222825fe130,0x230f3478507,0x240e0024407,0x249780651c1,0x255024a6684,0x25f11ff8024,0x26cf3f347f0,0x280e03ca3ff,0x293ce692304,0x2a0ff00f804,0x2ae04c1fe3e,0x2bec0f9de18,0x2ce81fc0ccf,0x2de04907fff,0x2f0c03fc080,0x2fb8ca3da0c,0x309ff68ec5e,0x31e7e740a1e,0x32ef1e8aa18,0x33debfe7ca3,0x353be20e0f9,0x363b4ff8f80,0x375320cf5f4,0x38500be5755,0x3943c80e70e,0x3a2feac5a43,0x3b477dce6ba,0x3c9883f5a1b,0x3d9eaaf4cc7,0x3ec7e6e3dc2,0x3fff1fce6a0,0x411f8ffbcfe,0x42aebbc73ff,0x442600fc35f,0x452fdfbeba6,0x46ac60681c0,0x4741fffffeb,0x48f90cf301c,0x49cffedfffe,0x4b901000011,0x4bc02000800,0x4be79542006,0x4c9e7a3d114,0x4d9a0151ef6,0x4e854c00200,0x4ee08009002,0x4f2c0040000,0x4f5500e2841,0x4fefa3b43f1,0x511dd0e59d1,0x522382079eb,0x531015c4187,0x53c82a00240,0x542802ea800,0x54a67d128f6,0x55bf04003af,0x56800a102bf,0x57351a10007,0x57cc00058bd,0x58707004800,0x58ccb2c2c21,0x59951f47a37,0x5ab3f3bef3e,0x5c2fff78070,0x5d5000ab815,0x5de90110000,0x5e2aa75e029,0x5f1e59faecf,0x60720e07ffe,0x61903bd5b54,0x629afc55c00,0x637cf39fb87,0x64cacffe3ff,0x6655c03fc9f,0x6775d000dbd,0x6850a0e0c20,0x68d09007f1a,0x699211c8006,0x6a10000e035,0x6a801ca4040,0x6af1fb1f862,0x6c000000040]
def parentPack : List Nat := [0x7ff555554aaaaa0000002,0x49249246da4924912492000000033,0x46db6da4924892492492490000073,0x49246db49244924924000000000b3,0x49248db6db6db6db69249124000f3,0x492491b4892492492492400000133,0x49249236db6db4924924492400173,0x7555555552aaaa80001c2,0x6dadb649249246db6d244920001f3,0x7fffffffd554aa0000252,0x5b649246db6924924492480000293,0x5ddddc443bbba2191108888888880000002e4,0x5b649246db6da4924492492000393,0x492491b6d249249224924920003e3,0x5b249248db6d24924912000000433,0x49249236db6924922492490000483,0x49236db49249124924924900004c3,0x5b2491b6db6da4924492490000503,0x49248db6db6924922492480000553,0x6db5b649246db69244900000005a3,0x5b6d9246db6924924492492000603,0x48db6da4924492492492000000653,0x6d6d9246da49248924920000006a3,0x5b6d9248db4924924492492000703,0x6db5b6db248db6da4492400000763,0x7ff6db6b6db6491b49224920007c3,0x6eedccccc4443bbbbbaaa2221999108800834,0x4a52946318c6308420f739cd6b18b5ad4a52880000925,0x6738c5ef7b5ad6b4e73949ac628c62102108400000a55,0x7665ddd5533332aaa21991110888000000be4,0x5ad6b4a5083def7392939ce7318c6294a528c63000cc5,0x7f7ad6b5ac6316a462f7bd8c520c62108408421000e25,0x6ee6664cccc4443bbb32aa221111088001014,0x665dd55554ccc4443bbb2aa221999998010e4,0x6eeee666665c332aa220888888880000011b4,0x5965965144d34b2cb248ebaeb4d1c71860e28a208186000001286,0x77cf3b6db6d96596575d75d6db6db6d75d34d279a082082001546,0x4210839ad6b5ac6318c39ce72108420421080000018f5,0x6665ddddddcccc43bbbb3332aaaa9110019f4,0x6f7bdef7bddef4a5294a5210739c62104208421001ab5,0x4e739ce1084210839ce6b5ac631084208421080001c85,0x5ef6b5ad6b5ab5ad6b5ab9ce5ad694a10839ca5001db5,0x5ddd554cc4443bbbb33311110000000001f44,0x6ddcccbbbbaaaa22219999111108000002004,0x56b58c61083def7bdce7394a4a52942108421010020d5,0x49ce739ce52108421084210840c6318c6300000002225,0x463084210839cd6b5ac6318c4a4e73908420000002345,0x5294a528f7b18c62d6b5ad6a5294a514a308420002455,0x6f38c5ef59ce528c5ad6a94a39ce739ce718c63002595,0x6739ce739b5ad694a52949ce739ca4a50808400002745,0x4a52946318c2108398c6252939ce739c84210840028d5,0x5ef7bc62d5ad694a10841ce7398c631042104210029f5,0x4a52842108420c5290842108210410842108420002b65,0x5ed6b4e31841ef5ad6b5ace739ce739c8421080002c85,0x6318c630f7bdad6ad69420e7398c528c6108421002df5,0x6b5ad6b56b5ad6b5ab58bdcd62d47394a518c00002f85,0x4a31842108418c62d6a5252839ce73188420842003125,0x51514ac740c0404040404040402f2d2d2a1916118b8a8888078382828281818003248,0x7ae5cb972e5cb66cd9b366cd9b3669d342850a13a6cd9b35f3c7858003c87,0x71bf7664a90f0e9d3a64c182c5868d10204080c18303060c1820408004427,0x46a290977bbddeef75391c8e16db158ac553a9d4ea753a9d449f491b08e361687432120004c69,0x5a6d369984b2592c8ec763afd7ebf5bca552a954aa552a39142d1689030180c06030000005e09,0x76eddbb76866878f1e3c0074d7]
def movePack : List Nat := [0xc12008108401324a931c6709803280a108021000012346729465014a320c4300be31a461003e0f00530a,0x4a1400003784f0d81303504a0dc1383586e59a52cb704e0da1ac3506e7de7b8f684d0d21b53626f3d472877800a0b,0x6a0deb3c900000de13c3586f4d693c500000d61a837c6f4d8928a78a00001bc2786e09c1b02606a0dedbd36200a0b,0xdc1383686b0400003586a0964800006d0d613c500000de13c3684d0d81a837aed4d6928900000de1b435800a0b,0x6f09e1b82706c0d41c1f82ed59a9c0680ed19a3ac658f00a01b42686b0961bd3626f09e1a8250200001b010000a0b,0x4a5110420fc9d0f3fd3243d29c1d33ccb31c66190232f8bf2789f2f0bd2709d1741d2b4a929444000542a,0x572ee1c018060080080000756ea1cc380300c0100100000eed5c79870060180200200001ddf80600400003b30030b,0x720eafdd7a2d44a45dc6b8f51aa3d06a0f70ea1543a0540e41d1691f71ae3c8690f70ae1c8290700c00800000030b,0x40040000380600400003a3764e694ce98d11ec1d0398710eadcd699d22e61c8392511e21d5a99d32e61d16908030b,0x779e8bdc6b8f61ac3d06a0f21a43dc2b8760ac1d0390750e00c030040040000380600400003ab730e00c03000030b,0x531ea1cc380300c0100100000eadc03002000015cbb870060180200200001d5bb0d61ec158398745ea1543900030b,0x70ec158398530ea3547a8700c0080000544e81cc2a2740e61553b0d61ea3547b0560ea1cc2aa534ea3547988030b,0x114200436acb2400003686b098684408d01420042806f5400003784f0d6084408d019a2840085009a1bd90000a0b,0x57150020180400400003b3270ec1cc3bbf75e8b48bb8570e8150390520ecdd939a760ac1cc298710a214cd408030b,0x760ac14d2b9d32502206b8a80101d9690a700e1c82b9a811035c6a0a801015c2a0200000a0040300800800000030b,0x6f09e1b82706c0981a82504c498484408a10021b5658a00001bc3686b0a0740908811a02840085009e28000000a0b,0x300800800005614e01c3b0730e8b48e90a70ec1d0390779eebd1691d72ee15c3b0560e8150390520ed1d939a0030b,0x710a215cd40881500202b9a811035c698a801015c298280100c0200200000a004031060100100000ae2a00400030b,0x280100c02002000015c540080ae0c0200200001cd691d214e01c398720eebcd6b9730a61c8290764e49c82900030b,0x300800800002700e1cc3bb573ee15c398530ecbd82b0720a40a0440a801009c038730ae8a0440d71500202b80030b,0x4c0d41283484904020050000096880400a000012d1008019e3345000009e080400cd1962800004d09608000000b0b,0x200000a004030080080000541a429c038740e41ddbaaf35a47dc2b8750aa1cc298720a41d97a2724ec1583a00030b,0x2801009c038720502205400804e01c3a0573502206b8d51500202b9a811035c6a0a80100a0040300800800000030b,0x4c44020050000040200668a000007c3606a09e5bc2786d09a1b02606a0941b82706c0981ac2586909208040080b0b,0x6b0961a82502b0161a825069092080400a0000080400cd1962800001f0d812cf684d0d612c2516c0981a825000b0b,0x11420043784f0dc1383604c0dc1383684d0d612c108811420041000004220450801042204670a10020b406800a0b,0x555aa54ca99545ae550aa030080080000571ae0c0200200001d1790571a835c2a0766e614c3a0540e614c1408030b,0x30080080000571ae0c0200200001d9a98f60e614d3a2f60e415c6b8760ac14d2b8d70ae3506b8540aab516b80030b,0x700c01556a9922ae35c2a2d43ae35c2a0400400002b8d70a63516a0d34a695cab957060100100000800800000030b,0x42084107e30c2083f95307c0f8c10c22fc2fcab87e0fb0f5dec3d77c618c0c3d77e54bbf37f2a41000193f078141b,0x5506a1441883636c2d85b03636c2d82a8350682c85a0b21680c81a0b21680c829ad3066144188333200001b10240b,0x350662d15b8910200001aab33662d4598b556a4dc9a935068ad059a340668cc9a2b72684d01b8b316e0cc2a28230b,0x551a634d298b0040154200200001d1691d21e414d298d30020002aad51aaac010031080080000740a8154ea88030b,0x4007c1001f0551800800003e0e8bb42e87451e3b82f0541dc17829ad35a6744ea8d30a4b48ea8d21aa14829a8050b,0x52064048280710a20c40886f09e000280d01a0140680715de13c2a0d11a80cc0983202414439b310221c02800060b,0x760ac1c8290573ae35c6b8573ae35c3b056080080000551aa15ca99572ae1546a8d50aa3543a0540ae34c6b80030b,0x4b040000280cd1a0134280cd1a0134280cd1a013437b6f09e1b0260200000800004f09ab39680cc1a013036a80a0b,0x2e1582b8160000586b8560ae0581356682d0960ac161b01600b0161b01582c0160301582c01604f59e0bc25802a0b,0x400400002b9571ae0c0200200001d17a0720ae35c3b2f60ac1c82b8d41ae1503b3760ac1cc298533aa14c2998030b,0x553aa35428030020100100270a815ceb8500600402002004e1582a0d70a814ce99d70ae150180400400001800030b,0x303584c05802c0588c0d61b01582c01602f35e2001612c15813d6582b0602b45802d0606c0568b005a00016002a0b,0x4d140130a80ce1983402704c0dabbc2786d09a1ac258502a0340281d01a0080000502a03403784f04000026200a0b,0xa22809e2047e1f822284880047eff8a01009e0fc7e1fc1e078222785e07826090a0180202785e078551a,0x531a694c6b9d71ae14d2b9d31ae15ceb85406010010000060100100000ae2c02002000014cba2d21ec1d03900030b,0x90720641004f092280150502a03346804d0de5b0b786c0400002688a1400002624c29c3306804e09814066200a0b,0x43080300100000600400b84538a31412004042004200200000c00804412e0980304404600c23a4738e1001000130b,0x2000015c6b830080080000765e415c698d70a61d97b0560e41482b9d30ae74c698571a635c298573ae34c6b80030b,0x500920a4048390320802784c1142800004c498534660cd0981b1659ec2d65b03584c498340e81d00980a41c800a0b,0xe615c6b8760ac1502a0d40a8350398530ae95c6b8574ae35c1a8150a8140180100800801383402814c2ba0030b,0x4538e314618c708a10c228c318a10c229c338a30c628430800800003002005c220c40c658c23a470400c00800130b,0x4802044100062088600844010400000401184210028100200a04610822100200a0a2188a0180200a0550a,0x541e80cc390551a634d29a570aa154298300800800003008008000030080080000730e6bcc390571aa35c3a28030b,0x4418e110108010800800003002005c0b84308a100100000600400b84402e114a194518631412004086190b110130b,0x2112c0000060188601886110040298a2188a0180200a0a628862088a018020298a2108a0100a6288550a,0x4117e3041000007e10ce184108670c200600bc180218c11c41802f0431803882f84107e0fd208bf1820fc1f88170b,0x4117e3041000007e0fd209bf3822fc6083f082304202410c01012f8411c010120040480300208c10829046080170b,0x410802fc702df5be3786f85e07e3041f85f0bc1782e820100378208a01002fc7005e0400001f84137e2fc1f90170b,0x220806018063123c6f09a3103c0e0180000220806008060180221040010c20080280882010840108560a,0x560ac3581a0330260c43aa751e63c4700f30e21bc2f8545a23515b0160a81516a2911a8100180200001502988030b,0x3ef81ef7e07bef81efbe08c107c0f83025cf82103df83ef7e9046083f0823041f8410400001f8605bff77e080181b,0x4008610c2099e03a0342084112604c21841382280208a300610410000086104618c10861042184008210c2180160b,0x4d39a0e82714d19c134268ce09a134e704d09bf38e69cd29c3346684cf9bea7ccf9ff405309000003feb7c6f8091b,0x340660c81782e0a8354988400400002a28030b]
def offsetPack : List Nat := [0x79399bbd1657016bac532873e9446e17027f3d1cadc662ed66a64aa2504742c90c5e1e0000009,0x5b6c95ca9d32893d9ecf6733195486391a88409eeef6a3196eb04ca28de581f8b4320d0001eb9,0x58ab153a6d2685329246610ff7abb1c0cd5eacd4c8f419d8d8642f94c94411989830100003619,0x54a97459848e330d83bf1eaee73b758eba58aa948a04a22d0271311547c3115080280a0004c99,0x73e3b3468d1a3264bf7eddbad5a8d19b3643f6ac5628467ce9916100061d7,0x7bdfa31debd7ac56ad5ab56a12a542850203870d9b36609cf141c1c006927,0x61bd7ae59af5ebd7af4284b88fdfb66cd983058990a14284e172020007197,0x5cb95264c870e04070e1c356ab56ad50a11223c78c18264c98b08000077a7,0x64e4e4dfda57d24ac1b9322e2ca8a52525201c1c1c16920f0b8987070301800007d68,0x59a3467cf93261c376edc3870e1c366ccd8af5ebd29c244890c1818008a47,0x6596596596534d33cba69a6820694410410410404104000008fd6,0x56b294a5294a5294a10839ce7318c6312630c600092f5,0x679e364f3cf3cf14513aebaca8a228a269a69a492492280009476,0x55ab56ad2a53a74e9d3a74a95162c080f19aa4070b931c282850a000097f7,0x6db6db5d75d3cf1bac30c30a28a2879e79e618186186000009dc6,0x4788fdcb560c183052a50a13c5c8102040810203468d1428384040800a127,0x7cf3cf6e7cf9f3e2b74e9d3a74e9d39d1e3be7ce9d3264b529a1e2000a5c7,0x7df71c6596575d75d4d34d30c30c2fbe8a28a289249200000ad86,0x61c386e5cb94e9d3a74e8509309db56ad5ab560c152a4a6c90e121400b167,0x6fae57df7db6d75d1140f38d34c30b2892492479e79861800b776,0x7bc679e38dd75d451145134d34d2492461861830c30c00000bae6,0x7ce5cb972df9b055993264c99322448305dbb66cd6a73a50910181c00bf27,0x697df7db6d74cf3cf3befbefaebae92492469a28a28a18600c6e6,0x5bb762c55ab5694993261c37cf9e3c68d17aa4a8d09a263c50a0a1400ca67,0x6ecd6294a8af5bb75ebd4a93e7cf9f3058b13264080d141c282000000d047,0x75d75d6db69a698dd65555555555554f3c924514502c30c00d726,0x7ffff554aaaa80000dac2,0x6aaa0000000000000daf2,0x7ffffffc0db21,0x42108420f7bdef7bdce739ce739ce739cd0000000db35,0x5924924924924924912000000dc33,0xdc80,0x46318c6316b525294a5294a5294a5294630000000dc85,0x77bdef6f7bdef7210800000000000000000000000dd95,0x77bdeef18b5ad6b5ad6b5294a52106b5a718c0000df65,0x400000000e191,0x492492492491b489000000000e1a3,0x49249248da492492492491200e1f3,0x492491b6db6d2492489000000e233,0x7f55552aaaaaaa800e282,0x7fffe0000e2b1,0x555554a0000000000e2c2,0x7fff5554a00000000e2e2,0x444444444444444444111110888000000e314,0x7fffffffff8000000e392,0x4cccccccccaaaaaa22222111088888800e3c4,0x7ff55552800000000e452,0x54ccccc99999999999999999999999980e484,0x5b6db6db6db6da92449240000e523,0xe570,0x5554a000000000000e572,0x555555554aa000000e592,0x7ffffffffffb6db6db6c00000e5b3,0x400000000e621,0x5a00000000000000000000000e633,0x5a00000000000000000000000e683,0x421084210842108396b39ce721084200000000000e6d5,0xe7d0,0x444222222222222222199980000000000e7d4,0x55555555555500000e852,0x7fff00000e871,0xe880,0x16db6db68000e883]
def repPack : List Nat := [0x5ac56b49a019a181988991811898809800024,0x4a5295c59c5c57109364ce4633442028e930c41000115,0x464cd54338709f2662996ac486109c3848b06005051608588162e40200157,0x4e9b198bf1ed0c2030e972e7500236086532268293af3e588802e78a80397,0x78a8b7be30c07d6255b944f44f9c71e2c308a069850c100280866,0x324661d1308b8f3b92f0f85140969d5a764b87120f9f1001e2f3e54280867,0x4ab732663c17ee5b8ad9b2f5a3c00f00d9b2f5a3c00f0081015b0acd808b7,0x324226a6b0414140c0c0004000003f3eb8b838b83e35b5bd3c8b0b281a19b1b100888,0x47bb0e491cbc0f44c23b0e3030004b249c4441c03bb40e44c41b9bbaba3aba3380868,0x4733813fbdc44134b48c5048c8bb8dbb8dc2c0c8484e8e0e300028c843c13b0e00888,0x55555c0a0a224dc54443cca1483b0e3dbc3cb48a4e1b1b43403ebcb2801b461b008a8,0x53d102d102bdbcbdbcd6d3d102d102cc4c015bbe518453cb003abacfcf4fcf54009e8,0x4bca43924bc3924a4847c5b2814746c342a8b93a4241a88029b90034b29d9db680de8,0x69615e5be0e05b5ad554da5458d2564f53d1ce3e4444314b00474290c290c73900e18,0x419b66b0000f5caf0cf5caf0c54a9098e171488184026eb50bd0c1c0017d7,0x48be314837b0acaa90219e3d3cb6b62faf2a29a11db5aea93420a73180011d28817d8,0x5cdadaca43b733b431c9c32d4cbdbad3d0109027014dc942bb302c90a680224d017d8,0x6f6a6f6a6ddb086b67638a5a8066e12cdee766de5de0e05e5de564e3e261e15c817d8,0x3c1edcda9e5c5925573bd8a556bb1dd1cec584d14886cc4bc847c74584bab70001d78,0x41a0c0ea13526526092627274828014ad24bcc6331439a91a2968ec72311789c4a190b51817f9,0x54e98469f366bc000054a04614d52c8d026c4f9b13494434c29999c9ce89969cea67273a017f9,0x1a96d3434ad4d2952bcba1e2c843c802bd7ca50ad1d8e45a2b0e86c1e0c005e3e126552a01c69,0x4ba773a231f08cd2694d668d0684b2584422449a311229ec892791474004d4cc7237188b81e49,0x48e391c8ec722f164e38a0f0680c01fafc4db85f69a4d0006c006623118cc7439dd8eb74022b9,0x6ad7ad379a5338be672bce72139a4021c3018c4203475,0x4b805ac498046dabe0577bc0592511c33c4fcb480040f3ae03476,0x427c6deb8604db3414cc23416cc43462181b1061993166244b00000a83597,0x22b000446a946b806f0a8001905d3a95167c88b2a43b72864c4411e183557,0x45431aa238a400172c2db82e95291237b5a9b7b7141436b635b534b3b32f302f83538,0x50cacf21a1cd004a4dcccbcdcb4b40404c4ac04ccc1717172e2e49484645c54303538,0x5044c5cecc4ac2804b96c9c72c44bf0446c518981643beb43fc3444534443e34036c8,0x66abec59d3bed2976c58d8ebe804676765500067e6666766e665e563636155d503478,0x42c54281a6b5bfb991c7bf39af44c4812f3f3980c2c4c442104143803941904083a28,0x3b5750ddc483c4003a544fd6d6504c3d5ddc5bd9005ddf5c5bd90017d5cfcbbc83768,0x546d800062626d6cdf5f6c6beaea6060dfdfe463e564c8bd575edd524de15b01037b8,0x47db6db8fc1e0f1f6ab563f1d160b1b4397916cb6c18442a12c800409cce611b2001026a034f9,0x1a2cd2694662f13894461b1186871a9048000174ba80ba8ab012abaa07015cae604552a836c9,0x4fe594a95c5e2f1685c54d66a85454d6938b42d266a7cc29f2c66300220c6633198c008803729,0x4f2a0674d520262828be1c170d5bc282c56bc60adcb370c5aad64c15849b7,0x50d520cf51215020ce223f36ad46bb9e2cb0302faf2e2d98969693130589801c84b28,0x48464530002f8ec4af18bab939b836bdbcc005b3b23d37b605b3313a3734b98404ec8,0x5a67585855d5e36e6869a1e962e6e8622be62b62b2e1df3260dedd00183930a684bd8,0x5ece4e5d5d4ed1d7dadada55d3d4d552d65655555752d2d24f4f51d150d00023852a8,0x49623248d476371e8ec6e24b87abd5bedf00365b2e80a3d1daf77a3b5ce13798499ae67285019,0x4c2593b9ccda75333c4c4ef2e60cc8f1303bcb1807a8e97a391064c3d905d7bbdc020075052a9,0x66e27bfb0160fa80e05a7a79b6e8e659f9360065dfefee6f113510ebea35f21085848,0x25b4b71b8db60200475a6d28dbe103158046bdef8407c5ef128c203d9163f5bbd514f34405019,0x75ba201cb4140195eacce6495e80066703cc0026502cb40c07958127373abe371787c2dc04fc9,0x6b4fc7d739f8fba67516c014a2cddad19bcc530ad73b2e6b2f72cc957137db265b11712905409,0x38bca864355914e043a3512df4357abdd6eb773b7daecedebfb6e0f2003bbe3bff81c500052a9,0x34e974bb2d965cd695d3aaa052e8159cceae56ec15fae56ec6042e012c2cd66d6ab4000005b19,0x37cfd4520d530b8c8b0b8b38502d01012d3d423d4dccac8080accbbcc1bcca8006848,0x441e420bf509d329424d1233c7cf133a78a13285098e1e282810410007367,0x1e3c7d69e80f5eb060e9d386ecd889306101c1299088102c20406080077e7,0x7c70]
def edgeGroup : List Nat := [0x2c4cd081bb3bda25d941144088080000004,0x1011414008aa208000002,0x8b3002a5000202200000021830011000004,0x1b00000080003848db080143b083b88800004,0x200988380003,0x4002460800001,0x2600220000001,0x1024a30c00001,0x800000000000008001200000003,0x500010000000002,0x180c000024000004804800900003,0x11001100148580020000011111ddd5d80004,0x38000000001110050584850000000000004,0x220001000110053bbbbd5003803801100004,0x20000000000050000002d020002200000004,0x5808dd8002020220022000202183280000004,0x20220002200002285000a0080004,0x218034445333000300300280002058200004,0x388380020218300142285000000004a000004,0x3800300000200080004a383bbbbb0000004,0x388302d03880000000000000104221800004,0xbb804000000000380008b30038830000004,0x380888b35094442ac4001001000004,0x1c36000000071b8000018c000003,0x30058024bcd80003bbb80000003000000004,0x201800003,0x0,0x4000000000001,0x1ea0100400001,0x12300000001,0x80400000001,0x200000001,0x1000201000001,0x20000800001,0x4440000000001,0x12c309800001,0x4800400080001,0x0,0x2000000000001,0x20000001,0x800001000001,0x2821020000001,0x6000001380001,0x430110000001,0x600000001,0x60841800001,0xe00c00001,0x408e024580001,0x832b080001,0x10004000001,0x4000020000000020200210400000340000004,0x1010001100001000151010000502000000004,0x108400000000000000000000004,0x28800100004000000000000000000000004,0x101010010110011001003d000000000000004,0xe000004100000003,0x1d00020000920020000000000003,0x11005800003300003900000038000000004,0x158050010101010101010100004,0x110010000000505801010000505800004,0x202d025020202d00050538100100001100004,0x28002250002a200020000380000202000004,0x800200000000500020020200002000000004,0x2d20202020202038000022002380000380004,0x2020280002020200008d0004400002000004,0x443180023b002800025800280050000000004,0x222200020580380483bb9804b05230000004,0x2800059a029a200019800008030000180004,0x240000000002433330000220000000000004,0x20083bb94201b202020142020022000004,0x408001a0000004b8380000003b80000000004,0x380143ad03883a2b3881d3380380280004,0x380380001100003b803880000000588000004,0x1833183381b83381b8c00390588c451000004,0x0,0x0,0x0,0x0,0x0,0x2a60000000001,0x0,0x0,0x2002102000001,0x801001000001,0x0,0x810000000001,0x8000001,0x0,0x15540000001,0x2100805300001,0x5020001500001,0x800080001,0x80001,0x0,0x0,0x4404101000001,0x50080000001,0x0,0x582002000001,0x80000001,0x4000000000001,0x1408001480001,0x1114300001,0x1020000000001,0x4425a800001,0x1a2ac0000001,0x248c4c8080001,0x4235a11c00001,0x2801524a80001,0x115000000000022880002,0x180000002580000003800000000000004,0x400400000000038bbca20003003800004,0x200000380380000000000024000004,0x600000001,0xc1200000001,0x850682100001,0xc000000003]
def witTape : List Nat := [0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7969c4714000000000000001e5a711c5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x7979c5714000f2f38ae28001e5e715c50000000000000007969c4714000000000000001e5a711c50000000000000007969c4714000000000000001e5a711c5000000000000,0x138ef2ce28000000000000004e3bcb38a00000000000000138ef2ce28000000000000004e3bcb38a0007969c27140000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x1390f2ee2800271de59c5000000000000000000000000001390f2ee28002721e5dc500004bce0d8a000595131124000000000000000000000000004e3bcb38a,0x266b4424800169c4cc490000000000000005a713312400000000000000000000000000000000000000798954714000f2d2a6e28001e5a54dc500000000000000000000000000000000000000000000000000000000000,0x9c779671400000000000000271de59c5000000000000000000000000000000000000000262712c500004bce1d8a0000979c3b1400012d3876280000000000000004b4e1d8a000000000000000000000000000000000000002dcb63822,0xfc917597400000000000000329e5dac9000000000000000976ca2b2400000000000000329e5dac9000000000000000976ca2b2400000000000000271de59c50004e3bcb38a000000000000000000000000000000000000004e43cbb8a,0x977ca5b240012ef94b64800000000000000000000000000976ca4b240000000000000025db292c9000000000000000976ca4b240000000000000025db292c90004bb6525920000000000000012ed949648000000000000004bb652592,0xdb9446a64000000000000000000000000004bb651592000ca7976b2400000000000000000000000000000000000000000000000000000000000000000000000004bb651592000000000000000000000000000000000000004bbe52d92,0x1b7088b4c80036e1116990000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007e50c44ba,0x8f07064a800000000000000000000000000000000000001f9230f2e8003f2461e5d0000000000000000000000000000000000000025df28ac9000653cbb59200000000000000194f2ed64800000000000000000000000,0x6557b4304000000000000001955ed0c10000000000000006557b4304000000000000001955ed0c10000000000000006557b4304000000000000001955ed0c10000000000000006557b4304000caaf686080011e4e0c9500023c1c192a,0x977c96b24000000000000000000000000000000000000007b8656304000f6ecaa608000000000000003dbb2a982000000000000000f6ecaa60800000000000000000000000000000000000000000000000001959ed4c100032b3da982,0x8745a2824000f6ecaa608000000000000003dbb2a982000000000000000000000000000000000000000000000000009c70a3b1400138e147628000000000000000000000000000000000000012f192f6480025df25ac9000000000000,0x590f4e628000000000000001643d398a000000000000000590f4e628000000000000001643d398a0007a7252314000000000000000000000000002d443a4120000000000000010e8b25048000000000000002d443a412,0xd8cf28608000000000000003dc363982000000000000000f70d8e608000b21e9cc50001643d398a000000000000000000000000000000000000001643d398a000000000000000000000000000b21e9cc50003d390918a,0xd8cf28608000000000000003633ca1820006c6794404000000000000001b19e51010003633ca1820006c6794404000000000000001b19e51010003633ca2020006c7795304000000000000000000000000003633ca182,0xd8ef6a80800000000000000000000000000000000000000d8cf68808001b19ed1010003633c82020006c6794404000000000000001b19e51010003633ca202000000000000000d8cf28808001b1de54c1000000000000,0xd8cf288080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006c6790404000d8cf28808000000000000003633ca202,0xd8cf28608001b19e51010003633da182000000000000000d8eeea608000000000000003633ba1820006c6774304000d8ef2a808001b1de5501000363bcaa02000000000000000d8cf28808000000000000003633ca202,0x6c6794304000d8cee8608001b19dd0c10000000000000006c6774304000d8cee8608001b19ed0c10000000000000006c7795404000000000000001b19ed0c10003633ca2020006c67b4304000000000000001b1de5501000363bcaa02,0x6c6775304000d8cee0608001b19dd0c10003633ba182000000000000000d8cee8608001b19dd0c10000000000000006c7775304000000000000000000000000000000000000006c6774304000d8cee0608001b19dd0c1000000000000,0x6c67b4304000d8cf68608001b19ed0c10003633b81820006c6774304000d8cee8608000000000000003633da1820006c6774304000000000000001b19dd0c1000000000000000000000000000000000000001b19ed0c1000000000000,0x1b19dd4c10003633ba1820006c6774304000000000000001b19dd0c10000000000000006c77b530400000000000000000000000000000000000,0x6c7775304000000000000000000000000003633ba182000000000000000d8cee8608000000000000003633ba182000000000000000d8cee86080000000000000000000000000000000000000000000000000000000000000000000000,0x6c67b430400000000000000000000000000000000000000000000000000d8ceea608001b19dd4c1000363bb9982000000000000000000000000000000000000002630da5020004c61b4a0400098c369408001b1ddd4c1000363bba982,0x6c67b4304000d8cee8608001b19ed0c10000000000000006c7775304000000000000001b19dc0c10003633da1820006c6774304000d8cf6860800000000000000363bba9820006c7775304000000000000001b19e50c10003633ba182,0x2c774031400058ee8862800000000000000163ba218a00000000000000098c327408001d10b0cc50000000000000006c6794304000e88586628001d10b0cc50000000000000007442c3314000e88586628001b1ddd4c1000000000000,0x98c3694080013186d2810002dcb63822000745251314000000000000000b1dd10c50000000000000007442c23140000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x6c67b4304000e88584628001b19ed0c1000000000000000745250314000e8a4a4628000000000000003a296118a0006c6794304000e884a4628001b19ed0c10000000000000004c71b5a0400000000000000000000000000000000000,0x4c67b4804000000000000001319ed201000000000000000000000000000000000000001319ed2010002633dac020004c67b4804000000000000001319ed2010002633da40200000000000000098cf690080016e5b1c11000000000000,0x6c67b4304000000000000000000000000000000000000004c67b580400098ef6b008000000000000002633da40200000000000000098cf690080000000000000000000000000000000000000000000000000000000000000000000000,0x6c67b430400098c369408000000000000002630da5020004c61b4a04000000000000001b19ed1010002630da5020004c61b4a040000000000000013186d2810002630da5020004c77b5804000000000000001b19ed0c10002633da402,0x2630da50200000000000000098c369408000000000000002630dad020004c61b4a040000000000000013186d2810000000000000004c61b5a0400098c369408000000000000002630da502,0x4c61b4a040000000000000013186d2810000000000000004c61b4a040000000000000013186d2810000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x4c71b5a04000000000000001b19ed0c10002630da5020006c67b4304000000000000000000000000000000000000000000000000000000000000013186d6810002630dad020004c71b5a0400098e36b40800131c6d681000000000000,0xd8cf28608001b19e4cc10000000000000006c6793304000d8cf26608001b19e4cc10000000000000004c71b5a04000000000000001b19ed0c10002630da5020006c67b4304000000000000001b19ed0c1000000000000,0x1b19ec8c10003dbb63182000000000000000f6ed8c60800000000000000000000000000000000000000f6ed8c608001eddb18c10003dbb63182000000000000000f6ed8c608001eddb18c10003dbb63182,0x7b76c6304000000000000000951e88c500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007b76c6304000000000000001eddb18c1000000000000,0xf6ed8c608000000000000003dbb63182000000000000000f6ed8c608001eddb18c1000000000000000000000000000f6ed8c608001b19ec9010000000000000007b76c6304000000000000001eddb18c1000000000000,0x6c67b3404000000000000000000000000003dbb63182000000000000000f6ed8c608000000000000003dbb6318200000000000000000000000000000000000000000000000000000000000000000000000001eddb18c10003dbb63182,0x5b86c604400000000000000000000000000000000000000000000000000000000000000000000000000000000000007b76c6304000000000000001eddb18c10000000000000006c67b3404000000000000001b19ecd010003633d9a02,0x3dbb63182000000000000000f6ed8c608000000000000003dbb63182000000000000000f6ed8c608001eddb18c1000000000000000000000000000000000000001eddb18c1000000000000,0xf6ed8c608000000000000003dbb63182000000000000000f6ed8c6080000000000000000000000000000000000000000000000000000000000000000000000000000000000000f6ed8c608000000000000003dbb63182,0x7b76c6404000f6cd8a808001ed9b15010003db3629820007b66c5404000f6cd8a808001eddb18c10003db362982000000000000000f6ed8c60800000000000000000000000000000000000000f6ed8c608000000000000003dbb63182,0x7969c4714000f6cd8a608000b15d10c50000db262d020007b66c5304000f2d388e28001ed9b14c10003db362a020007b66c5304000000000000001eddb19010003dbb632020007b66c5304000f6cd8a808001ed9b1501000000000000,0x7b66c5304000f6cd8a608001ed9b14c10000000000000007b66c0304000f6cd8a608001ed9b14c10003db3629820007b66c5304000f6cd8a608001ed9b14c10002630d85020009c579071400036c98b408002715e41c50003db362a02,0x7b66c5304000000000000001eddb18c10003dbb631820007b66c5304000f6cd8a608001ed9b14c10000000000000007b76c33040000000000000032565cec90003db3089820007b66c0304000f6ed8c608001ed9b14c10003db362982,0xc96973b24000b2ac642480032565c6c9000652cb8d920008c779661400138ef2ce2800271de59c50003db3629820007b66c5304000f6cd8a608000000000000003db3629820007b66c5304000000000000001ed9b14c10003db362982,0xca7975b2400194f2e164bb1d1135c29d800653cba592000ca7974b240012eb9496480032925c2c90004ba651d92000974ca3b240012e9947648001ed9316010003db362982000000000000000f6c98b008001ed9316010002ca898892,0x975ca2b240012e99456480016e1b10110004bae51592000975ba2b240012e96856480025db286c90006534ba592000ca6974b240012e7943648000000000000000000000000005a7634124000c68b442480016998d0490002d331a092,0x796953714000f6c98a808001ed9315010003db3629820007b74c6404000f6c98a808000000000000003db3629820007b66c5304000f6cd8a608001ed9b14c10003dbb631820007b66c530400000000000000329e5d6c9000653cba592,0x7969c3714000f6cd8a608001ed9b14c10003db3629820007b66c5304000f6ed8c608001ed9b14c10000000000000007b66c5304000000000000001e5eb11c50003db362a020007b66c5304000f6cd8a608001ed9b14c10003cb10998a,0x7b66c5304000000000000001ed9b14c10003db3629820001b64c5a0400138ef2ce28001ed9b14c10003db3629820007b66c5304000f6cd8a608000000000000003db362a020007b66c5404000f6cd8a608001ed9b14c10003cb461b8a,0x976c90b24000f6ad80808001955ed1010004bb648d920006557b4404000f4a428628001b15ed10100030abda182000976ca2b24000f6cd8a608001ed9b14c10003db3629820007b66c5304000f6ed8c608001ed9b14c1000000000000,0xca2970b240012ed945648001951dc8c100032a3b91820005b66a4044000f4e4046280025db282c90004bb652592000976ca4b2400040ce82628001e9c810c50003dbb02982000976ca4b240012ed9496480025db292c9000649cb8592,0x976b41b240019272e16480025db242c900023c1c192a0008755428240010eaa850480016e1a94d100043b2a14120007b76c53040000000000000021d950e090000000000000008765a4824000f6ec0a6080021d968e090001023a098a,0x976c91b24001b7088b4c80013106ca810006534bad920006c6772404000d8aee4808001b15dc8c10000000000000004c61b4a04000000000000000000000000002628d9d020007b46c0404000d8af66808001b15ecd0100043b2a0c12,0xdb7444a64000f6ecac608001edd958c10003dbb2a982000655771304000f6ecaa608001edd954c100032b3da1820006557b4304000d8af66608001955eccc100032abd99820006557b33040019272e16480025db242c90004bb648592,0x976c95b24000caaf646080025df256c90004bb64ad92000976c95b240000000000000025db252c900064b4b9d920007b6655304000f6ccaa6080025df24ec90000000000000007b6652304001f9030d2e8000000000000003b9b29182,0xb6ed8a0880016ddb1411000362bb99820005b76c50440000000000000016ddb1411000000000000000615773304000b70d8c088000000000000000000000000005b76c50440000000000000025db256c90003dbb2a982,0xd8aee2808001eddb1501000000000000000000000000000000000000001b15dc9010000000000000004c61b4a0400098a3674080025db286c90004bb650d92000976ca1b240008aa3674080016e1b18110004bb651592,0x6c57b4304000caaf68608001b15ed0c100032abda1820007b7655304000f6ec2a6080025dad0ec90003dbb629820007b76c5304000f6ed8a608000000000000003dbb62a020006c5771404000f6ed8a808001eddb14c10003dbb62a02,0x6557b3304000000000000001315ed201000262bd9c020006557b3304000caaf66608001155ed20100022abd9c020004c57b3804000caaf66608000000000000003dbb2a9820007b76c5304000000000000001edd954c10003dbb2a982,0x6c67b4304000000000000001b19ed0c10000000000000006c6794304000000000000001b19ed0c100043aaa0c120008755938240008aaf67008001955ecd010002628d9d020004551b3a04000cacf68608001955eccc1000000000000,0xd8cf68808001b19e51010003633ca2020006c6794304000d8cf68808001b19e50c10003633ca2020006c6794404000d8cf68608001b19e50c10003633ca1820006c6794304000d8ef6a608001b19ed0c1000000000000,0x6c6794304000d8cee6608001b19ed1010003633ca1820006c6794404000d8cf28808001b19ed0c10003633ca1820006c6794304000d8cf28608001b1ded4c10003633da182000000000000000d8cf68608000000000000003633da182,0x6c6794404000d8cf28808001b19dccc10003633d82020006c67b4404000d8cf68808001b19ed1010003633da2020006c77b5404000d8cf68808000000000000003633da202000000000000000d8cf20808001b19ed1010003633ca202,0x6c67b4304000d8cf68808001b19ed0c10003633da2020006c67b4404000d8ef6a608001b19ed0c10000000000000006c67b4304000000000000001b19ec1010003633da2020006c67b4404000d8cf20808001b19e51010003633ca202,0xd8ef6a808001b1ded501000363bdaa020006c67b4304000d8cf68808001b19ed0c10000000000000006c77b5404000d8cf68808001b19ed1010003633da2020006c67b4404000d8ef6a608001b19ed0c1000000000000,0x6c67b4304000d8cee8608001b19dd0c10003633ba1820006c6790404000d8cee8608001b19e51010003633ca2020006c6794404000d8cf68608001b19ed1010003633da182000000000000000d8cf68608001b19ed1010003633da182,0x6c7795404000d8cf28808001b19e50c10000000000000006c6794404000d8cf68608001b19ed0c10003633da1820006c77b5404000d8ef2a808001b19e51010003633ca182000000000000000d8cf28808001b19ed0c10003633da182,0x6c77b5304000d8cf68608000000000000003633da1820006c6794304000d8cf28608001b19e50c10003633b81820006c67b4304000d8cee8608001b19dd0c10003633ba1820006c67b4304000d8cf68608001b1de54c1000363bcaa02,0x6c67b4304000d8cee8608001b19dd0c10003633ba9820006c6770304000d8cee0608001b19ed0c10003633ca1820006c6774304000d8cee8608001b19dc0c10003633ba1820006c6774304000d8cee8608001b19e50c10003633ba182,0x6c67b4304000d8cee0608001b19ed0c10003633ba1820006c67b4304000000000000001b19ed0c10003633da1820006c67b4304000d8cf68608000000000000003633da182000000000000000d8ceea608001b19dc0c10003633ba182,0x6c67b4304000d8cf68608001b19ed0c10003633da1820006c67b4304000d8cf68608001b19ed0c1000363bda9820006c67b4304000000000000001b19ed0c10000000000000006c67b4304000000000000001b19ed0c10003633da182,0x6c67b4304000000000000001b19ed0c10003633da1820006c67b4304000d8cf68608001b19dd4c10003633b81820006c67b4304000d8cee8608001b19e50c10003633ba1820006c6774304000d8cee8608001b19ed0c10003633da182,0x6c67b4304000000000000001b19ed0c10000000000000006c67b4304000d8cf68608001b1ded4c10000000000000006c67b4304000d8cf68608001b19ed0c10003633da1820006c67b4304000d8cf68608001b19ed0c1000000000000,0x6c67b4304000d8cf6860800000000000000363bda9820006c67b4304000d8cf68608001b19ed0c10000000000000006c67b4304000d8ef6a608000000000000003633da1820006c67b4304000d8cf68608001b19ed0c10003633da182,0x6c6774304000d8cee0608001b19dd0c10003633ba1820006c6775304000d8cee0608001b19dd0c10003633ba1820006c6770304000d8cee8608001b19dd0c10003633da1820006c67b4304000d8cf68608000000000000003633da182,0xd8cee6609b116cf9c9018003633b9982000000000000000d8cb6a8080013186d2810002630da5020004c61b4a0400098c369408001b19dc8c10002630da5020006c6775304000d8cee4608001b19dc8c10003633ba982,0x6c67b4304000d8cf68608001b19ed0c1000362bba1820006c6775304000d8aee0608001b19dd4c10003633ba9820006c6775304000d8ceea608001b19dd4c10003633ba9820006c6775304000d8ceea608001b19dd4c10003633b9982,0x6c6774304000d8cf68608001b19ed0c10003633da1820006c67b4304000000000000001b19ed0c10003633da182000000000000000d8eee0608001b1ded4c1000363bba9820006c6774304000d8cee8608000000000000003633ba182,0x6c6774304000d8cee8608000000000000003633ba1820006c67b4304000d8cf68608001b1ddd4c1000363bba9820006c7775304000d8eeea608000000000000003633b8182000000000000000d8cee8608001b19dd0c1000000000000,0xd8cee0608001b19dd0c1000163ba018a0006c6794304000e88582628001b19ed0c10003633ca1820006c6794304000d8cf286080013186ce810003633da1820006c6774304000e88586628001d10b0cc50003633ba182,0x6c77b5304000d8ef6a608001b19ed0c10003633da1820006c67b4304000000000000001b1ded4c10003633da1820006c67b4304000d8cf68608001b19ed0c10003633da1820006c77b5304000d8cf68608000000000000003633da182,0x4c71b5a04000000000000000b1dd0cc50002630c8d020004c61b4a0400098c369408001d08844c50002dc3630220002c774031400098c369408001d10b08c50003a216118a0006c67b4304000d8cf68608001b19ed0c1000000000000,0x7a4252314000000000000001d10948c50003633da1820006c67b4304000d8cf686080013186d2810000000000000004c61b4a04b6ccabce498c00131b6d6810002630da5020004c61b4a0400098c3694080013186d2810002630da502,0x4c67b48040019312e5668000000000000003a296118a0007442c231400192f2e5668000000000000003a216118a0006c67b4304000d8cf68608001b19ed0c10000000000000006c67b430400098e36b408001d14b08c50003a216118a,0x4c67b480400098cf69008001b19ed0c10000000000000004c67b480400098cf69008001319ed2010002633da4020004c67b480400098cf69008000000000000002633dac020004c67b480400098cf69008001319ed6010002633da402,0x6c67b4304000000000000001319ed2010003633da1820006c67b430400098cf6b008001319ed6010002633dac020004c67b580400098cf6b008001319ed2010003633da1820004c67b4804000d8cf68608000000000000002633da402,0x6c67b430400098c3694080013186d2810002630da5020004c61b4a0400098c3694080013186d2810003633da2020004c61b4a0400098c3614080013186c2810003633da2020004c61b4a0400098c3694080013186d2810002633da402,0x6c67b440400098c36b408001b19dccc10003633da1820006c67b440400098c3694080013186d2810002630dad020004c61b4a0400098c3694080013186d2810003633da1820004c61b4a0400098c36b4080013186c2810002630da502,0x6c67b4304000d8cf68608001b19ed1010002630da5020004c61b4a0400098c369408001b19ed1010000000000000006c67b44040000000000000013186d2810002630d85020004c61b4a0400098c3694080013186d6810003633da182,0x6c67b4304000000000000001b19ed0c10002630da5020006c67b4304000000000000001319ed201000363bda9820006c67b4304000d8cf686080013186d2810003633da1820004c61b4a04000d8ef6a608001b19ed0c1000000000000,0x5b6655e734c600098c36b4080013186d6810002630dad020004c61b5a0400098c36b4080013186d2810002630da5020004c61b4a0400098c369408001b19ed0c10002630da5020006c67b4304000000000000001b19ed0c10002630da502,0x6c67b4304000d8cf68608001b19ed0c10002630dad020004c61b5a0400098c36b4080013186d6810002630dad020004c61b5a0400098c36b408000000000000002630dad020004c61b5a0400098c36b40ae590d61c30d8002630dad02,0x6c67b330400098c361408000000000000002630da5020006c67b43040000000000000013186d2810003633da1820006c67b4304000d8cf68608001b19ed0c10002638dad020004c61b4a04000d8cf68608000000000000002630da502,0x7b76c6304000f6ed8c608001eddb18c10003633c89820007b76c6304000f6ed8c608000951e84c50003633ca1820006c67b3304000d8cf26608001b19e4cc10003633c99820006c67b4304000d8cf66608001b19eccc10003633d9982,0x2c47a2314000000000000001eddb18c10003dbb631820007b76c6304000f6ed8c608001eddb18c10003dbb63182000000000000000f6ed8c608001eddb18c10003dbb631820007b76c6304000f6ed8c608000951e84c50003633b8982,0x7b76c63040004a8f44628000b11e8cc500012a3d198a0002c47a3314000588f46628001eddb18c10001623d098a0006c6771304000f6ed8c608001b19e44c10003dbb631820002547a1314000d8cf62608000b11e84c5000162ba098a,0x7b76c6304000f6ed8c608000000000000002dbb630220007b76c6304000f6ed8c608001eddb18c10003d192818a0006c67b23040004a8f44628001eddb18c10003633d91820007b76c6304000f6ed8c608001eddb18c10003dbb63182,0x7b76c6304000f6ed8c608001eddb18c10003dbb631820007b76c6304000f6ed8c608001eddb18c10003dbb631820007b76c6304000f6ed8c608001eddb18c10003dbb631820007b76c6304000f6ed8c608001eddb18c10003633d8a02,0x6c67b3404000d8cf66808000000000000003633d9a020006c67b4404000d8cf68808001b19ed1010003633d9a020006c67b3404000d8cf66608001b19eccc10003dbb631820007b76c6304000f6ed8c608001eddb18c10003dbb63182,0x6c6772304000b4e20824800325e5d2cd000000000000000854ba1c24000b4e2a8248000551688490003dbb631820000000000000012a9947648001eddb18c10003633d8a020005b76c6044000d8cee6608001b19eccc10003633d9982,0x6c65b2044000d8eb66088001b1ddc4c10003dbb631820006c67b2404000f6ed8c608002ae0119590003633b91820005b86c6044000d8cee4608001eddb18c100064bcba59a000000000000000000000000001eddb18c1000000000000,0x7b66c5404000f6cd8a608001eddb18c10003dbb631820007b76c6304000f6ed8c608001eddb18c10003dbb631820007b76c6304000f6ed8c608001eddb18c10003dbb631820007b76c6304000f6ed8c608001eddb18c10003dbb63182,0x7b66c5304000f6cd8a6080018d1500490003a3162982000635592124000e8a588608000b11d08c10003a29621820007452c4304000e885846080016950c8490003db3629820007b66c5304000f6cd8a608001ed9b14c10003db362982,0x6c6773304000d8aee460800000000000000362bb91820001b54c2a04000d8dce880800000000000000362f39a020006c4e73404000f6cd88608001ed9b10c10000000000000007b66c5304000f6cd8a608001ed9b14c10003db362982,0x7b26503040012ed92b6480025db256c900000000000000087544482400026ca8a248001ed9954c10003db32a982000655772304001f8e30b2e8001ed9954c100032abc91820007b5654304000f6aca8608001959dc8c10001d9fb9102,0x6c5770304000d8af66608001b15dccc10002dbb628220005b76c50440010ed6898480016ddb14110002dbb628220000000000000010eca890480021dd5160900043b2a2412000876544824000c2aee6608001b15eccc10003513a018a,0x6c67b4304000d8cf68608001b19ed0c10003633da1820006557b3304000f6ed8a608001eddb14c1000362bb89820006c577140400098c363408001b15dc8c1000362bb82020006c57b2404000caaf66608001955eccc10003633ba182,0x6c67b4304000d8cf68608000000000000003633da1820006c67b4304000d8cf68608001b19ed0c10003633da1820006c6794304000d8cf68608001b19ed0c10003633da1820006c67b4304000d8cf68608001b19ed0c10003633da182,0x6c67b4304000d8eeea608001b19dc0c10003633ba1820006c67b4304000d8cee8608001b19ed0c10003633da1820006c67b4304000d8cf68608001b19dd0c10003633b99820006c6773304000d8cf68608001b19ed0c1000000000000,0x4c61b5a0400098c36b408001b19ed0c10003633da1820007a48c2814000d8cf68608001b19ed0c10003a210998a000f746b020400098bb6940ae550d35c70d800262eda5020006c67b4304000000000000001b19ed0c10003633da182,0xf733b0204000f6ed8c608001b19dccc10002cb8ba09a0006c6773304000d8cee6608001b19eccc10003633d99820006c6771304000f6ed8c608001b19ec5010001623d118a0004c61b0a04000d8ceea608001b19ed4c10002630dad02,0xf15e88c50001e2bd118a0003c57a2314000788f44628000f11e80c50003633da1820005b76c504400078af44628000f15e88c50001e2bd118a000000000000000d8cf66608003555708410006aa2e1082]
def witWidth : Nat := 47
def vertexPerm : List (List Nat) := [[0,1,2,3,4,5,6,7,8],[0,5,8,3,4,1,7,6,2],[1,0,5,8,6,2,4,7,3],[1,2,3,8,6,0,7,4,5],[2,1,0,5,7,3,6,4,8],[2,3,8,5,7,1,4,6,0],[3,2,1,0,4,8,7,6,5],[3,8,5,0,4,2,6,7,1],[5,0,1,2,7,8,4,6,3],[5,8,3,2,7,0,6,4,1],[8,3,2,1,6,5,4,7,0],[8,5,0,1,6,3,7,4,2]]
def inverseGroup : List Nat := [0,1,2,8,4,11,6,7,3,9,10,5]
def count : Nat := 1998
end Bench2928.GurRow


namespace Bench2928.GurRow
abbrev Node := Nat × List Wire × List Nat
def field (t : List Nat) (i : Nat) : Nat :=
  let b := t.getD (i/32) 0
  let n := b % 16
  let z := b >>> 4
  z % 32768 + (((z >>> 15) >>> ((i % 32)*n)) % 2^n)
def descend (t : Node) (m : Nat) : Node :=
  let i := m % 16
  let j := (m >>> 4) % 16
  let v := t.2.1
  let a := v.getD i (0,0,0)
  let b := v.getD j (0,0,0)
  let z := gate (m.testBit 8) a b
  let rest := (v.eraseIdx j).eraseIdx i
  (t.1-1,z::((if m.testBit 9 then [a] else []) ++ ((if m.testBit 10 then [b] else []) ++ rest)),charge a b z t.2.2)
def rootBank (g i : Nat) : List Wire :=
  let ps := vertexPerm.getD g []
  let v := (List.range 9).map fun j => inputs.getD (ps.getD j 0) (0,0,0)
  if i=0 then v else v ++ [inputs.getD 9 (0,0,0)]
def locateRow (g : Nat) : Nat → Nat → Option Node
  | 0,_ => none
  | k+1,i =>
    if i < 2 then (if i = 0 ∨ g < 2 then some (14, rootBank g i,initial) else none)
    else (locateRow g k (field parentPack (i-2))).map fun p => descend p (field movePack (i-2))
def rowG (g i : Nat) : Option Node := if i < count then locateRow g 15 i else none
def row := rowG 0
def childG (i j : Nat) : Nat := field edgeGroup (field offsetPack i + j)
def childInv (i j : Nat) : Nat := inverseGroup.getD (childG i j) 0
def pop32 (x : Nat) : Nat :=
  let b := x - ((x >>> 1) &&& 0x55555555)
  let c := (b &&& 0x33333333) + ((b >>> 2) &&& 0x33333333)
  let e := (c + (c >>> 4)) &&& 0x0f0f0f0f
  ((e * 0x01010101) >>> 24) % 256
def childIx (i j : Nat) : Nat :=
  let e := field offsetPack i + j
  let f := repFlag.getD (e/32) 0
  let q := (f >>> 32) + pop32 (f % 2^(e % 32))
  if f.testBit (e % 32) then field repPack q else 2+e-q
end Bench2928.GurRow

namespace Bench2928.GurRow
open Mono2928 (rootV lit permAt stub root_which lit_idx map_neg map_lit p_bounds)
open Mono2928.Aut (wireMap)

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem rootBank_identity (i : Fin 2) : rootBank 0 i = rootV (i.val != 0) := by
  revert i
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem rootBank_index (g : Fin 12) (i : Fin 2) :
    rootBank g i = (rootBank 0 i).map (stub (permAt g)) := by
  revert g i
  decide +kernel

set_option maxRecDepth 16384 in
theorem bank_map (g : Fin 12) (i : Nat) (hi : i<2) (ok : i=0 ∨ g.val<2) :
    rootBank g i = (rootBank 0 i).map (wireMap (permAt g)) := by
  rw [rootBank_index g ⟨i,hi⟩,rootBank_identity ⟨i,hi⟩]
  apply List.map_congr_left
  intro w hw
  obtain ⟨j,rfl,hj⟩ := root_which _ w hw
  have hg : g.val < Mono2928.graphAutomorphisms.length := g.isLt
  have ⟨hl,hb⟩ := p_bounds hg
  unfold stub
  rw [lit_idx j]
  change (if j.val = 9 then lit 9 else lit ((permAt g).getD j.val 0)) = _
  split
  next he =>
    have hj9 : j.val = 9 := he
    have hi' : i ≠ 0 := by
      intro e
      subst i
      simp [hj9] at hj
    have small := ok.resolve_left hi'
    have fix0 : (permAt g).getD 0 0 = 0 :=
      (by decide +kernel : ∀ k : Fin 2, (permAt k.val).getD 0 0 = 0) ⟨g.val,small⟩
    rw [hj9]
    exact (map_neg hl fix0).symm
  next h =>
    have lt : j.val < 9 := by have := j.isLt; omega
    exact (map_lit (i:=⟨j.val,lt⟩) hl hb).symm
end Bench2928.GurRow

namespace Bench2928.GurRow
open Mono2928.DataBridge (Packed)
open Mono2928.Aut (wireMap)
private theorem zero_pack : (0,0,0) = Mono2928.pack (fun _ => false) := by decide +kernel
private theorem map_zero (g : Fin 12) : wireMap (Mono2928.permAt g) (0,0,0) = (0,0,0) := by
  simp only [wireMap,Nat.zero_testBit]
  exact zero_pack.symm
private theorem desc_map (f : Wire → Wire) (fz : f (0,0,0) = (0,0,0))
    (fg : ∀ d a b, f (gate d a b) = gate d (f a) (f b))
    (t u : Node) (hv : u.2.1 = t.2.1.map f) (m : Nat) :
    (descend u m).2.1 = ((descend t m).2.1).map f := by
  have get (i : Nat) : (t.2.1.map f).getD i (0,0,0) = f (t.2.1.getD i (0,0,0)) := by
    simpa only [fz] using (List.getD_map t.2.1 (0,0,0) (n:=i) f)
  cases ha : m.testBit 9 <;> cases hb : m.testBit 10 <;>
    simp only [descend,hv,ha,hb,get,fg,List.map_cons,List.map_nil,List.map_append,List.eraseIdx_map,
      Bool.false_eq_true,ite_false,ite_true]
private theorem loc_map (g : Fin 12) (fuel i : Nat) (t u : Node)
    (ht : locateRow 0 fuel i = some t) (hu : locateRow g fuel i = some u) :
    u.2.1 = t.2.1.map (wireMap (Mono2928.permAt g)) := by
  induction fuel generalizing i t u with
  | zero => simp [locateRow] at ht
  | succ n ih =>
    by_cases hi : i<2
    · by_cases ok : i=0 ∨ g.val<2
      · simp [locateRow,hi] at ht
        simp only [locateRow,if_pos hi,if_pos ok,Option.some.injEq] at hu
        subst t; subst u
        exact bank_map g i hi ok
      · simp only [locateRow,if_pos hi,if_neg ok] at hu
        contradiction
    · simp only [locateRow,hi,ite_false,Option.map_eq_some_iff] at ht hu
      obtain ⟨a,ha,rfl⟩ := ht
      obtain ⟨b,hb,rfl⟩ := hu
      exact desc_map _ (map_zero g) (Mono2928.Aut.map_gate _) _ _ (ih _ _ _ ha hb) _
theorem row_map (g : Fin 12) (i : Nat) (t u : Node)
    (ht : row i = some t) (hu : rowG g i = some u) :
    u.2.1 = t.2.1.map (wireMap (Mono2928.permAt g)) := by
  by_cases hi : i<count
  · simp only [row,rowG,hi,ite_true] at ht hu
    exact loc_map g 15 i t u ht hu
  · simp [row,rowG,hi] at ht
private theorem get_packed (v : List Wire) (hv : ∀ w ∈ v, Packed w) (i : Nat) : Packed (v.getD i (0,0,0)) := by
  by_cases h : i < v.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hv _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
    exact ⟨_,zero_pack⟩
private theorem desc_packed (t : Node) (hv : ∀ w ∈ t.2.1, Packed w) (m : Nat) :
    ∀ w ∈ (descend t m).2.1, Packed w := by
  let a := t.2.1.getD (m % 16) (0,0,0)
  let b := t.2.1.getD ((m >>> 4)%16) (0,0,0)
  let r := (t.2.1.eraseIdx ((m >>> 4)%16)).eraseIdx (m % 16)
  have hr : r.Sublist t.2.1 := (List.eraseIdx_sublist _ _).trans (List.eraseIdx_sublist _ _)
  have ha : Packed a := get_packed _ hv _
  have hb : Packed b := get_packed _ hv _
  have hz : Packed (gate (m.testBit 8) a b) := Mono2928.DataBridge.packed_gate _ ha hb
  intro w hw
  change w ∈ gate _ a b :: ((if m.testBit 9 then [a] else []) ++ ((if m.testBit 10 then [b] else []) ++ r)) at hw
  cases e : m.testBit 9 <;> cases e' : m.testBit 10 <;> simp [e,e'] at hw <;>
    rcases hw with h | h <;> first | simpa [h] using hz | exact hv _ (hr.subset h) | (rcases h with h|h <;> first | simpa [h] using ha | simpa [h] using hb | exact hv _ (hr.subset h) | (rcases h with h|h <;> first | simpa [h] using hb | exact hv _ (hr.subset h)))
private theorem loc_packed (fuel i : Nat) (t : Node) (ht : locateRow 0 fuel i = some t) :
    ∀ w ∈ t.2.1, Packed w := by
  induction fuel generalizing i t with
  | zero => simp [locateRow] at ht
  | succ n ih =>
    by_cases hi : i<2
    · simp [locateRow,hi] at ht
      subst t
      change ∀ w ∈ rootBank 0 i, _
      rw [rootBank_identity ⟨i,hi⟩]
      intro w hw
      by_cases e : (i != 0) = true
      · simp [Mono2928.rootV,e] at hw
        exact Mono2928.DataBridge.pack_mem_inputs w hw
      · simp only [Mono2928.rootV,e,Bool.false_eq_true,ite_false] at hw
        exact Mono2928.DataBridge.pack_mem_inputs w (List.take_subset _ _ hw)
    · simp only [locateRow,hi,ite_false,Option.map_eq_some_iff] at ht
      obtain ⟨a,ha,rfl⟩ := ht
      exact desc_packed a (ih _ _ ha) _
theorem row_packed (i : Nat) (t : Node) (ht : row i = some t) : ∀ w ∈ t.2.1, Packed w := by
  by_cases hi : i<count
  · simp only [row,rowG,hi,ite_true] at ht
    exact loc_packed 15 i t ht
  · simp [row,rowG,hi] at ht
end Bench2928.GurRow

namespace Mono2928.Aut.GurCheck
open Bench2928.GurRow
open OrbitDAG
open DataBridge
open PEqualNP.Outside.L_meta_2928.CoThetaNine (SignedLower)

set_option maxRecDepth 8192 in
def orbitRel (g j : Nat) (u t : State) : Bool :=
  if g = 0 then t.2 == u.2 && decide (u.1.Perm t.1)
  else g < 12 && t.2 == shiftSpend (maskBack g) u.2 &&
    match rowG (inverseIdx g) j with
    | none => false
    | some (_,v,_) => decide (u.1.Perm v)

set_option maxRecDepth 8192 in
def witness (rowId : Nat) : Option PruneWitness :=
  let bits := (witTape.getD (rowId / 16) 0 >>> ((rowId % 16) * witWidth)) % 2^witWidth
  if bits == 0 then none else
    let p := Bench2928.pos.getD ((bits >>> 3) % 16) 0
    let n := Bench2928.neg.getD ((bits >>> 7) % 16) 0
    let cs := (List.range (bits % 8)).map fun j =>
      let t := bits >>> (11+12*j)
      (t % 16, Bench2928.neg.getD ((t >>> 4)%16) 0, Bench2928.pos.getD ((t >>> 8)%16) 0)
    some (p,n,cs)

set_option maxRecDepth 8192 in
def verify (i : Nat) : Bool := prunedOK Sprint.nextS row childIx childG orbitRel count i witness

set_option maxRecDepth 8192 in
def block (start n : Nat) : Bool := (List.range n).all fun j => verify (start+j)

set_option maxRecDepth 8192 in
def valid (a z : Nat) := ∀ i, a ≤ i → i < z → verify i = true
set_option maxRecDepth 8192 in
theorem subsegment {a n : Nat} (h : block a n = true) : valid a (a+n) := by
  intro i le lt
  have hi : i-a < n := by omega
  have t := List.all_eq_true.mp h (i-a) (List.mem_range.mpr hi)
  change verify (a+(i-a)) = true at t
  simpa only [show a+(i-a) = i by omega] using t
set_option maxRecDepth 8192 in
theorem joinSeg {a b c : Nat} (l : valid a b) (r : valid b c) : valid a c := by
  intro i h z
  by_cases hi : i < b
  · exact l i h hi
  · exact r i (by omega) z
end Mono2928.Aut.GurCheck

namespace Mono2928.Aut.GurCheck
open Bench2928.GurRow
open OrbitDAG
open DataBridge
open PEqualNP.Outside.L_meta_2928.CoThetaNine (SignedLower)

set_option maxRecDepth 8192 in
theorem orbit_rel_sound
    (replay : ∀ (g j k k' : Nat) (v v' : List Wire) (s s' : List Nat), g<12 →
        row j = some (k,v,s) → rowG g j = some (k',v',s') → v' = v.map (wireMap (permAt g)))
    (packed : ∀ (i k : Nat) (v : List Wire) (s : List Nat), row i = some (k,v,s) → ∀ w∈v,Packed w)
    (g j k : Nat) (u t : State) (hr : row j=some (k,t)) (h : orbitRel g j u t=true)
    (f : Feasible k u.1 u.2) : Feasible k t.1 t.2 := by
  unfold orbitRel at h
  split at h
  · simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
    obtain ⟨S,gs,es,nd,pv,tr,ln,bb⟩ := f
    refine ⟨S,gs,?_,h.2.nodup_iff.mp nd,pv,tr,ln,h.1.symm ▸ bb⟩
    rw [←es]
    ext x
    simpa only [List.mem_toFinset] using (h.2.mem_iff (a:=x)).symm
  · simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
    obtain ⟨⟨hg,spent⟩,re⟩ := h
    cases e : rowG (inverseIdx g) j with
    | none => simp [e] at re
    | some r =>
      obtain ⟨k',v',s'⟩ := r
      simp only [e,decide_eq_true_eq] at re
      let gi : Fin 12 := ⟨g,hg⟩
      have eq := replay _ j k k' t.1 v' t.2 s' (inverse_facts gi).1 hr e
      rw [eq] at re
      have pp := perm_wireMap_inverse gi (packed _ _ _ _ hr) re
      exact feasible_map f g hg _ (fun _ => maskBack_lt hg) (fun _ => mask_perm hg) pp spent

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
theorem row_roots (b : Bool) : ∃ i<count, row i = some (14,rootV b,initial) := by
  cases b
  · exact ⟨0,by decide,by decide +kernel⟩
  · exact ⟨1,by decide,by decide +kernel⟩

set_option maxRecDepth 8192 in
theorem no_trace
    (transfer : ∀ (g j k : Nat) (u t : State), row j=some (k,t) → orbitRel g j u t=true →
      Feasible k u.1 u.2 → Feasible k t.1 t.2)
    (tested : ∀ i<count, verify i=true) (cert : SignedLower)
    {S : Finset Wire} {gs : List Move} (tr : ValidTrace gate Goal S gs)
    (hs : S⊆inputs.toFinset) (len : gs.length ≤ 14) : False := by
  obtain ⟨b,h⟩ := feasible_root cert tr hs len
  obtain ⟨i,hi,hr⟩ := row_roots b
  exact OrbitDAG.sound_with_pruning (advance:=Sprint.nextS) (fun k v s p hp => by
    rw [Sprint.sprint_eq, Hot.hot_eq]
    apply QuickProof.next_quick_correct
    rwa [←next_literal]) transfer (fun j hj _ _ _ rowEq feas => OrbitDAG.feasible_checked rowEq (tested j hj) feas) 14 i _ _ hi hr h
end Mono2928.Aut.GurCheck

namespace Mono2928.Aut.GurCheck
open Bench2928.GurRow
open PEqualNP.Outside.L_meta_2928.CoThetaNine (SignedLower)
set_option maxRecDepth 8192 in
theorem no_trace_checked (tested : ∀ i<count, verify i=true) (cert : SignedLower)
    {S : Finset Wire} {gs : List Move} (tr : ValidTrace gate Goal S gs)
    (hs : S⊆inputs.toFinset) (len : gs.length ≤ 14) : False :=
  no_trace (orbit_rel_sound
    (fun g i k l v w s t hg h q => row_map ⟨g,hg⟩ i (k,v,s) (l,w,t) h q)
    (fun i k v s h => row_packed i (k,v,s) h)) tested cert tr hs len
end Mono2928.Aut.GurCheck

namespace Mono2928.Aut.GurCheck
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g0 : block 0 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g8 : block 8 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g16 : block 16 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g24 : block 24 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g32 : block 32 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g40 : block 40 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g48 : block 48 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g56 : block 56 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g64 : block 64 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g72 : block 72 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g80 : block 80 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g88 : block 88 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g96 : block 96 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g104 : block 104 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g112 : block 112 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g120 : block 120 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g128 : block 128 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g136 : block 136 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g144 : block 144 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g152 : block 152 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g160 : block 160 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g168 : block 168 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g176 : block 176 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g184 : block 184 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g192 : block 192 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g200 : block 200 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g208 : block 208 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g216 : block 216 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g224 : block 224 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g232 : block 232 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g240 : block 240 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g248 : block 248 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g256 : block 256 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g264 : block 264 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g272 : block 272 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g280 : block 280 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g288 : block 288 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g296 : block 296 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g304 : block 304 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g312 : block 312 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g320 : block 320 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g328 : block 328 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g336 : block 336 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g344 : block 344 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g352 : block 352 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g360 : block 360 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g368 : block 368 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g376 : block 376 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g384 : block 384 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g392 : block 392 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g400 : block 400 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g408 : block 408 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g416 : block 416 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g424 : block 424 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g432 : block 432 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g440 : block 440 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g448 : block 448 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g456 : block 456 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g464 : block 464 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g472 : block 472 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g480 : block 480 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g488 : block 488 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g496 : block 496 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g504 : block 504 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g512 : block 512 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g520 : block 520 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g528 : block 528 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g536 : block 536 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g544 : block 544 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g552 : block 552 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g560 : block 560 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g568 : block 568 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g576 : block 576 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g584 : block 584 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g592 : block 592 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g600 : block 600 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g608 : block 608 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g616 : block 616 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g624 : block 624 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g632 : block 632 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g640 : block 640 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g648 : block 648 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g656 : block 656 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g664 : block 664 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g672 : block 672 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g680 : block 680 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g688 : block 688 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g696 : block 696 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g704 : block 704 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g712 : block 712 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g720 : block 720 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g728 : block 728 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g736 : block 736 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g744 : block 744 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g752 : block 752 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g760 : block 760 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g768 : block 768 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g776 : block 776 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g784 : block 784 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g792 : block 792 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g800 : block 800 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g808 : block 808 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g816 : block 816 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g824 : block 824 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g832 : block 832 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g840 : block 840 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g848 : block 848 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g856 : block 856 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g864 : block 864 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g872 : block 872 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g880 : block 880 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g888 : block 888 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g896 : block 896 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g904 : block 904 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g912 : block 912 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g920 : block 920 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g928 : block 928 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g936 : block 936 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g944 : block 944 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g952 : block 952 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g960 : block 960 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g968 : block 968 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g976 : block 976 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g984 : block 984 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g992 : block 992 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1000 : block 1000 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1008 : block 1008 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1016 : block 1016 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1024 : block 1024 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1032 : block 1032 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1040 : block 1040 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1048 : block 1048 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1056 : block 1056 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1064 : block 1064 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1072 : block 1072 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1080 : block 1080 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1088 : block 1088 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1096 : block 1096 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1104 : block 1104 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1112 : block 1112 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1120 : block 1120 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1128 : block 1128 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1136 : block 1136 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1144 : block 1144 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1152 : block 1152 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1160 : block 1160 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1168 : block 1168 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1176 : block 1176 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1184 : block 1184 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1192 : block 1192 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1200 : block 1200 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1208 : block 1208 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1216 : block 1216 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1224 : block 1224 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1232 : block 1232 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1240 : block 1240 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1248 : block 1248 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1256 : block 1256 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1264 : block 1264 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1272 : block 1272 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1280 : block 1280 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1288 : block 1288 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1296 : block 1296 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1304 : block 1304 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1312 : block 1312 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1320 : block 1320 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1328 : block 1328 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1336 : block 1336 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1344 : block 1344 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1352 : block 1352 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1360 : block 1360 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1368 : block 1368 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1376 : block 1376 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1384 : block 1384 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1392 : block 1392 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1400 : block 1400 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1408 : block 1408 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1416 : block 1416 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1424 : block 1424 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1432 : block 1432 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1440 : block 1440 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1448 : block 1448 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1456 : block 1456 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1464 : block 1464 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1472 : block 1472 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1480 : block 1480 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1488 : block 1488 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1496 : block 1496 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1504 : block 1504 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1512 : block 1512 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1520 : block 1520 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1528 : block 1528 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1536 : block 1536 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1544 : block 1544 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1552 : block 1552 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1560 : block 1560 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1568 : block 1568 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1576 : block 1576 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1584 : block 1584 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1592 : block 1592 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1600 : block 1600 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1608 : block 1608 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1616 : block 1616 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1624 : block 1624 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1632 : block 1632 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1640 : block 1640 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1648 : block 1648 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1656 : block 1656 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1664 : block 1664 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1672 : block 1672 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1680 : block 1680 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1688 : block 1688 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1696 : block 1696 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1704 : block 1704 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1712 : block 1712 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1720 : block 1720 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1728 : block 1728 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1736 : block 1736 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1744 : block 1744 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1752 : block 1752 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1760 : block 1760 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1768 : block 1768 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1776 : block 1776 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1784 : block 1784 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1792 : block 1792 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1800 : block 1800 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1808 : block 1808 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1816 : block 1816 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1824 : block 1824 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1832 : block 1832 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1840 : block 1840 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1848 : block 1848 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1856 : block 1856 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1864 : block 1864 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1872 : block 1872 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1880 : block 1880 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1888 : block 1888 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1896 : block 1896 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1904 : block 1904 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1912 : block 1912 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1920 : block 1920 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1928 : block 1928 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1936 : block 1936 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1944 : block 1944 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1952 : block 1952 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1960 : block 1960 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1968 : block 1968 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1976 : block 1976 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1984 : block 1984 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem g1992 : block 1992 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allGood : valid 0 1998 := (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g0) (subsegment g8)) (joinSeg (subsegment g16) (subsegment g24))) (joinSeg (joinSeg (subsegment g32) (subsegment g40)) (joinSeg (subsegment g48) (subsegment g56)))) (joinSeg (joinSeg (joinSeg (subsegment g64) (subsegment g72)) (joinSeg (subsegment g80) (subsegment g88))) (joinSeg (joinSeg (subsegment g96) (subsegment g104)) (joinSeg (subsegment g112) (subsegment g120))))) (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g128) (subsegment g136)) (joinSeg (subsegment g144) (subsegment g152))) (joinSeg (joinSeg (subsegment g160) (subsegment g168)) (joinSeg (subsegment g176) (subsegment g184)))) (joinSeg (joinSeg (joinSeg (subsegment g192) (subsegment g200)) (joinSeg (subsegment g208) (subsegment g216))) (joinSeg (joinSeg (subsegment g224) (subsegment g232)) (joinSeg (subsegment g240) (subsegment g248)))))) (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g256) (subsegment g264)) (joinSeg (subsegment g272) (subsegment g280))) (joinSeg (joinSeg (subsegment g288) (subsegment g296)) (joinSeg (subsegment g304) (subsegment g312)))) (joinSeg (joinSeg (joinSeg (subsegment g320) (subsegment g328)) (joinSeg (subsegment g336) (subsegment g344))) (joinSeg (joinSeg (subsegment g352) (subsegment g360)) (joinSeg (subsegment g368) (subsegment g376))))) (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g384) (subsegment g392)) (joinSeg (subsegment g400) (subsegment g408))) (joinSeg (joinSeg (subsegment g416) (subsegment g424)) (joinSeg (subsegment g432) (subsegment g440)))) (joinSeg (joinSeg (joinSeg (subsegment g448) (subsegment g456)) (joinSeg (subsegment g464) (subsegment g472))) (joinSeg (joinSeg (subsegment g480) (subsegment g488)) (joinSeg (subsegment g496) (subsegment g504))))))) (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g512) (subsegment g520)) (joinSeg (subsegment g528) (subsegment g536))) (joinSeg (joinSeg (subsegment g544) (subsegment g552)) (joinSeg (subsegment g560) (subsegment g568)))) (joinSeg (joinSeg (joinSeg (subsegment g576) (subsegment g584)) (joinSeg (subsegment g592) (subsegment g600))) (joinSeg (joinSeg (subsegment g608) (subsegment g616)) (joinSeg (subsegment g624) (subsegment g632))))) (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g640) (subsegment g648)) (joinSeg (subsegment g656) (subsegment g664))) (joinSeg (joinSeg (subsegment g672) (subsegment g680)) (joinSeg (subsegment g688) (subsegment g696)))) (joinSeg (joinSeg (joinSeg (subsegment g704) (subsegment g712)) (joinSeg (subsegment g720) (subsegment g728))) (joinSeg (joinSeg (subsegment g736) (subsegment g744)) (joinSeg (subsegment g752) (subsegment g760)))))) (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g768) (subsegment g776)) (joinSeg (subsegment g784) (subsegment g792))) (joinSeg (joinSeg (subsegment g800) (subsegment g808)) (joinSeg (subsegment g816) (subsegment g824)))) (joinSeg (joinSeg (joinSeg (subsegment g832) (subsegment g840)) (joinSeg (subsegment g848) (subsegment g856))) (joinSeg (joinSeg (subsegment g864) (subsegment g872)) (joinSeg (subsegment g880) (subsegment g888))))) (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g896) (subsegment g904)) (joinSeg (subsegment g912) (subsegment g920))) (joinSeg (joinSeg (subsegment g928) (subsegment g936)) (joinSeg (subsegment g944) (subsegment g952)))) (joinSeg (joinSeg (joinSeg (subsegment g960) (subsegment g968)) (joinSeg (subsegment g976) (subsegment g984))) (joinSeg (joinSeg (subsegment g992) (subsegment g1000)) (joinSeg (subsegment g1008) (subsegment g1016)))))))) (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g1024) (subsegment g1032)) (joinSeg (subsegment g1040) (subsegment g1048))) (joinSeg (joinSeg (subsegment g1056) (subsegment g1064)) (joinSeg (subsegment g1072) (subsegment g1080)))) (joinSeg (joinSeg (joinSeg (subsegment g1088) (subsegment g1096)) (joinSeg (subsegment g1104) (subsegment g1112))) (joinSeg (joinSeg (subsegment g1120) (subsegment g1128)) (joinSeg (subsegment g1136) (subsegment g1144))))) (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g1152) (subsegment g1160)) (joinSeg (subsegment g1168) (subsegment g1176))) (joinSeg (joinSeg (subsegment g1184) (subsegment g1192)) (joinSeg (subsegment g1200) (subsegment g1208)))) (joinSeg (joinSeg (joinSeg (subsegment g1216) (subsegment g1224)) (joinSeg (subsegment g1232) (subsegment g1240))) (joinSeg (joinSeg (subsegment g1248) (subsegment g1256)) (joinSeg (subsegment g1264) (subsegment g1272)))))) (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g1280) (subsegment g1288)) (joinSeg (subsegment g1296) (subsegment g1304))) (joinSeg (joinSeg (subsegment g1312) (subsegment g1320)) (joinSeg (subsegment g1328) (subsegment g1336)))) (joinSeg (joinSeg (joinSeg (subsegment g1344) (subsegment g1352)) (joinSeg (subsegment g1360) (subsegment g1368))) (joinSeg (joinSeg (subsegment g1376) (subsegment g1384)) (joinSeg (subsegment g1392) (subsegment g1400))))) (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g1408) (subsegment g1416)) (joinSeg (subsegment g1424) (subsegment g1432))) (joinSeg (joinSeg (subsegment g1440) (subsegment g1448)) (joinSeg (subsegment g1456) (subsegment g1464)))) (joinSeg (joinSeg (joinSeg (subsegment g1472) (subsegment g1480)) (joinSeg (subsegment g1488) (subsegment g1496))) (joinSeg (joinSeg (subsegment g1504) (subsegment g1512)) (joinSeg (subsegment g1520) (subsegment g1528))))))) (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g1536) (subsegment g1544)) (joinSeg (subsegment g1552) (subsegment g1560))) (joinSeg (joinSeg (subsegment g1568) (subsegment g1576)) (joinSeg (subsegment g1584) (subsegment g1592)))) (joinSeg (joinSeg (joinSeg (subsegment g1600) (subsegment g1608)) (joinSeg (subsegment g1616) (subsegment g1624))) (joinSeg (joinSeg (subsegment g1632) (subsegment g1640)) (joinSeg (subsegment g1648) (subsegment g1656))))) (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g1664) (subsegment g1672)) (joinSeg (subsegment g1680) (subsegment g1688))) (joinSeg (joinSeg (subsegment g1696) (subsegment g1704)) (joinSeg (subsegment g1712) (subsegment g1720)))) (joinSeg (joinSeg (joinSeg (subsegment g1728) (subsegment g1736)) (joinSeg (subsegment g1744) (subsegment g1752))) (joinSeg (joinSeg (subsegment g1760) (subsegment g1768)) (joinSeg (subsegment g1776) (subsegment g1784)))))) (joinSeg (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g1792) (subsegment g1800)) (joinSeg (subsegment g1808) (subsegment g1816))) (joinSeg (joinSeg (subsegment g1824) (subsegment g1832)) (joinSeg (subsegment g1840) (subsegment g1848)))) (joinSeg (joinSeg (joinSeg (subsegment g1856) (subsegment g1864)) (joinSeg (subsegment g1872) (subsegment g1880))) (joinSeg (joinSeg (subsegment g1888) (subsegment g1896)) (joinSeg (subsegment g1904) (subsegment g1912))))) (joinSeg (joinSeg (joinSeg (joinSeg (subsegment g1920) (subsegment g1928)) (joinSeg (subsegment g1936) (subsegment g1944))) (joinSeg (joinSeg (subsegment g1952) (subsegment g1960)) (joinSeg (subsegment g1968) (subsegment g1976)))) (joinSeg (subsegment g1984) (subsegment g1992)))))))
end Mono2928.Aut.GurCheck


end PEqualNP.Outside.L_meta_2928
theorem PEqualNP.Outside.L_meta_2928 : ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 ≤ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2 := by
  apply PEqualNP.Outside.L_meta_2928.Mono2928.FinalBridge.deskFromMono
  intro S moves sub tr len
  exact PEqualNP.Outside.L_meta_2928.Mono2928.Aut.GurCheck.no_trace_checked (fun i hi => PEqualNP.Outside.L_meta_2928.Mono2928.Aut.GurCheck.allGood i (Nat.zero_le i) hi) PEqualNP.Outside.L_meta_2928.CoThetaSeven.checked_lower tr sub len
